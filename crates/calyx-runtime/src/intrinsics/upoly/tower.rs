//! Polynomials over polynomial rings, flattened. As the handbook says of
//! Magma's gcds, a polynomial over a polynomial ring (over a polynomial
//! ring, ...) over a ground ring K goes into the multivariate polynomial
//! ring over K in all the variables, the outer ones first, where FLINT's
//! algorithms (`calyx_flint::mpoly`) run; the results come back the same
//! way.

use std::collections::BTreeMap;
use std::rc::Rc;

use calyx_flint::Integer;
use calyx_flint::gr::{Ctx, CtxKind, Elem, GrResult, MonomialOrder, Truth};
use calyx_flint::mpoly as fm;
use calyx_flint::upoly as fu;

type Terms = Vec<(Elem, Vec<u64>)>;

/// The number of variables of a polynomial context.
fn nvars(ctx: &Ctx) -> Option<usize> {
    match ctx.kind() {
        CtxKind::Poly => Some(1),
        CtxKind::MPoly { nvars, .. } => Some(*nvars),
        _ => None,
    }
}

/// Whether FLINT's multivariate algorithms run over the ring: the integers,
/// the rationals and finite fields (prime residue rings included).
fn ground(ctx: &Ctx) -> bool {
    match ctx.kind() {
        CtxKind::Integers | CtxKind::Rationals => true,
        CtxKind::Nmod(p) => Integer::from_u64(*p).is_prime(),
        CtxKind::FmpzMod(p) => p.is_prime(),
        CtxKind::FqZech { .. } | CtxKind::FqNmod { .. } | CtxKind::Fq { .. } | CtxKind::FqPacked { .. } => true,
        _ => false,
    }
}

/// The polynomial rings of a tower from the outer one in, each with the
/// position of its first variable among all of them, the ground ring and
/// the flat ring.
pub(crate) struct Tower {
    levels: Vec<(Rc<Ctx>, usize)>,
    ground: Rc<Ctx>,
    pub flat: Rc<Ctx>,
}

impl Tower {
    /// The tower of the polynomial ring with the context `ctx` if its
    /// coefficients are polynomials over a ground ring FLINT takes.
    pub fn of(ctx: &Rc<Ctx>) -> Option<Tower> {
        let (mut levels, mut n, mut c) = (Vec::new(), 0, ctx.clone());
        while let Some(k) = nvars(&c) {
            levels.push((c.clone(), n));
            n += k;
            c = c.base()?.clone();
        }
        if levels.len() < 2 || !ground(&c) {
            return None;
        }
        let flat = Ctx::mpoly(&c, n, MonomialOrder::Lex);
        Some(Tower { levels, ground: c, flat })
    }

    /// The terms of `x`, an element of the ring at `level` (the ground past
    /// the last), with the exponents `e` of the rings outside it.
    fn terms(&self, level: usize, x: &Elem, e: &mut Vec<u64>, out: &mut Terms) {
        let Some((ctx, off)) = self.levels.get(level) else {
            out.push((x.clone(), e.clone()));
            return;
        };
        let off = *off;
        match ctx.kind() {
            CtxKind::Poly => {
                for i in 0..x.poly_len() {
                    let c = x.poly_coeff(i);
                    if c.is_zero() != Truth::True {
                        e[off] = i as u64;
                        self.terms(level + 1, &c, e, out);
                    }
                }
                e[off] = 0;
            }
            _ => {
                for t in 0..x.mpoly_len() {
                    let (c, ex) = x.mpoly_term(t);
                    e[off..off + ex.len()].copy_from_slice(&ex);
                    self.terms(level + 1, &c, e, out);
                }
                let k = nvars(ctx).expect("a polynomial ring");
                e[off..off + k].fill(0);
            }
        }
    }

    /// The element of the ring at `level` with the flat terms `ts`, whose
    /// exponents of the rings outside it are 0.
    fn build(&self, level: usize, ts: Terms) -> GrResult<Elem> {
        let Some((ctx, off)) = self.levels.get(level) else {
            return Ok(ts.into_iter().next().map(|(c, _)| c).unwrap_or_else(|| Elem::zero(&self.ground)));
        };
        let (off, k) = (*off, nvars(ctx).expect("a polynomial ring"));
        let mut groups: BTreeMap<Vec<u64>, Terms> = BTreeMap::new();
        for (c, mut e) in ts {
            let key = e[off..off + k].to_vec();
            e[off..off + k].fill(0);
            groups.entry(key).or_default().push((c, e));
        }
        match ctx.kind() {
            CtxKind::Poly => {
                let deg = groups.keys().map(|g| g[0] as usize).max();
                let mut coeffs = vec![Elem::zero(ctx.base().expect("a polynomial ring")); deg.map_or(0, |d| d + 1)];
                for (g, ts) in groups {
                    coeffs[g[0] as usize] = self.build(level + 1, ts)?;
                }
                Elem::poly_from_coeffs(ctx, &coeffs)
            }
            _ => {
                let terms = groups.into_iter().map(|(g, ts)| Ok((self.build(level + 1, ts)?, g))).collect::<GrResult<Terms>>()?;
                Elem::mpoly_from_terms(ctx, &terms)
            }
        }
    }

    fn flatten_at(&self, level: usize, x: &Elem) -> GrResult<Elem> {
        let n = match self.flat.kind() {
            CtxKind::MPoly { nvars, .. } => *nvars,
            _ => unreachable!("a multivariate ring"),
        };
        let mut out = Vec::new();
        self.terms(level, x, &mut vec![0; n], &mut out);
        Elem::mpoly_from_terms(&self.flat, &out)
    }

    fn unflatten_at(&self, level: usize, y: &Elem) -> GrResult<Elem> {
        self.build(level, (0..y.mpoly_len()).map(|i| y.mpoly_term(i)).collect())
    }

    /// A polynomial of the outer ring in the flat ring.
    pub fn flatten(&self, x: &Elem) -> GrResult<Elem> {
        self.flatten_at(0, x)
    }

    /// A polynomial of the flat ring in the outer one.
    pub fn unflatten(&self, y: &Elem) -> GrResult<Elem> {
        self.unflatten_at(0, y)
    }

    /// A polynomial of the flat ring free of the outer variables as a
    /// coefficient of the outer ring.
    pub fn unflatten_coeff(&self, y: &Elem) -> GrResult<Elem> {
        self.unflatten_at(1, y)
    }

    /// The gcd in the outer ring, as FLINT normalizes it in the flat one.
    pub fn gcd(&self, x: &Elem, y: &Elem) -> GrResult<Elem> {
        self.unflatten(&fm::gcd(&self.flatten(x)?, &self.flatten(y)?)?)
    }

    /// `x / y` in the outer ring if y (non-zero) divides x.
    pub fn divides(&self, x: &Elem, y: &Elem) -> GrResult<Option<Elem>> {
        fm::divides(&self.flatten(x)?, &self.flatten(y)?)?.map(|q| self.unflatten(&q)).transpose()
    }
}

/// Whether the context is of polynomials (over polynomials ...) over a
/// ground ring FLINT's algorithms take.
pub(crate) fn over_ground(ctx: &Rc<Ctx>) -> bool {
    let mut c = ctx;
    while nvars(c).is_some() {
        c = c.base().expect("a polynomial ring");
    }
    !Rc::ptr_eq(c, ctx) && ground(c)
}

/// The gcd of two elements of a polynomial ring over a field or the
/// integers (possibly a tower), as FLINT normalizes it.
pub(crate) fn poly_gcd(x: &Elem, y: &Elem) -> GrResult<Elem> {
    match (Tower::of(x.ctx()), x.ctx().kind()) {
        (Some(t), _) => t.gcd(x, y),
        (None, CtxKind::Poly) => fu::gcd(x, y),
        (None, _) => fm::gcd(x, y),
    }
}

/// `x / y` in a polynomial ring over a field or the integers (possibly a
/// tower) if y (non-zero) divides x.
pub(crate) fn poly_divides(x: &Elem, y: &Elem) -> GrResult<Option<Elem>> {
    match (Tower::of(x.ctx()), x.ctx().kind()) {
        (Some(t), _) => t.divides(x, y),
        (None, CtxKind::Poly) => fu::divides(x, y),
        (None, _) => fm::divides(x, y),
    }
}
