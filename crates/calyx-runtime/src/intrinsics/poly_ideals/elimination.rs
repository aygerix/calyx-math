//! Elimination, variable extension and homogenization of ideals of
//! multivariate polynomial rings (the handbook's Polynomial Ring Ideal
//! Operations: Elimination, Variable Extension of Ideals and Homogenization
//! of Ideals).
//!
//! Elimination ideals come from reduced Gröbner bases in elimination orders
//! built on grevlex, reached from the easy basis of the ideal. Magma gives
//! them in two ways: `EliminationIdeal(I, k)` sorts that basis by leading
//! monomial in the ring's order and reduces each polynomial by those before
//! it, leaving I as it was; the set form, and preimages under the map of
//! `VariableExtension`, keep the grevlex basis, by decreasing leading
//! monomial, and the ideal keeps its easy basis.

use std::collections::BTreeMap;
use std::rc::Rc;

use calyx_flint::gr::{Elem, Truth};
use calyx_groebner::{self as gb, Order, Terms};

use super::{Dim, Easy, EasyKind, MPolIdeal, dimension_class, elements, homogeneous_terms, ideal_value, leading_monomials, monic, operand, operand_arg, unit, variable};
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::intrinsics::groebner::{engine, shape, terms};
use crate::intrinsics::mpoly::parse_order;
use crate::intrinsics::{arg_not, arg_range, one};
use crate::rings::{Ring, RingKind, make_elt, ring_of};
use crate::value::*;

/// The polynomial ring `pst`.
fn ring(pst: &Rc<Struct>) -> &Ring {
    match &pst.kind {
        StructKind::Ring(r) => r,
        _ => unreachable!("a polynomial ring"),
    }
}

/// Whether the polynomial with the terms `t` is free of the variables
/// marked in `elim`.
fn free_of(t: &Terms, elim: &[bool]) -> bool {
    t.iter().all(|(_, e)| e.iter().zip(elim).all(|(&k, &x)| k == 0 || !x))
}

/// The basis of the elimination ideal of the ideal `id` of `r` (the ring
/// for none) for the variables marked in `elim`, as the set form of
/// `EliminationIdeal` gives it: [1] or empty with every variable
/// eliminated, else the reduced Gröbner basis in grevlex by decreasing
/// leading monomial. The ideal keeps its easy basis.
fn elimination_basis(r: &Ring, id: Option<&MPolIdeal>, elim: &[bool]) -> RResult<Vec<Terms>> {
    let (base, n, _) = shape(r);
    let Some(id) = id else { return Ok(vec![vec![(Elem::one(base)?, vec![0; n])]]) };
    if elim.iter().all(|&x| x) {
        return Ok(match id.dimension()? {
            Dim::Unit => vec![vec![(Elem::one(base)?, vec![0; n])]],
            _ => Vec::new(),
        });
    }
    let easy = id.easy()?;
    let (u, v): (Vec<usize>, Vec<usize>) = (0..n).partition(|&i| elim[i]);
    let g = engine(r, gb::change_order(base, n, &easy.order, &easy.terms, &Order::Elim(u, v)))?;
    Ok(g.into_iter().filter(|t| free_of(t, elim)).collect())
}

/// The basis of the k-th elimination ideal of the ideal `id` of `r` (for
/// 0 < k < n) as `EliminationIdeal(I, k)` gives it, leaving the ideal as it
/// was: the polynomials free of the first k variables in its reduced
/// Gröbner basis for grevlex on them and then on the others, or in its
/// lexicographical basis if one is known (in a ring with that order),
/// sorted by increasing leading monomial in the ring's order; then each is
/// reduced by those before it in that order, dropping those that vanish,
/// and made monic. So the basis need not be a Gröbner basis in the ring's
/// order, nor sorted.
fn kth_elimination_basis(r: &Ring, id: &MPolIdeal, k: usize) -> RResult<Vec<Terms>> {
    let (base, n, order) = shape(r);
    let stored = match (order, &id.known.borrow().groebner) {
        (Order::Lex, Some(g)) => Some(g.iter().map(terms).collect::<Vec<_>>()),
        _ => None,
    };
    let g = match stored {
        Some(g) => g,
        None => {
            let easy = id.find_easy()?;
            engine(r, gb::change_order(base, n, &easy.order, &easy.terms, &Order::ElimK(k)))?
        }
    };
    let elim: Vec<bool> = (0..n).map(|i| i < k).collect();
    let mut ts: Vec<(Vec<u64>, Terms)> = g.into_iter().filter(|t| free_of(t, &elim)).map(|t| (leading_exponents(order, &t), t)).collect();
    ts.sort_by(|a, b| order.cmp(&a.0, &b.0));
    let mut kept: Vec<Terms> = Vec::with_capacity(ts.len());
    for (_, t) in ts {
        let t = if kept.is_empty() { t } else { engine(r, gb::normal_form(base, n, order, &t, &kept))? };
        if !t.is_empty() {
            kept.push(monic_terms(order, t)?);
        }
    }
    Ok(kept)
}

/// The exponents of the leading monomial of the non-zero polynomial with
/// the terms `t` in the order `o`.
fn leading_exponents(o: &Order, t: &Terms) -> Vec<u64> {
    t.iter().map(|(_, e)| e).max_by(|a, b| o.cmp(a, b)).expect("a non-zero polynomial").clone()
}

/// The non-zero polynomial with the terms `t` made monic in the order `o`.
fn monic_terms(o: &Order, t: Terms) -> RResult<Terms> {
    let lead = leading_exponents(o, &t);
    let c = t.iter().find(|(_, e)| *e == lead).expect("the leading term").0.clone();
    if c.is_one() == Truth::True {
        return Ok(t);
    }
    let inv = c.inv()?;
    t.into_iter().map(|(x, e)| Ok((x.mul(&inv)?, e))).collect()
}

/// `EliminationIdeal(I, k)`: the ideal of the polynomials of I free of the
/// first k variables (I itself for k = 0).
fn elimination_ideal(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (pst, id) = operand_arg(a, 0);
    let r = ring(&pst);
    let n = r.ngens();
    let k = a.int(1)?;
    let Some(k) = k.to_u64().filter(|&k| k <= n as u64) else { return Err(arg_range(2, k, 0, n)) };
    if k == 0 {
        return one(a.args[0].clone());
    }
    let ts = match id.as_deref() {
        Some(id) if (k as usize) < n => kth_elimination_basis(r, id, k as usize)?,
        _ => elimination_basis(r, id.as_deref(), &vec![true; n])?,
    };
    one(ideal_value(&pst, elements(r, &ts)?, false))
}

/// `EliminationIdeal(I, S)`: the ideal of the polynomials of I in the
/// variables of S, given by their numbers or as polynomials (I itself if
/// they are all the variables).
fn elimination_ideal_set(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (pst, id) = operand_arg(a, 0);
    let r = ring(&pst);
    let n = r.ngens();
    let Value::Set(s) = &a.args[1] else { unreachable!("a set") };
    let mut elim = vec![true; n];
    for x in s.iter() {
        let i = match &x {
            Value::Int(i) => match i.to_u64().filter(|&i| (1..=n as u64).contains(&i)) {
                Some(i) => i as usize - 1,
                None => return Err(RuntimeError::runtime(format!("Value for variable number ({i}) should be in the range [1..{n}]"))),
            },
            _ => match it.to_ring_elem(&pst, &x, false)?.as_ref().and_then(variable) {
                Some(i) => i,
                None => return Err(RuntimeError::runtime("Argument 2 contains non-variable")),
            },
        };
        elim[i] = false;
    }
    if elim.iter().all(|&x| !x) {
        return one(a.args[0].clone());
    }
    let ts = elimination_basis(r, id.as_deref(), &elim)?;
    one(ideal_value(&pst, elements(r, &ts)?, false))
}

/// The monic generator of I ∩ K[x_i] for an ideal I of `r` with the easy
/// basis `easy` that is zero-dimensional: the first power of x_i whose
/// normal form is a combination of those of the lower powers, found by
/// elimination on the normal forms.
fn univariate_generator(r: &Ring, easy: &Easy, i: usize) -> RResult<Terms> {
    let (base, n, _) = shape(r);
    let zero = Elem::zero(base);
    // The reduced normal forms, each with its pivot monomial (coefficient 1)
    // and the combination of the powers of x_i that it is.
    let mut rows: Vec<(Vec<u64>, BTreeMap<Vec<u64>, Elem>, Vec<Elem>)> = Vec::new();
    let mut power: Terms = vec![(Elem::one(base)?, vec![0; n])];
    for d in 0.. {
        let nf = engine(r, gb::normal_form(base, n, &easy.order, &power, &easy.terms))?;
        let mut v: BTreeMap<Vec<u64>, Elem> = nf.iter().cloned().map(|(c, e)| (e, c)).collect();
        let mut comb = vec![zero.clone(); d + 1];
        comb[d] = Elem::one(base)?;
        for (pivot, row, rc) in &rows {
            let Some(c) = v.get(pivot).cloned() else { continue };
            for (m, x) in row {
                let y = v.get(m).unwrap_or(&zero).sub(&c.mul(x)?)?;
                if y.is_zero() == Truth::True {
                    v.remove(m);
                } else {
                    v.insert(m.clone(), y);
                }
            }
            for (j, x) in rc.iter().enumerate() {
                comb[j] = comb[j].sub(&c.mul(x)?)?;
            }
        }
        let Some((pivot, c)) = v.iter().next().map(|(m, c)| (m.clone(), c.clone())) else {
            let mut out = Vec::new();
            for (j, c) in comb.into_iter().enumerate().rev() {
                if c.is_zero() != Truth::True {
                    let mut e = vec![0; n];
                    e[i] = j as u64;
                    out.push((c, e));
                }
            }
            return Ok(out);
        };
        let inv = c.inv()?;
        let v = v.into_iter().map(|(m, x)| Ok((m, x.mul(&inv)?))).collect::<RResult<_>>()?;
        let comb = comb.iter().map(|x| Ok(x.mul(&inv)?)).collect::<RResult<_>>()?;
        rows.push((pivot, v, comb));
        // The next power, from the normal form of this one.
        power = nf
            .into_iter()
            .map(|(c, mut e)| {
                e[i] += 1;
                (c, e)
            })
            .collect();
    }
    unreachable!("a zero-dimensional ideal")
}

/// The easy basis of the ideal (or ring) of argument 1, which must be
/// zero-dimensional.
fn zero_dimensional(id: Option<&MPolIdeal>) -> RResult<Rc<Easy>> {
    let not = || RuntimeError::runtime("Argument 1 must be zero dimensional");
    let id = id.ok_or_else(not)?;
    let easy = id.easy()?;
    match id.dimension()? {
        Dim::Exactly(0) => Ok(easy),
        _ => Err(not()),
    }
}

/// `UnivariateEliminationIdealGenerator(I, i)`: the monic generator of the
/// polynomials of the zero-dimensional ideal I in the i-th variable alone.
fn univariate_elimination_ideal_generator(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (pst, id) = operand_arg(a, 0);
    let r = ring(&pst);
    let n = r.ngens();
    let i = a.int(1)?;
    let Some(i) = i.to_u64().filter(|&i| (1..=n as u64).contains(&i)) else { return Err(arg_range(2, i, 1, n)) };
    let easy = zero_dimensional(id.as_deref())?;
    let g = univariate_generator(r, &easy, i as usize - 1)?;
    one(make_elt(&pst, Elem::mpoly_from_terms(&r.ctx, &g)?))
}

/// `UnivariateEliminationIdealGenerators(I)`: the generators of
/// `UnivariateEliminationIdealGenerator` for each variable.
fn univariate_elimination_ideal_generators(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (pst, id) = operand_arg(a, 0);
    let r = ring(&pst);
    let easy = zero_dimensional(id.as_deref())?;
    let mut gs = Vec::with_capacity(r.ngens());
    for i in 0..r.ngens() {
        gs.push(make_elt(&pst, Elem::mpoly_from_terms(&r.ctx, &univariate_generator(r, &easy, i)?)?));
    }
    one(Value::seq(Some(Value::Struct(pst.clone())), gs))
}

/// `RelationIdeal(Q)` and `RelationIdeal(Q, T)`: the ideal of the
/// polynomial ring T (of rank #Q, grevlex by default) of the relations
/// between the polynomials of Q. Its basis is the reduced Gröbner basis in
/// grevlex, by decreasing leading monomial and each polynomial monic in the
/// order of T; it is known to be homogeneous or not, and its dimension.
fn relation_ideal(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let q = a.seq(0)?.clone();
    if q.elems.is_empty() {
        return Err(arg_not(1, "non-empty"));
    }
    let Some(Value::Struct(pst)) = &q.universe else { unreachable!("polynomials") };
    let r = ring(pst);
    let (base, n, _) = shape(r);
    let RingKind::MPoly { base: bv, .. } = &r.kind else { unreachable!("a multivariate polynomial ring") };
    let k = q.elems.len();
    let tv = match a.args.get(1) {
        Some(tv) => {
            let (_, tr) = ring_of(tv).expect("a polynomial ring");
            if tr.ngens() != k {
                return Err(RuntimeError::runtime(format!("Argument 2 must have rank {k}")));
            }
            if !Rc::ptr_eq(shape(tr).0, base) {
                return Err(RuntimeError::runtime("Arguments have incompatible coefficient rings"));
            }
            tv.clone()
        }
        None => it.mpoly_ring(bv, k, Order::GRevLex, None, false)?,
    };
    // Eliminate the variables of P from the ideal of the y_j - Q[j] in a
    // ring with new variables y_j after them.
    let mut gens = Vec::with_capacity(k);
    for (j, f) in q.elems.iter().enumerate() {
        let f = it.to_ring_elem(pst, f, false)?.expect("an element of the universe");
        let mut t: Terms = terms(&f).into_iter().map(|(c, e)| Ok((c.neg()?, e.into_iter().chain(std::iter::repeat_n(0, k)).collect()))).collect::<RResult<_>>()?;
        let mut y = vec![0; n + k];
        y[n + j] = 1;
        t.push((Elem::one(base)?, y));
        gens.push(t);
    }
    let g = engine(r, gb::groebner(base, n + k, &Order::ElimK(n), &gens))?;
    let rel: Vec<Terms> = g.into_iter().filter(|t| t.iter().all(|(_, e)| e[..n].iter().all(|&x| x == 0))).map(|t| t.into_iter().map(|(c, e)| (c, e[n..].to_vec())).collect()).collect();
    let (tst, tr) = ring_of(&tv).expect("a polynomial ring");
    let basis = elements(tr, &rel)?.into_iter().map(|f| monic(tr, f)).collect::<RResult<_>>()?;
    let id = MPolIdeal::new(tst.clone(), basis, false);
    {
        let mut kn = id.known.borrow_mut();
        kn.homogeneous = Some(homogeneous_terms(tr, &rel));
        kn.dimension = Some(dimension_class(k, &leading_monomials(&rel)));
        kn.easy = Some(Rc::new(Easy { kind: EasyKind::GRevLex, order: Order::GRevLex, terms: rel }));
    }
    one(Value::structure(StructKind::MPolIdeal(Rc::new(id))))
}

// ----- variable extension and homogenization ---------------------------------------

/// A polynomial ring over the coefficient ring of `r` with `m` variables,
/// in the order named by argument `i` with its arguments after it (grevlex
/// if there is none), and with the names `name(p)` of the variables (by
/// position from 0); those without one print as `$.p`.
fn extended_ring(it: &mut Interp, a: &CallArgs, r: &Ring, m: usize, i: usize, name: impl Fn(usize) -> Option<String>) -> RResult<Value> {
    let RingKind::MPoly { base, .. } = &r.kind else { unreachable!("a multivariate polynomial ring") };
    let order = match a.args.get(i) {
        Some(Value::Str(s)) => parse_order(m, s.as_str(), &a.args[i + 1..], 5)?,
        _ => Order::GRevLex,
    };
    let q = it.mpoly_ring(base, m, order, None, false)?;
    let names: Vec<Option<String>> = (0..m).map(name).collect();
    if names.iter().any(Option::is_some) {
        let (_, qr) = ring_of(&q).expect("a polynomial ring");
        *qr.names.borrow_mut() = names.into_iter().enumerate().map(|(p, s)| s.unwrap_or_else(|| format!("$.{}", p + 1)).into()).collect();
    }
    Ok(q)
}

/// The name of variable `j` (from 0) of `r` as a new ring keeps it: none if
/// `r` has no names.
fn old_name(r: &Ring, j: usize) -> Option<String> {
    r.has_names().then(|| r.gen_name(j + 1))
}

/// The ideal (or the ring) `x` if it belongs to the domain `d` of a map.
fn domain_ideal(d: &Value, x: &Value) -> Option<Option<Rc<MPolIdeal>>> {
    let (pst, id) = operand(x)?;
    matches!(d, Value::Struct(s) if Rc::ptr_eq(s, &pst)).then_some(id)
}

/// Argument `x` of a map as an element of its domain `d`, into which it
/// is coerced as by `!` (from another polynomial ring of the same rank, say).
fn domain_element(it: &mut Interp, d: &Value, x: &Value) -> RResult<Elem> {
    let Value::Struct(pst) = d else { unreachable!("a polynomial ring") };
    it.to_ring_elem(pst, x, true)?.ok_or_else(|| RuntimeError::runtime("Element is not in the domain of the map").in_context("map application"))
}

/// Argument `y` of a preimage as an element of the codomain `c`.
fn codomain_element(it: &mut Interp, c: &Value, y: &Value) -> RResult<Elem> {
    let Value::Struct(qst) = c else { unreachable!("a polynomial ring") };
    it.to_ring_elem(qst, y, true)?.ok_or_else(|| RuntimeError::runtime("Element is not in the codomain of the map").in_context("@@"))
}

/// The ideal `j` and the map `f` from the ring `pst` to `q`, as a call
/// returns them: a statement printing the call shows only the ideal.
fn with_map(a: &CallArgs, pst: &Rc<Struct>, q: Value, j: Value, f: impl NativeMap + 'static) -> RResult<Vals> {
    if a.nresults < 2 {
        return one(j);
    }
    let f = MapObj { kind: MapKind::Map, domain: Value::Struct(pst.clone()), codomain: q, imp: MapImpl::Native(Rc::new(f)) };
    Ok(vals![j, Value::Map(Rc::new(f))])
}

/// The map of `VariableExtension` from P to Q, which has `k` variables more:
/// before those of P, or after them.
struct ExtensionMap {
    k: usize,
    before: bool,
}

impl ExtensionMap {
    /// The exponents in Q of the monomial of P with exponents `e`.
    fn up(&self, e: Vec<u64>) -> Vec<u64> {
        let pad = std::iter::repeat_n(0, self.k);
        if self.before { pad.chain(e).collect() } else { e.into_iter().chain(pad).collect() }
    }

    /// Which variables of Q are the new ones.
    fn new_vars(&self, m: usize) -> Vec<bool> {
        (0..m).map(|p| if self.before { p < self.k } else { p >= m - self.k }).collect()
    }

    /// The exponents in P of a monomial of Q free of the new variables.
    fn down(&self, e: &[u64]) -> Vec<u64> {
        let n = e.len() - self.k;
        if self.before { e[self.k..].to_vec() } else { e[..n].to_vec() }
    }

    /// The image in Q (with the ring `q`) of the polynomial `f` of P.
    fn image(&self, q: &Ring, f: &Elem) -> RResult<Elem> {
        let ts: Terms = terms(f).into_iter().map(|(c, e)| (c, self.up(e))).collect();
        Ok(Elem::mpoly_from_terms(&q.ctx, &ts)?)
    }

    /// The ideal of Q generated by the images of the basis of the ideal of
    /// P (the easy basis once it is known).
    fn image_ideal(&self, pst: &Rc<Struct>, qst: &Rc<Struct>, id: Option<&MPolIdeal>) -> RResult<Value> {
        let basis = match id {
            Some(id) => id.sum_basis()?,
            None => vec![unit(pst)?],
        };
        let q = ring(qst);
        let gens = basis.iter().map(|f| self.image(q, f)).collect::<RResult<_>>()?;
        Ok(ideal_value(qst, gens, false))
    }
}

impl NativeMap for ExtensionMap {
    fn apply(&self, it: &mut Interp, m: &MapObj, x: &Value) -> RResult<Value> {
        let (Value::Struct(pst), Value::Struct(qst)) = (&m.domain, &m.codomain) else { unreachable!("polynomial rings") };
        if let Some(id) = domain_ideal(&m.domain, x) {
            return self.image_ideal(pst, qst, id.as_deref());
        }
        let f = domain_element(it, &m.domain, x)?;
        Ok(make_elt(qst, self.image(ring(qst), &f)?))
    }

    /// The restriction to P of a polynomial of Q free of the new variables,
    /// or of the elimination ideal of an ideal of Q, as the set form of
    /// `EliminationIdeal` gives it.
    fn preimage(&self, it: &mut Interp, m: &MapObj, y: &Value) -> RResult<Value> {
        let (Value::Struct(pst), Value::Struct(qst)) = (&m.domain, &m.codomain) else { unreachable!("polynomial rings") };
        let (p, q) = (ring(pst), ring(qst));
        let new = self.new_vars(q.ngens());
        if let Some(id) = domain_ideal(&m.codomain, y) {
            let ts = elimination_basis(q, id.as_deref(), &new)?;
            let ts: Vec<Terms> = ts.into_iter().map(|t| t.into_iter().map(|(c, e)| (c, self.down(&e))).collect()).collect();
            return Ok(ideal_value(pst, elements(p, &ts)?, false));
        }
        let g = codomain_element(it, &m.codomain, y)?;
        let t = terms(&g);
        if !free_of(&t, &new) {
            return Err(RuntimeError::runtime("Polynomial cannot be restricted").in_context("@@"));
        }
        let t: Terms = t.into_iter().map(|(c, e)| (c, self.down(&e))).collect();
        Ok(make_elt(pst, Elem::mpoly_from_terms(&p.ctx, &t)?))
    }
}

/// `VariableExtension(I, k, b)` and `VariableExtension(I, k, b, order,
/// ...)`: the ideal of the ring with k more variables (before those of the
/// ring P of I if b is true, else after them; grevlex or the given order)
/// that I generates there, and the map from P.
fn variable_extension(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (pst, id) = operand_arg(a, 0);
    let r = ring(&pst);
    let n = r.ngens();
    let k = a.small_ge(1, 1)? as usize;
    let before = a.bool(2)?;
    let map = ExtensionMap { k, before };
    let q = extended_ring(it, a, r, n + k, 3, |p| {
        let j = if before { p.checked_sub(k) } else { Some(p).filter(|&p| p < n) };
        j.and_then(|j| old_name(r, j))
    })?;
    let Value::Struct(qst) = &q else { unreachable!("a polynomial ring") };
    let j = map.image_ideal(&pst, qst, id.as_deref())?;
    with_map(a, &pst, q.clone(), j, map)
}

/// The map of `Homogenization` from P to H, which has the variable H before
/// those of P, or after them.
struct HomogenizationMap {
    before: bool,
}

impl HomogenizationMap {
    /// The exponents in H of the monomial of P with exponents `e` times
    /// H^h.
    fn up(&self, e: Vec<u64>, h: u64) -> Vec<u64> {
        if self.before { std::iter::once(h).chain(e).collect() } else { e.into_iter().chain(std::iter::once(h)).collect() }
    }

    /// The exponents of a monomial of H with the exponent of H first.
    fn h_first(&self, mut e: Vec<u64>) -> Vec<u64> {
        if !self.before {
            e.rotate_right(1);
        }
        e
    }

    /// The homogenization in H (with the ring `q`) of the terms `t` of a
    /// polynomial of P.
    fn homogenize(&self, q: &Ring, t: Terms) -> RResult<Elem> {
        let d = t.iter().map(|(_, e)| e.iter().sum::<u64>()).max().unwrap_or(0);
        let ts: Terms = t.into_iter().map(|(c, e)| {
            let h = d - e.iter().sum::<u64>();
            (c, self.up(e, h))
        }).collect();
        Ok(Elem::mpoly_from_terms(&q.ctx, &ts)?)
    }

    /// The homogenization of the ideal (or ring) `id` of P: the ideal of H of
    /// its reduced Gröbner basis in grevlex homogenized, which the ideal
    /// keeps its easy basis for.
    fn image_ideal(&self, pst: &Rc<Struct>, qst: &Rc<Struct>, id: Option<&MPolIdeal>) -> RResult<Value> {
        let p = ring(pst);
        let (base, n, _) = shape(p);
        let g = match id {
            None => vec![vec![(Elem::one(base)?, vec![0; n])]],
            Some(id) => {
                let easy = id.easy()?;
                match easy.order {
                    Order::GRevLex => easy.terms.clone(),
                    _ => engine(p, gb::change_order(base, n, &easy.order, &easy.terms, &Order::GRevLex))?,
                }
            }
        };
        let q = ring(qst);
        let gens = g.into_iter().map(|t| self.homogenize(q, t)).collect::<RResult<_>>()?;
        Ok(ideal_value(qst, gens, false))
    }
}

impl NativeMap for HomogenizationMap {
    fn apply(&self, it: &mut Interp, m: &MapObj, x: &Value) -> RResult<Value> {
        let (Value::Struct(pst), Value::Struct(qst)) = (&m.domain, &m.codomain) else { unreachable!("polynomial rings") };
        if let Some(id) = domain_ideal(&m.domain, x) {
            return self.image_ideal(pst, qst, id.as_deref());
        }
        let f = domain_element(it, &m.domain, x)?;
        Ok(make_elt(qst, self.homogenize(ring(qst), terms(&f))?))
    }

    /// A polynomial of H with H set to 1, or the ideal of P of the
    /// polynomials of the reduced Gröbner basis of an ideal of H in the order
    /// that eliminates H before grevlex, with H set to 1.
    fn preimage(&self, it: &mut Interp, m: &MapObj, y: &Value) -> RResult<Value> {
        let (Value::Struct(pst), Value::Struct(qst)) = (&m.domain, &m.codomain) else { unreachable!("polynomial rings") };
        let (p, q) = (ring(pst), ring(qst));
        let (base, n1, _) = shape(q);
        let dehomogenize = |t: Terms| -> RResult<Elem> {
            let t: Terms = t.into_iter().map(|(c, e)| (c, e[1..].to_vec())).collect();
            Ok(Elem::mpoly_from_terms(&p.ctx, &t)?)
        };
        if let Some(id) = domain_ideal(&m.codomain, y) {
            let gens: Vec<Terms> = match &id {
                Some(id) => id.basis().iter().map(|f| terms(f).into_iter().map(|(c, e)| (c, self.h_first(e))).collect()).collect(),
                None => vec![vec![(Elem::one(base)?, vec![0; n1])]],
            };
            let g = engine(q, gb::groebner(base, n1, &Order::ElimK(1), &gens))?;
            let basis = g.into_iter().map(dehomogenize).collect::<RResult<_>>()?;
            return Ok(ideal_value(pst, basis, false));
        }
        let g = codomain_element(it, &m.codomain, y)?;
        let t: Terms = terms(&g).into_iter().map(|(c, e)| (c, self.h_first(e))).collect();
        Ok(make_elt(pst, dehomogenize(t)?))
    }
}

/// `Homogenization(I)`, `Homogenization(I, b)`, `Homogenization(I, b,
/// order, ...)` and `Homogenization(I, order, ...)`: the homogenization of
/// I in the ring H with a new variable H, before the variables of the ring
/// P of I if b is true (the default, unlike what the handbook says) and
/// after them otherwise, in grevlex or the given order; and the map from
/// P to H.
fn homogenization(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (pst, id) = operand_arg(a, 0);
    let r = ring(&pst);
    let n = r.ngens();
    let (before, i) = match a.args.get(1) {
        Some(Value::Bool(b)) => (*b, 2),
        _ => (true, 1),
    };
    let map = HomogenizationMap { before };
    let h = if before { 0 } else { n };
    let q = extended_ring(it, a, r, n + 1, i, |p| {
        if p == h {
            return Some("H".to_string());
        }
        old_name(r, if before { p - 1 } else { p }).or_else(|| Some(format!("$.{}", p + 1)))
    })?;
    let Value::Struct(qst) = &q else { unreachable!("a polynomial ring") };
    let j = map.image_ideal(&pst, qst, id.as_deref())?;
    with_map(a, &pst, q.clone(), j, map)
}

pub fn register(it: &mut Interp) {
    let params: Vec<(&str, Value)> = vec![
        ("Al", Value::str("Default")),
        ("Faugere", Value::Bool(true)),
        ("Dense", Value::Bool(false)),
        ("HomogeneousWeights", Value::Bool(true)),
        ("Homogenize", Value::Bool(true)),
        ("GlobalModular", Value::Bool(true)),
    ];
    let doc = "The k-th elimination ideal of I: its polynomials free of the first k variables.";
    it.def_params("EliminationIdeal", "I::RngMPol, k::RngIntElt -> RngMPol", &params, doc, elimination_ideal);
    let doc = "The elimination ideal of I of its polynomials in the variables of S (given by number or as polynomials) alone.";
    it.def("EliminationIdeal", "I::RngMPol, S::{RngIntElt} -> RngMPol", doc, elimination_ideal_set);
    it.def("EliminationIdeal", "I::RngMPol, S::{RngMPolElt} -> RngMPol", doc, elimination_ideal_set);
    let doc = "The monic generator of the polynomials of the zero-dimensional ideal I in the i-th variable alone.";
    it.def("UnivariateEliminationIdealGenerator", "I::RngMPol, i::RngIntElt -> RngMPolElt", doc, univariate_elimination_ideal_generator);
    let doc = "The monic generators of the polynomials of the zero-dimensional ideal I in each variable alone.";
    it.def("UnivariateEliminationIdealGenerators", "I::RngMPol -> [RngMPolElt]", doc, univariate_elimination_ideal_generators);
    let doc = "The ideal of the algebraic relations between the polynomials of Q, in a polynomial ring of rank #Q (T if given).";
    it.def("RelationIdeal", "Q::[RngMPolElt] -> RngMPol", doc, relation_ideal);
    it.def("RelationIdeal", "Q::[RngMPolElt], T::RngMPol -> RngMPol", doc, relation_ideal);
    let doc = "The ideal I in the ring with k more variables (before those of its ring if b is true), and the embedding.";
    it.def("VariableExtension", "I::RngMPol, k::RngIntElt, b::BoolElt -> RngMPol, Map", doc, variable_extension);
    it.def("VariableExtension", "I::RngMPol, k::RngIntElt, b::BoolElt, order::MonStgElt, ... -> RngMPol, Map", doc, variable_extension);
    let doc = "The homogenization of I in the ring with a new variable H (before the others if b is true, the default), and the map.";
    it.def("Homogenization", "I::RngMPol -> RngMPol, Map", doc, homogenization);
    it.def("Homogenization", "I::RngMPol, b::BoolElt -> RngMPol, Map", doc, homogenization);
    it.def("Homogenization", "I::RngMPol, b::BoolElt, order::MonStgElt, ... -> RngMPol, Map", doc, homogenization);
    it.def("Homogenization", "I::RngMPol, order::MonStgElt, ... -> RngMPol, Map", doc, homogenization);
}
