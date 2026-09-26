//! Ideals of multivariate polynomial rings (the handbook's Polynomial Rings
//! and Ideals: Creation of Ideals and Accessing their Bases, and First
//! Operations on Ideals; `elimination` has the sections after them).
//!
//! An ideal of a polynomial ring P is a structure of type RngMPol, like P
//! (`StructKind::MPolIdeal`), with its basis: the generators as given,
//! duplicates and zeros included. The functions of the ring (Rank, Name,
//! MonomialOrder, BaseRing and so on) answer for P, and P acts as the ideal
//! with basis [1].
//!
//! As in Magma, an ideal keeps what the Gröbner basis computations find out
//! about it, and prints it: whether it is homogeneous, its dimension, and
//! the reduced Gröbner basis in the ring's order, which replaces the basis
//! once it is computed. Membership and the predicates need only a Gröbner
//! basis in an "easy" order, grevlex or a weighted grevlex, which is cheaper
//! than most orders; `MPolIdeal::easy` says how Magma chooses it.

use std::cell::RefCell;
use std::cmp::Ordering;
use std::rc::Rc;

use calyx_flint::Integer;
use calyx_flint::gr::{Elem, Truth};
use calyx_flint::mpoly as fm;
use calyx_groebner::{self as gb, Order, Terms, Weights};
use calyx_syntax::ast::BinOp;

use super::groebner::{engine, shape, terms};
use super::mpoly::leading;
use super::{arg_ge, boolv, one};
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::print::{Level, Printer};
use crate::rings::{Elt, Ring, RingKind, make_elt, ring_of};
use crate::value::*;

mod elimination;

/// An ideal of a multivariate polynomial ring.
pub struct MPolIdeal {
    /// The polynomial ring (`Generic(I)`).
    pub ring: Rc<Struct>,
    /// The generators as given, the basis until a Gröbner basis replaces
    /// it. Products and powers of ideals use them.
    pub gens: Vec<Elem>,
    /// Whether the basis is fixed (`IdealWithFixedBasis`).
    pub fixed: bool,
    known: RefCell<Known>,
}

/// What is known about an ideal.
#[derive(Default)]
struct Known {
    homogeneous: Option<bool>,
    dimension: Option<Dim>,
    easy: Option<Rc<Easy>>,
    /// The reduced Gröbner basis in the ring's order, which is then the
    /// basis of the ideal.
    groebner: Option<Rc<[Elem]>>,
}

/// The dimension of an ideal, as far as it is known.
#[derive(Clone, Copy, PartialEq)]
enum Dim {
    /// The ideal is the whole ring (of dimension -1).
    Unit,
    Positive,
    Exactly(usize),
}

/// The order of an easy Gröbner basis.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum EasyKind {
    /// The ring's own order: the easy basis is the Gröbner basis of the
    /// ideal.
    Ring,
    /// grevlex.
    GRevLex,
    /// grevlex with weights that make the generators homogeneous.
    Weighted,
}

/// The Gröbner basis of an ideal in its easy order.
pub struct Easy {
    pub kind: EasyKind,
    pub order: Order,
    /// The reduced basis, by decreasing leading monomial, each polynomial
    /// monic with its terms in decreasing order.
    pub terms: Vec<Terms>,
}

impl MPolIdeal {
    pub fn new(ring: Rc<Struct>, gens: Vec<Elem>, fixed: bool) -> MPolIdeal {
        let StructKind::Ring(r) = &ring.kind else { unreachable!("a polynomial ring") };
        // A homogeneous basis shows that the ideal is homogeneous; an
        // inhomogeneous one shows nothing.
        let homogeneous = homogeneous_basis(r, &gens).then_some(true);
        MPolIdeal { ring, gens, fixed, known: RefCell::new(Known { homogeneous, ..Known::default() }) }
    }

    /// The polynomial ring.
    pub fn poly_ring(&self) -> &Rc<Ring> {
        match &self.ring.kind {
            StructKind::Ring(r) => r,
            _ => unreachable!("a polynomial ring"),
        }
    }

    /// Whether both ideals have one ring and one basis (the ideals are then
    /// equal).
    pub fn same_as(&self, other: &MPolIdeal) -> bool {
        self.poly_ring().id == other.poly_ring().id && self.gens.len() == other.gens.len() && self.gens.iter().zip(&other.gens).all(|(f, g)| f.equal(g) == Truth::True)
    }

    /// The basis: the Gröbner basis in the ring's order once it is known,
    /// else the generators.
    pub fn basis(&self) -> Vec<Elem> {
        match &self.known.borrow().groebner {
            Some(g) => g.to_vec(),
            None => self.gens.clone(),
        }
    }

    /// Whether the basis is the Gröbner basis in the ring's order.
    pub fn has_groebner(&self) -> bool {
        self.known.borrow().groebner.is_some()
    }

    /// Take the basis as it is (unsorted, not monic, unchecked) for the
    /// Gröbner basis in the ring's order, as `MarkGroebner` does; it then
    /// tells whether the ideal is homogeneous, and its dimension.
    pub fn mark_groebner(&self) {
        let r = self.poly_ring();
        let basis = self.basis();
        let lms: Vec<Vec<u64>> = basis.iter().filter_map(|f| leading(r, f)).map(|(_, e)| e).collect();
        let mut k = self.known.borrow_mut();
        k.homogeneous = Some(homogeneous_basis(r, &basis));
        k.dimension = Some(dimension_class(r.ngens(), &lms.iter().map(Vec::as_slice).collect::<Vec<_>>()));
        k.groebner = Some(basis.into());
    }

    /// Take what is known of `other`, an ideal of a ring of the same rank
    /// whose image this ideal is: its dimension, and whether it is
    /// homogeneous when the two rings have one grading.
    pub fn learn_from(&self, other: &MPolIdeal) {
        if std::ptr::eq(self, other) {
            return;
        }
        let o = other.known.borrow();
        let mut k = self.known.borrow_mut();
        if o.homogeneous.is_some() && super::mpoly::weights(self.poly_ring()) == super::mpoly::weights(other.poly_ring()) {
            k.homogeneous = o.homogeneous;
        }
        if o.dimension.is_some() {
            k.dimension = o.dimension;
        }
    }

    /// The Gröbner basis in the easy order, computed once; it tells whether
    /// the ideal is homogeneous and whether it is zero-dimensional. The easy
    /// order is the ring's own when that is a weighted grevlex order or when
    /// the leading monomials of the generators are pairwise coprime (they
    /// are then a Gröbner basis), and the basis of the ideal becomes the
    /// reduced Gröbner basis; else it is grevlex, weighted when weights make
    /// the generators homogeneous but for their constant terms.
    pub fn easy(&self) -> RResult<Rc<Easy>> {
        self.easy_with(gb::Strategy::default())
    }

    /// As `easy`, computed as `strategy` says.
    pub fn easy_with(&self, strategy: gb::Strategy) -> RResult<Rc<Easy>> {
        let easy = self.find_easy_with(strategy)?;
        self.keep_easy(&easy)?;
        Ok(easy)
    }

    /// The easy Gröbner basis, if it is known.
    pub fn known_easy(&self) -> Option<Rc<Easy>> {
        self.known.borrow().easy.clone()
    }

    /// The kind and the order of the easy Gröbner basis.
    fn easy_order(&self) -> (EasyKind, Order) {
        if let Some(e) = &self.known.borrow().easy {
            return (e.kind, e.order.clone());
        }
        let r = self.poly_ring();
        let (_, n, order) = shape(r);
        if matches!(order, Order::GRevLexW(_)) || coprime_leading(r, &self.gens) {
            return (EasyKind::Ring, order.clone());
        }
        match homogeneous_weights(n, &exponents(&self.gens)) {
            Some(w) if w.iter().any(|&x| x != 1) => (EasyKind::Weighted, Order::GRevLexW(w)),
            _ => (EasyKind::GRevLex, Order::GRevLex),
        }
    }

    /// The easy Gröbner basis, as known or computed (without keeping it).
    fn find_easy(&self) -> RResult<Rc<Easy>> {
        self.find_easy_with(gb::Strategy::default())
    }

    /// As `find_easy`, computed as `strategy` says when it is not known.
    fn find_easy_with(&self, strategy: gb::Strategy) -> RResult<Rc<Easy>> {
        if let Some(e) = &self.known.borrow().easy {
            return Ok(e.clone());
        }
        let r = self.poly_ring();
        let (base, n, _) = shape(r);
        let (kind, order) = self.easy_order();
        let terms = engine(r, gb::groebner_with(base, n, &order, &self.gens.iter().map(terms).collect::<Vec<_>>(), strategy))?;
        Ok(Rc::new(Easy { kind, order, terms }))
    }

    /// Keep the easy Gröbner basis `easy` and what it tells, unless one is
    /// kept already.
    fn keep_easy(&self, easy: &Rc<Easy>) -> RResult<()> {
        if self.known.borrow().easy.is_some() {
            return Ok(());
        }
        let r = self.poly_ring();
        let groebner = match easy.kind {
            EasyKind::Ring => Some(elements(r, &easy.terms)?.into()),
            _ => None,
        };
        let mut k = self.known.borrow_mut();
        k.homogeneous = Some(homogeneous_terms(r, &easy.terms));
        k.dimension.get_or_insert(dimension_class(r.ngens(), &leading_monomials(&easy.terms)));
        // A basis marked as the Gröbner basis stays.
        if k.groebner.is_none() {
            k.groebner = groebner;
        }
        k.easy = Some(easy.clone());
        Ok(())
    }

    /// The reduced Gröbner basis in the ring's order, computed once (from
    /// the easy basis); it becomes the basis of the ideal. An easy basis in
    /// the ring's order that a colon ideal was made with is it, but does not
    /// replace the basis.
    pub fn groebner(&self) -> RResult<Rc<[Elem]>> {
        self.groebner_with(gb::Strategy::default())
    }

    /// As `groebner`, computed as `strategy` says when it is not known. As
    /// Magma keeps what it has, a basis already known (or the easy basis it
    /// comes from) serves whatever the strategy: a proven basis over the
    /// rationals needs GlobalModular := false on the first computation.
    pub fn groebner_with(&self, strategy: gb::Strategy) -> RResult<Rc<[Elem]>> {
        if let Some(g) = &self.known.borrow().groebner {
            return Ok(g.clone());
        }
        let easy = self.easy_with(strategy)?;
        if let Some(g) = &self.known.borrow().groebner {
            return Ok(g.clone());
        }
        let r = self.poly_ring();
        if easy.kind == EasyKind::Ring {
            return Ok(elements(r, &easy.terms)?.into());
        }
        let g: Rc<[Elem]> = super::groebner::groebner_from_easy(r, &easy, strategy)?.into();
        self.known.borrow_mut().groebner = Some(g.clone());
        Ok(g)
    }

    /// Whether the ideal is homogeneous, which the easy basis decides.
    fn homogeneous(&self) -> RResult<bool> {
        self.easy()?;
        Ok(self.known.borrow().homogeneous == Some(true))
    }

    /// The dimension class, which the easy basis decides.
    fn dimension(&self) -> RResult<Dim> {
        self.easy()?;
        Ok(self.known.borrow().dimension.expect("known with the easy basis"))
    }

    /// The basis that sums of ideals take: the easy basis once it is known
    /// (each polynomial monic in the ring's order), else the generators.
    fn sum_basis(&self) -> RResult<Vec<Elem>> {
        let easy = self.known.borrow().easy.clone();
        let Some(easy) = easy else { return Ok(self.gens.clone()) };
        let r = self.poly_ring();
        elements(r, &easy.terms)?.into_iter().map(|f| monic(r, f)).collect()
    }

    /// Whether the polynomials `fs` of the ring are all in the ideal.
    pub fn contains_all(&self, fs: &[Elem]) -> RResult<bool> {
        let easy = self.easy()?;
        let r = self.poly_ring();
        let (base, n, _) = shape(r);
        let nfs = engine(r, gb::normal_forms(base, n, &easy.order, &fs.iter().map(terms).collect::<Vec<_>>(), &easy.terms))?;
        Ok(nfs.iter().all(|t| t.is_empty()))
    }

    /// The line on what is known, as Magma prints it before the basis
    /// ("Inhomogeneous, Dimension >0").
    fn header(&self) -> Option<String> {
        let k = self.known.borrow();
        let mut s = String::from(if k.homogeneous? { "Homogeneous" } else { "Inhomogeneous" });
        match k.dimension {
            Some(Dim::Positive) => s.push_str(", Dimension >0"),
            Some(Dim::Exactly(d)) => s.push_str(&format!(", Dimension {d}")),
            _ => {}
        }
        Some(s)
    }
}

fn ideal_value(ring: &Rc<Struct>, gens: Vec<Elem>, fixed: bool) -> Value {
    Value::structure(StructKind::MPolIdeal(Rc::new(MPolIdeal::new(ring.clone(), gens, fixed))))
}

/// A multivariate polynomial ring (as the ideal with basis [1]) or an ideal
/// of one: the ring and the ideal.
fn operand(v: &Value) -> Option<(Rc<Struct>, Option<Rc<MPolIdeal>>)> {
    match v.as_struct()? {
        StructKind::MPolIdeal(id) => Some((id.ring.clone(), Some(id.clone()))),
        StructKind::Ring(r) if matches!(r.kind, RingKind::MPoly { .. }) => {
            let Value::Struct(st) = v else { unreachable!() };
            Some((st.clone(), None))
        }
        _ => None,
    }
}

/// The unit of the ring `pst`.
fn unit(pst: &Rc<Struct>) -> RResult<Elem> {
    let StructKind::Ring(r) = &pst.kind else { unreachable!("a polynomial ring") };
    Ok(Elem::one(&r.ctx)?)
}

/// A multivariate polynomial ring or an ideal of one: the ring and the
/// basis ([1] for the ring).
fn ideal_parts(v: &Value) -> Option<(Rc<Struct>, Vec<Elem>)> {
    let (pst, id) = operand(v)?;
    let basis = match id {
        Some(id) => id.basis(),
        None => vec![unit(&pst).ok()?],
    };
    Some((pst, basis))
}

/// The generators of an operand of a product or power: those given for an
/// ideal, [1] for the ring.
fn generators_of(pst: &Rc<Struct>, id: &Option<Rc<MPolIdeal>>) -> RResult<Vec<Elem>> {
    match id {
        Some(id) => Ok(id.gens.clone()),
        None => Ok(vec![unit(pst)?]),
    }
}

/// Argument `i`, which the signature makes a polynomial ring or an ideal of
/// one: the ring and the ideal.
fn operand_arg(a: &CallArgs, i: usize) -> (Rc<Struct>, Option<Rc<MPolIdeal>>) {
    operand(&a.args[i]).expect("a polynomial ring or ideal")
}

/// Argument `i` as by `operand_arg`, with its basis.
fn ideal_arg(a: &CallArgs, i: usize) -> (Rc<Struct>, Vec<Elem>) {
    ideal_parts(&a.args[i]).expect("a polynomial ring or ideal")
}

fn coercion_map(domain: Value, codomain: Value) -> Value {
    Value::Map(Rc::new(MapObj { kind: MapKind::Map, domain, codomain, imp: MapImpl::Coercion }))
}

// ----- Gröbner bases ---------------------------------------------------------------

/// The polynomials of `r` with the terms `ts`.
fn elements(r: &Ring, ts: &[Terms]) -> RResult<Vec<Elem>> {
    ts.iter().map(|t| Ok(Elem::mpoly_from_terms(&r.ctx, t)?)).collect()
}

/// `f`, a polynomial of `r`, divided by its leading coefficient in the
/// ring's order.
fn monic(r: &Ring, f: Elem) -> RResult<Elem> {
    match leading(r, &f) {
        Some((c, _)) if c.is_one() != Truth::True => Ok(f.mpoly_mul_scalar(&c.inv()?)?),
        _ => Ok(f),
    }
}

/// The weighted degree of the monomial with exponents `e`.
fn wdeg(w: &[u64], e: &[u64]) -> u128 {
    w.iter().zip(e).map(|(&w, &k)| w as u128 * k as u128).sum()
}

/// Whether the terms `t` of a polynomial have one degree for the weights `w`.
fn homogeneous_in(w: &[u64], t: &Terms) -> bool {
    t.iter().all(|(_, e)| wdeg(w, e) == wdeg(w, &t[0].1))
}

/// Whether the polynomials `ts` of `r` are homogeneous in its grading.
fn homogeneous_terms(r: &Ring, ts: &[Terms]) -> bool {
    let w = super::mpoly::weights(r);
    ts.iter().all(|t| homogeneous_in(&w, t))
}

/// The exponents of the terms of the polynomials `gens`.
fn exponents(gens: &[Elem]) -> Vec<Vec<Vec<u64>>> {
    gens.iter().map(|g| (0..g.mpoly_len()).map(|i| g.mpoly_term(i).1).collect()).collect()
}

/// Whether the leading monomials of the non-zero polynomials `gens` of `r`
/// are pairwise coprime, which makes the polynomials a Gröbner basis.
fn coprime_leading(r: &Ring, gens: &[Elem]) -> bool {
    let mut used = vec![false; r.ngens()];
    for g in gens {
        let Some((_, e)) = leading(r, g) else { continue };
        for (i, &k) in e.iter().enumerate() {
            if k > 0 {
                if used[i] {
                    return false;
                }
                used[i] = true;
            }
        }
    }
    true
}

/// Positive weights of the `n` variables in which the terms of each of the
/// polynomials `polys` (as the exponents of their terms) but its constant
/// term have one weighted degree, as Magma chooses them for the easy order:
/// on each set of variables that the polynomials link, the weights with the
/// least sum, then with the least largest weight, the later variables the
/// heavier on a tie. None if there are none; where the weights are not
/// unique the search is bounded.
fn homogeneous_weights(n: usize, polys: &[Vec<Vec<u64>>]) -> Option<Vec<u64>> {
    // The equations: the differences of the exponents of the terms.
    let mut rows: Vec<Vec<i128>> = Vec::new();
    for p in polys {
        let es: Vec<&Vec<u64>> = p.iter().filter(|e| e.iter().any(|&k| k > 0)).collect();
        for e in es.iter().skip(1) {
            if e.iter().chain(es[0]).any(|&k| k > 1 << 20) {
                return None;
            }
            let row: Vec<i128> = e.iter().zip(es[0]).map(|(&a, &b)| a as i128 - b as i128).collect();
            if row.iter().any(|&x| x != 0) {
                rows.push(row);
            }
        }
    }
    // The sets of variables that the equations link.
    let mut link: Vec<usize> = (0..n).collect();
    fn root(link: &mut [usize], mut i: usize) -> usize {
        while link[i] != i {
            link[i] = link[link[i]];
            i = link[i];
        }
        i
    }
    for row in &rows {
        let vars: Vec<usize> = (0..n).filter(|&i| row[i] != 0).collect();
        for pair in vars.windows(2) {
            let (a, b) = (root(&mut link, pair[0]), root(&mut link, pair[1]));
            link[a] = b;
        }
    }
    let mut weights = vec![1; n];
    for c in 0..n {
        if root(&mut link, c) != c {
            continue;
        }
        let vars: Vec<usize> = (0..n).filter(|&i| root(&mut link, i) == c).collect();
        let eqs: Vec<Vec<i128>> = rows.iter().filter(|row| vars.iter().any(|&i| row[i] != 0)).map(|row| vars.iter().map(|&i| row[i]).collect()).collect();
        if eqs.is_empty() {
            continue;
        }
        for (i, w) in vars.iter().zip(linked_weights(eqs, vars.len())?) {
            weights[*i] = w;
        }
    }
    Some(weights)
}

/// The weights of `homogeneous_weights` for one set of `m` linked
/// variables with the equations `eqs`.
fn linked_weights(mut eqs: Vec<Vec<i128>>, m: usize) -> Option<Vec<u64>> {
    fn gcd(a: i128, b: i128) -> i128 {
        if b == 0 { a.abs() } else { gcd(b, a % b) }
    }
    // The reduced echelon form over the integers.
    let mut pivots = Vec::new();
    for c in 0..m {
        let r = pivots.len();
        let Some(p) = (r..eqs.len()).find(|&i| eqs[i][c] != 0) else { continue };
        eqs.swap(r, p);
        for i in 0..eqs.len() {
            if i != r && eqs[i][c] != 0 {
                let (x, y) = (eqs[r][c], eqs[i][c]);
                for j in 0..m {
                    eqs[i][j] = eqs[i][j].checked_mul(x)?.checked_sub(eqs[r][j].checked_mul(y)?)?;
                }
                let g = eqs[i].iter().fold(0, |g, &x| gcd(g, x));
                if g > 1 {
                    eqs[i].iter_mut().for_each(|x| *x /= g);
                }
            }
        }
        pivots.push(c);
    }
    let free: Vec<usize> = (0..m).filter(|c| !pivots.contains(c)).collect();
    if free.is_empty() {
        return None;
    }
    // The weights with the given values of the free variables, if integral.
    let solve = |vals: &[i128]| -> Option<Vec<i128>> {
        let mut w = vec![0; m];
        for (&f, &v) in free.iter().zip(vals) {
            w[f] = v;
        }
        for (r, &c) in pivots.iter().enumerate() {
            let s = free.iter().try_fold(0i128, |s, &f| s.checked_sub(eqs[r][f].checked_mul(w[f])?))?;
            if s % eqs[r][c] != 0 {
                return None;
            }
            w[c] = s / eqs[r][c];
        }
        Some(w)
    };
    let positive = |w: Vec<u64>| w.iter().all(|&x| x > 0).then_some(w);
    if free.len() == 1 {
        // A single ray: its primitive vector, if positive.
        let d = pivots.iter().enumerate().fold(1i128, |l, (r, &c)| {
            let q = eqs[r][c].abs() / gcd(eqs[r][c], eqs[r][free[0]]);
            l / gcd(l, q) * q
        });
        let w = solve(&[d])?;
        let g = w.iter().fold(0, |g, &x| gcd(g, x));
        return positive(w.iter().map(|&x| u64::try_from(x / g).unwrap_or(0)).collect());
    }
    // A bounded search over the free variables.
    let bound = (1..=32).rev().find(|&b: &i128| b.checked_pow(free.len() as u32).is_some_and(|t| t <= 1 << 16)).unwrap_or(1);
    let mut vals = vec![1; free.len()];
    let mut best: Option<Vec<i128>> = None;
    loop {
        if let Some(w) = solve(&vals).filter(|w| w.iter().all(|&x| x > 0)) {
            let key = |w: &[i128]| (w.iter().sum::<i128>(), *w.iter().max().unwrap());
            let better = best.as_ref().is_none_or(|b| key(&w).cmp(&key(b)).then_with(|| b.iter().rev().cmp(w.iter().rev())) == Ordering::Less);
            if better {
                best = Some(w);
            }
        }
        let Some(i) = vals.iter().position(|&v| v < bound) else { break };
        vals[i] += 1;
        vals[..i].iter_mut().for_each(|v| *v = 1);
    }
    positive(best?.iter().map(|&x| x as u64).collect())
}

/// The leading monomials of the polynomials `ts` (with their terms in
/// decreasing order).
fn leading_monomials(ts: &[Terms]) -> Vec<&[u64]> {
    ts.iter().filter_map(|t| t.first()).map(|(_, e)| e.as_slice()).collect()
}

/// The dimension class of an ideal of a ring of rank `n` with a Gröbner
/// basis with leading monomials `lms`: zero-dimensional when a power of each
/// variable is one of them.
fn dimension_class(n: usize, lms: &[&[u64]]) -> Dim {
    let pure = |i: usize| lms.iter().any(|e| e[i] > 0 && e.iter().enumerate().all(|(j, &k)| j == i || k == 0));
    if lms.iter().any(|e| e.iter().all(|&k| k == 0)) {
        Dim::Unit
    } else if (0..n).all(pure) {
        Dim::Exactly(0)
    } else {
        Dim::Positive
    }
}

/// A largest set of variables (by number) of which none of the leading
/// monomials `lms` of a Gröbner basis of a proper ideal is a product: a
/// maximally independent set, whose size is the dimension. Of the largest
/// sets, the one with the latest variables, as Magma chooses.
fn independent_set(n: usize, lms: &[&[u64]]) -> Vec<usize> {
    // The monomials with each variable, as their sets of variables.
    let mut with: Vec<Vec<Vec<usize>>> = vec![Vec::new(); n];
    for e in lms {
        let vars: Vec<usize> = (0..n).filter(|&i| e[i] > 0).collect();
        for &i in &vars {
            with[i].push(vars.clone());
        }
    }
    struct Search<'a> {
        with: &'a [Vec<Vec<usize>>],
        inset: Vec<bool>,
        cur: Vec<usize>,
        best: Vec<usize>,
    }
    impl Search<'_> {
        // Decide the variables below `v`, the later first; a set replaces
        // the best only if larger.
        fn run(&mut self, v: usize) {
            if self.cur.len() + v <= self.best.len() {
                return;
            }
            if v == 0 {
                self.best = self.cur.clone();
                return;
            }
            let i = v - 1;
            self.inset[i] = true;
            if self.with[i].iter().all(|vars| vars.iter().any(|&j| !self.inset[j])) {
                self.cur.push(i);
                self.run(i);
                self.cur.pop();
            }
            self.inset[i] = false;
            self.run(i);
        }
    }
    let mut s = Search { with: &with, inset: vec![false; n], cur: Vec::new(), best: Vec::new() };
    s.run(n);
    let mut u = s.best;
    u.sort_unstable();
    u
}

/// The number of monomials in `n` variables that none of the monomials
/// `lms` divides (for the leading monomials of a Gröbner basis of a
/// zero-dimensional ideal, the dimension of the quotient).
fn standard_monomials(n: usize, lms: &[&[u64]]) -> Integer {
    fn count(i: usize, e: &mut [u64], lms: &[&[u64]]) -> u128 {
        if i == e.len() {
            return 1;
        }
        let mut total = 0;
        loop {
            // The later variables are still 0.
            if lms.iter().any(|m| m.iter().zip(e.iter()).all(|(a, b)| a <= b)) {
                break;
            }
            total += count(i + 1, e, lms);
            e[i] += 1;
        }
        e[i] = 0;
        total
    }
    let mut e = vec![0; n];
    let c = count(0, &mut e, lms);
    Integer::from_limbs(&[c as u64, (c >> 64) as u64], false)
}

/// The terms of `f` with the exponent `k` of a new first variable.
fn lift(f: &Elem, k: u64) -> Terms {
    terms(f).into_iter().map(|(c, e)| (c, std::iter::once(k).chain(e).collect())).collect()
}

/// The order on a new first variable and `n` others that eliminates the
/// first and orders the monomials in the others by `o`.
fn eliminating(o: &Order, n: usize) -> Order {
    match o {
        Order::Lex => Order::Lex,
        Order::GRevLex => Order::ElimK(1),
        _ => {
            let row = |first: u64, rest: Vec<Integer>| std::iter::once(Integer::from_u64(first)).chain(rest).collect::<Vec<_>>();
            let mut rows = vec![row(1, vec![Integer::zero(); n])];
            rows.extend(o.weight_vectors(n).into_iter().map(|w| row(0, w)));
            Order::Weight(Weights::new(rows))
        }
    }
}

/// grevlex for the positive weights `w` with the variable `last` the least:
/// the one whose exponent decides a tie first.
fn bayer_order(w: &[u64], last: usize) -> Order {
    let n = w.len();
    let mut row: Vec<Integer> = w.iter().map(|&x| Integer::from_u64(x)).collect();
    let mut rows = vec![row.clone()];
    for i in std::iter::once(last).chain((0..n).rev().filter(|&i| i != last)).take(n - 1) {
        row[i] = Integer::zero();
        rows.push(row.clone());
    }
    Order::Weight(Weights::new(rows))
}

/// The intersection of the ideals of `r` that `fs` and `gs` generate, as its
/// reduced Gröbner basis in the order `o`: the polynomials free of a new
/// variable t in the ideal generated by t f for f in `fs` and (1 - t) g for
/// g in `gs`.
fn intersection(r: &Ring, o: &Order, fs: &[Elem], gs: &[Elem]) -> RResult<Vec<Terms>> {
    let (base, n, _) = shape(r);
    let mut gens: Vec<Terms> = fs.iter().map(|f| lift(f, 1)).collect();
    for g in gs {
        let mut t = lift(g, 0);
        for (c, e) in lift(g, 1) {
            t.push((c.neg()?, e));
        }
        gens.push(t);
    }
    let g = engine(r, gb::groebner(base, n + 1, &eliminating(o, n), &gens))?;
    Ok(g.into_iter().filter(|t| t.iter().all(|(_, e)| e[0] == 0)).map(|t| t.into_iter().map(|(c, e)| (c, e[1..].to_vec())).collect()).collect())
}

/// Whether some power of `f` is in the ideal of `r` generated by `gens`:
/// whether 1 - t f and `gens` generate the unit ideal in a ring with a new
/// variable t.
fn in_radical(r: &Ring, f: &Elem, gens: &[Elem]) -> RResult<bool> {
    let (base, n, _) = shape(r);
    let mut ts: Vec<Terms> = gens.iter().map(|g| lift(g, 0)).collect();
    let mut t: Terms = lift(f, 1).into_iter().map(|(c, e)| Ok((c.neg()?, e))).collect::<RResult<_>>()?;
    t.push((Elem::one(base)?, vec![0; n + 1]));
    ts.push(t);
    let g = engine(r, gb::groebner(base, n + 1, &Order::GRevLex, &ts))?;
    Ok(dimension_class(n + 1, &leading_monomials(&g)) == Dim::Unit)
}

// ----- construction ----------------------------------------------------------------

/// The basis of `ideal<P | ...>`: elements coercing into P, ideals of P,
/// and sets and sequences of these.
fn generators(it: &mut Interp, pst: &Rc<Struct>, right: &[Value]) -> RResult<Vec<Elem>> {
    let invalid = |i: usize| RuntimeError::runtime(format!("Rhs argument {} is invalid for this constructor", i + 1)).in_context("ideal< ... >");
    let mut out = Vec::new();
    for (i, v) in right.iter().enumerate() {
        let items: Vec<Value> = match v {
            Value::Seq(s) => s.elems.clone(),
            Value::Set(s) => s.iter().collect(),
            _ => vec![v.clone()],
        };
        for x in &items {
            if let Some((r, gs)) = ideal_parts(x) {
                if !struct_eq(&r, pst) {
                    return Err(invalid(i));
                }
                out.extend(gs);
                continue;
            }
            out.push(it.to_ring_elem(pst, x, false)?.ok_or_else(|| invalid(i))?);
        }
    }
    Ok(out)
}

/// `ideal<P | ...>` for a multivariate polynomial ring P: the ideal and its
/// inclusion into P.
pub fn ideal_constructor(it: &mut Interp, base: &Value, right: &[Value]) -> RResult<Option<Vec<Value>>> {
    let Some((pst, _)) = ring_of(base).filter(|(_, r)| matches!(r.kind, RingKind::MPoly { .. })) else { return Ok(None) };
    let pst = pst.clone();
    let gens = generators(it, &pst, right)?;
    let ideal = ideal_value(&pst, gens, false);
    Ok(Some(vec![ideal.clone(), coercion_map(ideal, base.clone())]))
}

/// The products of the elements of `xs` and `ys`, normalized, without
/// repetitions and in increasing order (as Magma builds the basis of a
/// product of ideals).
fn products(it: &mut Interp, pst: &Rc<Struct>, xs: &[Elem], ys: &[Elem]) -> RResult<Vec<Elem>> {
    let mut out = Vec::with_capacity(xs.len() * ys.len());
    for x in xs {
        for y in ys {
            out.push(x.mul(y)?);
        }
    }
    let out = normalized(it, pst, &out)?;
    sort_dedup(it, pst, out)
}

/// Polynomials of `pst` in increasing order (term by term in the monomial
/// order, then by coefficients), each once.
fn sort_dedup(it: &mut Interp, pst: &Rc<Struct>, mut xs: Vec<Elem>) -> RResult<Vec<Elem>> {
    let StructKind::Ring(r) = &pst.kind else { unreachable!("a polynomial ring") };
    let mut err = None;
    xs.sort_by(|x, y| match it.ring_elt_cmp(r, x, y) {
        Ok(o) => o.unwrap_or(Ordering::Equal),
        Err(e) => {
            err.get_or_insert(e);
            Ordering::Equal
        }
    });
    if let Some(e) = err {
        return Err(e);
    }
    xs.dedup_by(|x, y| x.equal(y) == Truth::True);
    Ok(xs)
}

/// The polynomials `xs` of `pst`, normalized.
fn normalized(it: &mut Interp, pst: &Rc<Struct>, xs: &[Elem]) -> RResult<Vec<Elem>> {
    xs.iter().map(|x| super::mpoly::normalized(it, &Elt { parent: pst.clone(), x: x.clone() })).collect()
}

/// `I^k`: the ring for k = 0, I for k = 1, else the products of k of the
/// generators.
fn ideal_pow(it: &mut Interp, a: &Value, k: &Integer) -> RResult<Value> {
    let (pst, id) = operand(a).expect("a polynomial ring or ideal");
    if k.sign() < 0 {
        return Err(arg_ge(2, k, 0).in_context("^"));
    }
    let Some(k) = k.to_u64().filter(|&k| k < 1 << 30) else {
        return Err(RuntimeError::runtime(format!("Argument 2 ({k}) is too large")).in_context("^"));
    };
    match k {
        0 => return Ok(Value::Struct(pst)),
        1 => return Ok(a.clone()),
        _ => {}
    }
    // The products are those of the distinct normalized elements.
    let xs = normalized(it, &pst, &generators_of(&pst, &id)?)?;
    let xs = sort_dedup(it, &pst, xs)?;
    let acc = match xs.as_slice() {
        [x] => normalized(it, &pst, &[x.pow(&Integer::from_u64(k))?])?,
        _ => {
            let mut acc = xs.clone();
            for _ in 1..k {
                acc = products(it, &pst, &acc, &xs)?;
            }
            acc
        }
    };
    Ok(ideal_value(&pst, acc, false))
}

// ----- operations ------------------------------------------------------------------

type Operand = Option<Rc<MPolIdeal>>;

/// `A eq B` for ideals of one ring (None for the ring itself), as Magma
/// decides it: by their reduced Gröbner bases, the easy ones when both are
/// in grevlex, else those in the ring's order (which become the bases).
fn ideals_equal(a: &Operand, b: &Operand) -> RResult<bool> {
    match (a, b) {
        (Some(x), Some(y)) if Rc::ptr_eq(x, y) => Ok(true),
        (Some(x), Some(y)) => {
            let (ex, ey) = (x.easy()?, y.easy()?);
            if ex.kind == EasyKind::GRevLex && ey.kind == EasyKind::GRevLex {
                return Ok(same_terms(&ex.terms, &ey.terms));
            }
            let (gx, gy) = (x.groebner()?, y.groebner()?);
            Ok(gx.len() == gy.len() && gx.iter().zip(gy.iter()).all(|(f, g)| f.equal(g) == Truth::True))
        }
        (Some(x), None) | (None, Some(x)) => {
            let g = x.groebner()?;
            Ok(g.len() == 1 && g[0].is_one() == Truth::True)
        }
        (None, None) => Ok(true),
    }
}

/// Whether two lists of polynomials as terms are equal.
fn same_terms(xs: &[Terms], ys: &[Terms]) -> bool {
    let same = |s: &Terms, t: &Terms| s.len() == t.len() && s.iter().zip(t).all(|((c, e), (d, f))| e == f && c.equal(d) == Truth::True);
    xs.len() == ys.len() && xs.iter().zip(ys).all(|(s, t)| same(s, t))
}

/// `A subset B`: the basis of A in B.
fn ideal_subset(pst: &Rc<Struct>, a: &Operand, b: &Operand) -> RResult<bool> {
    match (a, b) {
        (_, None) => Ok(true),
        (Some(x), Some(y)) if Rc::ptr_eq(x, y) => Ok(true),
        (None, Some(y)) => y.contains_all(&[unit(pst)?]),
        (Some(x), Some(y)) => y.contains_all(&x.basis()),
    }
}

/// Operators on ideals of multivariate polynomial rings (with an ideal
/// among the operands, or on the rings themselves as ideals).
pub fn ideal_binop(it: &mut Interp, op: BinOp, a: &Value, b: &Value) -> RResult<Option<Value>> {
    let is_ideal = |v: &Value| matches!(v.as_struct(), Some(StructKind::MPolIdeal(_)));
    if op == BinOp::Pow {
        return match (operand(a), b) {
            (Some(_), Value::Int(k)) => Ok(Some(ideal_pow(it, a, k)?)),
            _ => Ok(None),
        };
    }
    // The rings themselves have sums, products, intersections and
    // inclusions as ideals (their equality is that of structures).
    let ring_op = matches!(op, BinOp::Add | BinOp::Mul | BinOp::Meet | BinOp::Subset | BinOp::Notsubset);
    if !(ring_op || matches!(op, BinOp::Eq | BinOp::Ne) && (is_ideal(a) || is_ideal(b))) {
        return Ok(None);
    }
    let (Some((r, x)), Some((s, y))) = (operand(a), operand(b)) else { return Ok(None) };
    if !struct_eq(&r, &s) {
        return Err(RuntimeError::runtime(format!("Arguments are not compatible\nArgument types given: {}, {}", it.type_name_ext(a), it.type_name_ext(b))).in_context(op.intrinsic_name()));
    }
    let ctx = |e: RuntimeError| e.in_context(op.intrinsic_name());
    Ok(Some(match (op, &x, &y) {
        // The sum with the ring is the ring.
        (BinOp::Add, None, _) => a.clone(),
        (BinOp::Add, _, None) => b.clone(),
        (BinOp::Add, Some(x), Some(y)) => ideal_value(&r, [x.sum_basis().map_err(ctx)?, y.sum_basis().map_err(ctx)?].concat(), false),
        (BinOp::Mul, _, _) => ideal_value(&r, products(it, &r, &generators_of(&r, &x)?, &generators_of(&r, &y)?)?, false),
        (BinOp::Eq | BinOp::Ne, _, _) => Value::Bool(ideals_equal(&x, &y).map_err(ctx)? == (op == BinOp::Eq)),
        (BinOp::Subset | BinOp::Notsubset, _, _) => Value::Bool(ideal_subset(&r, &x, &y).map_err(ctx)? == (op == BinOp::Subset)),
        (BinOp::Meet, _, _) => meet(a, b).map_err(ctx)?,
        _ => unreachable!("an operator on ideals"),
    }))
}

/// Whether the basis of the ideal is [1].
fn unit_basis(id: &MPolIdeal) -> bool {
    matches!(id.basis().as_slice(), [f] if f.is_one() == Truth::True)
}

/// `A meet B` for ideals of one ring (or the ring itself), as Magma gives
/// it: A or B when the other is the ring, is the same ideal or has the basis
/// [1]; else a new ideal with the reduced Gröbner basis of the intersection
/// in grevlex, weighted if weights make the basis of A homogeneous.
fn meet(a: &Value, b: &Value) -> RResult<Value> {
    let (pst, x) = operand(a).expect("a polynomial ring or ideal");
    let (x, y) = match (x, operand(b).expect("a polynomial ring or ideal").1) {
        (_, None) => return Ok(a.clone()),
        (None, _) => return Ok(b.clone()),
        (Some(x), Some(y)) => (x, y),
    };
    if Rc::ptr_eq(&x, &y) || unit_basis(&y) {
        return Ok(a.clone());
    }
    if unit_basis(&x) {
        return Ok(b.clone());
    }
    let r = x.poly_ring();
    let fs = x.basis();
    // The weights of the easy order ignore constant terms; these may not.
    let exps = exponents(&fs);
    let constant = exps.iter().any(|p| p.len() > 1 && p.iter().any(|e| e.iter().all(|&k| k == 0)));
    let o = match homogeneous_weights(r.ngens(), &exps) {
        Some(w) if !constant && w.iter().any(|&k| k != 1) => Order::GRevLexW(w),
        _ => Order::GRevLex,
    };
    let ts = intersection(r, &o, &fs, &y.basis())?;
    Ok(ideal_value(&pst, elements(r, &ts)?, false))
}

// ----- colon ideals and saturation -------------------------------------------------

/// Whether two values are the same structure.
fn same_value(a: &Value, b: &Value) -> bool {
    matches!((a, b), (Value::Struct(x), Value::Struct(y)) if Rc::ptr_eq(x, y))
}

/// Whether `f` is a constant polynomial.
fn is_constant(f: &Elem) -> bool {
    (0..f.mpoly_len()).all(|i| f.mpoly_term(i).1.iter().all(|&k| k == 0))
}

/// The number of the variable that the polynomial `f` is, if it is one.
fn variable(f: &Elem) -> Option<usize> {
    if f.mpoly_len() != 1 {
        return None;
    }
    let (c, e) = f.mpoly_term(0);
    if c.is_one() != Truth::True || e.iter().sum::<u64>() != 1 {
        return None;
    }
    e.iter().position(|&k| k == 1)
}

/// `I : g` for an ideal I (or the ring), the value `iv`, and a polynomial g
/// of its ring, as Magma gives it: the ring for g = 0; I itself if I : g is
/// I, which leaves I as it was; else a new ideal with the reduced Gröbner
/// basis of I : g in the easy order of I, its easy basis (and I keeps its
/// own).
fn colon(iv: &Value, g: &Elem) -> RResult<Value> {
    let (pst, id) = operand(iv).expect("a polynomial ring or ideal");
    let Some(id) = id else { return Ok(iv.clone()) };
    if g.mpoly_len() == 0 {
        return Ok(Value::Struct(pst));
    }
    if is_constant(g) {
        return Ok(iv.clone());
    }
    let r = id.poly_ring();
    let (base, n, _) = shape(r);
    let (kind, order) = id.easy_order();
    // The intersection of I and (g) is g (I : g).
    let mut quotients = Vec::new();
    for t in intersection(r, &order, &id.basis(), std::slice::from_ref(g))? {
        let q = fm::divides(&Elem::mpoly_from_terms(&r.ctx, &t)?, g)?.expect("a multiple of g");
        quotients.push(terms(&q));
    }
    let quotients = engine(r, gb::groebner(base, n, &order, &quotients))?;
    let easy = id.find_easy()?;
    if same_terms(&quotients, &easy.terms) {
        return Ok(iv.clone());
    }
    id.keep_easy(&easy)?;
    // The basis is monic in the ring's order.
    let basis = elements(r, &quotients)?.into_iter().map(|f| monic(r, f)).collect::<RResult<_>>()?;
    let colon = MPolIdeal::new(pst.clone(), basis, false);
    {
        let mut k = colon.known.borrow_mut();
        k.homogeneous = Some(homogeneous_terms(r, &quotients));
        k.dimension = Some(dimension_class(n, &leading_monomials(&quotients)));
        k.easy = Some(Rc::new(Easy { kind, order, terms: quotients }));
    }
    Ok(Value::structure(StructKind::MPolIdeal(Rc::new(colon))))
}

/// I : f^∞ by the colons I : f, (I : f) : f and so on until one is the
/// ideal it was taken of: that ideal, and the number of colons that grew.
fn colon_iterated(iv: &Value, f: &Elem) -> RResult<(Value, u64)> {
    let (mut cur, mut s) = (iv.clone(), 0);
    loop {
        let next = colon(&cur, f)?;
        if same_value(&next, &cur) {
            return Ok((cur, s));
        }
        (cur, s) = (next, s + 1);
    }
}

/// The homogenization of the polynomial with the terms `t` for the weights
/// `w`, by a new first variable of weight 1.
fn homogenized(w: &[u64], t: &Terms) -> Terms {
    let d = t.iter().map(|(_, e)| wdeg(w, e)).max().unwrap_or(0);
    t.iter().map(|(c, e)| (c.clone(), std::iter::once((d - wdeg(w, e)) as u64).chain(e.iter().copied()).collect())).collect()
}

/// I : x^∞ for an ideal I (or the ring), the value `iv`, and the variable x
/// with number `i`, by Bayer's method as Magma uses it: the reduced Gröbner
/// basis of I in weighted grevlex with x the least variable, each polynomial
/// divided by the highest power of x that divides it. The weights are the
/// grading if I is homogeneous, else those of its easy order if they make I
/// homogeneous, else I is first homogenized by a new first variable (and
/// the basis dehomogenized). The ideal, I itself if x divides none of the
/// polynomials, and the highest power of x divided out.
fn bayer(iv: &Value, i: usize) -> RResult<(Value, u64)> {
    let (pst, id) = operand(iv).expect("a polynomial ring or ideal");
    let Some(id) = id else { return Ok((iv.clone(), 0)) };
    let r = id.poly_ring();
    let (base, n, _) = shape(r);
    let grading = super::mpoly::weights(r);
    let basis = id.basis();
    let (gens, w, homogenize) = if homogeneous_basis(r, &basis) {
        (basis.iter().map(terms).collect(), grading, false)
    } else {
        let easy = id.easy()?;
        let homogeneous = id.known.borrow().homogeneous == Some(true);
        match &easy.order {
            _ if homogeneous => (easy.terms.clone(), grading, false),
            Order::GRevLexW(w) => (easy.terms.clone(), w.clone(), !easy.terms.iter().all(|t| homogeneous_in(w, t))),
            Order::GRevLex => (easy.terms.clone(), vec![1; n], true),
            _ => (engine(r, gb::groebner(base, n, &Order::GRevLex, &easy.terms))?, vec![1; n], true),
        }
    };
    let (gens, w, last) = match homogenize {
        true => (gens.iter().map(|t| homogenized(&w, t)).collect(), std::iter::once(1).chain(w).collect::<Vec<_>>(), i + 1),
        false => (gens, w, i),
    };
    let g = engine(r, gb::groebner(base, w.len(), &bayer_order(&w, last), &gens))?;
    let power = |t: &Terms| t.iter().map(|(_, e)| e[last]).min().unwrap_or(0);
    let k = g.iter().map(power).max().unwrap_or(0);
    if k == 0 {
        return Ok((iv.clone(), 0));
    }
    let mut out = Vec::with_capacity(g.len());
    for t in &g {
        let d = power(t);
        let t: Terms = t
            .iter()
            .map(|(c, e)| {
                let mut e = e.clone();
                e[last] -= d;
                if homogenize {
                    e.remove(0);
                }
                (c.clone(), e)
            })
            .collect();
        out.push(Elem::mpoly_from_terms(&r.ctx, &t)?);
    }
    Ok((ideal_value(&pst, out, false), k))
}

/// I : f^∞ for an ideal I (or the ring), the value `iv`, and a polynomial f
/// of its ring, as Magma computes it: by the irreducible factors p of f in
/// increasing order, by Bayer's method for variables and by colons for the
/// others. The ideal (I itself for a constant f), and each factor with the
/// power of it that the saturation took.
fn saturate(it: &mut Interp, iv: &Value, f: &Elem) -> RResult<(Value, Vec<(Elem, u64)>)> {
    if is_constant(f) {
        return Ok((iv.clone(), Vec::new()));
    }
    let (pst, _) = operand(iv).expect("a polynomial ring or ideal");
    let mut ps = Vec::new();
    for (p, _) in fm::factor(f, false)?.1 {
        ps.push(super::mpoly::normalized(it, &Elt { parent: pst.clone(), x: p })?);
    }
    let mut cur = iv.clone();
    let mut powers = Vec::with_capacity(ps.len());
    for p in sort_dedup(it, &pst, ps)? {
        let (next, k) = match variable(&p) {
            Some(i) => bayer(&cur, i)?,
            None => colon_iterated(&cur, &p)?,
        };
        cur = next;
        powers.push((p, k));
    }
    Ok((cur, powers))
}

/// `x in I`: for x coercing into the ring, whether it is in I; a polynomial
/// of another ring is in no ideal.
pub fn ideal_contains(it: &mut Interp, id: &MPolIdeal, x: &Value) -> RResult<bool> {
    let ctx = |e: RuntimeError| e.in_context("in");
    match it.to_ring_elem(&id.ring, x, false)? {
        Some(f) => id.contains_all(&[f]).map_err(ctx),
        None if matches!(x, Value::Elt(e) if matches!(e.ring().kind, RingKind::MPoly { .. })) => Ok(false),
        None => Err(RuntimeError::runtime("Bad argument types").in_context("in")),
    }
}

/// `ChangeRing(I, S)`: the ideal of Q, the ring of I over S, generated by
/// the generators of I with their coefficients coerced into S.
pub fn change_ring(it: &mut Interp, id: &MPolIdeal, q: &Value) -> RResult<Value> {
    let Some((qst, _)) = ring_of(q) else { unreachable!("a polynomial ring") };
    let qst = qst.clone();
    let mut gens = Vec::with_capacity(id.gens.len());
    for g in &id.gens {
        match it.to_ring_elem(&qst, &make_elt(&id.ring, g.clone()), true)? {
            Some(x) => gens.push(x),
            None => return Err(RuntimeError::runtime("Cannot coerce element from source coefficent ring into the destination coefficient ring")),
        }
    }
    Ok(ideal_value(&qst, gens, false))
}

/// Whether the basis elements are homogeneous in the grading of the ring.
fn homogeneous_basis(r: &Ring, gens: &[Elem]) -> bool {
    gens.iter().all(|g| super::mpoly::homogeneous(r, g))
}

// ----- printing --------------------------------------------------------------------

/// A basis, one element per line between brackets.
fn fmt_basis(it: &mut Interp, p: &mut Printer, ring: &Rc<Struct>, gens: &[Elem], indent: usize) -> RResult<()> {
    p.newline(indent);
    p.write("[");
    let saved = p.cont;
    p.cont = indent + 4;
    for (i, g) in gens.iter().enumerate() {
        p.newline(indent + 4);
        it.fmt(p, &make_elt(ring, g.clone()), indent + 4)?;
        if i + 1 < gens.len() {
            p.write(",");
        }
    }
    p.cont = saved;
    p.newline(indent);
    p.write("]");
    Ok(())
}

/// Print an ideal: at the Magma level `ideal<P | ...>` with an element of
/// the basis per line, at the minimal level `Ideal of P`, and otherwise the
/// ring, the fixed basis, what is known of the ideal and the basis.
pub fn fmt_ideal(it: &mut Interp, p: &mut Printer, id: &MPolIdeal, indent: usize) -> RResult<()> {
    let r = id.poly_ring().clone();
    let basis = id.basis();
    if p.level == Level::Magma {
        let ring = it.format_ring(&r, Level::Magma)?.join("\n");
        p.write(&format!("ideal<{ring} |"));
        for (i, g) in basis.iter().enumerate() {
            p.newline(indent);
            it.fmt(p, &make_elt(&id.ring, g.clone()), indent)?;
            if i + 1 < basis.len() {
                p.write(",");
            }
        }
        p.newline(indent);
        p.write(">");
        return Ok(());
    }
    let minimal = p.level == Level::Minimal;
    let lines = it.format_ring(&r, if minimal { Level::Minimal } else { Level::Default })?;
    p.write("Ideal of ");
    for (i, line) in lines.iter().enumerate() {
        if i > 0 {
            p.newline(indent);
        }
        p.write(line);
    }
    if minimal {
        return Ok(());
    }
    if id.fixed {
        p.newline(indent);
        p.write("Fixed basis:");
        fmt_basis(it, p, &id.ring, &id.gens, indent)?;
    }
    if let Some(h) = id.header() {
        p.newline(indent);
        p.write(&h);
    }
    p.newline(indent);
    p.write(if id.has_groebner() { "Groebner basis:" } else { "Basis:" });
    fmt_basis(it, p, &id.ring, &basis, indent)
}

// ----- intrinsics ------------------------------------------------------------------

/// `Ideal(B)` and `IdealWithFixedBasis(B)` for a set or sequence B of
/// polynomials.
fn ideal_of(a: &CallArgs, fixed: bool) -> RResult<Vals> {
    let (universe, elems): (Option<Value>, Vec<Value>) = match &a.args[0] {
        Value::Seq(s) => (s.universe.clone(), s.elems.clone()),
        Value::Set(s) => (s.universe.clone(), s.iter().collect()),
        _ => unreachable!("a set or sequence"),
    };
    let Some((pst, _)) = universe.as_ref().and_then(ring_of) else { return Err(RuntimeError::runtime("Illegal null sequence")) };
    let gens = elems.iter().map(|v| match v {
        Value::Elt(e) => e.x.clone(),
        _ => unreachable!("a polynomial"),
    });
    one(ideal_value(pst, gens.collect(), fixed))
}

fn ideal_from(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    ideal_of(a, false)
}

fn ideal_with_fixed_basis(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    ideal_of(a, true)
}

fn principal_ideal(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let Value::Elt(f) = &a.args[0] else { unreachable!("a polynomial") };
    one(ideal_value(&f.parent, vec![f.x.clone()], false))
}

fn basis(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (pst, gens) = ideal_arg(a, 0);
    let elems = gens.into_iter().map(|g| make_elt(&pst, g)).collect();
    one(Value::seq(Some(Value::Struct(pst)), elems))
}

fn basis_element(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (pst, gens) = ideal_arg(a, 0);
    let (k, n) = (a.int(1)?, gens.len());
    match k.to_u64().filter(|&k| k >= 1 && k as usize <= n) {
        Some(i) => one(make_elt(&pst, gens[i as usize - 1].clone())),
        None => Err(RuntimeError::runtime(format!("Argument 2 ({k}) should be in the range [1 .. {n}]"))),
    }
}

fn generic(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(Value::Struct(ideal_arg(a, 0).0))
}

fn is_zero(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(ideal_arg(a, 0).1.iter().all(|g| g.mpoly_len() == 0))
}

/// `IsHomogeneous(I)`: true when the basis is homogeneous, else decided by
/// the easy Gröbner basis.
fn is_homogeneous(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (pst, id) = operand_arg(a, 0);
    let StructKind::Ring(r) = &pst.kind else { unreachable!("a polynomial ring") };
    match id {
        Some(id) if !homogeneous_basis(r, &id.basis()) => boolv(id.homogeneous()?),
        _ => boolv(true),
    }
}

fn is_proper(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    match operand_arg(a, 0).1 {
        Some(id) => boolv(id.dimension()? != Dim::Unit),
        None => boolv(false),
    }
}

fn is_zero_dimensional(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    match operand_arg(a, 0).1 {
        Some(id) => boolv(id.dimension()? == Dim::Exactly(0)),
        None => boolv(false),
    }
}

/// `Dimension(I)`: the dimension and a maximally independent set of
/// variables (-1 and nothing for the whole ring).
fn dimension(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let whole = || Ok(vals![Value::int(-1), Value::Undef]);
    let Some(id) = operand_arg(a, 0).1 else { return whole() };
    let easy = id.easy()?;
    if id.dimension()? == Dim::Unit {
        return whole();
    }
    let u = independent_set(id.poly_ring().ngens(), &leading_monomials(&easy.terms));
    id.known.borrow_mut().dimension = Some(Dim::Exactly(u.len()));
    Ok(vals![Value::int(u.len() as i64), Value::int_seq(u.iter().map(|&i| Integer::from_u64(i as u64 + 1)))])
}

/// `QuotientDimension(I)`: the dimension of P/I over the coefficient field
/// (Infinity unless I is zero-dimensional).
fn quotient_dimension(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let Some(id) = operand_arg(a, 0).1 else { return one(Value::int(0)) };
    let easy = id.easy()?;
    one(match id.dimension()? {
        Dim::Unit => Value::int(0),
        Dim::Exactly(0) => Value::Int(standard_monomials(id.poly_ring().ngens(), &leading_monomials(&easy.terms))),
        _ => Value::Infinity(true),
    })
}

/// `IsPrincipal(I)`: whether I has a Gröbner basis of one element, and the
/// element.
fn is_principal(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (pst, id) = operand_arg(a, 0);
    let Some(id) = id else { return Ok(vals![Value::Bool(true), make_elt(&pst, unit(&pst)?)]) };
    let easy = id.easy()?;
    let r = id.poly_ring();
    match elements(r, &easy.terms)?.as_slice() {
        [] => Ok(vals![Value::Bool(true), make_elt(&pst, Elem::zero(&r.ctx))]),
        [f] => Ok(vals![Value::Bool(true), make_elt(&pst, monic(r, f.clone())?)]),
        _ => Ok(vals![Value::Bool(false), Value::Undef]),
    }
}

/// `LeadingMonomialIdeal(I)`: the ideal of the leading monomials of the
/// Gröbner basis of I.
fn leading_monomial_ideal(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (pst, id) = operand_arg(a, 0);
    let Some(id) = id else { return one(ideal_value(&pst, vec![unit(&pst)?], false)) };
    let r = id.poly_ring();
    let one_c = Elem::one(r.ctx.base().expect("a polynomial ring"))?;
    let mut lms = Vec::new();
    for g in id.groebner()?.iter() {
        let (_, e) = leading(r, g).expect("a non-zero element of a Gröbner basis");
        lms.push(Elem::mpoly_from_terms(&r.ctx, &[(one_c.clone(), e)])?);
    }
    one(ideal_value(&pst, lms, false))
}

fn has_grevlex_order(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (pst, _) = operand_arg(a, 0);
    let StructKind::Ring(r) = &pst.kind else { unreachable!("a polynomial ring") };
    boolv(matches!(shape(r).2, Order::GRevLex))
}

/// `IsInRadical(f, I)`: whether some power of f is in I.
fn is_in_radical(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (pst, gens) = ideal_arg(a, 1);
    let Some(f) = it.to_ring_elem(&pst, &a.args[0], false)? else { return Err(RuntimeError::runtime("Arguments are not compatible")) };
    let StructKind::Ring(r) = &pst.kind else { unreachable!("a polynomial ring") };
    boolv(in_radical(r, &f, &gens)?)
}

/// `JacobianIdeal(f)`: the ideal generated by the partial derivatives of f,
/// and its inclusion into the ring (as the ideal constructor returns them).
fn jacobian_ideal(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let Value::Elt(f) = &a.args[0] else { unreachable!("a polynomial") };
    let r = f.ring();
    let mut gens = Vec::with_capacity(r.ngens());
    for i in 0..r.ngens() {
        let mut ts = Vec::new();
        for (c, mut e) in terms(&f.x) {
            if e[i] > 0 {
                let c = c.mul_integer(&Integer::from_u64(e[i]))?;
                e[i] -= 1;
                ts.push((c, e));
            }
        }
        gens.push(Elem::mpoly_from_terms(&r.ctx, &ts)?);
    }
    let ideal = ideal_value(&f.parent, gens, false);
    Ok(vals![ideal.clone(), coercion_map(ideal, Value::Struct(f.parent.clone()))])
}

/// Argument `i`, a polynomial, in the ring `pst` of the ideal argument.
fn element_arg(it: &mut Interp, a: &CallArgs, pst: &Rc<Struct>, i: usize) -> RResult<Elem> {
    it.to_ring_elem(pst, &a.args[i], false)?.ok_or_else(|| RuntimeError::runtime("Arguments are not compatible"))
}

/// The fold by `meet` of the ideals `ks`, the ring for none.
fn meet_all(pst: &Rc<Struct>, ks: impl Iterator<Item = RResult<Value>>) -> RResult<Value> {
    let mut out: Option<Value> = None;
    for k in ks {
        let k = k?;
        out = Some(match out {
            Some(m) => meet(&m, &k)?,
            None => k,
        });
    }
    Ok(out.unwrap_or_else(|| Value::Struct(pst.clone())))
}

/// `ColonIdeal(I, J)`: the intersection of the colons I : g for g in the
/// reduced Gröbner basis of J (which J keeps).
fn colon_ideal(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let ((r, x), (s, y)) = (operand_arg(a, 0), operand_arg(a, 1));
    if !struct_eq(&r, &s) {
        return Err(RuntimeError::runtime(format!("Arguments are not compatible\nArgument types given: {}, {}", it.type_name_ext(&a.args[0]), it.type_name_ext(&a.args[1]))));
    }
    let (Some(_), Some(y)) = (x, y) else { return one(a.args[0].clone()) };
    let g = y.groebner()?;
    one(meet_all(&r, g.iter().map(|g| colon(&a.args[0], g)))?)
}

/// `ColonIdeal(I, f)`: the saturation I : f^∞, and if asked for, the least
/// s with I : f^s = I : f^∞ (which the colons then find).
fn colon_element(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (pst, _) = operand_arg(a, 0);
    let f = element_arg(it, a, &pst, 1)?;
    if a.nresults >= 2 {
        let (c, s) = colon_iterated(&a.args[0], &f)?;
        return Ok(vals![c, Value::int(s as i64)]);
    }
    one(saturate(it, &a.args[0], &f)?.0)
}

/// `ColonIdealEquivalent(I, f)`: the saturation I : f^∞ and a product g of
/// powers of the irreducible factors of f with I : g = I : f^∞ (only the
/// saturation unless both are asked for).
fn colon_ideal_equivalent(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (pst, _) = operand_arg(a, 0);
    let f = element_arg(it, a, &pst, 1)?;
    let (c, powers) = saturate(it, &a.args[0], &f)?;
    if a.nresults < 2 {
        return one(c);
    }
    if f.mpoly_len() == 0 {
        return Ok(vals![c, make_elt(&pst, f)]);
    }
    let mut g = unit(&pst)?;
    for (p, k) in powers {
        g = g.mul(&p.pow(&Integer::from_u64(k))?)?;
    }
    Ok(vals![c, make_elt(&pst, g)])
}

/// `Saturation(I, J)`: the intersection of the saturations I : g^∞ for the
/// non-zero g in the basis of J.
fn saturation_by(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let ((r, x), (s, y)) = (operand_arg(a, 0), operand_arg(a, 1));
    if !struct_eq(&r, &s) {
        return Err(super::bare(RuntimeError::runtime("I and J must be ideals of the same ring")));
    }
    let (Some(_), Some(y)) = (x, y) else { return one(a.args[0].clone()) };
    let iv = a.args[0].clone();
    let basis: Vec<Elem> = y.basis().into_iter().filter(|g| g.mpoly_len() > 0).collect();
    one(meet_all(&r, basis.iter().map(|g| Ok(saturate(it, &iv, g)?.0)))?)
}

/// `Saturation(I)`: the saturation by the ideal of the variables, the
/// intersection of the saturations by each (by Bayer's method).
fn saturation(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (r, x) = operand_arg(a, 0);
    let Some(x) = x else { return one(a.args[0].clone()) };
    one(meet_all(&r, (0..x.poly_ring().ngens()).map(|i| Ok(bayer(&a.args[0], i)?.0)))?)
}

pub fn register(it: &mut Interp) {
    it.def("Ideal", "B::[RngMPolElt] -> RngMPol", "The ideal generated by the polynomials B, with basis B.", ideal_from);
    it.def("Ideal", "B::{RngMPolElt} -> RngMPol", "The ideal generated by the polynomials B, with basis B.", ideal_from);
    it.def("Ideal", "f::RngMPolElt -> RngMPol", "The principal ideal generated by f.", principal_ideal);
    it.def("IdealWithFixedBasis", "B::[RngMPolElt] -> RngMPol", "The ideal generated by the polynomials B, with the fixed basis B.", ideal_with_fixed_basis);
    for name in ["Basis", "Generators"] {
        it.def(name, "I::RngMPol -> [RngMPolElt]", "The basis of the ideal I.", basis);
    }
    it.def("BasisElement", "I::RngMPol, i::RngIntElt -> RngMPolElt", "The i-th element of the basis of the ideal I.", basis_element);
    it.def("Generic", "I::RngMPol -> RngMPol", "The polynomial ring of the ideal I.", generic);
    it.def("IsZero", "I::RngMPol -> BoolElt", "Whether I is the zero ideal.", is_zero);
    it.def("IsHomogeneous", "I::RngMPol -> BoolElt", "Whether the ideal I is homogeneous in the grading of its ring.", is_homogeneous);
    it.def("IsProper", "I::RngMPol -> BoolElt", "Whether the ideal I is not the whole ring.", is_proper);
    it.def("IsZeroDimensional", "I::RngMPol -> BoolElt", "Whether the ideal I has dimension 0.", is_zero_dimensional);
    let doc = "The dimension of the ideal I and a maximally independent set of variables modulo I (-1 for the whole ring).";
    it.def("Dimension", "I::RngMPol -> RngIntElt, [RngIntElt]", doc, dimension);
    let doc = "The dimension of P/I over the coefficient field of the ring P of the ideal I (Infinity unless I is zero-dimensional).";
    it.def("QuotientDimension", "I::RngMPol -> RngIntElt", doc, quotient_dimension);
    it.def("IsPrincipal", "I::RngMPol -> BoolElt, RngMPolElt", "Whether the ideal I is principal, and a generator.", is_principal);
    let doc = "The ideal generated by the leading monomials of the Gröbner basis of the ideal I.";
    it.def("LeadingMonomialIdeal", "I::RngMPol -> RngMPol", doc, leading_monomial_ideal);
    it.def("HasGrevlexOrder", "I::RngMPol -> BoolElt", "Whether the monomial order of the ideal I is grevlex.", has_grevlex_order);
    it.def("IsInRadical", "f::RngMPolElt, I::RngMPol -> BoolElt", "Whether f is in the radical of the ideal I.", is_in_radical);
    it.def("JacobianIdeal", "f::RngMPolElt -> RngMPol, Map", "The ideal generated by the partial derivatives of f, and its inclusion.", jacobian_ideal);
    for name in ["ColonIdeal", "IdealQuotient"] {
        it.def(name, "I::RngMPol, J::RngMPol -> RngMPol", "The colon ideal I : J of the polynomials f with f J in I.", colon_ideal);
        let doc = "The saturation I : f^∞ of the ideal I, and if asked for, the least s with I : f^s = I : f^∞.";
        it.def(name, "I::RngMPol, f::RngMPolElt -> RngMPol, RngIntElt", doc, colon_element);
    }
    for name in ["ColonIdealEquivalent", "Saturation"] {
        let doc = "The saturation I : f^∞ of the ideal I and a product g of powers of the factors of f with I : g = I : f^∞.";
        it.def(name, "I::RngMPol, f::RngMPolElt -> RngMPol, RngMPolElt", doc, colon_ideal_equivalent);
    }
    it.def("Saturation", "I::RngMPol, J::RngMPol -> RngMPol", "The saturation I : J^∞ of the ideal I by the ideal J.", saturation_by);
    it.def("Saturation", "I::RngMPol -> RngMPol", "The saturation of the ideal I by the ideal of the variables.", saturation);
    elimination::register(it);
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The exponents of the terms of the polynomials in `s` (coefficients
    /// ignored), in the variables `vars`: "x^2 + y, x*y - 1".
    fn polys(vars: &str, s: &str) -> Vec<Vec<Vec<u64>>> {
        let exps = |m: &str| {
            let mut e = vec![0; vars.len()];
            for f in m.split('*').map(str::trim).filter(|f| f.chars().all(|c| c.is_ascii_alphabetic() || c == '^' || c.is_ascii_digit())) {
                let (v, k) = f.split_once('^').unwrap_or((f, "1"));
                if let Some(i) = vars.find(v).filter(|_| v.len() == 1) {
                    e[i] += k.parse::<u64>().unwrap();
                }
            }
            e
        };
        s.split(',').map(|p| p.replace('-', "+").split('+').map(str::trim).filter(|t| !t.is_empty()).map(exps).collect()).collect()
    }

    #[test]
    fn weights_as_magma_finds_them() {
        // The weights of Magma 2.22's easy orders (EasyIdeal), except that
        // for x^2 - y*z^3, x*y Magma finds none (and uses grevlex) where
        // [2, 1, 1] would do.
        let cases: &[(&str, &str, Option<&[u64]>)] = &[
            ("xyz", "x^2 + y, x*y - z", Some(&[1, 2, 3])),
            ("xyz", "x^3 - y, y^2 - z, x*z - 1", Some(&[1, 3, 6])),
            ("xyz", "x*y - 1, x^2 + y^2 - 4", Some(&[1, 1, 1])),
            ("xyz", "x^2 + y, y^2 + z, z^2 + x", None),
            ("xyz", "x^2 + y, x^3 + y^2", None),
            ("xyz", "x*y - z^2, x^3 - y", Some(&[1, 3, 2])),
            ("xyz", "x^2 + y, x*y", Some(&[1, 2, 1])),
            ("xyz", "x + y^2, x*y", Some(&[2, 1, 1])),
            ("xyz", "x*y + z, x^2", Some(&[1, 1, 2])),
            ("xyz", "x^2*y + z^3, x*y", Some(&[1, 1, 1])),
            ("xyz", "x^2 + x, x*y", None),
            ("xyz", "x^6 + y^4, x*y", Some(&[2, 3, 1])),
            ("xyz", "x^2*z + y^3, x*y", Some(&[1, 1, 1])),
            ("xyz", "x + y^2 + z^3, x*y", Some(&[6, 3, 2])),
            ("xyz", "x^2 + y^2 + z, x*y", Some(&[1, 1, 2])),
            ("xyz", "x + y + z^2, x*y", Some(&[2, 2, 1])),
            ("xyz", "x^2 + y + z, x*y", Some(&[1, 2, 2])),
            ("xyz", "x^2 - y, x*y - 1", Some(&[1, 2, 1])),
            ("xyz", "x*y + z, x*z", Some(&[1, 1, 2])),
            ("xyz", "x*y + z^2, x*z", Some(&[1, 1, 1])),
            ("xyz", "x^2 + y*z, x*y", Some(&[1, 1, 1])),
            ("xyz", "x^3 + y*z, x*y", Some(&[1, 1, 2])),
            ("xyz", "x^3 + y*z, x*y, x + z^5", Some(&[5, 14, 1])),
            ("xyz", "x^2 + y, x*y, y^2 + z^3", Some(&[3, 6, 4])),
            ("xyz", "x^4 + y, x^2*y", Some(&[1, 4, 1])),
            ("xyz", "x^2 + y, x*y + 1", Some(&[1, 2, 1])),
            ("xyz", "x - y*z, x*y", Some(&[2, 1, 1])),
            ("xyz", "y - x*z, x*y", Some(&[1, 2, 1])),
            ("xyz", "x*y - z^3, x^2", Some(&[1, 2, 1])),
            ("xyz", "x^5 - y*z, x*y", Some(&[1, 2, 3])),
            ("xyz", "z - x*y^2, x*z", Some(&[1, 1, 3])),
            ("xyz", "x^3 - y^2*z, x*y", Some(&[1, 1, 1])),
            ("xyz", "x^2*y - z, x*z", Some(&[1, 1, 3])),
            ("xyz", "y^3 - x*z^2, x*y", Some(&[1, 1, 1])),
            ("xyz", "x - y^2*z^2, x*y", Some(&[4, 1, 1])),
            ("xyz", "z^3 - x*y, x^2", Some(&[1, 2, 1])),
            ("xyz", "x^2 + y^3 + z^6, x*z", Some(&[3, 2, 1])),
            ("abcd", "a*b - c, a*d", Some(&[1, 1, 2, 1])),
            ("abcd", "a - b*c, a*d", Some(&[2, 1, 1, 1])),
            ("abcd", "a^2 - b, c^3 - d, a*c", Some(&[1, 2, 1, 3])),
            ("abcd", "a*b - c*d, a^2 - d, a*c", Some(&[1, 2, 1, 2])),
            ("abcd", "a^2 - b*c*d, a*b", Some(&[2, 1, 1, 2])),
            ("abcd", "a - b, c^2 - d, a*c", Some(&[1, 1, 1, 2])),
            ("abcd", "a^3 - b*c, d^2 - a, a*b", Some(&[2, 3, 3, 1])),
        ];
        for (vars, s, w) in cases {
            assert_eq!(homogeneous_weights(vars.len(), &polys(vars, s)).as_deref(), *w, "{s}");
        }
    }

    #[test]
    fn dimensions_as_magma_finds_them() {
        // Dimension(Ideal(...)) in Magma 2.22: the dimension is the size of
        // the set of variables (numbered from 0 here).
        let cases: &[(&str, &[usize])] = &[
            ("x*y", &[1, 2]),
            ("y*z", &[0, 2]),
            ("x*z", &[1, 2]),
            ("x*y*z", &[1, 2]),
            ("x^2*y", &[1, 2]),
            ("y^2, x*z", &[2]),
            ("x*y, z^2", &[1]),
            ("x*z, y*z", &[0, 1]),
            ("x*y, y*z", &[0, 2]),
            ("x - 1, y, z", &[]),
        ];
        for (s, u) in cases {
            let lms: Vec<Vec<u64>> = polys("xyz", s).into_iter().map(|p| p[0].clone()).collect();
            let lms: Vec<&[u64]> = lms.iter().map(|e| e.as_slice()).collect();
            assert_eq!(independent_set(3, &lms), *u, "{s}");
        }
        assert_eq!(independent_set(3, &[]), [0, 1, 2]);
        let lms: [&[u64]; 3] = [&[2, 0, 0], &[0, 1, 0], &[0, 0, 3]];
        assert!(dimension_class(3, &lms) == Dim::Exactly(0));
        assert_eq!(standard_monomials(3, &lms), Integer::from_u64(6));
        let lms: [&[u64]; 2] = [&[2, 0, 0], &[1, 1, 0]];
        assert!(dimension_class(3, &lms) == Dim::Positive);
        assert!(dimension_class(3, &[&[0, 0, 0]]) == Dim::Unit);
    }
}
