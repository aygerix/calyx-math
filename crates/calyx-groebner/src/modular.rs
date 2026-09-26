//! Gröbner bases over the rationals by the modular method, Magma's default:
//! the reduced basis is computed modulo primes below 2^31, where F4 and FGLM
//! run in words, and its coefficients are recovered by Chinese remaindering
//! and rational reconstruction. F4 runs in full on one prime, traced, and is
//! replayed on the others. A lex basis in shape position is lifted through
//! its rational univariate representation, whose coefficients are far
//! smaller (see `rur`).
//!
//! For all but finitely many primes the basis modulo p is the reduction of
//! the basis over the rationals. The few others show other leading
//! monomials, so the bases are grouped by their leading monomials and the
//! largest group is lifted. As in Magma, the result is not proven: it is
//! accepted once it reduces to the basis modulo one more prime (Monte
//! Carlo). `Strategy::rational` computes over the rationals throughout.

use std::cmp::Ordering;
use std::rc::Rc;

use calyx_flint::gr::{Ctx, Elem};
use calyx_flint::{Crt, Integer, Rational, nmod_poly};

use crate::field::{Field, Zp};
use crate::order::Order;
use crate::poly::{Poly, Ring};
use crate::{Error, Terms, buchberger, f4, fglm, graded};

/// The most primes tried before the rationals are used throughout, a bound
/// against runaway: the coefficients would have about a million bits.
const MAX_PRIMES: usize = 1 << 15;

/// A polynomial over the rationals: integer coefficients over a common
/// denominator, and n exponents a term, in decreasing order for the order
/// it is used in.
struct QPoly {
    num: Vec<Integer>,
    den: Integer,
    e: Vec<u32>,
}

impl QPoly {
    fn new(t: &Terms, ring: &Ring) -> Result<QPoly, Error> {
        let mut terms = Vec::with_capacity(t.len());
        for (c, x) in t {
            let e = x.iter().map(|&x| u32::try_from(x).map_err(|_| Error::ExponentTooLarge)).collect::<Result<Vec<u32>, Error>>()?;
            terms.push((c.to_rational().map_err(|_| Error::Unsupported)?, e));
        }
        terms.sort_by(|a, b| ring.cmp(&b.1, &a.1));
        let mut merged: Vec<(Rational, Vec<u32>)> = Vec::with_capacity(terms.len());
        for (c, e) in terms {
            match merged.last_mut() {
                Some((d, f)) if *f == e => *d = &*d + &c,
                _ => merged.push((c, e)),
            }
        }
        merged.retain(|(c, _)| !c.is_zero());
        let den = merged.iter().fold(Integer::one(), |d, (c, _)| d.lcm(&c.denominator()));
        let num = merged.iter().map(|(c, _)| &c.numerator() * &den.divexact(&c.denominator())).collect();
        Ok(QPoly { num, den, e: merged.into_iter().flat_map(|(_, e)| e).collect() })
    }

    /// The polynomial modulo p; None if p divides the denominator or the
    /// leading coefficient.
    fn modulo(&self, f: &Zp, n: usize) -> Option<Poly<u64>> {
        let p = f.modulus();
        let d = self.den.mod_u64(p);
        if d == 0 || self.num[0].mod_u64(p) == 0 {
            return None;
        }
        let u = f.inv(&d);
        let mut g = Poly { c: Vec::with_capacity(self.num.len()), e: Vec::with_capacity(self.e.len()) };
        for (a, e) in self.num.iter().zip(self.e.chunks(n)) {
            let c = f.mul(&a.mod_u64(p), &u);
            if c != 0 {
                g.c.push(c);
                g.e.extend_from_slice(e);
            }
        }
        Some(g)
    }
}

fn qpolys(ts: &[Terms], ring: &Ring) -> Result<Vec<QPoly>, Error> {
    let mut out = Vec::with_capacity(ts.len());
    for t in ts {
        let q = QPoly::new(t, ring)?;
        if !q.num.is_empty() {
            out.push(q);
        }
    }
    Ok(out)
}

/// The reduced Gröbner basis in the order of `ring` of the ideal generated
/// by `gens`, polynomials over the rationals `q`; None if the modular method
/// gives up.
pub(crate) fn groebner(q: &Rc<Ctx>, ring: &Ring, gens: &[Terms]) -> Result<Option<Vec<Terms>>, Error> {
    if graded(&ring.order) {
        // F4 takes the pairs by weighted degree for a grevlexw order.
        let weights = match &ring.order {
            Order::GRevLexW(w) => w.clone(),
            _ => vec![1; ring.n],
        };
        let mut trace = None;
        return basis(q, ring, gens, |f, polys, check| traced(&mut trace, f, ring, polys, &weights, check));
    }
    // As Magma does, in an order that is not graded the basis is lifted in
    // grevlex and changed to the order.
    let grevlex = Ring { n: ring.n, order: Order::GRevLex };
    let Some(g) = groebner(q, &grevlex, gens)? else { return Ok(None) };
    change_order(q, &grevlex, &g, ring)
}

/// The reduced Gröbner basis in the order of `to` of the ideal whose reduced
/// Gröbner basis in the order of `from` is `gb`; None if the modular method
/// gives up. For a zero-dimensional ideal the primes take FGLM, which needs
/// no F4, and a lex basis in shape position is lifted through its rational
/// univariate representation (see `rur`); for others, Buchberger's algorithm
/// in the order.
pub(crate) fn change_order(q: &Rc<Ctx>, from: &Ring, gb: &[Terms], to: &Ring) -> Result<Option<Vec<Terms>>, Error> {
    let polys = qpolys(gb, from)?;
    if !zero_dimensional(&polys, from.n) {
        return basis(q, to, gb, |f, polys, _| Step::Basis(buchberger::groebner(f, to, polys, None)));
    }
    let modulo = |f: &Zp| polys.iter().map(|g| g.modulo(f, from.n)).collect::<Option<Vec<_>>>();
    if matches!(to.order, Order::Lex) && to.n >= 2 {
        if let Ok(b) = rur(to, |f| modulo(f).map(|gb| fglm::fglm(f, from, &gb, to).unwrap_or_default())) {
            return b.map(|b| export(q, &b)).transpose();
        }
    }
    lift(q, to, |f, _| match modulo(f) {
        Some(polys) => fglm::fglm(f, from, &polys, to).map_or(Step::Fails, Step::Basis),
        None => Step::Bad,
    })
}

/// The lex basis over the rationals of a zero-dimensional ideal in shape
/// position, x_i + r_i(x_n) for i < n and f(x_n) with f squarefree, whose
/// lex bases modulo primes `lex` gives (None for a bad prime). It is lifted
/// through its rational univariate representation, f and the h_i = r_i f'
/// mod f, whose coefficients are far smaller than those of the r_i. With f
/// and the h_i known, the r_i modulo a prime are h_i / f' mod f, which takes
/// no FGLM, and they are lifted in turn. None if the modular method gives
/// up; Err if a prime shows the ideal is not in shape position, or the
/// first one that f is not squarefree.
fn rur(to: &Ring, lex: impl Fn(&Zp) -> Option<Vec<Poly<u64>>>) -> Result<Option<Vec<QTerms>>, ()> {
    let n = to.n;
    let (mut shape, mut first) = (true, true);
    let rep = lifted(to, |f, _| {
        let Some(g) = lex(f) else { return Step::Bad };
        let Some((m, r)) = in_shape(&g, n) else {
            shape = false;
            return Step::Fails;
        };
        let p = f.modulus();
        let dm = derivative(f, &m);
        if std::mem::take(&mut first) && nmod_poly::invmod(&dm, &m, p).is_none() {
            shape = false;
            return Step::Fails;
        }
        // Each h_i with the term x_n^D, so that all have the leading
        // monomial of f.
        let h = r.iter().map(|r| {
            let mut h = nmod_poly::mulmod(r, &dm, &m, p);
            h.push(1);
            univariate(&h, n)
        });
        Step::Basis(std::iter::once(univariate(&m, n)).chain(h).collect())
    });
    let Some(rep) = rep else { return if shape { Ok(None) } else { Err(()) } };
    let d = rep[0][0].0[n - 1] as usize;
    let f = Dense::new(&rep[0], d + 1, n);
    let h: Vec<Dense> = rep[1..].iter().map(|t| Dense::new(t, d, n)).collect();
    Ok(lifted(to, |fp, _| {
        let (Some(m), Some(h)) = (f.modulo(fp), h.iter().map(|h| h.modulo(fp)).collect::<Option<Vec<_>>>()) else { return Step::Bad };
        let p = fp.modulus();
        match nmod_poly::invmod(&derivative(fp, &m), &m, p) {
            Some(s) => Step::Basis(shaped(&m, h.iter().map(|h| nmod_poly::mulmod(h, &s, &m, p)), n)),
            None => Step::Bad,
        }
    }))
}

/// The lex basis `g` modulo p as f and the r_i if it is in shape position,
/// x_i + r_i(x_n) for i < n and f(x_n) with f of positive degree D, dense
/// from the constant term up: D + 1 coefficients for f, D for each r_i.
fn in_shape(g: &[Poly<u64>], n: usize) -> Option<(Vec<u64>, Vec<Vec<u64>>)> {
    let lm_is = |p: &Poly<u64>, i: usize, k: u32| p.lm(n).iter().enumerate().all(|(j, &x)| x == if j == i { k } else { 0 });
    let d = g.last()?.lm(n)[n - 1];
    if g.len() != n || d == 0 || !lm_is(&g[n - 1], n - 1, d) || !(0..n - 1).all(|i| lm_is(&g[i], i, 1)) {
        return None;
    }
    // The other terms are in the staircase, the powers of x_n below D.
    let dense = |p: &Poly<u64>, skip: usize, len: usize| {
        let mut v = vec![0; len];
        (skip..p.len()).for_each(|j| v[p.exp(j, n)[n - 1] as usize] = p.c[j]);
        v
    };
    Some((dense(&g[n - 1], 0, d as usize + 1), g[..n - 1].iter().map(|p| dense(p, 1, d as usize)).collect()))
}

/// The lex basis in shape position with f = `m` and the r_i (see
/// `in_shape`).
fn shaped(m: &[u64], r: impl Iterator<Item = Vec<u64>>, n: usize) -> Vec<Poly<u64>> {
    let mut out: Vec<Poly<u64>> = r
        .enumerate()
        .map(|(i, r)| {
            let t = univariate(&r, n);
            let mut e = vec![0; n];
            e[i] = 1;
            e.extend(t.e);
            Poly { c: std::iter::once(1).chain(t.c).collect(), e }
        })
        .collect();
    out.push(univariate(m, n));
    out
}

/// The polynomial in the last of n variables with the coefficients `v`,
/// from the constant term up.
fn univariate(v: &[u64], n: usize) -> Poly<u64> {
    let mut p = Poly { c: Vec::new(), e: Vec::new() };
    for (k, &c) in v.iter().enumerate().rev().filter(|&(_, &c)| c != 0) {
        p.c.push(c);
        p.e.resize(p.e.len() + n - 1, 0);
        p.e.push(k as u32);
    }
    p
}

/// The derivative of the polynomial `m` modulo p, dense from the constant
/// term up.
fn derivative(f: &Zp, m: &[u64]) -> Vec<u64> {
    m.iter().enumerate().skip(1).map(|(k, c)| f.mul(&(k as u64 % f.modulus()), c)).collect()
}

/// A polynomial in the last variable over the rationals, dense from the
/// constant term up: integer coefficients over a common denominator.
struct Dense {
    num: Vec<Integer>,
    den: Integer,
}

impl Dense {
    /// The terms of `t` of degree below `len`, in n variables.
    fn new(t: &QTerms, len: usize, n: usize) -> Dense {
        let t: Vec<&(Vec<u32>, Rational)> = t.iter().filter(|(e, _)| (e[n - 1] as usize) < len).collect();
        let den = t.iter().fold(Integer::one(), |d, (_, c)| d.lcm(&c.denominator()));
        let mut num = vec![Integer::zero(); len];
        for (e, c) in t {
            num[e[n - 1] as usize] = &c.numerator() * &den.divexact(&c.denominator());
        }
        Dense { num, den }
    }

    /// The polynomial modulo p; None if p divides the denominator.
    fn modulo(&self, f: &Zp) -> Option<Vec<u64>> {
        let p = f.modulus();
        let d = self.den.mod_u64(p);
        (d != 0).then(|| {
            let u = f.inv(&d);
            self.num.iter().map(|a| f.mul(&a.mod_u64(p), &u)).collect()
        })
    }
}

/// Whether the basis `gb` is that of the unit ideal or of a zero-dimensional
/// one, whose leading monomials include a power of each variable.
fn zero_dimensional(gb: &[QPoly], n: usize) -> bool {
    let lms: Vec<&[u32]> = gb.iter().map(|g| &g.e[..n]).collect();
    let pure = |k: usize| lms.iter().any(|l| l.iter().enumerate().all(|(i, &x)| (x > 0) == (i == k)));
    !gb.is_empty() && (lms.iter().any(|l| l.iter().all(|&x| x == 0)) || (0..n).all(pure))
}

/// The basis in the order of `ring` of the ideal generated by `gens`, whose
/// bases modulo primes `modular` computes from the reductions of `gens` (see
/// `lift` for its last argument).
fn basis(q: &Rc<Ctx>, ring: &Ring, gens: &[Terms], mut modular: impl FnMut(&Zp, Vec<Poly<u64>>, bool) -> Step) -> Result<Option<Vec<Terms>>, Error> {
    let gens = qpolys(gens, ring)?;
    if gens.is_empty() {
        return Ok(Some(Vec::new()));
    }
    lift(q, ring, |f, check| match gens.iter().map(|g| g.modulo(f, ring.n)).collect::<Option<Vec<_>>>() {
        Some(polys) => modular(f, polys, check),
        None => Step::Bad,
    })
}

/// The basis modulo p of the ideal generated by `polys`, by F4: replaying
/// `trace`, the run of an earlier prime, else in full, traced. A prime that
/// checks a candidate (`check`) takes a full run too. The replay leaves out
/// what reduced to zero in the run traced, so a trace from a prime unlucky
/// in that way gives wrong bases, though with the leading monomials of the
/// others: the full run of a check prime shows it, and the lift starts
/// again, with a trace to come from the next prime.
fn traced(trace: &mut Option<f4::Trace>, f: &Zp, ring: &Ring, polys: Vec<Poly<u64>>, weights: &[u64], check: bool) -> Step {
    let replayed = trace.as_ref().and_then(|t| f4::replay(t, f, ring, &polys));
    match replayed {
        Some(g) if !check => Step::Basis(g),
        Some(h) => {
            let g = f4::groebner(f, ring, polys, weights, None);
            if h == g {
                return Step::Basis(g);
            }
            *trace = None;
            Step::Restart(g)
        }
        None => {
            let (g, t) = f4::learn(f, ring, polys, weights);
            *trace = t;
            Step::Basis(g)
        }
    }
}

/// What a computation modulo a prime gives.
enum Step {
    /// The basis modulo p, reduced and sorted.
    Basis(Vec<Poly<u64>>),
    /// Nothing: p divides a denominator or a leading coefficient.
    Bad,
    /// The method does not apply.
    Fails,
    /// The basis modulo p, which shows the bases so far may be wrong.
    Restart(Vec<Poly<u64>>),
}

/// The primes below 2^31, from the largest down.
fn primes() -> impl Iterator<Item = u64> {
    let mut p = 1u64 << 31;
    std::iter::from_fn(move || {
        p -= 1;
        while !Integer::from_u64(p).is_prime() {
            p -= 1;
        }
        Some(p)
    })
}

/// The basis over the rationals `q`, in the order of `ring`, whose
/// reductions modulo primes `step` computes; it is told whether the prime
/// checks a candidate.
fn lift(q: &Rc<Ctx>, ring: &Ring, step: impl FnMut(&Zp, bool) -> Step) -> Result<Option<Vec<Terms>>, Error> {
    lifted(ring, step).map(|c| export(q, &c)).transpose()
}

/// As `lift`, with the rational coefficients.
fn lifted(ring: &Ring, mut step: impl FnMut(&Zp, bool) -> Step) -> Option<Vec<QTerms>> {
    let n = ring.n;
    let mut groups: Vec<Lift> = Vec::new();
    let mut candidate: Option<(Vec<Vec<u32>>, Vec<QTerms>)> = None;
    for p in primes().take(MAX_PRIMES) {
        let ctx = Ctx::residue_ring(&Integer::from_u64(p));
        let f = Zp::new(&ctx);
        let g = match step(&f, candidate.is_some()) {
            Step::Basis(g) => g,
            Step::Restart(g) => {
                groups.clear();
                candidate = None;
                g
            }
            Step::Bad => continue,
            Step::Fails => return None,
        };
        let lms: Vec<Vec<u32>> = g.iter().map(|x| x.lm(n).to_vec()).collect();
        // A prime with the leading monomials of the candidate checks it; one
        // with others is taken for unlucky.
        if let Some((clms, c)) = &candidate {
            if *clms == lms {
                match agrees(c, &g, &f, n) {
                    Some(true) => return candidate.map(|(_, c)| c),
                    Some(false) => candidate = None,
                    None => continue,
                }
            }
        }
        let k = match groups.iter().position(|l| l.lms == lms) {
            Some(k) => k,
            None => {
                groups.push(Lift::new(lms));
                groups.len() - 1
            }
        };
        groups[k].add(&g, p, ring);
        // The largest group is lifted; a candidate from another is dropped.
        let best = (0..groups.len()).max_by_key(|&i| (groups[i].primes.len(), std::cmp::Reverse(i))).expect("a group");
        if best == k && candidate.as_ref().is_none_or(|(l, _)| *l != groups[k].lms) {
            candidate = groups[k].reconstruct().map(|c| (groups[k].lms.clone(), c));
        }
    }
    None
}

/// A polynomial over the rationals: its terms, exponents and coefficient,
/// in decreasing order.
type QTerms = Vec<(Vec<u32>, Rational)>;

/// Whether the basis `c` over the rationals reduces modulo p to `g`; None if
/// p divides one of its denominators.
fn agrees(c: &[QTerms], g: &[Poly<u64>], f: &Zp, n: usize) -> Option<bool> {
    let p = f.modulus();
    if c.len() != g.len() {
        return Some(false);
    }
    for (cp, gp) in c.iter().zip(g) {
        let mut j = 0;
        for (e, x) in cp {
            let d = x.denominator().mod_u64(p);
            if d == 0 {
                return None;
            }
            let y = f.mul(&x.numerator().mod_u64(p), &f.inv(&d));
            if y == 0 {
                continue;
            }
            if j == gp.len() || gp.exp(j, n) != &e[..] || gp.c[j] != y {
                return Some(false);
            }
            j += 1;
        }
        if j != gp.len() {
            return Some(false);
        }
    }
    Some(true)
}

fn export(q: &Rc<Ctx>, c: &[QTerms]) -> Result<Vec<Terms>, Error> {
    let elem = |x: &Rational| Elem::from_rational(q, x).map_err(|_| Error::Unsupported);
    c.iter().map(|p| p.iter().map(|(e, x)| Ok((elem(x)?, e.iter().map(|&k| k as u64).collect()))).collect()).collect()
}

/// The bases modulo primes with the same leading monomials, to combine by
/// Chinese remaindering.
struct Lift {
    lms: Vec<Vec<u32>>,
    primes: Vec<u64>,
    /// The terms of each polynomial, exponents and residues modulo each of
    /// the primes (0 where the term vanishes), in decreasing order.
    polys: Vec<Vec<(Vec<u32>, Vec<u32>)>>,
    /// Where reconstruction failed last: it is tried there first.
    hard: (usize, usize),
    /// How many primes the next reconstruction waits for.
    next: usize,
}

impl Lift {
    fn new(lms: Vec<Vec<u32>>) -> Lift {
        Lift { lms, primes: Vec::new(), polys: Vec::new(), hard: (0, 0), next: 1 }
    }

    /// Add the basis `g` modulo p.
    fn add(&mut self, g: &[Poly<u64>], p: u64, ring: &Ring) {
        let (n, k) = (ring.n, self.primes.len());
        if self.polys.is_empty() {
            self.polys = vec![Vec::new(); g.len()];
        }
        let new = |x: &Poly<u64>, j: usize| {
            let mut r = vec![0; k + 1];
            r[k] = x.c[j] as u32;
            (x.exp(j, n).to_vec(), r)
        };
        for (acc, x) in self.polys.iter_mut().zip(g) {
            let old = std::mem::take(acc);
            let mut merged = Vec::with_capacity(old.len().max(x.len()));
            let mut j = 0;
            for (e, mut r) in old {
                while j < x.len() && ring.cmp(x.exp(j, n), &e) == Ordering::Greater {
                    merged.push(new(x, j));
                    j += 1;
                }
                if j < x.len() && x.exp(j, n) == &e[..] {
                    r.push(x.c[j] as u32);
                    j += 1;
                } else {
                    r.push(0);
                }
                merged.push((e, r));
            }
            merged.extend((j..x.len()).map(|j| new(x, j)));
            *acc = merged;
        }
        self.primes.push(p);
    }

    /// The basis over the rationals whose coefficients are the fractions with
    /// numerator and denominator at most sqrt(m/2) congruent to the residues
    /// modulo the product m of the primes, if every one has one. It is tried
    /// once the primes have grown by a twentieth since the last try.
    fn reconstruct(&mut self) -> Option<Vec<QTerms>> {
        let k = self.primes.len();
        if k < self.next {
            return None;
        }
        self.next = (k + k / 20).max(k + 1);
        let crt = Crt::new(&self.primes).expect("distinct primes");
        let m = crt.modulus();
        let bound = (m - 1).fdiv_2exp(1).root(2).expect("a square root").0;
        let residues = |r: &[u32]| r.iter().map(|&x| x as u64).collect::<Vec<u64>>();
        // From where it failed last, round to there: a failure is likeliest
        // among the coefficients there. The denominator of a coefficient
        // often divides the lcm of those before it (the denominators of a
        // lex basis in shape position share most of their factors), and it
        // then needs no search.
        let at = || self.polys.iter().enumerate().flat_map(|(i, x)| (0..x.len()).map(move |j| (i, j)));
        let mut value: Vec<Vec<Option<Rational>>> = self.polys.iter().map(|x| vec![None; x.len()]).collect();
        let mut den = Integer::one();
        for (i, j) in at().skip_while(|&h| h != self.hard).chain(at().take_while(|&h| h != self.hard)) {
            let r = crt.combine(&residues(&self.polys[i][j].1));
            let c = with_denominator(&r, &den, m, &bound).or_else(|| {
                let c = Rational::reconstruct(&r, m, &bound)?;
                // Kept below m/2, where products with it still fit.
                let l = den.lcm(&c.denominator());
                den = if l.mul_2exp(1) < *m { l } else { c.denominator() };
                Some(c)
            });
            match c {
                Some(c) => value[i][j] = Some(c),
                None => {
                    self.hard = (i, j);
                    return None;
                }
            }
        }
        let terms = |(x, v): (&Vec<(Vec<u32>, Vec<u32>)>, Vec<Option<Rational>>)| {
            x.iter().zip(v).filter_map(|((e, _), c)| c.filter(|c| !c.is_zero()).map(|c| (e.clone(), c))).collect()
        };
        Some(self.polys.iter().zip(value).map(terms).collect())
    }
}

/// The fraction congruent to `r` modulo `m` whose denominator divides `d`,
/// if its numerator and denominator are at most `bound`; it is then the
/// fraction that rational reconstruction finds, for such fractions are
/// unique. Its product with `d` is found as the residue of r d nearest 0,
/// which it is if it is below m/2 in absolute value.
fn with_denominator(r: &Integer, d: &Integer, m: &Integer, bound: &Integer) -> Option<Rational> {
    let (_, a) = (r * d).div_rem_euclid(m)?;
    let b = m - &a;
    let a = if b < a { -b } else { a };
    if a.bits() > bound.bits() + d.bits() {
        return None;
    }
    let c = Rational::new(&a, d)?;
    (c.numerator().abs() <= *bound && c.denominator() <= *bound).then_some(c)
}
