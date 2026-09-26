//! Gröbner bases over the rationals by the modular method, Magma's default:
//! the reduced basis is computed modulo primes below 2^31, where F4 and FGLM
//! run in words, and its coefficients are recovered by Chinese remaindering
//! and rational reconstruction.
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
use calyx_flint::{Crt, Integer, Rational};

use crate::field::{Field, Zp};
use crate::order::Order;
use crate::poly::{Poly, Ring};
use crate::{Error, Terms, buchberger, fglm, graded, words_basis};

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
        return basis(q, ring, gens, |f, polys| words_basis(f, ring, polys, None));
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
/// no F4; for others, Buchberger's algorithm in the order.
pub(crate) fn change_order(q: &Rc<Ctx>, from: &Ring, gb: &[Terms], to: &Ring) -> Result<Option<Vec<Terms>>, Error> {
    let polys = qpolys(gb, from)?;
    if !zero_dimensional(&polys, from.n) {
        return basis(q, to, gb, |f, polys| buchberger::groebner(f, to, polys, None));
    }
    lift(q, to, |f| match polys.iter().map(|g| g.modulo(f, from.n)).collect::<Option<Vec<_>>>() {
        Some(polys) => fglm::fglm(f, from, &polys, to).map_or(Step::Fails, Step::Basis),
        None => Step::Bad,
    })
}

/// Whether the basis `gb` is that of the unit ideal or of a zero-dimensional
/// one, whose leading monomials include a power of each variable.
fn zero_dimensional(gb: &[QPoly], n: usize) -> bool {
    let lms: Vec<&[u32]> = gb.iter().map(|g| &g.e[..n]).collect();
    let pure = |k: usize| lms.iter().any(|l| l.iter().enumerate().all(|(i, &x)| (x > 0) == (i == k)));
    !gb.is_empty() && (lms.iter().any(|l| l.iter().all(|&x| x == 0)) || (0..n).all(pure))
}

/// The basis in the order of `ring` of the ideal generated by `gens`, whose
/// bases modulo primes `modular` computes from the reductions of `gens`.
fn basis(q: &Rc<Ctx>, ring: &Ring, gens: &[Terms], modular: impl Fn(&Zp, Vec<Poly<u64>>) -> Vec<Poly<u64>>) -> Result<Option<Vec<Terms>>, Error> {
    let gens = qpolys(gens, ring)?;
    if gens.is_empty() {
        return Ok(Some(Vec::new()));
    }
    lift(q, ring, |f| match gens.iter().map(|g| g.modulo(f, ring.n)).collect::<Option<Vec<_>>>() {
        Some(polys) => Step::Basis(modular(f, polys)),
        None => Step::Bad,
    })
}

/// What a computation modulo a prime gives.
enum Step {
    /// The basis modulo p, reduced and sorted.
    Basis(Vec<Poly<u64>>),
    /// Nothing: p divides a denominator or a leading coefficient.
    Bad,
    /// The method does not apply.
    Fails,
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
/// reductions modulo primes `step` computes.
fn lift(q: &Rc<Ctx>, ring: &Ring, mut step: impl FnMut(&Zp) -> Step) -> Result<Option<Vec<Terms>>, Error> {
    let n = ring.n;
    let mut groups: Vec<Lift> = Vec::new();
    let mut candidate: Option<(Vec<Vec<u32>>, Vec<QTerms>)> = None;
    for p in primes().take(MAX_PRIMES) {
        let ctx = Ctx::residue_ring(&Integer::from_u64(p));
        let f = Zp::new(&ctx);
        let g = match step(&f) {
            Step::Basis(g) => g,
            Step::Bad => continue,
            Step::Fails => return Ok(None),
        };
        let lms: Vec<Vec<u32>> = g.iter().map(|x| x.lm(n).to_vec()).collect();
        // A prime with the leading monomials of the candidate checks it; one
        // with others is taken for unlucky.
        if let Some((clms, c)) = &candidate {
            if *clms == lms {
                match agrees(c, &g, &f, n) {
                    Some(true) => return Ok(Some(export(q, c)?)),
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
    Ok(None)
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
        // among the coefficients there. A coefficient often has the
        // denominator of the one before it, which then needs no search.
        let at = || self.polys.iter().enumerate().flat_map(|(i, x)| (0..x.len()).map(move |j| (i, j)));
        let mut value: Vec<Vec<Option<Rational>>> = self.polys.iter().map(|x| vec![None; x.len()]).collect();
        let mut den: Vec<Integer> = vec![Integer::one(); self.polys.len()];
        for (i, j) in at().skip_while(|&h| h != self.hard).chain(at().take_while(|&h| h != self.hard)) {
            let r = crt.combine(&residues(&self.polys[i][j].1));
            let c = with_denominator(&r, &den[i], m, &bound).or_else(|| Rational::reconstruct(&r, m, &bound));
            match c {
                Some(c) => {
                    den[i] = c.denominator();
                    value[i][j] = Some(c);
                }
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

/// The fraction a/d congruent to `r` modulo `m` with |a| at most `bound`,
/// if there is one; it is then the fraction that rational reconstruction
/// finds, for `d` is at most `bound` and such fractions are unique.
fn with_denominator(r: &Integer, d: &Integer, m: &Integer, bound: &Integer) -> Option<Rational> {
    let (_, mut a) = (r * d).div_rem_euclid(m)?;
    if &a > bound {
        a -= m;
    }
    (a.abs() <= *bound).then(|| Rational::new(&a, d)).flatten()
}
