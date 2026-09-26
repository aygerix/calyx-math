//! Small roots of integer polynomials modulo an integer (SmallRoots), by
//! Coppersmith's method as May describes it (PhD thesis, 2003, Theorem 10).
//! For p monic of degree d, the polynomials n^(m-i) x^j p^i (i < m, j < d)
//! and x^j p^m (j < t) at xX span a lattice; if LLL finds a vector in it
//! shorter than n^(βm)/sqrt(dim) (Howgrave-Graham), its polynomial has
//! every root x0 of p modulo a divisor b >= n^β of n with |x0| <= X as a
//! root over Z.

use std::rc::Rc;

use calyx_flint::gr::{Ctx, Elem};
use calyx_flint::upoly as fu;
use calyx_flint::{Integer, lll_with};

use super::{is_integers, len, pol};
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::intrinsics::one;
use crate::value::*;

/// log2 |x| for x non-zero.
fn log2(x: &Integer) -> f64 {
    let b = x.bits();
    if b <= 1000 { x.abs().to_f64().log2() } else { x.abs().fdiv_2exp(b - 64).to_f64().log2() + (b - 64) as f64 }
}

fn mul(f: &[Integer], g: &[Integer]) -> Vec<Integer> {
    let mut h = vec![Integer::zero(); f.len() + g.len() - 1];
    for (i, a) in f.iter().enumerate() {
        for (j, b) in g.iter().enumerate() {
            h[i + j] += &(a * b);
        }
    }
    h
}

fn eval(p: &[Integer], x: &Integer) -> Integer {
    p.iter().rev().fold(Integer::zero(), |acc, c| &(&acc * x) + c)
}

/// The basis for exponent m and t shifts of p^m at xX; row k has degree k.
fn basis(p: &[Integer], n: &Integer, x: &Integer, m: usize, t: usize) -> Vec<Vec<Integer>> {
    let d = p.len() - 1;
    let dim = d * m + t;
    let mut rows = Vec::with_capacity(dim);
    let mut q = vec![Integer::one()];
    for i in 0..=m {
        let (c, count) = if i < m { (n.pow((m - i) as u64), d) } else { (Integer::one(), t) };
        for j in 0..count {
            let mut row = vec![Integer::zero(); dim];
            for (k, a) in q.iter().enumerate() {
                row[j + k] = a * &c;
            }
            rows.push(row);
        }
        if i < m {
            q = mul(&q, p);
        }
    }
    let mut xk = Integer::one();
    for k in 0..dim {
        for r in rows[k..].iter_mut() {
            r[k] *= &xk;
        }
        xk *= x;
    }
    rows
}

/// The bits by which the first vector of the reduced lattice for (m, t)
/// should beat Howgrave-Graham's bound, taking LLL to lose a factor 1.02
/// per dimension over det^(1/dim); `ln` and `lx` are log2 n and log2 X.
fn margin(d: usize, m: usize, t: usize, ln: f64, lx: f64, beta: f64) -> f64 {
    let dim = (d * m + t) as f64;
    let det = (d * m * (m + 1)) as f64 / 2.0 * ln + dim * (dim - 1.0) / 2.0 * lx;
    beta * m as f64 * ln - 0.5 * dim.log2() - det / dim - dim * 1.02f64.log2()
}

/// The largest lattice tried.
const MAX_DIM: usize = 160;

/// The shapes (m, t) to try, smallest lattice first: those with a positive
/// margin, or only the given exponent and shifts.
fn shapes(d: usize, ln: f64, lx: f64, beta: f64, m: Option<usize>, t: Option<usize>) -> Vec<(usize, usize)> {
    if let (Some(m), Some(t)) = (m, t) {
        return vec![(m, t)];
    }
    let mut out = Vec::new();
    for dim in 1..=MAX_DIM {
        for mm in 1..=dim / d {
            let tt = dim - d * mm;
            if m.is_some_and(|m| m != mm) || t.is_some_and(|t| t != tt) {
                continue;
            }
            if margin(d, mm, tt, ln, lx, beta) > 0.0 {
                out.push((mm, tt));
            }
        }
    }
    if out.is_empty() {
        // Out of reach: the best lattice below the largest dimension.
        let m = m.unwrap_or(((MAX_DIM - t.unwrap_or(0)) / d).max(1));
        let t = t.unwrap_or_else(|| (0..=MAX_DIM.saturating_sub(d * m)).max_by(|&a, &b| margin(d, m, a, ln, lx, beta).total_cmp(&margin(d, m, b, ln, lx, beta))).unwrap_or(0));
        out.push((m, t));
    }
    out
}

/// Whether x0 is a root of p modulo a divisor of n of at least n^β.
fn is_root(p: &[Integer], n: &Integer, x0: &Integer, beta: f64) -> bool {
    let g = eval(p, x0).gcd(n);
    if beta >= 1.0 { g == *n } else { g.bits() > 0 && log2(&g) >= beta * log2(n) - 1e-9 }
}

/// The integer roots of the polynomial of the lattice vector `v` (the
/// powers of X divided out), for the integer ring `zx` of p.
fn roots_of(zx: &Rc<Ctx>, v: &[Integer], x: &Integer) -> Vec<Integer> {
    let mut xk = Integer::one();
    let mut cs = Vec::with_capacity(v.len());
    for c in v {
        cs.push(c.divexact(&xk));
        xk *= x;
    }
    while cs.last().is_some_and(|c| c.is_zero()) {
        cs.pop();
    }
    if cs.len() < 2 {
        return Vec::new();
    }
    let zz = zx.base().expect("a polynomial ring");
    let es: Vec<Elem> = cs.iter().map(|c| Elem::from_integer(zz, c).expect("an integer")).collect();
    let f = Elem::poly_from_coeffs(zx, &es).expect("an integer polynomial");
    fu::roots(&f).map(|v| v.into_iter().filter_map(|(r, _)| r.to_integer().ok()).collect()).unwrap_or_default()
}

/// The integers x0 with |x0| <= x that are roots of the monic p (degree at
/// least 1, coefficients reduced modulo n > 1) modulo a divisor b >= n^β
/// of n, in increasing order, for the integer ring `zx` of p.
fn small_roots(zx: &Rc<Ctx>, p: &[Integer], n: &Integer, x: &Integer, beta: f64, m: Option<usize>, t: Option<usize>) -> Vec<Integer> {
    let d = p.len() - 1;
    let (ln, lx) = (log2(n), log2(x));
    // Without a power of p the lattice says nothing.
    let shapes: Vec<(usize, usize)> = shapes(d, ln, lx, beta, m, t).into_iter().filter(|&(m, _)| m > 0).collect();
    let mut need = f64::NEG_INFINITY;
    for (k, &(m, t)) in shapes.iter().enumerate() {
        let more = k + 1 < shapes.len();
        if margin(d, m, t, ln, lx, beta) < need && more {
            continue;
        }
        // The first vector must be shorter than n^(βm)/sqrt(dim): compare the
        // bits of its square. A rough reduction often suffices.
        let target = 2.0 * beta * m as f64 * ln - ((d * m + t) as f64).log2();
        let over = |rows: &[Vec<Integer>]| log2(&rows[0].iter().fold(Integer::zero(), |acc, c| &acc + &(c * c))) - target;
        let mut rows = basis(p, n, x, m, t);
        lll_with(&mut rows, 0.75);
        let mut o = over(&rows);
        if o >= 0.0 {
            lll_with(&mut rows, 0.99);
            o = over(&rows);
        }
        if o >= 0.0 && more {
            // Skip to lattices that should beat the bound by what this missed it.
            need = margin(d, m, t, ln, lx, beta) + o / 2.0 + 1.0;
            continue;
        }
        let mut rs: Vec<Integer> = roots_of(zx, &rows[0], x).into_iter().filter(|r| r.abs() <= *x && is_root(p, n, r, beta)).collect();
        rs.sort();
        rs.dedup();
        return rs;
    }
    Vec::new()
}

/// Whether X reaches the method's bound N^(β^2/d) / 2.
fn too_large(n: &Integer, x: &Integer, beta: f64, d: usize) -> bool {
    n.is_zero() || log2(x) + 1.0 >= beta * beta / d as f64 * log2(n)
}

fn bad_type(it: &Interp, a: &CallArgs, name: &str) -> RuntimeError {
    let types: Vec<String> = a.args.iter().map(|v| it.type_name_ext(v)).collect();
    RuntimeError::runtime(format!("Bad type for parameter '{name}'\nArgument types given: {}", types.join(", ")))
}

fn bool_param(it: &Interp, a: &CallArgs, name: &str) -> RResult<bool> {
    match a.param(name) {
        None | Some(Value::Undef) => Ok(false),
        Some(Value::Bool(b)) => Ok(*b),
        Some(_) => Err(bad_type(it, a, name)),
    }
}

/// The parameter Exponent or Finalshifts: None for 0 (chosen here).
fn shape_param(it: &Interp, a: &CallArgs, name: &str) -> RResult<Option<usize>> {
    match a.param(name) {
        None | Some(Value::Undef) => Ok(None),
        Some(Value::Int(k)) => match k.to_i64() {
            Some(0) => Ok(None),
            Some(v) if (1..1 << 10).contains(&v) => Ok(Some(v as usize)),
            _ => Err(RuntimeError::runtime(format!("Bad value for parameter '{name}' (should be non-negative and moderate)"))),
        },
        Some(_) => Err(bad_type(it, a, name)),
    }
}

pub(super) fn small_roots_fn(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    let (Value::Int(n), Value::Int(x)) = (&a.args[1], &a.args[2]) else { unreachable!("integer arguments") };
    let (n, x) = (n.abs(), x.clone());
    let beta = match a.param("Beta") {
        None | Some(Value::Undef) => 1.0,
        Some(Value::Real(r)) => r.x.to_f64(),
        Some(_) => return Err(bad_type(it, a, "Beta")),
    };
    if !(beta > 0.0 && beta <= 1.0) {
        return Err(RuntimeError::runtime("Bad value for parameter 'Beta' (should be in range (0, 1])"));
    }
    let (m, t) = (shape_param(it, a, "Exponent")?, shape_param(it, a, "Finalshifts")?);
    bool_param(it, a, "Direct")?;
    if !is_integers(&f) {
        return Err(RuntimeError::runtime("Polynomial coefficients must be integers"));
    }
    if len(&f) == 0 {
        return Err(RuntimeError::runtime("The input polynomial must be non-zero"));
    }
    let mut p: Vec<Integer> = (0..len(&f)).map(|i| f.x.poly_coeff(i).to_integer()).collect::<Result<_, _>>()?;
    if !p.last().expect("a non-zero polynomial").is_one() {
        return Err(RuntimeError::runtime("Argument 1 is not monic"));
    }
    if x.sign() <= 0 {
        return Err(RuntimeError::runtime("X must be positive"));
    }
    // With Bits X is 2^X, too large (above n) unless X is at most log2 n.
    let x = if bool_param(it, a, "Bits")? {
        match x.to_i64() {
            Some(e) if e <= n.bits() as i64 => Integer::one().mul_2exp(e as u64),
            _ => return Err(RuntimeError::runtime("X is too large")),
        }
    } else {
        x
    };
    if p.len() < 2 {
        return one(Value::seq(Some(Value::integers()), Vec::new()));
    }
    if too_large(&n, &x, beta, p.len() - 1) {
        return Err(RuntimeError::runtime("X is too large"));
    }
    for c in p.iter_mut() {
        *c = c.div_rem_euclid(&n).expect("n > 1").1;
    }
    let rs = small_roots(f.x.ctx(), &p, &n, &x, beta, m, t);
    one(Value::seq(Some(Value::integers()), rs.into_iter().map(Value::Int).collect()))
}
