//! Integration schemes on [-1, 1]: the nodes and weights of Gauss–Legendre,
//! Gauss–Jacobi, Clenshaw–Curtis and tanh–sinh (double exponential)
//! quadrature, each rounded correctly to the precision asked for (the
//! Gauss–Jacobi nodes: to within an error far below the last place). Nodes
//! are in increasing order.

use flint3_sys as sys;

use crate::ball::{self, Acb, Arb};
use crate::mpfr as m;
use crate::{Complex, Real};

/// The Gauss–Legendre nodes and weights on n points.
pub fn gauss_legendre(n: u64, bits: u64) -> (Vec<Real>, Vec<Real>) {
    // FLINT numbers the roots from the largest; x_k = -x_(n-1-k).
    let half: Vec<(Real, Real)> = (0..n.div_ceil(2))
        .map(|k| {
            let node = ball::eval_real(bits, |out, wp| unsafe { sys::arb_hypgeom_legendre_p_ui_root(out, std::ptr::null_mut(), n, k, wp) });
            let weight = ball::eval_real(bits, |out, wp| unsafe {
                let mut x = Arb::new();
                sys::arb_hypgeom_legendre_p_ui_root(x.mut_ptr(), out, n, k, wp);
            });
            (node, weight)
        })
        .collect();
    let mut nodes = Vec::with_capacity(n as usize);
    let mut weights = Vec::with_capacity(n as usize);
    for i in 0..n {
        let (k, neg) = if i < n / 2 { (i, true) } else { (n - 1 - i, false) };
        let (x, w) = &half[k as usize];
        nodes.push(if neg { x.neg() } else { x.clone() });
        weights.push(w.clone());
    }
    (nodes, weights)
}

/// `P_n(z)` and `P_(n-1)(z)` for the Jacobi polynomials of parameters
/// (a, b), and `P_n'(z)`, by the three-term recurrence (as `f64` or at the
/// precision of `z`).
trait Num: Clone {
    fn c(&self, v: f64) -> Self;
    fn add(&self, o: &Self) -> Self;
    fn sub(&self, o: &Self) -> Self;
    fn mul(&self, o: &Self) -> Self;
    fn div(&self, o: &Self) -> Self;
}

impl Num for f64 {
    fn c(&self, v: f64) -> f64 {
        v
    }
    fn add(&self, o: &f64) -> f64 {
        self + o
    }
    fn sub(&self, o: &f64) -> f64 {
        self - o
    }
    fn mul(&self, o: &f64) -> f64 {
        self * o
    }
    fn div(&self, o: &f64) -> f64 {
        self / o
    }
}

impl Num for Real {
    fn c(&self, v: f64) -> Real {
        Real::from_f64(v, self.prec())
    }
    fn add(&self, o: &Real) -> Real {
        Real::add(self, o)
    }
    fn sub(&self, o: &Real) -> Real {
        Real::sub(self, o)
    }
    fn mul(&self, o: &Real) -> Real {
        Real::mul(self, o)
    }
    fn div(&self, o: &Real) -> Real {
        Real::div(self, o).unwrap_or_else(|| Real::nan(self.prec()))
    }
}

/// `(P_n(z), P_(n-1)(z), P_n'(z))` for the Jacobi polynomials with weight
/// `(1-x)^a (1+x)^b`, as in Numerical Recipes' `gaujac`.
fn jacobi<T: Num>(n: u64, a: &T, b: &T, z: &T) -> (T, T, T) {
    let one = z.c(1.0);
    let two = z.c(2.0);
    let ab = a.add(b);
    let mut p1 = a.sub(b).add(&two.add(&ab).mul(z)).div(&two);
    let mut p2 = one.clone();
    for j in 2..=n {
        let p3 = p2;
        p2 = p1.clone();
        let jj = z.c(j as f64);
        let temp = z.c(2.0 * j as f64).add(&ab);
        let tm2 = temp.sub(&two);
        let an = two.mul(&jj).mul(&jj.add(&ab)).mul(&tm2);
        let bn = temp.sub(&one).mul(&a.mul(a).sub(&b.mul(b)).add(&temp.mul(&tm2).mul(z)));
        let jm1 = z.c((j - 1) as f64);
        let cn = two.mul(&jm1.add(a)).mul(&jm1.add(b)).mul(&temp);
        p1 = bn.mul(&p2).sub(&cn.mul(&p3)).div(&an);
    }
    let nn = z.c(n as f64);
    let temp = z.c(2.0 * n as f64).add(&ab);
    let num = nn.mul(&a.sub(b).sub(&temp.mul(z))).mul(&p1).add(&two.mul(&nn.add(a)).mul(&nn.add(b)).mul(&p2));
    let pp = num.div(&temp.mul(&one.sub(&z.mul(z))));
    (p1, p2, pp)
}

/// Approximations of the roots of the Jacobi polynomial of degree n, in
/// increasing order: the eigenvalues of its Jacobi matrix (Golub and
/// Welsch), by the implicit QL method (Numerical Recipes' `tqli`).
fn jacobi_roots_f64(n: u64, a: f64, b: f64) -> Vec<f64> {
    let n = n as usize;
    let ab = a + b;
    // The recurrence x p_k = β_k p_(k-1) + α_k p_k + β_(k+1) p_(k+1) of the
    // orthonormal polynomials.
    let mut d: Vec<f64> = (0..n)
        .map(|k| {
            let s = 2.0 * k as f64 + ab;
            if k == 0 { (b - a) / (ab + 2.0) } else { (b * b - a * a) / (s * (s + 2.0)) }
        })
        .collect();
    let mut e: Vec<f64> = (1..n)
        .map(|k| {
            let (k, s) = (k as f64, 2.0 * k as f64 + ab);
            if k == 1.0 {
                (4.0 * (1.0 + a) * (1.0 + b) / ((2.0 + ab) * (2.0 + ab) * (3.0 + ab))).sqrt()
            } else {
                (4.0 * k * (k + a) * (k + b) * (k + ab) / (s * s * (s + 1.0) * (s - 1.0))).sqrt()
            }
        })
        .collect();
    e.push(0.0);
    for l in 0..n {
        for _ in 0..60 {
            let mut m = l;
            while m + 1 < n {
                let dd = d[m].abs() + d[m + 1].abs();
                if e[m].abs() + dd == dd {
                    break;
                }
                m += 1;
            }
            if m == l {
                break;
            }
            let mut g = (d[l + 1] - d[l]) / (2.0 * e[l]);
            let mut r = g.hypot(1.0);
            g = d[m] - d[l] + e[l] / (g + r.copysign(g));
            let (mut s, mut c, mut p) = (1.0, 1.0, 0.0);
            let mut i = m;
            let mut underflow = false;
            while i > l {
                i -= 1;
                let f = s * e[i];
                let bb = c * e[i];
                r = f.hypot(g);
                e[i + 1] = r;
                if r == 0.0 {
                    d[i + 1] -= p;
                    e[m] = 0.0;
                    underflow = true;
                    break;
                }
                s = f / r;
                c = g / r;
                g = d[i + 1] - p;
                r = (d[i] - g) * s + 2.0 * c * bb;
                p = s * r;
                d[i + 1] = g + p;
                g = c * r - bb;
            }
            if underflow {
                continue;
            }
            d[l] -= p;
            e[l] = g;
            e[m] = 0.0;
        }
    }
    d.sort_by(|x, y| x.total_cmp(y));
    d
}

/// The Gauss–Jacobi nodes and weights on n points for the weight
/// `(1-x)^a (1+x)^b`, a, b > -1. The nodes are found by Newton's method at
/// a working precision well above `bits`.
pub fn gauss_jacobi(n: u64, a: &Real, b: &Real, bits: u64) -> (Vec<Real>, Vec<Real>) {
    let wp = bits + 64 + 64 - (n.max(1).leading_zeros() as u64);
    let (a, b) = (a.round_to(wp), b.round_to(wp));
    let guesses = jacobi_roots_f64(n, a.to_f64(), b.to_f64());
    let nn = Real::from_i64(n as i64, wp);
    let ab = a.add(&b);
    // Γ(n+a)Γ(n+b) / (Γ(n+1)Γ(n+a+b+1)) 2^(a+b) (2n+a+b), from logarithms
    let lg = |x: &Real| x.lgamma().0;
    let c = lg(&nn.add(&a)).add(&lg(&nn.add(&b))).sub(&lg(&nn.add_i64(1))).sub(&lg(&nn.add(&ab).add_i64(1))).unary(m::mpfr_exp);
    let c = c.mul(&Real::from_i64(2, wp).pow(&ab)).mul(&nn.mul_i64(2).add(&ab));
    let mut nodes = Vec::with_capacity(n as usize);
    let mut weights = Vec::with_capacity(n as usize);
    for g in &guesses {
        let mut z = Real::from_f64(*g, wp);
        let mut last = None;
        for _ in 0..wp.ilog2() + 8 {
            let (p1, _, pp) = jacobi(n, &a, &b, &z);
            let dz = p1.div(&pp).unwrap_or_else(|| Real::zero(wp));
            z = z.sub(&dz);
            let e = if dz.is_zero() { i64::MIN } else { dz.exponent() };
            if e < z.exponent().min(0) - wp as i64 + 8 && last.is_some_and(|l: i64| e < l) {
                break;
            }
            last = Some(e);
        }
        let (_, p2, pp) = jacobi(n, &a, &b, &z);
        let w = c.div(&pp.mul(&p2)).unwrap_or_else(|| Real::nan(wp));
        nodes.push(z.round_to(bits));
        weights.push(w.round_to(bits));
    }
    (nodes, weights)
}

/// The Clenshaw–Curtis nodes `cos(kπ/n)`, k = n, ..., 0, and weights on
/// n + 1 points.
pub fn clenshaw_curtis(n: u64, bits: u64) -> (Vec<Real>, Vec<Real>) {
    let mut nodes = Vec::with_capacity(n as usize + 1);
    let mut weights = Vec::with_capacity(n as usize + 1);
    for k in (0..=n).rev() {
        nodes.push(ball::eval_real(bits, |out, wp| unsafe {
            // cos(kπ/n) = cos(π·(k/n))
            let mut t = Arb::new();
            sys::arb_set_ui(t.mut_ptr(), k);
            sys::arb_div_ui(t.mut_ptr(), t.ptr(), n, wp);
            sys::arb_cos_pi(out, t.ptr(), wp);
        }));
        weights.push(ball::eval_real(bits, |out, wp| unsafe {
            // (c_k/n) (1 - Σ_(j=1)^(n/2) b_j/(4j²-1) cos(2jkπ/n)), with
            // b_j = 1 for j = n/2, else 2, and c_k = 1 at the ends, else 2
            let (mut s, mut t, mut u) = (Arb::new(), Arb::new(), Arb::new());
            sys::arb_one(s.mut_ptr());
            for j in 1..=n / 2 {
                sys::arb_set_ui(t.mut_ptr(), (2 * j * k) % (2 * n));
                sys::arb_div_ui(t.mut_ptr(), t.ptr(), n, wp);
                sys::arb_cos_pi(t.mut_ptr(), t.ptr(), wp);
                sys::arb_div_ui(t.mut_ptr(), t.ptr(), 4 * j * j - 1, wp);
                let bj = if 2 * j == n { 1 } else { 2 };
                sys::arb_mul_ui(u.mut_ptr(), t.ptr(), bj, wp);
                sys::arb_sub(s.mut_ptr(), s.ptr(), u.ptr(), wp);
            }
            let ck = if k == 0 || k == n { 1 } else { 2 };
            sys::arb_mul_ui(s.mut_ptr(), s.ptr(), ck, wp);
            sys::arb_div_ui(out, s.ptr(), n, wp);
        }));
    }
    (nodes, weights)
}

/// The tanh–sinh nodes `x_k = tanh(π/2 sinh(kh))`, k = -n, ..., n, their
/// weights `π/2 h cosh(kh) / cosh²(π/2 sinh(kh))` and the factors
/// `cosh²(π/2 sinh(kh)) = 1/(1 - x_k²)`, at the precision of h.
pub fn tanh_sinh(n: u64, h: &Real) -> (Vec<Real>, Vec<Real>, Vec<Real>) {
    let bits = h.prec();
    let hb = Arb::from_real(h);
    // u = π/2 sinh(kh), and cosh(kh)
    let args = |k: i64, u: *mut sys::arb_struct, ch: *mut sys::arb_struct, wp: i64| unsafe {
        let mut t = Arb::new();
        sys::arb_mul_si(t.mut_ptr(), hb.ptr(), k, wp);
        sys::arb_sinh_cosh(u, ch, t.ptr(), wp);
        sys::arb_const_pi(t.mut_ptr(), wp);
        sys::arb_mul(u, u, t.ptr(), wp);
        sys::arb_mul_2exp_si(u, u, -1);
    };
    let (mut xs, mut w1, mut w2) = (Vec::new(), Vec::new(), Vec::new());
    for k in -(n as i64)..=n as i64 {
        xs.push(ball::eval_real(bits, |out, wp| unsafe {
            let (mut u, mut ch) = (Arb::new(), Arb::new());
            args(k, u.mut_ptr(), ch.mut_ptr(), wp);
            sys::arb_tanh(out, u.ptr(), wp);
        }));
        w1.push(ball::eval_real(bits, |out, wp| unsafe {
            let (mut u, mut ch, mut t) = (Arb::new(), Arb::new(), Arb::new());
            args(k, u.mut_ptr(), ch.mut_ptr(), wp);
            sys::arb_sech(t.mut_ptr(), u.ptr(), wp);
            sys::arb_sqr(t.mut_ptr(), t.ptr(), wp);
            sys::arb_mul(t.mut_ptr(), t.ptr(), ch.ptr(), wp);
            sys::arb_mul(t.mut_ptr(), t.ptr(), hb.ptr(), wp);
            sys::arb_const_pi(u.mut_ptr(), wp);
            sys::arb_mul(t.mut_ptr(), t.ptr(), u.ptr(), wp);
            sys::arb_mul_2exp_si(out, t.ptr(), -1);
        }));
        w2.push(ball::eval_real(bits, |out, wp| unsafe {
            let (mut u, mut ch) = (Arb::new(), Arb::new());
            args(k, u.mut_ptr(), ch.mut_ptr(), wp);
            sys::arb_cosh(out, u.ptr(), wp);
            sys::arb_sqr(out, out, wp);
        }));
    }
    (xs, w1, w2)
}

/// The discrete Fourier transform `w_k = Σ_j v_j e^(-2πijk/n)` of complex
/// numbers of precision `bits`, each part rounded correctly.
pub fn dft(v: &[Complex], bits: u64) -> Vec<Complex> {
    let n = v.len();
    if n == 0 {
        return Vec::new();
    }
    let input: Vec<Acb> = v.iter().map(|z| z.acb()).collect();
    let mut last = Vec::new();
    for wp in ball::precisions(bits) {
        unsafe {
            let src = sys::_acb_vec_init(n as sys::slong);
            let dst = sys::_acb_vec_init(n as sys::slong);
            for (i, z) in input.iter().enumerate() {
                sys::acb_set(src.add(i), z.ptr());
            }
            sys::acb_dft(dst, src, n as sys::slong, wp as sys::slong);
            last = (0..n).map(|i| ball::round_acb(&*dst.add(i), bits)).collect();
            sys::_acb_vec_clear(src, n as sys::slong);
            sys::_acb_vec_clear(dst, n as sys::slong);
        }
        if last.iter().all(|z: &Result<Complex, Complex>| z.is_ok()) {
            break;
        }
    }
    last.into_iter().map(|z| z.unwrap_or_else(|mid| mid)).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Integer, Rational};

    fn q(n: i64, d: i64, bits: u64) -> Real {
        Real::from_rational(&Rational::new(&Integer::from_i64(n), &Integer::from_i64(d)).unwrap(), bits)
    }

    fn m(v: &[Real]) -> Vec<String> {
        v.iter().map(|x| x.mantissa_exponent().0.to_string()).collect()
    }

    /// Mantissas at 67 bits, checked with mpmath.
    /// The roots found are distinct, in [-1, 1] and in order.
    #[test]
    fn jacobi_roots() {
        for n in 1..=120u64 {
            for &(a, b) in &[(0.0, 0.0), (-1.0 / 3.0, -0.2), (-0.9, 0.5), (0.5, -0.9), (2.5, 3.0), (-0.5, -0.5), (10.0, 0.0), (0.0, 10.0)] {
                let x = jacobi_roots_f64(n, a, b);
                let ok = x.iter().all(|t| t.abs() < 1.0) && x.windows(2).all(|w| w[0] < w[1] - 1e-12);
                assert!(ok, "n = {n}, a = {a}, b = {b}: {x:?}");
            }
        }
    }

    #[test]
    fn schemes() {
        let (x, w) = gauss_legendre(5, 67);
        assert_eq!(m(&x), ["-133728541622272676038", "-79464044440531842659", "0", "79464044440531842659", "133728541622272676038"]);
        assert_eq!(m(&w), ["139856947610007045640", "141266249456666721459", "83953181917682581577", "141266249456666721459", "139856947610007045640"]);
        let (x, w) = gauss_jacobi(4, &q(-1, 3, 67), &q(-1, 5, 67), 67);
        assert_eq!(m(&x), ["-130029579144132949206", "-99427334043170628582", "113542847582078196040", "133512818988227480686"]);
        assert_eq!(m(&w), ["125833288261640513586", "101047917231845713082", "110798231195327930071", "88265984676856146853"]);
        let (x, w) = clenshaw_curtis(4, 67);
        assert_eq!(m(&x), ["-73786976294838206464", "-104350542602662257699", "0", "104350542602662257699", "73786976294838206464"]);
        assert_eq!(m(&w), ["78706108047827420228", "78706108047827420228", "118059162071741130342", "78706108047827420228", "78706108047827420228"]);
        let (x, w1, w2) = tanh_sinh(2, &q(1, 2, 67));
        assert_eq!(m(&x), ["-140397130825408530706", "-99504909229641035562", "0", "99504909229641035562", "140397130825408530706"]);
        assert_eq!(m(&w1), ["135781255770757076724", "142552981932928722147", "115904311329233965478", "142552981932928722147", "135781255770757076724"]);
        assert_eq!(m(&w2), ["97191459706024040974", "135300082548299472233", "73786976294838206464", "135300082548299472233", "97191459706024040974"]);
    }
}
