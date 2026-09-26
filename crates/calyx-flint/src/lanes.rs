//! Arithmetic in GF(p^n) = F_p[x]/(f) for odd primes p below 2^16, with the
//! n coordinates of an element in 8-bit lanes (p below 2^8, n up to 64) or
//! 16-bit ones (n up to 32), so that an element fits in 64 bytes and the
//! packed field contexts (see `packed`) keep it inline.
//!
//! Products sum in the narrowest lanes their bound allows (16 bits for
//! GF(3^40), 32 for GF(251^10)), eight coefficients of the result at a time
//! in a vector, then reduce modulo f by the rows x^(n+k) modulo f, with one
//! reduction modulo p per coefficient. Inverses and norms (resultants with
//! f) come from Euclid's algorithm with a table of inverses modulo p, the
//! Frobenius from its matrix, and traces from those of the powers of x.

use std::array;
use std::cell::OnceCell;

/// A coordinate, below p.
pub trait Lane: Copy + Eq + Default + std::fmt::Debug + 'static {
    fn get(self) -> u32;
    fn of(x: u32) -> Self;
}

impl Lane for u8 {
    #[inline(always)]
    fn get(self) -> u32 {
        self as u32
    }

    #[inline(always)]
    fn of(x: u32) -> u8 {
        x as u8
    }
}

impl Lane for u16 {
    #[inline(always)]
    fn get(self) -> u32 {
        self as u32
    }

    #[inline(always)]
    fn of(x: u32) -> u16 {
        x as u16
    }
}

/// Reduction modulo an odd p below 2^16 by Barrett's method, of words and
/// of 32- and 16-bit values. The quotient estimates are short by at most 1.
#[derive(Clone, Copy, Debug)]
struct Barrett {
    p: u64,
    /// floor(2^64 / p), floor(2^32 / p) and floor(2^16 / p), none exact as
    /// p is odd.
    m64: u64,
    m32: u32,
    m16: u16,
}

impl Barrett {
    fn new(p: u64) -> Barrett {
        Barrett { p, m64: u64::MAX / p, m32: ((1 << 32) / p) as u32, m16: ((1 << 16) / p) as u16 }
    }

    #[inline(always)]
    fn word(self, x: u64) -> u64 {
        let r = x - ((x as u128 * self.m64 as u128) >> 64) as u64 * self.p;
        if r >= self.p { r - self.p } else { r }
    }

    #[inline(always)]
    fn half(self, x: u32) -> u32 {
        let p = self.p as u32;
        let r = x - ((x as u64 * self.m32 as u64) >> 32) as u32 * p;
        if r >= p { r - p } else { r }
    }

    #[inline(always)]
    fn short(self, x: u16) -> u16 {
        let p = self.p as u16;
        let r = x - ((x as u32 * self.m16 as u32) >> 16) as u16 * p;
        if r >= p { r - p } else { r }
    }
}

/// A lane for sums of products, as narrow as their bound allows so that
/// more of them fit in a vector.
trait Acc: Copy + Default + Eq + std::ops::AddAssign + std::ops::Add<Output = Self> + std::ops::Mul<Output = Self> {
    fn of(x: u32) -> Self;
    fn get(self) -> u32;
    /// The value modulo p.
    fn modp(self, b: Barrett) -> Self;
}

impl Acc for u16 {
    #[inline(always)]
    fn of(x: u32) -> u16 {
        x as u16
    }

    #[inline(always)]
    fn get(self) -> u32 {
        self as u32
    }

    #[inline(always)]
    fn modp(self, b: Barrett) -> u16 {
        b.short(self)
    }
}

impl Acc for u32 {
    #[inline(always)]
    fn of(x: u32) -> u32 {
        x
    }

    #[inline(always)]
    fn get(self) -> u32 {
        self
    }

    #[inline(always)]
    fn modp(self, b: Barrett) -> u32 {
        b.half(self)
    }
}

impl Acc for u64 {
    #[inline(always)]
    fn of(x: u32) -> u64 {
        x as u64
    }

    #[inline(always)]
    fn get(self) -> u32 {
        self as u32
    }

    #[inline(always)]
    fn modp(self, b: Barrett) -> u64 {
        b.word(self)
    }
}

/// The rows x^(n+k) modulo f for k below n - 1, which reduce products, in
/// the lanes products sum in: the narrowest that holds their sums (below
/// 2n p^2), so that more of them fit in a vector.
#[derive(Clone, Debug)]
enum Rows<const N: usize> {
    W16(Vec<[u16; N]>),
    W32(Vec<[u32; N]>),
    W64(Vec<[u64; N]>),
}

/// The zeros in front of the polynomials in Euclid's algorithm, so that
/// shifted reads below them find zeros.
const PAD: usize = 8;

/// GF(p^n) for an odd prime p below 2^16, its elements `[T; N]` with n
/// coordinates (constant term first) and zeros after.
#[derive(Clone, Debug)]
pub struct FpLanes<T: Lane, const N: usize> {
    b: Barrett,
    n: usize,
    /// n rounded up to a multiple of 8, the length of rows.
    m: usize,
    /// The coefficients of f below x^n, and their negatives (x^n modulo f).
    f: [u32; N],
    fneg: [u32; N],
    rows: Rows<N>,
    /// The inverses modulo p, by residue (0 at 0), made when first needed.
    inv: OnceCell<Vec<T>>,
    /// Tr(x^i) for i below n.
    tr: [u32; N],
    /// x^(p i) modulo f for i below n: the rows of the Frobenius.
    frob: Vec<[u32; N]>,
}

/// The degree of the polynomial x (-1 for 0), from `top` down.
fn degree_of<A: Acc>(x: &[A], top: isize) -> isize {
    let mut d = top;
    while d >= 0 && x[d as usize] == A::default() {
        d -= 1;
    }
    d
}

impl<T: Lane, const N: usize> FpLanes<T, N> {
    /// The field for a monic irreducible f of degree n, 1 <= n <= N, given
    /// by its coefficients below x^n.
    pub fn new(p: u64, f: &[u64]) -> FpLanes<T, N> {
        let n = f.len();
        assert!(p % 2 == 1 && p > 2 && p >> (8 * std::mem::size_of::<T>()) == 0 && (1..=N).contains(&n));
        let fr: [u32; N] = array::from_fn(|i| if i < n { (f[i] % p) as u32 } else { 0 });
        let fneg: [u32; N] = array::from_fn(|i| ((p - fr[i] as u64) % p) as u32);
        let mut rows = Vec::with_capacity(n - 1);
        let mut r = fneg;
        for _ in 1..n {
            rows.push(r);
            let top = r[n - 1] as u64;
            r = array::from_fn(|i| if i < n { ((if i > 0 { r[i - 1] as u64 } else { 0 } + top * fneg[i] as u64) % p) as u32 } else { 0 });
        }
        let rows = match 2 * n as u64 * (p - 1) * (p - 1) + p {
            0..0x1_0000 => Rows::W16(rows.iter().map(|r| r.map(|x| x as u16)).collect()),
            0x1_0000..0x1_0000_0000 => Rows::W32(rows),
            _ => Rows::W64(rows.iter().map(|r| r.map(|x| x as u64)).collect()),
        };
        let (b, m) = (Barrett::new(p), n.next_multiple_of(8));
        let mut k: FpLanes<T, N> = FpLanes { b, n, m, f: fr, fneg, rows, inv: OnceCell::new(), tr: [0; N], frob: Vec::new() };
        // Newton's identities for the power sums of the roots of f: s_0 = n,
        // s_j = -(j f_(n-j) + the sum over 0 < i < j of f_(n-i) s_(j-i)).
        let mut s = vec![n as u64 % p; n];
        for j in 1..n {
            let t = (1..j).fold(j as u64 % p * k.f[n - j] as u64 % p, |t, i| (t + k.f[n - i] as u64 * s[j - i]) % p);
            s[j] = (p - t) % p;
        }
        for (t, &v) in k.tr.iter_mut().zip(&s) {
            *t = v as u32;
        }
        let xp = k.pow(&k.generator(), &[p]);
        let mut row = k.scalar(1);
        for _ in 0..n {
            k.frob.push(array::from_fn(|i| row[i].get()));
            row = k.mul(&row, &xp);
        }
        k
    }

    fn zero(&self) -> [T; N] {
        [T::default(); N]
    }

    /// The table of inverses modulo p: 1/i = -(p div i)/(p mod i).
    fn inverses(&self) -> &[T] {
        self.inv.get_or_init(|| {
            let p = self.b.p as u32;
            let mut inv = vec![T::default(); p as usize];
            inv[1] = T::of(1);
            for i in 2..p {
                inv[i as usize] = T::of((p - p / i) * inv[(p % i) as usize].get() % p);
            }
            inv
        })
    }

    /// The element c of the prime field.
    pub fn scalar(&self, c: u64) -> [T; N] {
        let mut r = self.zero();
        r[0] = T::of((c % self.b.p) as u32);
        r
    }

    /// The root of f.
    pub fn generator(&self) -> [T; N] {
        let mut r = self.zero();
        if self.n == 1 {
            r[0] = T::of(self.fneg[0]);
        } else {
            r[1] = T::of(1);
        }
        r
    }

    pub fn add(&self, a: &[T; N], b: &[T; N]) -> [T; N] {
        let p = self.b.p as u32;
        array::from_fn(|i| {
            let s = a[i].get() + b[i].get();
            T::of(if s >= p { s - p } else { s })
        })
    }

    pub fn sub(&self, a: &[T; N], b: &[T; N]) -> [T; N] {
        let p = self.b.p as u32;
        array::from_fn(|i| {
            let (x, y) = (a[i].get(), b[i].get());
            T::of(if x >= y { x - y } else { x + p - y })
        })
    }

    pub fn neg(&self, a: &[T; N]) -> [T; N] {
        let p = self.b.p as u32;
        array::from_fn(|i| T::of(if a[i].get() == 0 { 0 } else { p - a[i].get() }))
    }

    /// a*c for c below p.
    pub fn mul_scalar(&self, a: &[T; N], c: u64) -> [T; N] {
        let c = (c % self.b.p) as u32;
        array::from_fn(|i| T::of(self.b.half(a[i].get() * c)))
    }

    /// The 2n - 1 coefficients of a b (sums below n p^2), 8 at a time: each
    /// chunk sums its terms in a vector and is stored once.
    #[inline(always)]
    fn product<A: Acc>(&self, a: &[T; N], b: &[T; N]) -> [[A; 2]; N] {
        let n = self.n;
        // b between N zeros on each side, for shifted reads past its ends.
        let mut bp = [[A::default(); 3]; N];
        let bp = bp.as_flattened_mut();
        for (x, y) in bp[N..2 * N].iter_mut().zip(b) {
            *x = A::of(y.get());
        }
        let mut acc = [[A::default(); 2]; N];
        let out = acc.as_flattened_mut();
        for c in (0..2 * n - 1).step_by(8) {
            let mut s = [A::default(); 8];
            for i in (c + 1).saturating_sub(n)..n.min(c + 8) {
                let x = A::of(a[i].get());
                for (t, &y) in s.iter_mut().zip(&bp[N + c - i..N + c - i + 8]) {
                    *t += x * y;
                }
            }
            out[c..c + 8].copy_from_slice(&s);
        }
        acc
    }

    /// The element with the coefficients of a product: those of degree n and
    /// more taken modulo p and replaced by their multiples of the rows (the
    /// sums stay below 2n p^2), then all modulo p.
    #[inline(always)]
    fn reduce<A: Acc>(&self, acc: &[[A; 2]; N], rows: &[[A; N]]) -> [T; N] {
        let (n, m, c) = (self.n, self.m, acc.as_flattened());
        let mut lo: [A; N] = array::from_fn(|i| if i < n { c[i] } else { A::default() });
        for (k, row) in rows.iter().enumerate() {
            let h = c[n + k].modp(self.b);
            for (r, y) in lo[..m].chunks_exact_mut(8).zip(row[..m].chunks_exact(8)) {
                for (r, &y) in r.iter_mut().zip(y) {
                    *r += h * y;
                }
            }
        }
        array::from_fn(|i| if i < n { T::of(lo[i].modp(self.b).get()) } else { T::default() })
    }

    /// The 2n - 1 coefficients of a^2 as `product` finds them, with each
    /// product of two different coefficients once, doubled: a chunk at c
    /// takes the terms a_i a_(k-i) with 2i < c in full, and those with 2i
    /// from c to c + 7 weighted lane by lane (2 below the diagonal, 1 on it).
    #[inline(always)]
    fn square<A: Acc>(&self, a: &[T; N]) -> [[A; 2]; N] {
        const WEIGHTS: [[u32; 8]; 8] = {
            let mut w = [[0; 8]; 8];
            let mut d = 0;
            while d < 8 {
                let mut l = d;
                while l < 8 {
                    w[d][l] = if l == d { 1 } else { 2 };
                    l += 1;
                }
                d += 1;
            }
            w
        };
        let n = self.n;
        let mut ap = [[A::default(); 3]; N];
        let ap = ap.as_flattened_mut();
        for (x, y) in ap[N..2 * N].iter_mut().zip(a) {
            *x = A::of(y.get());
        }
        let mut acc = [[A::default(); 2]; N];
        let out = acc.as_flattened_mut();
        for c in (0..2 * n - 1).step_by(8) {
            let (mut s, lo) = ([A::default(); 8], (c + 1).saturating_sub(n));
            for i in lo..(c / 2).min(n) {
                let x = ap[N + i] + ap[N + i];
                for (t, &y) in s.iter_mut().zip(&ap[N + c - i..N + c - i + 8]) {
                    *t += x * y;
                }
            }
            for i in (c / 2).max(lo)..(c / 2 + 4).min(n) {
                let x = ap[N + i];
                for ((t, &y), &w) in s.iter_mut().zip(&ap[N + c - i..N + c - i + 8]).zip(&WEIGHTS[2 * i - c]) {
                    *t += A::of(w) * (x * y);
                }
            }
            out[c..c + 8].copy_from_slice(&s);
        }
        acc
    }

    pub fn mul(&self, a: &[T; N], b: &[T; N]) -> [T; N] {
        match &self.rows {
            Rows::W16(r) => self.reduce(&self.product::<u16>(a, b), r),
            Rows::W32(r) => self.reduce(&self.product::<u32>(a, b), r),
            Rows::W64(r) => self.reduce(&self.product::<u64>(a, b), r),
        }
    }

    pub fn sqr(&self, a: &[T; N]) -> [T; N] {
        match &self.rows {
            Rows::W16(r) => self.reduce(&self.square::<u16>(a), r),
            Rows::W32(r) => self.reduce(&self.square::<u32>(a), r),
            Rows::W64(r) => self.reduce(&self.square::<u64>(a), r),
        }
    }

    /// u_i + t v_(i-j) modulo p for i from j to top, over whole aligned
    /// chunks of 8 (the other lanes add zeros: v is 0 above its degree and
    /// PAD zeros lead it). The sums stay below p^2.
    #[inline(always)]
    fn shift_axpy<A: Acc>(&self, u: &mut [A], t: u32, v: &[A], j: usize, top: usize) {
        let (t, lo, hi) = (A::of(t), j & !7, (top + 8) & !7);
        for (x, &y) in u[PAD + lo..PAD + hi].iter_mut().zip(&v[PAD + lo - j..PAD + hi - j]) {
            *x = (*x + t * y).modp(self.b);
        }
    }

    /// u_i + t v_(i-j) + s v_(i-j+1) modulo p for i from j - 1 to top, as
    /// `shift_axpy` for two terms (j >= 1). The sums stay below 2p^2.
    #[inline(always)]
    fn shift_axpy2<A: Acc>(&self, u: &mut [A], t: u32, s: u32, v: &[A], j: usize, top: usize) {
        let (t, s, lo, hi) = (A::of(t), A::of(s), (j - 1) & !7, (top + 8) & !7);
        let (v1, v0) = (&v[PAD + lo - j..PAD + hi - j], &v[PAD + lo + 1 - j..PAD + hi + 1 - j]);
        for ((x, &y), &z) in u[PAD + lo..PAD + hi].iter_mut().zip(v1).zip(v0) {
            *x = (*x + t * y + s * z).modp(self.b);
        }
    }

    /// The inverse of a unit, by the extended Euclidean algorithm on a and
    /// f, two leading terms at a time, in the narrowest lanes 2p^2 fits.
    pub fn inv(&self, a: &[T; N]) -> Option<[T; N]> {
        match self.b.p {
            ..=181 => self.inv_with::<u16>(a),
            ..=46340 => self.inv_with::<u32>(a),
            _ => self.inv_with::<u64>(a),
        }
    }

    #[inline(always)]
    fn inv_with<A: Acc>(&self, a: &[T; N]) -> Option<[T; N]> {
        let (n, p, inv) = (self.n, self.b.p as u32, self.inverses());
        // Remainders u and v with cofactors: gu a = u and gv a = v modulo f.
        // With deg gu + deg v <= n and deg gv + deg u <= n throughout, all
        // have degree at most n. Coefficient i is at PAD + i.
        let (mut r, mut g) = ([[[A::default(); 4]; N]; 2], [[[A::default(); 4]; N]; 2]);
        let ([u, v], [gu, gv]) = (&mut r, &mut g);
        let (mut u, mut v, mut gu, mut gv) = (u.as_flattened_mut(), v.as_flattened_mut(), gu.as_flattened_mut(), gv.as_flattened_mut());
        for i in 0..n {
            (u[PAD + i], v[PAD + i]) = (A::of(a[i].get()), A::of(self.f[i]));
        }
        (v[PAD + n], gu[PAD]) = (A::of(1), A::of(1));
        let (mut du, mut dv, mut eu, mut ev) = (degree_of(&u[PAD..], n as isize - 1), n as isize, 0, -1);
        if du < 0 {
            return None;
        }
        loop {
            if du < dv {
                (u, v, gu, gv) = (v, u, gv, gu);
                (du, dv, eu, ev) = (dv, du, ev, eu);
            }
            if du == 0 {
                break;
            }
            if dv < 0 {
                return None;
            }
            let (j, c) = ((du - dv) as usize, inv[v[PAD + dv as usize].get() as usize].get());
            let t = p - self.b.half(u[PAD + du as usize].get() * c);
            if j == 0 {
                self.shift_axpy(u, t, v, j, du as usize);
                if ev >= 0 {
                    self.shift_axpy(gu, t, gv, j, j + ev as usize);
                    eu = eu.max(ev + j as isize);
                }
                du = degree_of(&u[PAD..], du - 1);
                continue;
            }
            // The next term of the quotient too, from the coefficient of
            // x^(du-1) that the first leaves (v_(dv-1) is a leading zero if
            // dv = 0).
            let r = self.b.half(u[PAD + du as usize - 1].get() + t * v[PAD + dv as usize - 1].get());
            let s = if r == 0 { 0 } else { p - self.b.half(r * c) };
            self.shift_axpy2(u, t, s, v, j, du as usize);
            if ev >= 0 {
                self.shift_axpy2(gu, t, s, gv, j, j + ev as usize);
                eu = eu.max(ev + j as isize);
            }
            du = degree_of(&u[PAD..], du - 2);
        }
        // gu/u, and x^n replaced by its remainder if gu reached degree n.
        let s = A::of(inv[u[PAD].get() as usize].get());
        let top = (gu[PAD + n] * s).modp(self.b).get();
        Some(array::from_fn(|i| if i < n { T::of(self.b.half((gu[PAD + i] * s).modp(self.b).get() + top * self.fneg[i])) } else { T::default() }))
    }

    /// b^e modulo p.
    fn pow_mod(&self, b: u32, mut e: u64) -> u64 {
        let (p, mut b, mut r) = (self.b.p, b as u64, 1);
        while e > 0 {
            if e & 1 == 1 {
                r = r * b % p;
            }
            (b, e) = (b * b % p, e >> 1);
        }
        r
    }

    /// The norm to F_p: the resultant of f and a, by Euclid's algorithm with
    /// Res(A, B) = (-1)^(deg A deg B) lc(B)^(deg A - deg R) Res(B, R) for R
    /// = A mod B, and Res(A, c) = c^deg A for a constant c.
    pub fn norm(&self, a: &[T; N]) -> u64 {
        if self.b.p < 256 { self.norm_with::<u16>(a) } else { self.norm_with::<u32>(a) }
    }

    #[inline(always)]
    fn norm_with<A: Acc>(&self, a: &[T; N]) -> u64 {
        let (n, p, inv) = (self.n, self.b.p as u32, self.inverses());
        let mut r = [[[A::default(); 4]; N]; 2];
        let [x, y] = &mut r;
        let (mut x, mut y) = (x.as_flattened_mut(), y.as_flattened_mut());
        for i in 0..n {
            (x[PAD + i], y[PAD + i]) = (A::of(self.f[i]), A::of(a[i].get()));
        }
        x[PAD + n] = A::of(1);
        let (mut dx, mut dy, mut res) = (n as isize, degree_of(&y[PAD..], n as isize - 1), 1);
        loop {
            if dy < 0 {
                return 0;
            }
            let lc = y[PAD + dy as usize].get();
            if dy == 0 {
                return res * self.pow_mod(lc, dx as u64) % p as u64;
            }
            let (d, li) = (dx, inv[lc as usize].get());
            while dx >= dy {
                let t = p - self.b.half(x[PAD + dx as usize].get() * li);
                self.shift_axpy(x, t, y, (dx - dy) as usize, dx as usize);
                dx = degree_of(&x[PAD..], dx - 1);
            }
            if dx < 0 {
                return 0;
            }
            if d * dy % 2 == 1 {
                res = (p as u64 - res) % p as u64;
            }
            res = res * self.pow_mod(lc, (d - dx) as u64) % p as u64;
            (x, y, dx, dy) = (y, x, dy, dx);
        }
    }

    /// a^e for the exponent with the given words (least significant first),
    /// by sliding windows of up to 4 bits over the odd powers a, a^3, ...,
    /// a^15 once e has more than 16 bits.
    pub fn pow(&self, a: &[T; N], e: &[u64]) -> [T; N] {
        let Some(top) = e.iter().rposition(|&x| x != 0) else { return self.scalar(1) };
        let bits = 64 * top + 64 - e[top].leading_zeros() as usize;
        let bit = |i: usize| (e[i / 64] >> (i % 64) & 1) as usize;
        if bits <= 16 {
            return (0..bits - 1).rev().fold(*a, |r, i| if bit(i) == 1 { self.mul(&self.sqr(&r), a) } else { self.sqr(&r) });
        }
        let a2 = self.sqr(a);
        let mut odd = [*a; 8];
        for i in 1..8 {
            odd[i] = self.mul(&odd[i - 1], &a2);
        }
        // The top bit is set, so the first window starts the result.
        let (mut r, mut i) = (None, bits as isize - 1);
        while i >= 0 {
            if bit(i as usize) == 0 {
                r = r.map(|x| self.sqr(&x));
                i -= 1;
                continue;
            }
            let mut j = (i - 3).max(0);
            while bit(j as usize) == 0 {
                j += 1;
            }
            let w = (j..=i).rev().fold(0, |w, t| w << 1 | bit(t as usize));
            r = Some(match r {
                None => odd[w >> 1],
                Some(x) => self.mul(&(j..=i).fold(x, |x, _| self.sqr(&x)), &odd[w >> 1]),
            });
            i = j - 1;
        }
        r.unwrap()
    }

    /// a^p, from the rows of the Frobenius.
    #[inline(always)]
    fn frobenius_with<A: Acc>(&self, a: &[T; N]) -> [T; N] {
        let (n, m) = (self.n, self.m);
        let mut acc = [A::default(); N];
        for (x, row) in a[..n].iter().zip(&self.frob) {
            let x = A::of(x.get());
            for (r, y) in acc[..m].chunks_exact_mut(8).zip(row[..m].chunks_exact(8)) {
                for (r, &y) in r.iter_mut().zip(y) {
                    *r += x * A::of(y);
                }
            }
        }
        array::from_fn(|i| if i < n { T::of(acc[i].modp(self.b).get()) } else { T::default() })
    }

    /// a^(p^k).
    pub fn frobenius(&self, a: &[T; N], k: u64) -> [T; N] {
        (0..k % self.n as u64).fold(*a, |x, _| match self.rows {
            Rows::W16(_) => self.frobenius_with::<u16>(&x),
            Rows::W32(_) => self.frobenius_with::<u32>(&x),
            Rows::W64(_) => self.frobenius_with::<u64>(&x),
        })
    }

    /// The trace to F_p.
    pub fn trace(&self, a: &[T; N]) -> u64 {
        self.b.word(a[..self.n].iter().zip(&self.tr).map(|(x, &t)| x.get() as u64 * t as u64).sum())
    }

    /// The n coordinates.
    pub fn coords(&self, a: &[T; N]) -> Vec<u64> {
        a[..self.n].iter().map(|x| x.get() as u64).collect()
    }

    /// The element with the given coordinates (missing ones are zero).
    pub fn from_coords(&self, c: &[u64]) -> [T; N] {
        let mut r = self.zero();
        for (x, &v) in r.iter_mut().zip(c).take(self.n) {
            *x = T::of((v % self.b.p) as u32);
        }
        r
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Integer;
    use crate::gr::{conway_polynomial, is_irreducible_mod_p};

    struct Lcg(u64);

    impl Lcg {
        fn next(&mut self) -> u64 {
            self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            self.0 ^ self.0 >> 29
        }
    }

    /// a*b modulo f (its coefficients below x^n) and p, the slow way.
    fn mulmod_naive(p: u64, f: &[u64], a: &[u64], b: &[u64]) -> Vec<u64> {
        let n = f.len();
        let mut c = vec![0u64; 2 * n];
        for i in 0..n {
            for j in 0..n {
                c[i + j] = (c[i + j] + a[i] * b[j]) % p;
            }
        }
        for k in (n..2 * n).rev() {
            let t = std::mem::take(&mut c[k]);
            for i in 0..n {
                c[k - n + i] = (c[k - n + i] + t * (p - f[i])) % p;
            }
        }
        c.truncate(n);
        c
    }

    /// The coefficients below x^n of a monic irreducible polynomial of
    /// degree n over F_p: Conway's if known, else a random one.
    fn modulus(p: u64, n: usize, rng: &mut Lcg) -> Vec<u64> {
        if let Some(c) = conway_polynomial(p, n as u64) {
            return c[..n].iter().map(|x| x.to_u64().unwrap()).collect();
        }
        for _ in 0..100 * n {
            let f: Vec<u64> = (0..n).map(|_| rng.next() % p).collect();
            let ints: Vec<Integer> = f.iter().chain(&[1]).map(|&c| Integer::from_u64(c)).collect();
            if is_irreducible_mod_p(&Integer::from_u64(p), &ints) {
                return f;
            }
        }
        panic!("no irreducible of degree {n} over F_{p}");
    }

    fn lanes_agree<T: Lane, const N: usize>(p: u64, f: &[u64], rng: &mut Lcg) {
        let (k, n) = (FpLanes::<T, N>::new(p, f), f.len());
        let q = Integer::from_u64(p).pow(n as u64);
        let qm1 = &q - &Integer::one();
        let (e_unit, e_norm) = (qm1.to_limbs(), qm1.divexact(&Integer::from_u64(p - 1)).to_limbs());
        let (zero, one) = (k.zero(), k.scalar(1));
        let rand = |rng: &mut Lcg| -> Vec<u64> { (0..n).map(|_| rng.next() % p).collect() };
        for i in 0..20 {
            let (ca, cb) = (rand(rng), if i == 0 { vec![0; n] } else { rand(rng) });
            let (a, b) = (k.from_coords(&ca), k.from_coords(&cb));
            assert_eq!(k.coords(&a), ca);
            assert_eq!(k.coords(&k.mul(&a, &b)), mulmod_naive(p, f, &ca, &cb), "{p} {n}");
            assert_eq!(k.sqr(&a), k.mul(&a, &a));
            assert_eq!(k.add(&k.sub(&a, &b), &b), a);
            assert_eq!(k.add(&a, &k.neg(&a)), zero);
            let c = rng.next() % p;
            assert_eq!(k.mul_scalar(&a, c), k.mul(&a, &k.scalar(c)));
            if a != zero {
                assert_eq!(k.mul(&a, &k.inv(&a).unwrap()), one);
                assert_eq!(k.pow(&a, &e_unit), one);
            }
            assert_eq!(k.scalar(k.norm(&a)), k.pow(&a, &e_norm));
            assert_eq!(k.norm(&k.mul(&a, &b)), k.norm(&a) * k.norm(&b) % p);
            for j in [0, 1, 2, n as u64 - 1, n as u64 + 1] {
                assert_eq!(k.frobenius(&a, j), k.pow(&a, &Integer::from_u64(p).pow(j % n as u64).to_limbs()));
            }
            let conjugates = (0..n as u64).fold(zero, |s, j| k.add(&s, &k.frobenius(&a, j)));
            assert_eq!(conjugates, k.scalar(k.trace(&a)));
        }
        assert_eq!((k.inv(&zero), k.norm(&zero)), (None, 0));
        let x = k.generator();
        let fx = (0..n).fold(k.pow(&x, &[n as u64]), |s, i| k.add(&s, &k.mul_scalar(&k.pow(&x, &[i as u64]), f[i])));
        assert_eq!(fx, zero);
    }

    fn check(p: u64, n: usize, rng: &mut Lcg) {
        let f = modulus(p, n, rng);
        match (p < 256, n) {
            (true, 1..=16) => lanes_agree::<u8, 16>(p, &f, rng),
            (true, 17..=32) => lanes_agree::<u8, 32>(p, &f, rng),
            (true, _) => lanes_agree::<u8, 64>(p, &f, rng),
            (false, 1..=8) => lanes_agree::<u16, 8>(p, &f, rng),
            (false, 9..=16) => lanes_agree::<u16, 16>(p, &f, rng),
            (false, _) => lanes_agree::<u16, 32>(p, &f, rng),
        }
    }

    #[test]
    fn lanes_agree_with_naive_arithmetic() {
        let mut rng = Lcg(0x243f_6a88_85a3_08d3);
        for n in [1, 2, 3, 13, 16, 17, 32, 40, 64] {
            check(3, n, &mut rng);
        }
        for (p, n) in [(5, 7), (7, 30), (7, 33), (127, 2), (251, 5), (251, 64)] {
            check(p, n, &mut rng);
        }
        for (p, n) in [(257, 1), (257, 2), (257, 32), (1009, 9), (32003, 16), (65521, 2), (65521, 8), (65521, 17), (65521, 32)] {
            check(p, n, &mut rng);
        }
    }
}
