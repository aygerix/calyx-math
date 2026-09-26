//! Magma's monomial orders.
//!
//! The nine orders of the handbook section "Representation and Monomial
//! Orders". Variables are numbered from 0 here, where Magma's tuples and
//! messages number them from 1. Every order is also given by weight vectors
//! (`weight_vectors`, the rows of MonomialOrderWeightVectors), but the
//! comparisons work on the exponents directly.
//!
//! lex, glex and grevlex are FLINT's own orders, so polynomials in those
//! orders are stored sorted; the others are stored in lex order and sorted
//! with `Order::cmp` where the order matters.

use std::cmp::Ordering;
use std::fmt::Display;
use std::hash::{Hash, Hasher};

use calyx_flint::gr::MonomialOrder;
use calyx_flint::{Integer, Rational};

/// A monomial order. The rank is not stored: comparisons take it from the
/// exponent vectors.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Order {
    /// `lex`: the first variable is the greatest.
    Lex,
    /// `glex`: total degree, then lex.
    GLex,
    /// `grevlex`: total degree, then the monomial with the smaller exponent
    /// in the last variable where they differ is the greater.
    GRevLex,
    /// `grevlexw W`: the degree weighted by the positive weights `W`, then
    /// as grevlex.
    GRevLexW(Vec<u64>),
    /// `elim k`: grevlex on the first k variables, then on the others.
    ElimK(usize),
    /// `elim U V`: grevlex on the variables in `U`, in that order, then on
    /// those in `V`. `invblock U V` is `elim V U`, as in Magma.
    Elim(Vec<usize>, Vec<usize>),
    /// `univ i`: grevlex on the variables other than the i-th, then the
    /// exponent of the i-th.
    Univ(usize),
    /// `weight Q`: the dot products with the rows of `Q` in turn.
    Weight(Weights),
}

/// The rows of a weight order: linearly independent, primitive vectors of
/// non-negative integers, with a word-sized copy when they fit.
#[derive(Clone, Debug)]
pub struct Weights {
    rows: Vec<Vec<Integer>>,
    words: Option<Vec<Vec<u64>>>,
}

impl Weights {
    /// The weights `rows`, which the caller has checked (as `Order::parse`
    /// does).
    pub fn new(rows: Vec<Vec<Integer>>) -> Weights {
        let words = rows.iter().map(|r| r.iter().map(Integer::to_u64).collect::<Option<Vec<u64>>>()).collect();
        Weights { rows, words }
    }

    pub fn rows(&self) -> &[Vec<Integer>] {
        &self.rows
    }

    fn cmp<E: Copy + Into<u64>>(&self, a: &[E], b: &[E]) -> Ordering {
        for (k, row) in self.rows.iter().enumerate() {
            let small = self.words.as_ref().and_then(|w| Some((dot_words(&w[k], a)?, dot_words(&w[k], b)?)));
            let o = match small {
                Some((x, y)) => x.cmp(&y),
                None => dot(row, a).cmp(&dot(row, b)),
            };
            if o.is_ne() {
                return o;
            }
        }
        Ordering::Equal
    }
}

impl PartialEq for Weights {
    fn eq(&self, other: &Weights) -> bool {
        self.rows == other.rows
    }
}

impl Eq for Weights {}

impl Hash for Weights {
    fn hash<H: Hasher>(&self, h: &mut H) {
        self.rows.hash(h)
    }
}

/// `row . e`, unless it overflows.
fn dot_words<E: Copy + Into<u64>>(row: &[u64], e: &[E]) -> Option<u128> {
    row.iter().zip(e).try_fold(0u128, |s, (&w, &x)| s.checked_add(w as u128 * x.into() as u128))
}

fn dot<E: Copy + Into<u64>>(row: &[Integer], e: &[E]) -> Integer {
    let mut s = Integer::zero();
    for (w, &x) in row.iter().zip(e) {
        let mut t = Integer::from_u64(x.into());
        t *= w;
        s += &t;
    }
    s
}

fn lex<E: Copy + Into<u64>>(a: &[E], b: &[E]) -> Ordering {
    a.iter().zip(b).map(|(&x, &y)| x.into().cmp(&y.into())).find(|o| o.is_ne()).unwrap_or(Ordering::Equal)
}

/// The degree in the variables `vars`.
fn degree<E: Copy + Into<u64>>(e: &[E], vars: impl Iterator<Item = usize>) -> u128 {
    vars.map(|i| e[i].into() as u128).sum()
}

/// The tie-break of grevlex on `vars`: the smaller exponent in the last
/// variable where they differ wins.
fn revlex<E: Copy + Into<u64>>(a: &[E], b: &[E], vars: impl DoubleEndedIterator<Item = usize>) -> Ordering {
    vars.rev().map(|i| b[i].into().cmp(&a[i].into())).find(|o| o.is_ne()).unwrap_or(Ordering::Equal)
}

/// grevlex on the variables `vars`, taken in that order.
fn grevlex<E: Copy + Into<u64>>(a: &[E], b: &[E], vars: impl DoubleEndedIterator<Item = usize> + Clone) -> Ordering {
    degree(a, vars.clone()).cmp(&degree(b, vars.clone())).then_with(|| revlex(a, b, vars))
}

fn join<T: Display>(it: impl Iterator<Item = T>) -> String {
    it.map(|x| x.to_string()).collect::<Vec<_>>().join(", ")
}

impl Order {
    /// Compare two exponent vectors of the same length.
    pub fn cmp<E: Copy + Into<u64>>(&self, a: &[E], b: &[E]) -> Ordering {
        debug_assert_eq!(a.len(), b.len());
        let n = a.len();
        match self {
            Order::Lex => lex(a, b),
            Order::GLex => degree(a, 0..n).cmp(&degree(b, 0..n)).then_with(|| lex(a, b)),
            Order::GRevLex => grevlex(a, b, 0..n),
            Order::GRevLexW(w) => {
                let wdeg = |e: &[E]| w.iter().zip(e).map(|(&w, &x)| w as u128 * x.into() as u128).sum::<u128>();
                wdeg(a).cmp(&wdeg(b)).then_with(|| revlex(a, b, 0..n))
            }
            Order::ElimK(k) => grevlex(a, b, 0..*k).then_with(|| grevlex(a, b, *k..n)),
            Order::Elim(u, v) => grevlex(a, b, u.iter().copied()).then_with(|| grevlex(a, b, v.iter().copied())),
            Order::Univ(i) => grevlex(a, b, (0..n).filter(|j| j != i)).then_with(|| a[*i].into().cmp(&b[*i].into())),
            Order::Weight(w) => w.cmp(a, b),
        }
    }

    /// Whether FLINT's polynomials keep their terms in this order.
    pub fn is_native(&self) -> bool {
        matches!(self, Order::Lex | Order::GLex | Order::GRevLex)
    }

    /// The order FLINT stores the terms in: this order if it is native,
    /// lex otherwise.
    pub fn storage(&self) -> MonomialOrder {
        match self {
            Order::GLex => MonomialOrder::DegLex,
            Order::GRevLex => MonomialOrder::DegRevLex,
            _ => MonomialOrder::Lex,
        }
    }

    /// The weight vectors of the order on `n` variables, as
    /// MonomialOrderWeightVectors gives them: the order compares the dot
    /// products with these rows in turn.
    pub fn weight_vectors(&self, n: usize) -> Vec<Vec<Integer>> {
        if let Order::Weight(w) = self {
            return w.rows.clone();
        }
        let unit = |i: usize| (0..n).map(|j| (i == j) as u64).collect::<Vec<u64>>();
        // grevlex on `vars`: the sum of all of them, then of all but the last, and so on.
        let block = |rows: &mut Vec<Vec<u64>>, vars: &[usize]| {
            for k in (1..=vars.len()).rev() {
                let mut r = vec![0; n];
                vars[..k].iter().for_each(|&i| r[i] = 1);
                rows.push(r);
            }
        };
        let all: Vec<usize> = (0..n).collect();
        let mut rows = Vec::with_capacity(n);
        match self {
            Order::Lex => rows.extend((0..n).map(unit)),
            Order::GLex => {
                rows.push(vec![1; n]);
                rows.extend((0..n.saturating_sub(1)).map(unit));
            }
            Order::GRevLex => block(&mut rows, &all),
            Order::GRevLexW(w) => rows.extend((1..=n).rev().map(|k| (0..n).map(|i| if i < k { w[i] } else { 0 }).collect())),
            Order::ElimK(k) => {
                block(&mut rows, &all[..*k]);
                block(&mut rows, &all[*k..]);
            }
            Order::Elim(u, v) => {
                block(&mut rows, u);
                block(&mut rows, v);
            }
            Order::Univ(i) => {
                block(&mut rows, &(0..n).filter(|j| j != i).collect::<Vec<_>>());
                rows.push(unit(*i));
            }
            Order::Weight(_) => unreachable!(),
        }
        rows.into_iter().map(|r| r.into_iter().map(Integer::from_u64).collect()).collect()
    }

    /// The tuple MonomialOrder returns: the name and the arguments, with the
    /// variables numbered from 1. The sequences hold integers.
    pub fn tuple(&self) -> (&'static str, Vec<OrderArg>) {
        let int = |k: usize| OrderArg::Int(Integer::from_u64(k as u64));
        let seq = |it: &mut dyn Iterator<Item = Integer>| OrderArg::Seq(it.map(|x| Rational::from_integer(&x)).collect());
        let vars = |v: &[usize]| seq(&mut v.iter().map(|&i| Integer::from_u64(i as u64 + 1)));
        match self {
            Order::Lex => ("lex", vec![]),
            Order::GLex => ("glex", vec![]),
            Order::GRevLex => ("grevlex", vec![]),
            Order::GRevLexW(w) => ("grevlexw", vec![seq(&mut w.iter().map(|&x| Integer::from_u64(x)))]),
            Order::ElimK(k) => ("elim", vec![int(*k)]),
            Order::Elim(u, v) => ("elim", vec![vars(u), vars(v)]),
            Order::Univ(i) => ("univ", vec![int(i + 1)]),
            Order::Weight(w) => ("weight", vec![seq(&mut w.rows.iter().flatten().cloned())]),
        }
    }

    /// What Magma prints after "Order: " for a ring with this order.
    pub fn describe(&self) -> String {
        match self {
            Order::Lex => "Lexicographical".into(),
            Order::GLex => "Graded Lexicographical".into(),
            Order::GRevLex => "Graded Reverse Lexicographical".into(),
            Order::GRevLexW(w) => format!("Grevlex with weights [{}]", join(w.iter())),
            Order::ElimK(k) => format!("Elimination ({k})"),
            Order::Elim(u, v) => format!("Elimination [{}], [{}]", join(u.iter().map(|i| i + 1)), join(v.iter().map(|i| i + 1))),
            Order::Univ(i) => format!("Univariate ({})", i + 1),
            Order::Weight(_) => "Weight [full]".into(),
        }
    }

    /// The largest weight Magma allows in a grevlexw order on `n` variables.
    pub fn max_grevlexw_weight(n: usize) -> u64 {
        const MAX: u64 = i32::MAX as u64;
        if n <= 1 { MAX } else { MAX / (2000 * n as u64) }
    }

    /// The order named `name` (in any case) with the arguments `args`, on `n`
    /// variables: the order of PolynomialRing(R, n, name, args...).
    pub fn parse(n: usize, name: &str, args: &[OrderArg]) -> Result<Order, OrderError> {
        use OrderArg::{Int, Seq};
        match (name.to_ascii_lowercase().as_str(), args) {
            ("lex", []) => Ok(Order::Lex),
            ("glex", []) => Ok(Order::GLex),
            ("grevlex", []) => Ok(Order::GRevLex),
            ("grevlexw", [w]) => {
                let w = entries(w, n)?;
                if w.iter().any(|x| x.sign() <= 0) {
                    return Err(OrderError::NotPositive { arg: 0 });
                }
                let max = Order::max_grevlexw_weight(n);
                let w = primitive(w).iter().map(|x| x.to_u64().filter(|&x| x <= max)).collect::<Option<Vec<u64>>>();
                Ok(Order::GRevLexW(w.ok_or(OrderError::WeightTooLarge)?))
            }
            ("elim", [Int(k)]) => Ok(Order::ElimK(in_range(k, 0, 1, n as i64 - 1)? as usize)),
            ("elim" | "invblock", [Seq(u)]) => {
                let u = variables(u, 0, n)?;
                let v = (0..n).filter(|i| !u.contains(i)).collect();
                Ok(if name.eq_ignore_ascii_case("elim") { Order::Elim(u, v) } else { Order::Elim(v, u) })
            }
            ("elim" | "invblock", [Seq(u), Seq(v)]) => {
                let u = variables(u, 0, n)?;
                if v.len() != n - u.len() {
                    return Err(OrderError::Length { arg: 1, len: n - u.len() });
                }
                let v = vars(v, n).filter(|v| v.iter().all(|i| !u.contains(i))).ok_or(OrderError::NotComplement { arg: 1, n })?;
                Ok(if name.eq_ignore_ascii_case("elim") { Order::Elim(u, v) } else { Order::Elim(v, u) })
            }
            ("univ", [Int(i)]) => Ok(Order::Univ(in_range(i, 0, 1, n as i64)? as usize - 1)),
            ("univ", [_]) => Err(OrderError::NotInteger),
            ("weight", [q]) => {
                let q = entries(q, n * n)?;
                if q.iter().any(|x| x.sign() < 0) {
                    return Err(OrderError::Negative { arg: 0 });
                }
                let rows: Vec<Vec<Integer>> = q.chunks(n).map(primitive).collect();
                if !independent(&rows) {
                    return Err(OrderError::Dependent { arg: 0 });
                }
                Ok(Order::Weight(Weights::new(rows)))
            }
            _ => Err(OrderError::Bad { name: name.to_string(), args: !args.is_empty() }),
        }
    }
}

impl From<MonomialOrder> for Order {
    fn from(o: MonomialOrder) -> Order {
        match o {
            MonomialOrder::Lex => Order::Lex,
            MonomialOrder::DegLex => Order::GLex,
            MonomialOrder::DegRevLex => Order::GRevLex,
        }
    }
}

/// An argument of an order, as the interpreter passes it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OrderArg {
    Int(Integer),
    /// A sequence of integers or rationals.
    Seq(Vec<Rational>),
    /// Anything else.
    Other,
}

/// Why `Order::parse` refused its arguments. The argument numbers count
/// from 0 at the first argument after the name.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OrderError {
    /// An unknown order, or the wrong number or kinds of arguments.
    Bad { name: String, args: bool },
    Range { arg: usize, value: Integer, lo: i64, hi: i64 },
    TooLarge { arg: usize, value: Integer },
    /// Not distinct variable numbers.
    NotVariables { arg: usize, n: usize },
    /// Not distinct variable numbers, disjoint from the previous argument.
    NotComplement { arg: usize, n: usize },
    Length { arg: usize, len: usize },
    TooLong { arg: usize, len: usize, n: usize },
    Empty { arg: usize },
    /// Not a sequence of `len` numbers.
    NotSequence { arg: usize, len: usize },
    NotPositive { arg: usize },
    Negative { arg: usize },
    Dependent { arg: usize },
    WeightTooLarge,
    NotInteger,
}

impl OrderError {
    /// Magma's message, with the arguments numbered from `first` at the one
    /// after the name (4 for PolynomialRing(R, n, name, ...)).
    pub fn message(&self, first: usize) -> String {
        match self {
            OrderError::Bad { name, args } => format!("Bad order \"{name}\"{}", if *args { ", ..." } else { "" }),
            OrderError::Range { arg, value, lo, hi } => format!("Argument {} ({value}) should be in the range [{lo} .. {hi}]", first + arg),
            OrderError::TooLarge { arg, value } => format!("Argument {} ({value}) is too large", first + arg),
            OrderError::NotVariables { arg, n } => format!("Argument {} is not a sequence of distinct integers in the range [ 1 .. {n} ]", first + arg),
            OrderError::NotComplement { arg, n } => {
                let (k, u) = (first + arg, first + arg - 1);
                format!("Argument {k} is not a sequence of distinct integers in the range [1 .. {n}] and distinct from argument {u}")
            }
            OrderError::Length { arg, len } => format!("Argument {} must have length {len}", first + arg),
            OrderError::TooLong { arg, len, n } => format!("Length of argument {} ({len}) must be less than {n}", first + arg),
            OrderError::Empty { arg } => format!("Sequence argument {} must be non-empty", first + arg),
            OrderError::NotSequence { arg, len } => format!("Order argument {} must be a sequence of {len} integers or rationals", first + arg),
            OrderError::NotPositive { arg } => format!("Entries of argument {} are not positive", first + arg),
            OrderError::Negative { arg } => format!("Entries of argument {} are not non-negative", first + arg),
            OrderError::Dependent { arg } => format!("Weight vectors of argument {} are not independent", first + arg),
            OrderError::WeightTooLarge => "Weight is too large".into(),
            OrderError::NotInteger => "Integer must be given for variable".into(),
        }
    }
}

/// The `len` numbers of the argument `a` (the first after the name).
fn entries(a: &OrderArg, len: usize) -> Result<&[Rational], OrderError> {
    match a {
        OrderArg::Seq(q) if q.len() == len => Ok(q),
        _ => Err(OrderError::NotSequence { arg: 0, len }),
    }
}

/// The integer `k`, argument `arg`, if it lies in `lo..=hi`.
fn in_range(k: &Integer, arg: usize, lo: i64, hi: i64) -> Result<i64, OrderError> {
    match k.to_i64().filter(|k| k.unsigned_abs() < 1 << 30) {
        None => Err(OrderError::TooLarge { arg, value: k.clone() }),
        Some(v) if v < lo || v > hi => Err(OrderError::Range { arg, value: k.clone(), lo, hi }),
        Some(v) => Ok(v),
    }
}

/// Distinct variable numbers in 1..=n, made 0-based.
fn vars(v: &[Rational], n: usize) -> Option<Vec<usize>> {
    let mut out: Vec<usize> = Vec::with_capacity(v.len());
    for x in v {
        let i = x.is_integral().then(|| x.numerator().to_u64()).flatten().filter(|&i| i >= 1 && i <= n as u64)? as usize - 1;
        if out.contains(&i) {
            return None;
        }
        out.push(i);
    }
    Some(out)
}

/// The first block of an elimination order: distinct variables, but not all
/// of them (Magma checks the length first).
fn variables(v: &[Rational], arg: usize, n: usize) -> Result<Vec<usize>, OrderError> {
    if v.is_empty() {
        return Err(OrderError::Empty { arg });
    }
    if v.len() >= n {
        return Err(OrderError::TooLong { arg, len: v.len(), n });
    }
    vars(v, n).ok_or(OrderError::NotVariables { arg, n })
}

/// The primitive integer vector with the direction of `row` (which is
/// non-negative).
fn primitive(row: &[Rational]) -> Vec<Integer> {
    let den = row.iter().fold(Integer::one(), |l, x| l.lcm(&x.denominator()));
    let mut ints: Vec<Integer> = row
        .iter()
        .map(|x| {
            let mut t = x.numerator();
            t *= &den.divexact(&x.denominator());
            t
        })
        .collect();
    let g = ints.iter().fold(Integer::zero(), |g, x| g.gcd(x));
    if !g.is_zero() && !g.is_one() {
        ints.iter_mut().for_each(|x| *x = x.divexact(&g));
    }
    ints
}

/// Whether the rows are linearly independent (fraction-free elimination).
fn independent(rows: &[Vec<Integer>]) -> bool {
    let mut m = rows.to_vec();
    let cols = m.first().map_or(0, Vec::len);
    let mut rank = 0;
    for c in 0..cols {
        let Some(p) = (rank..m.len()).find(|&r| !m[r][c].is_zero()) else { continue };
        m.swap(rank, p);
        for r in rank + 1..m.len() {
            if m[r][c].is_zero() {
                continue;
            }
            let (a, b) = (m[rank][c].clone(), m[r][c].clone());
            for j in c..cols {
                let mut y = m[rank][j].clone();
                y *= &b;
                m[r][j] *= &a;
                m[r][j] -= &y;
            }
        }
        rank += 1;
    }
    rank == m.len()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn next(s: &mut u64) -> u64 {
        *s ^= *s << 13;
        *s ^= *s >> 7;
        *s ^= *s << 17;
        *s
    }

    fn ints(v: &[i64]) -> Vec<Rational> {
        v.iter().map(|&x| Rational::from_i64(x)).collect()
    }

    fn rat(p: i64, q: i64) -> Rational {
        Rational::new(&Integer::from_i64(p), &Integer::from_i64(q)).unwrap()
    }

    fn parse(n: usize, name: &str, args: &[OrderArg]) -> Order {
        Order::parse(n, name, args).unwrap()
    }

    fn error(n: usize, name: &str, args: &[OrderArg]) -> String {
        Order::parse(n, name, args).unwrap_err().message(4)
    }

    fn some_orders() -> Vec<Order> {
        let matrix = |rows: [[i128; 4]; 4]| rows.iter().map(|r| r.iter().map(|&x| Integer::from_i128(x)).collect()).collect();
        let w = matrix([[100, 10, 1, 0], [1, 10, 100, 0], [0, 0, 0, 1], [1, 1, 1, 1]]);
        // Entries beyond a word take the multiprecision path.
        let huge = matrix([[1 << 70, 1, 0, 0], [0, 1 << 66, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]);
        vec![
            Order::Lex,
            Order::GLex,
            Order::GRevLex,
            Order::GRevLexW(vec![2, 3, 1, 5]),
            Order::ElimK(1),
            Order::ElimK(2),
            Order::ElimK(3),
            Order::Elim(vec![2, 0], vec![1, 3]),
            Order::Elim(vec![3], vec![1, 0, 2]),
            Order::Univ(0),
            Order::Univ(1),
            Order::Univ(3),
            Order::Weight(Weights::new(w)),
            Order::Weight(Weights::new(huge)),
        ]
    }

    #[test]
    fn comparisons_agree_with_the_weight_vectors() {
        let mut s = 0x9e3779b97f4a7c15;
        for o in some_orders() {
            let rows = o.weight_vectors(4);
            assert_eq!(rows.len(), 4, "{o:?}");
            let key = |e: &[u32]| rows.iter().map(|r| dot(r, e)).collect::<Vec<Integer>>();
            for _ in 0..2000 {
                let a: Vec<u32> = (0..4).map(|_| (next(&mut s) % 4) as u32).collect();
                let b: Vec<u32> = (0..4).map(|_| (next(&mut s) % 4) as u32).collect();
                assert_eq!(o.cmp(&a, &b), key(&a).cmp(&key(&b)), "{o:?} {a:?} {b:?}");
            }
        }
    }

    #[test]
    fn orders_are_monomial_orders() {
        let mut s = 0x2545f4914f6cdd1d;
        for o in some_orders() {
            for _ in 0..1000 {
                let [a, b, c]: [Vec<u64>; 3] = std::array::from_fn(|_| (0..4).map(|_| next(&mut s) % 5).collect());
                let add = |x: &[u64], y: &[u64]| x.iter().zip(y).map(|(p, q)| p + q).collect::<Vec<u64>>();
                assert_eq!(o.cmp(&a, &b), o.cmp(&add(&a, &c), &add(&b, &c)), "{o:?}");
                assert_ne!(o.cmp(&[0; 4], &a), Ordering::Greater, "{o:?}");
                assert_eq!(o.cmp(&a, &b), o.cmp(&b, &a).reverse());
            }
        }
    }

    #[test]
    fn handbook_examples_sort_as_printed() {
        let sorted = |o: &Order, mut v: Vec<Vec<u32>>| {
            v.sort_by(|a, b| o.cmp(b, a));
            v
        };
        // elim [1, 4], [2, 3]: a + d^10 + b + c^10 prints as d^10 + a + c^10 + b.
        let o = parse(4, "elim", &[OrderArg::Seq(ints(&[1, 4])), OrderArg::Seq(ints(&[2, 3]))]);
        let m = sorted(&o, vec![vec![1, 0, 0, 0], vec![0, 0, 0, 10], vec![0, 1, 0, 0], vec![0, 0, 10, 0]]);
        assert_eq!(m, [[0, 0, 0, 10], [1, 0, 0, 0], [0, 0, 10, 0], [0, 1, 0, 0]]);
        let rows = |o: &Order, n| o.weight_vectors(n).iter().map(|r| r.iter().map(|x| x.to_i64().unwrap()).collect::<Vec<_>>()).collect::<Vec<_>>();
        assert_eq!(rows(&o, 4), [[1, 0, 0, 1], [1, 0, 0, 0], [0, 1, 1, 0], [0, 1, 0, 0]]);
        assert_eq!(rows(&Order::GRevLex, 4), [[1, 1, 1, 1], [1, 1, 1, 0], [1, 1, 0, 0], [1, 0, 0, 0]]);
        assert_eq!(rows(&Order::Lex, 3), [[1, 0, 0], [0, 1, 0], [0, 0, 1]]);
        // weight [100,10,1, 1,10,100, 1,1,1]: the terms of (x + y^2 + z^3)^4.
        let o = parse(3, "weight", &[OrderArg::Seq(ints(&[100, 10, 1, 1, 10, 100, 1, 1, 1]))]);
        let terms = (0..=4u32).flat_map(|i| (0..=4 - i).map(move |j| vec![i, 2 * j, 3 * (4 - i - j)])).collect();
        let printed = [[4, 0, 0], [3, 2, 0], [3, 0, 3], [2, 4, 0], [2, 2, 3], [2, 0, 6], [1, 6, 0], [1, 4, 3], [1, 2, 6], [1, 0, 9]];
        let printed: Vec<[u32; 3]> = printed.into_iter().chain([[0, 8, 0], [0, 6, 3], [0, 4, 6], [0, 2, 9], [0, 0, 12]]).collect();
        assert_eq!(sorted(&o, terms), printed.iter().map(|m| m.to_vec()).collect::<Vec<_>>());
        assert_eq!(rows(&o, 3), [[100, 10, 1], [1, 10, 100], [1, 1, 1]]);
    }

    #[test]
    fn parsing_normalizes_as_magma_does() {
        use OrderArg::{Int, Seq};
        assert_eq!(parse(3, "LEX", &[]), Order::Lex);
        assert_eq!(parse(3, "Grevlex", &[]), Order::GRevLex);
        assert_eq!(parse(3, "grevlexw", &[Seq(vec![rat(1, 2), rat(1, 1), rat(1, 1)])]), Order::GRevLexW(vec![1, 2, 2]));
        assert_eq!(parse(3, "grevlexw", &[Seq(ints(&[3, 6, 9]))]), Order::GRevLexW(vec![1, 2, 3]));
        assert_eq!(parse(4, "elim", &[Int(Integer::from_i64(2))]), Order::ElimK(2));
        assert_eq!(parse(4, "elim", &[Seq(ints(&[3, 1]))]), Order::Elim(vec![2, 0], vec![1, 3]));
        assert_eq!(parse(4, "invblock", &[Seq(ints(&[1, 4])), Seq(ints(&[2, 3]))]), Order::Elim(vec![1, 2], vec![0, 3]));
        assert_eq!(parse(4, "invblock", &[Seq(ints(&[3]))]), Order::Elim(vec![0, 1, 3], vec![2]));
        assert_eq!(parse(4, "univ", &[Int(Integer::from_i64(2))]), Order::Univ(1));
        let w = parse(3, "weight", &[Seq(ints(&[2, 4, 0, 0, 3, 6, 0, 0, 5]))]);
        assert_eq!(w.tuple(), ("weight", vec![Seq(ints(&[1, 2, 0, 0, 1, 2, 0, 0, 1]))]));
        let w = parse(3, "weight", &[Seq(vec![rat(1, 2), rat(1, 3), rat(0, 1), rat(0, 1), rat(2, 3), rat(0, 1), rat(0, 1), rat(0, 1), rat(7, 4)])]);
        assert_eq!(w.tuple(), ("weight", vec![Seq(ints(&[3, 2, 0, 0, 1, 0, 0, 0, 1]))]));
        let big = Integer::from_i64(1 << 40);
        assert!(matches!(parse(2, "weight", &[Seq(vec![Rational::from_integer(&big), rat(1, 1), rat(0, 1), rat(1, 1)])]), Order::Weight(_)));
        assert_eq!(Order::Elim(vec![1, 2], vec![0, 3]).tuple(), ("elim", vec![Seq(ints(&[2, 3])), Seq(ints(&[1, 4]))]));
        assert_eq!(Order::ElimK(2).tuple(), ("elim", vec![Int(Integer::from_i64(2))]));
        assert_eq!(Order::Univ(1).tuple(), ("univ", vec![Int(Integer::from_i64(2))]));
        assert_eq!(Order::GRevLexW(vec![1, 2, 3]).describe(), "Grevlex with weights [1, 2, 3]");
        assert_eq!(Order::Elim(vec![1], vec![2, 0]).describe(), "Elimination [2], [3, 1]");
        assert_eq!(Order::ElimK(1).describe(), "Elimination (1)");
        assert_eq!(Order::Univ(1).describe(), "Univariate (2)");
        assert_eq!(w.describe(), "Weight [full]");
        assert_eq!(Order::max_grevlexw_weight(1), (1 << 31) - 1);
        assert_eq!([2, 3, 6, 20].map(Order::max_grevlexw_weight), [536870, 357913, 178956, 53687]);
        assert!(!w.is_native() && Order::GLex.is_native());
        assert_eq!(Order::GRevLex.storage(), MonomialOrder::DegRevLex);
        assert_eq!(Order::Univ(0).storage(), MonomialOrder::Lex);
    }

    const NOT_COMPLEMENT: &str = "Argument 5 is not a sequence of distinct integers in the range [1 .. 3] and distinct from argument 4";

    #[test]
    fn parsing_reports_magma_errors() {
        use OrderArg::{Int, Other, Seq};
        let int = |k: i64| Int(Integer::from_i64(k));
        let cases: Vec<(usize, &str, Vec<OrderArg>, &str)> = vec![
            (3, "foo", vec![], "Bad order \"foo\""),
            (3, "elim", vec![], "Bad order \"elim\""),
            (3, "elim", vec![Other], "Bad order \"elim\", ..."),
            (3, "lex", vec![int(2)], "Bad order \"lex\", ..."),
            (3, "elim", vec![int(1), int(2)], "Bad order \"elim\", ..."),
            (3, "elim", vec![Seq(ints(&[1])), Seq(ints(&[2, 3])), Seq(ints(&[1]))], "Bad order \"elim\", ..."),
            (3, "weight", vec![int(5)], "Order argument 4 must be a sequence of 9 integers or rationals"),
            (3, "weight", vec![Seq(ints(&[1, 1, 1, 0, 1, 0]))], "Order argument 4 must be a sequence of 9 integers or rationals"),
            (3, "weight", vec![Seq(ints(&[1, 1, 1, 1, 1, 1, 0, 0, 1]))], "Weight vectors of argument 4 are not independent"),
            (2, "weight", vec![Seq(ints(&[0, 0, 0, 1]))], "Weight vectors of argument 4 are not independent"),
            (3, "weight", vec![Seq(ints(&[1, -1, 1, 1, 0, 0, 0, 0, 1]))], "Entries of argument 4 are not non-negative"),
            (3, "univ", vec![Seq(ints(&[1]))], "Integer must be given for variable"),
            (3, "univ", vec![int(0)], "Argument 4 (0) should be in the range [1 .. 3]"),
            (3, "elim", vec![int(3)], "Argument 4 (3) should be in the range [1 .. 2]"),
            (1, "elim", vec![int(1)], "Argument 4 (1) should be in the range [1 .. 0]"),
            (3, "elim", vec![Int(Integer::from_i128(1 << 70))], "Argument 4 (1180591620717411303424) is too large"),
            (3, "elim", vec![int(1 << 30)], "Argument 4 (1073741824) is too large"),
            (3, "elim", vec![int(-(1 << 30))], "Argument 4 (-1073741824) is too large"),
            (3, "elim", vec![int((1 << 30) - 1)], "Argument 4 (1073741823) should be in the range [1 .. 2]"),
            (3, "elim", vec![int(-1)], "Argument 4 (-1) should be in the range [1 .. 2]"),
            (3, "elim", vec![Seq(ints(&[1, 1, 1]))], "Length of argument 4 (3) must be less than 3"),
            (3, "elim", vec![Seq(ints(&[1, 2, 4]))], "Length of argument 4 (3) must be less than 3"),
            (3, "elim", vec![Seq(ints(&[1, 1])), Seq(ints(&[2]))], "Argument 4 is not a sequence of distinct integers in the range [ 1 .. 3 ]"),
            (3, "invblock", vec![int(1)], "Bad order \"invblock\", ..."),
            (3, "univ", vec![int(1), int(2)], "Bad order \"univ\", ..."),
            (3, "grevlexw", vec![int(5)], "Order argument 4 must be a sequence of 3 integers or rationals"),
            (3, "grevlexw", vec![Seq(ints(&[1, 1, 1])), int(5)], "Bad order \"grevlexw\", ..."),
            (3, "elim", vec![Seq(ints(&[1, 1]))], "Argument 4 is not a sequence of distinct integers in the range [ 1 .. 3 ]"),
            (3, "elim", vec![Seq(ints(&[4]))], "Argument 4 is not a sequence of distinct integers in the range [ 1 .. 3 ]"),
            (3, "elim", vec![Seq(vec![rat(1, 2)])], "Argument 4 is not a sequence of distinct integers in the range [ 1 .. 3 ]"),
            (3, "elim", vec![Seq(ints(&[1, 2, 3]))], "Length of argument 4 (3) must be less than 3"),
            (3, "invblock", vec![Seq(ints(&[1, 2, 3]))], "Length of argument 4 (3) must be less than 3"),
            (3, "elim", vec![Seq(vec![]), Seq(ints(&[1, 2, 3]))], "Sequence argument 4 must be non-empty"),
            (3, "elim", vec![Seq(ints(&[1])), Seq(ints(&[2]))], "Argument 5 must have length 2"),
            (3, "invblock", vec![Seq(ints(&[1])), Seq(ints(&[2]))], "Argument 5 must have length 2"),
            (3, "elim", vec![Seq(ints(&[1])), Seq(ints(&[2, 1]))], NOT_COMPLEMENT),
            (3, "elim", vec![Seq(ints(&[1])), Seq(ints(&[2, 4]))], NOT_COMPLEMENT),
            (3, "grevlexw", vec![Seq(ints(&[1, 0, 1]))], "Entries of argument 4 are not positive"),
            (3, "grevlexw", vec![Seq(ints(&[1, 1]))], "Order argument 4 must be a sequence of 3 integers or rationals"),
            (3, "grevlexw", vec![Seq(ints(&[357914, 1, 1]))], "Weight is too large"),
        ];
        for (n, name, args, msg) in cases {
            assert_eq!(error(n, name, &args), msg, "{name} {args:?}");
        }
        assert_eq!(parse(3, "grevlexw", &[Seq(ints(&[357913, 1, 1]))]), Order::GRevLexW(vec![357913, 1, 1]));
    }
}
