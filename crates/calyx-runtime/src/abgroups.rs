//! Abelian groups given by one relation per generator, `n_i * G.i = 0`
//! (with `n_i = 0` for a free generator): the unit and additive groups of
//! residue class rings and of the integers.
//!
//! Every construction makes a new group, as in Magma: two unit groups of
//! the same ring are different groups, and their elements do not mix.

use std::rc::Rc;

use calyx_flint::Integer;
use calyx_syntax::ast::BinOp;

use crate::error::{RResult, RuntimeError};
use crate::interp::Interp;
use crate::value::{Struct, StructKind, Value};

/// An abelian group on generators with the given orders.
pub struct AbGroup {
    /// The order of each generator; 0 for a free generator.
    pub orders: Vec<Integer>,
}

/// An element of an abelian group.
pub struct AbElt {
    pub group: Rc<Struct>,
    /// Coefficients of the generators, reduced modulo their orders.
    pub coords: Box<[Integer]>,
}

impl AbGroup {
    pub fn ngens(&self) -> usize {
        self.orders.len()
    }

    pub fn is_finite(&self) -> bool {
        self.orders.iter().all(|n| !n.is_zero())
    }

    /// The order of the group, or `None` if it is infinite.
    pub fn order(&self) -> Option<Integer> {
        self.is_finite().then(|| self.orders.iter().fold(Integer::one(), |a, n| &a * n))
    }

    /// The invariant factors `d_1 | d_2 | ...` (each above 1, with 0 for
    /// each free factor, last).
    pub fn invariants(&self) -> Vec<Integer> {
        let mut d = self.orders.clone();
        // Replacing a pair by its gcd and lcm sorts the powers of every
        // prime; after the pass for i, d[i] divides all later entries.
        for i in 0..d.len() {
            for j in i + 1..d.len() {
                let g = d[i].gcd(&d[j]);
                let l = if g.is_zero() { g.clone() } else { (&d[i] * &d[j]).divexact(&g).abs() };
                d[i] = g;
                d[j] = l;
            }
        }
        d.retain(|x| !x.is_one());
        d
    }

    /// The least common multiple of the element orders, 0 if infinite.
    pub fn exponent(&self) -> Integer {
        if !self.is_finite() {
            return Integer::zero();
        }
        self.orders.iter().fold(Integer::one(), |a, n| a.lcm(n))
    }

    fn reduce(&self, i: usize, c: Integer) -> Integer {
        let n = &self.orders[i];
        if n.is_zero() { c } else { c.div_rem_euclid(n).unwrap().1 }
    }
}

/// The group data of an abelian group structure.
pub fn group_of(st: &Struct) -> Option<&Rc<AbGroup>> {
    match &st.kind {
        StructKind::AbGroup(g) => Some(g),
        _ => None,
    }
}

thread_local! {
    /// The group on no generators, which Magma shares between all the
    /// constructions giving it.
    static TRIVIAL: Rc<Struct> = Struct::new(StructKind::AbGroup(Rc::new(AbGroup { orders: Vec::new() })));
}

/// A new group on generators of the given orders (the shared trivial group
/// if there are none).
pub fn new_group(orders: Vec<Integer>) -> Rc<Struct> {
    if orders.is_empty() {
        return TRIVIAL.with(Rc::clone);
    }
    Struct::new(StructKind::AbGroup(Rc::new(AbGroup { orders })))
}

/// The element of `st` with the given coefficients, reduced.
pub fn elt(st: &Rc<Struct>, coords: Vec<Integer>) -> Value {
    let g = group_of(st).expect("an abelian group");
    let coords: Box<[Integer]> = coords.into_iter().enumerate().map(|(i, c)| g.reduce(i, c)).collect();
    Value::AbElt(Rc::new(AbElt { group: st.clone(), coords }))
}

pub fn zero(st: &Rc<Struct>) -> Value {
    let n = group_of(st).expect("an abelian group").ngens();
    elt(st, vec![Integer::zero(); n])
}

impl AbElt {
    pub fn group(&self) -> &AbGroup {
        group_of(&self.group).expect("an abelian group")
    }

    pub fn is_zero(&self) -> bool {
        self.coords.iter().all(|c| c.is_zero())
    }

    fn with(&self, coords: impl Iterator<Item = Integer>) -> Value {
        elt(&self.group, coords.collect())
    }

    pub fn add(&self, other: &AbElt) -> Value {
        self.with(self.coords.iter().zip(other.coords.iter()).map(|(a, b)| a + b))
    }

    pub fn sub(&self, other: &AbElt) -> Value {
        self.with(self.coords.iter().zip(other.coords.iter()).map(|(a, b)| a - b))
    }

    pub fn neg(&self) -> Value {
        self.with(self.coords.iter().map(|a| -a))
    }

    pub fn scale(&self, k: &Integer) -> Value {
        self.with(self.coords.iter().map(|a| a * k))
    }

    /// The order of the element, 0 if it is infinite.
    pub fn order(&self) -> Integer {
        let mut o = Integer::one();
        for (c, n) in self.coords.iter().zip(&self.group().orders) {
            if c.is_zero() {
                continue;
            }
            if n.is_zero() {
                return Integer::zero();
            }
            o = o.lcm(&n.divexact(&c.gcd(n)));
        }
        o
    }

    /// How Magma prints the element: `U.1 + 3*U.3`, `-2*F.1 + F.2`, `0`.
    pub fn format(&self) -> String {
        let name = self.group.name.borrow().map_or_else(|| "$".to_string(), |n| n.to_string());
        let mut s = String::new();
        for (i, c) in self.coords.iter().enumerate() {
            if c.is_zero() {
                continue;
            }
            let neg = c.sign() < 0;
            if s.is_empty() {
                if neg {
                    s.push('-');
                }
            } else {
                s.push_str(if neg { " - " } else { " + " });
            }
            let a = c.abs();
            if !a.is_one() {
                s.push_str(&format!("{a}*"));
            }
            s.push_str(&format!("{name}.{}", i + 1));
        }
        if s.is_empty() { "0".to_string() } else { s }
    }
}

const INCOMPATIBLE: &str = "Arguments are not compatible\nArgument types given: GrpAbElt, GrpAbElt";

impl Interp {
    /// Operators with an element of an abelian group among the operands;
    /// `None` leaves the rest (equality among them) to the generic rules.
    pub fn ab_binop(&mut self, op: BinOp, a: &Value, b: &Value) -> RResult<Option<Value>> {
        let err = |msg: &str| Err(RuntimeError::runtime(msg).in_context(op.intrinsic_name()));
        Ok(Some(match (op, a, b) {
            (BinOp::Add | BinOp::Sub, Value::AbElt(x), Value::AbElt(y)) => {
                if !Rc::ptr_eq(&x.group, &y.group) {
                    return err(INCOMPATIBLE);
                }
                if op == BinOp::Add { x.add(y) } else { x.sub(y) }
            }
            (BinOp::Mul, Value::Int(k), Value::AbElt(x)) | (BinOp::Mul, Value::AbElt(x), Value::Int(k)) => x.scale(k),
            (BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge, Value::AbElt(_), Value::AbElt(_)) => {
                return err("No comparison algorithm exists for given objects");
            }
            _ => return Ok(None),
        }))
    }

    /// `G ! x`: an element of `G`, a sequence of coefficients, 0, or an
    /// integer multiple of the generator of a group on one generator.
    /// `strict` (for `!`) gives Magma's errors for elements of other
    /// groups and sequences of the wrong length instead of failing softly.
    pub fn coerce_into_abgroup(&mut self, st: &Rc<Struct>, x: &Value, strict: bool) -> RResult<Result<Value, Option<String>>> {
        let g = group_of(st).expect("an abelian group").clone();
        let n = g.ngens();
        let hard = |msg: String| if strict { Err(RuntimeError::runtime(msg).in_context("!")) } else { Ok(Err(None)) };
        Ok(match x {
            Value::AbElt(e) if Rc::ptr_eq(&e.group, st) => Ok(x.clone()),
            Value::AbElt(_) => return hard("Could not find a covering module".to_string()),
            Value::Int(k) if k.is_zero() => Ok(zero(st)),
            Value::Int(k) if n == 1 => Ok(elt(st, vec![k.clone()])),
            Value::Seq(s) => {
                if s.elems.len() != n {
                    return hard(format!("Sequence argument length ({}) should be {n} to be coerced into a matrix or vector", s.elems.len()));
                }
                let mut coords = Vec::with_capacity(n);
                for c in &s.elems {
                    match self.try_coerce(&Value::integers(), c)? {
                        Ok(Value::Int(k)) => coords.push(k),
                        _ => return Ok(Err(None)),
                    }
                }
                Ok(elt(st, coords))
            }
            _ => Err(None),
        })
    }

    /// `x in G` for an abelian group `G`.
    pub fn ab_contains(&mut self, st: &Rc<Struct>, x: &Value) -> RResult<bool> {
        match x {
            Value::AbElt(e) if Rc::ptr_eq(&e.group, st) => Ok(true),
            Value::AbElt(_) => Err(RuntimeError::runtime("Could not find a covering group").in_context("in")),
            _ => Err(RuntimeError::runtime("Bad argument types").in_context("in")),
        }
    }

    /// The elements of a finite abelian group, the first coefficient
    /// varying fastest.
    pub fn enumerate_abgroup(&mut self, st: &Rc<Struct>) -> RResult<Vec<Value>> {
        let g = group_of(st).expect("an abelian group").clone();
        let order = g.order().ok_or_else(|| RuntimeError::runtime(crate::error::NOT_ITERABLE))?;
        let total = order.to_u64().filter(|&n| n <= 1 << 26).ok_or_else(|| RuntimeError::runtime("The group is too large to enumerate"))?;
        let orders: Vec<u64> = g.orders.iter().map(|n| n.to_u64().unwrap()).collect();
        let mut digits = vec![0u64; orders.len()];
        let mut out = Vec::with_capacity(total as usize);
        for _ in 0..total {
            self.check_interrupt()?;
            out.push(Value::AbElt(Rc::new(AbElt { group: st.clone(), coords: digits.iter().map(|&d| Integer::from_u64(d)).collect() })));
            for (d, &n) in digits.iter_mut().zip(&orders) {
                *d += 1;
                if *d < n {
                    break;
                }
                *d = 0;
            }
        }
        Ok(out)
    }
}
