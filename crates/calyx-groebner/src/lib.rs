//! Gröbner bases for calyx.
//!
//! This crate holds the algorithms behind Magma's chapter on Gröbner bases:
//! the monomial orders and the computation of bases. It depends on
//! calyx-flint only, so the algorithms can be tested without the
//! interpreter; polynomials cross the boundary as lists of terms
//! `(coefficient, exponents)` in the coefficient ring's `gr` context.

pub mod order;

pub use order::{Order, OrderArg, OrderError, Weights};
