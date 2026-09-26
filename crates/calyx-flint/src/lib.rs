//! Safe wrappers around the parts of FLINT used by calyx.
//!
//! This crate is the only place in the workspace that talks to `flint3-sys`
//! directly. Everything else works with the types exported here, so the
//! arithmetic backend can be swapped or extended without touching the
//! interpreter.

pub mod ball;
mod complex;
pub mod gr;
pub mod upoly;
mod integer;
pub mod mpfr;
mod nmod;
mod rational;
mod real;

pub use complex::{Complex, Elementary, ModifiedPolylog};
pub use integer::{Factorization, Integer};
pub use nmod::{Nmod, gcd as gcd_u64};
pub use rational::Rational;
pub use real::{Real, bits_for_digits, digits_for_bits, parse_decimal};

use std::ffi::CStr;
use std::os::raw::c_char;

/// Copy a FLINT-allocated C string into a Rust `String` and free it.
///
/// # Safety
/// `ptr` must be a NUL-terminated string allocated by FLINT's allocator.
unsafe fn take_flint_string(ptr: *mut c_char) -> String {
    let s = unsafe { CStr::from_ptr(ptr) }.to_string_lossy().into_owned();
    unsafe { flint3_sys::flint_free(ptr.cast()) };
    s
}
