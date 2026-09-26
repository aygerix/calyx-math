//! The structural properties Magma reports for a ring (`IsField`, `IsPID`,
//! `Characteristic`, ...), for the integers, rationals and reals as well as
//! the rings built on FLINT.

use calyx_flint::Integer;

use super::RingKind;
use crate::value::{StructKind, Value};

pub struct RingProps {
    pub field: bool,
    pub ordered: bool,
    pub domain: bool,
    pub ufd: bool,
    pub has_gcd: bool,
    /// Whether exact arithmetic is used (not real or complex numbers).
    pub exact: bool,
    /// `None` where Magma has no algorithm to decide (multivariate
    /// polynomial rings).
    pub euclidean: Option<bool>,
    pub magma_euclidean: bool,
    pub pid: Option<bool>,
    pub characteristic: Integer,
    /// `None` for an infinite ring.
    pub cardinality: Option<Integer>,
}

/// The properties of the ring `v`, if it is one.
pub fn ring_props(v: &Value) -> Option<RingProps> {
    let number_field = |exact: bool, magma_euclidean: bool| RingProps {
        field: true,
        ordered: true,
        domain: true,
        ufd: true,
        has_gcd: exact,
        exact,
        euclidean: Some(true),
        magma_euclidean,
        pid: Some(true),
        characteristic: Integer::zero(),
        cardinality: None,
    };
    Some(match v.as_struct()? {
        // An ideal dR of R = Z/mZ, a ring without one.
        StructKind::ResIdeal(r, d) => {
            let m = super::ideals::residue_modulus(r);
            RingProps {
                field: false,
                ordered: false,
                domain: false,
                ufd: false,
                has_gcd: true,
                exact: true,
                euclidean: Some(false),
                magma_euclidean: true,
                pid: Some(false),
                cardinality: Some(m.divexact(d)),
                characteristic: m,
            }
        }
        StructKind::Integers => RingProps { field: false, magma_euclidean: true, ..number_field(true, true) },
        StructKind::Rationals => number_field(true, false),
        StructKind::Reals(_) => number_field(false, false),
        StructKind::Ring(r) => match &r.kind {
            RingKind::Complex(_) => number_field(false, false),
            RingKind::Residue(m) => {
                let prime = m.is_prime();
                RingProps {
                    field: prime,
                    ordered: false,
                    domain: prime,
                    ufd: prime,
                    has_gcd: true,
                    exact: true,
                    euclidean: Some(prime),
                    magma_euclidean: true,
                    pid: Some(prime),
                    characteristic: m.clone(),
                    cardinality: Some(m.clone()),
                }
            }
            RingKind::Finite(f) => RingProps {
                field: true,
                ordered: false,
                domain: true,
                ufd: true,
                has_gcd: true,
                exact: true,
                euclidean: Some(true),
                magma_euclidean: false,
                pid: Some(true),
                characteristic: f.p.clone(),
                cardinality: Some(f.order()),
            },
            RingKind::UPoly { base, .. } => {
                let b = ring_props(base)?;
                let euclidean = b.field && b.exact;
                RingProps {
                    field: false,
                    ordered: false,
                    domain: b.domain,
                    ufd: b.ufd,
                    has_gcd: b.has_gcd,
                    exact: b.exact,
                    euclidean: Some(euclidean),
                    magma_euclidean: euclidean,
                    pid: Some(b.field),
                    characteristic: b.characteristic,
                    cardinality: None,
                }
            }
            // A quotient P/(f) is a domain when f is irreducible (and then a
            // field over a field).
            RingKind::UPolyRes { base, modulus, .. } => {
                let b = ring_props(base)?;
                let domain = crate::intrinsics::upoly::res_is_domain(modulus);
                let field = b.field && domain;
                RingProps {
                    field,
                    ordered: false,
                    domain,
                    ufd: field,
                    has_gcd: field,
                    exact: b.exact,
                    euclidean: Some(field),
                    magma_euclidean: field,
                    pid: Some(field),
                    characteristic: b.characteristic,
                    cardinality: b.cardinality.map(|q| q.pow(modulus.poly_len() as u64 - 1)),
                }
            }
            RingKind::MPoly { base, .. } => {
                let b = ring_props(base)?;
                RingProps {
                    field: false,
                    ordered: false,
                    domain: b.domain,
                    ufd: b.ufd,
                    has_gcd: b.has_gcd,
                    exact: b.exact,
                    euclidean: None,
                    magma_euclidean: false,
                    pid: None,
                    characteristic: b.characteristic,
                    cardinality: None,
                }
            }
            // The cardinality of an affine algebra needs a Gröbner basis
            // (`intrinsics/poly_ideals/affine.rs` finds it); whether it is a
            // field or a domain needs primality of ideals, which calyx lacks
            // for now.
            RingKind::MPolyRes { base, .. } => {
                let b = ring_props(base)?;
                RingProps {
                    field: false,
                    ordered: false,
                    domain: false,
                    ufd: false,
                    has_gcd: false,
                    exact: b.exact,
                    euclidean: Some(false),
                    magma_euclidean: false,
                    pid: None,
                    characteristic: b.characteristic,
                    cardinality: None,
                }
            }
        },
        _ => return None,
    })
}
