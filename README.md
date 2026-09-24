# Sage on Steroids

**An LLM-accelerated fork of [SageMath](https://www.sagemath.org/) that aims to achieve feature parity with Magma.**

Sage on Steroids is a research-focused SageMath fork for implementing advanced
computational mathematics, closing major feature gaps, and removing performance
bottlenecks that make otherwise-available algorithms impractical on serious
examples.

The project tracks upstream SageMath closely. The goal is not to replace Sage,
but to provide a faster-moving place where substantial mathematical features can
be developed, tested, benchmarked, and used without waiting indefinitely for
upstream integration.

## Why this fork?

Two things motivate this project.

First, important research functionality is still available mainly in proprietary
computer algebra systems. The long-term goal here is straightforward: make as
much of that mathematics as possible available in a free, inspectable, and
reproducible SageMath-based system.

Second, upstream review can be slow, especially for large or highly specialized
mathematical contributions that require scarce domain-expert reviewers. Useful
code should not have to remain on a private branch for months while review is
pending. This fork provides a place to ship mature work immediately, while
selected changes can still be proposed upstream when appropriate.

## LLM-accelerated development

Large language models are used aggressively as development tools: for code
generation and refactoring, profiling ideas, test construction, documentation,
API exploration, and reviewing large changes.

They are **not** treated as correctness oracles.

Mathematical code is expected to stand on ordinary evidence:

- exact or certified algorithms where the mathematics requires them;
- explicit precision tracking for numerical and p-adic computations;
- doctests and regression tests;
- comparisons with independent implementations;
- benchmark scripts and reproducible examples;
- failure rather than silent guessing when hypotheses or precision are
  insufficient.

The point of LLM acceleration is to increase the amount of serious mathematical
software that can be built and maintained, not to lower the standard for it.

## Current work

### Faster braid monodromy and fundamental groups

The `zariski_vankampen` implementation is being optimized substantially,
including:

- certified ball arithmetic in place of unnecessary exact `QQbar` work;
- cached polynomial restrictions and root data;
- lower-overhead parallel execution;
- deterministic strand ordering;
- faster braid decomposition and GAP interaction.

On larger arrangements, the resulting speedups can exceed an order of
magnitude.

Development branch: [`zvk-certified-numerics`](../../tree/zvk-certified-numerics)  
Upstream PR: [sagemath/sage#42844](https://github.com/sagemath/sage/pull/42844)

### General Coleman integration and effective Chabauty

Active development includes a general Coleman integration stack for curves given
by irreducible monic equations (Q(x,y)=0), working on the smooth projective
normalization rather than only on nonsingular affine or hyperelliptic models.

The implementation includes work on:

- finite and infinite integral bases;
- de Rham cohomology and Frobenius;
- ramified, bad, and infinite residue disks;
- integration at general and tangential endpoints;
- arbitrary differential reduction;
- effective Chabauty--Coleman;
- torsion packets;
- certified p-adic precision and descent.

The aim is a practical open implementation for computations that have
traditionally required proprietary software.

## Roadmap

The broader goal is feature parity with Magma in areas where SageMath is still
missing complete research workflows. Priorities include arithmetic geometry,
function fields, algebraic geometry, modular forms, explicit class field
theory, and other domains where open-source coverage remains incomplete.

New features should be useful as complete mathematical workflows, not merely
collections of low-level routines.

## Relationship to SageMath

This repository is derived directly from SageMath and periodically tracks its
`develop` branch.

For standard SageMath functionality, installation details, documentation, and
community support, use the upstream resources:

- [SageMath](https://www.sagemath.org/)
- [Documentation](https://doc.sagemath.org/)
- [Installation guide](https://doc.sagemath.org/html/en/installation/)
- [Upstream repository](https://github.com/sagemath/sage)

This README intentionally documents only what is different about this fork.

## Installation

Build Sage on Steroids the same way as upstream SageMath:

```bash
git clone --branch develop https://github.com/aygerix/sage-on-steroids.git
cd sage-on-steroids

make configure
./configure
make
./sage
```

Platform-specific prerequisites and alternative installation methods are
covered by the upstream [Sage installation
guide](https://doc.sagemath.org/html/en/installation/).

## Status

This is a research and development fork.

Some branches contain mature, heavily tested code; others may contain
experimental algorithms or interfaces that are still changing. If you use the
project for published computations, pin the exact commit or release used.

Bug reports, mathematical counterexamples, difficult benchmark cases, and
performance regressions are especially welcome.

## License

This repository is derived from SageMath and remains distributed under the
applicable SageMath and bundled-software licenses. See
[`COPYING.txt`](./COPYING.txt) for details.

Sage on Steroids is an independent fork and is not an official SageMath
distribution.
