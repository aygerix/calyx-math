# Roadmap and handbook coverage

calyx follows the structure of the Magma handbook. This page tracks what is
implemented, what is deliberately different, and what is missing.

## Part I: The Magma Language

| Chapter | Status |
| --- | --- |
| Statements and expressions | Done: assignment (multiple, indexed, generator, mutation), `delete`, booleans, `eq`/`cmpeq`, coercion `!`, `where ... is`, `select`, `case` statement and expression, `for`/`while`/`repeat`, `for random`, dual iteration `i -> x`, `break x`/`continue x`, `eval`, comments and `\` continuation, `time`/`vtime`, types and extended types, `ISA`, `MakeType`, `CoveringStructure`, random seeds, `IsIntrinsic`. |
| Functions, procedures and packages | Done: `function`/`procedure` (both forms), `func<>`/`proc<>`, parameters, variadic functions, `$$`, `forward`, `local`, reference arguments (including `~A[x]` and `` ~r`f ``), closures capturing values at creation, packages with `intrinsic`, `Attach`/`Detach`/`AttachSpec`, automatic reloading of changed packages, `import`, `require`/`requirege`/`requirerange`, `Nresults`, attributes (`AddAttribute`, `declare attributes`), user-defined types (`declare type`, `New`, `Clone`, user `Print`, `Parent`, `IsCoercible`, `in`, operators), verbose flags. |
| Input and output | Mostly done: strings and their intrinsics (including `Split` and `Regexp`), `print` with print levels, `printf`/`fprintf`/`Sprintf` (widths, `%o %O %m %h`), `Sprint`, previous values `$1`..., indentation, `PrintFile`, `SetOutputFile`, `SetLogFile`, file objects (`Open`, `Gets`, `Puts`, ...), `Pipe`, `System`, `load`/`iload`, `read`/`readi`. **Missing:** binary strings, sockets, `POpen`, asynchronous I/O, `ReadObject`/`WriteObject`, `save`/`restore`. |
| Environment and options | Partly done: `-b -e -h -n -s -S -V` and `name:=value` arguments, set/get intrinsics (`SetColumns`, `SetAssertions`, `SetVerbose`, ...), `ShowIdentifiers`, `ShowValues`, `ListSignatures`, `ListCategories`, `?Name` help. **Missing:** `%p`-style history commands, most environment variables, vi mode. |
| Parallelism | Not started. |
| Magma semantics | Done (see "Differences" below). |
| Profiler | Intrinsics accepted; no profile data is collected yet. |
| Debugger | `SetDebugOnError` accepted; no debugger yet. |

## Part II: Sets, Sequences, and Mappings

| Chapter | Status |
| --- | --- |
| Introduction to aggregates | Done: universes, automatic coercion to a common overstructure, power structures, nested aggregates, multi-indexing, sequences used as universes. |
| Sets | Done: enumerated sets (with lazy arithmetic progressions), indexed sets, multisets, formal sets, all constructors, power sets, `Include`/`Exclude`/`ChangeUniverse`/..., set operators, `Subsets`, `Multisets`, `Permutations`, quantifiers `exists`/`forall`/`rep`/`random`, reductions, iteration. |
| Sequences | Done. `Sort` gives its sorting permutation as an element of `Sym(n)`; the symmetric groups and their elements have what Part II needs (products, powers, inverses, the action `i^p`, conjugation, `Order`, `Eltseq`, `Sign`, `CycleStructure`, `Cycle`, generators, coercion from image sequences), and the rest of permutation groups comes in Part V. |
| Tuples and Cartesian products | Done. |
| Lists | Done. |
| Associative arrays | Done, including `Default` values and widening of the index universe. |
| Coproducts | Done. |
| Records | Done. |
| Mappings | Done for maps given by rules, graphs and coercions, composition, inverses and preimages. Homomorphisms given by generator images need the algebraic structures of later parts. |

## Checking against Magma

Output is checked against real Magma (V2.29-10, the version behind the
public Magma calculator). The scripts in `crates/calyx-cli/tests/compat`
have Magma's own output as their expected output, and cover print lists,
line wrapping, aggregate layout, records, error reports (source windows,
carets, call frames, `eval` errors, syntax error recovery), coercion
errors, `Sort`'s permutations, and the generic ring functions of Part III
(ring properties, element predicates and orders, ring printing and naming,
ideals of the integers, `Infinity`). Where the handbook's examples
disagree with current Magma (they were produced by many different
versions), calyx follows current Magma:
for example records print one field per line, reals print with all their
digits, and a literal such as `1/0` is rejected when it is read.

## Differences from Magma

- **Hash order.** Magma stores sets and associative arrays in hash tables.
  It prints sets of integers, rationals and residues sorted (as calyx does),
  but iterates over them, and prints sets of strings, tuples, sets and
  sequences, in its internal hash order. calyx iterates in sorted order
  (or insertion order), so loops over sets and some printed sets can list
  elements in a different order.
- **Iterator order.** In `[ e : x in X, y in Y ]` the first iterator is
  the inner loop, while in `[ e : x, y in S ]` the first variable is the
  outer one; both match Magma.
- **Extensions.** calyx also supports formal sequences `[! ... !]`, `@@`,
  `IsInjective`, `IsSurjective`, `IsBijective` and `Graph` for maps given
  by a graph, which Magma rejects.
- **Intrinsic descriptions** (`?Name`, or printing an intrinsic) use calyx's
  own documentation.
- **Random numbers** come from a different generator, so values differ from
  Magma's for the same seed. `SetSeed`/`GetSeed` behave the same way.
- **Extended reals.** Numbers mixed with `Infinity()` get the universe
  `Extended Reals` as in Magma, but keep their own types there (`Type`
  gives `RngIntElt` where Magma gives `ExtReElt`).
- **Magma's own packages.** Errors raised inside Magma's package code show
  a traceback into Magma's files (for example `ResidueClassField` of a
  non-maximal ideal); calyx reports just the error. Intrinsics Magma has
  only for other types (such as `IsMaximal`) are not declared in calyx, so
  calling them gives an undeclared-identifier error rather than "Bad
  argument types".

## Part III: Basic Rings (in progress)

The ring layer is in place: FLINT's generic rings (`gr`) provide residue
class rings, finite fields (Conway polynomials, Zech logarithms for fields
of up to 2^20 elements), univariate and multivariate polynomial rings and
the complex field. Rings are values with Magma's printing, automatic and
forced coercion, and caching (one `Integers(n)` per modulus, one default
`GF(q)`, one global `PolynomialRing(R)` per coefficient ring).

| Chapter | Status |
| --- | --- |
| Introduction to rings | Done: `Characteristic`, `#R` (`Infinity` for infinite rings), `IsFinite` and all the ring predicates (`IsField`, `IsEuclideanDomain`, `IsPID`, `IsUFD`, `HasGCD`, ..., with Magma's answers for every kind of ring), `PrimeRing`, `PrimeField`, `Centre`, ring equality and membership (with Magma's errors between unrelated rings), element predicates (`IsUnit`, `IsIdempotent`, `IsNilpotent`, `IsZeroDivisor`, `IsIrreducible`, `IsPrime`), Magma's order on residues, finite field elements and polynomials (`lt`, `Sort`), `Maximum`/`Minimum`, ideals of the integers (`ideal< >`, `quo< >`, ideal arithmetic, `ResidueClassField`), `ext< R \| >`, and naming of structures and aggregates by assignment (generators print as `F.1`, maps show `RngInt: Z`). **Pending:** `IsIrreducible`/`IsPrime` of polynomials (they need the polynomial factorisation of the polynomial chapters), ideals of polynomial rings, `Localization` and `Completion` (local rings come later). |
| Ring of integers, residue class rings, rationals, finite fields, polynomials, real and complex fields, nearfields | Not yet: the chapter-specific intrinsics come next. |

## To do

- **Confirm two compat scripts against Magma 2.29.** The scripts in
  `crates/calyx-cli/tests/compat/pending/` (naming of aggregates in maps and
  by loop variables; sequences of literals without a common universe) match
  Magma 2.22 but were written while the public calculator was offline.
  Record their 2.29 output and move them into the compat suite (see the
  README there).

## Next

1. The rest of Part III chapter by chapter: integers, residue class rings,
   rationals, finite fields (including towers and embeddings), univariate
   and multivariate polynomials (factorisation via FLINT), real and complex
   fields, then nearfields.
2. Generator-based constructors (`sub<>`, `quo<>`, `ext<>`, `hom<>` with
   generator images) on top of those structures.
3. Part V (groups), using GAP where it is the right tool, and Singular for
   commutative algebra.
