# Proof guide

`HilbertUMD.theorem_1_1` in
[MainTheorem.lean](../HilbertUMD/MainTheorem.lean), matching Theorem 1.1 of the
[paper](../paper/Hilbert-and-UMD-arxiv-v1.pdf), gives the two
dimensions `2^n` and common positive constants `c, C` for all eight
inequalities, with growth rates `n` and `√n`, for every `n ≥ 1` over both fields
and any sample-space universe.

[Main/PaperStatement.lean](../HilbertUMD/Main/PaperStatement.lean) supplies the
paper notation, proves the dimensions, and converts the internal
`main_theorem_p2` from `n+1` to `n`. The [paper alignment](PAPER-ALIGNMENT.md)
records the notation and conversion.

`HilbertUMD.main_theorem_p2_quantitative` exposes the individual coefficients
through `P2QuantitativeBounds` in
[Main/Statement.lean](../HilbertUMD/Main/Statement.lean).

## Spaces and constants

[Foundations/Dyadic.lean](../HilbertUMD/Foundations/Dyadic.lean) defines the
binary coordinate spaces and their dyadic norms.
[Foundations/Spaces.lean](../HilbertUMD/Foundations/Spaces.lean) equips `HSpace`,
`ESpace`, `XSpace`, and `YSpace` with the intended norms. The underlying
coordinate function space `Vec` has the sup norm; the matrix input space
`L1Vec` uses `PiLp 1`.

[Hilbert/HilbertConstant.lean](../HilbertUMD/Hilbert/HilbertConstant.lean)
defines the principal-value Hilbert constant on compactly supported C¹ tests.
[UMD/UMD.lean](../HilbertUMD/UMD/UMD.lean) defines a universe-parameterized UMD
constant using sigma-finite sample spaces and filtrations, and unimodular
coefficients. The internal and quantitative statements use universe zero;
the paper theorem permits an arbitrary sample-space universe.

[UMD/SampleSpaceLift.lean](../HilbertUMD/UMD/SampleSpaceLift.lean) lifts a
filtration and process to `ULift`, pushes the measure forward, and proves
the same martingale identities and Lp norms. This allows a UMD bound
from any universe to test the finite leaf spaces. The independent-sign
argument in [UMD/DyadicTerminal.lean](../HilbertUMD/UMD/DyadicTerminal.lean)
therefore proves the reverse dyadic reduction in every universe.
Together with the forward reduction, this gives the same-constant
equivalence in [UMD/UniverseIndependence.lean](../HilbertUMD/UMD/UniverseIndependence.lean).
Taking infima proves `umdConstant_two_universe_eq`, including when the
constant is infinite. `Paper.Theorem11Bounds.changeUniverse` uses that
equality to preserve every comparison constant in the paper theorem.

## The four comparisons

| Comparison | Lower bound | Upper bound |
| --- | --- | --- |
| Hilbert on `XSpace`: `n + 1` | Interval logarithm and summation-matrix witness | Hilbert L2 isometry and graph factorization |
| UMD on `XSpace`: `√(n + 1)` | Explicit finite dyadic witness | Summation-matrix estimate and sharp graph transfer |
| UMD on `YSpace`: `n + 1` | Alternating dyadic witness | Hilbert-valued martingale L2 bound and graph factorization |
| Hilbert on `YSpace`: `√(n + 1)` | Logarithmic step witness and binary coefficient estimate | Signed-dyadic matrix estimate and sharp graph transfer |

The lower bounds are assembled in
[Main/LowerBounds.lean](../HilbertUMD/Main/LowerBounds.lean) and
[Main/UMDBounds.lean](../HilbertUMD/Main/UMDBounds.lean).
The sharp transfers are combined in
[Main/Transfer.lean](../HilbertUMD/Main/Transfer.lean).
[Main/Assembly.lean](../HilbertUMD/Main/Assembly.lean) chooses common constants
and fills the eight fields of `P2MainBounds`.

The quantitative constants are assembled in
[Main/QuantitativeConstants.lean](../HilbertUMD/Main/QuantitativeConstants.lean).
The interval witness in
[LowerBounds/HilbertLowerConstants.lean](../HilbertUMD/LowerBounds/HilbertLowerConstants.lean)
gives `(n+1)/7`, using `(n log 2 - 1)/π` at large depths and the scalar
Hilbert isometry at small depths. The [paper alignment](PAPER-ALIGNMENT.md)
compares all proved coefficients with the paper.

## The analytic inputs

The matrix upper bounds use the shared cubic argument in `Analysis/` and
the energy estimates in `Matrices/`. Their scalar inputs come from two routes:

- The Hilbert route constructs the Fourier L2 operator, proves the
  principal-value identification, and establishes compatible L3 and L(3/2)
  operators. `HilbertThreeSharp` combines Cotlar's identity with skew duality
  to obtain the exact cubic energy identity and the scalar L3 bound 11/4.
  Gaussian amplification then supplies matrix data `(M,P) = (11/4,9)`.
- The martingale route proves the L3 transform, square-function, and maximal
  bounds, with Davis coefficient 29/8, lower-square coefficient 45/8,
  maximal coefficient 65/4, and product coefficient 1097. Finite filtrations
  are represented by weighted binary trees and approximated by fair dyadic
  trees to prove Paley–Walsh reduction over both scalar fields.

The cubic argument uses weighted testing to obtain `9B` and the
shared cubic mass of positive and negative parts to obtain the
endpoint factor `127/80`. After complexification and interpolation, the
matrix coefficient is `(127/40) sqrt(9 n (2 M² + 2 P))`.

`Interfaces/` contains proved interfaces between these constructions and their
consumers. The quantitative real UMD upper bound uses the real-sign matrix
estimate and the generic real Paley–Walsh reduction directly. The complex
Hilbert upper bound applies the complex matrix estimate before adding its
diagonal remainder.

## Verification boundary

`import HilbertUMD` imports all three public theorems. The audit in
[tests/MainTheorem.lean](../tests/MainTheorem.lean) checks their types, expands
the literal paper fields independently of the abbreviations, checks common
constants across independent and concrete sample-space universes, and traverses
their proof dependencies, including the comparison wrapper in `Solution`.
It rejects admissions, nonstandard axioms, and library modules that contribute
no declarations. The verification scripts also check that every library source
is reachable from the public import.

[tests/AxiomAudit.lean](../tests/AxiomAudit.lean) audits every project declaration,
including private helpers and declarations outside the theorem dependency
closures. Both audits inspect full proof bodies and allow only `propext`,
`Classical.choice`, and `Quot.sound`.
[tests/Definitions.lean](../tests/Definitions.lean) checks the norms, dimensions,
paper abbreviations, and operator definitions.

Run `scripts/verify.ps1` on Windows or `bash scripts/verify.sh` on Unix. Both
treat warnings as errors and use `leanchecker` to replay the compiled project
declarations through Lean's kernel, with one worker to limit memory use.
The GitHub workflow runs these checks on Linux and Windows and saves the
reports. Cache reuse does not skip audits or kernel replay.

The [paper alignment](PAPER-ALIGNMENT.md#proof-methods-and-scope) records the
differences in proof methods and the limits of the formalized result.
