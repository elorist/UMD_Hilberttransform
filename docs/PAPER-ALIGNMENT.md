# Paper alignment: 9 September 2026

The reference is the [paper PDF included in this repository](../paper/Hilbert-and-UMD-arxiv-v1.pdf).
Its authors are Emiel Lorist and Jan van Neerven.
The certification target is **Theorem 1.1**.

## Theorem 1.1

`HilbertUMD.theorem_1_1` in
[MainTheorem.lean](../HilbertUMD/MainTheorem.lean) provides one pair of
positive real constants before quantifying over all `n ≥ 1` and both
scalar fields. Each `Paper.Theorem11Bounds` contains the dimensions
`2^n` and all eight inequalities with `n` and `√n`.

[Main/PaperStatement.lean](../HilbertUMD/Main/PaperStatement.lean) uses the
paper's names through transparent abbreviations:

| Paper | Lean |
| --- | --- |
| X_n | `Paper.X 𝕜 n`, an abbreviation of `XSpace 𝕜 n` |
| Y_n | `Paper.Y 𝕜 n`, an abbreviation of `YSpace 𝕜 n` |
| hbar_{p,E} | `Paper.hbar 𝕜 p E`, the principal-value constant of the identity |
| beta_{p,E} | `Paper.beta 𝕜 p E`, the full UMD constant of the identity |
| N = 2^n | `Paper.finrank_X` and `Paper.finrank_Y` |

The auxiliary H_n and E_n are `HSpace` and `ESpace`. The matrices
Sigma_N and D_n are `summation` and `signedDyadic`, or
`summationOperator` and `signedDyadicOperator` when equipped with their
l1-to-linfinity operator domains. Their indexing and norms agree with the paper.

The internal `main_theorem_p2` uses n+1. The paper theorem converts
its bounds using n ≤ n+1 ≤ 2n and √(n+1) ≤ 2√n, without changing the depth
or the spaces. The same lower coefficient and twice the upper
coefficient work simultaneously over both fields.

The UMD definition includes sigma-finite spaces and filtrations and every
unimodular scalar of the selected field. The public paper theorem uses
sample spaces in any `Type u`. The proved equality
`umdConstant_two_universe_eq` removes dependence on that choice at p = 2,
and `Paper.Theorem11Bounds.changeUniverse` preserves the same comparison
constants. The internal and quantitative statements use universe zero;
their bounds transport by the same equality. The principal-value definition uses exactly
the paper's compactly supported C¹ tests and normalization 1/pi.

## Remark 1.2 and the quantitative companion

The numbers in Remark 1.2 are not the certification target.
`main_theorem_p2_quantitative` states the following bounds.
Write delta = (2/pi) log(27/16), and let n ≥ 1.

| Inequality | Paper | Public Lean quantitative theorem |
| --- | --- | --- |
| Lower bound for hbar_2(X_n) | n/7 | (n+1)/7, stronger |
| Upper bound for hbar_2(X_n) | n+1 | n+1 |
| Lower bound for beta_2(X_n) | √(n/14) | √(n+1)/(4√2) |
| Real upper bound for beta_2(X_n) | min(n+1, 176√(n+1)) | min(n+1, 285√(n+1)) |
| Complex upper bound for beta_2(X_n) | min(n+1, 351√(n+1)) | min(n+1, 448√(n+1)) |
| Lower bound for beta_2(Y_n) | 2n/3 | 2n/3 |
| Upper bound for beta_2(Y_n) | n+1 | n+1 |
| Lower bound for hbar_2(Y_n) | √(n/3) | delta √(n+1)/√2 |
| Upper bound for hbar_2(Y_n) | min(n+1, 40√(n+1)) | min(n+1, 57√(n+1)) |

The Y_n UMD matrix witness proves 2n/3 and the exact graph transfer preserves
that bound through [Main/UMDBounds.lean](../HilbertUMD/Main/UMDBounds.lean)
to the public quantitative theorem. Only the internal asymptotic assembly
converts it to a common coefficient times n+1. For the X_n UMD lower bound,
[SummationLower.lean](../HilbertUMD/LowerBounds/SummationLower.lean) proves an
exact diagonal variance identity; the numerical corollary uses only
the coarser coefficient 1/4. A short arithmetic refinement yields the paper's
√(n/14) target.

The stronger Hilbert lower coefficient follows from
[HilbertLowerConstants.lean](../HilbertUMD/LowerBounds/HilbertLowerConstants.lean).
The upper coefficients are assembled in
[Main/QuantitativeConstants.lean](../HilbertUMD/Main/QuantitativeConstants.lean).

## Proof methods and scope

The spaces, definitions, generic sharp graph transfers, and p = 2 growth
rates agree. The proof uses direct witnesses for the two square-root lower
bounds instead of the paper's quadratic-comparison argument.
The upper estimates use the same cancellation, cubic-testing, dyadic-energy,
duality, and interpolation mechanism, with different intermediate constants.

The paper uses scalar Hilbert L³ norm √3 and product coefficient 4; Lean
uses 11/4 and 9. Lean's real cubic endpoint uses the positive-part
factor 127/80, while other steps incur larger factors. See the
[proof guide](PROOF.md) for the checked route through the library.

## Optional extensions

Theorem 1.1 is complete. Further work could sharpen the quantitative
companion to match all of Remark 1.2, prove the extrapolation needed for
Corollary 1.3, or formalize the general quadratic-comparison theorems.
These are outside the certification target.

The summation-witness arithmetic for beta_2(X_n) can be sharpened using
the diagonal variance identity above. Matching the remaining coefficients
in the table requires stronger estimates.

## Verification

The default build includes `theorem_1_1`, `main_theorem_p2`, and
`main_theorem_p2_quantitative`.
[tests/MainTheorem.lean](../tests/MainTheorem.lean) checks the dimensions,
literal n/√n inequalities, common constants across universes, numerical
companion, and their transitive proof
dependencies. Only `propext`, `Classical.choice`, and `Quot.sound` are accepted.
[tests/Definitions.lean](../tests/Definitions.lean) independently checks the
norms, dimensions, paper abbreviations, and operator definitions.
[tests/AxiomAudit.lean](../tests/AxiomAudit.lean) also audits all project
declarations, including helpers outside the theorem dependency closures.
Both verification scripts reject warnings and replay compiled project
declarations through Lean's kernel using `leanchecker`.

Run `scripts/verify.ps1` on Windows or `bash scripts/verify.sh` on Unix.
The repository checker also verifies the exact SHA-256 hash of the fixed PDF.
