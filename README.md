# Hilbert and UMD constants

Lean formalization of **Theorem 1.1** of the
[manuscript prepared for arXiv v1](paper/Hilbert-and-UMD-arxiv-v1.pdf) by
Emiel Lorist and Jan van Neerven.

**This repository was generated with GPT-6 Astra, a large language model
(LLM), under human direction.** This includes the Lean code, documentation,
scripts, tests, and repository configuration. The formal proofs are checked
by Lean; the verification scripts also audit their dependencies and replay
the compiled proofs through Lean's kernel.

The certification target is Theorem 1.1, the p = 2 separation theorem over
both scalar fields. The library also supplies quantitative bounds with
some different coefficients from Remark 1.2. Corollary 1.3 and the paper's
background results are outside this certification target.

```lean
import HilbertUMD

#check HilbertUMD.theorem_1_1
#check HilbertUMD.umdConstant_two_universe_eq
#check HilbertUMD.Paper.finrank_X
#check HilbertUMD.Paper.finrank_Y
#check HilbertUMD.main_theorem_p2_quantitative
```

One pair of positive universal constants works for every `n ≥ 1`, over both
`ℝ` and `ℂ`, in all eight inequalities:

| Space | Hilbert constant | UMD constant |
| --- | --- | --- |
| `Paper.X 𝕜 n` = X_n | comparable to `n` | comparable to `√n` |
| `Paper.Y 𝕜 n` = Y_n | comparable to `√n` | comparable to `n` |

Both spaces have dimension `2^n`. The literal paper statement, including
the dimensions and all eight inequalities, is
`Paper.Theorem11Bounds` in
[Main/PaperStatement.lean](HilbertUMD/Main/PaperStatement.lean).
`Paper.hbar 𝕜 p E` and `Paper.beta 𝕜 p E` abbreviate the actual Hilbert and
UMD constants of E. They use the existing definitions, as do `Paper.X` and
`Paper.Y`. The proof is assembled in [MainTheorem.lean](HilbertUMD/MainTheorem.lean).
Theorem 1.1 permits any sample-space universe: `theorem_1_1.{u}` uses
`Paper.beta.{u}`, which quantifies over all sigma-finite sample spaces in
`Type u`, sigma-finite filtrations, and all real or complex unimodular
coefficients. The theorem `umdConstant_two_universe_eq` proves that
`umdConstant.{u} 2 T = umdConstant.{v} 2 T` for every operator between the
real or complex Banach spaces allowed by the reduction, including infinite
constants. See [UMD/UniverseIndependence.lean](HilbertUMD/UMD/UniverseIndependence.lean).
`Paper.Theorem11Bounds.changeUniverse` preserves the identical comparison
constants when changing universes.

The internal `main_theorem_p2` retains the equivalent `n+1` normalization.
It and the quantitative companion use universe zero; the equality above
transports their UMD bounds to any universe without changing a coefficient.
For `n ≥ 1`, the paper statement follows with the same lower coefficient
and twice the common upper coefficient, without reindexing the spaces.

The quantitative companion retains the linear upper bounds `n+1`, the
minimum forms, the stronger Hilbert lower bound `(n+1)/7` for X_n, and
the paper's UMD lower bound `2n/3` for Y_n.
Its square-root upper coefficients are **285 over ℝ**, **448 over ℂ**, and
**57** for the Hilbert constant of Y_n over either field; the paper uses
176, 351, and 40. See [paper alignment](docs/PAPER-ALIGNMENT.md) for the full
comparison. Matching Remark 1.2
is an optional extension, not unfinished work on Theorem 1.1.

## Source layout

- `HilbertUMD/Main/`: statement, comparison constants, and final assembly.
- `HilbertUMD/Foundations/`: binary geometry, matrices, and the normed spaces.
- `HilbertUMD/Transfer/`: decompositions and L² transfer estimates.
- `HilbertUMD/UMD/`: martingale bounds, finite-tree reduction, and restriction to real scalars.
- `HilbertUMD/Hilbert/`: Fourier and principal-value constructions and bounds.
- `HilbertUMD/Analysis/`: mixed norms, duality, amplification, and interpolation.
- `HilbertUMD/Matrices/`: the cubic matrix argument and sharp upper bounds.
- `HilbertUMD/LowerBounds/`: dyadic and logarithmic witnesses.
- `HilbertUMD/Interfaces/`: proved analytic interfaces connecting these constructions.
- `tests/MainTheorem.lean`: statement checks and transitive proof audit.
- `tests/AxiomAudit.lean`: audit of every project declaration and its dependencies.
- `tests/Definitions.lean`: checks for the dimensions, norms, and operator definitions.

Every mathematical module contributes declarations to the full theorem.
Supporting facts required to elaborate its proofs are retained.

## Verification

Clone the [repository cited in the paper](https://github.com/elorist/UMD_Hilberttransform)
and enter its directory:

```sh
git clone https://github.com/elorist/UMD_Hilberttransform.git
cd UMD_Hilberttransform
```

With Lean installed, fetch the pinned mathlib cache and verify:

```sh
lake exe cache get
bash scripts/verify.sh
```

For a fresh Linux x86_64 installation, use `bash scripts/bootstrap.sh`.
On other Unix platforms, install [elan](https://github.com/leanprover/elan)
first; the repository's lean-toolchain file selects Lean's version.

On Windows, use **PowerShell 7.2 or later** and Git:

```powershell
.\scripts\verify.ps1
```

For a fresh Windows checkout, run `.\scripts\bootstrap.ps1` first. Both
bootstrap scripts verify a pinned elan installer checksum. Windows uses the
user-wide `.elan` installation and stores installer downloads under
`~/.cache/lean/bootstrap`; Unix bootstrap uses `.tools/`. Neither changes the
machine PATH. The verification scripts also support an existing installation.

The default build includes the literal paper theorem, the internal asymptotic
theorem, and the quantitative companion. The audit checks their statements,
real and complex specializations, and all transitive proof dependencies.
`tests/Definitions.lean` separately
checks the dimensions, norms, and meanings of the operator constants. The audit rejects
admitted proofs and any axioms beyond `propext`, `Classical.choice`, and `Quot.sound`.
The verification scripts additionally audit every project declaration,
including private helpers, and recheck compiled project declarations with
Lean's kernel through `leanchecker`. Builds and Lean tests fail on warnings.
The reports are written to `.lake/verification/`; Windows also records a
`result.json` with source hashes, written only after every check passes.

Lean is pinned to `leanprover/lean4:v4.33.0`; mathlib is pinned to
`db584cd6d46c92f209a44c0f1c829460d327499d`. Transitive dependencies are pinned in
`lake-manifest.json`. Building requires no `lake update`.

The GitHub Actions workflow runs these checks automatically on Linux and
Windows after each push or pull request. A green check means every required
step passed. It caches the pinned toolchain, dependencies and build outputs,
and saves downloadable verification reports even when a check fails.
It also checks publishable files, local links, the exact fixed paper PDF hash, and
common credential patterns with
`python scripts/check_repo.py` (Python 3.10 or later). Development archives,
generated reports, toolchains, and caches are excluded by `.gitignore`.

See [CITATION.cff](CITATION.cff) for citation metadata and
[paper alignment](docs/PAPER-ALIGNMENT.md#optional-extensions) for optional extensions.

See [the proof guide](docs/PROOF.md) for the route from the constructions to
the eight inequalities.

## License

Unless a file states otherwise, the original software and repository
support files use the [Apache License 2.0](LICENSE). This includes the Lean
library, scripts, tests, GitHub workflows, build settings, configuration,
software metadata, and comments and documentation inside source files.

The paper PDF and prose in this README and [docs/](docs/)
use [Creative Commons Attribution 4.0 International](paper/LICENSE)
(`CC-BY-4.0`). Code examples in the prose are also available under Apache 2.0.

Third-party dependencies and separately identified third-party material
retain their own licences and notices. Both full licence texts are included
without modification.
