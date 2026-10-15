# Hilbert and UMD constants

Lean formalization of **Theorem 1.1** of the
[arXiv v1 manuscript](https://arxiv.org/abs/2609.10444v1) by
Emiel Lorist and Jan van Neerven.
The [paper PDF](paper/Hilbert-and-UMD-arxiv-v1.pdf) is included.

Start with [Challenge.lean](Challenge.lean) for the complete formal statement:
the concrete spaces, their Hilbert and UMD constants, the dimensions, and all
eight inequalities over both scalar fields. It imports only Mathlib; its one
intentional `sorry` marks the statement to be proved.

[Solution.lean](Solution.lean) proves that statement using the library.
Comparator checks that its statement and definitions match the Challenge and
that the proof uses only `propext`, `Classical.choice`, and `Quot.sound`.
Lean, NanoDa and con-ron independently check the exported proof.

**The entire repository was generated with GPT-6 Astra, a large language
model (LLM), under human direction.** This includes the Lean code,
documentation, scripts, tests and configuration.

## The result

For every `n ≥ 1`, both spaces have dimension `2^n`. One pair of positive
universal constants gives all eight inequalities over both `ℝ` and `ℂ`:

| Space | Hilbert constant | UMD constant |
| --- | --- | --- |
| `Paper.X 𝕜 n` = X_n | comparable to `n` | comparable to `√n` |
| `Paper.Y 𝕜 n` = Y_n | comparable to `√n` | comparable to `n` |

The verified paper claim is Theorem 1.1 at p = 2. The library also provides
quantitative bounds, some with different coefficients from Remark 1.2.
Corollary 1.3 is outside the formalization's scope.

```lean
import HilbertUMD

#check HilbertUMD.theorem_1_1
#check HilbertUMD.main_theorem_p2_quantitative
```

The [proof guide](docs/PROOF.md) maps the argument to its source files.
[Paper alignment](docs/PAPER-ALIGNMENT.md) records the definitions, universe
conventions, coefficient comparisons and differences in proof method.
[CITATION.cff](CITATION.cff) provides citation metadata;
[formalization.yaml](formalization.yaml) records scope, authorship and review status.

## Verification

Install Git and Python 3.10 or later, then clone the repository:

```sh
git clone https://github.com/elorist/UMD_Hilberttransform.git
cd UMD_Hilberttransform
```

The setup scripts install the pinned Lean toolchain, fetch the required
Mathlib cache and run verification. On Linux x86_64:

```sh
bash scripts/bootstrap.sh
```

On Windows, use PowerShell 7.2 or later:

```powershell
.\scripts\bootstrap.ps1
```

After setup, rerun checks with `bash scripts/verify.sh` or
`.\scripts\verify.ps1`. On other Unix platforms, install
[elan](https://github.com/leanprover/elan), then run:

```sh
lake exe cache get $(python3 scripts/check_repo.py --cache-imports)
bash scripts/verify.sh
```

Verification builds with warnings treated as errors, checks the theorem
statements and definitions, audits every project declaration for admissions
or extra axioms, and replays the compiled proofs through Lean's kernel.
GitHub runs the checks on Linux and Windows; reports are saved in
`.lake/verification/` and uploaded with each run.

Lean and dependency versions are pinned in [lean-toolchain](lean-toolchain)
and [lake-manifest.json](lake-manifest.json). No `lake update` is needed.

### Comparator

For the independent comparison on Linux, install `bubblewrap` and run:

```sh
bash scripts/verify-comparator.sh
```

This selects `HilbertUMD.Comparison.theorem_1_1` and requires acceptance by
Lean, NanoDa and con-ron. The Linux GitHub job runs it automatically.
The ordinary build excludes the Challenge's intentional proof hole.

## License

The Lean code and repository support files use [Apache 2.0](LICENSE).
The paper PDF, this README and [docs/](docs/) use
[CC BY 4.0](paper/LICENSE); code examples in that prose are also available
under Apache 2.0. Third-party material retains its own licences and notices.
