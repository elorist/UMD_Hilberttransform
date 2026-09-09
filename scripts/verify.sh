#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
if [[ -x "$PWD/.tools/elan/bin/elan" ]]; then
  export ELAN_HOME="$PWD/.tools/elan"
  export PATH="$ELAN_HOME/bin:$PATH"
fi
mkdir -p .lake/verification
rm -f -- .lake/verification/result.json
lake build --wfail 2>&1 | tee .lake/verification/build.log
lake env lean -DwarningAsError=true tests/MainTheorem.lean 2>&1 | tee .lake/verification/audit.log
grep -qF 'PASS: full main theorem' .lake/verification/audit.log
lake env lean -DwarningAsError=true tests/Definitions.lean 2>&1 | tee .lake/verification/definitions.log
lake env lean -DwarningAsError=true tests/AxiomAudit.lean 2>&1 | tee .lake/verification/axioms.log
grep -qF 'PASS: whole-project axiom audit' .lake/verification/axioms.log
# Each replay loads a full import environment. Bound memory use on CI runners.
LEAN_NUM_THREADS=1 lake env leanchecker -v HilbertUMD 2>&1 | tee .lake/verification/kernel.log
echo 'Verified the public theorems, definitions, all project axioms, and compiled proof kernel replay.'
