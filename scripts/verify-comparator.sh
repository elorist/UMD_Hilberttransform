#!/usr/bin/env bash
# The project's pinned toolchain supplies every proof checker.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
if [[ -x "$PWD/.tools/elan/bin/elan" ]]; then
  export ELAN_HOME="$PWD/.tools/elan"
  export PATH="$ELAN_HOME/bin:$PATH"
fi
mkdir -p .lake/verification
rm -f -- .lake/verification/comparator.json .lake/verification/comparator-run.log
exec > >(tee .lake/verification/comparator.log) 2>&1

config=''
prefix=''
stage='preflight'
finish() {
  local result=$?
  trap - EXIT
  if [[ -n "$config" ]]; then rm -f -- "$config"; fi
  if command -v python3 >/dev/null 2>&1; then
    python3 - "$result" "$stage" "$prefix" <<'PY'
import datetime
import hashlib
import json
from pathlib import Path
import subprocess
import sys

result, stage, prefix = sys.argv[1:]
run_log = Path(".lake/verification/comparator-run.log")
run_output = run_log.read_text(encoding="utf-8", errors="replace").splitlines() if run_log.exists() else []
kernel_names = ["Lean default", "nanoda", "con-ron"]
report = {
    "status": "passed" if result == "0" and stage == "complete" else "failed",
    "exitCode": int(result), "stage": stage,
    "leanToolchain": Path("lean-toolchain").read_text().strip(),
    "configurationSha256": hashlib.sha256(Path("comparator.json").read_bytes()).hexdigest(),
    "manifestSha256": hashlib.sha256(Path("lake-manifest.json").read_bytes()).hexdigest(),
    "commit": subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
    "requestedKernels": kernel_names,
    "acceptedKernels": [name for name in kernel_names if f"{name} kernel accepts the solution" in run_output],
    "comparisonCompleted": "Your solution is okay!" in run_output,
    "runLogSha256": hashlib.sha256(run_log.read_bytes()).hexdigest() if run_log.exists() else None,
    "toolSha256": {name: hashlib.sha256(path.read_bytes()).hexdigest()
                   for name in ["lake", "leanexport", "leanchecker", "nanoda_bin", "con-ron"]
                   if prefix and (path := Path(prefix) / "bin" / name).is_file()},
    "finishedAt": datetime.datetime.now(datetime.timezone.utc).isoformat(),
}
Path(".lake/verification/comparator.json").write_text(json.dumps(report, indent=2) + "\n")
PY
  fi
  exit "$result"
}
trap finish EXIT

if [[ "$(uname -s)" != Linux ]]; then
  echo 'error: the complete comparator check requires Linux and bubblewrap' >&2
  exit 1
fi
for command_name in bwrap lake lean python3; do
  if ! command -v "$command_name" >/dev/null 2>&1; then
    echo "error: $command_name is required to run the complete comparator check" >&2
    exit 1
  fi
done
python3 scripts/check_repo.py
toolchain=$(tr -d '[:space:]' < lean-toolchain)
# Elan honours this even when the caller has selected a different default.
export ELAN_TOOLCHAIN="$toolchain"
prefix=$(lean --print-prefix)
for tool in lake leanexport leanchecker nanoda_bin con-ron; do
  if [[ ! -x "$prefix/bin/$tool" ]]; then
    echo "error: toolchain $toolchain does not bundle $tool" >&2
    exit 1
  fi
done
export PATH="$prefix/bin:$PATH"
export COMPARATOR_BWRAP
COMPARATOR_BWRAP=$(command -v bwrap)
lean_version=$("$prefix/bin/lean" --version)
echo "$lean_version"
if [[ "$lean_version" != "Lean (version ${toolchain##*:v},"* ]]; then
  echo "error: the active compiler does not match $toolchain" >&2
  exit 1
fi

# Keep machine paths out of the repository configuration, and inject only the
# kernel binaries bundled with this toolchain.
config=$(mktemp "${TMPDIR:-/tmp}/hilbertumd-comparator.XXXXXX")
python3 - comparator.json "$config" "$prefix" <<'PY'
import json
from pathlib import Path
import sys

source, destination, prefix = sys.argv[1:]
config = json.loads(Path(source).read_text(encoding="utf-8"))
if not isinstance(config, dict):
    raise SystemExit("error: comparator.json must contain one JSON object")
if "external_kernels" in config:
    raise SystemExit("error: external_kernels must not appear in the repository configuration")
config.pop("enable_nanoda", None)
config["external_kernels"] = {
    "nanoda": [f"{prefix}/bin/nanoda_bin"],
    "con-ron": [f"{prefix}/bin/con-ron"],
}
Path(destination).write_text(json.dumps(config, indent=2) + "\n", encoding="utf-8")
PY

stage='cache'
df -h . "${TMPDIR:-/tmp}"
# Fetch only the project's import closure; caching all of Mathlib wastes the
# space needed by Comparator's exports and its independent kernel replays.
cache_imports=$(python3 scripts/check_repo.py --cache-imports)
mapfile -t cache_modules <<< "$cache_imports"
"$prefix/bin/lake" exe cache get "${cache_modules[@]}"
stage='comparator'
"$prefix/bin/lake" comparator --config "$config" 2>&1 | tee .lake/verification/comparator-run.log
stage='evidence'
# Require the bundled Comparator's verdicts, not just a successful shell exit.
for kernel in 'Lean default' nanoda con-ron; do
  grep -Fxq "$kernel kernel accepts the solution" .lake/verification/comparator-run.log
done
grep -Fxq 'Your solution is okay!' .lake/verification/comparator-run.log
stage='complete'
echo 'PASS: Theorem 1.1 matches its independent statement and passes Lean, NanoDa, and con-ron.'
