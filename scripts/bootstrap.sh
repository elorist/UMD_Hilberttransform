#!/usr/bin/env bash
# Install the pinned Linux x86_64 toolchain locally and verify the project.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."

if [[ "$(uname -s)-$(uname -m)" != Linux-x86_64 ]]; then
  echo 'This bootstrap supports Linux x86_64. On other systems, install elan and use scripts/verify.sh.' >&2
  exit 1
fi
command -v git >/dev/null
export ELAN_HOME="$PWD/.tools/elan"
export PATH="$ELAN_HOME/bin:$PATH"
if [[ ! -x "$ELAN_HOME/bin/elan" ]]; then
  mkdir -p .tools/elan-installer
  curl -fLsS https://github.com/leanprover/elan/releases/download/v4.2.4/elan-x86_64-unknown-linux-gnu.tar.gz \
    -o .tools/elan.tar.gz
  echo '42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63  .tools/elan.tar.gz' | sha256sum -c -
  tar -xzf .tools/elan.tar.gz -C .tools/elan-installer
  .tools/elan-installer/elan-init -y --no-modify-path --default-toolchain none
fi
elan toolchain install "$(tr -d '\r\n' < lean-toolchain)"
lake exe cache get
bash scripts/verify.sh
