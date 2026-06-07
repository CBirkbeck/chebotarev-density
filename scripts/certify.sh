#!/usr/bin/env bash
# Kernel-level certification of the headline Chebotarev theorems via
# leanprover/comparator: statement-identity against certification/Challenge.lean,
# axiom budget [propext, Quot.sound, Classical.choice], and kernel acceptance.
#
# Prerequisites (one-time):
#   git clone https://github.com/leanprover/comparator /tmp/comparator
#   cd /tmp/comparator && lake build          # toolchain matches this project
#   # the lean4export artifact lake fetches is a Linux ELF; build natively:
#   git clone https://github.com/leanprover/lean4export /tmp/lean4export
#   cd /tmp/lean4export && git checkout $(python3 -c "import json;print([p['rev'] for p in json.load(open('/tmp/comparator/lake-manifest.json'))['packages'] if p['name']=='lean4export'][0])") && lake build
#
# On Linux, install the real landrun (github.com/Zouuup/landrun) for sandboxing.
# On macOS, comparator's own scripts/fake-landrun.sh shim is used (no sandbox —
# acceptable here: the "solution" is this repository's own code, not adversarial).

set -euo pipefail

COMPARATOR_DIR="${COMPARATOR_DIR:-/tmp/comparator}"
export COMPARATOR_LEAN4EXPORT="${COMPARATOR_LEAN4EXPORT:-/tmp/lean4export/.lake/build/bin/lean4export}"
if ! command -v landrun >/dev/null 2>&1; then
  export COMPARATOR_LANDRUN="${COMPARATOR_LANDRUN:-$COMPARATOR_DIR/scripts/fake-landrun.sh}"
fi

lake env "$COMPARATOR_DIR/.lake/build/bin/comparator" certification/comparator-config.json
