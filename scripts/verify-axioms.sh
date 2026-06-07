#!/usr/bin/env bash
# Campaign gate: the four headline Chebotarev results must build and stay
# axiom-clean ([propext, Classical.choice, Quot.sound]) with zero sorries.
# Run after every cleanup batch commit.

set -euo pipefail

lake build CebotarevDensity 2>&1 | tail -2

TMP=/tmp/chebotarev-axiom-gate.lean
cat > "$TMP" <<'EOF'
import CebotarevDensity.Main
#print axioms Chebotarev.chebotarev_density
#print axioms Chebotarev.chebotarev_density_of_comm
#print axioms Chebotarev.density_split_completely
#print axioms Chebotarev.dirichlet_primes_in_AP
EOF

OUT=$(lake env lean "$TMP" 2>&1) || { echo "$OUT"; echo "FAIL: checker file did not elaborate"; exit 1; }
echo "$OUT"
rm -f "$TMP"

# Every line must list exactly the three standard axioms; fail on sorryAx or
# any custom axiom.
if echo "$OUT" | grep -q 'sorryAx'; then echo "FAIL: sorryAx present"; exit 1; fi
N=$(echo "$OUT" | grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" || true)
if [ "$N" -ne 4 ]; then echo "FAIL: expected 4 clean axiom lines, got $N"; exit 1; fi

# Advisory: no axiom declarations or sorries anywhere in the source.
if grep -rnE '^\s*(axiom|@\[.*\]\s*axiom)\s' CebotarevDensity/ --include='*.lean'; then
  echo "FAIL: axiom declaration found"; exit 1
fi
if grep -rnE '\bsorry\b' CebotarevDensity/ --include='*.lean' | grep -vE '^\S+:\d+:\s*(--|/-|.*-/)' | grep -vE 'docstring|sorry-free|sorried'; then
  echo "WARN: sorry-like tokens above (inspect — may be prose)"
fi

echo "AXIOM GATE: PASS (4/4 headline theorems clean, no sorryAx, no axiom decls)"
