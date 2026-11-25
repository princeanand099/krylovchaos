#!/usr/bin/env bash
set -euo pipefail

lake exe cache get || true
lake build KrylovChaos Solution

echo "=== Static Hygiene Check ==="
hits=$(grep -rnE '\b(sorry|sorryAx|admit|axiom|native_decide|unsafe|unsafeCast|implemented_by|extern|partial|skipKernelTC|local instance)\b' KrylovChaos.lean KrylovChaos/ comparator/ChallengeDefs.lean comparator/Solution.lean | grep -vE '^[^:]+:[0-9]+:[[:space:]]*(--|/[-!]|/-)' | grep -vE 'AuditAxioms\.lean' || true)
if [ -n "$hits" ]; then
  echo "HYGIENE_CHECK_FAILED:"
  echo "$hits"
  exit 1
fi
echo "HYGIENE_CHECK_PASSED"

if [ -f KrylovChaos/AuditAxioms.lean ]; then
  echo "=== Axiom Audit ==="
  lake env lean KrylovChaos/AuditAxioms.lean
fi

echo "=== Lake Comparator ==="
lake comparator --paranoid
