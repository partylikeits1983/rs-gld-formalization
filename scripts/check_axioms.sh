#!/usr/bin/env bash
# Assert the headline theorems are axiom-clean: they may depend ONLY on Lean's three
# foundational axioms (propext, Classical.choice, Quot.sound) — never on `sorryAx`
# (an unfinished proof) or `Lean.ofReduceBool` (a `native_decide` kernel bypass).
#
# Usage:  ./scripts/check_axioms.sh         (run from the repo root)
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"

THEOREMS=(
  "RSGLD.ListDecoding.interleave_list_size_ggr"          # GGR interleaving reduction (core)
  "RSGLD.ListDecoding.maxListSize_interleave_le_int"     # GGR reduction (integer form)
  "RSGLD.ListDecoding.treeLeaves_le"                     # erase-decode tree leaf count
  "RSGLD.ListDecoding.interleavedRS_field_size_condition_of_base_bound"      # base-RS bound => field-size condition
  "RSGLD.ListDecoding.interleaved_field_size_condition_of_base_poly_bound"   # Muralidhara–Sen plug-in
  "RSGLD.ListDecoding.gld_field_size_slightly_above_johnson_of_MS"           # MS slightly-above-Johnson corollary
  "RSGLD.SmoothCosetMDS.binom_three_dependent"           # smooth-coset MDS obstruction (core)
  "RSGLD.SmoothCosetMDS.binom_three_coeffs_nontrivial"
)

echo "== building (lake build) =="
lake build

TMP="$(mktemp -d)/axcheck.lean"
{
  echo "import RSGLD"
  for t in "${THEOREMS[@]}"; do echo "#print axioms $t"; done
} > "$TMP"

echo "== #print axioms report =="
OUT="$(lake env lean "$TMP")"
echo "$OUT"

echo "== verdict =="
fail=0
if grep -q "sorryAx" <<<"$OUT"; then
  echo "FAIL: a headline theorem depends on sorryAx (unfinished proof)"; fail=1
fi
if grep -q "ofReduceBool" <<<"$OUT"; then
  echo "FAIL: a headline theorem depends on Lean.ofReduceBool (native_decide bypass)"; fail=1
fi
for t in "${THEOREMS[@]}"; do
  if ! grep -q "'$t'" <<<"$OUT"; then
    echo "FAIL: no axiom report for $t (renamed or unknown?)"; fail=1
  fi
done
if [ "$fail" -eq 0 ]; then
  echo "OK: all ${#THEOREMS[@]} headline theorems are axiom-clean"
  echo "    (depend only on propext, Classical.choice, Quot.sound)"
else
  exit 1
fi
