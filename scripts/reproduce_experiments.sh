#!/usr/bin/env bash
# Reproduce the finite-field experiments underpinning the smooth-coset obstruction (route B).
# All arithmetic comes from scripts/mca_oracle.py (the validated RS/field source); the scripts
# here never re-implement field or RS arithmetic.
#
# Usage:  ./scripts/reproduce_experiments.sh      (run from the repo root)
set -euo pipefail
cd "$(dirname "$0")/.."
E=experiments/list_decoding

echo "############################################################"
echo "# 1. MDS(3) orbit-rep scan (calibrated; positive control)  #"
echo "############################################################"
python3 "$E/rim_smooth_coset_mds3.py" --q 41 --s 3 --k 3
echo
python3 "$E/rim_smooth_coset_mds3.py" --q 97 --s 5 --k 3

echo
echo "############################################################"
echo "# 2. Subcoset-binomial defect dimension + list witness     #"
echo "############################################################"
echo "--- d>k/2, d<k: DEFECT, witness above capacity ---"
python3 "$E/subcoset_defect_listsize.py" --q 97 --s 5 --k 7 --d 4
echo
echo "--- d<=k/2: NO defect (control) ---"
python3 "$E/subcoset_defect_listsize.py" --q 97 --s 5 --k 7 --d 2
echo
echo "--- k=d+1 sanity ---"
python3 "$E/subcoset_defect_listsize.py" --q 193 --s 5 --k 5 --d 4
echo
echo "--- IN-BAND witness (d>k): list is a small constant ---"
python3 "$E/subcoset_defect_listsize.py" --q 17 --s 3 --k 3 --d 4 --check-list

echo
echo "Done. Compare against the tables in research/smooth_coset_mds_failure.md."
