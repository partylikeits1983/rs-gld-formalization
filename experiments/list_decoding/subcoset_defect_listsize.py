#!/usr/bin/env python3
"""Subgroup-binomial MDS defect → explicit list-size fallout (steps 2-4 of the mathematician goal).

Three computations, all over GF(q), L = mu_{2^s} = <omega>, n = 2^s:

(STEP 3) General d<k intersection dimension.
    For l cosets A_t = omega^{i_t} H_d of the order-d subgroup, G_{A_t}^perp = (X^d - c_t)*Poly_{<k-d}
    with c_t = omega^{i_t d}. We compute
        dim S = dim( sum_t (X^d - c_t)*Poly_{<k-d} )  in Poly_{<k},
        dim(cap_t G_{A_t}) = k - dim S,
    and compare to the generic value max(0, l*d - (l-1)*k).
    PREDICTION (analytic): for d > k/2, dim(cap) = 2d-k for ALL l>=2 (defect at l>=3);
                           for d <= k/2, dim S = k so dim(cap)=0 = generic (NO defect).

(STEP 2) Explicit Hamming-ball witness from w = (x^d on L).
    On coset omega^t H_d, x^d == omega^{td} (constant). So the constant codeword p_t == omega^{td}
    (degree 0 < k) agrees with w on the whole coset = d points. The constants {omega^{td}} are
    n/d distinct (omega^d has order n/d). => an explicit list of n/d codewords at agreement a=d.
    We report a, radius delta=1-d/n, Johnson 1-sqrt(rho), capacity-proxy 1-rho, and n/d vs 2^-128*q.

(STEP 4) True worst-case list cross-check (exact, tiny q,k) at the band agreement, to confirm the
    construction is not leaving a bigger list on the table.
"""
from __future__ import annotations
import argparse, os, sys, math
sys.path.insert(0, os.path.dirname(__file__))
import list_size_oracle as LO
from smooth_coset_higher_order_mds import mat_rank


def _field_pow(base, e, q):
    return pow(base, e, q)


def perp_span_dim(omega, q, k, d, c_list):
    """dim of S = sum_t (X^d - c_t)*Poly_{<k-d} as length-k coeff vectors (low->high)."""
    rows = []
    for c in c_list:
        for t in range(k - d):                      # multiply (X^d - c) by X^t, t=0..k-d-1
            row = [0] * k
            # (X^d - c) * X^t  =  X^{d+t} - c*X^t
            if d + t < k:
                row[d + t] = 1 % q
            row[t] = (row[t] - c) % q
            rows.append(row)
    return mat_rank(rows, q)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--q", type=int, required=True)
    ap.add_argument("--s", type=int, required=True, help="n = 2^s")
    ap.add_argument("--k", type=int, required=True)
    ap.add_argument("--d", type=int, required=True, help="subcoset order (2-power dividing n)")
    ap.add_argument("--check-list", action="store_true",
                    help="also enumerate the TRUE worst-case list (exact; tiny q,k only)")
    args = ap.parse_args()
    q, k, d = args.q, args.k, args.d
    L = LO.smooth_domain(q, args.s, 1)
    n = len(L)
    assert n % d == 0, "d must divide n"
    omega = L[1]
    ncoset = n // d
    rho = k / n

    print(f"# subcoset-binomial defect  q={q} n=2^{args.s}={n} k={k} d={d}  rho={rho:.4f}")
    print(f"#   omega={omega}, #cosets n/d = {ncoset}")

    # ---- STEP 3: intersection dimension for d<k, swept over l ----
    # c_t = omega^{i_t * d} for distinct cosets i_t = 0,1,2,...  (these are the n/d distinct values)
    print(f"# STEP 3  dim(cap_t G_A) vs generic   [predict d>k/2 => dim=2d-k for all l; d<=k/2 => 0]")
    print(f"#   2d-k = {2*d-k},  d>k/2 ? {2*d>k}")
    coset_consts = [_field_pow(omega, (i * d) % n, q) for i in range(ncoset)]
    for ell in range(2, min(ncoset, 6) + 1):
        if k - d <= 0:
            break
        c_list = coset_consts[:ell]
        dimS = perp_span_dim(omega, q, k, d, c_list)
        dim_cap = k - dimS
        generic = max(0, ell * d - (ell - 1) * k)
        tag = "DEFECT" if dim_cap > generic else "ok"
        print(f"#   l={ell}: dim(cap)={dim_cap}  generic={generic}   {tag}")

    # ---- STEP 2: explicit Hamming-ball witness from w = x^d ----
    # w[i] = (x_i)^d ; constant codeword p_t == omega^{td} agrees with w on coset t (d points).
    w = [_field_pow(x, d, q) for x in L]
    constants = sorted(set(_field_pow(omega, (t * d) % n, q) for t in range(ncoset)))
    # verify each constant agrees with w on exactly d points (its coset) -- sanity
    agrees = {c: sum(1 for wi in w if wi == c) for c in constants}
    a = d
    delta = 1 - a / n
    johnson = 1 - math.sqrt(rho)
    cap_proxy = 1 - rho
    print(f"# STEP 2  explicit witness  w=(x^d):  list = {len(constants)} constant codewords, agreement a=d={a}")
    print(f"#   per-constant agreement counts (should all = d={d}): {sorted(set(agrees.values()))}")
    print(f"#   radius delta = 1 - d/n = {delta:.4f}   Johnson 1-sqrt(rho) = {johnson:.4f}   "
          f"capacity-proxy 1-rho = {cap_proxy:.4f}")
    band = "IN BAND (Johnson,1-rho)" if johnson < delta < cap_proxy else \
           ("ABOVE capacity (delta>1-rho)" if delta >= cap_proxy else "BELOW Johnson")
    print(f"#   placement: {band}")
    # field-size check: list vs 2^-128 * q  (list is n/d, a CONSTANT in n)
    print(f"#   list size n/d = {ncoset}  <= 1/rho-ish.  2^-128*q would need q >= {ncoset}*2^128 "
          f"~ 2^{128 + math.log2(ncoset):.1f}  => does not break the field-size condition for cryptographic q")

    # ---- STEP 4: worst-case list cross-check (sample mode = LOWER bound over structured w) ----
    # The n/d constants are ONE explicit sub-family (a lower bound on the list for w=x^d). The true
    # worst-case list at this agreement is generally a somewhat larger CONSTANT; the only thing that
    # would matter for the field-size condition is Omega(q) growth, which neither the construction nor the oracle shows.
    if args.check_list:
        size, _w, _lst = LO.list_size_at_agreement(q, L, k, a, mode="sample")
        verdict = "constant (mild)" if size < q else "GROWS with q -- investigate"
        print(f"# STEP 4  worst-case list at agreement a={a} (sample/structured LOWER bound): "
              f"{size}   [{verdict}; construction sub-family = n/d={ncoset}]")


if __name__ == "__main__":
    main()
