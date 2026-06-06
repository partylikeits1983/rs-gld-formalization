#!/usr/bin/env python3
"""MDS(3) structural test for smooth multiplicative cosets — calibrated, symmetry-reduced.

Tests BGM Def 1.8 at order ℓ=3 (the first nontrivial higher-order MDS): is `RS[L,k]` MDS(3) for
`L = μ_{2^s}`? MDS(3) ⟺ for every triple of subsets `A_1,A_2,A_3 ⊆ [n]` (size ≤ k), the column-span
intersection `dim(G_{A_1} ∩ G_{A_2} ∩ G_{A_3})` equals the GENERIC value. We compute it via
`dim(∩) = k − rank(G_{A_1}^⊥ ∪ G_{A_2}^⊥ ∪ G_{A_3}^⊥)`, where `G_A^⊥` (degree-`<k` polys vanishing on
`A`) has basis `{∏_{j∈A}(X−x_j)·X^t : 0 ≤ t < k−|A|}` (coefficient vectors in `GF(q)^k`).

**Smooth-specific defect** (the correct, overlap-safe criterion): for the SAME index-triple,
`dim(∩)_smooth > dim(∩)_random`. Forced (overlap) intersection cancels between the two; only a
genuine coset coincidence survives. Compared against a uniformly random evaluation set of the same
`(n,k,q)`.

**Calibration (positive control).** A *constructed* point set with a KNOWN MDS(3) failure — three
disjoint `(k−1)`-subsets whose vanishing polys are linearly dependent (`q_3 = q_1 + λ q_2`). The test
MUST flag it; otherwise the test is not sensitive and a null result is meaningless.

**Symmetry reduction.** `L = μ_{2^s}` is closed under the cyclic shift `i ↦ i+1 (mod n)`
(multiplication by `ω`), which preserves all ranks; and under relabeling of the three sets. We
enumerate triples of `(k−1)`-subsets up to cyclic shift (fix `0 ∈ A_1`) and relabeling
(`A_1 ≤ A_2 ≤ A_3` lexicographically) — exhaustive over orbit representatives, not sampled.
"""
from __future__ import annotations
import argparse, os, sys
from itertools import combinations
sys.path.insert(0, os.path.dirname(__file__))
import list_size_oracle as LO
from smooth_coset_higher_order_mds import mat_rank, random_eval_set


def vanishing_poly(points, q):
    """Coefficients (low→high) of ∏_{x in points}(X − x) mod q."""
    c = [1]
    for x in points:
        nc = [0] * (len(c) + 1)
        for i, ci in enumerate(c):
            nc[i + 1] = (nc[i + 1] + ci) % q
            nc[i] = (nc[i] - ci * x) % q
        c = nc
    return c


def perp_basis(A_points, q, k):
    """Basis of {deg<k polys vanishing on A_points}: V(X)·X^t, t=0..k-|A|-1, as length-k coeff vectors."""
    V = vanishing_poly(A_points, q)              # degree |A|
    rows = []
    for t in range(k - len(A_points)):
        row = [0] * k
        for i, ci in enumerate(V):
            if i + t < k:
                row[i + t] = ci % q
        rows.append(row)
    return rows


def inter_dim(L, A1, A2, A3, q, k):
    """dim(G_{A1} ∩ G_{A2} ∩ G_{A3}) = k − rank(stacked perp-bases)."""
    rows = (perp_basis([L[i] for i in A1], q, k)
            + perp_basis([L[i] for i in A2], q, k)
            + perp_basis([L[i] for i in A3], q, k))
    return k - mat_rank(rows, q)


def cyclic_relabel_reps(n, k):
    """Orbit reps of triples of (k-1)-subsets under cyclic shift (0 ∈ A1) and relabeling (A1≤A2≤A3)."""
    subs = list(combinations(range(n), k - 1))
    a1s = [A for A in subs if 0 in A]            # cyclic-shift rep: A1 contains 0
    out = []
    for A1 in a1s:
        for A2 in subs:
            if A2 < A1:
                continue
            for A3 in subs:
                if A3 < A2:
                    continue
                out.append((A1, A2, A3))
    return out


def scan(L, Lrand, q, k, reps, label):
    """Count smooth-specific MDS(3) defects: dim(∩)_L > dim(∩)_random on the same triple."""
    ndef = 0; first = None
    for (A1, A2, A3) in reps:
        ds = inter_dim(L, A1, A2, A3, q, k)
        dr = inter_dim(Lrand, A1, A2, A3, q, k)
        if ds > dr:
            ndef += 1
            if first is None:
                first = (A1, A2, A3, ds, dr)
    return ndef, first


def positive_control(q, k):
    """Construct a point set with a KNOWN MDS(3) failure (k=3): three disjoint 2-subsets whose
    vanishing quadratics are dependent (q3 = q1 + q2). Returns the point list or None."""
    if k != 3:
        return None
    # q1=(X-1)(X-2), q2=(X-3)(X-4); q3=q1+q2 (monic deg-2). Find its roots; if split & disjoint, use them.
    q1 = vanishing_poly([1, 2], q)               # [2,-3,1]
    q2 = vanishing_poly([3, 4], q)               # [12,-7,1]
    # q3 = q1 + q2 = X^2 + (-10)X + 14 ... but leading coeff 2; normalize to monic by halving
    s = [(q1[i] + q2[i]) % q for i in range(3)]  # 2X^2 -10X +14  → not monic
    inv2 = pow(2, q - 2, q)
    s = [(c * inv2) % q for c in s]              # monic X^2 -5X +7
    roots = [x for x in range(q) if (s[0] + s[1] * x + s[2] * x * x) % q == 0]
    roots = [r for r in roots if r not in (1, 2, 3, 4)]
    if len(set(roots)) < 2:
        return None
    e, f = roots[0], roots[1]
    return [1, 2, 3, 4, e, f]                     # subsets {0,1},{2,3},{4,5} are q1,q2,(q1+q2)/2 — dependent


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--q", type=int, required=True)
    ap.add_argument("--s", type=int, required=True, help="n=2^s")
    ap.add_argument("--k", type=int, required=True)
    ap.add_argument("--coset", type=int, default=1)
    args = ap.parse_args()
    L = LO.smooth_domain(args.q, args.s, args.coset)
    n = len(L)
    Lrand = random_eval_set(args.q, n, seed=2024)
    reps = cyclic_relabel_reps(n, args.k)
    print(f"# MDS(3) test  q={args.q} n=2^{args.s}={n} k={args.k}  ({len(reps)} cyclic/relabel orbit reps)")
    print(f"#   L_smooth = mu_{n} = {L}")
    # calibration
    pc = positive_control(args.q, args.k)
    if pc is not None:
        # the constructed defect triple {0,1},{2,3},{4,5} on pc
        ds = inter_dim(pc, (0, 1), (2, 3), (4, 5), args.q, args.k)
        dr = inter_dim(random_eval_set(args.q, 6, seed=7), (0, 1), (2, 3), (4, 5), args.q, args.k)
        ok = ds > dr
        print(f"#   POSITIVE CONTROL (constructed defect set {pc}): dim_defect={ds} dim_random={dr} "
              f"-> {'DETECTED ✓ (test is sensitive)' if ok else 'NOT detected ✗ (test INSENSITIVE)'}")
    else:
        print(f"#   POSITIVE CONTROL: (only implemented for k=3)")
    ndef, first = scan(L, Lrand, args.q, args.k, reps, "smooth")
    print(f"#   *** smooth-specific MDS(3) defects: {ndef} / {len(reps)} ***")
    if first:
        print(f"#   first: A1={first[0]} A2={first[1]} A3={first[2]}  dim_smooth={first[3]} dim_random={first[4]}")
    else:
        print(f"#   none — mu_{n} satisfies MDS(3) on all orbit reps (matches random/generic)")


if __name__ == "__main__":
    main()
