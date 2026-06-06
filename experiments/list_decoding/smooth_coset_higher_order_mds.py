#!/usr/bin/env python3
"""Structural test (Phase 3.3): do smooth multiplicative cosets satisfy higher-order MDS?

NOT a list-size sweep. Tests the rank/linear-dependence condition behind higher-order MDS / GM-MDS
directly, on `L = a·μ_{2^s}` vs random evaluation sets.

The concrete core of higher-order MDS (Roth / Brakensiek–Gopi–Makam). A column-span of `k−1` columns
of the `k×n` RS Vandermonde is a hyperplane in `GF(q)^k`, whose unique (up to scale) defining covector
is the coefficient vector of the **vanishing polynomial** `∏_{j∈A}(X − x_j)` (degree `k−1`). The
intersection `⋂_i span(A_i)` of `ℓ` such hyperplanes has dimension `k − rank(M)`, where `M` is the
`ℓ×k` matrix of those vanishing-poly coefficient vectors. **Generic (random) points:** the `ℓ`
vanishing polys of *distinct* `(k−1)`-subsets are linearly **independent** (rank `min(ℓ,k)`) — the
higher-order-MDS / generic value. A **DEFECT** is `rank(M) < min(ℓ,k)`: the smooth-coset structure
forces a linear dependence among the vanishing polynomials that a random set avoids. Such dependencies
are exactly the obstruction to the random-RS-capacity machinery (BGM MDS(ℓ) ⇒ list-decodable).

This is a *structural* witness only (finite, exact). It does NOT prove an asymptotic list-size
statement without a theorem — see `research/smooth_coset_genericity_attack.md`.
"""
from __future__ import annotations

import argparse
import math
import os
import sys
from itertools import combinations

sys.path.insert(0, os.path.dirname(__file__))
import list_size_oracle as LO  # smooth_domain, _is_prime, multiplicative_generator


# ---- prime-field GF(q) linear algebra (q prime) ----

def mat_rank(rows, q):
    """Rank over GF(q) (q prime) by Gaussian elimination. rows = list of list[int]."""
    M = [list(r) for r in rows]
    nrows = len(M)
    ncols = len(M[0]) if nrows else 0
    rank = 0
    col = 0
    for col in range(ncols):
        piv = None
        for i in range(rank, nrows):
            if M[i][col] % q != 0:
                piv = i
                break
        if piv is None:
            continue
        M[rank], M[piv] = M[piv], M[rank]
        inv = pow(M[rank][col], q - 2, q)
        M[rank] = [(x * inv) % q for x in M[rank]]
        for i in range(nrows):
            if i != rank and M[i][col] % q != 0:
                f = M[i][col]
                M[i] = [(M[i][j] - f * M[rank][j]) % q for j in range(ncols)]
        rank += 1
        if rank == nrows:
            break
    return rank


def mat_det(rows, q):
    """Determinant of a square matrix over GF(q) (q prime) via Gaussian elimination."""
    M = [list(r) for r in rows]
    n = len(M)
    det = 1
    for col in range(n):
        piv = None
        for i in range(col, n):
            if M[i][col] % q != 0:
                piv = i; break
        if piv is None:
            return 0
        if piv != col:
            M[col], M[piv] = M[piv], M[col]
            det = (-det) % q
        det = (det * M[col][col]) % q
        inv = pow(M[col][col], q - 2, q)
        for i in range(col + 1, n):
            if M[i][col] % q != 0:
                f = (M[i][col] * inv) % q
                M[i] = [(M[i][j] - f * M[col][j]) % q for j in range(n)]
    return det % q


def gm_mds_matrix(L, Ss, B, q):
    """The GM-MDS / higher-order-MDS test matrix [∏_{l∈S_i}(α_b − α_l)]_{i, b∈B} (BGM Thm 1.12 RS form).
    `Ss` = k zero-pattern subsets (index lists into L); `B` = k column indices into L."""
    rows = []
    for S in Ss:
        row = []
        for b in B:
            p = 1
            for l in S:
                p = (p * (L[b] - L[l])) % q
            row.append(p)
        rows.append(row)
    return rows


def vanishing_coeffs(subset_points, q, k):
    """Coefficient vector (length k) of ∏_{x in subset}(X - x) mod q, a degree-(|subset|) poly.
    For |subset| = k-1 this is a degree-(k-1) poly = a covector in GF(q)^k."""
    coeffs = [1]  # constant poly 1
    for x in subset_points:
        # multiply by (X - x)
        new = [0] * (len(coeffs) + 1)
        for i, c in enumerate(coeffs):
            new[i + 1] = (new[i + 1] + c) % q          # X * c
            new[i] = (new[i] - c * x) % q              # -x * c
        coeffs = new
    # pad to length k
    coeffs += [0] * (k - len(coeffs))
    return coeffs[:k]


def compare_defects(Lsmooth, Lrand, q, k, ell, max_tuples, seed=0):
    """For the SAME ell-tuples of (k-1)-subsets, compute the vanishing-poly-matrix rank on the smooth
    coset vs the random set. A *smooth-specific* defect = the random set is generic (full rank
    min(ell,k)) but the smooth coset is rank-deficient there — isolating coset structure from trivial
    shared-point dependences (which hit both sets equally). Returns
    (n_tested, n_both_deficient, n_smooth_specific, first_smooth_specific_or_None)."""
    n = len(Lsmooth)
    subsets = list(combinations(range(n), k - 1))
    target = min(ell, k)
    state = (seed * 1103515245 + 12345) & 0x7FFFFFFF
    def nxt():
        nonlocal state
        state = (state * 1103515245 + 12345) & 0x7FFFFFFF
        return state
    n_tested = 0; n_both = 0; n_smooth_only = 0; first = None
    seen = set(); nsub = len(subsets); attempts = 0
    while n_tested < max_tuples and attempts < max_tuples * 20:
        attempts += 1
        idxs = tuple(sorted({nxt() % nsub for _ in range(ell)}))
        if len(idxs) != ell or idxs in seen:
            continue
        seen.add(idxs)
        rk_s = mat_rank([vanishing_coeffs([Lsmooth[j] for j in subsets[si]], q, k) for si in idxs], q)
        rk_r = mat_rank([vanishing_coeffs([Lrand[j] for j in subsets[si]], q, k) for si in idxs], q)
        n_tested += 1
        if rk_s < target and rk_r < target:
            n_both += 1
        elif rk_s < target and rk_r == target:
            n_smooth_only += 1
            if first is None:
                first = ([subsets[si] for si in idxs], rk_s, target)
    return n_tested, n_both, n_smooth_only, first


def random_eval_set(q, n, seed):
    """A pseudo-random set of n distinct nonzero points in GF(q) (deterministic LCG)."""
    state = (seed * 2654435761 + 40503) & 0x7FFFFFFF
    def nxt():
        nonlocal state
        state = (state * 1103515245 + 12345) & 0x7FFFFFFF
        return state
    pts = []
    seen = set()
    while len(pts) < n:
        x = 1 + nxt() % (q - 1)
        if x not in seen:
            seen.add(x); pts.append(x)
    return pts


def gmmds_compare(Lsmooth, Lrand, q, k, max_tuples, seed=0):
    """The EXACT GM-MDS test (BGM Thm 1.12). Sample zero-patterns `S_1..S_k` (each |S_i|=k-1) and a
    k-subset `B` of columns; compute `det[∏_{l∈S_i}(α_b−α_l)]` for the smooth coset vs a random set.
    A **smooth-specific defect** = det_random ≠ 0 (so the pattern is generically MDS / Hall-valid) but
    det_smooth = 0 (the cyclotomic structure forces a higher-order-MDS failure a random set avoids).
    Returns (n_generic, n_both_zero, n_smooth_defect, first_defect)."""
    n = len(Lsmooth)
    state = (seed * 1103515245 + 12345) & 0x7FFFFFFF
    def nxt():
        nonlocal state
        state = (state * 1103515245 + 12345) & 0x7FFFFFFF
        return state
    def rand_subset(size):
        s = set()
        while len(s) < size:
            s.add(nxt() % n)
        return sorted(s)
    n_generic = 0; n_both0 = 0; n_smooth = 0; first = None
    for _ in range(max_tuples):
        Ss = [rand_subset(k - 1) for _ in range(k)]
        B = rand_subset(k)
        ds = mat_det(gm_mds_matrix(Lsmooth, Ss, B, q), q)
        dr = mat_det(gm_mds_matrix(Lrand, Ss, B, q), q)
        if dr != 0:
            n_generic += 1
            if ds == 0:
                n_smooth += 1
                if first is None:
                    first = (Ss, B)
        elif ds == 0:
            n_both0 += 1
    return n_generic, n_both0, n_smooth, first


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--q", type=int, required=True)
    ap.add_argument("--s", type=int, required=True, help="smooth domain n=2^s")
    ap.add_argument("--k", type=int, required=True)
    ap.add_argument("--max-tuples", type=int, default=20000)
    ap.add_argument("--coset", type=int, default=1)
    args = ap.parse_args()

    Lsmooth = LO.smooth_domain(args.q, args.s, args.coset)
    n = len(Lsmooth)
    Lrand = random_eval_set(args.q, n, seed=12345)
    print(f"# GM-MDS / higher-order-MDS structural test (BGM Thm 1.12 det form)  "
          f"q={args.q} n=2^{args.s}={n} k={args.k}")
    print(f"#   L_smooth = a*mu_{n} = {Lsmooth}")
    print(f"#   test: det[∏_{{l∈S_i}}(α_b−α_l)]; smooth-defect = random nonzero (Hall-valid) but smooth zero")
    ng, nb, nsd, first = gmmds_compare(Lsmooth, Lrand, args.q, args.k, args.max_tuples)
    print(f"#   Hall-valid patterns sampled (random det≠0): {ng}")
    print(f"#   both-zero (Hall-INvalid pattern, excluded):  {nb}")
    print(f"#   *** SMOOTH-SPECIFIC GM-MDS defects: {nsd} ***")
    if first is not None:
        print(f"#   first smooth defect: S={first[0]} B={first[1]}")
    else:
        print(f"#   no smooth-specific defect found in {ng} Hall-valid patterns "
              f"(consistent with: status OPEN, no cyclotomic defect at this size)")


if __name__ == "__main__":
    main()
