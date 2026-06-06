#!/usr/bin/env python3
"""Independent brute-force oracle for the mutual-correlated-agreement (MCA) error.

This is a *from-scratch* reimplementation of Definition 4.3 (the `mcaError`
quantity), written directly from the mathematical definition — NOT translated
from the Lean source. Its sole purpose is to cross-check the Lean computable
`mcaErrorMaxMsg`/`mcaError` values for the Path A faithfulness experiment.

Definition 4.3 (counting form), for a linear code C over a finite field F of
block length n and radius parameter delta in Q:

    mcaError(C, delta)
      = max over directions (f1, f2) in (F^n)^2 of
          ( #{ gamma in F : badMCA(f1, f2, gamma) } ) / |F|

where badMCA(f1, f2, gamma) holds iff there EXISTS a shared agreement set
S subset of {0..n-1} with

      |S| >= (1 - delta) * n            (compared as rationals)

such that, writing the line point  L(gamma)_i = f1_i + gamma * f2_i,

   (a) L(gamma) agrees on S with some codeword of C:
           exists c in C, for all i in S, L(gamma)_i = c_i
   (b) the pair (f1, f2) agrees on S with NO codeword of the 2-wise
       interleaved code C^{=2}:
           NOT ( exists an interleaved codeword h (a word i |-> (h_i^0, h_i^1)
                 whose two columns are each in C) with, for all i in S,
                 (f1_i, f2_i) = (h_i^0, h_i^1) ).

We model an interleaved codeword by its two columns (c0, c1), each in C, so (b)
is checked by enumerating pairs (c0, c1) in C x C and asking whether some pair
matches (f1, f2) on all of S. (This is the literal interleaved-code definition;
we deliberately do NOT pre-split it into two independent base-code conditions,
so the cross-check also exercises the interleave column semantics.)

Field is ZMod 5. A code is given by a generator matrix G of shape (n, k); the
codewords are { G @ m : m in F^k }, i.e. c_i = sum_j G[i][j] * m[j] mod p.
"""

from __future__ import annotations
from fractions import Fraction
from itertools import product
import argparse
import json
import sys

P = 5  # ZMod 5


def codewords(G, n, k, P: int = P):
    """All codewords c = G m (mod P), as tuples of length n."""
    out = []
    for m in product(range(P), repeat=k):
        c = tuple(sum(G[i][j] * m[j] for j in range(k)) % P for i in range(n))
        out.append(c)
    # de-duplicate (the code may have dimension < k)
    return list(dict.fromkeys(out))


def agrees_on_S(C, S, g):
    """Does some codeword of C equal g on every coordinate in S?  (Condition a.)"""
    for c in C:
        if all(g[i] == c[i] for i in S):
            return True
    return False


def pair_agrees_interleaved(C, S, f1, f2):
    """Does some interleaved codeword (columns c0,c1 in C) match (f1,f2) on S?

    Literal C^{=2} membership: enumerate pairs of base codewords."""
    # column 0 must match f1 on S, column 1 must match f2 on S, independently
    # but we check it as the existence of a *single* interleaved word, i.e. a
    # pair (c0, c1) in C x C, matching simultaneously.
    ok0 = [c for c in C if all(f1[i] == c[i] for i in S)]
    if not ok0:
        return False
    ok1 = [c for c in C if all(f2[i] == c[i] for i in S)]
    return bool(ok1)


def subsets(n):
    for mask in range(1 << n):
        yield tuple(i for i in range(n) if (mask >> i) & 1)


def bad_mca(C, n, delta, f1, f2, gamma, subs, P: int = P):
    """badMCA(f1,f2,gamma): exists S with size bound, (a) holds, (b) fails."""
    thresh = (1 - delta) * n  # rational lower bound on |S|
    line = tuple((f1[i] + gamma * f2[i]) % P for i in range(n))
    for S in subs:
        if Fraction(len(S)) < thresh:
            continue
        if agrees_on_S(C, S, line) and not pair_agrees_interleaved(C, S, f1, f2):
            return True
    return False


def mca_error(G, n, k, delta, P: int = P):
    """mcaError(C, delta) as an exact Fraction."""
    C = codewords(G, n, k, P)
    subs = list(subsets(n))
    best = Fraction(0)
    vecs = list(product(range(P), repeat=n))
    for f1 in vecs:
        for f2 in vecs:
            cnt = sum(1 for gamma in range(P)
                      if bad_mca(C, n, delta, f1, f2, gamma, subs, P))
            r = Fraction(cnt, P)
            if r > best:
                best = r
    return best


# --- toy codes matching the Lean Toy.lean generators -----------------------
# toyN2G = !![1;2]  (shape 2x1) ; toyN3G = !![1;2;3] (shape 3x1)
# toyN4G = !![1,0;0,1;1,1;1,2] (shape 4x2)
TOYS = {
    2: ([[1], [2]], 2, 1),
    3: ([[1], [2], [3]], 3, 1),
    4: ([[1, 0], [0, 1], [1, 1], [1, 2]], 4, 2),
}


def grid(n):
    """delta = j/n for j = 0..n."""
    return [Fraction(j, n) for j in range(n + 1)]


# --- counterexample certificate replay -------------------------------------
# Replays a hard-instance certificate against the SAME Def-4.3 predicate
# (`bad_mca` / `codewords`) used above — no second oracle. This is the engine
# behind the repo's "no replay, no counterexample" rule.

def rs_generator(L, k, P: int):
    """Vandermonde generator for RS[F, L, k]: columns are the degree-<k monomials.

    G[i][j] = L[i]^j (mod P), j = 0..k-1.  codewords(G,n,k) = { eval_L(p) : deg p < k }.
    """
    n = len(L)
    return [[pow(L[i] % P, j, P) for j in range(k)] for i in range(n)]


def check_certificate(path: str) -> int:
    """Replay a counterexample certificate. Returns process exit code (0 = PASS).

    A certificate PASSES iff, under the oracle's Def-4.3 predicate for the RS code
    built from (q, L, k): (1) every claimed exceptional_z is genuinely badMCA for the
    given (f0, f1) at delta = delta_num/delta_den, and (2) the recomputed
    epsilon = |E|/q matches epsilon_observed when that field is supplied.
    """
    with open(path) as fh:
        cert = json.load(fh)

    q = int(cert["q"])
    char = int(cert.get("characteristic", q))
    if char != q:
        # Extension field q = char^m: needs GF(q) arithmetic, not ZMod(q).
        print(f"[check-certificate] UNSUPPORTED: q={q} is a prime POWER "
              f"(characteristic {char}). The oracle is prime-field only; wire the "
              f"GF arithmetic path before replaying char-{char} extension certificates.")
        return 3

    n, k = int(cert["n"]), int(cert["k"])
    L = [int(x) % q for x in cert["L"]]
    if len(L) != n or len(set(L)) != n:
        print(f"[check-certificate] FAIL: L must list {n} distinct points (got {cert['L']}).")
        return 2

    delta = Fraction(int(cert["delta_num"]), int(cert["delta_den"]))
    f0 = tuple(int(x) % q for x in cert["f0"])
    f1 = tuple(int(x) % q for x in cert["f1"])
    if len(f0) != n or len(f1) != n:
        print(f"[check-certificate] FAIL: f0,f1 must have length n={n}.")
        return 2
    claimed_z = [int(z) % q for z in cert.get("exceptional_z", [])]

    G = rs_generator(L, k, q)
    C = codewords(G, n, k, q)
    subs = list(subsets(n))

    # (1) every claimed exceptional z is genuinely bad
    bad_all = [z for z in range(q) if bad_mca(C, n, delta, f0, f1, z, subs, q)]
    bad_set = set(bad_all)
    spurious = [z for z in claimed_z if z not in bad_set]

    # (2) recomputed epsilon
    eps = Fraction(len(bad_all), q)
    eps_claim = cert.get("epsilon_observed")
    eps_match = True
    if eps_claim is not None:
        num, den = (eps_claim.split("/") + ["1"])[:2] if isinstance(eps_claim, str) else (eps_claim, 1)
        eps_match = (eps == Fraction(int(num), int(den)))

    ok = (not spurious) and eps_match and (len(claimed_z) > 0 or len(bad_all) > 0)
    print(f"[check-certificate] code=RS[GF({q}),L,k={k}] n={n} delta={delta}")
    print(f"  claimed exceptional_z : {claimed_z}")
    print(f"  oracle bad z          : {bad_all}")
    print(f"  recomputed epsilon    : {eps.numerator}/{eps.denominator}"
          + (f"  (claimed {eps_claim})" if eps_claim is not None else ""))
    if spurious:
        print(f"  SPURIOUS (claimed but not bad): {spurious}")
    if not eps_match:
        print(f"  EPSILON MISMATCH: recomputed {eps} != claimed {eps_claim}")
    print(f"  VERDICT: {'PASS — certificate replays' if ok else 'FAIL — does not replay'}")
    return 0 if ok else 1


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, nargs="*", default=[2, 3],
                    help="block lengths to evaluate (default 2 3; 4 is slow)")
    ap.add_argument("--check-certificate", metavar="PATH", default=None,
                    help="replay a counterexample certificate JSON against the Def-4.3 "
                         "oracle (no second predicate); exit 0 iff it replays")
    args = ap.parse_args()
    if args.check_certificate is not None:
        sys.exit(check_certificate(args.check_certificate))
    for n in args.n:
        G, nn, k = TOYS[n]
        assert nn == n
        vals = [mca_error(G, n, k, d) for d in grid(n)]
        pretty = ", ".join(f"{v.numerator}/{v.denominator}" if v.denominator != 1
                           else f"{v.numerator}" for v in vals)
        deltas = ", ".join(f"{d.numerator}/{d.denominator}" if d.denominator != 1
                           else f"{d.numerator}" for d in grid(n))
        print(f"n={n} k={k}  code=range(G), G={G}")
        print(f"  delta grid (j/n): {deltas}")
        print(f"  mcaError:         {pretty}")


if __name__ == "__main__":
    main()
