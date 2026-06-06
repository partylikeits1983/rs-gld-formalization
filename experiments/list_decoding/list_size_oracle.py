#!/usr/bin/env python3
"""Worst-case combinatorial list-size oracle for plain RS on a SMOOTH domain.

Workstream A of the grand-list-decoding push (eprint 2026/680). This is the
empirical frontier engine: for `C = RS[GF(q), L, k]` with `L` a smooth domain
(multiplicative coset of a 2-power-order subgroup of `F*`, Def 2.12), it computes

    listSizeAtAgreement(C, a) := max over received words w in F^n of
                                 #{ c in C : agreement(c, w) >= a },

i.e. the worst-case list size at absolute agreement threshold `a` (errors n-a,
relative radius delta = (n-a)/n = 1 - a/n). The prize condition is the integer
statement `2^128 * listSize <= q`.

SINGLE-ORACLE RULE. Field/RS arithmetic is REUSED from `scripts/mca_oracle.py`
via `rs_generator` / `codewords` (the same generator the MCA oracle and the
certificate replayer use). This file does NOT re-implement RS or the field. It
DOES define the agreement / list-size predicate, which is a *different* quantity
from Def 4.3 (MCA) — that is deliberately new here.

REACH (honest limits). The exact worst case enumerates all q^n received words.
  - exhaustive (`--mode exact`): comfortable for q^n <= ~1e8 (n in {2,4}; n=8
    only for tiny q). This is the only mode that yields a true UPPER bound on the
    worst-case list size.
  - sampled (`--mode sample`): probes structured + random w; yields a LOWER bound
    (a witnessed list of that size exists). Use for larger n to DETECT blow-up;
    never report a sampled result as "worst case <= X".
Always print the mode and the searched range. Never claim "list <= X" from a
sampled run.

CERTIFICATE. `--check-certificate <file>` replays a list-size certificate against
this same predicate (no second implementation), mirroring mca_oracle.py's rule:
no replay, no result.
"""
from __future__ import annotations

import argparse
import json
import math
import os
import sys
from fractions import Fraction
from itertools import product

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "scripts"))
import mca_oracle as O  # noqa: E402  the single source of RS + field arithmetic


# --------------------------------------------------------------------------
# Smooth domains (Def 2.12): multiplicative coset of a 2-power-order subgroup.
# --------------------------------------------------------------------------

def _is_prime(q: int) -> bool:
    if q < 2:
        return False
    for d in range(2, int(math.isqrt(q)) + 1):
        if q % d == 0:
            return False
    return True


def multiplicative_generator(q: int) -> int:
    """A generator of GF(q)* for prime q (brute force; q is tiny here)."""
    assert _is_prime(q), f"smooth-domain helper is prime-field only (got q={q})"
    order = q - 1
    # prime factors of q-1
    factors, m = set(), order
    d = 2
    while d * d <= m:
        while m % d == 0:
            factors.add(d)
            m //= d
        d += 1
    if m > 1:
        factors.add(m)
    for g in range(2, q):
        if all(pow(g, order // p, q) != 1 for p in factors):
            return g
    raise RuntimeError(f"no generator found for GF({q})")


def smooth_domain(q: int, s: int, coset: int = 1):
    """L = coset * H where H <= GF(q)* has order n = 2^s (a 2-power subgroup).

    Requires 2^s | q-1. Returns the n distinct points as a list of ints in [0,q).
    `coset` is a representative; coset=1 gives the subgroup itself. Smooth per
    Def 2.12 (multiplicative coset of a 2-power-order subgroup).
    """
    n = 1 << s
    assert (q - 1) % n == 0, f"2^{s}={n} does not divide q-1={q-1}; no smooth domain"
    g = multiplicative_generator(q)
    h = pow(g, (q - 1) // n, q)          # generator of the order-n subgroup H
    H = [pow(h, i, q) for i in range(n)]
    L = [(coset % q) * x % q for x in H]
    assert len(set(L)) == n, "coset collapsed (coset must be a unit)"
    return L


# --------------------------------------------------------------------------
# List size at an agreement threshold.
# --------------------------------------------------------------------------

def agreement(c, w) -> int:
    """#{ i : c_i == w_i }."""
    return sum(1 for ci, wi in zip(c, w) if ci == wi)


def list_at(C, w, a: int):
    """The codewords of C agreeing with w on >= a coordinates."""
    return [c for c in C if agreement(c, w) >= a]


def _plurality(chosen, n):
    """Coordinate-wise plurality word of a set of codewords (worst-case-optimal w
    for that exact target list: maximises everyone's agreement simultaneously)."""
    w = []
    for i in range(n):
        counts = {}
        for c in chosen:
            counts[c[i]] = counts.get(c[i], 0) + 1
        w.append(max(counts, key=counts.get))
    return tuple(w)


def _structured_received_words(C, q: int, n: int, extra_random: int = 0, seed: int = 0,
                               pairs: bool = True, triples_budget: int = 200000):
    """Generator of candidate worst-case received words for the SAMPLED lower bound.

    Structured families that tend to maximise the list (in increasing strength):
      - every codeword itself;
      - plurality word of EVERY pair of codewords (exhaustive — catches every
        size>=2 cluster centred on a pair; O(|C|^2));
      - plurality word of triples, up to a budget (catches tighter clusters);
      - a deterministic LCG-seeded sprinkle of larger random subsets.

    Because the optimal w for a target list T is exactly the coordinate-wise
    plurality of T, scanning pluralities of small subsets is a principled lower
    bound, not a blind sample.
    """
    seen = set()

    def emit(w):
        t = tuple(w)
        if t not in seen:
            seen.add(t)
            return t
        return None

    nc = len(C)
    for c in C:                              # codewords themselves
        r = emit(c)
        if r is not None:
            yield r
    if pairs:
        for i in range(nc):
            for j in range(i + 1, nc):
                r = emit(_plurality((C[i], C[j]), n))
                if r is not None:
                    yield r
    # triples up to budget (deterministic order)
    budget = triples_budget
    for i in range(nc):
        if budget <= 0:
            break
        for j in range(i + 1, nc):
            if budget <= 0:
                break
            for l in range(j + 1, nc):
                if budget <= 0:
                    break
                budget -= 1
                r = emit(_plurality((C[i], C[j], C[l]), n))
                if r is not None:
                    yield r
    # larger random subsets (LCG-seeded, deterministic; no Math.random / time)
    state = (seed * 1103515245 + 12345) & 0x7FFFFFFF
    def nxt():
        nonlocal state
        state = (state * 1103515245 + 12345) & 0x7FFFFFFF
        return state
    for _ in range(extra_random):
        ksub = 2 + (nxt() % min(6, nc))
        chosen = [C[nxt() % nc] for _ in range(ksub)]
        r = emit(_plurality(chosen, n))
        if r is not None:
            yield r


def list_size_at_agreement(q, L, k, a, mode="exact", samples=20000, seed=0):
    """Worst-case list size at absolute agreement `a` for RS[GF(q), L, k].

    Returns (size, witness_w, witness_list). `mode='exact'` enumerates all q^n
    received words (true worst case / UPPER bound). `mode='sample'` probes
    structured + pseudo-random words (LOWER bound; a list of that size is exhibited).
    """
    n = len(L)
    G = O.rs_generator(L, k, q)
    C = O.codewords(G, n, k, q)
    best, best_w, best_list = 0, None, []

    if mode == "exact":
        for w in product(range(q), repeat=n):
            lst = list_at(C, w, a)
            if len(lst) > best:
                best, best_w, best_list = len(lst), w, lst
    elif mode == "sample":
        count = 0
        for w in _structured_received_words(C, q, n, extra_random=samples, seed=seed):
            lst = list_at(C, w, a)
            if len(lst) > best:
                best, best_w, best_list = len(lst), w, lst
            count += 1
        # note: count <= |C| + samples; report it in the caller
    else:
        raise ValueError(f"unknown mode {mode!r}")
    return best, best_w, best_list


# --------------------------------------------------------------------------
# Radius anchors (so every numeric result is placed against the theory).
# --------------------------------------------------------------------------

def anchors(n: int, k: int):
    """Absolute agreement thresholds for the canonical radii, as floats + ints.

    rho = k/n. Returns a dict name -> (agreement_fraction, absolute_agreement_a).
    - unique:  delta=(1-rho)/2  -> agree frac (1+rho)/2, a=(n+k)/2
    - johnson: delta=1-sqrt(rho) -> agree frac sqrt(rho), a=n*sqrt(rho)=sqrt(kn)
    - rate:    delta=1-rho       -> agree frac rho, a=k     (capacity is BELOW this delta)
    """
    rho = k / n
    return {
        "unique":  ((1 + rho) / 2, (n + k) / 2.0),
        "johnson": (math.sqrt(rho), math.sqrt(k * n)),
        "rate":    (rho, float(k)),
    }


# --------------------------------------------------------------------------
# Certificate emit / replay.
# --------------------------------------------------------------------------

def make_certificate(q, L, k, a, w, witness_list, mode):
    n = len(L)
    delta = Fraction(n - a, n)
    return {
        "kind": "list-size",
        "field": f"GF({q})", "q": q, "characteristic": q,
        "n": n, "k": k, "L": [x % q for x in L],
        "agreement_a": a,
        "delta_num": delta.numerator, "delta_den": delta.denominator,
        "received_w": list(w),
        "list_size": len(witness_list),
        "witness_list": [list(c) for c in witness_list],
        "search_mode": mode,
    }


def check_certificate(path: str) -> int:
    with open(path) as fh:
        cert = json.load(fh)
    if cert.get("kind") != "list-size":
        print(f"[check-certificate] not a list-size certificate (kind={cert.get('kind')!r})")
        return 2
    q = int(cert["q"])
    char = int(cert.get("characteristic", q))
    if char != q:
        print(f"[check-certificate] UNSUPPORTED prime power q={q} (char {char}); prime-field only.")
        return 3
    n, k = int(cert["n"]), int(cert["k"])
    L = [int(x) % q for x in cert["L"]]
    a = int(cert["agreement_a"])
    w = tuple(int(x) % q for x in cert["received_w"])
    if len(L) != n or len(set(L)) != n or len(w) != n:
        print("[check-certificate] FAIL: malformed L or w.")
        return 2

    G = O.rs_generator(L, k, q)
    C = O.codewords(G, n, k, q)
    recomputed = list_at(C, w, a)
    claimed = [tuple(c) for c in cert.get("witness_list", [])]
    recomputed_set = {tuple(c) for c in recomputed}

    # every claimed witness genuinely agrees on >= a and is a codeword
    bad = [c for c in claimed if (tuple(c) not in recomputed_set)]
    size_match = (len(recomputed) >= int(cert.get("list_size", len(claimed))))

    ok = (not bad) and size_match and len(recomputed) > 0
    print(f"[check-certificate] code=RS[GF({q}),L,k={k}] n={n} a={a} "
          f"delta={cert['delta_num']}/{cert['delta_den']}")
    print(f"  claimed list_size : {cert.get('list_size')}")
    print(f"  oracle list_size  : {len(recomputed)} (worst-case >= this for the given w)")
    if bad:
        print(f"  SPURIOUS witnesses (claimed but not in list): {bad}")
    print(f"  VERDICT: {'PASS — certificate replays' if ok else 'FAIL — does not replay'}")
    return 0 if ok else 1


# --------------------------------------------------------------------------
# CLI.
# --------------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--q", type=int, help="prime field size")
    ap.add_argument("--s", type=int, help="smooth-domain exponent: n = 2^s")
    ap.add_argument("--coset", type=int, default=1, help="coset representative (unit)")
    ap.add_argument("--k", type=int, help="RS dimension (deg < k)")
    ap.add_argument("--a", type=int, help="agreement threshold (default: sweep)")
    ap.add_argument("--mode", choices=["exact", "sample"], default="exact")
    ap.add_argument("--samples", type=int, default=20000)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--check-certificate", metavar="PATH", default=None)
    args = ap.parse_args()

    if args.check_certificate is not None:
        sys.exit(check_certificate(args.check_certificate))

    if args.q is None or args.s is None or args.k is None:
        ap.error("need --q --s --k (or --check-certificate)")

    L = smooth_domain(args.q, args.s, args.coset)
    n = len(L)
    rho = Fraction(args.k, n)
    anc = anchors(n, args.k)
    print(f"RS[GF({args.q}), smooth L (n=2^{args.s}={n}, coset={args.coset}), k={args.k}]  "
          f"rho={rho}  |C|={args.q ** args.k if args.k <= n else 'n/a'}")
    print(f"  L = {L}")
    print(f"  anchors (absolute agreement a): unique={anc['unique'][1]:.3f}  "
          f"johnson={anc['johnson'][1]:.3f}  rate(k)={anc['rate'][1]:.0f}")
    print(f"  mode={args.mode}" + (f" samples={args.samples}" if args.mode == "sample" else ""))

    a_values = [args.a] if args.a is not None else list(range(n, args.k, -1))
    print(f"  {'a':>3} {'delta':>7} {'listSize':>9}  note")
    for a in a_values:
        size, w, lst = list_size_at_agreement(
            args.q, L, args.k, a, mode=args.mode, samples=args.samples, seed=args.seed)
        delta = Fraction(n - a, n)
        note = []
        if a > anc["johnson"][1]:
            note.append("above-Johnson")
        elif a <= anc["johnson"][1] and a > anc["rate"][1]:
            note.append("BAND (Johnson..rate)")
        if abs(a - anc["unique"][1]) < 1:
            note.append("~unique")
        bound_ok = (2 ** 128) * size <= args.q
        note.append("prize-OK" if bound_ok else "prize-FAIL(small q)")
        print(f"  {a:>3} {str(delta):>7} {size:>9}  {' '.join(note)}")


if __name__ == "__main__":
    main()
