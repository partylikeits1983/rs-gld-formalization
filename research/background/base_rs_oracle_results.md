# Base-RS Frontier Oracle — finite-field counterexample search (Workstream BR-2)

**Engine:** `experiments/list_decoding/base_rs_oracle.py` (reuses `list_size_oracle.py` smooth-domain +
RS arithmetic). **Status of all results below: FINITE EVIDENCE ONLY, not asymptotic proof.** Date 2026-06-05.

**Goal.** Search fixed smooth-domain RS for a received word `w` with a large WORST-CASE base list
`B(η) = |Λ(RS[F,L,k], η)|` **beyond Johnson** (`η > 1−√ρ`), and decide whether `B(η) > 2^{-128}·|F|`
for large `q`. The prize now reduces (GLD-9 proved) to bounding `B(η)`; the prize fails iff
`B(η) > 2^{-128}·|F|` in the band. **We track the CONSTANT, not just `Ω(q)`** — a constant list does
not beat `2^{-128}·q` once `q > (constant)·2^{128}`.

## The strongest structured candidate: the multiplicative analogue of BKR

Ben-Sasson–Kopparty–Radhakrishnan's super-poly RS list is built from **subspace (linearized)
polynomials** vanishing on an **additive** subgroup. The literature map
(`research/base_rs_literature_map.md`) confirms there is **no known multiplicative analogue of the
BKR bad word**. We construct and test the natural candidate:

On a smooth domain `L` (a coset of a 2-power subgroup `H ≤ F*`, `|H|=n`), the vanishing polynomial of
an order-`d` **sub-coset** `c'·H_d` is the **binomial** `X^d − (c')^d` — the multiplicative analogue
of a subspace polynomial. So the received word **`w = eval_L(X^d)`** is matched by the **constant**
codeword `(c')^d` on every one of the `n/d` cosets (since `x^d = (c')^d` for all `x ∈ c'H_d`). Using
only constant (degree-0) codewords:
```
    |Λ(RS[F,L,k], w = eval_L(X^d), agreement a = d)| ≥ n/d.
```
This is **exact and replayable** (the `n/d` distinct `d`-th powers `(c')^d`), for any `q, n, d`.

## Results (exact lower bounds; `a = d` the sub-coset order)

| q | n=2^s | k | ρ | band orders d (k<d<√(kn)) | list n/d in band | growth with q? |
|---|---|---|---|---|---|---|
| 193 | 64 | 4 | 1/16 | d=8, 16 | 8, 4 | **constant** (≤ 1/ρ=16) |
| 257 | 256 | 16 | 1/16 | d=32, 64 | 8, 4 | **constant** |
| 97 | 32 | 8 | 1/4 | d=16 | 2 | **constant** (≤ 1/ρ=4) |
| 17 | 16 | 8 | 1/2 | (none: no 2-power in (8, 11.3]) | — | — |

**The decisive structural fact.** The list size `n/d` is large **only below the rate** (`a = d < k`,
i.e. `δ > 1−ρ`): there it is `Ω(n)` (e.g. 64, 128, 256). But `δ > 1−ρ` is **above capacity** — the
trivial regime where huge lists are expected and do **not** violate the prize (the prize threshold
`δ*_C < capacity < 1−ρ`). **Inside the prize-relevant band** `(1−√ρ, 1−ρ)` the construction gives
`n/d ≤ 1/ρ`, a **CONSTANT** independent of `n` and `q` (the smallest 2-power `d > k = ρn` is within a
factor 2 of `ρn`, so `n/d ≈ 1/ρ`).

## Prize relevance (the constant, tracked)

A constant band list `B = n/d ≤ 1/ρ` beats `2^{-128}·q` **only for `q < B·2^{128} ≈ 2^{130}`**.
For "sufficiently large `q`" (the prize regime, `q → ∞`) it does **NOT** beat `2^{-128}·|F|`. So the
multiplicative-BKR construction is **NOT a scalable band counterexample**: it gives `Ω(q)` lists only
in the trivial above-capacity regime, and only `O_ρ(1)` in the band.

## Expanded EXACT search — full worst-case list (all degree-<k polys, not just constants)

To rule out that *non-constant* codewords inflate the band list, we compute the EXACT full
worst-case list `#{p : deg p < k, agreement(eval_L(p), w) ≥ a}` over ALL `q^k` polynomials, for
several structured `w` (`X^d`, `X^d+X^{d/2}`, `X^d+1`, `2X^d`), across many fields. Reproduce:
```
python3 experiments/list_decoding/base_rs_oracle.py --mode exact-sweep --s 4 --k 2 --qs 17 97 113 193 241
python3 experiments/list_decoding/base_rs_oracle.py --mode exact-sweep --s 3 --k 2 --qs 41 73 89 137 193 257
```

| shape | band a | full worst-case list across q | trend |
|---|---|---|---|
| n=16, k=2, ρ=1/8 | a=4 | q=17,97,113,193,241 → **4,4,4,4,4** | **constant** (= n/d) |
| n=16, k=2, ρ=1/8 | a=3 | q=17→**20**, q≥97 → **4,4,4,4** | constant for large q; q=17 (n=q−1, full field) is the only outlier |
| **n=8, k=2, ρ=1/4 (n≈√q at q=73)** | a=3 | q=41,73,89,137,193,257 → **2,2,2,2,2,2** | **constant even in the `n≈√q` regime** |

**The decisive observations.**
1. Non-constant codewords add **nothing** at scale — the full worst-case list equals the constant
   `n/d` for all `q ≥ 97`.
2. The single outlier (q=17, a=3: list 20) is the **full-field** case `n = q−1 = 16`. A 2-power
   `n = q−1` means `q = 2^s+1` is a **Fermat prime** — only finitely many exist (3,5,17,257,65537),
   so this gives **no infinite family**.
3. Probing the **`n ≈ √q`** proximity-gap regime directly (`n=8`, `q=73` so `n ≈ √q`) still gives a
   **constant** band list — no growth as `q` increases through that regime.

## Honest conclusion (BR-2)

- The natural multiplicative analogue of the BKR bad word **fails to produce a band counterexample**
  — finite, exact evidence that it caps at `1/ρ` in `(1−√ρ, 1−ρ)`.
- No scalable (super-constant in the band) family was found. Worst-case search over *arbitrary* `w`
  is reach-limited (first band-bearing smooth size `n≥8` needs `q≥17`; exact `q^n` enumeration
  infeasible; sample lower bounds degrade with `q` — see `research/gld_frontier_oracle.md`).
- Combined with the literature map (genuinely open), the **counterexample track has no live lead**.

**What would change this:** an explicit `w` over a 2-power coset with `ω(poly(n))` (ideally `Ω(q)`)
agreeing degree-`<k` polynomials at some `η₀ > 1−√ρ` and `ρ ∈ {1/2,…,1/16}` — a genuinely
*super-constant* multiplicative bad word. None is known (the literature's "exact missing theorem").
