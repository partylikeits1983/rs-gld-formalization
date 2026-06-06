# Smooth-coset genericity — literature synthesis (deep-research, adversarially verified)

**Method.** Deep-research workflow: 5 search angles → 16 primary sources fetched → 80 claims extracted
→ 25 top claims 3-vote adversarially verified (**25/25 confirmed, 0 killed**). Complements the earlier
`research/smooth_coset_genericity_attack.md` (structural test) with verified primary-source theorem
statements.

## The exact structural condition (verified)

The condition behind random/generic RS achieving capacity above Johnson is **higher-order MDS,
`MDS(ℓ)`** — an **intersection-dimension** condition, **not** a single-minor nonvanishing condition:

> **BGM Def 1.8 (verbatim).** `C` is `MDS(ℓ)` if for any `ℓ` subsets `A₁,…,Aℓ ⊆ [n]` of size ≤ `k`,
> `dim(G_{A₁} ∩ ⋯ ∩ G_{Aℓ}) = dim(W_{A₁} ∩ ⋯ ∩ W_{Aℓ})`, where `W` is a *generic* `k×n` matrix of the
> same characteristic. (`ℓ=1` = ordinary all-minors MDS; `ℓ≥2` is a genuine subspace-intersection
> condition not reducible to one minor.)

**Equivalent explicit algebraic form (AGGLZ, Thm 2.11 / Def 2.6 / Rem 2.12):** full column rank of the
**Reduced Intersection Matrix `RIM_H`** over the rational function field `F_q(X₁,…,Xₙ)`, for every
`k`-weakly-partition-connected agreement hypergraph `H`; rows are `[1, Xᵢ, Xᵢ², …, Xᵢ^{k-1}]`. Full
rank ⟺ some maximal minor is a **nonzero polynomial determinant** in the `Xᵢ`.

**Capacity implication (BGM Thm 1.5, Cor 1.15; AGGLZ Thm 1.1):** `MDS(ℓ)` at order `ℓ ≈ (1−R)/ε`
yields `(1−R−ε, (1−R−ε)/ε)`-list-decodability (the generalized-Singleton/Shangguan–Tamo optimum). So
list size `L = (1−R−ε)/ε`, MDS order `ℓ = L+1`.

## Per-paper audit

| Paper | Theorem | Condition | Fixed smooth coset? | Where randomness enters |
|---|---|---|---|---|
| **BGM** *Generic RS Achieve LD Capacity* (2206.05256, STOC'23 / SIAM J.Comput. 23M1598064) | Def 1.8 `MDS(ℓ)`; Thm 1.12 GM-MDS; Thm 1.5 capacity; Thm 1.13 `GZP(ℓ)⇔MDS(ℓ)⇔LD-MDS(ℓ)` | intersection-dim `MDS(ℓ)`, via generic zero patterns `GZP(ℓ)` | **NO** | Def 1.4: code over `F(α₁,…,αₙ)` with **symbolic/transcendental** `αᵢ`, *no relations*; Thm 1.6 transfers to **random** points by `prob ≥ 1−c/|F|`, `c` exponential. §1.5 lists explicit constructions as the **first open problem**. |
| **Guo–Zhang** *Randomly Punctured RS … poly-size* (2304.01403, FOCS'23) | `(1−R−ε, O(1/ε))`-LD, `q ≥ 2^{poly(1/ε)}·n²` | RIM/GM-MDS (same condition) | **NO** | "**randomly punctured**" = uniform random distinct `αᵢ`; whp only. No structured-set claim (PDF: zero hits for subgroup/roots-of-unity/cyclotomic). |
| **AGGLZ** *Random RS … Linear-Sized Alphabets* (2304.09445, Adv. Combinatorics 2025:8) | Thm 2.11 RIM full rank; Thm 1.1 `q ≥ n + k·2^{10L/ε}`, prob `≥ 1−2^{−Ln}` | **RIM full column rank** over `F_q(X₁,…,Xₙ)` (the explicit form) | **NO** | proof: symbolic full rank (Thm 2.11) → **Schwartz–Zippel** (`1−Lk²/q`) + **union bound** over `2^{(L+1)n}` RIMs, "over the random choice of `α₁,…,αₙ`." Authors: "explicit codes approaching capacity is a major challenge." |
| **Brakensiek–Dhar–Gopi** *Generalized GM-MDS: Polynomial Codes are Higher-Order MDS* (2310.12888, STOC'24) | Def 1.2 = BGM Def 1.8; Thm 1.1 polynomial codes are higher-order MDS for **generic** points | same `MDS(ℓ)` | **NO** | "Since the entries … are **transcendental**, any determinant … is necessarily nonzero." Generic/existential; **no subgroup/coset coverage.** |
| **Explicit higher-order MDS** (2212.11262, ISIT'23) | explicit `MDS(3)` only over fields `~O(n^{32})` (general); `O(n^3/n^7/n^{50})` for `k=3/4/5` | `MDS(3)` | **NO** (none is a multiplicative coset) | constructions are special algebraic sets, **not** `a·μ_{2^s}`; small-field explicit higher-order MDS is itself "an important open problem." |
| **BSKR** *Subspace Polynomials & Limits to LD of RS* (math.toronto.edu/swastik/rsld.pdf, IEEE-IT 2010) | super-poly list `≥ n^{2log(1/α)}` | **additive** subspace-polynomial defect, **full field `n=|F|`** | **N/A (additive)** | the one proven *structured-set* obstruction — but **additive full field**, not multiplicative `μ_{2^s}`. (Distinction asserted-by-framing; not independently re-verified here.) |

## Translation to `L = a·μ_{2^s}`

The scalar `a` cancels (overall `a^{…}` factor), so the test depends only on `μ_{2^s}` (roots of
unity). The condition becomes: **does the GM-MDS / RIM determinant — a polynomial in the `Xᵢ`
specialized at `xᵢ = ωⁱ` (`ω` a primitive `2^s`-th root of unity) — vanish?** Generic points are a
non-root by construction; a structured coset is *exactly* the kind of point that the genericity /
Schwartz–Zippel "exceptional variety" argument cannot rule out. Finite low-order tests
(`research/smooth_coset_genericity_attack.md` §6) found **no `μ_{2^s}` defect**, but are inconclusive
(low order only; uncalibrated positive control).

## ONE next-theorem target — **(C) OBSTRUCTION**

> Every capacity-achieving RS result establishes `MDS(ℓ)` / RIM-full-rank **only generically/symbolically**
> and transfers to **random** points via Schwartz–Zippel + union bound. **No theorem establishes (or
> refutes) `MDS(ℓ)` for any fixed explicit evaluation set**, and the multiplicative coset `L = a·μ_{2^s}`
> status is **OPEN**.
>
> **The exact missing statement:** for `L = a·μ_{2^s}` (`ω` a primitive `2^s`-th root of unity), the
> **RIM `RIM_H(1, ω, ω², …, ω^{n-1})` has full column rank over `F_q`** (equivalently the GM-MDS
> cyclotomic determinant `det[∏_{j∈Sᵢ}(ωᵇ − ωʲ)]` is nonzero) **for every `k`-weakly-partition-connected
> `H` at order `ℓ ≈ (1−R)/ε`** — which would import BGM/AGGLZ capacity and give `B_C(E) ≤ O(1/ε)` at
> radius `1−ρ−ε`, settling the Grand List Decoding problem. Proving it = positive; an explicit cyclotomic/subgroup dependency
> that makes the determinant vanish = negative.

**Tractability note (the actionable angle).** For a radius bounded a *constant* `ε` below capacity, the
order `ℓ ≈ (1−R)/ε` is a **constant**, so the cyclotomic RIM determinant at fixed order `ℓ` is a
**finite, explicit object** — a concrete (possibly tractable) determinant-nonvanishing question at
`xᵢ = ωⁱ`, rather than an asymptotic one. The first checkable case is `ℓ = 3` (the first nontrivial
higher-order MDS), already partially probed in `smooth_coset_genericity_attack.md`.

## Caveats (from adversarial verification)
- **Goyal–Guruswami** (prompt focus paper 4, local-properties / subspace-design / proximity-gap) did
  **not** surface in any verified claim — unaddressed here; do not assume it touches plain-RS cosets.
- The **additive (BSKR) vs multiplicative** separation is asserted-by-framing, not independently
  re-verified in this run.
- `ℓ ≈ (1−R)/ε` carries a `(1−R)`/`+1` slack between list size `L` and MDS order `ℓ`.
- The "no coset result" conclusion rests partly on **absence of evidence** (no paper proves it for
  cosets) + the verified openness statements (BGM §1.5; AGGLZ).

## Citations
- Brakensiek, Gopi, Makam, *Generic Reed-Solomon Codes Achieve List-Decoding Capacity*, STOC 2023 / SIAM J. Comput. 2024. arXiv:2206.05256. https://arxiv.org/abs/2206.05256
- Guo, Zhang, *Randomly Punctured RS Codes Achieve the List Decoding Capacity over Polynomial-Size Alphabets*, FOCS 2023. arXiv:2304.01403.
- Alrabiah, Guo, Guruswami, Li, Zhang, *Random RS Codes Achieve List-Decoding Capacity with Linear-Sized Alphabets*, Advances in Combinatorics 2025:8. arXiv:2304.09445.
- Brakensiek, Dhar, Gopi, *Generalized GM-MDS: Polynomial Codes are Higher Order MDS*, STOC 2024. arXiv:2310.12888.
- (Explicit higher-order MDS) arXiv:2212.11262, ISIT 2023.
- Ben-Sasson, Kopparty, Radhakrishnan, *Subspace Polynomials and Limits to List Decoding of RS Codes*, IEEE-IT 2010. https://www.math.toronto.edu/swastik/rsld.pdf
- Kumar, Ron-Zewi, *Advances in List Decoding of Polynomial Codes* (survey, 2026). arXiv:2603.03841.
