# The Base-RS Frontier — the exact remaining problem for the grand challenge

**As of 2026-06-05, GLD-9 (GGR Lemma 2.10 / Thm 2.5) is fully proved in-repo (axiom-clean).** The
grand list-decoding challenge therefore reduces **entirely** to one base-code quantity.

## The remaining problem

> **Bound or determine the worst-case combinatorial base-RS list size**
> ```
>     B(η) := |Λ(RS[F,L,k], η)| = max over received words w of #{ p : deg p < k,
>                                       agreement(eval_L(p), w) ≥ (1−η)·n }
> ```
> for a **fixed smooth** evaluation domain `L` (multiplicative coset of a 2-power-order subgroup of
> `F*`, `|L|=n`), rate `ρ = k/n ∈ {1/2,1/4,1/8,1/16}`, and radius `η` in the **open band**
> `(1−√ρ, H_q⁻¹(1−ρ)]` — strictly **beyond the Johnson radius** `1−√ρ`.

Plain base RS, **worst-case** received word, list **SIZE** (not algorithmic radius), with **explicit
constants**.

## The GLD-9 implication (proved in-repo)

`maxListSize_interleave_le_int` (`MCA/ListDecoding/GGRComposition.lean`), m-independent:
```
    |Λ(C^{≡m}, η)| ≤ Nat.choose(b+r, r) · B(η)^r
```
with `b,r` from `(η, δ_min)` only — independent of the interleaving order `m`. So the interleaved /
folded prize is controlled by the **base** quantity `B(η)`.

## The prize condition

The grand list-decoding prize `|Λ(C^{≡m}, δ*_C)| ≤ 2^{-128}·|F|` is **implied** (via GLD-11
`interleavedRS_prize_of_base_bound`, axiom-clean) by a base bound `B(η) ≤ B` together with the
field-size condition
```
    Nat.choose(b+r, r) · B^r ≤ 2^{-128} · |F|.
```
Conversely, the prize **fails** at radius `η` if `B(η) > 2^{-128}·|F|` for sufficiently large `|F|`
(note: this needs `B(η) = Ω(|F|)` — a constant or any `o(|F|)` does NOT beat `2^{-128}·|F|`
asymptotically, since `2^{-128}` is a fixed constant).

## Status of the two attack routes (decision packet)

- **Import (positive theorem):** `research/base_rs_literature_map.md` — **genuinely OPEN**. Every
  published beyond-Johnson RS positive result needs random/generic points over large fields; none is
  proven for a fixed 2-power coset at constant rate. BKR's structured large-list is additive
  (subspace polynomials over the full field) and at vanishing rate — inapplicable here. No smooth-
  coset / Weil-sum / FFT-structure result bounds `B(η)` in the band. Certifiable floor only:
  `B(η) ≤ poly(n)` for `η ≤ 1−√ρ` (Guruswami–Sudan, repo `mds_list_bound`).
- **Counterexample (negative):** `research/base_rs_oracle_results.md` — the natural multiplicative
  analogue of the BKR bad word (`w = eval_L(X^d)`) gives only a **constant** band list `≤ 1/ρ` (finite
  exact evidence across `q=193,257,97`); `Ω(n)` lists occur only **below the rate** (above capacity,
  the trivial regime). **NOT a scalable band counterexample.** No super-constant multiplicative bad
  word is known.

## The exact missing theorem (either resolves the challenge)

- **(positive)** an explicit `P(n)` with absolute constants and an explicit `η₀ > 1−√ρ` such that
  `B(η₀) ≤ P(n)` for a 2-power coset at `ρ ∈ {1/2,…,1/16}`, with `Nat.choose(b+r,r)·P(n)^r ≤
  2^{-128}|F|`; **or**
- **(negative)** an explicit received word over such a coset with `Ω(|F|)` agreeing degree-`<k`
  polynomials at some `η₀ > 1−√ρ` — a *super-constant* multiplicative analogue of the BKR additive
  bad word.

**Neither is known as of June 2026.** Per the repo epistemic law, this is **external/blocked**; no
in-repo prover or counterexample budget is spent on it until external math supplies `B(η)`. The
in-repo provable contribution to the grand challenge (GLD-1…11, incl. the full GGR proof) is
**complete**.
