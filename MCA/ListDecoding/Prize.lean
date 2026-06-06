import Mathlib
import MCA.Code.ListDecode
import MCA.ReedSolomon.Defs
import MCA.ListDecoding.Interleaved

/-!
# The grand list decoding challenge: prize statement and prize-implication

The **grand list decoding challenge** (eprint 2026/680, §1): for `C = RS[F,L,k]` and
the `m`-interleaved code `C^{≡m}`, target `ε* = 2^{-128}`, determine the largest
`δ*_C` with `|Λ(C^{≡m}, δ*_C)| ≤ ε*·|F|`.

To avoid real-valued `ε`, we phrase the size condition with integer arithmetic:
`|Λ(C^{≡m},δ)| · 2^128 ≤ |F|` is exactly `|Λ| ≤ 2^{-128}·|F|`.

## Leaves
* `list_bound_implies_grand_condition` — GLD-5: the easy final implication
  (a list bound `B` with `2^128·B ≤ |F|` gives the prize inequality at `δ`).
* `GrandListDecodingChallenge` — GLD-6: the challenge as a `Prop` (stated, not proved;
  mirrors `MCA.Concrete.GrandProblemToy.GrandMCAProblem`). The near-capacity location
  of `δ*` is the open prize.
-/

namespace MCA.ListDecoding

open MCA.Code MCA.ReedSolomon

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]

/-! ### GLD-5 — the integer prize-implication

The hard half of the challenge is the combinatorial list bound; the final step is
trivial. If the interleaved list size is `≤ B` and `2^128·B ≤ |F|`, then the prize
inequality `2^128·|Λ(C^{≡m},δ)| ≤ |F|` (i.e. `|Λ| ≤ 2^{-128}·|F|`) holds. The
field-size dependence is exposed explicitly. -/
theorem list_bound_implies_grand_condition (L : Finset F) (k m : ℕ)
    [Fintype (interleave (code L k) m)] (δ : ℚ) (B : ℕ)
    (hL : maxListSize (interleavedRS L k m) δ ≤ B)
    (hB : 2 ^ 128 * B ≤ Fintype.card F) :
    2 ^ 128 * maxListSize (interleavedRS L k m) δ ≤ Fintype.card F := by
  calc 2 ^ 128 * maxListSize (interleavedRS L k m) δ
      ≤ 2 ^ 128 * B := by gcongr
    _ ≤ Fintype.card F := hB

/-! ### GLD-10b — the prize condition holds *below the Johnson radius* (certified tier)

Composing GLD-10 (`interleavedRS_johnson_bound`, the real-valued Johnson list bound for
`C^{≡m}`) with GLD-5 (the integer prize-implication). For any integer `B` dominating the
Johnson bound `(1/(2ηρ))^m` and a field large enough that `2^128·B ≤ |F|`, the prize
inequality `2^128·|Λ(C^{≡m},δ)| ≤ |F|` holds at every `δ ≤ 1−√ρ−η`.

This is the **honest certified statement**: it establishes the prize only in the easy region
*below* the Johnson radius (the `LIST_CERTIFIED` tier). It makes **no** claim inside the open
band `(1−√ρ, 1−ρ]`; per Lemma 2.10 (m-independent) and the literature triage
(`research/gld_literature_map.md`), the band is external open math. -/
theorem interleavedRS_prize_at_johnson (L : Finset F) (k : ℕ)
    (hk : 0 < k) (hk2 : 2 ≤ k) (hkn : k ≤ L.card) [Fintype (code L k)]
    (hq : 1 < Fintype.card F) (m : ℕ) [Fintype (interleave (code L k) m)]
    (η : ℝ) (hη : 0 < η) (ρ : ℝ) (hρ : ρ = (k : ℝ) / (L.card : ℝ))
    (δ : ℚ) (hδpos : 0 ≤ δ) (hδ : (δ : ℝ) ≤ 1 - Real.sqrt ρ - η)
    (B : ℕ) (hB : ((1 / (2 * η * ρ)) ^ m : ℝ) ≤ B)
    (hField : 2 ^ 128 * B ≤ Fintype.card F) :
    2 ^ 128 * maxListSize (interleavedRS L k m) δ ≤ Fintype.card F := by
  have hjohnson : (maxListSize (interleavedRS L k m) δ : ℝ) ≤ (1 / (2 * η * ρ)) ^ m :=
    interleavedRS_johnson_bound L k hk hk2 hkn hq m η hη ρ hρ δ hδpos hδ
  have hnat : maxListSize (interleavedRS L k m) δ ≤ B := by
    have : (maxListSize (interleavedRS L k m) δ : ℝ) ≤ (B : ℝ) := le_trans hjohnson hB
    exact_mod_cast this
  exact list_bound_implies_grand_condition L k m δ B hnat hField

/-! ### GLD-6 — the grand list decoding challenge as a `Prop` (stated, not proved) -/

/-- **The grand list decoding challenge** (eprint 2026/680, §1) for `(RS[F,L,k])^{≡m}`
and a target error `ε = εnum/εden` (the prize uses `εnum = 1`, `εden = 2^128`).

It asserts a sharp threshold `δ*` — list size `≤ ε·|F|` strictly below it and
`> ε·|F|` strictly above it (size condition written with integer cross-multiplication
`|Λ|·εden ≤ εnum·|F|`) — **and** that `δ*` lies in the band `[1 − √ρ, 1 − ρ]` between
the Johnson radius and capacity. The threshold half is the structured analogue of the
prize-implication (GLD-5); the band-location conjuncts are the **open** prize. This is
a `Prop`-valued `def`: it *states* the challenge and is not proved here. -/
def GrandListDecodingChallenge (L : Finset F) (k m : ℕ)
    [Fintype (interleave (code L k) m)] (εnum εden : ℕ) : Prop :=
  ∃ δstar : ℝ,
    -- (a) sharp threshold: feasible below, infeasible above
    (∀ δ : ℚ, (δ : ℝ) < δstar →
      maxListSize (interleavedRS L k m) δ * εden ≤ εnum * Fintype.card F) ∧
    (∀ δ : ℚ, δstar < (δ : ℝ) →
      εnum * Fintype.card F < maxListSize (interleavedRS L k m) δ * εden) ∧
    -- (b) the OPEN location claim: Johnson ≤ δ* ≤ capacity
    (1 - Real.sqrt ((k : ℝ) / (L.card : ℝ))) ≤ δstar ∧
    δstar ≤ 1 - (k : ℝ) / (L.card : ℝ)

end MCA.ListDecoding
