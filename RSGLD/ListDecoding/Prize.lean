import Mathlib
import RSGLD.Code.ListDecode
import RSGLD.ReedSolomon.Defs
import RSGLD.ListDecoding.Interleaved

/-!
# The grand list decoding challenge

The **grand list decoding challenge** (eprint 2026/680, §1): for `C = RS[F,L,k]` and the
`m`-interleaved code `C^{≡m}`, with target `ε = 2^{-128}`, determine the largest `δ*` with
`|Λ(C^{≡m}, δ*)| ≤ ε·|F|`.

To avoid real-valued `ε`, the size condition is phrased with integer arithmetic:
`|Λ(C^{≡m},δ)| · 2^128 ≤ |F|` is exactly `|Λ| ≤ 2^{-128}·|F|`.

* `list_bound_implies_grand_condition` — the easy final implication: a base list bound `B`
  with `2^128·B ≤ |F|` gives the field-size condition at `δ`.
* `GrandListDecodingChallenge` — the challenge as a `Prop` (stated, not proved); the
  near-capacity location of `δ*` is the open problem.
-/

namespace RSGLD.ListDecoding

open RSGLD.Code RSGLD.ReedSolomon

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]

/-! ### The integer field-size implication

The hard half of the challenge is the combinatorial list bound; the final step is
trivial. If the interleaved list size is `≤ B` and `2^128·B ≤ |F|`, then
`2^128·|Λ(C^{≡m},δ)| ≤ |F|` (i.e. `|Λ| ≤ 2^{-128}·|F|`) holds. -/
theorem list_bound_implies_grand_condition (L : Finset F) (k m : ℕ)
    [Fintype (interleave (code L k) m)] (δ : ℚ) (B : ℕ)
    (hL : maxListSize (interleavedRS L k m) δ ≤ B)
    (hB : 2 ^ 128 * B ≤ Fintype.card F) :
    2 ^ 128 * maxListSize (interleavedRS L k m) δ ≤ Fintype.card F := by
  calc 2 ^ 128 * maxListSize (interleavedRS L k m) δ
      ≤ 2 ^ 128 * B := by gcongr
    _ ≤ Fintype.card F := hB

/-! ### The grand list decoding challenge as a `Prop` (stated, not proved) -/

/-- **The grand list decoding challenge** (eprint 2026/680, §1) for `(RS[F,L,k])^{≡m}`
and a target error `ε = εnum/εden` (with `εnum = 1`, `εden = 2^128`).

It asserts a sharp threshold `δ*` — list size `≤ ε·|F|` strictly below it and
`> ε·|F|` strictly above it (size condition written with integer cross-multiplication
`|Λ|·εden ≤ εnum·|F|`) — **and** that `δ*` lies in the band `[1 − √ρ, 1 − ρ]` between
the Johnson radius and capacity. The threshold half is the structured analogue of the
field-size implication above; the band-location conjuncts are the **open** part. This is
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

end RSGLD.ListDecoding
