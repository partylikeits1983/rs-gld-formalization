import Mathlib

/-!
# The geometric core of the Johnson bound (Lemma 4.4.3, part 2)

The pure inner-product-space lemma underlying the q-ary Johnson bound, isolated
from any coding-theory content. This is the "easy" sum-of-squares half of GRS's
Geometric Lemma (Lemma 4.4.3 part 2) — NOT the harder linear-independence part 1.

If `M` vectors in a real inner-product space have bounded square-norm `‖vᵢ‖² ≤ U`
and pairwise inner products `⟨vᵢ,vⱼ⟩ ≤ −ε` with `ε > 0`, then
  `0 ≤ ‖Σ vᵢ‖² = Σ‖vᵢ‖² + 2·Σ_{i<j} ⟨vᵢ,vⱼ⟩ ≤ M·U − M(M−1)·ε`,
hence `M·(U − (M−1)·ε) ≥ 0`, giving `M ≤ 1 + U/ε`.

We phrase it over `Finset.sum` of a finite family `v : ι → E` so the `simplex_embed`
consumer can instantiate `ι` with the list `Finset C` and `E` with `EuclideanSpace ℝ`.
-/

namespace MCA.Code

open scoped InnerProductSpace BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **L1 — geometric core (GRS Lemma 4.4.3 part 2).** A finite family of vectors
with square-norm `≤ U` and pairwise inner product `≤ −ε` (with `0 < ε`) has size
at most `1 + U/ε`.

Proof obligation (the geometric heart of Theorem 3.2): expand
`0 ≤ ⟪Σ vᵢ, Σ vᵢ⟫ = Σᵢ ‖vᵢ‖² + Σ_{i≠j} ⟪vᵢ,vⱼ⟫` via `inner_sum`/`sum_inner` and
`real_inner_self_eq_norm_sq`, bound each term, and rearrange.

`M := |ι|` is the number of vectors. The conclusion is over `ℝ` so the
`johnson_bound` consumer can compare with `johnsonJqℓ`. -/
theorem geom_lemma_sum_sq (v : ι → E) (U ε : ℝ) (hε : 0 < ε) (hU : 0 ≤ U)
    (hself : ∀ i, ‖v i‖ ^ 2 ≤ U)
    (hcross : ∀ i j, i ≠ j → @inner ℝ _ _ (v i) (v j) ≤ -ε) :
    (Fintype.card ι : ℝ) ≤ 1 + U / ε := by
  -- M := |ι|.  Case-split on whether ι is empty.
  set M : ℕ := Fintype.card ι with hM
  rcases Nat.eq_zero_or_pos M with hM0 | hMpos
  · -- empty index type: 0 ≤ 1 + U/ε since 0 ≤ U/ε
    rw [hM0]
    have hUε : 0 ≤ U / ε := div_nonneg hU (le_of_lt hε)
    simp only [Nat.cast_zero]
    linarith
  · -- M ≥ 1.  Expand 0 ≤ ⟪Σ vᵢ, Σ vᵢ⟫.
    have hnn : (0 : ℝ) ≤ @inner ℝ _ _ (∑ i, v i) (∑ i, v i) := real_inner_self_nonneg
    -- expand the inner product as a double sum
    have hexpand : @inner ℝ _ _ (∑ i, v i) (∑ i, v i)
        = ∑ i, ∑ j, @inner ℝ _ _ (v i) (v j) := by
      rw [sum_inner]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [inner_sum]
    -- termwise bound: each ⟪vᵢ,vⱼ⟫ ≤ if i = j then U else -ε
    have hbound : ∑ i, ∑ j, @inner ℝ _ _ (v i) (v j)
        ≤ ∑ i : ι, ∑ j : ι, (if i = j then U else -ε) := by
      refine Finset.sum_le_sum (fun i _ => ?_)
      refine Finset.sum_le_sum (fun j _ => ?_)
      by_cases hij : i = j
      · subst hij
        simp only [if_true]
        rw [real_inner_self_eq_norm_sq]
        exact hself i
      · simp only [if_neg hij]
        exact hcross i j hij
    -- evaluate the double sum of the if-expression
    have heval : ∑ i : ι, ∑ j : ι, (if i = j then U else -ε)
        = (M : ℝ) * U - ((M : ℝ) ^ 2 - M) * ε := by
      have hinner : ∀ i : ι, ∑ j : ι, (if i = j then U else -ε)
          = U - ((M : ℝ) - 1) * ε := by
        intro i
        have hsplit : ∑ j : ι, (if i = j then U else -ε)
            = ∑ j : ι, ((if i = j then (U + ε) else (0:ℝ)) + (-ε)) := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          by_cases hij : i = j <;> simp [hij]
        rw [hsplit, Finset.sum_add_distrib]
        rw [Finset.sum_ite_eq Finset.univ i (fun _ => (U + ε))]
        simp only [Finset.mem_univ, if_true]
        rw [Finset.sum_const, Finset.card_univ, ← hM]
        ring
      rw [Finset.sum_congr rfl (fun i _ => hinner i)]
      rw [Finset.sum_const, Finset.card_univ, ← hM]
      ring
    -- combine: 0 ≤ M·U - (M²-M)·ε
    have hkey : (0:ℝ) ≤ (M : ℝ) * U - ((M : ℝ) ^ 2 - M) * ε := by
      calc (0:ℝ) ≤ @inner ℝ _ _ (∑ i, v i) (∑ i, v i) := hnn
        _ = ∑ i, ∑ j, @inner ℝ _ _ (v i) (v j) := hexpand
        _ ≤ ∑ i, ∑ j, (if i = j then U else -ε) := hbound
        _ = (M : ℝ) * U - ((M : ℝ) ^ 2 - M) * ε := heval
    -- M ≥ 1 as a real
    have hM1 : (1:ℝ) ≤ (M : ℝ) := by
      have : 1 ≤ M := hMpos
      exact_mod_cast this
    -- factor: 0 ≤ M·(U - (M-1)·ε), divide by M > 0 to get U - (M-1)·ε ≥ 0
    have hMr : (0:ℝ) < (M : ℝ) := by linarith
    have hfac : (0:ℝ) ≤ U - ((M : ℝ) - 1) * ε := by
      have : (M : ℝ) * (U - ((M : ℝ) - 1) * ε)
          = (M : ℝ) * U - ((M : ℝ) ^ 2 - M) * ε := by ring
      nlinarith [hkey, hMr]
    -- (M-1)·ε ≤ U, divide by ε to get M - 1 ≤ U/ε
    have hfinal : (M : ℝ) - 1 ≤ U / ε := by
      rw [le_div_iff₀ hε]
      linarith
    linarith

end MCA.Code
