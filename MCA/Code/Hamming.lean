import Mathlib

/-!
# Normalized Hamming distance

Mathlib already provides `hammingDist : (∀ i, β i) → (∀ i, β i) → ℕ` (the *count*
of disagreeing coordinates) together with `hammingDist_comm`,
`hammingDist_triangle`, and `hammingDist_eq_zero`
(`Mathlib.InformationTheory.Hamming`). The paper works with the *normalized*
(fractional) distance in `ℚ`, so this file is a thin wrapper that divides the
Mathlib count by the block length. All algebraic facts come for free from
Mathlib's count-level lemmas.

This matches Definition 2.3 of Arnon–Boneh–Fenzi (2026).
-/

namespace MCA.Code

variable {α : Type*} [DecidableEq α] {n : ℕ}

/-- Normalized Hamming distance: the fraction of disagreeing coordinates,
as a rational. (Definition 2.3.) -/
def normDist (u v : Fin n → α) : ℚ := (hammingDist u v : ℚ) / (n : ℚ)

/-- Restricted normalized Hamming distance: only count disagreements on `T`. -/
def normDistRestricted (T : Finset (Fin n)) (u v : Fin n → α) : ℚ :=
  ((T.filter fun i => u i ≠ v i).card : ℚ) / (T.card : ℚ)

@[simp] theorem normDist_self (u : Fin n → α) : normDist u u = 0 := by
  simp [normDist]

theorem normDist_comm (u v : Fin n → α) : normDist u v = normDist v u := by
  unfold normDist; rw [hammingDist_comm]

theorem normDist_nonneg (u v : Fin n → α) : 0 ≤ normDist u v := by
  unfold normDist; positivity

theorem normDist_triangle (u v w : Fin n → α) :
    normDist u w ≤ normDist u v + normDist v w := by
  unfold normDist
  rw [← add_div]
  gcongr
  exact_mod_cast hammingDist_triangle u v w

theorem normDist_eq_zero_iff (hn : 0 < n) (u v : Fin n → α) :
    normDist u v = 0 ↔ u = v := by
  unfold normDist
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [div_eq_zero_iff]
  simp [hn', Nat.cast_eq_zero, hammingDist_eq_zero]

theorem normDist_sub_left {α : Type*} [AddGroup α] [DecidableEq α] {n : ℕ}
    (u v : Fin n → α) :
    normDist u v = normDist (u - v) (0 : Fin n → α) := by
  unfold normDist
  congr 2
  unfold hammingDist
  congr 1
  apply Finset.filter_congr
  intro i _
  simp only [Pi.sub_apply, Pi.zero_apply, sub_ne_zero]

/-- Quantitative agreement implies small Hamming distance: if `g` and `c` agree
on every position of `S`, then they disagree on at most `n - |S|` positions. -/
theorem hammingDist_le_of_agreeOn {g c : Fin n → α} {S : Finset (Fin n)}
    (h : ∀ i ∈ S, g i = c i) :
    hammingDist g c ≤ n - S.card := by
  rw [hammingDist]
  have hsub : (Finset.univ.filter fun i => g i ≠ c i) ⊆ Sᶜ := by
    intro i hi
    rw [Finset.mem_filter] at hi
    rw [Finset.mem_compl]
    intro hiS
    exact hi.2 (h i hiS)
  calc (Finset.univ.filter fun i => g i ≠ c i).card
      ≤ Sᶜ.card := Finset.card_le_card hsub
    _ = n - S.card := by rw [Finset.card_compl, Fintype.card_fin]

/-- Normalized version of `hammingDist_le_of_agreeOn`. -/
theorem normDist_le_of_agreeOn {g c : Fin n → α} {S : Finset (Fin n)}
    (h : ∀ i ∈ S, g i = c i) :
    normDist g c ≤ ((n - S.card : ℕ) : ℚ) / (n : ℚ) := by
  unfold normDist
  gcongr
  exact_mod_cast hammingDist_le_of_agreeOn h

end MCA.Code
