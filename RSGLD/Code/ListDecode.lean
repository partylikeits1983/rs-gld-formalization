import Mathlib
import RSGLD.Code.Hamming
import RSGLD.Code.Defs

/-!
# List decoding

The list `Λ(C, δ, f)` of codewords within normalized distance `δ` of `f`, and the
maximum list size over all `f`. (Section 2.3.)

`maxListSize` is defined with `Finset.sup` over a `Fintype` alphabet rather than
the `sSup` of the design sketch — this avoids order-theoretic plumbing while
giving the same value on the finite instances we care about.
-/

namespace RSGLD.Code

variable {F : Type*} [Field F] {α : Type*} [AddCommGroup α] [Module F α]
  [DecidableEq α] {n : ℕ}

/-- The list of codewords of `C` within normalized distance `δ` of `f`. -/
def listAt (C : Submodule F (Fin n → α)) [Fintype C] (δ : ℚ) (f : Fin n → α) :
    Finset C :=
  Finset.univ.filter fun c : C => normDist f (c : Fin n → α) ≤ δ

theorem mem_listAt {C : Submodule F (Fin n → α)} [Fintype C] {δ : ℚ}
    {f : Fin n → α} {c : C} :
    c ∈ listAt C δ f ↔ normDist f (c : Fin n → α) ≤ δ := by
  simp [listAt]

/-- The list grows with the radius. -/
theorem listAt_subset_of_le (C : Submodule F (Fin n → α)) [Fintype C]
    {δ₁ δ₂ : ℚ} (h : δ₁ ≤ δ₂) (f : Fin n → α) :
    listAt C δ₁ f ⊆ listAt C δ₂ f := by
  intro c hc
  rw [mem_listAt] at hc ⊢
  exact hc.trans h

/-- The maximum list size of `C` at radius `δ`, taken over all received words. -/
noncomputable def maxListSize [Fintype α] (C : Submodule F (Fin n → α))
    [Fintype C] (δ : ℚ) : ℕ :=
  Finset.univ.sup fun f : Fin n → α => (listAt C δ f).card

end RSGLD.Code
