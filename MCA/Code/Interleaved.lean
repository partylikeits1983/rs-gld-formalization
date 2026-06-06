import Mathlib
import MCA.Code.Defs
import MCA.Code.ListDecode

/-!
# Interleaved codes

The `m`-wise interleaved code `C^{≡m}`: words `g : Fin n → (Fin m → F)` such that
every column `i ↦ g i j` is a codeword of `C`. Modeled cleanly as the infimum of
the comaps of the column-projection linear maps, so it is a submodule for free.

## Open obligations
* `maxListSize_interleaved_lb` (this file): interleaving cannot shrink the list.
* **GGR Lemma 2.10** (the matching upper bound for interleaved codes) is *not*
  stated here yet: a faithful statement needs the radius-dependent bound from the
  paper (an unconditional `interleaved ≤ base` is false — large joint lists above
  the Johnson radius are exactly the phenomenon Lemma 6.12 exploits). Deferred
  with a precise statement TODO; tracked in `Sorry.md`.
-/

namespace MCA.Code

variable {F : Type*} [Field F] {n : ℕ}

/-- Column projection: `g ↦ (i ↦ g i j)`, as an `F`-linear map. -/
def colProj (F : Type*) [Field F] (n m : ℕ) (j : Fin m) :
    (Fin n → Fin m → F) →ₗ[F] (Fin n → F) :=
  (LinearMap.proj j).compLeft (Fin n)

/-- The `m`-wise interleaved code `C^{≡m}`. (Section 2.) -/
def interleave (C : LinearCode F n) (m : ℕ) : Submodule F (Fin n → Fin m → F) :=
  ⨅ j : Fin m, C.comap (colProj F n m j)

theorem mem_interleave {C : LinearCode F n} {m : ℕ} {g : Fin n → Fin m → F} :
    g ∈ interleave C m ↔ ∀ j : Fin m, (fun i => g i j) ∈ C := by
  rw [interleave, Submodule.mem_iInf]
  simp only [Submodule.mem_comap]
  rfl

/-- The constant lift of a base codeword into the interleaved code: every column
of the lifted word equals the original codeword. Valid for any `m`. -/
def liftConst {C : LinearCode F n} {m : ℕ} (c : C) : interleave C m :=
  ⟨fun i _ => (c : Fin n → F) i, by
    rw [mem_interleave]
    intro _
    exact c.2⟩

theorem liftConst_val {C : LinearCode F n} {m : ℕ} (c : C) :
    (liftConst (m := m) c : Fin n → Fin m → F) = fun i _ => (c : Fin n → F) i := rfl

/-- The constant lift is injective when there is at least one column. -/
theorem liftConst_injective {C : LinearCode F n} {m : ℕ} (hm : 0 < m) :
    Function.Injective (liftConst (C := C) (m := m)) := by
  intro c₁ c₂ h
  apply Subtype.ext
  funext i
  have : (liftConst (m := m) c₁ : Fin n → Fin m → F) i ⟨0, hm⟩
       = (liftConst (m := m) c₂ : Fin n → Fin m → F) i ⟨0, hm⟩ := by rw [h]
  simpa [liftConst_val] using this

/-- The constant lift preserves Hamming distance to the corresponding constant
received word, when there is at least one column. -/
theorem hammingDist_liftConst [Fintype F] [DecidableEq F]
    {C : LinearCode F n} {m : ℕ} (hm : 0 < m) (f : Fin n → F) (c : C) :
    hammingDist (fun i (_ : Fin m) => f i)
      (liftConst (m := m) c : Fin n → Fin m → F) = hammingDist f (c : Fin n → F) := by
  unfold hammingDist
  congr 1
  apply Finset.filter_congr
  intro i _
  rw [liftConst_val]
  constructor
  · intro h hc
    exact h (by funext _; exact hc)
  · intro h hc
    exact h (congrFun hc ⟨0, hm⟩)

/-- Interleaving cannot decrease the maximum list size: `C^{≡m}` has at least the
list-decoding capacity of `C`. -/
theorem maxListSize_interleaved_lb [Fintype F] [DecidableEq F]
    (C : LinearCode F n) [Fintype C] (m : ℕ) (hm : 0 < m) [Fintype (interleave C m)] (δ : ℚ) :
    maxListSize C δ ≤ maxListSize (interleave C m) δ := by
  unfold maxListSize
  apply Finset.sup_le
  intro f _
  -- The constant received word lifting `f`.
  set Fhat : Fin n → Fin m → F := fun i _ => f i with hFhat
  refine le_trans ?_ (Finset.le_sup (f := fun g => (listAt (interleave C m) δ g).card)
    (Finset.mem_univ Fhat))
  -- Map `listAt C δ f` injectively into `listAt (interleave C m) δ F̂`.
  apply Finset.card_le_card_of_injOn liftConst
  · -- maps into
    intro c hc
    rw [Finset.mem_coe, mem_listAt] at hc ⊢
    -- normDist is preserved
    have hd : hammingDist Fhat (liftConst (m := m) c : Fin n → Fin m → F)
            = hammingDist f (c : Fin n → F) := hammingDist_liftConst hm f c
    unfold normDist at hc ⊢
    rw [hd]
    exact hc
  · -- injective on the set
    intro c₁ _ c₂ _ h
    exact liftConst_injective hm h

end MCA.Code
