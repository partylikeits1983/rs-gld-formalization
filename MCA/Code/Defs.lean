import Mathlib
import MCA.Code.Hamming

/-!
# Linear codes and proximity

A linear code over `F` with block length `n` is a submodule of `Fin n → F`. We
keep the alphabet polymorphic (`α`, an `F`-module) where it costs nothing, so the
same `deltaClose` serves both the base code (`α = F`) and interleaved codes
(`α = Fin m → F`).
-/

namespace MCA.Code

/-- A linear code over `F` with block length `n`: a submodule of `Fin n → F`.
(Definition 2.2.) -/
abbrev LinearCode (F : Type*) [Field F] (n : ℕ) : Type _ :=
  Submodule F (Fin n → F)

variable {F : Type*} [Field F] {α : Type*} [AddCommGroup α] [Module F α]
  [DecidableEq α] {n : ℕ}

/-- `f` is `δ`-close to the code `C`: some codeword lies within normalized
Hamming distance `δ`. (Section 2.3.) -/
def deltaClose (C : Submodule F (Fin n → α)) (δ : ℚ) (f : Fin n → α) : Prop :=
  ∃ c ∈ C, normDist f c ≤ δ

theorem deltaClose_of_mem {C : Submodule F (Fin n → α)} {δ : ℚ} {f : Fin n → α}
    (hf : f ∈ C) (hδ : 0 ≤ δ) : deltaClose C δ f :=
  ⟨f, hf, by simpa using hδ⟩

/-- `g` agrees with some codeword of `C` on every position in `S`: the
set-restricted analogue of `deltaClose`, encoding `Δ_S(g, C) = 0` from
Definition 4.3 (mutual correlated agreement). The shared set `S` is what
distinguishes MCA from CA. -/
def agreesOn (C : Submodule F (Fin n → α)) (S : Finset (Fin n)) (g : Fin n → α) : Prop :=
  ∃ c ∈ C, ∀ i ∈ S, g i = c i

/-- Bridge between the normalized-distance closeness `deltaClose` and the
agreement-set formulation `agreesOn`: `g` is `δ`-close to `C` iff it agrees with
some codeword on a set of `≥ (1 - δ)·n` positions. Requires `0 < n` (the
`normDist` divisor). -/
theorem deltaClose_iff_agreesOn (hn : 0 < n) (C : Submodule F (Fin n → α)) (δ : ℚ)
    (g : Fin n → α) :
    deltaClose C δ g ↔
      ∃ S : Finset (Fin n), (1 - δ) * (n : ℚ) ≤ (S.card : ℚ) ∧ agreesOn C S g := by
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnpos : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  constructor
  · rintro ⟨c, hc, hd⟩
    refine ⟨Finset.univ.filter (fun i => g i = c i), ?_, c, hc, ?_⟩
    · -- card bound
      have hsplit :
          (Finset.univ.filter (fun i => g i = c i)).card
            + (Finset.univ.filter (fun i => ¬ g i = c i)).card
            = (Finset.univ : Finset (Fin n)).card :=
        Finset.card_filter_add_card_filter_not _
      rw [Finset.card_univ, Fintype.card_fin] at hsplit
      have hham : (Finset.univ.filter (fun i => ¬ g i = c i)).card = hammingDist g c := by
        rw [hammingDist]
      -- normDist hypothesis: (hammingDist g c : ℚ) / n ≤ δ
      unfold normDist at hd
      rw [div_le_iff₀ hnpos] at hd
      -- S.card = n - hammingDist g c
      have hScard :
          ((Finset.univ.filter (fun i => g i = c i)).card : ℚ)
            = (n : ℚ) - (hammingDist g c : ℚ) := by
        have : ((Finset.univ.filter (fun i => g i = c i)).card : ℚ)
            + (hammingDist g c : ℚ) = (n : ℚ) := by
          rw [← hham]; exact_mod_cast hsplit
        linarith
      rw [hScard]
      linarith
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
  · rintro ⟨S, hcard, c, hc, hagree⟩
    refine ⟨c, hc, ?_⟩
    -- disagreement set ⊆ Sᶜ
    have hsub : Finset.univ.filter (fun i => g i ≠ c i) ⊆ Sᶜ := by
      intro i hi
      rw [Finset.mem_filter] at hi
      rw [Finset.mem_compl]
      intro hiS
      exact hi.2 (hagree i hiS)
    have hle : hammingDist g c ≤ Sᶜ.card := by
      rw [hammingDist]
      exact Finset.card_le_card hsub
    have hcompl : Sᶜ.card = n - S.card := by
      rw [Finset.card_compl, Fintype.card_fin]
    have hSle : S.card ≤ n := by
      have := S.card_le_univ
      rwa [Fintype.card_fin] at this
    have hleQ : (hammingDist g c : ℚ) ≤ (n : ℚ) - (S.card : ℚ) := by
      have h1 : (hammingDist g c : ℚ) ≤ (Sᶜ.card : ℚ) := by exact_mod_cast hle
      have h2 : (Sᶜ.card : ℚ) = (n : ℚ) - (S.card : ℚ) := by
        rw [hcompl]; push_cast [Nat.cast_sub hSle]; ring
      rw [h2] at h1; exact h1
    unfold normDist
    rw [div_le_iff₀ hnpos]
    -- (1-δ)*n ≤ S.card ⇒ hammingDist ≤ n - S.card ≤ δ*n
    nlinarith [hleQ, hcard]

theorem agreesOn_empty (C : Submodule F (Fin n → α)) (g : Fin n → α) :
    agreesOn C ∅ g := ⟨0, C.zero_mem, by simp⟩

theorem agreesOn_of_mem {C : Submodule F (Fin n → α)} {g : Fin n → α}
    (hg : g ∈ C) (S : Finset (Fin n)) : agreesOn C S g := ⟨g, hg, fun i _ => rfl⟩

theorem agreesOn_subset {C : Submodule F (Fin n → α)} {S S' : Finset (Fin n)}
    {g : Fin n → α} (h : agreesOn C S g) (hsub : S' ⊆ S) : agreesOn C S' g := by
  obtain ⟨c, hc, hagree⟩ := h
  exact ⟨c, hc, fun i hi => hagree i (hsub hi)⟩

theorem exists_maximal_commonAgree (C : Submodule F (Fin n → α)) (f₁ f₂ : Fin n → α) :
    ∃ T : Finset (Fin n),
      (agreesOn C T f₁ ∧ agreesOn C T f₂) ∧
      ∀ T' : Finset (Fin n), (agreesOn C T' f₁ ∧ agreesOn C T' f₂) → T'.card ≤ T.card := by
  classical
  set P : Finset (Fin n) → Prop := fun T => agreesOn C T f₁ ∧ agreesOn C T f₂ with hP
  set s : Finset (Finset (Fin n)) := Finset.univ.filter P with hs
  have hsne : s.Nonempty := by
    refine ⟨∅, ?_⟩
    rw [hs, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, agreesOn_empty C f₁, agreesOn_empty C f₂⟩
  obtain ⟨T, hTs, hTmax⟩ := s.exists_max_image Finset.card hsne
  have hPT : P T := (Finset.mem_filter.mp hTs).2
  refine ⟨T, hPT, ?_⟩
  intro T' hT'
  exact hTmax T' (Finset.mem_filter.mpr ⟨Finset.mem_univ T', hT'⟩)

theorem deltaClose_mono {C : Submodule F (Fin n → α)} {δ₁ δ₂ : ℚ} {g : Fin n → α}
    (h : deltaClose C δ₁ g) (hδ : δ₁ ≤ δ₂) : deltaClose C δ₂ g := by
  obtain ⟨c, hc, hd⟩ := h
  exact ⟨c, hc, le_trans hd hδ⟩

end MCA.Code
