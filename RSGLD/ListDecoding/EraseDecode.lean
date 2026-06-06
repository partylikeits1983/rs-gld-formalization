import Mathlib
import RSGLD.Code.Hamming
import RSGLD.ReedSolomon.MDS

/-!
# Erase-decode leaves for the GGR interleaving bound

Erasures are tracked as a **coordinate predicate** `hammingDistOutside S` (disagreements outside
the erased set `S`), rather than a `Fin (n−|S|)` punctured type (which would create cast hell).
The composition (`GGRComposition.lean`) assembles these leaves with the tree leaf-count
`RSGLD.ListDecoding.treeLeaves_le`.

* `hammingDistOutside` — disagreements outside the erased set `S`.
* `hammingDist_le_hammingDistOutside_add_card` — **combinatorial core**: erasing `S` removes
  at most `|S|` disagreements, i.e. `hammingDist x y ≤ hammingDistOutside S x y + |S|`.
-/

namespace RSGLD.Code

variable {α : Type*} [DecidableEq α] {n : ℕ}

/-- Hamming disagreements **outside** the erased set `S` (the expert's `distOutside`). -/
def hammingDistOutside (S : Finset (Fin n)) (x y : Fin n → α) : ℕ :=
  (Finset.univ.filter fun i => x i ≠ y i ∧ i ∉ S).card

/-- **L1′ (combinatorial core).** Total Hamming disagreements are at most the disagreements outside
`S` plus `|S|`: erasing the `|S|` coordinates of `S` removes at most `|S|` disagreements. This is the
minDist-free half of the puncture distance-drop; combined with the minimum-distance bound on
`hammingDist` for distinct codewords it yields `hammingDistOutside S c c' ≥ minDist·n − |S|`. -/
theorem hammingDist_le_hammingDistOutside_add_card (S : Finset (Fin n)) (x y : Fin n → α) :
    hammingDist x y ≤ hammingDistOutside S x y + S.card := by
  classical
  rw [hammingDist, hammingDistOutside]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun i => x i ≠ y i)) (p := fun i => i ∈ S)
  have h1 : ((Finset.univ.filter (fun i => x i ≠ y i)).filter (fun i => i ∈ S)).card ≤ S.card :=
    Finset.card_le_card (by
      intro i hi
      rw [Finset.mem_filter] at hi
      exact hi.2)
  have h2 : (Finset.univ.filter (fun i => x i ≠ y i)).filter (fun i => ¬ i ∈ S)
      = Finset.univ.filter (fun i => x i ≠ y i ∧ i ∉ S) := Finset.filter_filter _ _ _
  rw [h2] at hsplit
  omega

/-- Symmetry of `hammingDistOutside`. -/
theorem hammingDistOutside_comm (S : Finset (Fin n)) (x y : Fin n → α) :
    hammingDistOutside S x y = hammingDistOutside S y x := by
  unfold hammingDistOutside
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact and_congr_left (fun _ => ne_comm)

/-- Restricted triangle inequality: disagreements outside `S` obey the triangle inequality. -/
theorem hammingDistOutside_triangle (S : Finset (Fin n)) (x y z : Fin n → α) :
    hammingDistOutside S x z ≤ hammingDistOutside S x y + hammingDistOutside S y z := by
  classical
  unfold hammingDistOutside
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  obtain ⟨hxz, hiS⟩ := hi
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hxy : x i = y i
  · right; exact ⟨by rw [← hxy]; exact hxz, hiS⟩
  · left; exact ⟨hxy, hiS⟩

/-! ### The integer erase-decode budget invariant

The whole GGR core is done in **integer counts first**:
* `D` — a minimum-distance lower bound of `C`, as a coordinate count (`≈ δn`);
* `E` — the decoding radius in errors (`≈ ηn`);
* `G := D − E` (`≈ (δ−η)n`), with `E < D` so `G > 0`;
* `s := |S|` — the accumulated erased-coordinate count at a tree node;
* `b, r` — the Blue and Red budgets.

The invariant (addition-only form, nicer in Lean):
`s ≤ E  ∧  E ≤ s + b·G  ∧  D ≤ s + 2^r·G`.
It holds at the root (`s = 0`: `E ≤ b·G`, `D ≤ 2^r·G`) and is preserved into each child after
adding `w := |D_c \ S|` new erasures, with the White/Blue/Red trichotomy
`White: w < G`, `Blue: G ≤ w ∧ 2w < D−s`, `Red: G ≤ w ∧ D−s ≤ 2w`. -/

/-- The integer erase-decode budget invariant. -/
def Inv (D E b r s : ℕ) : Prop :=
  s ≤ E ∧ E ≤ s + b * (D - E) ∧ D ≤ s + 2 ^ r * (D - E)

/-- **White preservation.** A White child adds erasures (`s ≤ s'`) but keeps the budgets; the
invariant only gets easier as `s` grows. -/
theorem Inv.white {D E b r s s' : ℕ} (h : Inv D E b r s) (hss : s ≤ s') (hs'E : s' ≤ E) :
    Inv D E b r s' := by
  obtain ⟨_, h2, h3⟩ := h
  exact ⟨hs'E, by omega, by omega⟩

/-- **Blue preservation.** A Blue edge (`G ≤ w` new erasures) spends one Blue budget: `b > 0` and
the invariant holds with `b−1` at `s' = s + w`. -/
theorem Inv.blue {D E b r s w : ℕ} (hED : E < D) (h : Inv D E b r s)
    (hG : D - E ≤ w) (hs'E : s + w ≤ E) :
    0 < b ∧ Inv D E (b - 1) r (s + w) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hb : 0 < b := by
    rcases Nat.eq_zero_or_pos b with hb0 | hb0
    · subst hb0; simp only [Nat.zero_mul, Nat.add_zero] at h2; omega
    · exact hb0
  have hb1 : (b - 1) * (D - E) + (D - E) = b * (D - E) := by
    have hbpred : (b - 1) + 1 = b := Nat.succ_pred_eq_of_pos hb
    calc (b - 1) * (D - E) + (D - E) = ((b - 1) + 1) * (D - E) := by rw [add_one_mul]
      _ = b * (D - E) := by rw [hbpred]
  exact ⟨hb, hs'E, by omega, by omega⟩

/-- **Red preservation.** A Red edge (`D−s ≤ 2w`) spends one Red budget: `r > 0` and the invariant
holds with `r−1` at `s' = s + w`. The gap at least halves: `2·(D−s') ≤ D−s ≤ 2^r·G`, so
`D−s' ≤ 2^{r-1}·G`. -/
theorem Inv.red {D E b r s w : ℕ} (hED : E < D) (h : Inv D E b r s)
    (hred : D - s ≤ 2 * w) (hs'E : s + w ≤ E) :
    0 < r ∧ Inv D E b (r - 1) (s + w) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with hr0 | hr0
    · subst hr0; simp only [pow_zero, Nat.one_mul] at h3; omega
    · exact hr0
  have hpow : 2 ^ r = 2 * 2 ^ (r - 1) := by
    conv_lhs => rw [show r = (r - 1) + 1 from (Nat.succ_pred_eq_of_pos hr).symm]
    rw [pow_succ]; ring
  have h3' : D ≤ s + 2 * (2 ^ (r - 1) * (D - E)) := by rw [hpow] at h3; linarith [h3]
  exact ⟨hr, hs'E, by omega, by omega⟩

/-! ### L1′ proper — the residual distance-drop for distinct codewords

Combining the combinatorial core with the minimum-distance bound: two distinct codewords of `C`
differ, **outside any erased set `S`**, on at least `D − |S|` coordinates, where `D` is a
coordinate-count lower bound on `minDist C · n`. This is the geometric input to white-uniqueness
(L3) and blue-uniqueness (L4): `(D−E) + (E−s) = D−s` then forces siblings to coincide. -/

open RSGLD.ReedSolomon in
/-- A coordinate-count minimum-distance bound: distinct codewords differ on `≥ D` positions, where
`D ≤ minDist C · n`. -/
theorem minDistCount_le_hammingDist {F : Type*} [Field F] [DecidableEq F] {n : ℕ} (hn : 0 < n)
    {C : LinearCode F n} {c c' : Fin n → F} (hc : c ∈ C) (hc' : c' ∈ C) (hne : c ≠ c')
    (D : ℕ) (hD : (D : ℝ) ≤ minDist C * n) :
    D ≤ hammingDist c c' := by
  have hsub : c - c' ∈ C := Submodule.sub_mem C hc hc'
  have hne0 : c - c' ≠ (0 : Fin n → F) := sub_ne_zero.mpr hne
  have h1 : minDist C ≤ (normDist (c - c') (0 : Fin n → F) : ℝ) :=
    minDist_le_normDist C hsub hne0
  have h2 : normDist c c' = normDist (c - c') (0 : Fin n → F) := normDist_sub_left c c'
  rw [← h2] at h1
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have h3 : (normDist c c' : ℝ) = (hammingDist c c' : ℝ) / (n : ℝ) := by
    unfold normDist; push_cast; ring
  rw [h3, le_div_iff₀ hnr] at h1
  have : (D : ℝ) ≤ (hammingDist c c' : ℝ) := le_trans hD h1
  exact_mod_cast this

open RSGLD.ReedSolomon in
/-- **L1′ proper.** Distinct codewords of `C` differ on at least `D − |S|` coordinates **outside**
the erased set `S` (`D ≤ minDist C · n`). The geometric distance-drop driving white/blue uniqueness. -/
theorem D_sub_card_le_hammingDistOutside {F : Type*} [Field F] [DecidableEq F] {n : ℕ} (hn : 0 < n)
    {C : LinearCode F n} {c c' : Fin n → F} (hc : c ∈ C) (hc' : c' ∈ C) (hne : c ≠ c')
    (D : ℕ) (hD : (D : ℝ) ≤ minDist C * n) (S : Finset (Fin n)) :
    D - S.card ≤ hammingDistOutside S c c' := by
  have h1 := minDistCount_le_hammingDist hn hc hc' hne D hD
  have h2 := hammingDist_le_hammingDistOutside_add_card S c c'
  omega

/-! ### L3 / L4 — white- and blue-edge uniqueness

Both follow from L1′ (`D_sub_card_le_hammingDistOutside`) + the restricted triangle inequality, via
the integer identity `(D−E) + (E−s) = D−s`. A **white** child (`w < G = D−E`) coincides with any
extendable sibling (`s + w' ≤ E`); two **blue** children (`2w < D−s`) coincide. -/

open RSGLD.ReedSolomon in
/-- **L3 (white-edge uniqueness).** A White child `c` (`hammingDistOutside S c R < D−E`) equals any
extendable sibling `c'` (`|S| + hammingDistOutside S c' R ≤ E`): so a White node has a unique child. -/
theorem white_unique {F : Type*} [Field F] [DecidableEq F] {n : ℕ} (hn : 0 < n)
    {C : LinearCode F n} {S : Finset (Fin n)} {R c c' : Fin n → F}
    (hc : c ∈ C) (hc' : c' ∈ C) (D E : ℕ) (hD : (D : ℝ) ≤ minDist C * n)
    (hwhite : hammingDistOutside S c R < D - E)
    (hext : S.card + hammingDistOutside S c' R ≤ E) :
    c = c' := by
  by_contra hne
  have hdist := D_sub_card_le_hammingDistOutside hn hc hc' hne D hD S
  have htri := hammingDistOutside_triangle S c R c'
  have hsymm := hammingDistOutside_comm S R c'
  omega

open RSGLD.ReedSolomon in
/-- **L4 (blue-edge uniqueness).** Two Blue children (`2·hammingDistOutside S · R < D − |S|`) of a
node coincide: so a node has at most one Blue child. -/
theorem blue_unique {F : Type*} [Field F] [DecidableEq F] {n : ℕ} (hn : 0 < n)
    {C : LinearCode F n} {S : Finset (Fin n)} {R c c' : Fin n → F}
    (hc : c ∈ C) (hc' : c' ∈ C) (D : ℕ) (hD : (D : ℝ) ≤ minDist C * n)
    (hb : 2 * hammingDistOutside S c R < D - S.card)
    (hb' : 2 * hammingDistOutside S c' R < D - S.card) :
    c = c' := by
  by_contra hne
  have hdist := D_sub_card_le_hammingDistOutside hn hc hc' hne D hD S
  have htri := hammingDistOutside_triangle S c R c'
  have hsymm := hammingDistOutside_comm S R c'
  omega

end RSGLD.Code
