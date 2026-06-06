import Mathlib
import RSGLD.Code.Interleaved
import RSGLD.ListDecoding.EraseDecode

/-!
# GGR interleaving bound — the composition (erase-decode induction)

Assembles the erase-decode leaves of `EraseDecode.lean` and the tree leaf-count of
`TreeCount.lean` into the integer-parameterized GGR bound (paper Lemma 2.10 = GGR Thm 2.5). The
steps are: the red fan-out bound `≤ Λ`, the column-split count decomposition, the induction on `m`
(with the white / no-white case split and zero-case guards), the integer theorem, and the bridge
to `maxListSize`.

This file works with **columns** `Fin m → (Fin n → F)` (each a base word) and counts tuples of base
codewords whose total erased set is within the integer budget `E`. The bridge to
`maxListSize (interleave C m) (E/n)` is made at the end.
-/

namespace RSGLD.ListDecoding

open RSGLD.Code

variable {F : Type*} [Field F] [DecidableEq F] {n : ℕ}

/-- Disagreement positions of a single word `c` against a received column `R₀`. -/
def eraseSet (c R₀ : Fin n → F) : Finset (Fin n) :=
  Finset.univ.filter (fun i => c i ≠ R₀ i)

/-- Union of per-column disagreement positions of an `m`-tuple of words `M` against received
columns `R` — the total error/erasure set of the interleaved word. -/
def colBadSet (m : ℕ) (M R : Fin m → (Fin n → F)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => ∃ j : Fin m, M j i ≠ R j i)

omit [Field F] in
@[simp] theorem colBadSet_zero (M R : Fin 0 → (Fin n → F)) : colBadSet 0 M R = ∅ := by
  simp [colBadSet]

omit [Field F] in
/-- `|eraseSet c R₀| = hammingDist c R₀` — disagreements count is the Hamming distance. -/
theorem card_eraseSet (c R₀ : Fin n → F) : (eraseSet c R₀).card = hammingDist c R₀ := by
  rfl

omit [Field F] in
/-- **Column split.** The total erased set of `m+1` columns is the first column's erasures together
with the tail's total erased set. This drives the count decomposition. -/
theorem colBadSet_succ (m : ℕ) (M R : Fin (m + 1) → (Fin n → F)) :
    colBadSet (m + 1) M R
      = eraseSet (M 0) (R 0) ∪ colBadSet m (fun j => M j.succ) (fun j => R j.succ) := by
  classical
  ext i
  simp only [colBadSet, eraseSet, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union]
  constructor
  · rintro ⟨j, hj⟩
    rcases Fin.eq_zero_or_eq_succ j with h0 | ⟨k, hk⟩
    · subst h0; exact Or.inl hj
    · subst hk; exact Or.inr ⟨k, hj⟩
  · rintro (h0 | ⟨k, hk⟩)
    · exact ⟨0, h0⟩
    · exact ⟨k.succ, hk⟩

/-- The count of `m`-tuples of `C`-codewords whose total erased set (with pre-erased `S`) fits in
the integer budget `E`. The interleaved list size, in the recursion's column form. -/
noncomputable def Ninter (C : LinearCode F n) [Fintype C] (m : ℕ)
    (R : Fin m → (Fin n → F)) (S : Finset (Fin n)) (E : ℕ) : ℕ :=
  (Finset.univ.filter (fun M : Fin m → C =>
    (S ∪ colBadSet m (fun j => (M j : Fin n → F)) R).card ≤ E)).card

/-- **B — column-split decomposition.** Bounding the `(m+1)`-column count by the sum over the first
column of the `m`-column residual counts (pre-erased set grows by that column's disagreements). -/
theorem Ninter_succ_le (C : LinearCode F n) [Fintype C] (m : ℕ)
    (R : Fin (m + 1) → (Fin n → F)) (S : Finset (Fin n)) (E : ℕ) :
    Ninter C (m + 1) R S E
      ≤ ∑ c : C, Ninter C m (fun j => R j.succ) (S ∪ eraseSet (c : Fin n → F) (R 0)) E := by
  classical
  unfold Ninter
  rw [Finset.card_eq_sum_card_fiberwise (f := fun M : Fin (m + 1) → C => M 0)
       (t := Finset.univ) (fun M _ => Finset.mem_univ _)]
  apply Finset.sum_le_sum
  intro c _
  apply Finset.card_le_card_of_injOn (fun M => fun j => M j.succ)
  · intro M hM
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hM
    obtain ⟨hMcond, hM0⟩ := hM
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    have hsplit : (S ∪ colBadSet (m + 1) (fun j => (M j : Fin n → F)) R)
        = S ∪ eraseSet (c : Fin n → F) (R 0)
          ∪ colBadSet m (fun j => (M j.succ : Fin n → F)) (fun j => R j.succ) := by
      rw [colBadSet_succ, show ((M 0 : C) : Fin n → F) = (c : Fin n → F) from by rw [hM0]]
      ext i; simp only [Finset.mem_union]; tauto
    rw [← hsplit]; exact hMcond
  · intro M1 h1 M2 h2 heq
    simp only [Finset.mem_coe, Finset.mem_filter] at h1 h2
    funext j
    rcases Fin.eq_zero_or_eq_succ j with hj | ⟨k, hk⟩
    · subst hj; rw [h1.2, h2.2]
    · subst hk; exact congrFun heq k

omit [Field F] in
/-- New erasures: `|S ∪ eraseSet c R₀| = |S| + hammingDistOutside S c R₀`. So extendability
`|S ∪ eraseSet c R₀| ≤ E` is `S.card + w ≤ E` with `w := hammingDistOutside S c R₀`. -/
theorem card_union_eraseSet (S : Finset (Fin n)) (c R0 : Fin n → F) :
    (S ∪ eraseSet c R0).card = S.card + hammingDistOutside S c R0 := by
  classical
  have h1 : hammingDistOutside S c R0 = (eraseSet c R0 \ S).card := by
    rw [hammingDistOutside, eraseSet, Finset.sdiff_eq_filter, Finset.filter_filter]
  rw [h1, ← Finset.union_sdiff_self_eq_union,
      Finset.card_union_of_disjoint Finset.disjoint_sdiff]

/-- If the pre-erased set already exceeds the budget, there are no valid extensions. -/
theorem Ninter_eq_zero {C : LinearCode F n} [Fintype C] {m : ℕ} {R : Fin m → (Fin n → F)}
    {S : Finset (Fin n)} {E : ℕ} (hS : E < S.card) : Ninter C m R S E = 0 := by
  classical
  unfold Ninter
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro M _
  have : S.card ≤ (S ∪ colBadSet m (fun j => (M j : Fin n → F)) R).card :=
    Finset.card_le_card Finset.subset_union_left
  omega

/-- **A — the global base list size** `Λ := |Λ(C,E)|`, the per-node fan-out bound: the max over
received words `R₀` of the number of codewords within `E` errors. -/
noncomputable def baseListCount (C : LinearCode F n) [Fintype F] [Fintype C] (E : ℕ) : ℕ :=
  Finset.univ.sup (fun R0 : Fin n → F =>
    (Finset.univ.filter (fun c : C => hammingDist (c : Fin n → F) R0 ≤ E)).card)

/-- The base list at any received word `R₀` is bounded by the global `baseListCount`. -/
theorem card_baseList_le_baseListCount (C : LinearCode F n) [Fintype F] [Fintype C] (E : ℕ)
    (R0 : Fin n → F) :
    (Finset.univ.filter (fun c : C => hammingDist (c : Fin n → F) R0 ≤ E)).card
      ≤ baseListCount C E := by
  unfold baseListCount
  exact Finset.le_sup (f := fun R0 : Fin n → F =>
    (Finset.univ.filter (fun c : C => hammingDist (c : Fin n → F) R0 ≤ E)).card)
    (Finset.mem_univ R0)

/-- `baseListCount ≥ 1` (the zero codeword witnesses the base list at `R₀ = 0`). -/
theorem baseListCount_pos (C : LinearCode F n) [Fintype F] [Fintype C] (E : ℕ) :
    1 ≤ baseListCount C E := by
  classical
  refine le_trans ?_ (card_baseList_le_baseListCount C E (0 : Fin n → F))
  have hne : (Finset.univ.filter
      (fun c : C => hammingDist (c : Fin n → F) (0 : Fin n → F) ≤ E)).Nonempty :=
    ⟨⟨0, C.zero_mem⟩, by simp [Finset.mem_filter]⟩
  exact hne.card_pos

omit [Field F] in
/-- Extendable codewords lie in the base list at `R₀`: `|S ∪ eraseSet c R₀| ≤ E ⟹ hammingDist c R₀ ≤ E`. -/
theorem hammingDist_le_of_card_union_le {S : Finset (Fin n)} {c R0 : Fin n → F} {E : ℕ}
    (h : (S ∪ eraseSet c R0).card ≤ E) : hammingDist c R0 ≤ E := by
  have hle : (eraseSet c R0).card ≤ (S ∪ eraseSet c R0).card :=
    Finset.card_le_card Finset.subset_union_right
  rw [card_eraseSet] at hle
  omega

/-! ### C — the erase-decode induction (integer parameterized GGR bound) -/

open RSGLD.ReedSolomon in
/-- **C — the integer parameterized GGR bound (count form).** Under the integer invariant, the
interleaved count is bounded by `Nat.choose (b+r) r · Λ^r` with `Λ` the global base list size.
Induction on the column count `m`, with the white (unique child, same budgets) / no-white
(`N(b,r) ≤ N(b−1,r) + Λ·N(b,r−1)`, Pascal) split. -/
theorem Ninter_le (C : LinearCode F n) [Fintype F] [Fintype C] (hn : 0 < n)
    (D E : ℕ) (hED : E < D) (hD : (D : ℝ) ≤ minDist C * n) :
    ∀ (m b r : ℕ) (R : Fin m → (Fin n → F)) (S : Finset (Fin n)),
      Inv D E b r S.card →
      Ninter C m R S E ≤ Nat.choose (b + r) r * (baseListCount C E) ^ r := by
  intro m
  induction m with
  | zero =>
    intro b r R S hInv
    have h1 : Ninter C 0 R S E ≤ 1 := by
      unfold Ninter
      calc (Finset.univ.filter
              (fun M : Fin 0 → C => (S ∪ colBadSet 0 (fun j => (M j : Fin n → F)) R).card ≤ E)).card
            ≤ (Finset.univ : Finset (Fin 0 → C)).card := Finset.card_filter_le _ _
        _ = 1 := by simp
    have hb : 1 ≤ Nat.choose (b + r) r := Nat.choose_pos (Nat.le_add_left r b)
    have hL : 1 ≤ (baseListCount C E) ^ r := Nat.one_le_pow _ _ (baseListCount_pos C E)
    calc Ninter C 0 R S E ≤ 1 := h1
      _ = 1 * 1 := (one_mul 1).symm
      _ ≤ Nat.choose (b + r) r * (baseListCount C E) ^ r := Nat.mul_le_mul hb hL
  | succ m ih =>
    intro b r R S hInv
    obtain ⟨hInv1, hInv2, hInv3⟩ := hInv
    refine le_trans (Ninter_succ_le C m R S E) ?_
    classical
    set s := S.card with hs
    set w := fun c : C => hammingDistOutside S (c : Fin n → F) (R 0) with hw
    set g := fun c : C => Ninter C m (fun j => R j.succ) (S ∪ eraseSet (c : Fin n → F) (R 0)) E
      with hg
    have hcard : ∀ c : C, (S ∪ eraseSet (c : Fin n → F) (R 0)).card = s + w c :=
      fun c => card_union_eraseSet S (c : Fin n → F) (R 0)
    by_cases hW : ∃ c : C, s + w c ≤ E ∧ w c < D - E
    · -- WHITE case: the unique child
      obtain ⟨c₀, hc₀ext, hc₀white⟩ := hW
      have hsingle : (∑ c : C, g c) = g c₀ := by
        refine Finset.sum_eq_single c₀ (fun c _ hcne => ?_) (fun h => absurd (Finset.mem_univ c₀) h)
        by_cases hext : s + w c ≤ E
        · exact absurd (Subtype.coe_injective
            (white_unique hn c₀.2 c.2 D E hD hc₀white hext).symm) hcne
        · apply Ninter_eq_zero; rw [hcard]; omega
      rw [hsingle]
      have hInv' : Inv D E b r (S ∪ eraseSet (c₀ : Fin n → F) (R 0)).card := by
        rw [hcard]; exact Inv.white ⟨hInv1, hInv2, hInv3⟩ (Nat.le_add_right _ _) hc₀ext
      exact ih b r (fun j => R j.succ) _ hInv'
    · -- NO-WHITE case
      push Not at hW   -- hW : ∀ c, s + w c ≤ E → D - E ≤ w c
      rcases Nat.eq_zero_or_pos r with hr0 | hrpos
      · -- r = 0 ⟹ s = E ⟹ no extendable child ⟹ sum 0
        subst hr0
        rw [Finset.sum_eq_zero (fun c _ => ?_)]
        · simp
        apply Ninter_eq_zero; rw [hcard]
        by_contra hle; push Not at hle
        have := hW c hle
        simp only [pow_zero, Nat.one_mul] at hInv3
        omega
      · -- r ≥ 1
        set Λ := baseListCount C E with hΛ
        set blueExt := Finset.univ.filter
          (fun c : C => s + w c ≤ E ∧ D - E ≤ w c ∧ 2 * w c < D - s) with hblue
        set redExt := Finset.univ.filter
          (fun c : C => s + w c ≤ E ∧ D - E ≤ w c ∧ D - s ≤ 2 * w c) with hred
        have hsupp : ∀ c ∈ (Finset.univ : Finset C), c ∉ blueExt ∪ redExt → g c = 0 := by
          intro c _ hc
          apply Ninter_eq_zero; rw [hcard]
          by_contra hle; push Not at hle
          have hwG : D - E ≤ w c := hW c hle
          apply hc
          rw [Finset.mem_union, hblue, hred, Finset.mem_filter, Finset.mem_filter]
          rcases lt_or_ge (2 * w c) (D - s) with hlt | hge
          · exact Or.inl ⟨Finset.mem_univ c, hle, hwG, hlt⟩
          · exact Or.inr ⟨Finset.mem_univ c, hle, hwG, hge⟩
        have hdisj : Disjoint blueExt redExt := by
          rw [hblue, hred, Finset.disjoint_filter]
          intro c _ hbp hrp
          obtain ⟨_, _, hlt⟩ := hbp; obtain ⟨_, _, hge⟩ := hrp; omega
        rw [← Finset.sum_subset (Finset.subset_univ (blueExt ∪ redExt)) hsupp,
            Finset.sum_union hdisj]
        have hblue_card : blueExt.card ≤ 1 := by
          rw [Finset.card_le_one]
          intro a ha b' hb'
          rw [hblue, Finset.mem_filter] at ha hb'
          exact Subtype.coe_injective
            (blue_unique hn a.2 b'.2 D hD ha.2.2.2 hb'.2.2.2)
        have hblue_bound : (∑ c ∈ blueExt, g c) ≤ Nat.choose (b + r - 1) r * Λ ^ r := by
          have h1 : (∑ c ∈ blueExt, g c) ≤ blueExt.card • (Nat.choose (b + r - 1) r * Λ ^ r) := by
            apply Finset.sum_le_card_nsmul
            intro c hc
            rw [hblue, Finset.mem_filter] at hc
            obtain ⟨_, hext, hwG, _⟩ := hc
            obtain ⟨hbpos, hbinv⟩ := Inv.blue hED ⟨hInv1, hInv2, hInv3⟩ hwG hext
            have key := ih (b - 1) r (fun j => R j.succ) (S ∪ eraseSet (c : Fin n → F) (R 0))
              (by rw [hcard]; exact hbinv)
            rwa [show b - 1 + r = b + r - 1 by omega] at key
          rw [nsmul_eq_mul] at h1
          refine le_trans h1 ?_
          calc (blueExt.card : ℕ) * (Nat.choose (b + r - 1) r * Λ ^ r)
              ≤ 1 * (Nat.choose (b + r - 1) r * Λ ^ r) := by gcongr
            _ = Nat.choose (b + r - 1) r * Λ ^ r := one_mul _
        have hred_card : redExt.card ≤ Λ := by
          refine le_trans (Finset.card_le_card (fun c hc => ?_))
            (card_baseList_le_baseListCount C E (R 0))
          rw [hred, Finset.mem_filter] at hc
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ c, hammingDist_le_of_card_union_le (by rw [hcard]; exact hc.2.1)⟩
        have hred_bound : (∑ c ∈ redExt, g c) ≤ Nat.choose (b + r - 1) (r - 1) * Λ ^ r := by
          have h1 : (∑ c ∈ redExt, g c)
              ≤ redExt.card • (Nat.choose (b + r - 1) (r - 1) * Λ ^ (r - 1)) := by
            apply Finset.sum_le_card_nsmul
            intro c hc
            rw [hred, Finset.mem_filter] at hc
            obtain ⟨_, hext, _, hge⟩ := hc
            obtain ⟨hrpos', hrinv⟩ := Inv.red hED ⟨hInv1, hInv2, hInv3⟩ hge hext
            have key := ih b (r - 1) (fun j => R j.succ) (S ∪ eraseSet (c : Fin n → F) (R 0))
              (by rw [hcard]; exact hrinv)
            rwa [show b + (r - 1) = b + r - 1 by omega] at key
          rw [nsmul_eq_mul] at h1
          have hΛpow : Λ * Λ ^ (r - 1) = Λ ^ r := by
            rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hrpos]
          refine le_trans h1 ?_
          calc (redExt.card : ℕ) * (Nat.choose (b + r - 1) (r - 1) * Λ ^ (r - 1))
              ≤ Λ * (Nat.choose (b + r - 1) (r - 1) * Λ ^ (r - 1)) := by gcongr
            _ = Nat.choose (b + r - 1) (r - 1) * Λ ^ r := by rw [mul_left_comm, hΛpow]
        have hpascal : Nat.choose (b + r) r
            = Nat.choose (b + r - 1) r + Nat.choose (b + r - 1) (r - 1) := by
          obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
          rw [show b + (r' + 1) - 1 = b + r' by omega, show r' + 1 - 1 = r' by omega,
            show b + (r' + 1) = (b + r') + 1 by omega, Nat.choose_succ_succ, Nat.add_comm]
        calc (∑ c ∈ blueExt, g c) + ∑ c ∈ redExt, g c
            ≤ Nat.choose (b + r - 1) r * Λ ^ r + Nat.choose (b + r - 1) (r - 1) * Λ ^ r :=
              Nat.add_le_add hblue_bound hred_bound
          _ = Nat.choose (b + r) r * Λ ^ r := by rw [hpascal]; ring

/-! ### Bridge — from the count `Ninter` to `maxListSize (interleave C m)` -/

omit [Field F] in
/-- The interleaved Hamming distance equals the total erased-set (union of column disagreements). -/
theorem hammingDist_eq_colBadSet_card (m : ℕ) (M R : Fin n → Fin m → F) :
    hammingDist M R = (colBadSet m (fun j i => M i j) (fun j i => R i j)).card := by
  rw [hammingDist, colBadSet]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.ne_iff]

/-- `interleave C m` (matrices with columns in `C`) is equivalent to `m`-tuples of `C`-codewords. -/
def interleaveColsEquiv (C : LinearCode F n) (m : ℕ) : interleave C m ≃ (Fin m → C) where
  toFun M := fun j => ⟨fun i => (M : Fin n → Fin m → F) i j, mem_interleave.mp M.2 j⟩
  invFun T := ⟨fun i j => (T j : Fin n → F) i, mem_interleave.mpr (fun j => (T j).2)⟩
  left_inv M := by ext i j; rfl
  right_inv T := by ext j i; rfl

/-- **Bridge (card form).** The interleaved list at radius `E/n` around a matrix `R` has the same
size as the count `Ninter` of column-tuples within `E` errors. -/
theorem listAt_interleave_card_eq_Ninter (C : LinearCode F n) [Fintype F] [Fintype C]
    (m : ℕ) [Fintype (interleave C m)] (hn : 0 < n) (E : ℕ) (R : Fin n → Fin m → F) :
    (listAt (interleave C m) ((E : ℚ) / n) R).card = Ninter C m (fun j i => R i j) ∅ E := by
  classical
  rw [Ninter]
  refine Finset.card_equiv (interleaveColsEquiv C m) (fun M => ?_)
  rw [listAt, Finset.mem_filter, Finset.mem_filter]
  have hnq : (0 : ℚ) < n := by exact_mod_cast hn
  have hcard : (colBadSet m (fun j i => (interleaveColsEquiv C m M j : Fin n → F) i)
      (fun j i => R i j)).card = hammingDist R (M : Fin n → Fin m → F) := by
    rw [hammingDist_comm, hammingDist_eq_colBadSet_card m (M : Fin n → Fin m → F) R]
    rfl
  constructor
  · rintro ⟨_, hd⟩
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Finset.empty_union, hcard]
    rw [normDist, div_le_div_iff_of_pos_right hnq] at hd
    exact_mod_cast hd
  · rintro ⟨_, hd⟩
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Finset.empty_union, hcard] at hd
    rw [normDist, div_le_div_iff_of_pos_right hnq]
    exact_mod_cast hd

/-- The global base list count equals the base `maxListSize` at radius `E/n`. -/
theorem baseListCount_eq_maxListSize (C : LinearCode F n) [Fintype F] [Fintype C] (hn : 0 < n)
    (E : ℕ) : baseListCount C E = maxListSize C ((E : ℚ) / n) := by
  rw [baseListCount, maxListSize]
  refine Finset.sup_congr rfl (fun R0 _ => ?_)
  rw [listAt]
  refine congrArg Finset.card (Finset.filter_congr (fun c _ => ?_))
  have hnq : (0 : ℚ) < n := by exact_mod_cast hn
  rw [normDist, hammingDist_comm, div_le_div_iff_of_pos_right hnq]
  constructor
  · intro h; exact_mod_cast h
  · intro h; exact_mod_cast h

open RSGLD.ReedSolomon in
/-- **E — the integer parameterized GGR bound for `maxListSize`.** Under the integer conditions
`E ≤ b·(D−E)` and `D ≤ 2^r·(D−E)` (with `D ≤ minDist C · n`, `E < D`):
`|Λ(C^{≡m}, E/n)| ≤ Nat.choose (b+r) r · |Λ(C, E/n)|^r`. Obtained from `Ninter_le` (the count form)
via the bridge, taking the sup over received words. -/
theorem maxListSize_interleave_le_int (C : LinearCode F n) [Fintype F] [Fintype C] (m : ℕ)
    [Fintype (interleave C m)] (hn : 0 < n) (D E b r : ℕ) (hED : E < D)
    (hD : (D : ℝ) ≤ minDist C * n) (hb : E ≤ b * (D - E)) (hr2 : D ≤ 2 ^ r * (D - E)) :
    maxListSize (interleave C m) ((E : ℚ) / n)
      ≤ Nat.choose (b + r) r * (maxListSize C ((E : ℚ) / n)) ^ r := by
  have hInv0 : Inv D E b r (∅ : Finset (Fin n)).card := by
    rw [Finset.card_empty]; exact ⟨Nat.zero_le E, by simpa using hb, by simpa using hr2⟩
  rw [maxListSize]
  apply Finset.sup_le
  intro R _
  rw [listAt_interleave_card_eq_Ninter C m hn E R, ← baseListCount_eq_maxListSize C hn E]
  exact Ninter_le C hn D E hED hD m b r (fun j i => R i j) ∅ hInv0

end RSGLD.ListDecoding
