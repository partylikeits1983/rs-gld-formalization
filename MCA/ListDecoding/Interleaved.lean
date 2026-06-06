import Mathlib
import MCA.Code.Defs
import MCA.Code.ListDecode
import MCA.Code.Interleaved
import MCA.ReedSolomon.Defs
import MCA.ReedSolomon.MDS
import MCA.Code.JohnsonBound

/-!
# Interleaved Reed–Solomon list decoding (grand list decoding challenge)

This module attacks the **grand list decoding challenge** of eprint 2026/680
(Arnon–Boneh–Fenzi), `references/core/2026-680.pdf`: for `C = RS[F,L,k]` and the
`m`-interleaved code `C^{≡m}` (Definition 2.9), determine the largest `δ*` with
`|Λ(C^{≡m}, δ*)| ≤ ε*·|F|`.

The interleaved code itself (`MCA.Code.interleave`, general `m`), the list and max
list size (`MCA.Code.listAt`, `maxListSize` = Definition 2.8), the sandwich lower
bound (`maxListSize_interleaved_lb`), and `minDist_interleave_ge` already live in
the repo; this file specializes to RS and adds the new leaves.

## Honesty (CLAUDE epistemic law)

Paper **Lemma 2.10** bounds `|Λ(C^{≡m},δ)| ≤ r^{b+r}·|Λ(C,δ)|^r` *independently of
`m`*, so interleaving does **not** move the frontier — the challenge reduces to the
base-RS list size beyond Johnson (external open, BCIKS20/BCHKS25). The lemmas here
are the provable scaffolding (overlap, δmin, `m`-power sandwich, Johnson baseline);
the near-capacity `η^{-O(m)}` prize stays external.

## Leaves

* `interleavedRS`, `mem_interleavedRS` — GLD-1 (wrapper).
* `interleavedRS_agree_intersection_le` — GLD-2 (overlap lemma `|A_F ∩ A_G| ≤ k−1`).
-/

namespace MCA.ListDecoding

open MCA.Code MCA.ReedSolomon Polynomial

variable {F : Type*} [Field F] [DecidableEq F]

/-! ### GLD-1 — the interleaved Reed–Solomon code `C^{≡m}` -/

/-- The `m`-interleaved Reed–Solomon code `(RS[F,L,k])^{≡m}` (Definition 2.9 ∘ 2.11):
words `g : Fin n → (Fin m → F)` such that every column `i ↦ g i j` is a degree-`<k`
evaluation, i.e. a codeword of `RS[F,L,k]`. -/
@[reducible] noncomputable def interleavedRS (L : Finset F) (k m : ℕ) :
    Submodule F (Fin L.card → Fin m → F) :=
  interleave (code L k) m

/-- Membership in `(RS[F,L,k])^{≡m}`: every column is a Reed–Solomon codeword. -/
theorem mem_interleavedRS {L : Finset F} {k m : ℕ} {g : Fin L.card → Fin m → F} :
    g ∈ interleavedRS L k m ↔ ∀ j : Fin m, (fun i => g i j) ∈ code L k :=
  mem_interleave

/-! ### GLD-2 — the overlap lemma

Two **distinct** interleaved RS codewords, given as `m`-tuples of degree-`<k`
polynomials `P, Q`, can simultaneously agree with a single received word
`w : Fin n → Fin m → F` on at most `k − 1` positions.

Reason: pick a column `j` with `P j ≠ Q j`; then `h := P j − Q j` is a nonzero
polynomial of degree `< k`, and every common-agreement point is a root of `h` in
`L`, of which there are at most `k − 1` (`Polynomial.card_le_degree_of_subset_roots`,
the `rs_weight_lower_bound` pattern). This is the foundational counting input for
every interleaved list-size bound. -/
theorem interleavedRS_agree_intersection_le {L : Finset F} {k m : ℕ}
    (w : Fin L.card → Fin m → F) (P Q : Fin m → F[X])
    (hP : ∀ i, P i ∈ Polynomial.degreeLT F k)
    (hQ : ∀ i, Q i ∈ Polynomial.degreeLT F k)
    (hne : P ≠ Q) :
    (Finset.univ.filter fun x : Fin L.card =>
        (∀ i, (P i).eval (evalPoints L x) = w x i) ∧
        (∀ i, (Q i).eval (evalPoints L x) = w x i)).card ≤ k - 1 := by
  classical
  -- A column `j` where the two tuples differ.
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
  -- `h := P j − Q j` is a nonzero polynomial of degree `< k`.
  set h : F[X] := P j - Q j with hhdef
  have hhne : h ≠ 0 := sub_ne_zero.mpr hj
  have hhmem : h ∈ Polynomial.degreeLT F k := (Polynomial.degreeLT F k).sub_mem (hP j) (hQ j)
  rw [Polynomial.mem_degreeLT] at hhmem
  have hdeg : h.natDegree < k := by
    rw [Polynomial.natDegree_lt_iff_degree_lt hhne]; exact hhmem
  -- The agreement-intersection set.
  set S : Finset (Fin L.card) :=
    Finset.univ.filter fun x : Fin L.card =>
      (∀ i, (P i).eval (evalPoints L x) = w x i) ∧
      (∀ i, (Q i).eval (evalPoints L x) = w x i) with hS
  -- Every point of `S` is a root of `h`: `(P j)(x) = w x j = (Q j)(x)`.
  have hSroot : ∀ x ∈ S, h.eval (evalPoints L x) = 0 := by
    intro x hx
    rw [hS, Finset.mem_filter] at hx
    have h1 := hx.2.1 j
    have h2 := hx.2.2 j
    rw [hhdef, Polynomial.eval_sub, h1, h2, sub_self]
  -- Image of `S` under the injective `evalPoints` lies in `h.roots`.
  have himg : (S.image (evalPoints L)).val ⊆ h.roots := by
    intro x hx
    rw [Finset.mem_val, Finset.mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [Polynomial.mem_roots hhne]
    exact hSroot i hi
  -- Hence `|S| ≤ natDegree h ≤ k − 1`.
  have hScard : S.card ≤ h.natDegree := by
    have h1 : (S.image (evalPoints L)).card ≤ h.natDegree :=
      Polynomial.card_le_degree_of_subset_roots himg
    rwa [Finset.card_image_of_injective S (evalPoints_injective L)] at h1
  omega

/-! ### GLD-4 — the `m`-power sandwich upper bound

`|Λ(C^{≡m}, δ)| ≤ |Λ(C, δ)|^m` (Definition 2.9 remark in eprint 2026/680). Together
with the existing lower bound `maxListSize_interleaved_lb` this is the full sandwich
`|Λ(C,δ)| ≤ |Λ(C^{≡m},δ)| ≤ |Λ(C,δ)|^m`.

Proof: for a received word `w`, a codeword `g ∈ Λ(C^{≡m},δ,w)` is determined by its
`m` columns, each of which lies in `Λ(C,δ,w·j)` (a coordinate where a column differs
is a coordinate where the whole vector differs, so column distance ≤ vector distance
≤ δ). Hence `g ↦ (columns)` injects `Λ(C^{≡m},δ,w)` into `∏_j Λ(C,δ,w·j)`, whose
cardinality is `∏_j |Λ(C,δ,w·j)| ≤ |Λ(C,δ)|^m`. -/
theorem maxListSize_interleave_le_pow [Fintype F] {n : ℕ}
    (C : LinearCode F n) [Fintype C] (m : ℕ) [Fintype (interleave C m)] (δ : ℚ) :
    maxListSize (interleave C m) δ ≤ (maxListSize C δ) ^ m := by
  classical
  unfold maxListSize
  apply Finset.sup_le
  intro w _
  -- Column projection of an interleaved codeword as an element of `↥C`.
  set Φ : (interleave C m) → (Fin m → C) :=
    fun g j => ⟨fun i => (g : Fin n → Fin m → F) i j, (mem_interleave.mp g.2) j⟩ with hΦ
  -- Per-column distance ≤ vector distance.
  have hcol : ∀ (u v : Fin n → Fin m → F) (j : Fin m),
      hammingDist (fun i => u i j) (fun i => v i j) ≤ hammingDist u v := by
    intro u v j
    unfold hammingDist
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    intro hcontra
    exact hi (congrFun hcontra j)
  -- `Λ(C^{≡m},δ,w)` injects into `∏_j Λ(C,δ,w·j)`.
  have hsub : (listAt (interleave C m) δ w).card
      ≤ (Fintype.piFinset (fun j => listAt C δ (fun i => w i j))).card := by
    apply Finset.card_le_card_of_injOn Φ
    · -- maps into the product of column lists
      intro g hg
      have hgd : normDist w (g : Fin n → Fin m → F) ≤ δ := mem_listAt.mp hg
      apply Fintype.mem_piFinset.mpr
      intro j
      apply mem_listAt.mpr
      show normDist (fun i => w i j) (fun i => (g : Fin n → Fin m → F) i j) ≤ δ
      -- column distance ≤ vector distance ≤ δ
      have hle : hammingDist (fun i => w i j) (fun i => (g : Fin n → Fin m → F) i j)
            ≤ hammingDist w (g : Fin n → Fin m → F) := hcol w (g : Fin n → Fin m → F) j
      calc normDist (fun i => w i j) (fun i => (g : Fin n → Fin m → F) i j)
            ≤ normDist w (g : Fin n → Fin m → F) := by
              unfold normDist; gcongr <;> exact_mod_cast hle
        _ ≤ δ := hgd
    · -- injective on the list: a word is determined by its columns
      intro g₁ _ g₂ _ heq
      apply Subtype.ext
      funext i j
      have hj : Φ g₁ j = Φ g₂ j := congrFun heq j
      have hv : (Φ g₁ j : Fin n → F) = (Φ g₂ j : Fin n → F) := congrArg Subtype.val hj
      exact congrFun hv i
  -- `∏_j |Λ(C,δ,w·j)| ≤ |Λ(C,δ)|^m`.
  refine hsub.trans ?_
  rw [Fintype.card_piFinset]
  calc ∏ j : Fin m, (listAt C δ (fun i => w i j)).card
        ≤ ∏ _j : Fin m, maxListSize C δ := by
          apply Finset.prod_le_prod
          · intro _ _; exact Nat.zero_le _
          · intro j _
            exact Finset.le_sup (f := fun f : Fin n → F => (listAt C δ f).card)
              (Finset.mem_univ (fun i => w i j))
    _ = (maxListSize C δ) ^ m := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-! ### GLD-3 — interleaving preserves the minimum distance

`δmin(C^{≡m}) = δmin(C)` (roadmap D / paper Def 2.9). The `≥` direction is the
existing `minDist_interleave_ge` (a nonzero interleaved word has weight ≥ that of
any nonzero column). The `≤` direction uses the constant lift `liftConst`: the
diagonal embedding of a nonzero base codeword is a nonzero interleaved codeword of
the *same* normalized weight, so `δmin(C^{≡m})` lower-bounds every base weight,
hence `≤ δmin(C)`. For RS this gives `δmin((RS[F,L,k])^{≡m}) = (n−k+1)/n`. -/
theorem minDist_interleave_eq {n : ℕ} (C : LinearCode F n) (m : ℕ) (hm : 0 < m) :
    minDist (interleave C m) = minDist C := by
  classical
  refine le_antisymm ?_ (minDist_interleave_ge C m hm)
  -- `δmin(C^{≡m}) ≤ δmin(C)`: it is a lower bound of the base-weight set.
  by_cases hbot : ∃ c : Fin n → F, c ∈ C ∧ c ≠ 0
  · show minDist (interleave C m)
        ≤ sInf {d : ℝ | ∃ c ∈ C, c ≠ 0 ∧ d = (normDist c (0 : Fin n → F) : ℝ)}
    apply le_csInf
    · obtain ⟨c, hc, hcne⟩ := hbot
      exact ⟨(normDist c (0 : Fin n → F) : ℝ), c, hc, hcne, rfl⟩
    · rintro d ⟨c, hc, hcne, rfl⟩
      -- The constant lift of `c`.
      set cI : Fin n → Fin m → F :=
        ((liftConst (m := m) (⟨c, hc⟩ : C) : interleave C m) : Fin n → Fin m → F) with hcIdef
      have hcIval : cI = fun i (_ : Fin m) => c i := by rw [hcIdef, liftConst_val]
      have hcI_mem : cI ∈ interleave C m := (liftConst (m := m) (⟨c, hc⟩ : C)).property
      have hcI_ne : cI ≠ 0 := by
        obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hcne
        rw [Pi.zero_apply] at hi₀
        rw [Function.ne_iff]
        exact ⟨i₀, by rw [Pi.zero_apply, hcIval]; exact fun h => hi₀ (congrFun h ⟨0, hm⟩)⟩
      -- Same normalized weight as `c`: the nonzero-coordinate sets coincide.
      have hset : (Finset.univ.filter fun i => cI i ≠ (0 : Fin n → Fin m → F) i)
          = (Finset.univ.filter fun i => c i ≠ (0 : Fin n → F) i) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hcIval, Pi.zero_apply]
        constructor
        · intro h hci; exact h (by funext _; simp [hci])
        · intro h hc0; exact h (congrFun hc0 ⟨0, hm⟩)
      have hwt : normDist cI (0 : Fin n → Fin m → F) = normDist c (0 : Fin n → F) := by
        unfold normDist hammingDist; rw [hset]
      -- `δmin(C^{≡m}) ≤ normDist cI = normDist c = d`.
      have hbddI : BddBelow {d : ℝ | ∃ cI' ∈ interleave C m, cI' ≠ 0 ∧
          d = (normDist cI' (0 : Fin n → Fin m → F) : ℝ)} :=
        ⟨0, by rintro d ⟨cI', _, _, rfl⟩; exact_mod_cast normDist_nonneg cI' _⟩
      have hle : minDist (interleave C m) ≤ (normDist cI (0 : Fin n → Fin m → F) : ℝ) :=
        csInf_le hbddI ⟨cI, hcI_mem, hcI_ne, rfl⟩
      rwa [hwt] at hle
  · -- No nonzero base codeword ⟹ `C^{≡m}` is also trivial ⟹ both `δmin = 0`.
    have hminC : minDist C = 0 := by
      unfold minDist
      have hempty : {d : ℝ | ∃ c ∈ C, c ≠ 0 ∧ d = (normDist c (0 : Fin n → F) : ℝ)} = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro d ⟨c, hc, hcne, _⟩
        exact hbot ⟨c, hc, hcne⟩
      rw [hempty, Real.sInf_empty]
    -- Every nonzero interleaved codeword would have a nonzero base column.
    have hbotI : ¬ ∃ cI : Fin n → Fin m → F, cI ∈ interleave C m ∧ cI ≠ 0 := by
      rintro ⟨cI, hcI, hcIne⟩
      obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hcIne
      rw [Pi.zero_apply] at hi₀
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hi₀
      rw [Pi.zero_apply] at hj
      exact hbot ⟨fun i => cI i j, mem_interleave.mp hcI j, fun h => hj (congrFun h i₀)⟩
    have hminI : minDist (interleave C m) = 0 := by
      unfold minDist
      have hempty : {d : ℝ | ∃ cI ∈ interleave C m, cI ≠ 0 ∧
          d = (normDist cI (0 : Fin n → Fin m → F) : ℝ)} = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro d ⟨cI, hcI, hcIne, _⟩
        exact hbotI ⟨cI, hcI, hcIne⟩
      rw [hempty, Real.sInf_empty]
    rw [hminC]
    exact le_of_eq hminI

/-- The interleaved Reed–Solomon code has the same minimum distance as the base RS
code: `δmin((RS[F,L,k])^{≡m}) = (n−k+1)/n` (paper Def 2.11, MDS, via `deltaMin`). -/
theorem interleavedRS_minDist (L : Finset F) (k m : ℕ) (hk : 0 < k) (hkn : k ≤ L.card)
    (hm : 0 < m) :
    minDist (interleavedRS L k m) = ((L.card - k + 1 : ℕ) : ℝ) / (L.card : ℝ) := by
  show minDist (interleave (code L k) m) = _
  rw [minDist_interleave_eq (code L k) m hm, deltaMin L k hk hkn]

/-! ### GLD-10 — Johnson baseline for the interleaved RS code

Composing the base-RS Johnson list bound (`mds_list_bound`, Corollary 3.3) with the
`m`-power sandwich (GLD-4): below the Johnson radius `δ ≤ 1−√ρ−η`, the interleaved
list size is `poly(n,1/η)^m`. This validates the formal framework end-to-end — it is
the certified (`LIST_CERTIFIED`) tier for `C^{≡m}`. It is **not** near-capacity: the
bound blows up as `η → 0`, and (Lemma 2.10) interleaving does not move the frontier. -/
theorem interleavedRS_johnson_bound [Fintype F] (L : Finset F) (k : ℕ)
    (hk : 0 < k) (hk2 : 2 ≤ k) (hkn : k ≤ L.card) [Fintype (code L k)]
    (hq : 1 < Fintype.card F) (m : ℕ) [Fintype (interleave (code L k) m)]
    (η : ℝ) (hη : 0 < η) (ρ : ℝ) (hρ : ρ = (k : ℝ) / (L.card : ℝ))
    (δ : ℚ) (hδpos : 0 ≤ δ) (hδ : (δ : ℝ) ≤ 1 - Real.sqrt ρ - η) :
    (maxListSize (interleavedRS L k m) δ : ℝ) ≤ (1 / (2 * η * ρ)) ^ m := by
  have h4 : maxListSize (interleave (code L k) m) δ ≤ (maxListSize (code L k) δ) ^ m :=
    maxListSize_interleave_le_pow (code L k) m δ
  have hbase : (maxListSize (code L k) δ : ℝ) ≤ 1 / (2 * η * ρ) :=
    mds_list_bound L k hk hk2 hkn hq η hη ρ hρ δ hδpos hδ
  calc (maxListSize (interleavedRS L k m) δ : ℝ)
      = (maxListSize (interleave (code L k) m) δ : ℝ) := rfl
    _ ≤ ((maxListSize (code L k) δ : ℝ)) ^ m := by exact_mod_cast h4
    _ ≤ (1 / (2 * η * ρ)) ^ m := pow_le_pow_left₀ (Nat.cast_nonneg _) hbase m

end MCA.ListDecoding
