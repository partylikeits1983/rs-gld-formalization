import Mathlib
import MCA.Code.Hamming
import MCA.Code.Interleaved
import MCA.ReedSolomon.Defs

/-!
# Reed–Solomon codes are MDS

The dimension of `RS[F, L, k]` is `k` (when `k ≤ |L|`), and its minimum distance
meets the Singleton bound: `(|L| - k + 1)/|L|`. (Definition 2.11 / standard.)

Both proofs rest on the fact that two distinct polynomials of degree `< k` agree
on at most `k - 1` points — Mathlib has the polynomial side of this. They are left
as documented `sorry`s here; this file fixes the *statements*.
-/

namespace MCA.ReedSolomon

open MCA.Code

variable {F : Type*} [Field F] [DecidableEq F]

/-- The minimum normalized distance of a linear code: the least normalized weight
of a nonzero codeword. Valued in `ℝ` since `ℚ` lacks a `sInf`.

Polymorphic in the coordinate module `α` so the same definition serves both the
base code (`α = F`, i.e. `LinearCode F n = Submodule F (Fin n → F)`) and the
interleaved code (`α = Fin m → F`, i.e. `interleave C m`). With `α := F` every
existing `LinearCode`-level call site is unchanged. -/
noncomputable def minDist {n : ℕ} {α : Type*} [AddCommGroup α] [Module F α]
    [DecidableEq α] (C : Submodule F (Fin n → α)) : ℝ :=
  sInf { d : ℝ | ∃ c ∈ C, c ≠ 0 ∧ d = (normDist c (0 : Fin n → α) : ℝ) }

/-- The minimum distance is at most the normalized distance of any nonzero codeword. -/
theorem minDist_le_normDist {n : ℕ} (C : LinearCode F n) {c : Fin n → F}
    (hc : c ∈ C) (hne : c ≠ 0) :
    minDist C ≤ (normDist c (0 : Fin n → F) : ℝ) := by
  have hbdd : BddBelow { d : ℝ | ∃ c ∈ C, c ≠ 0 ∧
      d = (normDist c (0 : Fin n → F) : ℝ) } := by
    refine ⟨0, ?_⟩
    rintro d ⟨c, _, _, rfl⟩
    exact_mod_cast normDist_nonneg c (0 : Fin n → F)
  unfold minDist
  exact csInf_le hbdd ⟨c, hc, hne, rfl⟩

/-- A nonzero interleaved codeword has normalized weight at least `minDist C`: its
weight (number of nonzero rows) is at least that of any nonzero column, and every
column is a base codeword. Used to show interleaving cannot decrease the minimum
distance. -/
theorem interleave_minDist_le_normDist {n : ℕ} (C : LinearCode F n) (m : ℕ)
    {cI : Fin n → Fin m → F} (hcI : cI ∈ interleave C m)
    (hne : cI ≠ 0) :
    minDist C ≤ (normDist cI (0 : Fin n → Fin m → F) : ℝ) := by
  classical
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hne
  rw [Pi.zero_apply] at hi₀
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hi₀
  rw [Pi.zero_apply] at hj
  set cj : Fin n → F := fun i => cI i j with hcj
  have hcj_mem : cj ∈ C := mem_interleave.mp hcI j
  have hcj_ne : cj ≠ 0 := by
    rw [Function.ne_iff]
    exact ⟨i₀, by rw [Pi.zero_apply]; exact hj⟩
  have hcol := minDist_le_normDist C hcj_mem hcj_ne
  have hsub : (Finset.univ.filter fun i => cj i ≠ (0 : Fin n → F) i)
      ⊆ (Finset.univ.filter fun i => cI i ≠ (0 : Fin n → Fin m → F) i) := by
    intro i hi
    rw [Finset.mem_filter] at hi ⊢
    refine ⟨hi.1, ?_⟩
    intro hcontra
    apply hi.2
    rw [Pi.zero_apply] at hcontra
    show cI i j = 0
    rw [hcontra, Pi.zero_apply]
  have hham : hammingDist cj (0 : Fin n → F)
      ≤ hammingDist cI (0 : Fin n → Fin m → F) := by
    unfold hammingDist
    exact Finset.card_le_card hsub
  have hQ : normDist cj (0 : Fin n → F)
      ≤ normDist cI (0 : Fin n → Fin m → F) := by
    unfold normDist
    gcongr ?_ / _
    exact_mod_cast hham
  have hRcast : (normDist cj (0 : Fin n → F) : ℝ)
      ≤ (normDist cI (0 : Fin n → Fin m → F) : ℝ) := by
    exact_mod_cast hQ
  exact le_trans hcol hRcast

/-- Interleaving cannot decrease the minimum distance. -/
theorem minDist_interleave_ge {n : ℕ} (C : LinearCode F n) (m : ℕ) (hm : 0 < m) :
    minDist C ≤ minDist (interleave C m) := by
  classical
  by_cases hbot : ∃ c : Fin n → F, c ∈ C ∧ c ≠ 0
  · -- Nonzero base codeword exists ⟹ the interleaved set is nonempty.
    obtain ⟨c, hc, hcne⟩ := hbot
    set cI : Fin n → Fin m → F :=
      ((liftConst (m := m) (⟨c, hc⟩ : C) : interleave C m) : Fin n → Fin m → F) with hcIdef
    have hcI_mem : cI ∈ interleave C m := (liftConst (m := m) (⟨c, hc⟩ : C)).property
    have hcI_ne : cI ≠ 0 := by
      obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hcne
      rw [Pi.zero_apply] at hi₀
      rw [Function.ne_iff]
      refine ⟨i₀, ?_⟩
      rw [Pi.zero_apply, hcIdef, liftConst_val]
      simp only
      rw [Function.ne_iff]
      exact ⟨⟨0, hm⟩, hi₀⟩
    unfold minDist
    apply le_csInf
    · exact ⟨(normDist cI (0 : Fin n → Fin m → F) : ℝ), cI, hcI_mem, hcI_ne, rfl⟩
    · rintro d ⟨cI', hcI', hcI'_ne, rfl⟩
      exact interleave_minDist_le_normDist C m hcI' hcI'_ne
  · -- No nonzero base codeword ⟹ minDist C = 0.
    -- `hbot : ¬ ∃ c, c ∈ C ∧ c ≠ 0`
    have hminC : minDist C = 0 := by
      unfold minDist
      have hempty : { d : ℝ | ∃ c ∈ C, c ≠ 0 ∧
          d = (normDist c (0 : Fin n → F) : ℝ) } = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro d ⟨c, hc, hcne, _⟩
        exact hbot ⟨c, hc, hcne⟩
      rw [hempty, Real.sInf_empty]
    rw [hminC]
    unfold minDist
    apply Real.sInf_nonneg
    rintro d ⟨cI, _, _, rfl⟩
    exact_mod_cast normDist_nonneg cI (0 : Fin n → Fin m → F)

/-- Unique decoding below half the minimum distance: a word `g` has at most one
codeword within normalized distance `δ < minDist/2`. -/
theorem unique_codeword_below_half_minDist {n : ℕ} (C : LinearCode F n)
    (g : Fin n → F) {δ : ℚ} (hδ : (δ : ℝ) < minDist C / 2)
    {c₁ c₂ : Fin n → F} (h1 : c₁ ∈ C) (h2 : c₂ ∈ C)
    (hd1 : normDist g c₁ ≤ δ) (hd2 : normDist g c₂ ≤ δ) :
    c₁ = c₂ := by
  by_contra hne
  have hsub_mem : c₁ - c₂ ∈ C := C.sub_mem h1 h2
  have hsub_ne : c₁ - c₂ ≠ 0 := sub_ne_zero.mpr hne
  -- Triangle bound in ℚ, then translate to weight of the difference.
  have htri : normDist c₁ c₂ ≤ normDist c₁ g + normDist g c₂ :=
    normDist_triangle c₁ g c₂
  rw [normDist_comm c₁ g] at htri
  have hQ : normDist (c₁ - c₂) (0 : Fin n → F) ≤ 2 * δ := by
    rw [← normDist_sub_left c₁ c₂]
    linarith
  -- minDist lower bound (ℝ).
  have hlb : minDist C ≤ (normDist (c₁ - c₂) (0 : Fin n → F) : ℝ) :=
    minDist_le_normDist C hsub_mem hsub_ne
  -- Cast the ℚ inequality to ℝ.
  have hR : (normDist (c₁ - c₂) (0 : Fin n → F) : ℝ) ≤ 2 * (δ : ℝ) := by
    exact_mod_cast hQ
  linarith

omit [Field F] [DecidableEq F] in
/-- The evaluation points of `L` are distinct (the indexing map is injective). -/
theorem evalPoints_injective (L : Finset F) : Function.Injective (evalPoints L) := by
  intro i j h
  apply L.equivFin.symm.injective
  exact Subtype.ext h

omit [DecidableEq F] in
open Polynomial in
/-- `evalMap L` evaluated at `p` is the tuple of point-evaluations of `p`. -/
theorem evalMap_apply (L : Finset F) (p : F[X]) (i : Fin L.card) :
    evalMap L p i = p.eval (evalPoints L i) := rfl

omit [DecidableEq F] in
/-- The bundled multi-point evaluation is injective on degree-`< k` polynomials,
provided `k ≤ |L|`: a nonzero polynomial of degree `< k` has fewer than `k ≤ |L|`
roots, but it would vanish at all `|L|` distinct evaluation points. -/
theorem evalMap_injOn_degreeLT (L : Finset F) (k : ℕ) (hkn : k ≤ L.card) :
    Function.Injective ((evalMap L).domRestrict (Polynomial.degreeLT F k)) := by
  rw [← LinearMap.ker_eq_bot]
  rw [Submodule.eq_bot_iff]
  rintro ⟨p, hp⟩ hker
  rw [LinearMap.mem_ker] at hker
  rcases eq_or_ne p 0 with rfl | hpne
  · exact Subtype.ext rfl
  have hp0 : p = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p
      (evalPoints_injective L)
    · intro i
      have := congrArg (fun (v : Fin L.card → F) => v i) hker
      simpa [LinearMap.domRestrict_apply, evalMap_apply] using this
    · rw [Polynomial.mem_degreeLT] at hp
      rw [Fintype.card_fin]
      have hlt : p.natDegree < k := by
        rw [Polynomial.natDegree_lt_iff_degree_lt hpne]; exact hp
      omega
  exact Subtype.ext hp0

/-- The Reed–Solomon code has dimension `k` over `F` (when `k ≤ |L|`). -/
theorem code_dim_eq_k (L : Finset F) (k : ℕ) (hkn : k ≤ L.card) :
    Module.finrank F (code L k) = k := by
  have hcode : code L k = LinearMap.range
      ((evalMap L).domRestrict (Polynomial.degreeLT F k)) := by
    rw [code, LinearMap.range_domRestrict]
  rw [hcode, LinearMap.finrank_range_of_inj (evalMap_injOn_degreeLT L k hkn)]
  rw [(Polynomial.degreeLTEquiv F k).finrank_eq,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

/-- **Lower bound (root count).** A degree-`< k` polynomial `p` whose evaluation
vector `evalMap L p` is nonzero has Hamming weight at least `|L| - k + 1`: it can
vanish at at most `k - 1` of the `|L|` distinct evaluation points (a nonzero
poly of degree `< k` has `≤ k-1` roots, `poly_identity` /
`Polynomial.card_le_degree_of_subset_roots`), so it is nonzero on at least
`|L| - (k-1) = |L| - k + 1` of them.

Stated at the ℕ (Hamming-count) level to keep the leaf small; the ℚ/ℝ cast and
`Nat.sub` arithmetic are deferred to the `deltaMin` composition. Strictly smaller
than `deltaMin`: no `sInf`, no `le_antisymm`, a single `≥` over a fixed `p`. -/
theorem rs_weight_lower_bound (L : Finset F) (k : ℕ) (hkn : k ≤ L.card)
    (p : Polynomial F) (hp : p ∈ Polynomial.degreeLT F k) (hpne : evalMap L p ≠ 0) :
    L.card - k + 1 ≤ hammingDist (evalMap L p) (0 : Fin L.card → F) := by
  classical
  -- `p ≠ 0`: otherwise its evaluation vector would be `0`.
  have hpne0 : p ≠ 0 := by
    rintro rfl
    exact hpne (by simp)
  -- `p.natDegree < k`.
  rw [Polynomial.mem_degreeLT] at hp
  have hdeg : p.natDegree < k := by
    rw [Polynomial.natDegree_lt_iff_degree_lt hpne0]; exact hp
  -- The set of evaluation indices at which `p` vanishes.
  set Z : Finset (Fin L.card) :=
    Finset.univ.filter (fun i => p.eval (evalPoints L i) = 0) with hZ
  -- Its image under the injective `evalPoints` lies in `p.roots`.
  have himg : (Z.image (evalPoints L)).val ⊆ p.roots := by
    intro x hx
    rw [Finset.mem_val, Finset.mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [hZ, Finset.mem_filter] at hi
    rw [Polynomial.mem_roots hpne0]
    exact hi.2
  -- Hence `Z.card ≤ p.natDegree`.
  have hZcard : Z.card ≤ p.natDegree := by
    have h1 : (Z.image (evalPoints L)).card ≤ p.natDegree :=
      Polynomial.card_le_degree_of_subset_roots himg
    rwa [Finset.card_image_of_injective Z (evalPoints_injective L)] at h1
  -- The Hamming distance equals the number of nonzero coordinates,
  -- i.e. `L.card - Z.card`.
  have hham : hammingDist (evalMap L p) (0 : Fin L.card → F) = L.card - Z.card := by
    unfold hammingDist
    have heq : (Finset.univ.filter
        (fun i => evalMap L p i ≠ (0 : Fin L.card → F) i))
        = Finset.univ \ Z := by
      rw [hZ]
      ext i
      simp [evalMap_apply]
    rw [heq, Finset.card_sdiff_of_subset (Finset.subset_univ Z), Finset.card_univ,
      Fintype.card_fin]
  rw [hham]
  omega

/-- **Achievability.** There is a nonzero codeword of Hamming weight exactly
`|L| - k + 1`. Witness: take any `k - 1` of the distinct evaluation points (there
are at least `k - 1 ≤ |L|` of them by `hkn`) and form `∏ (X - C pt)`. This has
degree `k - 1 < k` (so lies in `degreeLT F k` and is a codeword), is nonzero
(product of monic linear factors), and vanishes at exactly those `k - 1` points,
hence its evaluation vector has weight `|L| - (k-1) = |L| - k + 1`.

Needs `hk : 0 < k` (for `k - 1` to be a genuine smaller index) and `hkn`. Stated
as an existential over codewords with an exact-weight equality; strictly smaller
than `deltaMin`: it constructs one witness rather than reasoning about the whole
`sInf`. -/
theorem rs_exists_min_weight (L : Finset F) (k : ℕ) (hk : 0 < k) (hkn : k ≤ L.card) :
    ∃ c ∈ code L k, c ≠ 0 ∧
      hammingDist c (0 : Fin L.card → F) = L.card - k + 1 := by
  classical
  -- Step 1: pick `k - 1` evaluation indices.
  have hk1 : k - 1 ≤ (Finset.univ : Finset (Fin L.card)).card := by
    rw [Finset.card_univ, Fintype.card_fin]; omega
  obtain ⟨S, _hSsub, hScard⟩ := Finset.exists_subset_card_eq hk1
  -- Step 2: the polynomial `p = ∏ i∈S (X - C (evalPoints L i))`.
  set p : Polynomial F :=
    ∏ i ∈ S, ((Polynomial.X : Polynomial F) - Polynomial.C (evalPoints L i)) with hp
  -- `p` is monic, hence nonzero.
  have hpmonic : p.Monic := by
    rw [hp]
    exact Polynomial.monic_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C _)
  have hpne0 : p ≠ 0 := hpmonic.ne_zero
  -- `degree p = k - 1`.
  have hpdeg : p.degree = ((k - 1 : ℕ) : WithBot ℕ) := by
    rw [hp, Polynomial.degree_prod]
    have : ∀ i ∈ S, (Polynomial.X - Polynomial.C (evalPoints L i)).degree = (1 : WithBot ℕ) :=
      fun i _ => Polynomial.degree_X_sub_C _
    rw [Finset.sum_congr rfl this]
    simp [hScard]
  -- `p ∈ degreeLT F k`.
  have hpmem : p ∈ Polynomial.degreeLT F k := by
    rw [Polynomial.mem_degreeLT, hpdeg]
    have : (k - 1 : ℕ) < k := by omega
    exact_mod_cast this
  -- Step 3: the codeword.
  refine ⟨evalMap L p, Submodule.mem_map_of_mem hpmem, ?_, ?_⟩
  · -- Step 6: nonzero. `S ≠ univ` since `S.card = k - 1 < L.card`.
    have hSne : S ≠ Finset.univ := by
      intro h
      have : S.card = (Finset.univ : Finset (Fin L.card)).card := by rw [h]
      rw [Finset.card_univ, Fintype.card_fin, hScard] at this
      omega
    obtain ⟨i, _, hiS⟩ := Finset.exists_of_ssubset
      (Finset.ssubset_univ_iff.mpr hSne)
    rw [Function.ne_iff]
    refine ⟨i, ?_⟩
    -- `evalMap L p i = ∏ j∈S (evalPoints L i - evalPoints L j) ≠ 0`.
    rw [evalMap_apply, hp, Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Pi.zero_apply]
    rw [Finset.prod_ne_zero_iff]
    intro j hj
    rw [sub_ne_zero]
    intro heq
    exact hiS ((evalPoints_injective L heq) ▸ hj)
  · -- Step 7: weight.
    -- The zero set of the codeword equals `S`.
    have hzero : (Finset.univ.filter (fun i => evalMap L p i = 0)) = S := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [evalMap_apply, hp, Polynomial.eval_prod]
      simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      rw [Finset.prod_eq_zero_iff]
      constructor
      · rintro ⟨j, hj, hij⟩
        rw [sub_eq_zero] at hij
        exact (evalPoints_injective L hij) ▸ hj
      · intro hi
        exact ⟨i, hi, by rw [sub_eq_zero]⟩
    unfold hammingDist
    have heq : (Finset.univ.filter
        (fun i => evalMap L p i ≠ (0 : Fin L.card → F) i))
        = Finset.univ \ S := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
        Pi.zero_apply]
      rw [← hzero]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [heq, Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ,
      Fintype.card_fin, hScard]
    omega

/-- Reed–Solomon is MDS: minimum distance `(|L| - k + 1)/|L|`.

Composition (non-leaf): `le_antisymm` on the `sInf` defining `minDist`.
- `≤`: `csInf_le` using the witness from `rs_exists_min_weight` (its normalized
  weight is in the set) and `BddBelow` by `0` via `normDist_nonneg`.
- `≥`: `le_csInf` using nonemptiness from `rs_exists_min_weight` and the per-element
  bound from `rs_weight_lower_bound`, then the `normDist` definition
  (`= hammingDist / |L|`), a ℚ→ℝ cast, and `Nat.sub` arithmetic (`omega`). -/
theorem deltaMin (L : Finset F) (k : ℕ) (hk : 0 < k) (hkn : k ≤ L.card) :
    minDist (code L k) = ((L.card - k + 1 : ℕ) : ℝ) / (L.card : ℝ) := by
  classical
  set R : ℝ := ((L.card - k + 1 : ℕ) : ℝ) / (L.card : ℝ) with hR
  -- `0 < L.card`.
  have hLpos : (0 : ℝ) < (L.card : ℝ) := by
    have : 0 < L.card := lt_of_lt_of_le hk hkn
    exact_mod_cast this
  -- Bridge: `(normDist c 0 : ℝ) = (hammingDist c 0 : ℝ) / L.card`.
  have bridge : ∀ c : Fin L.card → F,
      ((normDist c (0 : Fin L.card → F) : ℝ)) =
        (hammingDist c (0 : Fin L.card → F) : ℝ) / (L.card : ℝ) := by
    intro c
    simp only [normDist, Rat.cast_div, Rat.cast_natCast]
  -- The witness from `rs_exists_min_weight`.
  obtain ⟨cw, hcw_mem, hcw_ne, hcw_w⟩ := rs_exists_min_weight L k hk hkn
  -- `R ∈ S` (the set defining `minDist`).
  have hRmem : ∃ c ∈ code L k, c ≠ 0 ∧
      R = (normDist c (0 : Fin L.card → F) : ℝ) := by
    refine ⟨cw, hcw_mem, hcw_ne, ?_⟩
    rw [bridge cw, hcw_w, hR]
  -- `BddBelow` the set.
  have hbdd : BddBelow { d : ℝ | ∃ c ∈ code L k, c ≠ 0 ∧
      d = (normDist c (0 : Fin L.card → F) : ℝ) } := by
    refine ⟨0, ?_⟩
    rintro d ⟨c, _, _, rfl⟩
    exact_mod_cast normDist_nonneg c (0 : Fin L.card → F)
  unfold minDist
  apply le_antisymm
  · -- `sInf S ≤ R`.
    apply csInf_le hbdd
    exact hRmem
  · -- `R ≤ sInf S`.
    apply le_csInf
    · exact ⟨R, hRmem⟩
    · rintro d ⟨c, hc_mem, hc_ne, rfl⟩
      -- unpack `c = evalMap L p`, `p ∈ degreeLT F k`.
      rw [code, Submodule.mem_map] at hc_mem
      obtain ⟨p, hp, hpc⟩ := hc_mem
      subst hpc
      have hpne : evalMap L p ≠ 0 := hc_ne
      have hlb := rs_weight_lower_bound L k hkn p hp hpne
      -- cast the ℕ inequality and divide.
      rw [bridge (evalMap L p), hR]
      have hnum : ((L.card - k + 1 : ℕ) : ℝ) ≤ (hammingDist (evalMap L p) (0 : Fin L.card → F) : ℝ) := by
        exact_mod_cast hlb
      gcongr

end MCA.ReedSolomon
