import Mathlib
import MCA.Code.Hamming
import MCA.Code.Defs
import MCA.Code.ListDecode
import MCA.Code.Johnson
import MCA.Code.JohnsonGeometric
import MCA.Code.JohnsonEmbed
import MCA.ReedSolomon.MDS

/-!
# The Johnson bound (Theorem 3.2) and the MDS corollary (Corollary 3.3)

These are *classical* theorems (Johnson 1962), so they are real proof
obligations and live in `MCA/` (NOT `Conjectures/`). This file fixes their
statements over our `listAt` / `maxListSize` / `minDist` API and lays out the
decomposition of Theorem 3.2 along the cleanest q-ary route.

## The route (GRS Essential Coding Theory, Exercises 7.6–7.8, Lemma 4.4.3.2 +
   Lemma 4.4.4)

The proof is the *double-counting / inner-product* argument, NOT the harder
linear-independence argument. The geometric core is the easy "sum of squares is
nonnegative" half of the Geometric Lemma (Lemma 4.4.3 part 2):

  if `v₁,…,v_M ∈ ℝ^N` satisfy `‖vᵢ‖² ≤ U` and `⟨vᵢ,vⱼ⟩ ≤ −ε < 0` for `i ≠ j`,
  then from `0 ≤ ‖Σvᵢ‖² = Σ‖vᵢ‖² + 2·Σ_{i<j}⟨vᵢ,vⱼ⟩ ≤ M·U − M(M−1)·ε`
  we get `M ≤ 1 + U/ε`.

The codewords are mapped into `ℝ^N` (`N = n·q`) by the *simplex embedding* of
Lemma 4.4.4 (`φ(i) = eᵢ − e`, scaled), giving unit vectors whose pairwise inner
product is `1 − (q/(q−1))·Δ(c₁,c₂)`. Shifting the origin to a `(y, α)`-determined
point and tuning `α` makes the self and cross bounds yield `1 + U/ε = ℓ`, exactly
the `Jq,ℓ` radius.

Leaves (declared below as `sorry` stubs; see `lemma_graph.md` §P2):
  L1 `geom_lemma_sum_sq`        — the sum-of-squares list bound `M ≤ 1 + U/ε`
                                   (pure inner-product space; the geometric core).
  L2 `simplex_embed`            — Lemma 4.4.4: the embedding + inner-product formula.
  L3 `johnson_inner_bounds`     — algebra tuning `α`: self/cross inner-product
                                   bounds at radius `Jq,ℓ(δmin)`, yielding `U, ε`
                                   with `1 + U/ε = ℓ`.
  ── (compose) ──
  `johnson_bound`               — Theorem 3.2.
  `mds_list_bound`              — Corollary 3.3 (from `johnson_bound` + MDS δmin).
-/

namespace MCA.Code

open scoped InnerProductSpace
open MCA.ReedSolomon (minDist)

variable {F : Type*} [Field F] {α : Type*} [AddCommGroup α] [Module F α]
  [DecidableEq α] [Fintype α] {n : ℕ}

/-- `johnsonJqℓ q ℓ` is monotone increasing in its distance argument, when
`1 < q` and `1 < ℓ`. As `d` increases, the sqrt argument decreases, so the sqrt
decreases, so `1 − √(…)` increases; the leading coefficient `1 − 1/q ≥ 0`. -/
private theorem johnsonJqℓ_mono {q ℓ : ℕ} (hq : 1 < q) (hℓ : 1 < ℓ)
    {d₁ d₂ : ℝ} (hd : d₁ ≤ d₂) :
    johnsonJqℓ q ℓ d₁ ≤ johnsonJqℓ q ℓ d₂ := by
  unfold johnsonJqℓ
  have hqR : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hcoef_nn : (0 : ℝ) ≤ 1 - 1 / (q : ℝ) := by
    have : 1 / (q : ℝ) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    linarith
  -- the factor C := (q/(q-1))·((ℓ-1)/ℓ) ≥ 0
  have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  have hℓR : (1 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
  have hCnn : (0 : ℝ) ≤ (q : ℝ) / ((q : ℝ) - 1) * (((ℓ : ℝ) - 1) / (ℓ : ℝ)) := by
    apply mul_nonneg
    · positivity
    · apply div_nonneg <;> linarith
  -- sqrt argument: arg₂ ≤ arg₁
  have harg : 1 - (q : ℝ) / ((q : ℝ) - 1) * (((ℓ : ℝ) - 1) / (ℓ : ℝ)) * d₂
      ≤ 1 - (q : ℝ) / ((q : ℝ) - 1) * (((ℓ : ℝ) - 1) / (ℓ : ℝ)) * d₁ := by
    have := mul_le_mul_of_nonneg_left hd hCnn
    nlinarith [this]
  have hsqrt : Real.sqrt (1 - (q : ℝ) / ((q : ℝ) - 1) * (((ℓ : ℝ) - 1) / (ℓ : ℝ)) * d₂)
      ≤ Real.sqrt (1 - (q : ℝ) / ((q : ℝ) - 1) * (((ℓ : ℝ) - 1) / (ℓ : ℝ)) * d₁) :=
    Real.sqrt_le_sqrt harg
  apply mul_le_mul_of_nonneg_left _ hcoef_nn
  linarith [hsqrt]

/-! ## Theorem 3.2 — the Johnson bound (TARGET of the P2 decomposition) -/

/-- **Theorem 3.2 ([Joh62]).** For any code `C ⊆ Σⁿ` with `|Σ| = q`, the list of
codewords within normalized distance `Jq,ℓ(δmin(C))` of any received word has size
at most `ℓ`.

We state it over `maxListSize` (the max over all `f`), which is the cleanest
phrasing; the per-`f` form `(listAt C δ f).card ≤ ℓ` is an immediate consequence.

`q := Fintype.card α`. We require `1 < q` (a genuine alphabet) and `1 < ℓ`
(`Jq,ℓ` has the `(ℓ−1)/ℓ` factor; `ℓ > 1` keeps the geometric ε positive). The radius is the
*rational* `δ`-cast of the real `johnsonJqℓ`; we phrase it via `δ ≤ johnsonJqℓ …`
to keep `maxListSize`'s `ℚ` radius and the real Johnson function compatible. -/
theorem johnson_bound (C : Submodule F (Fin n → α)) [Fintype C]
    (ℓ : ℕ) (hℓ : 1 < ℓ) (hq : 1 < Fintype.card α)
    (δ : ℚ) (hδpos : 0 ≤ δ)
    (hδ : (δ : ℝ) ≤ johnsonJqℓ (Fintype.card α) ℓ (minDist C)) :
    maxListSize C δ ≤ ℓ := by
  classical
  -- Step 1: reduce maxListSize ≤ ℓ to a per-`f` bound.
  unfold maxListSize
  apply Finset.sup_le
  intro f _
  -- Fix `f`; let `L` be its list, `M := L.card`.
  set L : Finset C := listAt C δ f with hLdef
  set M : ℕ := L.card with hMdef
  -- Step 2: case-split on M < 2 vs M ≥ 2.
  rcases Nat.lt_or_ge M 2 with hM1 | hM2
  · have : M ≤ 1 := by omega
    exact le_trans this (le_of_lt hℓ)
  -- M ≥ 2.  We need 0 < n: if n = 0 all vectors are equal so L ≤ 1.
  have hn : 0 < n := by
    by_contra h
    push_neg at h
    have hn0 : n = 0 := by omega
    -- n = 0: every `Fin 0 → α` is the same, so any two codewords are equal,
    -- so L has at most one element, contradicting M ≥ 2.
    have hsub : L.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a _ b _
      apply Subtype.ext
      funext i
      exact absurd i.isLt (by omega)
    omega
  -- Index L by `Fin M` via the canonical equiv.
  set e : L ≃ Fin M := L.equivFin with hedef
  -- The codeword family.
  set c : Fin M → (Fin n → α) := fun i => ((e.symm i : C) : Fin n → α) with hcdef
  -- (b) each c i is within δ of f.
  have hclose : ∀ i, normDist f (c i) ≤ δ := by
    intro i
    have hmem : (e.symm i : C) ∈ L := (e.symm i).2
    have hmem' : (e.symm i : C) ∈ listAt C δ f := hmem
    exact (mem_listAt.mp hmem')
  -- distinctness of indices: i ≠ j ⟹ c i ≠ c j (as vectors).
  have hcdistinct : ∀ i j : Fin M, i ≠ j → c i ≠ c j := by
    intro i j hij
    simp only [hcdef]
    intro heq
    -- the two subtype elements are equal, contradicting e.symm injective.
    have hC : (e.symm i : C) = (e.symm j : C) := Subtype.ext heq
    have hL : e.symm i = e.symm j := Subtype.ext hC
    exact hij (e.symm.injective hL)
  -- (c) pairwise minDist-far.  First, define dmin as the min pairwise normDist.
  -- The pairs index: off-diagonal of Fin M × Fin M, nonempty since M ≥ 2.
  set offdiag : Finset (Fin M × Fin M) :=
    Finset.univ.filter (fun p : Fin M × Fin M => p.1 ≠ p.2) with hoffdef
  have hoff_nonempty : offdiag.Nonempty := by
    -- M ≥ 2 ⟹ ∃ two distinct indices.
    have h2 : 2 ≤ M := hM2
    have : (⟨0, by omega⟩ : Fin M) ≠ ⟨1, by omega⟩ := by
      simp [Fin.ext_iff]
    exact ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp [hoffdef, this]⟩
  -- dmin := minimum of normDist (c p.1) (c p.2) over off-diagonal pairs.
  set dmin : ℚ := offdiag.inf' hoff_nonempty
    (fun p => normDist (c p.1) (c p.2)) with hdmindef
  -- dmin ≤ each pairwise distance.
  have hmem_off : ∀ i j : Fin M, i ≠ j → (i, j) ∈ offdiag := by
    intro i j hij
    rw [hoffdef, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hij⟩
  have hdmin_le : ∀ i j, i ≠ j → dmin ≤ normDist (c i) (c j) := by
    intro i j hij
    exact Finset.inf'_le _ (hmem_off i j hij)
  -- 0 < dmin: distinct codewords are at positive distance.
  have hdmin_pos : 0 < dmin := by
    rw [hdmindef, Finset.lt_inf'_iff]
    intro p hp
    rw [hoffdef, Finset.mem_filter] at hp
    have hne : c p.1 ≠ c p.2 := hcdistinct p.1 p.2 hp.2
    rcases lt_or_eq_of_le (normDist_nonneg (c p.1) (c p.2)) with hlt | heq0
    · exact hlt
    · exfalso; apply hne
      exact (normDist_eq_zero_iff hn (c p.1) (c p.2)).mp heq0.symm
  -- minDist C ≤ dmin : each pairwise normDist ≥ minDist C, so their min does too.
  have hbdd : BddBelow { d : ℝ | ∃ x ∈ C, x ≠ 0 ∧
      d = (normDist x (0 : Fin n → α) : ℝ) } := by
    refine ⟨0, ?_⟩
    rintro d ⟨x, _, _, rfl⟩
    exact_mod_cast normDist_nonneg x (0 : Fin n → α)
  have hminDist_le_pair : ∀ i j, i ≠ j →
      minDist C ≤ (normDist (c i) (c j) : ℝ) := by
    intro i j hij
    -- c i - c j ∈ C, nonzero.
    set ci : C := (e.symm i : C) with hcidef
    set cj : C := (e.symm j : C) with hcjdef
    have hsub_mem : ((ci : Fin n → α) - (cj : Fin n → α)) ∈ C :=
      C.sub_mem ci.2 cj.2
    have hsub_ne : ((ci : Fin n → α) - (cj : Fin n → α)) ≠ 0 := by
      intro h
      apply hcdistinct i j hij
      simp only [hcdef]
      have : (ci : Fin n → α) = (cj : Fin n → α) := by
        rw [sub_eq_zero] at h; exact h
      exact this
    -- minDist C ≤ normDist (ci - cj) 0 by csInf_le.
    have hle : minDist C ≤ (normDist ((ci : Fin n → α) - (cj : Fin n → α))
        (0 : Fin n → α) : ℝ) := by
      unfold minDist
      apply csInf_le hbdd
      exact ⟨(ci : Fin n → α) - (cj : Fin n → α), hsub_mem, hsub_ne, rfl⟩
    -- normDist (ci - cj) 0 = normDist (c i) (c j).
    have heq : normDist ((ci : Fin n → α) - (cj : Fin n → α)) (0 : Fin n → α)
        = normDist (c i) (c j) := by
      rw [← normDist_sub_left]
    rw [heq] at hle
    exact hle
  have hminDist_le_dmin : minDist C ≤ (dmin : ℝ) := by
    -- dmin is attained at some off-diagonal pair p₀; at p₀, minDist ≤ that distance.
    obtain ⟨p₀, hp₀mem, hp₀eq⟩ := Finset.exists_mem_eq_inf' hoff_nonempty
      (fun p => normDist (c p.1) (c p.2))
    rw [hoffdef, Finset.mem_filter] at hp₀mem
    have hdmin_eq : dmin = normDist (c p₀.1) (c p₀.2) := by rw [hdmindef]; exact hp₀eq
    rw [hdmin_eq]
    exact hminDist_le_pair p₀.1 p₀.2 hp₀mem.2
  -- Step 6: radius bridge.  δ ≤ Jq,ℓ(minDist) ≤ Jq,ℓ(dmin).
  have hradius_real : (δ : ℝ) ≤ johnsonJqℓ (Fintype.card α) ℓ (dmin : ℝ) :=
    le_trans hδ (johnsonJqℓ_mono hq hℓ hminDist_le_dmin)
  -- unfold johnsonJqℓ to match johnson_inner_bounds' hradius shape.
  have hradius : (δ : ℝ) ≤
      (1 - 1 / (Fintype.card α : ℝ)) *
        (1 - Real.sqrt (1 - (Fintype.card α : ℝ) / ((Fintype.card α : ℝ) - 1)
          * (((ℓ : ℝ) - 1) / (ℓ : ℝ)) * (dmin : ℝ))) := by
    have h := hradius_real
    unfold johnsonJqℓ at h
    exact h
  -- Step 7: invoke the embedding + bounds + geometric core.
  obtain ⟨emb, hnorm, hinner⟩ := simplex_embed hn hq
  -- pairwise-far in the form johnson_inner_bounds wants.
  have hfar : ∀ i j, i ≠ j → dmin ≤ normDist (c i) (c j) := hdmin_le
  obtain ⟨v, U, ε, hε, hUε, hvbound, hcross⟩ :=
    johnson_inner_bounds emb hq hinner hnorm ℓ hℓ dmin δ hdmin_pos hδpos
      f c hfar hclose hradius
  -- 0 ≤ U.  From the bound: ‖v i‖² ≤ U and ‖v i‖² ≥ 0 (M ≥ 2 ⟹ ∃ i).
  have hUnn : 0 ≤ U := by
    have hnn : (0 : ℝ) ≤ ‖v ⟨0, by omega⟩‖ ^ 2 := sq_nonneg _
    exact le_trans hnn (hvbound ⟨0, by omega⟩)
  -- geom_lemma_sum_sq: |Fin M| ≤ 1 + U/ε = ℓ.
  have hgeom : (Fintype.card (Fin M) : ℝ) ≤ 1 + U / ε :=
    geom_lemma_sum_sq v U ε hε hUnn hvbound hcross
  rw [Fintype.card_fin] at hgeom
  rw [hUε] at hgeom
  -- M ≤ ℓ (ℕ).
  exact_mod_cast hgeom

/-! ## Corollary 3.3 — the MDS list-decoding bound

The two genuine real-analysis sub-lemmas of `mds_list_bound` (declared as `sorry`
leaves below). The composition chain is

  `1 − √ρ − η ≤[A] johnsonJq q (1−ρ) − η ≤[B] johnsonJqℓ q ℓ (1−ρ)`
              `≤[johnsonJqℓ_mono] johnsonJqℓ q ℓ δmin`,

then `johnson_bound` gives `maxListSize ≤ ℓ ≤ 1/(2ηρ)`. See `lemma_graph.md` §P2.

Recall the ordering of the three Johnson functions at a fixed `δ` (this is the
crux that makes the chain go the right way):

  `johnsonJqℓ q ℓ δ ≤ johnsonJq q δ`   (ℓ → ∞ is the LARGER radius), and
  `J δ = 1 − √(1−δ) ≤ johnsonJq q δ`   (finite alphabet HELPS list-decoding).

So the only slack that must be paid for with `η` is the *ℓ-gap* `johnsonJq −
johnsonJqℓ` (Sub-lemma B); the q-direction `J ≤ johnsonJq` is free (Sub-lemma A,
no `η`). -/

/-- **Sub-lemma A (q-direction, no slack).** The field-size-aware Johnson radius
`johnsonJq q (1−ρ)` is at least the field-free Johnson radius `J(1−ρ) = 1 − √ρ`.

This is the statement `(1−1/q)·(1 − √(1 − (q/(q−1))·(1−ρ))) ≥ 1 − √ρ`, true for
every `q ≥ 2` and every `ρ ∈ [0,1]` with `(q/(q−1))·(1−ρ) ≤ 1` (`harg`; this is
exactly `qρ ≥ 1`, supplied at the RS call site by `|L| ≤ |F|`).

Pure `Real.sqrt` algebra: `Real.sqrt_le_sqrt`, `Real.sq_sqrt`, `Real.le_sqrt`,
one `nlinarith`. No code, no slack. -/
private theorem johnsonJq_ge_one_sub_sqrt {q : ℕ} (hq : 1 < q) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (harg : (q : ℝ) / ((q : ℝ) - 1) * (1 - ρ) ≤ 1) :
    1 - Real.sqrt ρ ≤ johnsonJq q (1 - ρ) := by
  -- Basic positivity facts about q.
  have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < (q : ℝ) := lt_trans one_pos hq1
  have hqm1 : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  -- Abbreviations.
  set c : ℝ := 1 - 1 / (q : ℝ) with hc
  set β : ℝ := (q : ℝ) / ((q : ℝ) - 1) with hβ
  -- c·β = 1.
  have hcβ : c * β = 1 := by
    rw [hc, hβ]
    field_simp
  -- 0 < c < 1.
  have hc0 : 0 < c := by
    rw [hc]
    have : 1 / (q : ℝ) < 1 := by
      rw [div_lt_one hq0]; exact hq1
    linarith
  have hc1 : c ≤ 1 := by
    rw [hc]
    have h01 : 0 < 1 / (q:ℝ) := by positivity
    linarith
  -- harg gives ρ ≥ 1/q.
  have hβpos : 0 < β := by rw [hβ]; positivity
  -- From harg: β(1-ρ) ≤ 1, i.e. 1-ρ ≤ 1/β = c (since cβ=1), i.e. ρ ≥ 1-c = 1/q.
  have hρ_ge : (1 : ℝ) / q ≤ ρ := by
    -- harg : β * (1 - ρ) ≤ 1
    have h1 : β * (1 - ρ) ≤ 1 := harg
    -- multiply by c > 0 : c·β·(1-ρ) ≤ c, i.e. (1-ρ) ≤ c
    have h2 : c * (β * (1 - ρ)) ≤ c * 1 := by
      apply mul_le_mul_of_nonneg_left h1 (le_of_lt hc0)
    rw [← mul_assoc, hcβ, one_mul, mul_one] at h2
    -- h2 : 1 - ρ ≤ c = 1 - 1/q
    rw [hc] at h2
    linarith
  -- The sqrt argument of johnsonJq.
  set A : ℝ := 1 - β * (1 - ρ) with hA
  have hApos : 0 ≤ A := by rw [hA]; linarith [harg]
  -- Let sρ = √ρ, sA = √A.
  set sρ : ℝ := Real.sqrt ρ with hsρ
  set sA : ℝ := Real.sqrt A with hsA
  have hsρ0 : 0 ≤ sρ := Real.sqrt_nonneg ρ
  have hsA0 : 0 ≤ sA := Real.sqrt_nonneg A
  have hsρ_sq : sρ ^ 2 = ρ := by rw [hsρ, Real.sq_sqrt hρ0]
  have hsA_sq : sA ^ 2 = A := by rw [hsA, Real.sq_sqrt hApos]
  have hsρ1 : sρ ≤ 1 := by
    rw [hsρ]
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hρ1
  -- sρ ≥ 1/q : since ρ ≥ 1/q and 1/q ≤ 1, √ρ ≥ √(1/q) ≥ 1/q.
  have hsρ_ge : (1 : ℝ) / q ≤ sρ := by
    have hqinv1 : (1 : ℝ) / q ≤ 1 := by rw [div_le_one hq0]; linarith
    have hstep1 : Real.sqrt (1 / q) ≤ sρ := by
      rw [hsρ]; exact Real.sqrt_le_sqrt hρ_ge
    have hstep2 : (1 : ℝ) / q ≤ Real.sqrt (1 / q) := by
      have hnn : (0:ℝ) ≤ 1 / q := by positivity
      -- (1/q)^2 ≤ 1/q  ⟹  1/q ≤ √(1/q)
      have hsq : (1 / (q:ℝ)) ^ 2 ≤ 1 / q := by nlinarith [hqinv1, hnn]
      calc (1 : ℝ) / q = Real.sqrt ((1/q)^2) := by rw [Real.sqrt_sq hnn]
        _ ≤ Real.sqrt (1/q) := Real.sqrt_le_sqrt hsq
    linarith
  -- Now: c·sA ≤ sρ − 1/q. RHS ≥ 0. Square-compare.
  -- sA² = A = 1 − β(1−ρ) = 1 − β + β·sρ². And c²·β = c. So c²·sA² = c² − c + c·sρ².
  have hsA2_expand : sA ^ 2 = 1 - β + β * sρ ^ 2 := by
    rw [hsA_sq, hA, hsρ_sq]; ring
  have hc2β : c ^ 2 * β = c := by
    have : c ^ 2 * β = c * (c * β) := by ring
    rw [this, hcβ, mul_one]
  -- Target rearranged form: c·sA ≤ sρ − 1/q.
  have hRHS_nn : 0 ≤ sρ - 1 / q := by linarith
  have hkey : c * sA ≤ sρ - 1 / q := by
    -- both sides ≥ 0; compare squares.
    have hLHS_nn : 0 ≤ c * sA := mul_nonneg (le_of_lt hc0) hsA0
    -- (c·sA)² = c²·sA² = c² − c + c·sρ²  (using hc2β)
    have hLHS_sq : (c * sA) ^ 2 = c ^ 2 - c + c * sρ ^ 2 := by
      have : (c * sA) ^ 2 = c ^ 2 * sA ^ 2 := by ring
      rw [this, hsA2_expand]
      have heq : c ^ 2 * (1 - β + β * sρ ^ 2) = c ^ 2 - c ^ 2 * β + c ^ 2 * β * sρ ^ 2 := by ring
      rw [heq, hc2β]
    -- c = 1 - 1/q, so c² - c = -1/q + 1/q². Show (c·sA)² ≤ (sρ-1/q)².
    have hsq_le : (c * sA) ^ 2 ≤ (sρ - 1 / q) ^ 2 := by
      rw [hLHS_sq, hc]
      -- reduces to (sρ-1)² ≥ 0 after clearing /q ; use nlinarith
      have hfield : (1 - 1/(q:ℝ))^2 - (1 - 1/(q:ℝ)) + (1 - 1/(q:ℝ)) * sρ^2
          = sρ^2 - sρ^2/q - 1/q + 1/q^2 := by
        field_simp; ring
      rw [hfield]
      have hRHSsq : (sρ - 1/(q:ℝ))^2 = sρ^2 - 2*sρ/q + 1/q^2 := by
        field_simp; ring
      rw [hRHSsq]
      -- need sρ² − sρ²/q − 1/q + 1/q² ≤ sρ² − 2sρ/q + 1/q²
      -- i.e. −sρ²/q − 1/q ≤ −2sρ/q  ⟺ 2sρ/q ≤ sρ²/q + 1/q ⟺ (sρ−1)² ≥ 0
      have hnum : 2 * sρ ≤ sρ^2 + 1 := by nlinarith [sq_nonneg (sρ - 1)]
      have hkey2 : 2 * sρ / q ≤ (sρ^2 + 1) / q := by gcongr
      have hsplit : (sρ^2 + 1) / q = sρ^2 / q + 1/q := by ring
      rw [hsplit] at hkey2
      linarith
    -- from squares & both nonneg
    nlinarith [hsq_le, hLHS_nn, hRHS_nn]
  -- Final assembly: 1 − sρ ≤ c·(1 − sA) = c − c·sA.
  -- c·(1−sA) = c − c·sA ≥ c − (sρ − 1/q) = c + 1/q − sρ = 1 − sρ  (since c + 1/q = 1).
  have hc_plus : c + 1 / q = 1 := by rw [hc]; ring
  -- johnsonJq q (1-ρ) = c * (1 - sA).
  show 1 - sρ ≤ johnsonJq q (1 - ρ)
  rw [johnsonJq]
  -- goal: 1 - sρ ≤ (1 - 1/q) * (1 - √(1 - (q/(q-1))*(1-ρ)))
  -- the sqrt arg is exactly A; rewrite to c * (1 - sA)
  show 1 - sρ ≤ c * (1 - sA)
  nlinarith [hkey, hc_plus]

/-- **Sub-lemma B (ℓ-slack absorbed by η — the delicate √-difference estimate).**
The ℓ-gap `johnsonJq q d − johnsonJqℓ q ℓ d` is at most `η`, provided the sqrt
argument of `johnsonJq` is positive (`hApos`) and `ℓ` is large enough relative to
`η` and that sqrt (`hcoup`).

The estimate is the one-sided Lipschitz bound for `√`:
`√(A + βd/ℓ) − √A ≤ (βd/ℓ)/(2√A)` (valid when `A > 0`), combined with the exact
cancellation `coef·β = (1−1/q)·(q/(q−1)) = 1`. This gives
`johnsonJq q d − johnsonJqℓ q ℓ d ≤ d/(2ℓ·√A)`, where `A := 1 − (q/(q−1))·d`. The
hypothesis `hcoup : d ≤ 2·η·ℓ·√A` is exactly `d/(2ℓ√A) ≤ η`.

This is stated ABSTRACTLY over `q, ℓ, d, η` so the lemma is unconditionally true
given its hypotheses; the RS-specific discharge of `hApos`/`hcoup` (at `d = 1−ρ`,
where `A = (qρ−1)/(q−1)`) lives in the `mds_list_bound` composition. See the
COMPOSE note in `lemma_graph.md` §P2 for the `qρ ≈ 1` boundary subtlety. -/
private theorem johnsonJqℓ_ge_johnsonJq_sub {q ℓ : ℕ} (hq : 1 < q) (hℓ : 1 < ℓ)
    {d η : ℝ} (hd0 : 0 ≤ d)
    (hApos : 0 < 1 - (q : ℝ) / ((q : ℝ) - 1) * d)
    (hcoup : d ≤ 2 * η * (ℓ : ℝ) *
      Real.sqrt (1 - (q : ℝ) / ((q : ℝ) - 1) * d)) :
    johnsonJq q d - η ≤ johnsonJqℓ q ℓ d := by
  -- Casts and basic positivity.
  have hqR : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < (q : ℝ) := lt_trans zero_lt_one hqR
  have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  have hℓR : (1 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
  have hℓ0 : (0 : ℝ) < (ℓ : ℝ) := lt_trans zero_lt_one hℓR
  -- Abbreviations.
  set c : ℝ := 1 - 1 / (q : ℝ) with hc_def
  set β : ℝ := (q : ℝ) / ((q : ℝ) - 1) with hβ_def
  set A : ℝ := 1 - β * d with hA_def
  have hApos' : 0 < A := hApos
  -- c = (q-1)/q > 0.
  have hc_pos : 0 < c := by
    rw [hc_def]
    have : 1 / (q : ℝ) < 1 := by
      rw [div_lt_one hq0]; exact hqR
    linarith
  -- c · β = 1.
  have hcβ : c * β = 1 := by
    rw [hc_def, hβ_def]; field_simp
  -- 1/c = β.
  have hβc : β = 1 / c := by
    field_simp
    linarith [hcβ, mul_comm c β]
  -- β > 0.
  have hβpos : 0 < β := by rw [hβ_def]; positivity
  -- √A > 0.
  have hsA_pos : 0 < Real.sqrt A := Real.sqrt_pos.mpr hApos'
  have hsA_nn : 0 ≤ Real.sqrt A := le_of_lt hsA_pos
  -- η ≥ 0 from the coupling hypothesis.
  have hη : 0 ≤ η := by
    have hprod : (0 : ℝ) < 2 * (ℓ : ℝ) * Real.sqrt A := by positivity
    -- d ≤ 2 η ℓ √A and 0 ≤ d ⟹ 0 ≤ 2 η ℓ √A = η · (2 ℓ √A)
    have h0le : (0 : ℝ) ≤ 2 * η * (ℓ : ℝ) * Real.sqrt A := le_trans hd0 hcoup
    nlinarith [h0le, hprod]
  -- KEY algebra: rewrite the johnsonJqℓ sqrt argument.
  have hAt : 1 - β * (((ℓ : ℝ) - 1) / (ℓ : ℝ)) * d = A + β * d / (ℓ : ℝ) := by
    rw [hA_def]; field_simp; ring
  -- Reduce the goal to a sqrt inequality.
  rw [johnsonJq, johnsonJqℓ]
  -- Fold the abbreviation c on both sides.
  rw [← hc_def, ← hβ_def]
  rw [hAt, ← hA_def]
  -- Goal: c * (1 - √A) - η ≤ c * (1 - √(A + β*d/ℓ))
  -- equivalently c * √(A + β*d/ℓ) ≤ c * √A + η.
  rw [sub_le_iff_le_add]
  -- It suffices to prove √(A + β*d/ℓ) ≤ √A + η/c.
  have hsuff : Real.sqrt (A + β * d / (ℓ : ℝ)) ≤ Real.sqrt A + η / c := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    -- (√A + η/c)^2 = A + 2 √A (η/c) + (η/c)^2.
    have hsq : (Real.sqrt A + η / c) ^ 2
        = A + 2 * Real.sqrt A * (η / c) + (η / c) ^ 2 := by
      have hssq : Real.sqrt A ^ 2 = A := Real.sq_sqrt hApos'.le
      ring_nf
      nlinarith [hssq]
    rw [hsq]
    -- Suffices: β*d/ℓ ≤ 2 √A (η/c) + (η/c)^2.
    -- η/c = η·β.  And from hcoup: β*d/ℓ ≤ 2 β η √A = 2 √A (η/c).
    have hηc : η / c = η * β := by rw [hβc]; ring
    -- divide hcoup by ℓ > 0, multiply by β > 0.
    have hdiv : β * d / (ℓ : ℝ) ≤ 2 * β * η * Real.sqrt A := by
      have := mul_le_mul_of_nonneg_left hcoup (le_of_lt hβpos)
      -- β*d ≤ β*(2 η ℓ √A) = 2 β η ℓ √A
      rw [div_le_iff₀ hℓ0]
      nlinarith [this, hsA_nn]
    nlinarith [hdiv, hηc, sq_nonneg (η / c), hsA_nn]
  -- Multiply hsuff by c > 0.
  have hmul := mul_le_mul_of_nonneg_left hsuff (le_of_lt hc_pos)
  -- c * (√A + η/c) = c √A + η.
  have hrw : c * (Real.sqrt A + η / c) = c * Real.sqrt A + η := by
    field_simp
  rw [hrw] at hmul
  linarith [hmul]

/-- Pure scalar helper for `mds_list_bound` (`s = √ρ`): `1 ≤ 1/s² − 2η`.
Reduces to `2s³ − 3s² + 1 = (s−1)²(2s+1) ≥ 0`. Isolated so `nlinarith` runs in
a tiny context. -/
private theorem mds_aux_inv {s η : ℝ} (hspos : 0 < s) (hs1 : s ≤ 1)
    (hη : 0 < η) (hη_le : η ≤ 1 - s) : (1 : ℝ) ≤ 1 / s ^ 2 - 2 * η := by
  have hs2 : (0 : ℝ) < s ^ 2 := by positivity
  have hge : (1 + 2 * η) * s ^ 2 ≤ 1 := by
    have hsub : (1 + 2 * η) * s ^ 2 ≤ (1 + 2 * (1 - s)) * s ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (le_of_lt hs2); linarith
    have hpoly : (1 + 2 * (1 - s)) * s ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg (sq_nonneg (s - 1)) (by linarith : (0:ℝ) ≤ 2 * s + 1)]
    linarith
  have hkey : 1 + 2 * η ≤ 1 / s ^ 2 := by rw [le_div_iff₀ hs2]; linarith
  linarith

/-- Pure scalar helper for `mds_list_bound` (`s = √ρ`): the `η`-budget inequality
`1 − s² ≤ (1/s² − 2η)·(s/√2)`. Uses `√2 ≤ 3/2` and the polynomial
`(3/2)(1−s²)s ≤ 1 − 2(1−s)s²` on `[0,1]`. Isolated for a small `nlinarith`
context. -/
private theorem mds_aux_scalar {s η : ℝ} (hspos : 0 < s) (hs1 : s ≤ 1)
    (hη_le : η ≤ 1 - s) :
    1 - s ^ 2 ≤ (1 / s ^ 2 - 2 * η) * (s / Real.sqrt 2) := by
  have hs0 : 0 ≤ s := le_of_lt hspos
  have hs2 : (0 : ℝ) < s ^ 2 := by positivity
  have hsqrt2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt2_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hmul_goal : (1 - s ^ 2) * Real.sqrt 2 ≤ (1 / s ^ 2 - 2 * η) * s := by
    have hmono : (1 / s ^ 2 - 2 * (1 - s)) * s ≤ (1 / s ^ 2 - 2 * η) * s := by
      apply mul_le_mul_of_nonneg_right _ hs0; linarith
    refine le_trans ?_ hmono
    have hrhs2 : (1 / s ^ 2 - 2 * (1 - s)) * s = (1 - 2 * (1 - s) * s ^ 2) / s := by
      field_simp
    rw [hrhs2, le_div_iff₀ hspos]
    have hr2_le : Real.sqrt 2 ≤ 3 / 2 := by nlinarith [hsqrt2_sq, hsqrt2]
    have hfac_nn : (0 : ℝ) ≤ (1 - s ^ 2) * s := by
      apply mul_nonneg _ hs0; nlinarith
    have hstep1 : (1 - s ^ 2) * Real.sqrt 2 * s ≤ (3 / 2) * ((1 - s ^ 2) * s) := by
      have := mul_le_mul_of_nonneg_left hr2_le hfac_nn; nlinarith [this]
    -- (3/2)(1-s²)s ≤ 1-2(1-s)s²  ⟺  4(1-s)s² + 3(1-s²)s ≤ 2  (×2).  Cubic, min margin 0.27.
    have hstep2 : (3 / 2) * ((1 - s ^ 2) * s) ≤ 1 - 2 * (1 - s) * s ^ 2 := by
      nlinarith [mul_nonneg (sq_nonneg (s - 1)) hs0, sq_nonneg (s - 1),
        mul_nonneg (sq_nonneg (2 * s - 1)) hs0, hs0, hs1, sq_nonneg s,
        mul_nonneg hs0 hs0]
    linarith
  have hrhs_eq : (1 / s ^ 2 - 2 * η) * s
      = ((1 / s ^ 2 - 2 * η) * (s / Real.sqrt 2)) * Real.sqrt 2 := by
    field_simp
  rw [hrhs_eq] at hmul_goal
  exact le_of_mul_le_mul_right hmul_goal hsqrt2

set_option maxHeartbeats 1000000 in
/-- **Corollary 3.3.** For an MDS code `C` of rate `ρ` and every `η > 0`, the list
at radius `1 − √ρ − η` has size at most `1/(2·η·ρ)`.

Stated for the Reed–Solomon family (our concrete MDS codes), where `ρ = k/|L|` and
`δmin = (|L|−k+1)/|L| ≥ 1 − ρ` (`deltaMin`, proven). Derived from `johnson_bound`
by choosing `ℓ = ⌊1/(2ηρ)⌋` and checking `1 − √ρ − η ≤ Jq,ℓ(δmin)` via the chain
A → B → `johnsonJqℓ_mono` above.

`hq : 1 < Fintype.card F` is required by `johnson_bound` (`q = |F|`, the alphabet
of `code L k`). `0 < ρ` and `ρ ≤ 1` are derived in-proof from `0 < k`, `k ≤ |L|`,
`hρ`. The RS side fact `|L| ≤ |F|` (i.e. `Finset.card_le_univ L`) gives `qρ ≥ k ≥ 1`,
hence Sub-lemma A's `harg`. -/
theorem mds_list_bound {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    (L : Finset F) (k : ℕ) (hk : 0 < k) (hk2 : 2 ≤ k) (hkn : k ≤ L.card)
    [Fintype (MCA.ReedSolomon.code L k)]
    (hq : 1 < Fintype.card F)
    (η : ℝ) (hη : 0 < η)
    (ρ : ℝ) (hρ : ρ = (k : ℝ) / (L.card : ℝ))
    (δ : ℚ) (hδpos : 0 ≤ δ) (hδ : (δ : ℝ) ≤ 1 - Real.sqrt ρ - η) :
    (maxListSize (MCA.ReedSolomon.code L k) δ : ℝ) ≤ 1 / (2 * η * ρ) := by
  classical
  set q : ℕ := Fintype.card F with hqdef
  -- Basic positivity / casts.
  have hqR1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq0R : (0 : ℝ) < (q : ℝ) := lt_trans zero_lt_one hqR1
  have hq1R : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  have hkpos : 0 < L.card := lt_of_lt_of_le hk hkn
  have hLR : (0 : ℝ) < (L.card : ℝ) := by exact_mod_cast hkpos
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hk2R : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
  -- |L| ≤ q.
  have hLleq : (L.card : ℝ) ≤ (q : ℝ) := by
    have : L.card ≤ Fintype.card F := Finset.card_le_univ L
    exact_mod_cast this
  -- ρ = k/|L| ∈ (0,1].
  have hρpos : 0 < ρ := by rw [hρ]; positivity
  have hρ1 : ρ ≤ 1 := by
    rw [hρ, div_le_one hLR]; exact_mod_cast hkn
  -- q·ρ ≥ k ≥ 2.
  have hqρ : (q : ℝ) * ρ = (q : ℝ) * (k : ℝ) / (L.card : ℝ) := by
    rw [hρ]; ring
  have hqρ_ge_k : (k : ℝ) ≤ (q : ℝ) * ρ := by
    rw [hqρ, le_div_iff₀ hLR]
    have : (L.card : ℝ) * (k : ℝ) ≤ (q : ℝ) * (k : ℝ) := by
      apply mul_le_mul_of_nonneg_right hLleq (le_of_lt hkR)
    linarith
  have hqρ_ge2 : (2 : ℝ) ≤ (q : ℝ) * ρ := le_trans hk2R hqρ_ge_k
  -- harg for Sub-lemma A: (q/(q-1))(1-ρ) ≤ 1  ⟺  qρ ≥ 1.
  have harg : (q : ℝ) / ((q : ℝ) - 1) * (1 - ρ) ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one hq1R]; nlinarith [hqρ_ge2]
  -- A := 1 - (q/(q-1))(1-ρ) = (qρ-1)/(q-1) > 0, and A ≥ ρ/2.
  set A : ℝ := 1 - (q : ℝ) / ((q : ℝ) - 1) * (1 - ρ) with hAdef
  have hA_eq : A = ((q : ℝ) * ρ - 1) / ((q : ℝ) - 1) := by
    rw [hAdef]; field_simp; ring
  have hApos : 0 < A := by
    rw [hA_eq]; apply div_pos (by linarith [hqρ_ge2]) hq1R
  have hAge : ρ / 2 ≤ A := by
    rw [hA_eq, le_div_iff₀ hq1R]
    -- ρ/2·(q-1) ≤ qρ-1  ⟺  ρ(q+1) ≥ 2 ; since qρ≥2 and ρ>0.
    nlinarith [hqρ_ge2, hρpos, hρ1]
  -- √ρ and bounds.
  set s : ℝ := Real.sqrt ρ with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg ρ
  have hs_sq : s ^ 2 = ρ := by rw [hsdef, Real.sq_sqrt (le_of_lt hρpos)]
  have hspos : 0 < s := Real.sqrt_pos.mpr hρpos
  have hs1 : s ≤ 1 := by
    rw [hsdef]; rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hρ1
  -- δ nonneg ⟹ η ≤ 1 - s.
  have hδR : (0 : ℝ) ≤ (δ : ℝ) := by exact_mod_cast hδpos
  have hη_le : η ≤ 1 - s := by
    have : (0 : ℝ) ≤ 1 - s - η := le_trans hδR hδ
    linarith
  -- The list-size budget x := 1/(2ηρ) > 0.
  set x : ℝ := 1 / (2 * η * ρ) with hxdef
  have hxpos : 0 < x := by rw [hxdef]; positivity
  -- ℓ := ⌊x⌋.
  set ℓ : ℕ := ⌊x⌋₊ with hℓdef
  have hℓ_le_x : (ℓ : ℝ) ≤ x := Nat.floor_le (le_of_lt hxpos)
  -- Case split on ℓ < 2 (vacuous) vs ℓ ≥ 2.
  rcases Nat.lt_or_ge ℓ 2 with hℓ1 | hℓ2
  · -- VACUOUS: ℓ < 2 ⟹ x < 2 ⟹ η > 1/(4ρ) ⟹ s + η > 1, contradicting δ ≤ 1-s-η, 0≤δ.
    exfalso
    have hx_lt2 : x < 2 := by
      by_contra h
      push_neg at h
      -- 2 ≤ x ⟹ 2 ≤ ⌊x⌋ (since 2 is a Nat).
      have : (2 : ℕ) ≤ ℓ := by
        rw [hℓdef]; exact Nat.le_floor (by exact_mod_cast h)
      omega
    -- x = 1/(2ηρ) < 2 ⟹ 1 < 4ηρ ⟹ η > 1/(4ρ).
    have h4 : 1 < 4 * η * ρ := by
      rw [hxdef] at hx_lt2
      rw [div_lt_iff₀ (by positivity)] at hx_lt2
      nlinarith [hx_lt2]
    have hη_gt : 1 / (4 * ρ) < η := by
      rw [div_lt_iff₀ (by positivity)]; nlinarith [h4]
    -- s + 1/(4ρ) > 1  (the verified min ≈ 1.19): s + 1/(4ρ) ≥ 1, with strict from margin.
    -- s³ + ... : multiply by 4ρ = 4s²: 4s³ + 1 ≥ 4s², i.e. 4s³ - 4s² + 1 ≥ 0.
    have hkeyvac : 1 ≤ s + 1 / (4 * ρ) := by
      have h4ρ : (0 : ℝ) < 4 * ρ := by positivity
      rw [show s + 1 / (4 * ρ) = (s * (4 * ρ) + 1) / (4 * ρ) by field_simp,
        le_div_iff₀ h4ρ, one_mul]
      -- s·(4ρ) + 1 ≥ 4ρ, with ρ = s²: 4s³ + 1 ≥ 4s²  ⟺ 4s³ - 4s² + 1 ≥ 0.
      rw [← hs_sq]
      nlinarith [sq_nonneg (3 * s - 2), hs0, hs1, sq_nonneg s]
    -- Then η > 1/(4ρ) ≥ 1 - s, so 1 - s - η < 0 ≤ δ ≤ 1 - s - η, contradiction.
    have : (1 : ℝ) - s - η < 0 := by linarith [hη_gt, hkeyvac]
    linarith [le_trans hδR hδ]
  · -- MAIN: ℓ ≥ 2 (so 1 < ℓ).
    have hℓ_gt1 : 1 < ℓ := by omega
    have hℓR1 : (1 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ_gt1
    have hℓ0R : (0 : ℝ) < (ℓ : ℝ) := lt_trans zero_lt_one hℓR1
    -- ℓ ≥ x - 1.
    have hℓ_ge : x - 1 ≤ (ℓ : ℝ) := by
      have := Nat.lt_floor_add_one x
      rw [← hℓdef] at this
      linarith
    -- √A ≥ s/√2 :  A ≥ ρ/2 = s²/2 ⟹ √A ≥ √(s²/2) = s/√2.
    set sA : ℝ := Real.sqrt A with hsAdef
    have hsA0 : 0 ≤ sA := Real.sqrt_nonneg A
    have hsA_sq : sA ^ 2 = A := by rw [hsAdef, Real.sq_sqrt (le_of_lt hApos)]
    -- 1/ρ - 2η ≥ 1 > 0.  (1/ρ = 1/s²; η ≤ 1-s ⟹ 1/s² - 2(1-s) ≥ 1 ⟺ (s-1)²(2s+1) ≥ 0.)
    have hρeq : ρ = s ^ 2 := hs_sq.symm
    have h1ρ2η : (1 : ℝ) ≤ 1 / ρ - 2 * η := by
      rw [hρeq]; exact mds_aux_inv hspos hs1 hη hη_le
    have h1ρ2η_pos : (0 : ℝ) < 1 / ρ - 2 * η := by linarith
    -- hcoup : (1-ρ) ≤ 2η·ℓ·√A.
    -- Step a: 2η·ℓ ≥ 2η(x-1) = 1/ρ - 2η  (since x = 1/(2ηρ), 2ηx = 1/ρ).
    have h2ηx : 2 * η * x = 1 / ρ := by
      rw [hxdef]; field_simp
    have hstep_a : 1 / ρ - 2 * η ≤ 2 * η * (ℓ : ℝ) := by
      have h2η : (0 : ℝ) ≤ 2 * η := by positivity
      have hmul : 2 * η * (x - 1) ≤ 2 * η * (ℓ : ℝ) :=
        mul_le_mul_of_nonneg_left hℓ_ge h2η
      have hexpand : 2 * η * (x - 1) = 1 / ρ - 2 * η := by
        rw [mul_sub, h2ηx, mul_one]
      linarith [hmul, hexpand]
    -- Step b: √A ≥ s/√2  ⟹  combine.  We avoid √2: prove (1-ρ)·√2 ≤ (1/ρ-2η)·s, then use √A·√2 ≥ s.
    -- Easier: show (1-ρ) ≤ (1/ρ-2η)·sA directly via sA ≥ s/√2 and the scalar inequality.
    -- sA ≥ s/√2  ⟺  2·sA² ≥ s²  ⟺  2A ≥ ρ (true since A ≥ ρ/2).
    have hsqrt2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hsqrt2_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hsA_ge : s / Real.sqrt 2 ≤ sA := by
      rw [div_le_iff₀ hsqrt2]
      -- s ≤ sA·√2 ; both nonneg, compare squares: s² ≤ (sA√2)² = 2A ; ρ = s² ≤ 2A.
      have hboth : (0 : ℝ) ≤ sA * Real.sqrt 2 := mul_nonneg hsA0 (le_of_lt hsqrt2)
      have hrhs_sq : (sA * Real.sqrt 2) ^ 2 = 2 * A := by
        rw [mul_pow, hsA_sq, hsqrt2_sq]; ring
      have hsq_le : s ^ 2 ≤ (sA * Real.sqrt 2) ^ 2 := by
        rw [hrhs_sq, hs_sq]; linarith [hAge]
      nlinarith [hsq_le, hs0, hboth]
    -- The scalar inequality: (1-ρ) ≤ (1/ρ - 2η)·(s/√2).
    -- Multiply by √2 (>0): (1-ρ)√2 ≤ (1/ρ-2η)·s.  With ρ=s², η≤1-s:
    -- suffices (1-s²)√2 ≤ (1/s² - 2(1-s))·s = 1/s - 2(1-s)s.
    have hscalar : 1 - ρ ≤ (1 / ρ - 2 * η) * (s / Real.sqrt 2) := by
      rw [hρeq]; exact mds_aux_scalar hspos hs1 hη_le
    -- Assemble hcoup.
    have hcoup : (1 - ρ) ≤ 2 * η * (ℓ : ℝ) * sA := by
      -- (1-ρ) ≤ (1/ρ-2η)·(s/√2) ≤ (1/ρ-2η)·sA ≤ (2ηℓ)·sA
      have c1 : (1 / ρ - 2 * η) * (s / Real.sqrt 2) ≤ (1 / ρ - 2 * η) * sA :=
        mul_le_mul_of_nonneg_left hsA_ge (le_of_lt h1ρ2η_pos)
      have c2 : (1 / ρ - 2 * η) * sA ≤ 2 * η * (ℓ : ℝ) * sA :=
        mul_le_mul_of_nonneg_right hstep_a hsA0
      calc (1 - ρ) ≤ (1 / ρ - 2 * η) * (s / Real.sqrt 2) := hscalar
        _ ≤ (1 / ρ - 2 * η) * sA := c1
        _ ≤ 2 * η * (ℓ : ℝ) * sA := c2
    -- ===================================================================
    -- Build the Johnson chain and apply johnson_bound.
    -- ===================================================================
    have hd0 : (0 : ℝ) ≤ 1 - ρ := by linarith
    -- Sub-lemma A : 1 - √ρ ≤ johnsonJq q (1-ρ).
    have hA_chain : 1 - s ≤ johnsonJq q (1 - ρ) :=
      johnsonJq_ge_one_sub_sqrt hq (le_of_lt hρpos) hρ1 harg
    -- Sub-lemma B : johnsonJq q (1-ρ) - η ≤ johnsonJqℓ q ℓ (1-ρ).
    -- B's hApos / hcoup are at d = 1-ρ with A = our A, √A = sA.
    have hApos_B : 0 < 1 - (q : ℝ) / ((q : ℝ) - 1) * (1 - ρ) := hApos
    have hcoup_B : (1 - ρ) ≤ 2 * η * (ℓ : ℝ) *
        Real.sqrt (1 - (q : ℝ) / ((q : ℝ) - 1) * (1 - ρ)) := by
      have : Real.sqrt (1 - (q : ℝ) / ((q : ℝ) - 1) * (1 - ρ)) = sA := by
        rw [hsAdef, hAdef]
      rw [this]; exact hcoup
    have hB_chain : johnsonJq q (1 - ρ) - η ≤ johnsonJqℓ q ℓ (1 - ρ) :=
      johnsonJqℓ_ge_johnsonJq_sub hq hℓ_gt1 hd0 hApos_B hcoup_B
    -- 1 - ρ ≤ minDist (code L k) = (|L|-k+1)/|L|.
    have hmd : MCA.ReedSolomon.minDist (MCA.ReedSolomon.code L k)
        = ((L.card - k + 1 : ℕ) : ℝ) / (L.card : ℝ) :=
      MCA.ReedSolomon.deltaMin L k hk hkn
    have hρ_le_md : 1 - ρ ≤ MCA.ReedSolomon.minDist (MCA.ReedSolomon.code L k) := by
      rw [hmd, hρ]
      -- (|L|-k+1)/|L| ≥ 1 - k/|L| = (|L|-k)/|L|.  ℕ-sub: k ≤ |L|.
      rw [le_div_iff₀ hLR]
      have hcast : ((L.card - k + 1 : ℕ) : ℝ) = (L.card : ℝ) - (k : ℝ) + 1 := by
        rw [Nat.cast_add, Nat.cast_sub hkn, Nat.cast_one]
      rw [hcast]
      have hkdiv : (k : ℝ) / (L.card : ℝ) * (L.card : ℝ) = (k : ℝ) :=
        div_mul_cancel₀ (k : ℝ) hLR.ne'
      nlinarith [hkdiv, hLR]
    -- Monotonicity : johnsonJqℓ q ℓ (1-ρ) ≤ johnsonJqℓ q ℓ (minDist).
    have hmono_chain :
        johnsonJqℓ q ℓ (1 - ρ)
          ≤ johnsonJqℓ q ℓ (MCA.ReedSolomon.minDist (MCA.ReedSolomon.code L k)) :=
      johnsonJqℓ_mono hq hℓ_gt1 hρ_le_md
    -- Full chain : (δ:ℝ) ≤ 1-s-η ≤ johnsonJqℓ q ℓ (minDist).
    have hfull : (δ : ℝ)
        ≤ johnsonJqℓ q ℓ (MCA.ReedSolomon.minDist (MCA.ReedSolomon.code L k)) := by
      calc (δ : ℝ) ≤ 1 - s - η := hδ
        _ ≤ johnsonJq q (1 - ρ) - η := by linarith [hA_chain]
        _ ≤ johnsonJqℓ q ℓ (1 - ρ) := hB_chain
        _ ≤ _ := hmono_chain
    -- Apply johnson_bound : maxListSize ≤ ℓ.
    have hbound : maxListSize (MCA.ReedSolomon.code L k) δ ≤ ℓ :=
      johnson_bound (MCA.ReedSolomon.code L k) ℓ hℓ_gt1 hq δ hδpos hfull
    -- Conclude : (maxListSize : ℝ) ≤ ℓ ≤ x = 1/(2ηρ).
    have hcast : (maxListSize (MCA.ReedSolomon.code L k) δ : ℝ) ≤ (ℓ : ℝ) := by
      exact_mod_cast hbound
    calc (maxListSize (MCA.ReedSolomon.code L k) δ : ℝ)
        ≤ (ℓ : ℝ) := hcast
      _ ≤ x := hℓ_le_x
      _ = 1 / (2 * η * ρ) := by rw [hxdef]

end MCA.Code
