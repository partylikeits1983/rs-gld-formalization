import Mathlib
import MCA.Code.Hamming

/-!
# The simplex embedding (Lemma 4.4.4) and the inner-product bounds (GRS Ex. 7.6)

Two leaves bridging codes to the geometric core `geom_lemma_sum_sq`:

* `simplex_embed` (Lemma 4.4.4): a map `f : (Fin n → α) → EuclideanSpace ℝ (Fin n × α)`
  sending each word to a unit vector, with pairwise inner product
  `⟨f c₁, f c₂⟩ = 1 − (q/(q−1))·Δ(c₁,c₂)`, where `q = |α|`. Built coordinatewise
  from `φ(i) = eᵢ − e` (scaled by `√(q/(n(q−1)))`).

* `johnson_inner_bounds` (GRS Ex. 7.6 / Ex. 7.8 algebra): for codewords pairwise
  `δmin`-far and all within Johnson radius `Jq,ℓ(δmin)` of a received word `y`,
  the shifted vectors `vᵢ` (origin moved to a `(y,α)`-determined point) satisfy
  `‖vᵢ‖² ≤ U` and `⟨vᵢ,vⱼ⟩ ≤ −ε` with `1 + U/ε = ℓ`. Pure real-arithmetic tuning
  of the parameter `α` on top of `simplex_embed`'s inner-product identity.
-/

namespace MCA.Code

open scoped InnerProductSpace BigOperators

variable {α : Type*} [DecidableEq α] [Fintype α] {n : ℕ}

/-- **L2 — the simplex embedding (GRS Lemma 4.4.4).** There is a map from words to
`EuclideanSpace ℝ (Fin n × α)` whose image consists of unit vectors and whose
pairwise inner product is `1 − (q/(q−1))·Δ(c₁,c₂)` with `q = |α|`.

`Δ(c₁,c₂)` here is the *normalized* Hamming distance cast to `ℝ`. Requires `0 < n`
(the scaling divisor) and `1 < q` (so `q − 1 ≠ 0`).

Proof obligation: define `f c i := √(q/(n(q−1)))·(if (i.2 = c i.1) then 1 else 0) − …`
(the scaled `eᵢ − e` per coordinate), then compute `‖f c‖² = 1` and the inner-product
identity by summing the per-coordinate `⟨φ(x),φ(y)⟩ = [x=y] − 1/q` over the `n`
coordinates. The count of agreeing coordinates is `n − hammingDist c₁ c₂`. -/
theorem simplex_embed (hn : 0 < n) (hq : 1 < Fintype.card α) :
    ∃ f : (Fin n → α) → EuclideanSpace ℝ (Fin n × α),
      (∀ c, ‖f c‖ = 1) ∧
      (∀ c₁ c₂ : Fin n → α,
        @inner ℝ _ _ (f c₁) (f c₂)
          = 1 - (Fintype.card α : ℝ) / ((Fintype.card α : ℝ) - 1)
              * (normDist c₁ c₂ : ℝ)) := by
  classical
  set q : ℕ := Fintype.card α with hqdef
  -- Real cardinality and basic positivity facts.
  have hqR : (0 : ℝ) < (q : ℝ) := by
    have : 0 < q := lt_trans Nat.zero_lt_one hq
    exact_mod_cast this
  have hq1R : (0 : ℝ) < (q : ℝ) - 1 := by
    have : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    linarith
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  -- The "centered indicator" per-symbol simplex vector, normalized.
  set s : ℝ := Real.sqrt (((q : ℝ) - 1) / q) with hsdef
  have hsq_inner : ((q : ℝ) - 1) / q > 0 := by positivity
  have hs2 : s ^ 2 = ((q : ℝ) - 1) / q := by
    rw [hsdef, Real.sq_sqrt hsq_inner.le]
  have hspos : 0 < s := by rw [hsdef]; exact Real.sqrt_pos.mpr hsq_inner
  -- per-symbol vector `u b : α → ℝ`
  let u : α → α → ℝ := fun b a => ((if a = b then (1:ℝ) else 0) - 1 / q) / s
  -- KEY per-symbol Gram fact.
  have gram : ∀ b b' : α,
      (∑ a : α, u b a * u b' a)
        = if b = b' then (1 : ℝ) else -1 / ((q : ℝ) - 1) := by
    intro b b'
    have hcard : (Fintype.card α : ℝ) = (q : ℝ) := by rw [hqdef]
    -- expand the product, sum termwise.
    have hexpand : ∀ a : α,
        u b a * u b' a
          = (((if a = b then (1:ℝ) else 0) - 1/q) *
              ((if a = b' then (1:ℝ) else 0) - 1/q)) / s ^ 2 := by
      intro a
      simp only [u]
      rw [div_mul_div_comm, sq]
    rw [Finset.sum_congr rfl (fun a _ => hexpand a)]
    rw [← Finset.sum_div]
    -- compute the numerator sum
    have hnum : (∑ a : α, ((if a = b then (1:ℝ) else 0) - 1/q) *
          ((if a = b' then (1:ℝ) else 0) - 1/q))
        = (if b = b' then (1:ℝ) else 0) - 1 / q := by
      have : ∀ a : α, ((if a = b then (1:ℝ) else 0) - 1/q) *
          ((if a = b' then (1:ℝ) else 0) - 1/q)
          = (if a = b then (1:ℝ) else 0) * (if a = b' then (1:ℝ) else 0)
            - (1/q) * (if a = b then (1:ℝ) else 0)
            - (1/q) * (if a = b' then (1:ℝ) else 0)
            + (1/q) * (1/q) := by
        intro a; ring
      rw [Finset.sum_congr rfl (fun a _ => this a)]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
      -- four sums
      have s1 : (∑ a : α, (if a = b then (1:ℝ) else 0) * (if a = b' then (1:ℝ) else 0))
          = if b = b' then (1:ℝ) else 0 := by
        have hprod : ∀ a : α, (if a = b then (1:ℝ) else 0) * (if a = b' then (1:ℝ) else 0)
            = if (a = b ∧ a = b') then (1:ℝ) else 0 := by
          intro a
          by_cases h1 : a = b <;> by_cases h2 : a = b' <;> simp [h1, h2]
        rw [Finset.sum_congr rfl (fun a _ => hprod a)]
        by_cases hbb : b = b'
        · subst hbb
          rw [if_pos rfl]
          have hsimp : ∀ a : α, (if (a = b ∧ a = b) then (1:ℝ) else 0)
              = if a = b then (1:ℝ) else 0 := by
            intro a; by_cases h : a = b <;> simp [h]
          rw [Finset.sum_congr rfl (fun a _ => hsimp a)]
          rw [Finset.sum_ite_eq' Finset.univ b (fun _ => (1:ℝ))]
          simp
        · rw [if_neg hbb]
          apply Finset.sum_eq_zero
          intro a _
          rw [if_neg]
          rintro ⟨ha1, ha2⟩
          exact hbb (ha1 ▸ ha2)
      have s2 : (∑ a : α, (1/(q:ℝ)) * (if a = b then (1:ℝ) else 0)) = 1/q := by
        rw [← Finset.mul_sum]
        rw [Finset.sum_ite_eq' Finset.univ b (fun _ => (1:ℝ))]
        simp
      have s3 : (∑ a : α, (1/(q:ℝ)) * (if a = b' then (1:ℝ) else 0)) = 1/q := by
        rw [← Finset.mul_sum]
        rw [Finset.sum_ite_eq' Finset.univ b' (fun _ => (1:ℝ))]
        simp
      have s4 : (∑ _a : α, (1/(q:ℝ)) * (1/(q:ℝ))) = 1/q := by
        rw [Finset.sum_const, Finset.card_univ, ← hqdef]
        rw [nsmul_eq_mul]
        field_simp
      rw [s1, s2, s3, s4]
      ring
    rw [hnum, hs2]
    -- divide numerator by s^2 = (q-1)/q
    by_cases hbb : b = b'
    · subst hbb
      rw [if_pos rfl, if_pos rfl]
      field_simp
    · rw [if_neg hbb, if_neg hbb]
      rw [zero_sub]
      field_simp
  -- per-symbol self-Gram (norm) is 1.
  have gram_self : ∀ b : α, (∑ a : α, u b a * u b a) = 1 := by
    intro b; rw [gram b b, if_pos rfl]
  -- Build the embedding.
  refine ⟨fun c => WithLp.toLp 2 (fun p : Fin n × α => (1 / Real.sqrt n) * u (c p.1) p.2),
    ?_, ?_⟩
  · -- norms are 1
    intro c
    rw [EuclideanSpace.norm_eq]
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    congr 1
    rw [Fintype.sum_prod_type]
    have hsqrtn : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt hnR.le
    have hsqrtn_ne : Real.sqrt (n : ℝ) ≠ 0 := by
      rw [Ne, Real.sqrt_eq_zero hnR.le]; exact ne_of_gt hnR
    calc (∑ i : Fin n, ∑ a : α,
            ‖WithLp.toLp 2 (fun p : Fin n × α => (1 / Real.sqrt n) * u (c p.1) p.2) (i, a)‖ ^ 2)
        = ∑ i : Fin n, ∑ a : α, (1 / Real.sqrt n) ^ 2 * (u (c i) a) ^ 2 := by
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro a _
          rw [PiLp.toLp_apply]
          rw [Real.norm_eq_abs, sq_abs, mul_pow]
      _ = ∑ i : Fin n, (1 / Real.sqrt n) ^ 2 * (∑ a : α, (u (c i) a) ^ 2) := by
          apply Finset.sum_congr rfl; intro i _
          rw [Finset.mul_sum]
      _ = ∑ i : Fin n, (1 / Real.sqrt n) ^ 2 * 1 := by
          apply Finset.sum_congr rfl; intro i _
          rw [show (∑ a : α, (u (c i) a) ^ 2) = ∑ a : α, u (c i) a * u (c i) a from
            Finset.sum_congr rfl (fun a _ => by rw [sq])]
          rw [gram_self]
      _ = (n : ℝ) * ((1 / Real.sqrt n) ^ 2) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
      _ = 1 := by
          rw [div_pow, one_pow, hsqrtn]
          field_simp
  · -- inner product identity
    intro c₁ c₂
    rw [PiLp.inner_apply]
    have hsqrtn : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt hnR.le
    have hsqrtn_ne : Real.sqrt (n : ℝ) ≠ 0 := by
      rw [Ne, Real.sqrt_eq_zero hnR.le]; exact ne_of_gt hnR
    -- reduce real inner ⟪x,y⟫ on ℝ to x*y, sum over (i,a) factorized
    have hreduce : (∑ p : Fin n × α,
          @inner ℝ _ _ (WithLp.toLp 2 (fun p : Fin n × α => (1 / Real.sqrt n) * u (c₁ p.1) p.2) p)
            (WithLp.toLp 2 (fun p : Fin n × α => (1 / Real.sqrt n) * u (c₂ p.1) p.2) p))
        = ∑ i : Fin n, (1 / Real.sqrt n) ^ 2 *
            (∑ a : α, u (c₁ i) a * u (c₂ i) a) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro a _
      rw [PiLp.toLp_apply, PiLp.toLp_apply]
      rw [real_inner_eq_re_inner ℝ, RCLike.inner_apply]
      simp only [conj_trivial, RCLike.re_to_real]
      ring
    rw [hreduce]
    -- compute the gram per coordinate
    have hcoord : ∀ i : Fin n, (∑ a : α, u (c₁ i) a * u (c₂ i) a)
        = if c₁ i = c₂ i then (1:ℝ) else -1 / ((q:ℝ) - 1) := fun i => gram (c₁ i) (c₂ i)
    rw [Finset.sum_congr rfl (fun i _ => by rw [hcoord i])]
    -- factor out the scalar
    rw [← Finset.mul_sum]
    -- split the if-sum into agree / disagree using the disagreement filter card
    set d : ℕ := hammingDist c₁ c₂ with hddef
    have hdisagree : (Finset.univ.filter fun i => c₁ i ≠ c₂ i).card = d := rfl
    have hsplit : (∑ i : Fin n, if c₁ i = c₂ i then (1:ℝ) else -1 / ((q:ℝ) - 1))
        = (↑(n - d) : ℝ) * 1 + (↑d : ℝ) * (-1 / ((q:ℝ) - 1)) := by
      rw [Finset.sum_ite]
      have hagcard : (Finset.univ.filter fun i => c₁ i = c₂ i).card = n - d := by
        have hcompl : (Finset.univ.filter fun i => c₁ i = c₂ i)
            = (Finset.univ.filter fun i => c₁ i ≠ c₂ i)ᶜ := by
          ext i; simp
        rw [hcompl, Finset.card_compl, Fintype.card_fin, hdisagree]
      have hdiscard : (Finset.univ.filter fun i => ¬ (c₁ i = c₂ i)).card = d := hdisagree
      rw [Finset.sum_const, Finset.sum_const, hagcard, hdiscard]
      rw [nsmul_eq_mul, nsmul_eq_mul]
    rw [hsplit]
    -- relate normDist cast to (d / n : ℝ)
    have hnd : (normDist c₁ c₂ : ℝ) = (d : ℝ) / (n : ℝ) := by
      unfold normDist
      rw [← hddef]
      push_cast
      ring
    rw [hnd]
    -- d ≤ n so (n - d : ℕ) casts to (n : ℝ) - d
    have hdle : d ≤ n := by
      rw [hddef]
      have := hammingDist_le_of_agreeOn (g := c₁) (c := c₂) (S := (∅ : Finset (Fin n)))
        (by intro i hi; exact absurd hi (Finset.notMem_empty i))
      simpa using this
    have hndsub : (↑(n - d) : ℝ) = (n : ℝ) - (d : ℝ) := by
      rw [Nat.cast_sub hdle]
    rw [hndsub]
    -- final field computation: (1/√n)^2 = 1/n
    rw [div_pow, one_pow, hsqrtn]
    field_simp
    ring

/-- **L3 — the inner-product bounds with `α`-tuning (GRS Ex. 7.6/7.8).** Given the
embedding `f` of `simplex_embed`, a received word `y`, and `M` codewords `c : Fin M → …`
that are pairwise `δmin`-far and all within (normalized) distance `δ ≤ Jq,ℓ(δmin)` of
`y`, there exist `U, ε` with `0 < ε`, `1 + U/ε = ℓ`, and shifted vectors `v i` such
that `‖v i‖² ≤ U` and `⟨v i, v j⟩ ≤ −ε` for `i ≠ j`.

This is the real-arithmetic crux: choosing `α` (the origin-shift parameter, NOT the
alphabet) and discharging the two algebraic inequalities (7.26), (7.27) from the
inner-product identity of `simplex_embed`. The output `(v, U, ε)` is exactly the
hypothesis package of `geom_lemma_sum_sq`.

Stated abstractly over the inner-product identity (hypothesis `hf`) so it does not
re-derive `simplex_embed`. `dmin := minDist`-style normalized min distance as a
rational lower bound on pairwise distances; `δ` the Johnson radius. -/
theorem johnson_inner_bounds (f : (Fin n → α) → EuclideanSpace ℝ (Fin n × α))
    (hq : 1 < Fintype.card α)
    (hf : ∀ c₁ c₂ : Fin n → α,
        @inner ℝ _ _ (f c₁) (f c₂)
          = 1 - (Fintype.card α : ℝ) / ((Fintype.card α : ℝ) - 1)
              * (normDist c₁ c₂ : ℝ))
    (hfnorm : ∀ c, ‖f c‖ = 1)
    (ℓ : ℕ) (hℓ : 1 < ℓ)
    (dmin δ : ℚ) (hdmin : 0 < dmin) (hδpos : 0 ≤ δ)
    (y : Fin n → α) {M : ℕ} (c : Fin M → (Fin n → α))
    (hfar : ∀ i j, i ≠ j → dmin ≤ normDist (c i) (c j))
    (hclose : ∀ i, normDist y (c i) ≤ δ)
    (hradius : (δ : ℝ) ≤
      (1 - 1 / (Fintype.card α : ℝ)) *
        (1 - Real.sqrt (1 - (Fintype.card α : ℝ) / ((Fintype.card α : ℝ) - 1)
          * (((ℓ : ℝ) - 1) / (ℓ : ℝ)) * (dmin : ℝ)))) :
    ∃ (v : Fin M → EuclideanSpace ℝ (Fin n × α)) (U ε : ℝ),
      0 < ε ∧ 1 + U / ε = (ℓ : ℝ) ∧
      (∀ i, ‖v i‖ ^ 2 ≤ U) ∧
      (∀ i j, i ≠ j → @inner ℝ _ _ (v i) (v j) ≤ -ε) := by
  classical
  -- Real cardinality and basic positivity facts.
  set q : ℝ := (Fintype.card α : ℝ) with hqdef
  have hqR : (1 : ℝ) < q := by rw [hqdef]; exact_mod_cast hq
  have hq1R : (0 : ℝ) < q - 1 := by linarith
  -- β := q/(q-1) > 0
  set β : ℝ := q / (q - 1) with hβdef
  have hβpos : 0 < β := by rw [hβdef]; positivity
  -- dmin as a real, positive.
  have hdminR : (0 : ℝ) < (dmin : ℝ) := by exact_mod_cast hdmin
  -- ℓ > 0 as a real.
  have hℓR : (1 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
  have hℓpos : (0 : ℝ) < (ℓ : ℝ) := by linarith
  have hℓne : (ℓ : ℝ) ≠ 0 := ne_of_gt hℓpos
  -- 1 - 1/q = 1/β  (used to translate hradius)
  have hinvβ : 1 - 1 / q = 1 / β := by
    rw [hβdef]; field_simp
  -- The origin-shift parameter a := 1 - β δ.
  set a : ℝ := 1 - β * (δ : ℝ) with hadef
  -- The radius `R := β·((ℓ-1)/ℓ)·dmin`, the argument of the sqrt.
  set R : ℝ := β * (((ℓ : ℝ) - 1) / (ℓ : ℝ)) * (dmin : ℝ) with hRdef
  -- R ≥ 0
  have hRnn : 0 ≤ R := by
    rw [hRdef]
    have : (0 : ℝ) ≤ ((ℓ : ℝ) - 1) / (ℓ : ℝ) := by
      apply div_nonneg; linarith; linarith
    positivity
  -- U and ε.
  set U : ℝ := (((ℓ : ℝ) - 1) / (ℓ : ℝ)) * β * (dmin : ℝ) with hUdef
  set ε : ℝ := β * (dmin : ℝ) / (ℓ : ℝ) with hεdef
  -- ε > 0.
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  -- 1 + U/ε = ℓ.
  have hUε : 1 + U / ε = (ℓ : ℝ) := by
    rw [hUdef, hεdef]
    have hβdmin : β * (dmin : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  -- Restate hradius: β·δ ≤ 1 - √(1 - R), and rearrange to √(1-R) ≤ 1 - βδ.
  have hradius' : β * (δ : ℝ) ≤ 1 - Real.sqrt (1 - R) := by
    have h1 : (δ : ℝ) ≤ (1 / β) * (1 - Real.sqrt (1 - R)) := by
      rw [← hinvβ]; rw [hRdef] at hradius ⊢; convert hradius using 3
    -- multiply both sides by β > 0
    have := mul_le_mul_of_nonneg_left h1 hβpos.le
    rw [← mul_assoc] at this
    have hββ : β * (1 / β) = 1 := by field_simp
    rwa [hββ, one_mul] at this
  -- √(1-R) ≤ 1 - βδ = a, and a ≥ 0 (since √ ≥ 0).
  have hsqrt_le_a : Real.sqrt (1 - R) ≤ a := by rw [hadef]; linarith
  have hsqrt_nn : 0 ≤ Real.sqrt (1 - R) := Real.sqrt_nonneg _
  have hann : 0 ≤ a := le_trans hsqrt_nn hsqrt_le_a
  -- KEY: Ustar ≤ U, i.e. 1 - a² ≤ U.  (Ustar = 1 - (1-βδ)² = 1 - a².)
  -- From √(1-R) ≤ a with both ≥ 0: 1 - R ≤ a², hence 1 - a² ≤ R.
  -- But R = β·((ℓ-1)/ℓ)·dmin = U.  So 1 - a² ≤ U.
  have hRU : R = U := by rw [hRdef, hUdef]; ring
  have hUstar : 1 - a ^ 2 ≤ U := by
    -- 1 - R ≤ a²
    have hsq : 1 - R ≤ a ^ 2 := by
      rcases le_or_gt (1 - R) 0 with hneg | hpos
      · nlinarith [sq_nonneg a]
      · have := Real.sq_sqrt hpos.le
        nlinarith [hsqrt_le_a, hsqrt_nn, Real.sq_sqrt hpos.le]
    -- so 1 - a² ≤ R = U
    rw [← hRU]; linarith
  -- The witness vectors.
  refine ⟨fun i => f (c i) - a • f y, U, ε, hεpos, hUε, ?_, ?_⟩
  · -- ‖v i‖² ≤ U
    intro i
    -- normDist (c i) y = normDist y (c i) ≤ δ
    have hei : (normDist (c i) y : ℝ) ≤ (δ : ℝ) := by
      rw [normDist_comm]; exact_mod_cast hclose i
    have hei_nn : (0 : ℝ) ≤ (normDist (c i) y : ℝ) := by exact_mod_cast normDist_nonneg (c i) y
    set ei : ℝ := (normDist (c i) y : ℝ) with heidef
    -- Expand ‖v i‖² via real_inner_self_eq_norm_sq.
    have hnormsq : ‖f (c i) - a • f y‖ ^ 2
        = @inner ℝ _ _ (f (c i) - a • f y) (f (c i) - a • f y) := by
      rw [← real_inner_self_eq_norm_sq]
    rw [hnormsq]
    -- bilinear expansion
    have hii : @inner ℝ _ _ (f (c i)) (f (c i)) = 1 := by
      rw [hf (c i) (c i)]; simp
    have hyy : @inner ℝ _ _ (f y) (f y) = 1 := by
      rw [hf y y]; simp
    have hiy : @inner ℝ _ _ (f (c i)) (f y) = 1 - β * ei := by
      rw [hf (c i) y]
    have hexpand : @inner ℝ _ _ (f (c i) - a • f y) (f (c i) - a • f y)
        = @inner ℝ _ _ (f (c i)) (f (c i))
          - a * @inner ℝ _ _ (f (c i)) (f y)
          - a * @inner ℝ _ _ (f y) (f (c i))
          + a * a * @inner ℝ _ _ (f y) (f y) := by
      rw [inner_sub_left, inner_sub_right, inner_sub_right]
      rw [inner_smul_left, inner_smul_left, inner_smul_right, inner_smul_right]
      simp only [conj_trivial]
      ring
    have hyi : @inner ℝ _ _ (f y) (f (c i)) = 1 - β * ei := by
      rw [real_inner_comm]; exact hiy
    rw [hexpand, hii, hyy, hiy, hyi]
    -- = 1 - 2a(1-βei) + a² = (1-a)² + 2aβ ei
    -- bound: ei ≤ δ, a ≥ 0, β ≥ 0; (1-a)² + 2aβ ei ≤ (1-a)² + 2aβδ
    -- and (1-a)² + 2aβδ = 1 - a² since a = 1 - βδ ⟹ βδ = 1 - a.
    -- So ‖v i‖² ≤ 1 - a² ≤ U.
    have hbd : a * a * 1 - a * (1 - β * ei) - a * (1 - β * ei)
        + 1 ≤ 1 - a ^ 2 := by
      -- βδ = 1 - a
      have hβδ : β * (δ : ℝ) = 1 - a := by rw [hadef]; ring
      nlinarith [hei, hei_nn, hann, hβpos.le, mul_nonneg hann hβpos.le]
    -- reorder LHS to match
    have hgoal : 1 - a * (1 - β * ei) - a * (1 - β * ei) + a * a * 1
        = a * a * 1 - a * (1 - β * ei) - a * (1 - β * ei) + 1 := by ring
    rw [hgoal]
    linarith [hbd, hUstar]
  · -- ⟨v i, v j⟩ ≤ -ε
    intro i j hij
    have hei : (normDist (c i) y : ℝ) ≤ (δ : ℝ) := by
      rw [normDist_comm]; exact_mod_cast hclose i
    have hej : (normDist (c j) y : ℝ) ≤ (δ : ℝ) := by
      rw [normDist_comm]; exact_mod_cast hclose j
    have hei_nn : (0 : ℝ) ≤ (normDist (c i) y : ℝ) := by exact_mod_cast normDist_nonneg (c i) y
    have hej_nn : (0 : ℝ) ≤ (normDist (c j) y : ℝ) := by exact_mod_cast normDist_nonneg (c j) y
    have hdij : (dmin : ℝ) ≤ (normDist (c i) (c j) : ℝ) := by exact_mod_cast hfar i j hij
    set ei : ℝ := (normDist (c i) y : ℝ) with heidef
    set ej : ℝ := (normDist (c j) y : ℝ) with hejdef
    set dij : ℝ := (normDist (c i) (c j) : ℝ) with hdijdef
    have hii : @inner ℝ _ _ (f (c i)) (f (c j)) = 1 - β * dij := by
      rw [hf (c i) (c j)]
    have hyy : @inner ℝ _ _ (f y) (f y) = 1 := by
      rw [hf y y]; simp
    have hiy : @inner ℝ _ _ (f (c i)) (f y) = 1 - β * ei := by
      rw [hf (c i) y]
    have hjy : @inner ℝ _ _ (f (c j)) (f y) = 1 - β * ej := by
      rw [hf (c j) y]
    have hexpand : @inner ℝ _ _ (f (c i) - a • f y) (f (c j) - a • f y)
        = @inner ℝ _ _ (f (c i)) (f (c j))
          - a * @inner ℝ _ _ (f (c i)) (f y)
          - a * @inner ℝ _ _ (f y) (f (c j))
          + a * a * @inner ℝ _ _ (f y) (f y) := by
      rw [inner_sub_left, inner_sub_right, inner_sub_right]
      rw [inner_smul_left, inner_smul_left, inner_smul_right, inner_smul_right]
      simp only [conj_trivial]
      ring
    have hyj : @inner ℝ _ _ (f y) (f (c j)) = 1 - β * ej := by
      rw [real_inner_comm]; exact hjy
    rw [hexpand, hii, hyy, hiy, hyj]
    -- = (1 - β dij) - 2a + a²(... ) + aβ(ei+ej)
    -- ⟨v i,v j⟩ = (1-a)² - β dij + aβ(ei+ej) ≤ (1-a)² - β dmin + 2aβδ
    --           = (1 - a²) - β dmin ≤ U - β dmin = -ε.
    have hβδ : β * (δ : ℝ) = 1 - a := by rw [hadef]; ring
    -- U - β dmin = -ε
    have hUmε : U - β * (dmin : ℝ) = -ε := by
      rw [hUdef, hεdef]; field_simp; ring
    -- a*β ≥ 0
    have haβ : 0 ≤ a * β := mul_nonneg hann hβpos.le
    -- aβ ei ≤ aβ δ, aβ ej ≤ aβ δ
    have hbei : a * β * ei ≤ a * β * (δ : ℝ) := by
      apply mul_le_mul_of_nonneg_left hei haβ
    have hbej : a * β * ej ≤ a * β * (δ : ℝ) := by
      apply mul_le_mul_of_nonneg_left hej haβ
    -- β dij ≥ β dmin
    have hbdij : β * (dmin : ℝ) ≤ β * dij := by
      apply mul_le_mul_of_nonneg_left hdij hβpos.le
    -- LHS = 1 - β dij - a(1-β ei) - a(1-β ej) + a²
    --     = (1 - 2a + a²) + aβ(ei+ej) - β dij
    --     = (1-a)² + aβ ei + aβ ej - β dij
    have hkey : (1 - β * dij) - a * (1 - β * ei) - a * (1 - β * ej) + a * a * 1
        = (1 - a) ^ 2 + a * β * ei + a * β * ej - β * dij := by ring
    -- (1-a)² + 2aβδ = 1 - a²  (using βδ = 1 - a)
    have hsq : (1 - a) ^ 2 + 2 * (a * β * (δ : ℝ)) = 1 - a ^ 2 := by
      have : a * β * (δ : ℝ) = a * (1 - a) := by rw [mul_assoc, hβδ]
      rw [this]; ring
    rw [hkey]
    -- chain the bounds
    have hstep : (1 - a) ^ 2 + a * β * ei + a * β * ej - β * dij
        ≤ (1 - a ^ 2) - β * (dmin : ℝ) := by
      have h1 : (1 - a) ^ 2 + a * β * ei + a * β * ej - β * dij
          ≤ (1 - a) ^ 2 + a * β * (δ:ℝ) + a * β * (δ:ℝ) - β * (dmin:ℝ) := by
        linarith [hbei, hbej, hbdij]
      have h2 : (1 - a) ^ 2 + a * β * (δ:ℝ) + a * β * (δ:ℝ) - β * (dmin:ℝ)
          = (1 - a ^ 2) - β * (dmin : ℝ) := by linarith [hsq]
      linarith [h1, h2]
    linarith [hstep, hUstar, hUmε]

end MCA.Code
