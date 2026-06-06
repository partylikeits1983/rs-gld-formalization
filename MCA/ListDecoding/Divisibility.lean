import Mathlib
import MCA.ReedSolomon.Defs

/-!
# The gcd / divisibility route for interleaved RS list decoding

The structural source of any *potential* improvement of interleaving over the plain
Johnson bound (eprint 2026/680, roadmap G): if two interleaved RS codewords
`Fvec, Gvec` agree on a large set `S ⊆ L`, then every coordinate difference
`h_i := f_i − g_i` vanishes on `S`, hence is divisible by the common scalar factor
`D_S := ∏_{x∈S}(X − x)`; and the space of degree-`<k` vector polynomials divisible by
a fixed monic `D` of degree `d` collapses in dimension by `m·d`.

## Honesty (CLAUDE epistemic law)

This is genuine structure, but it does **not** beat the frontier: paper Lemma 2.10 is
`m`-independent, i.e. the `m`-fold dimension penalty proved here (GLD-8) is exactly
offset by the adversary's `m`-fold extra freedom in choosing the received word. So
these lemmas are recorded scaffolding; the near-capacity prize stays external.

## Leaves
* `vanish_prod_X_sub_C_dvd` / `vec_diff_vanish_dvd` — GLD-7.
* `dim_degreeLT_dvd_eq` (scalar) and `dim_vecPoly_dvd_eq` (`m`-fold) — GLD-8.
-/

namespace MCA.ListDecoding

open Polynomial

variable {F : Type*} [Field F] [DecidableEq F]

/-! ### GLD-7 — vanishing on `S` forces divisibility by `∏_{x∈S}(X − x)` -/

/-- A polynomial vanishing at every point of a finite set `S` is divisible by the
separable product `∏_{x∈S}(X − x)`. (The distinct roots `S` sit inside `h.roots`.) -/
theorem vanish_prod_X_sub_C_dvd {S : Finset F} {h : F[X]}
    (hv : ∀ x ∈ S, h.eval x = 0) :
    (∏ x ∈ S, (X - C x)) ∣ h := by
  rcases eq_or_ne h 0 with rfl | hne
  · exact dvd_zero _
  · have hform : (∏ x ∈ S, (X - C x)) = (S.val.map fun a => X - C a).prod := rfl
    rw [hform, Multiset.prod_X_sub_C_dvd_iff_le_roots hne, Multiset.le_iff_count]
    intro a
    by_cases ha : a ∈ S
    · rw [Multiset.count_eq_one_of_mem S.nodup (Finset.mem_val.mpr ha), Polynomial.count_roots]
      exact (Polynomial.rootMultiplicity_pos hne).mpr (hv a ha)
    · rw [Multiset.count_eq_zero.mpr (fun hc => ha (Finset.mem_val.mp hc))]
      exact Nat.zero_le _

/-- Vector form (roadmap G.1): if two `m`-tuples of polynomials agree at every point
of `S`, then `∏_{x∈S}(X − x)` divides every coordinate difference `P i − Q i`. -/
theorem vec_diff_vanish_dvd {S : Finset F} {m : ℕ} {P Q : Fin m → F[X]}
    (hv : ∀ x ∈ S, ∀ i, (P i).eval x = (Q i).eval x) (i : Fin m) :
    (∏ x ∈ S, (X - C x)) ∣ (P i - Q i) := by
  apply vanish_prod_X_sub_C_dvd
  intro x hx
  rw [Polynomial.eval_sub, hv x hx i, sub_self]

/-! ### GLD-8 — the dimension collapse for `D`-divisible degree-`<k` polynomials -/

/-- Multiples of `D`, as an `F`-submodule of `F[X]`. -/
def dvdSubmodule (D : F[X]) : Submodule F F[X] where
  carrier := {p | D ∣ p}
  add_mem' := fun ha hb => dvd_add ha hb
  zero_mem' := dvd_zero _
  smul_mem' := fun a p hp => by
    simp only [Set.mem_setOf_eq, Polynomial.smul_eq_C_mul]
    exact hp.mul_left _

@[simp] theorem mem_dvdSubmodule {D p : F[X]} : p ∈ dvdSubmodule D ↔ D ∣ p := Iff.rfl

/-- Degree-`<k` polynomials divisible by `D`. -/
noncomputable def degreeLTDvd (D : F[X]) (k : ℕ) : Submodule F F[X] :=
  Polynomial.degreeLT F k ⊓ dvdSubmodule D

theorem mem_degreeLTDvd {D p : F[X]} {k : ℕ} :
    p ∈ degreeLTDvd D k ↔ p.degree < k ∧ D ∣ p := by
  rw [degreeLTDvd, Submodule.mem_inf, Polynomial.mem_degreeLT, mem_dvdSubmodule]

/-- Multiplication-by-`D` as an `F`-linear map `F[X] →ₗ[F] F[X]`. -/
noncomputable def mulByD (D : F[X]) : F[X] →ₗ[F] F[X] where
  toFun := fun p => p * D
  map_add' := fun a b => by ring
  map_smul' := fun a p => by
    simp only [Polynomial.smul_eq_C_mul, RingHom.id_apply]; ring

/-- The `F`-linear isomorphism `degreeLT F (k-d) ≃ₗ[F] degreeLTDvd D k` given by
multiplication by the monic polynomial `D` of degree `d` (`d ≤ k`). -/
noncomputable def mulByDEquiv {D : F[X]} (hD : D.Monic) {d k : ℕ}
    (hd : D.natDegree = d) (hdk : d ≤ k) :
    (Polynomial.degreeLT F (k - d)) ≃ₗ[F] (degreeLTDvd D k) := by
  have hDne : D ≠ 0 := hD.ne_zero
  -- the linear map restricted to the subspace, landing in degreeLTDvd
  refine LinearEquiv.ofBijective
    (LinearMap.codRestrict (degreeLTDvd D k)
      ((mulByD D).domRestrict (Polynomial.degreeLT F (k - d))) ?_) ⟨?_, ?_⟩
  · -- lands in degreeLTDvd
    rintro ⟨p, hp⟩
    rw [Polynomial.mem_degreeLT] at hp
    rw [mem_degreeLTDvd]
    refine ⟨?_, Dvd.intro_left p rfl⟩
    simp only [LinearMap.domRestrict_apply, mulByD, LinearMap.coe_mk, AddHom.coe_mk]
    rcases eq_or_ne p 0 with rfl | hpne
    · simp
    · have hpd : p.degree < (k - d : ℕ) := hp
      have hDd : D.degree = (d : ℕ) := by
        rw [Polynomial.degree_eq_natDegree hDne, hd]
      rw [Polynomial.degree_mul, hDd]
      -- p.degree + d < k
      have hstep : (p.degree) + (d : ℕ) < ((k - d : ℕ) : WithBot ℕ) + (d : ℕ) :=
        WithBot.add_lt_add_right (by simp) hpd
      have hcast : ((k - d : ℕ) : WithBot ℕ) + (d : ℕ) = ((k : ℕ) : WithBot ℕ) := by
        rw [← Nat.cast_add, Nat.sub_add_cancel hdk]
      rwa [hcast] at hstep
  · -- injective
    rintro ⟨p, hp⟩ ⟨q, hq⟩ heq
    rw [Subtype.ext_iff] at heq
    simp only [LinearMap.codRestrict_apply, LinearMap.domRestrict_apply, mulByD,
      LinearMap.coe_mk, AddHom.coe_mk] at heq
    have hpq : p = q := mul_right_cancel₀ hDne heq
    rw [Subtype.mk.injEq]; exact hpq
  · -- surjective
    rintro ⟨q, hq⟩
    rw [mem_degreeLTDvd] at hq
    obtain ⟨hqdeg, hqdvd⟩ := hq
    -- p := q /ₘ D
    refine ⟨⟨q /ₘ D, ?_⟩, ?_⟩
    · rw [Polynomial.mem_degreeLT]
      -- degree (q /ₘ D) < k - d
      rcases eq_or_ne q 0 with rfl | hqne
      · simp only [Polynomial.zero_divByMonic]
        rw [Polynomial.degree_zero]
        exact WithBot.bot_lt_coe _
      · -- q = (q /ₘ D) * D, degree q = degree (q/ₘD) + d
        have hmul : q = (q /ₘ D) * D := by
          have hz := (Polynomial.modByMonic_eq_zero_iff_dvd hD).mpr hqdvd
          conv_lhs => rw [← Polynomial.modByMonic_add_div q D]
          rw [hz, zero_add, mul_comm]
        have hdivne : q /ₘ D ≠ 0 := by
          intro h; rw [h, zero_mul] at hmul; exact hqne hmul
        have hdegq : q.degree = (q /ₘ D).degree + (d : ℕ) := by
          conv_lhs => rw [hmul]
          rw [Polynomial.degree_mul, Polynomial.degree_eq_natDegree hDne, hd]
        rw [hdegq] at hqdeg
        -- (q/ₘD).degree + d < k  ⟹ (q/ₘD).degree < k - d
        have hk : ((k : ℕ) : WithBot ℕ) = ((k - d : ℕ) : WithBot ℕ) + (d : ℕ) := by
          rw [← Nat.cast_add, Nat.sub_add_cancel hdk]
        rw [hk] at hqdeg
        exact (WithBot.add_lt_add_iff_right (by simp)).mp hqdeg
    · rw [Subtype.ext_iff]
      simp only [LinearMap.codRestrict_apply, LinearMap.domRestrict_apply, mulByD,
        LinearMap.coe_mk, AddHom.coe_mk]
      -- (q /ₘ D) * D = q
      have hmul : q = (q /ₘ D) * D := by
        have hz := (Polynomial.modByMonic_eq_zero_iff_dvd hD).mpr hqdvd
        conv_lhs => rw [← Polynomial.modByMonic_add_div q D]
        rw [hz, zero_add, mul_comm]
      exact hmul.symm

/-- GLD-8 scalar: the dimension of degree-`<k` polynomials divisible by a monic `D` of
degree `d` (`d ≤ k`) collapses to `k - d`. -/
theorem dim_degreeLT_dvd_eq {D : F[X]} (hD : D.Monic) {d k : ℕ}
    (hd : D.natDegree = d) (hdk : d ≤ k) :
    Module.finrank F (degreeLTDvd D k) = k - d := by
  rw [← LinearEquiv.finrank_eq (mulByDEquiv hD hd hdk)]
  rw [LinearEquiv.finrank_eq (Polynomial.degreeLTEquiv F (k - d))]
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

/-- The `F`-linear isomorphism `(Submodule.pi univ (fun _ => W)) ≃ₗ[F] (Fin m → W)` for a
fixed submodule `W`, where the codomain carries the pointwise module structure. -/
noncomputable def piConstEquiv {m : ℕ} (W : Submodule F F[X]) :
    (Submodule.pi (Set.univ : Set (Fin m)) (fun _ => W)) ≃ₗ[F] (Fin m → W) where
  toFun := fun x i => ⟨(x : Fin m → F[X]) i, by
    have hx := x.2
    rw [Submodule.mem_pi] at hx
    exact hx i (Set.mem_univ i)⟩
  map_add' := fun a b => by ext i; rfl
  map_smul' := fun c a => by ext i; rfl
  invFun := fun y => ⟨fun i => (y i : F[X]), by
    rw [Submodule.mem_pi]
    intro i _
    exact (y i).2⟩
  left_inv := fun x => by ext i; rfl
  right_inv := fun y => by ext i; rfl

/-- GLD-8 m-fold: the `F`-dimension of `m`-tuples of degree-`<k` polynomials, each divisible
by a monic `D` of degree `d` (`d ≤ k`), is `m · (k - d)`. -/
theorem dim_vecPoly_dvd_eq {D : F[X]} (hD : D.Monic) {d k : ℕ}
    (hd : D.natDegree = d) (hdk : d ≤ k) (m : ℕ) :
    Module.finrank F (Submodule.pi (Set.univ : Set (Fin m)) (fun _ => degreeLTDvd D k))
      = m * (k - d) := by
  -- `degreeLT F k` is finite-dimensional (≃ₗ Fin k → F), hence so is its submodule.
  haveI hfin : FiniteDimensional F (Polynomial.degreeLT F k) :=
    (Polynomial.degreeLTEquiv F k).symm.finiteDimensional
  haveI : FiniteDimensional F (degreeLTDvd D k) := by
    unfold degreeLTDvd; infer_instance
  haveI : Module.Free F (degreeLTDvd D k) := Module.Free.of_divisionRing F (degreeLTDvd D k)
  rw [LinearEquiv.finrank_eq (piConstEquiv (degreeLTDvd D k))]
  rw [Module.finrank_pi_fintype]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [dim_degreeLT_dvd_eq hD hd hdk]

end MCA.ListDecoding
