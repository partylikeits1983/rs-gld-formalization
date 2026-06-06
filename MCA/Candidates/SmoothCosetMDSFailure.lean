import Mathlib

/-!
# Higher-order-MDS obstruction for smooth multiplicative cosets

This file records the **core algebraic mechanism** behind the finding that
`RS[μ_{2^s}, k]` fails higher-order MDS, `MDS(ℓ)`, for every `ℓ ≥ 3`
(`research/smooth_coset_mds_failure.md`, `research/smooth_coset_mds3_target.md`).

Setup: `L = μ_n = ⟨ω⟩`, `n = 2^s ∣ q−1`. For a 2-power `d ∣ n`, a coset `ω^t·H_d` of the
order-`d` subgroup `H_d` has **vanishing polynomial the binomial `X^d − ω^{td}`** (because
`∏_{ζ^d=1}(X − ω^t ζ) = X^d − ω^{td}`). All such binomials live in the **2-dimensional**
`span{1, X^d}`. Hence any THREE of them are linearly dependent — which is exactly the failure
of the intersection-dimension (`MDS(ℓ)`) condition that the generic/random-RS capacity proofs
(BGM, AGGLZ) rely on. So that capacity machinery **cannot be imported** to smooth cosets.

**Honesty law (project CLAUDE.md).** This is a *structural / method* obstruction, label
`proved` (the dependence identity below) for the algebra and
`experimentally-supported` for the `MDS(ℓ)`-failure framing. It is **NOT** a list-size
counterexample: the associated Hamming-ball list is only `O(1/ρ)` (a constant), and the
defect-bearing witness `w = (x^d)` sits *above* capacity — see
`research/smooth_coset_mds_failure.md`. No claim crosses `H_q⁻¹(1−ρ)`. Lives in the
axiom/sorry-exempt `MCA.Candidates` zone; in fact it is sorry-free and axiom-clean.
-/

namespace MCA.Candidates.SmoothCosetMDS

variable {F : Type*} [Field F]

/-- Coefficient vector (indices `0..d`) of the binomial `X^d − c`: top coefficient `1` at the
`X^d` slot, constant term `−c`, all middle coefficients `0`. This is the vanishing polynomial of
a coset `ω^t·H_d` of the order-`d` (2-power) subgroup of `μ_n`, with `c = ω^{td}`. -/
def binom (d : ℕ) (c : F) : Fin (d + 1) → F :=
  fun j => (if (j : ℕ) = d then (1 : F) else 0) - c * (if (j : ℕ) = 0 then (1 : F) else 0)

/-- **Higher-order-MDS obstruction (core algebraic mechanism), provable & axiom-clean.**
Any three binomials `X^d − c₀, X^d − c₁, X^d − c₂` satisfy an explicit linear dependence with
coefficients `(c₁−c₂, c₂−c₀, c₀−c₁)`. These coefficients are *not all zero* exactly when the
`cᵢ` are not all equal (distinct cosets ⇒ distinct `cᵢ`), so for three distinct cosets the
dependence is nontrivial: the three vanishing polynomials are linearly dependent. This is why
`dim(G_{A₀} ∩ G_{A₁} ∩ G_{A₂})` exceeds its generic value, i.e. `MDS(3)` fails — and, by the
same `span{1, X^d}` argument, `MDS(ℓ)` fails for all `ℓ ≥ 3`. -/
theorem binom_three_dependent (d : ℕ) (c : Fin 3 → F) :
    (c 1 - c 2) • binom d (c 0) + (c 2 - c 0) • binom d (c 1) + (c 0 - c 1) • binom d (c 2) = 0 := by
  funext j
  simp only [binom, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  ring

/-- The dependence is **nontrivial** when the three cosets are distinct: at least one coefficient
`(c₁−c₂, c₂−c₀, c₀−c₁)` is nonzero. (If all three vanished, `c₀ = c₁ = c₂`.) Together with
`binom_three_dependent` this is the precise statement that three distinct-coset vanishing
binomials are linearly dependent — the `MDS(3)` failure. -/
theorem binom_three_coeffs_nontrivial (c : Fin 3 → F)
    (h : c 0 ≠ c 1 ∨ c 1 ≠ c 2 ∨ c 0 ≠ c 2) :
    (c 1 - c 2) ≠ 0 ∨ (c 2 - c 0) ≠ 0 ∨ (c 0 - c 1) ≠ 0 := by
  rcases h with h | h | h
  · exact Or.inr (Or.inr (sub_ne_zero.mpr h))            -- c₀ ≠ c₁ ⇒ c₀−c₁ ≠ 0
  · exact Or.inl (sub_ne_zero.mpr h)                      -- c₁ ≠ c₂ ⇒ c₁−c₂ ≠ 0
  · exact Or.inr (Or.inl (sub_ne_zero.mpr (Ne.symm h)))  -- c₀ ≠ c₂ ⇒ c₂−c₀ ≠ 0

end MCA.Candidates.SmoothCosetMDS
