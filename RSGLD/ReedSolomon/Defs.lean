import Mathlib
import RSGLD.Code.Defs

/-!
# Reed–Solomon codes

`RS[F, L, k]` is the evaluation of degree-`< k` polynomials on the points of a
finite evaluation set `L ⊆ F`. (Definition 2.11.)

We define it as the image of `Polynomial.degreeLT F k` under the bundled
evaluation map `evalMap L`, so the result is a `Submodule` (hence a `LinearCode`)
with no extra work — `code_is_linear` is free.

The coordinates `Fin L.card → F` are indexed by a fixed bijection `L ≃ Fin L.card`
(`Finset.equivFin`); the particular ordering is irrelevant to the code as a set.
-/

namespace RSGLD.ReedSolomon

open Polynomial

variable {F : Type*} [Field F] [DecidableEq F]

/-- The evaluation points of `L`, indexed by `Fin L.card`. -/
noncomputable def evalPoints (L : Finset F) : Fin L.card → F :=
  fun i => (L.equivFin.symm i : F)

/-- Multi-point evaluation `p ↦ (i ↦ p(L i))` as an `F`-linear map. -/
noncomputable def evalMap (L : Finset F) : F[X] →ₗ[F] (Fin L.card → F) :=
  LinearMap.pi fun i => Polynomial.leval (evalPoints L i)

/-- The Reed–Solomon code `RS[F, L, k]`: evaluations of degree-`< k` polynomials.
(Definition 2.11.) Being a `Submodule.map`, it is automatically a linear code. -/
noncomputable def code (L : Finset F) (k : ℕ) : RSGLD.Code.LinearCode F L.card :=
  (Polynomial.degreeLT F k).map (evalMap L)

/-- The encoding of a message `m : Fin k → F` (its coefficient vector): build the
polynomial `∑ i, mᵢ Xⁱ` and evaluate. -/
noncomputable def encode (L : Finset F) (k : ℕ) (m : Fin k → F) : Fin L.card → F :=
  evalMap L (∑ i : Fin k, Polynomial.C (m i) * Polynomial.X ^ (i : ℕ))

omit [DecidableEq F] in
/-- An encoded message is a codeword. -/
theorem encode_mem_code (L : Finset F) (k : ℕ) (m : Fin k → F) :
    encode L k m ∈ code L k := by
  apply Submodule.mem_map_of_mem
  apply Submodule.sum_mem
  intro i _
  rw [Polynomial.mem_degreeLT]
  refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le (i : ℕ) (m i)) ?_
  exact_mod_cast i.is_lt

end RSGLD.ReedSolomon
