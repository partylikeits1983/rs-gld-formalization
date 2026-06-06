import Mathlib

/-!
# Johnson functions (Definition 3.1)

Definition 3.1 of Arnon–Boneh–Fenzi (2026) (`references/core/2026-680.pdf`,
~line 682) introduces three successively rougher Johnson bounds
`Jq,ℓ , Jq , J : (0,1) → ℝ`. We define them honestly as real-valued functions; they
are used to *state* the Johnson-radius theorems (Thm 3.2, Cor 3.3, Thm 4.12, Thm
4.18). No theorem about them is proved here.

Paper Definition 3.1 (verbatim, `q, ℓ ∈ ℕ`):

* `Jq,ℓ(δ) = (1 − 1/q)·(1 − √(1 − (q/(q−1))·((ℓ−1)/ℓ)·δ))`
* `Jq(δ)  = limℓ→∞ Jq,ℓ(δ) = (1 − 1/q)·(1 − √(1 − (q/(q−1))·δ))`
* `J(δ)   = limq→∞ Jq(δ)   = 1 − √(1 − δ)`

The coarsest bound `J(δ) = 1 − √(1 − δ)` is the field-size-independent Johnson
radius, the relevant frontier for the grand challenge (`J(δmin) = 1 − √ρ` for an
MDS code with `δmin = 1 − ρ`). It is the only one needed to phrase the open-band
brackets, but all three are recorded for faithfulness.
-/

namespace MCA.Code

/-- The coarsest Johnson function `J(δ) = 1 − √(1 − δ)` (Definition 3.1, the
`q → ∞` limit). For an MDS code of rate `ρ` (so `δmin = 1 − ρ`), the Johnson radius
is `J(1 − ρ) = 1 − √ρ`. -/
noncomputable def johnsonJ (δ : ℝ) : ℝ := 1 - Real.sqrt (1 - δ)

/-- The field-size-aware Johnson function `Jq(δ) = (1 − 1/q)·(1 − √(1 − (q/(q−1))·δ))`
(Definition 3.1, the `ℓ → ∞` limit). -/
noncomputable def johnsonJq (q : ℕ) (δ : ℝ) : ℝ :=
  (1 - 1 / (q : ℝ)) * (1 - Real.sqrt (1 - (q : ℝ) / ((q : ℝ) - 1) * δ))

/-- The finest Johnson function `Jq,ℓ(δ) = (1 − 1/q)·(1 − √(1 − (q/(q−1))·((ℓ−1)/ℓ)·δ))`
(Definition 3.1). The `(ℓ−1)/ℓ = 1 − 1/ℓ` factor (NOT `ℓ/(ℓ−1)`) is the correct one:
`Jq,ℓ` must increase in `ℓ` toward `Jq` (a larger list budget tolerates a larger
radius), and it is the factor in GRS *Essential Coding Theory* Ex. 7.8 (the
bounded-list q-ary Johnson bound). The inverted factor made `johnson_bound`'s
`ε = β·dmin − U` negative and the leaf unprovable (critic-confirmed 2026-05-26). -/
noncomputable def johnsonJqℓ (q ℓ : ℕ) (δ : ℝ) : ℝ :=
  (1 - 1 / (q : ℝ)) *
    (1 - Real.sqrt (1 - (q : ℝ) / ((q : ℝ) - 1) * (((ℓ : ℝ) - 1) / (ℓ : ℝ)) * δ))

end MCA.Code
