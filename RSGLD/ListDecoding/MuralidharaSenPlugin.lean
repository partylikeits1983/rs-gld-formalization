import Mathlib
import RSGLD.ListDecoding.BaseRSReduction

/-!
# Muralidhara–Sen plug-in: a slightly-above-Johnson field-size condition

**External input (cited, NOT formalized here).** Muralidhara & Sen, *Improvements on the Johnson
Bound for Reed–Solomon Codes*, Discrete Applied Math 156(6), 2008 (Thm 2.4 / Cor 2.5): for
`RS[F,L,k]` at error radius `E = n − √(nk) + c` — strictly above the Johnson radius `n − √(nk)` by
the additive constant `c` (relative `c/n`) — the worst-case list size is polynomial,
```
    B_C(E) := maxListSize C (E/n) ≤ n^D,
```
for every distinct evaluation set (hence every smooth multiplicative coset `L = a·μ_{2^s}`) and
independently of `q`.

This file does the **composition only** (the Muralidhara–Sen bound is held as a hypothesis):
- `interleaved_field_size_condition_of_base_poly_bound` — the general plug-in: a polynomial base
  bound `B_C(E) ≤ n^D` gives the interleaved field-size condition via the proved GGR reduction.
- `gld_field_size_slightly_above_johnson_of_MS` — the same at the Muralidhara–Sen radius
  `E = n − Nat.sqrt(n·k) + c`, with the Muralidhara–Sen bound as an explicit hypothesis.

**Scope.** The radius is above Johnson by only the additive `c` (relative `c/n`, vanishing as
`n → ∞`) — not a constant-relative improvement. It does not resolve the largest decodable `δ*`.
-/

namespace RSGLD.ListDecoding

open RSGLD.Code RSGLD.ReedSolomon

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]

/-- **Plug-in (general, conditional).** A *polynomial* base list bound `maxListSize C (E/n) ≤ n^D`
at an above-Johnson radius `E`, together with the GGR integer budget conditions and a field-size
condition `2^128 · choose(b+r,r) · n^{D·r} ≤ |F|`, yields `2^128 · |Λ(C^{≡m}, E/n)| ≤ |F|` for
**every** code `C`. Discharges to the proved reduction `interleave_list_le_of_base_bound`. -/
theorem interleaved_field_size_condition_of_base_poly_bound {n : ℕ} (C : LinearCode F n) [Fintype C]
    (m : ℕ) [Fintype (interleave C m)] (hn : 0 < n)
    (Dmin E b r D : ℕ) (hED : E < Dmin) (hD : (Dmin : ℝ) ≤ minDist C * n)
    (hb : E ≤ b * (Dmin - E)) (hr2 : Dmin ≤ 2 ^ r * (Dmin - E))
    (hMS : maxListSize C ((E : ℚ) / n) ≤ n ^ D)
    (hField : 2 ^ 128 * (Nat.choose (b + r) r * n ^ (D * r)) ≤ Fintype.card F) :
    2 ^ 128 * maxListSize (interleave C m) ((E : ℚ) / n) ≤ Fintype.card F := by
  have hpow : (n ^ D) ^ r = n ^ (D * r) := by rw [← pow_mul]
  have h1 : maxListSize (interleave C m) ((E : ℚ) / n)
      ≤ Nat.choose (b + r) r * n ^ (D * r) := by
    have := interleave_list_le_of_base_bound C m hn Dmin E b r hED hD hb hr2 (n ^ D) hMS
    rwa [hpow] at this
  calc 2 ^ 128 * maxListSize (interleave C m) ((E : ℚ) / n)
      ≤ 2 ^ 128 * (Nat.choose (b + r) r * n ^ (D * r)) := by gcongr
    _ ≤ Fintype.card F := hField

/-- **Plug-in at the Muralidhara–Sen radius (slightly above Johnson).** At the integer error radius
`E = n − Nat.sqrt(n·k) + c` (strictly above the Johnson radius `n − √(nk)` by the additive `c ≥ 1`),
the assumed bound `MS_bound : maxListSize C (E/n) ≤ n^D` and the field-size condition give
`2^128 · |Λ(C^{≡m}, E/n)| ≤ |F|`. `MS_bound` is the external Muralidhara–Sen theorem, held as a
hypothesis (provenance above). -/
theorem gld_field_size_slightly_above_johnson_of_MS {n : ℕ} (C : LinearCode F n) [Fintype C]
    (m : ℕ) [Fintype (interleave C m)] (hn : 0 < n) (k c : ℕ) (_hc : 1 ≤ c)
    (Dmin b r D : ℕ)
    (E : ℕ) (_hEdef : E = n - Nat.sqrt (n * k) + c)
    (hED : E < Dmin) (hD : (Dmin : ℝ) ≤ minDist C * n)
    (hb : E ≤ b * (Dmin - E)) (hr2 : Dmin ≤ 2 ^ r * (Dmin - E))
    (MS_bound : maxListSize C ((E : ℚ) / n) ≤ n ^ D)
    (hField : 2 ^ 128 * (Nat.choose (b + r) r * n ^ (D * r)) ≤ Fintype.card F) :
    2 ^ 128 * maxListSize (interleave C m) ((E : ℚ) / n) ≤ Fintype.card F :=
  interleaved_field_size_condition_of_base_poly_bound C m hn Dmin E b r D hED hD hb hr2 MS_bound hField

end RSGLD.ListDecoding
