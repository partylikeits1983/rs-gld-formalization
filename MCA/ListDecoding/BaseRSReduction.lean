import Mathlib
import MCA.ListDecoding.InterleavedListSize
import MCA.ListDecoding.Interleaved
import MCA.ListDecoding.Prize

/-!
# The grand challenge reduces to the base-RS frontier (UNCONDITIONAL)

This file makes the central honesty fact a **theorem**: the only thing standing between
the repo and the interleaved-RS prize is a bound on the *base* RS list size
`|Λ(RS[F,L,k], E/n)|`. Everything else (the `m`-interleaving) is discharged by the now-**proved**
GGR Lemma 2.10 (`interleave_list_size_ggr`, GLD-9), whose bound is **independent of `m`**.

* `interleave_list_le_of_base_bound` — feeds a base bound `B` through GGR 2.10 to get an
  interleaved bound `Nat.choose (b+r) r · B^r`.
* `interleavedRS_prize_of_base_bound` — chains that with the integer prize-implication
  (GLD-5): a base-RS bound `B` plus a field-size condition gives the prize inequality
  `2^128·|Λ(C^{≡m}, E/n)| ≤ |F|`.

**Status: UNCONDITIONAL (axiom-clean).** GLD-9 is now proved (erase-decode tree, `MCA/ListDecoding/`),
so these no longer depend on any `sorry`. The base bound `B` at radii `E/n > 1−√ρ` is the genuinely
OPEN input (literature triage: `research/gld_literature_map.md` — not importable, not
resolved-negative for fixed smooth-domain RS). Below Johnson, `B` is supplied by `mds_list_bound`;
the certified statement there is `MCA.ListDecoding.interleavedRS_prize_at_johnson`.
-/

namespace MCA.ListDecoding

open MCA.Code MCA.ReedSolomon

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]

/-- **Reduction (unconditional).** A base-code list bound `maxListSize C (E/n) ≤ B` propagates
through the `m`-independent GGR bound to `maxListSize (C^{≡m}) (E/n) ≤ Nat.choose (b+r) r · B^r`.
The interleaving order `m` appears nowhere on the right — the obstruction is entirely the
base bound `B`. -/
theorem interleave_list_le_of_base_bound {n : ℕ} (C : LinearCode F n) [Fintype C]
    (m : ℕ) [Fintype (interleave C m)] (hn : 0 < n)
    (D E b r : ℕ) (hED : E < D) (hD : (D : ℝ) ≤ minDist C * n)
    (hb : E ≤ b * (D - E)) (hr : D ≤ 2 ^ r * (D - E))
    (B : ℕ) (hBase : maxListSize C ((E : ℚ) / n) ≤ B) :
    maxListSize (interleave C m) ((E : ℚ) / n) ≤ Nat.choose (b + r) r * B ^ r := by
  calc maxListSize (interleave C m) ((E : ℚ) / n)
      ≤ Nat.choose (b + r) r * (maxListSize C ((E : ℚ) / n)) ^ r :=
        interleave_list_size_ggr C m hn D E b r hED hD hb hr
    _ ≤ Nat.choose (b + r) r * B ^ r := by gcongr

/-- **The interleaved-RS prize condition from a base-RS bound (unconditional).** Given a base-RS
list bound `B` at radius `E/n` and a field large enough that `2^128·(Nat.choose (b+r) r·B^r) ≤ |F|`,
the prize inequality `2^128·|Λ(C^{≡m}, E/n)| ≤ |F|` holds. The sole open input is `B`; for radius
`E/n` above Johnson it is external open math. -/
theorem interleavedRS_prize_of_base_bound (L : Finset F) (k : ℕ)
    [Fintype (code L k)] (m : ℕ) [Fintype (interleave (code L k) m)] (hn : 0 < L.card)
    (D E b r : ℕ) (hED : E < D) (hD : (D : ℝ) ≤ minDist (code L k) * L.card)
    (hb : E ≤ b * (D - E)) (hr : D ≤ 2 ^ r * (D - E))
    (B : ℕ) (hBase : maxListSize (code L k) ((E : ℚ) / L.card) ≤ B)
    (hField : 2 ^ 128 * (Nat.choose (b + r) r * B ^ r) ≤ Fintype.card F) :
    2 ^ 128 * maxListSize (interleavedRS L k m) ((E : ℚ) / L.card) ≤ Fintype.card F := by
  have h : maxListSize (interleavedRS L k m) ((E : ℚ) / L.card) ≤ Nat.choose (b + r) r * B ^ r :=
    interleave_list_le_of_base_bound (code L k) m hn D E b r hED hD hb hr B hBase
  exact list_bound_implies_grand_condition L k m ((E : ℚ) / L.card)
    (Nat.choose (b + r) r * B ^ r) h hField

end MCA.ListDecoding
