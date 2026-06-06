import Mathlib
import MCA.Code.ListDecode
import MCA.Code.Interleaved
import MCA.ReedSolomon.MDS
import MCA.ListDecoding.TreeCount
import MCA.ListDecoding.GGRComposition

/-!
# GGR interleaving list-size bound (GLD-9) — erase-decode tree, in-repo target

Paper **Lemma 2.10** (eprint 2026/680) = **Gopalan–Guruswami–Raghavendra, Theorem 2.5**
(arXiv:0811.4395; the tree leaf-count is their **Theorem 3.6**). For an arbitrary code `C` it bounds
the interleaved list size by the *base* list size, with a factor **independent of `m`**. Provable
in-repo by the erase-decode tree (NOT the rank/generalized-Hamming-weight route, which is GGR's
binary-only Thms 2.6–2.9). Plan + leaf decomposition: `research/ggr_2_10_proof_plan.md`.

## Notation (paper ↔ repo)

The paper's `δ` is the code's **relative distance** = `minDist C` here; the paper's `η` is the
**list-decoding radius** = the `maxListSize` argument here (a `ℚ`). The gap is `minDist C − η`.

## Two-tier statement (per expert directive — parameterize by inequalities, defer logs)

* **Core** (`interleave_list_size_ggr`): parameterized by `b r : ℕ` via the **inequalities**
  `η ≤ b·(minDist C − η)` and `minDist C ≤ 2^r·(minDist C − η)`. Conclusion
  `|Λ(C^{≡m}, η)| ≤ Nat.choose (b+r) r · |Λ(C, η)|^r`. No logs/ceilings inside the proof; the base
  list size enters only as the opaque per-node fan-out `Λ := |Λ(C, η)|`.
* **Corollary** (to be added once the core is proved): instantiate `b = ⌈η/(minDist−η)⌉`,
  `r = ⌈log₂(minDist/(minDist−η))⌉` (equivalently `minDist/2^r ≤ minDist−η`).

## Status: PROVED (axiom-clean) — discharged by the erase-decode tree

All leaves landed in `MCA/ListDecoding/`: L7 `treeLeaves_le` (`TreeCount.lean`); L1′–L6 + the
invariant in `EraseDecode.lean`; the count decomposition, fan-out, induction `Ninter_le`, and the
`maxListSize` bridge `maxListSize_interleave_le_int` in `GGRComposition.lean`. This file now just
re-exports the core integer theorem under the GLD-9 name — **no `sorry`**. `BaseRSReduction.lean`
(GLD-11) is therefore **unconditional**.

The base-RS list size `|Λ(C, E/n)|` stays an opaque parameter — GGR Thm 2.5 needs **no** base-RS
beyond-Johnson math (that is the separate external/open frontier, `research/gld_literature_map.md`).
-/

namespace MCA.ListDecoding

open MCA.Code MCA.ReedSolomon

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]

/-- **GGR Thm 2.5 / paper Lemma 2.10 — integer parameterized, PROVED.** For a code `C`, integer
error radius `E < D` with `D ≤ minDist C · n`, and `b r : ℕ` with `E ≤ b·(D−E)` and
`D ≤ 2^r·(D−E)`: `|Λ(C^{≡m}, E/n)| ≤ Nat.choose (b+r) r · |Λ(C, E/n)|^r`. The bound is independent of
`m`. Proved via the erase-decode tree (`maxListSize_interleave_le_int`). -/
theorem interleave_list_size_ggr {n : ℕ} (C : LinearCode F n) [Fintype C]
    (m : ℕ) [Fintype (interleave C m)] (hn : 0 < n)
    (D E b r : ℕ) (hED : E < D) (hD : (D : ℝ) ≤ minDist C * n)
    (hb : E ≤ b * (D - E)) (hr : D ≤ 2 ^ r * (D - E)) :
    maxListSize (interleave C m) ((E : ℚ) / n)
      ≤ Nat.choose (b + r) r * (maxListSize C ((E : ℚ) / n)) ^ r :=
  maxListSize_interleave_le_int C m hn D E b r hED hD hb hr

end MCA.ListDecoding
