import Mathlib
import RSGLD.Code.ListDecode
import RSGLD.Code.Interleaved
import RSGLD.ReedSolomon.MDS
import RSGLD.ListDecoding.TreeCount
import RSGLD.ListDecoding.GGRComposition

/-!
# GGR interleaving list-size bound

Paper **Lemma 2.10** (eprint 2026/680) = **Gopalan–Guruswami–Raghavendra, Theorem 2.5**
(arXiv:0811.4395; the tree leaf-count is their **Theorem 3.6**). For an arbitrary code `C` it
bounds the interleaved list size by the *base* list size, with a factor **independent of `m`**. It
is proved via the erase-decode tree (not the rank / generalized-Hamming-weight route).

## Notation (paper ↔ repo)

The paper's `δ` is the code's relative distance (`minDist C`); the paper's `η` is the
list-decoding radius (the `maxListSize` argument, a `ℚ`). The gap is `minDist C − η`.

## Statement

`interleave_list_size_ggr` is parameterized by `b r : ℕ` via the inequalities
`η ≤ b·(minDist C − η)` and `minDist C ≤ 2^r·(minDist C − η)`, with conclusion
`|Λ(C^{≡m}, η)| ≤ Nat.choose (b+r) r · |Λ(C, η)|^r`. The base list size enters only as the opaque
per-node fan-out `Λ := |Λ(C, η)|`.

The proof lives in `GGRComposition.lean` (count decomposition, fan-out, induction `Ninter_le`, and
the `maxListSize` bridge `maxListSize_interleave_le_int`), `EraseDecode.lean` (the erase-decode
leaves and the budget invariant), and `TreeCount.lean` (the tree leaf-count `treeLeaves_le`); this
file re-exports the core integer theorem. The base-RS list size `|Λ(C, E/n)|` stays an opaque
parameter — the reduction needs no base-RS beyond-Johnson math (that is the separate open frontier,
`research/gld_literature_map.md`).
-/

namespace RSGLD.ListDecoding

open RSGLD.Code RSGLD.ReedSolomon

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

end RSGLD.ListDecoding
