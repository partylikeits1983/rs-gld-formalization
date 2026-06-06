-- Core code/Hamming/list-decoding infrastructure
import MCA.Code.Hamming
import MCA.Code.Defs
import MCA.Code.ListDecode
import MCA.Code.Interleaved
import MCA.Code.Johnson
import MCA.Code.JohnsonGeometric
import MCA.Code.JohnsonEmbed
import MCA.Code.JohnsonBound

-- Reed–Solomon codes
import MCA.ReedSolomon.Defs
import MCA.ReedSolomon.MDS

-- The GGR interleaving reduction and its composition
import MCA.ListDecoding.TreeCount
import MCA.ListDecoding.EraseDecode
import MCA.ListDecoding.GGRComposition
import MCA.ListDecoding.InterleavedListSize
import MCA.ListDecoding.Interleaved
import MCA.ListDecoding.Prize
import MCA.ListDecoding.Divisibility
import MCA.ListDecoding.BaseRSReduction
import MCA.ListDecoding.MuralidharaSenPlugin

-- Smooth-coset higher-order-MDS obstruction
import MCA.Candidates.SmoothCosetMDSFailure

/-!
# `rs-gld-formalization` — root aggregator

A clean, reproducible Lean 4 / Mathlib formalization of three results for Reed–Solomon
list decoding (extracted from the `mca-problem` research lab):

1. **GGR interleaving reduction** — `MCA.ListDecoding.InterleavedListSize`
   (`interleave_list_size_ggr`, `maxListSize_interleave_le_int`).
2. **Muralidhara–Sen above-Johnson plug-in** — `MCA.ListDecoding.MuralidharaSenPlugin`
   (import-style composition with the reduction).
3. **Smooth-coset higher-order-MDS obstruction** — `MCA.Candidates.SmoothCosetMDSFailure`
   (`binom_three_dependent`, sorry-free and axiom-clean).

`lake build` builds the whole closure above. See `README.md` for the theorem map and
`research/theorem_dependency_graph.md` for how the pieces compose.
-/
