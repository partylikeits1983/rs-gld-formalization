-- Core code / Hamming / list-decoding infrastructure
import RSGLD.Code.Hamming
import RSGLD.Code.Defs
import RSGLD.Code.ListDecode
import RSGLD.Code.Interleaved

-- Reed–Solomon codes
import RSGLD.ReedSolomon.Defs
import RSGLD.ReedSolomon.MDS

-- The GGR interleaving reduction and its composition
import RSGLD.ListDecoding.TreeCount
import RSGLD.ListDecoding.EraseDecode
import RSGLD.ListDecoding.GGRComposition
import RSGLD.ListDecoding.InterleavedListSize
import RSGLD.ListDecoding.Interleaved
import RSGLD.ListDecoding.Prize
import RSGLD.ListDecoding.BaseRSReduction
import RSGLD.ListDecoding.MuralidharaSenPlugin

-- Smooth-coset higher-order-MDS obstruction
import RSGLD.SmoothCosetMDS

/-!
# `rs-gld-formalization` — root aggregator

A Lean 4 / Mathlib formalization of three results for Reed–Solomon list decoding:

1. **GGR interleaving list-size reduction** — `RSGLD.ListDecoding.InterleavedListSize`
   (`interleave_list_size_ggr`, `maxListSize_interleave_le_int`): the interleaved list size
   is controlled by the base-RS list size.
2. **Muralidhara–Sen plug-in** — `RSGLD.ListDecoding.MuralidharaSenPlugin`: composing the
   external Muralidhara–Sen bound with the reduction gives a verified slightly-above-Johnson
   field-size condition.
3. **Smooth-coset higher-order-MDS obstruction** — `RSGLD.SmoothCosetMDS`
   (`binom_three_dependent`): smooth roots-of-unity domains fail the higher-order-MDS
   condition that generic-RS capacity proofs rely on.

`lake build` builds the whole closure above. See `README.md` for the theorem map and
`research/theorem_dependency_graph.md` for how the pieces compose.
-/
