# rs-gld-formalization

A Lean 4 / Mathlib formalization of the **GGR interleaving list-size reduction** for Reed–Solomon
list decoding, together with a formalized **smooth-coset higher-order-MDS obstruction** and a
**Muralidhara–Sen plug-in** for a slightly-above-Johnson grand-list-decoding corollary.

Everything builds with `lake build`, is free of `sorry`, and depends only on Lean's three
foundational axioms (`propext`, `Classical.choice`, `Quot.sound`) — verified by
`./scripts/check_axioms.sh`.

---

## The three results

Let `C = RS[F, L, k]` be a Reed–Solomon code of block length `n = |L|`, rate `ρ = k/n`, with
`Λ(C, E)` its list of codewords within Hamming distance `E`, Johnson radius `1 − √ρ`, and `q`-ary
list-decoding capacity `H_q⁻¹(1 − ρ)`. Write `C^{≡m}` for the `m`-interleaved code.

**1. GGR interleaving reduction** (proved, axiom-clean). For radius `E` with parameters `b, r`
(from the gap `δ_min − E/n`):
```
   |Λ(C^{≡m}, E)|  ≤  C(b+r, r) · |Λ(C, E)|^r .
```
The bound is **independent of `m`**: interleaving does not move the list-decoding frontier. This
reduces the interleaved Grand List-Decoding Challenge to the base-RS worst-case list size `B_C(E)`.

**2. Muralidhara–Sen plug-in** (composition; the MS bound itself is imported as a hypothesis).
With the external Muralidhara–Sen bound `B_C(E) ≤ n^D` at `E = n − ⌈√(nk)⌉ + c` (radius
`1 − √ρ + O(1/n)`, just above Johnson):
```
   |Λ(C^{≡m}, E)|  ≤  C(b+r, r) · n^{Dr} ,
```
so the prize condition `2^128·|Λ(C^{≡m}, E)| ≤ |F|` holds once `|F| ≥ 2^128 · C(b+r, r) · n^{Dr}`.

**3. Smooth-coset obstruction** (proved core). For a smooth multiplicative domain `L = μ_{2^s}`,
a coset `ω^t H_d` of the order-`d` (2-power) subgroup has the **binomial** vanishing polynomial
`X^d − ω^{td} ∈ span{1, X^d}`. Any three such binomials are linearly dependent, so
```
   dim(⋂_t G_{A_t}) = max(0, 2d − k)   >   generic,    and
   RS[μ_{2^s}, k]  is NOT  MDS(ℓ)  for every  ℓ ≥ 3.
```
Hence the generic/random-RS capacity machinery (BGM/AGGLZ), which requires higher-order MDS,
**cannot be imported** to smooth cosets. (The list-decoding fallout is mild — see "What this does
not prove.")

---

## What this does NOT prove (honest scope)

- **No claim crosses capacity `H_q⁻¹(1 − ρ)`.** Nothing here decodes plain RS beyond what is
  classically known.
- **The base-RS list size beyond Johnson is open.** Result 1 *reduces* the interleaved challenge to
  `B_C(E)`; it does not bound `B_C(E)` beyond Johnson. That remains the external open problem.
- **The Muralidhara–Sen bound is imported, not re-proved.** Result 2 is a verified *composition*
  conditional on the cited MS theorem `B_C(E) ≤ n^D`; the radius gain is only `O(1/n)`.
- **The smooth-coset obstruction is a method obstruction, not a counterexample.** The `MDS(ℓ)`
  failure blocks the generic-RS *proof technique*; the associated Hamming-ball list is only `O(1/ρ)`
  (a constant), and its witness sits above capacity. It does **not** move `δ*_C`. See
  `research/smooth_coset_mds_failure.md` and the open question in
  `research/open_questions/hybrid_amplification.md`.

---

## Build & verify

Requires [`elan`](https://github.com/leanprover/elan) (Lean toolchain manager). The toolchain
(`leanprover/lean4:v4.29.0`) and Mathlib revision are pinned in `lean-toolchain` and
`lake-manifest.json`.

```bash
lake exe cache get      # fetch prebuilt Mathlib oleans (fast; avoids hours of compiling)
lake build              # build the whole closure — green, zero sorry, zero new axioms

./scripts/check_axioms.sh           # assert the headline theorems are axiom-clean
python3 -V && ./scripts/reproduce_experiments.sh   # reproduce the finite-field experiments
```

---

## Theorem map (paper term → Lean name)

| Result | Lean declaration | File |
|---|---|---|
| GGR reduction (core) | `MCA.ListDecoding.interleave_list_size_ggr` | `MCA/ListDecoding/InterleavedListSize.lean` |
| GGR reduction (integer form) | `MCA.ListDecoding.maxListSize_interleave_le_int` | `MCA/ListDecoding/GGRComposition.lean` |
| Erase-decode tree leaf count | `MCA.ListDecoding.treeLeaves_le` | `MCA/ListDecoding/TreeCount.lean` |
| Tree invariant (white/blue/red) | `MCA.ListDecoding.Inv` | `MCA/ListDecoding/EraseDecode.lean` |
| base-RS bound ⇒ prize | `MCA.ListDecoding.interleavedRS_prize_of_base_bound` | `MCA/ListDecoding/BaseRSReduction.lean` |
| Muralidhara–Sen plug-in | `MCA.ListDecoding.interleaved_prize_of_base_poly_bound` | `MCA/ListDecoding/MuralidharaSenPlugin.lean` |
| MS above-Johnson corollary | `MCA.ListDecoding.gld_prize_slightly_above_johnson_of_MS` | `MCA/ListDecoding/MuralidharaSenPlugin.lean` |
| Binomial dependence (MDS obstruction) | `MCA.Candidates.SmoothCosetMDS.binom_three_dependent` | `MCA/Candidates/SmoothCosetMDSFailure.lean` |

Full dependency graph: `research/theorem_dependency_graph.md`.

---

## Layout

```text
MCA/                       Lean sources (namespace MCA.*)
  Code/                    Hamming distance, linear codes, list decoding, Johnson bound
  ReedSolomon/             RS codes and the MDS distance property
  ListDecoding/            GGR reduction, erase-decode tree, MS plug-in
  Candidates/              smooth-coset MDS obstruction (axiom-exempt zone; here, sorry-free)
research/                  result write-ups
  background/              literature synthesis & oracle results
  open_questions/          the remaining open problems
experiments/list_decoding/ finite-field cross-checks (Python)
scripts/                   mca_oracle.py (RS/field arithmetic), check_axioms.sh, reproduce_experiments.sh
```

The `MCA.Candidates` namespace is, by convention, the axiom/`sorry`-exempt landing zone (mirroring
the research lab); the obstruction theorem that lives there happens to be sorry-free and axiom-clean.

---

## Provenance

This is the clean artifact extracted from the research lab repository `mca-problem`, which holds the
full development history, dead-ends, and ongoing exploratory work. This repo is the stable, citeable
subset.
