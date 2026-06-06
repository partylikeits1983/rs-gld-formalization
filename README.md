# rs-gld-formalization

A Lean 4 / Mathlib formalization of a Reed–Solomon interleaving list-size reduction, together with
a smooth-coset obstruction to importing generic Reed–Solomon capacity methods.

This repository concerns the **grand list-decoding problem** for interleaved Reed–Solomon codes —
roughly:

> If many interleaved Reed–Solomon codewords are close to a received word, how large can that list be?

> **In one sentence:** interleaving reduces to base RS; smooth cosets are not generic; the true
> base-RS frontier remains open.

The headline Lean theorems are `sorry`-free and depend only on Lean's three foundational axioms
(`propext`, `Classical.choice`, `Quot.sound`) — verified by `./scripts/check_axioms.sh`. Everything
builds with `lake build`.

---

## Notation

Let `C = RS[F, L, k]` be a Reed–Solomon code of block length `n = |L|` and rate `ρ = k/n`, and let
`Λ(C, E)` denote the list of codewords within Hamming distance `E` of a received word. Write
`C^{≡m}` for the `m`-interleaved code. The central base-code quantity is the worst-case Hamming-ball
list size

```
B_C(E) = max_w |Λ(C, w, E)|.
```

---

## Main results

The contribution has three layers: a formalized reduction, its mathematical consequence, and a
structural discovery about smooth domains.

### 1. Interleaving list-size reduction (formalized)

The repository formalizes the **GGR interleaving reduction**: for a code `C` and its `m`-interleaved
version `C^{≡m}`,

```
|Λ(C^{≡m}, E)|  ≤  binom(b+r, r) · |Λ(C, E)|^r,
```

where `b, r` are integer parameters determined by the gap between the relative decoding radius and
the minimum distance. The bound is **independent of `m`**. In words:

> The number of nearby interleaved codewords is controlled by the number of nearby ordinary
> Reed–Solomon codewords. Interleaving does not create a fundamentally new list-decoding frontier.

This reduces the interleaved grand list-decoding problem to the base quantity `B_C(E)`. The
remaining hard object is the worst-case Hamming-ball list size of ordinary Reed–Solomon codes:

> Interleaving is not the hard part. Base RS beyond Johnson is the hard part.

This is the formal-methods contribution — proved in Lean, `sorry`-free, axiom-clean.

### 2. Muralidhara–Sen plug-in

Muralidhara–Sen prove that for Reed–Solomon codes, at radius `E = n − √(nk) + c` (constant `c`), the
base list size is polynomial:

```
B_C(E)  ≤  n^D.
```

This radius is slightly above the Johnson radius, `1 − √ρ + O(1/n)`. Composing this external bound
with the formalized reduction gives

```
|Λ(C^{≡m}, E)|  ≤  binom(b+r, r) · n^{D r},
```

so the target inequality `2^128 · |Λ(C^{≡m}, E)| ≤ |F|` holds whenever
`|F| ≥ 2^128 · binom(b+r, r) · n^{D r}`. This is a verified, slightly-above-Johnson consequence for
the interleaved setting. The Muralidhara–Sen theorem itself is imported as an external hypothesis;
this repository formalizes the composition.

### 3. Smooth-coset higher-order-MDS obstruction

Random/generic Reed–Solomon capacity results rely on a structural property called **higher-order
MDS**, `MDS(ℓ)`. The repository identifies a structural obstruction for smooth multiplicative
domains `L = μ_{2^s}`.

Let `H_d` be the order-`d` subgroup and `ω` a primitive root. Each coset `ω^t H_d` has vanishing
polynomial

```
V_{ω^t H_d}(X) = X^d − ω^{td},
```

a binomial using only the monomials `1` and `X^d`. So these vanishing polynomials all lie in the
two-dimensional `span{1, X^d}`, and any three are linearly dependent. Consequently smooth
roots-of-unity domains fail `MDS(ℓ)` already at `ℓ = 3`, and for every `ℓ ≥ 3`. More precisely, for
suitable subcosets `A_t`,

```
dim(⋂_t G_{A_t}) = max(0, 2d − k),
```

which exceeds the generic value when `d > k/2` and `ℓ ≥ 3`. Thus smooth FFT-style domains sit on the
higher-order-MDS exceptional variety, and generic/random-RS capacity methods cannot be imported to
them directly.

---

## What this repository does NOT prove

The scope is deliberately careful.

- **It does not solve the full grand list-decoding problem.** The reduction shows interleaved list
  size is a controlled blowup of base-RS list size; it does not determine `B_C(E)` beyond Johnson.
  That remains the central open object.
- **The Muralidhara–Sen consequence is modest.** It gives progress only at radius
  `1 − √ρ + O(1/n)` — not a constant gap beyond Johnson.
- **The smooth-coset obstruction is not a large-list counterexample.** The `MDS(ℓ)` failure blocks a
  generic *proof strategy*, but the natural witness `w(x) = x^d` gives only `n/d` nearby constant
  codewords, at most `1/ρ` (a constant) in the relevant band. So it explains why generic/random-RS
  methods do not directly apply to smooth cosets, but it does not itself produce a large-list lower
  bound. See `research/smooth_coset_mds_failure.md` and
  `research/open_questions/hybrid_amplification.md`.

---

## Build and verify

Requires [`elan`](https://github.com/leanprover/elan). The toolchain (`leanprover/lean4:v4.29.0`)
and Mathlib revision are pinned in `lean-toolchain` and `lake-manifest.json`.

```bash
lake exe cache get      # fetch prebuilt Mathlib oleans (fast)
lake build              # build the whole closure — green, zero sorry, zero new axioms

./scripts/check_axioms.sh                            # assert the headline theorems are axiom-clean
python3 -V && ./scripts/reproduce_experiments.sh     # reproduce the finite-field experiments
```

---

## Theorem map

| Statement | Lean declaration | File |
|---|---|---|
| Interleaving reduction (core) | `RSGLD.ListDecoding.interleave_list_size_ggr` | `RSGLD/ListDecoding/InterleavedListSize.lean` |
| Integer interleaving bound | `RSGLD.ListDecoding.maxListSize_interleave_le_int` | `RSGLD/ListDecoding/GGRComposition.lean` |
| Erase-decode tree leaf count | `RSGLD.ListDecoding.treeLeaves_le` | `RSGLD/ListDecoding/TreeCount.lean` |
| Erase-decode budget invariant | `RSGLD.ListDecoding.Inv` | `RSGLD/ListDecoding/EraseDecode.lean` |
| Base bound ⇒ field-size condition | `RSGLD.ListDecoding.interleavedRS_field_size_condition_of_base_bound` | `RSGLD/ListDecoding/BaseRSReduction.lean` |
| Muralidhara–Sen polynomial plug-in | `RSGLD.ListDecoding.interleaved_field_size_condition_of_base_poly_bound` | `RSGLD/ListDecoding/MuralidharaSenPlugin.lean` |
| Slightly-above-Johnson corollary | `RSGLD.ListDecoding.gld_field_size_slightly_above_johnson_of_MS` | `RSGLD/ListDecoding/MuralidharaSenPlugin.lean` |
| Binomial dependence (MDS obstruction) | `RSGLD.SmoothCosetMDS.binom_three_dependent` | `RSGLD/SmoothCosetMDS.lean` |

Full dependency graph: `research/theorem_dependency_graph.md`.

---

## Repository layout

```text
RSGLD/
  Code/                 Hamming distance, linear codes, list decoding
  ReedSolomon/          Reed–Solomon codes and the MDS distance property
  ListDecoding/         Interleaving reduction, erase-decode tree, Muralidhara–Sen plug-in
  SmoothCosetMDS.lean   Smooth-coset higher-order-MDS obstruction (headline result)
research/               Result write-ups, theorem dependency graph, open questions
  background/           Literature synthesis & oracle results
  open_questions/       The remaining open problems
experiments/list_decoding/   Finite-field cross-checks (Python)
scripts/                Build, axiom-check, and experiment-reproduction scripts
```

---

## Provenance

This is the clean artifact extracted from the broader research repository `mca-problem`, which holds
the full development history, dead-ends, and ongoing exploratory work. This repository is the stable,
citeable subset:

1. the formalized interleaving reduction;
2. the Muralidhara–Sen composition;
3. the smooth-coset higher-order-MDS obstruction;
4. reproducible experiments supporting the structural claims.
