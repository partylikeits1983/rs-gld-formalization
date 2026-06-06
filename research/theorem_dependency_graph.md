# Theorem dependency graph & paper-term → Lean-name map

This repo formalizes one **reduction** (with a composition on top) and one **structural obstruction**.
Everything is for `C = RS[F, L, k]`, rate `ρ = k/n`, list `Λ(C, E) = {codewords within Hamming
distance ≤ E}`, Johnson radius `1 − √ρ`, capacity `H_q⁻¹(1 − ρ)`.

## The reduction chain (what composes into what)

```text
                         base-RS worst-case list size
                              B_C(E) = |Λ(C, E)|
                                     │
            ┌────────────────────────┴───────────────────────────┐
            │                                                      │
   GGR interleaving reduction                          (external input, plug a bound for B_C(E))
   |Λ(C^{≡m}, E)| ≤ C(b+r,r)·B_C(E)^r                            │
   [interleave_list_size_ggr,                                     │
    maxListSize_interleave_le_int]                                │
            │  builds on:                          ┌──────────────┴───────────────┐
            │  treeLeaves_le  (tree leaf count)    │ Muralidhara–Sen (external):   │
            │  EraseDecode.Inv.{white,blue,red}    │   B_C(E) ≤ n^D at             │
            │  GGRComposition.Ninter_le            │   E = n − ⌈√(nk)⌉ + c         │
            ▼                                       │   (radius 1−√ρ + O(1/n))      │
   interleaved field-size condition                 └──────────────┬───────────────┘
   2^128·|Λ(C^{≡m},E)| ≤ |F|                                       │
   [interleavedRS_field_size_condition_of_base_bound]  ◄─── compose ┘
            │
            ▼
   slightly-above-Johnson consequence
   field-size condition holds when |F| ≥ 2^128·C(b+r,r)·n^{Dr}
   [interleaved_field_size_condition_of_base_poly_bound,
    gld_field_size_slightly_above_johnson_of_MS]
```

The reduction is **`m`-independent**: interleaving does not move the frontier. The only external
input is a bound on the base-RS list size `B_C(E)`; beyond Johnson that is open in general, and the
Muralidhara–Sen bound supplies the modest `O(1/n)` step actually proved here.

## The structural obstruction (separate track)

```text
smooth coset L = μ_{2^s}, order-d (2-power) subgroup H_d
        │
        ▼
coset ω^t H_d has BINOMIAL vanishing polynomial  V = X^d − ω^{td} ∈ span{1, X^d}
        │
        ▼
any 3 such binomials are linearly dependent           [binom_three_dependent  (sorry-free)]
   (c₁−c₂)(X^d−c₀)+(c₂−c₀)(X^d−c₁)+(c₀−c₁)(X^d−c₂)=0   [binom_three_coeffs_nontrivial]
        │
        ▼
dim(⋂_t G_{A_t}) = max(0, 2d−k) > generic   ⇒   RS[μ_{2^s}, k] is NOT MDS(ℓ) for ℓ ≥ 3
        │
        ▼
the BGM/AGGLZ generic-RS capacity machinery (which requires MDS(ℓ)) cannot be imported,
BUT the list-decoding fallout is mild (route B): O(1/ρ) list, witness above capacity.
```

## Paper term → Lean name

| Result / object | Lean declaration | File |
|---|---|---|
| GGR interleaving reduction (core) | `RSGLD.ListDecoding.interleave_list_size_ggr` | `RSGLD/ListDecoding/InterleavedListSize.lean` |
| GGR reduction (integer form) | `RSGLD.ListDecoding.maxListSize_interleave_le_int` | `RSGLD/ListDecoding/GGRComposition.lean` |
| Erase-decode tree leaf count | `RSGLD.ListDecoding.treeLeaves_le` | `RSGLD/ListDecoding/TreeCount.lean` |
| Tree invariant (white/blue/red) | `RSGLD.ListDecoding.Inv` (`.white/.blue/.red`) | `RSGLD/ListDecoding/EraseDecode.lean` |
| Per-node intersection bound | `RSGLD.ListDecoding.Ninter_le` | `RSGLD/ListDecoding/GGRComposition.lean` |
| base-RS bound ⇒ field-size condition | `RSGLD.ListDecoding.interleavedRS_field_size_condition_of_base_bound` | `RSGLD/ListDecoding/BaseRSReduction.lean` |
| Muralidhara–Sen plug-in | `RSGLD.ListDecoding.interleaved_field_size_condition_of_base_poly_bound` | `RSGLD/ListDecoding/MuralidharaSenPlugin.lean` |
| MS slightly-above-Johnson corollary | `RSGLD.ListDecoding.gld_field_size_slightly_above_johnson_of_MS` | `RSGLD/ListDecoding/MuralidharaSenPlugin.lean` |
| Binomial dependence (MDS obstruction) | `RSGLD.SmoothCosetMDS.binom_three_dependent` | `RSGLD/SmoothCosetMDS.lean` |
| Nontrivial dependence coefficients | `RSGLD.SmoothCosetMDS.binom_three_coeffs_nontrivial` | `RSGLD/SmoothCosetMDS.lean` |
| RS is MDS (distance) | `RSGLD.ReedSolomon` (MDS lemmas) | `RSGLD/ReedSolomon/MDS.lean` |

All of the above are sorry-free and depend only on `propext, Classical.choice, Quot.sound`
(verified by `scripts/check_axioms.sh`).
