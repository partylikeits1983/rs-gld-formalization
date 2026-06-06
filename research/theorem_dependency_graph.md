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
   interleaved prize condition                      └──────────────┬───────────────┘
   2^128·|Λ(C^{≡m},E)| ≤ |F|                                       │
   [interleavedRS_prize_of_base_bound]  ◄───────────── compose ────┘
            │
            ▼
   slightly-above-Johnson GLD consequence
   prize holds when |F| ≥ 2^128·C(b+r,r)·n^{Dr}
   [interleaved_prize_of_base_poly_bound,
    gld_prize_slightly_above_johnson_of_MS]
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
| GGR interleaving reduction (core) | `MCA.ListDecoding.interleave_list_size_ggr` | `MCA/ListDecoding/InterleavedListSize.lean` |
| GGR reduction (integer form) | `MCA.ListDecoding.maxListSize_interleave_le_int` | `MCA/ListDecoding/GGRComposition.lean` |
| Erase-decode tree leaf count | `MCA.ListDecoding.treeLeaves_le` | `MCA/ListDecoding/TreeCount.lean` |
| Tree invariant (white/blue/red) | `MCA.ListDecoding.Inv` (`.white/.blue/.red`) | `MCA/ListDecoding/EraseDecode.lean` |
| Per-node intersection bound | `MCA.ListDecoding.Ninter_le` | `MCA/ListDecoding/GGRComposition.lean` |
| base-RS bound ⇒ prize | `MCA.ListDecoding.interleavedRS_prize_of_base_bound` | `MCA/ListDecoding/BaseRSReduction.lean` |
| Muralidhara–Sen plug-in | `MCA.ListDecoding.interleaved_prize_of_base_poly_bound` | `MCA/ListDecoding/MuralidharaSenPlugin.lean` |
| MS slightly-above-Johnson corollary | `MCA.ListDecoding.gld_prize_slightly_above_johnson_of_MS` | `MCA/ListDecoding/MuralidharaSenPlugin.lean` |
| Binomial dependence (MDS obstruction) | `MCA.Candidates.SmoothCosetMDS.binom_three_dependent` | `MCA/Candidates/SmoothCosetMDSFailure.lean` |
| Nontrivial dependence coefficients | `MCA.Candidates.SmoothCosetMDS.binom_three_coeffs_nontrivial` | `MCA/Candidates/SmoothCosetMDSFailure.lean` |
| RS is MDS (distance) | `MCA.ReedSolomon` (MDS lemmas) | `MCA/ReedSolomon/MDS.lean` |
| Johnson list-size baseline | `MCA.Code` (Johnson bound) | `MCA/Code/JohnsonBound.lean` |

All of the above are sorry-free and depend only on `propext, Classical.choice, Quot.sound`
(verified by `scripts/check_axioms.sh`).
