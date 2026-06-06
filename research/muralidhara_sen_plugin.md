# Muralidhara–Sen → GLD-9 plug-in (design + status)

**Fork A, positive but modest.** The first concrete positive in-repo target since GLD-9: import the
Muralidhara–Sen above-Johnson list bound and compose it with the proven GLD-9 reduction to certify the
interleaved Grand List Decoding target at radius `E = n − √(nk) + c`.

## The two layers

**Layer 1 — composition (DONE, axiom-clean).** `RSGLD/ListDecoding/MuralidharaSenPlugin.lean`,
`gld_field_size_slightly_above_johnson_of_MS`. Import-style: takes the MS bound `maxListSize C (E/n) ≤ n^Dexp` as a
*hypothesis*, threads it through `interleave_list_le_of_base_bound` (GLD-9) + a field-size condition,
and concludes `2^128 · maxListSize (interleave C m) (E/n) ≤ |F|`. Holds for **every** code `C`, hence
every smooth-coset RS. `#print axioms` = `[propext, Classical.choice, Quot.sound]`.

```
gld_field_size_slightly_above_johnson_of_MS :
  (hMS    : maxListSize C (E/n) ≤ n^Dexp)                 -- the Muralidhara–Sen input (assumed)
  (hED    : E < Dmin) (hD : Dmin ≤ minDist C · n)         -- E < min distance
  (hb     : E ≤ b·(Dmin−E)) (hr2 : Dmin ≤ 2^r·(Dmin−E))   -- GLD-9 integer budget
  (hField : 2^128 · choose(b+r,r) · (n^Dexp)^r ≤ |F|)     -- field-size condition
  ⟹  2^128 · maxListSize (interleave C m) (E/n) ≤ |F|     -- the Grand List Decoding target at E/n
```

**Layer 2 — the Muralidhara–Sen proof itself (NOT yet formalized; decide after Layer 1).** Their
divide-and-reduce argument (Discrete Applied Math 2008, Thm 2.4 / Cor 2.5), for arbitrary distinct
evaluation points (hence smooth cosets):
- **fix one agreement point** `x_i`, **divide `P(X)` by `(X − x_i)`** (Lemma 2.1): a degree-`<k` poly
  agreeing on `≥ t` points with `P(x_i)=y_i` ↔ a degree-`<(k−1)` poly on the reduced instance;
- this reduces an `(n,k,t)` instance to a union over `i` of `(n−1,k−1,t−1)` instances (Lemma 2.2:
  `|Poly(n,k,t)| ≤ Σ_i |Poly(n−1,k−1,t−1)|`);
- iterate `s = ⌈2√α/(1−√α)²⌉ + 1` times, until `t−s > √((n−s)(k−s))` lands in the **GS/Johnson** range,
  where the list is `O(n²)` for all RS (the Guruswami–Sudan / Johnson range);
- the iterated union gives `B_C(E) ≤ O(n^{Dexp})`, `Dexp = 2√α/(1−√α)²+3`.

## Field-size consequence (the careful scope)

`δ*_C ≥ 1 − √ρ + c/n` for any constant `c`, **provided `|F| ≥ 2^128 · poly(n)`** (`b ≈ ⌈1/√ρ⌉`,
`r ≈ ⌈log₂(1/√ρ+1)⌉` constants; `poly(n) = choose(b+r,r)·(n^Dexp)^r`). The radius is strictly above
Johnson by the **additive** `c` only — a **relative `c/n` improvement, not constant-relative**. So:
- ✅ certifies `δ*_C` **strictly above** the Johnson radius for fixed smooth cosets (large field);
- ❌ does **not** resolve the largest `δ*_C` (the band interior toward capacity stays external/open);
- ❌ vacuous in the `n≈√q` regime; exponent `Dexp` large at high rate (`ρ=1/2 ⇒ Dexp≈19`).

## Next steps
1. **(done)** Layer-1 composition `gld_field_size_slightly_above_johnson_of_MS`, axiom-clean.
2. **DECISION (2026-06-06): HOLD Layer 2 — cite Muralidhara–Sen externally (Tier-C baseline), like
   `[GGR11]` was before it was proven.** Reasoning: the MS reduction, while elementary in spirit
   (polynomial division + Johnson baseline), is a **multi-leaf effort comparable to the GGR composition**
   — and the tricky parts are the *worst-case-over-`w`* and the *code-length-changing* reduction
   `(n,k,t)→(n−1,k−1,t−1)` (a puncture, the same `Fin (n−1)`-cast hazard GGR avoided). For only a
   **`c/n` vanishing-relative** gain, that budget is better spent elsewhere. So `hMS` stays an assumed
   hypothesis discharged by the citation; Layer 1 is the in-repo content. **Layer 2 remains an
   available, lower-priority target** if an unconditional above-Johnson certificate is later wanted —
   the reduction starting point is recorded above.
3. The full Grand List Decoding problem (constant-relative beyond Johnson, up to capacity) stays the external open target
   (`research/next_theorem.md`, `research/theorem_matching_for_base_rs.md`).
