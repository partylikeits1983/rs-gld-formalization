# Smooth-coset higher-order-MDS failure → its (mild) list-decoding fallout

**Verdict: route B — mild-defect theorem.** Smooth cosets `L = μ_{2^s}` fail `MDS(ℓ)` for every
`ℓ ≥ 3` (explicit binomial mechanism), which **blocks the BGM/AGGLZ generic-RS capacity import**.
But the defect converts only into an `O(1/ρ)` Hamming-ball list, and its natural witness sits
**above capacity** — so it is a *method* obstruction, **not** a Grand-List-Decoding counterexample. `δ*_C` stays
open. Muralidhara–Sen (Fork A, `MuralidharaSenPlugin.lean`) is the separate modest positive track.

Companion: `research/smooth_coset_mds3_target.md` (the ℓ=3 attack), `research/smooth_coset_genericity_literature.md`
(why the import would need MDS(ℓ)). Lean: `RSGLD/SmoothCosetMDS.lean` (core
dependence identity, sorry-free, axiom-clean). Experiment: `experiments/list_decoding/subcoset_defect_listsize.py`.

---

## Step 1 — the MDS-failure theorem (locked, theorem-shaped)

**Setup.** `F = GF(q)`, `L = μ_n = ⟨ω⟩`, `n = 2^s ∣ q−1`, code `RS[F,L,k]` (degree `<k`). Vandermonde
columns `g_i = (1,x_i,…,x_i^{k-1})`, `G_A = span{g_i : i∈A} ⊆ F^k`. Work in the dual:
`G_A^⊥ = {p : deg p < k, p|_A = 0} = span{ V_A(X)·X^t : 0 ≤ t < k−|A| }`, `V_A = ∏_{j∈A}(X−x_j)`, and
`dim(⋂_t G_{A_t}) = k − dim(Σ_t G_{A_t}^⊥)`.

**Coset vanishing polynomials are binomials.** For a 2-power `d ∣ n`, the order-`d` subgroup is
`H_d = ⟨ω^{n/d}⟩ = μ_d`, and a coset `ω^t H_d` has
```
    V_{ω^t H_d}(X) = ∏_{ζ^d = 1} (X − ω^t ζ) = X^d − ω^{td}      (a binomial; c_t := ω^{td}).
```
The `n/d` cosets give the `n/d` distinct values `c_t = ω^{td}` (since `ω^d` has order `n/d`).

**Theorem (MDS(ℓ) failure).** Let `A_t = ω^{i_t} H_d` be `ℓ` distinct cosets, `c_t = ω^{i_t d}`.

- **(a) Hyperplane case `|A_t| = k−1`, i.e. `d = k−1`, `k ≥ 3`.** Then each `G_{A_t}^⊥ = span{V_{A_t}}`
  with `V_{A_t} = X^{k-1} − c_t ∈ span{1, X^{k-1}}` (dimension 2). So any `ℓ ≥ 3` are linearly
  dependent ⇒ `dim(⋂ G_{A_t}) ≥ k−2 > max(0, k−ℓ) = ` generic. **Not `MDS(ℓ)` for `ℓ ≥ 3`.**

- **(b) General `d < k`.** `G_{A_t}^⊥ = (X^d − c_t)·Poly_{<k−d}`. Then (proved by the monomial-support
  argument below, verified computationally):
  ```
      dim( Σ_{t=1}^ℓ (X^d − c_t)·Poly_{<k−d} ) = min( k, 2(k−d) ),   for all ℓ ≥ 2,
      ⇒  dim( ⋂_{t=1}^ℓ G_{A_t} ) = max( 0, 2d − k ),               INDEPENDENT of ℓ.
  ```
  Generic value is `max(0, ℓd − (ℓ−1)k)`. A **strict defect (MDS(ℓ) failure) occurs iff `d > k/2`
  and `ℓ ≥ 3`** (at `ℓ=2` the two agree, so `MDS(2)` holds — the first failure is exactly `ℓ=3`).

*Proof of the `dim = min(k,2(k−d))` count.* For `Q ∈ Poly_{<k−d}` and two cosets,
`(X^d−c_s)Q − (X^d−c_t)Q = (c_t−c_s)Q` with `c_t≠c_s`, so `Poly_{<k−d} ⊆ S`; then
`X^d·Q = (X^d−c_s)Q + c_s Q ∈ S`, so `X^d·Poly_{<k−d} ⊆ S`. Hence `S ⊇ Poly_{<k−d} + X^d·Poly_{<k−d}`,
whose monomial support is `{0,…,k−d−1} ∪ {d,…,k−1}` — size `2(k−d)` if `2d ≥ k` (disjoint), else all
of `{0,…,k−1}`. The generators `(X^d−c_t)X^t` lie in that same span, giving equality. ∎

The **core algebraic dependence** (the engine of both (a) and (b)) is proved sorry-free in Lean,
`RSGLD.SmoothCosetMDS.binom_three_dependent`:
```
    (c₁−c₂)·(X^d − c₀) + (c₂−c₀)·(X^d − c₁) + (c₀−c₁)·(X^d − c₂) = 0,
```
with coefficients nonzero-unless-all-`cᵢ`-equal (`binom_three_coeffs_nontrivial`).

**Computational confirmation** (`subcoset_defect_listsize.py`, `mat_rank` over `GF(q)`):
| q | n | k | d | d>k/2 | dim(⋂) ℓ=2..6 | generic ℓ=3 | verdict |
|---|---|---|---|---|---|---|---|
| 193 | 32 | 5 | 4 | yes | 3,3,3,3,3 | 2 | DEFECT ℓ≥3 (matches `2d−k=3`) |
| 97 | 32 | 7 | 4 | yes | 1,1,1,1,1 | 0 | DEFECT ℓ≥3 (matches `2d−k=1`) |
| 97 | 32 | 7 | 2 | no  | 0,0,0,0,0 | 0 | no defect (matches `2d−k≤0`) |

Plus the earlier full orbit-rep scans in `smooth_coset_mds3_target.md` (defects at substantial rates,
positive control DETECTED at q=97 ⇒ test sensitive).

---

## Step 2 — explicit Hamming-ball witness from the defect

**Received word** `w = (x^d)_{x∈L}`. On coset `ω^t H_d` the function `x ↦ x^d` is **constant**
`= ω^{td}`. So the **constant codeword** `p_t ≡ ω^{td}` (degree `0 < k`) agrees with `w` on exactly
the `d` points of that coset. The `n/d` constants `{ω^{td}}` are distinct ⇒
```
    explicit list of  n/d  codewords  at agreement  a = d,  radius  δ = 1 − d/n.
```
(Verified: each constant has agreement exactly `d`; list size exactly `n/d`.)

---

## Step 3 — placement & generalization `k > d` (the decisive computation)

Two regimes, both giving a constant list — for *different* reasons:

- **`d < k` (the MDS-defect regime).** Then `a = d ≤ k−1 < k = ρn`, so
  `δ = 1 − d/n > 1 − k/n = 1 − ρ ≥ H_q⁻¹(1−ρ)`: the witness sits **strictly above capacity**, where
  large lists are *expected* and carry **no Grand-List-Decoding implication**. (Confirmed: every `d<k` row reports
  `ABOVE capacity`.) This is the sharp reason the higher-order-MDS defect is benign: the defect lives
  at agreement `≤ k−1`, i.e. radius at/above capacity, not in the band `(1−√ρ, 1−ρ)`.

- **`d > k` (push into the band).** To reach `δ < 1−ρ` one needs `a = d > k`, hence a *fat* subcoset
  `d > k`. Then the list is `n/d < n/k = 1/ρ` — a **constant ≤ 1/ρ**. Verified in-band
  (`q=17, n=8, k=3, d=4`: `δ=0.5 ∈ (0.388, 0.625)`, construction list `n/d=2`, true sampled
  worst-case `10` — a small constant, **not** `Ω(q)`).

The `Σ_t (X^d−c_t)·Poly_{<k−d}` dimension count of Step 1(b) is what underlies this: the defect
dimension `2d−k` is positive only for `d > k/2`, and the number of available cosets `n/d` shrinks as
`d` grows, capping the contributed list at `O(1/ρ)`.

---

## Step 4 — can pure subgroup-binomial defects amplify to `Ω(q)`? (No, for single scale)

The construction contributes at most `n/d` codewords from one subgroup scale, and `n/d ≤ n/1`; in the
band (`d>k`) it is `< 1/ρ`. **For a fixed rate `ρ`, this is a constant in `n` and `q`** — it can never
reach the list-size threshold `> 2^{-128}·|F|` for cryptographic `q` (would need `q < (n/d)·2^{128}`).
This matches the independent worst-case oracle sweep (`research/base_rs_oracle_results.md`: in-band
list constant `≤ 1/ρ` across all tested `q`, including the `n≈√q` regime).

Amplification routes considered (and why single-scale binomials don't obviously beat `O(1/ρ)`):
1. **Multi-scale chains `H_d ⊂ H_{2d} ⊂ ⋯ ⊂ μ_n`.** A single `w = x^d` is tied to one scale; the
   total over all 2-power scales is `Σ_d n/d < 2n`, but these live at *different* agreements and
   cannot all be near one `w`.
2. **Products `∏_j (X^{d_j} − c_j)`.** As a received word this raises the degree but a degree-`<k`
   codeword agreeing on a full coset is still pinned to the constant family per scale.
3. **Piecewise-polynomial `w`** (different low-degree poly per coset): the "constant agrees on a full
   coset" structure breaks; agreement across `m` cosets is `m·d ≥ k` interpolation constraints,
   generically forcing uniqueness — no list blow-up.
4. **Additive–multiplicative hybrid (BSKR ⊗ coset)** and **rational `w = P/Q`** with `Q` coset-aligned:
   not pursued here; flagged as the **only residual micro-question**. The additive BSKR defect is
   `Ω(super-poly)` but at *full field* `n=|F|` and *below the rate* — does not combine cleanly with a
   multiplicative coset at the Grand List Decoding rates without a subfield coincidence.

**Conclusion (route B).** Pure single-subgroup binomial defects yield only `O(1/ρ)` codewords in the
Johnson-to-capacity band; the genuine higher-order-MDS defect lives above capacity. The smooth-coset
`MDS(ℓ)` failure is a real obstruction to the *generic-RS proof method*, not a movement of `δ*_C`.

---

## Honest labels

| claim | label | applies to fixed smooth-domain plain RS? |
|---|---|---|
| coset vanishing poly `= X^d − ω^{td}`; 3 binomials dependent | **proved** (Lean, `binom_three_dependent`) | yes |
| `dim(⋂) = max(0,2d−k)`, defect iff `d>k/2 ∧ ℓ≥3` | **proved** (monomial-support) + experimentally-confirmed | yes |
| `RS[μ_{2^s},k]` not `MDS(ℓ)` for `ℓ≥3` | **experimentally-supported** (full orbit scans) + proved core | yes |
| explicit witness list `= n/d` at agreement `d` | **proved** | yes |
| `d<k` witness is above capacity; in-band list `O(1/ρ)` | **proved** (inequality) + experimentally-confirmed | yes |
| BGM/AGGLZ capacity import blocked for `μ_{2^s}` | **proved-as-obstruction** (the condition they require fails) | yes |
| no `Ω(q)` list from single-scale binomials | **experimentally-supported** + structural argument | yes |
| hybrid/multi-scale amplification | **open micro-question** | unknown |

No claim crosses `H_q⁻¹(1−ρ)`. Muralidhara–Sen plug-in kept strictly separate (Fork A).
