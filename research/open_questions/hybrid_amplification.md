# Open question: can hybrid / multi-scale binomial defects amplify to a large list?

This is the one residual micro-question left by the smooth-coset analysis
(`research/smooth_coset_mds_failure.md`, Step 4). It is **open**; nothing here is claimed proved.

## What is settled

A single-scale subgroup-binomial defect on `L = μ_{2^s}` contributes only `O(1/ρ)` codewords in the
Johnson-to-capacity band — a constant in `n` and `q`, far below the prize threshold `2^{-128}·|F|`.
The received word `w = (x^d)` and the `n/d` constant codewords `ω^{td}` realize this, and the defect
intersection lives *above* capacity when `d < k`. So smooth cosets fail the generic-RS sufficient
condition (`MDS(ℓ)`), but the single-scale defect is benign.

## The open question

Can the binomial structure be *combined across scales or with the additive obstruction* to produce a
**super-constant (ideally `Ω(q)`) list in the band**? Concretely, do any of the following beat
`O(1/ρ)` at a band radius `δ ∈ (1−√ρ, H_q⁻¹(1−ρ))`?

1. **Multi-scale subgroup chains** `H_d ⊂ H_{2d} ⊂ ⋯ ⊂ μ_n`. A single `w = x^d` is tied to one
   scale; the total over all 2-power scales is `Σ_d n/d < 2n`, but those codewords sit at *different*
   agreements and cannot all be close to one `w`. Is there a single `w` simultaneously close to many
   across scales?
2. **Products of binomials** `∏_j (X^{d_j} − c_j)` as the received word. Higher degree, but a
   degree-`<k` codeword agreeing on a full coset still appears pinned to the per-scale constant family.
3. **Piecewise-polynomial `w`** (a different low-degree polynomial on each coset). The "constant agrees
   on a full coset" structure breaks; agreement across `m` cosets is `m·d` interpolation constraints,
   which generically forces uniqueness — so this seems to *prevent* a large list, not create one.
4. **Additive × multiplicative hybrid.** Combine the BSKR additive subspace-polynomial obstruction
   (super-polynomial list, but at *full field* `n = |F|` and *below the rate*) with a multiplicative
   coset, exploiting a subfield coincidence. The two obstructions live at incompatible parameters; is
   there a regime where they reinforce?
5. **Rational received words** `w = P/Q` with `Q` aligned to subgroup cosets.

## Why it matters / how it connects

A positive answer (an `Ω(q)` band list from a structured `w`) would be a genuine **negative
resolution** of the left endpoint `δ*_C = ` Johnson for smooth-coset plain RS — a publishable "no."
A clean negative answer (a proof that any single-scale-binomial-derived `w` has `O(poly(n))` band
list) would *upgrade route B from experimentally-supported to proved*. Either is a real result. This
is parked in the `mca-problem` research lab; it is **not** part of the verified artifact in this repo.
