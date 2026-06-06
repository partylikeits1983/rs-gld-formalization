# GLD Literature Map — Workstream B: is the fixed smooth-domain RS beyond-Johnson frontier open?

**Status:** literature triage complete (2026-06-05). **Verdict: GENUINELY OPEN** for fixed
smooth-domain plain RS at ρ∈{1/2,1/4,1/8,1/16}. Certifiable floor = Johnson `1−√ρ`. Recommended
in-repo move = formalize the GGR rank-counting core (GLD-9), keep the band itself external.

**Scope.** `C = RS[F,L,k]`, `L` = fixed **smooth domain** (multiplicative coset of a 2-power-order
subgroup of `F*`, eprint 2026/680 Def 2.12), `n=|L|`, `ρ=k/n ∈ {1/2,1/4,1/8,1/16}`. Target =
**worst-case combinatorial list SIZE** `|Λ(C,δ)| = max_w #{c∈C : Δ(c,w)≤δ}` polynomially bounded in
`n`. Johnson radius `1−√ρ`; capacity ceiling `H_q⁻¹(1−ρ)`. Open band `δ∈(1−√ρ, H_q⁻¹(1−ρ)]`.

**Three failure modes guarded against throughout:** (i) reporting a *random/generic-RS* theorem as
if it covered the fixed coset; (ii) reporting an *algorithmic* decoding-radius result as a
*combinatorial list-size* bound; (iii) blurring list-decoding vs list-recovery vs the
*agreement-below-rate* regime.

---

## 1. Applicability table

| # | Theorem (authors, venue, year, id) | Exact statement (radius / list-size / rate / field) | Flag | Holds for FIXED smooth multiplicative-coset RS at ρ∈{1/2,…,1/16}? |
|---|---|---|---|---|
| 1 | **Guo–Li–Shangguan–Tamo–Wootters**, "Improved List-Decodability and List-Recoverability of RS via Tree Packings", FOCS'21 / SICOMP (arXiv 2011.04453) | *There **exist** RS codes over **exponentially large fields** list-decodable to radius `1−ε` with rate `Ω(ε/(log(1/ε)+1))`*; list-recovery analog. Hypergraph Nash-Williams–Tutte **conjecture** ⇒ optimal non-asymptotic, still **existence**. | **adaptable (weak) / irrelevant-random-only in practice** | **No (unknown→no).** "There exist RS codes" = a *choice* of evaluation points over an exponential field; no claim that a multiplicative coset is among them. Even the conjectural endpoint is existential, not domain-specific. |
| 2 | **Brakensiek–Gopi–Makam**, "Generic RS Codes Achieve List-Decoding Capacity", STOC'23 (arXiv 2206.05256) | *With high probability a **random** RS code of rate `R` over an **exponentially large field** is `(1−R−ε, O(1/ε))`-list-decodable.* Via GM-MDS / MDS(ℓ) / generic-zero-pattern condition. | **irrelevant-random-only** | **No.** "Generic" = avoids an algebraic exceptional set; requires `q` exponential in `n`. **No theorem shows a multiplicative coset (or any explicit structured domain) is MDS(ℓ)/generic.** Verified the paper only proves it for *random/generic* placements. |
| 3 | **Brakensiek–Dhar–Gopi** et al., "Randomly Punctured RS … poly-size alphabets" (arXiv 2304.01403) and "Random RS … linear-sized alphabets" (arXiv 2304.09445) | *Randomly punctured RS of rate `R` is `(1−R−ε, O(1/ε))`-list-decodable over alphabet `≥ 2^{poly(1/ε)}·n²` (resp. `O(n)`), w.h.p.* | **irrelevant-random-only** | **No.** Hypothesis is **random puncturing** of the evaluation set. A fixed smooth coset is the opposite of random; nothing transfers. |
| 4 | **Shangguan–Tamo / Goldberg–Shangguan–Tamo**, generalized Singleton & beyond-Johnson (arXiv 1911.01502, 2105.14754; SICOMP) | `L=2`→ radius `⅔(1−R)` (beats Johnson iff `R≥¼`); `L=3`→ `¾(1−R)` (iff `R≥1/9`). **Existence** over exponential fields; explicit construction needs **double-exponential field `2^{k^n}`** with adversarial degree-`k`-extension points. | **adaptable / irrelevant-random-only** | **No.** Optimal small-list results are existential over (double-)exponential fields with hand-picked field-extension points — provably not a multiplicative coset; field size far beyond `q≈n`. |
| 5 | **Ben-Sasson–Kopparty–Radhakrishnan [BKR10]**, "Subspace Polynomials and Limits to List Decoding of RS", IEEE-IT 2010; + Guruswami–Rudra limits chapter | *For the **full field domain `L=F_q`**, a received word agrees with **super-polynomially many** degree-`<k` polynomials* — built from **subspace polynomials** (vanish on **additive** subgroups). Agreement is `< rate` (radius `> 1−R^{1/(2−α)}`), and "must exploit that evaluation points are distinct." | **suggests-counterexample — but does NOT apply here** | **No (for our band).** Two reasons: (i) the domain is the **additive** full field / subspace, not a **multiplicative** coset; (ii) the super-poly list occurs at agreement **below the rate**, i.e. **below the Johnson radius** for `ρ∈{1/2,…,1/16}`. So it does **not** collapse the open band to Johnson for these rates. |
| 6 | **Gopalan–Guruswami–Raghavendra [GGR11]**, "List Decoding Tensor Products and Interleaved Codes", arXiv 0811.4395 / SICOMP | Thm 2.5: `ℓ(C^{⊙m}, η) ≤ \binom{b+r}{r}·ℓ(C,η)^r`, `b=⌈η/(δ−η)⌉`, `r=⌈log δ/(δ−η)⌉`. **Independent of `m`.** | **directly-applicable (this is paper Lemma 2.10)** | **Yes (as the reduction).** It is a generic list-decodability statement for any base code `C`; with `C` = our RS it gives `|Λ(C^{≡m},δ)| ≤ C(b+r,r)·|Λ(C,δ)|^r`, m-independent. It reduces — does not resolve — the frontier. |
| 7 | **Guruswami–Sudan** (GS99) interpolation, Johnson bound | List-decode RS up to `1−√R` (Johnson) in poly time; **provably stops at Johnson** — interpolation breaks down beyond it. | **directly-applicable (lower endpoint only)** | **Yes** — gives the certifiable floor `δ ≥ 1−√ρ` (already in repo as `mds_list_bound` / `johnson_bound`). No GS variant provably exceeds Johnson for a fixed domain. |
| 8 | Interleaved/folded-RS *algorithmic* decoders (e.g. fast decoding of interleaved linearized RS, AIMS amc.2025035; Gabidulin-interleaved interpolation, arXiv 1404.6048) | Algorithmic / average-case unique-or-list decoding radii; many have **exponential worst-case lists** or only *probabilistic* guarantees. | **irrelevant-algorithmic — QUARANTINE** | **No.** These bound *decoder behavior / average case*, not worst-case combinatorial `|Λ|`. Folded-RS capacity results are a *different code* (not plain RS on a coset). Do not transfer. |

---

## 2. The m-independence reduction (GGR 2.10) — corroborated

**Confirmed by the literature.** Paper Lemma 2.10 is exactly **Gopalan–Guruswami–Raghavendra,
Thm 2.5** (arXiv 0811.4395). Verified statement: `ℓ(C^{⊙m},η) ≤ \binom{b+r}{r}·ℓ(C,η)^r` with
`b,r` functions of `(δ,η)` **only** — *crucially independent of the interleaving order `m`*. The
proof is a deletion/rank argument that reduces bounding the `m`-interleaved list to counting
**rank-≤`r`** codewords in a Hamming ball of the *base* code, which is an `m`-free quantity.

**Consequence (as the repo already records honestly).** Interleaving does not move the frontier:
`δ*_{C^{≡m}}` is governed by the base-RS list size `|Λ(RS,δ)|`. The gcd "dimension collapses by
`m·deg D`" route (repo GLD-7/8) does *not* beat this, because the `m`-fold dimension penalty is
offset by the adversary's `m`-fold extra freedom — the structural reason GGR is m-independent. The
`m`-interleaving in the prize is a **red herring**, as framed.

---

## 3. ONE-LINE BOTTOM-LINE VERDICT

**(a) GENUINELY OPEN.** For fixed smooth (multiplicative-coset) plain RS at `ρ∈{1/2,1/4,1/8,1/16}`,
the worst-case combinatorial list size in the band `(1−√ρ, H_q⁻¹(1−ρ)]` is **not importable**
(every published beyond-Johnson positive result needs random/generic evaluation points over
exponential-or-double-exponential fields; none is proven for a structured coset) and **not
resolved-negative** (the only structured-domain super-poly lower bound, BKR10, is *additive*-subspace
over the full field and sits at agreement *below the rate* = below Johnson for these rates). The only
certifiable endpoint for the fixed coset is the **Johnson floor `δ ≥ 1−√ρ`** (Guruswami–Sudan /
`mds_list_bound`).

---

## 4. Most-transferable technique → cleanest finite lemma

**Recommendation: do NOT attempt to cross Johnson in Lean — it is the external open problem.** The
single most transferable *certifiable* technique is the **GGR deletion/rank argument (Lemma 2.10 /
GLD-9)** composed with the **Johnson baseline (GLD-10)**. Concretely:

- **Cleanest finite combinatorial lemma worth formalizing:** "the number of codewords of `C` in a
  Hamming ball of radius `δn` that are **`F`-linearly dependent of rank `≤ r`** is bounded by a
  function of `(δ, δ_min, r)` independent of `m`" — the rank-counting core of GGR 2.10. This is
  finite, instance-checkable via the oracle, and is the lemma that turns GLD-4's crude `(·)^m`
  sandwich into the m-independent `C(b+r,r)·(·)^r` bound.
- **Everything above Johnson stays external** (label: `blocked-by-known-result`, applicability
  `fixed-smooth-domain RS: unknown→open`). No Lean attack has good odds at the band itself; the
  certifiable win is composing GGR's m-independence onto the already-proven Johnson list bound,
  exactly the repo's GLD-9→GLD-10 plan.

---

## 5. Full citations

- Z. Guo, R. Li, C. Shangguan, I. Tamo, M. Wootters. *Improved List-Decodability and List-Recoverability of Reed–Solomon Codes via Tree Packings.* FOCS 2021; SIAM J. Comput. arXiv:2011.04453. https://arxiv.org/abs/2011.04453
- J. Brakensiek, S. Gopi, V. Makam. *Generic Reed-Solomon Codes Achieve List-Decoding Capacity.* STOC 2023; SIAM J. Comput. (2024). arXiv:2206.05256. https://arxiv.org/abs/2206.05256
- *Randomly Punctured Reed-Solomon Codes Achieve the List Decoding Capacity over Polynomial-Size Alphabets.* arXiv:2304.01403. https://arxiv.org/pdf/2304.01403
- *Random Reed-Solomon Codes Achieve List-Decoding Capacity with Linear-Sized Alphabets.* arXiv:2304.09445. https://arxiv.org/pdf/2304.09445
- C. Shangguan, I. Tamo. *Combinatorial list-decoding of Reed-Solomon codes beyond the Johnson radius.* arXiv:1911.01502; *Generalized Singleton Bound …*, SIAM J. Comput. https://arxiv.org/abs/1911.01502 ; https://doi.org/10.1137/20M138795X
- E. Goldberg, C. Shangguan, I. Tamo. *List-decoding and list-recovery of Reed-Solomon codes beyond the Johnson radius for any rate.* arXiv:2105.14754. https://arxiv.org/pdf/2105.14754
- E. Ben-Sasson, S. Kopparty, J. Radhakrishnan. *Subspace Polynomials and Limits to List Decoding of Reed–Solomon Codes.* IEEE Trans. Inf. Theory 56(1), 2010. http://repository.ias.ac.in/89497/
- V. Guruswami, A. Rudra. *Limits to List Decoding Reed-Solomon Codes* (thesis chapter / IEEE-IT). https://cse.buffalo.edu/faculty/atri/papers/coding/thesis-chaps/chap6.pdf
- P. Gopalan, V. Guruswami, P. Raghavendra. *List Decoding Tensor Products and Interleaved Codes.* arXiv:0811.4395; SIAM J. Comput. https://arxiv.org/abs/0811.4395  **(= eprint 2026/680 Lemma 2.10 [GGR11])**
- V. Guruswami, M. Sudan. *Improved decoding of Reed-Solomon and algebraic-geometry codes.* IEEE-IT 1999 [GS99].
- G. Arnon, D. Boneh, G. Fenzi. *Open Problems in List Decoding and Correlated Agreement.* IACR ePrint 2026/680. https://eprint.iacr.org/2026/680

---

## 6. Takeaways for the repo's honesty ledger

- The repo's existing framing is **correct and corroborated**: GGR/Lemma 2.10 is m-independent
  (verified against arXiv 0811.4395), so the prize reduces to base-RS beyond Johnson = external/open.
- The one subtle trap checked and cleared: BKR10's super-poly list **looks** like a structured-domain
  counterexample (`δ*=Johnson`), but it is **additive (full-field subspace)**, not the **multiplicative
  coset** of Def 2.12, and lives at **agreement below the rate** (below Johnson for ρ∈{1/2,…,1/16}).
  So it does **not** resolve the challenge negatively for these rates — the band stays genuinely open.
- All capacity-achieving results are **random/generic over exponential fields** — none certifies a
  fixed smooth coset. Do not import them as if they did.
