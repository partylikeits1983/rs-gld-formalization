# GLD-9 Milestone — GGR Lemma 2.10 fully proved in-repo (2026-06-05)

**The `m`-interleaving bound of the grand list-decoding challenge is machine-checked, axiom-clean.**
This was the one tractable in-repo direction the literature triage identified; it is now complete.

## Theorem (integer parameterized form — the durable statement)

`RSGLD.ListDecoding.maxListSize_interleave_le_int` (re-exported as `interleave_list_size_ggr`):

> For a linear code `C ⊆ F^n` (`F` finite, `0 < n`), integer error radius `E < D` with
> `(D:ℝ) ≤ minDist C · n`, and `b r : ℕ` (write `G := D − E`) satisfying
> ```
>     E ≤ b·G        and        D ≤ 2^r·G,
> ```
> then for every interleaving order `m ≥ 1`:
> ```
>     maxListSize (interleave C m) (E/n)  ≤  Nat.choose (b+r) r · (maxListSize C (E/n))^r.
> ```

The bound is **independent of `m`**. `G = D − E` (the integer gap). The base list size
`maxListSize C (E/n)` enters only as an opaque parameter `Λ` — no base-RS beyond-Johnson math.

This is **paper Lemma 2.10 (eprint 2026/680) = Gopalan–Guruswami–Raghavendra Theorem 2.5**
(arXiv:0811.4395), with leaf count their **Theorem 3.6**. (GGR "Theorem 2.10" is a different result
about linear transformations — not cited here.)

## Proof components (all axiom-clean: `[propext, Classical.choice, Quot.sound]`)

Erase-decode tree (NOT the rank/generalized-Hamming-weight route, which is GGR's binary-only
Thms 2.6–2.9). Integer-count throughout.

| Leaf | Statement | File · name |
|---|---|---|
| **L7** | tree leaf count `≤ binom(b+r,r)·Λ^r` (GGR Thm 3.6) | `TreeCount.lean` · `treeLeaves_le` |
| **invariant** | `Inv := s≤E ∧ E≤s+bG ∧ D≤s+2^rG`; white/blue/red transitions | `EraseDecode.lean` · `Inv`, `Inv.white/blue/red` |
| **L1′** | distinct codewords differ on `≥ D−|S|` outside `S` | `EraseDecode.lean` · `D_sub_card_le_hammingDistOutside` |
| **L3/L4** | white-edge / blue-edge uniqueness | `EraseDecode.lean` · `white_unique`, `blue_unique` |
| **B** | column-split count decomposition | `GGRComposition.lean` · `Ninter_succ_le` |
| **A** | global base list size = per-node fan-out | `GGRComposition.lean` · `baseListCount`, `card_baseList_le_baseListCount` |
| **C** | the erase-decode induction (white / no-white Pascal split) | `GGRComposition.lean` · `Ninter_le` |
| **E** | bridge `Ninter` → `maxListSize` + the integer theorem | `GGRComposition.lean` · `interleaveColsEquiv`, `listAt_interleave_card_eq_Ninter`, `maxListSize_interleave_le_int` |

Key method (math-agent confirmed): integer-count invariant; trichotomy on new erasures `w`
(`white: w<G`; `blue: G≤w ∧ 2w<D−s`; `red: G≤w ∧ D−s≤2w`); **white is a non-branching path edge, NOT
a Pascal summand** — the Pascal recurrence `N(b,r) ≤ N(b−1,r)+Λ·N(b,r−1)` applies only in the
no-white case; red depth via gap-halving `2(D−s') ≤ D−s` (no logs in the core).

## Consequences

- The GLD-9 `sorry` is **removed**. `interleave_list_size_ggr` re-exports the proven core.
- **GLD-11** (`interleavedRS_field_size_condition_of_base_bound`, `BaseRSReduction.lean`) is now **unconditional,
  axiom-clean**: the interleaved-RS Grand List Decoding target reduces, with no `sorry`, to a single base-RS bound `B`.
- Proven files moved out of `Conjectures/` into `RSGLD/ListDecoding/`.

## Audit

- `#print axioms` of `treeLeaves_le`, `Ninter_le`, `maxListSize_interleave_le_int`,
  `interleave_list_size_ggr`, `interleavedRS_field_size_condition_of_base_bound` → `[propext, Classical.choice,
  Quot.sound]` only.
- Full `lake build` green (8302 jobs). No `sorry` in `RSGLD/ListDecoding/`.
- Tags: `gld9-leaves-checkpoint`, `gld9-proved`. Commits `b50ee7f` (Ninter_le) → `59d4592` (integer
  theorem) → `4930205` (discharge) → milestone-lock (move out of Conjectures).

## Deferred (optional, not needed)

Real `δ,η` / `⌈log₂⌉` wrapper (`b=⌈η/(δ−η)⌉`, `r=⌈log₂(δ/(δ−η))⌉`). The integer/`E/n` form is
mathematically stronger and connects to the Grand List Decoding target directly; the ceiling/log wrapper is cosmetic and
would only add floor-arithmetic churn. **TODO (optional polish):** derive the real `δ,η` wrapper from
the integer theorem if a later Grand List Decoding theorem needs it.
