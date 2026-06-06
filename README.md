# rs-gld-formalization

A Lean 4 / Mathlib formalization of a Reed–Solomon interleaving list-size reduction, together with
a smooth-coset obstruction to importing generic Reed–Solomon capacity methods.

This repository concerns the **grand list-decoding problem** for interleaved Reed–Solomon codes,
roughly:

> If many interleaved Reed–Solomon codewords are close to a received word, how large can that list be?

> **In one sentence:** interleaving reduces to base RS; smooth cosets are not generic; the true
> base-RS frontier remains open.

The headline Lean theorems are `sorry`-free and depend only on Lean's three foundational axioms
(`propext`, `Classical.choice`, `Quot.sound`), verified by `./scripts/check_axioms.sh`. Everything
builds with `lake build`.

---

# A Sharper Look at Grand List Decoding

> These notes summarize what we found after formalizing the interleaving reduction for Reed–Solomon list decoding.
>
> The background notes explain Reed–Solomon codes, Hamming balls, interleaving, and the Johnson radius.

---

## 0. The question

Let

$$C = RS[\mathbb{F},L,k]$$

be a Reed–Solomon code.

The Grand List Decoding problem asks about the interleaved code

$$C^{\equiv m}.$$

For a target parameter

$$\varepsilon^* = 2^{-128},$$

and constant $m$, the goal is to determine the largest radius

$$\delta_C^*$$

such that

$$|\Lambda(C^{\equiv m},\delta_C^*)| \le \varepsilon^*|\mathbb{F}|.$$

In words:

> How far can a received word be from the interleaved Reed–Solomon code while still guaranteeing that the number of nearby codewords is small?

The classical safe point is the Johnson radius:

$$1-\sqrt{\rho},$$

where

$$\rho = k/n.$$

The natural ceiling is roughly

$$1-\rho.$$

So the interesting region is the Johnson-to-capacity band:

$$1-\sqrt{\rho}<\delta<1-\rho.$$

The central question is:

> Can we control the list size of interleaved Reed–Solomon codes in this band?

---

## 1. The main reduction

The first result is the GGR interleaving list-size reduction, formalized as
[`interleave_list_size_ggr`](RSGLD/ListDecoding/InterleavedListSize.lean#L46).

It says:

$$|\Lambda(C^{\equiv m},E)| \le \binom{b+r}{r}|\Lambda(C,E)|^r.$$

This is the main formalized theorem.

It should be read as follows:

> The interleaved list size is controlled by the ordinary base-code list size.

So the interleaved problem does not need to be attacked directly.

Instead, it reduces to the base Reed–Solomon quantity

$$B_C(E)=\max_w|\Lambda(C,w,E)|.$$

That is the worst-case number of ordinary Reed–Solomon codewords inside a Hamming ball of radius $E$.

The reduction gives the implication:

$$B_C(E)\le B \quad\Longrightarrow\quad |\Lambda(C^{\equiv m},E)| \le \binom{b+r}{r}B^r.$$

Therefore the Grand List Decoding target follows if

$$\binom{b+r}{r}B^r \le 2^{-128}|\mathbb{F}|.$$

This is the first important point:

> Interleaving is not the main mystery anymore.
>
> The remaining mystery is the base Reed–Solomon list size.

---

## 2. What was formalized

The GGR reduction was formalized in Lean.

The proof is based on an erase-decode tree.

At a high level, the proof does the following:

1. Decode one interleaved column at a time.
2. Track which positions have already been erased.
3. Classify search-tree edges as white, blue, or red.
4. Show that white edges do not branch.
5. Show that blue edges can happen only a bounded number of times.
6. Show that red edges can happen only a bounded number of times.
7. Count the possible leaves of the tree.

The tree-counting part gives the binomial factor

$$\binom{b+r}{r}.$$

The result is machine-checked in Lean and axiom-clean in the repository. The tree leaf-count is
[`treeLeaves_le`](RSGLD/ListDecoding/TreeCount.lean#L26); the assembled bound is
[`maxListSize_interleave_le_int`](RSGLD/ListDecoding/GGRComposition.lean#L358), re-exported as
[`interleave_list_size_ggr`](RSGLD/ListDecoding/InterleavedListSize.lean#L46).

This matters because the reduction is now not just a citation or an informal dependency. It is a verified step in the chain:

```text
base RS list-size bound
        ↓
GGR interleaving reduction
        ↓
interleaved RS list-size bound
```

---

## 3. What changed?

Before this reduction, the problem looked like:

```text
Understand the list size of C^{≡m}.
```

After the reduction, the problem becomes:

```text
Understand the list size of C.
```

More precisely, it becomes:

$$B_C(\delta)=\max_w|\Lambda(C,w,\delta)|.$$

That is a cleaner object.

It removes the interleaving layer and isolates the true bottleneck:

> fixed-domain base Reed–Solomon list size beyond Johnson.

This is the main conceptual progress.

The Grand List Decoding problem is not solved, but it has been narrowed.

---

## 4. The Muralidhara–Sen plug-in

There is a known theorem of Muralidhara and Sen that gives an above-Johnson bound for ordinary Reed–Solomon codes.

The Johnson radius in block-length form is roughly

$$n-\sqrt{nk}.$$

Muralidhara–Sen gives a polynomial list-size bound at

$$E=n-\sqrt{nk}+c,$$

where $c$ is a constant.

So the base-code list size satisfies a bound of the form

$$B_C(E)\le n^D$$

for that radius.

Plugging this into the formalized GGR reduction gives

$$|\Lambda(C^{\equiv m},E)| \le \binom{b+r}{r}n^{Dr}.$$

Thus the target inequality

$$|\Lambda(C^{\equiv m},E)| \le 2^{-128}|\mathbb{F}|$$

holds whenever

$$2^{128}\binom{b+r}{r}n^{Dr} \le |\mathbb{F}|.$$

So we obtain a rigorous lower bound

$$\delta_C^* \ge 1-\sqrt{\rho}+O(1/n)$$

for sufficiently large field size.

The composition is formalized as
[`gld_field_size_slightly_above_johnson_of_MS`](RSGLD/ListDecoding/MuralidharaSenPlugin.lean#L58)
(general form: [`interleaved_field_size_condition_of_base_poly_bound`](RSGLD/ListDecoding/MuralidharaSenPlugin.lean#L37)).
The Muralidhara–Sen bound itself is taken as a hypothesis, not re-proved here.

This is a real above-Johnson consequence. But it is important to understand its size.

---

## 5. Why this is only slightly above Johnson

The Muralidhara–Sen radius is

$$E=n-\sqrt{nk}+c.$$

Divide by $n$:

$$\frac{E}{n}=1-\sqrt{\frac{k}{n}}+\frac{c}{n}.$$

Since

$$\rho=\frac{k}{n},$$

this becomes

$$\frac{E}{n}=1-\sqrt{\rho}+\frac{c}{n}.$$

The improvement beyond Johnson is

$$\frac{c}{n}.$$

That is why we write

$$O(1/n).$$

It means the improvement shrinks as the block length grows.

For example, if $n=1{,}000{,}000$ and $c=3$, then

$$\frac{c}{n}=\frac{3}{1{,}000{,}000}.$$

So Muralidhara–Sen gives a real but very small movement past Johnson.

It is not a constant-radius breakthrough.

---

## 6. The stronger hope: import generic RS capacity

There is another possible route.

Modern random or generic Reed–Solomon results can reach much stronger list-decoding behavior.

A natural hope was:

> Maybe smooth roots-of-unity domains behave enough like generic domains, so generic RS capacity methods can be imported.

This would be powerful because smooth domains are the domains used in fast Reed–Solomon and FRI-style settings.

The relevant smooth domain is

$$L=\mu_{2^s}.$$

This is the set of $2^s$-th roots of unity.

These domains are highly structured, FFT-friendly, and widely used.

The question was:

> Do these smooth domains satisfy the same genericity conditions used in random/generic Reed–Solomon capacity proofs?

The answer we found is no.

---

## 7. The obstruction: smooth cosets fail higher-order MDS

Generic Reed–Solomon capacity arguments rely on higher-order MDS-type conditions.

Very roughly, higher-order MDS says:

> Several spans of Reed–Solomon columns intersect only as much as random spans would.

Smooth roots-of-unity domains fail this condition.

The reason is simple and explicit.

Let $H_d$ be the order-$d$ subgroup of $\mu_n$.

A coset has the form

$$\omega^tH_d.$$

The polynomial that vanishes on this coset is

$$V_{\omega^tH_d}(X)=X^d-\omega^{td}.$$

This is a binomial.

It has only two terms.

So it lies in

$$\operatorname{span}\{1,X^d\}.$$

Therefore three such vanishing polynomials are linearly dependent. (This linear-dependence identity is the machine-checked core, [`binom_three_dependent`](RSGLD/SmoothCosetMDS.lean#L39).)

This creates a higher-order MDS failure.

More generally, for suitable subcosets $A_t$,

$$\dim\left(\bigcap_tG_{A_t}\right)=\max(0,2d-k).$$

A strict defect occurs when

$$d>k/2 \quad\text{and}\quad \ell\ge3.$$

Thus

$$RS[\mu_{2^s},k]$$

fails higher-order MDS for every $\ell\ge3$.

This is the second major finding:

> Smooth roots-of-unity domains are not generic in the higher-order-MDS sense.

---

## 8. The simplest example: pairs x and −x

The obstruction is easiest to see using pairs.

Suppose the domain contains both $x$ and $-x$.

Then the pair

$$\{x,-x\}$$

has vanishing polynomial

$$(X-x)(X+x)=X^2-x^2.$$

The middle term cancels.

Normally,

$$(X-a)(X-b)=X^2-(a+b)X+ab.$$

But if $b=-a$, then

$$a+b=0.$$

So the $X$ term disappears.

This means every pair $\{x,-x\}$ gives a polynomial of the form

$$X^2-c.$$

All such polynomials live in the two-dimensional space

$$\operatorname{span}\{1,X^2\}.$$

Three such polynomials must be linearly dependent.

This is the smallest instance of the smooth-coset obstruction.

---

## 9. Why this obstruction matters

The obstruction matters because it blocks a proof strategy.

The desired strategy was:

```text
generic/random RS capacity theorem
        ↓
show smooth cosets satisfy the same genericity condition
        ↓
obtain smooth-domain base-RS list-size bound
        ↓
apply GGR reduction
        ↓
obtain interleaved list-size bound
```

The smooth-coset result breaks this path at the second step.

Smooth cosets do not satisfy the required higher-order MDS condition.

So the generic/random RS proof machinery cannot be imported directly.

This does not prove that smooth domains have bad list decoding.

It proves that this particular route does not work.

---

## 10. Does the obstruction give a counterexample?

Not by itself.

The natural received word is

$$w(x)=x^d.$$

On each subgroup coset, $x^d$ is constant.

Therefore constant polynomials agree with $w$ on whole cosets.

This gives a list of size

$$n/d.$$

At first this looks like a possible large-list construction.

But the list-size fallout is mild.

There are two regimes.

---

## 11. Regime one: d < k

This is where the higher-order-MDS defect occurs.

The agreement is

$$a=d.$$

Since

$$d<k,$$

the agreement is below the code dimension.

The relative radius is

$$\delta=1-d/n.$$

Because $d<k$,

$$\delta>1-k/n=1-\rho.$$

So the witness lies beyond the capacity-style ceiling.

It is outside the useful Johnson-to-capacity band.

The defect is real, but this witness does not determine $\delta_C^*$.

---

## 12. Regime two: d > k

To enter the Johnson-to-capacity band, we need agreement greater than $k$.

That means

$$d>k.$$

But then the list size becomes

$$n/d<n/k=1/\rho.$$

For fixed rate $\rho$, this is just a constant.

For example, if

$$\rho=1/16,$$

then

$$1/\rho=16.$$

So the list size is at most about 16.

That is not a large-list counterexample.

---

## 13. What this tells us

The smooth-coset obstruction says:

> Smooth roots-of-unity domains are structurally non-generic.

But it also says:

> The obvious subgroup-binomial defect is too mild to solve the Grand List Decoding problem.

So it gives both a negative and a positive clarification.

It blocks the generic-RS import route.

But it also shows that the simplest smooth-coset defect does not create a large list in the useful band.

That narrows the problem.

---

## 14. The remaining open core

After these findings, the remaining theorem is precise.

We need to understand

$$B_C(\delta)=\max_w|\Lambda(RS[\mathbb{F},L,k],w,\delta)|$$

for smooth domains such as

$$L=\mu_{2^s}$$

in the band

$$1-\sqrt{\rho}<\delta<1-\rho.$$

If one proves

$$B_C(\delta)\le\operatorname{poly}(n)$$

or

$$B_C(\delta)\le O(1)$$

for a useful beyond-Johnson radius, then the GGR reduction immediately gives an interleaved result.

If one constructs

$$B_C(\delta)>2^{-128}|\mathbb{F}|,$$

then that gives a negative result.

This is the true remaining frontier:

> base smooth-domain Reed–Solomon list size beyond Johnson.

---

## 15. The whole story

```text
Original target:
  list size of interleaved RS C^{≡m}

        |
        | GGR reduction
        v

Base RS target:
  B_C(δ) = worst-case ordinary RS list size

        |
        | Muralidhara–Sen
        v

Slightly above Johnson:
  δ ≥ 1 - sqrt(ρ) + O(1/n)

        |
        | try generic/random RS capacity machinery?
        v

Blocked:
  smooth cosets fail higher-order MDS

        |
        v

Remaining open core:
  smooth-domain base RS list size beyond Johnson
```

---

## 16. Short version

The formalized GGR theorem says

$$|\Lambda(C^{\equiv m},E)|\le\binom{b+r}{r}|\Lambda(C,E)|^r.$$

So interleaved list decoding reduces to base Reed–Solomon list decoding.

Muralidhara–Sen gives a small above-Johnson base-code bound:

$$\delta\ge1-\sqrt{\rho}+O(1/n).$$

Smooth roots-of-unity domains fail higher-order MDS because subgroup cosets have binomial vanishing polynomials:

$$X^d-c.$$

This blocks the direct import of generic/random Reed–Solomon capacity proofs.

However, the natural list-decoding witness from this defect only gives constant-size lists in the useful band.

Therefore, the remaining missing theorem is still:

$$\text{base smooth-domain Reed–Solomon list size beyond Johnson}.$$

---

## 17. One-sentence version

The interleaved problem reduces to ordinary Reed–Solomon list decoding; Muralidhara–Sen gives a tiny above-Johnson positive result; smooth roots-of-unity domains are provably non-generic, but their obvious defect is too mild to solve the problem, leaving base smooth-domain Reed–Solomon list size beyond Johnson as the central remaining obstacle.

---

## Build and verify

Requires [`elan`](https://github.com/leanprover/elan). The toolchain (`leanprover/lean4:v4.29.0`)
and Mathlib revision are pinned in `lean-toolchain` and `lake-manifest.json`.

```bash
lake exe cache get      # fetch prebuilt Mathlib oleans (fast)
lake build              # build the whole closure: green, zero sorry, zero new axioms

./scripts/check_axioms.sh                            # assert the headline theorems are axiom-clean
python3 -V && ./scripts/reproduce_experiments.sh     # reproduce the finite-field experiments
```

---

## Theorem map

Each declaration links directly to the line that proves it.

| Statement | Lean declaration (click to view proof) |
|---|---|
| Interleaving reduction (core) | [`interleave_list_size_ggr`](RSGLD/ListDecoding/InterleavedListSize.lean#L46) |
| Integer interleaving bound | [`maxListSize_interleave_le_int`](RSGLD/ListDecoding/GGRComposition.lean#L358) |
| Erase-decode tree leaf count | [`treeLeaves_le`](RSGLD/ListDecoding/TreeCount.lean#L26) |
| Erase-decode budget invariant | [`Inv`](RSGLD/ListDecoding/EraseDecode.lean#L85) |
| Base bound ⇒ field-size condition | [`interleavedRS_field_size_condition_of_base_bound`](RSGLD/ListDecoding/BaseRSReduction.lean#L48) |
| Muralidhara–Sen polynomial plug-in | [`interleaved_field_size_condition_of_base_poly_bound`](RSGLD/ListDecoding/MuralidharaSenPlugin.lean#L37) |
| Slightly-above-Johnson corollary | [`gld_field_size_slightly_above_johnson_of_MS`](RSGLD/ListDecoding/MuralidharaSenPlugin.lean#L58) |
| Binomial dependence (MDS obstruction) | [`binom_three_dependent`](RSGLD/SmoothCosetMDS.lean#L39) |

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
