import Mathlib

/-!
# L7 — the erase-decode tree leaf-count bound (GGR Thm 3.6, standalone)

The combinatorial core of the GGR interleaving bound (paper Lemma 2.10 = GGR Thm 2.5,
arXiv:0811.4395; the leaf count is **Theorem 3.6** there). It is purely arithmetic — no code,
field, or distance — so it lives here as a reusable `Nat` lemma.

Think of `f b r` as the maximum number of leaves of a rooted "erase-decode" tree in which every
root-to-leaf path has at most `b` Blue edges and at most `r` Red edges, every node has at most one
Blue child (unique decoding) and at most `Λ` Red children (the base list size), and White edges are
non-branching (contracted away). The branching recurrence is

    f (b+1) (r+1) ≤ f b (r+1) + Λ · f (b+1) r,   f b 0 ≤ 1,   f 0 (r+1) ≤ Λ · f 0 r.

This file proves any such `f` satisfies `f b r ≤ Nat.choose (b+r) r · Λ^r`, by nested induction and
Pascal's rule (`Nat.choose_succ_succ`). The composition (L1′–L6) supplies a concrete `f` (the tree
leaf count) meeting these inequalities; this lemma turns them into the final bound.
-/

namespace RSGLD.ListDecoding

/-- **L7 (GGR Thm 3.6).** Any leaf-count function `f` obeying the Blue/Red branching recurrence is
bounded by `Nat.choose (b+r) r · Λ^r`. `Λ` is the per-node Red fan-out (the base list size, opaque). -/
theorem treeLeaves_le (Λ : ℕ) (f : ℕ → ℕ → ℕ)
    (h0 : ∀ b, f b 0 ≤ 1)
    (hb0 : ∀ r, f 0 (r + 1) ≤ Λ * f 0 r)
    (hrec : ∀ b r, f (b + 1) (r + 1) ≤ f b (r + 1) + Λ * f (b + 1) r) :
    ∀ b r, f b r ≤ Nat.choose (b + r) r * Λ ^ r := by
  intro b r
  induction r generalizing b with
  | zero => simpa using h0 b
  | succ r ih =>
    -- ih : ∀ b, f b r ≤ Nat.choose (b + r) r * Λ ^ r
    induction b with
    | zero =>
      -- f 0 (r+1) ≤ Λ · f 0 r ≤ Λ · (choose r r · Λ^r) = Λ^(r+1) = choose (r+1) (r+1) · Λ^(r+1)
      calc f 0 (r + 1) ≤ Λ * f 0 r := hb0 r
        _ ≤ Λ * (Nat.choose (0 + r) r * Λ ^ r) := by
              gcongr; exact ih 0
        _ = Nat.choose (0 + (r + 1)) (r + 1) * Λ ^ (r + 1) := by
              simp [Nat.choose_self, pow_succ]; ring
    | succ b ihb =>
      -- ihb : f b (r+1) ≤ choose (b+(r+1)) (r+1) · Λ^(r+1)
      -- ih (b+1) : f (b+1) r ≤ choose ((b+1)+r) r · Λ^r
      have hpascal : Nat.choose (b + 1 + (r + 1)) (r + 1)
          = Nat.choose (b + (r + 1)) (r + 1) + Nat.choose (b + 1 + r) r := by
        have := Nat.choose_succ_succ (b + r + 1) r
        -- (b+r+2).choose (r+1) = (b+r+1).choose r + (b+r+1).choose (r+1)
        have e1 : b + 1 + (r + 1) = (b + r + 1) + 1 := by ring
        have e2 : b + (r + 1) = b + r + 1 := by ring
        have e3 : b + 1 + r = b + r + 1 := by ring
        rw [e1, e2, e3, this, Nat.add_comm]
      calc f (b + 1) (r + 1)
          ≤ f b (r + 1) + Λ * f (b + 1) r := hrec b r
        _ ≤ Nat.choose (b + (r + 1)) (r + 1) * Λ ^ (r + 1)
              + Λ * (Nat.choose (b + 1 + r) r * Λ ^ r) := by
              gcongr
              exact ih (b + 1)
        _ = Nat.choose (b + (r + 1)) (r + 1) * Λ ^ (r + 1)
              + Nat.choose (b + 1 + r) r * Λ ^ (r + 1) := by ring
        _ = (Nat.choose (b + (r + 1)) (r + 1) + Nat.choose (b + 1 + r) r) * Λ ^ (r + 1) := by ring
        _ = Nat.choose (b + 1 + (r + 1)) (r + 1) * Λ ^ (r + 1) := by rw [hpascal]

end RSGLD.ListDecoding
