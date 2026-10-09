/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import FormalConjectures.OpenQuantumProblems.«35»

/-!
# The sign pattern of the six-qubit prism state

The prism graph on parties `0, …, 5` has the two triangles `0 2 4` and `1 3 5` and the three
rungs `0 3`, `1 4`, `2 5`. Its graph state has amplitude proportional to `(-1) ^ e`, where `e`
counts the edges with both ends set to `1`.

This file proves the two finite facts the AME proof needs.

* Rotating the parties, `i ↦ i + a`, maps the prism to itself, so it does not change the sign
  (`prismSign_rotate`).
* For four permutations `rep k`, which keep the parties `0 1 2`, `0 1 3`, `0 1 4` and `0 2 4`,
  summing the product of two signs over the three traced parties gives `8` when the two kept
  configurations agree and `0` otherwise (`prismSign_trace`).

Every set of three parties is a rotation of one of those four, and `AME62/Cover.lean` and
`AME62/Reduction.lean` turn that into all 720 permutations.
-/

namespace AME62

open OpenQuantumProblem35

/-- The number of prism edges with both ends set to `1` in `x`: the six triangle edges
`{i, i + 2}` and the three rungs `{i, i + 3}`. -/
def prismParity (x : Config 6 2) : ℕ :=
  ∑ i : Fin 6, (x i).val * (x (i + 2)).val +
    ∑ i : Fin 3, (x ⟨i.1, by omega⟩).val * (x ⟨i.1 + 3, by omega⟩).val

/-- The sign of the prism state at `x`. -/
def prismSign (x : Config 6 2) : ℤ :=
  (-1) ^ prismParity x

/-- Rotating the parties maps the prism to itself. Checked by the kernel over the six
rotations and 64 configurations. -/
theorem prismSign_rotate (a : Fin 6) (x : Config 6 2) :
    prismSign (permuteConfig (Equiv.addRight a) x) = prismSign x := by
  revert a x
  decide +kernel

/-- Four permutations, keeping the parties `0 1 2`, `0 1 3`, `0 1 4` and `0 2 4`. The `k`-th
sends its three kept parties, in order, to places `0, 1, 2`, and the other three, in order, to
places `3, 4, 5`. -/
def repFun : Fin 4 → Fin 6 → Fin 6 :=
  ![![0, 1, 2, 3, 4, 5], ![0, 1, 3, 2, 4, 5], ![0, 1, 3, 4, 2, 5], ![0, 3, 1, 4, 2, 5]]

/-- The inverse of `repFun k`: row `k` lists the three kept parties, then the other three. -/
def repInvFun : Fin 4 → Fin 6 → Fin 6 :=
  ![![0, 1, 2, 3, 4, 5], ![0, 1, 3, 2, 4, 5], ![0, 1, 4, 2, 3, 5], ![0, 2, 4, 1, 3, 5]]

lemma repInvFun_repFun : ∀ (k : Fin 4) (i : Fin 6), repInvFun k (repFun k i) = i := by
  decide

lemma repFun_repInvFun : ∀ (k : Fin 4) (i : Fin 6), repFun k (repInvFun k i) = i := by
  decide

/-- The four representative permutations. -/
def rep (k : Fin 4) : Equiv.Perm (Fin 6) where
  toFun := repFun k
  invFun := repInvFun k
  left_inv := repInvFun_repFun k
  right_inv := repFun_repInvFun k

/-- The finite core: for each representative, the traced sum of sign products is `8` on the
diagonal and `0` off it. Checked by the kernel: `4 × 8 × 8 × 8` sign products. Stated with
`6 / 2` and `6 - 6 / 2`, as in Formal Conjectures' `IsAME`, so that it rewrites directly inside
`HasMaximallyMixedFirstReduction`. -/
theorem prismSign_trace (k : Fin 4) (x y : Config (6 / 2) 2) :
    ∑ z : Config (6 - 6 / 2) 2,
        prismSign (permuteConfig (rep k) (combineFirst (n := 6) (d := 2) (6 / 2)
          (Nat.div_le_self 6 2) x z)) *
        prismSign (permuteConfig (rep k) (combineFirst (n := 6) (d := 2) (6 / 2)
          (Nat.div_le_self 6 2) y z)) =
      if x = y then 8 else 0 := by
  revert k x y
  decide +kernel

end AME62
