/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import AME62.Existence

/-!
# Control: the check is not vacuous

Dropping the rung `0 3` from the prism gives a six-qubit graph state, `controlState`. One
kernel-computed traced sign sum (`controlSign_trace_rep_three`) shows that the identity
`prismSign_trace` proves for the prism fails for it (`controlSign_trace_fails`), so
`prismSign_trace` does not hold for a trivial reason. The same entry shows `controlState` is not
AME under Formal Conjectures' definitions (`controlState_not_isAME`).
-/

namespace AME62

open OpenQuantumProblem35

/-- The sign of the prism state without the rung `0 3`. -/
def controlSign (x : Config 6 2) : ℤ :=
  (-1) ^ (∑ i : Fin 6, (x i).val * (x (i + 2)).val +
    ∑ i : Fin 2, (x ⟨i.1 + 1, by omega⟩).val * (x ⟨i.1 + 4, by omega⟩).val)

/-- One entry of the control's trace identity. Keeping the triangle `0 2 4` (representative `3`),
the kept configurations `000` and `100` give `8` where the prism gives `0`: party `0`'s only
remaining neighbours are `2` and `4`, both kept and set to `0`, so flipping it changes no edge. -/
theorem controlSign_trace_rep_three :
    ∑ z : Config (6 - 6 / 2) 2,
        controlSign (permuteConfig (rep 3) (combineFirst (n := 6) (d := 2) (6 / 2)
          (Nat.div_le_self 6 2) ![0, 0, 0] z)) *
        controlSign (permuteConfig (rep 3) (combineFirst (n := 6) (d := 2) (6 / 2)
          (Nat.div_le_self 6 2) ![1, 0, 0] z)) = 8 := by
  decide +kernel

/-- The control fails the identity that `prismSign_trace` proves for the prism. -/
theorem controlSign_trace_fails :
    ¬ ∀ (k : Fin 4) (x y : Config (6 / 2) 2),
      ∑ z : Config (6 - 6 / 2) 2,
          controlSign (permuteConfig (rep k) (combineFirst (n := 6) (d := 2) (6 / 2)
            (Nat.div_le_self 6 2) x z)) *
          controlSign (permuteConfig (rep k) (combineFirst (n := 6) (d := 2) (6 / 2)
            (Nat.div_le_self 6 2) y z)) =
        if x = y then 8 else 0 := by
  intro h
  have := h 3 ![0, 0, 0] ![1, 0, 0]
  rw [controlSign_trace_rep_three] at this
  simp at this

/-- The control state: the prism state without the rung `0 3`. -/
noncomputable def controlState : StateVector 6 2 :=
  mkStateVector fun x ↦ uniformCoeff 64 * (controlSign x : ℂ)

/-- The control state is not AME: after `rep 3`, entry `(000, 100)` of its reduction is `1/8`,
where the maximally mixed state has `0`. -/
theorem controlState_not_isAME : ¬ IsAME controlState := by
  rintro ⟨-, h⟩
  have h3 := h (rep 3)
  unfold HasMaximallyMixedFirstReduction at h3
  have h4 := congrFun (congrFun h3 ![0, 0, 0]) ![1, 0, 0]
  rw [maximallyMixed_apply, if_neg (by decide)] at h4
  unfold reducedDensityFirst at h4
  simp only [permuteState_apply, controlState, amplitude_mul_star] at h4
  rw [← Finset.mul_sum, ← Int.cast_sum, controlSign_trace_rep_three] at h4
  norm_num at h4

end AME62
