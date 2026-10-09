/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import AME62.Sign

/-!
# The six-qubit prism state

Every amplitude is `±1/8`, with the sign given by `prismSign`.
-/

namespace AME62

open OpenQuantumProblem35

/-- The six-qubit prism graph state. -/
noncomputable def prismState : StateVector 6 2 :=
  mkStateVector fun x ↦ uniformCoeff 64 * (prismSign x : ℂ)

@[simp]
lemma prismState_apply (x : Config 6 2) :
    prismState x = uniformCoeff 64 * (prismSign x : ℂ) := rfl

/-- Rotating the parties leaves the prism state unchanged. -/
lemma permuteState_rotate_prismState (a : Fin 6) :
    permuteState (Equiv.addRight a) prismState = prismState := by
  ext x
  simp [permuteState_apply, prismSign_rotate]

/-- Every sign has norm one. -/
lemma norm_prismSign (x : Config 6 2) : ‖(prismSign x : ℂ)‖ = 1 := by
  simp [prismSign]

/-- The prism state is normalized: 64 amplitudes, each of squared norm `1/64`. -/
lemma prismState_isNormalized : IsNormalized prismState := by
  rw [isNormalized_iff_norm_sq_eq_one]
  calc ‖prismState‖ ^ 2 = ∑ x : Config 6 2, ‖prismState x‖ ^ 2 := by
        simpa using EuclideanSpace.norm_sq_eq prismState
    _ = ∑ _x : Config 6 2, ‖uniformCoeff 64‖ ^ 2 := by
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        rw [prismState_apply, norm_mul, norm_prismSign, mul_one]
    _ = 1 := by
        simp [Finset.sum_const, uniformCoeff_norm_sq]

end AME62
