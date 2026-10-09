/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import AME62.Cover
import AME62.Reduction
import AME62.State

/-!
# Every three-party reduction of the prism state is maximally mixed

For each of the four representatives `rep k`, an entry of the reduction is `1/64` times the traced
sum of sign products, and `prismSign_trace` says that sum is `8` on the diagonal and `0` off it. So
every entry is `1/8` or `0`, which is the maximally mixed state on three qubits. Any other
permutation `π`, composed with some rotation, keeps the same parties as a representative
(`exists_rep`), so `π` composed with that rotation has a maximally mixed reduction
(`hasMaximallyMixedFirstReduction_of_kept`). The rotation leaves the prism state unchanged, so `π`
has one too (`hasMaximallyMixedFirstReduction_of_invariant`).
-/

namespace AME62

open OpenQuantumProblem35

/-- One term of the reduction: the product of two amplitudes is `1/64` times the product of
their signs. -/
lemma amplitude_mul_star (a b : ℤ) :
    uniformCoeff 64 * (a : ℂ) * star (uniformCoeff 64 * (b : ℂ)) =
      (64 : ℂ)⁻¹ * ((a * b : ℤ) : ℂ) := by
  have h : uniformCoeff 64 * star (uniformCoeff 64) = (64 : ℂ)⁻¹ := by
    simpa using uniformCoeff_mul_star 64
  rw [← h, star_mul', star_intCast]
  push_cast
  ring

/-- After each representative permutation, the prism state has a maximally mixed reduction on
the first three parties. -/
theorem prismState_reduction_rep (k : Fin 4) :
    HasMaximallyMixedFirstReduction (n := 6) (d := 2) (6 / 2) (Nat.div_le_self 6 2)
      (permuteState (rep k) prismState) := by
  unfold HasMaximallyMixedFirstReduction
  ext x y
  rw [maximallyMixed_apply]
  unfold reducedDensityFirst
  simp only [permuteState_apply, prismState_apply, amplitude_mul_star]
  rw [← Finset.mul_sum, ← Int.cast_sum, prismSign_trace]
  split_ifs <;> norm_num [card_config]

/-- After any permutation of the parties, the prism state has a maximally mixed reduction on
the first three parties. -/
theorem prismState_reduction (π : Equiv.Perm (Fin 6)) :
    HasMaximallyMixedFirstReduction (n := 6) (d := 2) (6 / 2) (Nat.div_le_self 6 2)
      (permuteState π prismState) := by
  obtain ⟨a, k, hk⟩ := exists_rep π
  exact hasMaximallyMixedFirstReduction_of_invariant _ (permuteState_rotate_prismState a)
    (hasMaximallyMixedFirstReduction_of_kept _ hk (prismState_reduction_rep k))

end AME62
