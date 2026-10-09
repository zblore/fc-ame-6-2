/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import FormalConjectures.OpenQuantumProblems.«35»

/-!
# A maximally mixed reduction depends only on which parties are kept

`IsAME` asks for a maximally mixed reduction after every permutation of the parties, but the
reduction only sees which parties a permutation sends to the first `m` places. This file proves
that, for any `n`, `d` and `m`:

* a permutation that keeps the first `m` places among themselves preserves a maximally mixed
  reduction (`hasMaximallyMixedFirstReduction_permuteState`): it reorders each block, and the
  trace over the second block is a sum that reordering does not change;
* so a permutation gives a maximally mixed reduction whenever another one that sends the same
  parties to the first `m` places does (`hasMaximallyMixedFirstReduction_of_kept`);
* and a permutation `g` that leaves the state unchanged can be composed in freely
  (`hasMaximallyMixedFirstReduction_of_invariant`).

For six qubits this turns 720 permutations into 20 sets of kept parties, and the symmetry of the
prism turns those into 4.
-/

namespace AME62

open OpenQuantumProblem35

/-- Permuting by `σ` and then by `π` is permuting by `π * σ`. -/
lemma permuteState_permuteState {n d : ℕ} (π σ : Equiv.Perm (Fin n)) (ψ : StateVector n d) :
    permuteState π (permuteState σ ψ) = permuteState (π * σ) ψ := by
  ext x
  simp only [permuteState_apply]
  rfl

section Block

variable {n d m : ℕ} (hm : m ≤ n) (τ : Equiv.Perm (Fin n)) (hτ : ∀ i, (τ i).1 < m ↔ i.1 < m)

/-- How `τ` moves the first `m` parties among themselves. -/
def leftPart (j : Fin m) : Fin m :=
  ⟨(τ (leftIndex hm j)).1, (hτ _).2 (by simp [leftIndex])⟩

include hτ in
/-- `τ` sends each of the last `n - m` parties to one of the last `n - m`. -/
lemma le_rightIndex (j : Fin (n - m)) : m ≤ (τ (rightIndex hm j)).1 := by
  by_contra h
  have := (hτ _).1 (Nat.lt_of_not_le h)
  simp [rightIndex] at this

/-- How `τ` moves the last `n - m` parties among themselves. -/
def rightPart (j : Fin (n - m)) : Fin (n - m) :=
  ⟨(τ (rightIndex hm j)).1 - m, by
    have := (τ (rightIndex hm j)).2
    have := le_rightIndex hm τ hτ j
    omega⟩

/-- `leftPart` is a bijection of the first block; injective is enough on a finite type. -/
lemma leftPart_injective : Function.Injective (leftPart hm τ hτ) := by
  intro j₁ j₂ h
  have h' : τ (leftIndex hm j₁) = τ (leftIndex hm j₂) :=
    Fin.ext (by simpa [leftPart] using congrArg Fin.val h)
  simpa [leftIndex, Fin.ext_iff] using τ.injective h'

/-- `rightPart` is injective, so, as for `leftPart`, a bijection of the second block. -/
lemma rightPart_injective : Function.Injective (rightPart hm τ hτ) := by
  intro j₁ j₂ h
  have h₁ := le_rightIndex hm τ hτ j₁
  have h₂ := le_rightIndex hm τ hτ j₂
  have h' : τ (rightIndex hm j₁) = τ (rightIndex hm j₂) := by
    have := congrArg Fin.val h
    simp only [rightPart] at this
    exact Fin.ext (by omega)
  have := congrArg Fin.val (τ.injective h')
  simp only [rightIndex] at this
  exact Fin.ext (by omega)

/-- Permuting a combined configuration by `τ` permutes each block separately. -/
lemma permuteConfig_combineFirst (x : Config m d) (z : Config (n - m) d) :
    permuteConfig τ (combineFirst m hm x z) =
      combineFirst m hm (x ∘ leftPart hm τ hτ) (z ∘ rightPart hm τ hτ) := by
  funext i
  by_cases hi : i.1 < m
  · have hτi : (τ i).1 < m := (hτ i).2 hi
    simp only [permuteConfig, combineFirst, dif_pos hi, dif_pos hτi, Function.comp]
    rfl
  · have hτi : ¬ (τ i).1 < m := fun h ↦ hi ((hτ i).1 h)
    simp only [permuteConfig, combineFirst, dif_neg hi, dif_neg hτi, Function.comp]
    have hr : rightIndex hm ⟨i.1 - m, by omega⟩ = i := Fin.ext (show m + (i.1 - m) = i.1 by omega)
    congr 1
    exact Fin.ext (by simp [rightPart, hr])

include hτ in
/-- A permutation that keeps the first `m` parties among themselves preserves a maximally mixed
reduction on them. -/
theorem hasMaximallyMixedFirstReduction_permuteState {ψ : StateVector n d}
    (h : HasMaximallyMixedFirstReduction m hm ψ) :
    HasMaximallyMixedFirstReduction m hm (permuteState τ ψ) := by
  unfold HasMaximallyMixedFirstReduction at h ⊢
  ext x y
  set L := leftPart hm τ hτ
  set R := rightPart hm τ hτ
  have hL : Function.Bijective L := Finite.injective_iff_bijective.mp (leftPart_injective hm τ hτ)
  have hR : Function.Bijective fun z : Config (n - m) d ↦ z ∘ R :=
    Finite.injective_iff_bijective.mp
      (Finite.injective_iff_bijective.mp (rightPart_injective hm τ hτ)).2.injective_comp_right
  have hxy : x ∘ L = y ∘ L ↔ x = y := hL.2.injective_comp_right.eq_iff
  calc reducedDensityFirst m hm (permuteState τ ψ) x y
      = ∑ z : Config (n - m) d, ψ (combineFirst m hm (x ∘ L) (z ∘ R)) *
          star (ψ (combineFirst m hm (y ∘ L) (z ∘ R))) := by
        simp only [reducedDensityFirst, permuteState_apply, permuteConfig_combineFirst hm τ hτ]
        rfl
    _ = reducedDensityFirst m hm ψ (x ∘ L) (y ∘ L) :=
        hR.sum_comp fun z ↦ ψ (combineFirst m hm (x ∘ L) z) *
          star (ψ (combineFirst m hm (y ∘ L) z))
    _ = maximallyMixed m d x y := by
        rw [h, maximallyMixed_apply, maximallyMixed_apply]
        simp only [hxy]

end Block

/-- If `π` and `ρ` send the same parties to the first `m` places, `π` gives a maximally mixed
reduction whenever `ρ` does. -/
theorem hasMaximallyMixedFirstReduction_of_kept {n d m : ℕ} (hm : m ≤ n)
    {π ρ : Equiv.Perm (Fin n)} (hkept : ∀ i, (π i).1 < m ↔ (ρ i).1 < m) {ψ : StateVector n d}
    (h : HasMaximallyMixedFirstReduction m hm (permuteState ρ ψ)) :
    HasMaximallyMixedFirstReduction m hm (permuteState π ψ) := by
  have hτ : ∀ i, ((π * ρ⁻¹) i).1 < m ↔ i.1 < m := fun i ↦ by
    simpa using hkept (ρ⁻¹ i)
  have := hasMaximallyMixedFirstReduction_permuteState hm _ hτ h
  rwa [permuteState_permuteState, inv_mul_cancel_right] at this

/-- If `g` leaves `ψ` unchanged, `π` gives a maximally mixed reduction whenever `π * g` does. -/
theorem hasMaximallyMixedFirstReduction_of_invariant {n d m : ℕ} (hm : m ≤ n)
    {π g : Equiv.Perm (Fin n)} {ψ : StateVector n d} (hg : permuteState g ψ = ψ)
    (h : HasMaximallyMixedFirstReduction m hm (permuteState (π * g) ψ)) :
    HasMaximallyMixedFirstReduction m hm (permuteState π ψ) := by
  rwa [← permuteState_permuteState, hg] at h

end AME62
