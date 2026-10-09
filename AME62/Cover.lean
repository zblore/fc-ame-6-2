/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import AME62.Sign

/-!
# Every permutation, after a rotation, keeps the same parties as a representative

A permutation `π` keeps party `i` in the reduction when it sends `i` to one of the first three
places. Exactly three parties are kept, and each set of three is a rotation of the set kept by
one of the four `rep k`.
-/

namespace AME62

/-- A permutation keeps exactly three of the six parties. -/
lemma card_kept (π : Equiv.Perm (Fin 6)) :
    (Finset.univ.filter fun i ↦ (π i).1 < 6 / 2).card = 3 := by
  have : (Finset.univ.filter fun i ↦ (π i).1 < 6 / 2) =
      (Finset.univ.filter fun j : Fin 6 ↦ j.1 < 6 / 2).map π.symm.toEmbedding := by
    ext i
    simp [Finset.mem_map_equiv]
  rw [this, Finset.card_map]
  decide

/-- Each set of three parties, given by its indicator `b`, is a rotation of the set kept by some
representative. Checked by the kernel over the 64 indicators. -/
lemma exists_rep_of_card (b : Fin 6 → Bool)
    (hb : (Finset.univ.filter fun i ↦ b i = true).card = 3) :
    ∃ a : Fin 6, ∃ k : Fin 4, ∀ i, b (i + a) = decide ((repFun k i).1 < 6 / 2) := by
  revert b
  decide +kernel

/-- Every permutation, after a rotation, keeps the same parties as some representative. -/
theorem exists_rep (π : Equiv.Perm (Fin 6)) :
    ∃ a : Fin 6, ∃ k : Fin 4,
      ∀ i, ((π * Equiv.addRight a) i).1 < 6 / 2 ↔ (rep k i).1 < 6 / 2 := by
  obtain ⟨a, k, hk⟩ := exists_rep_of_card (fun i ↦ decide ((π i).1 < 6 / 2))
    (by simpa using card_kept π)
  exact ⟨a, k, fun i ↦ by simpa [rep] using hk i⟩

end AME62
