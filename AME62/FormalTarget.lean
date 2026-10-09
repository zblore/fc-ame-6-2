/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import AME62.Existence

/-!
# The Formal Conjectures target

`OpenQuantumProblem35.ame_6_2_exists` in Formal Conjectures states `ExistsAME 6 2` and leaves
it as `sorry`. This file proves the same proposition from the pinned Formal Conjectures
definitions, without using that declaration.
-/

namespace AME62

open OpenQuantumProblem35

/-- The prism state is absolutely maximally entangled. -/
theorem prismState_isAME : IsAME prismState :=
  ⟨prismState_isNormalized, prismState_reduction⟩

/-- An AME(6,2) state exists. -/
theorem ame_6_2_exists : ExistsAME 6 2 :=
  ⟨prismState, prismState_isAME⟩

end AME62
