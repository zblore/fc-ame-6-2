/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import AME62

/-!
Audit: the headline statement is the same term as Formal Conjectures' `ame_6_2_exists`, and the
proofs use only the three standard axioms. Any failure is an error, so `lake env lean` exits
nonzero. As a control, Formal Conjectures' own declaration must show `sorryAx`, which shows the
axiom check can fail.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some ours := env.find? `AME62.ame_6_2_exists | throwError "AME62.ame_6_2_exists missing"
  let some theirs := env.find? `OpenQuantumProblem35.ame_6_2_exists
    | throwError "OpenQuantumProblem35.ame_6_2_exists missing"
  unless ours.type == theirs.type do
    throwError m!"statements differ: {ours.type} vs {theirs.type}"
  let standard : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [`AME62.ame_6_2_exists, `AME62.prismSign_trace, `AME62.exists_rep_of_card,
      `AME62.repInvFun_repFun, `AME62.controlSign_trace_fails, `AME62.controlState_not_isAME] do
    let axs ← collectAxioms n
    let extra := axs.filter fun a ↦ !standard.contains a
    unless extra.isEmpty do throwError m!"{n} uses axioms outside the standard three: {extra}"
  let fc ← collectAxioms `OpenQuantumProblem35.ame_6_2_exists
  unless fc.contains ``sorryAx do
    throwError "control failed: Formal Conjectures' ame_6_2_exists no longer shows sorryAx"
  logInfo m!"audit passed: statement identical ({ours.type}); standard axioms only; control ok"
