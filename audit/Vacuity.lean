/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import AME62

/-!
Audit, after csd-lean4's `check-vacuity`: every declaration in `AME62` is used by another one,
except the headline results the project exists to state. Any unused declaration is an error, so
`lake env lean` exits nonzero.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  -- Lean generates equation lemmas (`prismSign.eq_1`, `eq_def`, `eq_unfold`) and congruence
  -- lemmas (`leftPart.congr_simp`), which are not written by hand. They are recognised by name
  -- only: a declaration whose last component is `eq_<digits>`, `eq_def`, `eq_unfold` or
  -- `congr_simp` is skipped. That is a naming rule, not proof that Lean generated it, so these
  -- suffixes are reserved: never use them for a hand-written declaration.
  let isEqnLemma : Name → Bool
    | .str _ s => s == "congr_simp" || s == "eq_def" || s == "eq_unfold" ||
        (s.startsWith "eq_" && s.length > 3 && (s.toList.drop 3).all Char.isDigit)
    | _ => false
  let ours := env.constants.fold (fun (acc : Array Name) n _ ↦
    if (`AME62).isPrefixOf n && !n.isInternal && !isEqnLemma n then acc.push n else acc) #[]
  let headlines : List Name :=
    [`AME62.ame_6_2_exists, `AME62.controlSign_trace_fails, `AME62.controlState_not_isAME]
  let mut used : NameSet := {}
  for n in ours do
    if let some ci := env.find? n then
      let v := match ci with
        | .thmInfo t => t.value.getUsedConstants
        | .defnInfo d => d.value.getUsedConstants
        | _ => #[]
      for m in ci.type.getUsedConstants ++ v do
        if m != n then used := used.insert m
  let unused := ours.filter fun n ↦ !used.contains n && !headlines.contains n
  unless unused.isEmpty do throwError m!"unused declarations: {unused.toList}"
  unless ours.size ≥ 10 do throwError m!"only {ours.size} declarations found; wrong prefix?"
  logInfo m!"vacuity audit passed: {ours.size} declarations, none unused apart from the headlines"
