/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Lean.Meta.Tactic.TryThis
public meta import Batteries.Control.Nondet.Basic
public import Batteries.Linter.UnreachableTactic
public import Mathlib.Tactic.Basic

/-!
# The `hint` tactic.

The `hint` tactic tries the kitchen sink:
it runs every tactic registered via the `register_hint <prio> tac` command
on the current goal, and reports which ones succeed.

## Future work
It would be nice to run the tactics in parallel.
-/

public meta section

open Lean Elab Tactic

open Lean.Meta.Tactic.TryThis

namespace Mathlib.Tactic.Hint

/-- An environment extension for registering hint tactics with priorities. -/
initialize hintExtension :
    SimplePersistentEnvExtension (Nat × TSyntax `tactic) (List (Nat × TSyntax `tactic)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := (·.cons)
    addImportedFn := mkStateFromImportedEntries (·.cons) {}
  }

/--
Definition of `addHint` / `addHint` 的定义

English:
definition addHint
  signature: (prio : Nat) (stx : TSyntax `tactic)
  body: do
  modifyEnv fun env => hintExtension.addEntry env (prio, stx)

中文:
定义 addHint
  签名: (prio : 自然数) (stx : TSyntax `tactic)
  定义体: do
  modifyEnv fun env => hintExtension.addEntry env (prio, stx)
-/
def addHint (prio : Nat) (stx : TSyntax `tactic) : CoreM Unit := do
  modifyEnv fun env => hintExtension.addEntry env (prio, stx)

/--
Definition of `getHints` / `getHints` 的定义

English:
definition getHints
  signature: : CoreM (List (Nat × TSyntax `tactic))
  body: return hintExtension.getState (← getEnv)

中文:
定义 getHints
  签名: : CoreM (List (自然数 × TSyntax `tactic))
  定义体: return hintExtension.getState (← getEnv)

Depends on / 依赖: getEnv, getState, hintExtension, hintExtension.getState, return
-/
def getHints : CoreM (List (Nat × TSyntax `tactic)) :=
  return hintExtension.getState (← getEnv)

open Lean.Elab.Command in
/--
Register a tactic for use with the `hint` tactic, e.g. `register_hint 1000 simp_all`.
The numeric argument specifies the priority: tactics with larger priorities run before
those with smaller priorities. The priority must be provided explicitly.
-/
elab (name := registerHintStx)
    "register_hint" prio:num tac:tactic : command =>
    liftTermElabM do
  let tac : TSyntax `tactic := ⟨tac.raw.copyHeadTailInfoFrom .missing⟩
  let some prio := prio.raw.isNatLit?
    | throwError "expected a numeric literal for priority"
  addHint prio tac

initialize
  Batteries.Linter.UnreachableTactic.ignoreTacticKindsRef.modify fun s => s.insert ``registerHintStx

/--
Definition of `suggestion` / `suggestion` 的定义

English:
definition suggestion
  signature: (tac : TSyntax `tactic) (trees : PersistentArray InfoTree)
  body: do
  -- TODO `addExactSuggestion` has an option to construct `postInfo?`
  -- Factor that out so we can use it here instead of copying and pasting?
  let goals ← getGoals
  let postInfo? ← if goals.isEmpty then pure none else
    let mut str := "\nRemaining subgoals:"
    for g in goals do
      let

中文:
定义 suggestion
  签名: (tac : TSyntax `tactic) (trees : PersistentArray InfoTree)
  定义体: do
  -- TODO `addExactSuggestion` has an option to construct `postInfo?`
  -- Factor that out so we can use it here instead of copying and pasting?
  let goals ← getGoals
  let postInfo? ← if goals.isEmpty then pure none else
    let mut str := "\nRemaining subgoals:"
    for g in goals do
      let
-/
def suggestion (tac : TSyntax `tactic) (trees : PersistentArray InfoTree) : TacticM Suggestion := do
  -- TODO `addExactSuggestion` has an option to construct `postInfo?`
  -- Factor that out so we can use it here instead of copying and pasting?
  let goals ← getGoals
  let postInfo? ← if goals.isEmpty then pure none else
    let mut str := "\nRemaining subgoals:"
    for g in goals do
      let e ← PrettyPrinter.ppExpr (← instantiateMVars (← g.getType))
      str := str ++ Format.pretty ("\n⊢ " ++ e)
    pure (some str)
  /-
  #adaptation_note 2025-08-27
  Suggestion styling was deprecated in lean4#9966.
  We use emojis for now instead.
  -/
  -- let style? := if goals.isEmpty then some .success else none
  let preInfo? := if goals.isEmpty then some "🎉️ " else none
  let suggestions := collectTryThisSuggestions trees
  let suggestion := match suggestions[0]? with
  | some s => s.suggestion
  | none => SuggestionText.tsyntax tac
  return { preInfo?, suggestion, postInfo? }

-- TODO We could run the tactics in parallel.
-- TODO With widget support, could we run the tactics in parallel
-- and do live updates of the widget as results come in?
/--
Definition of `hint` / `hint` 的定义

English:
definition hint
  signature: (stx : Syntax)
  body: withMainContext do
.toList.map (·.2) let tacs := (← getHints).toArray.qsort (·.1 > ·.1)
  let tacs := Nondet.ofList tacs
  let results := tacs.filterMapM fun t : TSyntax `tactic => do
    if let some { msgs, trees, .. } ← observing? (withResetServerInfo (evalTactic t)) then
      if msgs.hasErrors t

中文:
定义 hint
  签名: (stx : Syntax)
  定义体: withMainContext do
.toList.map (·.2) let tacs := (← getHints).toArray.qsort (·.1 > ·.1)
  let tacs := Nondet.ofList tacs
  let results := tacs.filterMapM fun t : TSyntax `tactic => do
    if let some { msgs, trees, .. } ← observing? (withResetServerInfo (evalTactic t)) then
      if msgs.hasErrors t

Depends on / 依赖: withMainContext
-/
def hint (stx : Syntax) : TacticM Unit := withMainContext do
.toList.map (·.2) let tacs := (← getHints).toArray.qsort (·.1 > ·.1)
  let tacs := Nondet.ofList tacs
  let results := tacs.filterMapM fun t : TSyntax `tactic => do
    if let some { msgs, trees, .. } ← observing? (withResetServerInfo (evalTactic t)) then
      if msgs.hasErrors then
        return none
      else
        return some (← getGoals, ← suggestion t trees)
    else
      return none
  let results ← (results.toMLList.takeUpToFirst fun r => r.1.1.isEmpty).asArray
  let results := results.qsort (·.1.1.length < ·.1.1.length)
  addSuggestions stx (results.map (·.1.2))
  match results.find? (·.1.1.isEmpty) with
  | some r =>
    -- We don't restore the entire state, as that would delete the suggestion messages.
    setMCtx r.2.term.meta.meta.mctx
  | none => admitGoal (← getMainGoal)

/--
The `hint` tactic tries every tactic registered using `register_hint <prio> tac`,
and reports any that succeed.
-/
syntax (name := hintStx) "hint" : tactic

@[inherit_doc hintStx]
elab_rules : tactic
  | `(tactic| hint%$tk) => hint tk

end Mathlib.Tactic.Hint
