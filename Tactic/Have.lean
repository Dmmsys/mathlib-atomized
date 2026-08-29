/-
Copyright (c) 2022 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Edward Ayers, Mario Carneiro
-/
module

public import Mathlib.Init
public meta import Lean.Elab.Binders
public meta import Lean.Elab.SyntheticMVars
public meta import Lean.Meta.Tactic.Assert

/-!
# Extending `have`, `let` and `suffices`

This file extends the `have`, `let` and `suffices` tactics to allow the addition of hypotheses to
the context without requiring their proofs to be provided immediately.

As a style choice, this should not be used in mathlib; but is provided for downstream users who
preferred the old style.
-/

public meta section

namespace Mathlib.Tactic
open Lean Elab.Tactic Meta Parser Term Syntax.MonadTraverser

/--
Definition of `optBinderIdent` / `optBinderIdent` 的定义

English:
definition optBinderIdent
  signature: : Parser
  body: leading_parser
  -- Note: the withResetCache is because leading_parser seems to add a cache boundary,
  -- which causes the `hygieneInfo` parser not to be able to undo the trailing whitespace
(ppSpace >> Term.binderIdent) > withResetCache hygieneInfo

中文:
定义 optBinderIdent
  签名: : Parser
  定义体: leading_parser
  -- Note: the withResetCache is because leading_parser seems to add a cache boundary,
  -- which causes the `hygieneInfo` parser not to be able to undo the trailing whitespace
(ppSpace >> Term.binderIdent) > withResetCache hygieneInfo

Depends on / 依赖: leading_parser
-/
def optBinderIdent : Parser := leading_parser
  -- Note: the withResetCache is because leading_parser seems to add a cache boundary,
  -- which causes the `hygieneInfo` parser not to be able to undo the trailing whitespace
(ppSpace >> Term.binderIdent) > withResetCache hygieneInfo

/--
Definition of `optBinderIdent.name` / `optBinderIdent.name` 的定义

English:
definition optBinderIdent.name
  signature: (id : TSyntax ``optBinderIdent)
  body: .getId if id.raw[0].isIdent then id.raw[0].getId else HygieneInfo.mkIdent ⟨id.raw[0]⟩ `this

中文:
定义 optBinderIdent.name
  签名: (id : TSyntax ``optBinderIdent)
  定义体: .getId if id.raw[0].isIdent then id.raw[0].getId else HygieneInfo.mkIdent ⟨id.raw[0]⟩ `this

Depends on / 依赖: HygieneInfo, HygieneInfo.mkIdent, id.raw, isIdent, mkIdent
-/
def optBinderIdent.name (id : TSyntax ``optBinderIdent) : Name :=
.getId if id.raw[0].isIdent then id.raw[0].getId else HygieneInfo.mkIdent ⟨id.raw[0]⟩ `this

/--
Definition of `haveIdLhs'` / `haveIdLhs'` 的定义

English:
definition haveIdLhs'
  signature: : Parser
  body: optBinderIdent >> many (ppSpace >>
    checkColGt "expected to be indented" >> letIdBinder) >> optType

@[tactic_alt Lean.Parser.Tactic.tacticHave__]

中文:
定义 haveIdLhs'
  签名: : Parser
  定义体: optBinderIdent >> many (ppSpace >>
    checkColGt "expected to be indented" >> letIdBinder) >> optType

@[tactic_alt Lean.Parser.Tactic.tacticHave__]

Depends on / 依赖: checkColGt, expected, indented, letIdBinder, optBinderIdent, optType, ppSpace
-/
def haveIdLhs' : Parser :=
  optBinderIdent >> many (ppSpace >>
    checkColGt "expected to be indented" >> letIdBinder) >> optType

@[tactic_alt Lean.Parser.Tactic.tacticHave__]
syntax "have" haveIdLhs' : tactic
@[tactic_alt Lean.Parser.Tactic.tacticLet__]
syntax "let " haveIdLhs' : tactic
@[tactic_alt Lean.Parser.Tactic.tacticSuffices_]
syntax "suffices" haveIdLhs' : tactic

open Elab Term in
/--
Definition of `haveLetCore` / `haveLetCore` 的定义

English:
definition haveLetCore
  signature: (goal : MVarId) (name : TSyntax ``optBinderIdent)
  body: let declFn := if keepTerm then MVarId.define else MVarId.assert
  goal.withContext do
    let n := optBinderIdent.name name
    let elabBinders k := if bis.isEmpty then k #[] else elabBinders bis k
    let (goal1, t, p) ← elabBinders fun es => do
      let t ← match t with
      | none => mkFreshTyp

中文:
定义 haveLetCore
  签名: (goal : MVarId) (name : TSyntax ``optBinderIdent)
  定义体: let declFn := if keepTerm then MVarId.define else MVarId.assert
  goal.withContext do
    let n := optBinderIdent.name name
    let elabBinders k := if bis.isEmpty then k #[] else elabBinders bis k
    let (goal1, t, p) ← elabBinders fun es => do
      let t ← match t with
      | none => mkFreshTyp

Depends on / 依赖: MVarId, MVarId.assert, MVarId.define, MetavarKind, MetavarKind.syntheticOpaque, Term.elabType, Term.synthesizeSyntheticMVars, assert, bis.isEmpty, declFn, define, elabBinders, elabType, goal.withContext, instantiateMVars, isEmpty, keepTerm, mkForallFVars, mkFreshExprMVar, mkFreshTypeMVar
-/
def haveLetCore (goal : MVarId) (name : TSyntax ``optBinderIdent)
    (bis : Array (TSyntax ``letIdBinder))
    (t : Option Term) (keepTerm : Bool) : TermElabM (MVarId × MVarId) :=
  let declFn := if keepTerm then MVarId.define else MVarId.assert
  goal.withContext do
    let n := optBinderIdent.name name
    let elabBinders k := if bis.isEmpty then k #[] else elabBinders bis k
    let (goal1, t, p) ← elabBinders fun es => do
      let t ← match t with
      | none => mkFreshTypeMVar
      | some stx => withRef stx do
        let e ← Term.elabType stx
        Term.synthesizeSyntheticMVars (postpone := .no)
        instantiateMVars e
      let p ← mkFreshExprMVar t MetavarKind.syntheticOpaque n
      pure (p.mvarId!, ← mkForallFVars es t, ← mkLambdaFVars es p)
    let (fvar, goal2) ← (← declFn goal n t p).intro1P
    goal2.withContext do
      Term.addTermInfo' (isBinder := true) name.raw[0] (mkFVar fvar)
    pure (goal1, goal2)

/-- An extension of the `have` tactic that turns the hypothesis into a goal to be proved later -/
elab_rules : tactic
| `(tactic| have $n:optBinderIdent $bs* $[: $t:term]?) => do
  let (goal1, goal2) ← haveLetCore (← getMainGoal) n bs t false
  replaceMainGoal [goal1, goal2]

/--
An extension of the `suffices` tactic that turns the hypothesis into a goal to be proved later
-/
elab_rules : tactic
| `(tactic| suffices $n:optBinderIdent $bs* $[: $t:term]?) => do
  let (goal1, goal2) ← haveLetCore (← getMainGoal) n bs t false
  replaceMainGoal [goal2, goal1]

/-- An extension of the `let` tactic that turns the hypothesis into a goal to be proved later -/
elab_rules : tactic
| `(tactic| let $n:optBinderIdent $bs* $[: $t:term]?) => withMainContext do
  let (goal1, goal2) ← haveLetCore (← getMainGoal) n bs t true
  replaceMainGoal [goal1, goal2]

end Mathlib.Tactic
