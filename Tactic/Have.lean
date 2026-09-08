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

/-- A parser for optional binder identifiers -/
/-
**Mathlib.Tactic.optBinderIdent** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic`。
形式化陈述：optBinderIdent : Parser
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A parser for optional binder identifiers
-/
def optBinderIdent : Parser := leading_parser
  -- Note: the withResetCache is because leading_parser seems to add a cache boundary,
  -- which causes the `hygieneInfo` parser not to be able to undo the trailing whitespace
  (ppSpace >> Term.binderIdent) <|> withResetCache hygieneInfo

/-- Retrieves the name of the optional identifier, if provided. Returns `this` otherwise -/
/-
**Mathlib.Tactic.optBinderIdent.name** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.o
ptBinderIdent`。
形式化陈述：TSyntax `Mathlib.Tactic.optBinderIdent → Name
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Retrieves the name of the optional identifier, if provided. Returns `this` other
wise
-/
def optBinderIdent.name (id : TSyntax ``optBinderIdent) : Name :=
  if id.raw[0].isIdent then id.raw[0].getId else HygieneInfo.mkIdent ⟨id.raw[0]⟩ `this |>.getId

/--
Uses `checkColGt` to prevent

```lean
have h
exact Nat
```

From being interpreted as
```lean
have h
  exact Nat
```
-/
/-
**Mathlib.Tactic.haveIdLhs'** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic`。
形式化陈述：haveIdLhs' : Parser
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Uses `checkColGt` to prevent

```lean
have h
exact Nat
```

From being interpreted as
```lean
have h
  exact Nat
```
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
Adds hypotheses to the context, turning them into goals to be proved later if their proof terms
aren't provided (`t: Option Term := none`).

If the bound term is intended to be kept in the context, pass `keepTerm : Bool := true`. This is
useful when extending the `let` tactic, which is expected to show the proof term in the infoview.
-/
/-
**Mathlib.Tactic.haveLetCore** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic`。
形式化陈述：haveLetCore (goal : MVarId) (name : TSyntax ``optBinderIdent) (bis : Array
 (TSyntax ``letIdBinder)) (t : Option Term) (keepTerm : Bool) : TermElabM (MVarI
d × MVarId)
参数：goal : MVarId；name : TSyntax ``optBinderIdent；bis : Array (TSyntax ``letIdBin
der)；t : Option Term；keepTerm : Bool。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Adds hypotheses to the context, turning them into goals to be proved later if th
eir proof terms
aren't provided (`t: Option Term := none`).

If the bound term is intended to be kept in the context, pass `keepTerm : Bool :
= true`. This is
useful when extending the `let` tactic, which is expected to show the proof term
 in the infoview.
-/
def haveLetCore (goal : MVarId) (name : TSyntax ``optBinderIdent)
    (bis : Array (TSyntax ``letIdBinder))
    (t : Option Term) (keepTerm : Bool) : TermElabM (MVarId × MVarId) :=
  let declFn := if keepTerm then MVarId.define else MVarId.assert
  goal.withContext do
    let n := optBinderIdent.name name
    let elabBinders k := if bis.isEmpty then k #[] else elabBinders bis k
    let (goal1, t, p) ← elabBinders fun es ↦ do
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

