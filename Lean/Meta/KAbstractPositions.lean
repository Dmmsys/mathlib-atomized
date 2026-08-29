/-
Copyright (c) 2023 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Init
public import Lean.HeadIndex
public import Lean.Meta.ExprLens
public import Lean.Meta.Check

/-!

# Find the positions of a pattern in an expression

This file defines some tools for dealing with subexpressions and occurrence numbers.
This is used for creating a `rw` tactic call that rewrites a selected expression.

`viewKAbstractSubExpr` takes an expression and a position in the expression, and returns
the subexpression together with an optional occurrence number that would be required to find
the subexpression using `kabstract` (which is what `rw` uses to find the position of the rewrite)

`rw` can fail if the motive is not type correct. `kabstractIsTypeCorrect` checks
whether this is the case.

-/

@[expose] public section

namespace Lean.Meta

/--
Definition of `kabstractPositions` / `kabstractPositions` 的定义

English:
definition kabstractPositions
  signature: (p e : Expr)
  body: do
  let mctx ← getMCtx
  let pHeadIdx := p.toHeadIndex
  let pNumArgs := p.headNumArgs
  let rec
  /-- The main loop that loops through all subexpressions -/
  visit (e : Expr) (pos : SubExpr.Pos) (positions : Array SubExpr.Pos) :
      MetaM (Array SubExpr.Pos) := do
    let visitChildren : Array SubExpr.Pos -> MetaM (Array SubExpr.Pos) :=
      match e with
      | .app fn arg => visit fn pos.pushAppFn
                                    >=> visit arg pos.pushAppArg
      | .mdata _ expr => visit expr pos
      | .proj _ _ struct => visit struct pos.pushProj
      | .letE _ type value body _ => visit type pos.pushLetVarType
                                    >=> visit value pos.pushLetValue
                                    >=> visit body pos.pushLetBody
      | .lam _ binderType body _ => visit binderType pos.pushBindingDomain
                                    >=> visit body pos.pushBindingBody
      | .forallE _ binderType body _ => visit binderType pos.pushBindingDomain
                                    >=> visit body pos.pushBindingBody
      | _ => pure
    if e.hasLooseBVars then
      visitChildren positions
    else if e.toHeadIndex != pHeadIdx || e.headNumArgs != pNumArgs then
      visitChildren positions
    else
      if ← isDefEq e p then
        setMCtx mctx -- reset the `MetavarContext` because `isDefEq` can modify it if it succeeds
        visitChildren (positions.push pos)
      else
        visitChildren positions
  visit e .root #[]

中文:
定义 kabstractPositions
  签名: (p e : Expr)
  定义体: do
  let mctx ← getMCtx
  let pHeadIdx := p.toHeadIndex
  let pNumArgs := p.headNumArgs
  let rec
  /-- The main loop that loops through all subexpressions -/
  visit (e : Expr) (pos : SubExpr.Pos) (positions : Array SubExpr.Pos) :
      MetaM (Array SubExpr.Pos) := do
    let visitChildren : Array SubExpr.Pos -> MetaM (Array SubExpr.Pos) :=
      match e with
      | .app fn arg => visit fn pos.pushAppFn
                                    >=> visit arg pos.pushAppArg
      | .mdata _ expr => visit expr pos
      | .proj _ _ struct => visit struct pos.pushProj
      | .letE _ type value body _ => visit type pos.pushLetVarType
                                    >=> visit value pos.pushLetValue
                                    >=> visit body pos.pushLetBody
      | .lam _ binderType body _ => visit binderType pos.pushBindingDomain
                                    >=> visit body pos.pushBindingBody
      | .forallE _ binderType body _ => visit binderType pos.pushBindingDomain
                                    >=> visit body pos.pushBindingBody
      | _ => pure
    if e.hasLooseBVars then
      visitChildren positions
    else if e.toHeadIndex != pHeadIdx || e.headNumArgs != pNumArgs then
      visitChildren positions
    else
      if ← isDefEq e p then
        setMCtx mctx -- reset the `MetavarContext` because `isDefEq` can modify it if it succeeds
        visitChildren (positions.push pos)
      else
        visitChildren positions
  visit e .root #[]
-/
def kabstractPositions (p e : Expr) : MetaM (Array SubExpr.Pos) := do
  let mctx ← getMCtx
  let pHeadIdx := p.toHeadIndex
  let pNumArgs := p.headNumArgs
  let rec
  /-- The main loop that loops through all subexpressions -/
  visit (e : Expr) (pos : SubExpr.Pos) (positions : Array SubExpr.Pos) :
      MetaM (Array SubExpr.Pos) := do
    let visitChildren : Array SubExpr.Pos -> MetaM (Array SubExpr.Pos) :=
      match e with
      | .app fn arg => visit fn pos.pushAppFn
                                    >=> visit arg pos.pushAppArg
      | .mdata _ expr => visit expr pos
      | .proj _ _ struct => visit struct pos.pushProj
      | .letE _ type value body _ => visit type pos.pushLetVarType
                                    >=> visit value pos.pushLetValue
                                    >=> visit body pos.pushLetBody
      | .lam _ binderType body _ => visit binderType pos.pushBindingDomain
                                    >=> visit body pos.pushBindingBody
      | .forallE _ binderType body _ => visit binderType pos.pushBindingDomain
                                    >=> visit body pos.pushBindingBody
      | _ => pure
    if e.hasLooseBVars then
      visitChildren positions
    else if e.toHeadIndex != pHeadIdx || e.headNumArgs != pNumArgs then
      visitChildren positions
    else
      if ← isDefEq e p then
        setMCtx mctx -- reset the `MetavarContext` because `isDefEq` can modify it if it succeeds
        visitChildren (positions.push pos)
      else
        visitChildren positions
  visit e .root #[]

/--
Definition of `viewKAbstractSubExpr` / `viewKAbstractSubExpr` 的定义

English:
definition viewKAbstractSubExpr
  signature: (e : Expr) (pos : SubExpr.Pos)
  body: do
  let subExpr ← Core.viewSubexpr pos e
  if subExpr.hasLooseBVars then
    return none
  let positions ← kabstractPositions subExpr e
  let some n := positions.idxOf? pos | unreachable!
  return some (subExpr, if positions.size == 1 then none else some (n + 1))

中文:
定义 viewKAbstractSubExpr
  签名: (e : Expr) (pos : SubExpr.Pos)
  定义体: do
  let subExpr ← Core.viewSubexpr pos e
  if subExpr.hasLooseBVars then
    return none
  let positions ← kabstractPositions subExpr e
  let some n := positions.idxOf? pos | unreachable!
  return some (subExpr, if positions.size == 1 then none else some (n + 1))
-/
def viewKAbstractSubExpr (e : Expr) (pos : SubExpr.Pos) : MetaM (Option (Expr × Option Nat)) := do
  let subExpr ← Core.viewSubexpr pos e
  if subExpr.hasLooseBVars then
    return none
  let positions ← kabstractPositions subExpr e
  let some n := positions.idxOf? pos | unreachable!
  return some (subExpr, if positions.size == 1 then none else some (n + 1))

/--
Definition of `kabstractIsTypeCorrect` / `kabstractIsTypeCorrect` 的定义

English:
definition kabstractIsTypeCorrect
  signature: (e subExpr : Expr) (pos : SubExpr.Pos)
  body: do
  withLocalDeclD `_a (← inferType subExpr) fun fvar => do
    isTypeCorrect (← replaceSubexpr (fun _ => pure fvar) pos e)

中文:
定义 kabstractIsTypeCorrect
  签名: (e subExpr : Expr) (pos : SubExpr.Pos)
  定义体: do
  withLocalDeclD `_a (← inferType subExpr) fun fvar => do
    isTypeCorrect (← replaceSubexpr (fun _ => pure fvar) pos e)
-/
def kabstractIsTypeCorrect (e subExpr : Expr) (pos : SubExpr.Pos) : MetaM Bool := do
  withLocalDeclD `_a (← inferType subExpr) fun fvar => do
    isTypeCorrect (← replaceSubexpr (fun _ => pure fvar) pos e)

end Lean.Meta
