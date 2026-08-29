/-
Copyright (c) 2018 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, David Renshaw
-/
module

public meta import Lean.Elab.Tactic.Location
public meta import Lean.Meta.Tactic.SplitIf
public meta import Lean.Elab.Tactic.Simp
public import Mathlib.Tactic.Core

/-!
Tactic to split if-then-else expressions.
-/

public meta section

namespace Mathlib.Tactic

open Lean Elab.Tactic Parser.Tactic Lean.Meta

/--
Inductive type `SplitPosition` / 归纳类型 `SplitPosition`

English:
inductive SplitPosition
  constructors (2):
    - target: 
    - hyp: (fvarId: FVarId)

中文:
归纳类型 SplitPosition
  构造子 (2 个):
    - target: 
    - hyp: (fvarId: FVarId)
-/
private inductive SplitPosition
| target
| hyp (fvarId: FVarId)

/--
Definition of `getSplitCandidates` / `getSplitCandidates` 的定义

English:
definition getSplitCandidates
  signature: (loc : Location)
  body: match loc with
| Location.wildcard => do
  let candidates ← (← getLCtx).getFVarIds.mapM
    (fun fvarId => do
      let typ ← instantiateMVars (← inferType (mkFVar fvarId))
      return (SplitPosition.hyp fvarId, typ))
  pure ((SplitPosition.target, ← getMainTarget) :: candidates.toList)
| Location.targets hyps tgt => do
  let candidates ← (← hyps.mapM getFVarId).mapM
    (fun fvarId => do
      let typ ← instantiateMVars (← inferType (mkFVar fvarId))
      return (SplitPosition.hyp fvarId, typ))
  if tgt
  then return (SplitPosition.target, ← getMainTarget) :: candidates.toList
  else return candidates.toList

中文:
定义 getSplitCandidates
  签名: (loc : Location)
  定义体: match loc with
| Location.wildcard => do
  let candidates ← (← getLCtx).getFVarIds.mapM
    (fun fvarId => do
      let typ ← instantiateMVars (← inferType (mkFVar fvarId))
      return (SplitPosition.hyp fvarId, typ))
  pure ((SplitPosition.target, ← getMainTarget) :: candidates.toList)
| Location.targets hyps tgt => do
  let candidates ← (← hyps.mapM getFVarId).mapM
    (fun fvarId => do
      let typ ← instantiateMVars (← inferType (mkFVar fvarId))
      return (SplitPosition.hyp fvarId, typ))
  if tgt
  then return (SplitPosition.target, ← getMainTarget) :: candidates.toList
  else return candidates.toList
-/
private def getSplitCandidates (loc : Location) : TacticM (List (SplitPosition × Expr)) :=
match loc with
| Location.wildcard => do
  let candidates ← (← getLCtx).getFVarIds.mapM
    (fun fvarId => do
      let typ ← instantiateMVars (← inferType (mkFVar fvarId))
      return (SplitPosition.hyp fvarId, typ))
  pure ((SplitPosition.target, ← getMainTarget) :: candidates.toList)
| Location.targets hyps tgt => do
  let candidates ← (← hyps.mapM getFVarId).mapM
    (fun fvarId => do
      let typ ← instantiateMVars (← inferType (mkFVar fvarId))
      return (SplitPosition.hyp fvarId, typ))
  if tgt
  then return (SplitPosition.target, ← getMainTarget) :: candidates.toList
  else return candidates.toList

/--
Definition of `findIfToSplit?` / `findIfToSplit?` 的定义

English:
definition findIfToSplit?
  signature: (e : Expr)
  body: match e.find? fun e => (e.isIte || e.isDIte) && !(e.getArg! 1 5).hasLooseBVars with
  | some iteApp =>
    let cond := iteApp.getArg! 1 5
    let dec := iteApp.getArg! 2 5
    -- Try to find a nested `if` in `cond`
.getD (cond, dec) findIfToSplit? cond
  | none => none

中文:
定义 findIfToSplit?
  签名: (e : Expr)
  定义体: match e.find? fun e => (e.isIte || e.isDIte) && !(e.getArg! 1 5).hasLooseBVars with
  | some iteApp =>
    let cond := iteApp.getArg! 1 5
    let dec := iteApp.getArg! 2 5
    -- Try to find a nested `if` in `cond`
.getD (cond, dec) findIfToSplit? cond
  | none => none
-/
private partial def findIfToSplit? (e : Expr) : Option (Expr × Expr) :=
  match e.find? fun e => (e.isIte || e.isDIte) && !(e.getArg! 1 5).hasLooseBVars with
  | some iteApp =>
    let cond := iteApp.getArg! 1 5
    let dec := iteApp.getArg! 2 5
    -- Try to find a nested `if` in `cond`
.getD (cond, dec) findIfToSplit? cond
  | none => none

/--
Definition of `findIfCondAt` / `findIfCondAt` 的定义

English:
definition findIfCondAt
  signature: (loc : Location)
  body: do
  for (pos, e) in (← getSplitCandidates loc) do
    if let some (cond, _) := findIfToSplit? e
    then return some (pos, cond)
  return none

中文:
定义 findIfCondAt
  签名: (loc : Location)
  定义体: do
  for (pos, e) in (← getSplitCandidates loc) do
    if let some (cond, _) := findIfToSplit? e
    then return some (pos, cond)
  return none
-/
private def findIfCondAt (loc : Location) : TacticM (Option (SplitPosition × Expr)) := do
  for (pos, e) in (← getSplitCandidates loc) do
    if let some (cond, _) := findIfToSplit? e
    then return some (pos, cond)
  return none

/--
Definition of `discharge?` / `discharge?` 的定义

English:
definition discharge?
  signature: (e : Expr)
  body: do
  let e ← instantiateMVars e
  if let some e1 ← (← SplitIf.mkDischarge? false) e
    then return some e1
  if e.isConstOf `True
    then return some (mkConst `True.intro)
  return none

中文:
定义 discharge?
  签名: (e : Expr)
  定义体: do
  let e ← instantiateMVars e
  if let some e1 ← (← SplitIf.mkDischarge? false) e
    then return some e1
  if e.isConstOf `True
    then return some (mkConst `True.intro)
  return none
-/
private def discharge? (e : Expr) : SimpM (Option Expr) := do
  let e ← instantiateMVars e
  if let some e1 ← (← SplitIf.mkDischarge? false) e
    then return some e1
  if e.isConstOf `True
    then return some (mkConst `True.intro)
  return none

/--
Definition of `reduceIfsAt` / `reduceIfsAt` 的定义

English:
definition reduceIfsAt
  signature: (loc : Location)
  body: do
  let ctx ← SplitIf.getSimpContext
  let ctx := ctx.setFailIfUnchanged false
  let _ ← simpLocation ctx (← ({} : Simp.SimprocsArray).add `reduceCtorEq false) discharge? loc
  pure ()

中文:
定义 reduceIfsAt
  签名: (loc : Location)
  定义体: do
  let ctx ← SplitIf.getSimpContext
  let ctx := ctx.setFailIfUnchanged false
  let _ ← simpLocation ctx (← ({} : Simp.SimprocsArray).add `reduceCtorEq false) discharge? loc
  pure ()
-/
private def reduceIfsAt (loc : Location) : TacticM Unit := do
  let ctx ← SplitIf.getSimpContext
  let ctx := ctx.setFailIfUnchanged false
  let _ ← simpLocation ctx (← ({} : Simp.SimprocsArray).add `reduceCtorEq false) discharge? loc
  pure ()

/--
Definition of `splitIf1` / `splitIf1` 的定义

English:
definition splitIf1
  signature: (cond : Expr) (hName : Name) (loc : Location)
  body: do
  let splitCases :=
    evalTactic (← `(tactic| by_cases $(mkIdent hName) : $(← Elab.Term.exprToSyntax cond)))
  andThenOnSubgoals splitCases (reduceIfsAt loc)

中文:
定义 splitIf1
  签名: (cond : Expr) (hName : Name) (loc : Location)
  定义体: do
  let splitCases :=
    evalTactic (← `(tactic| by_cases $(mkIdent hName) : $(← Elab.Term.exprToSyntax cond)))
  andThenOnSubgoals splitCases (reduceIfsAt loc)
-/
private def splitIf1 (cond : Expr) (hName : Name) (loc : Location) : TacticM Unit := do
  let splitCases :=
    evalTactic (← `(tactic| by_cases $(mkIdent hName) : $(← Elab.Term.exprToSyntax cond)))
  andThenOnSubgoals splitCases (reduceIfsAt loc)

/--
Definition of `getNextName` / `getNextName` 的定义

English:
definition getNextName
  signature: (hNames: IO.Ref (List (TSyntax `Lean.binderIdent)))
  body: do
  match ← hNames.get with
  | [] => mkFreshUserName `h
  | n::ns => do hNames.set ns
                if let `(binderIdent| $x:ident) := n
                then pure x.getId
                else pure `_

中文:
定义 getNextName
  签名: (hNames: IO.Ref (列表 (TSyntax `Lean.binderIdent)))
  定义体: do
  match ← hNames.get with
  | [] => mkFreshUserName `h
  | n::ns => do hNames.set ns
                if let `(binderIdent| $x:ident) := n
                then pure x.getId
                else pure `_
-/
private def getNextName (hNames: IO.Ref (List (TSyntax `Lean.binderIdent))) : MetaM Name := do
  match ← hNames.get with
  | [] => mkFreshUserName `h
  | n::ns => do hNames.set ns
                if let `(binderIdent| $x:ident) := n
                then pure x.getId
                else pure `_

/--
Definition of `valueKnown` / `valueKnown` 的定义

English:
definition valueKnown
  signature: (cond : Expr)
  body: do
  let not_cond := mkApp (mkConst `Not) cond
  for h in ← getLocalHyps do
    let ty ← instantiateMVars (← inferType h)
    if cond == ty then return true
    if not_cond == ty then return true
  return false

中文:
定义 valueKnown
  签名: (cond : Expr)
  定义体: do
  let not_cond := mkApp (mkConst `Not) cond
  for h in ← getLocalHyps do
    let ty ← instantiateMVars (← inferType h)
    if cond == ty then return true
    if not_cond == ty then return true
  return false
-/
private def valueKnown (cond : Expr) : TacticM Bool := do
  let not_cond := mkApp (mkConst `Not) cond
  for h in ← getLocalHyps do
    let ty ← instantiateMVars (← inferType h)
    if cond == ty then return true
    if not_cond == ty then return true
  return false

/--
Definition of `splitIfsCore` / `splitIfsCore` 的定义

English:
definition splitIfsCore
  body: fun done => withMainContext do
  let some (_,cond) ← findIfCondAt loc
      | Meta.throwTacticEx `split_ifs (← getMainGoal) "no if-then-else conditions to split"

  -- If `cond` is `¬p` then use `p` instead.
  let cond := if cond.isAppOf `Not then cond.getAppArgs[0]! else cond

  if done.contains cond then return ()
  let no_split ← valueKnown cond
  if no_split then
    andThenOnSubgoals (reduceIfsAt loc) (splitIfsCore loc hNames (cond::done) <|> pure ())
  else do
    let hName ← getNextName hNames
    andThenOnSubgoals (splitIf1 cond hName loc) ((splitIfsCore loc hNames (cond::done)) <|>
      pure ())

中文:
定义 splitIfsCore
  定义体: fun done => withMainContext do
  let some (_,cond) ← findIfCondAt loc
      | Meta.throwTacticEx `split_ifs (← getMainGoal) "no if-then-else conditions to split"

  -- If `cond` is `¬p` then use `p` instead.
  let cond := if cond.isAppOf `Not then cond.getAppArgs[0]! else cond

  if done.contains cond then return ()
  let no_split ← valueKnown cond
  if no_split then
    andThenOnSubgoals (reduceIfsAt loc) (splitIfsCore loc hNames (cond::done) <|> pure ())
  else do
    let hName ← getNextName hNames
    andThenOnSubgoals (splitIf1 cond hName loc) ((splitIfsCore loc hNames (cond::done)) <|>
      pure ())
-/
private partial def splitIfsCore
    (loc : Location)
    (hNames : IO.Ref (List (TSyntax `Lean.binderIdent))) :
    List Expr -> TacticM Unit := fun done => withMainContext do
  let some (_,cond) ← findIfCondAt loc
      | Meta.throwTacticEx `split_ifs (← getMainGoal) "no if-then-else conditions to split"

  -- If `cond` is `¬p` then use `p` instead.
  let cond := if cond.isAppOf `Not then cond.getAppArgs[0]! else cond

  if done.contains cond then return ()
  let no_split ← valueKnown cond
  if no_split then
    andThenOnSubgoals (reduceIfsAt loc) (splitIfsCore loc hNames (cond::done) <|> pure ())
  else do
    let hName ← getNextName hNames
    andThenOnSubgoals (splitIf1 cond hName loc) ((splitIfsCore loc hNames (cond::done)) <|>
      pure ())

/-- `split_ifs` splits the main goal in two goals for every if-then-else expression it contains,
by applying excluded middle to the condition. If the goal has the form `g (if p then x else y)`,
`split_ifs` will result in two goals `h✝ : p ⊢ g x` and `h✝ : ¬p ⊢ g y`. If there are multiple
if-then-else expressions, then `split_ifs` will split them all, starting with a top-most one whose
condition does not contain another if-then-else expression.

* `split_ifs with h₁ h₂ h₃` names the introduced hypotheses.
  Note that names are not reused across splits: on a goal of the form
  `⊢ (if p then 1 else 2) + (if q then 3 else 4)`, use `split_ifs with hp hq hq` to name all
  the hypotheses.
* `split_ifs at l` splits the if-then-else expressions at location(s) `l`.
-/
syntax (name := splitIfs) "split_ifs" (location)? (" with" (ppSpace colGt binderIdent)+)? : tactic

elab_rules : tactic
| `(tactic| split_ifs $[$loc:location]? $[with $withArg*]?) =>
  let loc := match loc with
  | none => Location.targets #[] true
  | some loc => expandLocation loc
  let names := match withArg with
  | none => []
  | some args => args.toList
  withMainContext do
    let names ← IO.mkRef names
    splitIfsCore loc names []
    for name in ← names.get do
      logWarningAt name m!"unused name: {name}"

end Mathlib.Tactic
