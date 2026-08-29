/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Init
public meta import Lean.Elab.Command
public meta import Lean.Server.InfoUtils

/-!
# The `have` vs `let` linter

The `have` vs `let` linter flags uses of `have` to introduce a hypothesis whose Type is not `Prop`.

The option for this linter is a natural number, but really there are only 3 settings:
* `0` -- inactive;
* `1` -- active only on noisy declarations;
* `2` or more -- always active.

TODO:
* Also lint `let` vs `have`.
* `haveI` may need to change to `let/letI`?
* `replace`, `classical!`, `classical`, `tauto` internally use `have`:
  should the linter act on them as well?
-/

meta section

open Lean Elab Command Meta

namespace Mathlib.Linter

/-- The `have` vs `let` linter emits a warning on `have`s introducing a hypothesis whose
Type is not `Prop`.
There are three settings:
* `0` -- inactive;
* `1` -- active only on noisy declarations;
* `2` or more -- always active.

The default value is `1`.
-/
public register_option linter.haveLet : Nat := {
  defValue := 0
  descr := "enable the `have` vs `let` linter:\n\
            * 0 -- inactive;\n\
            * 1 -- active only on noisy declarations;\n\
            * 2 or more -- always active."
}

namespace haveLet

/--
Definition of `isHave?` / `isHave?` 的定义

English:
definition isHave?
  signature: : Syntax -> Bool

中文:
定义 isHave?
  签名: : Syntax -> 布尔
-/
def isHave? : Syntax -> Bool
  | .node _ ``Lean.Parser.Tactic.tacticHave__ _ => true
  | _ => false

end haveLet

end Mathlib.Linter

namespace Mathlib.Linter.haveLet

/--
Definition of `InfoTree.foldInfoM` / `InfoTree.foldInfoM` 的定义

English:
definition InfoTree.foldInfoM
  signature: {α m} [Monad m] (f : ContextInfo -> Info -> α -> m α) (init : α)
  body: InfoTree.foldInfo (fun ctx i ma => do f ctx i (← ma)) (pure init)

中文:
定义 InfoTree.foldInfoM
  签名: {α m} [Monad m] (f : ContextInfo -> Info -> α -> m α) (init : α)
  定义体: InfoTree.foldInfo (fun ctx i ma => do f ctx i (← ma)) (pure init)

Depends on / 依赖: InfoTree, InfoTree.foldInfo, foldInfo
-/
def InfoTree.foldInfoM {α m} [Monad m] (f : ContextInfo -> Info -> α -> m α) (init : α) :
    InfoTree -> m α :=
  InfoTree.foldInfo (fun ctx i ma => do f ctx i (← ma)) (pure init)

/--
Definition of `toFormat_propTypes` / `toFormat_propTypes` 的定义

English:
definition toFormat_propTypes
  signature: (ctx : ContextInfo) (lc : LocalContext) (es : Array (Expr × Name))
  body: do
  ctx.runMetaM lc do
    es.filterMapM fun (e, name) => do
      let typ ← inferType (← instantiateMVars e)
      if typ.isProp then return none else return (← ppExpr e, name)

中文:
定义 toFormat_propTypes
  签名: (ctx : ContextInfo) (lc : LocalContext) (es : Array (Expr × Name))
  定义体: do
  ctx.runMetaM lc do
    es.filterMapM fun (e, name) => do
      let typ ← inferType (← instantiateMVars e)
      if typ.isProp then return none else return (← ppExpr e, name)
-/
def toFormat_propTypes (ctx : ContextInfo) (lc : LocalContext) (es : Array (Expr × Name)) :
    CommandElabM (Array (Format × Name)) := do
  ctx.runMetaM lc do
    es.filterMapM fun (e, name) => do
      let typ ← inferType (← instantiateMVars e)
      if typ.isProp then return none else return (← ppExpr e, name)

/-- returns the `have` syntax whose corresponding hypothesis does not have Type `Prop` and
also a `Format`ted version of the corresponding Type. -/
public partial
/--
Definition of `nonPropHaves` / `nonPropHaves` 的定义

English:
definition nonPropHaves
  signature: : InfoTree -> CommandElabM (Array (Syntax × Format))
  body: InfoTree.foldInfoM (init := #[]) fun ctx info args => return args ++ (← (do
    let .ofTacticInfo i := info | return #[]
    let stx := i.stx
    let .original .. := stx.getHeadInfo | return #[]
    unless isHave? stx do return #[]
    let mctx := i.mctxAfter
    let mvdecls := i.goalsAfter.filterMa

中文:
定义 nonPropHaves
  签名: : InfoTree -> CommandElabM (Array (Syntax × Format))
  定义体: InfoTree.foldInfoM (init := #[]) fun ctx info args => return args ++ (← (do
    let .ofTacticInfo i := info | return #[]
    let stx := i.stx
    let .original .. := stx.getHeadInfo | return #[]
    unless isHave? stx do return #[]
    let mctx := i.mctxAfter
    let mvdecls := i.goalsAfter.filterMa

Depends on / 依赖: InfoTree, InfoTree.foldInfoM, filterMap, foldInfoM, getHeadInfo, goalsAfter, i.goalsAfter.filterMap, i.mctxAfter, i.stx, isHave, mctx.decls.find, mctxAfter, mvdecls, ofTacticInfo, original, return, stx.getHeadInfo, unless
-/
def nonPropHaves : InfoTree -> CommandElabM (Array (Syntax × Format)) :=
  InfoTree.foldInfoM (init := #[]) fun ctx info args => return args ++ (← (do
    let .ofTacticInfo i := info | return #[]
    let stx := i.stx
    let .original .. := stx.getHeadInfo | return #[]
    unless isHave? stx do return #[]
    let mctx := i.mctxAfter
    let mvdecls := i.goalsAfter.filterMap (mctx.decls.find? ·)
    -- We extract the `MetavarDecl` with largest index after a `have`, since this one
    -- holds information about the metavariable where `have` introduces the new hypothesis,
    -- and determine the relevant `LocalContext`.
.lctx .getD default let lc := mvdecls.toArray.getMax? (·.index < ·.index)
    -- we also accumulate all `fvarId`s from all local contexts before the use of `have`
    -- so that we can then isolate the `fvarId`s that are created by `have`
    let oldMvdecls := i.goalsBefore.filterMap (mctx.decls.find? ·)
    let oldFVars := (oldMvdecls.map (·.lctx.decls.toList.reduceOption)).flatten.map (·.fvarId)
    -- `newDecls` are the local declarations whose `FVarID` did not exist before the `have`.
    -- Effectively they are the declarations that we want to test for being in `Prop` or not.
    let newDecls := lc.decls.toList.reduceOption.filter (! oldFVars.contains ·.fvarId)
    -- Now, we get the `MetaM` state up and running to find the types of each entry of `newDecls`.
    -- For each entry which is a `Type`, we print a warning on `have`.
    let fmts ← toFormat_propTypes ctx lc (newDecls.map (fun e => (e.type, e.userName))).toArray
    return fmts.map fun (fmt, na) => (stx, f!"{na} : {fmt}")))

/--
Definition of `haveLetLinter` / `haveLetLinter` 的定义

English:
definition haveLetLinter
  signature: : Linter where run
  body: withSetOptionIn fun _stx => do
  let gh := linter.haveLet.get (← getOptions)
  unless gh != 0 && (← getInfoState).enabled do
    return
  unless gh == 1 && (← MonadState.get).messages.unreported.isEmpty do
    let trees ← getInfoTrees
    for t in trees do
      for (s, fmt) in ← nonPropHaves t do
 

中文:
定义 haveLetLinter
  签名: : Linter where run
  定义体: withSetOptionIn fun _stx => do
  let gh := linter.haveLet.get (← getOptions)
  unless gh != 0 && (← getInfoState).enabled do
    return
  unless gh == 1 && (← MonadState.get).messages.unreported.isEmpty do
    let trees ← getInfoTrees
    for t in trees do
      for (s, fmt) in ← nonPropHaves t do
 

Depends on / 依赖: _stx, withSetOptionIn
-/
def haveLetLinter : Linter where run := withSetOptionIn fun _stx => do
  let gh := linter.haveLet.get (← getOptions)
  unless gh != 0 && (← getInfoState).enabled do
    return
  unless gh == 1 && (← MonadState.get).messages.unreported.isEmpty do
    let trees ← getInfoTrees
    for t in trees do
      for (s, fmt) in ← nonPropHaves t do
        logLint0Disable linter.haveLet s
          m!"'{fmt}' is a Type and not a Prop. Consider using 'let' instead of 'have'."

initialize addLinter haveLetLinter

end haveLet

end Mathlib.Linter
