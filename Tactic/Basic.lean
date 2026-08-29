/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kyle Miller
-/
module -- shake: keep-all, shake: keep-downstream

public meta import Lean.Elab.BuiltinCommand
public import Mathlib.Tactic.PPWithUniv
public import Mathlib.Tactic.ExtendDoc
public import Mathlib.Tactic.Linter.OldObtain
public import Batteries.Util.LibraryNote -- For `library_note` command.

/-!
# Basic tactics and utilities for tactic writing

This file defines some basic utilities for tactic writing, and also
- a dummy `variables` macro (which warns that the Lean 4 name is `variable`)
- the `introv` tactic, which allows the user to automatically introduce the variables of a theorem
  and explicitly name the non-dependent hypotheses,
- an `assumption` macro, calling the `assumption` tactic on all goals
- the tactics `match_target` and `clear_aux_decl` (clearing all auxiliary declarations from the
  context).
-/

public meta section

namespace Mathlib.Tactic
open Lean Parser.Tactic Elab Command Elab.Tactic Meta

/-- Syntax for the `variables` command: this command is just a stub,
and merely warns that it has been renamed to `variable` in Lean 4. -/
syntax (name := «variables») "variables" (ppSpace bracketedBinder)* : command

/--
Definition of `elabVariables` / `elabVariables` 的定义

English:
definition elabVariables
  signature: : CommandElab

中文:
定义 elabVariables
  签名: : CommandElab
-/
@[command_elab «variables»] def elabVariables : CommandElab
  | `(variables%$pos $binders*) => do
    logWarningAt pos "'variables' has been replaced by 'variable' in lean 4"
    elabVariable (← `(variable%$pos $binders*))
  | _ => throwUnsupportedSyntax

/--
Definition of `pushFVarAliasInfo` / `pushFVarAliasInfo` 的定义

English:
definition pushFVarAliasInfo
  signature: {m : Type -> Type} [Monad m] [MonadInfoTree m]
  body: do
  for old in oldFVars, new in newFVars do
    if old != new then
      let decl := newLCtx.get! new
      pushInfoLeaf (.ofFVarAliasInfo { id := new, baseId := old, userName := decl.userName })

中文:
定义 pushFVarAliasInfo
  签名: {m : 类型 -> 类型} [单子 m] [MonadInfoTree m]
  定义体: do
  for old in oldFVars, new in newFVars do
    if old != new then
      let decl := newLCtx.get! new
      pushInfoLeaf (.ofFVarAliasInfo { id := new, baseId := old, userName := decl.userName })
-/
def pushFVarAliasInfo {m : Type -> Type} [Monad m] [MonadInfoTree m]
    (oldFVars newFVars : Array FVarId) (newLCtx : LocalContext) : m Unit := do
  for old in oldFVars, new in newFVars do
    if old != new then
      let decl := newLCtx.get! new
      pushInfoLeaf (.ofFVarAliasInfo { id := new, baseId := old, userName := decl.userName })

/--
`introv` introduces the parameters to a dependent function according to their parameter name. If the
first parameter is not depended on by the rest of the function type, `introv` with no (remaining)
arguments does nothing.

* `introv h₁ h₂ ...` introduces non-depended-on parameters in between sequences of depended-on
  parameters, using the names `h₁`, `h₂`, ... in turn. Use `_` to anonymize a specific hypothesis.

Examples:
```
example : ∀ a b : Nat, a = b → b = a := by
  introv h
  /-
  The goal state is:
  a b : ℕ,
  h : a = b
  ⊢ b = a
  -/
  exact h.symm
```

```
example : forall a b : Nat, a = b -> forall c, b = c -> a = c := by
  introv h₁ h₂
  /-
  The goal state is:
  a b : ℕ,
  h₁ : a = b,
  c : ℕ,
  h₂ : b = c
  ⊢ a = c
  -/
  exact h₁.trans h₂
```
-/
syntax (name := introv) "introv" (ppSpace colGt binderIdent)* : tactic
/--
Definition of `evalIntrov` / `evalIntrov` 的定义

English:
definition evalIntrov
  signature: : Tactic
  body: fun stx => do
  match stx with
  | `(tactic| introv) => introsDep
  | `(tactic| introv $h:ident $hs:binderIdent*) =>
    evalTactic (← `(tactic| introv; intro $h:ident; introv $hs:binderIdent*))
  | `(tactic| introv _%$tk $hs:binderIdent*) =>
    evalTactic (← `(tactic| introv; intro _%$tk; introv $hs:binderIdent*))
  | _ => throwUnsupportedSyntax

中文:
定义 eval整数rov
  签名: : Tactic
  定义体: fun stx => do
  match stx with
  | `(tactic| introv) => introsDep
  | `(tactic| introv $h:ident $hs:binderIdent*) =>
    evalTactic (← `(tactic| introv; intro $h:ident; introv $hs:binderIdent*))
  | `(tactic| introv _%$tk $hs:binderIdent*) =>
    evalTactic (← `(tactic| introv; intro _%$tk; introv $hs:binderIdent*))
  | _ => throwUnsupportedSyntax
-/
@[tactic introv] partial def evalIntrov : Tactic := fun stx => do
  match stx with
  | `(tactic| introv) => introsDep
  | `(tactic| introv $h:ident $hs:binderIdent*) =>
    evalTactic (← `(tactic| introv; intro $h:ident; introv $hs:binderIdent*))
  | `(tactic| introv _%$tk $hs:binderIdent*) =>
    evalTactic (← `(tactic| introv; intro _%$tk; introv $hs:binderIdent*))
  | _ => throwUnsupportedSyntax
where
  introsDep : TacticM Unit := do
    let t ← getMainTarget
    match t with
    | Expr.forallE _ _ e _ =>
      if e.hasLooseBVars then
        intro1PStep
        introsDep
    | _ => pure ()
  intro1PStep : TacticM Unit :=
    liftMetaTactic fun goal => do
      let (_, goal) ← goal.intro1P
      pure [goal]

/-- Try calling `assumption` on all goals; succeeds if it closes at least one goal. -/
macro "assumption'" : tactic => `(tactic| any_goals assumption)

/-- This tactic clears all auxiliary declarations from the context. -/
elab (name := clearAuxDecl) "clear_aux_decl" : tactic => withMainContext do
  let mut g ← getMainGoal
  for ldec in ← getLCtx do
    if ldec.isAuxDecl then
      g ← g.tryClear ldec.fvarId
  replaceMainGoal [g]

attribute [pp_with_univ] ULift PUnit PEmpty

/--
Definition of `withResetServerInfo.Result` / `withResetServerInfo.Result` 的定义

English:
structure withResetServerInfo.Result
  parameters: (α : Type)
  axioms and operations (3):
    - result? : Option α
    - msgs : MessageLog
    - trees : PersistentArray InfoTree

中文:
结构 withResetServerInfo.Result
  参数: (α : 类型)
  公理与运算 (3 个):
    - result? : 选项类型 α
    - msgs : MessageLog
    - trees : PersistentArray InfoTree
-/
structure withResetServerInfo.Result (α : Type) where
  /-- Return value of the executed tactic. -/
  result? : Option α
  /-- Messages produced by the executed tactic. -/
  msgs : MessageLog
  /-- Info trees produced by the executed tactic, wrapped in `CommandContextInfo.save`. -/
  trees : PersistentArray InfoTree

/--
Definition of `withResetServerInfo` / `withResetServerInfo` 的定义

English:
definition withResetServerInfo
  signature: {α : Type} (t : TacticM α)
  body: do
  let (savedMsgs, savedTrees) ← modifyGetThe Core.State fun st =>
    ((st.messages, st.infoState.trees), { st with messages := {}, infoState.trees := {} })
Prod.snd < > MonadFinally.tryFinally' t fun result? => do
    let msgs ← Core.getMessageLog
    let ist ← getInfoState
    let trees ← ist.trees.mapM fun tree => do
      let tree := tree.substitute ist.assignment
let ctx := .commandCtx ← CommandContextInfo.save
      return InfoTree.context ctx tree
    modifyThe Core.State fun st =>
      { st with messages := savedMsgs, infoState.trees := savedTrees }
    return { result?, msgs, trees }

中文:
定义 withResetServerInfo
  签名: {α : 类型} (t : TacticM α)
  定义体: do
  let (savedMsgs, savedTrees) ← modifyGetThe Core.State fun st =>
    ((st.messages, st.infoState.trees), { st with messages := {}, infoState.trees := {} })
Prod.snd < > MonadFinally.tryFinally' t fun result? => do
    let msgs ← Core.getMessageLog
    let ist ← getInfoState
    let trees ← ist.trees.mapM fun tree => do
      let tree := tree.substitute ist.assignment
let ctx := .commandCtx ← CommandContextInfo.save
      return InfoTree.context ctx tree
    modifyThe Core.State fun st =>
      { st with messages := savedMsgs, infoState.trees := savedTrees }
    return { result?, msgs, trees }
-/
def withResetServerInfo {α : Type} (t : TacticM α) :
    TacticM (withResetServerInfo.Result α) := do
  let (savedMsgs, savedTrees) ← modifyGetThe Core.State fun st =>
    ((st.messages, st.infoState.trees), { st with messages := {}, infoState.trees := {} })
Prod.snd < > MonadFinally.tryFinally' t fun result? => do
    let msgs ← Core.getMessageLog
    let ist ← getInfoState
    let trees ← ist.trees.mapM fun tree => do
      let tree := tree.substitute ist.assignment
let ctx := .commandCtx ← CommandContextInfo.save
      return InfoTree.context ctx tree
    modifyThe Core.State fun st =>
      { st with messages := savedMsgs, infoState.trees := savedTrees }
    return { result?, msgs, trees }

end Mathlib.Tactic
