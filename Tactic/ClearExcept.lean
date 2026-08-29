/-
Copyright (c) 2022 Joshua Clune. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joshua Clune
-/
module

public import Mathlib.Init
public meta import Lean.Elab.Tactic.ElabTerm

/-!
# The `clear*` tactic

This file provides a variant of the `clear` tactic, which clears all hypotheses it can
besides a provided list, class instances, and auxiliary declarations.
-/

public meta section

open Lean.Meta

namespace Lean.Elab.Tactic

/--
Definition of `getVarsToClear` / `getVarsToClear` 的定义

English:
definition getVarsToClear
  signature: (preserve : Array FVarId)
  body: do
  let mut toClear : Array FVarId := #[]
  for decl in ← getLCtx do
    unless preserve.contains decl.fvarId || decl.isAuxDecl do
      if let none ← isClass? decl.type then
        toClear := toClear.push decl.fvarId
  return toClear

中文:
定义 getVarsToClear
  签名: (preserve : Array FVarId)
  定义体: do
  let mut toClear : Array FVarId := #[]
  for decl in ← getLCtx do
    unless preserve.contains decl.fvarId || decl.isAuxDecl do
      if let none ← isClass? decl.type then
        toClear := toClear.push decl.fvarId
  return toClear
-/
def getVarsToClear (preserve : Array FVarId) : MetaM (Array FVarId) := do
  let mut toClear : Array FVarId := #[]
  for decl in ← getLCtx do
    unless preserve.contains decl.fvarId || decl.isAuxDecl do
      if let none ← isClass? decl.type then
        toClear := toClear.push decl.fvarId
  return toClear

/--
Definition of `clearExcept` / `clearExcept` 的定义

English:
definition clearExcept
  signature: (preserve : Array FVarId) (goal : MVarId)
  body: do
  let toClear ← getVarsToClear preserve
  goal.tryClearMany toClear

中文:
定义 clearExcept
  签名: (preserve : Array FVarId) (goal : MVarId)
  定义体: do
  let toClear ← getVarsToClear preserve
  goal.tryClearMany toClear
-/
def clearExcept (preserve : Array FVarId) (goal : MVarId) : MetaM MVarId := do
  let toClear ← getVarsToClear preserve
  goal.tryClearMany toClear

/-- Clears all hypotheses it can, except those provided after a minus sign, class instances, and
hidden auxiliary declarations (for example recursive hypotheses). Example:
```
  clear * - h₁ h₂
```
The intent is that `clear * -` only clears user-visible local declarations; hidden auxiliary
declarations should be handled by more specific mechanisms when needed. -/
syntax (name := clearExceptTactic) "clear " "*" " -" (ppSpace colGt ident)* : tactic

elab_rules : tactic
  | `(tactic| clear * - $hs:ident*) => do
    let fvarIds ← getFVarIds hs
    liftMetaTactic1 fun goal => clearExcept fvarIds goal

end Lean.Elab.Tactic
