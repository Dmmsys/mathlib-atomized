/-
Copyright (c) 2025 Robert Maxton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Maxton
-/
module

public import Mathlib.Init
public meta import Lean.PrettyPrinter.Delaborator.Builtins

/-! Delab checking canonicity.

Provides a series of monadic functions in `DelabM` for delaborating expressions differently
if their given instances differ (by definitional equality) with what is synthesized.
Synthesized instances are considered 'canonical' for this purpose.
-/

public meta section
open Lean Meta PrettyPrinter.Delaborator SubExpr

/--
Definition of `Lean.Meta.isCanonicalInstance` / `Lean.Meta.isCanonicalInstance` 的定义

English:
definition Lean.Meta.isCanonicalInstance
  signature: (inst : Expr)
  body: do
  let type ← inferType inst
  let .some synthInst ← trySynthInstance type | return false
  isDefEqI inst synthInst

中文:
定义 Lean.Meta.isCanonicalInstance
  签名: (inst : Expr)
  定义体: do
  let type ← inferType inst
  let .some synthInst ← trySynthInstance type | return false
  isDefEqI inst synthInst
-/
def Lean.Meta.isCanonicalInstance (inst : Expr) : MetaM Bool := do
  let type ← inferType inst
  let .some synthInst ← trySynthInstance type | return false
  isDefEqI inst synthInst

/--
Definition of `delabCheckingCanonical` / `delabCheckingCanonical` 的定义

English:
definition delabCheckingCanonical
  signature: : DelabM (Bool × Term)
  body: do
  let inst ← getExpr
  if ← isCanonicalInstance inst then
    return (true, ← withAnnotateTermInfo `(_))
  else
    return (false, ← delab)

中文:
定义 delabCheckingCanonical
  签名: : DelabM (布尔 × Term)
  定义体: do
  let inst ← getExpr
  if ← isCanonicalInstance inst then
    return (true, ← withAnnotateTermInfo `(_))
  else
    return (false, ← delab)
-/
def delabCheckingCanonical : DelabM (Bool × Term) := do
  let inst ← getExpr
  if ← isCanonicalInstance inst then
    return (true, ← withAnnotateTermInfo `(_))
  else
    return (false, ← delab)

namespace Delab.Noncanonical

/--
Definition of `delabUnary` / `delabUnary` 的定义

English:
definition delabUnary
  signature: (arity arg : Nat) (mkStx : Term -> Delab)
  body: whenPPOption Lean.getPPNotation whenNotPPOption getPPExplicit withOverApp arity do
    let (false, instD) ← withNaryArg arg delabCheckingCanonical | failure
    mkStx instD

中文:
定义 delabUnary
  签名: (arity arg : 自然数) (mkStx : Term -> Delab)
  定义体: whenPPOption Lean.getPPNotation whenNotPPOption getPPExplicit withOverApp arity do
    let (false, instD) ← withNaryArg arg delabCheckingCanonical | failure
    mkStx instD

Depends on / 依赖: Lean.getPPNotation, delabCheckingCanonical, failure, getPPExplicit, getPPNotation, whenNotPPOption, whenPPOption, withNaryArg, withOverApp
-/
def delabUnary (arity arg : Nat) (mkStx : Term -> Delab) : Delab :=
whenPPOption Lean.getPPNotation whenNotPPOption getPPExplicit withOverApp arity do
    let (false, instD) ← withNaryArg arg delabCheckingCanonical | failure
    mkStx instD

/--
Definition of `delabBinary` / `delabBinary` 的定义

English:
definition delabBinary
  signature: (arity arg₁ arg₂ : Nat) (mkStx : Term -> Term -> DelabM Term)
  body: whenPPOption Lean.getPPNotation whenNotPPOption getPPExplicit withOverApp arity do
    let (canonα?, instDα) ← withNaryArg arg₁ delabCheckingCanonical
    let (canonβ?, instDβ) ← withNaryArg arg₂ delabCheckingCanonical
    if canonα? && canonβ? then failure
    mkStx instDα instDβ

中文:
定义 delabBinary
  签名: (arity arg₁ arg₂ : 自然数) (mkStx : Term -> Term -> DelabM Term)
  定义体: whenPPOption Lean.getPPNotation whenNotPPOption getPPExplicit withOverApp arity do
    let (canonα?, instDα) ← withNaryArg arg₁ delabCheckingCanonical
    let (canonβ?, instDβ) ← withNaryArg arg₂ delabCheckingCanonical
    if canonα? && canonβ? then failure
    mkStx instDα instDβ

Depends on / 依赖: Lean.getPPNotation, delabCheckingCanonical, failure, getPPExplicit, getPPNotation, whenNotPPOption, whenPPOption, withNaryArg, withOverApp
-/
def delabBinary (arity arg₁ arg₂ : Nat) (mkStx : Term -> Term -> DelabM Term) : Delab :=
whenPPOption Lean.getPPNotation whenNotPPOption getPPExplicit withOverApp arity do
    let (canonα?, instDα) ← withNaryArg arg₁ delabCheckingCanonical
    let (canonβ?, instDβ) ← withNaryArg arg₂ delabCheckingCanonical
    if canonα? && canonβ? then failure
    mkStx instDα instDβ

end Delab.Noncanonical
