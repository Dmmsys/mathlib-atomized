/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Init
public import Lean.LocalContext
public import Batteries.Control.AlternativeMonad

/-!
# Additional methods about `LocalContext`
-/

public section

namespace Lean.LocalContext

universe u v
variable {m : Type u -> Type v} [AlternativeMonad m]
variable {β : Type u}

/--
Definition of `firstDeclM` / `firstDeclM` 的定义

English:
definition firstDeclM
  signature: (lctx : LocalContext) (f : LocalDecl -> m β)
  body: do match (← lctx.findDeclM? (optional ∘ f)) with
  | none => failure
  | some b => pure b

中文:
定义 firstDeclM
  签名: (lctx : LocalContext) (f : LocalDecl -> m β)
  定义体: do match (← lctx.findDeclM? (optional ∘ f)) with
  | none => failure
  | some b => pure b
-/
@[specialize] def firstDeclM (lctx : LocalContext) (f : LocalDecl -> m β) : m β :=
  do match (← lctx.findDeclM? (optional ∘ f)) with
  | none => failure
  | some b => pure b

/--
Definition of `lastDeclM` / `lastDeclM` 的定义

English:
definition lastDeclM
  signature: (lctx : LocalContext) (f : LocalDecl -> m β)
  body: do match (← lctx.findDeclRevM? (optional ∘ f)) with
  | none => failure
  | some b => pure b

中文:
定义 lastDeclM
  签名: (lctx : LocalContext) (f : LocalDecl -> m β)
  定义体: do match (← lctx.findDeclRevM? (optional ∘ f)) with
  | none => failure
  | some b => pure b
-/
@[specialize] def lastDeclM (lctx : LocalContext) (f : LocalDecl -> m β) : m β :=
  do match (← lctx.findDeclRevM? (optional ∘ f)) with
  | none => failure
  | some b => pure b

end Lean.LocalContext
