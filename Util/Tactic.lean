/-
Copyright (c) 2022 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Jannis Limperg
-/
module

public import Mathlib.Init
public meta import Lean.MetavarContext

/-!
# Miscellaneous helper functions for tactics.

TODO: Ideally we would find good homes for everything in this file, eventually removing it.
-/

public meta section

namespace Mathlib.Tactic

open Lean Meta Tactic

variable {m : Type -> Type}

/--
Definition of `modifyMetavarDecl` / `modifyMetavarDecl` 的定义

English:
definition modifyMetavarDecl
  signature: [MonadMCtx m] (mvarId : MVarId)
  body: modifyMCtx fun mctx =>
    match mctx.decls.find? mvarId with
    | none => mctx
    | some mdecl => { mctx with decls := mctx.decls.insert mvarId (f mdecl) }

中文:
定义 modifyMetavarDecl
  签名: [MonadMCtx m] (mvarId : MVarId)
  定义体: modifyMCtx fun mctx =>
    match mctx.decls.find? mvarId with
    | none => mctx
    | some mdecl => { mctx with decls := mctx.decls.insert mvarId (f mdecl) }

Depends on / 依赖: insert, mctx.decls.find, mctx.decls.insert, modifyMCtx, mvarId
-/
def modifyMetavarDecl [MonadMCtx m] (mvarId : MVarId)
    (f : MetavarDecl -> MetavarDecl) : m Unit :=
  modifyMCtx fun mctx =>
    match mctx.decls.find? mvarId with
    | none => mctx
    | some mdecl => { mctx with decls := mctx.decls.insert mvarId (f mdecl) }

/--
Definition of `modifyTarget` / `modifyTarget` 的定义

English:
definition modifyTarget
  signature: [MonadMCtx m] (mvarId : MVarId) (f : Expr -> Expr)
  body: modifyMetavarDecl mvarId fun mdecl =>
    { mdecl with type := f mdecl.type }

中文:
定义 modifyTarget
  签名: [MonadMCtx m] (mvarId : MVarId) (f : Expr -> Expr)
  定义体: modifyMetavarDecl mvarId fun mdecl =>
    { mdecl with type := f mdecl.type }

Depends on / 依赖: mdecl.type, modifyMetavarDecl, mvarId
-/
def modifyTarget [MonadMCtx m] (mvarId : MVarId) (f : Expr -> Expr) : m Unit :=
  modifyMetavarDecl mvarId fun mdecl =>
    { mdecl with type := f mdecl.type }

/--
Definition of `modifyLocalContext` / `modifyLocalContext` 的定义

English:
definition modifyLocalContext
  signature: [MonadMCtx m] (mvarId : MVarId)
  body: modifyMetavarDecl mvarId fun mdecl =>
    { mdecl with lctx := f mdecl.lctx }

中文:
定义 modifyLocalContext
  签名: [MonadMCtx m] (mvarId : MVarId)
  定义体: modifyMetavarDecl mvarId fun mdecl =>
    { mdecl with lctx := f mdecl.lctx }

Depends on / 依赖: mdecl.lctx, modifyMetavarDecl, mvarId
-/
def modifyLocalContext [MonadMCtx m] (mvarId : MVarId)
    (f : LocalContext -> LocalContext) : m Unit :=
  modifyMetavarDecl mvarId fun mdecl =>
    { mdecl with lctx := f mdecl.lctx }

/--
Definition of `modifyLocalDecl` / `modifyLocalDecl` 的定义

English:
definition modifyLocalDecl
  signature: [MonadMCtx m] (mvarId : MVarId) (fvarId : FVarId)
  body: modifyLocalContext mvarId fun lctx => lctx.modifyLocalDecl fvarId f

中文:
定义 modifyLocalDecl
  签名: [MonadMCtx m] (mvarId : MVarId) (fvarId : FVarId)
  定义体: modifyLocalContext mvarId fun lctx => lctx.modifyLocalDecl fvarId f

Depends on / 依赖: fvarId, lctx.modifyLocalDecl, modifyLocalContext, modifyLocalDecl, mvarId
-/
def modifyLocalDecl [MonadMCtx m] (mvarId : MVarId) (fvarId : FVarId)
    (f : LocalDecl -> LocalDecl) : m Unit :=
  modifyLocalContext mvarId fun lctx => lctx.modifyLocalDecl fvarId f

end Mathlib.Tactic
