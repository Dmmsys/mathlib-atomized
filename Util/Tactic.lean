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

variable {m : Type → Type}

/--
`modifyMetavarDecl mvarId f` updates the `MetavarDecl` for `mvarId` with `f`.
Conditions on `f`:

- The target of `f mdecl` is defeq to the target of `mdecl`.
- The local context of `f mdecl` must contain the same fvars as the local
  context of `mdecl`. For each fvar in the local context of `f mdecl`, the type
  (and value, if any) of the fvar must be defeq to the corresponding fvar in
  the local context of `mdecl`.

If `mvarId` does not refer to a declared metavariable, nothing happens.
-/
/-
**Mathlib.Tactic.modifyMetavarDecl** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic`。
形式化陈述：modifyMetavarDecl [MonadMCtx m] (mvarId : MVarId) (f : MetavarDecl -> Meta
varDecl) : m Unit
参数：mvarId : MVarId；f : MetavarDecl -> MetavarDecl。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`modifyMetavarDecl mvarId f` updates the `MetavarDecl` for `mvarId` with `f`.
Conditions on `f`:

- The target of `f mdecl` is defeq to the target of `mdecl`.
- The local context of `f mdecl` must contain the same fvars as the local
  context of `mdecl`. For each fvar in the local context of `f mdecl`, the type
  (and value, if any) of the fvar must be defeq to the corresponding fvar in
  the local context of `mdecl`.

If `mvarId` does not refer to a declared metavariable, nothing happens.
-/
def modifyMetavarDecl [MonadMCtx m] (mvarId : MVarId)
    (f : MetavarDecl → MetavarDecl) : m Unit :=
  modifyMCtx fun mctx ↦
    match mctx.decls.find? mvarId with
    | none => mctx
    | some mdecl => { mctx with decls := mctx.decls.insert mvarId (f mdecl) }

/--
`modifyTarget mvarId f` updates the target of the metavariable `mvarId` with
`f`. For any `e`, `f e` must be defeq to `e`. If `mvarId` does not refer to
a declared metavariable, nothing happens.
-/
/-
**Mathlib.Tactic.modifyTarget** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic`。
形式化陈述：modifyTarget [MonadMCtx m] (mvarId : MVarId) (f : Expr -> Expr) : m Unit
参数：mvarId : MVarId；f : Expr -> Expr。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`modifyTarget mvarId f` updates the target of the metavariable `mvarId` with
`f`. For any `e`, `f e` must be defeq to `e`. If `mvarId` does not refer to
a declared metavariable, nothing happens.
-/
def modifyTarget [MonadMCtx m] (mvarId : MVarId) (f : Expr → Expr) : m Unit :=
  modifyMetavarDecl mvarId fun mdecl ↦
    { mdecl with type := f mdecl.type }

/--
`modifyLocalContext mvarId f` updates the local context of the metavariable
`mvarId` with `f`. The new local context must contain the same fvars as the old
local context and the types (and values, if any) of the fvars in the new local
context must be defeq to their equivalents in the old local context.

If `mvarId` does not refer to a declared metavariable, nothing happens.
-/
/-
**Mathlib.Tactic.modifyLocalContext** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic`。
形式化陈述：modifyLocalContext [MonadMCtx m] (mvarId : MVarId) (f : LocalContext -> Lo
calContext) : m Unit
参数：mvarId : MVarId；f : LocalContext -> LocalContext。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`modifyLocalContext mvarId f` updates the local context of the metavariable
`mvarId` with `f`. The new local context must contain the same fvars as the old
local context and the types (and values, if any) of the fvars in the new local
context must be defeq to their equivalents in the old local context.

If `mvarId` does not refer to a declared metavariable, nothing happens.
-/
def modifyLocalContext [MonadMCtx m] (mvarId : MVarId)
    (f : LocalContext → LocalContext) : m Unit :=
  modifyMetavarDecl mvarId fun mdecl ↦
    { mdecl with lctx := f mdecl.lctx }

/--
`modifyLocalDecl mvarId fvarId f` updates the local decl `fvarId` in the local
context of `mvarId` with `f`. `f` must leave the `fvarId` and `index` of the
`LocalDecl` unchanged. The type of the new `LocalDecl` must be defeq to the type
of the old `LocalDecl` (and the same applies to the value of the `LocalDecl`, if
any).

If `mvarId` does not refer to a declared metavariable or if `fvarId` does not
exist in the local context of `mvarId`, nothing happens.
-/
/-
**Mathlib.Tactic.modifyLocalDecl** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic`。
形式化陈述：modifyLocalDecl [MonadMCtx m] (mvarId : MVarId) (fvarId : FVarId) (f : Loc
alDecl -> LocalDecl) : m Unit
参数：mvarId : MVarId；fvarId : FVarId；f : LocalDecl -> LocalDecl。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`modifyLocalDecl mvarId fvarId f` updates the local decl `fvarId` in the local
context of `mvarId` with `f`. `f` must leave the `fvarId` and `index` of the
`LocalDecl` unchanged. The type of the new `LocalDecl` must be defeq to the type
of the old `LocalDecl` (and the same applies to the value of the `LocalDecl`, if
any).

If `mvarId` does not refer to a declared metavariable or if `fvarId` does not
exist in the local context of `mvarId`, nothing happens.
-/
def modifyLocalDecl [MonadMCtx m] (mvarId : MVarId) (fvarId : FVarId)
    (f : LocalDecl → LocalDecl) : m Unit :=
  modifyLocalContext mvarId fun lctx ↦ lctx.modifyLocalDecl fvarId f

end Mathlib.Tactic

