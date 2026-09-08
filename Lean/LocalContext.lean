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
variable {m : Type u → Type v} [AlternativeMonad m]
variable {β : Type u}

/-- Return the result of `f` on the first local declaration on which `f` succeeds. -/
/-
**Lean.LocalContext.firstDeclM** 是 Mathlib 中的一个定义，位于命名空间 `Lean.LocalContext`。
形式化陈述：{m : Type u → Type v} → [AlternativeMonad m] → {β : Type u} → LocalContext
 → (LocalDecl → m β) → m β
参数：LocalDecl → m β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Return the result of `f` on the first local declaration on which `f` succeeds.
-/
@[specialize] def firstDeclM (lctx : LocalContext) (f : LocalDecl → m β) : m β :=
  do match (← lctx.findDeclM? (optional ∘ f)) with
  | none   => failure
  | some b => pure b

/-- Return the result of `f` on the last local declaration on which `f` succeeds. -/
/-
**Lean.LocalContext.lastDeclM** 是 Mathlib 中的一个定义，位于命名空间 `Lean.LocalContext`。
形式化陈述：{m : Type u → Type v} → [AlternativeMonad m] → {β : Type u} → LocalContext
 → (LocalDecl → m β) → m β
参数：LocalDecl → m β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Return the result of `f` on the last local declaration on which `f` succeeds.
-/
@[specialize] def lastDeclM (lctx : LocalContext) (f : LocalDecl → m β) : m β :=
  do match (← lctx.findDeclRevM? (optional ∘ f)) with
  | none   => failure
  | some b => pure b

end Lean.LocalContext

