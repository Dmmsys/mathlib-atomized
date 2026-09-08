/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Init

/-!
# Json serialization typeclass for `PUnit` & `Fin n` & `Subtype p`
-/

public section

universe u


namespace Lean

deriving instance FromJson, ToJson for PUnit

-- See https://github.com/leanprover/lean4/issues/10295
attribute [nolint unusedArguments] Lean.instToJsonPUnit_mathlib.toJson

/-
**Lean.** 是 Mathlib 中的一个实例，位于命名空间 `Lean`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {n : Nat} : FromJson (Fin n) where
  fromJson? j := do
    let i : Nat ← fromJson? j
    if h : i < n then
      return ⟨i, h⟩
    else
      throw s!"must be less than {n}"
/-
**Lean.** 是 Mathlib 中的一个实例，位于命名空间 `Lean`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {n : Nat} : ToJson (Fin n) where
  toJson i := toJson i.val
/-
**Lean.** 是 Mathlib 中的一个实例，位于命名空间 `Lean`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type u} [FromJson α] (p : α → Prop) [DecidablePred p] : FromJson (Subtype p) where
  fromJson? j := do
    let i : α ← fromJson? j
    if h : p i then
      return ⟨i, h⟩
    else
      throw "condition does not hold"
/-
**Lean.** 是 Mathlib 中的一个实例，位于命名空间 `Lean`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type u} [ToJson α] (p : α → Prop) : ToJson (Subtype p) where
  toJson x := toJson x.val

end Lean

