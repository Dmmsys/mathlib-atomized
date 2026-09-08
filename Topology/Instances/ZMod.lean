/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Topology.Order
public import Mathlib.Data.ZMod.Defs

/-!
# Topology on `ZMod N`

We equip `ZMod N` with the discrete topology.
-/

public section

namespace ZMod

variable {N : ℕ}

/-- The discrete topology (every set is open). -/
/-
**ZMod.** 是 Mathlib 中的一个实例，位于命名空间 `ZMod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The discrete topology (every set is open).
-/
instance : TopologicalSpace (ZMod N) := ⊥
/-
**ZMod.** 是 Mathlib 中的一个实例，位于命名空间 `ZMod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DiscreteTopology (ZMod N) := ⟨rfl⟩

end ZMod

