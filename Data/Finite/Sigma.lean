/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sigma

/-!
# Finiteness of sigma types
-/

public section

variable {α : Type*}

namespace Finite

/-
**Finite.** 是 Mathlib 中的一个实例，位于命名空间 `Finite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {β : α → Type*} [Finite α] [∀ a, Finite (β a)] : Finite (Σ a, β a) := by
  let := Fintype.ofFinite α
  let := fun a => Fintype.ofFinite (β a)
  infer_instance
/-
**Finite.** 是 Mathlib 中的一个实例，位于命名空间 `Finite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {ι : Sort*} {π : ι → Sort*} [Finite ι] [∀ i, Finite (π i)] : Finite (Σ' i, π i) :=
  of_equiv _ (Equiv.psigmaEquivSigmaPLift π).symm

end Finite

