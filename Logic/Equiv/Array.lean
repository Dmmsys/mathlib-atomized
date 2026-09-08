/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Logic.Equiv.List

/-!
# Equivalences involving `Array`
-/

@[expose] public section


namespace Equiv

/-- The natural equivalence between arrays and lists. -/
/-
**Equiv.arrayEquivList** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：arrayEquivList (α : Type*) : Array α ≃ List α where toFun
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural equivalence between arrays and lists.
-/
def arrayEquivList (α : Type*) : Array α ≃ List α where
  toFun := Array.toList
  invFun := Array.mk

end Equiv

/- Porting note: removed instances for what would be ported as `Traversable (Array α)` and
`LawfulTraversable (Array α)`. These would

1. be implemented directly in terms of `Array` functionality for efficiency, rather than being the
traversal of some other type transported along an equivalence to `Array α` (as the traversable
instance for `array` was)

2. belong in `Mathlib/Control/Traversable/Instances.lean` instead of this file. -/

-- namespace Array'

-- open Function

-- variable {n : ℕ}

-- instance : Traversable (Array' n) :=
--   @Equiv.traversable (flip Vector n) _ (fun α => Equiv.vectorEquivArray α n) _

-- instance : LawfulTraversable (Array' n) :=
--   @Equiv.isLawfulTraversable (flip Vector n) _ (fun α => Equiv.vectorEquivArray α n) _ _

-- end Array'

/-- If `α` is encodable, then so is `Array α`. -/
/-
**Array.encodable** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Array.encodable {α} [Encodable α] : Encodable (Array α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α` is encodable, then so is `Array α`.
-/
instance Array.encodable {α} [Encodable α] : Encodable (Array α) :=
  Encodable.ofEquiv _ (Equiv.arrayEquivList _)

/-- If `α` is countable, then so is `Array α`. -/
/-
**Array.countable** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Array.countable {α} [Countable α] : Countable (Array α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Countable.of_equiv`：Countable.of_equiv (α : Sort*) [Countable α] (e : α 
≃ β) : Countable β
· 使用定理 `List.countable`：∀ {α : Type u_2} [Countable α], Countable (List α)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `α` is countable, then so is `Array α`.
-/
instance Array.countable {α} [Countable α] : Countable (Array α) :=
  Countable.of_equiv _ (Equiv.arrayEquivList α).symm
