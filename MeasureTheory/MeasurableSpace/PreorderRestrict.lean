/-
Copyright (c) 2024 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.Order.Restriction

/-!
# Measurability of the restriction function for functions indexed by a preorder

We prove that the map which restricts a function `f : (i : α) → X i` to elements `≤ a` is
measurable.
-/

public section

open MeasureTheory

namespace Preorder

variable {α : Type*} [Preorder α] {X : α → Type*} [∀ a, MeasurableSpace (X a)]

@[fun_prop]
/-
**Preorder.measurable_restrictLe** 是 Mathlib 中的一个定理，位于命名空间 `Preorder`。
形式化陈述：measurable_restrictLe (a : α) : Measurable (restrictLe (π
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.measurable_restrict`：Set.measurable_restrict (s : Set δ) : Measurabl
e (s.domRestrict (π
-/
theorem measurable_restrictLe (a : α) : Measurable (restrictLe (π := X) a) :=
    Set.measurable_restrict _

@[fun_prop]
/-
**Preorder.measurable_restrictLe** 是 Mathlib 中的一个定理，位于命名空间 `Preorder`。
形式化陈述：measurable_restrictLe (a : α) : Measurable (restrictLe (π
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.measurable_restrict`：Set.measurable_restrict (s : Set δ) : Measurabl
e (s.domRestrict (π
-/
theorem measurable_restrictLe₂ {a b : α} (hab : a ≤ b) : Measurable (restrictLe₂ (π := X) hab) :=
  Set.measurable_restrict₂ _

variable [LocallyFiniteOrderBot α]

@[fun_prop]
/-
**Preorder.measurable_frestrictLe** 是 Mathlib 中的一个定理，位于命名空间 `Preorder`。
形式化陈述：measurable_frestrictLe (a : α) : Measurable (frestrictLe (π
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.measurable_restrict`：Finset.measurable_restrict (s : Finset δ) : 
Measurable (s.restrict (π
-/
theorem measurable_frestrictLe (a : α) : Measurable (frestrictLe (π := X) a) :=
  Finset.measurable_restrict _

@[fun_prop]
/-
**Preorder.measurable_frestrictLe** 是 Mathlib 中的一个定理，位于命名空间 `Preorder`。
形式化陈述：measurable_frestrictLe (a : α) : Measurable (frestrictLe (π
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.measurable_restrict`：Finset.measurable_restrict (s : Finset δ) : 
Measurable (s.restrict (π
-/
theorem measurable_frestrictLe₂ {a b : α} (hab : a ≤ b) : Measurable (frestrictLe₂ (π := X) hab) :=
  Finset.measurable_restrict₂ _

end Preorder

