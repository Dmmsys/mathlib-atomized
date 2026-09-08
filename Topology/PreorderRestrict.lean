/-
Copyright (c) 2024 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Order.Restriction
public import Mathlib.Topology.Constructions

/-!
# Continuity of the restriction function for functions indexed by a preorder

We prove that the map which restricts a function `f : (i : α) → X i` to elements `≤ a` is
continuous.
-/

public section

namespace Preorder

variable {α : Type*} [Preorder α] {X : α → Type*} [∀ i, TopologicalSpace (X i)]

@[continuity, fun_prop]
/-
**Preorder.continuous_restrictLe** 是 Mathlib 中的一个定理，位于命名空间 `Preorder`。
形式化陈述：continuous_restrictLe (a : α) : Continuous (restrictLe (π
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Pi.continuous_domRestrict`：Pi.continuous_domRestrict (S : Set ι) : Conti
nuous (S.domRestrict : (forall i : ι, A i) -> (forall i : S, A i))
-/
theorem continuous_restrictLe (a : α) : Continuous (restrictLe (π := X) a) :=
  Pi.continuous_domRestrict _

@[continuity, fun_prop]
/-
**Preorder.continuous_restrictLe** 是 Mathlib 中的一个定理，位于命名空间 `Preorder`。
形式化陈述：continuous_restrictLe (a : α) : Continuous (restrictLe (π
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Pi.continuous_domRestrict`：Pi.continuous_domRestrict (S : Set ι) : Conti
nuous (S.domRestrict : (forall i : ι, A i) -> (forall i : S, A i))
-/
theorem continuous_restrictLe₂ {a b : α} (hab : a ≤ b) : Continuous (restrictLe₂ (π := X) hab) :=
  Pi.continuous_domRestrict₂ _

variable [LocallyFiniteOrderBot α]

@[continuity, fun_prop]
/-
**Preorder.continuous_frestrictLe** 是 Mathlib 中的一个定理，位于命名空间 `Preorder`。
形式化陈述：continuous_frestrictLe (a : α) : Continuous (frestrictLe (π
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.continuous_restrict`：Finset.continuous_restrict (s : Finset ι) : 
Continuous (s.restrict (π
-/
theorem continuous_frestrictLe (a : α) : Continuous (frestrictLe (π := X) a) :=
  Finset.continuous_restrict _

@[continuity, fun_prop]
/-
**Preorder.continuous_frestrictLe** 是 Mathlib 中的一个定理，位于命名空间 `Preorder`。
形式化陈述：continuous_frestrictLe (a : α) : Continuous (frestrictLe (π
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.continuous_restrict`：Finset.continuous_restrict (s : Finset ι) : 
Continuous (s.restrict (π
-/
theorem continuous_frestrictLe₂ {a b : α} (hab : a ≤ b) :
    Continuous (frestrictLe₂ (π := X) hab) :=
  Finset.continuous_restrict₂ _

end Preorder

