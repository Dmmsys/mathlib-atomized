/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.UpperLower
public import Mathlib.Topology.Algebra.Group.Pointwise

/-!
# Topological facts about upper/lower/order-connected sets

The topological closure and interior of an upper/lower/order-connected set is an
upper/lower/order-connected set (with the notable exception of the closure of an order-connected
set).

## Implementation notes

The same lemmas are true in the additive/multiplicative worlds. To avoid code duplication, we
provide `HasUpperLowerClosure`, an ad hoc axiomatisation of the properties we need.
-/

public section


open Function Set

open scoped Pointwise

/-- Ad hoc class stating that the closure of an upper set is an upper set. This is used to state
lemmas that do not mention algebraic operations for both the additive and multiplicative versions
simultaneously. If you find a satisfying replacement for this typeclass, please remove it! -/
/-
**HasUpperLowerClosure** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_1) → [TopologicalSpace α] → [Preorder α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Ad hoc class stating that the closure of an upper set is an upper set. This is u
sed to state
lemmas that do not mention algebraic operations for both the additive and multip
licative versions
simultaneously. If you find a satisfying replacement for this typeclass, please 
remove it!
-/
class HasUpperLowerClosure (α : Type*) [TopologicalSpace α] [Preorder α] : Prop where
  isUpperSet_closure : ∀ s : Set α, IsUpperSet s → IsUpperSet (closure s)
  isLowerSet_closure : ∀ s : Set α, IsLowerSet s → IsLowerSet (closure s)
  isOpen_upperClosure : ∀ s : Set α, IsOpen s → IsOpen (upperClosure s : Set α)
  isOpen_lowerClosure : ∀ s : Set α, IsOpen s → IsOpen (lowerClosure s : Set α)

variable {α : Type*} [TopologicalSpace α]

-- See note [lower instance priority]
@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IsOrderedMonoid.to_hasUpperLowerClosure
    [CommGroup α] [Preorder α] [IsOrderedMonoid α]
    [ContinuousConstSMul α α] : HasUpperLowerClosure α where
  isUpperSet_closure s h x y hxy hx :=
    closure_mono (h.smul_subset <| one_le_div'.2 hxy) <| by
      rw [closure_smul]
      exact ⟨x, hx, div_mul_cancel _ _⟩
  isLowerSet_closure s h x y hxy hx :=
    closure_mono (h.smul_subset <| div_le_one'.2 hxy) <| by
      rw [closure_smul]
      exact ⟨x, hx, div_mul_cancel _ _⟩
  isOpen_upperClosure s hs := by
    rw [← mul_one s, ← mul_upperClosure]
    exact hs.mul_right
  isOpen_lowerClosure s hs := by
    rw [← mul_one s, ← mul_lowerClosure]
    exact hs.mul_right

variable [Preorder α] [HasUpperLowerClosure α] {s : Set α}
/-
**IsUpperSet.closure** 是 Mathlib 中的一个定理，位于命名空间 `IsUpperSet`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] [inst_1 : Preorder α] [HasUpp
erLowerClosure α] {s : Set α},   IsUpperSet s → IsUpperSet (closure s)
参数：closure s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasUpperLowerClosure.isUpperSet_closure`：∀ {α : Type u_1} {inst : Topolo
gicalSpace α} {inst_1 : Preorder α} [self : HasUpperLowerClosure α] (s : Set α),
   IsUpperSet s → IsUpperSet …
-/
protected theorem IsUpperSet.closure : IsUpperSet s → IsUpperSet (closure s) :=
  HasUpperLowerClosure.isUpperSet_closure _
/-
**IsLowerSet.closure** 是 Mathlib 中的一个定理，位于命名空间 `IsLowerSet`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] [inst_1 : Preorder α] [HasUpp
erLowerClosure α] {s : Set α},   IsLowerSet s → IsLowerSet (closure s)
参数：closure s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasUpperLowerClosure.isLowerSet_closure`：∀ {α : Type u_1} {inst : Topolo
gicalSpace α} {inst_1 : Preorder α} [self : HasUpperLowerClosure α] (s : Set α),
   IsLowerSet s → IsLowerSet …
-/
protected theorem IsLowerSet.closure : IsLowerSet s → IsLowerSet (closure s) :=
  HasUpperLowerClosure.isLowerSet_closure _
/-
**IsOpen.upperClosure** 是 Mathlib 中的一个定理，位于命名空间 `IsOpen`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] [inst_1 : Preorder α] [HasUpp
erLowerClosure α] {s : Set α},   IsOpen s → IsOpen ↑(upperClosure s)
参数：upperClosure s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasUpperLowerClosure.isOpen_upperClosure`：∀ {α : Type u_1} {inst : Topol
ogicalSpace α} {inst_1 : Preorder α} [self : HasUpperLowerClosure α] (s : Set α)
,   IsOpen s → IsOpen ↑(upperC…
-/
protected theorem IsOpen.upperClosure : IsOpen s → IsOpen (upperClosure s : Set α) :=
  HasUpperLowerClosure.isOpen_upperClosure _
/-
**IsOpen.lowerClosure** 是 Mathlib 中的一个定理，位于命名空间 `IsOpen`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] [inst_1 : Preorder α] [HasUpp
erLowerClosure α] {s : Set α},   IsOpen s → IsOpen ↑(lowerClosure s)
参数：lowerClosure s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasUpperLowerClosure.isOpen_lowerClosure`：∀ {α : Type u_1} {inst : Topol
ogicalSpace α} {inst_1 : Preorder α} [self : HasUpperLowerClosure α] (s : Set α)
,   IsOpen s → IsOpen ↑(lowerC…
-/
protected theorem IsOpen.lowerClosure : IsOpen s → IsOpen (lowerClosure s : Set α) :=
  HasUpperLowerClosure.isOpen_lowerClosure _
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasUpperLowerClosure αᵒᵈ where
  isUpperSet_closure := @IsLowerSet.closure α _ _ _
  isLowerSet_closure := @IsUpperSet.closure α _ _ _
  isOpen_upperClosure := @IsOpen.lowerClosure α _ _ _
  isOpen_lowerClosure := @IsOpen.upperClosure α _ _ _

/-
Note: `s.OrdConnected` does not imply `(closure s).OrdConnected`, as we can see by taking
`s := Ioo 0 1 × Ioo 1 2 ∪ Ioo 2 3 × Ioo 0 1` because then
`closure s = Icc 0 1 × Icc 1 2 ∪ Icc 2 3 × Icc 0 1` is not order-connected as
`(1, 1) ∈ closure s`, `(2, 1) ∈ closure s` but `Icc (1, 1) (2, 1) ⊈ closure s`.

`s` looks like
```
xxooooo
xxooooo
oooooxx
oooooxx
```
-/
/-
**IsUpperSet.interior** 是 Mathlib 中的一个定理，位于命名空间 `IsUpperSet`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] [inst_1 : Preorder α] [HasUpp
erLowerClosure α] {s : Set α},   IsUpperSet s → IsUpperSet (interior s)
参数：interior s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isLowerSet_compl`：∀ {α : Type u_1} [inst : LE α] {s : Set α}, IsLowerSet
 sᶜ ↔ IsUpperSet s
· 使用定理 `closure_compl`：closure_compl : closure sᶜ = (interior s)ᶜ
· 使用定理 `IsLowerSet.closure`：∀ {α : Type u_1} [inst : TopologicalSpace α] [inst_1
 : Preorder α] [HasUpperLowerClosure α] {s : Set α},   IsLowerSet s → IsLowerSet
 (closur…
· 使用定理 `IsUpperSet.compl`：IsUpperSet.compl (hs : IsUpperSet s) : IsLowerSet sᶜ

--- 原说明 ---
Note: `s.OrdConnected` does not imply `(closure s).OrdConnected`, as we can see 
by taking
`s := Ioo 0 1 × Ioo 1 2 ∪ Ioo 2 3 × Ioo 0 1` because then
`closure s = Icc 0 1 × Icc 1 2 ∪ Icc 2 3 × Icc 0 1` is not order-connected as
`(1, 1) ∈ closure s`, `(2, 1) ∈ closure s` but `Icc (1, 1) (2, 1) ⊈ closure s`.

`s` looks like
```
xxooooo
xxooooo
oooooxx
oooooxx
```
-/
protected theorem IsUpperSet.interior (h : IsUpperSet s) : IsUpperSet (interior s) := by
  rw [← isLowerSet_compl, ← closure_compl]
  exact h.compl.closure
/-
**IsLowerSet.interior** 是 Mathlib 中的一个定理，位于命名空间 `IsLowerSet`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] [inst_1 : Preorder α] [HasUpp
erLowerClosure α] {s : Set α},   IsLowerSet s → IsLowerSet (interior s)
参数：interior s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUpperSet.interior`：∀ {α : Type u_1} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [HasUpperLowerClosure α] {s : Set α},   IsUpperSet s → IsUpperSe
t (interi…
· 使用定理 `instHasUpperLowerClosureOrderDual`：∀ {α : Type u_1} [inst : TopologicalS
pace α] [inst_1 : Preorder α] [HasUpperLowerClosure α], HasUpperLowerClosure αᵒᵈ
· 使用定理 `IsLowerSet.toDual`：∀ {α : Type u_1} [inst : LE α] {s : Set α}, IsLowerSe
t s → IsUpperSet (⇑OrderDual.ofDual ⁻¹' s)
-/
protected theorem IsLowerSet.interior (h : IsLowerSet s) : IsLowerSet (interior s) :=
  h.toDual.interior
/-
**Set.OrdConnected.interior** 是 Mathlib 中的一个定理，位于命名空间 `Set.OrdConnected`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] [inst_1 : Preorder α] [HasUpp
erLowerClosure α] {s : Set α},   s.OrdConnected → (interior s).OrdConnected
参数：interior s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.OrdConnected.upperClosure_inter_lowerClosure`：Set.OrdConnected.upper
Closure_inter_lowerClosure (h : s.OrdConnected) : ↑(upperClosure s) inter ↑(lowe
rClosure s) = s
· 使用定理 `interior_inter`：interior_inter : interior (s inter t) = interior s inter
 interior t
· 使用定理 `Set.OrdConnected.inter`：∀ {α : Type u_1} [inst : Preorder α] {s t : Set 
α}, s.OrdConnected → t.OrdConnected → (s ∩ t).OrdConnected
· 使用定理 `IsUpperSet.ordConnected`：IsUpperSet.ordConnected (h : IsUpperSet s) : s.
OrdConnected
· 使用定理 `IsUpperSet.interior`：∀ {α : Type u_1} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [HasUpperLowerClosure α] {s : Set α},   IsUpperSet s → IsUpperSe
t (interi…
· 使用定理 `UpperSet.upper`：∀ {α : Type u_1} [inst : LE α] (s : UpperSet α), IsUpper
Set ↑s
· 使用定理 `IsLowerSet.ordConnected`：IsLowerSet.ordConnected (h : IsLowerSet s) : s.
OrdConnected
· 使用定理 `IsLowerSet.interior`：∀ {α : Type u_1} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [HasUpperLowerClosure α] {s : Set α},   IsLowerSet s → IsLowerSe
t (interi…
· 使用定理 `LowerSet.lower`：∀ {α : Type u_1} [inst : LE α] (s : LowerSet α), IsLower
Set ↑s
-/
protected theorem Set.OrdConnected.interior (h : s.OrdConnected) : (interior s).OrdConnected := by
  rw [← h.upperClosure_inter_lowerClosure, interior_inter]
  exact
    (upperClosure s).upper.interior.ordConnected.inter (lowerClosure s).lower.interior.ordConnected
