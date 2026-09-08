/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin, Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Group.OrderIso

/-!
# Lattice ordered groups

Lattice ordered groups were introduced by [Birkhoff][birkhoff1942]. They form the algebraic
underpinnings of vector lattices, Banach lattices, AL-space, AM-space etc.

A lattice ordered group is a type `α` satisfying:
* `Lattice α`
* `CommGroup α`
* `MulLeftMono α`
* `MulRightMono α`

This file establishes basic properties of lattice ordered groups. It is shown that when the group is
commutative, the lattice is distributive. This also holds in the non-commutative case
([Birkhoff][birkhoff1942],[Fuchs][fuchs1963]) but we do not yet have the machinery to establish this
in mathlib.

## References

* [Birkhoff, Lattice-ordered Groups][birkhoff1942]
* [Bourbaki, Algebra II][bourbaki1981]
* [Fuchs, Partially Ordered Algebraic Systems][fuchs1963]
* [Zaanen, Lectures on "Riesz Spaces"][zaanen1966]
* [Banasiak, Banach Lattices in Applications][banasiak]

## Tags

lattice, order, group
-/

@[expose] public section

open Function

variable {α : Type*}

section Group
variable [Lattice α] [Group α]

-- Special case of Bourbaki A.VI.9 (1)
@[to_additive]
/-
**mul_sup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_sup [MulLeftMono α] (a b c : α) : c * (a ⊔ b) = c * a ⊔ c * b
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_sup`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup
 α] [inst_1 : SemilatticeSup β] (f : α ≃o β) (x y : α),   f (x ⊔ y) = f x ⊔ f y
-/
lemma mul_sup [MulLeftMono α] (a b c : α) :
    c * (a ⊔ b) = c * a ⊔ c * b :=
  (OrderIso.mulLeft _).map_sup _ _

@[to_additive]
/-
**sup_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sup_mul [MulRightMono α] (a b c : α) : (a ⊔ b) * c = a * c ⊔ b * c
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_sup`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup
 α] [inst_1 : SemilatticeSup β] (f : α ≃o β) (x y : α),   f (x ⊔ y) = f x ⊔ f y
-/
lemma sup_mul [MulRightMono α] (a b c : α) :
    (a ⊔ b) * c = a * c ⊔ b * c :=
  (OrderIso.mulRight _).map_sup _ _

@[to_additive]
/-
**mul_inf** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_inf [MulLeftMono α] (a b c : α) : c * (a ⊓ b) = c * a ⊓ c * b
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_inf`：OrderIso.map_inf [SemilatticeInf α] [SemilatticeInf β]
 (f : α ≃o β) (x y : α) : f (x ⊓ y) = f x ⊓ f y
-/
lemma mul_inf [MulLeftMono α] (a b c : α) :
    c * (a ⊓ b) = c * a ⊓ c * b :=
  (OrderIso.mulLeft _).map_inf _ _

@[to_additive]
/-
**inf_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inf_mul [MulRightMono α] (a b c : α) : (a ⊓ b) * c = a * c ⊓ b * c
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_inf`：OrderIso.map_inf [SemilatticeInf α] [SemilatticeInf β]
 (f : α ≃o β) (x y : α) : f (x ⊓ y) = f x ⊓ f y
-/
lemma inf_mul [MulRightMono α] (a b c : α) :
    (a ⊓ b) * c = a * c ⊓ b * c :=
  (OrderIso.mulRight _).map_inf _ _

@[to_additive]
/-
**sup_div** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sup_div [MulRightMono α] (a b c : α) : (a ⊔ b) / c = a / c ⊔ b / c
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_sup`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup
 α] [inst_1 : SemilatticeSup β] (f : α ≃o β) (x y : α),   f (x ⊔ y) = f x ⊔ f y
-/
lemma sup_div [MulRightMono α] (a b c : α) :
    (a ⊔ b) / c = a / c ⊔ b / c :=
  (OrderIso.divRight _).map_sup _ _

@[to_additive]
/-
**inf_div** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inf_div [MulRightMono α] (a b c : α) : (a ⊓ b) / c = a / c ⊓ b / c
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_inf`：OrderIso.map_inf [SemilatticeInf α] [SemilatticeInf β]
 (f : α ≃o β) (x y : α) : f (x ⊓ y) = f x ⊓ f y
-/
lemma inf_div [MulRightMono α] (a b c : α) :
    (a ⊓ b) / c = a / c ⊓ b / c :=
  (OrderIso.divRight _).map_inf _ _

section
variable [MulLeftMono α] [MulRightMono α]

/-
**inv_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] [MulLeftMono α] [Mu
lRightMono α] (a b : α), (a ⊔ b)⁻¹ = a⁻¹ ⊓ b⁻¹
参数：a b : α；a ⊔ b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_sup`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup
 α] [inst_1 : SemilatticeSup β] (f : α ≃o β) (x y : α),   f (x ⊔ y) = f x ⊔ f y
-/
@[to_additive] lemma inv_sup (a b : α) : (a ⊔ b)⁻¹ = a⁻¹ ⊓ b⁻¹ := (OrderIso.inv α).map_sup _ _
/-
**inv_inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] [MulLeftMono α] [Mu
lRightMono α] (a b : α), (a ⊓ b)⁻¹ = a⁻¹ ⊔ b⁻¹
参数：a b : α；a ⊓ b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_inf`：OrderIso.map_inf [SemilatticeInf α] [SemilatticeInf β]
 (f : α ≃o β) (x y : α) : f (x ⊓ y) = f x ⊓ f y
-/
@[to_additive] lemma inv_inf (a b : α) : (a ⊓ b)⁻¹ = a⁻¹ ⊔ b⁻¹ := (OrderIso.inv α).map_inf _ _

@[to_additive]
/-
**div_sup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：div_sup (a b c : α) : c / (a ⊔ b) = c / a ⊓ c / b
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_sup`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup
 α] [inst_1 : SemilatticeSup β] (f : α ≃o β) (x y : α),   f (x ⊔ y) = f x ⊔ f y
-/
lemma div_sup (a b c : α) : c / (a ⊔ b) = c / a ⊓ c / b := (OrderIso.divLeft c).map_sup _ _

@[to_additive]
/-
**div_inf** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：div_inf (a b c : α) : c / (a ⊓ b) = c / a ⊔ c / b
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_inf`：OrderIso.map_inf [SemilatticeInf α] [SemilatticeInf β]
 (f : α ≃o β) (x y : α) : f (x ⊓ y) = f x ⊓ f y
-/
lemma div_inf (a b c : α) : c / (a ⊓ b) = c / a ⊔ c / b := (OrderIso.divLeft c).map_inf _ _

-- In fact 0 ≤ n•a implies 0 ≤ a, see L. Fuchs, "Partially ordered algebraic systems"
-- Chapter V, 1.E
-- See also `one_le_pow_iff` for the existing version in linear orders
@[to_additive]
/-
**pow_two_semiclosed** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_two_semiclosed {a : α} (ha : 1 <= a ^ 2) : 1 <= a
参数：ha : 1 <= a ^ 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mul_inf`：mul_inf [MulLeftMono α] (a b c : α) : c * (a ⊓ b) = c * a ⊓ c *
 b
· 使用引理 `inf_mul`：inf_mul [MulRightMono α] (a b c : α) : (a ⊓ b) * c = a * c ⊓ b 
* c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `inf_assoc`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a ⊓ b ⊓
 c = a ⊓ (b ⊓ c)
· 使用定理 `inf_left_idem`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ (
a ⊓ b) = a ⊓ b
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `inf_eq_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
= b ↔ b ≤ a
· 使用定理 `mul_eq_left`：mul_eq_left : a * b = a ↔ b = 1
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
-/
lemma pow_two_semiclosed
    {a : α} (ha : 1 ≤ a ^ 2) : 1 ≤ a := by
  suffices this : (a ⊓ 1) * (a ⊓ 1) = a ⊓ 1 by
    rwa [← inf_eq_right, ← mul_eq_left]
  rw [mul_inf, inf_mul, ← pow_two, mul_one, one_mul, inf_assoc, inf_left_idem, inf_comm,
    inf_assoc, inf_of_le_left ha]

end

end Group

variable [Lattice α] [CommGroup α]

-- Fuchs p67
-- Bourbaki A.VI.10 Prop 7
@[to_additive]
/-
**inf_mul_sup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inf_mul_sup [MulLeftMono α] (a b : α) : (a ⊓ b) * (a ⊔ b) = a * b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mul_sup`：mul_sup [MulLeftMono α] (a b c : α) : c * (a ⊔ b) = c * a ⊔ c *
 b
· 使用定理 `mul_inv_cancel_right`：mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a
· 使用引理 `mul_inv_cancel_comm`：mul_inv_cancel_comm (a b : G) : a * b * a⁻¹ = b
· 使用定理 `inv_inf`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Group α] [MulLeft
Mono α] [MulRightMono α] (a b : α), (a ⊓ b)⁻¹ = a⁻¹ ⊔ b⁻¹
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
-/
lemma inf_mul_sup [MulLeftMono α] (a b : α) : (a ⊓ b) * (a ⊔ b) = a * b :=
  calc
    (a ⊓ b) * (a ⊔ b) = (a ⊓ b) * (a * b * (b⁻¹ ⊔ a⁻¹)) := by
      rw [mul_sup b⁻¹ a⁻¹ (a * b), mul_inv_cancel_right, mul_inv_cancel_comm]
    _ = (a ⊓ b) * (a * b * (a ⊓ b)⁻¹) := by rw [inv_inf, sup_comm]
    _ = a * b := by rw [mul_comm, inv_mul_cancel_right]

/-- Every lattice ordered commutative group is a distributive lattice. -/
-- Non-comm case needs cancellation law https://ncatlab.org/nlab/show/distributive+lattice
@[to_additive (attr := instance_reducible)
  /-- Every lattice ordered commutative additive group is a distributive lattice -/]
/-
**CommGroup.toDistribLattice** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：CommGroup.toDistribLattice (α : Type*) [Lattice α] [CommGroup α] [MulLeftM
ono α] : DistribLattice α where le_sup_inf x y z
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def CommGroup.toDistribLattice (α : Type*) [Lattice α] [CommGroup α]
    [MulLeftMono α] : DistribLattice α where
  le_sup_inf x y z := by
    rw [← mul_le_mul_iff_left (x ⊓ (y ⊓ z)), inf_mul_sup x (y ⊓ z), ← inv_mul_le_iff_le_mul,
      le_inf_iff]
    constructor
    · rw [inv_mul_le_iff_le_mul, ← inf_mul_sup x y]
      exact mul_le_mul' (inf_le_inf_left _ inf_le_left) inf_le_left
    · rw [inv_mul_le_iff_le_mul, ← inf_mul_sup x z]
      exact mul_le_mul' (inf_le_inf_left _ inf_le_right) inf_le_right
