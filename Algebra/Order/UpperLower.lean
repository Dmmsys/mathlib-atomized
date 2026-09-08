/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Lattice
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Group.OrderIso
public import Mathlib.Algebra.Order.Monoid.OrderDual
public import Mathlib.Order.UpperLower.Closure

/-!
# Algebraic operations on upper/lower sets

Upper/lower sets are preserved under pointwise algebraic operations in ordered groups.
-/

public section

open Set
open scoped Pointwise

section OrderedCommMonoid

variable {α : Type*} [CommMonoid α] [Preorder α] [IsOrderedMonoid α] {s : Set α} {x : α}

@[to_additive]
/-
**IsUpperSet.smul_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUpperSet.smul_subset (hs : IsUpperSet s) (hx : 1 <= x) : x • s subseteq 
s
参数：hs : IsUpperSet s；hx : 1 <= x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.smul_set_subset_iff`：smul_set_subset_iff : a • s subseteq t ↔ forall
 ⦃b⦄, b in s -> a • b in t
· 使用定理 `le_mul_of_one_le_left'`：le_mul_of_one_le_left' [MulRightMono α] {a b : α
} (h : 1 <= b) : a <= b * a
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem IsUpperSet.smul_subset (hs : IsUpperSet s) (hx : 1 ≤ x) : x • s ⊆ s :=
  smul_set_subset_iff.2 fun _ ↦ hs <| le_mul_of_one_le_left' hx

@[to_additive]
/-
**IsLowerSet.smul_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLowerSet.smul_subset (hs : IsLowerSet s) (hx : x <= 1) : x • s subseteq 
s
参数：hs : IsLowerSet s；hx : x <= 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.smul_set_subset_iff`：smul_set_subset_iff : a • s subseteq t ↔ forall
 ⦃b⦄, b in s -> a • b in t
· 使用定理 `mul_le_of_le_one_left'`：mul_le_of_le_one_left' [MulRightMono α] {a b : α
} (h : b <= 1) : b * a <= a
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem IsLowerSet.smul_subset (hs : IsLowerSet s) (hx : x ≤ 1) : x • s ⊆ s :=
  smul_set_subset_iff.2 fun _ ↦ hs <| mul_le_of_le_one_left' hx

end OrderedCommMonoid

section OrderedCommGroup

variable {α : Type*} [CommGroup α] [Preorder α] [IsOrderedMonoid α] {s t : Set α} {a : α}

@[to_additive]
/-
**IsUpperSet.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUpperSet.smul (hs : IsUpperSet s) : IsUpperSet (a • s)
参数：hs : IsUpperSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUpperSet.image`：IsUpperSet.image (hs : IsUpperSet s) (f : α ≃o β) : Is
UpperSet (f '' s : Set β)
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem IsUpperSet.smul (hs : IsUpperSet s) : IsUpperSet (a • s) := hs.image <| OrderIso.mulLeft _

@[to_additive]
/-
**IsLowerSet.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLowerSet.smul (hs : IsLowerSet s) : IsLowerSet (a • s)
参数：hs : IsLowerSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLowerSet.image`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [i
nst_1 : Preorder β] {s : Set α},   IsLowerSet s → ∀ (f : α ≃o β), IsLowerSet (⇑f
 '' s)
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem IsLowerSet.smul (hs : IsLowerSet s) : IsLowerSet (a • s) := hs.image <| OrderIso.mulLeft _

@[to_additive]
/-
**Set.OrdConnected.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.OrdConnected.smul (hs : s.OrdConnected) : (a • s).OrdConnected
参数：hs : s.OrdConnected。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.OrdConnected.upperClosure_inter_lowerClosure`：Set.OrdConnected.upper
Closure_inter_lowerClosure (h : s.OrdConnected) : ↑(upperClosure s) inter ↑(lowe
rClosure s) = s
· 使用定理 `Set.smul_set_inter`：smul_set_inter : a • (s inter t) = a • s inter a • t
· 使用定理 `Set.OrdConnected.inter`：∀ {α : Type u_1} [inst : Preorder α] {s t : Set 
α}, s.OrdConnected → t.OrdConnected → (s ∩ t).OrdConnected
· 使用定理 `IsUpperSet.ordConnected`：IsUpperSet.ordConnected (h : IsUpperSet s) : s.
OrdConnected
· 使用定理 `IsUpperSet.smul`：IsUpperSet.smul (hs : IsUpperSet s) : IsUpperSet (a • s
)
· 使用定理 `UpperSet.upper`：∀ {α : Type u_1} [inst : LE α] (s : UpperSet α), IsUpper
Set ↑s
· 使用定理 `IsLowerSet.ordConnected`：IsLowerSet.ordConnected (h : IsLowerSet s) : s.
OrdConnected
· 使用定理 `IsLowerSet.smul`：IsLowerSet.smul (hs : IsLowerSet s) : IsLowerSet (a • s
)
· 使用定理 `LowerSet.lower`：∀ {α : Type u_1} [inst : LE α] (s : LowerSet α), IsLower
Set ↑s
-/
theorem Set.OrdConnected.smul (hs : s.OrdConnected) : (a • s).OrdConnected := by
  rw [← hs.upperClosure_inter_lowerClosure, smul_set_inter]
  exact (upperClosure _).upper.smul.ordConnected.inter (lowerClosure _).lower.smul.ordConnected

@[to_additive]
/-
**IsUpperSet.mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUpperSet.mul_left (ht : IsUpperSet t) : IsUpperSet (s * t)
参数：ht : IsUpperSet t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用引理 `Set.iUnion_smul_set`：iUnion_smul_set (s : Set α) (t : Set β) : ⋃ a in s,
 a • t = s • t
· 使用定理 `isUpperSet_iUnion₂`：isUpperSet_iUnion₂ {f : forall i, κ i -> Set α} (hf 
: forall i j, IsUpperSet (f i j)) : IsUpperSet (⋃ (i) (j), f i j)
· 使用定理 `IsUpperSet.smul`：IsUpperSet.smul (hs : IsUpperSet s) : IsUpperSet (a • s
)
-/
theorem IsUpperSet.mul_left (ht : IsUpperSet t) : IsUpperSet (s * t) := by
  rw [← smul_eq_mul, ← Set.iUnion_smul_set]
  exact isUpperSet_iUnion₂ fun x _ ↦ ht.smul

@[to_additive]
/-
**IsUpperSet.mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUpperSet.mul_right (hs : IsUpperSet s) : IsUpperSet (s * t)
参数：hs : IsUpperSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `IsUpperSet.mul_left`：IsUpperSet.mul_left (ht : IsUpperSet t) : IsUpperSe
t (s * t)
-/
theorem IsUpperSet.mul_right (hs : IsUpperSet s) : IsUpperSet (s * t) := by
  rw [mul_comm]
  exact hs.mul_left

@[to_additive]
/-
**IsLowerSet.mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLowerSet.mul_left (ht : IsLowerSet t) : IsLowerSet (s * t)
参数：ht : IsLowerSet t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUpperSet.mul_left`：IsUpperSet.mul_left (ht : IsUpperSet t) : IsUpperSe
t (s * t)
· 使用定理 `IsLowerSet.toDual`：∀ {α : Type u_1} [inst : LE α] {s : Set α}, IsLowerSe
t s → IsUpperSet (⇑OrderDual.ofDual ⁻¹' s)
-/
theorem IsLowerSet.mul_left (ht : IsLowerSet t) : IsLowerSet (s * t) := ht.toDual.mul_left

@[to_additive]
/-
**IsLowerSet.mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLowerSet.mul_right (hs : IsLowerSet s) : IsLowerSet (s * t)
参数：hs : IsLowerSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUpperSet.mul_right`：IsUpperSet.mul_right (hs : IsUpperSet s) : IsUpper
Set (s * t)
· 使用定理 `IsLowerSet.toDual`：∀ {α : Type u_1} [inst : LE α] {s : Set α}, IsLowerSe
t s → IsUpperSet (⇑OrderDual.ofDual ⁻¹' s)
-/
theorem IsLowerSet.mul_right (hs : IsLowerSet s) : IsLowerSet (s * t) := hs.toDual.mul_right

@[to_additive]
/-
**IsUpperSet.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUpperSet.inv {α : Type*} [CommGroup α] [PartialOrder α] [IsOrderedMonoid
 α] {s : Set α} (hs : IsUpperSet s) : IsLowerSet s⁻¹
参数：hs : IsUpperSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inv_le_inv'`：inv_le_inv' : a <= b -> b⁻¹ <= a⁻¹
-/
theorem IsUpperSet.inv {α : Type*} [CommGroup α] [PartialOrder α] [IsOrderedMonoid α]
  {s : Set α} (hs : IsUpperSet s) : IsLowerSet s⁻¹ := fun _ _ h ↦ hs <| inv_le_inv' h

@[to_additive]
/-
**IsLowerSet.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLowerSet.inv {α : Type*} [CommGroup α] [PartialOrder α] [IsOrderedMonoid
 α] {s : Set α} (hs : IsLowerSet s) : IsUpperSet s⁻¹
参数：hs : IsLowerSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inv_le_inv'`：inv_le_inv' : a <= b -> b⁻¹ <= a⁻¹
-/
theorem IsLowerSet.inv {α : Type*} [CommGroup α] [PartialOrder α] [IsOrderedMonoid α]
  {s : Set α} (hs : IsLowerSet s) : IsUpperSet s⁻¹ := fun _ _ h ↦ hs <| inv_le_inv' h

@[to_additive]
/-
**IsUpperSet.div_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUpperSet.div_left {α : Type*} [CommGroup α] [PartialOrder α] [IsOrderedM
onoid α] {s t : Set α} (ht : IsUpperSet t) : IsLowerSet (s / t)
参数：ht : IsUpperSet t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `IsLowerSet.mul_left`：IsLowerSet.mul_left (ht : IsLowerSet t) : IsLowerSe
t (s * t)
· 使用定理 `IsUpperSet.inv`：IsUpperSet.inv {α : Type*} [CommGroup α] [PartialOrder α
] [IsOrderedMonoid α] {s : Set α} (hs : IsUpperSet s) : IsLowerSet s⁻¹
-/
theorem IsUpperSet.div_left {α : Type*} [CommGroup α] [PartialOrder α] [IsOrderedMonoid α]
    {s t : Set α} (ht : IsUpperSet t) : IsLowerSet (s / t) := by
  rw [div_eq_mul_inv]
  exact ht.inv.mul_left

@[to_additive]
/-
**IsUpperSet.div_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUpperSet.div_right (hs : IsUpperSet s) : IsUpperSet (s / t)
参数：hs : IsUpperSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `IsUpperSet.mul_right`：IsUpperSet.mul_right (hs : IsUpperSet s) : IsUpper
Set (s * t)
-/
theorem IsUpperSet.div_right (hs : IsUpperSet s) : IsUpperSet (s / t) := by
  rw [div_eq_mul_inv]
  exact hs.mul_right

@[to_additive]
/-
**IsLowerSet.div_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLowerSet.div_left {α : Type*} [CommGroup α] [PartialOrder α] [IsOrderedM
onoid α] {s t : Set α} (ht : IsLowerSet t) : IsUpperSet (s / t)
参数：ht : IsLowerSet t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUpperSet.div_left`：IsUpperSet.div_left {α : Type*} [CommGroup α] [Part
ialOrder α] [IsOrderedMonoid α] {s t : Set α} (ht : IsUpperSet t) : IsLowerSet (
s / t)
· 使用定理 `IsLowerSet.toDual`：∀ {α : Type u_1} [inst : LE α] {s : Set α}, IsLowerSe
t s → IsUpperSet (⇑OrderDual.ofDual ⁻¹' s)
-/
theorem IsLowerSet.div_left {α : Type*} [CommGroup α] [PartialOrder α] [IsOrderedMonoid α]
  {s t : Set α} (ht : IsLowerSet t) : IsUpperSet (s / t) := ht.toDual.div_left

@[to_additive]
/-
**IsLowerSet.div_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLowerSet.div_right (hs : IsLowerSet s) : IsLowerSet (s / t)
参数：hs : IsLowerSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUpperSet.div_right`：IsUpperSet.div_right (hs : IsUpperSet s) : IsUpper
Set (s / t)
· 使用定理 `IsLowerSet.toDual`：∀ {α : Type u_1} [inst : LE α] {s : Set α}, IsLowerSe
t s → IsUpperSet (⇑OrderDual.ofDual ⁻¹' s)
-/
theorem IsLowerSet.div_right (hs : IsLowerSet s) : IsLowerSet (s / t) := hs.toDual.div_right

namespace UpperSet

@[to_additive]
/-
**UpperSet.** 是 Mathlib 中的一个实例，位于命名空间 `UpperSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (UpperSet α) :=
  ⟨Ici 1⟩

@[to_additive]
/-
**UpperSet.** 是 Mathlib 中的一个实例，位于命名空间 `UpperSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul (UpperSet α) :=
  ⟨fun s t ↦ ⟨image2 (· * ·) s t, s.2.mul_right⟩⟩

@[to_additive]
/-
**UpperSet.** 是 Mathlib 中的一个实例，位于命名空间 `UpperSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Div (UpperSet α) :=
  ⟨fun s t ↦ ⟨image2 (· / ·) s t, s.2.div_right⟩⟩

@[to_additive]
/-
**UpperSet.** 是 Mathlib 中的一个实例，位于命名空间 `UpperSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul α (UpperSet α) :=
  ⟨fun a s ↦ ⟨(a • ·) '' s, s.2.smul⟩⟩

omit [IsOrderedMonoid α] in
@[to_additive (attr := simp, norm_cast)]
/-
**UpperSet.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：coe_one : ((1 : UpperSet α) : Set α) = Set.Ici 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one : ((1 : UpperSet α) : Set α) = Set.Ici 1 :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/-
**UpperSet.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：coe_mul (s t : UpperSet α) : (↑(s * t) : Set α) = s * t
参数：s t : UpperSet α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul (s t : UpperSet α) : (↑(s * t) : Set α) = s * t :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/-
**UpperSet.coe_div** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：coe_div (s t : UpperSet α) : (↑(s / t) : Set α) = s / t
参数：s t : UpperSet α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_div (s t : UpperSet α) : (↑(s / t) : Set α) = s / t :=
  rfl

omit [IsOrderedMonoid α] in
@[to_additive (attr := simp)]
/-
**UpperSet.Ici_one** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：Ici_one : Ici (1 : α) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ici_one : Ici (1 : α) = 1 :=
  rfl

@[to_additive]
/-
**UpperSet.** 是 Mathlib 中的一个实例，位于命名空间 `UpperSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulAction α (UpperSet α) :=
  SetLike.coe_injective.mulAction _ (fun _ _ => rfl)

@[to_additive]
/-
**UpperSet.commSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `UpperSet`。
形式化陈述：commSemigroup : CommSemigroup (UpperSet α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperSet.coe_mul`：coe_mul (s t : UpperSet α) : (↑(s * t) : Set α) = s * 
t
-/
instance commSemigroup : CommSemigroup (UpperSet α) :=
  { (SetLike.coe_injective.commSemigroup _ coe_mul : CommSemigroup (UpperSet α)) with }

@[to_additive]
/-
**UpperSet.one_mul** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem one_mul (s : UpperSet α) : 1 * s = s :=
  SetLike.coe_injective <|
    (subset_mul_right _ self_mem_Ici).antisymm' <| by
      rw [← smul_eq_mul, ← Set.iUnion_smul_set]
      exact Set.iUnion₂_subset fun _ ↦ s.upper.smul_subset

@[to_additive]
/-
**UpperSet.** 是 Mathlib 中的一个实例，位于命名空间 `UpperSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommMonoid (UpperSet α) :=
  { UpperSet.commSemigroup with
    one_mul := private one_mul
    mul_one := fun s ↦ by
      rw [mul_comm]
      exact one_mul _ }

end UpperSet

namespace LowerSet

@[to_additive]
/-
**LowerSet.** 是 Mathlib 中的一个实例，位于命名空间 `LowerSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (LowerSet α) :=
  ⟨Iic 1⟩

@[to_additive]
/-
**LowerSet.** 是 Mathlib 中的一个实例，位于命名空间 `LowerSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul (LowerSet α) :=
  ⟨fun s t ↦ ⟨image2 (· * ·) s t, s.2.mul_right⟩⟩

@[to_additive]
/-
**LowerSet.** 是 Mathlib 中的一个实例，位于命名空间 `LowerSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Div (LowerSet α) :=
  ⟨fun s t ↦ ⟨image2 (· / ·) s t, s.2.div_right⟩⟩

@[to_additive]
/-
**LowerSet.** 是 Mathlib 中的一个实例，位于命名空间 `LowerSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul α (LowerSet α) :=
  ⟨fun a s ↦ ⟨(a • ·) '' s, s.2.smul⟩⟩

@[to_additive (attr := simp, norm_cast)]
/-
**LowerSet.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `LowerSet`。
形式化陈述：coe_mul (s t : LowerSet α) : (↑(s * t) : Set α) = s * t
参数：s t : LowerSet α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul (s t : LowerSet α) : (↑(s * t) : Set α) = s * t :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/-
**LowerSet.coe_div** 是 Mathlib 中的一个定理，位于命名空间 `LowerSet`。
形式化陈述：coe_div (s t : LowerSet α) : (↑(s / t) : Set α) = s / t
参数：s t : LowerSet α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_div (s t : LowerSet α) : (↑(s / t) : Set α) = s / t :=
  rfl

omit [IsOrderedMonoid α] in
@[to_additive (attr := simp)]
/-
**LowerSet.Iic_one** 是 Mathlib 中的一个定理，位于命名空间 `LowerSet`。
形式化陈述：Iic_one : Iic (1 : α) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Iic_one : Iic (1 : α) = 1 :=
  rfl

@[to_additive]
/-
**LowerSet.** 是 Mathlib 中的一个实例，位于命名空间 `LowerSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulAction α (LowerSet α) :=
  SetLike.coe_injective.mulAction _ (fun _ _ => rfl)

@[to_additive]
/-
**LowerSet.commSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `LowerSet`。
形式化陈述：commSemigroup : CommSemigroup (LowerSet α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSet.coe_mul`：coe_mul (s t : LowerSet α) : (↑(s * t) : Set α) = s * 
t
-/
instance commSemigroup : CommSemigroup (LowerSet α) :=
  { (SetLike.coe_injective.commSemigroup _ coe_mul : CommSemigroup (LowerSet α)) with }

@[to_additive]
/-
**LowerSet.one_mul** 是 Mathlib 中的一个定理，位于命名空间 `LowerSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem one_mul (s : LowerSet α) : 1 * s = s :=
  SetLike.coe_injective <|
    (subset_mul_right _ self_mem_Iic).antisymm' <| by
      rw [← smul_eq_mul, ← Set.iUnion_smul_set]
      exact Set.iUnion₂_subset fun _ ↦ s.lower.smul_subset

@[to_additive]
/-
**LowerSet.** 是 Mathlib 中的一个实例，位于命名空间 `LowerSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommMonoid (LowerSet α) :=
  { LowerSet.commSemigroup with
    one_mul := private one_mul
    mul_one := fun s ↦ by
      rw [mul_comm]
      exact one_mul _ }

end LowerSet

variable (a s t)

omit [IsOrderedMonoid α] in
@[to_additive (attr := simp)]
/-
**upperClosure_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperClosure_one : upperClosure (1 : Set α) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `upperClosure_singleton`：upperClosure_singleton (a : α) : upperClosure ({
a} : Set α) = UpperSet.Ici a
-/
theorem upperClosure_one : upperClosure (1 : Set α) = 1 :=
  upperClosure_singleton _

omit [IsOrderedMonoid α] in
@[to_additive (attr := simp)]
/-
**lowerClosure_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerClosure_one : lowerClosure (1 : Set α) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lowerClosure_singleton`：∀ {α : Type u_1} [inst : Preorder α] (a : α), lo
werClosure {a} = LowerSet.Iic a
-/
theorem lowerClosure_one : lowerClosure (1 : Set α) = 1 :=
  lowerClosure_singleton _

@[to_additive (attr := simp)]
/-
**upperClosure_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperClosure_smul : upperClosure (a • s) = a • upperClosure s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `upperClosure_image`：upperClosure_image (f : α ≃o β) : upperClosure (f ''
 s) = UpperSet.map f (upperClosure s)
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem upperClosure_smul : upperClosure (a • s) = a • upperClosure s :=
  upperClosure_image <| OrderIso.mulLeft a

@[to_additive (attr := simp)]
/-
**lowerClosure_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerClosure_smul : lowerClosure (a • s) = a • lowerClosure s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lowerClosure_image`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] 
[inst_1 : Preorder β] {s : Set α} (f : α ≃o β),   lowerClosure (⇑f '' s) = (Lowe
rSet.map…
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem lowerClosure_smul : lowerClosure (a • s) = a • lowerClosure s :=
  lowerClosure_image <| OrderIso.mulLeft a

@[to_additive]
/-
**mul_upperClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_upperClosure : s * upperClosure t = upperClosure (s * t)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `upperClosure_iUnion`：upperClosure_iUnion (f : ι -> Set α) : upperClosure
 (⋃ i, f i) = ⨅ i, upperClosure (f i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `upperClosure_smul`：upperClosure_smul : upperClosure (a • s) = a • upperC
losure s
· 使用定理 `UpperSet.coe_iInf₂`：coe_iInf₂ (f : forall i, κ i -> UpperSet α) : (↑(⨅ (
i) (j), f i j) : Set α) = ⋃ (i) (j), f i j
-/
theorem mul_upperClosure : s * upperClosure t = upperClosure (s * t) := by
  simp_rw [← smul_eq_mul, ← Set.iUnion_smul_set, upperClosure_iUnion, upperClosure_smul,
    UpperSet.coe_iInf₂]
  rfl

@[to_additive]
/-
**mul_lowerClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_lowerClosure : s * lowerClosure t = lowerClosure (s * t)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `lowerClosure_iUnion`：lowerClosure_iUnion (f : ι -> Set α) : lowerClosure
 (⋃ i, f i) = ⨆ i, lowerClosure (f i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `lowerClosure_smul`：lowerClosure_smul : lowerClosure (a • s) = a • lowerC
losure s
· 使用定理 `LowerSet.coe_iSup₂`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_5} [
inst : LE α] (f : (i : ι) → κ i → LowerSet α),   ↑(⨆ i, ⨆ j, f i j) = ⋃ i, ⋃ j, 
↑(f i j)
-/
theorem mul_lowerClosure : s * lowerClosure t = lowerClosure (s * t) := by
  simp_rw [← smul_eq_mul, ← Set.iUnion_smul_set, lowerClosure_iUnion, lowerClosure_smul,
    LowerSet.coe_iSup₂]
  rfl

@[to_additive]
/-
**upperClosure_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperClosure_mul : ↑(upperClosure s) * t = upperClosure (s * t)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_upperClosure`：mul_upperClosure : s * upperClosure t = upperClosure (
s * t)
-/
theorem upperClosure_mul : ↑(upperClosure s) * t = upperClosure (s * t) := by
  simp_rw [mul_comm _ t]
  exact mul_upperClosure _ _

@[to_additive]
/-
**lowerClosure_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerClosure_mul : ↑(lowerClosure s) * t = lowerClosure (s * t)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_lowerClosure`：mul_lowerClosure : s * lowerClosure t = lowerClosure (
s * t)
-/
theorem lowerClosure_mul : ↑(lowerClosure s) * t = lowerClosure (s * t) := by
  simp_rw [mul_comm _ t]
  exact mul_lowerClosure _ _

@[to_additive (attr := simp)]
/-
**upperClosure_mul_distrib** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperClosure_mul_distrib : upperClosure (s * t) = upperClosure s * upperCl
osure t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UpperSet.coe_mul`：coe_mul (s t : UpperSet α) : (↑(s * t) : Set α) = s * 
t
· 使用定理 `mul_upperClosure`：mul_upperClosure : s * upperClosure t = upperClosure (
s * t)
· 使用定理 `upperClosure_mul`：upperClosure_mul : ↑(upperClosure s) * t = upperClosur
e (s * t)
· 使用定理 `UpperSet.upperClosure`：∀ {α : Type u_1} [inst : Preorder α] (s : UpperSe
t α), upperClosure ↑s = s
-/
theorem upperClosure_mul_distrib : upperClosure (s * t) = upperClosure s * upperClosure t :=
  SetLike.coe_injective <| by
    rw [UpperSet.coe_mul, mul_upperClosure, upperClosure_mul, UpperSet.upperClosure]

@[to_additive (attr := simp)]
/-
**lowerClosure_mul_distrib** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerClosure_mul_distrib : lowerClosure (s * t) = lowerClosure s * lowerCl
osure t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LowerSet.coe_mul`：coe_mul (s t : LowerSet α) : (↑(s * t) : Set α) = s * 
t
· 使用定理 `mul_lowerClosure`：mul_lowerClosure : s * lowerClosure t = lowerClosure (
s * t)
· 使用定理 `lowerClosure_mul`：lowerClosure_mul : ↑(lowerClosure s) * t = lowerClosur
e (s * t)
· 使用定理 `LowerSet.lowerClosure`：∀ {α : Type u_1} [inst : Preorder α] (s : LowerSe
t α), lowerClosure ↑s = s
-/
theorem lowerClosure_mul_distrib : lowerClosure (s * t) = lowerClosure s * lowerClosure t :=
  SetLike.coe_injective <| by
    rw [LowerSet.coe_mul, mul_lowerClosure, lowerClosure_mul, LowerSet.lowerClosure]

end OrderedCommGroup

