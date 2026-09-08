/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs

/-! # Bundled ordered monoid structures on `Multiplicative α` and `Additive α`. -/

public section

variable {α : Type*}

/-
**Multiplicative.isOrderedMonoid** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Multiplicative.isOrderedMonoid [AddCommMonoid α] [Preorder α] [IsOrderedAd
dMonoid α] : IsOrderedMonoid (Multiplicative α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedAddMonoid.add_le_add_left`：∀ {α : Type u_2} {inst : AddCommMono
id α} {inst_1 : Preorder α} [self : IsOrderedAddMonoid α] (a b : α),   a ≤ b → ∀
 (c : α), a + c ≤ b + c
-/
instance Multiplicative.isOrderedMonoid [AddCommMonoid α] [Preorder α] [IsOrderedAddMonoid α] :
    IsOrderedMonoid (Multiplicative α) :=
  { mul_le_mul_left := @IsOrderedAddMonoid.add_le_add_left α _ _ _ }
/-
**Additive.isOrderedAddMonoid** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Additive.isOrderedAddMonoid [CommMonoid α] [Preorder α] [IsOrderedMonoid α
] : IsOrderedAddMonoid (Additive α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedMonoid.mul_le_mul_left`：∀ {α : Type u_2} {inst : CommMonoid α} 
{inst_1 : Preorder α} [self : IsOrderedMonoid α] (a b : α),   a ≤ b → ∀ (c : α),
 a * c ≤ b * c
-/
instance Additive.isOrderedAddMonoid [CommMonoid α] [Preorder α] [IsOrderedMonoid α] :
    IsOrderedAddMonoid (Additive α) :=
  { add_le_add_left := @IsOrderedMonoid.mul_le_mul_left α _ _ _ }
/-
**Multiplicative.isOrderedCancelMonoid** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Multiplicative.isOrderedCancelMonoid [AddCommMonoid α] [Preorder α] [IsOrd
eredCancelAddMonoid α] : IsOrderedCancelMonoid (Multiplicative α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `IsOrderedCancelAddMonoid.le_of_add_le_add_left`：∀ {α : Type u_2} {inst :
 AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α] (a b
 c : α),   a + b ≤ a + c → b ≤ c
-/
instance Multiplicative.isOrderedCancelMonoid
    [AddCommMonoid α] [Preorder α] [IsOrderedCancelAddMonoid α] :
    IsOrderedCancelMonoid (Multiplicative α) :=
  { le_of_mul_le_mul_left := @IsOrderedCancelAddMonoid.le_of_add_le_add_left α _ _ _ }
/-
**Additive.isOrderedCancelAddMonoid** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Additive.isOrderedCancelAddMonoid [CommMonoid α] [Preorder α] [IsOrderedCa
ncelMonoid α] : IsOrderedCancelAddMonoid (Additive α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedCancelMonoid.toIsOrderedMonoid`：∀ {α : Type u_2} {inst : CommMo
noid α} {inst_1 : Preorder α} [self : IsOrderedCancelMonoid α], IsOrderedMonoid 
α
· 使用定理 `IsOrderedCancelMonoid.le_of_mul_le_mul_left`：∀ {α : Type u_2} {inst : Co
mmMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelMonoid α] (a b c : α), 
  a * b ≤ a * c → b ≤ c
-/
instance Additive.isOrderedCancelAddMonoid
    [CommMonoid α] [Preorder α] [IsOrderedCancelMonoid α] :
    IsOrderedCancelAddMonoid (Additive α) :=
  { le_of_add_le_add_left := @IsOrderedCancelMonoid.le_of_mul_le_mul_left α _ _ _ }
/-
**Multiplicative.canonicallyOrderedMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Multiplicative.canonicallyOrderedMul [AddMonoid α] [Preorder α] [Canonical
lyOrderedAdd α] : CanonicallyOrderedMul (Multiplicative α) where le_mul_self _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `le_add_self`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ b + a
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b
-/
instance Multiplicative.canonicallyOrderedMul
    [AddMonoid α] [Preorder α] [CanonicallyOrderedAdd α] :
    CanonicallyOrderedMul (Multiplicative α) where
  le_mul_self _ _ := le_add_self (α := α)
  le_self_mul _ _ := le_self_add (α := α)
/-
**Additive.canonicallyOrderedAdd** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Additive.canonicallyOrderedAdd [Monoid α] [Preorder α] [CanonicallyOrdered
Mul α] : CanonicallyOrderedAdd (Additive α) where le_add_self _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CanonicallyOrderedMul.toExistsMulOfLE`：∀ {α : Type u_1} {inst : Mul α} {
inst_1 : LE α} [self : CanonicallyOrderedMul α], ExistsMulOfLE α
· 使用定理 `le_mul_self`：le_mul_self : a <= b * a
· 使用定理 `le_self_mul`：le_self_mul : a <= a * b
-/
instance Additive.canonicallyOrderedAdd
    [Monoid α] [Preorder α] [CanonicallyOrderedMul α] :
    CanonicallyOrderedAdd (Additive α) where
  le_add_self _ _ := le_mul_self (α := α)
  le_self_add _ _ := le_self_mul (α := α)
