/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Order.Hom.Basic

/-!
# Ordered monoids

This file develops some additional material on ordered monoids.
-/

@[expose] public section


open Function

universe u

variable {α : Type u} {β : Type*} [CommMonoid α] [Preorder α]

/-- Pullback an `IsOrderedMonoid` under an injective map. -/
@[to_additive /-- Pullback an `IsOrderedAddMonoid` under an injective map. -/]
/-
**Function.Injective.isOrderedMonoid** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Function.Injective.isOrderedMonoid [IsOrderedMonoid α] [CommMonoid β] [Pre
order β] (f : β -> α) (mul : forall x y, f (x * y) = f x * f y) (le : forall {x 
y}, f x <= f y ↔ x <= y) : IsOrderedMonoid β where mul_le_mul_left a b ab c
参数：f : β -> α；mul : forall x y, f (x * y) = f x * f y；le : forall {x y}, f x <= 
f y ↔ x <= y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
Pullback an `IsOrderedMonoid` under an injective map.
-/
lemma Function.Injective.isOrderedMonoid [IsOrderedMonoid α] [CommMonoid β]
    [Preorder β] (f : β → α) (mul : ∀ x y, f (x * y) = f x * f y)
    (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) :
    IsOrderedMonoid β where
  mul_le_mul_left a b ab c := le.1 <| by rw [mul, mul]; grw [le.2 ab]

/-- Pullback an `IsOrderedMonoid` under a strictly monotone map. -/
@[to_additive /-- Pullback an `IsOrderedAddMonoid` under a strictly monotone map. -/]
/-
**StrictMono.isOrderedMonoid** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictMono.isOrderedMonoid [IsOrderedMonoid α] [CommMonoid β] [LinearOrder
 β] (f : β -> α) (hf : StrictMono f) (mul : forall x y, f (x * y) = f x * f y) :
 IsOrderedMonoid β
参数：f : β -> α；hf : StrictMono f；mul : forall x y, f (x * y) = f x * f y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.Injective.isOrderedMonoid`：Function.Injective.isOrderedMonoid [
IsOrderedMonoid α] [CommMonoid β] [Preorder β] (f : β -> α) (mul : forall x y, f
 (x * y) = f x * f y) (l…
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b

--- 原说明 ---
Pullback an `IsOrderedMonoid` under a strictly monotone map.
-/
lemma StrictMono.isOrderedMonoid [IsOrderedMonoid α] [CommMonoid β] [LinearOrder β]
    (f : β → α) (hf : StrictMono f) (mul : ∀ x y, f (x * y) = f x * f y) :
    IsOrderedMonoid β :=
  Function.Injective.isOrderedMonoid f mul hf.le_iff_le

/-- Pullback an `IsOrderedCancelMonoid` under an injective map. -/
@[to_additive Function.Injective.isOrderedCancelAddMonoid
    /-- Pullback an `IsOrderedCancelAddMonoid` under an injective map. -/]
/-
**Function.Injective.isOrderedCancelMonoid** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Function.Injective.isOrderedCancelMonoid [IsOrderedCancelMonoid α] [CommMo
noid β] [Preorder β] (f : β -> α) (mul : forall x y, f (x * y) = f x * f y) (le 
: forall {x y}, f x <= f y ↔ x <= y) : IsOrderedCancelMonoid β where __
参数：f : β -> α；mul : forall x y, f (x * y) = f x * f y；le : forall {x y}, f x <= 
f y ↔ x <= y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.Injective.isOrderedMonoid`：Function.Injective.isOrderedMonoid [
IsOrderedMonoid α] [CommMonoid β] [Preorder β] (f : β -> α) (mul : forall x y, f
 (x * y) = f x * f y) (l…
· 使用定理 `IsOrderedCancelMonoid.toIsOrderedMonoid`：∀ {α : Type u_2} {inst : CommMo
noid α} {inst_1 : Preorder α} [self : IsOrderedCancelMonoid α], IsOrderedMonoid 
α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_le_mul_iff_left`：mul_le_mul_iff_left [MulLeftMono α] [MulLeftReflect
LE α] (a : α) {b c : α} : a * b <= a * c ↔ b <= c
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `IsOrderedCancelMonoid.toMulLeftReflectLE`：∀ {α : Type u_2} [inst : CommM
onoid α] [inst_1 : Preorder α] [IsOrderedCancelMonoid α], MulLeftReflectLE α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma Function.Injective.isOrderedCancelMonoid [IsOrderedCancelMonoid α] [CommMonoid β]
    [Preorder β]
    (f : β → α) (mul : ∀ x y, f (x * y) = f x * f y)
    (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) :
    IsOrderedCancelMonoid β where
  __ := Function.Injective.isOrderedMonoid f mul le
  le_of_mul_le_mul_left a b c bc := le.1 <|
      (mul_le_mul_iff_left (f a)).1 (by rwa [← mul, ← mul, le])

/-- Pullback an `IsOrderedCancelMonoid` under a strictly monotone map. -/
@[to_additive /-- Pullback an `IsOrderedAddCancelMonoid` under a strictly monotone map. -/]
/-
**StrictMono.isOrderedCancelMonoid** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictMono.isOrderedCancelMonoid [IsOrderedCancelMonoid α] [CommMonoid β] 
[LinearOrder β] (f : β -> α) (hf : StrictMono f) (mul : forall x y, f (x * y) = 
f x * f y) : IsOrderedCancelMonoid β where __
参数：f : β -> α；hf : StrictMono f；mul : forall x y, f (x * y) = f x * f y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictMono.isOrderedMonoid`：StrictMono.isOrderedMonoid [IsOrderedMonoid 
α] [CommMonoid β] [LinearOrder β] (f : β -> α) (hf : StrictMono f) (mul : forall
 x y, f (x * y) …
· 使用定理 `IsOrderedCancelMonoid.toIsOrderedMonoid`：∀ {α : Type u_2} {inst : CommMo
noid α} {inst_1 : Preorder α} [self : IsOrderedCancelMonoid α], IsOrderedMonoid 
α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `IsOrderedCancelMonoid.toMulLeftReflectLE`：∀ {α : Type u_2} [inst : CommM
onoid α] [inst_1 : Preorder α] [IsOrderedCancelMonoid α], MulLeftReflectLE α

--- 原说明 ---
Pullback an `IsOrderedCancelMonoid` under a strictly monotone map.
-/
lemma StrictMono.isOrderedCancelMonoid [IsOrderedCancelMonoid α] [CommMonoid β] [LinearOrder β]
    (f : β → α) (hf : StrictMono f) (mul : ∀ x y, f (x * y) = f x * f y) :
    IsOrderedCancelMonoid β where
  __ := hf.isOrderedMonoid f mul
  le_of_mul_le_mul_left a b c h := by simpa [← hf.le_iff_le, mul] using h

-- TODO find a better home for the next two constructions.
/-- The order embedding sending `b` to `a * b`, for some fixed `a`.
See also `OrderIso.mulLeft` when working in an ordered group. -/
@[to_additive (attr := simps!)
      /-- The order embedding sending `b` to `a + b`, for some fixed `a`.
       See also `OrderIso.addLeft` when working in an additive ordered group. -/]
/-
**OrderEmbedding.mulLeft** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OrderEmbedding.mulLeft {α : Type*} [Mul α] [LinearOrder α] [MulLeftStrictM
ono α] (m : α) : α ↪o α
参数：m : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def OrderEmbedding.mulLeft {α : Type*} [Mul α] [LinearOrder α]
    [MulLeftStrictMono α] (m : α) : α ↪o α :=
  OrderEmbedding.ofStrictMono (fun n => m * n) mul_right_strictMono

/-- The order embedding sending `b` to `b * a`, for some fixed `a`.
See also `OrderIso.mulRight` when working in an ordered group. -/
@[to_additive (attr := simps!)
      /-- The order embedding sending `b` to `b + a`, for some fixed `a`.
       See also `OrderIso.addRight` when working in an additive ordered group. -/]
/-
**OrderEmbedding.mulRight** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OrderEmbedding.mulRight {α : Type*} [Mul α] [LinearOrder α] [MulRightStric
tMono α] (m : α) : α ↪o α
参数：m : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def OrderEmbedding.mulRight {α : Type*} [Mul α] [LinearOrder α]
    [MulRightStrictMono α] (m : α) : α ↪o α :=
  OrderEmbedding.ofStrictMono (fun n => n * m) mul_left_strictMono
