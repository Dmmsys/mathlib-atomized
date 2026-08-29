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
/--
lemma `Function.Injective.isOrderedMonoid` / 引理 `Function.Injective.isOrderedMonoid`

English:
lemma Function.Injective.isOrderedMonoid
  statement: [IsOrderedMonoid α] [CommMonoid β]
  proof: le.1 by rw [mul, mul]; grw [le.2 ab]

中文:
引理 函数.单射.isOrderedMonoid
  结论: [是Ordered幺半群 α] [交换幺半群 β]
  证明: le.1 by rw [mul, mul]; grw [le.2 ab]
-/
lemma Function.Injective.isOrderedMonoid [IsOrderedMonoid α] [CommMonoid β]
    [Preorder β] (f : β -> α) (mul : forall x y, f (x * y) = f x * f y)
    (le : forall {x y}, f x <= f y ↔ x <= y) :
    IsOrderedMonoid β where
mul_le_mul_left a b ab c := le.1 by rw [mul, mul]; grw [le.2 ab]

/-- Pullback an `IsOrderedMonoid` under a strictly monotone map. -/
@[to_additive /-- Pullback an `IsOrderedAddMonoid` under a strictly monotone map. -/]
/--
lemma `StrictMono.isOrderedMonoid` / 引理 `StrictMono.isOrderedMonoid`

English:
lemma StrictMono.isOrderedMonoid
  statement: [IsOrderedMonoid α] [CommMonoid β] [LinearOrder β]
  proof: Function.Injective.isOrderedMonoid f mul hf.le_iff_le

中文:
引理 严格递增.isOrderedMonoid
  结论: [是Ordered幺半群 α] [交换幺半群 β] [线性序 β]
  证明: Function.Injective.isOrderedMonoid f mul hf.le_iff_le

Depends on / 依赖: Function, Function.Injective.isOrderedMonoid, Injective, hf.le_iff_le, isOrderedMonoid, le_iff_le
-/
lemma StrictMono.isOrderedMonoid [IsOrderedMonoid α] [CommMonoid β] [LinearOrder β]
    (f : β -> α) (hf : StrictMono f) (mul : forall x y, f (x * y) = f x * f y) :
    IsOrderedMonoid β :=
  Function.Injective.isOrderedMonoid f mul hf.le_iff_le

/-- Pullback an `IsOrderedCancelMonoid` under an injective map. -/
@[to_additive Function.Injective.isOrderedCancelAddMonoid
    /-- Pullback an `IsOrderedCancelAddMonoid` under an injective map. -/]
/--
lemma `Function.Injective.isOrderedCancelMonoid` / 引理 `Function.Injective.isOrderedCancelMonoid`

English:
lemma Function.Injective.isOrderedCancelMonoid
  statement: [IsOrderedCancelMonoid α] [CommMonoid β]
  proof: Function.Injective.isOrderedMonoid f mul le
le_of_mul_le_mul_left a b c bc := le.1
      (mul_le_mul_iff_left (f a)).1 (by rwa [← mul, ← mul, le])

中文:
引理 函数.单射.isOrderedCancelMonoid
  结论: [是OrderedCancel幺半群 α] [交换幺半群 β]
  证明: Function.Injective.isOrderedMonoid f mul le
le_of_mul_le_mul_left a b c bc := le.1
      (mul_le_mul_iff_left (f a)).1 (by rwa [← mul, ← mul, le])

Depends on / 依赖: Function, Function.Injective.isOrderedMonoid, Injective, isOrderedMonoid
-/
lemma Function.Injective.isOrderedCancelMonoid [IsOrderedCancelMonoid α] [CommMonoid β]
    [Preorder β]
    (f : β -> α) (mul : forall x y, f (x * y) = f x * f y)
    (le : forall {x y}, f x <= f y ↔ x <= y) :
    IsOrderedCancelMonoid β where
  __ := Function.Injective.isOrderedMonoid f mul le
le_of_mul_le_mul_left a b c bc := le.1
      (mul_le_mul_iff_left (f a)).1 (by rwa [← mul, ← mul, le])

/-- Pullback an `IsOrderedCancelMonoid` under a strictly monotone map. -/
@[to_additive /-- Pullback an `IsOrderedAddCancelMonoid` under a strictly monotone map. -/]
/--
lemma `StrictMono.isOrderedCancelMonoid` / 引理 `StrictMono.isOrderedCancelMonoid`

English:
lemma StrictMono.isOrderedCancelMonoid
  statement: [IsOrderedCancelMonoid α] [CommMonoid β] [LinearOrder β]
  proof: hf.isOrderedMonoid f mul
  le_of_mul_le_mul_left a b c h := by simpa [← hf.le_iff_le, mul] using h

中文:
引理 严格递增.isOrderedCancelMonoid
  结论: [是OrderedCancel幺半群 α] [交换幺半群 β] [线性序 β]
  证明: hf.isOrderedMonoid f mul
  le_of_mul_le_mul_left a b c h := by simpa [← hf.le_iff_le, mul] using h

Depends on / 依赖: hf.isOrderedMonoid, isOrderedMonoid
-/
lemma StrictMono.isOrderedCancelMonoid [IsOrderedCancelMonoid α] [CommMonoid β] [LinearOrder β]
    (f : β -> α) (hf : StrictMono f) (mul : forall x y, f (x * y) = f x * f y) :
    IsOrderedCancelMonoid β where
  __ := hf.isOrderedMonoid f mul
  le_of_mul_le_mul_left a b c h := by simpa [← hf.le_iff_le, mul] using h

-- TODO find a better home for the next two constructions.
/-- The order embedding sending `b` to `a * b`, for some fixed `a`.
See also `OrderIso.mulLeft` when working in an ordered group. -/
@[to_additive (attr := simps!)
      /-- The order embedding sending `b` to `a + b`, for some fixed `a`.
       See also `OrderIso.addLeft` when working in an additive ordered group. -/]
/--
Definition of `OrderEmbedding.mulLeft` / `OrderEmbedding.mulLeft` 的定义

English:
definition OrderEmbedding.mulLeft
  signature: {α : Type*} [Mul α] [LinearOrder α]
  body: OrderEmbedding.ofStrictMono (fun n => m * n) mul_right_strictMono

中文:
定义 OrderEmbedding.mulLeft
  签名: {α : 类型} [乘法 α] [线性序 α]
  定义体: OrderEmbedding.ofStrictMono (fun n => m * n) mul_right_strictMono

Depends on / 依赖: OrderEmbedding, OrderEmbedding.ofStrictMono, mul_right_strictMono, ofStrictMono
-/
def OrderEmbedding.mulLeft {α : Type*} [Mul α] [LinearOrder α]
    [MulLeftStrictMono α] (m : α) : α ↪o α :=
  OrderEmbedding.ofStrictMono (fun n => m * n) mul_right_strictMono

/-- The order embedding sending `b` to `b * a`, for some fixed `a`.
See also `OrderIso.mulRight` when working in an ordered group. -/
@[to_additive (attr := simps!)
      /-- The order embedding sending `b` to `b + a`, for some fixed `a`.
       See also `OrderIso.addRight` when working in an additive ordered group. -/]
/--
Definition of `OrderEmbedding.mulRight` / `OrderEmbedding.mulRight` 的定义

English:
definition OrderEmbedding.mulRight
  signature: {α : Type*} [Mul α] [LinearOrder α]
  body: OrderEmbedding.ofStrictMono (fun n => n * m) mul_left_strictMono

中文:
定义 OrderEmbedding.mulRight
  签名: {α : 类型} [乘法 α] [线性序 α]
  定义体: OrderEmbedding.ofStrictMono (fun n => n * m) mul_left_strictMono

Depends on / 依赖: OrderEmbedding, OrderEmbedding.ofStrictMono, mul_left_strictMono, ofStrictMono
-/
def OrderEmbedding.mulRight {α : Type*} [Mul α] [LinearOrder α]
    [MulRightStrictMono α] (m : α) : α ↪o α :=
  OrderEmbedding.ofStrictMono (fun n => n * m) mul_left_strictMono
