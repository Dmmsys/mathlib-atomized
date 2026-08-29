/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.Algebra.Order.Hom.Monoid
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags

/-!

# Order Monoid Isomorphisms on `Additive` and `Multiplicative`.

-/

@[expose] public section

section TypeTags

/--
Definition of `OrderMonoidIso.toAdditive` / `OrderMonoidIso.toAdditive` 的定义

English:
definition OrderMonoidIso.toAdditive
  signature: {G H : Type*}
  body: ⟨MulEquiv.toAdditive e, by simp⟩
  invFun e := ⟨MulEquiv.toAdditive.symm e, by simp⟩
  left_inv e := by ext; simp
  right_inv e := by ext; simp

中文:
定义 OrderMonoidIso.toAdditive
  签名: {G H : 类型}
  定义体: ⟨MulEquiv.toAdditive e, by simp⟩
  invFun e := ⟨MulEquiv.toAdditive.symm e, by simp⟩
  left_inv e := by ext; simp
  right_inv e := by ext; simp

Depends on / 依赖: MulEquiv, MulEquiv.toAdditive, toAdditive
-/
def OrderMonoidIso.toAdditive {G H : Type*}
    [CommMonoid G] [PartialOrder G] [CommMonoid H] [PartialOrder H] :
    (G ≃*o H) ≃ (Additive G ≃+o Additive H) where
  toFun e := ⟨MulEquiv.toAdditive e, by simp⟩
  invFun e := ⟨MulEquiv.toAdditive.symm e, by simp⟩
  left_inv e := by ext; simp
  right_inv e := by ext; simp

/--
Definition of `OrderAddMonoidIso.toMultiplicative` / `OrderAddMonoidIso.toMultiplicative` 的定义

English:
definition OrderAddMonoidIso.toMultiplicative
  signature: {G H : Type*}
  body: ⟨AddEquiv.toMultiplicative e, by simp⟩
  invFun e := ⟨AddEquiv.toMultiplicative.symm e, by simp⟩
  left_inv e := by ext; simp
  right_inv e := by ext; simp

中文:
定义 OrderAddMonoidIso.toMultiplicative
  签名: {G H : 类型}
  定义体: ⟨AddEquiv.toMultiplicative e, by simp⟩
  invFun e := ⟨AddEquiv.toMultiplicative.symm e, by simp⟩
  left_inv e := by ext; simp
  right_inv e := by ext; simp

Depends on / 依赖: AddEquiv, AddEquiv.toMultiplicative, toMultiplicative
-/
def OrderAddMonoidIso.toMultiplicative {G H : Type*}
    [AddCommMonoid G] [PartialOrder G] [AddCommMonoid H] [PartialOrder H] :
    (G ≃+o H) ≃ (Multiplicative G ≃*o Multiplicative H) where
  toFun e := ⟨AddEquiv.toMultiplicative e, by simp⟩
  invFun e := ⟨AddEquiv.toMultiplicative.symm e, by simp⟩
  left_inv e := by ext; simp
  right_inv e := by ext; simp

/--
Definition of `OrderAddMonoidIso.toMultiplicativeRight` / `OrderAddMonoidIso.toMultiplicativeRight` 的定义

English:
definition OrderAddMonoidIso.toMultiplicativeRight
  signature: {G H : Type*}
  body: ⟨e.toAddEquiv.toMultiplicativeRight, by simp⟩
  invFun e := ⟨e.toMulEquiv.toAdditiveLeft, by simp⟩
  left_inv e := by ext; simp
  right_inv e := by ext; simp

中文:
定义 OrderAddMonoidIso.toMultiplicativeRight
  签名: {G H : 类型}
  定义体: ⟨e.toAddEquiv.toMultiplicativeRight, by simp⟩
  invFun e := ⟨e.toMulEquiv.toAdditiveLeft, by simp⟩
  left_inv e := by ext; simp
  right_inv e := by ext; simp

Depends on / 依赖: e.toAddEquiv.toMultiplicativeRight, toAddEquiv, toMultiplicativeRight
-/
def OrderAddMonoidIso.toMultiplicativeRight {G H : Type*}
    [CommMonoid G] [PartialOrder G] [AddCommMonoid H] [PartialOrder H] :
    (Additive G ≃+o H) ≃ (G ≃*o Multiplicative H) where
  toFun e := ⟨e.toAddEquiv.toMultiplicativeRight, by simp⟩
  invFun e := ⟨e.toMulEquiv.toAdditiveLeft, by simp⟩
  left_inv e := by ext; simp
  right_inv e := by ext; simp

/--
Definition of `OrderMonoidIso.toAdditiveLeft` / `OrderMonoidIso.toAdditiveLeft` 的定义

English:
abbreviation OrderMonoidIso.toAdditiveLeft
  signature: {G H : Type*}
  body: OrderAddMonoidIso.toMultiplicativeRight.symm

中文:
缩写 OrderMonoidIso.toAdditiveLeft
  签名: {G H : 类型}
  定义体: OrderAddMonoidIso.toMultiplicativeRight.symm

Depends on / 依赖: OrderAddMonoidIso, OrderAddMonoidIso.toMultiplicativeRight.symm, toMultiplicativeRight
-/
abbrev OrderMonoidIso.toAdditiveLeft {G H : Type*}
    [CommMonoid G] [PartialOrder G] [AddCommMonoid H] [PartialOrder H] :
    (G ≃*o Multiplicative H) ≃ (Additive G ≃+o H) :=
  OrderAddMonoidIso.toMultiplicativeRight.symm

/--
Definition of `OrderAddMonoidIso.toMultiplicativeLeft` / `OrderAddMonoidIso.toMultiplicativeLeft` 的定义

English:
definition OrderAddMonoidIso.toMultiplicativeLeft
  signature: {G H : Type*}
  body: ⟨e.toAddEquiv.toMultiplicativeLeft, by simp⟩
  invFun e := ⟨e.toMulEquiv.toAdditiveRight, by simp⟩
  left_inv e := by ext; simp
  right_inv e := by ext; simp

中文:
定义 OrderAddMonoidIso.toMultiplicativeLeft
  签名: {G H : 类型}
  定义体: ⟨e.toAddEquiv.toMultiplicativeLeft, by simp⟩
  invFun e := ⟨e.toMulEquiv.toAdditiveRight, by simp⟩
  left_inv e := by ext; simp
  right_inv e := by ext; simp

Depends on / 依赖: e.toAddEquiv.toMultiplicativeLeft, toAddEquiv, toMultiplicativeLeft
-/
def OrderAddMonoidIso.toMultiplicativeLeft {G H : Type*}
    [AddCommMonoid G] [PartialOrder G] [CommMonoid H] [PartialOrder H] :
    (G ≃+o Additive H) ≃ (Multiplicative G ≃*o H) where
  toFun e := ⟨e.toAddEquiv.toMultiplicativeLeft, by simp⟩
  invFun e := ⟨e.toMulEquiv.toAdditiveRight, by simp⟩
  left_inv e := by ext; simp
  right_inv e := by ext; simp

/--
Definition of `OrderMonoidIso.toAdditiveRight` / `OrderMonoidIso.toAdditiveRight` 的定义

English:
abbreviation OrderMonoidIso.toAdditiveRight
  signature: {G H : Type*}
  body: OrderAddMonoidIso.toMultiplicativeLeft.symm

中文:
缩写 OrderMonoidIso.toAdditiveRight
  签名: {G H : 类型}
  定义体: OrderAddMonoidIso.toMultiplicativeLeft.symm

Depends on / 依赖: OrderAddMonoidIso, OrderAddMonoidIso.toMultiplicativeLeft.symm, toMultiplicativeLeft
-/
abbrev OrderMonoidIso.toAdditiveRight {G H : Type*}
    [AddCommMonoid G] [PartialOrder G] [CommMonoid H] [PartialOrder H] :
    (Multiplicative G ≃*o H) ≃ (G ≃+o Additive H) :=
  OrderAddMonoidIso.toMultiplicativeLeft.symm

/--
Definition of `OrderMonoidIso.toMultiplicative_toAdditive` / `OrderMonoidIso.toMultiplicative_toAdditive` 的定义

English:
definition OrderMonoidIso.toMultiplicative_toAdditive
  signature: {G : Type*} [CommMonoid G] [PartialOrder G]
  body: OrderAddMonoidIso.toMultiplicativeLeft OrderMonoidIso.toAdditive (.refl _)

中文:
定义 OrderMonoidIso.toMultiplicative_toAdditive
  签名: {G : 类型} [交换幺半群 G] [偏序 G]
  定义体: OrderAddMonoidIso.toMultiplicativeLeft OrderMonoidIso.toAdditive (.refl _)

Depends on / 依赖: OrderAddMonoidIso, OrderAddMonoidIso.toMultiplicativeLeft, OrderMonoidIso, OrderMonoidIso.toAdditive, toAdditive, toMultiplicativeLeft
-/
def OrderMonoidIso.toMultiplicative_toAdditive {G : Type*} [CommMonoid G] [PartialOrder G] :
    Multiplicative (Additive G) ≃*o G :=
OrderAddMonoidIso.toMultiplicativeLeft OrderMonoidIso.toAdditive (.refl _)

/--
Definition of `OrderAddMonoidIso.toAdditive_toMultiplicative` / `OrderAddMonoidIso.toAdditive_toMultiplicative` 的定义

English:
definition OrderAddMonoidIso.toAdditive_toMultiplicative
  signature: {G : Type*} [AddCommMonoid G] [PartialOrder G]
  body: OrderMonoidIso.toAdditiveLeft OrderAddMonoidIso.toMultiplicative (.refl _)

中文:
定义 OrderAddMonoidIso.toAdditive_toMultiplicative
  签名: {G : 类型} [加法交换幺半群 G] [偏序 G]
  定义体: OrderMonoidIso.toAdditiveLeft OrderAddMonoidIso.toMultiplicative (.refl _)

Depends on / 依赖: OrderAddMonoidIso, OrderAddMonoidIso.toMultiplicative, OrderMonoidIso, OrderMonoidIso.toAdditiveLeft, toAdditiveLeft, toMultiplicative
-/
def OrderAddMonoidIso.toAdditive_toMultiplicative {G : Type*} [AddCommMonoid G] [PartialOrder G] :
    Additive (Multiplicative G) ≃+o G :=
OrderMonoidIso.toAdditiveLeft OrderAddMonoidIso.toMultiplicative (.refl _)

/--
Instance `Additive.instUniqueOrderAddMonoidIso` / 实例 `Additive.instUniqueOrderAddMonoidIso`

English:
instance Additive.instUniqueOrderAddMonoidIso
  signature: {G H : Type*}
  body: OrderMonoidIso.toAdditive.symm.unique

中文:
实例 加性.instUniqueOrderAddMonoidIso
  签名: {G H : 类型}
  定义体: OrderMonoidIso.toAdditive.symm.unique

Depends on / 依赖: OrderMonoidIso, OrderMonoidIso.toAdditive.symm.unique, toAdditive, unique
-/
instance Additive.instUniqueOrderAddMonoidIso {G H : Type*}
    [CommMonoid G] [PartialOrder G] [CommMonoid H] [PartialOrder H] [Unique (G ≃*o H)] :
    Unique (Additive G ≃+o Additive H) :=
  OrderMonoidIso.toAdditive.symm.unique

/--
Instance `Multiplicative.instUniqueOrderdMonoidIso` / 实例 `Multiplicative.instUniqueOrderdMonoidIso`

English:
instance Multiplicative.instUniqueOrderdMonoidIso
  signature: {G H : Type*}
  body: OrderAddMonoidIso.toMultiplicative.symm.unique

中文:
实例 Multiplicative.instUniqueOrderdMonoidIso
  签名: {G H : 类型}
  定义体: OrderAddMonoidIso.toMultiplicative.symm.unique

Depends on / 依赖: OrderAddMonoidIso, OrderAddMonoidIso.toMultiplicative.symm.unique, toMultiplicative, unique
-/
instance Multiplicative.instUniqueOrderdMonoidIso {G H : Type*}
    [AddCommMonoid G] [PartialOrder G] [AddCommMonoid H] [PartialOrder H] [Unique (G ≃+o H)] :
    Unique (Multiplicative G ≃*o Multiplicative H) :=
  OrderAddMonoidIso.toMultiplicative.symm.unique

end TypeTags
