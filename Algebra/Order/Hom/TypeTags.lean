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

/-- Reinterpret `G ≃*o H` as `Additive G ≃+o Additive H`. -/
/-
**OrderMonoidIso.toAdditive** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OrderMonoidIso.toAdditive {G H : Type*} [CommMonoid G] [PartialOrder G] [C
ommMonoid H] [PartialOrder H] : (G ≃*o H) ≃ (Additive G ≃+o Additive H) where to
Fun e
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Reinterpret `G ≃*o H` as `Additive G ≃+o Additive H`.
-/
def OrderMonoidIso.toAdditive {G H : Type*}
    [CommMonoid G] [PartialOrder G] [CommMonoid H] [PartialOrder H] :
    (G ≃*o H) ≃ (Additive G ≃+o Additive H) where
  toFun e := ⟨MulEquiv.toAdditive e, by simp⟩
  invFun e := ⟨MulEquiv.toAdditive.symm e, by simp⟩
  left_inv e := by ext; simp
  right_inv e := by ext; simp

/-- Reinterpret `G ≃+o H` as `Multiplicative G ≃*o Multiplicative H`. -/
/-
**OrderAddMonoidIso.toMultiplicative** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OrderAddMonoidIso.toMultiplicative {G H : Type*} [AddCommMonoid G] [Partia
lOrder G] [AddCommMonoid H] [PartialOrder H] : (G ≃+o H) ≃ (Multiplicative G ≃*o
 Multiplicative H) where toFun e
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Reinterpret `G ≃+o H` as `Multiplicative G ≃*o Multiplicative H`.
-/
def OrderAddMonoidIso.toMultiplicative {G H : Type*}
    [AddCommMonoid G] [PartialOrder G] [AddCommMonoid H] [PartialOrder H] :
    (G ≃+o H) ≃ (Multiplicative G ≃*o Multiplicative H) where
  toFun e := ⟨AddEquiv.toMultiplicative e, by simp⟩
  invFun e := ⟨AddEquiv.toMultiplicative.symm e, by simp⟩
  left_inv e := by ext; simp
  right_inv e := by ext; simp

/-- Reinterpret `Additive G ≃+o H` as `G ≃*o Multiplicative H`. -/
/-
**OrderAddMonoidIso.toMultiplicativeRight** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OrderAddMonoidIso.toMultiplicativeRight {G H : Type*} [CommMonoid G] [Part
ialOrder G] [AddCommMonoid H] [PartialOrder H] : (Additive G ≃+o H) ≃ (G ≃*o Mul
tiplicative H) where toFun e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret `Additive G ≃+o H` as `G ≃*o Multiplicative H`.
-/
def OrderAddMonoidIso.toMultiplicativeRight {G H : Type*}
    [CommMonoid G] [PartialOrder G] [AddCommMonoid H] [PartialOrder H] :
    (Additive G ≃+o H) ≃ (G ≃*o Multiplicative H) where
  toFun e := ⟨e.toAddEquiv.toMultiplicativeRight, by simp⟩
  invFun e := ⟨e.toMulEquiv.toAdditiveLeft, by simp⟩
  left_inv e := by ext; simp
  right_inv e := by ext; simp

/-- Reinterpret `G ≃* Multiplicative H` as `Additive G ≃+ H`. -/
/-
**OrderMonoidIso.toAdditiveLeft** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：OrderMonoidIso.toAdditiveLeft {G H : Type*} [CommMonoid G] [PartialOrder G
] [AddCommMonoid H] [PartialOrder H] : (G ≃*o Multiplicative H) ≃ (Additive G ≃+
o H)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Reinterpret `G ≃* Multiplicative H` as `Additive G ≃+ H`.
-/
abbrev OrderMonoidIso.toAdditiveLeft {G H : Type*}
    [CommMonoid G] [PartialOrder G] [AddCommMonoid H] [PartialOrder H] :
    (G ≃*o Multiplicative H) ≃ (Additive G ≃+o H) :=
  OrderAddMonoidIso.toMultiplicativeRight.symm

/-- Reinterpret `G ≃+o Additive H` as `Multiplicative G ≃*o H`. -/
/-
**OrderAddMonoidIso.toMultiplicativeLeft** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OrderAddMonoidIso.toMultiplicativeLeft {G H : Type*} [AddCommMonoid G] [Pa
rtialOrder G] [CommMonoid H] [PartialOrder H] : (G ≃+o Additive H) ≃ (Multiplica
tive G ≃*o H) where toFun e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret `G ≃+o Additive H` as `Multiplicative G ≃*o H`.
-/
def OrderAddMonoidIso.toMultiplicativeLeft {G H : Type*}
    [AddCommMonoid G] [PartialOrder G] [CommMonoid H] [PartialOrder H] :
    (G ≃+o Additive H) ≃ (Multiplicative G ≃*o H) where
  toFun e := ⟨e.toAddEquiv.toMultiplicativeLeft, by simp⟩
  invFun e := ⟨e.toMulEquiv.toAdditiveRight, by simp⟩
  left_inv e := by ext; simp
  right_inv e := by ext; simp

/-- Reinterpret `Multiplicative G ≃*o H` as `G ≃+o Additive H` as. -/
/-
**OrderMonoidIso.toAdditiveRight** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：OrderMonoidIso.toAdditiveRight {G H : Type*} [AddCommMonoid G] [PartialOrd
er G] [CommMonoid H] [PartialOrder H] : (Multiplicative G ≃*o H) ≃ (G ≃+o Additi
ve H)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Reinterpret `Multiplicative G ≃*o H` as `G ≃+o Additive H` as.
-/
abbrev OrderMonoidIso.toAdditiveRight {G H : Type*}
    [AddCommMonoid G] [PartialOrder G] [CommMonoid H] [PartialOrder H] :
    (Multiplicative G ≃*o H) ≃ (G ≃+o Additive H) :=
  OrderAddMonoidIso.toMultiplicativeLeft.symm

/-- The multiplicative version of an additivized ordered monoid is order-mul-equivalent to itself.
-/
/-
**OrderMonoidIso.toMultiplicative_toAdditive** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OrderMonoidIso.toMultiplicative_toAdditive {G : Type*} [CommMonoid G] [Par
tialOrder G] : Multiplicative (Additive G) ≃*o G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiplicative version of an additivized ordered monoid is order-mul-equival
ent to itself.
-/
def OrderMonoidIso.toMultiplicative_toAdditive {G : Type*} [CommMonoid G] [PartialOrder G] :
    Multiplicative (Additive G) ≃*o G :=
  OrderAddMonoidIso.toMultiplicativeLeft <| OrderMonoidIso.toAdditive (.refl _)

/-- The additive version of a multiplicativized ordered additive monoid is
order-add-equivalent to itself. -/
/-
**OrderAddMonoidIso.toAdditive_toMultiplicative** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OrderAddMonoidIso.toAdditive_toMultiplicative {G : Type*} [AddCommMonoid G
] [PartialOrder G] : Additive (Multiplicative G) ≃+o G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The additive version of a multiplicativized ordered additive monoid is
order-add-equivalent to itself.
-/
def OrderAddMonoidIso.toAdditive_toMultiplicative {G : Type*} [AddCommMonoid G] [PartialOrder G] :
    Additive (Multiplicative G) ≃+o G :=
  OrderMonoidIso.toAdditiveLeft <| OrderAddMonoidIso.toMultiplicative (.refl _)
/-
**Additive.instUniqueOrderAddMonoidIso** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Additive.instUniqueOrderAddMonoidIso {G H : Type*} [CommMonoid G] [Partial
Order G] [CommMonoid H] [PartialOrder H] [Unique (G ≃*o H)] : Unique (Additive G
 ≃+o Additive H)
参数：G ≃*o H。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
instance Additive.instUniqueOrderAddMonoidIso {G H : Type*}
    [CommMonoid G] [PartialOrder G] [CommMonoid H] [PartialOrder H] [Unique (G ≃*o H)] :
    Unique (Additive G ≃+o Additive H) :=
  OrderMonoidIso.toAdditive.symm.unique
/-
**Multiplicative.instUniqueOrderdMonoidIso** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Multiplicative.instUniqueOrderdMonoidIso {G H : Type*} [AddCommMonoid G] [
PartialOrder G] [AddCommMonoid H] [PartialOrder H] [Unique (G ≃+o H)] : Unique (
Multiplicative G ≃*o Multiplicative H)
参数：G ≃+o H。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
instance Multiplicative.instUniqueOrderdMonoidIso {G H : Type*}
    [AddCommMonoid G] [PartialOrder G] [AddCommMonoid H] [PartialOrder H] [Unique (G ≃+o H)] :
    Unique (Multiplicative G ≃*o Multiplicative H) :=
  OrderAddMonoidIso.toMultiplicative.symm.unique

end TypeTags

