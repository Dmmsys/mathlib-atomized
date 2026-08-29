/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Johan Commelin, Patrick Massot
-/
module

public import Mathlib.Algebra.Group.WithOne.Map
public import Mathlib.Algebra.GroupWithZero.InjSurj
public import Mathlib.Algebra.GroupWithZero.Regular
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Order.AddGroupWithTop
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Group.Units
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Monoid.OrderDual
public import Mathlib.Algebra.Order.Monoid.TypeTags
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Set.Function

/-!
# Linearly ordered commutative groups and monoids with a zero element adjoined

This file sets up a special class of linearly ordered commutative monoids
that show up as the target of so-called “valuations” in algebraic number theory.

Usually, in the informal literature, these objects are constructed
by taking a linearly ordered commutative group Γ and formally adjoining a zero element: `Γ ∪ {0}`.

The disadvantage is that a type such as `NNReal` is not of that form,
whereas it is a very common target for valuations.
The solutions is to use a typeclass, and that is exactly what we do in this file.
-/

@[expose] public section

variable {α β : Type*}

/--
Definition of `LinearOrderedCommMonoidWithZero` / `LinearOrderedCommMonoidWithZero` 的定义

English:
class LinearOrderedCommMonoidWithZero
  parameters: (α : Type*)
  extends: CommMonoidWithZero α, LinearOrder α, 
  (no additional axioms)

中文:
类 LinearOrderedCommMonoidWithZero
  参数: (α : 类型)
  继承: CommMonoidWithZero α, LinearOrder α, 
  (无附加公理)
-/
class LinearOrderedCommMonoidWithZero (α : Type*) extends CommMonoidWithZero α, LinearOrder α,
    PosMulStrictMono α, OrderBot α, IsBotZeroClass α where

/--
Definition of `LinearOrderedCommGroupWithZero` / `LinearOrderedCommGroupWithZero` 的定义

English:
class LinearOrderedCommGroupWithZero
  parameters: (α : Type*)
  extends: LinearOrderedCommMonoidWithZero α, 
  (no additional axioms)

中文:
类 LinearOrderedCommGroupWithZero
  参数: (α : 类型)
  继承: LinearOrderedCommMonoidWithZero α, 
  (无附加公理)
-/
class LinearOrderedCommGroupWithZero (α : Type*) extends LinearOrderedCommMonoidWithZero α,
  CommGroupWithZero α

section LinearOrderedCommMonoidWithZero
variable [LinearOrderedCommMonoidWithZero α] {a b : α} {n : Nat}

/-!
The following facts are true more generally in a (linearly) ordered commutative monoid.
-/

-- See note [lower instance priority]
instance (priority := 100) LinearOrderedCommMonoidWithZero.toMulPosStrictMono :
    MulPosStrictMono α := posMulStrictMono_iff_mulPosStrictMono.1 inferInstance

-- See note [lower instance priority]
instance (priority := 100) LinearOrderedCommMonoidWithZero.toIsOrderedMonoid :
    IsOrderedMonoid α where
  mul_le_mul_left a b hab c := by
    obtain rfl | hc := eq_or_ne c 0
    · simp
    obtain rfl | hab := hab.eq_or_lt
    · simp
    · exact (mul_lt_mul_of_pos_right hab hc.pos).le

-- See note [lower instance priority]
instance (priority := 100) : IsCancelMulZero α where
  mul_left_cancel_of_ne_zero ha := (strictMono_mul_left_of_pos ha.pos).injective
  mul_right_cancel_of_ne_zero ha := (strictMono_mul_right_of_pos ha.pos).injective

/--
Definition of `Function.Injective.linearOrderedCommMonoidWithZero` / `Function.Injective.linearOrderedCommMonoidWithZero` 的定义

English:
abbreviation Function.Injective.linearOrderedCommMonoidWithZero
  signature: {β : Type*} [Zero β] [Bot β] [One β]
  body: hf.linearOrder f le lt hinf hsup compare
  __ := hf.commMonoidWithZero f zero one mul npow
  __ := Function.Injective.posMulStrictMono f zero mul lt
isBot_zero _ := le.1 zero ▸ zero_le
bot_le _ := le.1 bot ▸ bot_le

中文:
缩写 Function.Injective.linearOrderedCommMonoidWithZero
  签名: {β : 类型} [Zero β] [Bot β] [One β]
  定义体: hf.linearOrder f le lt hinf hsup compare
  __ := hf.commMonoidWithZero f zero one mul npow
  __ := Function.Injective.posMulStrictMono f zero mul lt
isBot_zero _ := le.1 zero ▸ zero_le
bot_le _ := le.1 bot ▸ bot_le

Depends on / 依赖: compare, hf.linearOrder, linearOrder
-/
abbrev Function.Injective.linearOrderedCommMonoidWithZero {β : Type*} [Zero β] [Bot β] [One β]
    [Mul β] [Pow β Nat] [LE β] [LT β] [Max β] [Min β] [Ord β]
    [DecidableEq β] [DecidableLE β] [DecidableLT β]
    (f : β -> α) (hf : Function.Injective f) (zero : f 0 = 0)
    (one : f 1 = 1) (mul : forall x y, f (x * y) = f x * f y) (npow : forall (x) (n : Nat), f (x ^ n) = f x ^ n)
    (le : forall {x y}, f x <= f y ↔ x <= y) (lt : forall {x y}, f x < f y ↔ x < y)
    (hsup : forall x y, f (x ⊔ y) = max (f x) (f y)) (hinf : forall x y, f (x ⊓ y) = min (f x) (f y))
    (bot : f ⊥ = ⊥)
    (compare : forall x y, compare (f x) (f y) = compare x y) :
    LinearOrderedCommMonoidWithZero β where
  __ := hf.linearOrder f le lt hinf hsup compare
  __ := hf.commMonoidWithZero f zero one mul npow
  __ := Function.Injective.posMulStrictMono f zero mul lt
isBot_zero _ := le.1 zero ▸ zero_le
bot_le _ := le.1 bot ▸ bot_le

instance (priority := 100) LinearOrderedCommMonoidWithZero.toIsMulTorsionFree :
    IsMulTorsionFree α where
  pow_left_injective n hn := by simpa using (pow_left_strictMonoOn₀ (M₀ := α) hn).injOn

/--
Instance `instLinearOrderedAddCommMonoidWithTopAdditiveOrderDual` / 实例 `instLinearOrderedAddCommMonoidWithTopAdditiveOrderDual`

English:
instance instLinearOrderedAddCommMonoidWithTopAdditiveOrderDual
  signature: :
  body: by ext; simp [bot_eq_zero]
  isAddLeftRegular_of_ne_top := by simp +contextual [IsRegular.of_ne_zero, bot_eq_zero]

中文:
实例 instLinearOrderedAddCommMonoidWithTopAdditiveOrderDual
  签名: :
  定义体: by ext; simp [bot_eq_zero]
  isAddLeftRegular_of_ne_top := by simp +contextual [IsRegular.of_ne_zero, bot_eq_zero]

Depends on / 依赖: IsRegular, IsRegular.of_ne_zero, bot_eq_zero, contextual, isAddLeftRegular_of_ne_top, of_ne_zero
-/
instance instLinearOrderedAddCommMonoidWithTopAdditiveOrderDual :
    LinearOrderedAddCommMonoidWithTop (Additive αᵒᵈ) where
  top_add' a := by ext; simp [bot_eq_zero]
  isAddLeftRegular_of_ne_top := by simp +contextual [IsRegular.of_ne_zero, bot_eq_zero]

set_option backward.isDefEq.respectTransparency false in
/--
Instance `instLinearOrderedAddCommMonoidWithTopOrderDualAdditive` / 实例 `instLinearOrderedAddCommMonoidWithTopOrderDualAdditive`

English:
instance instLinearOrderedAddCommMonoidWithTopOrderDualAdditive
  signature: :
  body: by ext; simp; simp [bot_eq_zero (α := α)]
  isAddLeftRegular_of_ne_top := by simp; simp +contextual [bot_eq_zero, IsRegular.of_ne_zero]

中文:
实例 instLinearOrderedAddCommMonoidWithTopOrderDualAdditive
  签名: :
  定义体: by ext; simp; simp [bot_eq_zero (α := α)]
  isAddLeftRegular_of_ne_top := by simp; simp +contextual [bot_eq_zero, IsRegular.of_ne_zero]

Depends on / 依赖: IsRegular, IsRegular.of_ne_zero, bot_eq_zero, contextual, isAddLeftRegular_of_ne_top, of_ne_zero
-/
instance instLinearOrderedAddCommMonoidWithTopOrderDualAdditive :
    LinearOrderedAddCommMonoidWithTop (Additive α)ᵒᵈ where
  top_add' a := by ext; simp; simp [bot_eq_zero (α := α)]
  isAddLeftRegular_of_ne_top := by simp; simp +contextual [bot_eq_zero, IsRegular.of_ne_zero]

variable [IsReduced α]

/--
lemma `pow_pos_iff` / 引理 `pow_pos_iff`

English:
lemma pow_pos_iff
  given: (hn : n != 0)
  statement: 0 < a ^ n ↔ 0 < a
  proof: by
  simp_rw [pos_iff_ne_zero, pow_ne_zero_iff hn]

中文:
引理 pow_pos_iff
  条件: (hn : n != 0)
  结论: 0 < a ^ n ↔ 0 < a
  证明: by
  simp_rw [pos_iff_ne_zero, pow_ne_zero_iff hn]

Depends on / 依赖: pos_iff_ne_zero, pow_ne_zero_iff, simp_rw
-/
lemma pow_pos_iff (hn : n != 0) : 0 < a ^ n ↔ 0 < a := by
  simp_rw [pos_iff_ne_zero, pow_ne_zero_iff hn]

end LinearOrderedCommMonoidWithZero

section LinearOrderedCommGroupWithZero
variable [LinearOrderedCommGroupWithZero α] {a b c d : α} {m n : Nat}

@[simp]
/--
theorem `Units.zero_lt` / 定理 `Units.zero_lt`

English:
theorem Units.zero_lt
  given: (u : αˣ)
  statement: (0 : α) < u
  proof: u.ne_zero.pos

中文:
定理 Units.zero_lt
  条件: (u : αˣ)
  结论: (0 : α) < u
  证明: u.ne_zero.pos

Depends on / 依赖: ne_zero, u.ne_zero.pos
-/
theorem Units.zero_lt (u : αˣ) : (0 : α) < u :=
  u.ne_zero.pos

/--
theorem `mul_inv_lt_of_lt_mul₀` / 定理 `mul_inv_lt_of_lt_mul₀`

English:
theorem mul_inv_lt_of_lt_mul₀
  given: (h : a < b * c)
  statement: a * c⁻¹ < b
  proof: by
  contrapose! h
  simpa only [inv_inv] using mul_inv_le_of_le_mul₀ zero_le zero_le h

中文:
定理 mul_inv_lt_of_lt_mul₀
  条件: (h : a < b * c)
  结论: a * c⁻¹ < b
  证明: by
  contrapose! h
  simpa only [inv_inv] using mul_inv_le_of_le_mul₀ zero_le zero_le h

Depends on / 依赖: contrapose, inv_inv, zero_le
-/
theorem mul_inv_lt_of_lt_mul₀ (h : a < b * c) : a * c⁻¹ < b := by
  contrapose! h
  simpa only [inv_inv] using mul_inv_le_of_le_mul₀ zero_le zero_le h

/--
theorem `inv_mul_lt_of_lt_mul₀` / 定理 `inv_mul_lt_of_lt_mul₀`

English:
theorem inv_mul_lt_of_lt_mul₀
  given: (h : a < b * c)
  statement: b⁻¹ * a < c
  proof: by
  rw [mul_comm] at *
  exact mul_inv_lt_of_lt_mul₀ h

中文:
定理 inv_mul_lt_of_lt_mul₀
  条件: (h : a < b * c)
  结论: b⁻¹ * a < c
  证明: by
  rw [mul_comm] at *
  exact mul_inv_lt_of_lt_mul₀ h

Depends on / 依赖: mul_comm
-/
theorem inv_mul_lt_of_lt_mul₀ (h : a < b * c) : b⁻¹ * a < c := by
  rw [mul_comm] at *
  exact mul_inv_lt_of_lt_mul₀ h

/--
theorem `lt_of_mul_lt_mul_of_le₀` / 定理 `lt_of_mul_lt_mul_of_le₀`

English:
theorem lt_of_mul_lt_mul_of_le₀
  given: (h : a * b < c * d) (hc : 0 < c) (hh : c <= a)
  statement: b < d
  proof: by
  have ha : a != 0 := ne_of_gt (lt_of_lt_of_le hc hh)
  rw [← inv_le_inv₀ ha.pos hc] at hh
  simpa [inv_mul_cancel_left₀ ha, inv_mul_cancel_left₀ hc.ne']
    using mul_lt_mul_of_le_of_lt_of_nonneg_of_pos hh h zero_le (inv_pos.2 hc)

中文:
定理 lt_of_mul_lt_mul_of_le₀
  条件: (h : a * b < c * d) (hc : 0 < c) (hh : c <= a)
  结论: b < d
  证明: by
  have ha : a != 0 := ne_of_gt (lt_of_lt_of_le hc hh)
  rw [← inv_le_inv₀ ha.pos hc] at hh
  simpa [inv_mul_cancel_left₀ ha, inv_mul_cancel_left₀ hc.ne']
    using mul_lt_mul_of_le_of_lt_of_nonneg_of_pos hh h zero_le (inv_pos.2 hc)

Depends on / 依赖: ha.pos, hc.ne, inv_pos, lt_of_lt_of_le, mul_lt_mul_of_le_of_lt_of_nonneg_of_pos, ne_of_gt, zero_le
-/
theorem lt_of_mul_lt_mul_of_le₀ (h : a * b < c * d) (hc : 0 < c) (hh : c <= a) : b < d := by
  have ha : a != 0 := ne_of_gt (lt_of_lt_of_le hc hh)
  rw [← inv_le_inv₀ ha.pos hc] at hh
  simpa [inv_mul_cancel_left₀ ha, inv_mul_cancel_left₀ hc.ne']
    using mul_lt_mul_of_le_of_lt_of_nonneg_of_pos hh h zero_le (inv_pos.2 hc)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LinearOrderedAddCommGroupWithTop (Additive αᵒᵈ)
  body: by simp
  neg_top := by ext; simp [bot_eq_zero]
  add_neg_cancel_of_ne_top := by
    simp +contextual [bot_eq_zero, Additive.ext_iff, OrderDual.ext_iff, -Additive.toMul_eq_top,
      -ofDual_eq_zero]

中文:
实例 :
  签名: LinearOrderedAddCommGroupWithTop (Additive αᵒᵈ)
  定义体: by simp
  neg_top := by ext; simp [bot_eq_zero]
  add_neg_cancel_of_ne_top := by
    simp +contextual [bot_eq_zero, Additive.ext_iff, OrderDual.ext_iff, -Additive.toMul_eq_top,
      -ofDual_eq_zero]

Depends on / 依赖: Additive, Additive.ext_iff, Additive.toMul_eq_top, OrderDual, OrderDual.ext_iff, add_neg_cancel_of_ne_top, bot_eq_zero, contextual, ext_iff, neg_top, ofDual_eq_zero, toMul_eq_top
-/
instance : LinearOrderedAddCommGroupWithTop (Additive αᵒᵈ) where
  top_add' := by simp
  neg_top := by ext; simp [bot_eq_zero]
  add_neg_cancel_of_ne_top := by
    simp +contextual [bot_eq_zero, Additive.ext_iff, OrderDual.ext_iff, -Additive.toMul_eq_top,
      -ofDual_eq_zero]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LinearOrderedAddCommGroupWithTop (Additive α)ᵒᵈ
  body: by simp
  neg_top := by ext; simp; simp [bot_eq_zero]
  add_neg_cancel_of_ne_top := by
    simp
    simp +contextual [bot_eq_zero, Additive.ext_iff, OrderDual.ext_iff, -Additive.toMul_eq_top,
      -ofDual_eq_zero]

中文:
实例 :
  签名: LinearOrderedAddCommGroupWithTop (Additive α)ᵒᵈ
  定义体: by simp
  neg_top := by ext; simp; simp [bot_eq_zero]
  add_neg_cancel_of_ne_top := by
    simp
    simp +contextual [bot_eq_zero, Additive.ext_iff, OrderDual.ext_iff, -Additive.toMul_eq_top,
      -ofDual_eq_zero]

Depends on / 依赖: Additive, Additive.ext_iff, Additive.toMul_eq_top, OrderDual, OrderDual.ext_iff, add_neg_cancel_of_ne_top, bot_eq_zero, contextual, ext_iff, neg_top, ofDual_eq_zero, toMul_eq_top
-/
instance : LinearOrderedAddCommGroupWithTop (Additive α)ᵒᵈ where
  top_add' := by simp
  neg_top := by ext; simp; simp [bot_eq_zero]
  add_neg_cancel_of_ne_top := by
    simp
    simp +contextual [bot_eq_zero, Additive.ext_iff, OrderDual.ext_iff, -Additive.toMul_eq_top,
      -ofDual_eq_zero]

-- Counterexample with monoid for the backward direction:
-- Take `Mᵐ⁰` where `M := ℚ ×ₗ ℕ`.
/--
lemma `denselyOrdered_iff_denselyOrdered_units_and_nontrivial_units` / 引理 `denselyOrdered_iff_denselyOrdered_units_and_nontrivial_units`

English:
lemma denselyOrdered_iff_denselyOrdered_units_and_nontrivial_units
  proof: by
  refine ⟨fun H => ⟨?_, ?_⟩, fun ⟨H₁, H₂⟩ => ?_⟩
  · obtain ⟨x, hx, hx'⟩ := exists_between (zero_lt_one' α)
    exact ⟨Units.mk0 x hx.ne', 1, by simpa [Units.ext_iff] using hx'.ne⟩
  · refine ⟨fun x y h => ?_⟩
    obtain ⟨z, hz⟩ := exists_between (Units.val_lt_val.mpr h)
    refine ⟨Units.mk0 z (

中文:
引理 denselyOrdered_iff_denselyOrdered_units_and_nontrivial_units
  证明: by
  refine ⟨fun H => ⟨?_, ?_⟩, fun ⟨H₁, H₂⟩ => ?_⟩
  · obtain ⟨x, hx, hx'⟩ := exists_between (zero_lt_one' α)
    exact ⟨Units.mk0 x hx.ne', 1, by simpa [Units.ext_iff] using hx'.ne⟩
  · refine ⟨fun x y h => ?_⟩
    obtain ⟨z, hz⟩ := exists_between (Units.val_lt_val.mpr h)
    refine ⟨Units.mk0 z (

Depends on / 依赖: Units.ext_iff, Units.mk0, Units.val_lt_val, Units.val_lt_val.mpr, eq_zero_or_pos, exists_between, exists_one_lt, ext_iff, hx.ne, isUnit, ne_zero_of_lt, val_lt_val, zero_lt_one
-/
lemma denselyOrdered_iff_denselyOrdered_units_and_nontrivial_units :
    DenselyOrdered α ↔ Nontrivial αˣ ∧ DenselyOrdered αˣ := by
  refine ⟨fun H => ⟨?_, ?_⟩, fun ⟨H₁, H₂⟩ => ?_⟩
  · obtain ⟨x, hx, hx'⟩ := exists_between (zero_lt_one' α)
    exact ⟨Units.mk0 x hx.ne', 1, by simpa [Units.ext_iff] using hx'.ne⟩
  · refine ⟨fun x y h => ?_⟩
    obtain ⟨z, hz⟩ := exists_between (Units.val_lt_val.mpr h)
    refine ⟨Units.mk0 z (ne_zero_of_lt hz.1), by simp [← Units.val_lt_val, hz]⟩
  · refine ⟨fun x y h => ?_⟩
    lift y to αˣ using (ne_zero_of_lt h).isUnit
    obtain rfl | hx := eq_zero_or_pos x
    · obtain ⟨z, hz⟩ := exists_one_lt' (α := αˣ)
exact ⟨(y * z⁻¹ : αˣ), by simp, Units.val_lt_val.mpr by simp [hz]⟩
    · lift x to αˣ using hx.ne'.isUnit
      obtain ⟨z, hz, hz'⟩ := H₂.dense x y (Units.val_lt_val.mpr h)
      exact ⟨z, by simp [hz, hz']⟩

-- Counterexample with monoid: `{ x : ℝ | 0 ≤ x ≤ 1 }`
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DenselyOrdered
  signature: α] : Nontrivial αˣ
  body: by
  have := denselyOrdered_iff_denselyOrdered_units_and_nontrivial_units (α := α)
  tauto

中文:
实例 [DenselyOrdered
  签名: α] : Nontrivial αˣ
  定义体: by
  have := denselyOrdered_iff_denselyOrdered_units_and_nontrivial_units (α := α)
  tauto

Depends on / 依赖: denselyOrdered_iff_denselyOrdered_units_and_nontrivial_units
-/
instance [DenselyOrdered α] : Nontrivial αˣ := by
  have := denselyOrdered_iff_denselyOrdered_units_and_nontrivial_units (α := α)
  tauto

-- Counterexample with monoid:
-- `{ x : ℝ | x = 0 ∨ ∃ (a : ℤ) (b c : ℕ), x = Real.exp (a + b * √2 - c * √3) }`
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DenselyOrdered
  signature: α] : DenselyOrdered αˣ
  body: by
  have := denselyOrdered_iff_denselyOrdered_units_and_nontrivial_units (α := α)
  tauto

中文:
实例 [DenselyOrdered
  签名: α] : DenselyOrdered αˣ
  定义体: by
  have := denselyOrdered_iff_denselyOrdered_units_and_nontrivial_units (α := α)
  tauto

Depends on / 依赖: denselyOrdered_iff_denselyOrdered_units_and_nontrivial_units
-/
instance [DenselyOrdered α] : DenselyOrdered αˣ := by
  have := denselyOrdered_iff_denselyOrdered_units_and_nontrivial_units (α := α)
  tauto

/--
lemma `denselyOrdered_units_iff` / 引理 `denselyOrdered_units_iff`

English:
lemma denselyOrdered_units_iff
  given: [Nontrivial αˣ]
  statement: DenselyOrdered αˣ ↔ DenselyOrdered α
  proof: by
  have := denselyOrdered_iff_denselyOrdered_units_and_nontrivial_units (α := α)
  tauto

中文:
引理 denselyOrdered_units_iff
  条件: [Nontrivial αˣ]
  结论: DenselyOrdered αˣ ↔ DenselyOrdered α
  证明: by
  have := denselyOrdered_iff_denselyOrdered_units_and_nontrivial_units (α := α)
  tauto

Depends on / 依赖: denselyOrdered_iff_denselyOrdered_units_and_nontrivial_units
-/
lemma denselyOrdered_units_iff [Nontrivial αˣ] : DenselyOrdered αˣ ↔ DenselyOrdered α := by
  have := denselyOrdered_iff_denselyOrdered_units_and_nontrivial_units (α := α)
  tauto

end LinearOrderedCommGroupWithZero

/--
Instance `instLinearOrderedCommMonoidWithZeroMultiplicativeOrderDual` / 实例 `instLinearOrderedCommMonoidWithZeroMultiplicativeOrderDual`

English:
instance instLinearOrderedCommMonoidWithZeroMultiplicativeOrderDual
  body: .ofAdd .toDual ⊤
  zero_mul := @top_add _ (_)
  mul_zero := @add_top _ (_)
  isBot_zero _ := (le_top : _ <= ⊤)
  mul_lt_mul_of_pos_left := by
    simpa [← ofAdd_add, ← toDual_add]
      using! fun a ha b c hbc => add_right_strictMono_of_ne_top (by simpa using! ha.ne') hbc

@[simp]

中文:
实例 instLinearOrderedCommMonoidWithZeroMultiplicativeOrderDual
  定义体: .ofAdd .toDual ⊤
  zero_mul := @top_add _ (_)
  mul_zero := @add_top _ (_)
  isBot_zero _ := (le_top : _ <= ⊤)
  mul_lt_mul_of_pos_left := by
    simpa [← ofAdd_add, ← toDual_add]
      using! fun a ha b c hbc => add_right_strictMono_of_ne_top (by simpa using! ha.ne') hbc

@[simp]

Depends on / 依赖: toDual
-/
instance instLinearOrderedCommMonoidWithZeroMultiplicativeOrderDual
    [LinearOrderedAddCommMonoidWithTop α] :
    LinearOrderedCommMonoidWithZero (Multiplicative αᵒᵈ) where
zero := .ofAdd .toDual ⊤
  zero_mul := @top_add _ (_)
  mul_zero := @add_top _ (_)
  isBot_zero _ := (le_top : _ <= ⊤)
  mul_lt_mul_of_pos_left := by
    simpa [← ofAdd_add, ← toDual_add]
      using! fun a ha b c hbc => add_right_strictMono_of_ne_top (by simpa using! ha.ne') hbc

@[simp]
/--
theorem `ofDual_toAdd_zero` / 定理 `ofDual_toAdd_zero`

English:
theorem ofDual_toAdd_zero
  given: [LinearOrderedAddCommMonoidWithTop α]
  proof: rfl

中文:
定理 ofDual_toAdd_zero
  条件: [LinearOrderedAddCommMonoidWithTop α]
  证明: rfl
-/
theorem ofDual_toAdd_zero [LinearOrderedAddCommMonoidWithTop α] :
    OrderDual.ofDual (0 : Multiplicative αᵒᵈ).toAdd = ⊤ := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LinearOrderedAddCommGroupWithTop
  signature: α] :
  body: LinearOrderedAddCommGroupWithTop.neg_top (α := α)
  mul_inv_cancel := LinearOrderedAddCommGroupWithTop.add_neg_cancel_of_ne_top (α := α)

中文:
实例 [LinearOrderedAddCommGroupWithTop
  签名: α] :
  定义体: LinearOrderedAddCommGroupWithTop.neg_top (α := α)
  mul_inv_cancel := LinearOrderedAddCommGroupWithTop.add_neg_cancel_of_ne_top (α := α)

Depends on / 依赖: LinearOrderedAddCommGroupWithTop, LinearOrderedAddCommGroupWithTop.neg_top, neg_top
-/
instance [LinearOrderedAddCommGroupWithTop α] :
    LinearOrderedCommGroupWithZero (Multiplicative αᵒᵈ) where
  inv_zero := LinearOrderedAddCommGroupWithTop.neg_top (α := α)
  mul_inv_cancel := LinearOrderedAddCommGroupWithTop.add_neg_cancel_of_ne_top (α := α)

namespace WithZero

section Bot

/--
Instance `instBot` / 实例 `instBot`

English:
instance instBot
  signature: : Bot (WithZero α)
  body: ⟨none⟩

@[simp← ]

中文:
实例 instBot
  签名: : Bot (WithZero α)
  定义体: ⟨none⟩

@[simp← ]
-/
instance instBot : Bot (WithZero α) :=
  ⟨none⟩

@[simp← ]
/--
lemma `zero_eq_bot` / 引理 `zero_eq_bot`

English:
lemma zero_eq_bot
  statement: (0 : WithZero α) = ⊥
  proof: rfl

中文:
引理 zero_eq_bot
  结论: (0 : WithZero α) = ⊥
  证明: rfl
-/
lemma zero_eq_bot : (0 : WithZero α) = ⊥ := rfl

end Bot

section LE
variable [LE α] {x y : WithZero α} {a b : α}

instance (priority := 10) le : LE (WithZero α) := inferInstanceAs LE (WithBot α)

/--
lemma `le_def` / 引理 `le_def`

English:
lemma le_def
  statement: x <= y ↔ forall a : α, x = ↑a -> exists b : α, y = ↑b ∧ a <= b
  proof: WithBot.le_iff_forall

中文:
引理 le_def
  结论: x <= y ↔ 对任意 a : α, x = ↑a -> 存在 b : α, y = ↑b ∧ a <= b
  证明: WithBot.le_iff_forall

Depends on / 依赖: WithBot, WithBot.le_iff_forall, le_iff_forall
-/
lemma le_def : x <= y ↔ forall a : α, x = ↑a -> exists b : α, y = ↑b ∧ a <= b := WithBot.le_iff_forall

/--
lemma `coe_le_coe` / 引理 `coe_le_coe`

English:
lemma coe_le_coe
  statement: (a : WithZero α) <= b ↔ a <= b
  proof: WithBot.coe_le_coe

中文:
引理 coe_le_coe
  结论: (a : WithZero α) <= b ↔ a <= b
  证明: WithBot.coe_le_coe
-/
@[simp, norm_cast] lemma coe_le_coe : (a : WithZero α) <= b ↔ a <= b := WithBot.coe_le_coe

/--
lemma `not_coe_le_zero` / 引理 `not_coe_le_zero`

English:
lemma not_coe_le_zero
  given: (a : α)
  statement: ¬(a : WithZero α) <= 0
  proof: WithBot.not_coe_le_bot _

中文:
引理 not_coe_le_zero
  条件: (a : α)
  结论: ¬(a : WithZero α) <= 0
  证明: WithBot.not_coe_le_bot _

Depends on / 依赖: WithBot, WithBot.not_coe_le_bot, not_coe_le_bot
-/
lemma not_coe_le_zero (a : α) : ¬(a : WithZero α) <= 0 := WithBot.not_coe_le_bot _

/--
Instance `instOrderBot` / 实例 `instOrderBot`

English:
instance instOrderBot
  signature: : OrderBot (WithZero α)
  body: inferInstanceAs OrderBot (WithBot α)

中文:
实例 instOrderBot
  签名: : OrderBot (WithZero α)
  定义体: inferInstanceAs OrderBot (WithBot α)

Depends on / 依赖: OrderBot, WithBot
-/
instance instOrderBot : OrderBot (WithZero α) := inferInstanceAs OrderBot (WithBot α)

/--
Instance `instBoundedOrder` / 实例 `instBoundedOrder`

English:
instance instBoundedOrder
  signature: [OrderTop α]
  body: inferInstanceAs BoundedOrder (WithBot α)

中文:
实例 instBoundedOrder
  签名: [OrderTop α]
  定义体: inferInstanceAs BoundedOrder (WithBot α)

Depends on / 依赖: BoundedOrder, WithBot
-/
instance instBoundedOrder [OrderTop α] : BoundedOrder (WithZero α) :=
inferInstanceAs BoundedOrder (WithBot α)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsBotZeroClass (WithZero α)
  body: bot_le

@[deprecated _root_.zero_le (since := "2026-05-06")]

中文:
实例 :
  签名: IsBotZeroClass (WithZero α)
  定义体: bot_le

@[deprecated _root_.zero_le (since := "2026-05-06")]

Depends on / 依赖: bot_le
-/
instance : IsBotZeroClass (WithZero α) where
  isBot_zero _ := bot_le

@[deprecated _root_.zero_le (since := "2026-05-06")]
/--
lemma `zero_le` / 引理 `zero_le`

English:
lemma zero_le
  given: (a : WithZero α)
  statement: 0 <= a
  proof: by simp

中文:
引理 zero_le
  条件: (a : WithZero α)
  结论: 0 <= a
  证明: by simp
-/
protected lemma zero_le (a : WithZero α) : 0 <= a := by simp

/-- There is a general version `le_zero_iff`, but this lemma does not require a `PartialOrder`. -/
@[simp]
/--
lemma `nonpos_iff_eq_zero` / 引理 `nonpos_iff_eq_zero`

English:
lemma nonpos_iff_eq_zero
  statement: x <= 0 ↔ x = 0
  proof: WithBot.le_bot_iff

中文:
引理 nonpos_iff_eq_zero
  结论: x <= 0 ↔ x = 0
  证明: WithBot.le_bot_iff
-/
protected lemma nonpos_iff_eq_zero : x <= 0 ↔ x = 0 := WithBot.le_bot_iff

/--
lemma `coe_le_iff` / 引理 `coe_le_iff`

English:
lemma coe_le_iff
  statement: a <= x ↔ exists b : α, x = b ∧ a <= b
  proof: WithBot.coe_le_iff

中文:
引理 coe_le_iff
  结论: a <= x ↔ 存在 b : α, x = b ∧ a <= b
  证明: WithBot.coe_le_iff

Depends on / 依赖: WithBot, WithBot.coe_le_iff, coe_le_iff
-/
lemma coe_le_iff : a <= x ↔ exists b : α, x = b ∧ a <= b := WithBot.coe_le_iff
/--
lemma `le_coe_iff` / 引理 `le_coe_iff`

English:
lemma le_coe_iff
  statement: x <= b ↔ forall a : α, x = ↑a -> a <= b
  proof: WithBot.le_coe_iff

中文:
引理 le_coe_iff
  结论: x <= b ↔ 对任意 a : α, x = ↑a -> a <= b
  证明: WithBot.le_coe_iff

Depends on / 依赖: WithBot, WithBot.le_coe_iff, le_coe_iff
-/
lemma le_coe_iff : x <= b ↔ forall a : α, x = ↑a -> a <= b := WithBot.le_coe_iff

/--
lemma `_root_.IsMax.withZero` / 引理 `_root_.IsMax.withZero`

English:
lemma _root_.IsMax.withZero
  given: (h : IsMax a)
  statement: IsMax (a : WithZero α)
  proof: h.withBot

中文:
引理 _root_.IsMax.withZero
  条件: (h : IsMax a)
  结论: IsMax (a : WithZero α)
  证明: h.withBot
-/
protected lemma _root_.IsMax.withZero (h : IsMax a) : IsMax (a : WithZero α) := h.withBot

/--
lemma `le_unzero_iff` / 引理 `le_unzero_iff`

English:
lemma le_unzero_iff
  given: (hy : y != 0)
  statement: a <= unzero hy ↔ a <= y
  proof: WithBot.le_unbot_iff _

中文:
引理 le_unzero_iff
  条件: (hy : y != 0)
  结论: a <= unzero hy ↔ a <= y
  证明: WithBot.le_unbot_iff _

Depends on / 依赖: WithBot, WithBot.le_unbot_iff, le_unbot_iff
-/
lemma le_unzero_iff (hy : y != 0) : a <= unzero hy ↔ a <= y := WithBot.le_unbot_iff _
/--
lemma `unbot_le_iff` / 引理 `unbot_le_iff`

English:
lemma unbot_le_iff
  given: (hx : x != 0)
  statement: unzero hx <= b ↔ x <= b
  proof: WithBot.unbot_le_iff _

中文:
引理 unbot_le_iff
  条件: (hx : x != 0)
  结论: unzero hx <= b ↔ x <= b
  证明: WithBot.unbot_le_iff _

Depends on / 依赖: WithBot, WithBot.unbot_le_iff, unbot_le_iff
-/
lemma unbot_le_iff (hx : x != 0) : unzero hx <= b ↔ x <= b := WithBot.unbot_le_iff _

/--
lemma `one_le_coe` / 引理 `one_le_coe`

English:
lemma one_le_coe
  given: [One α]
  statement: 1 <= (a : WithZero α) ↔ 1 <= a
  proof: coe_le_coe

中文:
引理 one_le_coe
  条件: [One α]
  结论: 1 <= (a : WithZero α) ↔ 1 <= a
  证明: coe_le_coe
-/
@[simp, norm_cast] lemma one_le_coe [One α] : 1 <= (a : WithZero α) ↔ 1 <= a := coe_le_coe
/--
lemma `coe_le_one` / 引理 `coe_le_one`

English:
lemma coe_le_one
  given: [One α]
  statement: (a : WithZero α) <= 1 ↔ a <= 1
  proof: coe_le_coe

中文:
引理 coe_le_one
  条件: [One α]
  结论: (a : WithZero α) <= 1 ↔ a <= 1
  证明: coe_le_coe
-/
@[simp, norm_cast] lemma coe_le_one [One α] : (a : WithZero α) <= 1 ↔ a <= 1 := coe_le_coe

/--
lemma `unzero_le_unzero` / 引理 `unzero_le_unzero`

English:
lemma unzero_le_unzero
  given: (hx : x != 0) (hy : y != 0)
  statement: unzero hx <= unzero hy ↔ x <= y
  proof: WithBot.unbot_le_unbot_iff ..

中文:
引理 unzero_le_unzero
  条件: (hx : x != 0) (hy : y != 0)
  结论: unzero hx <= unzero hy ↔ x <= y
  证明: WithBot.unbot_le_unbot_iff ..
-/
@[simp] lemma unzero_le_unzero (hx : x != 0) (hy : y != 0) : unzero hx <= unzero hy ↔ x <= y :=
  WithBot.unbot_le_unbot_iff ..

end LE

section LT

variable [LT α] {x y : WithZero α} {a b : α}

/-- The order on `WithZero α`, defined by `⊥ < ↑a` and `a < b → ↑a < ↑b`. -/
instance (priority := 10) instLT : LT (WithZero α) := inferInstanceAs LT (WithBot α)

/--
lemma `lt_def` / 引理 `lt_def`

English:
lemma lt_def
  statement: x < y ↔ x = 0 ∧ (exists b : α, y = b) ∨ exists a b : α, a < b ∧ x = ↑a ∧ y = ↑b
  proof: WithBot.lt_def

中文:
引理 lt_def
  结论: x < y ↔ x = 0 ∧ (存在 b : α, y = b) ∨ 存在 a b : α, a < b ∧ x = ↑a ∧ y = ↑b
  证明: WithBot.lt_def

Depends on / 依赖: WithBot, WithBot.lt_def, lt_def
-/
lemma lt_def : x < y ↔ x = 0 ∧ (exists b : α, y = b) ∨ exists a b : α, a < b ∧ x = ↑a ∧ y = ↑b :=
  WithBot.lt_def

/--
lemma `lt_iff_exists` / 引理 `lt_iff_exists`

English:
lemma lt_iff_exists
  statement: x < y ↔ exists b : α, y = ↑b ∧ forall a : α, x = ↑a -> a < b
  proof: WithBot.lt_iff_exists

中文:
引理 lt_iff_exists
  结论: x < y ↔ 存在 b : α, y = ↑b ∧ 对任意 a : α, x = ↑a -> a < b
  证明: WithBot.lt_iff_exists

Depends on / 依赖: WithBot, WithBot.lt_iff_exists, lt_iff_exists
-/
lemma lt_iff_exists : x < y ↔ exists b : α, y = ↑b ∧ forall a : α, x = ↑a -> a < b := WithBot.lt_iff_exists

/--
lemma `coe_lt_coe` / 引理 `coe_lt_coe`

English:
lemma coe_lt_coe
  statement: (a : WithZero α) < b ↔ a < b
  proof: by simp [lt_def]

中文:
引理 coe_lt_coe
  结论: (a : WithZero α) < b ↔ a < b
  证明: by simp [lt_def]
-/
@[simp, norm_cast] lemma coe_lt_coe : (a : WithZero α) < b ↔ a < b := by simp [lt_def]
/--
lemma `zero_lt_coe` / 引理 `zero_lt_coe`

English:
lemma zero_lt_coe
  given: (a : α)
  statement: 0 < (a : WithZero α)
  proof: by simp [lt_def]

中文:
引理 zero_lt_coe
  条件: (a : α)
  结论: 0 < (a : WithZero α)
  证明: by simp [lt_def]
-/
@[simp] lemma zero_lt_coe (a : α) : 0 < (a : WithZero α) := by simp [lt_def]
/--
lemma `not_lt_zero` / 引理 `not_lt_zero`

English:
lemma not_lt_zero
  given: (a : WithZero α)
  statement: ¬a < 0
  proof: by simp [lt_def]

中文:
引理 not_lt_zero
  条件: (a : WithZero α)
  结论: ¬a < 0
  证明: by simp [lt_def]
-/
@[simp] protected lemma not_lt_zero (a : WithZero α) : ¬a < 0 := by simp [lt_def]

/--
lemma `lt_iff_exists_coe` / 引理 `lt_iff_exists_coe`

English:
lemma lt_iff_exists_coe
  statement: x < y ↔ exists b : α, y = b ∧ x < b
  proof: WithBot.lt_iff_exists_coe

中文:
引理 lt_iff_exists_coe
  结论: x < y ↔ 存在 b : α, y = b ∧ x < b
  证明: WithBot.lt_iff_exists_coe

Depends on / 依赖: WithBot, WithBot.lt_iff_exists_coe, lt_iff_exists_coe
-/
lemma lt_iff_exists_coe : x < y ↔ exists b : α, y = b ∧ x < b := WithBot.lt_iff_exists_coe

/--
lemma `lt_coe_iff` / 引理 `lt_coe_iff`

English:
lemma lt_coe_iff
  statement: x < b ↔ forall a : α, x = a -> a < b
  proof: WithBot.lt_coe_iff

中文:
引理 lt_coe_iff
  结论: x < b ↔ 对任意 a : α, x = a -> a < b
  证明: WithBot.lt_coe_iff

Depends on / 依赖: WithBot, WithBot.lt_coe_iff, lt_coe_iff
-/
lemma lt_coe_iff : x < b ↔ forall a : α, x = a -> a < b := WithBot.lt_coe_iff

/--
lemma `pos_iff_ne_zero` / 引理 `pos_iff_ne_zero`

English:
lemma pos_iff_ne_zero
  statement: 0 < x ↔ x != 0
  proof: WithBot.bot_lt_iff_ne_bot

中文:
引理 pos_iff_ne_zero
  结论: 0 < x ↔ x != 0
  证明: WithBot.bot_lt_iff_ne_bot
-/
protected lemma pos_iff_ne_zero : 0 < x ↔ x != 0 := WithBot.bot_lt_iff_ne_bot

/--
lemma `lt_unzero_iff` / 引理 `lt_unzero_iff`

English:
lemma lt_unzero_iff
  given: (hy : y != 0)
  statement: a < unzero hy ↔ a < y
  proof: WithBot.lt_unbot_iff _

中文:
引理 lt_unzero_iff
  条件: (hy : y != 0)
  结论: a < unzero hy ↔ a < y
  证明: WithBot.lt_unbot_iff _

Depends on / 依赖: WithBot, WithBot.lt_unbot_iff, lt_unbot_iff
-/
lemma lt_unzero_iff (hy : y != 0) : a < unzero hy ↔ a < y := WithBot.lt_unbot_iff _
/--
lemma `unzero_lt_iff` / 引理 `unzero_lt_iff`

English:
lemma unzero_lt_iff
  given: (hx : x != 0)
  statement: unzero hx < b ↔ x < b
  proof: WithBot.unbot_lt_iff _

中文:
引理 unzero_lt_iff
  条件: (hx : x != 0)
  结论: unzero hx < b ↔ x < b
  证明: WithBot.unbot_lt_iff _

Depends on / 依赖: WithBot, WithBot.unbot_lt_iff, unbot_lt_iff
-/
lemma unzero_lt_iff (hx : x != 0) : unzero hx < b ↔ x < b := WithBot.unbot_lt_iff _

/--
lemma `one_lt_coe` / 引理 `one_lt_coe`

English:
lemma one_lt_coe
  given: [One α]
  statement: 1 < (a : WithZero α) ↔ 1 < a
  proof: coe_lt_coe

中文:
引理 one_lt_coe
  条件: [One α]
  结论: 1 < (a : WithZero α) ↔ 1 < a
  证明: coe_lt_coe
-/
@[simp, norm_cast] lemma one_lt_coe [One α] : 1 < (a : WithZero α) ↔ 1 < a := coe_lt_coe
/--
lemma `coe_lt_one` / 引理 `coe_lt_one`

English:
lemma coe_lt_one
  given: [One α]
  statement: (a : WithZero α) < 1 ↔ a < 1
  proof: coe_lt_coe

中文:
引理 coe_lt_one
  条件: [One α]
  结论: (a : WithZero α) < 1 ↔ a < 1
  证明: coe_lt_coe
-/
@[simp, norm_cast] lemma coe_lt_one [One α] : (a : WithZero α) < 1 ↔ a < 1 := coe_lt_coe

end LT

section Preorder

variable [Preorder α] [Preorder β] {x y : WithZero α} {a b : α}

/--
Instance `instPreorder` / 实例 `instPreorder`

English:
instance instPreorder
  signature: : Preorder (WithZero α)
  body: inferInstanceAs Preorder (WithBot α)

中文:
实例 instPreorder
  签名: : Preorder (WithZero α)
  定义体: inferInstanceAs Preorder (WithBot α)

Depends on / 依赖: Preorder, WithBot
-/
instance instPreorder : Preorder (WithZero α) := inferInstanceAs Preorder (WithBot α)

/--
Instance `instMulLeftMono` / 实例 `instMulLeftMono`

English:
instance instMulLeftMono
  signature: [Mul α] [MulLeftMono α]
  body: by
  refine ⟨fun a b c hbc => ?_⟩
  induction a; · exact zero_le
  induction b; · exact zero_le
  rcases WithZero.coe_le_iff.1 hbc with ⟨c, rfl, hbc'⟩
  rw [← coe_mul _ c]; rw [← coe_mul]; rw [coe_le_coe]
  exact mul_le_mul_right hbc' _

中文:
实例 instMulLeftMono
  签名: [Mul α] [MulLeftMono α]
  定义体: by
  refine ⟨fun a b c hbc => ?_⟩
  induction a; · exact zero_le
  induction b; · exact zero_le
  rcases WithZero.coe_le_iff.1 hbc with ⟨c, rfl, hbc'⟩
  rw [← coe_mul _ c]; rw [← coe_mul]; rw [coe_le_coe]
  exact mul_le_mul_right hbc' _

Depends on / 依赖: WithZero, WithZero.coe_le_iff, coe_le_coe, coe_le_iff, coe_mul, mul_le_mul_right, zero_le
-/
instance instMulLeftMono [Mul α] [MulLeftMono α] :
    MulLeftMono (WithZero α) := by
  refine ⟨fun a b c hbc => ?_⟩
  induction a; · exact zero_le
  induction b; · exact zero_le
  rcases WithZero.coe_le_iff.1 hbc with ⟨c, rfl, hbc'⟩
  rw [← coe_mul _ c]; rw [← coe_mul]; rw [coe_le_coe]
  exact mul_le_mul_right hbc' _

/--
lemma `addLeftMono` / 引理 `addLeftMono`

English:
lemma addLeftMono
  statement: [AddZeroClass α] [AddLeftMono α]
  proof: by
  refine ⟨fun a b c hbc => ?_⟩
  induction a
  · rwa [zero_add, zero_add]
  induction b
  · rw [add_zero]
    induction c
    · rw [add_zero]
    · rw [← coe_add, coe_le_coe]
      exact le_add_of_nonneg_right (h _)
  · rcases WithZero.coe_le_iff.1 hbc with ⟨c, rfl, hbc'⟩
    rw [← coe_add]; rw [

中文:
引理 addLeftMono
  结论: [AddZeroClass α] [AddLeftMono α]
  证明: by
  refine ⟨fun a b c hbc => ?_⟩
  induction a
  · rwa [zero_add, zero_add]
  induction b
  · rw [add_zero]
    induction c
    · rw [add_zero]
    · rw [← coe_add, coe_le_coe]
      exact le_add_of_nonneg_right (h _)
  · rcases WithZero.coe_le_iff.1 hbc with ⟨c, rfl, hbc'⟩
    rw [← coe_add]; rw [
-/
protected lemma addLeftMono [AddZeroClass α] [AddLeftMono α]
    (h : forall a : α, 0 <= a) : AddLeftMono (WithZero α) := by
  refine ⟨fun a b c hbc => ?_⟩
  induction a
  · rwa [zero_add, zero_add]
  induction b
  · rw [add_zero]
    induction c
    · rw [add_zero]
    · rw [← coe_add, coe_le_coe]
      exact le_add_of_nonneg_right (h _)
  · rcases WithZero.coe_le_iff.1 hbc with ⟨c, rfl, hbc'⟩
    rw [← coe_add]; rw [← coe_add _ c]; rw [coe_le_coe]
    gcongr

/--
Instance `instExistsAddOfLE` / 实例 `instExistsAddOfLE`

English:
instance instExistsAddOfLE
  signature: [Add α] [ExistsAddOfLE α]
  body: by
    induction a
    · simp
    induction b
    · simp
    intro h
    obtain ⟨c, rfl⟩ := exists_add_of_le (WithZero.coe_le_coe.1 h)
    exact ⟨c, rfl⟩

中文:
实例 instExistsAddOfLE
  签名: [Add α] [ExistsAddOfLE α]
  定义体: by
    induction a
    · simp
    induction b
    · simp
    intro h
    obtain ⟨c, rfl⟩ := exists_add_of_le (WithZero.coe_le_coe.1 h)
    exact ⟨c, rfl⟩

Depends on / 依赖: WithZero, WithZero.coe_le_coe, coe_le_coe, exists_add_of_le
-/
instance instExistsAddOfLE [Add α] [ExistsAddOfLE α] : ExistsAddOfLE (WithZero α) where
  exists_add_of_le {a b} := by
    induction a
    · simp
    induction b
    · simp
    intro h
    obtain ⟨c, rfl⟩ := exists_add_of_le (WithZero.coe_le_coe.1 h)
    exact ⟨c, rfl⟩

/--
lemma `map'_mono` / 引理 `map'_mono`

English:
lemma map'_mono
  given: [MulOneClass α] [MulOneClass β] {f : α ->* β} (hf : Monotone f)
  proof: by simpa [Monotone, WithZero.forall]

中文:
引理 map'_mono
  条件: [MulOneClass α] [MulOneClass β] {f : α ->* β} (hf : Monotone f)
  证明: by simpa [Monotone, WithZero.forall]
-/
lemma map'_mono [MulOneClass α] [MulOneClass β] {f : α ->* β} (hf : Monotone f) :
    Monotone (map' f) := by simpa [Monotone, WithZero.forall]

/--
lemma `map'_strictMono` / 引理 `map'_strictMono`

English:
lemma map'_strictMono
  given: [MulOneClass α] [MulOneClass β] {f : α ->* β} (hf : StrictMono f)
  proof: by simpa [StrictMono, WithZero.forall]

中文:
引理 map'_strictMono
  条件: [MulOneClass α] [MulOneClass β] {f : α ->* β} (hf : StrictMono f)
  证明: by simpa [StrictMono, WithZero.forall]
-/
lemma map'_strictMono [MulOneClass α] [MulOneClass β] {f : α ->* β} (hf : StrictMono f) :
    StrictMono (map' f) := by simpa [StrictMono, WithZero.forall]

/--
theorem `exists_ne_zero_and_lt` / 定理 `exists_ne_zero_and_lt`

English:
theorem exists_ne_zero_and_lt
  given: [NoMinOrder α] (hx : x != 0)
  proof: by
  obtain ⟨z, hlt⟩ := exists_lt (WithZero.unzero hx)
  rw [← WithZero.coe_lt_coe]; rw [WithZero.coe_unzero hx] at hlt
  exact ⟨z, WithZero.coe_ne_zero, hlt⟩

中文:
定理 exists_ne_zero_and_lt
  条件: [NoMinOrder α] (hx : x != 0)
  证明: by
  obtain ⟨z, hlt⟩ := exists_lt (WithZero.unzero hx)
  rw [← WithZero.coe_lt_coe]; rw [WithZero.coe_unzero hx] at hlt
  exact ⟨z, WithZero.coe_ne_zero, hlt⟩

Depends on / 依赖: WithZero, WithZero.coe_lt_coe, WithZero.coe_ne_zero, WithZero.coe_unzero, WithZero.unzero, coe_lt_coe, coe_ne_zero, coe_unzero, exists_lt, unzero
-/
theorem exists_ne_zero_and_lt [NoMinOrder α] (hx : x != 0) :
    exists y, y != 0 ∧ y < x := by
  obtain ⟨z, hlt⟩ := exists_lt (WithZero.unzero hx)
  rw [← WithZero.coe_lt_coe]; rw [WithZero.coe_unzero hx] at hlt
  exact ⟨z, WithZero.coe_ne_zero, hlt⟩

section Multiplicative

open Multiplicative

/--
theorem `toAdd_unzero_lt_of_lt_ofAdd` / 定理 `toAdd_unzero_lt_of_lt_ofAdd`

English:
theorem toAdd_unzero_lt_of_lt_ofAdd
  proof: by
  rwa [← coe_unzero ha, coe_lt_coe, ← toAdd_lt, toAdd_ofAdd] at h

中文:
定理 toAdd_unzero_lt_of_lt_ofAdd
  证明: by
  rwa [← coe_unzero ha, coe_lt_coe, ← toAdd_lt, toAdd_ofAdd] at h

Depends on / 依赖: coe_lt_coe, coe_unzero, toAdd_lt, toAdd_ofAdd
-/
theorem toAdd_unzero_lt_of_lt_ofAdd
    {a : WithZero (Multiplicative α)} {b : α} (ha : a != 0) (h : a < ofAdd b) :
    toAdd (unzero ha) < b := by
  rwa [← coe_unzero ha, coe_lt_coe, ← toAdd_lt, toAdd_ofAdd] at h

/--
theorem `lt_ofAdd_of_toAdd_unzero_lt` / 定理 `lt_ofAdd_of_toAdd_unzero_lt`

English:
theorem lt_ofAdd_of_toAdd_unzero_lt
  proof: by
  rwa [← coe_unzero ha, coe_lt_coe, ← ofAdd_toAdd (unzero ha), ofAdd_lt]

中文:
定理 lt_ofAdd_of_toAdd_unzero_lt
  证明: by
  rwa [← coe_unzero ha, coe_lt_coe, ← ofAdd_toAdd (unzero ha), ofAdd_lt]

Depends on / 依赖: coe_lt_coe, coe_unzero, ofAdd_lt, ofAdd_toAdd, unzero
-/
theorem lt_ofAdd_of_toAdd_unzero_lt
    {a : WithZero (Multiplicative α)} {b : α} (ha : a != 0) (h : toAdd (unzero ha) < b) :
    a < ofAdd b := by
  rwa [← coe_unzero ha, coe_lt_coe, ← ofAdd_toAdd (unzero ha), ofAdd_lt]

/--
theorem `lt_ofAdd_iff` / 定理 `lt_ofAdd_iff`

English:
theorem lt_ofAdd_iff
  proof: ⟨toAdd_unzero_lt_of_lt_ofAdd ha, lt_ofAdd_of_toAdd_unzero_lt ha⟩

中文:
定理 lt_ofAdd_iff
  证明: ⟨toAdd_unzero_lt_of_lt_ofAdd ha, lt_ofAdd_of_toAdd_unzero_lt ha⟩

Depends on / 依赖: lt_ofAdd_of_toAdd_unzero_lt, toAdd_unzero_lt_of_lt_ofAdd
-/
theorem lt_ofAdd_iff
    {a : WithZero (Multiplicative α)} {b : α} (ha : a != 0) :
    a < ofAdd b ↔ toAdd (unzero ha) < b :=
  ⟨toAdd_unzero_lt_of_lt_ofAdd ha, lt_ofAdd_of_toAdd_unzero_lt ha⟩

/--
theorem `toAdd_unzero_le_of_lt_ofAdd` / 定理 `toAdd_unzero_le_of_lt_ofAdd`

English:
theorem toAdd_unzero_le_of_lt_ofAdd
  proof: by
  rwa [← coe_unzero ha, coe_le_coe, ← toAdd_le, toAdd_ofAdd] at h

中文:
定理 toAdd_unzero_le_of_lt_ofAdd
  证明: by
  rwa [← coe_unzero ha, coe_le_coe, ← toAdd_le, toAdd_ofAdd] at h

Depends on / 依赖: coe_le_coe, coe_unzero, toAdd_le, toAdd_ofAdd
-/
theorem toAdd_unzero_le_of_lt_ofAdd
    {a : WithZero (Multiplicative α)} {b : α} (ha : a != 0) (h : a <= ofAdd b) :
    toAdd (unzero ha) <= b := by
  rwa [← coe_unzero ha, coe_le_coe, ← toAdd_le, toAdd_ofAdd] at h

/--
theorem `le_ofAdd_of_toAdd_unzero_le` / 定理 `le_ofAdd_of_toAdd_unzero_le`

English:
theorem le_ofAdd_of_toAdd_unzero_le
  proof: by
  rwa [← coe_unzero ha, coe_le_coe, ← ofAdd_toAdd (unzero ha), ofAdd_le]

中文:
定理 le_ofAdd_of_toAdd_unzero_le
  证明: by
  rwa [← coe_unzero ha, coe_le_coe, ← ofAdd_toAdd (unzero ha), ofAdd_le]

Depends on / 依赖: coe_le_coe, coe_unzero, ofAdd_le, ofAdd_toAdd, unzero
-/
theorem le_ofAdd_of_toAdd_unzero_le
    {a : WithZero (Multiplicative α)} {b : α} (ha : a != 0) (h : toAdd (unzero ha) <= b) :
    a <= ofAdd b := by
  rwa [← coe_unzero ha, coe_le_coe, ← ofAdd_toAdd (unzero ha), ofAdd_le]

/--
theorem `le_ofAdd_iff` / 定理 `le_ofAdd_iff`

English:
theorem le_ofAdd_iff
  proof: ⟨toAdd_unzero_le_of_lt_ofAdd ha, le_ofAdd_of_toAdd_unzero_le ha⟩

中文:
定理 le_ofAdd_iff
  证明: ⟨toAdd_unzero_le_of_lt_ofAdd ha, le_ofAdd_of_toAdd_unzero_le ha⟩

Depends on / 依赖: le_ofAdd_of_toAdd_unzero_le, toAdd_unzero_le_of_lt_ofAdd
-/
theorem le_ofAdd_iff
    {a : WithZero (Multiplicative α)} {b : α} (ha : a != 0) :
    a <= ofAdd b ↔ toAdd (unzero ha) <= b :=
  ⟨toAdd_unzero_le_of_lt_ofAdd ha, le_ofAdd_of_toAdd_unzero_le ha⟩

/--
lemma `toAdd_unzero_eq_iff` / 引理 `toAdd_unzero_eq_iff`

English:
lemma toAdd_unzero_eq_iff
  statement: {α : Type*} {a : WithZero (Multiplicative α)} (h : a != 0)
  proof: ⟨fun k => by subst k; exact (coe_unzero h).symm, fun k => by subst k; rfl⟩

中文:
引理 toAdd_unzero_eq_iff
  结论: {α : 类型} {a : WithZero (Multiplicative α)} (h : a != 0)
  证明: ⟨fun k => by subst k; exact (coe_unzero h).symm, fun k => by subst k; rfl⟩

Depends on / 依赖: coe_unzero
-/
lemma toAdd_unzero_eq_iff {α : Type*} {a : WithZero (Multiplicative α)} (h : a != 0)
    (b : α) : (WithZero.unzero h).toAdd = b ↔ a = Multiplicative.ofAdd b :=
  ⟨fun k => by subst k; exact (coe_unzero h).symm, fun k => by subst k; rfl⟩

end Multiplicative

end Preorder

section PartialOrder
variable [PartialOrder α]

/--
Instance `instPartialOrder` / 实例 `instPartialOrder`

English:
instance instPartialOrder
  signature: : PartialOrder (WithZero α)
  body: inferInstanceAs PartialOrder (WithBot α)

中文:
实例 instPartialOrder
  签名: : PartialOrder (WithZero α)
  定义体: inferInstanceAs PartialOrder (WithBot α)

Depends on / 依赖: PartialOrder, WithBot
-/
instance instPartialOrder : PartialOrder (WithZero α) :=
inferInstanceAs PartialOrder (WithBot α)

/--
Instance `instMulLeftReflectLT` / 实例 `instMulLeftReflectLT`

English:
instance instMulLeftReflectLT
  signature: [Mul α] [MulLeftReflectLT α]
  body: by
  refine ⟨fun a b c h => ?_⟩
  have := h.ne_zero
  induction a
  · simp at this
  induction c
  · simp at this
  induction b
  exacts [zero_lt_coe _, coe_lt_coe.mpr (lt_of_mul_lt_mul_left' <| coe_lt_coe.mp h)]

中文:
实例 instMulLeftReflectLT
  签名: [Mul α] [MulLeftReflectLT α]
  定义体: by
  refine ⟨fun a b c h => ?_⟩
  have := h.ne_zero
  induction a
  · simp at this
  induction c
  · simp at this
  induction b
  exacts [zero_lt_coe _, coe_lt_coe.mpr (lt_of_mul_lt_mul_left' <| coe_lt_coe.mp h)]

Depends on / 依赖: coe_lt_coe, coe_lt_coe.mp, coe_lt_coe.mpr, exacts, h.ne_zero, lt_of_mul_lt_mul_left, ne_zero, zero_lt_coe
-/
instance instMulLeftReflectLT [Mul α] [MulLeftReflectLT α] :
    MulLeftReflectLT (WithZero α) := by
  refine ⟨fun a b c h => ?_⟩
  have := h.ne_zero
  induction a
  · simp at this
  induction c
  · simp at this
  induction b
  exacts [zero_lt_coe _, coe_lt_coe.mpr (lt_of_mul_lt_mul_left' <| coe_lt_coe.mp h)]

end PartialOrder


section Lattice

/--
Instance `semilatticeSup` / 实例 `semilatticeSup`

English:
instance semilatticeSup
  signature: [SemilatticeSup α]
  body: by cases x <;> cases y <;> simp
  le_sup_right x y := by cases x <;> cases y <;> simp
  sup_le x y z := by cases x <;> cases y <;> cases z <;> simp; simpa using sup_le

中文:
实例 semilatticeSup
  签名: [SemilatticeSup α]
  定义体: by cases x <;> cases y <;> simp
  le_sup_right x y := by cases x <;> cases y <;> simp
  sup_le x y z := by cases x <;> cases y <;> cases z <;> simp; simpa using sup_le

Depends on / 依赖: le_sup_right, sup_le
-/
instance semilatticeSup [SemilatticeSup α] : SemilatticeSup (WithZero α) where
  sup
    -- note this is `Option.merge`, but with the right defeq when unfolding
    | 0, 0 => 0
    | (a : α), 0 => a
    | 0, (b : α) => b
    | (a : α), (b : α) => ↑(a ⊔ b)
  le_sup_left x y := by cases x <;> cases y <;> simp
  le_sup_right x y := by cases x <;> cases y <;> simp
  sup_le x y z := by cases x <;> cases y <;> cases z <;> simp; simpa using sup_le

/--
theorem `coe_sup` / 定理 `coe_sup`

English:
theorem coe_sup
  given: [SemilatticeSup α] (a b : α)
  statement: ((a ⊔ b : α) : WithZero α) = (a : WithZero α) ⊔ b
  proof: rfl

中文:
定理 coe_sup
  条件: [SemilatticeSup α] (a b : α)
  结论: ((a ⊔ b : α) : WithZero α) = (a : WithZero α) ⊔ b
  证明: rfl
-/
theorem coe_sup [SemilatticeSup α] (a b : α) : ((a ⊔ b : α) : WithZero α) = (a : WithZero α) ⊔ b :=
  rfl

/--
Instance `semilatticeInf` / 实例 `semilatticeInf`

English:
instance semilatticeInf
  signature: [SemilatticeInf α]
  body: .map₂ (· ⊓ ·)
  inf_le_left x y := by cases x <;> cases y <;> simp
  inf_le_right x y := by cases x <;> cases y <;> simp
  le_inf x y z := by cases x <;> cases y <;> cases z <;> simp; simpa using le_inf

中文:
实例 semilatticeInf
  签名: [SemilatticeInf α]
  定义体: .map₂ (· ⊓ ·)
  inf_le_left x y := by cases x <;> cases y <;> simp
  inf_le_right x y := by cases x <;> cases y <;> simp
  le_inf x y z := by cases x <;> cases y <;> cases z <;> simp; simpa using le_inf
-/
instance semilatticeInf [SemilatticeInf α] : SemilatticeInf (WithZero α) where
  inf := .map₂ (· ⊓ ·)
  inf_le_left x y := by cases x <;> cases y <;> simp
  inf_le_right x y := by cases x <;> cases y <;> simp
  le_inf x y z := by cases x <;> cases y <;> cases z <;> simp; simpa using le_inf

/--
theorem `coe_inf` / 定理 `coe_inf`

English:
theorem coe_inf
  given: [SemilatticeInf α] (a b : α)
  statement: ((a ⊓ b : α) : WithZero α) = (a : WithZero α) ⊓ b
  proof: rfl

中文:
定理 coe_inf
  条件: [SemilatticeInf α] (a b : α)
  结论: ((a ⊓ b : α) : WithZero α) = (a : WithZero α) ⊓ b
  证明: rfl
-/
theorem coe_inf [SemilatticeInf α] (a b : α) : ((a ⊓ b : α) : WithZero α) = (a : WithZero α) ⊓ b :=
  rfl

/--
Instance `instLattice` / 实例 `instLattice`

English:
instance instLattice
  signature: [Lattice α]

中文:
实例 instLattice
  签名: [Lattice α]
-/
instance instLattice [Lattice α] : Lattice (WithZero α) where

end Lattice

/--
Instance `decidableEq` / 实例 `decidableEq`

English:
instance decidableEq
  signature: [DecidableEq α]
  body: inferInstanceAs DecidableEq (Option α)

中文:
实例 decidableEq
  签名: [DecidableEq α]
  定义体: inferInstanceAs DecidableEq (Option α)

Depends on / 依赖: DecidableEq
-/
instance decidableEq [DecidableEq α] : DecidableEq (WithZero α) :=
inferInstanceAs DecidableEq (Option α)

/--
Instance `decidableLE` / 实例 `decidableLE`

English:
instance decidableLE
  signature: [Preorder α] [DecidableLE α]

中文:
实例 decidableLE
  签名: [Preorder α] [DecidableLE α]
-/
instance decidableLE [Preorder α] [DecidableLE α] : DecidableLE (WithZero α)
| 0, _ => isTrue by simp
| (a : α), 0 => isFalse by simp
  | (a : α), (b : α) => decidable_of_iff' _ coe_le_coe

/--
Instance `decidableLT` / 实例 `decidableLT`

English:
instance decidableLT
  signature: [Preorder α] [DecidableLT α]

中文:
实例 decidableLT
  签名: [Preorder α] [DecidableLT α]
-/
instance decidableLT [Preorder α] [DecidableLT α] : DecidableLT (WithZero α)
| _, 0 => isFalse by simp
| 0, (a : α) => isTrue by simp
  | (a : α), (b : α) => decidable_of_iff' _ coe_lt_coe

/--
Instance `total_le` / 实例 `total_le`

English:
instance total_le
  signature: [Preorder α] [@Std.Total α (· <= ·)]
  body: by cases x <;> cases y <;> simp; simpa using Std.Total.total ..

中文:
实例 total_le
  签名: [Preorder α] [@Std.Total α (· <= ·)]
  定义体: by cases x <;> cases y <;> simp; simpa using Std.Total.total ..

Depends on / 依赖: Std.Total.total
-/
instance total_le [Preorder α] [@Std.Total α (· <= ·)] : @Std.Total (WithZero α) (· <= ·) where
  total x y := by cases x <;> cases y <;> simp; simpa using Std.Total.total ..

section LinearOrder
variable [LinearOrder α] {a b c : α} {x y : WithZero α}

/--
Instance `instLinearOrder` / 实例 `instLinearOrder`

English:
instance instLinearOrder
  signature: : LinearOrder (WithZero α)
  body: Lattice.toLinearOrder _

中文:
实例 instLinearOrder
  签名: : LinearOrder (WithZero α)
  定义体: Lattice.toLinearOrder _

Depends on / 依赖: Lattice, Lattice.toLinearOrder, toLinearOrder
-/
instance instLinearOrder : LinearOrder (WithZero α) := Lattice.toLinearOrder _

/--
lemma `le_max_iff` / 引理 `le_max_iff`

English:
lemma le_max_iff
  statement: (a : WithZero α) <= max (b : WithZero α) c ↔ a <= max b c
  proof: by
  simp only [WithZero.coe_le_coe, le_max_iff]

中文:
引理 le_max_iff
  结论: (a : WithZero α) <= max (b : WithZero α) c ↔ a <= max b c
  证明: by
  simp only [WithZero.coe_le_coe, le_max_iff]
-/
protected lemma le_max_iff : (a : WithZero α) <= max (b : WithZero α) c ↔ a <= max b c := by
  simp only [WithZero.coe_le_coe, le_max_iff]

/--
lemma `min_le_iff` / 引理 `min_le_iff`

English:
lemma min_le_iff
  statement: min (a : WithZero α) b <= c ↔ min a b <= c
  proof: by
  simp only [WithZero.coe_le_coe, min_le_iff]

中文:
引理 min_le_iff
  结论: min (a : WithZero α) b <= c ↔ min a b <= c
  证明: by
  simp only [WithZero.coe_le_coe, min_le_iff]
-/
protected lemma min_le_iff : min (a : WithZero α) b <= c ↔ min a b <= c := by
  simp only [WithZero.coe_le_coe, min_le_iff]

/--
theorem `exists_ne_zero_and_le_and_le` / 定理 `exists_ne_zero_and_le_and_le`

English:
theorem exists_ne_zero_and_le_and_le
  given: (hx : x != 0) (hy : y != 0)
  proof: ⟨x ⊓ y, by simp [min_eq_iff, hx, hy], by simp, by simp⟩

中文:
定理 exists_ne_zero_and_le_and_le
  条件: (hx : x != 0) (hy : y != 0)
  证明: ⟨x ⊓ y, by simp [min_eq_iff, hx, hy], by simp, by simp⟩

Depends on / 依赖: min_eq_iff
-/
theorem exists_ne_zero_and_le_and_le (hx : x != 0) (hy : y != 0) :
    exists z, z != 0 ∧ z <= x ∧ z <= y :=
  ⟨x ⊓ y, by simp [min_eq_iff, hx, hy], by simp, by simp⟩

/--
theorem `exists_ne_zero_and_lt_and_lt` / 定理 `exists_ne_zero_and_lt_and_lt`

English:
theorem exists_ne_zero_and_lt_and_lt
  given: [NoMinOrder α] (hx : x != 0) (hy : y != 0)
  proof: by
  obtain ⟨z', hnz', hzx, hzy⟩ := exists_ne_zero_and_le_and_le hx hy
  obtain ⟨z, hnz, hlt⟩ := exists_ne_zero_and_lt hnz'
  use z, hnz
  constructor <;> exact lt_of_lt_of_le hlt ‹z' <= _›

中文:
定理 exists_ne_zero_and_lt_and_lt
  条件: [NoMinOrder α] (hx : x != 0) (hy : y != 0)
  证明: by
  obtain ⟨z', hnz', hzx, hzy⟩ := exists_ne_zero_and_le_and_le hx hy
  obtain ⟨z, hnz, hlt⟩ := exists_ne_zero_and_lt hnz'
  use z, hnz
  constructor <;> exact lt_of_lt_of_le hlt ‹z' <= _›

Depends on / 依赖: exists_ne_zero_and_le_and_le, exists_ne_zero_and_lt, lt_of_lt_of_le
-/
theorem exists_ne_zero_and_lt_and_lt [NoMinOrder α] (hx : x != 0) (hy : y != 0) :
    exists z, z != 0 ∧ z < x ∧ z < y := by
  obtain ⟨z', hnz', hzx, hzy⟩ := exists_ne_zero_and_le_and_le hx hy
  obtain ⟨z, hnz, hlt⟩ := exists_ne_zero_and_lt hnz'
  use z, hnz
  constructor <;> exact lt_of_lt_of_le hlt ‹z' <= _›

end LinearOrder

/--
Instance `isOrderedMonoid` / 实例 `isOrderedMonoid`

English:
instance isOrderedMonoid
  signature: [CommMonoid α] [Preorder α] [IsOrderedMonoid α]
  body: mul_le_mul_left

中文:
实例 isOrderedMonoid
  签名: [CommMonoid α] [Preorder α] [IsOrderedMonoid α]
  定义体: mul_le_mul_left

Depends on / 依赖: mul_le_mul_left
-/
instance isOrderedMonoid [CommMonoid α] [Preorder α] [IsOrderedMonoid α] :
    IsOrderedMonoid (WithZero α) where
  mul_le_mul_left _ _ := mul_le_mul_left

/-
Note 1 : the below is not an instance because it requires `zero_le`. It seems
like a rather pathological definition because α already has a zero.
Note 2 : there is no multiplicative analogue because it does not seem necessary.
Mathematicians might be more likely to use the order-dual version, where all
elements are ≤ 1 and then 1 is the top element.
-/
-- See note [reducible non-instances]
/--
lemma `isOrderedAddMonoid` / 引理 `isOrderedAddMonoid`

English:
lemma isOrderedAddMonoid
  statement: [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α]
  proof: by
  have := WithZero.addLeftMono zero_le
  exact ⟨fun _ _ => add_le_add_left, by simpa [add_comm] using fun _ _ => add_le_add_left⟩

中文:
引理 isOrderedAddMonoid
  结论: [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α]
  证明: by
  have := WithZero.addLeftMono zero_le
  exact ⟨fun _ _ => add_le_add_left, by simpa [add_comm] using fun _ _ => add_le_add_left⟩
-/
protected lemma isOrderedAddMonoid [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α]
    (zero_le : forall a : α, 0 <= a) :
    IsOrderedAddMonoid (WithZero α) := by
  have := WithZero.addLeftMono zero_le
  exact ⟨fun _ _ => add_le_add_left, by simpa [add_comm] using fun _ _ => add_le_add_left⟩

/--
Instance `instCanonicallyOrderedAdd` / 实例 `instCanonicallyOrderedAdd`

English:
instance instCanonicallyOrderedAdd
  signature: [AddZeroClass α] [Preorder α] [CanonicallyOrderedAdd α]

中文:
实例 instCanonicallyOrderedAdd
  签名: [AddZeroClass α] [Preorder α] [CanonicallyOrderedAdd α]
-/
instance instCanonicallyOrderedAdd [AddZeroClass α] [Preorder α] [CanonicallyOrderedAdd α] :
    CanonicallyOrderedAdd (WithZero α) where
  le_add_self
  | 0, _ => bot_le
  | (a : α), 0 => le_rfl
  | (a : α), (b : α) => WithZero.coe_le_coe.2 le_add_self
  le_self_add
  | 0, _ => bot_le
  | (a : α), 0 => le_rfl
  | (a : α), (b : α) => WithZero.coe_le_coe.2 le_self_add

/--
Instance `instLinearOrderedCommMonoidWithZero` / 实例 `instLinearOrderedCommMonoidWithZero`

English:
instance instLinearOrderedCommMonoidWithZero
  signature: [CommMonoid α] [LinearOrder α]
  body: zero_le
  mul_lt_mul_of_pos_left
  | (a : α), _, 0, (c : α), _ => by simp [← WithZero.coe_mul]
  | (a : α), _, (b : α), (c : α), hbc => by norm_cast at *; exact mul_lt_mul_right hbc _

中文:
实例 instLinearOrderedCommMonoidWithZero
  签名: [CommMonoid α] [LinearOrder α]
  定义体: zero_le
  mul_lt_mul_of_pos_left
  | (a : α), _, 0, (c : α), _ => by simp [← WithZero.coe_mul]
  | (a : α), _, (b : α), (c : α), hbc => by norm_cast at *; exact mul_lt_mul_right hbc _

Depends on / 依赖: zero_le
-/
instance instLinearOrderedCommMonoidWithZero [CommMonoid α] [LinearOrder α]
    [IsOrderedCancelMonoid α] : LinearOrderedCommMonoidWithZero (WithZero α) where
  isBot_zero _ := zero_le
  mul_lt_mul_of_pos_left
  | (a : α), _, 0, (c : α), _ => by simp [← WithZero.coe_mul]
  | (a : α), _, (b : α), (c : α), hbc => by norm_cast at *; exact mul_lt_mul_right hbc _

/--
Instance `instLinearOrderedCommGroupWithZero` / 实例 `instLinearOrderedCommGroupWithZero`

English:
instance instLinearOrderedCommGroupWithZero
  signature: [CommGroup α] [LinearOrder α] [IsOrderedMonoid α]

中文:
实例 instLinearOrderedCommGroupWithZero
  签名: [CommGroup α] [LinearOrder α] [IsOrderedMonoid α]
-/
instance instLinearOrderedCommGroupWithZero [CommGroup α] [LinearOrder α] [IsOrderedMonoid α] :
    LinearOrderedCommGroupWithZero (WithZero α) where

-- Add a shortcut instance for the common case, to speed up unification.
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LinearOrderedCommGroupWithZero Intᵐ⁰
  body: inferInstance

中文:
实例 :
  签名: LinearOrderedCommGroupWithZero 整数ᵐ⁰
  定义体: inferInstance
-/
instance : LinearOrderedCommGroupWithZero Intᵐ⁰ := inferInstance

/-! ### Exponential and logarithm -/

variable {G : Type*} [Preorder G] {a b : G}

/--
lemma `exp_le_exp` / 引理 `exp_le_exp`

English:
lemma exp_le_exp
  statement: exp a <= exp b ↔ a <= b
  proof: by simp [exp]

中文:
引理 exp_le_exp
  结论: exp a <= exp b ↔ a <= b
  证明: by simp [exp]
-/
@[simp] lemma exp_le_exp : exp a <= exp b ↔ a <= b := by simp [exp]
/--
lemma `exp_lt_exp` / 引理 `exp_lt_exp`

English:
lemma exp_lt_exp
  statement: exp a < exp b ↔ a < b
  proof: by simp [exp]

中文:
引理 exp_lt_exp
  结论: exp a < exp b ↔ a < b
  证明: by simp [exp]
-/
@[simp] lemma exp_lt_exp : exp a < exp b ↔ a < b := by simp [exp]

/--
lemma `exp_pos` / 引理 `exp_pos`

English:
lemma exp_pos
  statement: 0 < exp a
  proof: by simp [exp]

中文:
引理 exp_pos
  结论: 0 < exp a
  证明: by simp [exp]
-/
@[simp] lemma exp_pos : 0 < exp a := by simp [exp]

variable [AddGroup G] {x y : Gᵐ⁰}

/--
lemma `log_le_iff_le_exp` / 引理 `log_le_iff_le_exp`

English:
lemma log_le_iff_le_exp
  given: (hx : x != 0)
  statement: log x <= a ↔ x <= exp a
  proof: by
  rw [← toAdd_unzero_eq_log hx]; rw [← le_ofAdd_iff hx]; rw [exp]

中文:
引理 log_le_iff_le_exp
  条件: (hx : x != 0)
  结论: log x <= a ↔ x <= exp a
  证明: by
  rw [← toAdd_unzero_eq_log hx]; rw [← le_ofAdd_iff hx]; rw [exp]

Depends on / 依赖: le_ofAdd_iff, toAdd_unzero_eq_log
-/
lemma log_le_iff_le_exp (hx : x != 0) : log x <= a ↔ x <= exp a := by
  rw [← toAdd_unzero_eq_log hx]; rw [← le_ofAdd_iff hx]; rw [exp]

/--
lemma `log_lt_iff_lt_exp` / 引理 `log_lt_iff_lt_exp`

English:
lemma log_lt_iff_lt_exp
  given: (hx : x != 0)
  statement: log x < a ↔ x < exp a
  proof: by
  rw [← toAdd_unzero_eq_log hx]; rw [← lt_ofAdd_iff hx]; rw [exp]

中文:
引理 log_lt_iff_lt_exp
  条件: (hx : x != 0)
  结论: log x < a ↔ x < exp a
  证明: by
  rw [← toAdd_unzero_eq_log hx]; rw [← lt_ofAdd_iff hx]; rw [exp]

Depends on / 依赖: lt_ofAdd_iff, toAdd_unzero_eq_log
-/
lemma log_lt_iff_lt_exp (hx : x != 0) : log x < a ↔ x < exp a := by
  rw [← toAdd_unzero_eq_log hx]; rw [← lt_ofAdd_iff hx]; rw [exp]

/--
lemma `log_le_log` / 引理 `log_le_log`

English:
lemma log_le_log
  given: (hx : x != 0) (hy : y != 0)
  statement: log x <= log y ↔ x <= y
  proof: by
  rw [log_le_iff_le_exp hx]; rw [exp_log hy]

中文:
引理 log_le_log
  条件: (hx : x != 0) (hy : y != 0)
  结论: log x <= log y ↔ x <= y
  证明: by
  rw [log_le_iff_le_exp hx]; rw [exp_log hy]
-/
@[simp] lemma log_le_log (hx : x != 0) (hy : y != 0) : log x <= log y ↔ x <= y := by
  rw [log_le_iff_le_exp hx]; rw [exp_log hy]

/--
lemma `log_lt_log` / 引理 `log_lt_log`

English:
lemma log_lt_log
  given: (hx : x != 0) (hy : y != 0)
  statement: log x < log y ↔ x < y
  proof: by
  rw [log_lt_iff_lt_exp hx]; rw [exp_log hy]

中文:
引理 log_lt_log
  条件: (hx : x != 0) (hy : y != 0)
  结论: log x < log y ↔ x < y
  证明: by
  rw [log_lt_iff_lt_exp hx]; rw [exp_log hy]
-/
@[simp] lemma log_lt_log (hx : x != 0) (hy : y != 0) : log x < log y ↔ x < y := by
  rw [log_lt_iff_lt_exp hx]; rw [exp_log hy]

/--
lemma `le_log_iff_exp_le` / 引理 `le_log_iff_exp_le`

English:
lemma le_log_iff_exp_le
  given: (hx : x != 0)
  statement: a <= log x ↔ exp a <= x
  proof: by
  rw [← log_le_log exp_ne_zero hx]; rw [log_exp]

中文:
引理 le_log_iff_exp_le
  条件: (hx : x != 0)
  结论: a <= log x ↔ exp a <= x
  证明: by
  rw [← log_le_log exp_ne_zero hx]; rw [log_exp]

Depends on / 依赖: exp_ne_zero, log_exp, log_le_log
-/
lemma le_log_iff_exp_le (hx : x != 0) : a <= log x ↔ exp a <= x := by
  rw [← log_le_log exp_ne_zero hx]; rw [log_exp]

/--
lemma `lt_log_iff_exp_lt` / 引理 `lt_log_iff_exp_lt`

English:
lemma lt_log_iff_exp_lt
  given: (hx : x != 0)
  statement: a < log x ↔ exp a < x
  proof: by
  rw [← log_lt_log exp_ne_zero hx]; rw [log_exp]

中文:
引理 lt_log_iff_exp_lt
  条件: (hx : x != 0)
  结论: a < log x ↔ exp a < x
  证明: by
  rw [← log_lt_log exp_ne_zero hx]; rw [log_exp]

Depends on / 依赖: exp_ne_zero, log_exp, log_lt_log
-/
lemma lt_log_iff_exp_lt (hx : x != 0) : a < log x ↔ exp a < x := by
  rw [← log_lt_log exp_ne_zero hx]; rw [log_exp]

/--
lemma `le_exp_of_log_le` / 引理 `le_exp_of_log_le`

English:
lemma le_exp_of_log_le
  given: (hxa : log x <= a)
  statement: x <= exp a
  proof: by
  obtain rfl | hx := eq_or_ne x 0 <;> simp [← log_le_iff_le_exp, *]

中文:
引理 le_exp_of_log_le
  条件: (hxa : log x <= a)
  结论: x <= exp a
  证明: by
  obtain rfl | hx := eq_or_ne x 0 <;> simp [← log_le_iff_le_exp, *]

Depends on / 依赖: eq_or_ne, log_le_iff_le_exp
-/
lemma le_exp_of_log_le (hxa : log x <= a) : x <= exp a := by
  obtain rfl | hx := eq_or_ne x 0 <;> simp [← log_le_iff_le_exp, *]

/--
lemma `lt_exp_of_log_lt` / 引理 `lt_exp_of_log_lt`

English:
lemma lt_exp_of_log_lt
  given: (hxa : log x < a)
  statement: x < exp a
  proof: by
  obtain rfl | hx := eq_or_ne x 0 <;> simp [← log_lt_iff_lt_exp, *]

中文:
引理 lt_exp_of_log_lt
  条件: (hxa : log x < a)
  结论: x < exp a
  证明: by
  obtain rfl | hx := eq_or_ne x 0 <;> simp [← log_lt_iff_lt_exp, *]

Depends on / 依赖: eq_or_ne, log_lt_iff_lt_exp
-/
lemma lt_exp_of_log_lt (hxa : log x < a) : x < exp a := by
  obtain rfl | hx := eq_or_ne x 0 <;> simp [← log_lt_iff_lt_exp, *]

/--
lemma `le_log_of_exp_le` / 引理 `le_log_of_exp_le`

English:
lemma le_log_of_exp_le
  given: (hax : exp a <= x)
  statement: a <= log x
  proof: (le_log_iff_exp_le (exp_pos.trans_le hax).ne').2 hax

中文:
引理 le_log_of_exp_le
  条件: (hax : exp a <= x)
  结论: a <= log x
  证明: (le_log_iff_exp_le (exp_pos.trans_le hax).ne').2 hax

Depends on / 依赖: exp_pos, exp_pos.trans_le, le_log_iff_exp_le, trans_le
-/
lemma le_log_of_exp_le (hax : exp a <= x) : a <= log x :=
  (le_log_iff_exp_le (exp_pos.trans_le hax).ne').2 hax

/--
lemma `lt_log_of_exp_lt` / 引理 `lt_log_of_exp_lt`

English:
lemma lt_log_of_exp_lt
  given: (hax : exp a < x)
  statement: a < log x
  proof: (lt_log_iff_exp_lt (exp_pos.trans hax).ne').2 hax

中文:
引理 lt_log_of_exp_lt
  条件: (hax : exp a < x)
  结论: a < log x
  证明: (lt_log_iff_exp_lt (exp_pos.trans hax).ne').2 hax

Depends on / 依赖: exp_pos, exp_pos.trans, lt_log_iff_exp_lt
-/
lemma lt_log_of_exp_lt (hax : exp a < x) : a < log x :=
  (lt_log_iff_exp_lt (exp_pos.trans hax).ne').2 hax

/--
Definition of `expOrderIso` / `expOrderIso` 的定义

English:
definition expOrderIso
  signature: : G ≃o Gᵐ⁰ˣ where
  body: expEquiv
  map_rel_iff' := by simp [← Units.val_le_val]

中文:
定义 expOrderIso
  签名: : G ≃o Gᵐ⁰ˣ where
  定义体: expEquiv
  map_rel_iff' := by simp [← Units.val_le_val]
-/
@[simps! -isSimp] def expOrderIso : G ≃o Gᵐ⁰ˣ where
  __ := expEquiv
  map_rel_iff' := by simp [← Units.val_le_val]

/--
Definition of `logOrderIso` / `logOrderIso` 的定义

English:
definition logOrderIso
  signature: : Gᵐ⁰ˣ ≃o G where
  body: logEquiv
  map_rel_iff' := by simp

中文:
定义 logOrderIso
  签名: : Gᵐ⁰ˣ ≃o G where
  定义体: logEquiv
  map_rel_iff' := by simp
-/
@[simps! -isSimp] def logOrderIso : Gᵐ⁰ˣ ≃o G where
  __ := logEquiv
  map_rel_iff' := by simp

/--
lemma `lt_mul_exp_iff_le` / 引理 `lt_mul_exp_iff_le`

English:
lemma lt_mul_exp_iff_le
  given: {x y : Intᵐ⁰} (hy : y != 0)
  statement: x < y * exp 1 ↔ x <= y
  proof: by
  lift y to Multiplicative Int using hy
  obtain rfl | hx := eq_or_ne x 0
  · simp
  lift x to Multiplicative Int using hx
  rw [← log_le_log]; rw [← log_lt_log] <;> simp [log_mul, Int.lt_add_one_iff]

中文:
引理 lt_mul_exp_iff_le
  条件: {x y : 整数ᵐ⁰} (hy : y != 0)
  结论: x < y * exp 1 ↔ x <= y
  证明: by
  lift y to Multiplicative Int using hy
  obtain rfl | hx := eq_or_ne x 0
  · simp
  lift x to Multiplicative Int using hx
  rw [← log_le_log]; rw [← log_lt_log] <;> simp [log_mul, Int.lt_add_one_iff]

Depends on / 依赖: Int.lt_add_one_iff, Multiplicative, eq_or_ne, log_le_log, log_lt_log, log_mul, lt_add_one_iff
-/
lemma lt_mul_exp_iff_le {x y : Intᵐ⁰} (hy : y != 0) : x < y * exp 1 ↔ x <= y := by
  lift y to Multiplicative Int using hy
  obtain rfl | hx := eq_or_ne x 0
  · simp
  lift x to Multiplicative Int using hx
  rw [← log_le_log]; rw [← log_lt_log] <;> simp [log_mul, Int.lt_add_one_iff]

/--
lemma `exists_exp_neg_natCast_lt` / 引理 `exists_exp_neg_natCast_lt`

English:
lemma exists_exp_neg_natCast_lt
  given: {x : Intᵐ⁰} (hx : x != 0)
  proof: by
  obtain ⟨y, hnz, hyx⟩ := WithZero.exists_ne_zero_and_lt hx
  use (-y.log).toNat
  apply lt_of_le_of_lt _ hyx
  rw [← WithZero.le_log_iff_exp_le hnz]; rw [Int.neg_le_iff]
  exact Int.self_le_toNat _

中文:
引理 exists_exp_neg_natCast_lt
  条件: {x : 整数ᵐ⁰} (hx : x != 0)
  证明: by
  obtain ⟨y, hnz, hyx⟩ := WithZero.exists_ne_zero_and_lt hx
  use (-y.log).toNat
  apply lt_of_le_of_lt _ hyx
  rw [← WithZero.le_log_iff_exp_le hnz]; rw [Int.neg_le_iff]
  exact Int.self_le_toNat _

Depends on / 依赖: Int.neg_le_iff, Int.self_le_toNat, WithZero, WithZero.exists_ne_zero_and_lt, WithZero.le_log_iff_exp_le, exists_ne_zero_and_lt, le_log_iff_exp_le, lt_of_le_of_lt, neg_le_iff, self_le_toNat, y.log
-/
lemma exists_exp_neg_natCast_lt {x : Intᵐ⁰} (hx : x != 0) :
    exists (k : Nat), exp (-(k : Int)) < x := by
  obtain ⟨y, hnz, hyx⟩ := WithZero.exists_ne_zero_and_lt hx
  use (-y.log).toNat
  apply lt_of_le_of_lt _ hyx
  rw [← WithZero.le_log_iff_exp_le hnz]; rw [Int.neg_le_iff]
  exact Int.self_le_toNat _

/--
lemma `exists_exp_neg_natCast_lt_and_lt` / 引理 `exists_exp_neg_natCast_lt_and_lt`

English:
lemma exists_exp_neg_natCast_lt_and_lt
  given: {x y : Intᵐ⁰} (hx : x != 0) (hy : y != 0)
  proof: by
  obtain ⟨z, hz, hzx, hzy⟩ := WithZero.exists_ne_zero_and_le_and_le hx hy
  obtain ⟨k, hk⟩ := exists_exp_neg_natCast_lt hz
  grind

中文:
引理 exists_exp_neg_natCast_lt_and_lt
  条件: {x y : 整数ᵐ⁰} (hx : x != 0) (hy : y != 0)
  证明: by
  obtain ⟨z, hz, hzx, hzy⟩ := WithZero.exists_ne_zero_and_le_and_le hx hy
  obtain ⟨k, hk⟩ := exists_exp_neg_natCast_lt hz
  grind

Depends on / 依赖: WithZero, WithZero.exists_ne_zero_and_le_and_le, exists_exp_neg_natCast_lt, exists_ne_zero_and_le_and_le
-/
lemma exists_exp_neg_natCast_lt_and_lt {x y : Intᵐ⁰} (hx : x != 0) (hy : y != 0) :
    exists (k : Nat), exp (-(k : Int)) < x ∧ exp (-(k : Int)) < y := by
  obtain ⟨z, hz, hzx, hzy⟩ := WithZero.exists_ne_zero_and_le_and_le hx hy
  obtain ⟨k, hk⟩ := exists_exp_neg_natCast_lt hz
  grind

/--
lemma `le_exp_log` / 引理 `le_exp_log`

English:
lemma le_exp_log
  given: {x : Gᵐ⁰}
  proof: by
  cases x
  · simp
  · rfl

中文:
引理 le_exp_log
  条件: {x : Gᵐ⁰}
  证明: by
  cases x
  · simp
  · rfl
-/
lemma le_exp_log {x : Gᵐ⁰} :
    x <= exp (log x) := by
  cases x
  · simp
  · rfl

section LE

-- This section is not generated by `to_additive` because `WithOne` does not have a `LE` instance.

variable [LE α] {x y : WithZero α} {a b : α}

/--
lemma `le_unzeroD_iff` / 引理 `le_unzeroD_iff`

English:
lemma le_unzeroD_iff
  given: (hx : x != 0)
  statement: b <= x.unzeroD a ↔ b <= x
  proof: by
  lift x to α using hx; simp

中文:
引理 le_unzeroD_iff
  条件: (hx : x != 0)
  结论: b <= x.unzeroD a ↔ b <= x
  证明: by
  lift x to α using hx; simp
-/
lemma le_unzeroD_iff (hx : x != 0) : b <= x.unzeroD a ↔ b <= x := by
  lift x to α using hx; simp

/--
lemma `unzeroD_le_iff` / 引理 `unzeroD_le_iff`

English:
lemma unzeroD_le_iff
  given: (hx : x = 0 -> a <= b)
  statement: x.unzeroD a <= b ↔ x <= b
  proof: by
  cases x <;> simp [hx]

中文:
引理 unzeroD_le_iff
  条件: (hx : x = 0 -> a <= b)
  结论: x.unzeroD a <= b ↔ x <= b
  证明: by
  cases x <;> simp [hx]
-/
lemma unzeroD_le_iff (hx : x = 0 -> a <= b) : x.unzeroD a <= b ↔ x <= b := by
  cases x <;> simp [hx]

/--
lemma `unzeroD_mono` / 引理 `unzeroD_mono`

English:
lemma unzeroD_mono
  given: (hx : x != 0) (h : x <= y)
  statement: x.unzeroD a <= y.unzeroD a
  proof: by
  lift x to α using hx
  cases y <;> simp_all

中文:
引理 unzeroD_mono
  条件: (hx : x != 0) (h : x <= y)
  结论: x.unzeroD a <= y.unzeroD a
  证明: by
  lift x to α using hx
  cases y <;> simp_all
-/
lemma unzeroD_mono (hx : x != 0) (h : x <= y) : x.unzeroD a <= y.unzeroD a := by
  lift x to α using hx
  cases y <;> simp_all

end LE

section LT

variable [LT α] {x y : WithZero α} {a b : α}

/--
lemma `lt_unzeroD_iff` / 引理 `lt_unzeroD_iff`

English:
lemma lt_unzeroD_iff
  given: (hx : x != 0)
  statement: b < x.unzeroD a ↔ b < x
  proof: by
  lift x to α using hx; simp

中文:
引理 lt_unzeroD_iff
  条件: (hx : x != 0)
  结论: b < x.unzeroD a ↔ b < x
  证明: by
  lift x to α using hx; simp
-/
lemma lt_unzeroD_iff (hx : x != 0) : b < x.unzeroD a ↔ b < x := by
  lift x to α using hx; simp

/--
lemma `unzeroD_lt_iff` / 引理 `unzeroD_lt_iff`

English:
lemma unzeroD_lt_iff
  given: (hx : x = 0 -> a < b)
  statement: x.unzeroD a < b ↔ x < b
  proof: by
  cases x <;> simp [hx]

中文:
引理 unzeroD_lt_iff
  条件: (hx : x = 0 -> a < b)
  结论: x.unzeroD a < b ↔ x < b
  证明: by
  cases x <;> simp [hx]
-/
lemma unzeroD_lt_iff (hx : x = 0 -> a < b) : x.unzeroD a < b ↔ x < b := by
  cases x <;> simp [hx]

end LT

section Preorder

variable [Preorder α] {x y : WithZero α} {a b : α}

/--
theorem `le_coe_unzeroD` / 定理 `le_coe_unzeroD`

English:
theorem le_coe_unzeroD
  given: (x : WithZero α) (b : α)
  statement: x <= x.unzeroD b
  proof: by cases x <;> simp

中文:
定理 le_coe_unzeroD
  条件: (x : WithZero α) (b : α)
  结论: x <= x.unzeroD b
  证明: by cases x <;> simp
-/
theorem le_coe_unzeroD (x : WithZero α) (b : α) : x <= x.unzeroD b := by cases x <;> simp

end Preorder

section PartialOrder

variable [PartialOrder α] {x y : WithZero α} {a b : α}

/--
lemma `le_unzeroD` / 引理 `le_unzeroD`

English:
lemma le_unzeroD
  given: (hy : b <= y)
  statement: b <= y.unzeroD a
  proof: by
  have hne : y != 0 := ne_bot_of_le_ne_bot WithZero.coe_ne_zero hy
  rwa [le_unzeroD_iff hne]

中文:
引理 le_unzeroD
  条件: (hy : b <= y)
  结论: b <= y.unzeroD a
  证明: by
  have hne : y != 0 := ne_bot_of_le_ne_bot WithZero.coe_ne_zero hy
  rwa [le_unzeroD_iff hne]

Depends on / 依赖: WithZero, WithZero.coe_ne_zero, coe_ne_zero, le_unzeroD_iff, ne_bot_of_le_ne_bot
-/
lemma le_unzeroD (hy : b <= y) : b <= y.unzeroD a := by
  have hne : y != 0 := ne_bot_of_le_ne_bot WithZero.coe_ne_zero hy
  rwa [le_unzeroD_iff hne]

end PartialOrder

end WithZero
