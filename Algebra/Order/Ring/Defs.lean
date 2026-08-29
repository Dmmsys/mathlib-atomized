/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Yaël Dillies, Yuyang Zhao
-/
module

public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Monoid.NatCast
public import Mathlib.Algebra.Order.Monoid.Unbundled.MinMax
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.GrindInstances
public import Mathlib.Tactic.Tauto
public import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE

/-!
# Ordered rings and semirings

This file develops the basics of ordered (semi)rings.

Each typeclass here comprises
* an algebraic class (`Semiring`, `CommSemiring`, `Ring`, `CommRing`)
* an order class (`PartialOrder`, `LinearOrder`)
* assumptions on how both interact ((strict) monotonicity, canonicity)

For short,
* "`+` respects `≤`" means "monotonicity of addition"
* "`+` respects `<`" means "strict monotonicity of addition"
* "`*` respects `≤`" means "monotonicity of multiplication by a nonnegative number".
* "`*` respects `<`" means "strict monotonicity of multiplication by a positive number".

## Typeclasses

* `IsOrderedRing`: Semiring with a partial order such that addition and multiplication by a
  nonnegative number are both monotone.
* `IsStrictOrderedRing`: Nontrivial semiring with a partial order such that addition and
  multiplication by a positive number are both strictly monotone.

## Hierarchy

The hardest part of proving order lemmas might be to figure out the correct generality and its
corresponding typeclass. Here's an attempt at demystifying it. For each typeclass, we list its
immediate predecessors and what conditions are added to each of them.

* `PartialOrder` + `Semiring` + `IsOrderedRing`
  - `IsOrderedAddMonoid` & multiplication & `*` respects `≤`
* `PartialOrder` + `Semiring` + `IsStrictOrderedRing`
  - `IsOrderedCancelAddMonoid` & multiplication & `*` respects `<` & nontriviality
* `LinearOrder` + `Ring` + `IsOrderedRing`
  - `IsStrictOrderedRing` & totality of the order
  - `IsDomain` & linear order structure
-/

public section

assert_not_exists MonoidHom

open Function

universe u

variable {R : Type u}

-- TODO: assume weaker typeclasses

/--
Definition of `IsOrderedRing` / `IsOrderedRing` 的定义

English:
class IsOrderedRing
  parameters: (R : Type*) [Semiring R] [PartialOrder R]
  (no additional axioms)

中文:
类 是Ordered环
  参数: (R : 类型) [半环 R] [偏序 R]
  (无附加公理)
-/
class IsOrderedRing (R : Type*) [Semiring R] [PartialOrder R] extends
    IsOrderedAddMonoid R, ZeroLEOneClass R, PosMulMono R, MulPosMono R where

-- See note [lower instance priority]
attribute [instance 100] IsOrderedRing.toZeroLEOneClass
attribute [instance 200] IsOrderedRing.toPosMulMono
attribute [instance 200] IsOrderedRing.toMulPosMono

/--
Definition of `IsStrictOrderedRing` / `IsStrictOrderedRing` 的定义

English:
class IsStrictOrderedRing
  parameters: (R : Type*) [Semiring R] [PartialOrder R]
  (no additional axioms)

中文:
类 是StrictOrdered环
  参数: (R : 类型) [半环 R] [偏序 R]
  (无附加公理)
-/
class IsStrictOrderedRing (R : Type*) [Semiring R] [PartialOrder R] extends
    IsOrderedCancelAddMonoid R, ZeroLEOneClass R, Nontrivial R, PosMulStrictMono R,
    MulPosStrictMono R where

-- See note [lower instance priority]
attribute [instance 100] IsStrictOrderedRing.toZeroLEOneClass
attribute [instance 100] IsStrictOrderedRing.toNontrivial
attribute [instance 200] IsStrictOrderedRing.toPosMulStrictMono
attribute [instance 200] IsStrictOrderedRing.toMulPosStrictMono

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semiring
  signature: R] [PartialOrder R] [IsStrictOrderedRing R] : Lean.Grind.OrderedRing R where
  body: zero_lt_one
  mul_lt_mul_of_pos_left := mul_lt_mul_of_pos_left
  mul_lt_mul_of_pos_right := mul_lt_mul_of_pos_right

中文:
实例 [半环
  签名: R] [偏序 R] [是StrictOrdered环 R] : Lean.Grind.OrderedRing R where
  定义体: zero_lt_one
  mul_lt_mul_of_pos_left := mul_lt_mul_of_pos_left
  mul_lt_mul_of_pos_right := mul_lt_mul_of_pos_right

Depends on / 依赖: zero_lt_one
-/
instance [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] : Lean.Grind.OrderedRing R where
  zero_lt_one := zero_lt_one
  mul_lt_mul_of_pos_left := mul_lt_mul_of_pos_left
  mul_lt_mul_of_pos_right := mul_lt_mul_of_pos_right

/--
lemma `IsOrderedRing.of_mul_nonneg` / 引理 `IsOrderedRing.of_mul_nonneg`

English:
lemma IsOrderedRing.of_mul_nonneg
  statement: [Ring R] [PartialOrder R] [IsOrderedAddMonoid R]
  proof: by
    simpa only [mul_sub, sub_nonneg] using mul_nonneg _ _ ha (sub_nonneg.2 hbc)
  mul_le_mul_of_nonneg_right a ha b c hbc := by
    simpa only [sub_mul, sub_nonneg] using mul_nonneg _ _ (sub_nonneg.2 hbc) ha

中文:
引理 是Ordered环.of_mul_nonneg
  结论: [环 R] [偏序 R] [是OrderedAdd幺半群 R]
  证明: by
    simpa only [mul_sub, sub_nonneg] using mul_nonneg _ _ ha (sub_nonneg.2 hbc)
  mul_le_mul_of_nonneg_right a ha b c hbc := by
    simpa only [sub_mul, sub_nonneg] using mul_nonneg _ _ (sub_nonneg.2 hbc) ha

Depends on / 依赖: mul_le_mul_of_nonneg_right, mul_nonneg, mul_sub, sub_mul, sub_nonneg
-/
lemma IsOrderedRing.of_mul_nonneg [Ring R] [PartialOrder R] [IsOrderedAddMonoid R]
    [ZeroLEOneClass R] (mul_nonneg : forall a b : R, 0 <= a -> 0 <= b -> 0 <= a * b) :
    IsOrderedRing R where
  mul_le_mul_of_nonneg_left a ha b c hbc := by
    simpa only [mul_sub, sub_nonneg] using mul_nonneg _ _ ha (sub_nonneg.2 hbc)
  mul_le_mul_of_nonneg_right a ha b c hbc := by
    simpa only [sub_mul, sub_nonneg] using mul_nonneg _ _ (sub_nonneg.2 hbc) ha

/--
lemma `IsStrictOrderedRing.of_mul_pos` / 引理 `IsStrictOrderedRing.of_mul_pos`

English:
lemma IsStrictOrderedRing.of_mul_pos
  statement: [Ring R] [PartialOrder R] [IsOrderedAddMonoid R]
  proof: by
    simpa only [mul_sub, sub_pos] using mul_pos _ _ ha (sub_pos.2 hbc)
  mul_lt_mul_of_pos_right a ha b c hbc := by
    simpa only [sub_mul, sub_pos] using mul_pos _ _ (sub_pos.2 hbc) ha

中文:
引理 是StrictOrdered环.of_mul_pos
  结论: [环 R] [偏序 R] [是OrderedAdd幺半群 R]
  证明: by
    simpa only [mul_sub, sub_pos] using mul_pos _ _ ha (sub_pos.2 hbc)
  mul_lt_mul_of_pos_right a ha b c hbc := by
    simpa only [sub_mul, sub_pos] using mul_pos _ _ (sub_pos.2 hbc) ha

Depends on / 依赖: mul_lt_mul_of_pos_right, mul_pos, mul_sub, sub_mul, sub_pos
-/
lemma IsStrictOrderedRing.of_mul_pos [Ring R] [PartialOrder R] [IsOrderedAddMonoid R]
    [ZeroLEOneClass R] [Nontrivial R] (mul_pos : forall a b : R, 0 < a -> 0 < b -> 0 < a * b) :
    IsStrictOrderedRing R where
  mul_lt_mul_of_pos_left a ha b c hbc := by
    simpa only [mul_sub, sub_pos] using mul_pos _ _ ha (sub_pos.2 hbc)
  mul_lt_mul_of_pos_right a ha b c hbc := by
    simpa only [sub_mul, sub_pos] using mul_pos _ _ (sub_pos.2 hbc) ha

-- see Note [lower instance priority]
/-- Turn an ordered domain into a strict ordered ring. -/
instance (priority := 50) IsOrderedRing.toIsStrictOrderedRing (R : Type*)
    [Ring R] [PartialOrder R] [IsOrderedRing R] [NoZeroDivisors R] [Nontrivial R] :
    IsStrictOrderedRing R :=
  .of_mul_pos fun _ _ ap bp => (mul_nonneg ap.le bp.le).lt_of_ne' (mul_ne_zero ap.ne' bp.ne')

section IsStrictOrderedRing
variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]

-- see Note [lower instance priority]
instance (priority := 100) IsStrictOrderedRing.toIsOrderedRing : IsOrderedRing R where
  __ := ‹IsStrictOrderedRing R›

/--
theorem `AddMonoidWithOne.toCharZero` / 定理 `AddMonoidWithOne.toCharZero`

English:
theorem AddMonoidWithOne.toCharZero
  statement: {R}
  proof: (strictMono_nat_of_lt_succ fun n => by rw [Nat.cast_succ]; apply lt_add_one).injective

中文:
定理 加法带幺幺半群.toCharZero
  结论: {R}
  证明: (strictMono_nat_of_lt_succ fun n => by rw [Nat.cast_succ]; apply lt_add_one).injective

Depends on / 依赖: Nat.cast_succ, cast_succ, injective, lt_add_one, strictMono_nat_of_lt_succ
-/
theorem AddMonoidWithOne.toCharZero {R}
    [AddMonoidWithOne R] [PartialOrder R] [ZeroLEOneClass R]
    [NeZero (1 : R)] [AddLeftStrictMono R] : CharZero R where
  cast_injective :=
    (strictMono_nat_of_lt_succ fun n => by rw [Nat.cast_succ]; apply lt_add_one).injective

-- see Note [lower instance priority]
instance (priority := 100) IsStrictOrderedRing.toCharZero :
    CharZero R := AddMonoidWithOne.toCharZero

-- see Note [lower instance priority]
instance (priority := 100) IsStrictOrderedRing.toNoMaxOrder : NoMaxOrder R :=
  ⟨fun a => ⟨a + 1, lt_add_of_pos_right _ one_pos⟩⟩

end IsStrictOrderedRing

section LinearOrder

variable [Semiring R] [LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R]

-- See note [lower instance priority]
instance (priority := 100) IsStrictOrderedRing.noZeroDivisors : NoZeroDivisors R where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} hab := by
    contrapose! hab
    obtain ha | ha := hab.1.lt_or_gt <;> obtain hb | hb := hab.2.lt_or_gt
    exacts [(mul_pos_of_neg_of_neg ha hb).ne', (mul_neg_of_neg_of_pos ha hb).ne,
      (mul_neg_of_pos_of_neg ha hb).ne, (mul_pos ha hb).ne']

-- Note that we can't use `NoZeroDivisors.to_isDomain` since we are merely in a semiring.
-- See note [lower instance priority]
instance (priority := 100) IsStrictOrderedRing.isDomain : IsDomain R where
  mul_left_cancel_of_ne_zero {a} ha _ _ h := by
    obtain ha | ha := ha.lt_or_gt
    exacts [(strictAnti_mul_left ha).injective h, (strictMono_mul_left_of_pos ha).injective h]
  mul_right_cancel_of_ne_zero {a} ha _ _ h := by
    obtain ha | ha := ha.lt_or_gt
    exacts [(strictAnti_mul_right ha).injective h, (strictMono_mul_right_of_pos ha).injective h]

end LinearOrder

/-! Note that `OrderDual` does not satisfy any of the ordered ring typeclasses due to the
`zero_le_one` field. -/

section OrderedRing

variable [Ring R] [PartialOrder R] [IsOrderedRing R] {a b c : R}

/--
lemma `one_add_le_one_sub_mul_one_add` / 引理 `one_add_le_one_sub_mul_one_add`

English:
lemma one_add_le_one_sub_mul_one_add
  given: (h : a + b + b * c <= c)
  statement: 1 + a <= (1 - b) * (1 + c)
  proof: by
  rw [one_sub_mul]; rw [mul_one_add]; rw [le_sub_iff_add_le]; rw [add_assoc]; rw [← add_assoc a]
  gcongr

中文:
引理 one_add_le_one_sub_mul_one_add
  条件: (h : a + b + b * c <= c)
  结论: 1 + a <= (1 - b) * (1 + c)
  证明: by
  rw [one_sub_mul]; rw [mul_one_add]; rw [le_sub_iff_add_le]; rw [add_assoc]; rw [← add_assoc a]
  gcongr

Depends on / 依赖: add_assoc, le_sub_iff_add_le, mul_one_add, one_sub_mul
-/
lemma one_add_le_one_sub_mul_one_add (h : a + b + b * c <= c) : 1 + a <= (1 - b) * (1 + c) := by
  rw [one_sub_mul]; rw [mul_one_add]; rw [le_sub_iff_add_le]; rw [add_assoc]; rw [← add_assoc a]
  gcongr

/--
lemma `one_add_le_one_add_mul_one_sub` / 引理 `one_add_le_one_add_mul_one_sub`

English:
lemma one_add_le_one_add_mul_one_sub
  given: (h : a + c + b * c <= b)
  statement: 1 + a <= (1 + b) * (1 - c)
  proof: by
  rw [mul_one_sub]; rw [one_add_mul]; rw [le_sub_iff_add_le]; rw [add_assoc]; rw [← add_assoc a]
  gcongr

中文:
引理 one_add_le_one_add_mul_one_sub
  条件: (h : a + c + b * c <= b)
  结论: 1 + a <= (1 + b) * (1 - c)
  证明: by
  rw [mul_one_sub]; rw [one_add_mul]; rw [le_sub_iff_add_le]; rw [add_assoc]; rw [← add_assoc a]
  gcongr

Depends on / 依赖: add_assoc, le_sub_iff_add_le, mul_one_sub, one_add_mul
-/
lemma one_add_le_one_add_mul_one_sub (h : a + c + b * c <= b) : 1 + a <= (1 + b) * (1 - c) := by
  rw [mul_one_sub]; rw [one_add_mul]; rw [le_sub_iff_add_le]; rw [add_assoc]; rw [← add_assoc a]
  gcongr

/--
lemma `one_sub_le_one_sub_mul_one_add` / 引理 `one_sub_le_one_sub_mul_one_add`

English:
lemma one_sub_le_one_sub_mul_one_add
  given: (h : b + b * c <= a + c)
  statement: 1 - a <= (1 - b) * (1 + c)
  proof: by
  rw [one_sub_mul]; rw [mul_one_add]; rw [sub_le_sub_iff]; rw [add_assoc]; rw [add_comm c]
  gcongr

中文:
引理 one_sub_le_one_sub_mul_one_add
  条件: (h : b + b * c <= a + c)
  结论: 1 - a <= (1 - b) * (1 + c)
  证明: by
  rw [one_sub_mul]; rw [mul_one_add]; rw [sub_le_sub_iff]; rw [add_assoc]; rw [add_comm c]
  gcongr

Depends on / 依赖: add_assoc, add_comm, mul_one_add, one_sub_mul, sub_le_sub_iff
-/
lemma one_sub_le_one_sub_mul_one_add (h : b + b * c <= a + c) : 1 - a <= (1 - b) * (1 + c) := by
  rw [one_sub_mul]; rw [mul_one_add]; rw [sub_le_sub_iff]; rw [add_assoc]; rw [add_comm c]
  gcongr

/--
lemma `one_sub_le_one_add_mul_one_sub` / 引理 `one_sub_le_one_add_mul_one_sub`

English:
lemma one_sub_le_one_add_mul_one_sub
  given: (h : c + b * c <= a + b)
  statement: 1 - a <= (1 + b) * (1 - c)
  proof: by
  rw [mul_one_sub]; rw [one_add_mul]; rw [sub_le_sub_iff]; rw [add_assoc]; rw [add_comm b]
  gcongr

中文:
引理 one_sub_le_one_add_mul_one_sub
  条件: (h : c + b * c <= a + b)
  结论: 1 - a <= (1 + b) * (1 - c)
  证明: by
  rw [mul_one_sub]; rw [one_add_mul]; rw [sub_le_sub_iff]; rw [add_assoc]; rw [add_comm b]
  gcongr

Depends on / 依赖: add_assoc, add_comm, mul_one_sub, one_add_mul, sub_le_sub_iff
-/
lemma one_sub_le_one_add_mul_one_sub (h : c + b * c <= a + b) : 1 - a <= (1 + b) * (1 - c) := by
  rw [mul_one_sub]; rw [one_add_mul]; rw [sub_le_sub_iff]; rw [add_assoc]; rw [add_comm b]
  gcongr

/--
theorem `IsOrderedRing.toCharZero` / 定理 `IsOrderedRing.toCharZero`

English:
theorem IsOrderedRing.toCharZero
  given: [Nontrivial R]
  statement: CharZero R
  proof: AddMonoidWithOne.toCharZero

中文:
定理 是Ordered环.toCharZero
  条件: [非平凡 R]
  结论: 特征零 R
  证明: AddMonoidWithOne.toCharZero

Depends on / 依赖: AddMonoidWithOne, AddMonoidWithOne.toCharZero, toCharZero
-/
theorem IsOrderedRing.toCharZero [Nontrivial R] : CharZero R := AddMonoidWithOne.toCharZero

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: R] : NoMaxOrder R
  body: ⟨fun a => ⟨a + 1, by simp⟩⟩

中文:
实例 [非平凡
  签名: R] : NoMax序 R
  定义体: ⟨fun a => ⟨a + 1, by simp⟩⟩
-/
instance [Nontrivial R] : NoMaxOrder R := ⟨fun a => ⟨a + 1, by simp⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: R] : NoMinOrder R
  body: ⟨fun a => ⟨a - 1, by simp⟩⟩

中文:
实例 [非平凡
  签名: R] : NoMin序 R
  定义体: ⟨fun a => ⟨a - 1, by simp⟩⟩
-/
instance [Nontrivial R] : NoMinOrder R := ⟨fun a => ⟨a - 1, by simp⟩⟩

end OrderedRing
