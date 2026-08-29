/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Logic.Nontrivial.Defs
public import Mathlib.Logic.Basic
public import Batteries.Tactic.SeqFocus

/-!
# Typeclasses for groups with an adjoined zero element

This file provides just the typeclass definitions, and the projection lemmas that expose their
members.

## Main definitions

* `GroupWithZero`
* `CommGroupWithZero`
-/

public section

assert_not_exists DenselyOrdered Ring

universe u

-- We have to fix the universe of `G₀` here, since the default argument to
-- `GroupWithZero.div'` cannot contain a universe metavariable.
variable {G₀ : Type u} {M₀ : Type*}

/--
Definition of `MulZeroClass` / `MulZeroClass` 的定义

English:
class MulZeroClass
  parameters: (M₀ : Type u)
  extends: Mul M₀, Zero M₀
  axioms and operations (2):
    - zero_mul : forall a : M₀, 0 * a = 0
    - mul_zero : forall a : M₀, a * 0 = 0

中文:
类 MulZeroClass
  参数: (M₀ : 类型u)
  继承: Mul M₀, Zero M₀
  公理与运算 (2 个):
    - zero_mul : 对任意 a : M₀, 0 * a = 0
    - mul_zero : 对任意 a : M₀, a * 0 = 0
-/
class MulZeroClass (M₀ : Type u) extends Mul M₀, Zero M₀ where
  /-- Zero is a left absorbing element for multiplication -/
  zero_mul : forall a : M₀, 0 * a = 0
  /-- Zero is a right absorbing element for multiplication -/
  mul_zero : forall a : M₀, a * 0 = 0

export MulZeroClass (zero_mul mul_zero)
attribute [simp] zero_mul mul_zero

/--
Definition of `IsLeftCancelMulZero` / `IsLeftCancelMulZero` 的定义

English:
class IsLeftCancelMulZero
  parameters: (M₀ : Type u) [Mul M₀] [Zero M₀]
  axioms and operations (1):
    - mul_left_cancel_of_ne_zero : forall {a : M₀}, a != 0 -> IsLeftRegular a

中文:
类 IsLeftCancelMulZero
  参数: (M₀ : 类型u) [Mul M₀] [Zero M₀]
  公理与运算 (1 个):
    - mul_left_cancel_of_ne_zero : 对任意 {a : M₀}, a != 0 -> IsLeftRegular a
-/
@[mk_iff] class IsLeftCancelMulZero (M₀ : Type u) [Mul M₀] [Zero M₀] : Prop where
  /-- Multiplication by a nonzero element is left cancellative. -/
  protected mul_left_cancel_of_ne_zero : forall {a : M₀}, a != 0 -> IsLeftRegular a

section IsLeftCancelMulZero
section Mul
variable [Mul M₀] [Zero M₀] [IsLeftCancelMulZero M₀] {a b c : M₀}

/--
theorem `mul_left_cancel₀` / 定理 `mul_left_cancel₀`

English:
theorem mul_left_cancel₀
  given: (ha : a != 0) (h : a * b = a * c)
  statement: b = c
  proof: IsLeftCancelMulZero.mul_left_cancel_of_ne_zero ha h

中文:
定理 mul_left_cancel₀
  条件: (ha : a != 0) (h : a * b = a * c)
  结论: b = c
  证明: IsLeftCancelMulZero.mul_left_cancel_of_ne_zero ha h

Depends on / 依赖: IsLeftCancelMulZero, IsLeftCancelMulZero.mul_left_cancel_of_ne_zero, mul_left_cancel_of_ne_zero
-/
theorem mul_left_cancel₀ (ha : a != 0) (h : a * b = a * c) : b = c :=
  IsLeftCancelMulZero.mul_left_cancel_of_ne_zero ha h

/--
theorem `mul_right_injective₀` / 定理 `mul_right_injective₀`

English:
theorem mul_right_injective₀
  given: (ha : a != 0)
  statement: Function.Injective (a * ·)
  proof: fun _ _ => mul_left_cancel₀ ha

中文:
定理 mul_right_injective₀
  条件: (ha : a != 0)
  结论: Function.Injective (a * ·)
  证明: fun _ _ => mul_left_cancel₀ ha
-/
theorem mul_right_injective₀ (ha : a != 0) : Function.Injective (a * ·) :=
  fun _ _ => mul_left_cancel₀ ha

/--
lemma `mul_right_inj'` / 引理 `mul_right_inj'`

English:
lemma mul_right_inj'
  given: (ha : a != 0)
  statement: a * b = a * c ↔ b = c
  proof: (mul_right_injective₀ ha).eq_iff

中文:
引理 mul_right_inj'
  条件: (ha : a != 0)
  结论: a * b = a * c ↔ b = c
  证明: (mul_right_injective₀ ha).eq_iff

Depends on / 依赖: eq_iff
-/
lemma mul_right_inj' (ha : a != 0) : a * b = a * c ↔ b = c := (mul_right_injective₀ ha).eq_iff

end Mul

variable [MulZeroClass M₀] [IsLeftCancelMulZero M₀] {a b c : M₀}

/--
lemma `mul_eq_mul_left_iff` / 引理 `mul_eq_mul_left_iff`

English:
lemma mul_eq_mul_left_iff
  statement: a * b = a * c ↔ b = c ∨ a = 0
  proof: by
  by_cases ha : a = 0 <;> [simp only [ha, zero_mul, or_true]; simp [mul_right_inj', ha]]

中文:
引理 mul_eq_mul_left_iff
  结论: a * b = a * c ↔ b = c ∨ a = 0
  证明: by
  by_cases ha : a = 0 <;> [simp only [ha, zero_mul, or_true]; simp [mul_right_inj', ha]]
-/
@[simp] lemma mul_eq_mul_left_iff : a * b = a * c ↔ b = c ∨ a = 0 := by
  by_cases ha : a = 0 <;> [simp only [ha, zero_mul, or_true]; simp [mul_right_inj', ha]]

end IsLeftCancelMulZero

/--
Definition of `IsRightCancelMulZero` / `IsRightCancelMulZero` 的定义

English:
class IsRightCancelMulZero
  parameters: (M₀ : Type u) [Mul M₀] [Zero M₀]
  axioms and operations (1):
    - mul_right_cancel_of_ne_zero : forall {a : M₀}, a != 0 -> IsRightRegular a

中文:
类 IsRightCancelMulZero
  参数: (M₀ : 类型u) [Mul M₀] [Zero M₀]
  公理与运算 (1 个):
    - mul_right_cancel_of_ne_zero : 对任意 {a : M₀}, a != 0 -> IsRightRegular a
-/
@[mk_iff] class IsRightCancelMulZero (M₀ : Type u) [Mul M₀] [Zero M₀] : Prop where
  /-- Multiplication by a nonzero element is right cancellative. -/
  protected mul_right_cancel_of_ne_zero : forall {a : M₀}, a != 0 -> IsRightRegular a

section IsRightCancelMulZero
section Mul
variable [Mul M₀] [Zero M₀] [IsRightCancelMulZero M₀] {a b c : M₀}

/--
theorem `mul_right_cancel₀` / 定理 `mul_right_cancel₀`

English:
theorem mul_right_cancel₀
  given: (hb : b != 0) (h : a * b = c * b)
  statement: a = c
  proof: IsRightCancelMulZero.mul_right_cancel_of_ne_zero hb h

中文:
定理 mul_right_cancel₀
  条件: (hb : b != 0) (h : a * b = c * b)
  结论: a = c
  证明: IsRightCancelMulZero.mul_right_cancel_of_ne_zero hb h

Depends on / 依赖: IsRightCancelMulZero, IsRightCancelMulZero.mul_right_cancel_of_ne_zero, mul_right_cancel_of_ne_zero
-/
theorem mul_right_cancel₀ (hb : b != 0) (h : a * b = c * b) : a = c :=
  IsRightCancelMulZero.mul_right_cancel_of_ne_zero hb h

/--
theorem `mul_left_injective₀` / 定理 `mul_left_injective₀`

English:
theorem mul_left_injective₀
  given: (hb : b != 0)
  statement: Function.Injective fun a => a * b
  proof: fun _ _ => mul_right_cancel₀ hb

中文:
定理 mul_left_injective₀
  条件: (hb : b != 0)
  结论: Function.Injective fun a => a * b
  证明: fun _ _ => mul_right_cancel₀ hb
-/
theorem mul_left_injective₀ (hb : b != 0) : Function.Injective fun a => a * b :=
  fun _ _ => mul_right_cancel₀ hb

/--
lemma `mul_left_inj'` / 引理 `mul_left_inj'`

English:
lemma mul_left_inj'
  given: (hc : c != 0)
  statement: a * c = b * c ↔ a = b
  proof: (mul_left_injective₀ hc).eq_iff

中文:
引理 mul_left_inj'
  条件: (hc : c != 0)
  结论: a * c = b * c ↔ a = b
  证明: (mul_left_injective₀ hc).eq_iff

Depends on / 依赖: eq_iff
-/
lemma mul_left_inj' (hc : c != 0) : a * c = b * c ↔ a = b := (mul_left_injective₀ hc).eq_iff

end Mul

variable [MulZeroClass M₀] [IsRightCancelMulZero M₀] {a b c : M₀}

/--
lemma `mul_eq_mul_right_iff` / 引理 `mul_eq_mul_right_iff`

English:
lemma mul_eq_mul_right_iff
  statement: a * c = b * c ↔ a = b ∨ c = 0
  proof: by
  by_cases hc : c = 0 <;> [simp only [hc, mul_zero, or_true]; simp [mul_left_inj', hc]]

中文:
引理 mul_eq_mul_right_iff
  结论: a * c = b * c ↔ a = b ∨ c = 0
  证明: by
  by_cases hc : c = 0 <;> [simp only [hc, mul_zero, or_true]; simp [mul_left_inj', hc]]
-/
@[simp] lemma mul_eq_mul_right_iff : a * c = b * c ↔ a = b ∨ c = 0 := by
  by_cases hc : c = 0 <;> [simp only [hc, mul_zero, or_true]; simp [mul_left_inj', hc]]

end IsRightCancelMulZero

/--
Definition of `IsCancelMulZero` / `IsCancelMulZero` 的定义

English:
class IsCancelMulZero
  parameters: (M₀ : Type u) [Mul M₀] [Zero M₀]
  extends: IsLeftCancelMulZero M₀, IsRightCancelMulZero M₀
  (no additional axioms)

中文:
类 IsCancelMulZero
  参数: (M₀ : 类型u) [Mul M₀] [Zero M₀]
  继承: IsLeftCancelMulZero M₀, IsRightCancelMulZero M₀
  (无附加公理)
-/
@[mk_iff] class IsCancelMulZero (M₀ : Type u) [Mul M₀] [Zero M₀] : Prop
  extends IsLeftCancelMulZero M₀, IsRightCancelMulZero M₀

/--
theorem `isCancelMulZero_iff_forall_isRegular` / 定理 `isCancelMulZero_iff_forall_isRegular`

English:
theorem isCancelMulZero_iff_forall_isRegular
  given: {M₀} [Mul M₀] [Zero M₀]
  proof: by
  simp only [isCancelMulZero_iff, isLeftCancelMulZero_iff, isRightCancelMulZero_iff, ← forall_and]
  exact forall₂_congr fun _ _ => isRegular_iff.symm

中文:
定理 isCancelMulZero_iff_forall_isRegular
  条件: {M₀} [Mul M₀] [Zero M₀]
  证明: by
  simp only [isCancelMulZero_iff, isLeftCancelMulZero_iff, isRightCancelMulZero_iff, ← forall_and]
  exact forall₂_congr fun _ _ => isRegular_iff.symm

Depends on / 依赖: forall_and, isCancelMulZero_iff, isLeftCancelMulZero_iff, isRegular_iff, isRegular_iff.symm, isRightCancelMulZero_iff
-/
theorem isCancelMulZero_iff_forall_isRegular {M₀} [Mul M₀] [Zero M₀] :
    IsCancelMulZero M₀ ↔ forall {a : M₀}, a != 0 -> IsRegular a := by
  simp only [isCancelMulZero_iff, isLeftCancelMulZero_iff, isRightCancelMulZero_iff, ← forall_and]
  exact forall₂_congr fun _ _ => isRegular_iff.symm

/--
Definition of `NoZeroDivisors` / `NoZeroDivisors` 的定义

English:
class NoZeroDivisors
  parameters: (M₀ : Type*) [Mul M₀] [Zero M₀]
  axioms and operations (1):
    - eq_zero_or_eq_zero_of_mul_eq_zero : forall {a b : M₀}, a * b = 0 -> a = 0 ∨ b = 0

中文:
类 NoZeroDivisors
  参数: (M₀ : 类型) [Mul M₀] [Zero M₀]
  公理与运算 (1 个):
    - eq_zero_or_eq_zero_of_mul_eq_zero : 对任意 {a b : M₀}, a * b = 0 -> a = 0 ∨ b = 0
-/
@[mk_iff] class NoZeroDivisors (M₀ : Type*) [Mul M₀] [Zero M₀] : Prop where
  /-- For all `a` and `b` of `M₀`, `a * b = 0` implies `a = 0` or `b = 0`. -/
  eq_zero_or_eq_zero_of_mul_eq_zero : forall {a b : M₀}, a * b = 0 -> a = 0 ∨ b = 0

export NoZeroDivisors (eq_zero_or_eq_zero_of_mul_eq_zero)
/--
Definition of `SemigroupWithZero` / `SemigroupWithZero` 的定义

English:
class SemigroupWithZero
  parameters: (S₀ : Type u)
  extends: Semigroup S₀, MulZeroClass S₀
  (no additional axioms)

中文:
类 SemigroupWithZero
  参数: (S₀ : 类型u)
  继承: Semigroup S₀, MulZeroClass S₀
  (无附加公理)
-/
class SemigroupWithZero (S₀ : Type u) extends Semigroup S₀, MulZeroClass S₀

/--
Definition of `MulZeroOneClass` / `MulZeroOneClass` 的定义

English:
class MulZeroOneClass
  parameters: (M₀ : Type u)
  extends: MulOneClass M₀, MulZeroClass M₀
  (no additional axioms)

中文:
类 MulZeroOneClass
  参数: (M₀ : 类型u)
  继承: MulOneClass M₀, MulZeroClass M₀
  (无附加公理)
-/
class MulZeroOneClass (M₀ : Type u) extends MulOneClass M₀, MulZeroClass M₀

/--
Definition of `MonoidWithZero` / `MonoidWithZero` 的定义

English:
class MonoidWithZero
  parameters: (M₀ : Type u)
  extends: Monoid M₀, MulZeroOneClass M₀, SemigroupWithZero M₀
  (no additional axioms)

中文:
类 MonoidWithZero
  参数: (M₀ : 类型u)
  继承: Monoid M₀, MulZeroOneClass M₀, SemigroupWithZero M₀
  (无附加公理)
-/
class MonoidWithZero (M₀ : Type u) extends Monoid M₀, MulZeroOneClass M₀, SemigroupWithZero M₀

section MonoidWithZero

variable [MonoidWithZero M₀]

/--
theorem `pow_mul_apply_eq_pow_mul` / 定理 `pow_mul_apply_eq_pow_mul`

English:
theorem pow_mul_apply_eq_pow_mul
  statement: {M : Type*} [Monoid M] (f : M₀ -> M) {x : M₀}
  proof: by
  induction n with
  | zero => intro y; rw [pow_zero, pow_zero, one_mul, one_mul]
  | succ n hn => intro y; rw [pow_succ', pow_succ', mul_assoc, mul_assoc, hx, hn]

中文:
定理 pow_mul_apply_eq_pow_mul
  结论: {M : 类型} [Monoid M] (f : M₀ -> M) {x : M₀}
  证明: by
  induction n with
  | zero => intro y; rw [pow_zero, pow_zero, one_mul, one_mul]
  | succ n hn => intro y; rw [pow_succ', pow_succ', mul_assoc, mul_assoc, hx, hn]

Depends on / 依赖: mul_assoc, one_mul, pow_succ, pow_zero
-/
theorem pow_mul_apply_eq_pow_mul {M : Type*} [Monoid M] (f : M₀ -> M) {x : M₀}
    (hx : forall y : M₀, f (x * y) = f x * f y) (n : Nat) :
    forall (y : M₀), f (x ^ n * y) = f x ^ n * f y := by
  induction n with
  | zero => intro y; rw [pow_zero, pow_zero, one_mul, one_mul]
  | succ n hn => intro y; rw [pow_succ', pow_succ', mul_assoc, mul_assoc, hx, hn]

end MonoidWithZero

/-- A type `M` is a `CancelMonoidWithZero` if it is a monoid with zero element, `0` is left
and right absorbing, and left/right multiplication by a non-zero element is injective. -/
@[deprecated "Use `[MonoidWithZero M₀] [IsCancelMulZero M₀].`" (since := "2026-01-11")]
/--
Definition of `CancelMonoidWithZero` / `CancelMonoidWithZero` 的定义

English:
structure CancelMonoidWithZero
  parameters: (M₀ : Type*)
  extends: MonoidWithZero M₀, IsCancelMulZero M₀
  (no additional axioms)

中文:
结构 CancelMonoidWithZero
  参数: (M₀ : 类型)
  继承: MonoidWithZero M₀, IsCancelMulZero M₀
  (无附加公理)
-/
structure CancelMonoidWithZero (M₀ : Type*) extends MonoidWithZero M₀, IsCancelMulZero M₀

/--
Definition of `CommMonoidWithZero` / `CommMonoidWithZero` 的定义

English:
class CommMonoidWithZero
  parameters: (M₀ : Type*)
  extends: CommMonoid M₀, MonoidWithZero M₀
  (no additional axioms)

中文:
类 CommMonoidWithZero
  参数: (M₀ : 类型)
  继承: CommMonoid M₀, MonoidWithZero M₀
  (无附加公理)
-/
class CommMonoidWithZero (M₀ : Type*) extends CommMonoid M₀, MonoidWithZero M₀

section MulZeroClass

variable (M₀) [MulZeroClass M₀]

-- see Note [lower instance priority]
instance (priority := 10) IsLeftCancelMulZero.to_noZeroDivisors [IsLeftCancelMulZero M₀] :
    NoZeroDivisors M₀ where
  eq_zero_or_eq_zero_of_mul_eq_zero {x _} h :=
    or_iff_not_imp_left.mpr fun ne => mul_left_cancel₀ ne ((mul_zero x).symm ▸ h)

-- see Note [lower instance priority]
instance (priority := 10) IsRightCancelMulZero.to_noZeroDivisors [IsRightCancelMulZero M₀] :
    NoZeroDivisors M₀ where
  eq_zero_or_eq_zero_of_mul_eq_zero {_ y} h :=
    or_iff_not_imp_right.mpr fun ne => mul_right_cancel₀ ne ((zero_mul y).symm ▸ h)

end MulZeroClass

section CommMagma

variable [CommMagma M₀] [Zero M₀]

/--
lemma `IsLeftCancelMulZero.to_isRightCancelMulZero` / 引理 `IsLeftCancelMulZero.to_isRightCancelMulZero`

English:
lemma IsLeftCancelMulZero.to_isRightCancelMulZero
  given: [IsLeftCancelMulZero M₀]
  proof: fun hb _ _ h => mul_left_cancel₀ hb (mul_comm _ _).trans (h.trans (mul_comm _ _))

中文:
引理 IsLeftCancelMulZero.to_isRightCancelMulZero
  条件: [IsLeftCancelMulZero M₀]
  证明: fun hb _ _ h => mul_left_cancel₀ hb (mul_comm _ _).trans (h.trans (mul_comm _ _))

Depends on / 依赖: h.trans, mul_comm
-/
lemma IsLeftCancelMulZero.to_isRightCancelMulZero [IsLeftCancelMulZero M₀] :
    IsRightCancelMulZero M₀ where
  mul_right_cancel_of_ne_zero :=
fun hb _ _ h => mul_left_cancel₀ hb (mul_comm _ _).trans (h.trans (mul_comm _ _))

/--
lemma `IsRightCancelMulZero.to_isLeftCancelMulZero` / 引理 `IsRightCancelMulZero.to_isLeftCancelMulZero`

English:
lemma IsRightCancelMulZero.to_isLeftCancelMulZero
  given: [IsRightCancelMulZero M₀]
  proof: fun hb _ _ h => mul_right_cancel₀ hb (mul_comm _ _).trans (h.trans (mul_comm _ _))

中文:
引理 IsRightCancelMulZero.to_isLeftCancelMulZero
  条件: [IsRightCancelMulZero M₀]
  证明: fun hb _ _ h => mul_right_cancel₀ hb (mul_comm _ _).trans (h.trans (mul_comm _ _))

Depends on / 依赖: h.trans, mul_comm
-/
lemma IsRightCancelMulZero.to_isLeftCancelMulZero [IsRightCancelMulZero M₀] :
    IsLeftCancelMulZero M₀ where
  mul_left_cancel_of_ne_zero :=
fun hb _ _ h => mul_right_cancel₀ hb (mul_comm _ _).trans (h.trans (mul_comm _ _))

/--
lemma `IsLeftCancelMulZero.to_isCancelMulZero` / 引理 `IsLeftCancelMulZero.to_isCancelMulZero`

English:
lemma IsLeftCancelMulZero.to_isCancelMulZero
  given: [IsLeftCancelMulZero M₀]
  proof: { IsLeftCancelMulZero.to_isRightCancelMulZero with }

中文:
引理 IsLeftCancelMulZero.to_isCancelMulZero
  条件: [IsLeftCancelMulZero M₀]
  证明: { IsLeftCancelMulZero.to_isRightCancelMulZero with }

Depends on / 依赖: IsLeftCancelMulZero, IsLeftCancelMulZero.to_isRightCancelMulZero, to_isRightCancelMulZero
-/
lemma IsLeftCancelMulZero.to_isCancelMulZero [IsLeftCancelMulZero M₀] :
    IsCancelMulZero M₀ :=
{ IsLeftCancelMulZero.to_isRightCancelMulZero with }

/--
lemma `IsRightCancelMulZero.to_isCancelMulZero` / 引理 `IsRightCancelMulZero.to_isCancelMulZero`

English:
lemma IsRightCancelMulZero.to_isCancelMulZero
  given: [IsRightCancelMulZero M₀]
  proof: { IsRightCancelMulZero.to_isLeftCancelMulZero with }

中文:
引理 IsRightCancelMulZero.to_isCancelMulZero
  条件: [IsRightCancelMulZero M₀]
  证明: { IsRightCancelMulZero.to_isLeftCancelMulZero with }

Depends on / 依赖: IsRightCancelMulZero, IsRightCancelMulZero.to_isLeftCancelMulZero, to_isLeftCancelMulZero
-/
lemma IsRightCancelMulZero.to_isCancelMulZero [IsRightCancelMulZero M₀] :
    IsCancelMulZero M₀ :=
{ IsRightCancelMulZero.to_isLeftCancelMulZero with }

end CommMagma

/-- A type `M` is a `CancelCommMonoidWithZero` if it is a commutative monoid with zero element,
`0` is left and right absorbing,
and left/right multiplication by a non-zero element is injective. -/
@[deprecated "Use `[CommMonoidWithZero M₀] [IsCancelMulZero M₀].`" (since := "2026-01-11")]
/--
Definition of `CancelCommMonoidWithZero` / `CancelCommMonoidWithZero` 的定义

English:
structure CancelCommMonoidWithZero
  parameters: (M₀ : Type*)
  extends: CommMonoidWithZero M₀, IsLeftCancelMulZero M₀
  (no additional axioms)

中文:
结构 CancelCommMonoidWithZero
  参数: (M₀ : 类型)
  继承: CommMonoidWithZero M₀, IsLeftCancelMulZero M₀
  (无附加公理)
-/
structure CancelCommMonoidWithZero (M₀ : Type*)
    extends CommMonoidWithZero M₀, IsLeftCancelMulZero M₀

/--
Definition of `MulDivCancelClass` / `MulDivCancelClass` 的定义

English:
class MulDivCancelClass
  parameters: (M₀ : Type*) [MonoidWithZero M₀] [Div M₀]
  axioms and operations (1):
    - mul_div_cancel((a b : M₀)) : b != 0 -> a * b / b = a

中文:
类 MulDivCancelClass
  参数: (M₀ : 类型) [MonoidWithZero M₀] [Div M₀]
  公理与运算 (1 个):
    - mul_div_cancel((a b : M₀)) : b != 0 -> a * b / b = a
-/
class MulDivCancelClass (M₀ : Type*) [MonoidWithZero M₀] [Div M₀] : Prop where
  protected mul_div_cancel (a b : M₀) : b != 0 -> a * b / b = a

section MulDivCancelClass
variable [MonoidWithZero M₀] [Div M₀] [MulDivCancelClass M₀]

/--
lemma `mul_div_cancel_right₀` / 引理 `mul_div_cancel_right₀`

English:
lemma mul_div_cancel_right₀
  given: (a : M₀) {b : M₀} (hb : b != 0)
  statement: a * b / b = a
  proof: MulDivCancelClass.mul_div_cancel _ _ hb

中文:
引理 mul_div_cancel_right₀
  条件: (a : M₀) {b : M₀} (hb : b != 0)
  结论: a * b / b = a
  证明: MulDivCancelClass.mul_div_cancel _ _ hb
-/
@[simp] lemma mul_div_cancel_right₀ (a : M₀) {b : M₀} (hb : b != 0) : a * b / b = a :=
  MulDivCancelClass.mul_div_cancel _ _ hb

end MulDivCancelClass

section MulDivCancelClass
variable [CommMonoidWithZero M₀] [Div M₀] [MulDivCancelClass M₀]

/--
lemma `mul_div_cancel_left₀` / 引理 `mul_div_cancel_left₀`

English:
lemma mul_div_cancel_left₀
  given: (b : M₀) {a : M₀} (ha : a != 0)
  statement: a * b / a = b
  proof: by
  rw [mul_comm]; rw [mul_div_cancel_right₀ _ ha]

中文:
引理 mul_div_cancel_left₀
  条件: (b : M₀) {a : M₀} (ha : a != 0)
  结论: a * b / a = b
  证明: by
  rw [mul_comm]; rw [mul_div_cancel_right₀ _ ha]
-/
@[simp] lemma mul_div_cancel_left₀ (b : M₀) {a : M₀} (ha : a != 0) : a * b / a = b := by
  rw [mul_comm]; rw [mul_div_cancel_right₀ _ ha]

end MulDivCancelClass

/--
Definition of `GroupWithZero` / `GroupWithZero` 的定义

English:
class GroupWithZero
  parameters: (G₀ : Type u)
  extends: MonoidWithZero G₀, DivInvMonoid G₀, Nontrivial G₀
  axioms and operations (2):
    - inv_zero : (0 : G₀)⁻¹ = 0
    - mul_inv_cancel((a : G₀)) : a != 0 -> a * a⁻¹ = 1

中文:
类 GroupWithZero
  参数: (G₀ : 类型u)
  继承: MonoidWithZero G₀, DivInvMonoid G₀, Nontrivial G₀
  公理与运算 (2 个):
    - inv_zero : (0 : G₀)⁻¹ = 0
    - mul_inv_cancel((a : G₀)) : a != 0 -> a * a⁻¹ = 1
-/
class GroupWithZero (G₀ : Type u) extends MonoidWithZero G₀, DivInvMonoid G₀, Nontrivial G₀ where
  /-- The inverse of `0` in a group with zero is `0`. -/
  protected inv_zero : (0 : G₀)⁻¹ = 0
  /-- Every nonzero element of a group with zero is invertible. -/
  protected mul_inv_cancel (a : G₀) : a != 0 -> a * a⁻¹ = 1

section GroupWithZero
variable [GroupWithZero G₀] {a : G₀}

/--
lemma `inv_zero` / 引理 `inv_zero`

English:
lemma inv_zero
  statement: (0 : G₀)⁻¹ = 0
  proof: GroupWithZero.inv_zero

@[simp high] -- should take priority over `IsUnit.mul_inv_cancel`

中文:
引理 inv_zero
  结论: (0 : G₀)⁻¹ = 0
  证明: GroupWithZero.inv_zero

@[simp high] -- should take priority over `IsUnit.mul_inv_cancel`
-/
@[simp] lemma inv_zero : (0 : G₀)⁻¹ = 0 := GroupWithZero.inv_zero

@[simp high] -- should take priority over `IsUnit.mul_inv_cancel`
/--
lemma `mul_inv_cancel₀` / 引理 `mul_inv_cancel₀`

English:
lemma mul_inv_cancel₀
  given: (h : a != 0)
  statement: a * a⁻¹ = 1
  proof: GroupWithZero.mul_inv_cancel a h

中文:
引理 mul_inv_cancel₀
  条件: (h : a != 0)
  结论: a * a⁻¹ = 1
  证明: GroupWithZero.mul_inv_cancel a h

Depends on / 依赖: GroupWithZero, GroupWithZero.mul_inv_cancel, mul_inv_cancel
-/
lemma mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1 := GroupWithZero.mul_inv_cancel a h

-- See note [lower instance priority]
instance (priority := 100) GroupWithZero.toMulDivCancelClass : MulDivCancelClass G₀ where
  mul_div_cancel a b hb := by rw [div_eq_mul_inv, mul_assoc, mul_inv_cancel₀ hb, mul_one]

end GroupWithZero

/--
Definition of `CommGroupWithZero` / `CommGroupWithZero` 的定义

English:
class CommGroupWithZero
  parameters: (G₀ : Type*)
  extends: CommMonoidWithZero G₀, GroupWithZero G₀
  (no additional axioms)

中文:
类 CommGroupWithZero
  参数: (G₀ : 类型)
  继承: CommMonoidWithZero G₀, GroupWithZero G₀
  (无附加公理)
-/
class CommGroupWithZero (G₀ : Type*) extends CommMonoidWithZero G₀, GroupWithZero G₀

/--
lemma `eq_zero_or_one_of_sq_eq_self` / 引理 `eq_zero_or_one_of_sq_eq_self`

English:
lemma eq_zero_or_one_of_sq_eq_self
  statement: [MonoidWithZero M₀] [IsRightCancelMulZero M₀]
  proof: or_iff_not_imp_left.mpr (mul_left_injective₀ · <| by simpa [sq] using hx)

中文:
引理 eq_zero_or_one_of_sq_eq_self
  结论: [MonoidWithZero M₀] [IsRightCancelMulZero M₀]
  证明: or_iff_not_imp_left.mpr (mul_left_injective₀ · <| by simpa [sq] using hx)

Depends on / 依赖: or_iff_not_imp_left, or_iff_not_imp_left.mpr
-/
lemma eq_zero_or_one_of_sq_eq_self [MonoidWithZero M₀] [IsRightCancelMulZero M₀]
    {x : M₀} (hx : x ^ 2 = x) :
    x = 0 ∨ x = 1 :=
  or_iff_not_imp_left.mpr (mul_left_injective₀ · <| by simpa [sq] using hx)

section GroupWithZero

variable [GroupWithZero G₀] {a b : G₀}

@[simp high] -- should take priority over `IsUnit.mul_inv_cancel_right`
/--
theorem `mul_inv_cancel_right₀` / 定理 `mul_inv_cancel_right₀`

English:
theorem mul_inv_cancel_right₀
  given: (h : b != 0) (a : G₀)
  statement: a * b * b⁻¹ = a
  proof: calc
    a * b * b⁻¹ = a * (b * b⁻¹) := mul_assoc _ _ _
    _ = a := by simp [h]

@[simp high] -- should take priority over `IsUnit.mul_inv_cancel_left`

中文:
定理 mul_inv_cancel_right₀
  条件: (h : b != 0) (a : G₀)
  结论: a * b * b⁻¹ = a
  证明: calc
    a * b * b⁻¹ = a * (b * b⁻¹) := mul_assoc _ _ _
    _ = a := by simp [h]

@[simp high] -- should take priority over `IsUnit.mul_inv_cancel_left`

Depends on / 依赖: mul_assoc
-/
theorem mul_inv_cancel_right₀ (h : b != 0) (a : G₀) : a * b * b⁻¹ = a :=
  calc
    a * b * b⁻¹ = a * (b * b⁻¹) := mul_assoc _ _ _
    _ = a := by simp [h]

@[simp high] -- should take priority over `IsUnit.mul_inv_cancel_left`
/--
theorem `mul_inv_cancel_left₀` / 定理 `mul_inv_cancel_left₀`

English:
theorem mul_inv_cancel_left₀
  given: (h : a != 0) (b : G₀)
  statement: a * (a⁻¹ * b) = b
  proof: calc
    a * (a⁻¹ * b) = a * a⁻¹ * b := (mul_assoc _ _ _).symm
    _ = b := by simp [h]

中文:
定理 mul_inv_cancel_left₀
  条件: (h : a != 0) (b : G₀)
  结论: a * (a⁻¹ * b) = b
  证明: calc
    a * (a⁻¹ * b) = a * a⁻¹ * b := (mul_assoc _ _ _).symm
    _ = b := by simp [h]

Depends on / 依赖: mul_assoc
-/
theorem mul_inv_cancel_left₀ (h : a != 0) (b : G₀) : a * (a⁻¹ * b) = b :=
  calc
    a * (a⁻¹ * b) = a * a⁻¹ * b := (mul_assoc _ _ _).symm
    _ = b := by simp [h]

end GroupWithZero

section MulZeroClass

variable [MulZeroClass M₀]

/--
theorem `mul_eq_zero_of_left` / 定理 `mul_eq_zero_of_left`

English:
theorem mul_eq_zero_of_left
  given: {a : M₀} (h : a = 0) (b : M₀)
  statement: a * b = 0
  proof: h.symm ▸ zero_mul b

中文:
定理 mul_eq_zero_of_left
  条件: {a : M₀} (h : a = 0) (b : M₀)
  结论: a * b = 0
  证明: h.symm ▸ zero_mul b

Depends on / 依赖: h.symm, zero_mul
-/
theorem mul_eq_zero_of_left {a : M₀} (h : a = 0) (b : M₀) : a * b = 0 := h.symm ▸ zero_mul b

/--
theorem `mul_eq_zero_of_right` / 定理 `mul_eq_zero_of_right`

English:
theorem mul_eq_zero_of_right
  given: (a : M₀) {b : M₀} (h : b = 0)
  statement: a * b = 0
  proof: h.symm ▸ mul_zero a

中文:
定理 mul_eq_zero_of_right
  条件: (a : M₀) {b : M₀} (h : b = 0)
  结论: a * b = 0
  证明: h.symm ▸ mul_zero a

Depends on / 依赖: h.symm, mul_zero
-/
theorem mul_eq_zero_of_right (a : M₀) {b : M₀} (h : b = 0) : a * b = 0 := h.symm ▸ mul_zero a

/--
lemma `noZeroDivisors_iff_right_eq_zero_of_mul` / 引理 `noZeroDivisors_iff_right_eq_zero_of_mul`

English:
lemma noZeroDivisors_iff_right_eq_zero_of_mul
  proof: by
  simp only [noZeroDivisors_iff, or_iff_not_imp_left]
  exact ⟨fun h a ha b eq => h eq ha, fun h a b eq ha => h a ha b eq⟩

中文:
引理 noZeroDivisors_iff_right_eq_zero_of_mul
  证明: by
  simp only [noZeroDivisors_iff, or_iff_not_imp_left]
  exact ⟨fun h a ha b eq => h eq ha, fun h a b eq ha => h a ha b eq⟩

Depends on / 依赖: noZeroDivisors_iff, or_iff_not_imp_left
-/
lemma noZeroDivisors_iff_right_eq_zero_of_mul :
    NoZeroDivisors M₀ ↔ forall x : M₀, x != 0 -> forall y, x * y = 0 -> y = 0 := by
  simp only [noZeroDivisors_iff, or_iff_not_imp_left]
  exact ⟨fun h a ha b eq => h eq ha, fun h a b eq ha => h a ha b eq⟩

/--
lemma `noZeroDivisors_iff_left_eq_zero_of_mul` / 引理 `noZeroDivisors_iff_left_eq_zero_of_mul`

English:
lemma noZeroDivisors_iff_left_eq_zero_of_mul
  proof: by
  simp only [noZeroDivisors_iff, or_iff_not_imp_right]
  exact ⟨fun h b hb a eq => h eq hb, fun h a b eq hb => h b hb a eq⟩

中文:
引理 noZeroDivisors_iff_left_eq_zero_of_mul
  证明: by
  simp only [noZeroDivisors_iff, or_iff_not_imp_right]
  exact ⟨fun h b hb a eq => h eq hb, fun h a b eq hb => h b hb a eq⟩

Depends on / 依赖: noZeroDivisors_iff, or_iff_not_imp_right
-/
lemma noZeroDivisors_iff_left_eq_zero_of_mul :
    NoZeroDivisors M₀ ↔ forall x : M₀, x != 0 -> forall y, y * x = 0 -> y = 0 := by
  simp only [noZeroDivisors_iff, or_iff_not_imp_right]
  exact ⟨fun h b hb a eq => h eq hb, fun h a b eq hb => h b hb a eq⟩

/--
lemma `noZeroDivisors_iff_eq_zero_of_mul` / 引理 `noZeroDivisors_iff_eq_zero_of_mul`

English:
lemma noZeroDivisors_iff_eq_zero_of_mul
  proof: by
  simp only [forall_and, ← noZeroDivisors_iff_right_eq_zero_of_mul,
    ← noZeroDivisors_iff_left_eq_zero_of_mul, and_self]

中文:
引理 noZeroDivisors_iff_eq_zero_of_mul
  证明: by
  simp only [forall_and, ← noZeroDivisors_iff_right_eq_zero_of_mul,
    ← noZeroDivisors_iff_left_eq_zero_of_mul, and_self]

Depends on / 依赖: and_self, forall_and, noZeroDivisors_iff_left_eq_zero_of_mul, noZeroDivisors_iff_right_eq_zero_of_mul
-/
lemma noZeroDivisors_iff_eq_zero_of_mul :
    NoZeroDivisors M₀ ↔ forall x : M₀, x != 0 -> (forall y, x * y = 0 -> y = 0) ∧ (forall y, y * x = 0 -> y = 0) := by
  simp only [forall_and, ← noZeroDivisors_iff_right_eq_zero_of_mul,
    ← noZeroDivisors_iff_left_eq_zero_of_mul, and_self]

variable [NoZeroDivisors M₀] {a b : M₀}

/-- If `α` has no zero divisors, then the product of two elements equals zero iff one of them
equals zero. -/
@[simp]
/--
theorem `mul_eq_zero` / 定理 `mul_eq_zero`

English:
theorem mul_eq_zero
  statement: a * b = 0 ↔ a = 0 ∨ b = 0
  proof: ⟨eq_zero_or_eq_zero_of_mul_eq_zero,
    fun o => o.elim (fun h => mul_eq_zero_of_left h b) (mul_eq_zero_of_right a)⟩

中文:
定理 mul_eq_zero
  结论: a * b = 0 ↔ a = 0 ∨ b = 0
  证明: ⟨eq_zero_or_eq_zero_of_mul_eq_zero,
    fun o => o.elim (fun h => mul_eq_zero_of_left h b) (mul_eq_zero_of_right a)⟩

Depends on / 依赖: eq_zero_or_eq_zero_of_mul_eq_zero, mul_eq_zero_of_left, mul_eq_zero_of_right, o.elim
-/
theorem mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0 :=
  ⟨eq_zero_or_eq_zero_of_mul_eq_zero,
    fun o => o.elim (fun h => mul_eq_zero_of_left h b) (mul_eq_zero_of_right a)⟩

/-- If `α` has no zero divisors, then the product of two elements equals zero iff one of them
equals zero. -/
@[simp]
/--
theorem `zero_eq_mul` / 定理 `zero_eq_mul`

English:
theorem zero_eq_mul
  statement: 0 = a * b ↔ a = 0 ∨ b = 0
  proof: by simp [eqComm]

中文:
定理 zero_eq_mul
  结论: 0 = a * b ↔ a = 0 ∨ b = 0
  证明: by simp [eqComm]

Depends on / 依赖: eqComm
-/
theorem zero_eq_mul : 0 = a * b ↔ a = 0 ∨ b = 0 := by simp [eqComm]

/--
theorem `mul_ne_zero_iff` / 定理 `mul_ne_zero_iff`

English:
theorem mul_ne_zero_iff
  statement: a * b != 0 ↔ a != 0 ∧ b != 0
  proof: mul_eq_zero.not.trans not_or

中文:
定理 mul_ne_zero_iff
  结论: a * b != 0 ↔ a != 0 ∧ b != 0
  证明: mul_eq_zero.not.trans not_or

Depends on / 依赖: mul_eq_zero, mul_eq_zero.not.trans, not_or
-/
theorem mul_ne_zero_iff : a * b != 0 ↔ a != 0 ∧ b != 0 := mul_eq_zero.not.trans not_or

/--
theorem `mul_eq_zero_comm` / 定理 `mul_eq_zero_comm`

English:
theorem mul_eq_zero_comm
  statement: a * b = 0 ↔ b * a = 0
  proof: mul_eq_zero.trans or_comm.trans mul_eq_zero.symm

中文:
定理 mul_eq_zero_comm
  结论: a * b = 0 ↔ b * a = 0
  证明: mul_eq_zero.trans or_comm.trans mul_eq_zero.symm

Depends on / 依赖: mul_eq_zero, mul_eq_zero.symm, mul_eq_zero.trans, or_comm, or_comm.trans
-/
theorem mul_eq_zero_comm : a * b = 0 ↔ b * a = 0 :=
mul_eq_zero.trans or_comm.trans mul_eq_zero.symm

/--
theorem `mul_ne_zero_comm` / 定理 `mul_ne_zero_comm`

English:
theorem mul_ne_zero_comm
  statement: a * b != 0 ↔ b * a != 0
  proof: mul_eq_zero_comm.not

中文:
定理 mul_ne_zero_comm
  结论: a * b != 0 ↔ b * a != 0
  证明: mul_eq_zero_comm.not

Depends on / 依赖: mul_eq_zero_comm, mul_eq_zero_comm.not
-/
theorem mul_ne_zero_comm : a * b != 0 ↔ b * a != 0 := mul_eq_zero_comm.not

/--
theorem `mul_self_eq_zero` / 定理 `mul_self_eq_zero`

English:
theorem mul_self_eq_zero
  statement: a * a = 0 ↔ a = 0
  proof: by simp

中文:
定理 mul_self_eq_zero
  结论: a * a = 0 ↔ a = 0
  证明: by simp
-/
theorem mul_self_eq_zero : a * a = 0 ↔ a = 0 := by simp

/--
theorem `zero_eq_mul_self` / 定理 `zero_eq_mul_self`

English:
theorem zero_eq_mul_self
  statement: 0 = a * a ↔ a = 0
  proof: by simp

中文:
定理 zero_eq_mul_self
  结论: 0 = a * a ↔ a = 0
  证明: by simp
-/
theorem zero_eq_mul_self : 0 = a * a ↔ a = 0 := by simp

/--
theorem `mul_self_ne_zero` / 定理 `mul_self_ne_zero`

English:
theorem mul_self_ne_zero
  statement: a * a != 0 ↔ a != 0
  proof: mul_self_eq_zero.not

中文:
定理 mul_self_ne_zero
  结论: a * a != 0 ↔ a != 0
  证明: mul_self_eq_zero.not

Depends on / 依赖: mul_self_eq_zero, mul_self_eq_zero.not
-/
theorem mul_self_ne_zero : a * a != 0 ↔ a != 0 := mul_self_eq_zero.not

/--
theorem `zero_ne_mul_self` / 定理 `zero_ne_mul_self`

English:
theorem zero_ne_mul_self
  statement: 0 != a * a ↔ a != 0
  proof: zero_eq_mul_self.not

中文:
定理 zero_ne_mul_self
  结论: 0 != a * a ↔ a != 0
  证明: zero_eq_mul_self.not

Depends on / 依赖: zero_eq_mul_self, zero_eq_mul_self.not
-/
theorem zero_ne_mul_self : 0 != a * a ↔ a != 0 := zero_eq_mul_self.not

/--
theorem `mul_eq_zero_iff_left` / 定理 `mul_eq_zero_iff_left`

English:
theorem mul_eq_zero_iff_left
  given: (ha : a != 0)
  statement: a * b = 0 ↔ b = 0
  proof: by simp [ha]

中文:
定理 mul_eq_zero_iff_left
  条件: (ha : a != 0)
  结论: a * b = 0 ↔ b = 0
  证明: by simp [ha]
-/
theorem mul_eq_zero_iff_left (ha : a != 0) : a * b = 0 ↔ b = 0 := by simp [ha]

/--
theorem `mul_eq_zero_iff_right` / 定理 `mul_eq_zero_iff_right`

English:
theorem mul_eq_zero_iff_right
  given: (hb : b != 0)
  statement: a * b = 0 ↔ a = 0
  proof: by simp [hb]

中文:
定理 mul_eq_zero_iff_right
  条件: (hb : b != 0)
  结论: a * b = 0 ↔ a = 0
  证明: by simp [hb]
-/
theorem mul_eq_zero_iff_right (hb : b != 0) : a * b = 0 ↔ a = 0 := by simp [hb]

/--
theorem `mul_ne_zero_iff_left` / 定理 `mul_ne_zero_iff_left`

English:
theorem mul_ne_zero_iff_left
  given: (ha : a != 0)
  statement: a * b != 0 ↔ b != 0
  proof: by simp [ha]

中文:
定理 mul_ne_zero_iff_left
  条件: (ha : a != 0)
  结论: a * b != 0 ↔ b != 0
  证明: by simp [ha]
-/
theorem mul_ne_zero_iff_left (ha : a != 0) : a * b != 0 ↔ b != 0 := by simp [ha]

/--
theorem `mul_ne_zero_iff_right` / 定理 `mul_ne_zero_iff_right`

English:
theorem mul_ne_zero_iff_right
  given: (hb : b != 0)
  statement: a * b != 0 ↔ a != 0
  proof: by simp [hb]

中文:
定理 mul_ne_zero_iff_right
  条件: (hb : b != 0)
  结论: a * b != 0 ↔ a != 0
  证明: by simp [hb]
-/
theorem mul_ne_zero_iff_right (hb : b != 0) : a * b != 0 ↔ a != 0 := by simp [hb]

end MulZeroClass
