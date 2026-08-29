/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland
-/
module

public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Tactic.Spread

/-!
# Semirings and rings

This file defines semirings, rings and domains. This is analogous to
`Mathlib/Algebra/Group/Defs.lean` and `Mathlib/Algebra/Group/Basic.lean`, the difference being that
those are about `+` and `*` separately, while the present file is about their interaction.
the present file is about their interaction.

## Main definitions

* `Distrib`: Typeclass for distributivity of multiplication over addition.
* `HasDistribNeg`: Typeclass for commutativity of negation and multiplication. This is useful when
  dealing with multiplicative submonoids which are closed under negation without being closed under
  addition, for example `Units`.
* `(NonUnital)(NonAssoc)(Semi)Ring`: Typeclasses for possibly non-unital or non-associative
  rings and semirings. Some combinations are not defined yet because they haven't found use.
  For Lie Rings, there is a type synonym `CommutatorRing` defined in
  `Mathlib/Algebra/Algebra/NonUnitalHom.lean` turning the bracket into a multiplication so that the
  instance `instNonUnitalNonAssocSemiringCommutatorRing` can be defined.

## Tags

`Semiring`, `CommSemiring`, `Ring`, `CommRing`, domain, `IsDomain`, nonzero, units
-/

public section


/-!
Previously an import dependency on `Mathlib/Algebra/Group/Basic.lean` had crept in.
In general, the `.Defs` files in the basic algebraic hierarchy should only depend on earlier `.Defs`
files, without importing `.Basic` theory development.

These `assert_not_exists` statements guard against this returning.
-/
assert_not_exists DivisionMonoid.toDivInvOneMonoid mul_rotate


universe u v

variable {α : Type u} {R : Type v}

open Function

/-!
### `Distrib` class
-/


/--
Definition of `Distrib` / `Distrib` 的定义

English:
class Distrib
  parameters: (R : Type*)
  extends: Mul R, Add R
  axioms and operations (2):
    - left_distrib : forall a b c : R, a * (b + c) = a * b + a * c
    - right_distrib : forall a b c : R, (a + b) * c = a * c + b * c

中文:
类 Distrib
  参数: (R : 类型)
  继承: 乘法 R, 加法 R
  公理与运算 (2 个):
    - left_distrib : 对任意 a b c : R, a * (b + c) = a * b + a * c
    - right_distrib : 对任意 a b c : R, (a + b) * c = a * c + b * c
-/
class Distrib (R : Type*) extends Mul R, Add R where
  /-- Multiplication is left distributive over addition -/
  protected left_distrib : forall a b c : R, a * (b + c) = a * b + a * c
  /-- Multiplication is right distributive over addition -/
  protected right_distrib : forall a b c : R, (a + b) * c = a * c + b * c

/--
Definition of `LeftDistribClass` / `LeftDistribClass` 的定义

English:
class LeftDistribClass
  parameters: (R : Type*) [Mul R] [Add R]
  axioms and operations (1):
    - left_distrib : forall a b c : R, a * (b + c) = a * b + a * c

中文:
类 LeftDistrib类
  参数: (R : 类型) [乘法 R] [加法 R]
  公理与运算 (1 个):
    - left_distrib : 对任意 a b c : R, a * (b + c) = a * b + a * c
-/
class LeftDistribClass (R : Type*) [Mul R] [Add R] : Prop where
  /-- Multiplication is left distributive over addition -/
  protected left_distrib : forall a b c : R, a * (b + c) = a * b + a * c

/--
Definition of `RightDistribClass` / `RightDistribClass` 的定义

English:
class RightDistribClass
  parameters: (R : Type*) [Mul R] [Add R]
  axioms and operations (1):
    - right_distrib : forall a b c : R, (a + b) * c = a * c + b * c

中文:
类 RightDistrib类
  参数: (R : 类型) [乘法 R] [加法 R]
  公理与运算 (1 个):
    - right_distrib : 对任意 a b c : R, (a + b) * c = a * c + b * c
-/
class RightDistribClass (R : Type*) [Mul R] [Add R] : Prop where
  /-- Multiplication is right distributive over addition -/
  protected right_distrib : forall a b c : R, (a + b) * c = a * c + b * c

-- see Note [lower instance priority]
instance (priority := 100) Distrib.leftDistribClass (R : Type*) [Distrib R] : LeftDistribClass R :=
  ⟨Distrib.left_distrib⟩

-- see Note [lower instance priority]
instance (priority := 100) Distrib.rightDistribClass (R : Type*) [Distrib R] :
    RightDistribClass R :=
  ⟨Distrib.right_distrib⟩

/--
theorem `left_distrib` / 定理 `left_distrib`

English:
theorem left_distrib
  given: [Mul R] [Add R] [LeftDistribClass R] (a b c : R)
  proof: LeftDistribClass.left_distrib a b c

alias mul_add := left_distrib

中文:
定理 left_distrib
  条件: [乘法 R] [加法 R] [LeftDistrib类 R] (a b c : R)
  证明: LeftDistribClass.left_distrib a b c

alias mul_add := left_distrib

Depends on / 依赖: LeftDistribClass, LeftDistribClass.left_distrib, left_distrib
-/
theorem left_distrib [Mul R] [Add R] [LeftDistribClass R] (a b c : R) :
    a * (b + c) = a * b + a * c :=
  LeftDistribClass.left_distrib a b c

alias mul_add := left_distrib

/--
theorem `right_distrib` / 定理 `right_distrib`

English:
theorem right_distrib
  given: [Mul R] [Add R] [RightDistribClass R] (a b c : R)
  proof: RightDistribClass.right_distrib a b c

alias add_mul := right_distrib

中文:
定理 right_distrib
  条件: [乘法 R] [加法 R] [RightDistrib类 R] (a b c : R)
  证明: RightDistribClass.right_distrib a b c

alias add_mul := right_distrib

Depends on / 依赖: RightDistribClass, RightDistribClass.right_distrib, right_distrib
-/
theorem right_distrib [Mul R] [Add R] [RightDistribClass R] (a b c : R) :
    (a + b) * c = a * c + b * c :=
  RightDistribClass.right_distrib a b c

alias add_mul := right_distrib

/--
theorem `distrib_three_right` / 定理 `distrib_three_right`

English:
theorem distrib_three_right
  given: [Mul R] [Add R] [RightDistribClass R] (a b c d : R)
  proof: by simp [right_distrib]

中文:
定理 distrib_three_right
  条件: [乘法 R] [加法 R] [RightDistrib类 R] (a b c d : R)
  证明: by simp [right_distrib]

Depends on / 依赖: right_distrib
-/
theorem distrib_three_right [Mul R] [Add R] [RightDistribClass R] (a b c d : R) :
    (a + b + c) * d = a * d + b * d + c * d := by simp [right_distrib]

/-!
### Classes of semirings and rings

We make sure that the canonical path from `NonAssocSemiring` to `Ring` passes through `Semiring`,
as this is a path which is followed all the time in linear algebra where the defining semilinear map
`σ : R →+* S` depends on the `NonAssocSemiring` structure of `R` and `S` while the module
definition depends on the `Semiring` structure.

It is not currently possible to adjust priorities by hand (see https://github.com/leanprover/lean4/issues/2115). Instead, the last
declared instance is used, so we make sure that `Semiring` is declared after `NonAssocRing`, so
that `Semiring -> NonAssocSemiring` is tried before `NonAssocRing -> NonAssocSemiring`.
TODO: clean this once https://github.com/leanprover/lean4/issues/2115 is fixed
-/

/--
Definition of `NonUnitalNonAssocSemiring` / `NonUnitalNonAssocSemiring` 的定义

English:
class NonUnitalNonAssocSemiring
  parameters: (α : Type u)
  extends: AddCommMonoid α, Distrib α, MulZeroClass α
  (no additional axioms)

中文:
类 非幺非结合半环
  参数: (α : 类型u)
  继承: 加法交换幺半群 α, Distrib α, 乘零类 α
  (无附加公理)
-/
class NonUnitalNonAssocSemiring (α : Type u) extends AddCommMonoid α, Distrib α, MulZeroClass α

/--
Definition of `NonUnitalSemiring` / `NonUnitalSemiring` 的定义

English:
class NonUnitalSemiring
  parameters: (α : Type u)
  extends: NonUnitalNonAssocSemiring α, SemigroupWithZero α
  (no additional axioms)

中文:
类 非幺半环
  参数: (α : 类型u)
  继承: 非幺非结合半环 α, 带零半群 α
  (无附加公理)
-/
class NonUnitalSemiring (α : Type u) extends NonUnitalNonAssocSemiring α, SemigroupWithZero α

/--
Definition of `NonAssocSemiring` / `NonAssocSemiring` 的定义

English:
class NonAssocSemiring
  parameters: (α : Type u)
  extends: NonUnitalNonAssocSemiring α, MulZeroOneClass α, 
  (no additional axioms)

中文:
类 非结合半环
  参数: (α : 类型u)
  继承: 非幺非结合半环 α, 乘零幺类 α, 
  (无附加公理)
-/
class NonAssocSemiring (α : Type u) extends NonUnitalNonAssocSemiring α, MulZeroOneClass α,
    AddCommMonoidWithOne α

/--
Definition of `NonUnitalNonAssocRing` / `NonUnitalNonAssocRing` 的定义

English:
class NonUnitalNonAssocRing
  parameters: (α : Type u)
  extends: AddCommGroup α, NonUnitalNonAssocSemiring α
  (no additional axioms)

中文:
类 非幺非结合环
  参数: (α : 类型u)
  继承: 加法交换群 α, 非幺非结合半环 α
  (无附加公理)
-/
class NonUnitalNonAssocRing (α : Type u) extends AddCommGroup α, NonUnitalNonAssocSemiring α

/--
Definition of `NonUnitalRing` / `NonUnitalRing` 的定义

English:
class NonUnitalRing
  parameters: (α : Type*)
  extends: NonUnitalNonAssocRing α, NonUnitalSemiring α
  (no additional axioms)

中文:
类 非幺环
  参数: (α : 类型)
  继承: 非幺非结合环 α, 非幺半环 α
  (无附加公理)
-/
class NonUnitalRing (α : Type*) extends NonUnitalNonAssocRing α, NonUnitalSemiring α

/--
Definition of `NonAssocRing` / `NonAssocRing` 的定义

English:
class NonAssocRing
  parameters: (α : Type*)
  extends: NonUnitalNonAssocRing α, NonAssocSemiring α, 
  (no additional axioms)

中文:
类 非结合环
  参数: (α : 类型)
  继承: 非幺非结合环 α, 非结合半环 α, 
  (无附加公理)
-/
class NonAssocRing (α : Type*) extends NonUnitalNonAssocRing α, NonAssocSemiring α,
    AddCommGroupWithOne α

/--
Definition of `Semiring` / `Semiring` 的定义

English:
class Semiring
  parameters: (α : Type u)
  extends: AddCommMonoid α, MonoidWithZero α, NonUnitalSemiring α, 
  (no additional axioms)

中文:
类 半环
  参数: (α : 类型u)
  继承: 加法交换幺半群 α, 带零幺半群 α, 非幺半环 α, 
  (无附加公理)
-/
class Semiring (α : Type u) extends AddCommMonoid α, MonoidWithZero α, NonUnitalSemiring α,
  NonAssocSemiring α

/-- A `Ring` is a `Semiring` with negation making it an additive group. -/
@[wikidata Q161172]
/--
Definition of `Ring` / `Ring` 的定义

English:
class Ring
  parameters: (R : Type u)
  extends: Semiring R, AddCommGroup R, AddGroupWithOne R
  (no additional axioms)

中文:
类 环
  参数: (R : 类型u)
  继承: 半环 R, 加法交换群 R, 加法带幺群 R
  (无附加公理)
-/
class Ring (R : Type u) extends Semiring R, AddCommGroup R, AddGroupWithOne R

-- Add some short-cut instances to avoid going through the less used ring type classes.
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semiring
  signature: α] : Distrib α
  body: inferInstance

中文:
实例 [半环
  签名: α] : Distrib α
  定义体: inferInstance
-/
instance [Semiring α] : Distrib α := inferInstance
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semiring
  signature: α] : MulZeroClass α
  body: inferInstance

中文:
实例 [半环
  签名: α] : 乘零类 α
  定义体: inferInstance
-/
instance [Semiring α] : MulZeroClass α := inferInstance
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semiring
  signature: α] : MulZeroOneClass α
  body: inferInstance

中文:
实例 [半环
  签名: α] : 乘零幺类 α
  定义体: inferInstance
-/
instance [Semiring α] : MulZeroOneClass α := inferInstance
attribute [instance] Semiring.toAddCommMonoid Semiring.toMonoid

/-!
### Semirings
-/

section DistribMulOneClass

variable [Add α] [MulOneClass α]

/--
theorem `add_one_mul` / 定理 `add_one_mul`

English:
theorem add_one_mul
  given: [RightDistribClass α] (a b : α)
  statement: (a + 1) * b = a * b + b
  proof: by
  rw [add_mul]; rw [one_mul]

中文:
定理 add_one_mul
  条件: [RightDistrib类 α] (a b : α)
  结论: (a + 1) * b = a * b + b
  证明: by
  rw [add_mul]; rw [one_mul]

Depends on / 依赖: add_mul, one_mul
-/
theorem add_one_mul [RightDistribClass α] (a b : α) : (a + 1) * b = a * b + b := by
  rw [add_mul]; rw [one_mul]

/--
theorem `mul_add_one` / 定理 `mul_add_one`

English:
theorem mul_add_one
  given: [LeftDistribClass α] (a b : α)
  statement: a * (b + 1) = a * b + a
  proof: by
  rw [mul_add]; rw [mul_one]

中文:
定理 mul_add_one
  条件: [LeftDistrib类 α] (a b : α)
  结论: a * (b + 1) = a * b + a
  证明: by
  rw [mul_add]; rw [mul_one]

Depends on / 依赖: mul_add, mul_one
-/
theorem mul_add_one [LeftDistribClass α] (a b : α) : a * (b + 1) = a * b + a := by
  rw [mul_add]; rw [mul_one]

/--
theorem `one_add_mul` / 定理 `one_add_mul`

English:
theorem one_add_mul
  given: [RightDistribClass α] (a b : α)
  statement: (1 + a) * b = b + a * b
  proof: by
  rw [add_mul]; rw [one_mul]

中文:
定理 one_add_mul
  条件: [RightDistrib类 α] (a b : α)
  结论: (1 + a) * b = b + a * b
  证明: by
  rw [add_mul]; rw [one_mul]

Depends on / 依赖: add_mul, one_mul
-/
theorem one_add_mul [RightDistribClass α] (a b : α) : (1 + a) * b = b + a * b := by
  rw [add_mul]; rw [one_mul]

/--
theorem `mul_one_add` / 定理 `mul_one_add`

English:
theorem mul_one_add
  given: [LeftDistribClass α] (a b : α)
  statement: a * (1 + b) = a + a * b
  proof: by
  rw [mul_add]; rw [mul_one]

中文:
定理 mul_one_add
  条件: [LeftDistrib类 α] (a b : α)
  结论: a * (1 + b) = a + a * b
  证明: by
  rw [mul_add]; rw [mul_one]

Depends on / 依赖: mul_add, mul_one
-/
theorem mul_one_add [LeftDistribClass α] (a b : α) : a * (1 + b) = a + a * b := by
  rw [mul_add]; rw [mul_one]

end DistribMulOneClass

section NonAssocSemiring

variable [NonAssocSemiring α]

/--
theorem `two_mul` / 定理 `two_mul`

English:
theorem two_mul
  given: (n : α)
  statement: 2 * n = n + n
  proof: (congrArg₂ _ one_add_one_eq_two.symm rfl).trans (right_distrib 1 1 n).trans (by rw [one_mul])

中文:
定理 two_mul
  条件: (n : α)
  结论: 2 * n = n + n
  证明: (congrArg₂ _ one_add_one_eq_two.symm rfl).trans (right_distrib 1 1 n).trans (by rw [one_mul])

Depends on / 依赖: AlgebraicGeometry, Scheme, _root_, _root_.AlgebraicGeometry.Scheme.compactSpace_of_isAffine, compactSpace_of_isAffine, one_add_one_eq_two, one_add_one_eq_two.symm, one_mul, right_distrib
-/
theorem two_mul (n : α) : 2 * n = n + n :=
(congrArg₂ _ one_add_one_eq_two.symm rfl).trans (right_distrib 1 1 n).trans (by rw [one_mul])

/--
theorem `mul_two` / 定理 `mul_two`

English:
theorem mul_two
  given: (n : α)
  statement: n * 2 = n + n
  proof: (congrArg₂ _ rfl one_add_one_eq_two.symm).trans (left_distrib n 1 1).trans (by rw [mul_one])

中文:
定理 mul_two
  条件: (n : α)
  结论: n * 2 = n + n
  证明: (congrArg₂ _ rfl one_add_one_eq_two.symm).trans (left_distrib n 1 1).trans (by rw [mul_one])

Depends on / 依赖: left_distrib, mul_one, one_add_one_eq_two, one_add_one_eq_two.symm
-/
theorem mul_two (n : α) : n * 2 = n + n :=
(congrArg₂ _ rfl one_add_one_eq_two.symm).trans (left_distrib n 1 1).trans (by rw [mul_one])

/--
lemma `nsmul_eq_mul` / 引理 `nsmul_eq_mul`

English:
lemma nsmul_eq_mul
  given: (n : Nat) (a : α)
  statement: n • a = n * a
  proof: by
  induction n with
  | zero => rw [zero_nsmul, Nat.cast_zero, zero_mul]
  | succ n ih => rw [succ_nsmul, ih, Nat.cast_succ, add_mul, one_mul]

中文:
引理 nsmul_eq_mul
  条件: (n : 自然数) (a : α)
  结论: n • a = n * a
  证明: by
  induction n with
  | zero => rw [zero_nsmul, Nat.cast_zero, zero_mul]
  | succ n ih => rw [succ_nsmul, ih, Nat.cast_succ, add_mul, one_mul]
-/
@[simp] lemma nsmul_eq_mul (n : Nat) (a : α) : n • a = n * a := by
  induction n with
  | zero => rw [zero_nsmul, Nat.cast_zero, zero_mul]
  | succ n ih => rw [succ_nsmul, ih, Nat.cast_succ, add_mul, one_mul]

end NonAssocSemiring

section MulZeroClass
variable [MulZeroClass α] (P Q : Prop) [Decidable P] [Decidable Q] (a b : α)

/--
lemma `ite_zero_mul` / 引理 `ite_zero_mul`

English:
lemma ite_zero_mul
  statement: ite P a 0 * b = ite P (a * b) 0
  proof: by simp

中文:
引理 ite_zero_mul
  结论: ite P a 0 * b = ite P (a * b) 0
  证明: by simp
-/
lemma ite_zero_mul : ite P a 0 * b = ite P (a * b) 0 := by simp

/--
lemma `mul_ite_zero` / 引理 `mul_ite_zero`

English:
lemma mul_ite_zero
  statement: a * ite P b 0 = ite P (a * b) 0
  proof: by simp

中文:
引理 mul_ite_zero
  结论: a * ite P b 0 = ite P (a * b) 0
  证明: by simp
-/
lemma mul_ite_zero : a * ite P b 0 = ite P (a * b) 0 := by simp

/--
lemma `ite_zero_mul_ite_zero` / 引理 `ite_zero_mul_ite_zero`

English:
lemma ite_zero_mul_ite_zero
  statement: ite P a 0 * ite Q b 0 = ite (P ∧ Q) (a * b) 0
  proof: by
  simp only [← ite_and, ite_mul, mul_ite, mul_zero, zero_mul, and_comm]

中文:
引理 ite_zero_mul_ite_zero
  结论: ite P a 0 * ite Q b 0 = ite (P ∧ Q) (a * b) 0
  证明: by
  simp only [← ite_and, ite_mul, mul_ite, mul_zero, zero_mul, and_comm]

Depends on / 依赖: and_comm, ite_and, ite_mul, mul_ite, mul_zero, zero_mul
-/
lemma ite_zero_mul_ite_zero : ite P a 0 * ite Q b 0 = ite (P ∧ Q) (a * b) 0 := by
  simp only [← ite_and, ite_mul, mul_ite, mul_zero, zero_mul, and_comm]

end MulZeroClass

/--
theorem `mul_boole` / 定理 `mul_boole`

English:
theorem mul_boole
  given: {α} [MulZeroOneClass α] (P : Prop) [Decidable P] (a : α)
  proof: by simp

中文:
定理 mul_boole
  条件: {α} [乘零幺类 α] (P : 命题) [可判定 P] (a : α)
  证明: by simp
-/
theorem mul_boole {α} [MulZeroOneClass α] (P : Prop) [Decidable P] (a : α) :
    (a * if P then 1 else 0) = if P then a else 0 := by simp

/--
theorem `boole_mul` / 定理 `boole_mul`

English:
theorem boole_mul
  given: {α} [MulZeroOneClass α] (P : Prop) [Decidable P] (a : α)
  proof: by simp

中文:
定理 boole_mul
  条件: {α} [乘零幺类 α] (P : 命题) [可判定 P] (a : α)
  证明: by simp
-/
theorem boole_mul {α} [MulZeroOneClass α] (P : Prop) [Decidable P] (a : α) :
    (if P then 1 else 0) * a = if P then a else 0 := by simp

/--
Definition of `NonUnitalNonAssocCommSemiring` / `NonUnitalNonAssocCommSemiring` 的定义

English:
class NonUnitalNonAssocCommSemiring
  parameters: (α : Type u)
  extends: NonUnitalNonAssocSemiring α, CommMagma α
  (no additional axioms)

中文:
类 非幺非结合交换半环
  参数: (α : 类型u)
  继承: 非幺非结合半环 α, 交换原群 α
  (无附加公理)
-/
class NonUnitalNonAssocCommSemiring (α : Type u) extends NonUnitalNonAssocSemiring α, CommMagma α

attribute [instance 100] NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring

/--
Definition of `NonUnitalCommSemiring` / `NonUnitalCommSemiring` 的定义

English:
class NonUnitalCommSemiring
  parameters: (α : Type u)
  extends: NonUnitalSemiring α, CommSemigroup α
  (no additional axioms)

中文:
类 非幺交换半环
  参数: (α : 类型u)
  继承: 非幺半环 α, 交换半群 α
  (无附加公理)
-/
class NonUnitalCommSemiring (α : Type u) extends NonUnitalSemiring α, CommSemigroup α

/--
Definition of `NonAssocCommSemiring` / `NonAssocCommSemiring` 的定义

English:
class NonAssocCommSemiring
  parameters: (α : Type u)
  extends: NonAssocSemiring α, NonUnitalNonAssocCommSemiring α
  (no additional axioms)

中文:
类 非结合交换半环
  参数: (α : 类型u)
  继承: 非结合半环 α, 非幺非结合交换半环 α
  (无附加公理)
-/
class NonAssocCommSemiring (α : Type u)
  extends NonAssocSemiring α, NonUnitalNonAssocCommSemiring α

/--
Definition of `CommSemiring` / `CommSemiring` 的定义

English:
class CommSemiring
  parameters: (R : Type u)
  extends: Semiring R, CommMonoid R
  (no additional axioms)

中文:
类 交换半环
  参数: (R : 类型u)
  继承: 半环 R, 交换幺半群 R
  (无附加公理)
-/
class CommSemiring (R : Type u) extends Semiring R, CommMonoid R

attribute [instance 100] NonAssocCommSemiring.toNonAssocSemiring
attribute [instance 100] NonAssocCommSemiring.toNonUnitalNonAssocCommSemiring

-- see Note [lower instance priority]
instance (priority := 100) NonUnitalCommSemiring.toNonUnitalNonAssocCommSemiring
    [NonUnitalCommSemiring α] : NonUnitalNonAssocCommSemiring α where

-- see Note [lower instance priority]
instance (priority := 100) CommSemiring.toNonAssocCommSemiring [CommSemiring α] :
    NonAssocCommSemiring α where

-- see Note [lower instance priority]
instance (priority := 100) CommSemiring.toNonUnitalCommSemiring [CommSemiring α] :
    NonUnitalCommSemiring α :=
  { (inferInstance : CommMonoid α), (inferInstance : CommSemiring α) with }

-- see Note [lower instance priority]
instance (priority := 100) CommSemiring.toCommMonoidWithZero [CommSemiring α] :
    CommMonoidWithZero α :=
  { (inferInstance : CommMonoid α), (inferInstance : CommSemiring α) with }

section CommSemiring

variable [CommSemiring α]

/--
theorem `add_mul_self_eq` / 定理 `add_mul_self_eq`

English:
theorem add_mul_self_eq
  given: (a b : α)
  statement: (a + b) * (a + b) = a * a + 2 * a * b + b * b
  proof: by
  simp only [two_mul, add_mul, mul_add, add_assoc, mul_comm b]

中文:
定理 add_mul_self_eq
  条件: (a b : α)
  结论: (a + b) * (a + b) = a * a + 2 * a * b + b * b
  证明: by
  simp only [two_mul, add_mul, mul_add, add_assoc, mul_comm b]

Depends on / 依赖: add_assoc, add_mul, mul_add, mul_comm, two_mul
-/
theorem add_mul_self_eq (a b : α) : (a + b) * (a + b) = a * a + 2 * a * b + b * b := by
  simp only [two_mul, add_mul, mul_add, add_assoc, mul_comm b]

/--
lemma `add_sq` / 引理 `add_sq`

English:
lemma add_sq
  given: (a b : α)
  statement: (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2
  proof: by
  simp only [sq, add_mul_self_eq]

中文:
引理 add_sq
  条件: (a b : α)
  结论: (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2
  证明: by
  simp only [sq, add_mul_self_eq]

Depends on / 依赖: Algebra, Spec.structureSheaf, add_mul_self_eq, presheaf, presheaf.obj, structureSheaf
-/
lemma add_sq (a b : α) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  simp only [sq, add_mul_self_eq]

/--
lemma `add_sq'` / 引理 `add_sq'`

English:
lemma add_sq'
  given: (a b : α)
  statement: (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b
  proof: by
  rw [add_sq]; rw [add_assoc]; rw [add_comm _ (b ^ 2)]; rw [add_assoc]

alias add_pow_two := add_sq

中文:
引理 add_sq'
  条件: (a b : α)
  结论: (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b
  证明: by
  rw [add_sq]; rw [add_assoc]; rw [add_comm _ (b ^ 2)]; rw [add_assoc]

alias add_pow_two := add_sq

Depends on / 依赖: add_assoc, add_comm, add_sq
-/
lemma add_sq' (a b : α) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b := by
  rw [add_sq]; rw [add_assoc]; rw [add_comm _ (b ^ 2)]; rw [add_assoc]

alias add_pow_two := add_sq

end CommSemiring

section HasDistribNeg

/--
Definition of `HasDistribNeg` / `HasDistribNeg` 的定义

English:
class HasDistribNeg
  parameters: (α : Type*) [Mul α]
  extends: InvolutiveNeg α
  axioms and operations (2):
    - neg_mul : forall x y : α, -x * y = -(x * y)
    - mul_neg : forall x y : α, x * -y = -(x * y)

中文:
类 有DistribNeg
  参数: (α : 类型) [乘法 α]
  继承: InvolutiveNeg α
  公理与运算 (2 个):
    - neg_mul : 对任意 x y : α, -x * y = -(x * y)
    - mul_neg : 对任意 x y : α, x * -y = -(x * y)

Depends on / 依赖: IsLocalization, IsLocalization.Away, PrimeSpectrum, PrimeSpectrum.basicOpen, Spec.structureSheaf, basicOpen, obj.obj, structureSheaf
-/
class HasDistribNeg (α : Type*) [Mul α] extends InvolutiveNeg α where
  /-- Negation is left distributive over multiplication -/
  neg_mul : forall x y : α, -x * y = -(x * y)
  /-- Negation is right distributive over multiplication -/
  mul_neg : forall x y : α, x * -y = -(x * y)

section Mul

variable [Mul α] [HasDistribNeg α]

@[simp]
/--
theorem `neg_mul` / 定理 `neg_mul`

English:
theorem neg_mul
  given: (a b : α)
  statement: -a * b = -(a * b)
  proof: HasDistribNeg.neg_mul _ _

@[simp]

中文:
定理 neg_mul
  条件: (a b : α)
  结论: -a * b = -(a * b)
  证明: HasDistribNeg.neg_mul _ _

@[simp]

Depends on / 依赖: HasDistribNeg, HasDistribNeg.neg_mul, neg_mul
-/
theorem neg_mul (a b : α) : -a * b = -(a * b) :=
  HasDistribNeg.neg_mul _ _

@[simp]
/--
theorem `mul_neg` / 定理 `mul_neg`

English:
theorem mul_neg
  given: (a b : α)
  statement: a * -b = -(a * b)
  proof: HasDistribNeg.mul_neg _ _

中文:
定理 mul_neg
  条件: (a b : α)
  结论: a * -b = -(a * b)
  证明: HasDistribNeg.mul_neg _ _

Depends on / 依赖: HasDistribNeg, HasDistribNeg.mul_neg, mul_neg
-/
theorem mul_neg (a b : α) : a * -b = -(a * b) :=
  HasDistribNeg.mul_neg _ _

/--
theorem `neg_mul_neg` / 定理 `neg_mul_neg`

English:
theorem neg_mul_neg
  given: (a b : α)
  statement: -a * -b = a * b
  proof: by simp

中文:
定理 neg_mul_neg
  条件: (a b : α)
  结论: -a * -b = a * b
  证明: by simp
-/
theorem neg_mul_neg (a b : α) : -a * -b = a * b := by simp

/--
theorem `neg_mul_eq_neg_mul` / 定理 `neg_mul_eq_neg_mul`

English:
theorem neg_mul_eq_neg_mul
  given: (a b : α)
  statement: -(a * b) = -a * b
  proof: (neg_mul _ _).symm

中文:
定理 neg_mul_eq_neg_mul
  条件: (a b : α)
  结论: -(a * b) = -a * b
  证明: (neg_mul _ _).symm

Depends on / 依赖: neg_mul
-/
theorem neg_mul_eq_neg_mul (a b : α) : -(a * b) = -a * b :=
  (neg_mul _ _).symm

/--
theorem `neg_mul_eq_mul_neg` / 定理 `neg_mul_eq_mul_neg`

English:
theorem neg_mul_eq_mul_neg
  given: (a b : α)
  statement: -(a * b) = a * -b
  proof: (mul_neg _ _).symm

中文:
定理 neg_mul_eq_mul_neg
  条件: (a b : α)
  结论: -(a * b) = a * -b
  证明: (mul_neg _ _).symm

Depends on / 依赖: mul_neg
-/
theorem neg_mul_eq_mul_neg (a b : α) : -(a * b) = a * -b :=
  (mul_neg _ _).symm

/--
theorem `neg_mul_comm` / 定理 `neg_mul_comm`

English:
theorem neg_mul_comm
  given: (a b : α)
  statement: -a * b = a * -b
  proof: by simp

中文:
定理 neg_mul_comm
  条件: (a b : α)
  结论: -a * b = a * -b
  证明: by simp
-/
theorem neg_mul_comm (a b : α) : -a * b = a * -b := by simp

end Mul

section MulOneClass

variable [MulOneClass α] [HasDistribNeg α]

/--
theorem `neg_eq_neg_one_mul` / 定理 `neg_eq_neg_one_mul`

English:
theorem neg_eq_neg_one_mul
  given: (a : α)
  statement: -a = -1 * a
  proof: by simp

中文:
定理 neg_eq_neg_one_mul
  条件: (a : α)
  结论: -a = -1 * a
  证明: by simp
-/
theorem neg_eq_neg_one_mul (a : α) : -a = -1 * a := by simp

/--
theorem `mul_neg_one` / 定理 `mul_neg_one`

English:
theorem mul_neg_one
  given: (a : α)
  statement: a * -1 = -a
  proof: by simp

中文:
定理 mul_neg_one
  条件: (a : α)
  结论: a * -1 = -a
  证明: by simp
-/
theorem mul_neg_one (a : α) : a * -1 = -a := by simp

/--
theorem `neg_one_mul` / 定理 `neg_one_mul`

English:
theorem neg_one_mul
  given: (a : α)
  statement: -1 * a = -a
  proof: by simp

中文:
定理 neg_one_mul
  条件: (a : α)
  结论: -1 * a = -a
  证明: by simp
-/
theorem neg_one_mul (a : α) : -1 * a = -a := by simp

end MulOneClass

section MulZeroClass

variable [MulZeroClass α] [HasDistribNeg α]

instance (priority := 100) MulZeroClass.negZeroClass : NegZeroClass α where
  __ := (inferInstance : Zero α); __ := (inferInstance : InvolutiveNeg α)
  neg_zero := by rw [← zero_mul (0 : α), ← neg_mul, mul_zero, mul_zero]

end MulZeroClass

end HasDistribNeg

/-!
### Rings
-/

section NonUnitalNonAssocRing

variable [NonUnitalNonAssocRing α]

instance (priority := 100) NonUnitalNonAssocRing.toHasDistribNeg : HasDistribNeg α where
  neg_neg := neg_neg
neg_mul a b := eq_neg_of_add_eq_zero_left by rw [← right_distrib, neg_add_cancel, zero_mul]
mul_neg a b := eq_neg_of_add_eq_zero_left by rw [← left_distrib, neg_add_cancel, mul_zero]

/--
theorem `mul_sub_left_distrib` / 定理 `mul_sub_left_distrib`

English:
theorem mul_sub_left_distrib
  given: (a b c : α)
  statement: a * (b - c) = a * b - a * c
  proof: by
  simpa only [sub_eq_add_neg, neg_mul_eq_mul_neg] using mul_add a b (-c)

alias mul_sub := mul_sub_left_distrib

中文:
定理 mul_sub_left_distrib
  条件: (a b c : α)
  结论: a * (b - c) = a * b - a * c
  证明: by
  simpa only [sub_eq_add_neg, neg_mul_eq_mul_neg] using mul_add a b (-c)

alias mul_sub := mul_sub_left_distrib

Depends on / 依赖: mul_add, neg_mul_eq_mul_neg, sub_eq_add_neg
-/
theorem mul_sub_left_distrib (a b c : α) : a * (b - c) = a * b - a * c := by
  simpa only [sub_eq_add_neg, neg_mul_eq_mul_neg] using mul_add a b (-c)

alias mul_sub := mul_sub_left_distrib

/--
theorem `mul_sub_right_distrib` / 定理 `mul_sub_right_distrib`

English:
theorem mul_sub_right_distrib
  given: (a b c : α)
  statement: (a - b) * c = a * c - b * c
  proof: by
  simpa only [sub_eq_add_neg, neg_mul_eq_neg_mul] using add_mul a (-b) c

alias sub_mul := mul_sub_right_distrib

中文:
定理 mul_sub_right_distrib
  条件: (a b c : α)
  结论: (a - b) * c = a * c - b * c
  证明: by
  simpa only [sub_eq_add_neg, neg_mul_eq_neg_mul] using add_mul a (-b) c

alias sub_mul := mul_sub_right_distrib

Depends on / 依赖: add_mul, neg_mul_eq_neg_mul, sub_eq_add_neg
-/
theorem mul_sub_right_distrib (a b c : α) : (a - b) * c = a * c - b * c := by
  simpa only [sub_eq_add_neg, neg_mul_eq_neg_mul] using add_mul a (-b) c

alias sub_mul := mul_sub_right_distrib

end NonUnitalNonAssocRing

section NonAssocRing

variable [NonAssocRing α]

/--
theorem `sub_one_mul` / 定理 `sub_one_mul`

English:
theorem sub_one_mul
  given: (a b : α)
  statement: (a - 1) * b = a * b - b
  proof: by rw [sub_mul, one_mul]

中文:
定理 sub_one_mul
  条件: (a b : α)
  结论: (a - 1) * b = a * b - b
  证明: by rw [sub_mul, one_mul]

Depends on / 依赖: one_mul, sub_mul
-/
theorem sub_one_mul (a b : α) : (a - 1) * b = a * b - b := by rw [sub_mul, one_mul]

/--
theorem `mul_sub_one` / 定理 `mul_sub_one`

English:
theorem mul_sub_one
  given: (a b : α)
  statement: a * (b - 1) = a * b - a
  proof: by rw [mul_sub, mul_one]

中文:
定理 mul_sub_one
  条件: (a b : α)
  结论: a * (b - 1) = a * b - a
  证明: by rw [mul_sub, mul_one]

Depends on / 依赖: mul_one, mul_sub
-/
theorem mul_sub_one (a b : α) : a * (b - 1) = a * b - a := by rw [mul_sub, mul_one]

/--
theorem `one_sub_mul` / 定理 `one_sub_mul`

English:
theorem one_sub_mul
  given: (a b : α)
  statement: (1 - a) * b = b - a * b
  proof: by rw [sub_mul, one_mul]

中文:
定理 one_sub_mul
  条件: (a b : α)
  结论: (1 - a) * b = b - a * b
  证明: by rw [sub_mul, one_mul]

Depends on / 依赖: one_mul, sub_mul
-/
theorem one_sub_mul (a b : α) : (1 - a) * b = b - a * b := by rw [sub_mul, one_mul]

/--
theorem `mul_one_sub` / 定理 `mul_one_sub`

English:
theorem mul_one_sub
  given: (a b : α)
  statement: a * (1 - b) = a - a * b
  proof: by rw [mul_sub, mul_one]

中文:
定理 mul_one_sub
  条件: (a b : α)
  结论: a * (1 - b) = a - a * b
  证明: by rw [mul_sub, mul_one]

Depends on / 依赖: mul_one, mul_sub
-/
theorem mul_one_sub (a b : α) : a * (1 - b) = a - a * b := by rw [mul_sub, mul_one]

/--
lemma `mul_one_sub_mul` / 引理 `mul_one_sub_mul`

English:
lemma mul_one_sub_mul
  given: (a b c : α)
  statement: a * (1 - b) * c = a * c - a * b * c
  proof: by
  rw [mul_one_sub]; rw [sub_mul]

中文:
引理 mul_one_sub_mul
  条件: (a b c : α)
  结论: a * (1 - b) * c = a * c - a * b * c
  证明: by
  rw [mul_one_sub]; rw [sub_mul]

Depends on / 依赖: mul_one_sub, sub_mul
-/
lemma mul_one_sub_mul (a b c : α) : a * (1 - b) * c = a * c - a * b * c := by
  rw [mul_one_sub]; rw [sub_mul]

end NonAssocRing

section Ring

variable [Ring α]

-- A (unital, associative) ring is a not-necessarily-unital ring
-- see Note [lower instance priority]
instance (priority := 100) Ring.toNonUnitalRing : NonUnitalRing α :=
  { ‹Ring α› with }

-- A (unital, associative) ring is a not-necessarily-associative ring
-- see Note [lower instance priority]
instance (priority := 100) Ring.toNonAssocRing : NonAssocRing α :=
  { ‹Ring α› with }

end Ring

/--
Definition of `NonUnitalNonAssocCommRing` / `NonUnitalNonAssocCommRing` 的定义

English:
class NonUnitalNonAssocCommRing
  parameters: (α : Type u)
  extends: NonUnitalNonAssocRing α, NonUnitalNonAssocCommSemiring α
  (no additional axioms)

中文:
类 非幺非结合交换环
  参数: (α : 类型u)
  继承: 非幺非结合环 α, 非幺非结合交换半环 α
  (无附加公理)
-/
class NonUnitalNonAssocCommRing (α : Type u)
  extends NonUnitalNonAssocRing α, NonUnitalNonAssocCommSemiring α

/--
Definition of `NonUnitalCommRing` / `NonUnitalCommRing` 的定义

English:
class NonUnitalCommRing
  parameters: (α : Type u)
  extends: NonUnitalRing α, NonUnitalNonAssocCommRing α
  (no additional axioms)

中文:
类 非幺交换环
  参数: (α : 类型u)
  继承: 非幺环 α, 非幺非结合交换环 α
  (无附加公理)
-/
class NonUnitalCommRing (α : Type u) extends NonUnitalRing α, NonUnitalNonAssocCommRing α

/--
Definition of `NonAssocCommRing` / `NonAssocCommRing` 的定义

English:
class NonAssocCommRing
  parameters: (α : Type u)
  extends: NonAssocRing α, NonUnitalNonAssocCommRing α, NonAssocCommSemiring α
  (no additional axioms)

中文:
类 非结合交换环
  参数: (α : 类型u)
  继承: 非结合环 α, 非幺非结合交换环 α, 非结合交换半环 α
  (无附加公理)
-/
class NonAssocCommRing (α : Type u)
  extends NonAssocRing α, NonUnitalNonAssocCommRing α, NonAssocCommSemiring α

attribute [instance 100] NonAssocCommRing.toNonAssocRing
attribute [instance 100] NonAssocCommRing.toNonUnitalNonAssocCommRing
attribute [instance 100] NonAssocCommRing.toNonAssocCommSemiring

-- see Note [lower instance priority]
instance (priority := 100) NonUnitalCommRing.toNonUnitalCommSemiring [s : NonUnitalCommRing α] :
    NonUnitalCommSemiring α :=
  { s with }

/-- A commutative ring is a ring with commutative multiplication. -/
@[wikidata Q858656]
/--
Definition of `CommRing` / `CommRing` 的定义

English:
class CommRing
  parameters: (α : Type u)
  extends: Ring α, CommMonoid α
  (no additional axioms)

中文:
类 交换环
  参数: (α : 类型u)
  继承: 环 α, 交换幺半群 α
  (无附加公理)
-/
class CommRing (α : Type u) extends Ring α, CommMonoid α

instance (priority := 100) CommRing.toNonAssocCommRing [CommRing α] : NonAssocCommRing α where

instance (priority := 100) CommRing.toCommSemiring [s : CommRing α] : CommSemiring α :=
  { s with }

-- see Note [lower instance priority]
instance (priority := 100) CommRing.toNonUnitalCommRing [s : CommRing α] : NonUnitalCommRing α :=
  { s with }

-- see Note [lower instance priority]
instance (priority := 100) CommRing.toAddCommGroupWithOne [s : CommRing α] :
    AddCommGroupWithOne α :=
  { s with }

/-- A domain is a nontrivial semiring such that multiplication by a nonzero element
is cancellative on both sides. In other words, a nontrivial semiring `R` satisfying
`∀ {a b c : R}, a ≠ 0 → a * b = a * c → b = c` and
`∀ {a b c : R}, b ≠ 0 → a * b = c * b → a = c`.

This is implemented as a mixin for `Semiring α`.
To obtain an integral domain use `[CommRing α] [IsDomain α]`. -/
@[stacks 09FE]
/--
Definition of `IsDomain` / `IsDomain` 的定义

English:
class IsDomain
  parameters: (α : Type u) [Semiring α]
  extends: IsCancelMulZero α, Nontrivial α
  (no additional axioms)

中文:
类 是整环
  参数: (α : 类型u) [半环 α]
  继承: 是乘零消去 α, 非平凡 α
  (无附加公理)
-/
class IsDomain (α : Type u) [Semiring α] : Prop extends IsCancelMulZero α, Nontrivial α

namespace IsMulCommutative

/-- A `NonUnitalNonAssocSemiring` which `IsMulCommutative` is a `NonUnitalNonAssocCommSemiring`.

This is primarily used to deduce the bundled version from the unbundled one for commutative
subobjects in a noncommutative ambient type. As such this is only available inside the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthesis for bundled
commutativity.

See note [commutative subobjects]. -/
scoped instance (priority := 50) [NonUnitalNonAssocSemiring R] [IsMulCommutative R] :
    NonUnitalNonAssocCommSemiring R where

/-- A `NonUnitalSemiring` which `IsMulCommutative` is a `NonUnitalCommSemiring`.

This is primarily used to deduce the bundled version from the unbundled one for commutative
subobjects in a noncommutative ambient type. As such this is only available inside the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthesis for bundled
commutativity.

See note [commutative subobjects]. -/
scoped instance (priority := 50) [NonUnitalSemiring R] [IsMulCommutative R] :
    NonUnitalCommSemiring R where

/-- A `NonUnitalNonAssocRing` which `IsMulCommutative` is a `NonUnitalNonAssocCommRing`.

This is primarily used to deduce the bundled version from the unbundled one for commutative
subobjects in a noncommutative ambient type. As such this is only available inside the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthesis for bundled
commutativity.

See note [commutative subobjects]. -/
scoped instance (priority := 50) [NonUnitalNonAssocRing R] [IsMulCommutative R] :
    NonUnitalNonAssocCommRing R where

/-- A `NonUnitalRing` which `IsMulCommutative` is a `NonUnitalCommRing`.

This is primarily used to deduce the bundled version from the unbundled one for commutative
subobjects in a noncommutative ambient type. As such this is only available inside the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthesis for bundled
commutativity.

See note [commutative subobjects]. -/
scoped instance (priority := 50) [NonUnitalRing R] [IsMulCommutative R] :
    NonUnitalCommRing R where

/-- A `NonAssocSemiring` which `IsMulCommutative` is a `NonAssocCommSemiring`.

This is primarily used to deduce the bundled version from the unbundled one for commutative
subobjects in a noncommutative ambient type. As such this is only available inside the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthesis for bundled
commutativity.

See note [commutative subobjects]. -/
scoped instance (priority := 50) [NonAssocSemiring R] [IsMulCommutative R] :
    NonAssocCommSemiring R where

/-- A `Semiring` which `IsMulCommutative` is a `CommSemiring`.

This is primarily used to deduce the bundled version from the unbundled one for commutative
subobjects in a noncommutative ambient type. As such this is only available inside the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthesis for bundled
commutativity.

See note [commutative subobjects]. -/
scoped instance (priority := 50) [Semiring R] [IsMulCommutative R] :
    CommSemiring R where

/-- A `NonAssocRing` which `IsMulCommutative` is a `NonAssocCommRing`.

This is primarily used to deduce the bundled version from the unbundled one for commutative
subobjects in a noncommutative ambient type. As such this is only available inside the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthesis for bundled
commutativity.

See note [commutative subobjects]. -/
scoped instance (priority := 50) [NonAssocRing R] [IsMulCommutative R] :
    NonAssocCommRing R where

/-- A `Ring` which `IsMulCommutative` is a `CommRing`.

This is primarily used to deduce the bundled version from the unbundled one for commutative
subobjects in a noncommutative ambient type. As such this is only available inside the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthesis for bundled
commutativity.

See note [commutative subobjects]. -/
scoped instance (priority := 50) [Ring R] [IsMulCommutative R] :
    CommRing R where

end IsMulCommutative
