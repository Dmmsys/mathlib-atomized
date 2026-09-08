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


/-- A typeclass stating that multiplication is left and right distributive
over addition. -/
/-
**Distrib** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_1 → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A typeclass stating that multiplication is left and right distributive
over addition.
-/
class Distrib (R : Type*) extends Mul R, Add R where
  /-- Multiplication is left distributive over addition -/
  protected left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
  /-- Multiplication is right distributive over addition -/
  protected right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

/-- A typeclass stating that multiplication is left distributive over addition. -/
/-
**LeftDistribClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) → [Mul R] → [Add R] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A typeclass stating that multiplication is left distributive over addition.
-/
class LeftDistribClass (R : Type*) [Mul R] [Add R] : Prop where
  /-- Multiplication is left distributive over addition -/
  protected left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c

/-- A typeclass stating that multiplication is right distributive over addition. -/
/-
**RightDistribClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) → [Mul R] → [Add R] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A typeclass stating that multiplication is right distributive over addition.
-/
class RightDistribClass (R : Type*) [Mul R] [Add R] : Prop where
  /-- Multiplication is right distributive over addition -/
  protected right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) Distrib.leftDistribClass (R : Type*) [Distrib R] : LeftDistribClass R :=
  ⟨Distrib.left_distrib⟩

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) Distrib.rightDistribClass (R : Type*) [Distrib R] :
    RightDistribClass R :=
  ⟨Distrib.right_distrib⟩
/-
**left_distrib** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：left_distrib [Mul R] [Add R] [LeftDistribClass R] (a b c : R) : a * (b + c
) = a * b + a * c
参数：a b c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LeftDistribClass.left_distrib`：∀ {R : Type u_1} {inst : Mul R} {inst_1 :
 Add R} [self : LeftDistribClass R] (a b c : R), a * (b + c) = a * b + a * c
-/
theorem left_distrib [Mul R] [Add R] [LeftDistribClass R] (a b c : R) :
    a * (b + c) = a * b + a * c :=
  LeftDistribClass.left_distrib a b c

alias mul_add := left_distrib
/-
**right_distrib** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：right_distrib [Mul R] [Add R] [RightDistribClass R] (a b c : R) : (a + b) 
* c = a * c + b * c
参数：a b c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RightDistribClass.right_distrib`：∀ {R : Type u_1} {inst : Mul R} {inst_1
 : Add R} [self : RightDistribClass R] (a b c : R), (a + b) * c = a * c + b * c
-/
theorem right_distrib [Mul R] [Add R] [RightDistribClass R] (a b c : R) :
    (a + b) * c = a * c + b * c :=
  RightDistribClass.right_distrib a b c

alias add_mul := right_distrib
/-
**distrib_three_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：distrib_three_right [Mul R] [Add R] [RightDistribClass R] (a b c d : R) : 
(a + b + c) * d = a * d + b * d + c * d
参数：a b c d : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `right_distrib`：right_distrib [Mul R] [Add R] [RightDistribClass R] (a b 
c : R) : (a + b) * c = a * c + b * c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
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

/-- A not-necessarily-unital, not-necessarily-associative semiring. See `CommutatorRing` and the
  documentation thereof in case you need a `NonUnitalNonAssocSemiring` instance on a Lie ring
  or a Lie algebra. -/
/-
**NonUnitalNonAssocSemiring** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A not-necessarily-unital, not-necessarily-associative semiring. See `CommutatorR
ing` and the
  documentation thereof in case you need a `NonUnitalNonAssocSemiring` instance 
on a Lie ring
  or a Lie algebra.
-/
class NonUnitalNonAssocSemiring (α : Type u) extends AddCommMonoid α, Distrib α, MulZeroClass α

/-- An associative but not-necessarily unital semiring. -/
/-
**NonUnitalSemiring** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An associative but not-necessarily unital semiring.
-/
class NonUnitalSemiring (α : Type u) extends NonUnitalNonAssocSemiring α, SemigroupWithZero α

/-- A unital but not-necessarily-associative semiring. -/
/-
**NonAssocSemiring** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A unital but not-necessarily-associative semiring.
-/
class NonAssocSemiring (α : Type u) extends NonUnitalNonAssocSemiring α, MulZeroOneClass α,
    AddCommMonoidWithOne α

/-- A not-necessarily-unital, not-necessarily-associative ring. -/
/-
**NonUnitalNonAssocRing** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A not-necessarily-unital, not-necessarily-associative ring.
-/
class NonUnitalNonAssocRing (α : Type u) extends AddCommGroup α, NonUnitalNonAssocSemiring α

/-- An associative but not-necessarily unital ring. -/
/-
**NonUnitalRing** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_1 → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An associative but not-necessarily unital ring.
-/
class NonUnitalRing (α : Type*) extends NonUnitalNonAssocRing α, NonUnitalSemiring α

/-- A unital but not-necessarily-associative ring. -/
/-
**NonAssocRing** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_1 → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A unital but not-necessarily-associative ring.
-/
class NonAssocRing (α : Type*) extends NonUnitalNonAssocRing α, NonAssocSemiring α,
    AddCommGroupWithOne α

/-- A `Semiring` is a type with addition, multiplication, a `0` and a `1` where addition is
commutative and associative, multiplication is associative and left and right distributive over
addition, and `0` and `1` are additive and multiplicative identities. -/
/-
**Semiring** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Semiring` is a type with addition, multiplication, a `0` and a `1` where addi
tion is
commutative and associative, multiplication is associative and left and right di
stributive over
addition, and `0` and `1` are additive and multiplicative identities.
-/
class Semiring (α : Type u) extends AddCommMonoid α, MonoidWithZero α, NonUnitalSemiring α,
  NonAssocSemiring α

/-- A `Ring` is a `Semiring` with negation making it an additive group. -/
@[wikidata Q161172]
/-
**Ring** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Ring` is a `Semiring` with negation making it an additive group.
-/
class Ring (R : Type u) extends Semiring R, AddCommGroup R, AddGroupWithOne R

-- Add some short-cut instances to avoid going through the less used ring type classes.
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semiring α] : Distrib α := inferInstance
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semiring α] : MulZeroClass α := inferInstance
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semiring α] : MulZeroOneClass α := inferInstance
attribute [instance] Semiring.toAddCommMonoid Semiring.toMonoid

/-!
### Semirings
-/

section DistribMulOneClass

variable [Add α] [MulOneClass α]

/-
**add_one_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：add_one_mul [RightDistribClass α] (a b : α) : (a + 1) * b = a * b + b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem add_one_mul [RightDistribClass α] (a b : α) : (a + 1) * b = a * b + b := by
  rw [add_mul, one_mul]
/-
**mul_add_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_add_one [LeftDistribClass α] (a b : α) : a * (b + 1) = a * b + a
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem mul_add_one [LeftDistribClass α] (a b : α) : a * (b + 1) = a * b + a := by
  rw [mul_add, mul_one]
/-
**one_add_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_add_mul [RightDistribClass α] (a b : α) : (1 + a) * b = b + a * b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem one_add_mul [RightDistribClass α] (a b : α) : (1 + a) * b = b + a * b := by
  rw [add_mul, one_mul]
/-
**mul_one_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_one_add [LeftDistribClass α] (a b : α) : a * (1 + b) = a + a * b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem mul_one_add [LeftDistribClass α] (a b : α) : a * (1 + b) = a + a * b := by
  rw [mul_add, mul_one]

end DistribMulOneClass

section NonAssocSemiring

variable [NonAssocSemiring α]

/-
**two_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：two_mul (n : α) : 2 * n = n + n
参数：n : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → γ
) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_add_one_eq_two`：one_add_one_eq_two [AddMonoidWithOne R] : 1 + 1 = (2
 : R)
· 使用定理 `right_distrib`：right_distrib [Mul R] [Add R] [RightDistribClass R] (a b 
c : R) : (a + b) * c = a * c + b * c
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem two_mul (n : α) : 2 * n = n + n :=
  (congrArg₂ _ one_add_one_eq_two.symm rfl).trans <| (right_distrib 1 1 n).trans (by rw [one_mul])
/-
**mul_two** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_two (n : α) : n * 2 = n + n
参数：n : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → γ
) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_add_one_eq_two`：one_add_one_eq_two [AddMonoidWithOne R] : 1 + 1 = (2
 : R)
· 使用定理 `left_distrib`：left_distrib [Mul R] [Add R] [LeftDistribClass R] (a b c :
 R) : a * (b + c) = a * b + a * c
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem mul_two (n : α) : n * 2 = n + n :=
  (congrArg₂ _ rfl one_add_one_eq_two.symm).trans <| (left_distrib n 1 1).trans (by rw [mul_one])
/-
**nsmul_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α), n • a = ↑n * a
参数：n : ℕ；a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 0 • a = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `succ_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (n : ℕ), (n + 
1) • a = n • a + a
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
@[simp] lemma nsmul_eq_mul (n : ℕ) (a : α) : n • a = n * a := by
  induction n with
  | zero => rw [zero_nsmul, Nat.cast_zero, zero_mul]
  | succ n ih => rw [succ_nsmul, ih, Nat.cast_succ, add_mul, one_mul]

end NonAssocSemiring

section MulZeroClass
variable [MulZeroClass α] (P Q : Prop) [Decidable P] [Decidable Q] (a b : α)

/-
**ite_zero_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ite_zero_mul : ite P a 0 * b = ite P (a * b) 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ite_zero_mul : ite P a 0 * b = ite P (a * b) 0 := by simp
/-
**mul_ite_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_ite_zero : a * ite P b 0 = ite P (a * b) 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mul_ite_zero : a * ite P b 0 = ite P (a * b) 0 := by simp
/-
**ite_zero_mul_ite_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ite_zero_mul_ite_zero : ite P a 0 * ite Q b 0 = ite (P ∧ Q) (a * b) 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ite_zero_mul_ite_zero : ite P a 0 * ite Q b 0 = ite (P ∧ Q) (a * b) 0 := by
  simp only [← ite_and, ite_mul, mul_ite, mul_zero, zero_mul, and_comm]

end MulZeroClass

/-
**mul_boole** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_boole {α} [MulZeroOneClass α] (P : Prop) [Decidable P] (a : α) : (a * 
if P then 1 else 0) = if P then a else 0
参数：P : Prop；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_boole {α} [MulZeroOneClass α] (P : Prop) [Decidable P] (a : α) :
    (a * if P then 1 else 0) = if P then a else 0 := by simp
/-
**boole_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：boole_mul {α} [MulZeroOneClass α] (P : Prop) [Decidable P] (a : α) : (if P
 then 1 else 0) * a = if P then a else 0
参数：P : Prop；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem boole_mul {α} [MulZeroOneClass α] (P : Prop) [Decidable P] (a : α) :
    (if P then 1 else 0) * a = if P then a else 0 := by simp

/-- A not-necessarily-unital, not-necessarily-associative, but commutative semiring. -/
/-
**NonUnitalNonAssocCommSemiring** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A not-necessarily-unital, not-necessarily-associative, but commutative semiring.
-/
class NonUnitalNonAssocCommSemiring (α : Type u) extends NonUnitalNonAssocSemiring α, CommMagma α

attribute [instance 100] NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring

/-- A non-unital commutative semiring is a `NonUnitalSemiring` with commutative multiplication.
In other words, it is a type with the following structures: additive commutative monoid
(`AddCommMonoid`), commutative semigroup (`CommSemigroup`), distributive laws (`Distrib`), and
multiplication by zero law (`MulZeroClass`). -/
/-
**NonUnitalCommSemiring** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-unital commutative semiring is a `NonUnitalSemiring` with commutative mult
iplication.
In other words, it is a type with the following structures: additive commutative
 monoid
(`AddCommMonoid`), commutative semigroup (`CommSemigroup`), distributive laws (`
Distrib`), and
multiplication by zero law (`MulZeroClass`).
-/
class NonUnitalCommSemiring (α : Type u) extends NonUnitalSemiring α, CommSemigroup α

/-- A non-associative commutative semiring is a `NonAssocSemiring` with commutative
multiplication. -/
/-
**NonAssocCommSemiring** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-associative commutative semiring is a `NonAssocSemiring` with commutative
multiplication.
-/
class NonAssocCommSemiring (α : Type u)
  extends NonAssocSemiring α, NonUnitalNonAssocCommSemiring α

/-- A commutative semiring is a semiring with commutative multiplication. -/
/-
**CommSemiring** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A commutative semiring is a semiring with commutative multiplication.
-/
class CommSemiring (R : Type u) extends Semiring R, CommMonoid R

attribute [instance 100] NonAssocCommSemiring.toNonAssocSemiring
attribute [instance 100] NonAssocCommSemiring.toNonUnitalNonAssocCommSemiring

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) NonUnitalCommSemiring.toNonUnitalNonAssocCommSemiring
    [NonUnitalCommSemiring α] : NonUnitalNonAssocCommSemiring α where

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) CommSemiring.toNonAssocCommSemiring [CommSemiring α] :
    NonAssocCommSemiring α where

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) CommSemiring.toNonUnitalCommSemiring [CommSemiring α] :
    NonUnitalCommSemiring α :=
  { (inferInstance : CommMonoid α), (inferInstance : CommSemiring α) with }

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) CommSemiring.toCommMonoidWithZero [CommSemiring α] :
    CommMonoidWithZero α :=
  { (inferInstance : CommMonoid α), (inferInstance : CommSemiring α) with }

section CommSemiring

variable [CommSemiring α]

/-
**add_mul_self_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：add_mul_self_eq (a b : α) : (a + b) * (a + b) = a * a + 2 * a * b + b * b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem add_mul_self_eq (a b : α) : (a + b) * (a + b) = a * a + 2 * a * b + b * b := by
  simp only [two_mul, add_mul, mul_add, add_assoc, mul_comm b]
/-
**add_sq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：add_sq (a b : α) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `add_mul_self_eq`：add_mul_self_eq (a b : α) : (a + b) * (a + b) = a * a +
 2 * a * b + b * b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma add_sq (a b : α) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  simp only [sq, add_mul_self_eq]
/-
**add_sq'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：add_sq' (a b : α) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `add_sq`：add_sq (a b : α) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
lemma add_sq' (a b : α) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b := by
  rw [add_sq, add_assoc, add_comm _ (b ^ 2), add_assoc]

alias add_pow_two := add_sq

end CommSemiring

section HasDistribNeg

/-- Typeclass for a negation operator that distributes across multiplication.

This is useful for dealing with submonoids of a ring that contain `-1` without having to duplicate
lemmas. -/
/-
**HasDistribNeg** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_1) → [Mul α] → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for a negation operator that distributes across multiplication.

This is useful for dealing with submonoids of a ring that contain `-1` without h
aving to duplicate
lemmas.
-/
class HasDistribNeg (α : Type*) [Mul α] extends InvolutiveNeg α where
  /-- Negation is left distributive over multiplication -/
  neg_mul : ∀ x y : α, -x * y = -(x * y)
  /-- Negation is right distributive over multiplication -/
  mul_neg : ∀ x y : α, x * -y = -(x * y)

section Mul

variable [Mul α] [HasDistribNeg α]

@[simp]
/-
**neg_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：neg_mul (a b : α) : -a * b = -(a * b)
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDistribNeg.neg_mul`：∀ {α : Type u_1} {inst : Mul α} [self : HasDistri
bNeg α] (x y : α), -x * y = -(x * y)
-/
theorem neg_mul (a b : α) : -a * b = -(a * b) :=
  HasDistribNeg.neg_mul _ _

@[simp]
/-
**mul_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_neg (a b : α) : a * -b = -(a * b)
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDistribNeg.mul_neg`：∀ {α : Type u_1} {inst : Mul α} [self : HasDistri
bNeg α] (x y : α), x * -y = -(x * y)
-/
theorem mul_neg (a b : α) : a * -b = -(a * b) :=
  HasDistribNeg.mul_neg _ _
/-
**neg_mul_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：neg_mul_neg (a b : α) : -a * -b = a * b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem neg_mul_neg (a b : α) : -a * -b = a * b := by simp
/-
**neg_mul_eq_neg_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：neg_mul_eq_neg_mul (a b : α) : -(a * b) = -a * b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
-/
theorem neg_mul_eq_neg_mul (a b : α) : -(a * b) = -a * b :=
  (neg_mul _ _).symm
/-
**neg_mul_eq_mul_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：neg_mul_eq_mul_neg (a b : α) : -(a * b) = a * -b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
-/
theorem neg_mul_eq_mul_neg (a b : α) : -(a * b) = a * -b :=
  (mul_neg _ _).symm
/-
**neg_mul_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：neg_mul_comm (a b : α) : -a * b = a * -b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem neg_mul_comm (a b : α) : -a * b = a * -b := by simp

end Mul

section MulOneClass

variable [MulOneClass α] [HasDistribNeg α]

/-
**neg_eq_neg_one_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：neg_eq_neg_one_mul (a : α) : -a = -1 * a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem neg_eq_neg_one_mul (a : α) : -a = -1 * a := by simp

/-- An element of a ring multiplied by the additive inverse of one is the element's additive
  inverse. -/
/-
**mul_neg_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_neg_one (a : α) : a * -1 = -a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
An element of a ring multiplied by the additive inverse of one is the element's 
additive
  inverse.
-/
theorem mul_neg_one (a : α) : a * -1 = -a := by simp

/-- The additive inverse of one multiplied by an element of a ring is the element's additive
  inverse. -/
/-
**neg_one_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：neg_one_mul (a : α) : -1 * a = -a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The additive inverse of one multiplied by an element of a ring is the element's 
additive
  inverse.
-/
theorem neg_one_mul (a : α) : -1 * a = -a := by simp

end MulOneClass

section MulZeroClass

variable [MulZeroClass α] [HasDistribNeg α]

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
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

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) NonUnitalNonAssocRing.toHasDistribNeg : HasDistribNeg α where
  neg_neg := neg_neg
  neg_mul a b := eq_neg_of_add_eq_zero_left <| by rw [← right_distrib, neg_add_cancel, zero_mul]
  mul_neg a b := eq_neg_of_add_eq_zero_left <| by rw [← left_distrib, neg_add_cancel, mul_zero]
/-
**mul_sub_left_distrib** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_sub_left_distrib (a b c : α) : a * (b - c) = a * b - a * c
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_mul_eq_mul_neg`：neg_mul_eq_mul_neg (a b : α) : -(a * b) = a * -b
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
-/
theorem mul_sub_left_distrib (a b c : α) : a * (b - c) = a * b - a * c := by
  simpa only [sub_eq_add_neg, neg_mul_eq_mul_neg] using mul_add a b (-c)

alias mul_sub := mul_sub_left_distrib
/-
**mul_sub_right_distrib** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_sub_right_distrib (a b c : α) : (a - b) * c = a * c - b * c
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_mul_eq_neg_mul`：neg_mul_eq_neg_mul (a b : α) : -(a * b) = -a * b
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
-/
theorem mul_sub_right_distrib (a b c : α) : (a - b) * c = a * c - b * c := by
  simpa only [sub_eq_add_neg, neg_mul_eq_neg_mul] using add_mul a (-b) c

alias sub_mul := mul_sub_right_distrib

end NonUnitalNonAssocRing

section NonAssocRing

variable [NonAssocRing α]

/-
**sub_one_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sub_one_mul (a b : α) : (a - 1) * b = a * b - b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem sub_one_mul (a b : α) : (a - 1) * b = a * b - b := by rw [sub_mul, one_mul]
/-
**mul_sub_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_sub_one (a b : α) : a * (b - 1) = a * b - a
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem mul_sub_one (a b : α) : a * (b - 1) = a * b - a := by rw [mul_sub, mul_one]
/-
**one_sub_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_sub_mul (a b : α) : (1 - a) * b = b - a * b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem one_sub_mul (a b : α) : (1 - a) * b = b - a * b := by rw [sub_mul, one_mul]
/-
**mul_one_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_one_sub (a b : α) : a * (1 - b) = a - a * b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem mul_one_sub (a b : α) : a * (1 - b) = a - a * b := by rw [mul_sub, mul_one]
/-
**mul_one_sub_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_one_sub_mul (a b c : α) : a * (1 - b) * c = a * c - a * b * c
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one_sub`：mul_one_sub (a b : α) : a * (1 - b) = a - a * b
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
-/
lemma mul_one_sub_mul (a b c : α) : a * (1 - b) * c = a * c - a * b * c := by
  rw [mul_one_sub, sub_mul]

end NonAssocRing

section Ring

variable [Ring α]

-- A (unital, associative) ring is a not-necessarily-unital ring
-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) Ring.toNonUnitalRing : NonUnitalRing α :=
  { ‹Ring α› with }

-- A (unital, associative) ring is a not-necessarily-associative ring
-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) Ring.toNonAssocRing : NonAssocRing α :=
  { ‹Ring α› with }

end Ring

/-- A non-unital non-associative commutative ring is a `NonUnitalNonAssocRing` with commutative
multiplication. -/
/-
**NonUnitalNonAssocCommRing** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-unital non-associative commutative ring is a `NonUnitalNonAssocRing` with 
commutative
multiplication.
-/
class NonUnitalNonAssocCommRing (α : Type u)
  extends NonUnitalNonAssocRing α, NonUnitalNonAssocCommSemiring α

/-- A non-unital commutative ring is a `NonUnitalRing` with commutative multiplication. -/
/-
**NonUnitalCommRing** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-unital commutative ring is a `NonUnitalRing` with commutative multiplicati
on.
-/
class NonUnitalCommRing (α : Type u) extends NonUnitalRing α, NonUnitalNonAssocCommRing α

/-- A non-associative commutative ring is a `NonAssocRing` with commutative multiplication. -/
/-
**NonAssocCommRing** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-associative commutative ring is a `NonAssocRing` with commutative multipli
cation.
-/
class NonAssocCommRing (α : Type u)
  extends NonAssocRing α, NonUnitalNonAssocCommRing α, NonAssocCommSemiring α

attribute [instance 100] NonAssocCommRing.toNonAssocRing
attribute [instance 100] NonAssocCommRing.toNonUnitalNonAssocCommRing
attribute [instance 100] NonAssocCommRing.toNonAssocCommSemiring

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) NonUnitalCommRing.toNonUnitalCommSemiring [s : NonUnitalCommRing α] :
    NonUnitalCommSemiring α :=
  { s with }

/-- A commutative ring is a ring with commutative multiplication. -/
@[wikidata Q858656]
/-
**CommRing** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A commutative ring is a ring with commutative multiplication.
-/
class CommRing (α : Type u) extends Ring α, CommMonoid α
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) CommRing.toNonAssocCommRing [CommRing α] : NonAssocCommRing α where
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) CommRing.toCommSemiring [s : CommRing α] : CommSemiring α :=
  { s with }

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) CommRing.toNonUnitalCommRing [s : CommRing α] : NonUnitalCommRing α :=
  { s with }

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
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
/-
**IsDomain** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u) → [Semiring α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A domain is a nontrivial semiring such that multiplication by a nonzero element
is cancellative on both sides. In other words, a nontrivial semiring `R` satisfy
ing
`∀ {a b c : R}, a ≠ 0 → a * b = a * c → b = c` and
`∀ {a b c : R}, b ≠ 0 → a * b = c * b → a = c`.

This is implemented as a mixin for `Semiring α`.
To obtain an integral domain use `[CommRing α] [IsDomain α]`.
-/
class IsDomain (α : Type u) [Semiring α] : Prop extends IsCancelMulZero α, Nontrivial α

namespace IsMulCommutative

/-- A `NonUnitalNonAssocSemiring` which `IsMulCommutative` is a `NonUnitalNonAssocCommSemiring`.

This is primarily used to deduce the bundled version from the unbundled one for commutative
subobjects in a noncommutative ambient type. As such this is only available inside the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthesis for bundled
commutativity.

See note [commutative subobjects]. -/
/-
**IsMulCommutative.** 是 Mathlib 中的一个实例，位于命名空间 `IsMulCommutative`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `NonUnitalNonAssocSemiring` which `IsMulCommutative` is a `NonUnitalNonAssocCo
mmSemiring`.

This is primarily used to deduce the bundled version from the unbundled one for 
commutative
subobjects in a noncommutative ambient type. As such this is only available insi
de the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthe
sis for bundled
commutativity.

See note [commutative subobjects].
-/
scoped instance (priority := 50) [NonUnitalNonAssocSemiring R] [IsMulCommutative R] :
    NonUnitalNonAssocCommSemiring R where

/-- A `NonUnitalSemiring` which `IsMulCommutative` is a `NonUnitalCommSemiring`.

This is primarily used to deduce the bundled version from the unbundled one for commutative
subobjects in a noncommutative ambient type. As such this is only available inside the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthesis for bundled
commutativity.

See note [commutative subobjects]. -/
/-
**IsMulCommutative.** 是 Mathlib 中的一个实例，位于命名空间 `IsMulCommutative`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `NonUnitalSemiring` which `IsMulCommutative` is a `NonUnitalCommSemiring`.

This is primarily used to deduce the bundled version from the unbundled one for 
commutative
subobjects in a noncommutative ambient type. As such this is only available insi
de the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthe
sis for bundled
commutativity.

See note [commutative subobjects].
-/
scoped instance (priority := 50) [NonUnitalSemiring R] [IsMulCommutative R] :
    NonUnitalCommSemiring R where

/-- A `NonUnitalNonAssocRing` which `IsMulCommutative` is a `NonUnitalNonAssocCommRing`.

This is primarily used to deduce the bundled version from the unbundled one for commutative
subobjects in a noncommutative ambient type. As such this is only available inside the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthesis for bundled
commutativity.

See note [commutative subobjects]. -/
/-
**IsMulCommutative.** 是 Mathlib 中的一个实例，位于命名空间 `IsMulCommutative`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `NonUnitalNonAssocRing` which `IsMulCommutative` is a `NonUnitalNonAssocCommRi
ng`.

This is primarily used to deduce the bundled version from the unbundled one for 
commutative
subobjects in a noncommutative ambient type. As such this is only available insi
de the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthe
sis for bundled
commutativity.

See note [commutative subobjects].
-/
scoped instance (priority := 50) [NonUnitalNonAssocRing R] [IsMulCommutative R] :
    NonUnitalNonAssocCommRing R where

/-- A `NonUnitalRing` which `IsMulCommutative` is a `NonUnitalCommRing`.

This is primarily used to deduce the bundled version from the unbundled one for commutative
subobjects in a noncommutative ambient type. As such this is only available inside the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthesis for bundled
commutativity.

See note [commutative subobjects]. -/
/-
**IsMulCommutative.** 是 Mathlib 中的一个实例，位于命名空间 `IsMulCommutative`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `NonUnitalRing` which `IsMulCommutative` is a `NonUnitalCommRing`.

This is primarily used to deduce the bundled version from the unbundled one for 
commutative
subobjects in a noncommutative ambient type. As such this is only available insi
de the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthe
sis for bundled
commutativity.

See note [commutative subobjects].
-/
scoped instance (priority := 50) [NonUnitalRing R] [IsMulCommutative R] :
    NonUnitalCommRing R where

/-- A `NonAssocSemiring` which `IsMulCommutative` is a `NonAssocCommSemiring`.

This is primarily used to deduce the bundled version from the unbundled one for commutative
subobjects in a noncommutative ambient type. As such this is only available inside the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthesis for bundled
commutativity.

See note [commutative subobjects]. -/
/-
**IsMulCommutative.** 是 Mathlib 中的一个实例，位于命名空间 `IsMulCommutative`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `NonAssocSemiring` which `IsMulCommutative` is a `NonAssocCommSemiring`.

This is primarily used to deduce the bundled version from the unbundled one for 
commutative
subobjects in a noncommutative ambient type. As such this is only available insi
de the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthe
sis for bundled
commutativity.

See note [commutative subobjects].
-/
scoped instance (priority := 50) [NonAssocSemiring R] [IsMulCommutative R] :
    NonAssocCommSemiring R where

/-- A `Semiring` which `IsMulCommutative` is a `CommSemiring`.

This is primarily used to deduce the bundled version from the unbundled one for commutative
subobjects in a noncommutative ambient type. As such this is only available inside the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthesis for bundled
commutativity.

See note [commutative subobjects]. -/
/-
**IsMulCommutative.** 是 Mathlib 中的一个实例，位于命名空间 `IsMulCommutative`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Semiring` which `IsMulCommutative` is a `CommSemiring`.

This is primarily used to deduce the bundled version from the unbundled one for 
commutative
subobjects in a noncommutative ambient type. As such this is only available insi
de the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthe
sis for bundled
commutativity.

See note [commutative subobjects].
-/
scoped instance (priority := 50) [Semiring R] [IsMulCommutative R] :
    CommSemiring R where

/-- A `NonAssocRing` which `IsMulCommutative` is a `NonAssocCommRing`.

This is primarily used to deduce the bundled version from the unbundled one for commutative
subobjects in a noncommutative ambient type. As such this is only available inside the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthesis for bundled
commutativity.

See note [commutative subobjects]. -/
/-
**IsMulCommutative.** 是 Mathlib 中的一个实例，位于命名空间 `IsMulCommutative`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `NonAssocRing` which `IsMulCommutative` is a `NonAssocCommRing`.

This is primarily used to deduce the bundled version from the unbundled one for 
commutative
subobjects in a noncommutative ambient type. As such this is only available insi
de the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthe
sis for bundled
commutativity.

See note [commutative subobjects].
-/
scoped instance (priority := 50) [NonAssocRing R] [IsMulCommutative R] :
    NonAssocCommRing R where

/-- A `Ring` which `IsMulCommutative` is a `CommRing`.

This is primarily used to deduce the bundled version from the unbundled one for commutative
subobjects in a noncommutative ambient type. As such this is only available inside the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthesis for bundled
commutativity.

See note [commutative subobjects]. -/
/-
**IsMulCommutative.** 是 Mathlib 中的一个实例，位于命名空间 `IsMulCommutative`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Ring` which `IsMulCommutative` is a `CommRing`.

This is primarily used to deduce the bundled version from the unbundled one for 
commutative
subobjects in a noncommutative ambient type. As such this is only available insi
de the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthe
sis for bundled
commutativity.

See note [commutative subobjects].
-/
scoped instance (priority := 50) [Ring R] [IsMulCommutative R] :
    CommRing R where

end IsMulCommutative

