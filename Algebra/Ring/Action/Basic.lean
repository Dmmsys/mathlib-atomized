/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.GroupWithZero.Action.End
public import Mathlib.Algebra.Ring.Hom.Defs

/-!
# Group action on rings

This file defines the typeclass of monoid acting on semirings `MulSemiringAction M R`.

An example of a `MulSemiringAction` is the action of the Galois group `Gal(L/K)` on
the big field `L`. Note that `Algebra` does not in general satisfy the axioms
of `MulSemiringAction`.

## Implementation notes

There is no separate typeclass for group acting on rings, group acting on fields, etc.
They are all grouped under `MulSemiringAction`.

## Note

The corresponding typeclass of subrings invariant under such an action, `IsInvariantSubring`, is
defined in `Mathlib/Algebra/Ring/Action/Invariant.lean`.

## Tags

group action

-/

@[expose] public section

assert_not_exists Equiv.Perm.equivUnitsEnd Prod.fst_mul

universe u v

/-- Typeclass for multiplicative actions by monoids on semirings.

This combines `DistribMulAction` with `MulDistribMulAction`: it expresses
the interplay between the action and both addition and multiplication on the target.
Two key axioms are `g • (x + y) = (g • x) + (g • y)` and `g • (x * y) = (g • x) * (g • y)`.

A typical use case is the action of a Galois group $Gal(L/K)$ on the field `L`.
-/
/-
**MulSemiringAction** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type u) → (R : Type v) → [Monoid M] → [Semiring R] → Type (max u v)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for multiplicative actions by monoids on semirings.

This combines `DistribMulAction` with `MulDistribMulAction`: it expresses
the interplay between the action and both addition and multiplication on the tar
get.
Two key axioms are `g • (x + y) = (g • x) + (g • y)` and `g • (x * y) = (g • x) 
* (g • y)`.

A typical use case is the action of a Galois group $Gal(L/K)$ on the field `L`.
-/
class MulSemiringAction (M : Type u) (R : Type v) [Monoid M] [Semiring R] extends
  DistribMulAction M R where
  /-- Multiplying `1` by a scalar gives `1` -/
  smul_one : ∀ g : M, (g • (1 : R) : R) = 1
  /-- Scalar multiplication distributes across multiplication -/
  smul_mul : ∀ (g : M) (x y : R), g • (x * y) = g • x * g • y

section Semiring

variable (M N : Type*) [Monoid M] [Monoid N]
variable (R : Type v) [Semiring R]

-- note we could not use `extends` since these typeclasses are made with `old_structure_cmd`
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) MulSemiringAction.toMulDistribMulAction
    (M R) {_ : Monoid M} {_ : Semiring R} [h : MulSemiringAction M R] :
    MulDistribMulAction M R :=
  { h with }

/-- Each element of the monoid defines a semiring homomorphism. -/
@[simps!]
/-
**MulSemiringAction.toRingHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MulSemiringAction.toRingHom [MulSemiringAction M R] (x : M) : R ->+* R
参数：x : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Each element of the monoid defines a semiring homomorphism.
-/
def MulSemiringAction.toRingHom [MulSemiringAction M R] (x : M) : R →+* R :=
  { MulDistribMulAction.toMonoidHom R x, DistribSMul.toAddMonoidHom R x with }
/-
**toRingHom_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toRingHom_injective [MulSemiringAction M R] [FaithfulSMul M R] : Function.
Injective (MulSemiringAction.toRingHom M R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FaithfulSMul.eq_of_smul_eq_smul`：∀ {M : Type u_4} {α : Type u_5} {inst :
 SMul M α} [self : FaithfulSMul M α] {m₁ m₂ : M},   (∀ (a : α), m₁ • a = m₂ • a)
 → m₁ = m₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `RingHom.ext_iff`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} {f g : α →+* β},   f = g ↔ ∀ (x_2 : α), f x_2 = g x
_2
-/
theorem toRingHom_injective [MulSemiringAction M R] [FaithfulSMul M R] :
    Function.Injective (MulSemiringAction.toRingHom M R) := fun _ _ h =>
  eq_of_smul_eq_smul fun r => RingHom.ext_iff.1 h r

/-- The tautological action by `R →+* R` on `R`.

This generalizes `Function.End.applyMulAction`. -/
/-
**RingHom.applyMulSemiringAction** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：RingHom.applyMulSemiringAction : MulSemiringAction (R ->+* R) R where smul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tautological action by `R →+* R` on `R`.

This generalizes `Function.End.applyMulAction`.
-/
instance RingHom.applyMulSemiringAction : MulSemiringAction (R →+* R) R where
  smul := (· <| ·)
  smul_one := map_one
  smul_mul := map_mul
  smul_zero := map_zero
  smul_add := map_add
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp]
/-
**RingHom.smul_def** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：∀ (R : Type v) [inst : Semiring R] (f : R →+* R) (a : R), f • a = f a
参数：R : Type v；f : R →+* R；a : R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem RingHom.smul_def (f : R →+* R) (a : R) : f • a = f a :=
  rfl

/-- `RingHom.applyMulSemiringAction` is faithful. -/
/-
**RingHom.applyFaithfulSMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：RingHom.applyFaithfulSMul : FaithfulSMul (R ->+* R) R
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g

--- 原说明 ---
`RingHom.applyMulSemiringAction` is faithful.
-/
instance RingHom.applyFaithfulSMul : FaithfulSMul (R →+* R) R :=
  ⟨fun {_ _} h => RingHom.ext h⟩

section

variable {M N}

/-- Compose a `MulSemiringAction` with a `MonoidHom`, with action `f r' • m`.
See note [reducible non-instances]. -/
/-
**MulSemiringAction.compHom** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：MulSemiringAction.compHom (f : N ->* M) [MulSemiringAction M R] : MulSemir
ingAction N R
参数：f : N ->* M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Compose a `MulSemiringAction` with a `MonoidHom`, with action `f r' • m`.
See note [reducible non-instances].
-/
abbrev MulSemiringAction.compHom (f : N →* M) [MulSemiringAction M R] : MulSemiringAction N R :=
  { DistribMulAction.compHom R f, MulDistribMulAction.compHom R f with }

end

section SimpLemmas

attribute [simp] smul_one smul_mul' smul_zero smul_add

end SimpLemmas

end Semiring

