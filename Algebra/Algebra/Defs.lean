/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs

/-!
# Algebras over commutative semirings

In this file we define associative unital `Algebra`s over commutative (semi)rings.

* algebra homomorphisms `AlgHom` are defined in `Mathlib/Algebra/Algebra/Hom.lean`;

* algebra equivalences `AlgEquiv` are defined in `Mathlib/Algebra/Algebra/Equiv.lean`;

* `Subalgebra`s are defined in `Mathlib/Algebra/Algebra/Subalgebra/Basic.lean`;

* The category `AlgCat R` of `R`-algebras is defined in the file
  `Mathlib/Algebra/Category/AlgCat/Basic.lean`.

See the implementation notes for remarks about non-associative and non-unital algebras.

## Main definitions:

* `Algebra R A`: the algebra typeclass.
* `algebraMap R A : R →+* A`: the canonical map from `R` to `A`, as a `RingHom`. This is the
  preferred spelling of this map, it is also available as:
  * `Algebra.linearMap R A : R →ₗ[R] A`, a `LinearMap`.
  * `Algebra.ofId R A : R →ₐ[R] A`, an `AlgHom` (defined in a later file).

## Implementation notes

Given a commutative (semi)ring `R`, there are two ways to define an `R`-algebra structure on a
(possibly noncommutative) (semi)ring `A`:
* By endowing `A` with a morphism of rings `R →+* A` denoted `algebraMap R A` which lands in the
  center of `A`.
* By requiring `A` be an `R`-module such that the action associates and commutes with multiplication
  as `r • (a₁ * a₂) = (r • a₁) * a₂ = a₁ * (r • a₂)`.

We define `Algebra R A` in a way that subsumes both definitions, by extending `SMul R A` and
requiring that this scalar action `r • x` must agree with left multiplication by the image of the
structure morphism `algebraMap R A r * x`.

As a result, there are two ways to talk about an `R`-algebra `A` when `A` is a semiring:
1. ```lean
   variable [CommSemiring R] [Semiring A]
   variable [Algebra R A]
   ```
2. ```lean
   variable [CommSemiring R] [Semiring A]
   variable [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
   ```

The first approach implies the second via typeclass search; so any lemma stated with the second set
of arguments will automatically apply to the first set. Typeclass search does not know that the
second approach implies the first, but this can be shown with:
```lean
example {R A : Type*} [CommSemiring R] [Semiring A]
  [Module R A] [SMulCommClass R A A] [IsScalarTower R A A] : Algebra R A :=
Algebra.ofModule smul_mul_assoc mul_smul_comm
```

The advantage of the first approach is that `algebraMap R A` is available, and `AlgHom R A B` and
`Subalgebra R A` can be used. For concrete `R` and `A`, `algebraMap R A` is often definitionally
convenient.

The advantage of the second approach is that `CommSemiring R`, `Semiring A`, and `Module R A` can
all be relaxed independently; for instance, this allows us to:
* Replace `Semiring A` with `NonUnitalNonAssocSemiring A` in order to describe non-unital and/or
  non-associative algebras.
* Replace `CommSemiring R` and `Module R A` with `CommGroup R'` and `DistribMulAction R' A`,
  which when `R' = Rˣ` lets us talk about the "algebra-like" action of `Rˣ` on an
  `R`-algebra `A`.

While `AlgHom R A B` cannot be used in the second approach, `NonUnitalAlgHom R A B` still can.

You should always use the first approach when working with associative unital algebras, and mimic
the second approach only when you need to weaken a condition on either `R` or `A`.

-/

@[expose] public section

assert_not_exists Field Finset Module.End

universe u v w u₁ v₁

/-- An associative unital `R`-algebra is a semiring `A` equipped with a map into its center `R → A`.

See the implementation notes in this file for discussion of the details of this definition.
-/
/-
**Algebra** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) → (A : Type v) → [CommSemiring R] → [Semiring A] → Type (max 
u v)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An associative unital `R`-algebra is a semiring `A` equipped with a map into its
 center `R → A`.

See the implementation notes in this file for discussion of the details of this 
definition.
-/
class Algebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] extends SMul R A where
  /-- Embedding `R →+* A` given by `Algebra` structure. -/
  algebraMap (R) (A) : R →+* A
  commutes' : ∀ r x, algebraMap r * x = x * algebraMap r
  smul_def' : ∀ r x, r • x = algebraMap r * x

export Algebra (algebraMap)
/-
**Algebra.subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.subsingleton (R : Type u) (A : Type v) [CommSemiring R] [Semiring 
A] [Algebra R A] [Subsingleton R] : Subsingleton A
参数：R : Type u；A : Type v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.codomain_trivial`：codomain_trivial (f : α ->+* β) [h : Subsingle
ton α] : Subsingleton β
-/
theorem Algebra.subsingleton (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] [Algebra R A]
    [Subsingleton R] : Subsingleton A :=
  (algebraMap R A).codomain_trivial

/-- Coercion from a commutative semiring to an algebra over this semiring. -/
@[coe, reducible]
/-
**Algebra.cast** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Algebra.cast {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] : R
 -> A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion from a commutative semiring to an algebra over this semiring.
-/
def Algebra.cast {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] : R → A :=
  algebraMap R A

namespace algebraMap

/-
**algebraMap.coeHTCT** 是 Mathlib 中的一个定义，位于命名空间 `algebraMap`。
形式化陈述：(R : Type u_1) → (A : Type u_2) → [inst : CommSemiring R] → [inst_1 : Semi
ring A] → [Algebra R A] → CoeHTCT R A
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
scoped instance coeHTCT (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A] :
    CoeHTCT R A :=
  ⟨Algebra.cast⟩

section CommSemiringSemiring

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

@[norm_cast]
/-
**algebraMap.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `algebraMap`。
形式化陈述：coe_zero : (↑(0 : R) : A) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem coe_zero : (↑(0 : R) : A) = 0 :=
  map_zero (algebraMap R A)

@[norm_cast]
/-
**algebraMap.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `algebraMap`。
形式化陈述：coe_one : (↑(1 : R) : A) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem coe_one : (↑(1 : R) : A) = 1 :=
  map_one (algebraMap R A)

@[norm_cast]
/-
**algebraMap.coe_natCast** 是 Mathlib 中的一个定理，位于命名空间 `algebraMap`。
形式化陈述：coe_natCast (a : Nat) : (↑(a : R) : A) = a
参数：a : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
-/
theorem coe_natCast (a : ℕ) : (↑(a : R) : A) = a :=
  map_natCast (algebraMap R A) a

@[norm_cast]
/-
**algebraMap.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `algebraMap`。
形式化陈述：coe_add (a b : R) : (↑(a + b : R) : A) = ↑a + ↑b
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
-/
theorem coe_add (a b : R) : (↑(a + b : R) : A) = ↑a + ↑b :=
  map_add (algebraMap R A) a b

@[norm_cast]
/-
**algebraMap.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `algebraMap`。
形式化陈述：coe_mul (a b : R) : (↑(a * b : R) : A) = ↑a * ↑b
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
-/
theorem coe_mul (a b : R) : (↑(a * b : R) : A) = ↑a * ↑b :=
  map_mul (algebraMap R A) a b

@[norm_cast]
/-
**algebraMap.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `algebraMap`。
形式化陈述：coe_pow (a : R) (n : Nat) : (↑(a ^ n : R) : A) = (a : A) ^ n
参数：a : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem coe_pow (a : R) (n : ℕ) : (↑(a ^ n : R) : A) = (a : A) ^ n :=
  map_pow (algebraMap R A) _ _

end CommSemiringSemiring

section CommRingRing

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

@[norm_cast]
/-
**algebraMap.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `algebraMap`。
形式化陈述：coe_neg (x : R) : (↑(-x : R) : A) = -↑x
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
-/
theorem coe_neg (x : R) : (↑(-x : R) : A) = -↑x :=
  map_neg (algebraMap R A) x

@[norm_cast]
/-
**algebraMap.coe_sub** 是 Mathlib 中的一个定理，位于命名空间 `algebraMap`。
形式化陈述：coe_sub (a b : R) : (↑(a - b : R) : A) = ↑a - ↑b
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
-/
theorem coe_sub (a b : R) :
    (↑(a - b : R) : A) = ↑a - ↑b :=
  map_sub (algebraMap R A) a b

end CommRingRing

end algebraMap

/-- Creating an algebra from a morphism to the center of a semiring.
See note [reducible non-instances].

*Warning:* In general this should not be used if `S` already has a `SMul R S`
instance, since this creates another `SMul R S` instance from the supplied `RingHom` and
this will likely create a diamond. -/
/-
**RingHom.toAlgebra'** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：RingHom.toAlgebra' {R S} [CommSemiring R] [Semiring S] (i : R ->+* S) (h :
 forall c x, i c * x = x * i c) : Algebra R S where smul c x
参数：i : R ->+* S；h : forall c x, i c * x = x * i c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Creating an algebra from a morphism to the center of a semiring.
See note [reducible non-instances].

*Warning:* In general this should not be used if `S` already has a `SMul R S`
instance, since this creates another `SMul R S` instance from the supplied `Ring
Hom` and
this will likely create a diamond.
-/
abbrev RingHom.toAlgebra' {R S} [CommSemiring R] [Semiring S] (i : R →+* S)
    (h : ∀ c x, i c * x = x * i c) : Algebra R S where
  smul c x := i c * x
  commutes' := h
  smul_def' _ _ := rfl
  algebraMap := i

-- just simple lemmas for a declaration that is itself primed, no need for docstrings
set_option linter.docPrime false in
/-
**RingHom.smul_toAlgebra'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingHom.smul_toAlgebra' {R S} [CommSemiring R] [Semiring S] (i : R ->+* S)
 (h : forall c x, i c * x = x * i c) (r : R) (s : S) : let _
参数：i : R ->+* S；h : forall c x, i c * x = x * i c；r : R；s : S。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem RingHom.smul_toAlgebra' {R S} [CommSemiring R] [Semiring S] (i : R →+* S)
    (h : ∀ c x, i c * x = x * i c) (r : R) (s : S) :
    let _ := RingHom.toAlgebra' i h
    r • s = i r * s := rfl

set_option linter.docPrime false in
/-
**RingHom.algebraMap_toAlgebra'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingHom.algebraMap_toAlgebra' {R S} [CommSemiring R] [Semiring S] (i : R -
>+* S) (h : forall c x, i c * x = x * i c) : @algebraMap R S _ _ (i.toAlgebra' h
) = i
参数：i : R ->+* S；h : forall c x, i c * x = x * i c。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem RingHom.algebraMap_toAlgebra' {R S} [CommSemiring R] [Semiring S] (i : R →+* S)
    (h : ∀ c x, i c * x = x * i c) :
    @algebraMap R S _ _ (i.toAlgebra' h) = i :=
  rfl

/-- Creating an algebra from a morphism to a commutative semiring.
See note [reducible non-instances].

*Warning:* In general this should not be used if `S` already has a `SMul R S`
instance, since this creates another `SMul R S` instance from the supplied `RingHom` and
this will likely create a diamond. -/
/-
**RingHom.toAlgebra** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：RingHom.toAlgebra {R S} [CommSemiring R] [CommSemiring S] (i : R ->+* S) :
 Algebra R S
参数：i : R ->+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Creating an algebra from a morphism to a commutative semiring.
See note [reducible non-instances].

*Warning:* In general this should not be used if `S` already has a `SMul R S`
instance, since this creates another `SMul R S` instance from the supplied `Ring
Hom` and
this will likely create a diamond.
-/
abbrev RingHom.toAlgebra {R S} [CommSemiring R] [CommSemiring S] (i : R →+* S) : Algebra R S :=
  i.toAlgebra' fun _ => mul_comm _
/-
**RingHom.smul_toAlgebra** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingHom.smul_toAlgebra {R S} [CommSemiring R] [CommSemiring S] (i : R ->+*
 S) (r : R) (s : S) : let _
参数：i : R ->+* S；r : R；s : S。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem RingHom.smul_toAlgebra {R S} [CommSemiring R] [CommSemiring S] (i : R →+* S)
    (r : R) (s : S) :
    let _ := RingHom.toAlgebra i
    r • s = i r * s := rfl
/-
**RingHom.algebraMap_toAlgebra** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingHom.algebraMap_toAlgebra {R S} [CommSemiring R] [CommSemiring S] (i : 
R ->+* S) : @algebraMap R S _ _ i.toAlgebra = i
参数：i : R ->+* S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem RingHom.algebraMap_toAlgebra {R S} [CommSemiring R] [CommSemiring S] (i : R →+* S) :
    @algebraMap R S _ _ i.toAlgebra = i :=
  rfl

namespace Algebra

variable {R : Type u} {S : Type v} {A : Type w} {B : Type*}

/-- Let `R` be a commutative semiring, let `A` be a semiring with a `Module R` structure.
If `(r • 1) * x = x * (r • 1) = r • x` for all `r : R` and `x : A`, then `A` is an `Algebra`
over `R`.

See note [reducible non-instances]. -/
/-
**Algebra.ofModule'** 是 Mathlib 中的一个缩写定义，位于命名空间 `Algebra`。
形式化陈述：ofModule' [CommSemiring R] [Semiring A] [Module R A] (h₁ : forall (r : R) 
(x : A), r • (1 : A) * x = r • x) (h₂ : forall (r : R) (x : A), x * r • (1 : A) 
= r • x) : Algebra R A where algebraMap
参数：h₁ : forall (r : R) (x : A), r • (1 : A) * x = r • x；h₂ : forall (r : R) (x :
 A), x * r • (1 : A) = r • x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `R` be a commutative semiring, let `A` be a semiring with a `Module R` struc
ture.
If `(r • 1) * x = x * (r • 1) = r • x` for all `r : R` and `x : A`, then `A` is 
an `Algebra`
over `R`.

See note [reducible non-instances].
-/
abbrev ofModule' [CommSemiring R] [Semiring A] [Module R A]
    (h₁ : ∀ (r : R) (x : A), r • (1 : A) * x = r • x)
    (h₂ : ∀ (r : R) (x : A), x * r • (1 : A) = r • x) : Algebra R A where
  algebraMap :=
  { toFun r := r • (1 : A)
    map_one' := one_smul _ _
    map_mul' r₁ r₂ := by simp only [h₁, mul_smul]
    map_zero' := zero_smul _ _
    map_add' r₁ r₂ := add_smul r₁ r₂ 1 }
  commutes' r x := by simp [h₁, h₂]
  smul_def' r x := by simp [h₁]

/-- Let `R` be a commutative semiring, let `A` be a semiring with a `Module R` structure.
If `(r • x) * y = x * (r • y) = r • (x * y)` for all `r : R` and `x y : A`, then `A`
is an `Algebra` over `R`.

See note [reducible non-instances]. -/
/-
**Algebra.ofModule** 是 Mathlib 中的一个缩写定义，位于命名空间 `Algebra`。
形式化陈述：ofModule [CommSemiring R] [Semiring A] [Module R A] (h₁ : forall (r : R) (
x y : A), r • x * y = r • (x * y)) (h₂ : forall (r : R) (x y : A), x * r • y = r
 • (x * y)) : Algebra R A
参数：h₁ : forall (r : R) (x y : A), r • x * y = r • (x * y)；h₂ : forall (r : R) (x
 y : A), x * r • y = r • (x * y)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `R` be a commutative semiring, let `A` be a semiring with a `Module R` struc
ture.
If `(r • x) * y = x * (r • y) = r • (x * y)` for all `r : R` and `x y : A`, then
 `A`
is an `Algebra` over `R`.

See note [reducible non-instances].
-/
abbrev ofModule [CommSemiring R] [Semiring A] [Module R A]
    (h₁ : ∀ (r : R) (x y : A), r • x * y = r • (x * y))
    (h₂ : ∀ (r : R) (x y : A), x * r • y = r • (x * y)) : Algebra R A :=
  ofModule' (fun r x => by rw [h₁, one_mul]) fun r x => by rw [h₂, mul_one]

section Semiring

variable [CommSemiring R] [CommSemiring S]
variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

-- We'll later use this to show `Algebra ℤ M` is a subsingleton.
/-- To prove two algebra structures on a fixed `[CommSemiring R] [Semiring A]` agree,
it suffices to check the `algebraMap`s agree.
-/
@[ext]
/-
**Algebra.algebra_ext** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：algebra_ext {R : Type*} [CommSemiring R] {A : Type*} [Semiring A] (P Q : A
lgebra R A) (h : forall r : R, (haveI
参数：P Q : Algebra R A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.smul_def'`：∀ {R : Type u} {A : Type v} {inst : CommSemiring R} {
inst_1 : Semiring A} [self : Algebra R A] (r : R) (x : A),   r • x = (algebraMap
 R A) r…

--- 原说明 ---
To prove two algebra structures on a fixed `[CommSemiring R] [Semiring A]` agree
,
it suffices to check the `algebraMap`s agree.
-/
theorem algebra_ext {R : Type*} [CommSemiring R] {A : Type*} [Semiring A] (P Q : Algebra R A)
    (h : ∀ r : R, (haveI := P; algebraMap R A r) = haveI := Q; algebraMap R A r) :
    P = Q := by
  replace h : P.algebraMap = Q.algebraMap := DFunLike.ext _ _ h
  have h' : (haveI := P; (· • ·) : R → A → A) = (haveI := Q; (· • ·) : R → A → A) := by
    funext r a
    rw [P.smul_def', Q.smul_def', h]
  rcases P with @⟨⟨P⟩⟩
  congr

/-- An auxiliary lemma used to prove theorems of the form
`RingHom.X (algebraMap R S) ↔ Algebra.X R S`. -/
/-
**Algebra._root_.toAlgebra_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary lemma used to prove theorems of the form
`RingHom.X (algebraMap R S) ↔ Algebra.X R S`.
-/
lemma _root_.toAlgebra_algebraMap [Algebra R S] :
    (algebraMap R S).toAlgebra = ‹_› :=
  algebra_ext _ _ fun _ ↦ rfl

-- see Note [lower instance priority]
/-
**Algebra.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 200) toModule {R A} {_ : CommSemiring R} {_ : Semiring A} [Algebra R A] :
    Module R A where
  one_smul _ := by simp [smul_def']
  mul_smul := by simp [smul_def', mul_assoc]
  smul_add := by simp [smul_def', mul_add]
  smul_zero := by simp [smul_def']
  add_smul := by simp [smul_def', add_mul]
  zero_smul := by simp [smul_def']
/-
**Algebra.smul_def** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：smul_def (r : R) (x : A) : r • x = algebraMap R A r * x
参数：r : R；x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.smul_def'`：∀ {R : Type u} {A : Type v} {inst : CommSemiring R} {
inst_1 : Semiring A} [self : Algebra R A] (r : R) (x : A),   r • x = (algebraMap
 R A) r…
-/
theorem smul_def (r : R) (x : A) : r • x = algebraMap R A r * x :=
  Algebra.smul_def' r x
/-
**Algebra.algebraMap_eq_smul_one** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：algebraMap_eq_smul_one (r : R) : algebraMap R A r = r • (1 : A)
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
-/
theorem algebraMap_eq_smul_one (r : R) : algebraMap R A r = r • (1 : A) :=
  calc
    algebraMap R A r = algebraMap R A r * 1 := (mul_one _).symm
    _ = r • (1 : A) := (Algebra.smul_def r 1).symm
/-
**Algebra.algebraMap_eq_smul_one'** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：algebraMap_eq_smul_one' : ⇑(algebraMap R A) = fun r => r • (1 : A)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
-/
theorem algebraMap_eq_smul_one' : ⇑(algebraMap R A) = fun r => r • (1 : A) :=
  funext algebraMap_eq_smul_one

/-- `mul_comm` for `Algebra`s when one element is from the base ring. -/
/-
**Algebra.commutes** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：commutes (r : R) (x : A) : algebraMap R A r * x = x * algebraMap R A r
参数：r : R；x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.commutes'`：∀ {R : Type u} {A : Type v} {inst : CommSemiring R} {
inst_1 : Semiring A} [self : Algebra R A] (r : R) (x : A),   (algebraMap R A) r 
* x = x…

--- 原说明 ---
`mul_comm` for `Algebra`s when one element is from the base ring.
-/
theorem commutes (r : R) (x : A) : algebraMap R A r * x = x * algebraMap R A r :=
  Algebra.commutes' r x
/-
**Algebra.commute_algebraMap_left** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`。
形式化陈述：commute_algebraMap_left (r : R) (x : A) : Commute (algebraMap R A r) x
参数：r : R；x : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.commutes`：commutes (r : R) (x : A) : algebraMap R A r * x = x * 
algebraMap R A r
-/
lemma commute_algebraMap_left (r : R) (x : A) : Commute (algebraMap R A r) x :=
  Algebra.commutes r x
/-
**Algebra.commute_algebraMap_right** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`。
形式化陈述：commute_algebraMap_right (r : R) (x : A) : Commute x (algebraMap R A r)
参数：r : R；x : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.commutes`：commutes (r : R) (x : A) : algebraMap R A r * x = x * 
algebraMap R A r
-/
lemma commute_algebraMap_right (r : R) (x : A) : Commute x (algebraMap R A r) :=
  (Algebra.commutes r x).symm

/-- `mul_left_comm` for `Algebra`s when one element is from the base ring. -/
/-
**Algebra.left_comm** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：left_comm (x : A) (r : R) (y : A) : x * (algebraMap R A r * y) = algebraMa
p R A r * (x * y)
参数：x : A；r : R；y : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Algebra.commutes`：commutes (r : R) (x : A) : algebraMap R A r * x = x * 
algebraMap R A r

--- 原说明 ---
`mul_left_comm` for `Algebra`s when one element is from the base ring.
-/
theorem left_comm (x : A) (r : R) (y : A) :
    x * (algebraMap R A r * y) = algebraMap R A r * (x * y) := by
  rw [← mul_assoc, ← commutes, mul_assoc]

/-- `mul_right_comm` for `Algebra`s when one element is from the base ring. -/
/-
**Algebra.right_comm** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：right_comm (x : A) (r : R) (y : A) : x * algebraMap R A r * y = x * y * al
gebraMap R A r
参数：x : A；r : R；y : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Algebra.commutes`：commutes (r : R) (x : A) : algebraMap R A r * x = x * 
algebraMap R A r
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
`mul_right_comm` for `Algebra`s when one element is from the base ring.
-/
theorem right_comm (x : A) (r : R) (y : A) :
    x * algebraMap R A r * y = x * y * algebraMap R A r := by
  rw [mul_assoc, commutes, ← mul_assoc]

/-- This has high priority because it is almost always the right instance when it applies. -/
/-
**Algebra.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This has high priority because it is almost always the right instance when it ap
plies.
-/
instance (priority := high) _root_.IsScalarTower.right : IsScalarTower R A A :=
  ⟨fun x y z => by rw [smul_eq_mul, smul_eq_mul, smul_def, smul_def, mul_assoc]⟩

@[simp]
/-
**Algebra._root_.RingHom.smulOneHom_eq_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.RingHom.smulOneHom_eq_algebraMap : RingHom.smulOneHom = algebraMap R A :=
  RingHom.ext fun r => (algebraMap_eq_smul_one r).symm

-- TODO: set up `IsScalarTower.smulCommClass` earlier so that we can actually prove this using
-- `mul_smul_comm s x y`.

/-- This is just a special case of the global `mul_smul_comm` lemma that requires less typeclass
search (and was here first). -/
@[simp]
/-
**Algebra.mul_smul_comm** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：∀ {R : Type u} {A : Type w} [inst : CommSemiring R] [inst_1 : Semiring A] 
[inst_2 : Algebra R A] (s : R) (x y : A),   x * s • y = s • (x * y)
参数：s : R；x y : A；x * y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `Algebra.left_comm`：left_comm (x : A) (r : R) (y : A) : x * (algebraMap R
 A r * y) = algebraMap R A r * (x * y)

--- 原说明 ---
This is just a special case of the global `mul_smul_comm` lemma that requires le
ss typeclass
search (and was here first).
-/
protected theorem mul_smul_comm (s : R) (x y : A) : x * s • y = s • (x * y) := by
  rw [smul_def, smul_def, left_comm]

/-- This is just a special case of the global `smul_mul_assoc` lemma that requires less typeclass
search (and was here first). -/
@[simp]
/-
**Algebra.smul_mul_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：∀ {R : Type u} {A : Type w} [inst : CommSemiring R] [inst_1 : Semiring A] 
[inst_2 : Algebra R A] (r : R) (x y : A),   r • x * y = r • (x * y)
参数：r : R；x y : A；x * y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
This is just a special case of the global `smul_mul_assoc` lemma that requires l
ess typeclass
search (and was here first).
-/
protected theorem smul_mul_assoc (r : R) (x y : A) : r • x * y = r • (x * y) :=
  smul_mul_assoc r x y

@[simp]
/-
**Algebra._root_.smul_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.smul_algebraMap {α : Type*} [Monoid α] [MulDistribMulAction α A]
    [SMulCommClass α R A] (a : α) (r : R) : a • algebraMap R A r = algebraMap R A r := by
  rw [algebraMap_eq_smul_one, smul_comm a r (1 : A), smul_one]

section compHom

variable (A) (f : S →+* R)

/--
Compose an `Algebra` with a `RingHom`, with action `f s • m`.

This is the algebra version of `Module.compHom`.
-/
/-
**Algebra.compHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `Algebra`。
形式化陈述：compHom : Algebra S A where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Compose an `Algebra` with a `RingHom`, with action `f s • m`.

This is the algebra version of `Module.compHom`.
-/
abbrev compHom : Algebra S A where
  __ := Module.compHom A f
  algebraMap := (algebraMap R A).comp f
  commutes' _ _ := Algebra.commutes _ _
  smul_def' _ _ := Algebra.smul_def _ _
/-
**Algebra.compHom_smul_def** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：compHom_smul_def (s : S) (x : A) : letI
参数：s : S；x : A。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compHom_smul_def (s : S) (x : A) :
    letI := compHom A f
    s • x = f s • x := rfl
/-
**Algebra.compHom_algebraMap_eq** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：compHom_algebraMap_eq : letI
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compHom_algebraMap_eq :
    letI := compHom A f
    algebraMap S A = (algebraMap R A).comp f := rfl
/-
**Algebra.compHom_algebraMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：compHom_algebraMap_apply (s : S) : letI
参数：s : S。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compHom_algebraMap_apply (s : S) :
    letI := compHom A f
    algebraMap S A s = (algebraMap R A) (f s) := rfl

end compHom


variable (R A)

/-- The canonical ring homomorphism `algebraMap R A : R →+* A` for any `R`-algebra `A`,
packaged as an `R`-linear map.
-/
/-
**Algebra.linearMap** 是 Mathlib 中的一个定义，位于命名空间 `Algebra`。
形式化陈述：(R : Type u) → (A : Type w) → [inst : CommSemiring R] → [inst_1 : Semiring
 A] → [inst_2 : Algebra R A] → R →ₗ[R] A
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical ring homomorphism `algebraMap R A : R →+* A` for any `R`-algebra `
A`,
packaged as an `R`-linear map.
-/
protected def linearMap : R →ₗ[R] A :=
  { algebraMap R A with map_smul' := fun x y => by simp [Algebra.smul_def] }

@[inherit_doc] scoped[RingTheory.LinearMap] notation "η" => Algebra.linearMap _ _
@[inherit_doc] scoped[RingTheory.LinearMap] notation "η[" R "]" => Algebra.linearMap R _

@[simp]
/-
**Algebra.linearMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：linearMap_apply (r : R) : Algebra.linearMap R A r = algebraMap R A r
参数：r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem linearMap_apply (r : R) : Algebra.linearMap R A r = algebraMap R A r :=
  rfl
/-
**Algebra.coe_linearMap** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：coe_linearMap : ⇑(Algebra.linearMap R A) = algebraMap R A
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_linearMap : ⇑(Algebra.linearMap R A) = algebraMap R A :=
  rfl

-- see Note [higher instance priority]
/-- The identity map inducing an `Algebra` structure. -/
/-
**Algebra.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity map inducing an `Algebra` structure.
-/
instance (priority := 1100) id : Algebra R R where
  -- We override `toFun` and `toSMul` because `RingHom.id` is not reducible and cannot
  -- be made so without a significant performance hit.
  -- see library note [reducible non-instances].
  toSMul := instSMulOfMul
  __ := (RingHom.id R).toAlgebra
/-
**Algebra.linearMap_self** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：∀ (R : Type u) [inst : CommSemiring R], Algebra.linearMap R R = LinearMap.
id
参数：R : Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma linearMap_self : Algebra.linearMap R R = .id := rfl

variable {R A}
/-
**Algebra.algebraMap_self** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R], algebraMap R R = RingHom.id R
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma algebraMap_self : algebraMap R R = .id _ := rfl
/-
**Algebra.algebraMap_self_apply** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`。
形式化陈述：algebraMap_self_apply (x : R) : algebraMap R R x = x
参数：x : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma algebraMap_self_apply (x : R) : algebraMap R R x = x := rfl

end Semiring

end Algebra

section algebraMap

variable {A B : Type*} (a : A) (b : B) (C : Type*)
  [SMul A B] [CommSemiring B] [Semiring C] [Algebra B C]

@[norm_cast]
/-
**algebraMap.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：algebraMap.coe_smul [SMul A C] [IsScalarTower A B C] : (a • b : B) = a • (
b : C)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem algebraMap.coe_smul [SMul A C] [IsScalarTower A B C] : (a • b : B) = a • (b : C) := by
  simp [Algebra.algebraMap_eq_smul_one]

@[norm_cast]
/-
**algebraMap.coe_smul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：algebraMap.coe_smul' [Monoid A] [MulDistribMulAction A C] [SMulDistribClas
s A B C] : (a • b : B) = a • (b : C)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `SMulDistribClass.smul_distrib_smul`：∀ {G : Type u_9} {R : Type u_10} {S 
: Type u_11} {inst : SMul G R} {inst_1 : SMul G S} {inst_2 : SMul R S}   [self :
 SMulDistribClass G R S]…
· 使用定理 `MulDistribMulAction.smul_one`：∀ {M : Type u_9} {N : Type u_10} {inst : M
onoid M} {inst_1 : Monoid N} [self : MulDistribMulAction M N] (r : M),   r • 1 =
 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem algebraMap.coe_smul' [Monoid A] [MulDistribMulAction A C] [SMulDistribClass A B C] :
    (a • b : B) = a • (b : C) := by
  simp [Algebra.algebraMap_eq_smul_one, smul_distrib_smul]
/-
**algebraMap.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：algebraMap.smul [SMul A C] [IsScalarTower A B C] : algebraMap B C (a • b) 
= a • (algebraMap B C b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `algebraMap.coe_smul`：algebraMap.coe_smul [SMul A C] [IsScalarTower A B C
] : (a • b : B) = a • (b : C)
-/
theorem algebraMap.smul [SMul A C] [IsScalarTower A B C] :
    algebraMap B C (a • b) = a • (algebraMap B C b) := coe_smul _ _ _
/-
**algebraMap.smul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：algebraMap.smul' [Monoid A] [MulDistribMulAction A C] [SMulDistribClass A 
B C] : algebraMap B C (a • b) = a • (algebraMap B C b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `algebraMap.coe_smul'`：algebraMap.coe_smul' [Monoid A] [MulDistribMulActi
on A C] [SMulDistribClass A B C] : (a • b : B) = a • (b : C)
-/
theorem algebraMap.smul' [Monoid A] [MulDistribMulAction A C] [SMulDistribClass A B C] :
    algebraMap B C (a • b) = a • (algebraMap B C b) := coe_smul' _ _ _

end algebraMap

