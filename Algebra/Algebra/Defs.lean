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

/--
Definition of `Algebra` / `Algebra` 的定义

English:
class Algebra
  parameters: (R : Type u) (A : Type v) [CommSemiring R] [Semiring A]
  extends: SMul R A
  axioms and operations (3):
    - algebraMap((R) (A)) : R ->+* A
    - commutes' : forall r x, algebraMap r * x = x * algebraMap r
    - smul_def' : forall r x, r • x = algebraMap r * x

中文:
类 Algebra
  参数: (R : 类型u) (A : 类型v) [CommSemiring R] [Semiring A]
  继承: SMul R A
  公理与运算 (3 个):
    - algebraMap((R) (A)) : R ->+* A
    - commutes' : 对任意 r x, algebraMap r * x = x * algebraMap r
    - smul_def' : 对任意 r x, r • x = algebraMap r * x
-/
class Algebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] extends SMul R A where
  /-- Embedding `R →+* A` given by `Algebra` structure. -/
  algebraMap (R) (A) : R ->+* A
  commutes' : forall r x, algebraMap r * x = x * algebraMap r
  smul_def' : forall r x, r • x = algebraMap r * x

export Algebra (algebraMap)

/--
theorem `Algebra.subsingleton` / 定理 `Algebra.subsingleton`

English:
theorem Algebra.subsingleton
  statement: (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] [Algebra R A]
  proof: (algebraMap R A).codomain_trivial

中文:
定理 Algebra.subsingleton
  结论: (R : 类型u) (A : 类型v) [CommSemiring R] [Semiring A] [Algebra R A]
  证明: (algebraMap R A).codomain_trivial

Depends on / 依赖: algebraMap, codomain_trivial
-/
theorem Algebra.subsingleton (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] [Algebra R A]
    [Subsingleton R] : Subsingleton A :=
  (algebraMap R A).codomain_trivial

/-- Coercion from a commutative semiring to an algebra over this semiring. -/
@[coe, reducible]
/--
Definition of `Algebra.cast` / `Algebra.cast` 的定义

English:
definition Algebra.cast
  signature: {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  body: algebraMap R A

中文:
定义 Algebra.cast
  签名: {R A : 类型} [CommSemiring R] [Semiring A] [Algebra R A]
  定义体: algebraMap R A

Depends on / 依赖: algebraMap
-/
def Algebra.cast {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] : R -> A :=
  algebraMap R A

namespace algebraMap

scoped instance coeHTCT (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A] :
    CoeHTCT R A :=
  ⟨Algebra.cast⟩

section CommSemiringSemiring

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

@[norm_cast]
/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  statement: (↑(0 : R) : A) = 0
  proof: map_zero (algebraMap R A)

@[norm_cast]

中文:
定理 coe_zero
  结论: (↑(0 : R) : A) = 0
  证明: map_zero (algebraMap R A)

@[norm_cast]

Depends on / 依赖: algebraMap, map_zero
-/
theorem coe_zero : (↑(0 : R) : A) = 0 :=
  map_zero (algebraMap R A)

@[norm_cast]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: (↑(1 : R) : A) = 1
  proof: map_one (algebraMap R A)

@[norm_cast]

中文:
定理 coe_one
  结论: (↑(1 : R) : A) = 1
  证明: map_one (algebraMap R A)

@[norm_cast]

Depends on / 依赖: algebraMap, map_one
-/
theorem coe_one : (↑(1 : R) : A) = 1 :=
  map_one (algebraMap R A)

@[norm_cast]
/--
theorem `coe_natCast` / 定理 `coe_natCast`

English:
theorem coe_natCast
  given: (a : Nat)
  statement: (↑(a : R) : A) = a
  proof: map_natCast (algebraMap R A) a

@[norm_cast]

中文:
定理 coe_natCast
  条件: (a : 自然数)
  结论: (↑(a : R) : A) = a
  证明: map_natCast (algebraMap R A) a

@[norm_cast]

Depends on / 依赖: algebraMap, map_natCast
-/
theorem coe_natCast (a : Nat) : (↑(a : R) : A) = a :=
  map_natCast (algebraMap R A) a

@[norm_cast]
/--
theorem `coe_add` / 定理 `coe_add`

English:
theorem coe_add
  given: (a b : R)
  statement: (↑(a + b : R) : A) = ↑a + ↑b
  proof: map_add (algebraMap R A) a b

@[norm_cast]

中文:
定理 coe_add
  条件: (a b : R)
  结论: (↑(a + b : R) : A) = ↑a + ↑b
  证明: map_add (algebraMap R A) a b

@[norm_cast]

Depends on / 依赖: algebraMap, map_add
-/
theorem coe_add (a b : R) : (↑(a + b : R) : A) = ↑a + ↑b :=
  map_add (algebraMap R A) a b

@[norm_cast]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (a b : R)
  statement: (↑(a * b : R) : A) = ↑a * ↑b
  proof: map_mul (algebraMap R A) a b

@[norm_cast]

中文:
定理 coe_mul
  条件: (a b : R)
  结论: (↑(a * b : R) : A) = ↑a * ↑b
  证明: map_mul (algebraMap R A) a b

@[norm_cast]

Depends on / 依赖: algebraMap, map_mul
-/
theorem coe_mul (a b : R) : (↑(a * b : R) : A) = ↑a * ↑b :=
  map_mul (algebraMap R A) a b

@[norm_cast]
/--
theorem `coe_pow` / 定理 `coe_pow`

English:
theorem coe_pow
  given: (a : R) (n : Nat)
  statement: (↑(a ^ n : R) : A) = (a : A) ^ n
  proof: map_pow (algebraMap R A) _ _

中文:
定理 coe_pow
  条件: (a : R) (n : 自然数)
  结论: (↑(a ^ n : R) : A) = (a : A) ^ n
  证明: map_pow (algebraMap R A) _ _

Depends on / 依赖: algebraMap, map_pow
-/
theorem coe_pow (a : R) (n : Nat) : (↑(a ^ n : R) : A) = (a : A) ^ n :=
  map_pow (algebraMap R A) _ _

end CommSemiringSemiring

section CommRingRing

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

@[norm_cast]
/--
theorem `coe_neg` / 定理 `coe_neg`

English:
theorem coe_neg
  given: (x : R)
  statement: (↑(-x : R) : A) = -↑x
  proof: map_neg (algebraMap R A) x

@[norm_cast]

中文:
定理 coe_neg
  条件: (x : R)
  结论: (↑(-x : R) : A) = -↑x
  证明: map_neg (algebraMap R A) x

@[norm_cast]

Depends on / 依赖: algebraMap, map_neg
-/
theorem coe_neg (x : R) : (↑(-x : R) : A) = -↑x :=
  map_neg (algebraMap R A) x

@[norm_cast]
/--
theorem `coe_sub` / 定理 `coe_sub`

English:
theorem coe_sub
  given: (a b : R)
  proof: map_sub (algebraMap R A) a b

中文:
定理 coe_sub
  条件: (a b : R)
  证明: map_sub (algebraMap R A) a b

Depends on / 依赖: algebraMap, map_sub
-/
theorem coe_sub (a b : R) :
    (↑(a - b : R) : A) = ↑a - ↑b :=
  map_sub (algebraMap R A) a b

end CommRingRing

end algebraMap

/--
Definition of `RingHom.toAlgebra'` / `RingHom.toAlgebra'` 的定义

English:
abbreviation RingHom.toAlgebra'
  signature: {R S} [CommSemiring R] [Semiring S] (i : R ->+* S)
  body: i c * x
  commutes' := h
  smul_def' _ _ := rfl
  algebraMap := i

中文:
缩写 RingHom.toAlgebra'
  签名: {R S} [CommSemiring R] [Semiring S] (i : R ->+* S)
  定义体: i c * x
  commutes' := h
  smul_def' _ _ := rfl
  algebraMap := i
-/
abbrev RingHom.toAlgebra' {R S} [CommSemiring R] [Semiring S] (i : R ->+* S)
    (h : forall c x, i c * x = x * i c) : Algebra R S where
  smul c x := i c * x
  commutes' := h
  smul_def' _ _ := rfl
  algebraMap := i

-- just simple lemmas for a declaration that is itself primed, no need for docstrings
set_option linter.docPrime false in
/--
theorem `RingHom.smul_toAlgebra'` / 定理 `RingHom.smul_toAlgebra'`

English:
theorem RingHom.smul_toAlgebra'
  statement: {R S} [CommSemiring R] [Semiring S] (i : R ->+* S)
  proof: RingHom.toAlgebra' i h
    r • s = i r * s := rfl

中文:
定理 RingHom.smul_toAlgebra'
  结论: {R S} [CommSemiring R] [Semiring S] (i : R ->+* S)
  证明: RingHom.toAlgebra' i h
    r • s = i r * s := rfl

Depends on / 依赖: RingHom, RingHom.toAlgebra, toAlgebra
-/
theorem RingHom.smul_toAlgebra' {R S} [CommSemiring R] [Semiring S] (i : R ->+* S)
    (h : forall c x, i c * x = x * i c) (r : R) (s : S) :
    let _ := RingHom.toAlgebra' i h
    r • s = i r * s := rfl

set_option linter.docPrime false in
/--
theorem `RingHom.algebraMap_toAlgebra'` / 定理 `RingHom.algebraMap_toAlgebra'`

English:
theorem RingHom.algebraMap_toAlgebra'
  statement: {R S} [CommSemiring R] [Semiring S] (i : R ->+* S)
  proof: rfl

中文:
定理 RingHom.algebraMap_toAlgebra'
  结论: {R S} [CommSemiring R] [Semiring S] (i : R ->+* S)
  证明: rfl
-/
theorem RingHom.algebraMap_toAlgebra' {R S} [CommSemiring R] [Semiring S] (i : R ->+* S)
    (h : forall c x, i c * x = x * i c) :
    @algebraMap R S _ _ (i.toAlgebra' h) = i :=
  rfl

/--
Definition of `RingHom.toAlgebra` / `RingHom.toAlgebra` 的定义

English:
abbreviation RingHom.toAlgebra
  signature: {R S} [CommSemiring R] [CommSemiring S] (i : R ->+* S)
  body: i.toAlgebra' fun _ => mul_comm _

中文:
缩写 RingHom.toAlgebra
  签名: {R S} [CommSemiring R] [CommSemiring S] (i : R ->+* S)
  定义体: i.toAlgebra' fun _ => mul_comm _

Depends on / 依赖: i.toAlgebra, mul_comm, toAlgebra
-/
abbrev RingHom.toAlgebra {R S} [CommSemiring R] [CommSemiring S] (i : R ->+* S) : Algebra R S :=
  i.toAlgebra' fun _ => mul_comm _

/--
theorem `RingHom.smul_toAlgebra` / 定理 `RingHom.smul_toAlgebra`

English:
theorem RingHom.smul_toAlgebra
  statement: {R S} [CommSemiring R] [CommSemiring S] (i : R ->+* S)
  proof: RingHom.toAlgebra i
    r • s = i r * s := rfl

中文:
定理 RingHom.smul_toAlgebra
  结论: {R S} [CommSemiring R] [CommSemiring S] (i : R ->+* S)
  证明: RingHom.toAlgebra i
    r • s = i r * s := rfl

Depends on / 依赖: RingHom, RingHom.toAlgebra, toAlgebra
-/
theorem RingHom.smul_toAlgebra {R S} [CommSemiring R] [CommSemiring S] (i : R ->+* S)
    (r : R) (s : S) :
    let _ := RingHom.toAlgebra i
    r • s = i r * s := rfl

/--
theorem `RingHom.algebraMap_toAlgebra` / 定理 `RingHom.algebraMap_toAlgebra`

English:
theorem RingHom.algebraMap_toAlgebra
  given: {R S} [CommSemiring R] [CommSemiring S] (i : R ->+* S)
  proof: rfl

中文:
定理 RingHom.algebraMap_toAlgebra
  条件: {R S} [CommSemiring R] [CommSemiring S] (i : R ->+* S)
  证明: rfl
-/
theorem RingHom.algebraMap_toAlgebra {R S} [CommSemiring R] [CommSemiring S] (i : R ->+* S) :
    @algebraMap R S _ _ i.toAlgebra = i :=
  rfl

namespace Algebra

variable {R : Type u} {S : Type v} {A : Type w} {B : Type*}

/--
Definition of `ofModule'` / `ofModule'` 的定义

English:
abbreviation ofModule'
  signature: [CommSemiring R] [Semiring A] [Module R A]
  body: { toFun r := r • (1 : A)
    map_one' := one_smul _ _
    map_mul' r₁ r₂ := by simp only [h₁, mul_smul]
    map_zero' := zero_smul _ _
    map_add' r₁ r₂ := add_smul r₁ r₂ 1 }
  commutes' r x := by simp [h₁, h₂]
  smul_def' r x := by simp [h₁]

中文:
缩写 ofModule'
  签名: [CommSemiring R] [Semiring A] [Module R A]
  定义体: { toFun r := r • (1 : A)
    map_one' := one_smul _ _
    map_mul' r₁ r₂ := by simp only [h₁, mul_smul]
    map_zero' := zero_smul _ _
    map_add' r₁ r₂ := add_smul r₁ r₂ 1 }
  commutes' r x := by simp [h₁, h₂]
  smul_def' r x := by simp [h₁]

Depends on / 依赖: add_smul, commutes, map_add, map_mul, map_one, map_zero, mul_smul, one_smul, smul_def, zero_smul
-/
abbrev ofModule' [CommSemiring R] [Semiring A] [Module R A]
    (h₁ : forall (r : R) (x : A), r • (1 : A) * x = r • x)
    (h₂ : forall (r : R) (x : A), x * r • (1 : A) = r • x) : Algebra R A where
  algebraMap :=
  { toFun r := r • (1 : A)
    map_one' := one_smul _ _
    map_mul' r₁ r₂ := by simp only [h₁, mul_smul]
    map_zero' := zero_smul _ _
    map_add' r₁ r₂ := add_smul r₁ r₂ 1 }
  commutes' r x := by simp [h₁, h₂]
  smul_def' r x := by simp [h₁]

/--
Definition of `ofModule` / `ofModule` 的定义

English:
abbreviation ofModule
  signature: [CommSemiring R] [Semiring A] [Module R A]
  body: ofModule' (fun r x => by rw [h₁, one_mul]) fun r x => by rw [h₂, mul_one]

中文:
缩写 ofModule
  签名: [CommSemiring R] [Semiring A] [Module R A]
  定义体: ofModule' (fun r x => by rw [h₁, one_mul]) fun r x => by rw [h₂, mul_one]

Depends on / 依赖: mul_one, ofModule, one_mul
-/
abbrev ofModule [CommSemiring R] [Semiring A] [Module R A]
    (h₁ : forall (r : R) (x y : A), r • x * y = r • (x * y))
    (h₂ : forall (r : R) (x y : A), x * r • y = r • (x * y)) : Algebra R A :=
  ofModule' (fun r x => by rw [h₁, one_mul]) fun r x => by rw [h₂, mul_one]

section Semiring

variable [CommSemiring R] [CommSemiring S]
variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

-- We'll later use this to show `Algebra ℤ M` is a subsingleton.
/-- To prove two algebra structures on a fixed `[CommSemiring R] [Semiring A]` agree,
it suffices to check the `algebraMap`s agree.
-/
@[ext]
/--
theorem `algebra_ext` / 定理 `algebra_ext`

English:
theorem algebra_ext
  statement: {R : Type*} [CommSemiring R] {A : Type*} [Semiring A] (P Q : Algebra R A)
  proof: by
  replace h : P.algebraMap = Q.algebraMap := DFunLike.ext _ _ h
  have h' : (haveI := P; (· • ·) : R -> A -> A) = (haveI := Q; (· • ·) : R -> A -> A) := by
    funext r a
    rw [P.smul_def']; rw [Q.smul_def']; rw [h]
  rcases P with @⟨⟨P⟩⟩
  congr

中文:
定理 algebra_ext
  结论: {R : 类型} [CommSemiring R] {A : 类型} [Semiring A] (P Q : Algebra R A)
  证明: by
  replace h : P.algebraMap = Q.algebraMap := DFunLike.ext _ _ h
  have h' : (haveI := P; (· • ·) : R -> A -> A) = (haveI := Q; (· • ·) : R -> A -> A) := by
    funext r a
    rw [P.smul_def']; rw [Q.smul_def']; rw [h]
  rcases P with @⟨⟨P⟩⟩
  congr

Depends on / 依赖: algebraMap
-/
theorem algebra_ext {R : Type*} [CommSemiring R] {A : Type*} [Semiring A] (P Q : Algebra R A)
    (h : forall r : R, (haveI := P; algebraMap R A r) = haveI := Q; algebraMap R A r) :
    P = Q := by
  replace h : P.algebraMap = Q.algebraMap := DFunLike.ext _ _ h
  have h' : (haveI := P; (· • ·) : R -> A -> A) = (haveI := Q; (· • ·) : R -> A -> A) := by
    funext r a
    rw [P.smul_def']; rw [Q.smul_def']; rw [h]
  rcases P with @⟨⟨P⟩⟩
  congr

/--
lemma `_root_.toAlgebra_algebraMap` / 引理 `_root_.toAlgebra_algebraMap`

English:
lemma _root_.toAlgebra_algebraMap
  given: [Algebra R S]
  proof: algebra_ext _ _ fun _ => rfl

中文:
引理 _root_.toAlgebra_algebraMap
  条件: [Algebra R S]
  证明: algebra_ext _ _ fun _ => rfl

Depends on / 依赖: algebra_ext
-/
lemma _root_.toAlgebra_algebraMap [Algebra R S] :
    (algebraMap R S).toAlgebra = ‹_› :=
  algebra_ext _ _ fun _ => rfl

-- see Note [lower instance priority]
instance (priority := 200) toModule {R A} {_ : CommSemiring R} {_ : Semiring A} [Algebra R A] :
    Module R A where
  one_smul _ := by simp [smul_def']
  mul_smul := by simp [smul_def', mul_assoc]
  smul_add := by simp [smul_def', mul_add]
  smul_zero := by simp [smul_def']
  add_smul := by simp [smul_def', add_mul]
  zero_smul := by simp [smul_def']

/--
theorem `smul_def` / 定理 `smul_def`

English:
theorem smul_def
  given: (r : R) (x : A)
  statement: r • x = algebraMap R A r * x
  proof: Algebra.smul_def' r x

中文:
定理 smul_def
  条件: (r : R) (x : A)
  结论: r • x = algebraMap R A r * x
  证明: Algebra.smul_def' r x

Depends on / 依赖: Algebra, Algebra.smul_def, smul_def
-/
theorem smul_def (r : R) (x : A) : r • x = algebraMap R A r * x :=
  Algebra.smul_def' r x

/--
theorem `algebraMap_eq_smul_one` / 定理 `algebraMap_eq_smul_one`

English:
theorem algebraMap_eq_smul_one
  given: (r : R)
  statement: algebraMap R A r = r • (1 : A)
  proof: calc
    algebraMap R A r = algebraMap R A r * 1 := (mul_one _).symm
    _ = r • (1 : A) := (Algebra.smul_def r 1).symm

中文:
定理 algebraMap_eq_smul_one
  条件: (r : R)
  结论: algebraMap R A r = r • (1 : A)
  证明: calc
    algebraMap R A r = algebraMap R A r * 1 := (mul_one _).symm
    _ = r • (1 : A) := (Algebra.smul_def r 1).symm

Depends on / 依赖: Algebra, Algebra.smul_def, algebraMap, mul_one, smul_def
-/
theorem algebraMap_eq_smul_one (r : R) : algebraMap R A r = r • (1 : A) :=
  calc
    algebraMap R A r = algebraMap R A r * 1 := (mul_one _).symm
    _ = r • (1 : A) := (Algebra.smul_def r 1).symm

/--
theorem `algebraMap_eq_smul_one'` / 定理 `algebraMap_eq_smul_one'`

English:
theorem algebraMap_eq_smul_one'
  statement: ⇑(algebraMap R A) = fun r => r • (1 : A)
  proof: funext algebraMap_eq_smul_one

中文:
定理 algebraMap_eq_smul_one'
  结论: ⇑(algebraMap R A) = fun r => r • (1 : A)
  证明: funext algebraMap_eq_smul_one

Depends on / 依赖: algebraMap_eq_smul_one
-/
theorem algebraMap_eq_smul_one' : ⇑(algebraMap R A) = fun r => r • (1 : A) :=
  funext algebraMap_eq_smul_one

/--
theorem `commutes` / 定理 `commutes`

English:
theorem commutes
  given: (r : R) (x : A)
  statement: algebraMap R A r * x = x * algebraMap R A r
  proof: Algebra.commutes' r x

中文:
定理 commutes
  条件: (r : R) (x : A)
  结论: algebraMap R A r * x = x * algebraMap R A r
  证明: Algebra.commutes' r x

Depends on / 依赖: Algebra, Algebra.commutes, commutes
-/
theorem commutes (r : R) (x : A) : algebraMap R A r * x = x * algebraMap R A r :=
  Algebra.commutes' r x

/--
lemma `commute_algebraMap_left` / 引理 `commute_algebraMap_left`

English:
lemma commute_algebraMap_left
  given: (r : R) (x : A)
  statement: Commute (algebraMap R A r) x
  proof: Algebra.commutes r x

中文:
引理 commute_algebraMap_left
  条件: (r : R) (x : A)
  结论: Commute (algebraMap R A r) x
  证明: Algebra.commutes r x

Depends on / 依赖: Algebra, Algebra.commutes, commutes
-/
lemma commute_algebraMap_left (r : R) (x : A) : Commute (algebraMap R A r) x :=
  Algebra.commutes r x

/--
lemma `commute_algebraMap_right` / 引理 `commute_algebraMap_right`

English:
lemma commute_algebraMap_right
  given: (r : R) (x : A)
  statement: Commute x (algebraMap R A r)
  proof: (Algebra.commutes r x).symm

中文:
引理 commute_algebraMap_right
  条件: (r : R) (x : A)
  结论: Commute x (algebraMap R A r)
  证明: (Algebra.commutes r x).symm

Depends on / 依赖: Algebra, Algebra.commutes, commutes
-/
lemma commute_algebraMap_right (r : R) (x : A) : Commute x (algebraMap R A r) :=
  (Algebra.commutes r x).symm

/--
theorem `left_comm` / 定理 `left_comm`

English:
theorem left_comm
  given: (x : A) (r : R) (y : A)
  proof: by
  rw [← mul_assoc]; rw [← commutes]; rw [mul_assoc]

中文:
定理 left_comm
  条件: (x : A) (r : R) (y : A)
  证明: by
  rw [← mul_assoc]; rw [← commutes]; rw [mul_assoc]

Depends on / 依赖: commutes, mul_assoc
-/
theorem left_comm (x : A) (r : R) (y : A) :
    x * (algebraMap R A r * y) = algebraMap R A r * (x * y) := by
  rw [← mul_assoc]; rw [← commutes]; rw [mul_assoc]

/--
theorem `right_comm` / 定理 `right_comm`

English:
theorem right_comm
  given: (x : A) (r : R) (y : A)
  proof: by
  rw [mul_assoc]; rw [commutes]; rw [← mul_assoc]

中文:
定理 right_comm
  条件: (x : A) (r : R) (y : A)
  证明: by
  rw [mul_assoc]; rw [commutes]; rw [← mul_assoc]

Depends on / 依赖: commutes, mul_assoc
-/
theorem right_comm (x : A) (r : R) (y : A) :
    x * algebraMap R A r * y = x * y * algebraMap R A r := by
  rw [mul_assoc]; rw [commutes]; rw [← mul_assoc]

/-- This has high priority because it is almost always the right instance when it applies. -/
instance (priority := high) _root_.IsScalarTower.right : IsScalarTower R A A :=
  ⟨fun x y z => by rw [smul_eq_mul, smul_eq_mul, smul_def, smul_def, mul_assoc]⟩

@[simp]
/--
theorem `_root_.RingHom.smulOneHom_eq_algebraMap` / 定理 `_root_.RingHom.smulOneHom_eq_algebraMap`

English:
theorem _root_.RingHom.smulOneHom_eq_algebraMap
  statement: RingHom.smulOneHom = algebraMap R A
  proof: RingHom.ext fun r => (algebraMap_eq_smul_one r).symm

中文:
定理 _root_.RingHom.smulOneHom_eq_algebraMap
  结论: RingHom.smulOneHom = algebraMap R A
  证明: RingHom.ext fun r => (algebraMap_eq_smul_one r).symm

Depends on / 依赖: RingHom, RingHom.ext, algebraMap_eq_smul_one
-/
theorem _root_.RingHom.smulOneHom_eq_algebraMap : RingHom.smulOneHom = algebraMap R A :=
  RingHom.ext fun r => (algebraMap_eq_smul_one r).symm

-- TODO: set up `IsScalarTower.smulCommClass` earlier so that we can actually prove this using
-- `mul_smul_comm s x y`.

/-- This is just a special case of the global `mul_smul_comm` lemma that requires less typeclass
search (and was here first). -/
@[simp]
/--
theorem `mul_smul_comm` / 定理 `mul_smul_comm`

English:
theorem mul_smul_comm
  given: (s : R) (x y : A)
  statement: x * s • y = s • (x * y)
  proof: by
  rw [smul_def]; rw [smul_def]; rw [left_comm]

中文:
定理 mul_smul_comm
  条件: (s : R) (x y : A)
  结论: x * s • y = s • (x * y)
  证明: by
  rw [smul_def]; rw [smul_def]; rw [left_comm]
-/
protected theorem mul_smul_comm (s : R) (x y : A) : x * s • y = s • (x * y) := by
  rw [smul_def]; rw [smul_def]; rw [left_comm]

/-- This is just a special case of the global `smul_mul_assoc` lemma that requires less typeclass
search (and was here first). -/
@[simp]
/--
theorem `smul_mul_assoc` / 定理 `smul_mul_assoc`

English:
theorem smul_mul_assoc
  given: (r : R) (x y : A)
  statement: r • x * y = r • (x * y)
  proof: smul_mul_assoc r x y

@[simp]

中文:
定理 smul_mul_assoc
  条件: (r : R) (x y : A)
  结论: r • x * y = r • (x * y)
  证明: smul_mul_assoc r x y

@[simp]
-/
protected theorem smul_mul_assoc (r : R) (x y : A) : r • x * y = r • (x * y) :=
  smul_mul_assoc r x y

@[simp]
/--
theorem `_root_.smul_algebraMap` / 定理 `_root_.smul_algebraMap`

English:
theorem _root_.smul_algebraMap
  statement: {α : Type*} [Monoid α] [MulDistribMulAction α A]
  proof: by
  rw [algebraMap_eq_smul_one]; rw [smul_comm a r (1 : A)]; rw [smul_one]

中文:
定理 _root_.smul_algebraMap
  结论: {α : 类型} [Monoid α] [MulDistribMulAction α A]
  证明: by
  rw [algebraMap_eq_smul_one]; rw [smul_comm a r (1 : A)]; rw [smul_one]

Depends on / 依赖: algebraMap_eq_smul_one, smul_comm, smul_one
-/
theorem _root_.smul_algebraMap {α : Type*} [Monoid α] [MulDistribMulAction α A]
    [SMulCommClass α R A] (a : α) (r : R) : a • algebraMap R A r = algebraMap R A r := by
  rw [algebraMap_eq_smul_one]; rw [smul_comm a r (1 : A)]; rw [smul_one]

section compHom

variable (A) (f : S ->+* R)

/--
Definition of `compHom` / `compHom` 的定义

English:
abbreviation compHom
  signature: : Algebra S A where
  body: Module.compHom A f
  algebraMap := (algebraMap R A).comp f
  commutes' _ _ := Algebra.commutes _ _
  smul_def' _ _ := Algebra.smul_def _ _

中文:
缩写 compHom
  签名: : Algebra S A where
  定义体: Module.compHom A f
  algebraMap := (algebraMap R A).comp f
  commutes' _ _ := Algebra.commutes _ _
  smul_def' _ _ := Algebra.smul_def _ _

Depends on / 依赖: Module, Module.compHom, compHom
-/
abbrev compHom : Algebra S A where
  __ := Module.compHom A f
  algebraMap := (algebraMap R A).comp f
  commutes' _ _ := Algebra.commutes _ _
  smul_def' _ _ := Algebra.smul_def _ _

/--
theorem `compHom_smul_def` / 定理 `compHom_smul_def`

English:
theorem compHom_smul_def
  given: (s : S) (x : A)
  proof: compHom A f
    s • x = f s • x := rfl

中文:
定理 compHom_smul_def
  条件: (s : S) (x : A)
  证明: compHom A f
    s • x = f s • x := rfl

Depends on / 依赖: compHom
-/
theorem compHom_smul_def (s : S) (x : A) :
    letI := compHom A f
    s • x = f s • x := rfl

/--
theorem `compHom_algebraMap_eq` / 定理 `compHom_algebraMap_eq`

English:
theorem compHom_algebraMap_eq
  proof: compHom A f
    algebraMap S A = (algebraMap R A).comp f := rfl

中文:
定理 compHom_algebraMap_eq
  证明: compHom A f
    algebraMap S A = (algebraMap R A).comp f := rfl

Depends on / 依赖: compHom
-/
theorem compHom_algebraMap_eq :
    letI := compHom A f
    algebraMap S A = (algebraMap R A).comp f := rfl

/--
theorem `compHom_algebraMap_apply` / 定理 `compHom_algebraMap_apply`

English:
theorem compHom_algebraMap_apply
  given: (s : S)
  proof: compHom A f
    algebraMap S A s = (algebraMap R A) (f s) := rfl

中文:
定理 compHom_algebraMap_apply
  条件: (s : S)
  证明: compHom A f
    algebraMap S A s = (algebraMap R A) (f s) := rfl

Depends on / 依赖: compHom
-/
theorem compHom_algebraMap_apply (s : S) :
    letI := compHom A f
    algebraMap S A s = (algebraMap R A) (f s) := rfl

end compHom


variable (R A)

/--
Definition of `linearMap` / `linearMap` 的定义

English:
definition linearMap
  signature: : R ->ₗ[R] A
  body: { algebraMap R A with map_smul' := fun x y => by simp [Algebra.smul_def] }

@[inherit_doc] scoped[RingTheory.LinearMap] notation "η" => Algebra.linearMap _ _
@[inherit_doc] scoped[RingTheory.LinearMap] notation "η[" R "]" => Algebra.linearMap R _

@[simp]

中文:
定义 linearMap
  签名: : R ->ₗ[R] A
  定义体: { algebraMap R A with map_smul' := fun x y => by simp [Algebra.smul_def] }

@[inherit_doc] scoped[RingTheory.LinearMap] notation "η" => Algebra.linearMap _ _
@[inherit_doc] scoped[RingTheory.LinearMap] notation "η[" R "]" => Algebra.linearMap R _

@[simp]
-/
protected def linearMap : R ->ₗ[R] A :=
  { algebraMap R A with map_smul' := fun x y => by simp [Algebra.smul_def] }

@[inherit_doc] scoped[RingTheory.LinearMap] notation "η" => Algebra.linearMap _ _
@[inherit_doc] scoped[RingTheory.LinearMap] notation "η[" R "]" => Algebra.linearMap R _

@[simp]
/--
theorem `linearMap_apply` / 定理 `linearMap_apply`

English:
theorem linearMap_apply
  given: (r : R)
  statement: Algebra.linearMap R A r = algebraMap R A r
  proof: rfl

中文:
定理 linearMap_apply
  条件: (r : R)
  结论: Algebra.linearMap R A r = algebraMap R A r
  证明: rfl
-/
theorem linearMap_apply (r : R) : Algebra.linearMap R A r = algebraMap R A r :=
  rfl

/--
theorem `coe_linearMap` / 定理 `coe_linearMap`

English:
theorem coe_linearMap
  statement: ⇑(Algebra.linearMap R A) = algebraMap R A
  proof: rfl

中文:
定理 coe_linearMap
  结论: ⇑(Algebra.linearMap R A) = algebraMap R A
  证明: rfl
-/
theorem coe_linearMap : ⇑(Algebra.linearMap R A) = algebraMap R A :=
  rfl

-- see Note [higher instance priority]
/-- The identity map inducing an `Algebra` structure. -/
instance (priority := 1100) id : Algebra R R where
  -- We override `toFun` and `toSMul` because `RingHom.id` is not reducible and cannot
  -- be made so without a significant performance hit.
  -- see library note [reducible non-instances].
  toSMul := instSMulOfMul
  __ := (RingHom.id R).toAlgebra

/--
lemma `linearMap_self` / 引理 `linearMap_self`

English:
lemma linearMap_self
  statement: Algebra.linearMap R R = .id
  proof: rfl

中文:
引理 linearMap_self
  结论: Algebra.linearMap R R = .id
  证明: rfl
-/
@[simp] lemma linearMap_self : Algebra.linearMap R R = .id := rfl

variable {R A}

/--
lemma `algebraMap_self` / 引理 `algebraMap_self`

English:
lemma algebraMap_self
  statement: algebraMap R R = .id _
  proof: rfl

中文:
引理 algebraMap_self
  结论: algebraMap R R = .id _
  证明: rfl
-/
@[simp] lemma algebraMap_self : algebraMap R R = .id _ := rfl
/--
lemma `algebraMap_self_apply` / 引理 `algebraMap_self_apply`

English:
lemma algebraMap_self_apply
  given: (x : R)
  statement: algebraMap R R x = x
  proof: rfl

中文:
引理 algebraMap_self_apply
  条件: (x : R)
  结论: algebraMap R R x = x
  证明: rfl
-/
lemma algebraMap_self_apply (x : R) : algebraMap R R x = x := rfl

end Semiring

end Algebra

section algebraMap

variable {A B : Type*} (a : A) (b : B) (C : Type*)
  [SMul A B] [CommSemiring B] [Semiring C] [Algebra B C]

@[norm_cast]
/--
theorem `algebraMap.coe_smul` / 定理 `algebraMap.coe_smul`

English:
theorem algebraMap.coe_smul
  given: [SMul A C] [IsScalarTower A B C]
  statement: (a • b : B) = a • (b : C)
  proof: by
  simp [Algebra.algebraMap_eq_smul_one]

@[norm_cast]

中文:
定理 algebraMap.coe_smul
  条件: [SMul A C] [IsScalarTower A B C]
  结论: (a • b : B) = a • (b : C)
  证明: by
  simp [Algebra.algebraMap_eq_smul_one]

@[norm_cast]

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, algebraMap_eq_smul_one
-/
theorem algebraMap.coe_smul [SMul A C] [IsScalarTower A B C] : (a • b : B) = a • (b : C) := by
  simp [Algebra.algebraMap_eq_smul_one]

@[norm_cast]
/--
theorem `algebraMap.coe_smul'` / 定理 `algebraMap.coe_smul'`

English:
theorem algebraMap.coe_smul'
  given: [Monoid A] [MulDistribMulAction A C] [SMulDistribClass A B C]
  proof: by
  simp [Algebra.algebraMap_eq_smul_one, smul_distrib_smul]

中文:
定理 algebraMap.coe_smul'
  条件: [Monoid A] [MulDistribMulAction A C] [SMulDistribClass A B C]
  证明: by
  simp [Algebra.algebraMap_eq_smul_one, smul_distrib_smul]

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, algebraMap_eq_smul_one, smul_distrib_smul
-/
theorem algebraMap.coe_smul' [Monoid A] [MulDistribMulAction A C] [SMulDistribClass A B C] :
    (a • b : B) = a • (b : C) := by
  simp [Algebra.algebraMap_eq_smul_one, smul_distrib_smul]

/--
theorem `algebraMap.smul` / 定理 `algebraMap.smul`

English:
theorem algebraMap.smul
  given: [SMul A C] [IsScalarTower A B C]
  proof: coe_smul _ _ _

中文:
定理 algebraMap.smul
  条件: [SMul A C] [IsScalarTower A B C]
  证明: coe_smul _ _ _

Depends on / 依赖: coe_smul
-/
theorem algebraMap.smul [SMul A C] [IsScalarTower A B C] :
    algebraMap B C (a • b) = a • (algebraMap B C b) := coe_smul _ _ _

/--
theorem `algebraMap.smul'` / 定理 `algebraMap.smul'`

English:
theorem algebraMap.smul'
  given: [Monoid A] [MulDistribMulAction A C] [SMulDistribClass A B C]
  proof: coe_smul' _ _ _

中文:
定理 algebraMap.smul'
  条件: [Monoid A] [MulDistribMulAction A C] [SMulDistribClass A B C]
  证明: coe_smul' _ _ _

Depends on / 依赖: coe_smul
-/
theorem algebraMap.smul' [Monoid A] [MulDistribMulAction A C] [SMulDistribClass A B C] :
    algebraMap B C (a • b) = a • (algebraMap B C b) := coe_smul' _ _ _

end algebraMap
