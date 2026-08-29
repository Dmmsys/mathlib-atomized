/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval

/-!
## Counit morphisms for multivariate polynomials

One may consider the ring of multivariate polynomials `MvPolynomial A R` with coefficients in `R`
and variables indexed by `A`. If `A` is not just a type, but an algebra over `R`,
then there is a natural surjective algebra homomorphism `MvPolynomial A R →ₐ[R] A`
obtained by `X a ↦ a`.

### Main declarations

* `MvPolynomial.ACounit R A` is the natural surjective algebra homomorphism
  `MvPolynomial A R →ₐ[R] A` obtained by `X a ↦ a`
* `MvPolynomial.counit` is an “absolute” variant with `R = ℤ`
* `MvPolynomial.counitNat` is an “absolute” variant with `R = ℕ`

-/

@[expose] public section


namespace MvPolynomial

open Function

variable (A B R : Type*) [CommSemiring A] [CommSemiring B] [CommRing R] [Algebra A B]

/--
Definition of `ACounit` / `ACounit` 的定义

English:
definition ACounit
  signature: : MvPolynomial B A ->ₐ[A] B
  body: aeval id

中文:
定义 ACounit
  签名: : MvPolynomial B A ->ₐ[A] B
  定义体: aeval id
-/
noncomputable def ACounit : MvPolynomial B A ->ₐ[A] B :=
  aeval id

variable {B}

@[simp]
/--
theorem `ACounit_X` / 定理 `ACounit_X`

English:
theorem ACounit_X
  given: (b : B)
  statement: ACounit A B (X b) = b
  proof: aeval_X _ b

中文:
定理 ACounit_X
  条件: (b : B)
  结论: ACounit A B (X b) = b
  证明: aeval_X _ b

Depends on / 依赖: aeval_X
-/
theorem ACounit_X (b : B) : ACounit A B (X b) = b :=
  aeval_X _ b

variable {A} (B)

/--
theorem `ACounit_C` / 定理 `ACounit_C`

English:
theorem ACounit_C
  given: (a : A)
  statement: ACounit A B (C a) = algebraMap A B a
  proof: aeval_C _ a

中文:
定理 ACounit_C
  条件: (a : A)
  结论: ACounit A B (C a) = algebraMap A B a
  证明: aeval_C _ a

Depends on / 依赖: aeval_C
-/
theorem ACounit_C (a : A) : ACounit A B (C a) = algebraMap A B a :=
  aeval_C _ a

variable (A)

/--
theorem `ACounit_surjective` / 定理 `ACounit_surjective`

English:
theorem ACounit_surjective
  statement: Surjective (ACounit A B)
  proof: fun b => ⟨X b, ACounit_X A b⟩

中文:
定理 ACounit_surjective
  结论: Surjective (ACounit A B)
  证明: fun b => ⟨X b, ACounit_X A b⟩

Depends on / 依赖: ACounit_X
-/
theorem ACounit_surjective : Surjective (ACounit A B) := fun b => ⟨X b, ACounit_X A b⟩

/--
Definition of `counit` / `counit` 的定义

English:
definition counit
  signature: : MvPolynomial R Int ->+* R
  body: (ACounit Int R).toRingHom

中文:
定义 counit
  签名: : MvPolynomial R 整数 ->+* R
  定义体: (ACounit Int R).toRingHom

Depends on / 依赖: ACounit, toRingHom
-/
noncomputable def counit : MvPolynomial R Int ->+* R :=
  (ACounit Int R).toRingHom

/--
Definition of `counitNat` / `counitNat` 的定义

English:
definition counitNat
  signature: : MvPolynomial A Nat ->+* A
  body: ACounit Nat A

中文:
定义 counitNat
  签名: : MvPolynomial A 自然数 ->+* A
  定义体: ACounit Nat A

Depends on / 依赖: ACounit
-/
noncomputable def counitNat : MvPolynomial A Nat ->+* A :=
  ACounit Nat A

/--
theorem `counit_surjective` / 定理 `counit_surjective`

English:
theorem counit_surjective
  statement: Surjective (counit R)
  proof: ACounit_surjective Int R

中文:
定理 counit_surjective
  结论: Surjective (counit R)
  证明: ACounit_surjective Int R

Depends on / 依赖: ACounit_surjective
-/
theorem counit_surjective : Surjective (counit R) :=
  ACounit_surjective Int R

/--
theorem `counitNat_surjective` / 定理 `counitNat_surjective`

English:
theorem counitNat_surjective
  statement: Surjective (counitNat A)
  proof: ACounit_surjective Nat A

中文:
定理 counitNat_surjective
  结论: Surjective (counit自然数 A)
  证明: ACounit_surjective Nat A

Depends on / 依赖: ACounit_surjective
-/
theorem counitNat_surjective : Surjective (counitNat A) :=
  ACounit_surjective Nat A

/--
theorem `counit_C` / 定理 `counit_C`

English:
theorem counit_C
  given: (n : Int)
  statement: counit R (C n) = n
  proof: ACounit_C _ _

中文:
定理 counit_C
  条件: (n : 整数)
  结论: counit R (C n) = n
  证明: ACounit_C _ _

Depends on / 依赖: ACounit_C
-/
theorem counit_C (n : Int) : counit R (C n) = n :=
  ACounit_C _ _

/--
theorem `counitNat_C` / 定理 `counitNat_C`

English:
theorem counitNat_C
  given: (n : Nat)
  statement: counitNat A (C n) = n
  proof: ACounit_C _ _

中文:
定理 counitNat_C
  条件: (n : 自然数)
  结论: counit自然数 A (C n) = n
  证明: ACounit_C _ _

Depends on / 依赖: ACounit_C
-/
theorem counitNat_C (n : Nat) : counitNat A (C n) = n :=
  ACounit_C _ _

variable {R A}

@[simp]
/--
theorem `counit_X` / 定理 `counit_X`

English:
theorem counit_X
  given: (r : R)
  statement: counit R (X r) = r
  proof: ACounit_X _ _

@[simp]

中文:
定理 counit_X
  条件: (r : R)
  结论: counit R (X r) = r
  证明: ACounit_X _ _

@[simp]

Depends on / 依赖: ACounit_X
-/
theorem counit_X (r : R) : counit R (X r) = r :=
  ACounit_X _ _

@[simp]
/--
theorem `counitNat_X` / 定理 `counitNat_X`

English:
theorem counitNat_X
  given: (a : A)
  statement: counitNat A (X a) = a
  proof: ACounit_X _ _

中文:
定理 counitNat_X
  条件: (a : A)
  结论: counit自然数 A (X a) = a
  证明: ACounit_X _ _

Depends on / 依赖: ACounit_X
-/
theorem counitNat_X (a : A) : counitNat A (X a) = a :=
  ACounit_X _ _

end MvPolynomial
