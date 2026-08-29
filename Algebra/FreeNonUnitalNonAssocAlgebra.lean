/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Free
public import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Free algebras

Given a semiring `R` and a type `X`, we construct the free non-unital, non-associative algebra on
`X` with coefficients in `R`, together with its universal property. The construction is valuable
because it can be used to build free algebras with more structure, e.g., free Lie algebras.

Note that elsewhere we have a construction of the free unital, associative algebra. This is called
`FreeAlgebra`.

## Main definitions

  * `FreeNonUnitalNonAssocAlgebra`
  * `FreeNonUnitalNonAssocAlgebra.lift`
  * `FreeNonUnitalNonAssocAlgebra.of`

## Implementation details

We construct the free algebra as the magma algebra, with coefficients in `R`, of the free magma on
`X`. However we regard this as an implementation detail and thus deliberately omit the lemmas
`of_apply` and `lift_apply`, and we mark `FreeNonUnitalNonAssocAlgebra` and `lift` as
irreducible once we have established the universal property.

## Tags

free algebra, non-unital, non-associative, free magma, magma algebra, universal property,
forgetful functor, adjoint functor
-/

@[expose] public noncomputable section

open scoped MonoidAlgebra

variable (R X A : Type*) [Semiring R]

/--
Definition of `FreeNonUnitalNonAssocAlgebra` / `FreeNonUnitalNonAssocAlgebra` 的定义

English:
abbreviation FreeNonUnitalNonAssocAlgebra
  body: R[FreeMagma X]

中文:
缩写 FreeNonUnitalNonAssocAlgebra
  定义体: R[FreeMagma X]

Depends on / 依赖: FreeMagma
-/
abbrev FreeNonUnitalNonAssocAlgebra := R[FreeMagma X]

namespace FreeNonUnitalNonAssocAlgebra

variable {X A}

/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: : X -> FreeNonUnitalNonAssocAlgebra R X
  body: MonoidAlgebra.ofMagma R _ ∘ FreeMagma.of

中文:
定义 of
  签名: : X -> FreeNonUnitalNonAssocAlgebra R X
  定义体: MonoidAlgebra.ofMagma R _ ∘ FreeMagma.of

Depends on / 依赖: FreeMagma, FreeMagma.of, MonoidAlgebra, MonoidAlgebra.ofMagma, ofMagma
-/
def of : X -> FreeNonUnitalNonAssocAlgebra R X :=
  MonoidAlgebra.ofMagma R _ ∘ FreeMagma.of

variable [NonUnitalNonAssocSemiring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : (X -> A) ≃ (FreeNonUnitalNonAssocAlgebra R X ->ₙₐ[R] A)
  body: FreeMagma.lift.trans (MonoidAlgebra.liftMagma R)

@[simp]

中文:
定义 lift
  签名: : (X -> A) ≃ (FreeNonUnitalNonAssocAlgebra R X ->ₙₐ[R] A)
  定义体: FreeMagma.lift.trans (MonoidAlgebra.liftMagma R)

@[simp]

Depends on / 依赖: FreeMagma, FreeMagma.lift.trans, MonoidAlgebra, MonoidAlgebra.liftMagma, liftMagma
-/
def lift : (X -> A) ≃ (FreeNonUnitalNonAssocAlgebra R X ->ₙₐ[R] A) :=
  FreeMagma.lift.trans (MonoidAlgebra.liftMagma R)

@[simp]
/--
theorem `lift_symm_apply` / 定理 `lift_symm_apply`

English:
theorem lift_symm_apply
  given: (F : FreeNonUnitalNonAssocAlgebra R X ->ₙₐ[R] A)
  proof: rfl

@[simp]

中文:
定理 lift_symm_apply
  条件: (F : FreeNonUnitalNonAssocAlgebra R X ->ₙₐ[R] A)
  证明: rfl

@[simp]
-/
theorem lift_symm_apply (F : FreeNonUnitalNonAssocAlgebra R X ->ₙₐ[R] A) :
    (lift R).symm F = F ∘ of R := rfl

@[simp]
/--
theorem `of_comp_lift` / 定理 `of_comp_lift`

English:
theorem of_comp_lift
  given: (f : X -> A)
  statement: lift R f ∘ of R = f
  proof: (lift R).left_inv f

@[simp]

中文:
定理 of_comp_lift
  条件: (f : X -> A)
  结论: lift R f ∘ of R = f
  证明: (lift R).left_inv f

@[simp]

Depends on / 依赖: left_inv
-/
theorem of_comp_lift (f : X -> A) : lift R f ∘ of R = f :=
  (lift R).left_inv f

@[simp]
/--
theorem `lift_unique` / 定理 `lift_unique`

English:
theorem lift_unique
  given: (f : X -> A) (F : FreeNonUnitalNonAssocAlgebra R X ->ₙₐ[R] A)
  proof: (lift R).symm_apply_eq

@[simp]

中文:
定理 lift_unique
  条件: (f : X -> A) (F : FreeNonUnitalNonAssocAlgebra R X ->ₙₐ[R] A)
  证明: (lift R).symm_apply_eq

@[simp]

Depends on / 依赖: symm_apply_eq
-/
theorem lift_unique (f : X -> A) (F : FreeNonUnitalNonAssocAlgebra R X ->ₙₐ[R] A) :
    F ∘ of R = f ↔ F = lift R f :=
  (lift R).symm_apply_eq

@[simp]
/--
theorem `lift_of_apply` / 定理 `lift_of_apply`

English:
theorem lift_of_apply
  given: (f : X -> A) (x)
  statement: lift R f (of R x) = f x
  proof: congr_fun (of_comp_lift _ f) x

@[simp]

中文:
定理 lift_of_apply
  条件: (f : X -> A) (x)
  结论: lift R f (of R x) = f x
  证明: congr_fun (of_comp_lift _ f) x

@[simp]

Depends on / 依赖: congr_fun, of_comp_lift
-/
theorem lift_of_apply (f : X -> A) (x) : lift R f (of R x) = f x :=
  congr_fun (of_comp_lift _ f) x

@[simp]
/--
theorem `lift_comp_of` / 定理 `lift_comp_of`

English:
theorem lift_comp_of
  given: (F : FreeNonUnitalNonAssocAlgebra R X ->ₙₐ[R] A)
  statement: lift R (F ∘ of R) = F
  proof: (lift R).apply_symm_apply F

@[ext]

中文:
定理 lift_comp_of
  条件: (F : FreeNonUnitalNonAssocAlgebra R X ->ₙₐ[R] A)
  结论: lift R (F ∘ of R) = F
  证明: (lift R).apply_symm_apply F

@[ext]

Depends on / 依赖: apply_symm_apply
-/
theorem lift_comp_of (F : FreeNonUnitalNonAssocAlgebra R X ->ₙₐ[R] A) : lift R (F ∘ of R) = F :=
  (lift R).apply_symm_apply F

@[ext]
/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  statement: {F₁ F₂ : FreeNonUnitalNonAssocAlgebra R X ->ₙₐ[R] A}
  proof: (lift R).symm.injective funext h

中文:
定理 hom_ext
  结论: {F₁ F₂ : FreeNonUnitalNonAssocAlgebra R X ->ₙₐ[R] A}
  证明: (lift R).symm.injective funext h

Depends on / 依赖: injective, symm.injective
-/
theorem hom_ext {F₁ F₂ : FreeNonUnitalNonAssocAlgebra R X ->ₙₐ[R] A}
    (h : forall x, F₁ (of R x) = F₂ (of R x)) : F₁ = F₂ :=
(lift R).symm.injective funext h

end FreeNonUnitalNonAssocAlgebra
