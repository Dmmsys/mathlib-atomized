/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Anne Baanen
-/
module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.LinearAlgebra.Span.Basic


/-!
# Towers of algebras

In this file we prove basic facts about towers of algebras.

An algebra tower A/S/R is expressed by having instances of `Algebra A S`,
`Algebra R S`, `Algebra R A` and `IsScalarTower R S A`, the latter asserting the
compatibility condition `(r • s) • a = r • (s • a)`.

An important definition is `toAlgHom R S A`, the canonical `R`-algebra homomorphism `S →ₐ[R] A`.

-/

@[expose] public section


open scoped Pointwise

universe u v w u₁ v₁

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁) (M : Type v₁)

namespace Algebra

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
variable [AddCommMonoid M] [Module R M] [Module A M] [Module B M]
variable [IsScalarTower R A M] [IsScalarTower R B M] [SMulCommClass A B M]
variable {A}


/--
Definition of `lsmul` / `lsmul` 的定义

English:
definition lsmul
  signature: : A ->ₐ[R] Module.End B M where
  body: DistribSMul.toLinearMap B M
  map_one' := LinearMap.ext fun _ => one_smul A _
map_mul' a b := LinearMap.ext smul_assoc a b
  map_zero' := LinearMap.ext fun _ => zero_smul A _
  map_add' _a _b := LinearMap.ext fun _ => add_smul _ _ _
commutes' r := LinearMap.ext algebraMap_smul A r

@[simp]

中文:
定义 lsmul
  签名: : A ->ₐ[R] Module.End B M where
  定义体: DistribSMul.toLinearMap B M
  map_one' := LinearMap.ext fun _ => one_smul A _
map_mul' a b := LinearMap.ext smul_assoc a b
  map_zero' := LinearMap.ext fun _ => zero_smul A _
  map_add' _a _b := LinearMap.ext fun _ => add_smul _ _ _
commutes' r := LinearMap.ext algebraMap_smul A r

@[simp]

Depends on / 依赖: DistribSMul, DistribSMul.toLinearMap, toLinearMap
-/
def lsmul : A ->ₐ[R] Module.End B M where
  toFun := DistribSMul.toLinearMap B M
  map_one' := LinearMap.ext fun _ => one_smul A _
map_mul' a b := LinearMap.ext smul_assoc a b
  map_zero' := LinearMap.ext fun _ => zero_smul A _
  map_add' _a _b := LinearMap.ext fun _ => add_smul _ _ _
commutes' r := LinearMap.ext algebraMap_smul A r

@[simp]
/--
theorem `lsmul_coe` / 定理 `lsmul_coe`

English:
theorem lsmul_coe
  given: (a : A)
  statement: (lsmul R B M a : M -> M) = (a • ·)
  proof: rfl

中文:
定理 lsmul_coe
  条件: (a : A)
  结论: (lsmul R B M a : M -> M) = (a • ·)
  证明: rfl
-/
theorem lsmul_coe (a : A) : (lsmul R B M a : M -> M) = (a • ·) := rfl

/--
lemma `lsmul_apply` / 引理 `lsmul_apply`

English:
lemma lsmul_apply
  given: (a : A) (m : M)
  statement: lsmul R B M a m = a • m
  proof: rfl

中文:
引理 lsmul_apply
  条件: (a : A) (m : M)
  结论: lsmul R B M a m = a • m
  证明: rfl
-/
lemma lsmul_apply (a : A) (m : M) : lsmul R B M a m = a • m := rfl

/--
lemma `lsmul_eq_smul_one` / 引理 `lsmul_eq_smul_one`

English:
lemma lsmul_eq_smul_one
  given: (a : A)
  statement: lsmul R R M a = a • 1
  proof: rfl

中文:
引理 lsmul_eq_smul_one
  条件: (a : A)
  结论: lsmul R R M a = a • 1
  证明: rfl
-/
lemma lsmul_eq_smul_one (a : A) : lsmul R R M a = a • 1 := rfl

end Algebra

namespace IsScalarTower

section Module

variable [CommSemiring R] [Semiring A] [Algebra R A]
variable [MulAction A M]
variable {R} {M}

/--
theorem `algebraMap_smul` / 定理 `algebraMap_smul`

English:
theorem algebraMap_smul
  given: [SMul R M] [IsScalarTower R A M] (r : R) (x : M)
  proof: by
  rw [Algebra.algebraMap_eq_smul_one]; rw [smul_assoc]; rw [one_smul]

中文:
定理 algebraMap_smul
  条件: [SMul R M] [IsScalarTower R A M] (r : R) (x : M)
  证明: by
  rw [Algebra.algebraMap_eq_smul_one]; rw [smul_assoc]; rw [one_smul]

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, algebraMap_eq_smul_one, one_smul, smul_assoc
-/
theorem algebraMap_smul [SMul R M] [IsScalarTower R A M] (r : R) (x : M) :
    algebraMap R A r • x = r • x := by
  rw [Algebra.algebraMap_eq_smul_one]; rw [smul_assoc]; rw [one_smul]

variable {A} in
/--
theorem `of_algebraMap_smul` / 定理 `of_algebraMap_smul`

English:
theorem of_algebraMap_smul
  given: [SMul R M] (h : forall (r : R) (x : M), algebraMap R A r • x = r • x)
  proof: by rw [Algebra.smul_def, mul_smul, h]

中文:
定理 of_algebraMap_smul
  条件: [SMul R M] (h : 对任意 (r : R) (x : M), algebraMap R A r • x = r • x)
  证明: by rw [Algebra.smul_def, mul_smul, h]

Depends on / 依赖: Algebra, Algebra.smul_def, mul_smul, smul_def
-/
theorem of_algebraMap_smul [SMul R M] (h : forall (r : R) (x : M), algebraMap R A r • x = r • x) :
    IsScalarTower R A M where
  smul_assoc r a x := by rw [Algebra.smul_def, mul_smul, h]

variable (R M) in
/--
theorem `of_compHom` / 定理 `of_compHom`

English:
theorem of_compHom
  statement: letI
  proof: MulAction.compHom M (algebraMap R A : R ->* A); IsScalarTower R A M :=
  letI := MulAction.compHom M (algebraMap R A : R ->* A); of_algebraMap_smul fun _ _ => rfl

中文:
定理 of_compHom
  结论: letI
  证明: MulAction.compHom M (algebraMap R A : R ->* A); IsScalarTower R A M :=
  letI := MulAction.compHom M (algebraMap R A : R ->* A); of_algebraMap_smul fun _ _ => rfl

Depends on / 依赖: IsScalarTower, MulAction, MulAction.compHom, algebraMap, compHom
-/
theorem of_compHom : letI := MulAction.compHom M (algebraMap R A : R ->* A); IsScalarTower R A M :=
  letI := MulAction.compHom M (algebraMap R A : R ->* A); of_algebraMap_smul fun _ _ => rfl

end Module

section Semiring

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]
variable [Algebra R S] [Algebra S A] [Algebra S B]
variable {R S A}

/--
theorem `of_algebraMap_eq` / 定理 `of_algebraMap_eq`

English:
theorem of_algebraMap_eq
  statement: [Algebra R A]
  proof: ⟨fun x y z => by simp_rw [Algebra.smul_def, map_mul, mul_assoc, h]⟩

中文:
定理 of_algebraMap_eq
  结论: [Algebra R A]
  证明: ⟨fun x y z => by simp_rw [Algebra.smul_def, map_mul, mul_assoc, h]⟩

Depends on / 依赖: Algebra, Algebra.smul_def, map_mul, mul_assoc, simp_rw, smul_def
-/
theorem of_algebraMap_eq [Algebra R A]
    (h : forall x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S A :=
  ⟨fun x y z => by simp_rw [Algebra.smul_def, map_mul, mul_assoc, h]⟩

/--
theorem `of_algebraMap_eq'` / 定理 `of_algebraMap_eq'`

English:
theorem of_algebraMap_eq'
  statement: [Algebra R A]
  proof: of_algebraMap_eq RingHom.ext_iff.1 h

中文:
定理 of_algebraMap_eq'
  结论: [Algebra R A]
  证明: of_algebraMap_eq RingHom.ext_iff.1 h

Depends on / 依赖: RingHom, RingHom.ext_iff, ext_iff, of_algebraMap_eq
-/
theorem of_algebraMap_eq' [Algebra R A]
    (h : algebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A :=
of_algebraMap_eq RingHom.ext_iff.1 h

variable (R S A)
variable [Algebra R A] [Algebra R B]
variable [IsScalarTower R S A] [IsScalarTower R S B]

/--
theorem `algebraMap_eq` / 定理 `algebraMap_eq`

English:
theorem algebraMap_eq
  statement: algebraMap R A = (algebraMap S A).comp (algebraMap R S)
  proof: RingHom.ext fun x => by
    simp_rw [RingHom.comp_apply, Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul]

中文:
定理 algebraMap_eq
  结论: algebraMap R A = (algebraMap S A).comp (algebraMap R S)
  证明: RingHom.ext fun x => by
    simp_rw [RingHom.comp_apply, Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul]

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, RingHom, RingHom.comp_apply, RingHom.ext, algebraMap_eq_smul_one, comp_apply, one_smul, simp_rw, smul_assoc
-/
theorem algebraMap_eq : algebraMap R A = (algebraMap S A).comp (algebraMap R S) :=
  RingHom.ext fun x => by
    simp_rw [RingHom.comp_apply, Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul]

/--
theorem `algebraMap_apply` / 定理 `algebraMap_apply`

English:
theorem algebraMap_apply
  given: (x : R)
  statement: algebraMap R A x = algebraMap S A (algebraMap R S x)
  proof: by
  rw [algebraMap_eq R S A]; rw [RingHom.comp_apply]

@[ext]

中文:
定理 algebraMap_apply
  条件: (x : R)
  结论: algebraMap R A x = algebraMap S A (algebraMap R S x)
  证明: by
  rw [algebraMap_eq R S A]; rw [RingHom.comp_apply]

@[ext]

Depends on / 依赖: RingHom, RingHom.comp_apply, algebraMap_eq, comp_apply
-/
theorem algebraMap_apply (x : R) : algebraMap R A x = algebraMap S A (algebraMap R S x) := by
  rw [algebraMap_eq R S A]; rw [RingHom.comp_apply]

@[ext]
/--
theorem `Algebra.ext` / 定理 `Algebra.ext`

English:
theorem Algebra.ext
  statement: {S : Type u} {A : Type v} [CommSemiring S] [Semiring A] (h1 h2 : Algebra S A)
  proof: Algebra.algebra_ext _ _ fun r => by
    simpa only [@Algebra.smul_def _ _ _ _ h1, @Algebra.smul_def _ _ _ _ h2, mul_one] using h r 1

中文:
定理 Algebra.ext
  结论: {S : 类型u} {A : 类型v} [CommSemiring S] [Semiring A] (h1 h2 : Algebra S A)
  证明: Algebra.algebra_ext _ _ fun r => by
    simpa only [@Algebra.smul_def _ _ _ _ h1, @Algebra.smul_def _ _ _ _ h2, mul_one] using h r 1
-/
theorem Algebra.ext {S : Type u} {A : Type v} [CommSemiring S] [Semiring A] (h1 h2 : Algebra S A)
    (h : forall (r : S) (x : A), (by have I := h1; exact r • x) = r • x) : h1 = h2 :=
  Algebra.algebra_ext _ _ fun r => by
    simpa only [@Algebra.smul_def _ _ _ _ h1, @Algebra.smul_def _ _ _ _ h2, mul_one] using h r 1

variable {R S A B}

@[simp]
/--
theorem `_root_.AlgHom.map_algebraMap` / 定理 `_root_.AlgHom.map_algebraMap`

English:
theorem _root_.AlgHom.map_algebraMap
  given: (f : A ->ₐ[S] B) (r : R)
  proof: by
  rw [algebraMap_apply R S A r]; rw [f.commutes]; rw [← algebraMap_apply R S B]

中文:
定理 _root_.AlgHom.map_algebraMap
  条件: (f : A ->ₐ[S] B) (r : R)
  证明: by
  rw [algebraMap_apply R S A r]; rw [f.commutes]; rw [← algebraMap_apply R S B]

Depends on / 依赖: algebraMap_apply, commutes, f.commutes
-/
theorem _root_.AlgHom.map_algebraMap (f : A ->ₐ[S] B) (r : R) :
    f (algebraMap R A r) = algebraMap R B r := by
  rw [algebraMap_apply R S A r]; rw [f.commutes]; rw [← algebraMap_apply R S B]

variable (R)

@[simp]
/--
theorem `_root_.AlgHom.comp_algebraMap_of_tower` / 定理 `_root_.AlgHom.comp_algebraMap_of_tower`

English:
theorem _root_.AlgHom.comp_algebraMap_of_tower
  given: (f : A ->ₐ[S] B)
  proof: RingHom.ext (AlgHom.map_algebraMap f)

中文:
定理 _root_.AlgHom.comp_algebraMap_of_tower
  条件: (f : A ->ₐ[S] B)
  证明: RingHom.ext (AlgHom.map_algebraMap f)

Depends on / 依赖: AlgHom, AlgHom.map_algebraMap, RingHom, RingHom.ext, map_algebraMap
-/
theorem _root_.AlgHom.comp_algebraMap_of_tower (f : A ->ₐ[S] B) :
    (f : A ->+* B).comp (algebraMap R A) = algebraMap R B :=
  RingHom.ext (AlgHom.map_algebraMap f)

-- conflicts with IsScalarTower.Subalgebra
instance (priority := 999) subsemiring (U : Subsemiring S) : IsScalarTower U S A :=
  of_algebraMap_eq fun _x => rfl

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/12096): removed @[nolint instance_priority], linter not ported yet
instance (priority := 999) of_algHom {R A B : Type*} [CommSemiring R] [CommSemiring A]
    [CommSemiring B] [Algebra R A] [Algebra R B] (f : A ->ₐ[R] B) :
    @IsScalarTower R A B _ f.toRingHom.toAlgebra.toSMul _ :=
  letI := (f : A ->+* B).toAlgebra
  of_algebraMap_eq fun x => (f.commutes x).symm

end Semiring

end IsScalarTower

section Homs

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]
variable [Algebra R S] [Algebra S A] [Algebra S B]
variable [Algebra R A] [Algebra R B]
variable [IsScalarTower R S A] [IsScalarTower R S B]
variable {A S B}

open IsScalarTower

namespace AlgHom

/--
Definition of `restrictScalars` / `restrictScalars` 的定义

English:
definition restrictScalars
  signature: (f : A ->ₐ[S] B)
  body: { (f : A ->+* B) with
    commutes' := fun r => by
      rw [algebraMap_apply R S A]; rw [algebraMap_apply R S B]
      exact f.commutes (algebraMap R S r) }

中文:
定义 restrictScalars
  签名: (f : A ->ₐ[S] B)
  定义体: { (f : A ->+* B) with
    commutes' := fun r => by
      rw [algebraMap_apply R S A]; rw [algebraMap_apply R S B]
      exact f.commutes (algebraMap R S r) }

Depends on / 依赖: algebraMap, algebraMap_apply, commutes, f.commutes
-/
def restrictScalars (f : A ->ₐ[S] B) : A ->ₐ[R] B :=
  { (f : A ->+* B) with
    commutes' := fun r => by
      rw [algebraMap_apply R S A]; rw [algebraMap_apply R S B]
      exact f.commutes (algebraMap R S r) }

/--
theorem `restrictScalars_apply` / 定理 `restrictScalars_apply`

English:
theorem restrictScalars_apply
  given: (f : A ->ₐ[S] B) (x : A)
  statement: f.restrictScalars R x = f x
  proof: rfl

中文:
定理 restrictScalars_apply
  条件: (f : A ->ₐ[S] B) (x : A)
  结论: f.restrictScalars R x = f x
  证明: rfl
-/
theorem restrictScalars_apply (f : A ->ₐ[S] B) (x : A) : f.restrictScalars R x = f x := rfl

/--
lemma `toLinearMap_restrictScalars` / 引理 `toLinearMap_restrictScalars`

English:
lemma toLinearMap_restrictScalars
  given: (f : A ->ₐ[S] B)
  proof: rfl

@[simp]

中文:
引理 toLinearMap_restrictScalars
  条件: (f : A ->ₐ[S] B)
  证明: rfl

@[simp]
-/
@[simp] lemma toLinearMap_restrictScalars (f : A ->ₐ[S] B) :
    (f.restrictScalars R).toLinearMap = f.toLinearMap.restrictScalars R := rfl

@[simp]
/--
theorem `coe_restrictScalars` / 定理 `coe_restrictScalars`

English:
theorem coe_restrictScalars
  given: (f : A ->ₐ[S] B)
  statement: (f.restrictScalars R : A ->+* B) = f
  proof: rfl

@[simp]

中文:
定理 coe_restrictScalars
  条件: (f : A ->ₐ[S] B)
  结论: (f.restrictScalars R : A ->+* B) = f
  证明: rfl

@[simp]
-/
theorem coe_restrictScalars (f : A ->ₐ[S] B) : (f.restrictScalars R : A ->+* B) = f := rfl

@[simp]
/--
theorem `coe_restrictScalars'` / 定理 `coe_restrictScalars'`

English:
theorem coe_restrictScalars'
  given: (f : A ->ₐ[S] B)
  statement: (restrictScalars R f : A -> B) = f
  proof: rfl

中文:
定理 coe_restrictScalars'
  条件: (f : A ->ₐ[S] B)
  结论: (restrictScalars R f : A -> B) = f
  证明: rfl
-/
theorem coe_restrictScalars' (f : A ->ₐ[S] B) : (restrictScalars R f : A -> B) = f := rfl

/--
theorem `restrictScalars_injective` / 定理 `restrictScalars_injective`

English:
theorem restrictScalars_injective
  proof: fun _ _ h =>
  AlgHom.ext (AlgHom.congr_fun h :)

中文:
定理 restrictScalars_injective
  证明: fun _ _ h =>
  AlgHom.ext (AlgHom.congr_fun h :)
-/
theorem restrictScalars_injective :
    Function.Injective (restrictScalars R : (A ->ₐ[S] B) -> A ->ₐ[R] B) := fun _ _ h =>
  AlgHom.ext (AlgHom.congr_fun h :)

section

variable {R}

/-- Any `f : A →ₐ[R] B` is also an `S`-algebra homomorphism if the `R`-algebra structure on
`A` and `B` factors via a surjective ring homomorphism `R →+* S`. -/
@[simps! apply symm_apply]
/--
Definition of `extendScalarsOfSurjective` / `extendScalarsOfSurjective` 的定义

English:
definition extendScalarsOfSurjective
  signature: (h : Function.Surjective (algebraMap R S))
  body: { f with commutes' := by simp [h.forall, ← IsScalarTower.algebraMap_apply] }
  invFun := restrictScalars R

@[simp]

中文:
定义 extendScalarsOfSurjective
  签名: (h : Function.Surjective (algebraMap R S))
  定义体: { f with commutes' := by simp [h.forall, ← IsScalarTower.algebraMap_apply] }
  invFun := restrictScalars R

@[simp]

Depends on / 依赖: IsScalarTower, IsScalarTower.algebraMap_apply, algebraMap_apply, commutes, h.forall
-/
def extendScalarsOfSurjective (h : Function.Surjective (algebraMap R S)) :
    (A ->ₐ[R] B) ≃ (A ->ₐ[S] B) where
  toFun f := { f with commutes' := by simp [h.forall, ← IsScalarTower.algebraMap_apply] }
  invFun := restrictScalars R

@[simp]
/--
lemma `restrictScalars_extendScalarsOfSurjective` / 引理 `restrictScalars_extendScalarsOfSurjective`

English:
lemma restrictScalars_extendScalarsOfSurjective
  statement: (h : Function.Surjective (algebraMap R S))
  proof: rfl

中文:
引理 restrictScalars_extendScalarsOfSurjective
  结论: (h : Function.Surjective (algebraMap R S))
  证明: rfl
-/
lemma restrictScalars_extendScalarsOfSurjective (h : Function.Surjective (algebraMap R S))
    (f : A ->ₐ[R] B) :
    (f.extendScalarsOfSurjective h).restrictScalars R = f := rfl

/-- Any `f : A →ₐ[R] B` is also an `S`-algebra homomorphism if the `R`-algebra structure on
`A` and `B` factors via a surjective ring homomorphism `R →+* S`. -/
@[simps! apply symm_apply]
/--
Definition of `extendScalarsHomOfSurjective` / `extendScalarsHomOfSurjective` 的定义

English:
definition extendScalarsHomOfSurjective
  signature: (h : Function.Surjective (algebraMap R S))
  body: extendScalarsOfSurjective h
  map_mul' _ _ := rfl

中文:
定义 extendScalarsHomOfSurjective
  签名: (h : Function.Surjective (algebraMap R S))
  定义体: extendScalarsOfSurjective h
  map_mul' _ _ := rfl

Depends on / 依赖: extendScalarsOfSurjective
-/
def extendScalarsHomOfSurjective (h : Function.Surjective (algebraMap R S)) :
    (A ->ₐ[R] A) ≃* (A ->ₐ[S] A) where
  __ := extendScalarsOfSurjective h
  map_mul' _ _ := rfl

end

end AlgHom

namespace AlgEquiv

/--
Definition of `restrictScalars` / `restrictScalars` 的定义

English:
definition restrictScalars
  signature: (f : A ≃ₐ[S] B)
  body: { (f : A ≃+* B) with
    commutes' := fun r => by
      rw [algebraMap_apply R S A]; rw [algebraMap_apply R S B]
      exact f.commutes (algebraMap R S r) }

中文:
定义 restrictScalars
  签名: (f : A ≃ₐ[S] B)
  定义体: { (f : A ≃+* B) with
    commutes' := fun r => by
      rw [algebraMap_apply R S A]; rw [algebraMap_apply R S B]
      exact f.commutes (algebraMap R S r) }

Depends on / 依赖: algebraMap, algebraMap_apply, commutes, f.commutes
-/
def restrictScalars (f : A ≃ₐ[S] B) : A ≃ₐ[R] B :=
  { (f : A ≃+* B) with
    commutes' := fun r => by
      rw [algebraMap_apply R S A]; rw [algebraMap_apply R S B]
      exact f.commutes (algebraMap R S r) }

/--
theorem `restrictScalars_apply` / 定理 `restrictScalars_apply`

English:
theorem restrictScalars_apply
  given: (f : A ≃ₐ[S] B) (x : A)
  statement: f.restrictScalars R x = f x
  proof: rfl

中文:
定理 restrictScalars_apply
  条件: (f : A ≃ₐ[S] B) (x : A)
  结论: f.restrictScalars R x = f x
  证明: rfl
-/
theorem restrictScalars_apply (f : A ≃ₐ[S] B) (x : A) : f.restrictScalars R x = f x := rfl

/--
lemma `toAlgHom_restrictScalars` / 引理 `toAlgHom_restrictScalars`

English:
lemma toAlgHom_restrictScalars
  given: (f : A ≃ₐ[S] B)
  proof: rfl

中文:
引理 toAlgHom_restrictScalars
  条件: (f : A ≃ₐ[S] B)
  证明: rfl
-/
@[simp] lemma toAlgHom_restrictScalars (f : A ≃ₐ[S] B) :
    (f.restrictScalars R).toAlgHom = f.toAlgHom.restrictScalars R := rfl

/--
lemma `toLinearEquiv_restrictScalars` / 引理 `toLinearEquiv_restrictScalars`

English:
lemma toLinearEquiv_restrictScalars
  given: (f : A ≃ₐ[S] B)
  proof: rfl

@[simp]

中文:
引理 toLinearEquiv_restrictScalars
  条件: (f : A ≃ₐ[S] B)
  证明: rfl

@[simp]
-/
@[simp] lemma toLinearEquiv_restrictScalars (f : A ≃ₐ[S] B) :
    (f.restrictScalars R).toLinearEquiv = f.toLinearEquiv.restrictScalars R := rfl

@[simp]
/--
theorem `toRingEquiv_restrictScalars` / 定理 `toRingEquiv_restrictScalars`

English:
theorem toRingEquiv_restrictScalars
  given: (f : A ≃ₐ[S] B)
  statement: (f.restrictScalars R : A ≃+* B) = f
  proof: rfl

@[simp]

中文:
定理 toRingEquiv_restrictScalars
  条件: (f : A ≃ₐ[S] B)
  结论: (f.restrictScalars R : A ≃+* B) = f
  证明: rfl

@[simp]
-/
theorem toRingEquiv_restrictScalars (f : A ≃ₐ[S] B) : (f.restrictScalars R : A ≃+* B) = f := rfl

@[simp]
/--
theorem `coe_restrictScalars` / 定理 `coe_restrictScalars`

English:
theorem coe_restrictScalars
  given: (f : A ≃ₐ[S] B)
  statement: (restrictScalars R f : A -> B) = f
  proof: rfl

@[deprecated (since := "2026-07-06")] alias coe_restrictScalars' := coe_restrictScalars

中文:
定理 coe_restrictScalars
  条件: (f : A ≃ₐ[S] B)
  结论: (restrictScalars R f : A -> B) = f
  证明: rfl

@[deprecated (since := "2026-07-06")] alias coe_restrictScalars' := coe_restrictScalars
-/
theorem coe_restrictScalars (f : A ≃ₐ[S] B) : (restrictScalars R f : A -> B) = f := rfl

@[deprecated (since := "2026-07-06")] alias coe_restrictScalars' := coe_restrictScalars

/--
theorem `restrictScalars_injective` / 定理 `restrictScalars_injective`

English:
theorem restrictScalars_injective
  proof: fun _ _ h =>
  AlgEquiv.ext (AlgEquiv.congr_fun h :)

@[simp]

中文:
定理 restrictScalars_injective
  证明: fun _ _ h =>
  AlgEquiv.ext (AlgEquiv.congr_fun h :)

@[simp]
-/
theorem restrictScalars_injective :
    Function.Injective (restrictScalars R : (A ≃ₐ[S] B) -> A ≃ₐ[R] B) := fun _ _ h =>
  AlgEquiv.ext (AlgEquiv.congr_fun h :)

@[simp]
/--
lemma `symm_restrictScalars` / 引理 `symm_restrictScalars`

English:
lemma symm_restrictScalars
  given: (f : A ≃ₐ[S] B)
  proof: rfl

@[deprecated "Use `symm_restrictScalars` instead." (since := "2026-07-06")]

中文:
引理 symm_restrictScalars
  条件: (f : A ≃ₐ[S] B)
  证明: rfl

@[deprecated "Use `symm_restrictScalars` instead." (since := "2026-07-06")]
-/
lemma symm_restrictScalars (f : A ≃ₐ[S] B) :
    (f.restrictScalars R).symm = f.symm.restrictScalars R :=
  rfl

@[deprecated "Use `symm_restrictScalars` instead." (since := "2026-07-06")]
/--
lemma `restrictScalars_symm_apply` / 引理 `restrictScalars_symm_apply`

English:
lemma restrictScalars_symm_apply
  given: (f : A ≃ₐ[S] B) (x : B)
  proof: by
  simp

@[deprecated "Use `symm_restrictScalars` instead." (since := "2026-07-06")]

中文:
引理 restrictScalars_symm_apply
  条件: (f : A ≃ₐ[S] B) (x : B)
  证明: by
  simp

@[deprecated "Use `symm_restrictScalars` instead." (since := "2026-07-06")]
-/
lemma restrictScalars_symm_apply (f : A ≃ₐ[S] B) (x : B) :
    (f.restrictScalars R).symm x = f.symm x := by
  simp

@[deprecated "Use `symm_restrictScalars` instead." (since := "2026-07-06")]
/--
lemma `coe_restrictScalars_symm` / 引理 `coe_restrictScalars_symm`

English:
lemma coe_restrictScalars_symm
  given: (f : A ≃ₐ[S] B)
  proof: by
  simp

@[deprecated "Use `symm_restrictScalars` instead." (since := "2026-07-06")]

中文:
引理 coe_restrictScalars_symm
  条件: (f : A ≃ₐ[S] B)
  证明: by
  simp

@[deprecated "Use `symm_restrictScalars` instead." (since := "2026-07-06")]
-/
lemma coe_restrictScalars_symm (f : A ≃ₐ[S] B) :
    ((f.restrictScalars R).symm : B ≃+* A) = f.symm := by
  simp

@[deprecated "Use `symm_restrictScalars` instead." (since := "2026-07-06")]
/--
lemma `coe_restrictScalars_symm'` / 引理 `coe_restrictScalars_symm'`

English:
lemma coe_restrictScalars_symm'
  given: (f : A ≃ₐ[S] B)
  proof: by
  simp

中文:
引理 coe_restrictScalars_symm'
  条件: (f : A ≃ₐ[S] B)
  证明: by
  simp
-/
lemma coe_restrictScalars_symm' (f : A ≃ₐ[S] B) :
    ((restrictScalars R f).symm : B -> A) = f.symm := by
  simp

/--
Definition of `restrictScalarsHom` / `restrictScalarsHom` 的定义

English:
definition restrictScalarsHom
  signature: : (A ≃ₐ[S] A) ->* (A ≃ₐ[R] A)
  body: MulSemiringAction.toAlgAut (A ≃ₐ[S] A) R A

@[simp]

中文:
定义 restrictScalarsHom
  签名: : (A ≃ₐ[S] A) ->* (A ≃ₐ[R] A)
  定义体: MulSemiringAction.toAlgAut (A ≃ₐ[S] A) R A

@[simp]

Depends on / 依赖: MulSemiringAction, MulSemiringAction.toAlgAut, toAlgAut
-/
def restrictScalarsHom : (A ≃ₐ[S] A) ->* (A ≃ₐ[R] A) :=
  MulSemiringAction.toAlgAut (A ≃ₐ[S] A) R A

@[simp]
/--
theorem `restrictScalarsHom_apply` / 定理 `restrictScalarsHom_apply`

English:
theorem restrictScalarsHom_apply
  given: (f : A ≃ₐ[S] A)
  statement: f.restrictScalarsHom R = f.restrictScalars R
  proof: rfl

中文:
定理 restrictScalarsHom_apply
  条件: (f : A ≃ₐ[S] A)
  结论: f.restrictScalarsHom R = f.restrictScalars R
  证明: rfl
-/
theorem restrictScalarsHom_apply (f : A ≃ₐ[S] A) : f.restrictScalarsHom R = f.restrictScalars R :=
  rfl

/--
theorem `restrictScalarsHom_injective` / 定理 `restrictScalarsHom_injective`

English:
theorem restrictScalarsHom_injective
  proof: restrictScalars_injective R

中文:
定理 restrictScalarsHom_injective
  证明: restrictScalars_injective R

Depends on / 依赖: restrictScalars_injective
-/
theorem restrictScalarsHom_injective :
    Function.Injective (restrictScalarsHom R : (A ≃ₐ[S] A) ->* (A ≃ₐ[R] A)) :=
  restrictScalars_injective R

section

variable {R}

/-- Any `f : A ≃ₐ[R] B` is also an `S`-algebra isomorphism if the `R`-algebra structure on
`A` and `B` factors via a surjective ring homomorphism `R →+* S`. -/
@[simps! apply symm_apply]
/--
Definition of `extendScalarsOfSurjective` / `extendScalarsOfSurjective` 的定义

English:
definition extendScalarsOfSurjective
  signature: (h : Function.Surjective (algebraMap R S))
  body: { f with commutes' := (f.toAlgHom.extendScalarsOfSurjective h).commutes' }
  invFun := AlgEquiv.restrictScalars R

中文:
定义 extendScalarsOfSurjective
  签名: (h : Function.Surjective (algebraMap R S))
  定义体: { f with commutes' := (f.toAlgHom.extendScalarsOfSurjective h).commutes' }
  invFun := AlgEquiv.restrictScalars R

Depends on / 依赖: commutes, extendScalarsOfSurjective, f.toAlgHom.extendScalarsOfSurjective, toAlgHom
-/
def extendScalarsOfSurjective (h : Function.Surjective (algebraMap R S)) :
    (A ≃ₐ[R] B) ≃ A ≃ₐ[S] B where
  toFun f := { f with commutes' := (f.toAlgHom.extendScalarsOfSurjective h).commutes' }
  invFun := AlgEquiv.restrictScalars R

/--
lemma `coe_extendScalarsOfSurjective` / 引理 `coe_extendScalarsOfSurjective`

English:
lemma coe_extendScalarsOfSurjective
  statement: (h : Function.Surjective (algebraMap R S))
  proof: rfl

@[simp]

中文:
引理 coe_extendScalarsOfSurjective
  结论: (h : Function.Surjective (algebraMap R S))
  证明: rfl

@[simp]
-/
@[simp] lemma coe_extendScalarsOfSurjective (h : Function.Surjective (algebraMap R S))
    (f : A ≃ₐ[R] B) : ⇑(extendScalarsOfSurjective h f) = f := rfl

@[simp]
/--
lemma `restrictScalars_extendScalarsOfSurjective` / 引理 `restrictScalars_extendScalarsOfSurjective`

English:
lemma restrictScalars_extendScalarsOfSurjective
  statement: (h : Function.Surjective (algebraMap R S))
  proof: rfl

@[simp]

中文:
引理 restrictScalars_extendScalarsOfSurjective
  结论: (h : Function.Surjective (algebraMap R S))
  证明: rfl

@[simp]
-/
lemma restrictScalars_extendScalarsOfSurjective (h : Function.Surjective (algebraMap R S))
    (f : A ≃ₐ[R] B) :
    (f.extendScalarsOfSurjective h).restrictScalars R = f := rfl

@[simp]
/--
lemma `extendScalarsOfSurjective_symm` / 引理 `extendScalarsOfSurjective_symm`

English:
lemma extendScalarsOfSurjective_symm
  statement: (h : Function.Surjective (algebraMap R S))
  proof: rfl

中文:
引理 extendScalarsOfSurjective_symm
  结论: (h : Function.Surjective (algebraMap R S))
  证明: rfl
-/
lemma extendScalarsOfSurjective_symm (h : Function.Surjective (algebraMap R S))
    (f : A ≃ₐ[R] B) :
    (f.extendScalarsOfSurjective h).symm = f.symm.extendScalarsOfSurjective h := rfl

/-- Any `f : A ≃ₐ[R] B` is also an `S`-algebra isomorphism if the `R`-algebra structure on
`A` and `B` factors via a surjective ring homomorphism `R →+* S`. -/
@[simps! apply symm_apply]
/--
Definition of `extendScalarsHomOfSurjective` / `extendScalarsHomOfSurjective` 的定义

English:
definition extendScalarsHomOfSurjective
  signature: (h : Function.Surjective ⇑(algebraMap R S))
  body: extendScalarsOfSurjective h
  map_mul' _ _ := rfl

@[simp]

中文:
定义 extendScalarsHomOfSurjective
  签名: (h : Function.Surjective ⇑(algebraMap R S))
  定义体: extendScalarsOfSurjective h
  map_mul' _ _ := rfl

@[simp]

Depends on / 依赖: extendScalarsOfSurjective
-/
def extendScalarsHomOfSurjective (h : Function.Surjective ⇑(algebraMap R S)) :
    (A ≃ₐ[R] A) ≃* (A ≃ₐ[S] A) where
  __ := extendScalarsOfSurjective h
  map_mul' _ _ := rfl

@[simp]
/--
lemma `toMonoidHom_symm_extendScalarsHomOfSurjective` / 引理 `toMonoidHom_symm_extendScalarsHomOfSurjective`

English:
lemma toMonoidHom_symm_extendScalarsHomOfSurjective
  given: (h : Function.Surjective (algebraMap R S))
  proof: rfl

中文:
引理 toMonoidHom_symm_extendScalarsHomOfSurjective
  条件: (h : Function.Surjective (algebraMap R S))
  证明: rfl

Depends on / 依赖: restrictScalarsHom
-/
lemma toMonoidHom_symm_extendScalarsHomOfSurjective (h : Function.Surjective (algebraMap R S)) :
    (extendScalarsHomOfSurjective h (A := A).symm : (A ≃ₐ[S] A) ->* _) = restrictScalarsHom R :=
  rfl

end

end AlgEquiv

end Homs

namespace Submodule

variable {M}
variable [CommSemiring R] [Semiring A] [Algebra R A] [AddCommMonoid M]
variable [Module R M] [Module A M] [IsScalarTower R A M]

/--
theorem `restrictScalars_span` / 定理 `restrictScalars_span`

English:
theorem restrictScalars_span
  given: (hsur : Function.Surjective (algebraMap R A)) (X : Set M)
  proof: by
  refine ((span_le_restrictScalars R A X).antisymm fun m hm => ?_).symm
  refine span_induction subset_span (zero_mem _) (fun _ _ _ _ => add_mem) (fun a m _ hm => ?_) hm
  obtain ⟨r, rfl⟩ := hsur a
  simpa [algebraMap_smul] using smul_mem _ r hm

中文:
定理 restrictScalars_span
  条件: (hsur : Function.Surjective (algebraMap R A)) (X : Set M)
  证明: by
  refine ((span_le_restrictScalars R A X).antisymm fun m hm => ?_).symm
  refine span_induction subset_span (zero_mem _) (fun _ _ _ _ => add_mem) (fun a m _ hm => ?_) hm
  obtain ⟨r, rfl⟩ := hsur a
  simpa [algebraMap_smul] using smul_mem _ r hm

Depends on / 依赖: add_mem, algebraMap_smul, antisymm, smul_mem, span_induction, span_le_restrictScalars, subset_span, zero_mem
-/
theorem restrictScalars_span (hsur : Function.Surjective (algebraMap R A)) (X : Set M) :
    restrictScalars R (span A X) = span R X := by
  refine ((span_le_restrictScalars R A X).antisymm fun m hm => ?_).symm
  refine span_induction subset_span (zero_mem _) (fun _ _ _ _ => add_mem) (fun a m _ hm => ?_) hm
  obtain ⟨r, rfl⟩ := hsur a
  simpa [algebraMap_smul] using smul_mem _ r hm

/--
theorem `coe_span_eq_span_of_surjective` / 定理 `coe_span_eq_span_of_surjective`

English:
theorem coe_span_eq_span_of_surjective
  given: (h : Function.Surjective (algebraMap R A)) (s : Set M)
  proof: congr_arg ((↑) : Submodule R M -> Set M) (Submodule.restrictScalars_span R A h s)

中文:
定理 coe_span_eq_span_of_surjective
  条件: (h : Function.Surjective (algebraMap R A)) (s : Set M)
  证明: congr_arg ((↑) : Submodule R M -> Set M) (Submodule.restrictScalars_span R A h s)

Depends on / 依赖: Submodule, Submodule.restrictScalars_span, congr_arg, restrictScalars_span
-/
theorem coe_span_eq_span_of_surjective (h : Function.Surjective (algebraMap R A)) (s : Set M) :
    (Submodule.span A s : Set M) = Submodule.span R s :=
  congr_arg ((↑) : Submodule R M -> Set M) (Submodule.restrictScalars_span R A h s)

/--
Given a commutative ring `R`, an `R`-algebra `S` and an `R`-module `M` with a scalar tower
`IsScalarTower R S M`, if the algebra map from `R` to `S` is surjective, then this induces an order
isomorphism `Submodule S M ≃o Submodule R M`.
-/
@[simps apply symm_apply]
/--
Definition of `orderIsoOfAlgebraMapSurjective` / `orderIsoOfAlgebraMapSurjective` 的定义

English:
definition orderIsoOfAlgebraMapSurjective
  body: N.restrictScalars R
  invFun N := ⟨N.toAddSubmonoid, by simpa [h.forall] using N.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := .rfl

中文:
定义 orderIsoOfAlgebraMapSurjective
  定义体: N.restrictScalars R
  invFun N := ⟨N.toAddSubmonoid, by simpa [h.forall] using N.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := .rfl

Depends on / 依赖: N.restrictScalars, restrictScalars
-/
def orderIsoOfAlgebraMapSurjective
    {R S M : Type*} [CommRing R] [Ring S] [AddCommGroup M]
    [Algebra R S] [Module R M] [Module S M] [IsScalarTower R S M]
    (h : Function.Surjective (algebraMap R S)) : Submodule S M ≃o Submodule R M where
  toFun N := N.restrictScalars R
  invFun N := ⟨N.toAddSubmonoid, by simpa [h.forall] using N.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := .rfl

end Submodule

section Semiring

variable {R S A}

namespace Submodule

section Module

variable [Semiring R] [Semiring S] [AddCommMonoid A]
variable [Module R S] [Module S A] [Module R A] [IsScalarTower R S A]

open IsScalarTower

/--
theorem `smul_mem_span_smul_of_mem` / 定理 `smul_mem_span_smul_of_mem`

English:
theorem smul_mem_span_smul_of_mem
  statement: {s : Set S} {t : Set A} {k : S} (hks : k in span R s) {x : A}
  proof: span_induction (fun _ hc => subset_span <| Set.smul_mem_smul hc hx)
    (by rw [zero_smul]; exact zero_mem _)
    (fun c₁ c₂ _ _ ih₁ ih₂ => by rw [add_smul]; exact add_mem ih₁ ih₂)
    (fun b c _ hc => by rw [IsScalarTower.smul_assoc]; exact smul_mem _ _ hc) hks

中文:
定理 smul_mem_span_smul_of_mem
  结论: {s : Set S} {t : Set A} {k : S} (hks : k in span R s) {x : A}
  证明: span_induction (fun _ hc => subset_span <| Set.smul_mem_smul hc hx)
    (by rw [zero_smul]; exact zero_mem _)
    (fun c₁ c₂ _ _ ih₁ ih₂ => by rw [add_smul]; exact add_mem ih₁ ih₂)
    (fun b c _ hc => by rw [IsScalarTower.smul_assoc]; exact smul_mem _ _ hc) hks

Depends on / 依赖: IsScalarTower, IsScalarTower.smul_assoc, Set.smul_mem_smul, add_mem, add_smul, smul_assoc, smul_mem, smul_mem_smul, span_induction, subset_span, zero_mem, zero_smul
-/
theorem smul_mem_span_smul_of_mem {s : Set S} {t : Set A} {k : S} (hks : k in span R s) {x : A}
    (hx : x in t) : k • x in span R (s • t) :=
  span_induction (fun _ hc => subset_span <| Set.smul_mem_smul hc hx)
    (by rw [zero_smul]; exact zero_mem _)
    (fun c₁ c₂ _ _ ih₁ ih₂ => by rw [add_smul]; exact add_mem ih₁ ih₂)
    (fun b c _ hc => by rw [IsScalarTower.smul_assoc]; exact smul_mem _ _ hc) hks

/--
theorem `span_smul_of_span_eq_top` / 定理 `span_smul_of_span_eq_top`

English:
theorem span_smul_of_span_eq_top
  given: {s : Set S} (hs : span R s = ⊤) (t : Set A)
  proof: le_antisymm
    (span_le.2 fun _x ⟨p, _hps, _q, hqt, hpqx⟩ => hpqx ▸ (span S t).smul_mem p (subset_span hqt))
    fun _ hp => closure_induction (hx := hp) (zero_mem _) (fun _ _ _ _ => add_mem) fun s0 y hy => by
      refine span_induction (fun x hx => subset_span <| by exact ⟨x, hx, y, hy, rfl⟩) ?_ 

中文:
定理 span_smul_of_span_eq_top
  条件: {s : Set S} (hs : span R s = ⊤) (t : Set A)
  证明: le_antisymm
    (span_le.2 fun _x ⟨p, _hps, _q, hqt, hpqx⟩ => hpqx ▸ (span S t).smul_mem p (subset_span hqt))
    fun _ hp => closure_induction (hx := hp) (zero_mem _) (fun _ _ _ _ => add_mem) fun s0 y hy => by
      refine span_induction (fun x hx => subset_span <| by exact ⟨x, hx, y, hy, rfl⟩) ?_ 

Depends on / 依赖: IsScalarTower, IsScalarTower.smul_assoc, _hps, add_mem, add_smul, closure_induction, le_antisymm, mem_top, smul_assoc, smul_mem, span_induction, span_le, subset_span, zero_mem, zero_smul
-/
theorem span_smul_of_span_eq_top {s : Set S} (hs : span R s = ⊤) (t : Set A) :
    span R (s • t) = (span S t).restrictScalars R :=
  le_antisymm
    (span_le.2 fun _x ⟨p, _hps, _q, hqt, hpqx⟩ => hpqx ▸ (span S t).smul_mem p (subset_span hqt))
    fun _ hp => closure_induction (hx := hp) (zero_mem _) (fun _ _ _ _ => add_mem) fun s0 y hy => by
      refine span_induction (fun x hx => subset_span <| by exact ⟨x, hx, y, hy, rfl⟩) ?_ ?_ ?_
        (hs ▸ mem_top : s0 in span R s)
      · rw [zero_smul]; apply zero_mem
      · intro _ _ _ _; rw [add_smul]; apply add_mem
      · intro r s0 _ hy; rw [IsScalarTower.smul_assoc]; exact smul_mem _ r hy

-- The following two lemmas were originally used to prove `span_smul_of_span_eq_top`
-- but are now not needed.
/--
theorem `smul_mem_span_smul'` / 定理 `smul_mem_span_smul'`

English:
theorem smul_mem_span_smul'
  statement: {s : Set S} (hs : span R s = ⊤) {t : Set A} {k : S} {x : A}
  proof: by
  rw [span_smul_of_span_eq_top hs] at hx ⊢; exact (span S t).smul_mem k hx

中文:
定理 smul_mem_span_smul'
  结论: {s : Set S} (hs : span R s = ⊤) {t : Set A} {k : S} {x : A}
  证明: by
  rw [span_smul_of_span_eq_top hs] at hx ⊢; exact (span S t).smul_mem k hx

Depends on / 依赖: smul_mem, span_smul_of_span_eq_top
-/
theorem smul_mem_span_smul' {s : Set S} (hs : span R s = ⊤) {t : Set A} {k : S} {x : A}
    (hx : x in span R (s • t)) : k • x in span R (s • t) := by
  rw [span_smul_of_span_eq_top hs] at hx ⊢; exact (span S t).smul_mem k hx

/--
theorem `smul_mem_span_smul` / 定理 `smul_mem_span_smul`

English:
theorem smul_mem_span_smul
  statement: {s : Set S} (hs : span R s = ⊤) {t : Set A} {k : S} {x : A}
  proof: by
  rw [span_smul_of_span_eq_top hs]
  exact (span S t).smul_mem k (span_le_restrictScalars R S t hx)

中文:
定理 smul_mem_span_smul
  结论: {s : Set S} (hs : span R s = ⊤) {t : Set A} {k : S} {x : A}
  证明: by
  rw [span_smul_of_span_eq_top hs]
  exact (span S t).smul_mem k (span_le_restrictScalars R S t hx)

Depends on / 依赖: smul_mem, span_le_restrictScalars, span_smul_of_span_eq_top
-/
theorem smul_mem_span_smul {s : Set S} (hs : span R s = ⊤) {t : Set A} {k : S} {x : A}
    (hx : x in span R t) : k • x in span R (s • t) := by
  rw [span_smul_of_span_eq_top hs]
  exact (span S t).smul_mem k (span_le_restrictScalars R S t hx)

end Module

section Algebra

variable [CommSemiring R] [Semiring S] [AddCommMonoid A]
variable [Algebra R S] [Module S A] [Module R A] [IsScalarTower R S A]

/--
theorem `span_algebraMap_image` / 定理 `span_algebraMap_image`

English:
theorem span_algebraMap_image
  given: (a : Set R)
  proof: (Submodule.span_image <| Algebra.linearMap R S).trans rfl

中文:
定理 span_algebraMap_image
  条件: (a : Set R)
  证明: (Submodule.span_image <| Algebra.linearMap R S).trans rfl

Depends on / 依赖: Algebra, Algebra.linearMap, Submodule, Submodule.span_image, linearMap, span_image
-/
theorem span_algebraMap_image (a : Set R) :
    Submodule.span R (algebraMap R S '' a) = (Submodule.span R a).map (Algebra.linearMap R S) :=
  (Submodule.span_image <| Algebra.linearMap R S).trans rfl

/--
theorem `span_algebraMap_image_of_tower` / 定理 `span_algebraMap_image_of_tower`

English:
theorem span_algebraMap_image_of_tower
  statement: {S T : Type*} [CommSemiring S] [Semiring T] [Module R S]
  proof: (Submodule.span_image <| (Algebra.linearMap S T).restrictScalars R).trans rfl

中文:
定理 span_algebraMap_image_of_tower
  结论: {S T : 类型} [CommSemiring S] [Semiring T] [Module R S]
  证明: (Submodule.span_image <| (Algebra.linearMap S T).restrictScalars R).trans rfl

Depends on / 依赖: Algebra, Algebra.linearMap, Submodule, Submodule.span_image, linearMap, restrictScalars, span_image
-/
theorem span_algebraMap_image_of_tower {S T : Type*} [CommSemiring S] [Semiring T] [Module R S]
    [Algebra R T] [Algebra S T] [IsScalarTower R S T] (a : Set S) :
    Submodule.span R (algebraMap S T '' a) =
      (Submodule.span R a).map ((Algebra.linearMap S T).restrictScalars R) :=
  (Submodule.span_image <| (Algebra.linearMap S T).restrictScalars R).trans rfl

/--
theorem `map_mem_span_algebraMap_image` / 定理 `map_mem_span_algebraMap_image`

English:
theorem map_mem_span_algebraMap_image
  statement: {S T : Type*} [CommSemiring S] [Semiring T] [Algebra R S]
  proof: by
  rw [span_algebraMap_image_of_tower]; rw [mem_map]
  exact ⟨x, hx, rfl⟩

中文:
定理 map_mem_span_algebraMap_image
  结论: {S T : 类型} [CommSemiring S] [Semiring T] [Algebra R S]
  证明: by
  rw [span_algebraMap_image_of_tower]; rw [mem_map]
  exact ⟨x, hx, rfl⟩

Depends on / 依赖: mem_map, span_algebraMap_image_of_tower
-/
theorem map_mem_span_algebraMap_image {S T : Type*} [CommSemiring S] [Semiring T] [Algebra R S]
    [Algebra R T] [Algebra S T] [IsScalarTower R S T] (x : S) (a : Set S)
    (hx : x in Submodule.span R a) : algebraMap S T x in Submodule.span R (algebraMap S T '' a) := by
  rw [span_algebraMap_image_of_tower]; rw [mem_map]
  exact ⟨x, hx, rfl⟩

end Algebra

end Submodule

end Semiring

section Ring

namespace Algebra

variable [CommSemiring R] [Semiring A] [IsDomain A] [Semiring B] [Algebra R A] [Algebra R B]
variable [AddCommGroup M] [Module R M] [Module A M] [Module B M]
variable [IsScalarTower R A M] [IsScalarTower R B M] [SMulCommClass A B M]

/--
theorem `lsmul_injective` / 定理 `lsmul_injective`

English:
theorem lsmul_injective
  given: [Module.IsTorsionFree A M] {x : A} (hx : x != 0)
  proof: smul_right_injective M hx

中文:
定理 lsmul_injective
  条件: [Module.IsTorsionFree A M] {x : A} (hx : x != 0)
  证明: smul_right_injective M hx

Depends on / 依赖: smul_right_injective
-/
theorem lsmul_injective [Module.IsTorsionFree A M] {x : A} (hx : x != 0) :
    Function.Injective (lsmul R B M x) :=
  smul_right_injective M hx

end Algebra

end Ring

section Algebra.algebraMapSubmonoid

@[simp]
/--
theorem `Algebra.algebraMapSubmonoid_map_map` / 定理 `Algebra.algebraMapSubmonoid_map_map`

English:
theorem Algebra.algebraMapSubmonoid_map_map
  statement: {R A B : Type*} [CommSemiring R] [CommSemiring A]
  proof: algebraMapSubmonoid_map_eq _ (IsScalarTower.toAlgHom R A B)

中文:
定理 Algebra.algebraMapSubmonoid_map_map
  结论: {R A B : 类型} [CommSemiring R] [CommSemiring A]
  证明: algebraMapSubmonoid_map_eq _ (IsScalarTower.toAlgHom R A B)

Depends on / 依赖: IsScalarTower, IsScalarTower.toAlgHom, algebraMapSubmonoid_map_eq, toAlgHom
-/
theorem Algebra.algebraMapSubmonoid_map_map {R A B : Type*} [CommSemiring R] [CommSemiring A]
    [Algebra R A] (M : Submonoid R) [Semiring B] [Algebra R B] [Algebra A B] [IsScalarTower R A B] :
    algebraMapSubmonoid B (algebraMapSubmonoid A M) = algebraMapSubmonoid B M :=
  algebraMapSubmonoid_map_eq _ (IsScalarTower.toAlgHom R A B)

end Algebra.algebraMapSubmonoid
