/-
Copyright (c) 2023 Andrew Yang, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.RingHom.Finite
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Localization.NormTrace
public import Mathlib.RingTheory.Norm.Transitivity

/-!
# Restriction of various maps between fields to integrally closed subrings.

In this file, we assume `A` is an integrally closed domain; `K` is the fraction ring of `A`;
`L` is a finite extension of `K`; `B` is the integral closure of `A` in `L`.
We call this the AKLB setup.

## Main definitions
- `galRestrict`: The restriction `Aut(L/K) → Aut(B/A)` as an `MulEquiv` in an AKLB setup.
- `Algebra.intTrace`: The trace map of a finite extension of integrally closed domains `B/A` is
  defined to be the restriction of the trace map of `Frac(B)/Frac(A)`.
- `Algebra.intNorm`: The norm map of a finite extension of integrally closed domains `B/A` is
  defined to be the restriction of the norm map of `Frac(B)/Frac(A)`.

-/

@[expose] public section

open Module nonZeroDivisors

variable (A K L L₂ L₃ B B₂ B₃ : Type*)
variable [CommRing A] [CommRing B] [CommRing B₂] [CommRing B₃]
variable [Algebra A B] [Algebra A B₂] [Algebra A B₃]
variable [Field K] [Field L] [Field L₂] [Field L₃]
variable [Algebra A K] [IsFractionRing A K]
variable [Algebra K L] [Algebra A L] [IsScalarTower A K L]
variable [Algebra K L₂] [Algebra A L₂] [IsScalarTower A K L₂]
variable [Algebra K L₃] [Algebra A L₃] [IsScalarTower A K L₃]
variable [Algebra B L] [IsScalarTower A B L] [IsIntegralClosure B A L]
variable [Algebra B₂ L₂] [IsScalarTower A B₂ L₂] [IsIntegralClosure B₂ A L₂]
variable [Algebra B₃ L₃] [IsScalarTower A B₃ L₃] [IsIntegralClosure B₃ A L₃]

section galois

section galRestrict'
variable {K L L₂ L₃}
omit [IsFractionRing A K]

/-- A generalization of `galRestrictHom` beyond endomorphisms. -/
noncomputable
/--
Definition of `galRestrict'` / `galRestrict'` 的定义

English:
definition galRestrict'
  signature: (f : L ->ₐ[K] L₂)
  body: (IsIntegralClosure.equiv A (integralClosure A L₂) L₂ B₂).toAlgHom.comp
      (((f.restrictScalars A).comp (IsScalarTower.toAlgHom A B L)).codRestrict
        (integralClosure A L₂) (fun x => IsIntegral.map _ (IsIntegralClosure.isIntegral A L x)))

中文:
定义 galRestrict'
  签名: (f : L ->ₐ[K] L₂)
  定义体: (IsIntegralClosure.equiv A (integralClosure A L₂) L₂ B₂).toAlgHom.comp
      (((f.restrictScalars A).comp (IsScalarTower.toAlgHom A B L)).codRestrict
        (integralClosure A L₂) (fun x => IsIntegral.map _ (IsIntegralClosure.isIntegral A L x)))

Depends on / 依赖: IsIntegral, IsIntegral.map, IsIntegralClosure, IsIntegralClosure.equiv, IsIntegralClosure.isIntegral, IsScalarTower, IsScalarTower.toAlgHom, codRestrict, f.restrictScalars, integralClosure, isIntegral, restrictScalars, toAlgHom, toAlgHom.comp
-/
def galRestrict' (f : L ->ₐ[K] L₂) : (B ->ₐ[A] B₂) :=
  (IsIntegralClosure.equiv A (integralClosure A L₂) L₂ B₂).toAlgHom.comp
      (((f.restrictScalars A).comp (IsScalarTower.toAlgHom A B L)).codRestrict
        (integralClosure A L₂) (fun x => IsIntegral.map _ (IsIntegralClosure.isIntegral A L x)))

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `algebraMap_galRestrict'_apply` / 引理 `algebraMap_galRestrict'_apply`

English:
lemma algebraMap_galRestrict'_apply
  given: (σ : L ->ₐ[K] L₂) (x : B)
  proof: by
  simp [galRestrict', galRestrict', Subalgebra.algebraMap_eq]

@[simp]

中文:
引理 algebraMap_galRestrict'_apply
  条件: (σ : L ->ₐ[K] L₂) (x : B)
  证明: by
  simp [galRestrict', galRestrict', Subalgebra.algebraMap_eq]

@[simp]

Depends on / 依赖: Subalgebra, Subalgebra.algebraMap_eq, algebraMap_eq, galRestrict
-/
lemma algebraMap_galRestrict'_apply (σ : L ->ₐ[K] L₂) (x : B) :
    algebraMap B₂ L₂ (galRestrict' A B B₂ σ x) = σ (algebraMap B L x) := by
  simp [galRestrict', galRestrict', Subalgebra.algebraMap_eq]

@[simp]
/--
theorem `galRestrict'_id` / 定理 `galRestrict'_id`

English:
theorem galRestrict'_id
  statement: galRestrict' A B B (.id K L) = .id A B
  proof: by
  ext
  apply IsIntegralClosure.algebraMap_injective B A L
  simp

中文:
定理 galRestrict'_id
  结论: galRestrict' A B B (.id K L) = .id A B
  证明: by
  ext
  apply IsIntegralClosure.algebraMap_injective B A L
  simp
-/
theorem galRestrict'_id : galRestrict' A B B (.id K L) = .id A B := by
  ext
  apply IsIntegralClosure.algebraMap_injective B A L
  simp

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `galRestrict'_comp` / 定理 `galRestrict'_comp`

English:
theorem galRestrict'_comp
  given: (σ : L ->ₐ[K] L₂) (σ' : L₂ ->ₐ[K] L₃)
  proof: by
  ext x
  apply (IsIntegralClosure.equiv A (integralClosure A L₃) L₃ B₃).symm.injective
  ext
  simp [galRestrict', Subalgebra.algebraMap_eq]

中文:
定理 galRestrict'_comp
  条件: (σ : L ->ₐ[K] L₂) (σ' : L₂ ->ₐ[K] L₃)
  证明: by
  ext x
  apply (IsIntegralClosure.equiv A (integralClosure A L₃) L₃ B₃).symm.injective
  ext
  simp [galRestrict', Subalgebra.algebraMap_eq]
-/
theorem galRestrict'_comp (σ : L ->ₐ[K] L₂) (σ' : L₂ ->ₐ[K] L₃) :
    galRestrict' A B B₃ (σ'.comp σ) = (galRestrict' A B₂ B₃ σ').comp (galRestrict' A B B₂ σ) := by
  ext x
  apply (IsIntegralClosure.equiv A (integralClosure A L₃) L₃ B₃).symm.injective
  ext
  simp [galRestrict', Subalgebra.algebraMap_eq]

end galRestrict'

variable [Algebra.IsAlgebraic K L]

section galLift
variable {A B B₂ B₃}

/-- A generalization of the lift `End(B/A) → End(L/K)` in an ALKB setup.
This is inverse to the restriction. See `galRestrictHom`. -/
noncomputable
/--
Definition of `galLift` / `galLift` 的定义

English:
definition galLift
  signature: (σ : B ->ₐ[A] B₂)
  body: haveI := (IsFractionRing.injective A K).isDomain
  haveI := IsTorsionFree.trans_faithfulSMul A K L₂
  haveI := IsIntegralClosure.isLocalization A K L B
  haveI H : forall (y : Algebra.algebraMapSubmonoid B A⁰),
      IsUnit (((algebraMap B₂ L₂).comp σ) (y : B)) := by
    rintro ⟨_, x, hx, rfl⟩
    simpa only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, AlgHom.commutes,
      isUnit_iff_ne_zero, ne_eq, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective _ _),
      ← IsScalarTower.algebraMap_apply] using nonZeroDivisors.ne_zero hx
  haveI H_eq : (IsLocalization.lift (S := L) H).comp (algebraMap K L) = (algebraMap K L₂) := by
    apply IsLocalization.ringHom_ext A⁰
    ext
    simp only [RingHom.coe_comp, Function.comp_apply, ← IsScalarTower.algebraMap_apply A K L,
      ← IsScalarTower.algebraMap_apply A K L₂,
      IsScalarTower.algebraMap_apply A B L, IsScalarTower.algebraMap_apply A B₂ L₂,
      IsLocalization.lift_eq, RingHom.coe_coe, AlgHom.commutes]
  { IsLocalization.lift (S := L) H with commutes' := DFunLike.congr_fun H_eq }

omit [IsIntegralClosure B₂ A L₂] in
@[simp]

中文:
定义 galLift
  签名: (σ : B ->ₐ[A] B₂)
  定义体: haveI := (IsFractionRing.injective A K).isDomain
  haveI := IsTorsionFree.trans_faithfulSMul A K L₂
  haveI := IsIntegralClosure.isLocalization A K L B
  haveI H : forall (y : Algebra.algebraMapSubmonoid B A⁰),
      IsUnit (((algebraMap B₂ L₂).comp σ) (y : B)) := by
    rintro ⟨_, x, hx, rfl⟩
    simpa only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, AlgHom.commutes,
      isUnit_iff_ne_zero, ne_eq, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective _ _),
      ← IsScalarTower.algebraMap_apply] using nonZeroDivisors.ne_zero hx
  haveI H_eq : (IsLocalization.lift (S := L) H).comp (algebraMap K L) = (algebraMap K L₂) := by
    apply IsLocalization.ringHom_ext A⁰
    ext
    simp only [RingHom.coe_comp, Function.comp_apply, ← IsScalarTower.algebraMap_apply A K L,
      ← IsScalarTower.algebraMap_apply A K L₂,
      IsScalarTower.algebraMap_apply A B L, IsScalarTower.algebraMap_apply A B₂ L₂,
      IsLocalization.lift_eq, RingHom.coe_coe, AlgHom.commutes]
  { IsLocalization.lift (S := L) H with commutes' := DFunLike.congr_fun H_eq }

omit [IsIntegralClosure B₂ A L₂] in
@[simp]

Depends on / 依赖: AlgHom, AlgHom.commutes, Algebra, Algebra.algebraMapSubmonoid, FaithfulSMul, FaithfulSMul.algebraMap_injective, Function, Function.comp_apply, IsFractionRing, IsFractionRing.injective, IsIntegralClosure, IsIntegralClosure.isLocalization, IsScalarTower, IsScalarTower.algebraMap_apply, IsTorsionFree, IsTorsionFree.trans_faithfulSMul, IsUnit, RingHom, RingHom.coe_coe, RingHom.coe_comp
-/
def galLift (σ : B ->ₐ[A] B₂) : L ->ₐ[K] L₂ :=
  haveI := (IsFractionRing.injective A K).isDomain
  haveI := IsTorsionFree.trans_faithfulSMul A K L₂
  haveI := IsIntegralClosure.isLocalization A K L B
  haveI H : forall (y : Algebra.algebraMapSubmonoid B A⁰),
      IsUnit (((algebraMap B₂ L₂).comp σ) (y : B)) := by
    rintro ⟨_, x, hx, rfl⟩
    simpa only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, AlgHom.commutes,
      isUnit_iff_ne_zero, ne_eq, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective _ _),
      ← IsScalarTower.algebraMap_apply] using nonZeroDivisors.ne_zero hx
  haveI H_eq : (IsLocalization.lift (S := L) H).comp (algebraMap K L) = (algebraMap K L₂) := by
    apply IsLocalization.ringHom_ext A⁰
    ext
    simp only [RingHom.coe_comp, Function.comp_apply, ← IsScalarTower.algebraMap_apply A K L,
      ← IsScalarTower.algebraMap_apply A K L₂,
      IsScalarTower.algebraMap_apply A B L, IsScalarTower.algebraMap_apply A B₂ L₂,
      IsLocalization.lift_eq, RingHom.coe_coe, AlgHom.commutes]
  { IsLocalization.lift (S := L) H with commutes' := DFunLike.congr_fun H_eq }

omit [IsIntegralClosure B₂ A L₂] in
@[simp]
/--
theorem `galLift_algebraMap_apply` / 定理 `galLift_algebraMap_apply`

English:
theorem galLift_algebraMap_apply
  given: (σ : B ->ₐ[A] B₂) (x : B)
  proof: by
  simp [galLift]

@[simp]

中文:
定理 galLift_algebraMap_apply
  条件: (σ : B ->ₐ[A] B₂) (x : B)
  证明: by
  simp [galLift]

@[simp]

Depends on / 依赖: galLift
-/
theorem galLift_algebraMap_apply (σ : B ->ₐ[A] B₂) (x : B) :
    galLift K L L₂ σ (algebraMap B L x) = algebraMap B₂ L₂ (σ x) := by
  simp [galLift]

@[simp]
/--
theorem `galLift_id` / 定理 `galLift_id`

English:
theorem galLift_id
  statement: galLift K L L (.id A B) = .id K L
  proof: by
  ext; simp [galLift]

omit [IsIntegralClosure B₃ A L₃] in

中文:
定理 galLift_id
  结论: galLift K L L (.id A B) = .id K L
  证明: by
  ext; simp [galLift]

omit [IsIntegralClosure B₃ A L₃] in

Depends on / 依赖: galLift
-/
theorem galLift_id : galLift K L L (.id A B) = .id K L := by
  ext; simp [galLift]

omit [IsIntegralClosure B₃ A L₃] in
/--
theorem `galLift_comp` / 定理 `galLift_comp`

English:
theorem galLift_comp
  given: [Algebra.IsAlgebraic K L₂] (σ : B ->ₐ[A] B₂) (σ' : B₂ ->ₐ[A] B₃)
  proof: have := (IsFractionRing.injective A K).isDomain
  have := IsIntegralClosure.isLocalization A K L B
AlgHom.coe_ringHom_injective IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid B A⁰)
 RingHom.ext fun x => by simp

中文:
定理 galLift_comp
  条件: [代数.是代数 K L₂] (σ : B ->ₐ[A] B₂) (σ' : B₂ ->ₐ[A] B₃)
  证明: have := (IsFractionRing.injective A K).isDomain
  have := IsIntegralClosure.isLocalization A K L B
AlgHom.coe_ringHom_injective IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid B A⁰)
 RingHom.ext fun x => by simp

Depends on / 依赖: AlgHom, AlgHom.coe_ringHom_injective, Algebra, Algebra.algebraMapSubmonoid, IsFractionRing, IsFractionRing.injective, IsIntegralClosure, IsIntegralClosure.isLocalization, IsLocalization, IsLocalization.ringHom_ext, RingHom, RingHom.ext, algebraMapSubmonoid, coe_ringHom_injective, injective, isDomain, isLocalization, ringHom_ext
-/
theorem galLift_comp [Algebra.IsAlgebraic K L₂] (σ : B ->ₐ[A] B₂) (σ' : B₂ ->ₐ[A] B₃) :
    galLift K L L₃ (σ'.comp σ) = (galLift K L₂ L₃ σ').comp (galLift K L L₂ σ) :=
  have := (IsFractionRing.injective A K).isDomain
  have := IsIntegralClosure.isLocalization A K L B
AlgHom.coe_ringHom_injective IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid B A⁰)
 RingHom.ext fun x => by simp

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `galLift_galRestrict'` / 定理 `galLift_galRestrict'`

English:
theorem galLift_galRestrict'
  given: (σ : L ->ₐ[K] L₂)
  proof: have := (IsFractionRing.injective A K).isDomain
  have := IsIntegralClosure.isLocalization A K L B
AlgHom.coe_ringHom_injective IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid B A⁰)
 RingHom.ext fun x => by simp [galRestrict', Subalgebra.algebraMap_eq, galLift]

@[simp]

中文:
定理 galLift_galRestrict'
  条件: (σ : L ->ₐ[K] L₂)
  证明: have := (IsFractionRing.injective A K).isDomain
  have := IsIntegralClosure.isLocalization A K L B
AlgHom.coe_ringHom_injective IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid B A⁰)
 RingHom.ext fun x => by simp [galRestrict', Subalgebra.algebraMap_eq, galLift]

@[simp]

Depends on / 依赖: AlgHom, AlgHom.coe_ringHom_injective, Algebra, Algebra.algebraMapSubmonoid, IsFractionRing, IsFractionRing.injective, IsIntegralClosure, IsIntegralClosure.isLocalization, IsLocalization, IsLocalization.ringHom_ext, RingHom, RingHom.ext, Subalgebra, Subalgebra.algebraMap_eq, algebraMapSubmonoid, algebraMap_eq, coe_ringHom_injective, galLift, galRestrict, injective
-/
theorem galLift_galRestrict' (σ : L ->ₐ[K] L₂) :
    galLift K L L₂ (galRestrict' A B B₂ σ) = σ :=
  have := (IsFractionRing.injective A K).isDomain
  have := IsIntegralClosure.isLocalization A K L B
AlgHom.coe_ringHom_injective IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid B A⁰)
 RingHom.ext fun x => by simp [galRestrict', Subalgebra.algebraMap_eq, galLift]

@[simp]
/--
theorem `galRestrict'_galLift` / 定理 `galRestrict'_galLift`

English:
theorem galRestrict'_galLift
  given: (σ : B ->ₐ[A] B₂)
  proof: have := (IsFractionRing.injective A K).isDomain
  have := IsIntegralClosure.isLocalization A K L B
  AlgHom.ext fun x => IsIntegralClosure.algebraMap_injective B₂ A L₂
    (by simp)

中文:
定理 galRestrict'_galLift
  条件: (σ : B ->ₐ[A] B₂)
  证明: have := (IsFractionRing.injective A K).isDomain
  have := IsIntegralClosure.isLocalization A K L B
  AlgHom.ext fun x => IsIntegralClosure.algebraMap_injective B₂ A L₂
    (by simp)
-/
theorem galRestrict'_galLift (σ : B ->ₐ[A] B₂) :
    galRestrict' A B B₂ (galLift K L L₂ σ) = σ :=
  have := (IsFractionRing.injective A K).isDomain
  have := IsIntegralClosure.isLocalization A K L B
  AlgHom.ext fun x => IsIntegralClosure.algebraMap_injective B₂ A L₂
    (by simp)

/--
A version of `galLift` for `AlgEquiv`.
-/
@[simps! -fullyApplied apply symm_apply]
noncomputable
/--
Definition of `galLiftEquiv` / `galLiftEquiv` 的定义

English:
definition galLiftEquiv
  signature: [Algebra.IsAlgebraic K L₂] (σ : B ≃ₐ[A] B₂)
  body: AlgEquiv.ofAlgHom (galLift K L L₂ σ.toAlgHom) (galLift K L₂ L σ.symm.toAlgHom)
  (by simp [← galLift_comp]) (by simp [← galLift_comp])

中文:
定义 galLiftEquiv
  签名: [代数.是代数 K L₂] (σ : B ≃ₐ[A] B₂)
  定义体: AlgEquiv.ofAlgHom (galLift K L L₂ σ.toAlgHom) (galLift K L₂ L σ.symm.toAlgHom)
  (by simp [← galLift_comp]) (by simp [← galLift_comp])

Depends on / 依赖: AlgEquiv, AlgEquiv.ofAlgHom, galLift, galLift_comp, ofAlgHom, symm.toAlgHom, toAlgHom
-/
def galLiftEquiv [Algebra.IsAlgebraic K L₂] (σ : B ≃ₐ[A] B₂) : L ≃ₐ[K] L₂ :=
  AlgEquiv.ofAlgHom (galLift K L L₂ σ.toAlgHom) (galLift K L₂ L σ.symm.toAlgHom)
  (by simp [← galLift_comp]) (by simp [← galLift_comp])

/--
theorem `galLiftEquiv_algebraMap_apply` / 定理 `galLiftEquiv_algebraMap_apply`

English:
theorem galLiftEquiv_algebraMap_apply
  given: [Algebra.IsAlgebraic K L₂] (σ : B ≃ₐ[A] B₂) (x : B)
  proof: by
  simp [galLiftEquiv]

中文:
定理 galLiftEquiv_algebraMap_apply
  条件: [代数.是代数 K L₂] (σ : B ≃ₐ[A] B₂) (x : B)
  证明: by
  simp [galLiftEquiv]

Depends on / 依赖: galLiftEquiv
-/
theorem galLiftEquiv_algebraMap_apply [Algebra.IsAlgebraic K L₂] (σ : B ≃ₐ[A] B₂) (x : B) :
    galLiftEquiv K L L₂ σ (algebraMap B L x) = algebraMap B₂ L₂ (σ x) := by
  simp [galLiftEquiv]

end galLift

/-- The restriction `End(L/K) → End(B/A)` in an AKLB setup.
Also see `galRestrict` for the `AlgEquiv` version. -/
@[simps -isSimp]
noncomputable
/--
Definition of `galRestrictHom` / `galRestrictHom` 的定义

English:
definition galRestrictHom
  signature: : (L ->ₐ[K] L) ≃* (B ->ₐ[A] B) where
  body: galRestrict' A B B f
  map_mul' σ₁ σ₂ := galRestrict'_comp _ _ _ _ σ₂ σ₁
  invFun := galLift K L L
  left_inv σ := galLift_galRestrict' _ _ _ σ
  right_inv σ := galRestrict'_galLift _ _ _ σ

@[simp]

中文:
定义 galRestrictHom
  签名: : (L ->ₐ[K] L) ≃* (B ->ₐ[A] B) where
  定义体: galRestrict' A B B f
  map_mul' σ₁ σ₂ := galRestrict'_comp _ _ _ _ σ₂ σ₁
  invFun := galLift K L L
  left_inv σ := galLift_galRestrict' _ _ _ σ
  right_inv σ := galRestrict'_galLift _ _ _ σ

@[simp]

Depends on / 依赖: galRestrict
-/
def galRestrictHom : (L ->ₐ[K] L) ≃* (B ->ₐ[A] B) where
  toFun f := galRestrict' A B B f
  map_mul' σ₁ σ₂ := galRestrict'_comp _ _ _ _ σ₂ σ₁
  invFun := galLift K L L
  left_inv σ := galLift_galRestrict' _ _ _ σ
  right_inv σ := galRestrict'_galLift _ _ _ σ

@[simp]
/--
lemma `algebraMap_galRestrictHom_apply` / 引理 `algebraMap_galRestrictHom_apply`

English:
lemma algebraMap_galRestrictHom_apply
  given: (σ : L ->ₐ[K] L) (x : B)
  proof: algebraMap_galRestrict'_apply _ _ _ _ _

@[simp, nolint unusedHavesSuffices] -- false positive from unfolding galRestrictHom

中文:
引理 algebraMap_galRestrictHom_apply
  条件: (σ : L ->ₐ[K] L) (x : B)
  证明: algebraMap_galRestrict'_apply _ _ _ _ _

@[simp, nolint unusedHavesSuffices] -- false positive from unfolding galRestrictHom

Depends on / 依赖: _apply, algebraMap_galRestrict
-/
lemma algebraMap_galRestrictHom_apply (σ : L ->ₐ[K] L) (x : B) :
    algebraMap B L (galRestrictHom A K L B σ x) = σ (algebraMap B L x) :=
  algebraMap_galRestrict'_apply _ _ _ _ _

@[simp, nolint unusedHavesSuffices] -- false positive from unfolding galRestrictHom
/--
lemma `galRestrictHom_symm_algebraMap_apply` / 引理 `galRestrictHom_symm_algebraMap_apply`

English:
lemma galRestrictHom_symm_algebraMap_apply
  given: (σ : B ->ₐ[A] B) (x : B)
  proof: galLift_algebraMap_apply _ _ _ _ _

中文:
引理 galRestrictHom_symm_algebraMap_apply
  条件: (σ : B ->ₐ[A] B) (x : B)
  证明: galLift_algebraMap_apply _ _ _ _ _

Depends on / 依赖: galLift_algebraMap_apply
-/
lemma galRestrictHom_symm_algebraMap_apply (σ : B ->ₐ[A] B) (x : B) :
    (galRestrictHom A K L B).symm σ (algebraMap B L x) = algebraMap B L (σ x) :=
  galLift_algebraMap_apply _ _ _ _ _

/-- The restriction `Aut(L/K) → Aut(B/A)` in an AKLB setup. -/
noncomputable
/--
Definition of `galRestrict` / `galRestrict` 的定义

English:
definition galRestrict
  signature: : Gal(L/K) ≃* (B ≃ₐ[A] B)
  body: (AlgEquiv.algHomUnitsEquiv K L).symm.trans
    ((Units.mapEquiv <| galRestrictHom A K L B).trans (AlgEquiv.algHomUnitsEquiv A B))

中文:
定义 galRestrict
  签名: : Gal(L/K) ≃* (B ≃ₐ[A] B)
  定义体: (AlgEquiv.algHomUnitsEquiv K L).symm.trans
    ((Units.mapEquiv <| galRestrictHom A K L B).trans (AlgEquiv.algHomUnitsEquiv A B))

Depends on / 依赖: AlgEquiv, AlgEquiv.algHomUnitsEquiv, Units.mapEquiv, algHomUnitsEquiv, galRestrictHom, mapEquiv, symm.trans
-/
def galRestrict : Gal(L/K) ≃* (B ≃ₐ[A] B) :=
  (AlgEquiv.algHomUnitsEquiv K L).symm.trans
    ((Units.mapEquiv <| galRestrictHom A K L B).trans (AlgEquiv.algHomUnitsEquiv A B))

variable {K L}

/--
lemma `coe_galRestrict_apply` / 引理 `coe_galRestrict_apply`

English:
lemma coe_galRestrict_apply
  given: (σ : Gal(L/K))
  proof: rfl

中文:
引理 coe_galRestrict_apply
  条件: (σ : Gal(L/K))
  证明: rfl
-/
lemma coe_galRestrict_apply (σ : Gal(L/K)) :
    (galRestrict A K L B σ : B ->ₐ[A] B) = galRestrictHom A K L B σ := rfl

variable {B}

/--
lemma `galRestrict_apply` / 引理 `galRestrict_apply`

English:
lemma galRestrict_apply
  given: (σ : Gal(L/K)) (x : B)
  proof: rfl

中文:
引理 galRestrict_apply
  条件: (σ : Gal(L/K)) (x : B)
  证明: rfl
-/
lemma galRestrict_apply (σ : Gal(L/K)) (x : B) :
    galRestrict A K L B σ x = galRestrictHom A K L B σ x := rfl

/--
lemma `algebraMap_galRestrict_apply` / 引理 `algebraMap_galRestrict_apply`

English:
lemma algebraMap_galRestrict_apply
  given: (σ : Gal(L/K)) (x : B)
  proof: algebraMap_galRestrictHom_apply A K L B σ.toAlgHom x

中文:
引理 algebraMap_galRestrict_apply
  条件: (σ : Gal(L/K)) (x : B)
  证明: algebraMap_galRestrictHom_apply A K L B σ.toAlgHom x

Depends on / 依赖: algebraMap_galRestrictHom_apply, toAlgHom
-/
lemma algebraMap_galRestrict_apply (σ : Gal(L/K)) (x : B) :
    algebraMap B L (galRestrict A K L B σ x) = σ (algebraMap B L x) :=
  algebraMap_galRestrictHom_apply A K L B σ.toAlgHom x

variable (K) in
/--
lemma `galRestrict_symm_algebraMap_apply` / 引理 `galRestrict_symm_algebraMap_apply`

English:
lemma galRestrict_symm_algebraMap_apply
  given: (σ : B ≃ₐ[A] B) (x : B)
  proof: galRestrictHom_symm_algebraMap_apply A K L B σ x

中文:
引理 galRestrict_symm_algebraMap_apply
  条件: (σ : B ≃ₐ[A] B) (x : B)
  证明: galRestrictHom_symm_algebraMap_apply A K L B σ x

Depends on / 依赖: galRestrictHom_symm_algebraMap_apply
-/
lemma galRestrict_symm_algebraMap_apply (σ : B ≃ₐ[A] B) (x : B) :
    (galRestrict A K L B).symm σ (algebraMap B L x) = algebraMap B L (σ x) :=
  galRestrictHom_symm_algebraMap_apply A K L B σ x

end galois

variable [FiniteDimensional K L]

/--
lemma `prod_galRestrict_eq_norm` / 引理 `prod_galRestrict_eq_norm`

English:
lemma prod_galRestrict_eq_norm
  given: [IsGalois K L] [IsIntegrallyClosed A] (x : B)
  proof: by
  apply IsIntegralClosure.algebraMap_injective B A L
  rw [← IsScalarTower.algebraMap_apply]; rw [IsScalarTower.algebraMap_eq A K L]
  simp only [map_prod, algebraMap_galRestrict_apply, IsIntegralClosure.algebraMap_mk',
    Algebra.norm_eq_prod_automorphisms, RingHom.coe_comp, Function.comp_apply]

中文:
引理 prod_galRestrict_eq_norm
  条件: [是Galois K L] [是整闭 A] (x : B)
  证明: by
  apply IsIntegralClosure.algebraMap_injective B A L
  rw [← IsScalarTower.algebraMap_apply]; rw [IsScalarTower.algebraMap_eq A K L]
  simp only [map_prod, algebraMap_galRestrict_apply, IsIntegralClosure.algebraMap_mk',
    Algebra.norm_eq_prod_automorphisms, RingHom.coe_comp, Function.comp_apply]

Depends on / 依赖: Algebra, Algebra.norm, algebraMap
-/
lemma prod_galRestrict_eq_norm [IsGalois K L] [IsIntegrallyClosed A] (x : B) :
    (∏ σ : Gal(L/K), galRestrict A K L B σ x) =
    algebraMap A B (IsIntegralClosure.mk' (R := A) A (Algebra.norm K <| algebraMap B L x)
      (Algebra.isIntegral_norm K (IsIntegralClosure.isIntegral A L x).algebraMap)) := by
  apply IsIntegralClosure.algebraMap_injective B A L
  rw [← IsScalarTower.algebraMap_apply]; rw [IsScalarTower.algebraMap_eq A K L]
  simp only [map_prod, algebraMap_galRestrict_apply, IsIntegralClosure.algebraMap_mk',
    Algebra.norm_eq_prod_automorphisms, RingHom.coe_comp, Function.comp_apply]

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

noncomputable
instance (priority := 900) [IsDomain A] [IsDomain B] [IsIntegrallyClosed B]
    [Module.Finite A B] [IsTorsionFree A B] : Fintype (B ≃ₐ[A] B) :=
  haveI : IsIntegralClosure B A (FractionRing B) :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  -- TODO: How is this even supposed to fire? `R` and `S` cannot be inferred.
  haveI : Algebra.IsAlgebraic (FractionRing A) (FractionRing B) :=
    isAlgebraic_of_isFractionRing A B ..
  haveI : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) (FractionRing B) :=
    IsIntegralClosure.isLocalization _ (FractionRing A) _ _
  haveI : FiniteDimensional (FractionRing A) (FractionRing B) := .of_isLocalization A B A⁰
  Fintype.ofEquiv _ (galRestrict A (FractionRing A) (FractionRing B) B).toEquiv

variable {Aₘ Bₘ} [CommRing Aₘ] [CommRing Bₘ] [Algebra Aₘ Bₘ] [Algebra A Aₘ] [Algebra B Bₘ]
variable [Algebra A Bₘ] [IsScalarTower A Aₘ Bₘ] [IsScalarTower A B Bₘ]
variable (M : Submonoid A) [IsLocalization M Aₘ]
variable [IsLocalization (Algebra.algebraMapSubmonoid B M) Bₘ]

section trace

/-- The restriction of the trace on `L/K` restricted onto `B/A` in an AKLB setup.
See `Algebra.intTrace` instead. -/
noncomputable
/--
Definition of `Algebra.intTraceAux` / `Algebra.intTraceAux` 的定义

English:
definition Algebra.intTraceAux
  signature: [IsIntegrallyClosed A]
  body: (IsIntegralClosure.equiv A (integralClosure A K) K A).toLinearMap.comp
    ((((Algebra.trace K L).restrictScalars A).comp
      (IsScalarTower.toAlgHom A B L).toLinearMap).codRestrict
        (Subalgebra.toSubmodule <| integralClosure A K) (fun x => isIntegral_trace
          (IsIntegral.algebraMap (IsIntegralClosure.isIntegral A L x))))

中文:
定义 代数.intTraceAux
  签名: [是整闭 A]
  定义体: (IsIntegralClosure.equiv A (integralClosure A K) K A).toLinearMap.comp
    ((((Algebra.trace K L).restrictScalars A).comp
      (IsScalarTower.toAlgHom A B L).toLinearMap).codRestrict
        (Subalgebra.toSubmodule <| integralClosure A K) (fun x => isIntegral_trace
          (IsIntegral.algebraMap (IsIntegralClosure.isIntegral A L x))))

Depends on / 依赖: Algebra, Algebra.trace, IsIntegral, IsIntegral.algebraMap, IsIntegralClosure, IsIntegralClosure.equiv, IsIntegralClosure.isIntegral, IsScalarTower, IsScalarTower.toAlgHom, Subalgebra, Subalgebra.toSubmodule, algebraMap, codRestrict, integralClosure, isIntegral, isIntegral_trace, restrictScalars, toAlgHom, toLinearMap, toLinearMap.comp
-/
def Algebra.intTraceAux [IsIntegrallyClosed A] :
    B ->ₗ[A] A :=
  (IsIntegralClosure.equiv A (integralClosure A K) K A).toLinearMap.comp
    ((((Algebra.trace K L).restrictScalars A).comp
      (IsScalarTower.toAlgHom A B L).toLinearMap).codRestrict
        (Subalgebra.toSubmodule <| integralClosure A K) (fun x => isIntegral_trace
          (IsIntegral.algebraMap (IsIntegralClosure.isIntegral A L x))))

variable {A K L B}

/--
lemma `Algebra.map_intTraceAux` / 引理 `Algebra.map_intTraceAux`

English:
lemma Algebra.map_intTraceAux
  given: [IsIntegrallyClosed A] (x : B)
  proof: IsIntegralClosure.algebraMap_equiv A (integralClosure A K) K A _

中文:
引理 代数.map_intTraceAux
  条件: [是整闭 A] (x : B)
  证明: IsIntegralClosure.algebraMap_equiv A (integralClosure A K) K A _

Depends on / 依赖: IsIntegralClosure, IsIntegralClosure.algebraMap_equiv, algebraMap_equiv, integralClosure
-/
lemma Algebra.map_intTraceAux [IsIntegrallyClosed A] (x : B) :
    algebraMap A K (Algebra.intTraceAux A K L B x) = Algebra.trace K L (algebraMap B L x) :=
  IsIntegralClosure.algebraMap_equiv A (integralClosure A K) K A _

variable (A B)
variable [IsDomain A] [IsIntegrallyClosed A] [IsDomain B] [IsIntegrallyClosed B]
variable [Module.Finite A B] [IsTorsionFree A B]

/-- The trace of a finite extension of integrally closed domains `B/A` is the restriction of
the trace on `Frac(B)/Frac(A)` onto `B/A`. See `Algebra.algebraMap_intTrace`. -/
noncomputable
/--
Definition of `Algebra.intTrace` / `Algebra.intTrace` 的定义

English:
definition Algebra.intTrace
  signature: : B ->ₗ[A] A
  body: haveI : IsIntegralClosure B A (FractionRing B) :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  -- TODO: How is this even supposed to fire? `R` and `S` cannot be inferred.
  haveI : Algebra.IsAlgebraic (FractionRing A) (FractionRing B) :=
    isAlgebraic_of_isFractionRing A B ..
  haveI : IsLocalization (algebraMapSubmonoid B A⁰) (FractionRing B) :=
    IsIntegralClosure.isLocalization _ (FractionRing A) _ _
  haveI : FiniteDimensional (FractionRing A) (FractionRing B) := .of_isLocalization A B A⁰
  Algebra.intTraceAux A (FractionRing A) (FractionRing B) B

中文:
定义 代数.intTrace
  签名: : B ->ₗ[A] A
  定义体: haveI : IsIntegralClosure B A (FractionRing B) :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  -- TODO: How is this even supposed to fire? `R` and `S` cannot be inferred.
  haveI : Algebra.IsAlgebraic (FractionRing A) (FractionRing B) :=
    isAlgebraic_of_isFractionRing A B ..
  haveI : IsLocalization (algebraMapSubmonoid B A⁰) (FractionRing B) :=
    IsIntegralClosure.isLocalization _ (FractionRing A) _ _
  haveI : FiniteDimensional (FractionRing A) (FractionRing B) := .of_isLocalization A B A⁰
  Algebra.intTraceAux A (FractionRing A) (FractionRing B) B

Depends on / 依赖: FractionRing, IsIntegralClosure, IsIntegralClosure.of_isIntegrallyClosed, of_isIntegrallyClosed
-/
def Algebra.intTrace : B ->ₗ[A] A :=
  haveI : IsIntegralClosure B A (FractionRing B) :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  -- TODO: How is this even supposed to fire? `R` and `S` cannot be inferred.
  haveI : Algebra.IsAlgebraic (FractionRing A) (FractionRing B) :=
    isAlgebraic_of_isFractionRing A B ..
  haveI : IsLocalization (algebraMapSubmonoid B A⁰) (FractionRing B) :=
    IsIntegralClosure.isLocalization _ (FractionRing A) _ _
  haveI : FiniteDimensional (FractionRing A) (FractionRing B) := .of_isLocalization A B A⁰
  Algebra.intTraceAux A (FractionRing A) (FractionRing B) B

variable {A B}

/--
lemma `Algebra.algebraMap_intTrace` / 引理 `Algebra.algebraMap_intTrace`

English:
lemma Algebra.algebraMap_intTrace
  given: (x : B)
  proof: by
  have : IsIntegralClosure B A (FractionRing B) :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  -- TODO: How is this even supposed to fire? `R` and `S` cannot be inferred.
  have : Algebra.IsAlgebraic (FractionRing A) (FractionRing B) :=
    isAlgebraic_of_isFractionRing A B ..
  have : IsLocalization (algebraMapSubmonoid B A⁰) (FractionRing B) :=
    IsIntegralClosure.isLocalization _ (FractionRing A) _ _
  have : FiniteDimensional (FractionRing A) (FractionRing B) := .of_isLocalization A B A⁰
  have := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  apply (FractionRing.algEquiv A K).symm.injective
  rw [AlgEquiv.commutes]; rw [Algebra.intTrace]; rw [Algebra.map_intTraceAux]; rw [← AlgEquiv.commutes (FractionRing.algEquiv B L)]
  apply Algebra.trace_eq_of_equiv_equiv (FractionRing.algEquiv A K).toRingEquiv
    (FractionRing.algEquiv B L).toRingEquiv
  ext
  exact IsFractionRing.algEquiv_commutes (FractionRing.algEquiv A K) (FractionRing.algEquiv B L) _

中文:
引理 代数.algebraMap_intTrace
  条件: (x : B)
  证明: by
  have : IsIntegralClosure B A (FractionRing B) :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  -- TODO: How is this even supposed to fire? `R` and `S` cannot be inferred.
  have : Algebra.IsAlgebraic (FractionRing A) (FractionRing B) :=
    isAlgebraic_of_isFractionRing A B ..
  have : IsLocalization (algebraMapSubmonoid B A⁰) (FractionRing B) :=
    IsIntegralClosure.isLocalization _ (FractionRing A) _ _
  have : FiniteDimensional (FractionRing A) (FractionRing B) := .of_isLocalization A B A⁰
  have := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  apply (FractionRing.algEquiv A K).symm.injective
  rw [AlgEquiv.commutes]; rw [Algebra.intTrace]; rw [Algebra.map_intTraceAux]; rw [← AlgEquiv.commutes (FractionRing.algEquiv B L)]
  apply Algebra.trace_eq_of_equiv_equiv (FractionRing.algEquiv A K).toRingEquiv
    (FractionRing.algEquiv B L).toRingEquiv
  ext
  exact IsFractionRing.algEquiv_commutes (FractionRing.algEquiv A K) (FractionRing.algEquiv B L) _

Depends on / 依赖: FractionRing, IsIntegralClosure, IsIntegralClosure.of_isIntegrallyClosed, of_isIntegrallyClosed
-/
lemma Algebra.algebraMap_intTrace (x : B) :
    algebraMap A K (Algebra.intTrace A B x) = Algebra.trace K L (algebraMap B L x) := by
  have : IsIntegralClosure B A (FractionRing B) :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  -- TODO: How is this even supposed to fire? `R` and `S` cannot be inferred.
  have : Algebra.IsAlgebraic (FractionRing A) (FractionRing B) :=
    isAlgebraic_of_isFractionRing A B ..
  have : IsLocalization (algebraMapSubmonoid B A⁰) (FractionRing B) :=
    IsIntegralClosure.isLocalization _ (FractionRing A) _ _
  have : FiniteDimensional (FractionRing A) (FractionRing B) := .of_isLocalization A B A⁰
  have := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  apply (FractionRing.algEquiv A K).symm.injective
  rw [AlgEquiv.commutes]; rw [Algebra.intTrace]; rw [Algebra.map_intTraceAux]; rw [← AlgEquiv.commutes (FractionRing.algEquiv B L)]
  apply Algebra.trace_eq_of_equiv_equiv (FractionRing.algEquiv A K).toRingEquiv
    (FractionRing.algEquiv B L).toRingEquiv
  ext
  exact IsFractionRing.algEquiv_commutes (FractionRing.algEquiv A K) (FractionRing.algEquiv B L) _

/--
lemma `Algebra.algebraMap_intTrace_fractionRing` / 引理 `Algebra.algebraMap_intTrace_fractionRing`

English:
lemma Algebra.algebraMap_intTrace_fractionRing
  given: (x : B)
  proof: by
  have : IsIntegralClosure B A (FractionRing B) :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  -- TODO: How is this even supposed to fire? `R` and `S` cannot be inferred.
  have : Algebra.IsAlgebraic (FractionRing A) (FractionRing B) :=
    isAlgebraic_of_isFractionRing A B ..
  have : IsLocalization (algebraMapSubmonoid B A⁰) (FractionRing B) :=
    IsIntegralClosure.isLocalization _ (FractionRing A) _ _
  have : FiniteDimensional (FractionRing A) (FractionRing B) := .of_isLocalization A B A⁰
  exact Algebra.map_intTraceAux x

中文:
引理 代数.algebraMap_intTrace_fractionRing
  条件: (x : B)
  证明: by
  have : IsIntegralClosure B A (FractionRing B) :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  -- TODO: How is this even supposed to fire? `R` and `S` cannot be inferred.
  have : Algebra.IsAlgebraic (FractionRing A) (FractionRing B) :=
    isAlgebraic_of_isFractionRing A B ..
  have : IsLocalization (algebraMapSubmonoid B A⁰) (FractionRing B) :=
    IsIntegralClosure.isLocalization _ (FractionRing A) _ _
  have : FiniteDimensional (FractionRing A) (FractionRing B) := .of_isLocalization A B A⁰
  exact Algebra.map_intTraceAux x

Depends on / 依赖: FractionRing, IsIntegralClosure, IsIntegralClosure.of_isIntegrallyClosed, of_isIntegrallyClosed
-/
lemma Algebra.algebraMap_intTrace_fractionRing (x : B) :
    algebraMap A (FractionRing A) (Algebra.intTrace A B x) =
      Algebra.trace (FractionRing A) (FractionRing B) (algebraMap B _ x) := by
  have : IsIntegralClosure B A (FractionRing B) :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  -- TODO: How is this even supposed to fire? `R` and `S` cannot be inferred.
  have : Algebra.IsAlgebraic (FractionRing A) (FractionRing B) :=
    isAlgebraic_of_isFractionRing A B ..
  have : IsLocalization (algebraMapSubmonoid B A⁰) (FractionRing B) :=
    IsIntegralClosure.isLocalization _ (FractionRing A) _ _
  have : FiniteDimensional (FractionRing A) (FractionRing B) := .of_isLocalization A B A⁰
  exact Algebra.map_intTraceAux x

variable (A B)

/--
lemma `Algebra.intTrace_eq_trace` / 引理 `Algebra.intTrace_eq_trace`

English:
lemma Algebra.intTrace_eq_trace
  given: [Module.Free A B]
  statement: Algebra.intTrace A B = Algebra.trace A B
  proof: by
  ext x
  have : IsIntegralClosure B A (FractionRing B) :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  -- TODO: How is this even supposed to fire? `R` and `S` cannot be inferred.
  have : Algebra.IsAlgebraic (FractionRing A) (FractionRing B) :=
    isAlgebraic_of_isFractionRing A B ..
  have : IsLocalization (algebraMapSubmonoid B A⁰) (FractionRing B) :=
    IsIntegralClosure.isLocalization _ (FractionRing A) _ _
  apply IsFractionRing.injective A (FractionRing A)
  rw [Algebra.algebraMap_intTrace_fractionRing]; rw [Algebra.trace_localization A A⁰]

中文:
引理 代数.intTrace_eq_trace
  条件: [模.自由 A B]
  结论: 代数.intTrace A B = 代数.trace A B
  证明: by
  ext x
  have : IsIntegralClosure B A (FractionRing B) :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  -- TODO: How is this even supposed to fire? `R` and `S` cannot be inferred.
  have : Algebra.IsAlgebraic (FractionRing A) (FractionRing B) :=
    isAlgebraic_of_isFractionRing A B ..
  have : IsLocalization (algebraMapSubmonoid B A⁰) (FractionRing B) :=
    IsIntegralClosure.isLocalization _ (FractionRing A) _ _
  apply IsFractionRing.injective A (FractionRing A)
  rw [Algebra.algebraMap_intTrace_fractionRing]; rw [Algebra.trace_localization A A⁰]

Depends on / 依赖: FractionRing, IsIntegralClosure, IsIntegralClosure.of_isIntegrallyClosed, of_isIntegrallyClosed
-/
lemma Algebra.intTrace_eq_trace [Module.Free A B] : Algebra.intTrace A B = Algebra.trace A B := by
  ext x
  have : IsIntegralClosure B A (FractionRing B) :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  -- TODO: How is this even supposed to fire? `R` and `S` cannot be inferred.
  have : Algebra.IsAlgebraic (FractionRing A) (FractionRing B) :=
    isAlgebraic_of_isFractionRing A B ..
  have : IsLocalization (algebraMapSubmonoid B A⁰) (FractionRing B) :=
    IsIntegralClosure.isLocalization _ (FractionRing A) _ _
  apply IsFractionRing.injective A (FractionRing A)
  rw [Algebra.algebraMap_intTrace_fractionRing]; rw [Algebra.trace_localization A A⁰]

open nonZeroDivisors

variable [IsDomain Aₘ] [IsIntegrallyClosed Aₘ] [IsDomain Bₘ] [IsIntegrallyClosed Bₘ]
variable [IsTorsionFree Aₘ Bₘ] [Module.Finite Aₘ Bₘ]

set_option backward.isDefEq.respectTransparency.types false in
include M in
/--
lemma `Algebra.intTrace_eq_of_isLocalization` / 引理 `Algebra.intTrace_eq_of_isLocalization`

English:
lemma Algebra.intTrace_eq_of_isLocalization
  proof: by
  by_cases hM : 0 in M
  · subsingleton [IsLocalization.uniqueOfZeroMem (S := Aₘ) hM]
  replace hM : M <= A⁰ := fun x hx => mem_nonZeroDivisors_iff_ne_zero.mpr (fun e => hM (e ▸ hx))
  let K := FractionRing A
  let L := FractionRing B
  have : IsIntegralClosure B A L :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  -- TODO: How is this even supposed to fire? `R` and `S` cannot be inferred.
  have : Algebra.IsAlgebraic (FractionRing A) (FractionRing B) :=
    isAlgebraic_of_isFractionRing A B ..
  have : IsLocalization (algebraMapSubmonoid B A⁰) L :=
    IsIntegralClosure.isLocalization _ (FractionRing A) _ _
  let f : Aₘ ->+* K := IsLocalization.map _ (T := A⁰) (RingHom.id A) hM
  let := f.toAlgebra
  have : IsScalarTower A Aₘ K := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, RingHomCompTriple.comp_eq])
  let := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M Aₘ K
  let g : Bₘ ->+* L := IsLocalization.map _
      (M := algebraMapSubmonoid B M) (T := algebraMapSubmonoid B A⁰)
      (RingHom.id B) (Submonoid.monotone_map hM)
  let := g.toAlgebra
  have : IsScalarTower B Bₘ L := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, RingHomCompTriple.comp_eq])
  let := ((algebraMap K L).comp f).toAlgebra
  have : IsScalarTower Aₘ K L := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Aₘ Bₘ L := by
    apply IsScalarTower.of_algebraMap_eq'
    apply IsLocalization.ringHom_ext M
    rw [RingHom.algebraMap_toAlgebra]; rw [RingHom.algebraMap_toAlgebra (R := Bₘ)]; rw [RingHom.comp_assoc]; rw [RingHom.comp_assoc]; rw [← IsScalarTower.algebraMap_eq]; rw [IsScalarTower.algebraMap_eq A B Bₘ]; rw [IsLocalization.map_comp]; rw [RingHom.comp_id]; rw [← RingHom.comp_assoc]; rw [IsLocalization.map_comp]; rw [RingHom.comp_id]; rw [← IsScalarTower.algebraMap_eq]; rw [← IsScalarTower.algebraMap_eq]
  let := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (algebraMapSubmonoid B M) Bₘ L
  have : FiniteDimensional K L := .of_isLocalization A B A⁰
  have : IsIntegralClosure Bₘ Aₘ L :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  apply IsFractionRing.injective Aₘ K
  rw [← IsScalarTower.algebraMap_apply]; rw [Algebra.algebraMap_intTrace_fractionRing]; rw [Algebra.algebraMap_intTrace (L := L)]; rw [← IsScalarTower.algebraMap_apply]

中文:
引理 代数.intTrace_eq_of_isLocalization
  证明: by
  by_cases hM : 0 in M
  · subsingleton [IsLocalization.uniqueOfZeroMem (S := Aₘ) hM]
  replace hM : M <= A⁰ := fun x hx => mem_nonZeroDivisors_iff_ne_zero.mpr (fun e => hM (e ▸ hx))
  let K := FractionRing A
  let L := FractionRing B
  have : IsIntegralClosure B A L :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  -- TODO: How is this even supposed to fire? `R` and `S` cannot be inferred.
  have : Algebra.IsAlgebraic (FractionRing A) (FractionRing B) :=
    isAlgebraic_of_isFractionRing A B ..
  have : IsLocalization (algebraMapSubmonoid B A⁰) L :=
    IsIntegralClosure.isLocalization _ (FractionRing A) _ _
  let f : Aₘ ->+* K := IsLocalization.map _ (T := A⁰) (RingHom.id A) hM
  let := f.toAlgebra
  have : IsScalarTower A Aₘ K := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, RingHomCompTriple.comp_eq])
  let := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M Aₘ K
  let g : Bₘ ->+* L := IsLocalization.map _
      (M := algebraMapSubmonoid B M) (T := algebraMapSubmonoid B A⁰)
      (RingHom.id B) (Submonoid.monotone_map hM)
  let := g.toAlgebra
  have : IsScalarTower B Bₘ L := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, RingHomCompTriple.comp_eq])
  let := ((algebraMap K L).comp f).toAlgebra
  have : IsScalarTower Aₘ K L := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Aₘ Bₘ L := by
    apply IsScalarTower.of_algebraMap_eq'
    apply IsLocalization.ringHom_ext M
    rw [RingHom.algebraMap_toAlgebra]; rw [RingHom.algebraMap_toAlgebra (R := Bₘ)]; rw [RingHom.comp_assoc]; rw [RingHom.comp_assoc]; rw [← IsScalarTower.algebraMap_eq]; rw [IsScalarTower.algebraMap_eq A B Bₘ]; rw [IsLocalization.map_comp]; rw [RingHom.comp_id]; rw [← RingHom.comp_assoc]; rw [IsLocalization.map_comp]; rw [RingHom.comp_id]; rw [← IsScalarTower.algebraMap_eq]; rw [← IsScalarTower.algebraMap_eq]
  let := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (algebraMapSubmonoid B M) Bₘ L
  have : FiniteDimensional K L := .of_isLocalization A B A⁰
  have : IsIntegralClosure Bₘ Aₘ L :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  apply IsFractionRing.injective Aₘ K
  rw [← IsScalarTower.algebraMap_apply]; rw [Algebra.algebraMap_intTrace_fractionRing]; rw [Algebra.algebraMap_intTrace (L := L)]; rw [← IsScalarTower.algebraMap_apply]

Depends on / 依赖: FractionRing, IsIntegralClosure, IsIntegralClosure.of_isIntegrallyClosed, IsLocalization, IsLocalization.uniqueOfZeroMem, mem_nonZeroDivisors_iff_ne_zero, mem_nonZeroDivisors_iff_ne_zero.mpr, of_isIntegrallyClosed, replace, subsingleton, uniqueOfZeroMem
-/
lemma Algebra.intTrace_eq_of_isLocalization
    (x : B) :
    algebraMap A Aₘ (Algebra.intTrace A B x) = Algebra.intTrace Aₘ Bₘ (algebraMap B Bₘ x) := by
  by_cases hM : 0 in M
  · subsingleton [IsLocalization.uniqueOfZeroMem (S := Aₘ) hM]
  replace hM : M <= A⁰ := fun x hx => mem_nonZeroDivisors_iff_ne_zero.mpr (fun e => hM (e ▸ hx))
  let K := FractionRing A
  let L := FractionRing B
  have : IsIntegralClosure B A L :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  -- TODO: How is this even supposed to fire? `R` and `S` cannot be inferred.
  have : Algebra.IsAlgebraic (FractionRing A) (FractionRing B) :=
    isAlgebraic_of_isFractionRing A B ..
  have : IsLocalization (algebraMapSubmonoid B A⁰) L :=
    IsIntegralClosure.isLocalization _ (FractionRing A) _ _
  let f : Aₘ ->+* K := IsLocalization.map _ (T := A⁰) (RingHom.id A) hM
  let := f.toAlgebra
  have : IsScalarTower A Aₘ K := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, RingHomCompTriple.comp_eq])
  let := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M Aₘ K
  let g : Bₘ ->+* L := IsLocalization.map _
      (M := algebraMapSubmonoid B M) (T := algebraMapSubmonoid B A⁰)
      (RingHom.id B) (Submonoid.monotone_map hM)
  let := g.toAlgebra
  have : IsScalarTower B Bₘ L := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, RingHomCompTriple.comp_eq])
  let := ((algebraMap K L).comp f).toAlgebra
  have : IsScalarTower Aₘ K L := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Aₘ Bₘ L := by
    apply IsScalarTower.of_algebraMap_eq'
    apply IsLocalization.ringHom_ext M
    rw [RingHom.algebraMap_toAlgebra]; rw [RingHom.algebraMap_toAlgebra (R := Bₘ)]; rw [RingHom.comp_assoc]; rw [RingHom.comp_assoc]; rw [← IsScalarTower.algebraMap_eq]; rw [IsScalarTower.algebraMap_eq A B Bₘ]; rw [IsLocalization.map_comp]; rw [RingHom.comp_id]; rw [← RingHom.comp_assoc]; rw [IsLocalization.map_comp]; rw [RingHom.comp_id]; rw [← IsScalarTower.algebraMap_eq]; rw [← IsScalarTower.algebraMap_eq]
  let := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (algebraMapSubmonoid B M) Bₘ L
  have : FiniteDimensional K L := .of_isLocalization A B A⁰
  have : IsIntegralClosure Bₘ Aₘ L :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  apply IsFractionRing.injective Aₘ K
  rw [← IsScalarTower.algebraMap_apply]; rw [Algebra.algebraMap_intTrace_fractionRing]; rw [Algebra.algebraMap_intTrace (L := L)]; rw [← IsScalarTower.algebraMap_apply]

end trace

section norm

variable [IsIntegrallyClosed A]

/-- The restriction of the norm on `L/K` restricted onto `B/A` in an AKLB setup.
See `Algebra.intNorm` instead. -/
noncomputable
/--
Definition of `Algebra.intNormAux` / `Algebra.intNormAux` 的定义

English:
definition Algebra.intNormAux
  signature: :
  body: fun s => IsIntegralClosure.mk' (R := A) A (Algebra.norm K (algebraMap B L s))
    (isIntegral_norm K <| IsIntegral.map (IsScalarTower.toAlgHom A B L)
      (IsIntegralClosure.isIntegral A L s))
  map_one' := by simp
  map_mul' := fun x y => by simpa using IsIntegralClosure.mk'_mul _ _ _ _ _

中文:
定义 代数.intNormAux
  签名: :
  定义体: fun s => IsIntegralClosure.mk' (R := A) A (Algebra.norm K (algebraMap B L s))
    (isIntegral_norm K <| IsIntegral.map (IsScalarTower.toAlgHom A B L)
      (IsIntegralClosure.isIntegral A L s))
  map_one' := by simp
  map_mul' := fun x y => by simpa using IsIntegralClosure.mk'_mul _ _ _ _ _

Depends on / 依赖: Algebra, Algebra.norm, IsIntegralClosure, IsIntegralClosure.mk, algebraMap
-/
def Algebra.intNormAux :
    B ->* A where
  toFun := fun s => IsIntegralClosure.mk' (R := A) A (Algebra.norm K (algebraMap B L s))
    (isIntegral_norm K <| IsIntegral.map (IsScalarTower.toAlgHom A B L)
      (IsIntegralClosure.isIntegral A L s))
  map_one' := by simp
  map_mul' := fun x y => by simpa using IsIntegralClosure.mk'_mul _ _ _ _ _

variable {A K L B}

omit [FiniteDimensional K L] in
/--
lemma `Algebra.map_intNormAux` / 引理 `Algebra.map_intNormAux`

English:
lemma Algebra.map_intNormAux
  given: (x : B)
  proof: by
  dsimp [Algebra.intNormAux]
  exact IsIntegralClosure.algebraMap_mk' _ _ _

中文:
引理 代数.map_intNormAux
  条件: (x : B)
  证明: by
  dsimp [Algebra.intNormAux]
  exact IsIntegralClosure.algebraMap_mk' _ _ _

Depends on / 依赖: Algebra, Algebra.intNormAux, IsIntegralClosure, IsIntegralClosure.algebraMap_mk, algebraMap_mk, intNormAux
-/
lemma Algebra.map_intNormAux (x : B) :
    algebraMap A K (Algebra.intNormAux A K L B x) = Algebra.norm K (algebraMap B L x) := by
  dsimp [Algebra.intNormAux]
  exact IsIntegralClosure.algebraMap_mk' _ _ _

variable (A B)
variable [IsDomain A] [IsDomain B] [IsIntegrallyClosed B] [Algebra.IsIntegral A B]
  [IsTorsionFree A B]

/-- The norm of a finite extension of integrally closed domains `B/A` is the restriction of
the norm on `Frac(B)/Frac(A)` onto `B/A`. See `Algebra.algebraMap_intNorm`. -/
noncomputable
/--
Definition of `Algebra.intNorm` / `Algebra.intNorm` 的定义

English:
definition Algebra.intNorm
  signature: : B ->* A
  body: Algebra.intNormAux A (FractionRing A) (FractionRing B) B

中文:
定义 代数.intNorm
  签名: : B ->* A
  定义体: Algebra.intNormAux A (FractionRing A) (FractionRing B) B

Depends on / 依赖: Algebra, Algebra.intNormAux, FractionRing, intNormAux
-/
def Algebra.intNorm : B ->* A := Algebra.intNormAux A (FractionRing A) (FractionRing B) B

variable {A B}

/--
lemma `Algebra.algebraMap_intNorm` / 引理 `Algebra.algebraMap_intNorm`

English:
lemma Algebra.algebraMap_intNorm
  given: (x : B)
  proof: by
  have := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  apply (FractionRing.algEquiv A K).symm.injective
  rw [AlgEquiv.commutes]; rw [Algebra.intNorm]; rw [Algebra.map_intNormAux]; rw [← AlgEquiv.commutes (FractionRing.algEquiv B L)]
  apply Algebra.norm_eq_of_equiv_equiv (FractionRing.algEquiv A K).toRingEquiv
    (FractionRing.algEquiv B L).toRingEquiv
  ext
  exact IsFractionRing.algEquiv_commutes (FractionRing.algEquiv A K) (FractionRing.algEquiv B L) _

@[simp]

中文:
引理 代数.algebraMap_intNorm
  条件: (x : B)
  证明: by
  have := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  apply (FractionRing.algEquiv A K).symm.injective
  rw [AlgEquiv.commutes]; rw [Algebra.intNorm]; rw [Algebra.map_intNormAux]; rw [← AlgEquiv.commutes (FractionRing.algEquiv B L)]
  apply Algebra.norm_eq_of_equiv_equiv (FractionRing.algEquiv A K).toRingEquiv
    (FractionRing.algEquiv B L).toRingEquiv
  ext
  exact IsFractionRing.algEquiv_commutes (FractionRing.algEquiv A K) (FractionRing.algEquiv B L) _

@[simp]

Depends on / 依赖: AlgEquiv, AlgEquiv.commutes, Algebra, Algebra.intNorm, Algebra.map_intNormAux, Algebra.norm_eq_of_equiv_equiv, FractionRing, FractionRing.algEquiv, IsFractionRing, IsFractionRing.algEquiv_commutes, IsIntegralClosure, IsIntegralClosure.isFractionRing_of_finite_extension, algEquiv, algEquiv_commutes, commutes, injective, intNorm, isFractionRing_of_finite_extension, map_intNormAux, norm_eq_of_equiv_equiv
-/
lemma Algebra.algebraMap_intNorm (x : B) :
    algebraMap A K (Algebra.intNorm A B x) = Algebra.norm K (algebraMap B L x) := by
  have := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  apply (FractionRing.algEquiv A K).symm.injective
  rw [AlgEquiv.commutes]; rw [Algebra.intNorm]; rw [Algebra.map_intNormAux]; rw [← AlgEquiv.commutes (FractionRing.algEquiv B L)]
  apply Algebra.norm_eq_of_equiv_equiv (FractionRing.algEquiv A K).toRingEquiv
    (FractionRing.algEquiv B L).toRingEquiv
  ext
  exact IsFractionRing.algEquiv_commutes (FractionRing.algEquiv A K) (FractionRing.algEquiv B L) _

@[simp]
/--
lemma `Algebra.algebraMap_intNorm_fractionRing` / 引理 `Algebra.algebraMap_intNorm_fractionRing`

English:
lemma Algebra.algebraMap_intNorm_fractionRing
  given: (x : B)
  proof: Algebra.map_intNormAux x

中文:
引理 代数.algebraMap_intNorm_fractionRing
  条件: (x : B)
  证明: Algebra.map_intNormAux x

Depends on / 依赖: Algebra, Algebra.map_intNormAux, map_intNormAux
-/
lemma Algebra.algebraMap_intNorm_fractionRing (x : B) :
    algebraMap A (FractionRing A) (Algebra.intNorm A B x) =
      Algebra.norm (FractionRing A) (algebraMap B (FractionRing B) x) :=
  Algebra.map_intNormAux x

variable (A B)

/--
theorem `Algebra.intNorm_intNorm` / 定理 `Algebra.intNorm_intNorm`

English:
theorem Algebra.intNorm_intNorm
  statement: {C : Type*} [CommRing C] [IsDomain C] [IsIntegrallyClosed C]
  proof: by
  apply FaithfulSMul.algebraMap_injective A (FractionRing A)
  rw [algebraMap_intNorm_fractionRing]; rw [algebraMap_intNorm_fractionRing]; rw [algebraMap_intNorm_fractionRing]; rw [Algebra.norm_norm]

中文:
定理 代数.intNorm_intNorm
  结论: {C : 类型} [交换环 C] [是整环 C] [是整闭 C]
  证明: by
  apply FaithfulSMul.algebraMap_injective A (FractionRing A)
  rw [algebraMap_intNorm_fractionRing]; rw [algebraMap_intNorm_fractionRing]; rw [algebraMap_intNorm_fractionRing]; rw [Algebra.norm_norm]

Depends on / 依赖: Algebra, Algebra.norm_norm, FaithfulSMul, FaithfulSMul.algebraMap_injective, FractionRing, algebraMap_injective, algebraMap_intNorm_fractionRing, norm_norm
-/
theorem Algebra.intNorm_intNorm {C : Type*} [CommRing C] [IsDomain C] [IsIntegrallyClosed C]
    [Algebra A C] [Algebra B C] [IsScalarTower A B C] [Algebra.IsIntegral A C]
    [Algebra.IsIntegral B C] [IsTorsionFree A C] [IsTorsionFree B C] (x : C) :
    intNorm A B (intNorm B C x) = intNorm A C x := by
  apply FaithfulSMul.algebraMap_injective A (FractionRing A)
  rw [algebraMap_intNorm_fractionRing]; rw [algebraMap_intNorm_fractionRing]; rw [algebraMap_intNorm_fractionRing]; rw [Algebra.norm_norm]

/--
lemma `Algebra.intNorm_eq_norm` / 引理 `Algebra.intNorm_eq_norm`

English:
lemma Algebra.intNorm_eq_norm
  given: [Module.Free A B] [Module.Finite A B]
  proof: by
  ext x
  have : IsIntegralClosure B A (FractionRing B) :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  apply IsFractionRing.injective A (FractionRing A)
  rw [Algebra.algebraMap_intNorm_fractionRing]; rw [Algebra.norm_localization A A⁰]

@[simp]

中文:
引理 代数.intNorm_eq_norm
  条件: [模.自由 A B] [模.有限 A B]
  证明: by
  ext x
  have : IsIntegralClosure B A (FractionRing B) :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  apply IsFractionRing.injective A (FractionRing A)
  rw [Algebra.algebraMap_intNorm_fractionRing]; rw [Algebra.norm_localization A A⁰]

@[simp]

Depends on / 依赖: Algebra, Algebra.algebraMap_intNorm_fractionRing, Algebra.norm_localization, FractionRing, IsFractionRing, IsFractionRing.injective, IsIntegralClosure, IsIntegralClosure.of_isIntegrallyClosed, algebraMap_intNorm_fractionRing, injective, norm_localization, of_isIntegrallyClosed
-/
lemma Algebra.intNorm_eq_norm [Module.Free A B] [Module.Finite A B] :
    Algebra.intNorm A B = Algebra.norm A := by
  ext x
  have : IsIntegralClosure B A (FractionRing B) :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  apply IsFractionRing.injective A (FractionRing A)
  rw [Algebra.algebraMap_intNorm_fractionRing]; rw [Algebra.norm_localization A A⁰]

@[simp]
/--
lemma `Algebra.intNorm_zero` / 引理 `Algebra.intNorm_zero`

English:
lemma Algebra.intNorm_zero
  given: [FiniteDimensional (FractionRing A) (FractionRing B)]
  proof: by
  have : IsIntegralClosure B A (FractionRing B) :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  apply IsFractionRing.injective A (FractionRing A)
  simp

中文:
引理 代数.intNorm_zero
  条件: [有限维 (FractionRing A) (FractionRing B)]
  证明: by
  have : IsIntegralClosure B A (FractionRing B) :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  apply IsFractionRing.injective A (FractionRing A)
  simp

Depends on / 依赖: FractionRing, IsFractionRing, IsFractionRing.injective, IsIntegralClosure, IsIntegralClosure.of_isIntegrallyClosed, injective, of_isIntegrallyClosed
-/
lemma Algebra.intNorm_zero [FiniteDimensional (FractionRing A) (FractionRing B)] :
    Algebra.intNorm A B 0 = 0 := by
  have : IsIntegralClosure B A (FractionRing B) :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  apply IsFractionRing.injective A (FractionRing A)
  simp

variable {A B}

attribute [local instance] FractionRing.liftAlgebra

@[simp]
/--
theorem `Algebra.intNorm_map_algEquiv` / 定理 `Algebra.intNorm_map_algEquiv`

English:
theorem Algebra.intNorm_map_algEquiv
  statement: [IsDomain B₂] [IsIntegrallyClosed B₂] [Algebra.IsIntegral A B₂]
  proof: by
  apply FaithfulSMul.algebraMap_injective A (FractionRing A)
  rw [algebraMap_intNorm_fractionRing]; rw [algebraMap_intNorm_fractionRing]; rw [← galLiftEquiv_algebraMap_apply (FractionRing A) (FractionRing B)]; rw [norm_eq_of_algEquiv]

@[simp]

中文:
定理 代数.intNorm_map_algEquiv
  结论: [是整环 B₂] [是整闭 B₂] [代数.是整 A B₂]
  证明: by
  apply FaithfulSMul.algebraMap_injective A (FractionRing A)
  rw [algebraMap_intNorm_fractionRing]; rw [algebraMap_intNorm_fractionRing]; rw [← galLiftEquiv_algebraMap_apply (FractionRing A) (FractionRing B)]; rw [norm_eq_of_algEquiv]

@[simp]

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, FractionRing, algebraMap_injective, algebraMap_intNorm_fractionRing, galLiftEquiv_algebraMap_apply, norm_eq_of_algEquiv
-/
theorem Algebra.intNorm_map_algEquiv [IsDomain B₂] [IsIntegrallyClosed B₂] [Algebra.IsIntegral A B₂]
    [IsTorsionFree A B₂] [Algebra.IsAlgebraic (FractionRing A) (FractionRing B)]
    [Algebra.IsAlgebraic (FractionRing A) (FractionRing B₂)]
    (x : B) (σ : B ≃ₐ[A] B₂) :
    Algebra.intNorm A B₂ (σ x) = Algebra.intNorm A B x := by
  apply FaithfulSMul.algebraMap_injective A (FractionRing A)
  rw [algebraMap_intNorm_fractionRing]; rw [algebraMap_intNorm_fractionRing]; rw [← galLiftEquiv_algebraMap_apply (FractionRing A) (FractionRing B)]; rw [norm_eq_of_algEquiv]

@[simp]
/--
lemma `Algebra.intNorm_eq_zero` / 引理 `Algebra.intNorm_eq_zero`

English:
lemma Algebra.intNorm_eq_zero
  given: [FiniteDimensional (FractionRing A) (FractionRing B)] {x : B}
  proof: by
  rw [← (IsFractionRing.injective A (FractionRing A)).eq_iff]; rw [← (IsFractionRing.injective B (FractionRing B)).eq_iff]
  simp only [algebraMap_intNorm_fractionRing, map_zero, norm_eq_zero_iff]

中文:
引理 代数.intNorm_eq_zero
  条件: [有限维 (FractionRing A) (FractionRing B)] {x : B}
  证明: by
  rw [← (IsFractionRing.injective A (FractionRing A)).eq_iff]; rw [← (IsFractionRing.injective B (FractionRing B)).eq_iff]
  simp only [algebraMap_intNorm_fractionRing, map_zero, norm_eq_zero_iff]

Depends on / 依赖: FractionRing, IsFractionRing, IsFractionRing.injective, algebraMap_intNorm_fractionRing, eq_iff, injective, map_zero, norm_eq_zero_iff
-/
lemma Algebra.intNorm_eq_zero [FiniteDimensional (FractionRing A) (FractionRing B)] {x : B} :
    Algebra.intNorm A B x = 0 ↔ x = 0 := by
  rw [← (IsFractionRing.injective A (FractionRing A)).eq_iff]; rw [← (IsFractionRing.injective B (FractionRing B)).eq_iff]
  simp only [algebraMap_intNorm_fractionRing, map_zero, norm_eq_zero_iff]

/--
lemma `Algebra.intNorm_ne_zero` / 引理 `Algebra.intNorm_ne_zero`

English:
lemma Algebra.intNorm_ne_zero
  given: [FiniteDimensional (FractionRing A) (FractionRing B)] {x : B}
  proof: by simp

中文:
引理 代数.intNorm_ne_zero
  条件: [有限维 (FractionRing A) (FractionRing B)] {x : B}
  证明: by simp
-/
lemma Algebra.intNorm_ne_zero [FiniteDimensional (FractionRing A) (FractionRing B)] {x : B} :
    Algebra.intNorm A B x != 0 ↔ x != 0 := by simp

variable [IsDomain Aₘ] [IsIntegrallyClosed Aₘ] [IsDomain Bₘ] [IsIntegrallyClosed Bₘ]
variable [IsTorsionFree Aₘ Bₘ] [Algebra.IsIntegral Aₘ Bₘ]

set_option backward.isDefEq.respectTransparency.types false in
include M in
/--
lemma `Algebra.intNorm_eq_of_isLocalization` / 引理 `Algebra.intNorm_eq_of_isLocalization`

English:
lemma Algebra.intNorm_eq_of_isLocalization
  statement: [FiniteDimensional (FractionRing A) (FractionRing B)]
  proof: by
  by_cases hM : 0 in M
  · subsingleton [IsLocalization.uniqueOfZeroMem (S := Aₘ) hM]
  replace hM : M <= A⁰ := fun x hx => mem_nonZeroDivisors_iff_ne_zero.mpr (fun e => hM (e ▸ hx))
  let K := FractionRing A
  let L := FractionRing B
  let f : Aₘ ->+* K := IsLocalization.map _ (T := A⁰) (RingHom.id A) hM
  let := f.toAlgebra
  have : IsScalarTower A Aₘ K := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, RingHomCompTriple.comp_eq])
  let := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M Aₘ K
  let g : Bₘ ->+* L := IsLocalization.map _
      (M := algebraMapSubmonoid B M) (T := algebraMapSubmonoid B A⁰)
      (RingHom.id B) (Submonoid.monotone_map hM)
  let := g.toAlgebra
  have : IsScalarTower B Bₘ L := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, RingHomCompTriple.comp_eq])
  let := ((algebraMap K L).comp f).toAlgebra
  have : IsScalarTower Aₘ K L := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Aₘ Bₘ L := by
    apply IsScalarTower.of_algebraMap_eq'
    apply IsLocalization.ringHom_ext M
    rw [RingHom.algebraMap_toAlgebra]; rw [RingHom.algebraMap_toAlgebra (R := Bₘ)]; rw [RingHom.comp_assoc]; rw [RingHom.comp_assoc]; rw [← IsScalarTower.algebraMap_eq]; rw [IsScalarTower.algebraMap_eq A B Bₘ]; rw [IsLocalization.map_comp]; rw [RingHom.comp_id]; rw [← RingHom.comp_assoc]; rw [IsLocalization.map_comp]; rw [RingHom.comp_id]; rw [← IsScalarTower.algebraMap_eq]; rw [← IsScalarTower.algebraMap_eq]
  let := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (algebraMapSubmonoid B M) Bₘ L
  have : IsIntegralClosure Bₘ Aₘ L :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  apply IsFractionRing.injective Aₘ K
  rw [← IsScalarTower.algebraMap_apply]; rw [Algebra.algebraMap_intNorm_fractionRing]; rw [Algebra.algebraMap_intNorm (L := L)]; rw [← IsScalarTower.algebraMap_apply]

中文:
引理 代数.intNorm_eq_of_isLocalization
  结论: [有限维 (FractionRing A) (FractionRing B)]
  证明: by
  by_cases hM : 0 in M
  · subsingleton [IsLocalization.uniqueOfZeroMem (S := Aₘ) hM]
  replace hM : M <= A⁰ := fun x hx => mem_nonZeroDivisors_iff_ne_zero.mpr (fun e => hM (e ▸ hx))
  let K := FractionRing A
  let L := FractionRing B
  let f : Aₘ ->+* K := IsLocalization.map _ (T := A⁰) (RingHom.id A) hM
  let := f.toAlgebra
  have : IsScalarTower A Aₘ K := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, RingHomCompTriple.comp_eq])
  let := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M Aₘ K
  let g : Bₘ ->+* L := IsLocalization.map _
      (M := algebraMapSubmonoid B M) (T := algebraMapSubmonoid B A⁰)
      (RingHom.id B) (Submonoid.monotone_map hM)
  let := g.toAlgebra
  have : IsScalarTower B Bₘ L := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, RingHomCompTriple.comp_eq])
  let := ((algebraMap K L).comp f).toAlgebra
  have : IsScalarTower Aₘ K L := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Aₘ Bₘ L := by
    apply IsScalarTower.of_algebraMap_eq'
    apply IsLocalization.ringHom_ext M
    rw [RingHom.algebraMap_toAlgebra]; rw [RingHom.algebraMap_toAlgebra (R := Bₘ)]; rw [RingHom.comp_assoc]; rw [RingHom.comp_assoc]; rw [← IsScalarTower.algebraMap_eq]; rw [IsScalarTower.algebraMap_eq A B Bₘ]; rw [IsLocalization.map_comp]; rw [RingHom.comp_id]; rw [← RingHom.comp_assoc]; rw [IsLocalization.map_comp]; rw [RingHom.comp_id]; rw [← IsScalarTower.algebraMap_eq]; rw [← IsScalarTower.algebraMap_eq]
  let := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (algebraMapSubmonoid B M) Bₘ L
  have : IsIntegralClosure Bₘ Aₘ L :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  apply IsFractionRing.injective Aₘ K
  rw [← IsScalarTower.algebraMap_apply]; rw [Algebra.algebraMap_intNorm_fractionRing]; rw [Algebra.algebraMap_intNorm (L := L)]; rw [← IsScalarTower.algebraMap_apply]

Depends on / 依赖: FractionRing, IsFractionRing, IsFractionRing.isFract, IsLocalization, IsLocalization.map, IsLocalization.map_comp, IsLocalization.uniqueOfZeroMem, IsScalarTower, IsScalarTower.of_algebraMap_eq, RingHom, RingHom.algebraMap_toAlgebra, RingHom.id, RingHomCompTriple, RingHomCompTriple.comp_eq, algebraMap_toAlgebra, comp_eq, f.toAlgebra, isFract, map_comp, mem_nonZeroDivisors_iff_ne_zero
-/
lemma Algebra.intNorm_eq_of_isLocalization [FiniteDimensional (FractionRing A) (FractionRing B)]
    (x : B) :
    algebraMap A Aₘ (Algebra.intNorm A B x) = Algebra.intNorm Aₘ Bₘ (algebraMap B Bₘ x) := by
  by_cases hM : 0 in M
  · subsingleton [IsLocalization.uniqueOfZeroMem (S := Aₘ) hM]
  replace hM : M <= A⁰ := fun x hx => mem_nonZeroDivisors_iff_ne_zero.mpr (fun e => hM (e ▸ hx))
  let K := FractionRing A
  let L := FractionRing B
  let f : Aₘ ->+* K := IsLocalization.map _ (T := A⁰) (RingHom.id A) hM
  let := f.toAlgebra
  have : IsScalarTower A Aₘ K := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, RingHomCompTriple.comp_eq])
  let := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M Aₘ K
  let g : Bₘ ->+* L := IsLocalization.map _
      (M := algebraMapSubmonoid B M) (T := algebraMapSubmonoid B A⁰)
      (RingHom.id B) (Submonoid.monotone_map hM)
  let := g.toAlgebra
  have : IsScalarTower B Bₘ L := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, RingHomCompTriple.comp_eq])
  let := ((algebraMap K L).comp f).toAlgebra
  have : IsScalarTower Aₘ K L := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Aₘ Bₘ L := by
    apply IsScalarTower.of_algebraMap_eq'
    apply IsLocalization.ringHom_ext M
    rw [RingHom.algebraMap_toAlgebra]; rw [RingHom.algebraMap_toAlgebra (R := Bₘ)]; rw [RingHom.comp_assoc]; rw [RingHom.comp_assoc]; rw [← IsScalarTower.algebraMap_eq]; rw [IsScalarTower.algebraMap_eq A B Bₘ]; rw [IsLocalization.map_comp]; rw [RingHom.comp_id]; rw [← RingHom.comp_assoc]; rw [IsLocalization.map_comp]; rw [RingHom.comp_id]; rw [← IsScalarTower.algebraMap_eq]; rw [← IsScalarTower.algebraMap_eq]
  let := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (algebraMapSubmonoid B M) Bₘ L
  have : IsIntegralClosure Bₘ Aₘ L :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  apply IsFractionRing.injective Aₘ K
  rw [← IsScalarTower.algebraMap_apply]; rw [Algebra.algebraMap_intNorm_fractionRing]; rw [Algebra.algebraMap_intNorm (L := L)]; rw [← IsScalarTower.algebraMap_apply]

end norm

variable [IsDomain A] [IsIntegrallyClosed A] [IsDomain B] [IsIntegrallyClosed B]
  [Module.Finite A B] [IsTorsionFree A B]

/--
lemma `Algebra.algebraMap_intNorm_of_isGalois` / 引理 `Algebra.algebraMap_intNorm_of_isGalois`

English:
lemma Algebra.algebraMap_intNorm_of_isGalois
  given: [IsGalois (FractionRing A) (FractionRing B)] {x : B}
  proof: by
  have : FiniteDimensional (FractionRing A) (FractionRing B) := .of_isLocalization A B A⁰
  rw [← (galRestrict A (FractionRing A) (FractionRing B) B).toEquiv.prod_comp]
  simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
  convert! (prod_galRestrict_eq_norm A (FractionRing A) (FractionRing B) B x).symm

中文:
引理 代数.algebraMap_intNorm_of_isGalois
  条件: [是Galois (FractionRing A) (FractionRing B)] {x : B}
  证明: by
  have : FiniteDimensional (FractionRing A) (FractionRing B) := .of_isLocalization A B A⁰
  rw [← (galRestrict A (FractionRing A) (FractionRing B) B).toEquiv.prod_comp]
  simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
  convert! (prod_galRestrict_eq_norm A (FractionRing A) (FractionRing B) B x).symm

Depends on / 依赖: EquivLike, EquivLike.coe_coe, FiniteDimensional, FractionRing, MulEquiv, MulEquiv.toEquiv_eq_coe, coe_coe, convert, galRestrict, of_isLocalization, prod_comp, prod_galRestrict_eq_norm, toEquiv, toEquiv.prod_comp, toEquiv_eq_coe
-/
lemma Algebra.algebraMap_intNorm_of_isGalois [IsGalois (FractionRing A) (FractionRing B)] {x : B} :
    algebraMap A B (Algebra.intNorm A B x) = ∏ σ : B ≃ₐ[A] B, σ x := by
  have : FiniteDimensional (FractionRing A) (FractionRing B) := .of_isLocalization A B A⁰
  rw [← (galRestrict A (FractionRing A) (FractionRing B) B).toEquiv.prod_comp]
  simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
  convert! (prod_galRestrict_eq_norm A (FractionRing A) (FractionRing B) B x).symm

open Polynomial IsScalarTower in
/--
theorem `Algebra.dvd_algebraMap_intNorm_self` / 定理 `Algebra.dvd_algebraMap_intNorm_self`

English:
theorem Algebra.dvd_algebraMap_intNorm_self
  given: (x : B)
  statement: x ∣ algebraMap A B (intNorm A B x)
  proof: by
  classical
  have : FiniteDimensional (FractionRing A) (FractionRing B) := .of_isLocalization A B A⁰
  by_cases hx : x = 0
  · exact ⟨1, by simp [hx]⟩
  let K := FractionRing A
  let L := FractionRing B
  let E := AlgebraicClosure L
  suffices IsIntegral A ((algebraMap B L x)⁻¹ * (algebraMap A L (intNorm A B x))) by
obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp
      _root_.IsIntegral.tower_top (A := B) this
    refine ⟨y, ?_⟩
    apply FaithfulSMul.algebraMap_injective B L
    rw [← algebraMap_apply]; rw [map_mul]; rw [hy]; rw [mul_inv_cancel_left₀]
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective B L)).mpr hx
  rw [← isIntegral_algHom_iff (toAlgHom A L E)
    (FaithfulSMul.algebraMap_injective L E)]; rw [coe_toAlgHom']; rw [map_mul]; rw [map_inv₀]; rw [algebraMap_apply A K L]; rw [algebraMap_intNorm (L := L)]; rw [← algebraMap_apply]; rw [← algebraMap_apply]; rw [norm_eq_prod_roots _ (IsAlgClosed.splits _)]; rw [← Multiset.prod_erase
    (a := algebraMap B E x)]
  · have := IsTorsionFree.trans_faithfulSMul B L E
    rw [mul_pow]; rw [← mul_pow_sub_one (Nat.pos_iff_ne_zero.1 Module.finrank_pos) (algebraMap B E x)]; rw [mul_assoc]; rw [inv_mul_cancel_left₀]
    · refine IsIntegral.mul (IsIntegral.pow ?_ _)
        (IsIntegral.pow (IsIntegral.multiset_prod (fun a ha => ⟨minpoly A x, minpoly.monic
          (IsIntegral.isIntegral x), ?_⟩)) _)
      · exact (isIntegral_algebraMap_iff (isTorsionFree_iff_algebraMap_injective.1 this)).mpr
          (IsIntegral.isIntegral x)
      · replace ha := Multiset.erase_subset _ _ ha
        suffices (aeval a) ((minpoly A x).map (algebraMap A K)) = 0 by simpa
        rw [← minpoly.isIntegrallyClosed_eq_field_fractions K L (IsIntegral.isIntegral x)]
        simp only [mem_roots', ne_eq, Polynomial.map_eq_zero, IsRoot.def, eval_map_algebraMap] at ha
        exact ha.2
    · exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective B E)).mpr hx
  · simp only [mem_roots', ne_eq, Polynomial.map_eq_zero, IsRoot.def, eval_map_algebraMap]
    refine ⟨minpoly.ne_zero (IsIntegral.isIntegral _), ?_⟩
    simp [algebraMap_apply B L E, aeval_algebraMap_apply]

中文:
定理 代数.dvd_algebraMap_intNorm_self
  条件: (x : B)
  结论: x ∣ algebraMap A B (intNorm A B x)
  证明: by
  classical
  have : FiniteDimensional (FractionRing A) (FractionRing B) := .of_isLocalization A B A⁰
  by_cases hx : x = 0
  · exact ⟨1, by simp [hx]⟩
  let K := FractionRing A
  let L := FractionRing B
  let E := AlgebraicClosure L
  suffices IsIntegral A ((algebraMap B L x)⁻¹ * (algebraMap A L (intNorm A B x))) by
obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp
      _root_.IsIntegral.tower_top (A := B) this
    refine ⟨y, ?_⟩
    apply FaithfulSMul.algebraMap_injective B L
    rw [← algebraMap_apply]; rw [map_mul]; rw [hy]; rw [mul_inv_cancel_left₀]
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective B L)).mpr hx
  rw [← isIntegral_algHom_iff (toAlgHom A L E)
    (FaithfulSMul.algebraMap_injective L E)]; rw [coe_toAlgHom']; rw [map_mul]; rw [map_inv₀]; rw [algebraMap_apply A K L]; rw [algebraMap_intNorm (L := L)]; rw [← algebraMap_apply]; rw [← algebraMap_apply]; rw [norm_eq_prod_roots _ (IsAlgClosed.splits _)]; rw [← Multiset.prod_erase
    (a := algebraMap B E x)]
  · have := IsTorsionFree.trans_faithfulSMul B L E
    rw [mul_pow]; rw [← mul_pow_sub_one (Nat.pos_iff_ne_zero.1 Module.finrank_pos) (algebraMap B E x)]; rw [mul_assoc]; rw [inv_mul_cancel_left₀]
    · refine IsIntegral.mul (IsIntegral.pow ?_ _)
        (IsIntegral.pow (IsIntegral.multiset_prod (fun a ha => ⟨minpoly A x, minpoly.monic
          (IsIntegral.isIntegral x), ?_⟩)) _)
      · exact (isIntegral_algebraMap_iff (isTorsionFree_iff_algebraMap_injective.1 this)).mpr
          (IsIntegral.isIntegral x)
      · replace ha := Multiset.erase_subset _ _ ha
        suffices (aeval a) ((minpoly A x).map (algebraMap A K)) = 0 by simpa
        rw [← minpoly.isIntegrallyClosed_eq_field_fractions K L (IsIntegral.isIntegral x)]
        simp only [mem_roots', ne_eq, Polynomial.map_eq_zero, IsRoot.def, eval_map_algebraMap] at ha
        exact ha.2
    · exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective B E)).mpr hx
  · simp only [mem_roots', ne_eq, Polynomial.map_eq_zero, IsRoot.def, eval_map_algebraMap]
    refine ⟨minpoly.ne_zero (IsIntegral.isIntegral _), ?_⟩
    simp [algebraMap_apply B L E, aeval_algebraMap_apply]

Depends on / 依赖: AlgebraicClosure, FaithfulSMul, FaithfulSMul.algebraMap_injective, FiniteDimensional, FractionRing, IsIntegral, IsIntegrallyClosed, IsIntegrallyClosed.isIntegral_iff.mp, _root_, _root_.IsIntegral.tower_top, algebraMap, algebraMap_apply, algebraMap_injective, classical, intNorm, isIntegral_iff, map_mul, of_isLocalization, tower_top
-/
theorem Algebra.dvd_algebraMap_intNorm_self (x : B) : x ∣ algebraMap A B (intNorm A B x) := by
  classical
  have : FiniteDimensional (FractionRing A) (FractionRing B) := .of_isLocalization A B A⁰
  by_cases hx : x = 0
  · exact ⟨1, by simp [hx]⟩
  let K := FractionRing A
  let L := FractionRing B
  let E := AlgebraicClosure L
  suffices IsIntegral A ((algebraMap B L x)⁻¹ * (algebraMap A L (intNorm A B x))) by
obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp
      _root_.IsIntegral.tower_top (A := B) this
    refine ⟨y, ?_⟩
    apply FaithfulSMul.algebraMap_injective B L
    rw [← algebraMap_apply]; rw [map_mul]; rw [hy]; rw [mul_inv_cancel_left₀]
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective B L)).mpr hx
  rw [← isIntegral_algHom_iff (toAlgHom A L E)
    (FaithfulSMul.algebraMap_injective L E)]; rw [coe_toAlgHom']; rw [map_mul]; rw [map_inv₀]; rw [algebraMap_apply A K L]; rw [algebraMap_intNorm (L := L)]; rw [← algebraMap_apply]; rw [← algebraMap_apply]; rw [norm_eq_prod_roots _ (IsAlgClosed.splits _)]; rw [← Multiset.prod_erase
    (a := algebraMap B E x)]
  · have := IsTorsionFree.trans_faithfulSMul B L E
    rw [mul_pow]; rw [← mul_pow_sub_one (Nat.pos_iff_ne_zero.1 Module.finrank_pos) (algebraMap B E x)]; rw [mul_assoc]; rw [inv_mul_cancel_left₀]
    · refine IsIntegral.mul (IsIntegral.pow ?_ _)
        (IsIntegral.pow (IsIntegral.multiset_prod (fun a ha => ⟨minpoly A x, minpoly.monic
          (IsIntegral.isIntegral x), ?_⟩)) _)
      · exact (isIntegral_algebraMap_iff (isTorsionFree_iff_algebraMap_injective.1 this)).mpr
          (IsIntegral.isIntegral x)
      · replace ha := Multiset.erase_subset _ _ ha
        suffices (aeval a) ((minpoly A x).map (algebraMap A K)) = 0 by simpa
        rw [← minpoly.isIntegrallyClosed_eq_field_fractions K L (IsIntegral.isIntegral x)]
        simp only [mem_roots', ne_eq, Polynomial.map_eq_zero, IsRoot.def, eval_map_algebraMap] at ha
        exact ha.2
    · exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective B E)).mpr hx
  · simp only [mem_roots', ne_eq, Polynomial.map_eq_zero, IsRoot.def, eval_map_algebraMap]
    refine ⟨minpoly.ne_zero (IsIntegral.isIntegral _), ?_⟩
    simp [algebraMap_apply B L E, aeval_algebraMap_apply]
