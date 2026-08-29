/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Jujian Zhang
-/
module

public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Module

/-!
# Localized Module

Given a commutative semiring `R`, a multiplicative subset `S ⊆ R` and an `R`-module `M`, we can
localize `M` by `S`. This gives us a `Localization S`-module.

## Main definition

* `isLocalizedModule_iff_isBaseChange` : A localization of modules corresponds to a base change.
-/

@[expose] public section

variable {R : Type*} [CommSemiring R] (S : Submonoid R)
  (A : Type*) [CommSemiring A] [Algebra R A] [IsLocalization S A]
  {M : Type*} [AddCommMonoid M] [Module R M]
  {M' : Type*} [AddCommMonoid M'] [Module R M'] [Module A M'] [IsScalarTower R A M']
  (f : M ->ₗ[R] M')

/--
theorem `IsLocalizedModule.isBaseChange` / 定理 `IsLocalizedModule.isBaseChange`

English:
theorem IsLocalizedModule.isBaseChange
  given: [IsLocalizedModule S f]
  statement: IsBaseChange A f
  proof: .of_lift_unique _ fun Q _ _ _ _ g => by
    obtain ⟨ℓ, rfl, h₂⟩ := IsLocalizedModule.is_universal S f g fun s => by
      rw [← (Algebra.lsmul R (A := A) R Q).commutes]; exact (IsLocalization.map_units A s).map _
    refine ⟨ℓ.extendScalarsOfIsLocalization S A, by simp, fun g'' h => ?_⟩
    cases h₂ (LinearMap.restrictScalars R g'') h; rfl

中文:
定理 是Localized模.isBaseChange
  条件: [是Localized模 S f]
  结论: IsBaseChange A f
  证明: .of_lift_unique _ fun Q _ _ _ _ g => by
    obtain ⟨ℓ, rfl, h₂⟩ := IsLocalizedModule.is_universal S f g fun s => by
      rw [← (Algebra.lsmul R (A := A) R Q).commutes]; exact (IsLocalization.map_units A s).map _
    refine ⟨ℓ.extendScalarsOfIsLocalization S A, by simp, fun g'' h => ?_⟩
    cases h₂ (LinearMap.restrictScalars R g'') h; rfl

Depends on / 依赖: Algebra, Algebra.lsmul, IsLocalization, IsLocalization.map_units, IsLocalizedModule, IsLocalizedModule.is_universal, LinearMap, LinearMap.restrictScalars, commutes, extendScalarsOfIsLocalization, is_universal, map_units, of_lift_unique, restrictScalars
-/
theorem IsLocalizedModule.isBaseChange [IsLocalizedModule S f] : IsBaseChange A f :=
  .of_lift_unique _ fun Q _ _ _ _ g => by
    obtain ⟨ℓ, rfl, h₂⟩ := IsLocalizedModule.is_universal S f g fun s => by
      rw [← (Algebra.lsmul R (A := A) R Q).commutes]; exact (IsLocalization.map_units A s).map _
    refine ⟨ℓ.extendScalarsOfIsLocalization S A, by simp, fun g'' h => ?_⟩
    cases h₂ (LinearMap.restrictScalars R g'') h; rfl

variable (M) in
/--
lemma `LocalizedModule.isBaseChange` / 引理 `LocalizedModule.isBaseChange`

English:
lemma LocalizedModule.isBaseChange
  proof: IsLocalizedModule.isBaseChange S (Localization S) (LocalizedModule.mkLinearMap S M)

中文:
引理 LocalizedModule.isBaseChange
  证明: IsLocalizedModule.isBaseChange S (Localization S) (LocalizedModule.mkLinearMap S M)

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.isBaseChange, Localization, LocalizedModule, LocalizedModule.mkLinearMap, isBaseChange, mkLinearMap
-/
lemma LocalizedModule.isBaseChange :
    IsBaseChange (Localization S) (LocalizedModule.mkLinearMap S M) :=
  IsLocalizedModule.isBaseChange S (Localization S) (LocalizedModule.mkLinearMap S M)

/--
theorem `isLocalizedModule_iff_isBaseChange` / 定理 `isLocalizedModule_iff_isBaseChange`

English:
theorem isLocalizedModule_iff_isBaseChange
  statement: IsLocalizedModule S f ↔ IsBaseChange A f
  proof: by
  refine ⟨fun _ => IsLocalizedModule.isBaseChange S A f, fun h => ?_⟩
  let : Module A (LocalizedModule S M) := LocalizedModule.moduleOfIsLocalization ..
  have : IsBaseChange A (LocalizedModule.mkLinearMap S M) := IsLocalizedModule.isBaseChange S A _
  let e := (this.equiv.symm.trans h.equiv).restrictScalars R
  convert! IsLocalizedModule.of_linearEquiv S (LocalizedModule.mkLinearMap S M) e
  ext
  rw [LinearMap.coe_comp]; rw [LinearEquiv.coe_coe]; rw [Function.comp_apply]; rw [LinearEquiv.restrictScalars_apply]; rw [LinearEquiv.trans_apply]; rw [IsBaseChange.equiv_symm_apply]; rw [IsBaseChange.equiv_tmul]; rw [one_smul]

中文:
定理 isLocalizedModule_iff_isBaseChange
  结论: 是Localized模 S f ↔ IsBaseChange A f
  证明: by
  refine ⟨fun _ => IsLocalizedModule.isBaseChange S A f, fun h => ?_⟩
  let : Module A (LocalizedModule S M) := LocalizedModule.moduleOfIsLocalization ..
  have : IsBaseChange A (LocalizedModule.mkLinearMap S M) := IsLocalizedModule.isBaseChange S A _
  let e := (this.equiv.symm.trans h.equiv).restrictScalars R
  convert! IsLocalizedModule.of_linearEquiv S (LocalizedModule.mkLinearMap S M) e
  ext
  rw [LinearMap.coe_comp]; rw [LinearEquiv.coe_coe]; rw [Function.comp_apply]; rw [LinearEquiv.restrictScalars_apply]; rw [LinearEquiv.trans_apply]; rw [IsBaseChange.equiv_symm_apply]; rw [IsBaseChange.equiv_tmul]; rw [one_smul]

Depends on / 依赖: Function, Function.comp_apply, IsBaseChange, IsLocalizedModule, IsLocalizedModule.isBaseChange, IsLocalizedModule.of_linearEquiv, LinearEquiv, LinearEquiv.coe_coe, LinearEquiv.restrictScalars, LinearMap, LinearMap.coe_comp, LocalizedModule, LocalizedModule.mkLinearMap, LocalizedModule.moduleOfIsLocalization, Module, coe_coe, coe_comp, comp_apply, convert, h.equiv
-/
theorem isLocalizedModule_iff_isBaseChange : IsLocalizedModule S f ↔ IsBaseChange A f := by
  refine ⟨fun _ => IsLocalizedModule.isBaseChange S A f, fun h => ?_⟩
  let : Module A (LocalizedModule S M) := LocalizedModule.moduleOfIsLocalization ..
  have : IsBaseChange A (LocalizedModule.mkLinearMap S M) := IsLocalizedModule.isBaseChange S A _
  let e := (this.equiv.symm.trans h.equiv).restrictScalars R
  convert! IsLocalizedModule.of_linearEquiv S (LocalizedModule.mkLinearMap S M) e
  ext
  rw [LinearMap.coe_comp]; rw [LinearEquiv.coe_coe]; rw [Function.comp_apply]; rw [LinearEquiv.restrictScalars_apply]; rw [LinearEquiv.trans_apply]; rw [IsBaseChange.equiv_symm_apply]; rw [IsBaseChange.equiv_tmul]; rw [one_smul]

open TensorProduct

variable (M) in
/--
Definition of `LocalizedModule.equivTensorProduct` / `LocalizedModule.equivTensorProduct` 的定义

English:
definition LocalizedModule.equivTensorProduct
  signature: :
  body: (LocalizedModule.isBaseChange S M).equiv.symm

@[simp]

中文:
定义 LocalizedModule.equivTensorProduct
  签名: :
  定义体: (LocalizedModule.isBaseChange S M).equiv.symm

@[simp]

Depends on / 依赖: LocalizedModule, LocalizedModule.isBaseChange, equiv.symm, isBaseChange
-/
noncomputable def LocalizedModule.equivTensorProduct :
    LocalizedModule S M ≃ₗ[Localization S] Localization S otimes[R] M :=
  (LocalizedModule.isBaseChange S M).equiv.symm

@[simp]
/--
lemma `LocalizedModule.equivTensorProduct_symm_apply_tmul` / 引理 `LocalizedModule.equivTensorProduct_symm_apply_tmul`

English:
lemma LocalizedModule.equivTensorProduct_symm_apply_tmul
  given: (x : M) (r : R) (s : S)
  proof: by
  simp [equivTensorProduct, IsBaseChange.equiv_tmul, mk_smul_mk, smul'_mk]

@[simp]

中文:
引理 LocalizedModule.equivTensorProduct_symm_apply_tmul
  条件: (x : M) (r : R) (s : S)
  证明: by
  simp [equivTensorProduct, IsBaseChange.equiv_tmul, mk_smul_mk, smul'_mk]

@[simp]

Depends on / 依赖: IsBaseChange, IsBaseChange.equiv_tmul, equivTensorProduct, equiv_tmul, mk_smul_mk
-/
lemma LocalizedModule.equivTensorProduct_symm_apply_tmul (x : M) (r : R) (s : S) :
    (equivTensorProduct S M).symm (Localization.mk r s otimesₜ[R] x) = r • mk x s := by
  simp [equivTensorProduct, IsBaseChange.equiv_tmul, mk_smul_mk, smul'_mk]

@[simp]
/--
lemma `LocalizedModule.equivTensorProduct_symm_apply_tmul_one` / 引理 `LocalizedModule.equivTensorProduct_symm_apply_tmul_one`

English:
lemma LocalizedModule.equivTensorProduct_symm_apply_tmul_one
  given: (x : M)
  proof: by
  simp [← Localization.mk_one]

@[simp]

中文:
引理 LocalizedModule.equivTensorProduct_symm_apply_tmul_one
  条件: (x : M)
  证明: by
  simp [← Localization.mk_one]

@[simp]

Depends on / 依赖: Localization, Localization.mk_one, mk_one
-/
lemma LocalizedModule.equivTensorProduct_symm_apply_tmul_one (x : M) :
    (equivTensorProduct S M).symm (1 otimesₜ[R] x) = mk x 1 := by
  simp [← Localization.mk_one]

@[simp]
/--
lemma `LocalizedModule.equivTensorProduct_apply_mk` / 引理 `LocalizedModule.equivTensorProduct_apply_mk`

English:
lemma LocalizedModule.equivTensorProduct_apply_mk
  given: (x : M) (s : S)
  proof: by
  apply (equivTensorProduct S M).symm.injective
  simp

中文:
引理 LocalizedModule.equivTensorProduct_apply_mk
  条件: (x : M) (s : S)
  证明: by
  apply (equivTensorProduct S M).symm.injective
  simp

Depends on / 依赖: equivTensorProduct, injective, symm.injective
-/
lemma LocalizedModule.equivTensorProduct_apply_mk (x : M) (s : S) :
    equivTensorProduct S M (mk x s) = Localization.mk 1 s otimesₜ[R] x := by
  apply (equivTensorProduct S M).symm.injective
  simp

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
instance {T : Type*} [CommSemiring T] [Algebra R T] :
    IsLocalizedModule S (IsScalarTower.toAlgHom R T (A otimes[R] T) : T ->ₗ[R] A otimes[R] T) := by
  rw [isLocalizedModule_iff_isBaseChange (S := S) (A := A)]
  exact TensorProduct.isBaseChange _ _ _

namespace IsLocalization

open TensorProduct Algebra.TensorProduct

/--
Instance `tensorProduct_isLocalizedModule` / 实例 `tensorProduct_isLocalizedModule`

English:
instance tensorProduct_isLocalizedModule
  signature: : IsLocalizedModule S (TensorProduct.mk R A M 1)
  body: (isLocalizedModule_iff_isBaseChange _ A _).mpr (TensorProduct.isBaseChange _ _ _)

中文:
实例 tensorProduct_isLocalizedModule
  签名: : 是Localized模 S (张量积.mk R A M 1)
  定义体: (isLocalizedModule_iff_isBaseChange _ A _).mpr (TensorProduct.isBaseChange _ _ _)

Depends on / 依赖: TensorProduct, TensorProduct.isBaseChange, isBaseChange, isLocalizedModule_iff_isBaseChange
-/
instance tensorProduct_isLocalizedModule : IsLocalizedModule S (TensorProduct.mk R A M 1) :=
  (isLocalizedModule_iff_isBaseChange _ A _).mpr (TensorProduct.isBaseChange _ _ _)

variable (M₁ M₂ B C) [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂]
  [Module A M₁] [Module A M₂] [IsScalarTower R A M₁] [IsScalarTower R A M₂]
  [Semiring B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
  [Semiring C] [Algebra R C] [Algebra A C] [IsScalarTower R A C]
include S

/--
theorem `tensorProduct_compatibleSMul` / 定理 `tensorProduct_compatibleSMul`

English:
theorem tensorProduct_compatibleSMul
  statement: CompatibleSMul R A M₁ M₂ where
  proof: by
    obtain ⟨r, s, rfl⟩ := exists_mk'_eq S a
    rw [← (map_units A s).smul_left_cancel]
    simp_rw [algebraMap_smul, smul_tmul', ← smul_assoc, smul_tmul, ← smul_assoc, smul_mk'_self,
      algebraMap_smul, smul_tmul]

中文:
定理 tensorProduct_compatibleSMul
  结论: 余mpatibleSMul R A M₁ M₂ where
  证明: by
    obtain ⟨r, s, rfl⟩ := exists_mk'_eq S a
    rw [← (map_units A s).smul_left_cancel]
    simp_rw [algebraMap_smul, smul_tmul', ← smul_assoc, smul_tmul, ← smul_assoc, smul_mk'_self,
      algebraMap_smul, smul_tmul]

Depends on / 依赖: _self, algebraMap_smul, exists_mk, map_units, simp_rw, smul_assoc, smul_left_cancel, smul_mk, smul_tmul
-/
theorem tensorProduct_compatibleSMul : CompatibleSMul R A M₁ M₂ where
  smul_tmul a _ _ := by
    obtain ⟨r, s, rfl⟩ := exists_mk'_eq S a
    rw [← (map_units A s).smul_left_cancel]
    simp_rw [algebraMap_smul, smul_tmul', ← smul_assoc, smul_tmul, ← smul_assoc, smul_mk'_self,
      algebraMap_smul, smul_tmul]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Module
  signature: (Localization S) M₁] [Module (Localization S) M₂]
  body: tensorProduct_compatibleSMul S ..

中文:
实例 [模
  签名: (Localization S) M₁] [模 (Localization S) M₂]
  定义体: tensorProduct_compatibleSMul S ..

Depends on / 依赖: Nonempty, asymptoticNhds_eq_smul_vadd, infer_instance, tensorProduct_compatibleSMul
-/
instance [Module (Localization S) M₁] [Module (Localization S) M₂]
    [IsScalarTower R (Localization S) M₁] [IsScalarTower R (Localization S) M₂] :
    CompatibleSMul R (Localization S) M₁ M₂ :=
  tensorProduct_compatibleSMul S ..

instance (N N') [AddCommMonoid N] [Module R N] [AddCommMonoid N'] [Module R N'] (g : N ->ₗ[R] N')
    [IsLocalizedModule S f] [IsLocalizedModule S g] :
    IsLocalizedModule S (TensorProduct.map f g) := by
  let eM := IsLocalizedModule.linearEquiv S f (TensorProduct.mk R (Localization S) M 1)
  let eN := IsLocalizedModule.linearEquiv S g (TensorProduct.mk R (Localization S) N 1)
  convert!
IsLocalizedModule.of_linearEquiv S (TensorProduct.mk R (Localization S) (M otimes[R] N) 1)
      (AlgebraTensorModule.distribBaseChange R (Localization S) ..).restrictScalars R ≪≫ₗ
        (congr eM eN ≪≫ₗ TensorProduct.equivOfCompatibleSMul ..).symm
  ext; congrm (?_ otimesₜ ?_) <;> simp [LinearEquiv.eq_symm_apply, eM, eN]

/--
Definition of `moduleTensorEquiv` / `moduleTensorEquiv` 的定义

English:
definition moduleTensorEquiv
  signature: : M₁ otimes[A] M₂ ≃ₗ[A] M₁ otimes[R] M₂
  body: have := tensorProduct_compatibleSMul S A M₁ M₂
  equivOfCompatibleSMul R A A M₁ M₂

中文:
定义 moduleTensorEquiv
  签名: : M₁ otimes[A] M₂ ≃ₗ[A] M₁ otimes[R] M₂
  定义体: have := tensorProduct_compatibleSMul S A M₁ M₂
  equivOfCompatibleSMul R A A M₁ M₂

Depends on / 依赖: equivOfCompatibleSMul, tensorProduct_compatibleSMul
-/
noncomputable def moduleTensorEquiv : M₁ otimes[A] M₂ ≃ₗ[A] M₁ otimes[R] M₂ :=
  have := tensorProduct_compatibleSMul S A M₁ M₂
  equivOfCompatibleSMul R A A M₁ M₂

/--
Definition of `moduleLid` / `moduleLid` 的定义

English:
definition moduleLid
  signature: : A otimes[R] M₁ ≃ₗ[A] M₁
  body: have := tensorProduct_compatibleSMul S A A M₁
  (equivOfCompatibleSMul R A A A M₁).symm ≪≫ₗ TensorProduct.lid _ _

中文:
定义 moduleLid
  签名: : A otimes[R] M₁ ≃ₗ[A] M₁
  定义体: have := tensorProduct_compatibleSMul S A A M₁
  (equivOfCompatibleSMul R A A A M₁).symm ≪≫ₗ TensorProduct.lid _ _

Depends on / 依赖: TensorProduct, TensorProduct.lid, equivOfCompatibleSMul, tensorProduct_compatibleSMul
-/
noncomputable def moduleLid : A otimes[R] M₁ ≃ₗ[A] M₁ :=
  have := tensorProduct_compatibleSMul S A A M₁
  (equivOfCompatibleSMul R A A A M₁).symm ≪≫ₗ TensorProduct.lid _ _

/--
Definition of `algebraTensorEquiv` / `algebraTensorEquiv` 的定义

English:
definition algebraTensorEquiv
  signature: : B otimes[A] C ≃ₐ[A] B otimes[R] C
  body: have := tensorProduct_compatibleSMul S A B C
  Algebra.TensorProduct.equivOfCompatibleSMul R A A B C

中文:
定义 algebraTensorEquiv
  签名: : B otimes[A] C ≃ₐ[A] B otimes[R] C
  定义体: have := tensorProduct_compatibleSMul S A B C
  Algebra.TensorProduct.equivOfCompatibleSMul R A A B C

Depends on / 依赖: Algebra, Algebra.TensorProduct.equivOfCompatibleSMul, TensorProduct, equivOfCompatibleSMul, tensorProduct_compatibleSMul
-/
noncomputable def algebraTensorEquiv : B otimes[A] C ≃ₐ[A] B otimes[R] C :=
  have := tensorProduct_compatibleSMul S A B C
  Algebra.TensorProduct.equivOfCompatibleSMul R A A B C

/--
Definition of `algebraLid` / `algebraLid` 的定义

English:
definition algebraLid
  signature: : A otimes[R] B ≃ₐ[A] B
  body: have := tensorProduct_compatibleSMul S A A B
  Algebra.TensorProduct.lidOfCompatibleSMul R A B

中文:
定义 algebraLid
  签名: : A otimes[R] B ≃ₐ[A] B
  定义体: have := tensorProduct_compatibleSMul S A A B
  Algebra.TensorProduct.lidOfCompatibleSMul R A B

Depends on / 依赖: Algebra, Algebra.TensorProduct.lidOfCompatibleSMul, TensorProduct, lidOfCompatibleSMul, tensorProduct_compatibleSMul
-/
noncomputable def algebraLid : A otimes[R] B ≃ₐ[A] B :=
  have := tensorProduct_compatibleSMul S A A B
  Algebra.TensorProduct.lidOfCompatibleSMul R A B

set_option linter.docPrime false in
/--
theorem `bijective_linearMap_mul'` / 定理 `bijective_linearMap_mul'`

English:
theorem bijective_linearMap_mul'
  statement: Function.Bijective (LinearMap.mul' R A)
  proof: have := tensorProduct_compatibleSMul S A A A
  (Algebra.TensorProduct.lmulEquiv R A).bijective

中文:
定理 bijective_linearMap_mul'
  结论: 函数.双射 (线性映射.mul' R A)
  证明: have := tensorProduct_compatibleSMul S A A A
  (Algebra.TensorProduct.lmulEquiv R A).bijective

Depends on / 依赖: Algebra, Algebra.TensorProduct.lmulEquiv, TensorProduct, bijective, lmulEquiv, tensorProduct_compatibleSMul
-/
theorem bijective_linearMap_mul' : Function.Bijective (LinearMap.mul' R A) :=
  have := tensorProduct_compatibleSMul S A A A
  (Algebra.TensorProduct.lmulEquiv R A).bijective

end IsLocalization

variable (T B : Type*) [CommSemiring T] [CommSemiring B]
  [Algebra R T] [Algebra T B] [Algebra R B] [Algebra A B] [IsScalarTower R T B]
  [IsScalarTower R A B]

variable {T B} in
/--
lemma `Algebra.isLocalization_iff_isPushout` / 引理 `Algebra.isLocalization_iff_isPushout`

English:
lemma Algebra.isLocalization_iff_isPushout
  proof: by
  rw [Algebra.IsPushout.comm]; rw [Algebra.isPushout_iff]; rw [← isLocalizedModule_iff_isLocalization]
  rw [← isLocalizedModule_iff_isBaseChange (S := S)]

中文:
引理 代数.isLocalization_iff_isPushout
  证明: by
  rw [Algebra.IsPushout.comm]; rw [Algebra.isPushout_iff]; rw [← isLocalizedModule_iff_isLocalization]
  rw [← isLocalizedModule_iff_isBaseChange (S := S)]

Depends on / 依赖: Algebra, Algebra.IsPushout.comm, Algebra.isPushout_iff, IsPushout, isLocalizedModule_iff_isBaseChange, isLocalizedModule_iff_isLocalization, isPushout_iff
-/
lemma Algebra.isLocalization_iff_isPushout :
    IsLocalization (Algebra.algebraMapSubmonoid T S) B ↔ IsPushout R T A B := by
  rw [Algebra.IsPushout.comm]; rw [Algebra.isPushout_iff]; rw [← isLocalizedModule_iff_isLocalization]
  rw [← isLocalizedModule_iff_isBaseChange (S := S)]

/--
lemma `Algebra.isPushout_of_isLocalization` / 引理 `Algebra.isPushout_of_isLocalization`

English:
lemma Algebra.isPushout_of_isLocalization
  given: [IsLocalization (Algebra.algebraMapSubmonoid T S) B]
  proof: (Algebra.isLocalization_iff_isPushout S _).mp inferInstance

中文:
引理 代数.isPushout_of_isLocalization
  条件: [是Localization (代数.algebraMapSubmonoid T S) B]
  证明: (Algebra.isLocalization_iff_isPushout S _).mp inferInstance

Depends on / 依赖: Algebra, Algebra.isLocalization_iff_isPushout, isLocalization_iff_isPushout
-/
lemma Algebra.isPushout_of_isLocalization [IsLocalization (Algebra.algebraMapSubmonoid T S) B] :
    Algebra.IsPushout R T A B :=
  (Algebra.isLocalization_iff_isPushout S _).mp inferInstance

/--
lemma `Submonoid.map_isUnit_le_isUnit` / 引理 `Submonoid.map_isUnit_le_isUnit`

English:
lemma Submonoid.map_isUnit_le_isUnit
  statement: {M N : Type*} [Monoid M] [Monoid N]
  proof: by
  rintro x ⟨y, hy, rfl⟩
  exact hy.map _

中文:
引理 子幺半群.map_isUnit_le_isUnit
  结论: {M N : 类型} [幺半群 M] [幺半群 N]
  证明: by
  rintro x ⟨y, hy, rfl⟩
  exact hy.map _

Depends on / 依赖: hy.map
-/
lemma Submonoid.map_isUnit_le_isUnit {M N : Type*} [Monoid M] [Monoid N]
    {F : Type*} [FunLike F M N] [MonoidHomClass F M N] (f : F) :
    Submonoid.map f (IsUnit.submonoid M) <= IsUnit.submonoid N := by
  rintro x ⟨y, hy, rfl⟩
  exact hy.map _

/--
lemma `Algebra.algebraMapSubmonoid_isUnit_le_isUnit` / 引理 `Algebra.algebraMapSubmonoid_isUnit_le_isUnit`

English:
lemma Algebra.algebraMapSubmonoid_isUnit_le_isUnit
  statement: {R S : Type*} [CommSemiring R] [Semiring S]
  proof: by
  rintro x ⟨y, hy, rfl⟩
  exact hy.map _

中文:
引理 代数.algebraMapSubmonoid_isUnit_le_isUnit
  结论: {R S : 类型} [交换半环 R] [半环 S]
  证明: by
  rintro x ⟨y, hy, rfl⟩
  exact hy.map _

Depends on / 依赖: hy.map
-/
lemma Algebra.algebraMapSubmonoid_isUnit_le_isUnit {R S : Type*} [CommSemiring R] [Semiring S]
    [Algebra R S] :
    Algebra.algebraMapSubmonoid S (IsUnit.submonoid R) <= IsUnit.submonoid S := by
  rintro x ⟨y, hy, rfl⟩
  exact hy.map _

instance {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S] :
    IsLocalization (Algebra.algebraMapSubmonoid S (IsUnit.submonoid R)) S :=
  IsLocalization.of_le_isUnit Algebra.algebraMapSubmonoid_isUnit_le_isUnit

/--
lemma `Algebra.IsPushout.of_bijective_left` / 引理 `Algebra.IsPushout.of_bijective_left`

English:
lemma Algebra.IsPushout.of_bijective_left
  statement: [Algebra A T] [IsScalarTower R A T]
  proof: by
  have : IsLocalization (IsUnit.submonoid R) A :=
    IsLocalization.of_le_isUnit_of_bijective Algebra.algebraMapSubmonoid_isUnit_le_isUnit H
  apply isPushout_of_isLocalization (IsUnit.submonoid R)

中文:
引理 代数.是推出.of_bijective_left
  结论: [代数 A T] [标量塔 R A T]
  证明: by
  have : IsLocalization (IsUnit.submonoid R) A :=
    IsLocalization.of_le_isUnit_of_bijective Algebra.algebraMapSubmonoid_isUnit_le_isUnit H
  apply isPushout_of_isLocalization (IsUnit.submonoid R)

Depends on / 依赖: Algebra, Algebra.algebraMapSubmonoid_isUnit_le_isUnit, IsLocalization, IsLocalization.of_le_isUnit_of_bijective, IsUnit, IsUnit.submonoid, algebraMapSubmonoid_isUnit_le_isUnit, isPushout_of_isLocalization, of_le_isUnit_of_bijective, submonoid
-/
lemma Algebra.IsPushout.of_bijective_left [Algebra A T] [IsScalarTower R A T]
    (H : Function.Bijective (algebraMap R A)) :
    IsPushout R T A T := by
  have : IsLocalization (IsUnit.submonoid R) A :=
    IsLocalization.of_le_isUnit_of_bijective Algebra.algebraMapSubmonoid_isUnit_le_isUnit H
  apply isPushout_of_isLocalization (IsUnit.submonoid R)

/--
lemma `Algebra.IsPushout.of_bijective_right` / 引理 `Algebra.IsPushout.of_bijective_right`

English:
lemma Algebra.IsPushout.of_bijective_right
  statement: [Algebra A T] [IsScalarTower R A T]
  proof: by
  have : IsLocalization (algebraMapSubmonoid A (IsUnit.submonoid R)) T := by
    apply IsLocalization.of_le_isUnit_of_bijective _ H
    simpa using Algebra.algebraMapSubmonoid_isUnit_le
  apply Algebra.isPushout_of_isLocalization (IsUnit.submonoid R)

中文:
引理 代数.是推出.of_bijective_right
  结论: [代数 A T] [标量塔 R A T]
  证明: by
  have : IsLocalization (algebraMapSubmonoid A (IsUnit.submonoid R)) T := by
    apply IsLocalization.of_le_isUnit_of_bijective _ H
    simpa using Algebra.algebraMapSubmonoid_isUnit_le
  apply Algebra.isPushout_of_isLocalization (IsUnit.submonoid R)

Depends on / 依赖: Algebra, Algebra.algebraMapSubmonoid_isUnit_le, Algebra.isPushout_of_isLocalization, IsLocalization, IsLocalization.of_le_isUnit_of_bijective, IsUnit, IsUnit.submonoid, algebraMapSubmonoid, algebraMapSubmonoid_isUnit_le, isPushout_of_isLocalization, of_le_isUnit_of_bijective, submonoid
-/
lemma Algebra.IsPushout.of_bijective_right [Algebra A T] [IsScalarTower R A T]
    (H : Function.Bijective (algebraMap A T)) :
    IsPushout R A R T := by
  have : IsLocalization (algebraMapSubmonoid A (IsUnit.submonoid R)) T := by
    apply IsLocalization.of_le_isUnit_of_bijective _ H
    simpa using Algebra.algebraMapSubmonoid_isUnit_le
  apply Algebra.isPushout_of_isLocalization (IsUnit.submonoid R)

variable (R M) in
open TensorProduct in
instance {α} [IsLocalizedModule S f] :
    IsLocalizedModule S (Finsupp.mapRange.linearMap (α := α) f) := by
  classical
  let e : Localization S otimes[R] M ≃ₗ[R] M' :=
    (LocalizedModule.equivTensorProduct S M).symm.restrictScalars R ≪≫ₗ IsLocalizedModule.iso S f
  let e' : Localization S otimes[R] (α ->₀ M) ≃ₗ[R] (α ->₀ M') :=
    finsuppRight R R (Localization S) M α ≪≫ₗ Finsupp.mapRange.linearEquiv e
  suffices IsLocalizedModule S (e'.symm.toLinearMap ∘ₗ Finsupp.mapRange.linearMap f) by
    convert! this.of_linearEquiv (e := e')
    ext
    simp
  rw [isLocalizedModule_iff_isBaseChange S (Localization S)]
  convert! TensorProduct.isBaseChange R (α ->₀ M) (Localization S) using 1
  ext a m
  apply (finsuppRight R R (Localization S) M α).injective
  ext b
  apply e.injective
  suffices (if a = b then f m else 0) = e (1 otimesₜ[R] if a = b then m else 0) by
    simpa [e', Finsupp.single_apply, -EmbeddingLike.apply_eq_iff_eq, apply_ite]
  split_ifs with h
  · simp [e]
  · simp only [tmul_zero, map_zero]

open Finsupp in
/--
theorem `IsLocalizedModule.map_linearCombination` / 定理 `IsLocalizedModule.map_linearCombination`

English:
theorem IsLocalizedModule.map_linearCombination
  given: {α : Type*} {v : α -> M} [IsLocalizedModule S f]
  proof: linearMap_ext (S := S) (mapRange.linearMap (Algebra.linearMap R A)) f by
    ext; simp [IsLocalizedModule.map_comp]

中文:
定理 是Localized模.map_linearCombination
  条件: {α : 类型} {v : α -> M} [是Localized模 S f]
  证明: linearMap_ext (S := S) (mapRange.linearMap (Algebra.linearMap R A)) f by
    ext; simp [IsLocalizedModule.map_comp]

Depends on / 依赖: Algebra, Algebra.linearMap, IsLocalizedModule, IsLocalizedModule.map_comp, linearMap, linearMap_ext, mapRange, mapRange.linearMap, map_comp
-/
theorem IsLocalizedModule.map_linearCombination {α : Type*} {v : α -> M} [IsLocalizedModule S f] :
    map S (mapRange.linearMap (Algebra.linearMap R A)) f (linearCombination R v) =
      linearCombination A (f ∘ v) :=
linearMap_ext (S := S) (mapRange.linearMap (Algebra.linearMap R A)) f by
    ext; simp [IsLocalizedModule.map_comp]

section

variable (S : Submonoid A) {N : Type*} [AddCommMonoid N] [Module R N]
variable [Module A M] [IsScalarTower R A M]

open TensorProduct

/--
Instance `IsLocalizedModule.rTensor` / 实例 `IsLocalizedModule.rTensor`

English:
instance IsLocalizedModule.rTensor
  signature: (g : M ->ₗ[A] M') [h : IsLocalizedModule S g]
  body: by
  let Aₚ := Localization S
  let : Module Aₚ M' := (IsLocalizedModule.iso S g).symm.toAddEquiv.module Aₚ
  have : IsScalarTower A Aₚ M' := (IsLocalizedModule.iso S g).symm.isScalarTower Aₚ
  have : IsScalarTower R Aₚ M' :=
IsScalarTower.of_algebraMap_smul fun r x => by simp [IsScalarTower.algebraMap_apply R A Aₚ]
  rw [isLocalizedModule_iff_isBaseChange (S := S) (A := Aₚ)] at h ⊢
  exact isBaseChange_tensorProduct_map _ h

中文:
实例 是Localized模.rTensor
  签名: (g : M ->ₗ[A] M') [h : 是Localized模 S g]
  定义体: by
  let Aₚ := Localization S
  let : Module Aₚ M' := (IsLocalizedModule.iso S g).symm.toAddEquiv.module Aₚ
  have : IsScalarTower A Aₚ M' := (IsLocalizedModule.iso S g).symm.isScalarTower Aₚ
  have : IsScalarTower R Aₚ M' :=
IsScalarTower.of_algebraMap_smul fun r x => by simp [IsScalarTower.algebraMap_apply R A Aₚ]
  rw [isLocalizedModule_iff_isBaseChange (S := S) (A := Aₚ)] at h ⊢
  exact isBaseChange_tensorProduct_map _ h

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.iso, IsScalarTower, IsScalarTower.algebraMap_apply, IsScalarTower.of_algebraMap_smul, Localization, Module, algebraMap_apply, isBaseChange_tensorProduct_map, isLocalizedModule_iff_isBaseChange, isScalarTower, module, of_algebraMap_smul, symm.isScalarTower, symm.toAddEquiv.module, toAddEquiv
-/
instance IsLocalizedModule.rTensor (g : M ->ₗ[A] M') [h : IsLocalizedModule S g] :
    IsLocalizedModule S (AlgebraTensorModule.rTensor R N g) := by
  let Aₚ := Localization S
  let : Module Aₚ M' := (IsLocalizedModule.iso S g).symm.toAddEquiv.module Aₚ
  have : IsScalarTower A Aₚ M' := (IsLocalizedModule.iso S g).symm.isScalarTower Aₚ
  have : IsScalarTower R Aₚ M' :=
IsScalarTower.of_algebraMap_smul fun r x => by simp [IsScalarTower.algebraMap_apply R A Aₚ]
  rw [isLocalizedModule_iff_isBaseChange (S := S) (A := Aₚ)] at h ⊢
  exact isBaseChange_tensorProduct_map _ h

variable {P : Type*} [AddCommMonoid P] [Module R P] (f : N ->ₗ[R] P)

/--
lemma `IsLocalizedModule.map_lTensor` / 引理 `IsLocalizedModule.map_lTensor`

English:
lemma IsLocalizedModule.map_lTensor
  given: (g : M ->ₗ[A] M') [h : IsLocalizedModule S g]
  proof: by
  apply linearMap_ext S (AlgebraTensorModule.rTensor R N g) (AlgebraTensorModule.rTensor R P g)
  rw [map_comp]
  ext
  simp

中文:
引理 是Localized模.map_lTensor
  条件: (g : M ->ₗ[A] M') [h : 是Localized模 S g]
  证明: by
  apply linearMap_ext S (AlgebraTensorModule.rTensor R N g) (AlgebraTensorModule.rTensor R P g)
  rw [map_comp]
  ext
  simp

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.rTensor, linearMap_ext, map_comp, rTensor
-/
lemma IsLocalizedModule.map_lTensor (g : M ->ₗ[A] M') [h : IsLocalizedModule S g] :
    IsLocalizedModule.map S (AlgebraTensorModule.rTensor R N g) (AlgebraTensorModule.rTensor R P g)
      (AlgebraTensorModule.lTensor A M f) = AlgebraTensorModule.lTensor A M' f := by
  apply linearMap_ext S (AlgebraTensorModule.rTensor R N g) (AlgebraTensorModule.rTensor R P g)
  rw [map_comp]
  ext
  simp

end

section

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    (r : R) (A : Type*) [CommSemiring A] [Algebra R A]

/--
Instance `IsLocalization.tensor` / 实例 `IsLocalization.tensor`

English:
instance IsLocalization.tensor
  signature: (M : Submonoid R) [IsLocalization M A]
  body: by
  let _ : Algebra A (S otimes[R] A) := Algebra.TensorProduct.rightAlgebra
  rw [Algebra.isLocalization_iff_isPushout _ A]
  infer_instance

中文:
实例 是Localization.tensor
  签名: (M : 子幺半群 R) [是Localization M A]
  定义体: by
  let _ : Algebra A (S otimes[R] A) := Algebra.TensorProduct.rightAlgebra
  rw [Algebra.isLocalization_iff_isPushout _ A]
  infer_instance

Depends on / 依赖: Algebra, Algebra.TensorProduct.rightAlgebra, Algebra.isLocalization_iff_isPushout, TensorProduct, infer_instance, isLocalization_iff_isPushout, otimes, rightAlgebra
-/
instance IsLocalization.tensor (M : Submonoid R) [IsLocalization M A] :
    IsLocalization (Algebra.algebraMapSubmonoid S M) (S otimes[R] A) := by
  let _ : Algebra A (S otimes[R] A) := Algebra.TensorProduct.rightAlgebra
  rw [Algebra.isLocalization_iff_isPushout _ A]
  infer_instance

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/--
Instance `IsLocalization.tensorRight` / 实例 `IsLocalization.tensorRight`

English:
instance IsLocalization.tensorRight
  signature: (M : Submonoid R) [IsLocalization M A]
  body: by
  rw [Algebra.isLocalization_iff_isPushout _ A]
  infer_instance

中文:
实例 是Localization.tensorRight
  签名: (M : 子幺半群 R) [是Localization M A]
  定义体: by
  rw [Algebra.isLocalization_iff_isPushout _ A]
  infer_instance

Depends on / 依赖: Algebra, Algebra.isLocalization_iff_isPushout, infer_instance, isLocalization_iff_isPushout
-/
instance IsLocalization.tensorRight (M : Submonoid R) [IsLocalization M A] :
    IsLocalization (Algebra.algebraMapSubmonoid S M) (A otimes[R] S) := by
  rw [Algebra.isLocalization_iff_isPushout _ A]
  infer_instance

open Algebra.TensorProduct in
/--
lemma `IsLocalization.tmul_mk'` / 引理 `IsLocalization.tmul_mk'`

English:
lemma IsLocalization.tmul_mk'
  given: (M : Submonoid R) [IsLocalization M A] (s : S) (x : R) (y : M)
  proof: by
  rw [IsLocalization.eq_mk'_iff_mul_eq]; rw [algebraMap_apply]; rw [Algebra.algebraMap_self]; rw [RingHomCompTriple.comp_apply]; rw [tmul_one_eq_one_tmul]; rw [tmul_mul_tmul]; rw [mul_one]; rw [mul_comm]; rw [IsLocalization.mk'_spec']; rw [algebraMap_apply]; rw [Algebra.algebraMap_self]; rw [RingHom.id_apply]; rw [← Algebra.smul_def]; rw [smul_tmul]; rw [Algebra.smul_def]; rw [mul_one]

中文:
引理 是Localization.tmul_mk'
  条件: (M : 子幺半群 R) [是Localization M A] (s : S) (x : R) (y : M)
  证明: by
  rw [IsLocalization.eq_mk'_iff_mul_eq]; rw [algebraMap_apply]; rw [Algebra.algebraMap_self]; rw [RingHomCompTriple.comp_apply]; rw [tmul_one_eq_one_tmul]; rw [tmul_mul_tmul]; rw [mul_one]; rw [mul_comm]; rw [IsLocalization.mk'_spec']; rw [algebraMap_apply]; rw [Algebra.algebraMap_self]; rw [RingHom.id_apply]; rw [← Algebra.smul_def]; rw [smul_tmul]; rw [Algebra.smul_def]; rw [mul_one]

Depends on / 依赖: Algebra, Algebra.algebraMap_self, Algebra.smul_def, IsLocalization, IsLocalization.eq_mk, IsLocalization.mk, RingHom, RingHom.id_apply, RingHomCompTriple, RingHomCompTriple.comp_apply, _iff_mul_eq, _spec, algebraMap_apply, algebraMap_self, comp_apply, eq_mk, id_apply, mul_comm, mul_one, smul_def
-/
lemma IsLocalization.tmul_mk' (M : Submonoid R) [IsLocalization M A] (s : S) (x : R) (y : M) :
    s otimesₜ IsLocalization.mk' A x y =
      IsLocalization.mk' (S otimes[R] A) (algebraMap R S x * s)
        ⟨algebraMap R S y.1, Algebra.mem_algebraMapSubmonoid_of_mem _⟩ := by
  rw [IsLocalization.eq_mk'_iff_mul_eq]; rw [algebraMap_apply]; rw [Algebra.algebraMap_self]; rw [RingHomCompTriple.comp_apply]; rw [tmul_one_eq_one_tmul]; rw [tmul_mul_tmul]; rw [mul_one]; rw [mul_comm]; rw [IsLocalization.mk'_spec']; rw [algebraMap_apply]; rw [Algebra.algebraMap_self]; rw [RingHom.id_apply]; rw [← Algebra.smul_def]; rw [smul_tmul]; rw [Algebra.smul_def]; rw [mul_one]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
open Algebra.TensorProduct in
/--
lemma `IsLocalization.mk'_tmul` / 引理 `IsLocalization.mk'_tmul`

English:
lemma IsLocalization.mk'_tmul
  given: (M : Submonoid R) [IsLocalization M A] (s : S) (x : R) (y : M)
  proof: by
  simp [IsLocalization.eq_mk'_iff_mul_eq, map_mul,
    RingHom.algebraMap_toAlgebra]

中文:
引理 是Localization.mk'_tmul
  条件: (M : 子幺半群 R) [是Localization M A] (s : S) (x : R) (y : M)
  证明: by
  simp [IsLocalization.eq_mk'_iff_mul_eq, map_mul,
    RingHom.algebraMap_toAlgebra]
-/
lemma IsLocalization.mk'_tmul (M : Submonoid R) [IsLocalization M A] (s : S) (x : R) (y : M) :
    IsLocalization.mk' A x y otimesₜ s =
      IsLocalization.mk' (A otimes[R] S) (algebraMap R S x * s)
        ⟨algebraMap R S y.1, Algebra.mem_algebraMapSubmonoid_of_mem _⟩ := by
  simp [IsLocalization.eq_mk'_iff_mul_eq, map_mul,
    RingHom.algebraMap_toAlgebra]

namespace Localization

variable {R : Type*} [CommRing R] (M : Submonoid R) (Rₘ : Type*) [CommRing Rₘ] [Algebra R Rₘ]
  (S : Type*) [CommRing S] [Algebra R S]

/--
Definition of `tensorLeftAlgEquiv` / `tensorLeftAlgEquiv` 的定义

English:
definition tensorLeftAlgEquiv
  signature: :
  body: (algEquiv (Algebra.algebraMapSubmonoid S M) (S otimes[R] Localization M)).symm

中文:
定义 tensorLeftAlgEquiv
  签名: :
  定义体: (algEquiv (Algebra.algebraMapSubmonoid S M) (S otimes[R] Localization M)).symm

Depends on / 依赖: Algebra, Algebra.algebraMapSubmonoid, Localization, algEquiv, algebraMapSubmonoid, otimes
-/
noncomputable def tensorLeftAlgEquiv :
    (S otimes[R] Localization M) ≃ₐ[S] Localization (Algebra.algebraMapSubmonoid S M) :=
  (algEquiv (Algebra.algebraMapSubmonoid S M) (S otimes[R] Localization M)).symm

variable {S} in
@[simp]
/--
theorem `tensorLeftAlgEquiv_apply_tmul_one` / 定理 `tensorLeftAlgEquiv_apply_tmul_one`

English:
theorem tensorLeftAlgEquiv_apply_tmul_one
  given: (x : S)
  proof: (tensorLeftAlgEquiv M S).commutes x

中文:
定理 tensorLeftAlgEquiv_apply_tmul_one
  条件: (x : S)
  证明: (tensorLeftAlgEquiv M S).commutes x

Depends on / 依赖: commutes, tensorLeftAlgEquiv
-/
theorem tensorLeftAlgEquiv_apply_tmul_one (x : S) :
    tensorLeftAlgEquiv M S (x otimesₜ[R] 1) = algebraMap _ _ x :=
  (tensorLeftAlgEquiv M S).commutes x

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `tensorLeftAlgEquiv_apply_one_tmul` / 定理 `tensorLeftAlgEquiv_apply_one_tmul`

English:
theorem tensorLeftAlgEquiv_apply_one_tmul
  given: (x : Localization M)
  proof: by
  let Rₘ := Localization M
  let Sₘ := Localization (Algebra.algebraMapSubmonoid S M)
  obtain ⟨x, y, rfl⟩ := IsLocalization.exists_mk'_eq M x
  let : Algebra Rₘ (S otimes[R] Rₘ) := Algebra.TensorProduct.rightAlgebra
  have h1 : (1 : S) otimesₜ[R] IsLocalization.mk' Rₘ x y = algebraMap _ _ (IsLocalization.mk' Rₘ x y) :=
    rfl
  rw [h1]; rw [tensorLeftAlgEquiv]; rw [algEquiv_symm_apply]; rw [IsLocalization.algebraMap_mk' S]; rw [IsLocalization.map_mk']; rw [IsLocalization.mk'_eq_iff_eq_mul]
  simp_rw [RingHom.id_apply]
  have h x : algebraMap S Sₘ ((algebraMap R S) x) = algebraMap Rₘ Sₘ ((algebraMap R Rₘ) x) := by
    rw [← IsScalarTower.algebraMap_apply]; rw [← IsScalarTower.algebraMap_apply]
  rw [h]; rw [h]; rw [← map_mul]; rw [IsLocalization.mk'_spec]

中文:
定理 tensorLeftAlgEquiv_apply_one_tmul
  条件: (x : Localization M)
  证明: by
  let Rₘ := Localization M
  let Sₘ := Localization (Algebra.algebraMapSubmonoid S M)
  obtain ⟨x, y, rfl⟩ := IsLocalization.exists_mk'_eq M x
  let : Algebra Rₘ (S otimes[R] Rₘ) := Algebra.TensorProduct.rightAlgebra
  have h1 : (1 : S) otimesₜ[R] IsLocalization.mk' Rₘ x y = algebraMap _ _ (IsLocalization.mk' Rₘ x y) :=
    rfl
  rw [h1]; rw [tensorLeftAlgEquiv]; rw [algEquiv_symm_apply]; rw [IsLocalization.algebraMap_mk' S]; rw [IsLocalization.map_mk']; rw [IsLocalization.mk'_eq_iff_eq_mul]
  simp_rw [RingHom.id_apply]
  have h x : algebraMap S Sₘ ((algebraMap R S) x) = algebraMap Rₘ Sₘ ((algebraMap R Rₘ) x) := by
    rw [← IsScalarTower.algebraMap_apply]; rw [← IsScalarTower.algebraMap_apply]
  rw [h]; rw [h]; rw [← map_mul]; rw [IsLocalization.mk'_spec]

Depends on / 依赖: Algebra, Algebra.TensorProduct.rightAlgebra, Algebra.algebraMapSubmonoid, IsLocalization, IsLocalization.algebraMap_mk, IsLocalization.exists_mk, IsLocalization.map_mk, IsLocalization.mk, Localization, RingHom, TensorProduct, _eq_iff_eq_mul, algEquiv_symm_apply, algebraMap, algebraMapSubmonoid, algebraMap_mk, exists_mk, map_mk, otimes, rightAlgebra
-/
theorem tensorLeftAlgEquiv_apply_one_tmul (x : Localization M) :
    tensorLeftAlgEquiv M S (1 otimesₜ[R] x) = algebraMap _ _ x := by
  let Rₘ := Localization M
  let Sₘ := Localization (Algebra.algebraMapSubmonoid S M)
  obtain ⟨x, y, rfl⟩ := IsLocalization.exists_mk'_eq M x
  let : Algebra Rₘ (S otimes[R] Rₘ) := Algebra.TensorProduct.rightAlgebra
  have h1 : (1 : S) otimesₜ[R] IsLocalization.mk' Rₘ x y = algebraMap _ _ (IsLocalization.mk' Rₘ x y) :=
    rfl
  rw [h1]; rw [tensorLeftAlgEquiv]; rw [algEquiv_symm_apply]; rw [IsLocalization.algebraMap_mk' S]; rw [IsLocalization.map_mk']; rw [IsLocalization.mk'_eq_iff_eq_mul]
  simp_rw [RingHom.id_apply]
  have h x : algebraMap S Sₘ ((algebraMap R S) x) = algebraMap Rₘ Sₘ ((algebraMap R Rₘ) x) := by
    rw [← IsScalarTower.algebraMap_apply]; rw [← IsScalarTower.algebraMap_apply]
  rw [h]; rw [h]; rw [← map_mul]; rw [IsLocalization.mk'_spec]

/--
Definition of `tensorRightAlgEquiv` / `tensorRightAlgEquiv` 的定义

English:
definition tensorRightAlgEquiv
  signature: :
  body: (Algebra.TensorProduct.comm R (Localization M) S).toRingEquiv.trans
    (tensorLeftAlgEquiv M S).toRingEquiv
  commutes' := tensorLeftAlgEquiv_apply_one_tmul M S

@[simp]

中文:
定义 tensorRightAlgEquiv
  签名: :
  定义体: (Algebra.TensorProduct.comm R (Localization M) S).toRingEquiv.trans
    (tensorLeftAlgEquiv M S).toRingEquiv
  commutes' := tensorLeftAlgEquiv_apply_one_tmul M S

@[simp]

Depends on / 依赖: Algebra, Algebra.TensorProduct.comm, Localization, TensorProduct, toRingEquiv, toRingEquiv.trans
-/
noncomputable def tensorRightAlgEquiv :
    Localization M otimes[R] S ≃ₐ[Localization M] Localization (Algebra.algebraMapSubmonoid S M) where
  __ := (Algebra.TensorProduct.comm R (Localization M) S).toRingEquiv.trans
    (tensorLeftAlgEquiv M S).toRingEquiv
  commutes' := tensorLeftAlgEquiv_apply_one_tmul M S

@[simp]
/--
theorem `tensorRightAlgEquiv_apply_tmul_one` / 定理 `tensorRightAlgEquiv_apply_tmul_one`

English:
theorem tensorRightAlgEquiv_apply_tmul_one
  given: (x : Localization M)
  proof: (tensorRightAlgEquiv M S).commutes x

中文:
定理 tensorRightAlgEquiv_apply_tmul_one
  条件: (x : Localization M)
  证明: (tensorRightAlgEquiv M S).commutes x

Depends on / 依赖: commutes, tensorRightAlgEquiv
-/
theorem tensorRightAlgEquiv_apply_tmul_one (x : Localization M) :
    tensorRightAlgEquiv M S (x otimesₜ[R] 1) = algebraMap _ _ x :=
  (tensorRightAlgEquiv M S).commutes x

variable {S} in
@[simp]
/--
theorem `tensorRightAlgEquiv_apply_one_tmul` / 定理 `tensorRightAlgEquiv_apply_one_tmul`

English:
theorem tensorRightAlgEquiv_apply_one_tmul
  given: (x : S)
  proof: (tensorLeftAlgEquiv M S).commutes x

中文:
定理 tensorRightAlgEquiv_apply_one_tmul
  条件: (x : S)
  证明: (tensorLeftAlgEquiv M S).commutes x

Depends on / 依赖: commutes, tensorLeftAlgEquiv
-/
theorem tensorRightAlgEquiv_apply_one_tmul (x : S) :
    tensorRightAlgEquiv M S (1 otimesₜ[R] x) = algebraMap _ _ x :=
  (tensorLeftAlgEquiv M S).commutes x

end Localization

variable (R S) {A} in
/--
lemma `IsLocalization.tensorProduct_tensorProduct` / 引理 `IsLocalization.tensorProduct_tensorProduct`

English:
lemma IsLocalization.tensorProduct_tensorProduct
  statement: (M : Submonoid A)
  proof: (Algebra.isLocalization_iff_isPushout M _).mpr
    (Algebra.IsPushout.tensorProduct_tensorProduct R S A B H).symm

中文:
引理 是Localization.tensorProduct_tensorProduct
  结论: (M : 子幺半群 A)
  证明: (Algebra.isLocalization_iff_isPushout M _).mpr
    (Algebra.IsPushout.tensorProduct_tensorProduct R S A B H).symm

Depends on / 依赖: Algebra, Algebra.IsPushout.tensorProduct_tensorProduct, Algebra.isLocalization_iff_isPushout, IsPushout, isLocalization_iff_isPushout, tensorProduct_tensorProduct
-/
lemma IsLocalization.tensorProduct_tensorProduct (M : Submonoid A)
    (B : Type*) [CommSemiring B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [IsLocalization M B]
    [Algebra (A otimes[R] S) (B otimes[R] S)] [IsScalarTower A (A otimes[R] S) (B otimes[R] S)]
    (H : (algebraMap (A otimes[R] S) (B otimes[R] S)).comp Algebra.TensorProduct.includeRight.toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom) :
    IsLocalization (Algebra.algebraMapSubmonoid (A otimes[R] S) M) (B otimes[R] S) :=
  (Algebra.isLocalization_iff_isPushout M _).mpr
    (Algebra.IsPushout.tensorProduct_tensorProduct R S A B H).symm

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
variable (R S) {A} in
/--
lemma `IsLocalization.tensorProduct_tensorProduct_right` / 引理 `IsLocalization.tensorProduct_tensorProduct_right`

English:
lemma IsLocalization.tensorProduct_tensorProduct_right
  statement: (M : Submonoid A)
  proof: by
  change IsLocalization (Algebra.algebraMapSubmonoid _ M) (S otimes[R] B)
  let : Algebra A (S otimes[R] B) := .compHom _ (algebraMap A B)
  have : IsScalarTower A (S otimes[R] A) (S otimes[R] B) := .of_algebraMap_eq' H.symm
  have : IsScalarTower R A (S otimes[R] B) :=
.of_algebraMap_eq' by
      rw [Algebra.compHom_algebraMap_eq]; rw [RingHom.comp_assoc]; rw [← IsScalarTower.algebraMap_eq]; rw [IsScalarTower.algebraMap_eq R B]
  have : IsScalarTower R (S otimes[R] A) (S otimes[R] B) := .to₁₃₄ _ A _ _
  have : IsScalarTower A B (S otimes[R] B) := .of_algebraMap_eq' rfl
  rw [Algebra.isLocalization_iff_isPushout _ B]; rw [Algebra.IsPushout.comm]; rw [← Algebra.IsPushout.comp_iff R _ S]
  infer_instance

中文:
引理 是Localization.tensorProduct_tensorProduct_right
  结论: (M : 子幺半群 A)
  证明: by
  change IsLocalization (Algebra.algebraMapSubmonoid _ M) (S otimes[R] B)
  let : Algebra A (S otimes[R] B) := .compHom _ (algebraMap A B)
  have : IsScalarTower A (S otimes[R] A) (S otimes[R] B) := .of_algebraMap_eq' H.symm
  have : IsScalarTower R A (S otimes[R] B) :=
.of_algebraMap_eq' by
      rw [Algebra.compHom_algebraMap_eq]; rw [RingHom.comp_assoc]; rw [← IsScalarTower.algebraMap_eq]; rw [IsScalarTower.algebraMap_eq R B]
  have : IsScalarTower R (S otimes[R] A) (S otimes[R] B) := .to₁₃₄ _ A _ _
  have : IsScalarTower A B (S otimes[R] B) := .of_algebraMap_eq' rfl
  rw [Algebra.isLocalization_iff_isPushout _ B]; rw [Algebra.IsPushout.comm]; rw [← Algebra.IsPushout.comp_iff R _ S]
  infer_instance

Depends on / 依赖: Algebra, Algebra.algebraMapSubmonoid, Algebra.compHom_algebraMap_eq, H.symm, IsLocalization, IsScalarTower, IsScalarTower.algebraMap_eq, RingHom, RingHom.comp_assoc, algebraMap, algebraMapSubmonoid, algebraMap_eq, compHom, compHom_algebraMap_eq, comp_assoc, of_algebraMap_eq, otimes
-/
lemma IsLocalization.tensorProduct_tensorProduct_right (M : Submonoid A)
    (B : Type*) [CommSemiring B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [IsLocalization M B]
    [Algebra (S otimes[R] A) (S otimes[R] B)] [IsScalarTower S (S otimes[R] A) (S otimes[R] B)]
    (H : (algebraMap (S otimes[R] A) (S otimes[R] B)).comp Algebra.TensorProduct.includeRight.toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom.comp (algebraMap A B)) :
    IsLocalization (M.map (Algebra.TensorProduct.includeRight (R := R) (A := S))) (S otimes[R] B) := by
  change IsLocalization (Algebra.algebraMapSubmonoid _ M) (S otimes[R] B)
  let : Algebra A (S otimes[R] B) := .compHom _ (algebraMap A B)
  have : IsScalarTower A (S otimes[R] A) (S otimes[R] B) := .of_algebraMap_eq' H.symm
  have : IsScalarTower R A (S otimes[R] B) :=
.of_algebraMap_eq' by
      rw [Algebra.compHom_algebraMap_eq]; rw [RingHom.comp_assoc]; rw [← IsScalarTower.algebraMap_eq]; rw [IsScalarTower.algebraMap_eq R B]
  have : IsScalarTower R (S otimes[R] A) (S otimes[R] B) := .to₁₃₄ _ A _ _
  have : IsScalarTower A B (S otimes[R] B) := .of_algebraMap_eq' rfl
  rw [Algebra.isLocalization_iff_isPushout _ B]; rw [Algebra.IsPushout.comm]; rw [← Algebra.IsPushout.comp_iff R _ S]
  infer_instance

variable (R S) {A} in
/-- The natural isomorphism `S ⊗[R] A[M⁻¹] ≃ (S ⊗[R] A)[M⁻¹]`. -/
noncomputable
/--
Definition of `IsLocalization.tensorProductEquivOfMapIncludeRight` / `IsLocalization.tensorProductEquivOfMapIncludeRight` 的定义

English:
definition IsLocalization.tensorProductEquivOfMapIncludeRight
  signature: (M : Submonoid A)
  body: letI M' : Submonoid (S otimes[R] A) := M.map (Algebra.TensorProduct.includeRight (R := R) (A := S))
  letI : Algebra (S otimes[R] A) (S otimes[R] B) :=
    (Algebra.TensorProduct.map (AlgHom.id R S) (IsScalarTower.toAlgHom R _ _)).toAlgebra
  haveI : IsScalarTower S (S otimes[R] A) (S otimes[R] B) :=
.of_algebraMap_eq by intro; simp [RingHom.algebraMap_toAlgebra]
  haveI := IsLocalization.tensorProduct_tensorProduct_right R S M B
    (by ext; simp [RingHom.algebraMap_toAlgebra])
  (IsLocalization.algEquiv M' _ _).restrictScalars S

中文:
定义 是Localization.tensorProductEquivOfMapIncludeRight
  签名: (M : 子幺半群 A)
  定义体: letI M' : Submonoid (S otimes[R] A) := M.map (Algebra.TensorProduct.includeRight (R := R) (A := S))
  letI : Algebra (S otimes[R] A) (S otimes[R] B) :=
    (Algebra.TensorProduct.map (AlgHom.id R S) (IsScalarTower.toAlgHom R _ _)).toAlgebra
  haveI : IsScalarTower S (S otimes[R] A) (S otimes[R] B) :=
.of_algebraMap_eq by intro; simp [RingHom.algebraMap_toAlgebra]
  haveI := IsLocalization.tensorProduct_tensorProduct_right R S M B
    (by ext; simp [RingHom.algebraMap_toAlgebra])
  (IsLocalization.algEquiv M' _ _).restrictScalars S
-/
def IsLocalization.tensorProductEquivOfMapIncludeRight (M : Submonoid A)
    (B : Type*) [CommSemiring B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [IsLocalization M B]
    (C : Type*) [CommSemiring C] [Algebra S C] [Algebra (S otimes[R] A) C] [IsScalarTower S (S otimes[R] A) C]
    [IsLocalization (M.map (Algebra.TensorProduct.includeRight (R := R) (A := S))) C] :
    S otimes[R] B ≃ₐ[S] C :=
  letI M' : Submonoid (S otimes[R] A) := M.map (Algebra.TensorProduct.includeRight (R := R) (A := S))
  letI : Algebra (S otimes[R] A) (S otimes[R] B) :=
    (Algebra.TensorProduct.map (AlgHom.id R S) (IsScalarTower.toAlgHom R _ _)).toAlgebra
  haveI : IsScalarTower S (S otimes[R] A) (S otimes[R] B) :=
.of_algebraMap_eq by intro; simp [RingHom.algebraMap_toAlgebra]
  haveI := IsLocalization.tensorProduct_tensorProduct_right R S M B
    (by ext; simp [RingHom.algebraMap_toAlgebra])
  (IsLocalization.algEquiv M' _ _).restrictScalars S

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `IsLocalization.tensorProductEquivOfMapIncludeRight_tmul` / 引理 `IsLocalization.tensorProductEquivOfMapIncludeRight_tmul`

English:
lemma IsLocalization.tensorProductEquivOfMapIncludeRight_tmul
  statement: (M : Submonoid A)
  proof: by
  let : Algebra (S otimes[R] A) (S otimes[R] B) :=
    (Algebra.TensorProduct.map (AlgHom.id R S) (IsScalarTower.toAlgHom R _ _)).toAlgebra
  have heq : x otimesₜ[R] (algebraMap A B) a = algebraMap _ _ (x otimesₜ[R] a) := rfl
  simp [heq, IsLocalization.tensorProductEquivOfMapIncludeRight]

中文:
引理 是Localization.tensorProductEquivOfMapIncludeRight_tmul
  结论: (M : 子幺半群 A)
  证明: by
  let : Algebra (S otimes[R] A) (S otimes[R] B) :=
    (Algebra.TensorProduct.map (AlgHom.id R S) (IsScalarTower.toAlgHom R _ _)).toAlgebra
  have heq : x otimesₜ[R] (algebraMap A B) a = algebraMap _ _ (x otimesₜ[R] a) := rfl
  simp [heq, IsLocalization.tensorProductEquivOfMapIncludeRight]
-/
lemma IsLocalization.tensorProductEquivOfMapIncludeRight_tmul (M : Submonoid A)
    (B : Type*) [CommSemiring B] [Algebra R B] [Algebra A B]
    [IsScalarTower R A B] [IsLocalization M B]
    (C : Type*) [CommSemiring C] [Algebra S C] [Algebra (S otimes[R] A) C] [IsScalarTower S (S otimes[R] A) C]
    [IsLocalization (M.map (Algebra.TensorProduct.includeRight (R := R) (A := S))) C]
    (x : S) (a : A) :
    IsLocalization.tensorProductEquivOfMapIncludeRight R S M B C (x otimesₜ algebraMap A B a) =
      algebraMap _ _ (x otimesₜ[R] a) := by
  let : Algebra (S otimes[R] A) (S otimes[R] B) :=
    (Algebra.TensorProduct.map (AlgHom.id R S) (IsScalarTower.toAlgHom R _ _)).toAlgebra
  have heq : x otimesₜ[R] (algebraMap A B) a = algebraMap _ _ (x otimesₜ[R] a) := rfl
  simp [heq, IsLocalization.tensorProductEquivOfMapIncludeRight]

variable (R S) {A} in
/-- The natural isomorphism `S ⊗[R] A[1/g] ≃ (S ⊗[R] A)[1/g]`. -/
noncomputable
/--
Definition of `IsLocalization.Away.tensorProductEquivTMulRight` / `IsLocalization.Away.tensorProductEquivTMulRight` 的定义

English:
definition IsLocalization.Away.tensorProductEquivTMulRight
  signature: (g : A) (B : Type*) [CommSemiring B]
  body: haveI : IsLocalization
      ((Submonoid.powers g).map (Algebra.TensorProduct.includeRight (R := R) (A := S)))
      (Localization.Away ((1 : S) otimesₜ[R] g)) := by
    simp only [Submonoid.map_powers, Algebra.TensorProduct.includeRight_apply]
    infer_instance
  IsLocalization.tensorProductEquivOfMapIncludeRight _ _ (.powers g) _ _

@[simp]

中文:
定义 是Localization.Away.tensorProductEquivTMulRight
  签名: (g : A) (B : 类型) [交换半环 B]
  定义体: haveI : IsLocalization
      ((Submonoid.powers g).map (Algebra.TensorProduct.includeRight (R := R) (A := S)))
      (Localization.Away ((1 : S) otimesₜ[R] g)) := by
    simp only [Submonoid.map_powers, Algebra.TensorProduct.includeRight_apply]
    infer_instance
  IsLocalization.tensorProductEquivOfMapIncludeRight _ _ (.powers g) _ _

@[simp]

Depends on / 依赖: Algebra, Algebra.TensorProduct.includeRight, Algebra.TensorProduct.includeRight_apply, IsLocalization, IsLocalization.tensorProductEquivOfMapIncludeRight, Localization, Localization.Away, Submonoid, Submonoid.map_powers, Submonoid.powers, TensorProduct, includeRight, includeRight_apply, infer_instance, map_powers, powers, tensorProductEquivOfMapIncludeRight
-/
def IsLocalization.Away.tensorProductEquivTMulRight (g : A) (B : Type*) [CommSemiring B]
    [Algebra R B] [Algebra A B] [IsScalarTower R A B] [IsLocalization.Away g B] :
    S otimes[R] B ≃ₐ[S] Localization.Away ((1 : S) otimesₜ[R] g) :=
  haveI : IsLocalization
      ((Submonoid.powers g).map (Algebra.TensorProduct.includeRight (R := R) (A := S)))
      (Localization.Away ((1 : S) otimesₜ[R] g)) := by
    simp only [Submonoid.map_powers, Algebra.TensorProduct.includeRight_apply]
    infer_instance
  IsLocalization.tensorProductEquivOfMapIncludeRight _ _ (.powers g) _ _

@[simp]
/--
lemma `IsLocalization.Away.tensorProductEquivTMulRight_tmul` / 引理 `IsLocalization.Away.tensorProductEquivTMulRight_tmul`

English:
lemma IsLocalization.Away.tensorProductEquivTMulRight_tmul
  statement: (g : A) (B : Type*) [CommSemiring B]
  proof: haveI : IsLocalization
      ((Submonoid.powers g).map (Algebra.TensorProduct.includeRight (R := R) (A := S)))
      (Localization.Away ((1 : S) otimesₜ[R] g)) := by
    simp only [Submonoid.map_powers, Algebra.TensorProduct.includeRight_apply]
    infer_instance
  IsLocalization.tensorProductEquivOfMapIncludeRight_tmul _ _ _ _ _ _

中文:
引理 是Localization.Away.tensorProductEquivTMulRight_tmul
  结论: (g : A) (B : 类型) [交换半环 B]
  证明: haveI : IsLocalization
      ((Submonoid.powers g).map (Algebra.TensorProduct.includeRight (R := R) (A := S)))
      (Localization.Away ((1 : S) otimesₜ[R] g)) := by
    simp only [Submonoid.map_powers, Algebra.TensorProduct.includeRight_apply]
    infer_instance
  IsLocalization.tensorProductEquivOfMapIncludeRight_tmul _ _ _ _ _ _

Depends on / 依赖: Algebra, Algebra.TensorProduct.includeRight, Algebra.TensorProduct.includeRight_apply, IsLocalization, IsLocalization.tensorProductEquivOfMapIncludeRight_tmul, Localization, Localization.Away, Submonoid, Submonoid.map_powers, Submonoid.powers, TensorProduct, includeRight, includeRight_apply, infer_instance, map_powers, powers, tensorProductEquivOfMapIncludeRight_tmul
-/
lemma IsLocalization.Away.tensorProductEquivTMulRight_tmul (g : A) (B : Type*) [CommSemiring B]
    [Algebra R B] [Algebra A B] [IsScalarTower R A B] [IsLocalization.Away g B]
    (x : S) (a : A) :
    IsLocalization.Away.tensorProductEquivTMulRight R S g B (x otimesₜ algebraMap _ _ a) =
      algebraMap _ _ (x otimesₜ[R] a) :=
  haveI : IsLocalization
      ((Submonoid.powers g).map (Algebra.TensorProduct.includeRight (R := R) (A := S)))
      (Localization.Away ((1 : S) otimesₜ[R] g)) := by
    simp only [Submonoid.map_powers, Algebra.TensorProduct.includeRight_apply]
    infer_instance
  IsLocalization.tensorProductEquivOfMapIncludeRight_tmul _ _ _ _ _ _

namespace IsLocalization.Away

/--
Instance `tensor` / 实例 `tensor`

English:
instance tensor
  signature: [IsLocalization.Away r A]
  body: by
  simp only [IsLocalization.Away, ← Algebra.algebraMapSubmonoid_powers]
  infer_instance

中文:
实例 tensor
  签名: [是Localization.Away r A]
  定义体: by
  simp only [IsLocalization.Away, ← Algebra.algebraMapSubmonoid_powers]
  infer_instance

Depends on / 依赖: Algebra, Algebra.algebraMapSubmonoid_powers, IsLocalization, IsLocalization.Away, algebraMapSubmonoid_powers, infer_instance
-/
instance tensor [IsLocalization.Away r A] :
    IsLocalization.Away (algebraMap R S r) (S otimes[R] A) := by
  simp only [IsLocalization.Away, ← Algebra.algebraMapSubmonoid_powers]
  infer_instance

variable (S) in
/--
Definition of `tensorEquiv` / `tensorEquiv` 的定义

English:
abbreviation tensorEquiv
  signature: [IsLocalization.Away r A]
  body: IsLocalization.algEquiv (Submonoid.powers <| algebraMap R S r) _ _

中文:
缩写 tensorEquiv
  签名: [是Localization.Away r A]
  定义体: IsLocalization.algEquiv (Submonoid.powers <| algebraMap R S r) _ _

Depends on / 依赖: IsLocalization, IsLocalization.algEquiv, Submonoid, Submonoid.powers, algEquiv, algebraMap, powers
-/
noncomputable abbrev tensorEquiv [IsLocalization.Away r A] :
    S otimes[R] A ≃ₐ[S] Localization.Away (algebraMap R S r) :=
  IsLocalization.algEquiv (Submonoid.powers <| algebraMap R S r) _ _

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/--
Instance `tensorRight` / 实例 `tensorRight`

English:
instance tensorRight
  signature: [IsLocalization.Away r A]
  body: by
  simp only [IsLocalization.Away, ← Algebra.algebraMapSubmonoid_powers]
  infer_instance

中文:
实例 tensorRight
  签名: [是Localization.Away r A]
  定义体: by
  simp only [IsLocalization.Away, ← Algebra.algebraMapSubmonoid_powers]
  infer_instance

Depends on / 依赖: Algebra, Algebra.algebraMapSubmonoid_powers, IsLocalization, IsLocalization.Away, algebraMapSubmonoid_powers, infer_instance
-/
instance tensorRight [IsLocalization.Away r A] :
    IsLocalization.Away (algebraMap R S r) (A otimes[R] S) := by
  simp only [IsLocalization.Away, ← Algebra.algebraMapSubmonoid_powers]
  infer_instance

variable (S) in
/--
Definition of `tensorRightEquiv` / `tensorRightEquiv` 的定义

English:
abbreviation tensorRightEquiv
  signature: [IsLocalization.Away r A]
  body: IsLocalization.algEquiv (Submonoid.powers <| algebraMap R S r) _ _

中文:
缩写 tensorRightEquiv
  签名: [是Localization.Away r A]
  定义体: IsLocalization.algEquiv (Submonoid.powers <| algebraMap R S r) _ _

Depends on / 依赖: IsLocalization, IsLocalization.algEquiv, Submonoid, Submonoid.powers, algEquiv, algebraMap, powers
-/
noncomputable abbrev tensorRightEquiv [IsLocalization.Away r A] :
    A otimes[R] S ≃ₐ[S] Localization.Away (algebraMap R S r) :=
  IsLocalization.algEquiv (Submonoid.powers <| algebraMap R S r) _ _

end IsLocalization.Away

end
