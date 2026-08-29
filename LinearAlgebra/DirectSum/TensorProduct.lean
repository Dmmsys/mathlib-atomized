/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Algebra.DirectSum.Module
/-!
# Tensor products of direct sums

This file shows that taking `TensorProduct`s commutes with taking `DirectSum`s in both arguments.

## Main results

* `TensorProduct.directSum`
* `TensorProduct.directSumLeft`
* `TensorProduct.directSumRight`
-/

@[expose] public section

universe u v₁ v₂ w₁ w₁' w₂ w₂'

section Ring

namespace TensorProduct

open TensorProduct

open DirectSum

open LinearMap

attribute [local ext] TensorProduct.ext

variable (R : Type u) [CommSemiring R] (S) [Semiring S] [Algebra R S]
variable {ι₁ : Type v₁} {ι₂ : Type v₂}
variable [DecidableEq ι₁] [DecidableEq ι₂]
variable (M₁ : ι₁ -> Type w₁) (M₁' : Type w₁') (M₂ : ι₂ -> Type w₂) (M₂' : Type w₂')
variable [forall i₁, AddCommMonoid (M₁ i₁)] [AddCommMonoid M₁']
variable [forall i₂, AddCommMonoid (M₂ i₂)] [AddCommMonoid M₂']
variable [forall i₁, Module R (M₁ i₁)] [Module R M₁'] [forall i₂, Module R (M₂ i₂)] [Module R M₂']
variable [forall i₁, Module S (M₁ i₁)] [forall i₁, IsScalarTower R S (M₁ i₁)]
variable [Module S M₁'] [IsScalarTower R S M₁']

/--
Definition of `directSum` / `directSum` 的定义

English:
definition directSum
  signature: :
  body: by
  refine LinearEquiv.ofLinearMap ?toFun ?invFun ?left ?right
· exact AlgebraTensorModule.lift
toModule S _ _ fun i₁ => flip toModule R _ _ fun i₂ => flip AlgebraTensorModule.curry
      DirectSum.lof S (ι₁ × ι₂) (fun i => M₁ i.1 otimes[R] M₂ i.2) (i₁, i₂)
  · exact toModule S _ _ fun i => AlgebraTensorModule.map (lof S _ M₁ i.1) (lof R _ M₂ i.2)
  · ext ⟨i₁, i₂⟩ x₁ x₂ : 4
    simp only [coe_comp, Function.comp_apply, toModule_lof, AlgebraTensorModule.map_tmul,
      AlgebraTensorModule.lift_apply, lift.tmul, coe_restrictScalars, flip_apply,
      AlgebraTensorModule.curry_apply, curry_apply, id_comp]
  · ext i₁ i₂ x₁ x₂ : 5
    simp only [coe_comp, Function.comp_apply, AlgebraTensorModule.curry_apply, curry_apply,
      coe_restrictScalars, AlgebraTensorModule.lift_apply, lift.tmul, toModule_lof, flip_apply,
      AlgebraTensorModule.map_tmul, id_coe, id_eq]

中文:
定义 directSum
  签名: :
  定义体: by
  refine LinearEquiv.ofLinearMap ?toFun ?invFun ?left ?right
· exact AlgebraTensorModule.lift
toModule S _ _ fun i₁ => flip toModule R _ _ fun i₂ => flip AlgebraTensorModule.curry
      DirectSum.lof S (ι₁ × ι₂) (fun i => M₁ i.1 otimes[R] M₂ i.2) (i₁, i₂)
  · exact toModule S _ _ fun i => AlgebraTensorModule.map (lof S _ M₁ i.1) (lof R _ M₂ i.2)
  · ext ⟨i₁, i₂⟩ x₁ x₂ : 4
    simp only [coe_comp, Function.comp_apply, toModule_lof, AlgebraTensorModule.map_tmul,
      AlgebraTensorModule.lift_apply, lift.tmul, coe_restrictScalars, flip_apply,
      AlgebraTensorModule.curry_apply, curry_apply, id_comp]
  · ext i₁ i₂ x₁ x₂ : 5
    simp only [coe_comp, Function.comp_apply, AlgebraTensorModule.curry_apply, curry_apply,
      coe_restrictScalars, AlgebraTensorModule.lift_apply, lift.tmul, toModule_lof, flip_apply,
      AlgebraTensorModule.map_tmul, id_coe, id_eq]
-/
protected def directSum :
    ((⨁ i₁, M₁ i₁) otimes[R] ⨁ i₂, M₂ i₂) ≃ₗ[S] ⨁ i : ι₁ × ι₂, M₁ i.1 otimes[R] M₂ i.2 := by
  refine LinearEquiv.ofLinearMap ?toFun ?invFun ?left ?right
· exact AlgebraTensorModule.lift
toModule S _ _ fun i₁ => flip toModule R _ _ fun i₂ => flip AlgebraTensorModule.curry
      DirectSum.lof S (ι₁ × ι₂) (fun i => M₁ i.1 otimes[R] M₂ i.2) (i₁, i₂)
  · exact toModule S _ _ fun i => AlgebraTensorModule.map (lof S _ M₁ i.1) (lof R _ M₂ i.2)
  · ext ⟨i₁, i₂⟩ x₁ x₂ : 4
    simp only [coe_comp, Function.comp_apply, toModule_lof, AlgebraTensorModule.map_tmul,
      AlgebraTensorModule.lift_apply, lift.tmul, coe_restrictScalars, flip_apply,
      AlgebraTensorModule.curry_apply, curry_apply, id_comp]
  · ext i₁ i₂ x₁ x₂ : 5
    simp only [coe_comp, Function.comp_apply, AlgebraTensorModule.curry_apply, curry_apply,
      coe_restrictScalars, AlgebraTensorModule.lift_apply, lift.tmul, toModule_lof, flip_apply,
      AlgebraTensorModule.map_tmul, id_coe, id_eq]

/--
Definition of `directSumLeft` / `directSumLeft` 的定义

English:
definition directSumLeft
  signature: : (⨁ i₁, M₁ i₁) otimes[R] M₂' ≃ₗ[S] ⨁ i, M₁ i otimes[R] M₂'
  body: TensorProduct.AlgebraTensorModule.congr 1 (DirectSum.lid _ _).symm ≪≫ₗ
  TensorProduct.directSum R S M₁ (fun _ : Unit => M₂') ≪≫ₗ
  DirectSum.lequivCongrLeft S (Equiv.prodUnique _ _)

中文:
定义 directSumLeft
  签名: : (⨁ i₁, M₁ i₁) otimes[R] M₂' ≃ₗ[S] ⨁ i, M₁ i otimes[R] M₂'
  定义体: TensorProduct.AlgebraTensorModule.congr 1 (DirectSum.lid _ _).symm ≪≫ₗ
  TensorProduct.directSum R S M₁ (fun _ : Unit => M₂') ≪≫ₗ
  DirectSum.lequivCongrLeft S (Equiv.prodUnique _ _)

Depends on / 依赖: AlgebraTensorModule, DirectSum, DirectSum.lequivCongrLeft, DirectSum.lid, ENNReal, ENNReal.mul_rpow_of_nonneg, Equiv.prodUnique, TensorProduct, TensorProduct.AlgebraTensorModule.congr, TensorProduct.directSum, directSum, eLpNorm, lequivCongrLeft, mul_rpow_of_nonneg, prodUnique
-/
def directSumLeft : (⨁ i₁, M₁ i₁) otimes[R] M₂' ≃ₗ[S] ⨁ i, M₁ i otimes[R] M₂' :=
  TensorProduct.AlgebraTensorModule.congr 1 (DirectSum.lid _ _).symm ≪≫ₗ
  TensorProduct.directSum R S M₁ (fun _ : Unit => M₂') ≪≫ₗ
  DirectSum.lequivCongrLeft S (Equiv.prodUnique _ _)

/--
Definition of `directSumRight` / `directSumRight` 的定义

English:
definition directSumRight
  signature: : (M₁' otimes[R] ⨁ i, M₂ i) ≃ₗ[S] ⨁ i, M₁' otimes[R] M₂ i
  body: TensorProduct.AlgebraTensorModule.congr (DirectSum.lid _ _).symm 1 ≪≫ₗ
  TensorProduct.directSum R S (fun _ : Unit => M₁') M₂ ≪≫ₗ
  DirectSum.lequivCongrLeft S (Equiv.uniqueProd _ _)

@[deprecated (since := "2026-03-04")] alias directSumRight' := directSumRight

中文:
定义 directSumRight
  签名: : (M₁' otimes[R] ⨁ i, M₂ i) ≃ₗ[S] ⨁ i, M₁' otimes[R] M₂ i
  定义体: TensorProduct.AlgebraTensorModule.congr (DirectSum.lid _ _).symm 1 ≪≫ₗ
  TensorProduct.directSum R S (fun _ : Unit => M₁') M₂ ≪≫ₗ
  DirectSum.lequivCongrLeft S (Equiv.uniqueProd _ _)

@[deprecated (since := "2026-03-04")] alias directSumRight' := directSumRight

Depends on / 依赖: AlgebraTensorModule, DirectSum, DirectSum.lequivCongrLeft, DirectSum.lid, Equiv.uniqueProd, TensorProduct, TensorProduct.AlgebraTensorModule.congr, TensorProduct.directSum, directSum, lequivCongrLeft, uniqueProd
-/
def directSumRight : (M₁' otimes[R] ⨁ i, M₂ i) ≃ₗ[S] ⨁ i, M₁' otimes[R] M₂ i :=
  TensorProduct.AlgebraTensorModule.congr (DirectSum.lid _ _).symm 1 ≪≫ₗ
  TensorProduct.directSum R S (fun _ : Unit => M₁') M₂ ≪≫ₗ
  DirectSum.lequivCongrLeft S (Equiv.uniqueProd _ _)

@[deprecated (since := "2026-03-04")] alias directSumRight' := directSumRight

variable {M₁ M₁' M₂ M₂'}

@[simp]
/--
theorem `directSum_lof_tmul_lof` / 定理 `directSum_lof_tmul_lof`

English:
theorem directSum_lof_tmul_lof
  given: (i₁ : ι₁) (m₁ : M₁ i₁) (i₂ : ι₂) (m₂ : M₂ i₂)
  proof: by
  simp [TensorProduct.directSum]

@[simp]

中文:
定理 directSum_lof_tmul_lof
  条件: (i₁ : ι₁) (m₁ : M₁ i₁) (i₂ : ι₂) (m₂ : M₂ i₂)
  证明: by
  simp [TensorProduct.directSum]

@[simp]

Depends on / 依赖: TensorProduct, TensorProduct.directSum, directSum
-/
theorem directSum_lof_tmul_lof (i₁ : ι₁) (m₁ : M₁ i₁) (i₂ : ι₂) (m₂ : M₂ i₂) :
    TensorProduct.directSum R S M₁ M₂ (DirectSum.lof S ι₁ M₁ i₁ m₁ otimesₜ DirectSum.lof R ι₂ M₂ i₂ m₂) =
      DirectSum.lof S (ι₁ × ι₂) (fun i => M₁ i.1 otimes[R] M₂ i.2) (i₁, i₂) (m₁ otimesₜ m₂) := by
  simp [TensorProduct.directSum]

@[simp]
/--
theorem `directSum_symm_lof_tmul` / 定理 `directSum_symm_lof_tmul`

English:
theorem directSum_symm_lof_tmul
  given: (i₁ : ι₁) (m₁ : M₁ i₁) (i₂ : ι₂) (m₂ : M₂ i₂)
  proof: by
  rw [LinearEquiv.symm_apply_eq]; rw [directSum_lof_tmul_lof]

中文:
定理 directSum_symm_lof_tmul
  条件: (i₁ : ι₁) (m₁ : M₁ i₁) (i₂ : ι₂) (m₂ : M₂ i₂)
  证明: by
  rw [LinearEquiv.symm_apply_eq]; rw [directSum_lof_tmul_lof]

Depends on / 依赖: LinearEquiv, LinearEquiv.symm_apply_eq, directSum_lof_tmul_lof, symm_apply_eq
-/
theorem directSum_symm_lof_tmul (i₁ : ι₁) (m₁ : M₁ i₁) (i₂ : ι₂) (m₂ : M₂ i₂) :
    (TensorProduct.directSum R S M₁ M₂).symm
      (DirectSum.lof S (ι₁ × ι₂) (fun i => M₁ i.1 otimes[R] M₂ i.2) (i₁, i₂) (m₁ otimesₜ m₂)) =
      (DirectSum.lof S ι₁ M₁ i₁ m₁ otimesₜ DirectSum.lof R ι₂ M₂ i₂ m₂) := by
  rw [LinearEquiv.symm_apply_eq]; rw [directSum_lof_tmul_lof]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `directSumLeft_tmul_lof` / 定理 `directSumLeft_tmul_lof`

English:
theorem directSumLeft_tmul_lof
  given: (i : ι₁) (x : M₁ i) (y : M₂')
  proof: by
  simpa [directSumLeft] using! lequivCongrLeft_lof S (by simp) _ _ rfl

@[simp]

中文:
定理 directSumLeft_tmul_lof
  条件: (i : ι₁) (x : M₁ i) (y : M₂')
  证明: by
  simpa [directSumLeft] using! lequivCongrLeft_lof S (by simp) _ _ rfl

@[simp]

Depends on / 依赖: directSumLeft, lequivCongrLeft_lof
-/
theorem directSumLeft_tmul_lof (i : ι₁) (x : M₁ i) (y : M₂') :
    directSumLeft R S M₁ M₂' (DirectSum.lof S _ _ i x otimesₜ[R] y) =
    DirectSum.lof S _ _ i (x otimesₜ[R] y) := by
  simpa [directSumLeft] using! lequivCongrLeft_lof S (by simp) _ _ rfl

@[simp]
/--
theorem `directSumLeft_symm_lof_tmul` / 定理 `directSumLeft_symm_lof_tmul`

English:
theorem directSumLeft_symm_lof_tmul
  given: (i : ι₁) (x : M₁ i) (y : M₂')
  proof: by
  rw [LinearEquiv.symm_apply_eq]; rw [directSumLeft_tmul_lof]

中文:
定理 directSumLeft_symm_lof_tmul
  条件: (i : ι₁) (x : M₁ i) (y : M₂')
  证明: by
  rw [LinearEquiv.symm_apply_eq]; rw [directSumLeft_tmul_lof]

Depends on / 依赖: LinearEquiv, LinearEquiv.symm_apply_eq, directSumLeft_tmul_lof, symm_apply_eq
-/
theorem directSumLeft_symm_lof_tmul (i : ι₁) (x : M₁ i) (y : M₂') :
    (directSumLeft R S M₁ M₂').symm (DirectSum.lof S _ _ i (x otimesₜ[R] y)) =
      DirectSum.lof S _ _ i x otimesₜ[R] y := by
  rw [LinearEquiv.symm_apply_eq]; rw [directSumLeft_tmul_lof]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `directSumLeft_tmul` / 引理 `directSumLeft_tmul`

English:
lemma directSumLeft_tmul
  given: (m : ⨁ i, M₁ i) (n : M₂') (i : ι₁)
  proof: by
  suffices (DirectSum.component S ι₁ _ i) ∘ₗ (directSumLeft R S M₁ M₂').toLinearMap ∘ₗ
      ((AlgebraTensorModule.mk R S (⨁ i, M₁ i) M₂').flip n) =
        ((AlgebraTensorModule.mk R S (M₁ i) M₂').flip n) ∘ₗ (DirectSum.component S ι₁ M₁ i) by
    simpa using! LinearMap.congr_fun this m
  ext j n
  by_cases hj : j = i
  · subst hj; simp
  · simp [DirectSum.component.of, hj]

中文:
引理 directSumLeft_tmul
  条件: (m : ⨁ i, M₁ i) (n : M₂') (i : ι₁)
  证明: by
  suffices (DirectSum.component S ι₁ _ i) ∘ₗ (directSumLeft R S M₁ M₂').toLinearMap ∘ₗ
      ((AlgebraTensorModule.mk R S (⨁ i, M₁ i) M₂').flip n) =
        ((AlgebraTensorModule.mk R S (M₁ i) M₂').flip n) ∘ₗ (DirectSum.component S ι₁ M₁ i) by
    simpa using! LinearMap.congr_fun this m
  ext j n
  by_cases hj : j = i
  · subst hj; simp
  · simp [DirectSum.component.of, hj]

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.mk, DirectSum, DirectSum.component, DirectSum.component.of, LinearMap, LinearMap.congr_fun, component, congr_fun, directSumLeft, toLinearMap
-/
lemma directSumLeft_tmul (m : ⨁ i, M₁ i) (n : M₂') (i : ι₁) :
    directSumLeft R S M₁ M₂' (m otimesₜ[R] n) i = (m i) otimesₜ[R] n := by
  suffices (DirectSum.component S ι₁ _ i) ∘ₗ (directSumLeft R S M₁ M₂').toLinearMap ∘ₗ
      ((AlgebraTensorModule.mk R S (⨁ i, M₁ i) M₂').flip n) =
        ((AlgebraTensorModule.mk R S (M₁ i) M₂').flip n) ∘ₗ (DirectSum.component S ι₁ M₁ i) by
    simpa using! LinearMap.congr_fun this m
  ext j n
  by_cases hj : j = i
  · subst hj; simp
  · simp [DirectSum.component.of, hj]

/--
lemma `directSumLeft_symm_of` / 引理 `directSumLeft_symm_of`

English:
lemma directSumLeft_symm_of
  given: {i : ι₁} (x : (M₁ i) otimes[R] M₂')
  proof: by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => rw [← lof_eq_of S, directSumLeft_symm_lof_tmul, rTensor_tmul, lof_eq_of, lof_eq_of]
  | add x y h₁ h₂ => simp [h₁, h₂]

中文:
引理 directSumLeft_symm_of
  条件: {i : ι₁} (x : (M₁ i) otimes[R] M₂')
  证明: by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => rw [← lof_eq_of S, directSumLeft_symm_lof_tmul, rTensor_tmul, lof_eq_of, lof_eq_of]
  | add x y h₁ h₂ => simp [h₁, h₂]

Depends on / 依赖: TensorProduct, TensorProduct.induction_on, directSumLeft_symm_lof_tmul, induction_on, lof_eq_of, rTensor_tmul
-/
lemma directSumLeft_symm_of {i : ι₁} (x : (M₁ i) otimes[R] M₂') :
    (directSumLeft R S M₁ M₂').symm ((of (fun i => M₁ i otimes[R] M₂') i) x) =
      rTensor M₂' (lof R ι₁ M₁ i) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => rw [← lof_eq_of S, directSumLeft_symm_lof_tmul, rTensor_tmul, lof_eq_of, lof_eq_of]
  | add x y h₁ h₂ => simp [h₁, h₂]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `directSumRight_tmul_lof` / 定理 `directSumRight_tmul_lof`

English:
theorem directSumRight_tmul_lof
  given: (x : M₁') (i : ι₂) (y : M₂ i)
  proof: by
  simpa [directSumRight] using! lequivCongrLeft_lof S (by simp) _ _ rfl

@[simp]

中文:
定理 directSumRight_tmul_lof
  条件: (x : M₁') (i : ι₂) (y : M₂ i)
  证明: by
  simpa [directSumRight] using! lequivCongrLeft_lof S (by simp) _ _ rfl

@[simp]

Depends on / 依赖: directSumRight, lequivCongrLeft_lof
-/
theorem directSumRight_tmul_lof (x : M₁') (i : ι₂) (y : M₂ i) :
    directSumRight R S M₁' M₂ (x otimesₜ[R] DirectSum.lof R _ _ i y) =
    DirectSum.lof S _ _ i (x otimesₜ[R] y) := by
  simpa [directSumRight] using! lequivCongrLeft_lof S (by simp) _ _ rfl

@[simp]
/--
theorem `directSumRight_symm_lof_tmul` / 定理 `directSumRight_symm_lof_tmul`

English:
theorem directSumRight_symm_lof_tmul
  given: (x : M₁') (i : ι₂) (y : M₂ i)
  proof: by
  rw [LinearEquiv.symm_apply_eq]; rw [directSumRight_tmul_lof]

中文:
定理 directSumRight_symm_lof_tmul
  条件: (x : M₁') (i : ι₂) (y : M₂ i)
  证明: by
  rw [LinearEquiv.symm_apply_eq]; rw [directSumRight_tmul_lof]

Depends on / 依赖: LinearEquiv, LinearEquiv.symm_apply_eq, directSumRight_tmul_lof, symm_apply_eq
-/
theorem directSumRight_symm_lof_tmul (x : M₁') (i : ι₂) (y : M₂ i) :
    (directSumRight R S M₁' M₂).symm (DirectSum.lof S _ _ i (x otimesₜ[R] y)) =
      x otimesₜ[R] DirectSum.lof R _ _ i y := by
  rw [LinearEquiv.symm_apply_eq]; rw [directSumRight_tmul_lof]

/--
lemma `directSumRight_comp_rTensor` / 引理 `directSumRight_comp_rTensor`

English:
lemma directSumRight_comp_rTensor
  given: (f : M₁' ->ₗ[R] M₂')
  proof: by
  ext; simp

@[simp]

中文:
引理 directSumRight_comp_rTensor
  条件: (f : M₁' ->ₗ[R] M₂')
  证明: by
  ext; simp

@[simp]
-/
lemma directSumRight_comp_rTensor (f : M₁' ->ₗ[R] M₂') :
    (directSumRight R R M₂' M₁).toLinearMap ∘ₗ f.rTensor _ =
      (lmap fun _ => f.rTensor _) ∘ₗ directSumRight R R M₁' M₁ := by
  ext; simp

@[simp]
/--
lemma `directSumRight_tmul` / 引理 `directSumRight_tmul`

English:
lemma directSumRight_tmul
  given: (m : M₁') (n : ⨁ i, M₂ i) (i : ι₂)
  proof: by
  suffices (DirectSum.component S ι₂ _ i).restrictScalars R ∘ₗ
      (directSumRight R S M₁' M₂).toLinearMap.restrictScalars R ∘ₗ
        (TensorProduct.mk R M₁' (⨁ i, M₂ i) m) =
          (TensorProduct.mk R M₁' (M₂ i) m) ∘ₗ (DirectSum.component R ι₂ M₂ i) by
    simpa using! LinearMap.congr_fun this n
  ext j n
  by_cases hj : j = i
  · subst hj; simp
  · simp [DirectSum.component.of, hj]

中文:
引理 directSumRight_tmul
  条件: (m : M₁') (n : ⨁ i, M₂ i) (i : ι₂)
  证明: by
  suffices (DirectSum.component S ι₂ _ i).restrictScalars R ∘ₗ
      (directSumRight R S M₁' M₂).toLinearMap.restrictScalars R ∘ₗ
        (TensorProduct.mk R M₁' (⨁ i, M₂ i) m) =
          (TensorProduct.mk R M₁' (M₂ i) m) ∘ₗ (DirectSum.component R ι₂ M₂ i) by
    simpa using! LinearMap.congr_fun this n
  ext j n
  by_cases hj : j = i
  · subst hj; simp
  · simp [DirectSum.component.of, hj]

Depends on / 依赖: DirectSum, DirectSum.component, DirectSum.component.of, LinearMap, LinearMap.congr_fun, TensorProduct, TensorProduct.mk, component, congr_fun, directSumRight, restrictScalars, toLinearMap, toLinearMap.restrictScalars
-/
lemma directSumRight_tmul (m : M₁') (n : ⨁ i, M₂ i) (i : ι₂) :
    directSumRight R S M₁' M₂ (m otimesₜ[R] n) i = m otimesₜ[R] (n i) := by
  suffices (DirectSum.component S ι₂ _ i).restrictScalars R ∘ₗ
      (directSumRight R S M₁' M₂).toLinearMap.restrictScalars R ∘ₗ
        (TensorProduct.mk R M₁' (⨁ i, M₂ i) m) =
          (TensorProduct.mk R M₁' (M₂ i) m) ∘ₗ (DirectSum.component R ι₂ M₂ i) by
    simpa using! LinearMap.congr_fun this n
  ext j n
  by_cases hj : j = i
  · subst hj; simp
  · simp [DirectSum.component.of, hj]

variable (S₀ : Type*) [CommSemiring S₀] [Algebra R S₀] [Algebra S₀ S]
  [Module S₀ M₁'] [IsScalarTower R S₀ M₁'] [IsScalarTower S₀ S M₁']

set_option backward.isDefEq.respectTransparency false in
/--
lemma `restrictScalar_directSumRight` / 引理 `restrictScalar_directSumRight`

English:
lemma restrictScalar_directSumRight
  proof: LinearEquiv.restrictScalars_injective R LinearEquiv.toLinearMap_injective by ext; simp [lof]

@[deprecated (since := "2026-03-04")]
alias directSumRight'_restrict := restrictScalar_directSumRight

中文:
引理 restrictScalar_directSumRight
  证明: LinearEquiv.restrictScalars_injective R LinearEquiv.toLinearMap_injective by ext; simp [lof]

@[deprecated (since := "2026-03-04")]
alias directSumRight'_restrict := restrictScalar_directSumRight

Depends on / 依赖: LinearEquiv, LinearEquiv.restrictScalars_injective, LinearEquiv.toLinearMap_injective, restrictScalars_injective, toLinearMap_injective
-/
lemma restrictScalar_directSumRight :
    (directSumRight R S M₁' M₂).restrictScalars S₀ = directSumRight R S₀ M₁' M₂ :=
LinearEquiv.restrictScalars_injective R LinearEquiv.toLinearMap_injective by ext; simp [lof]

@[deprecated (since := "2026-03-04")]
alias directSumRight'_restrict := restrictScalar_directSumRight

/--
lemma `coe_directSumRight` / 引理 `coe_directSumRight`

English:
lemma coe_directSumRight
  proof: congr($(restrictScalar_directSumRight ..))

@[deprecated (since := "2026-03-04")] alias coe_directSumRight' := coe_directSumRight

中文:
引理 coe_directSumRight
  证明: congr($(restrictScalar_directSumRight ..))

@[deprecated (since := "2026-03-04")] alias coe_directSumRight' := coe_directSumRight

Depends on / 依赖: restrictScalar_directSumRight
-/
lemma coe_directSumRight :
    ⇑(directSumRight R S M₁' M₂) = directSumRight R R M₁' M₂ :=
  congr($(restrictScalar_directSumRight ..))

@[deprecated (since := "2026-03-04")] alias coe_directSumRight' := coe_directSumRight

end TensorProduct

end Ring
