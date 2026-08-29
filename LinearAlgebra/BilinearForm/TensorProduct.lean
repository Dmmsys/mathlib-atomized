/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Hom
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# The bilinear form on a tensor product

## Main definitions

* `LinearMap.BilinMap.tensorDistrib (B₁ ⊗ₜ B₂)`: the bilinear form on `M₁ ⊗ M₂` constructed by
  applying `B₁` on `M₁` and `B₂` on `M₂`.
* `LinearMap.BilinMap.tensorDistribEquiv`: `BilinForm.tensorDistrib` as an equivalence on finite
  free modules.

-/

@[expose] public section

universe u v w uR uA uM₁ uM₂ uN₁ uN₂

variable {R : Type uR} {A : Type uA} {M₁ : Type uM₁} {M₂ : Type uM₂} {N₁ : Type uN₁} {N₂ : Type uN₂}

open TensorProduct

namespace LinearMap

open LinearMap (BilinMap BilinForm)

section CommSemiring

variable [CommSemiring R] [CommSemiring A]
variable [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid N₁] [AddCommMonoid N₂]
variable [Algebra R A] [Module R M₁] [Module A M₁] [Module R N₁] [Module A N₁]
variable [SMulCommClass R A M₁] [IsScalarTower R A M₁]
variable [SMulCommClass R A N₁] [IsScalarTower R A N₁]
variable [Module R M₂] [Module R N₂]

namespace BilinMap

variable (R A) in
/--
Definition of `tensorDistrib` / `tensorDistrib` 的定义

English:
definition tensorDistrib
  signature: :
  body: (TensorProduct.lift.equiv (.id A) (M₁ otimes[R] M₂) (M₁ otimes[R] M₂) (N₁ otimes[R] N₂)).symm.toLinearMap ∘ₗ
  ((LinearMap.llcomp A _ _ _).flip
    (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R R A A M₁ M₂ M₁ M₂).toLinearMap)
  ∘ₗ TensorProduct.AlgebraTensorModule.homTensorHomMap R _ _

中文:
定义 tensorDistrib
  签名: :
  定义体: (TensorProduct.lift.equiv (.id A) (M₁ otimes[R] M₂) (M₁ otimes[R] M₂) (N₁ otimes[R] N₂)).symm.toLinearMap ∘ₗ
  ((LinearMap.llcomp A _ _ _).flip
    (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R R A A M₁ M₂ M₁ M₂).toLinearMap)
  ∘ₗ TensorProduct.AlgebraTensorModule.homTensorHomMap R _ _

Depends on / 依赖: AlgebraTensorModule, LinearMap, LinearMap.llcomp, TensorProduct, TensorProduct.AlgebraTensorModule.congr, TensorProduct.AlgebraTensorModule.homTensorHomMap, TensorProduct.AlgebraTensorModule.tensorTensorTensorComm, TensorProduct.lift.equiv, homTensorHomMap, llcomp, otimes, symm.toLinearMap, tensorTensorTensorComm, toLinearMap
-/
def tensorDistrib :
    (BilinMap A M₁ N₁ otimes[R] BilinMap R M₂ N₂) ->ₗ[A] BilinMap A (M₁ otimes[R] M₂) (N₁ otimes[R] N₂) :=
  (TensorProduct.lift.equiv (.id A) (M₁ otimes[R] M₂) (M₁ otimes[R] M₂) (N₁ otimes[R] N₂)).symm.toLinearMap ∘ₗ
  ((LinearMap.llcomp A _ _ _).flip
    (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R R A A M₁ M₂ M₁ M₂).toLinearMap)
  ∘ₗ TensorProduct.AlgebraTensorModule.homTensorHomMap R _ _ _ _ _ _
  ∘ₗ (TensorProduct.AlgebraTensorModule.congr
    (TensorProduct.lift.equiv (.id A) M₁ M₁ N₁)
    (TensorProduct.lift.equiv (.id R) _ _ _)).toLinearMap

@[simp]
/--
theorem `tensorDistrib_tmul` / 定理 `tensorDistrib_tmul`

English:
theorem tensorDistrib_tmul
  statement: (B₁ : BilinMap A M₁ N₁) (B₂ : BilinMap R M₂ N₂) (m₁ : M₁) (m₂ : M₂)
  proof: rfl

中文:
定理 tensorDistrib_tmul
  结论: (B₁ : BilinMap A M₁ N₁) (B₂ : BilinMap R M₂ N₂) (m₁ : M₁) (m₂ : M₂)
  证明: rfl
-/
theorem tensorDistrib_tmul (B₁ : BilinMap A M₁ N₁) (B₂ : BilinMap R M₂ N₂) (m₁ : M₁) (m₂ : M₂)
    (m₁' : M₁) (m₂' : M₂) :
    tensorDistrib R A (B₁ otimesₜ B₂) (m₁ otimesₜ m₂) (m₁' otimesₜ m₂')
      = B₁ m₁ m₁' otimesₜ B₂ m₂ m₂' :=
  rfl

/--
Definition of `tmul` / `tmul` 的定义

English:
abbreviation tmul
  signature: (B₁ : BilinMap A M₁ N₁) (B₂ : BilinMap R M₂ N₂)
  body: tensorDistrib R A (B₁ otimesₜ[R] B₂)

中文:
缩写 tmul
  签名: (B₁ : BilinMap A M₁ N₁) (B₂ : BilinMap R M₂ N₂)
  定义体: tensorDistrib R A (B₁ otimesₜ[R] B₂)
-/
protected abbrev tmul (B₁ : BilinMap A M₁ N₁) (B₂ : BilinMap R M₂ N₂) :
    BilinMap A (M₁ otimes[R] M₂) (N₁ otimes[R] N₂) :=
  tensorDistrib R A (B₁ otimesₜ[R] B₂)

attribute [local ext] TensorProduct.ext in
/--
lemma `tmul_isSymm` / 引理 `tmul_isSymm`

English:
lemma tmul_isSymm
  statement: {B₁ : BilinMap A M₁ N₁} {B₂ : BilinMap R M₂ N₂}
  proof: by
  revert x y
  rw [isSymm_iff_eq_flip]
  aesop

中文:
引理 tmul_isSymm
  结论: {B₁ : BilinMap A M₁ N₁} {B₂ : BilinMap R M₂ N₂}
  证明: by
  revert x y
  rw [isSymm_iff_eq_flip]
  aesop

Depends on / 依赖: isSymm_iff_eq_flip, revert
-/
lemma tmul_isSymm {B₁ : BilinMap A M₁ N₁} {B₂ : BilinMap R M₂ N₂}
    (hB₁ : forall x y, B₁ x y = B₁ y x) (hB₂ : forall x y, B₂ x y = B₂ y x)
    (x y : M₁ otimes[R] M₂) :
    B₁.tmul B₂ x y = B₁.tmul B₂ y x := by
  revert x y
  rw [isSymm_iff_eq_flip]
  aesop

variable (A) in
/--
Definition of `baseChange` / `baseChange` 的定义

English:
definition baseChange
  signature: (B : BilinMap R M₂ N₂)
  body: BilinMap.tmul (R := R) (A := A) (M₁ := A) (M₂ := M₂) (LinearMap.mul A A) B

@[simp]

中文:
定义 baseChange
  签名: (B : BilinMap R M₂ N₂)
  定义体: BilinMap.tmul (R := R) (A := A) (M₁ := A) (M₂ := M₂) (LinearMap.mul A A) B

@[simp]
-/
protected def baseChange (B : BilinMap R M₂ N₂) : BilinMap A (A otimes[R] M₂) (A otimes[R] N₂) :=
  BilinMap.tmul (R := R) (A := A) (M₁ := A) (M₂ := M₂) (LinearMap.mul A A) B

@[simp]
/--
theorem `baseChange_tmul` / 定理 `baseChange_tmul`

English:
theorem baseChange_tmul
  statement: (B₂ : BilinMap R M₂ N₂) (a : A) (m₂ : M₂)
  proof: rfl

中文:
定理 baseChange_tmul
  结论: (B₂ : BilinMap R M₂ N₂) (a : A) (m₂ : M₂)
  证明: rfl
-/
theorem baseChange_tmul (B₂ : BilinMap R M₂ N₂) (a : A) (m₂ : M₂)
    (a' : A) (m₂' : M₂) :
    B₂.baseChange A (a otimesₜ m₂) (a' otimesₜ m₂') = (a * a') otimesₜ (B₂ m₂ m₂') :=
  rfl

/--
lemma `baseChange_isSymm` / 引理 `baseChange_isSymm`

English:
lemma baseChange_isSymm
  given: {B₂ : BilinMap R M₂ N₂} (hB₂ : forall x y, B₂ x y = B₂ y x) (x y : A otimes[R] M₂)
  proof: tmul_isSymm mul_comm hB₂ x y

中文:
引理 baseChange_isSymm
  条件: {B₂ : BilinMap R M₂ N₂} (hB₂ : 对任意 x y, B₂ x y = B₂ y x) (x y : A otimes[R] M₂)
  证明: tmul_isSymm mul_comm hB₂ x y

Depends on / 依赖: mul_comm, tmul_isSymm
-/
lemma baseChange_isSymm {B₂ : BilinMap R M₂ N₂} (hB₂ : forall x y, B₂ x y = B₂ y x) (x y : A otimes[R] M₂) :
    B₂.baseChange A x y = B₂.baseChange A y x :=
  tmul_isSymm mul_comm hB₂ x y

end BilinMap

namespace BilinForm

variable (R A) in
/--
Definition of `tensorDistrib` / `tensorDistrib` 的定义

English:
definition tensorDistrib
  signature: : BilinForm A M₁ otimes[R] BilinForm R M₂ ->ₗ[A] BilinForm A (M₁ otimes[R] M₂)
  body: (AlgebraTensorModule.rid R A A).congrRight₂.toLinearMap ∘ₗ (BilinMap.tensorDistrib R A)

中文:
定义 tensorDistrib
  签名: : BilinForm A M₁ otimes[R] BilinForm R M₂ ->ₗ[A] BilinForm A (M₁ otimes[R] M₂)
  定义体: (AlgebraTensorModule.rid R A A).congrRight₂.toLinearMap ∘ₗ (BilinMap.tensorDistrib R A)

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.rid, BilinMap, BilinMap.tensorDistrib, tensorDistrib, toLinearMap
-/
def tensorDistrib : BilinForm A M₁ otimes[R] BilinForm R M₂ ->ₗ[A] BilinForm A (M₁ otimes[R] M₂) :=
  (AlgebraTensorModule.rid R A A).congrRight₂.toLinearMap ∘ₗ (BilinMap.tensorDistrib R A)

variable (R A) in
-- TODO: make the RHS `MulOpposite.op (B₂ m₂ m₂') • B₁ m₁ m₁'` so that this has a nicer defeq for
-- `R = A` of `B₁ m₁ m₁' * B₂ m₂ m₂'`, as it did before the generalization in https://github.com/leanprover-community/mathlib4/pull/6306.
@[simp]
/--
theorem `tensorDistrib_tmul` / 定理 `tensorDistrib_tmul`

English:
theorem tensorDistrib_tmul
  statement: (B₁ : BilinForm A M₁) (B₂ : BilinForm R M₂) (m₁ : M₁) (m₂ : M₂)
  proof: rfl

中文:
定理 tensorDistrib_tmul
  结论: (B₁ : BilinForm A M₁) (B₂ : BilinForm R M₂) (m₁ : M₁) (m₂ : M₂)
  证明: rfl
-/
theorem tensorDistrib_tmul (B₁ : BilinForm A M₁) (B₂ : BilinForm R M₂) (m₁ : M₁) (m₂ : M₂)
    (m₁' : M₁) (m₂' : M₂) :
    tensorDistrib R A (B₁ otimesₜ B₂) (m₁ otimesₜ m₂) (m₁' otimesₜ m₂')
      = B₂ m₂ m₂' • B₁ m₁ m₁' :=
  rfl

/--
Definition of `tmul` / `tmul` 的定义

English:
abbreviation tmul
  signature: (B₁ : BilinForm A M₁) (B₂ : BilinMap R M₂ R)
  body: tensorDistrib R A (B₁ otimesₜ[R] B₂)

中文:
缩写 tmul
  签名: (B₁ : BilinForm A M₁) (B₂ : BilinMap R M₂ R)
  定义体: tensorDistrib R A (B₁ otimesₜ[R] B₂)
-/
protected abbrev tmul (B₁ : BilinForm A M₁) (B₂ : BilinMap R M₂ R) : BilinMap A (M₁ otimes[R] M₂) A :=
  tensorDistrib R A (B₁ otimesₜ[R] B₂)

attribute [local ext] TensorProduct.ext in
/--
lemma `_root_.LinearMap.IsSymm.tmul` / 引理 `_root_.LinearMap.IsSymm.tmul`

English:
lemma _root_.LinearMap.IsSymm.tmul
  statement: {B₁ : BilinForm A M₁} {B₂ : BilinForm R M₂}
  proof: by
  rw [LinearMap.isSymm_iff_eq_flip]
  ext x₁ x₂ y₁ y₂
  exact congr_arg₂ (HSMul.hSMul) (hB₂.eq x₂ y₂) (hB₁.eq x₁ y₁)

中文:
引理 _root_.LinearMap.IsSymm.tmul
  结论: {B₁ : BilinForm A M₁} {B₂ : BilinForm R M₂}
  证明: by
  rw [LinearMap.isSymm_iff_eq_flip]
  ext x₁ x₂ y₁ y₂
  exact congr_arg₂ (HSMul.hSMul) (hB₂.eq x₂ y₂) (hB₁.eq x₁ y₁)

Depends on / 依赖: HSMul.hSMul, LinearMap, LinearMap.isSymm_iff_eq_flip, isSymm_iff_eq_flip
-/
lemma _root_.LinearMap.IsSymm.tmul {B₁ : BilinForm A M₁} {B₂ : BilinForm R M₂}
    (hB₁ : B₁.IsSymm) (hB₂ : B₂.IsSymm) : (B₁.tmul B₂).IsSymm := by
  rw [LinearMap.isSymm_iff_eq_flip]
  ext x₁ x₂ y₁ y₂
  exact congr_arg₂ (HSMul.hSMul) (hB₂.eq x₂ y₂) (hB₁.eq x₁ y₁)

variable (A) in
/--
Definition of `baseChange` / `baseChange` 的定义

English:
definition baseChange
  signature: (B : BilinForm R M₂)
  body: BilinForm.tmul (R := R) (A := A) (M₁ := A) (M₂ := M₂) (LinearMap.mul A A) B

@[simp]

中文:
定义 baseChange
  签名: (B : BilinForm R M₂)
  定义体: BilinForm.tmul (R := R) (A := A) (M₁ := A) (M₂ := M₂) (LinearMap.mul A A) B

@[simp]
-/
protected def baseChange (B : BilinForm R M₂) : BilinForm A (A otimes[R] M₂) :=
  BilinForm.tmul (R := R) (A := A) (M₁ := A) (M₂ := M₂) (LinearMap.mul A A) B

@[simp]
/--
theorem `baseChange_tmul` / 定理 `baseChange_tmul`

English:
theorem baseChange_tmul
  statement: (B₂ : BilinForm R M₂) (a : A) (m₂ : M₂)
  proof: rfl

中文:
定理 baseChange_tmul
  结论: (B₂ : BilinForm R M₂) (a : A) (m₂ : M₂)
  证明: rfl
-/
theorem baseChange_tmul (B₂ : BilinForm R M₂) (a : A) (m₂ : M₂)
    (a' : A) (m₂' : M₂) :
    B₂.baseChange A (a otimesₜ m₂) (a' otimesₜ m₂') = (B₂ m₂ m₂') • (a * a') :=
  rfl

/--
lemma `baseChange_zero` / 引理 `baseChange_zero`

English:
lemma baseChange_zero
  statement: (0 : BilinForm R M₂).baseChange A = 0
  proof: by ext; simp

中文:
引理 baseChange_zero
  结论: (0 : BilinForm R M₂).baseChange A = 0
  证明: by ext; simp
-/
@[simp] lemma baseChange_zero : (0 : BilinForm R M₂).baseChange A = 0 := by ext; simp

/--
lemma `baseChange_eq_zero_iff` / 引理 `baseChange_eq_zero_iff`

English:
lemma baseChange_eq_zero_iff
  statement: [FaithfulSMul R A]
  proof: by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  ext m m'
  simpa [← Algebra.algebraMap_eq_smul_one] using LinearMap.congr_fun₂ h (1 otimesₜ[R] m) (1 otimesₜ[R] m')

中文:
引理 baseChange_eq_zero_iff
  结论: [FaithfulSMul R A]
  证明: by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  ext m m'
  simpa [← Algebra.algebraMap_eq_smul_one] using LinearMap.congr_fun₂ h (1 otimesₜ[R] m) (1 otimesₜ[R] m')
-/
@[simp] lemma baseChange_eq_zero_iff [FaithfulSMul R A]
    (B : BilinForm R M₂) : B.baseChange A = 0 ↔ B = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  ext m m'
  simpa [← Algebra.algebraMap_eq_smul_one] using LinearMap.congr_fun₂ h (1 otimesₜ[R] m) (1 otimesₜ[R] m')

variable (A) in
/--
lemma `IsSymm.baseChange` / 引理 `IsSymm.baseChange`

English:
lemma IsSymm.baseChange
  given: {B₂ : BilinForm R M₂} (hB₂ : B₂.IsSymm)
  statement: (B₂.baseChange A).IsSymm
  proof: IsSymm.tmul ⟨mul_comm⟩ hB₂

中文:
引理 IsSymm.baseChange
  条件: {B₂ : BilinForm R M₂} (hB₂ : B₂.IsSymm)
  结论: (B₂.baseChange A).IsSymm
  证明: IsSymm.tmul ⟨mul_comm⟩ hB₂

Depends on / 依赖: IsSymm, IsSymm.tmul, mul_comm
-/
lemma IsSymm.baseChange {B₂ : BilinForm R M₂} (hB₂ : B₂.IsSymm) : (B₂.baseChange A).IsSymm :=
  IsSymm.tmul ⟨mul_comm⟩ hB₂

end BilinForm

end CommSemiring

section CommRing

variable [CommRing R]
variable [AddCommGroup M₁] [AddCommGroup M₂]
variable [Module R M₁] [Module R M₂]
variable [Module.Free R M₁] [Module.Finite R M₁]
variable [Module.Free R M₂] [Module.Finite R M₂]

namespace BilinForm

variable (R) in
/--
Definition of `tensorDistribEquiv` / `tensorDistribEquiv` 的定义

English:
definition tensorDistribEquiv
  signature: :
  body: -- the same `LinearEquiv`s as from `tensorDistrib`,
  -- but with the inner linear map also as an equiv
  TensorProduct.congr
    (TensorProduct.lift.equiv (.id R) _ _ _) (TensorProduct.lift.equiv (.id R) _ _ _) ≪≫ₗ
  TensorProduct.dualDistribEquiv R (M₁ otimes M₁) (M₂ otimes M₂) ≪≫ₗ
  (TensorProduc

中文:
定义 tensorDistribEquiv
  签名: :
  定义体: -- the same `LinearEquiv`s as from `tensorDistrib`,
  -- but with the inner linear map also as an equiv
  TensorProduct.congr
    (TensorProduct.lift.equiv (.id R) _ _ _) (TensorProduct.lift.equiv (.id R) _ _ _) ≪≫ₗ
  TensorProduct.dualDistribEquiv R (M₁ otimes M₁) (M₂ otimes M₂) ≪≫ₗ
  (TensorProduc
-/
noncomputable def tensorDistribEquiv :
    BilinForm R M₁ otimes[R] BilinForm R M₂ ≃ₗ[R] BilinForm R (M₁ otimes[R] M₂) :=
  -- the same `LinearEquiv`s as from `tensorDistrib`,
  -- but with the inner linear map also as an equiv
  TensorProduct.congr
    (TensorProduct.lift.equiv (.id R) _ _ _) (TensorProduct.lift.equiv (.id R) _ _ _) ≪≫ₗ
  TensorProduct.dualDistribEquiv R (M₁ otimes M₁) (M₂ otimes M₂) ≪≫ₗ
  (TensorProduct.tensorTensorTensorComm R _ _ _ _).dualMap ≪≫ₗ
  (TensorProduct.lift.equiv (.id R) _ _ _).symm

@[simp]
/--
theorem `tensorDistribEquiv_tmul` / 定理 `tensorDistribEquiv_tmul`

English:
theorem tensorDistribEquiv_tmul
  statement: (B₁ : BilinForm R M₁) (B₂ : BilinForm R M₂) (m₁ : M₁) (m₂ : M₂)
  proof: rfl

中文:
定理 tensorDistribEquiv_tmul
  结论: (B₁ : BilinForm R M₁) (B₂ : BilinForm R M₂) (m₁ : M₁) (m₂ : M₂)
  证明: rfl
-/
theorem tensorDistribEquiv_tmul (B₁ : BilinForm R M₁) (B₂ : BilinForm R M₂) (m₁ : M₁) (m₂ : M₂)
    (m₁' : M₁) (m₂' : M₂) :
    tensorDistribEquiv R (M₁ := M₁) (M₂ := M₂) (B₁ otimesₜ[R] B₂) (m₁ otimesₜ m₂) (m₁' otimesₜ m₂')
      = B₁ m₁ m₁' * B₂ m₂ m₂' :=
  rfl

variable (R M₁ M₂) in
-- TODO: make this `rfl`
@[simp]
/--
theorem `tensorDistribEquiv_toLinearMap` / 定理 `tensorDistribEquiv_toLinearMap`

English:
theorem tensorDistribEquiv_toLinearMap
  proof: by
  ext B₁ B₂ : 3
  ext
  exact mul_comm _ _

@[simp]

中文:
定理 tensorDistribEquiv_toLinearMap
  证明: by
  ext B₁ B₂ : 3
  ext
  exact mul_comm _ _

@[simp]

Depends on / 依赖: mul_comm, tensorDistrib, toLinearMap
-/
theorem tensorDistribEquiv_toLinearMap :
    (tensorDistribEquiv R (M₁ := M₁) (M₂ := M₂)).toLinearMap = tensorDistrib R R := by
  ext B₁ B₂ : 3
  ext
  exact mul_comm _ _

@[simp]
/--
theorem `tensorDistribEquiv_apply` / 定理 `tensorDistribEquiv_apply`

English:
theorem tensorDistribEquiv_apply
  given: (B : BilinForm R M₁ otimes BilinForm R M₂)
  proof: DFunLike.congr_fun (tensorDistribEquiv_toLinearMap R M₁ M₂) B

中文:
定理 tensorDistribEquiv_apply
  条件: (B : BilinForm R M₁ otimes BilinForm R M₂)
  证明: DFunLike.congr_fun (tensorDistribEquiv_toLinearMap R M₁ M₂) B

Depends on / 依赖: tensorDistrib
-/
theorem tensorDistribEquiv_apply (B : BilinForm R M₁ otimes BilinForm R M₂) :
    tensorDistribEquiv R (M₁ := M₁) (M₂ := M₂) B = tensorDistrib R R B :=
  DFunLike.congr_fun (tensorDistribEquiv_toLinearMap R M₁ M₂) B

end BilinForm

end CommRing

end LinearMap
