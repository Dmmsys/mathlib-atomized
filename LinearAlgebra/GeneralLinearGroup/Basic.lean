/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Module.Equiv.Basic

/-!
# The general linear group of linear maps

The general linear group is defined to be the group of invertible linear maps from `M` to itself.

See also `Matrix.GeneralLinearGroup`

## Main definitions

* `LinearMap.GeneralLinearGroup`

-/

@[expose] public section


variable (R M : Type*)

namespace LinearMap

variable [Semiring R] [AddCommMonoid M] [Module R M]

/--
Definition of `GeneralLinearGroup` / `GeneralLinearGroup` 的定义

English:
abbreviation GeneralLinearGroup
  body: (M ->ₗ[R] M)ˣ

中文:
缩写 GeneralLinearGroup
  定义体: (M ->ₗ[R] M)ˣ
-/
abbrev GeneralLinearGroup :=
  (M ->ₗ[R] M)ˣ

namespace GeneralLinearGroup

variable {R M}

/--
Definition of `toLinearEquiv` / `toLinearEquiv` 的定义

English:
definition toLinearEquiv
  signature: (f : GeneralLinearGroup R M)
  body: { f.val with
    invFun := f.inv.toFun
    left_inv := fun m => show (f.inv * f.val) m = m by simp
    right_inv := fun m => show (f.val * f.inv) m = m by simp }

中文:
定义 toLinearEquiv
  签名: (f : GeneralLinearGroup R M)
  定义体: { f.val with
    invFun := f.inv.toFun
    left_inv := fun m => show (f.inv * f.val) m = m by simp
    right_inv := fun m => show (f.val * f.inv) m = m by simp }

Depends on / 依赖: f.inv, f.inv.toFun, f.val, invFun, left_inv, right_inv
-/
def toLinearEquiv (f : GeneralLinearGroup R M) : M ≃ₗ[R] M :=
  { f.val with
    invFun := f.inv.toFun
    left_inv := fun m => show (f.inv * f.val) m = m by simp
    right_inv := fun m => show (f.val * f.inv) m = m by simp }

/--
lemma `coe_toLinearEquiv` / 引理 `coe_toLinearEquiv`

English:
lemma coe_toLinearEquiv
  given: (f : GeneralLinearGroup R M)
  proof: rfl

中文:
引理 coe_toLinearEquiv
  条件: (f : GeneralLinearGroup R M)
  证明: rfl
-/
@[simp] lemma coe_toLinearEquiv (f : GeneralLinearGroup R M) :
    f.toLinearEquiv = (f : M -> M) := rfl

/--
theorem `toLinearEquiv_mul` / 定理 `toLinearEquiv_mul`

English:
theorem toLinearEquiv_mul
  given: (f g : GeneralLinearGroup R M)
  proof: by
  rfl

中文:
定理 toLinearEquiv_mul
  条件: (f g : GeneralLinearGroup R M)
  证明: by
  rfl
-/
theorem toLinearEquiv_mul (f g : GeneralLinearGroup R M) :
    (f * g).toLinearEquiv = f.toLinearEquiv * g.toLinearEquiv := by
  rfl

/--
theorem `toLinearEquiv_inv` / 定理 `toLinearEquiv_inv`

English:
theorem toLinearEquiv_inv
  given: (f : GeneralLinearGroup R M)
  proof: by
  rfl

中文:
定理 toLinearEquiv_inv
  条件: (f : GeneralLinearGroup R M)
  证明: by
  rfl
-/
theorem toLinearEquiv_inv (f : GeneralLinearGroup R M) :
    (f⁻¹).toLinearEquiv = (f.toLinearEquiv)⁻¹ := by
  rfl

/--
Definition of `ofLinearEquiv` / `ofLinearEquiv` 的定义

English:
definition ofLinearEquiv
  signature: (f : M ≃ₗ[R] M)
  body: f
  inv := (f.symm : M ->ₗ[R] M)
  val_inv := LinearMap.ext fun _ => f.apply_symm_apply _
  inv_val := LinearMap.ext fun _ => f.symm_apply_apply _

中文:
定义 ofLinearEquiv
  签名: (f : M ≃ₗ[R] M)
  定义体: f
  inv := (f.symm : M ->ₗ[R] M)
  val_inv := LinearMap.ext fun _ => f.apply_symm_apply _
  inv_val := LinearMap.ext fun _ => f.symm_apply_apply _
-/
def ofLinearEquiv (f : M ≃ₗ[R] M) : GeneralLinearGroup R M where
  val := f
  inv := (f.symm : M ->ₗ[R] M)
  val_inv := LinearMap.ext fun _ => f.apply_symm_apply _
  inv_val := LinearMap.ext fun _ => f.symm_apply_apply _

/--
lemma `coe_ofLinearEquiv` / 引理 `coe_ofLinearEquiv`

English:
lemma coe_ofLinearEquiv
  given: (f : M ≃ₗ[R] M)
  proof: rfl

中文:
引理 coe_ofLinearEquiv
  条件: (f : M ≃ₗ[R] M)
  证明: rfl
-/
@[simp] lemma coe_ofLinearEquiv (f : M ≃ₗ[R] M) :
    ofLinearEquiv f = (f : M -> M) := rfl

/--
theorem `ofLinearEquiv_mul` / 定理 `ofLinearEquiv_mul`

English:
theorem ofLinearEquiv_mul
  given: (f g : M ≃ₗ[R] M)
  proof: by
  rfl

中文:
定理 ofLinearEquiv_mul
  条件: (f g : M ≃ₗ[R] M)
  证明: by
  rfl
-/
theorem ofLinearEquiv_mul (f g : M ≃ₗ[R] M) :
    ofLinearEquiv (f * g) = ofLinearEquiv f * ofLinearEquiv g := by
  rfl

/--
theorem `ofLinearEquiv_inv` / 定理 `ofLinearEquiv_inv`

English:
theorem ofLinearEquiv_inv
  given: (f : M ≃ₗ[R] M)
  proof: by
  rfl

@[simp]

中文:
定理 ofLinearEquiv_inv
  条件: (f : M ≃ₗ[R] M)
  证明: by
  rfl

@[simp]
-/
theorem ofLinearEquiv_inv (f : M ≃ₗ[R] M) :
    ofLinearEquiv (f⁻¹) = (ofLinearEquiv f)⁻¹ := by
  rfl

@[simp]
/--
lemma `ofLinearEquiv_smul` / 引理 `ofLinearEquiv_smul`

English:
lemma ofLinearEquiv_smul
  given: (f : M ≃ₗ[R] M) (x : M)
  proof: rfl

中文:
引理 ofLinearEquiv_smul
  条件: (f : M ≃ₗ[R] M) (x : M)
  证明: rfl
-/
lemma ofLinearEquiv_smul (f : M ≃ₗ[R] M) (x : M) :
    ofLinearEquiv f • x = f x := rfl

variable (R M) in
/--
Definition of `generalLinearEquiv` / `generalLinearEquiv` 的定义

English:
definition generalLinearEquiv
  signature: : GeneralLinearGroup R M ≃* M ≃ₗ[R] M where
  body: toLinearEquiv
  invFun := ofLinearEquiv
  map_mul' x y := by ext; rfl

@[simp]

中文:
定义 generalLinearEquiv
  签名: : GeneralLinearGroup R M ≃* M ≃ₗ[R] M where
  定义体: toLinearEquiv
  invFun := ofLinearEquiv
  map_mul' x y := by ext; rfl

@[simp]

Depends on / 依赖: toLinearEquiv
-/
def generalLinearEquiv : GeneralLinearGroup R M ≃* M ≃ₗ[R] M where
  toFun := toLinearEquiv
  invFun := ofLinearEquiv
  map_mul' x y := by ext; rfl

@[simp]
/--
theorem `generalLinearEquiv_to_linearMap` / 定理 `generalLinearEquiv_to_linearMap`

English:
theorem generalLinearEquiv_to_linearMap
  given: (f : GeneralLinearGroup R M)
  proof: by ext; rfl

@[simp]

中文:
定理 generalLinearEquiv_to_linearMap
  条件: (f : GeneralLinearGroup R M)
  证明: by ext; rfl

@[simp]
-/
theorem generalLinearEquiv_to_linearMap (f : GeneralLinearGroup R M) :
    (generalLinearEquiv R M f : M ->ₗ[R] M) = f := by ext; rfl

@[simp]
/--
theorem `coeFn_generalLinearEquiv` / 定理 `coeFn_generalLinearEquiv`

English:
theorem coeFn_generalLinearEquiv
  given: (f : GeneralLinearGroup R M)
  proof: rfl

中文:
定理 coeFn_generalLinearEquiv
  条件: (f : GeneralLinearGroup R M)
  证明: rfl
-/
theorem coeFn_generalLinearEquiv (f : GeneralLinearGroup R M) :
    (generalLinearEquiv R M f) = (f : M -> M) := rfl

section Functoriality

variable {R₁ R₂ R₃ M₁ M₂ M₃ : Type*}
  [Semiring R₁] [Semiring R₂] [Semiring R₃]
  [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
  [Module R₁ M₁] [Module R₂ M₂] [Module R₃ M₃]
  {σ₁₂ : R₁ ->+* R₂} {σ₂₃ : R₂ ->+* R₃} {σ₁₃ : R₁ ->+* R₃}
  {σ₂₁ : R₂ ->+* R₁} {σ₃₂ : R₃ ->+* R₂} {σ₃₁ : R₃ ->+* R₁}
  [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₃ σ₃₂] [RingHomInvPair σ₁₃ σ₃₁]
  [RingHomInvPair σ₂₁ σ₁₂] [RingHomInvPair σ₃₂ σ₂₃] [RingHomInvPair σ₃₁ σ₁₃]
  [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₃₂ σ₂₁ σ₃₁]

/--
Definition of `congrLinearEquiv` / `congrLinearEquiv` 的定义

English:
definition congrLinearEquiv
  signature: (e₁₂ : M₁ ≃ₛₗ[σ₁₂] M₂)
  body: Units.mapEquiv (LinearEquiv.conjRingEquiv e₁₂).toMulEquiv

中文:
定义 congrLinearEquiv
  签名: (e₁₂ : M₁ ≃ₛₗ[σ₁₂] M₂)
  定义体: Units.mapEquiv (LinearEquiv.conjRingEquiv e₁₂).toMulEquiv

Depends on / 依赖: LinearEquiv, LinearEquiv.conjRingEquiv, Units.mapEquiv, conjRingEquiv, mapEquiv, toMulEquiv
-/
def congrLinearEquiv (e₁₂ : M₁ ≃ₛₗ[σ₁₂] M₂) :
    GeneralLinearGroup R₁ M₁ ≃* GeneralLinearGroup R₂ M₂ :=
  Units.mapEquiv (LinearEquiv.conjRingEquiv e₁₂).toMulEquiv

/--
lemma `congrLinearEquiv_apply` / 引理 `congrLinearEquiv_apply`

English:
lemma congrLinearEquiv_apply
  given: (e₁₂ : M₁ ≃ₛₗ[σ₁₂] M₂) (g : GeneralLinearGroup R₁ M₁)
  proof: rfl

中文:
引理 congrLinearEquiv_apply
  条件: (e₁₂ : M₁ ≃ₛₗ[σ₁₂] M₂) (g : GeneralLinearGroup R₁ M₁)
  证明: rfl
-/
@[simp] lemma congrLinearEquiv_apply (e₁₂ : M₁ ≃ₛₗ[σ₁₂] M₂) (g : GeneralLinearGroup R₁ M₁) :
    congrLinearEquiv e₁₂ g = ofLinearEquiv (e₁₂.symm.trans <| g.toLinearEquiv.trans e₁₂) :=
  rfl

/--
lemma `congrLinearEquiv_symm` / 引理 `congrLinearEquiv_symm`

English:
lemma congrLinearEquiv_symm
  given: (e₁₂ : M₁ ≃ₛₗ[σ₁₂] M₂)
  proof: rfl

@[simp]

中文:
引理 congrLinearEquiv_symm
  条件: (e₁₂ : M₁ ≃ₛₗ[σ₁₂] M₂)
  证明: rfl

@[simp]
-/
@[simp] lemma congrLinearEquiv_symm (e₁₂ : M₁ ≃ₛₗ[σ₁₂] M₂) :
    (congrLinearEquiv e₁₂).symm = congrLinearEquiv e₁₂.symm :=
  rfl

@[simp]
/--
lemma `congrLinearEquiv_trans` / 引理 `congrLinearEquiv_trans`

English:
lemma congrLinearEquiv_trans
  proof: rfl

中文:
引理 congrLinearEquiv_trans
  证明: rfl
-/
lemma congrLinearEquiv_trans
    {N₁ N₂ N₃ : Type*} [AddCommMonoid N₁] [AddCommMonoid N₂] [AddCommMonoid N₃]
    [Module R N₁] [Module R N₂] [Module R N₃] (e₁₂ : N₁ ≃ₗ[R] N₂) (e₂₃ : N₂ ≃ₗ[R] N₃) :
    (congrLinearEquiv e₁₂).trans (congrLinearEquiv e₂₃) = congrLinearEquiv (e₁₂.trans e₂₃) :=
  rfl

/--
lemma `congrLinearEquiv_trans'` / 引理 `congrLinearEquiv_trans'`

English:
lemma congrLinearEquiv_trans'
  given: (e₁₂ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂₃ : M₂ ≃ₛₗ[σ₂₃] M₃)
  proof: rfl

@[simp]

中文:
引理 congrLinearEquiv_trans'
  条件: (e₁₂ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂₃ : M₂ ≃ₛₗ[σ₂₃] M₃)
  证明: rfl

@[simp]
-/
lemma congrLinearEquiv_trans' (e₁₂ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂₃ : M₂ ≃ₛₗ[σ₂₃] M₃) :
    (congrLinearEquiv e₁₂).trans (congrLinearEquiv e₂₃) =
      congrLinearEquiv (e₁₂.trans e₂₃) :=
  rfl

@[simp]
/--
lemma `congrLinearEquiv_refl` / 引理 `congrLinearEquiv_refl`

English:
lemma congrLinearEquiv_refl
  proof: rfl

中文:
引理 congrLinearEquiv_refl
  证明: rfl
-/
lemma congrLinearEquiv_refl :
    congrLinearEquiv (LinearEquiv.refl R₁ M₁) = MulEquiv.refl (GeneralLinearGroup R₁ M₁) :=
  rfl

end Functoriality

end GeneralLinearGroup

end LinearMap
