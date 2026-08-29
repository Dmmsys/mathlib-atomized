/-
Copyright (c) 2025 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Morrison
-/
module

public import Mathlib.Data.Finsupp.ToDFinsupp
public import Mathlib.LinearAlgebra.PiTensorProduct.DFinsupp
public import Mathlib.RingTheory.PiTensorProduct

/-!
# Results on finitely supported functions.

* `ofFinsuppEquiv`, the tensor product of the family `κ i →₀ M i` indexed by `ι` is linearly
  equivalent to `∏ i, κ i →₀ ⨂[R] i, M i`.
-/

@[expose] public section

namespace PiTensorProduct

open PiTensorProduct TensorProduct

attribute [local ext] TensorProduct.ext

variable {R ι : Type*} {κ M : ι -> Type*}
variable [CommSemiring R] [Fintype ι] [DecidableEq ι] [(i : ι) -> DecidableEq (κ i)]
variable [forall i, AddCommMonoid (M i)] [forall i, Module R (M i)] [forall i, DecidableEq (M i)]

/--
Definition of `ofFinsuppEquiv` / `ofFinsuppEquiv` 的定义

English:
definition ofFinsuppEquiv
  signature: :
  body: haveI := Classical.typeDecidableEq (⨂[R] (i : ι), M i)
  PiTensorProduct.congr (fun _ => finsuppLequivDFinsupp R) ≪≫ₗ
    ofDFinsuppEquiv ≪≫ₗ
    (finsuppLequivDFinsupp R).symm

@[simp]

中文:
定义 ofFinsuppEquiv
  签名: :
  定义体: haveI := Classical.typeDecidableEq (⨂[R] (i : ι), M i)
  PiTensorProduct.congr (fun _ => finsuppLequivDFinsupp R) ≪≫ₗ
    ofDFinsuppEquiv ≪≫ₗ
    (finsuppLequivDFinsupp R).symm

@[simp]

Depends on / 依赖: Classical, Classical.typeDecidableEq, PiTensorProduct, PiTensorProduct.congr, finsuppLequivDFinsupp, ofDFinsuppEquiv, typeDecidableEq
-/
noncomputable def ofFinsuppEquiv :
    (⨂[R] i, κ i ->₀ M i) ≃ₗ[R] ((i : ι) -> κ i) ->₀ ⨂[R] i, M i :=
  haveI := Classical.typeDecidableEq (⨂[R] (i : ι), M i)
  PiTensorProduct.congr (fun _ => finsuppLequivDFinsupp R) ≪≫ₗ
    ofDFinsuppEquiv ≪≫ₗ
    (finsuppLequivDFinsupp R).symm

@[simp]
/--
theorem `ofFinsuppEquiv_tprod_single` / 定理 `ofFinsuppEquiv_tprod_single`

English:
theorem ofFinsuppEquiv_tprod_single
  given: (p : (i : ι) -> κ i) (m : (i : ι) -> M i)
  proof: by
  simp [ofFinsuppEquiv]

@[simp]

中文:
定理 ofFinsuppEquiv_tprod_single
  条件: (p : (i : ι) -> κ i) (m : (i : ι) -> M i)
  证明: by
  simp [ofFinsuppEquiv]

@[simp]

Depends on / 依赖: ofFinsuppEquiv
-/
theorem ofFinsuppEquiv_tprod_single (p : (i : ι) -> κ i) (m : (i : ι) -> M i) :
    ofFinsuppEquiv (⨂ₜ[R] i, Finsupp.single (p i) (m i)) =
    Finsupp.single p (⨂ₜ[R] i, m i) := by
  simp [ofFinsuppEquiv]

@[simp]
/--
theorem `ofFinsuppEquiv_apply` / 定理 `ofFinsuppEquiv_apply`

English:
theorem ofFinsuppEquiv_apply
  given: (f : (i : ι) -> (κ i ->₀ M i)) (p : (i : ι) -> κ i)
  proof: by
  simp [ofFinsuppEquiv]

@[simp]

中文:
定理 ofFinsuppEquiv_apply
  条件: (f : (i : ι) -> (κ i ->₀ M i)) (p : (i : ι) -> κ i)
  证明: by
  simp [ofFinsuppEquiv]

@[simp]

Depends on / 依赖: ofFinsuppEquiv
-/
theorem ofFinsuppEquiv_apply (f : (i : ι) -> (κ i ->₀ M i)) (p : (i : ι) -> κ i) :
    ofFinsuppEquiv (⨂ₜ[R] i, f i) p = ⨂ₜ[R] i, f i (p i) := by
  simp [ofFinsuppEquiv]

@[simp]
/--
theorem `ofFinsuppEquiv_symm_single_tprod` / 定理 `ofFinsuppEquiv_symm_single_tprod`

English:
theorem ofFinsuppEquiv_symm_single_tprod
  given: (p : (i : ι) -> κ i) (m : (i : ι) -> M i)
  proof: (LinearEquiv.symm_apply_eq _).2 (ofFinsuppEquiv_tprod_single _ _).symm

中文:
定理 ofFinsuppEquiv_symm_single_tprod
  条件: (p : (i : ι) -> κ i) (m : (i : ι) -> M i)
  证明: (LinearEquiv.symm_apply_eq _).2 (ofFinsuppEquiv_tprod_single _ _).symm

Depends on / 依赖: LinearEquiv, LinearEquiv.symm_apply_eq, ofFinsuppEquiv_tprod_single, symm_apply_eq
-/
theorem ofFinsuppEquiv_symm_single_tprod (p : (i : ι) -> κ i) (m : (i : ι) -> M i) :
    ofFinsuppEquiv.symm (Finsupp.single p (⨂ₜ[R] i, m i)) =
    ⨂ₜ[R] i, Finsupp.single (p i) (m i) :=
  (LinearEquiv.symm_apply_eq _).2 (ofFinsuppEquiv_tprod_single _ _).symm

variable [DecidableEq R]

/--
Definition of `ofFinsuppEquiv'` / `ofFinsuppEquiv'` 的定义

English:
definition ofFinsuppEquiv'
  signature: : (⨂[R] i, (κ i ->₀ R)) ≃ₗ[R] ((i : ι) -> κ i) ->₀ R
  body: ofFinsuppEquiv ≪≫ₗ
  Finsupp.lcongr (Equiv.refl ((i : ι) -> κ i)) (constantBaseRingEquiv ι R).toLinearEquiv

@[simp]

中文:
定义 ofFinsuppEquiv'
  签名: : (⨂[R] i, (κ i ->₀ R)) ≃ₗ[R] ((i : ι) -> κ i) ->₀ R
  定义体: ofFinsuppEquiv ≪≫ₗ
  Finsupp.lcongr (Equiv.refl ((i : ι) -> κ i)) (constantBaseRingEquiv ι R).toLinearEquiv

@[simp]

Depends on / 依赖: Equiv.refl, Finsupp, Finsupp.lcongr, constantBaseRingEquiv, lcongr, ofFinsuppEquiv, toLinearEquiv
-/
noncomputable def ofFinsuppEquiv' : (⨂[R] i, (κ i ->₀ R)) ≃ₗ[R] ((i : ι) -> κ i) ->₀ R :=
  ofFinsuppEquiv ≪≫ₗ
  Finsupp.lcongr (Equiv.refl ((i : ι) -> κ i)) (constantBaseRingEquiv ι R).toLinearEquiv

@[simp]
/--
theorem `ofFinsuppEquiv'_apply_apply` / 定理 `ofFinsuppEquiv'_apply_apply`

English:
theorem ofFinsuppEquiv'_apply_apply
  given: (f : (i : ι) -> κ i ->₀ R) (p : (i : ι) -> κ i)
  proof: by
  simp [ofFinsuppEquiv']

@[simp]

中文:
定理 ofFinsuppEquiv'_apply_apply
  条件: (f : (i : ι) -> κ i ->₀ R) (p : (i : ι) -> κ i)
  证明: by
  simp [ofFinsuppEquiv']

@[simp]
-/
theorem ofFinsuppEquiv'_apply_apply (f : (i : ι) -> κ i ->₀ R) (p : (i : ι) -> κ i) :
    ofFinsuppEquiv' (⨂ₜ[R] i, f i) p = ∏ i, f i (p i) := by
  simp [ofFinsuppEquiv']

@[simp]
/--
theorem `ofFinsuppEquiv'_tprod_single` / 定理 `ofFinsuppEquiv'_tprod_single`

English:
theorem ofFinsuppEquiv'_tprod_single
  given: (p : (i : ι) -> κ i) (r : ι -> R)
  proof: by
  simp [ofFinsuppEquiv']

中文:
定理 ofFinsuppEquiv'_tprod_single
  条件: (p : (i : ι) -> κ i) (r : ι -> R)
  证明: by
  simp [ofFinsuppEquiv']
-/
theorem ofFinsuppEquiv'_tprod_single (p : (i : ι) -> κ i) (r : ι -> R) :
    ofFinsuppEquiv' (⨂ₜ[R] i, Finsupp.single (p i) (r i)) =
    Finsupp.single p (∏ i, r i) := by
  simp [ofFinsuppEquiv']

end PiTensorProduct
