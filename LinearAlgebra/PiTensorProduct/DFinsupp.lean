/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel, Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Multilinear.DFinsupp

/-!
# Tensor products of finitely supported functions

This file shows that taking `PiTensorProduct`s commutes with taking `DFinsupp`s in all arguments.

## Main results

* `ofDFinsuppEquiv`: the linear equivalence between a `PiTensorProduct` of `DFinsupp`s
  and the `DFinsupp` of the `PiTensorProduct`s.
-/

@[expose] public section

namespace PiTensorProduct

open LinearMap TensorProduct

variable {R ι : Type*} {κ : ι -> Type*} {M : (i : ι) -> κ i -> Type*}
  [CommSemiring R] [Π i (j : κ i), AddCommMonoid (M i j)] [Π i (j : κ i), Module R (M i j)]
  [Fintype ι] [DecidableEq ι] [(i : ι) -> DecidableEq (κ i)]

/--
Definition of `ofDFinsuppEquiv` / `ofDFinsuppEquiv` 的定义

English:
definition ofDFinsuppEquiv
  signature: :
  body: LinearEquiv.ofLinearMap
    (lift <| MultilinearMap.fromDFinsuppEquiv κ R
      fun p => (DFinsupp.lsingle p).compMultilinearMap (tprod R))
    (DFinsupp.lsum R fun p => lift <|
      (PiTensorProduct.map fun i => DFinsupp.lsingle (p i)).compMultilinearMap (tprod R))
    (by ext p x; simp)
    (by ext x; simp)

@[simp]

中文:
定义 ofDFinsuppEquiv
  签名: :
  定义体: LinearEquiv.ofLinearMap
    (lift <| MultilinearMap.fromDFinsuppEquiv κ R
      fun p => (DFinsupp.lsingle p).compMultilinearMap (tprod R))
    (DFinsupp.lsum R fun p => lift <|
      (PiTensorProduct.map fun i => DFinsupp.lsingle (p i)).compMultilinearMap (tprod R))
    (by ext p x; simp)
    (by ext x; simp)

@[simp]

Depends on / 依赖: DFinsupp, DFinsupp.lsingle, DFinsupp.lsum, LinearEquiv, LinearEquiv.ofLinearMap, MultilinearMap, MultilinearMap.fromDFinsuppEquiv, PiTensorProduct, PiTensorProduct.map, compMultilinearMap, fromDFinsuppEquiv, lsingle, ofLinearMap
-/
def ofDFinsuppEquiv :
    (⨂[R] i, (Π₀ j : κ i, M i j)) ≃ₗ[R] Π₀ p : Π i, κ i, ⨂[R] i, M i (p i) :=
  LinearEquiv.ofLinearMap
    (lift <| MultilinearMap.fromDFinsuppEquiv κ R
      fun p => (DFinsupp.lsingle p).compMultilinearMap (tprod R))
    (DFinsupp.lsum R fun p => lift <|
      (PiTensorProduct.map fun i => DFinsupp.lsingle (p i)).compMultilinearMap (tprod R))
    (by ext p x; simp)
    (by ext x; simp)

@[simp]
/--
theorem `ofDFinsuppEquiv_tprod_single` / 定理 `ofDFinsuppEquiv_tprod_single`

English:
theorem ofDFinsuppEquiv_tprod_single
  given: (p : Π i, κ i) (x : Π i, M i (p i))
  proof: by
  simp [ofDFinsuppEquiv]

@[simp]

中文:
定理 ofDFinsuppEquiv_tprod_single
  条件: (p : Π i, κ i) (x : Π i, M i (p i))
  证明: by
  simp [ofDFinsuppEquiv]

@[simp]

Depends on / 依赖: ofDFinsuppEquiv
-/
theorem ofDFinsuppEquiv_tprod_single (p : Π i, κ i) (x : Π i, M i (p i)) :
    ofDFinsuppEquiv (⨂ₜ[R] i, DFinsupp.single (p i) (x i)) =
      DFinsupp.single p (⨂ₜ[R] i, x i) := by
  simp [ofDFinsuppEquiv]

@[simp]
/--
theorem `ofDFinsuppEquiv_symm_single_tprod` / 定理 `ofDFinsuppEquiv_symm_single_tprod`

English:
theorem ofDFinsuppEquiv_symm_single_tprod
  given: (p : Π i, κ i) (x : Π i, M i (p i))
  proof: by
  simp [ofDFinsuppEquiv]

@[simp]

中文:
定理 ofDFinsuppEquiv_symm_single_tprod
  条件: (p : Π i, κ i) (x : Π i, M i (p i))
  证明: by
  simp [ofDFinsuppEquiv]

@[simp]

Depends on / 依赖: ofDFinsuppEquiv
-/
theorem ofDFinsuppEquiv_symm_single_tprod (p : Π i, κ i) (x : Π i, M i (p i)) :
    ofDFinsuppEquiv.symm (DFinsupp.single p (tprod R x)) =
      (⨂ₜ[R] i, DFinsupp.single (p i) (x i)) := by
  simp [ofDFinsuppEquiv]

@[simp]
/--
theorem `ofDFinsuppEquiv_tprod_apply` / 定理 `ofDFinsuppEquiv_tprod_apply`

English:
theorem ofDFinsuppEquiv_tprod_apply
  given: (x : Π i, Π₀ j, M i j) (p : Π i, κ i)
  proof: by
  classical
  simpa [ofDFinsuppEquiv, MultilinearMap.fromDFinsuppEquiv_apply] using fun i hi =>
    ((tprod R).map_coord_zero (m := fun i => x i (p i)) i hi).symm

中文:
定理 ofDFinsuppEquiv_tprod_apply
  条件: (x : Π i, Π₀ j, M i j) (p : Π i, κ i)
  证明: by
  classical
  simpa [ofDFinsuppEquiv, MultilinearMap.fromDFinsuppEquiv_apply] using fun i hi =>
    ((tprod R).map_coord_zero (m := fun i => x i (p i)) i hi).symm

Depends on / 依赖: MultilinearMap, MultilinearMap.fromDFinsuppEquiv_apply, classical, fromDFinsuppEquiv_apply, map_coord_zero, ofDFinsuppEquiv
-/
theorem ofDFinsuppEquiv_tprod_apply (x : Π i, Π₀ j, M i j) (p : Π i, κ i) :
    ofDFinsuppEquiv (tprod R x) p = ⨂ₜ[R] i, x i (p i) := by
  classical
  simpa [ofDFinsuppEquiv, MultilinearMap.fromDFinsuppEquiv_apply] using fun i hi =>
    ((tprod R).map_coord_zero (m := fun i => x i (p i)) i hi).symm

end PiTensorProduct
