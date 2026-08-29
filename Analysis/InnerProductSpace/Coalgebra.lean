/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.RingTheory.Coalgebra.Basic

/-!
# Finite-dimensional inner product space with a (co)algebra structure

This file proves that a finite-dimensional inner product space has a
coalgebra structure if it has an algebra structure, where
the comultiplication and counit maps are given by taking adjoints of the
multiplication and algebra linear maps, respectively.
This is implemented by providing a linear equivalence between the inner product space
and an algebra.

And similarly, a finite-dimensional inner product space has an algebra
structure if it has a coalgebra structure, where `x * y = (adjoint comul) (x ⊗ₜ y)`,
`(1 : A) = (adjoint counit) (1 : 𝕜)` and `algebraMap = adjoint counit`.

This is useful for when we have a finite-dimensional C⋆-algebra with a faithful and
positive linear functional (so that it induces an inner product structure), and want the coalgebra
structure to be the _adjoint_ of the algebra structure.
This comes up in non-commutative graph theory for example.
-/

@[expose] public section

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

open TensorProduct LinearMap LinearIsometryEquiv Coalgebra

open EuclideanSpace in
/--
theorem `Pi.comul_eq_adjoint` / 定理 `Pi.comul_eq_adjoint`

English:
theorem Pi.comul_eq_adjoint
  given: {n : Type*} [Fintype n] [DecidableEq n]
  proof: by
  ext
  simp only [comp_apply, ← toLinearMap_congr, LinearEquiv.coe_coe, ← LinearEquiv.symm_apply_eq]
  simp [TensorProduct.ext_iff_inner_left, adjoint_inner_right, inner_eq_star_dotProduct]

中文:
定理 依赖函数类型.comul_eq_adjoint
  条件: {n : 类型} [有限类型 n] [DecidableEq n]
  证明: by
  ext
  simp only [comp_apply, ← toLinearMap_congr, LinearEquiv.coe_coe, ← LinearEquiv.symm_apply_eq]
  simp [TensorProduct.ext_iff_inner_left, adjoint_inner_right, inner_eq_star_dotProduct]

Depends on / 依赖: LinearEquiv, LinearEquiv.coe_coe, LinearEquiv.symm_apply_eq, TensorProduct, TensorProduct.ext_iff_inner_left, adjoint_inner_right, coe_coe, comp_apply, ext_iff_inner_left, inner_eq_star_dotProduct, symm_apply_eq, toLinearMap_congr
-/
theorem Pi.comul_eq_adjoint {n : Type*} [Fintype n] [DecidableEq n] :
    comul = map (equiv n 𝕜).toLinearMap (equiv n 𝕜).toLinearMap ∘ₗ
      ((equiv n 𝕜).symm.toLinearMap ∘ₗ mul' 𝕜 (n -> 𝕜) ∘ₗ
        map (equiv n 𝕜).toLinearMap (equiv n 𝕜).toLinearMap).adjoint ∘ₗ
      (equiv n 𝕜).symm.toLinearMap := by
  ext
  simp only [comp_apply, ← toLinearMap_congr, LinearEquiv.coe_coe, ← LinearEquiv.symm_apply_eq]
  simp [TensorProduct.ext_iff_inner_left, adjoint_inner_right, inner_eq_star_dotProduct]

open EuclideanSpace in
/--
theorem `Pi.counit_eq_adjoint` / 定理 `Pi.counit_eq_adjoint`

English:
theorem Pi.counit_eq_adjoint
  given: {n : Type*} [Fintype n] [DecidableEq n]
  proof: by
  ext
  simp [← toSpanSingleton_one_eq_algebraLinearMap, comp_toSpanSingleton,
    adjoint_toSpanSingleton, inner_eq_star_dotProduct]

中文:
定理 依赖函数类型.counit_eq_adjoint
  条件: {n : 类型} [有限类型 n] [DecidableEq n]
  证明: by
  ext
  simp [← toSpanSingleton_one_eq_algebraLinearMap, comp_toSpanSingleton,
    adjoint_toSpanSingleton, inner_eq_star_dotProduct]

Depends on / 依赖: adjoint_toSpanSingleton, comp_toSpanSingleton, inner_eq_star_dotProduct, toSpanSingleton_one_eq_algebraLinearMap
-/
theorem Pi.counit_eq_adjoint {n : Type*} [Fintype n] [DecidableEq n] :
    counit = ((equiv n 𝕜).symm.toLinearMap ∘ₗ Algebra.linearMap 𝕜 (n -> 𝕜)).adjoint ∘ₗ
      (equiv n 𝕜).symm.toLinearMap := by
  ext
  simp [← toSpanSingleton_one_eq_algebraLinearMap, comp_toSpanSingleton,
    adjoint_toSpanSingleton, inner_eq_star_dotProduct]

namespace InnerProductSpace

section coalgebraOfAlgebra
variable {A : Type*} [Ring A] [Module 𝕜 A] [SMulCommClass 𝕜 A A] [IsScalarTower 𝕜 A A]

/--
Definition of `coalgebraOfAlgebra` / `coalgebraOfAlgebra` 的定义

English:
abbreviation coalgebraOfAlgebra
  signature: (e : E ≃ₗ[𝕜] A)
  body: adjoint (e.symm.toLinearMap ∘ₗ mul' 𝕜 A ∘ₗ map e.toLinearMap e.toLinearMap)
  counit := innerₛₗ 𝕜 (e.symm 1)
  coassoc := by
    rw [← adjoint_lTensor]; rw [← adjoint_rTensor]; rw [← toLinearEquiv_assocIsometry]; rw [← (assocIsometry 𝕜 _ _ _).symm_symm]; rw [← adjoint_toLinearMap_eq_symm]
    simp_rw [← adjoint_comp]
    congr 1; ext; simp [mul_assoc]
  rTensor_counit_comp_comul := by
    rw [← adjoint_toSpanSingleton]; rw [← adjoint_rTensor]; rw [← adjoint_comp]; rw [← toLinearMap_symm_lid]; rw [← toLinearEquiv_lidIsometry]; rw [← toLinearEquiv_symm]; rw [← adjoint_toLinearMap_eq_symm]
    congr 1; ext; simp
  lTensor_counit_comp_comul := by
    rw [← adjoint_toSpanSingleton]; rw [← adjoint_lTensor]; rw [← adjoint_comp]; rw [← toLinearMap_symm_rid]; rw [← comm_trans_lid]; rw [← toLinearEquiv_commIsometry]; rw [← toLinearEquiv_lidIsometry]; rw [← toLinearEquiv_trans]; rw [← toLinearEquiv_symm]; rw [← adjoint_toLinearMap_eq_symm]
    congr 1; ext; simp

中文:
缩写 coalgebraOfAlgebra
  签名: (e : E ≃ₗ[𝕜] A)
  定义体: adjoint (e.symm.toLinearMap ∘ₗ mul' 𝕜 A ∘ₗ map e.toLinearMap e.toLinearMap)
  counit := innerₛₗ 𝕜 (e.symm 1)
  coassoc := by
    rw [← adjoint_lTensor]; rw [← adjoint_rTensor]; rw [← toLinearEquiv_assocIsometry]; rw [← (assocIsometry 𝕜 _ _ _).symm_symm]; rw [← adjoint_toLinearMap_eq_symm]
    simp_rw [← adjoint_comp]
    congr 1; ext; simp [mul_assoc]
  rTensor_counit_comp_comul := by
    rw [← adjoint_toSpanSingleton]; rw [← adjoint_rTensor]; rw [← adjoint_comp]; rw [← toLinearMap_symm_lid]; rw [← toLinearEquiv_lidIsometry]; rw [← toLinearEquiv_symm]; rw [← adjoint_toLinearMap_eq_symm]
    congr 1; ext; simp
  lTensor_counit_comp_comul := by
    rw [← adjoint_toSpanSingleton]; rw [← adjoint_lTensor]; rw [← adjoint_comp]; rw [← toLinearMap_symm_rid]; rw [← comm_trans_lid]; rw [← toLinearEquiv_commIsometry]; rw [← toLinearEquiv_lidIsometry]; rw [← toLinearEquiv_trans]; rw [← toLinearEquiv_symm]; rw [← adjoint_toLinearMap_eq_symm]
    congr 1; ext; simp

Depends on / 依赖: adjoint, e.symm.toLinearMap, e.toLinearMap, toLinearMap
-/
noncomputable abbrev coalgebraOfAlgebra (e : E ≃ₗ[𝕜] A) : Coalgebra 𝕜 E where
  comul := adjoint (e.symm.toLinearMap ∘ₗ mul' 𝕜 A ∘ₗ map e.toLinearMap e.toLinearMap)
  counit := innerₛₗ 𝕜 (e.symm 1)
  coassoc := by
    rw [← adjoint_lTensor]; rw [← adjoint_rTensor]; rw [← toLinearEquiv_assocIsometry]; rw [← (assocIsometry 𝕜 _ _ _).symm_symm]; rw [← adjoint_toLinearMap_eq_symm]
    simp_rw [← adjoint_comp]
    congr 1; ext; simp [mul_assoc]
  rTensor_counit_comp_comul := by
    rw [← adjoint_toSpanSingleton]; rw [← adjoint_rTensor]; rw [← adjoint_comp]; rw [← toLinearMap_symm_lid]; rw [← toLinearEquiv_lidIsometry]; rw [← toLinearEquiv_symm]; rw [← adjoint_toLinearMap_eq_symm]
    congr 1; ext; simp
  lTensor_counit_comp_comul := by
    rw [← adjoint_toSpanSingleton]; rw [← adjoint_lTensor]; rw [← adjoint_comp]; rw [← toLinearMap_symm_rid]; rw [← comm_trans_lid]; rw [← toLinearEquiv_commIsometry]; rw [← toLinearEquiv_lidIsometry]; rw [← toLinearEquiv_trans]; rw [← toLinearEquiv_symm]; rw [← adjoint_toLinearMap_eq_symm]
    congr 1; ext; simp

end coalgebraOfAlgebra

section algebraOfCoalgebra
variable [Coalgebra 𝕜 E]

/--
Definition of `mulOfCoalgebra` / `mulOfCoalgebra` 的定义

English:
abbreviation mulOfCoalgebra
  signature: :
  body: adjoint (comul (R := 𝕜) (A := E)) (x otimesₜ y)

中文:
缩写 mulOfCoalgebra
  签名: :
  定义体: adjoint (comul (R := 𝕜) (A := E)) (x otimesₜ y)

Depends on / 依赖: adjoint
-/
noncomputable abbrev mulOfCoalgebra :
    Mul E where mul x y := adjoint (comul (R := 𝕜) (A := E)) (x otimesₜ y)

attribute [local instance] InnerProductSpace.mulOfCoalgebra in
/--
lemma `AlgebraOfCoalgebra.mul_def` / 引理 `AlgebraOfCoalgebra.mul_def`

English:
lemma AlgebraOfCoalgebra.mul_def
  given: (x y : E)
  proof: rfl

中文:
引理 AlgebraOfCoalgebra.mul_def
  条件: (x y : E)
  证明: rfl
-/
lemma AlgebraOfCoalgebra.mul_def (x y : E) :
    x * y = adjoint (comul (R := 𝕜) (A := E)) (x otimesₜ y) := rfl

attribute [local simp] AlgebraOfCoalgebra.mul_def

attribute [local instance] InnerProductSpace.mulOfCoalgebra in
/--
Definition of `ringOfCoalgebra` / `ringOfCoalgebra` 的定义

English:
abbreviation ringOfCoalgebra
  signature: :
  body: by simp [tmul_add]
  right_distrib x y z := by simp [add_tmul]
  zero_mul x := by simp
  mul_zero x := by simp
  mul_assoc x y z := by
    simp_rw [AlgebraOfCoalgebra.mul_def, ← rTensor_tmul, ← comp_apply, ← adjoint_rTensor,
      ← adjoint_comp, ← coassoc_symm, adjoint_comp, adjoint_lTensor, comp_apply,
      ← toLinearEquiv_assocIsometry, ← toLinearEquiv_symm, adjoint_toLinearMap_eq_symm]
    simp only [symm_symm, toLinearEquiv_assocIsometry, LinearEquiv.coe_coe, assoc_tmul,
      lTensor_tmul]
  one := adjoint (counit (R := 𝕜) (A := E)) 1
  one_mul x := by
    dsimp [OfNat.ofNat]
    rw [← rTensor_tmul]; rw [← comp_apply]; rw [← adjoint_rTensor]; rw [← adjoint_comp]; rw [rTensor_counit_comp_comul]; rw [← toLinearMap_symm_lid]; rw [← toLinearEquiv_lidIsometry]; rw [← toLinearEquiv_symm]; rw [adjoint_toLinearMap_eq_symm]
    exact one_smul _ _
  mul_one x := by
    dsimp [OfNat.ofNat]
    rw [← lTensor_tmul]; rw [← comp_apply]; rw [← adjoint_lTensor]; rw [← adjoint_comp]; rw [lTensor_counit_comp_comul]; rw [← toLinearMap_symm_rid]; rw [← comm_trans_lid]; rw [← toLinearEquiv_commIsometry]; rw [← toLinearEquiv_lidIsometry]; rw [← toLinearEquiv_trans]; rw [← toLinearEquiv_symm]; rw [adjoint_toLinearMap_eq_symm]
    exact one_smul _ _

中文:
缩写 ringOfCoalgebra
  签名: :
  定义体: by simp [tmul_add]
  right_distrib x y z := by simp [add_tmul]
  zero_mul x := by simp
  mul_zero x := by simp
  mul_assoc x y z := by
    simp_rw [AlgebraOfCoalgebra.mul_def, ← rTensor_tmul, ← comp_apply, ← adjoint_rTensor,
      ← adjoint_comp, ← coassoc_symm, adjoint_comp, adjoint_lTensor, comp_apply,
      ← toLinearEquiv_assocIsometry, ← toLinearEquiv_symm, adjoint_toLinearMap_eq_symm]
    simp only [symm_symm, toLinearEquiv_assocIsometry, LinearEquiv.coe_coe, assoc_tmul,
      lTensor_tmul]
  one := adjoint (counit (R := 𝕜) (A := E)) 1
  one_mul x := by
    dsimp [OfNat.ofNat]
    rw [← rTensor_tmul]; rw [← comp_apply]; rw [← adjoint_rTensor]; rw [← adjoint_comp]; rw [rTensor_counit_comp_comul]; rw [← toLinearMap_symm_lid]; rw [← toLinearEquiv_lidIsometry]; rw [← toLinearEquiv_symm]; rw [adjoint_toLinearMap_eq_symm]
    exact one_smul _ _
  mul_one x := by
    dsimp [OfNat.ofNat]
    rw [← lTensor_tmul]; rw [← comp_apply]; rw [← adjoint_lTensor]; rw [← adjoint_comp]; rw [lTensor_counit_comp_comul]; rw [← toLinearMap_symm_rid]; rw [← comm_trans_lid]; rw [← toLinearEquiv_commIsometry]; rw [← toLinearEquiv_lidIsometry]; rw [← toLinearEquiv_trans]; rw [← toLinearEquiv_symm]; rw [adjoint_toLinearMap_eq_symm]
    exact one_smul _ _

Depends on / 依赖: AlgebraOfCoalgebra, AlgebraOfCoalgebra.mul_def, LinearEquiv, LinearEquiv.coe_coe, add_tmul, adjoint, adjoint_comp, adjoint_lTensor, adjoint_rTensor, adjoint_toLinearMap_eq_symm, assoc_tmul, coassoc_symm, coe_coe, comp_apply, counit, lTensor_tmul, mul_assoc, mul_def, mul_zero, rTensor_tmul
-/
noncomputable abbrev ringOfCoalgebra :
    Ring E where
  left_distrib x y z := by simp [tmul_add]
  right_distrib x y z := by simp [add_tmul]
  zero_mul x := by simp
  mul_zero x := by simp
  mul_assoc x y z := by
    simp_rw [AlgebraOfCoalgebra.mul_def, ← rTensor_tmul, ← comp_apply, ← adjoint_rTensor,
      ← adjoint_comp, ← coassoc_symm, adjoint_comp, adjoint_lTensor, comp_apply,
      ← toLinearEquiv_assocIsometry, ← toLinearEquiv_symm, adjoint_toLinearMap_eq_symm]
    simp only [symm_symm, toLinearEquiv_assocIsometry, LinearEquiv.coe_coe, assoc_tmul,
      lTensor_tmul]
  one := adjoint (counit (R := 𝕜) (A := E)) 1
  one_mul x := by
    dsimp [OfNat.ofNat]
    rw [← rTensor_tmul]; rw [← comp_apply]; rw [← adjoint_rTensor]; rw [← adjoint_comp]; rw [rTensor_counit_comp_comul]; rw [← toLinearMap_symm_lid]; rw [← toLinearEquiv_lidIsometry]; rw [← toLinearEquiv_symm]; rw [adjoint_toLinearMap_eq_symm]
    exact one_smul _ _
  mul_one x := by
    dsimp [OfNat.ofNat]
    rw [← lTensor_tmul]; rw [← comp_apply]; rw [← adjoint_lTensor]; rw [← adjoint_comp]; rw [lTensor_counit_comp_comul]; rw [← toLinearMap_symm_rid]; rw [← comm_trans_lid]; rw [← toLinearEquiv_commIsometry]; rw [← toLinearEquiv_lidIsometry]; rw [← toLinearEquiv_trans]; rw [← toLinearEquiv_symm]; rw [adjoint_toLinearMap_eq_symm]
    exact one_smul _ _

attribute [local instance] InnerProductSpace.ringOfCoalgebra in
/--
Definition of `algebraOfCoalgebra` / `algebraOfCoalgebra` 的定义

English:
abbreviation algebraOfCoalgebra
  signature: : Algebra 𝕜 E where
  body: { toFun := adjoint (Coalgebra.counit (R := 𝕜) (A := E))
      map_one' := rfl
      map_mul' x y := by
        simp_rw [AlgebraOfCoalgebra.mul_def, ← map_tmul, ← adjoint_map, ← comp_apply,
          ← adjoint_comp, ← lTensor_comp_rTensor, comp_assoc, rTensor_counit_comp_comul,
          adjoint_comp, ← toLinearMap_symm_lid, ← toLinearEquiv_lidIsometry, ← toLinearEquiv_symm,
          adjoint_toLinearMap_eq_symm]
        simp only [LinearIsometryEquiv.symm_symm, toLinearEquiv_lidIsometry, adjoint_lTensor,
          coe_comp, LinearEquiv.coe_coe, Function.comp_apply, lTensor_tmul, lid_tmul]
        rw [← smul_eq_mul]; rw [← _root_.map_smul]
      map_zero' := map_zero _
      map_add' := map_add _ }
  commutes' r x := by
    dsimp
    simp_rw [← rTensor_tmul, ← lTensor_tmul, ← adjoint_lTensor, ← adjoint_rTensor,
      ← comp_apply, ← adjoint_comp, rTensor_counit_comp_comul, lTensor_counit_comp_comul,
      ← toLinearMap_symm_rid, ← toLinearMap_symm_lid, ← comm_trans_lid,
      ← toLinearEquiv_commIsometry, ← toLinearEquiv_lidIsometry, ← toLinearEquiv_trans,
      ← toLinearEquiv_symm, adjoint_toLinearMap_eq_symm]
    simp
  smul_def' r x := by
    dsimp
    simp_rw [← rTensor_tmul, ← adjoint_rTensor, ← comp_apply, ← adjoint_comp,
      rTensor_counit_comp_comul, ← toLinearMap_symm_lid, ← toLinearEquiv_lidIsometry,
      ← toLinearEquiv_symm, adjoint_toLinearMap_eq_symm]
    simp

中文:
缩写 algebraOfCoalgebra
  签名: : 代数 𝕜 E where
  定义体: { toFun := adjoint (Coalgebra.counit (R := 𝕜) (A := E))
      map_one' := rfl
      map_mul' x y := by
        simp_rw [AlgebraOfCoalgebra.mul_def, ← map_tmul, ← adjoint_map, ← comp_apply,
          ← adjoint_comp, ← lTensor_comp_rTensor, comp_assoc, rTensor_counit_comp_comul,
          adjoint_comp, ← toLinearMap_symm_lid, ← toLinearEquiv_lidIsometry, ← toLinearEquiv_symm,
          adjoint_toLinearMap_eq_symm]
        simp only [LinearIsometryEquiv.symm_symm, toLinearEquiv_lidIsometry, adjoint_lTensor,
          coe_comp, LinearEquiv.coe_coe, Function.comp_apply, lTensor_tmul, lid_tmul]
        rw [← smul_eq_mul]; rw [← _root_.map_smul]
      map_zero' := map_zero _
      map_add' := map_add _ }
  commutes' r x := by
    dsimp
    simp_rw [← rTensor_tmul, ← lTensor_tmul, ← adjoint_lTensor, ← adjoint_rTensor,
      ← comp_apply, ← adjoint_comp, rTensor_counit_comp_comul, lTensor_counit_comp_comul,
      ← toLinearMap_symm_rid, ← toLinearMap_symm_lid, ← comm_trans_lid,
      ← toLinearEquiv_commIsometry, ← toLinearEquiv_lidIsometry, ← toLinearEquiv_trans,
      ← toLinearEquiv_symm, adjoint_toLinearMap_eq_symm]
    simp
  smul_def' r x := by
    dsimp
    simp_rw [← rTensor_tmul, ← adjoint_rTensor, ← comp_apply, ← adjoint_comp,
      rTensor_counit_comp_comul, ← toLinearMap_symm_lid, ← toLinearEquiv_lidIsometry,
      ← toLinearEquiv_symm, adjoint_toLinearMap_eq_symm]
    simp

Depends on / 依赖: AlgebraOfCoalgebra, AlgebraOfCoalgebra.mul_def, Coalgebra, Coalgebra.counit, Function, Function.comp_app, LinearEquiv, LinearEquiv.coe_coe, LinearIsometryEquiv, LinearIsometryEquiv.symm_symm, adjoint, adjoint_comp, adjoint_lTensor, adjoint_map, adjoint_toLinearMap_eq_symm, coe_coe, coe_comp, comp_app, comp_apply, comp_assoc
-/
noncomputable abbrev algebraOfCoalgebra : Algebra 𝕜 E where
  algebraMap :=
    { toFun := adjoint (Coalgebra.counit (R := 𝕜) (A := E))
      map_one' := rfl
      map_mul' x y := by
        simp_rw [AlgebraOfCoalgebra.mul_def, ← map_tmul, ← adjoint_map, ← comp_apply,
          ← adjoint_comp, ← lTensor_comp_rTensor, comp_assoc, rTensor_counit_comp_comul,
          adjoint_comp, ← toLinearMap_symm_lid, ← toLinearEquiv_lidIsometry, ← toLinearEquiv_symm,
          adjoint_toLinearMap_eq_symm]
        simp only [LinearIsometryEquiv.symm_symm, toLinearEquiv_lidIsometry, adjoint_lTensor,
          coe_comp, LinearEquiv.coe_coe, Function.comp_apply, lTensor_tmul, lid_tmul]
        rw [← smul_eq_mul]; rw [← _root_.map_smul]
      map_zero' := map_zero _
      map_add' := map_add _ }
  commutes' r x := by
    dsimp
    simp_rw [← rTensor_tmul, ← lTensor_tmul, ← adjoint_lTensor, ← adjoint_rTensor,
      ← comp_apply, ← adjoint_comp, rTensor_counit_comp_comul, lTensor_counit_comp_comul,
      ← toLinearMap_symm_rid, ← toLinearMap_symm_lid, ← comm_trans_lid,
      ← toLinearEquiv_commIsometry, ← toLinearEquiv_lidIsometry, ← toLinearEquiv_trans,
      ← toLinearEquiv_symm, adjoint_toLinearMap_eq_symm]
    simp
  smul_def' r x := by
    dsimp
    simp_rw [← rTensor_tmul, ← adjoint_rTensor, ← comp_apply, ← adjoint_comp,
      rTensor_counit_comp_comul, ← toLinearMap_symm_lid, ← toLinearEquiv_lidIsometry,
      ← toLinearEquiv_symm, adjoint_toLinearMap_eq_symm]
    simp

end algebraOfCoalgebra
end InnerProductSpace
