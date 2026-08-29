/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Algebra.TransferInstance
public import Mathlib.Algebra.Algebra.Unitization
public import Mathlib.Analysis.Normed.Lp.ProdLp

/-! # Unitization equipped with the $L^1$ norm

In another file, the `Unitization 𝕜 A` of a non-unital normed `𝕜`-algebra `A` is equipped with the
norm inherited as the pullback via a map (closely related to) the left-regular representation of the
algebra on itself (see `Unitization.instNormedRing`).

However, this construction is only valid (and an isometry) when `A` is a `RegularNormedAlgebra`.
Sometimes it is useful to consider the unitization of a non-unital algebra with the $L^1$ norm
instead. This file provides that norm on the type synonym `WithLp 1 (Unitization 𝕜 A)`, along
with the algebra isomorphism between `Unitization 𝕜 A` and `WithLp 1 (Unitization 𝕜 A)`.
Note that `TrivSqZeroExt` is also equipped with the $L^1$ norm in the analogous way, but it is
registered as an instance without the type synonym.

One application of this is a straightforward proof that the quasispectrum of an element in a
non-unital Banach algebra is compact, which can be established by passing to the unitization.
-/

@[expose] public section

variable (𝕜 A : Type*) [NormedField 𝕜] [NonUnitalNormedRing A]
variable [NormedSpace 𝕜 A]

namespace WithLp

open Unitization

/--
Definition of `unitization_addEquiv_prod` / `unitization_addEquiv_prod` 的定义

English:
definition unitization_addEquiv_prod
  signature: : WithLp 1 (Unitization 𝕜 A) ≃+ WithLp 1 (𝕜 × A)
  body: (WithLp.linearEquiv 1 𝕜 (Unitization 𝕜 A)).toAddEquiv.trans
    (addEquiv 𝕜 A).trans (WithLp.linearEquiv 1 𝕜 (𝕜 × A)).symm.toAddEquiv

中文:
定义 unitization_addEquiv_prod
  签名: : WithLp 1 (Unitization 𝕜 A) ≃+ WithLp 1 (𝕜 × A)
  定义体: (WithLp.linearEquiv 1 𝕜 (Unitization 𝕜 A)).toAddEquiv.trans
    (addEquiv 𝕜 A).trans (WithLp.linearEquiv 1 𝕜 (𝕜 × A)).symm.toAddEquiv

Depends on / 依赖: Unitization, WithLp, WithLp.linearEquiv, addEquiv, linearEquiv, symm.toAddEquiv, toAddEquiv, toAddEquiv.trans
-/
noncomputable def unitization_addEquiv_prod : WithLp 1 (Unitization 𝕜 A) ≃+ WithLp 1 (𝕜 × A) :=
(WithLp.linearEquiv 1 𝕜 (Unitization 𝕜 A)).toAddEquiv.trans
    (addEquiv 𝕜 A).trans (WithLp.linearEquiv 1 𝕜 (𝕜 × A)).symm.toAddEquiv

/--
Instance `instUnitizationNormedAddCommGroup` / 实例 `instUnitizationNormedAddCommGroup`

English:
instance instUnitizationNormedAddCommGroup
  signature: :
  body: NormedAddCommGroup.induced (WithLp 1 (Unitization 𝕜 A)) (WithLp 1 (𝕜 × A))
    (unitization_addEquiv_prod 𝕜 A) (AddEquiv.injective _)

中文:
实例 instUnitizationNormedAddCommGroup
  签名: :
  定义体: NormedAddCommGroup.induced (WithLp 1 (Unitization 𝕜 A)) (WithLp 1 (𝕜 × A))
    (unitization_addEquiv_prod 𝕜 A) (AddEquiv.injective _)

Depends on / 依赖: AddEquiv, AddEquiv.injective, NormedAddCommGroup, NormedAddCommGroup.induced, Unitization, WithLp, induced, injective, unitization_addEquiv_prod
-/
noncomputable instance instUnitizationNormedAddCommGroup :
    NormedAddCommGroup (WithLp 1 (Unitization 𝕜 A)) :=
  NormedAddCommGroup.induced (WithLp 1 (Unitization 𝕜 A)) (WithLp 1 (𝕜 × A))
    (unitization_addEquiv_prod 𝕜 A) (AddEquiv.injective _)

/--
Definition of `uniformEquiv_unitization_addEquiv_prod` / `uniformEquiv_unitization_addEquiv_prod` 的定义

English:
definition uniformEquiv_unitization_addEquiv_prod
  signature: :
  body: { unitization_addEquiv_prod 𝕜 A with
    uniformContinuous_invFun := uniformContinuous_comap' uniformContinuous_id
    uniformContinuous_toFun := uniformContinuous_iff_le_comap.mpr le_rfl }

中文:
定义 uniformEquiv_unitization_addEquiv_prod
  签名: :
  定义体: { unitization_addEquiv_prod 𝕜 A with
    uniformContinuous_invFun := uniformContinuous_comap' uniformContinuous_id
    uniformContinuous_toFun := uniformContinuous_iff_le_comap.mpr le_rfl }

Depends on / 依赖: le_rfl, uniformContinuous_comap, uniformContinuous_id, uniformContinuous_iff_le_comap, uniformContinuous_iff_le_comap.mpr, uniformContinuous_invFun, uniformContinuous_toFun, unitization_addEquiv_prod
-/
noncomputable def uniformEquiv_unitization_addEquiv_prod :
    WithLp 1 (Unitization 𝕜 A) ≃ᵤ WithLp 1 (𝕜 × A) :=
  { unitization_addEquiv_prod 𝕜 A with
    uniformContinuous_invFun := uniformContinuous_comap' uniformContinuous_id
    uniformContinuous_toFun := uniformContinuous_iff_le_comap.mpr le_rfl }

/--
Instance `instCompleteSpace` / 实例 `instCompleteSpace`

English:
instance instCompleteSpace
  signature: [CompleteSpace 𝕜] [CompleteSpace A]
  body: .mpr completeSpace_congr (uniformEquiv_unitization_addEquiv_prod 𝕜 A).isUniformEmbedding
    inferInstance

中文:
实例 instCompleteSpace
  签名: [CompleteSpace 𝕜] [CompleteSpace A]
  定义体: .mpr completeSpace_congr (uniformEquiv_unitization_addEquiv_prod 𝕜 A).isUniformEmbedding
    inferInstance

Depends on / 依赖: completeSpace_congr, isUniformEmbedding, uniformEquiv_unitization_addEquiv_prod
-/
instance instCompleteSpace [CompleteSpace 𝕜] [CompleteSpace A] :
    CompleteSpace (WithLp 1 (Unitization 𝕜 A)) :=
.mpr completeSpace_congr (uniformEquiv_unitization_addEquiv_prod 𝕜 A).isUniformEmbedding
    inferInstance

variable {𝕜 A}

open ENNReal in
/--
lemma `unitization_norm_def` / 引理 `unitization_norm_def`

English:
lemma unitization_norm_def
  given: (x : WithLp 1 (Unitization 𝕜 A))
  proof: calc
  ‖x‖ = (‖(ofLp x).fst‖ ^ (1 : Real>=0∞).toReal +
      ‖(ofLp x).snd‖ ^ (1 : Real>=0∞).toReal) ^ (1 / (1 : Real>=0∞).toReal) :=
    prod_norm_eq_add (by simp : 0 < (1 : Real>=0∞).toReal) _
  _ = ‖(ofLp x).fst‖ + ‖(ofLp x).snd‖ := by simp

中文:
引理 unitization_norm_def
  条件: (x : WithLp 1 (Unitization 𝕜 A))
  证明: calc
  ‖x‖ = (‖(ofLp x).fst‖ ^ (1 : Real>=0∞).toReal +
      ‖(ofLp x).snd‖ ^ (1 : Real>=0∞).toReal) ^ (1 / (1 : Real>=0∞).toReal) :=
    prod_norm_eq_add (by simp : 0 < (1 : Real>=0∞).toReal) _
  _ = ‖(ofLp x).fst‖ + ‖(ofLp x).snd‖ := by simp
-/
lemma unitization_norm_def (x : WithLp 1 (Unitization 𝕜 A)) :
    ‖x‖ = ‖(ofLp x).fst‖ + ‖(ofLp x).snd‖ := calc
  ‖x‖ = (‖(ofLp x).fst‖ ^ (1 : Real>=0∞).toReal +
      ‖(ofLp x).snd‖ ^ (1 : Real>=0∞).toReal) ^ (1 / (1 : Real>=0∞).toReal) :=
    prod_norm_eq_add (by simp : 0 < (1 : Real>=0∞).toReal) _
  _ = ‖(ofLp x).fst‖ + ‖(ofLp x).snd‖ := by simp

/--
lemma `unitization_nnnorm_def` / 引理 `unitization_nnnorm_def`

English:
lemma unitization_nnnorm_def
  given: (x : WithLp 1 (Unitization 𝕜 A))
  proof: Subtype.ext unitization_norm_def x

中文:
引理 unitization_nnnorm_def
  条件: (x : WithLp 1 (Unitization 𝕜 A))
  证明: Subtype.ext unitization_norm_def x

Depends on / 依赖: Subtype, Subtype.ext, unitization_norm_def
-/
lemma unitization_nnnorm_def (x : WithLp 1 (Unitization 𝕜 A)) :
    ‖x‖₊ = ‖(ofLp x).fst‖₊ + ‖(ofLp x).snd‖₊ :=
Subtype.ext unitization_norm_def x

/--
lemma `unitization_norm_inr` / 引理 `unitization_norm_inr`

English:
lemma unitization_norm_inr
  given: (x : A)
  statement: ‖toLp 1 (x : Unitization 𝕜 A)‖ = ‖x‖
  proof: by
  simp [unitization_norm_def]

中文:
引理 unitization_norm_inr
  条件: (x : A)
  结论: ‖toLp 1 (x : Unitization 𝕜 A)‖ = ‖x‖
  证明: by
  simp [unitization_norm_def]

Depends on / 依赖: unitization_norm_def
-/
lemma unitization_norm_inr (x : A) : ‖toLp 1 (x : Unitization 𝕜 A)‖ = ‖x‖ := by
  simp [unitization_norm_def]

/--
lemma `unitization_nnnorm_inr` / 引理 `unitization_nnnorm_inr`

English:
lemma unitization_nnnorm_inr
  given: (x : A)
  statement: ‖toLp 1 (x : Unitization 𝕜 A)‖₊ = ‖x‖₊
  proof: by
  simp [unitization_nnnorm_def]

中文:
引理 unitization_nnnorm_inr
  条件: (x : A)
  结论: ‖toLp 1 (x : Unitization 𝕜 A)‖₊ = ‖x‖₊
  证明: by
  simp [unitization_nnnorm_def]

Depends on / 依赖: unitization_nnnorm_def
-/
lemma unitization_nnnorm_inr (x : A) : ‖toLp 1 (x : Unitization 𝕜 A)‖₊ = ‖x‖₊ := by
  simp [unitization_nnnorm_def]

/--
lemma `unitization_isometry_inr` / 引理 `unitization_isometry_inr`

English:
lemma unitization_isometry_inr
  statement: Isometry fun x : A => toLp 1 (x : Unitization 𝕜 A)
  proof: AddMonoidHomClass.isometry_of_norm
    ((WithLp.linearEquiv 1 𝕜 (Unitization 𝕜 A)).symm.comp <| Unitization.inrHom 𝕜 𝕜 A)
    unitization_norm_inr

中文:
引理 unitization_isometry_inr
  结论: Isometry fun x : A => toLp 1 (x : Unitization 𝕜 A)
  证明: AddMonoidHomClass.isometry_of_norm
    ((WithLp.linearEquiv 1 𝕜 (Unitization 𝕜 A)).symm.comp <| Unitization.inrHom 𝕜 𝕜 A)
    unitization_norm_inr

Depends on / 依赖: AddMonoidHomClass, AddMonoidHomClass.isometry_of_norm, Unitization, Unitization.inrHom, WithLp, WithLp.linearEquiv, inrHom, isometry_of_norm, linearEquiv, symm.comp, unitization_norm_inr
-/
lemma unitization_isometry_inr : Isometry fun x : A => toLp 1 (x : Unitization 𝕜 A) :=
  AddMonoidHomClass.isometry_of_norm
    ((WithLp.linearEquiv 1 𝕜 (Unitization 𝕜 A)).symm.comp <| Unitization.inrHom 𝕜 𝕜 A)
    unitization_norm_inr

variable [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]

/--
Instance `instUnitizationRing` / 实例 `instUnitizationRing`

English:
instance instUnitizationRing
  signature: : Ring (WithLp 1 (Unitization 𝕜 A))
  body: (WithLp.equiv 1 (Unitization 𝕜 A)).ring

@[simp]

中文:
实例 instUnitizationRing
  签名: : Ring (WithLp 1 (Unitization 𝕜 A))
  定义体: (WithLp.equiv 1 (Unitization 𝕜 A)).ring

@[simp]

Depends on / 依赖: Unitization, WithLp, WithLp.equiv
-/
instance instUnitizationRing : Ring (WithLp 1 (Unitization 𝕜 A)) :=
  (WithLp.equiv 1 (Unitization 𝕜 A)).ring

@[simp]
/--
lemma `unitization_mul` / 引理 `unitization_mul`

English:
lemma unitization_mul
  given: (x y : WithLp 1 (Unitization 𝕜 A))
  statement: ofLp (x * y) = ofLp x * ofLp y
  proof: rfl

中文:
引理 unitization_mul
  条件: (x y : WithLp 1 (Unitization 𝕜 A))
  结论: ofLp (x * y) = ofLp x * ofLp y
  证明: rfl
-/
lemma unitization_mul (x y : WithLp 1 (Unitization 𝕜 A)) : ofLp (x * y) = ofLp x * ofLp y := rfl

instance {R : Type*} [CommSemiring R] [Algebra R 𝕜] [DistribMulAction R A] [IsScalarTower R 𝕜 A] :
    Algebra R (WithLp 1 (Unitization 𝕜 A)) :=
  (WithLp.equiv 1 (Unitization 𝕜 A)).algebra R

@[simp]
/--
lemma `unitization_algebraMap` / 引理 `unitization_algebraMap`

English:
lemma unitization_algebraMap
  given: (r : 𝕜)
  proof: rfl

中文:
引理 unitization_algebraMap
  条件: (r : 𝕜)
  证明: rfl
-/
lemma unitization_algebraMap (r : 𝕜) :
    ofLp (algebraMap 𝕜 (WithLp 1 (Unitization 𝕜 A)) r) = algebraMap 𝕜 (Unitization 𝕜 A) r := rfl

/-- `equiv` bundled as an algebra isomorphism with `Unitization 𝕜 A`. -/
@[simps!]
/--
Definition of `unitizationAlgEquiv` / `unitizationAlgEquiv` 的定义

English:
definition unitizationAlgEquiv
  signature: (R : Type*) [CommSemiring R] [Algebra R 𝕜] [DistribMulAction R A]
  body: WithLp.linearEquiv _ R _
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

中文:
定义 unitizationAlgEquiv
  签名: (R : 类型) [CommSemiring R] [Algebra R 𝕜] [DistribMulAction R A]
  定义体: WithLp.linearEquiv _ R _
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

Depends on / 依赖: WithLp, WithLp.linearEquiv, linearEquiv
-/
def unitizationAlgEquiv (R : Type*) [CommSemiring R] [Algebra R 𝕜] [DistribMulAction R A]
    [IsScalarTower R 𝕜 A] : WithLp 1 (Unitization 𝕜 A) ≃ₐ[R] Unitization 𝕜 A where
  __ := WithLp.linearEquiv _ R _
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/--
Instance `instUnitizationNormedRing` / 实例 `instUnitizationNormedRing`

English:
instance instUnitizationNormedRing
  signature: : NormedRing (WithLp 1 (Unitization 𝕜 A)) where
  body: dist_eq_norm_neg_add
  norm_mul_le x y := by
    simp_rw [unitization_norm_def, add_mul, mul_add, unitization_mul, fst_mul, snd_mul]
    rw [add_assoc]; rw [add_assoc]
    gcongr
    · exact norm_mul_le _ _
    · apply (norm_add_le _ _).trans
      gcongr
      · simp [norm_smul]
      · apply (norm

中文:
实例 instUnitizationNormedRing
  签名: : NormedRing (WithLp 1 (Unitization 𝕜 A)) where
  定义体: dist_eq_norm_neg_add
  norm_mul_le x y := by
    simp_rw [unitization_norm_def, add_mul, mul_add, unitization_mul, fst_mul, snd_mul]
    rw [add_assoc]; rw [add_assoc]
    gcongr
    · exact norm_mul_le _ _
    · apply (norm_add_le _ _).trans
      gcongr
      · simp [norm_smul]
      · apply (norm

Depends on / 依赖: dist_eq_norm_neg_add
-/
noncomputable instance instUnitizationNormedRing : NormedRing (WithLp 1 (Unitization 𝕜 A)) where
  dist_eq := dist_eq_norm_neg_add
  norm_mul_le x y := by
    simp_rw [unitization_norm_def, add_mul, mul_add, unitization_mul, fst_mul, snd_mul]
    rw [add_assoc]; rw [add_assoc]
    gcongr
    · exact norm_mul_le _ _
    · apply (norm_add_le _ _).trans
      gcongr
      · simp [norm_smul]
      · apply (norm_add_le _ _).trans
        gcongr
        · simp [norm_smul, mul_comm]
        · exact norm_mul_le _ _

/--
Instance `instUnitizationNormedAlgebra` / 实例 `instUnitizationNormedAlgebra`

English:
instance instUnitizationNormedAlgebra
  signature: :
  body: by
    simp_rw [unitization_norm_def, ofLp_smul, fst_smul, snd_smul, norm_smul, mul_add]
    exact le_rfl

中文:
实例 instUnitizationNormedAlgebra
  签名: :
  定义体: by
    simp_rw [unitization_norm_def, ofLp_smul, fst_smul, snd_smul, norm_smul, mul_add]
    exact le_rfl

Depends on / 依赖: fst_smul, le_rfl, mul_add, norm_smul, ofLp_smul, simp_rw, snd_smul, unitization_norm_def
-/
noncomputable instance instUnitizationNormedAlgebra :
    NormedAlgebra 𝕜 (WithLp 1 (Unitization 𝕜 A)) where
  norm_smul_le r x := by
    simp_rw [unitization_norm_def, ofLp_smul, fst_smul, snd_smul, norm_smul, mul_add]
    exact le_rfl

end WithLp
