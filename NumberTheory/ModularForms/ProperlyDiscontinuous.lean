/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction
public import Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups
public import Mathlib.Topology.Algebra.Group.DiscontinuousSubgroup

/-!
# Arithmetic subgroups act properly discontinuously
-/

public section

open Matrix

open scoped MatrixGroups UpperHalfPlane

/--
Instance `properlyDiscontinuousSL2ZRange` / 实例 `properlyDiscontinuousSL2ZRange`

English:
instance properlyDiscontinuousSL2ZRange
  signature: : ProperlyDiscontinuousSMul 𝒮ℒ ℍ
  body: by
  let 𝒮ℒ' : Subgroup SL(2, Real) := (SpecialLinearGroup.map (Int.castRingHom Real)).range
  have : ProperlyDiscontinuousSMul 𝒮ℒ' ℍ := inferInstance
  simp only [Subgroup.properlyDiscontinuousSMul_iff] at this ⊢
  refine fun K L hK hL => ((this hK hL).map SpecialLinearGroup.toGL).subset fun g => ?

中文:
实例 properlyDiscontinuousSL2ZRange
  签名: : 命题erlyDiscontinuousSMul 𝒮ℒ ℍ
  定义体: by
  let 𝒮ℒ' : Subgroup SL(2, Real) := (SpecialLinearGroup.map (Int.castRingHom Real)).range
  have : ProperlyDiscontinuousSMul 𝒮ℒ' ℍ := inferInstance
  simp only [Subgroup.properlyDiscontinuousSMul_iff] at this ⊢
  refine fun K L hK hL => ((this hK hL).map SpecialLinearGroup.toGL).subset fun g => ?

Depends on / 依赖: Int.castRingHom, ProperlyDiscontinuousSMul, SpecialLinearGroup, SpecialLinearGroup.map, SpecialLinearGroup.toGL, Subgroup, Subgroup.properlyDiscontinuousSMul_iff, castRingHom, properlyDiscontinuousSMul_iff, subset
-/
instance properlyDiscontinuousSL2ZRange : ProperlyDiscontinuousSMul 𝒮ℒ ℍ := by
  let 𝒮ℒ' : Subgroup SL(2, Real) := (SpecialLinearGroup.map (Int.castRingHom Real)).range
  have : ProperlyDiscontinuousSMul 𝒮ℒ' ℍ := inferInstance
  simp only [Subgroup.properlyDiscontinuousSMul_iff] at this ⊢
  refine fun K L hK hL => ((this hK hL).map SpecialLinearGroup.toGL).subset fun g => ?_
  rintro ⟨⟨γ, rfl⟩, hγ⟩
  exact ⟨γ, ⟨by simp [𝒮ℒ'], hγ⟩, rfl⟩

/--
Instance `Subgroup.IsArithmetic.properlyDiscontinuous` / 实例 `Subgroup.IsArithmetic.properlyDiscontinuous`

English:
instance Subgroup.IsArithmetic.properlyDiscontinuous
  signature: {𝒢 : Subgroup (GL (Fin 2) Real)}
  body: by
  rw [is_commensurable.properlyDiscontinuousSMul_iff]
  infer_instance

中文:
实例 Subgroup.IsArithmetic.properlyDiscontinuous
  签名: {𝒢 : Subgroup (GL (Fin 2) 实数)}
  定义体: by
  rw [is_commensurable.properlyDiscontinuousSMul_iff]
  infer_instance

Depends on / 依赖: infer_instance, is_commensurable, is_commensurable.properlyDiscontinuousSMul_iff, properlyDiscontinuousSMul_iff
-/
instance Subgroup.IsArithmetic.properlyDiscontinuous {𝒢 : Subgroup (GL (Fin 2) Real)}
    [IsArithmetic 𝒢] : ProperlyDiscontinuousSMul 𝒢 ℍ := by
  rw [is_commensurable.properlyDiscontinuousSMul_iff]
  infer_instance

end
