/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.RingTheory.Coalgebra.Basic

/-!
# MulOpposite of coalgebras

Suppose `R` is a commutative semiring, and `A` is an `R`-coalgebra,
then `Aᵐᵒᵖ` is an `R`-coalgebra, where we define the comultiplication and counit maps naturally.
-/

public section

namespace MulOpposite

open scoped TensorProduct

open TensorProduct Coalgebra LinearMap

variable {R A : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CoalgebraStruct
  signature: R A] : CoalgebraStruct R Aᵐᵒᵖ where
  body: map (opLinearEquiv R).toLinearMap (opLinearEquiv R).toLinearMap ∘ₗ
    comul ∘ₗ (opLinearEquiv R).symm.toLinearMap
  counit := counit ∘ₗ (opLinearEquiv R).symm.toLinearMap

中文:
实例 [CoalgebraStruct
  签名: R A] : CoalgebraStruct R Aᵐᵒᵖ where
  定义体: map (opLinearEquiv R).toLinearMap (opLinearEquiv R).toLinearMap ∘ₗ
    comul ∘ₗ (opLinearEquiv R).symm.toLinearMap
  counit := counit ∘ₗ (opLinearEquiv R).symm.toLinearMap

Depends on / 依赖: opLinearEquiv, toLinearMap
-/
noncomputable instance [CoalgebraStruct R A] : CoalgebraStruct R Aᵐᵒᵖ where
  comul := map (opLinearEquiv R).toLinearMap (opLinearEquiv R).toLinearMap ∘ₗ
    comul ∘ₗ (opLinearEquiv R).symm.toLinearMap
  counit := counit ∘ₗ (opLinearEquiv R).symm.toLinearMap

/--
lemma `comul_def` / 引理 `comul_def`

English:
lemma comul_def
  given: [CoalgebraStruct R A]
  proof: rfl

中文:
引理 comul_def
  条件: [CoalgebraStruct R A]
  证明: rfl

Depends on / 依赖: opLinearEquiv, toLinearMap
-/
lemma comul_def [CoalgebraStruct R A] :
    comul (R := R) (A := Aᵐᵒᵖ) = map (opLinearEquiv R).toLinearMap (opLinearEquiv R).toLinearMap ∘ₗ
      comul ∘ₗ (opLinearEquiv R).symm.toLinearMap := rfl

/--
lemma `counit_def` / 引理 `counit_def`

English:
lemma counit_def
  given: [CoalgebraStruct R A]
  proof: rfl

中文:
引理 counit_def
  条件: [CoalgebraStruct R A]
  证明: rfl

Depends on / 依赖: counit, opLinearEquiv, symm.toLinearMap, toLinearMap
-/
lemma counit_def [CoalgebraStruct R A] :
    counit (R := R) (A := Aᵐᵒᵖ) = counit ∘ₗ (opLinearEquiv R).symm.toLinearMap := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Coalgebra
  signature: R A] : Coalgebra R Aᵐᵒᵖ where
  body: ext fun _ => by
    rw [comul_def]; rw [rTensor_comp]; rw [rTensor_comp]
    simp only [coe_comp, LinearEquiv.coe_coe, Function.comp_apply, lTensor_map, rTensor_def]
    simp_rw [← map_map_assoc, map_map, comp_assoc, ← lTensor_comp_rTensor]
    simp [lTensor_tensor, comp_assoc]
  rTensor_counit_comp

中文:
实例 [Coalgebra
  签名: R A] : Coalgebra R Aᵐᵒᵖ where
  定义体: ext fun _ => by
    rw [comul_def]; rw [rTensor_comp]; rw [rTensor_comp]
    simp only [coe_comp, LinearEquiv.coe_coe, Function.comp_apply, lTensor_map, rTensor_def]
    simp_rw [← map_map_assoc, map_map, comp_assoc, ← lTensor_comp_rTensor]
    simp [lTensor_tensor, comp_assoc]
  rTensor_counit_comp

Depends on / 依赖: Function, Function.comp_apply, LinearEquiv, LinearEquiv.coe_coe, coe_coe, coe_comp, comp_apply, comp_assoc, comul_def, counit_def, lTensor_comp_rTensor, lTensor_counit_comp_comul, lTensor_map, lTensor_tensor, map_map, map_map_assoc, rTensor_comp, rTensor_counit_comp_comul, rTensor_def, rTensor_map
-/
noncomputable instance [Coalgebra R A] : Coalgebra R Aᵐᵒᵖ where
  coassoc := ext fun _ => by
    rw [comul_def]; rw [rTensor_comp]; rw [rTensor_comp]
    simp only [coe_comp, LinearEquiv.coe_coe, Function.comp_apply, lTensor_map, rTensor_def]
    simp_rw [← map_map_assoc, map_map, comp_assoc, ← lTensor_comp_rTensor]
    simp [lTensor_tensor, comp_assoc]
  rTensor_counit_comp_comul := ext fun _ => by
    simp only [counit_def, comul_def, coe_comp, Function.comp_apply, rTensor_map, comp_assoc]
    simp [← lTensor_comp_rTensor]
  lTensor_counit_comp_comul := ext fun _ => by
    simp only [counit_def, comul_def, coe_comp, Function.comp_apply, lTensor_map, comp_assoc]
    simp [← rTensor_comp_lTensor]

end MulOpposite
