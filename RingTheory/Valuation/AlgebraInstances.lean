/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
module

public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Algebra instances

This file contains several `Algebra` and `IsScalarTower` instances related to extensions
of a field with a valuation, as well as their unit balls.

## Main definitions
* `ValuationSubring.algebra` : Given an algebra between two field extensions `L` and `E` of a
  field `K` with a valuation, create an algebra between their two rings of integers.

## Main statements

* `integralClosure_algebraMap_injective` : the unit ball of a field `K` with respect to a
  valuation injects into its integral closure in a field extension `L` of `K`.
-/

@[expose] public section

open Function Valuation
open scoped WithZero

variable {K : Type*} [Field K] (v : Valuation K Intᵐ⁰) (L : Type*) [Field L] [Algebra K L]

namespace ValuationSubring

-- Shortcut instance with potential performance benefit
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra v.valuationSubring L
  body: inferInstance

中文:
实例 :
  签名: 代数 v.valuationSubring L
  定义体: inferInstance
-/
instance : Algebra v.valuationSubring L := inferInstance

/--
theorem `algebraMap_injective` / 定理 `algebraMap_injective`

English:
theorem algebraMap_injective
  statement: Injective (algebraMap v.valuationSubring L)
  proof: (FaithfulSMul.algebraMap_injective K L).comp (IsFractionRing.injective _ _)

中文:
定理 algebraMap_injective
  结论: 单射 (algebraMap v.valuationSubring L)
  证明: (FaithfulSMul.algebraMap_injective K L).comp (IsFractionRing.injective _ _)

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, IsFractionRing, IsFractionRing.injective, algebraMap_injective, injective
-/
theorem algebraMap_injective : Injective (algebraMap v.valuationSubring L) :=
  (FaithfulSMul.algebraMap_injective K L).comp (IsFractionRing.injective _ _)

/--
theorem `isIntegral_of_mem_ringOfIntegers` / 定理 `isIntegral_of_mem_ringOfIntegers`

English:
theorem isIntegral_of_mem_ringOfIntegers
  given: {x : L} (hx : x in integralClosure v.valuationSubring L)
  proof: integralClosure.isIntegral ⟨x, hx⟩

中文:
定理 is整数egral_of_mem_ringOf整数egers
  条件: {x : L} (hx : x in integralClosure v.valuationSubring L)
  证明: integralClosure.isIntegral ⟨x, hx⟩

Depends on / 依赖: integralClosure, integralClosure.isIntegral, isIntegral
-/
theorem isIntegral_of_mem_ringOfIntegers {x : L} (hx : x in integralClosure v.valuationSubring L) :
    IsIntegral v.valuationSubring (⟨x, hx⟩ : integralClosure v.valuationSubring L) :=
  integralClosure.isIntegral ⟨x, hx⟩

/--
theorem `isIntegral_of_mem_ringOfIntegers'` / 定理 `isIntegral_of_mem_ringOfIntegers'`

English:
theorem isIntegral_of_mem_ringOfIntegers'
  given: {x : integralClosure v.valuationSubring L}
  proof: by
  apply isIntegral_of_mem_ringOfIntegers

中文:
定理 is整数egral_of_mem_ringOf整数egers'
  条件: {x : integralClosure v.valuationSubring L}
  证明: by
  apply isIntegral_of_mem_ringOfIntegers

Depends on / 依赖: isIntegral_of_mem_ringOfIntegers
-/
theorem isIntegral_of_mem_ringOfIntegers' {x : integralClosure v.valuationSubring L} :
    IsIntegral v.valuationSubring (x : integralClosure v.valuationSubring L) := by
  apply isIntegral_of_mem_ringOfIntegers

variable (E : Type _) [Field E] [Algebra K E] [Algebra L E] [IsScalarTower K L E]

-- Shortcut instance with potential performance benefit
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsScalarTower v.valuationSubring L E
  body: inferInstance

中文:
实例 :
  签名: 标量塔 v.valuationSubring L E
  定义体: inferInstance
-/
instance : IsScalarTower v.valuationSubring L E := inferInstance

-- TODO: fix the smul field
/--
Instance `algebra` / 实例 `algebra`

English:
instance algebra
  signature: :
  body: RingHom.toAlgebra
    { toFun := fun k => ⟨algebraMap L E k, IsIntegral.algebraMap k.2⟩
      map_zero' :=
Subtype.ext by simp only [Subalgebra.coe_zero, map_zero]
map_one' := Subtype.ext by simp only [Subalgebra.coe_one, map_one]
      map_add' := fun x y =>
Subtype.ext by simp only [map_add, Subal

中文:
实例 algebra
  签名: :
  定义体: RingHom.toAlgebra
    { toFun := fun k => ⟨algebraMap L E k, IsIntegral.algebraMap k.2⟩
      map_zero' :=
Subtype.ext by simp only [Subalgebra.coe_zero, map_zero]
map_one' := Subtype.ext by simp only [Subalgebra.coe_one, map_one]
      map_add' := fun x y =>
Subtype.ext by simp only [map_add, Subal

Depends on / 依赖: IsIntegral, IsIntegral.algebraMap, RingHom, RingHom.toAlgebra, Subalgebra, Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_one, Subalgebra.coe_zero, Subtype, Subtype.ext, algebraMap, coe_add, coe_mul, coe_one, coe_zero, map_add, map_mul, map_one, map_zero
-/
instance algebra :
    Algebra (integralClosure v.valuationSubring L) (integralClosure v.valuationSubring E) :=
  RingHom.toAlgebra
    { toFun := fun k => ⟨algebraMap L E k, IsIntegral.algebraMap k.2⟩
      map_zero' :=
Subtype.ext by simp only [Subalgebra.coe_zero, map_zero]
map_one' := Subtype.ext by simp only [Subalgebra.coe_one, map_one]
      map_add' := fun x y =>
Subtype.ext by simp only [map_add, Subalgebra.coe_add]
      map_mul' := fun x y =>
Subtype.ext by simp only [Subalgebra.coe_mul, map_mul] }

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def equiv (R : Type*) [CommRing R] [Algebra v.valuationSubring R]
  body: (IsIntegralClosure.equiv v.valuationSubring R L
    (integralClosure v.valuationSubring L)).symm.toRingEquiv

中文:
定义 noncomputable
  签名: def equiv (R : 类型) [交换环 R] [代数 v.valuationSubring R]
  定义体: (IsIntegralClosure.equiv v.valuationSubring R L
    (integralClosure v.valuationSubring L)).symm.toRingEquiv
-/
protected noncomputable def equiv (R : Type*) [CommRing R] [Algebra v.valuationSubring R]
    [Algebra R L] [IsScalarTower v.valuationSubring R L]
    [IsIntegralClosure R v.valuationSubring L] : integralClosure v.valuationSubring L ≃+* R :=
  (IsIntegralClosure.equiv v.valuationSubring R L
    (integralClosure v.valuationSubring L)).symm.toRingEquiv

/--
theorem `integralClosure_algebraMap_injective` / 定理 `integralClosure_algebraMap_injective`

English:
theorem integralClosure_algebraMap_injective
  proof: FaithfulSMul.algebraMap_injective ..

中文:
定理 integralClosure_algebraMap_injective
  证明: FaithfulSMul.algebraMap_injective ..

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap_injective
-/
theorem integralClosure_algebraMap_injective :
    Injective (algebraMap v.valuationSubring (integralClosure v.valuationSubring L)) :=
  FaithfulSMul.algebraMap_injective ..

end ValuationSubring
