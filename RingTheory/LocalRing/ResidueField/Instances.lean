/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

import Mathlib.RingTheory.Finiteness.Quotient

/-! # Instances on residue fields -/

public section

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra A B]
    [Algebra R B] [IsScalarTower R A B]

variable (p : Ideal A) (q : Ideal B) [q.LiesOver p]

section maximal

variable [p.IsMaximal] [q.IsMaximal] [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
  [Localization.AtPrime.IsLiesOverAlgebra p q]

attribute [local instance] Ideal.Quotient.field

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Algebra.IsSeparable
  signature: (A ⧸ p) (B ⧸ q)] :
  body: by
  refine Algebra.IsSeparable.of_equiv_equiv
    (.ofBijective _ p.bijective_algebraMap_quotient_residueField)
    (.ofBijective _ q.bijective_algebraMap_quotient_residueField) ?_
  ext x
  simp [RingHom.algebraMap_toAlgebra, ← IsScalarTower.algebraMap_apply]

中文:
实例 [代数.是可分
  签名: (A ⧸ p) (B ⧸ q)] :
  定义体: by
  refine Algebra.IsSeparable.of_equiv_equiv
    (.ofBijective _ p.bijective_algebraMap_quotient_residueField)
    (.ofBijective _ q.bijective_algebraMap_quotient_residueField) ?_
  ext x
  simp [RingHom.algebraMap_toAlgebra, ← IsScalarTower.algebraMap_apply]

Depends on / 依赖: Algebra, Algebra.IsSeparable.of_equiv_equiv, IsScalarTower, IsScalarTower.algebraMap_apply, IsSeparable, RingHom, RingHom.algebraMap_toAlgebra, algebraMap_apply, algebraMap_toAlgebra, bijective_algebraMap_quotient_residueField, ofBijective, of_equiv_equiv, p.bijective_algebraMap_quotient_residueField, q.bijective_algebraMap_quotient_residueField
-/
instance [Algebra.IsSeparable (A ⧸ p) (B ⧸ q)] :
    Algebra.IsSeparable p.ResidueField q.ResidueField := by
  refine Algebra.IsSeparable.of_equiv_equiv
    (.ofBijective _ p.bijective_algebraMap_quotient_residueField)
    (.ofBijective _ q.bijective_algebraMap_quotient_residueField) ?_
  ext x
  simp [RingHom.algebraMap_toAlgebra, ← IsScalarTower.algebraMap_apply]

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Algebra.IsSeparable
  signature: p.ResidueField q.ResidueField] :
  body: by
  refine Algebra.IsSeparable.of_equiv_equiv
    (.symm <| .ofBijective _ p.bijective_algebraMap_quotient_residueField)
    (.symm <| .ofBijective _ q.bijective_algebraMap_quotient_residueField) ?_
  apply RingHom.ext fun x => ?_
  obtain ⟨x, rfl⟩ :=
    (RingEquiv.ofBijective _ p.bijective_algebraMap_quotient_residueField).surjective x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  apply (RingEquiv.ofBijective _ q.bijective_algebraMap_quotient_residueField).injective
  simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, RingEquiv.symm_apply_apply,
    RingEquiv.apply_symm_apply]
  simp [RingHom.algebraMap_toAlgebra, ← IsScalarTower.algebraMap_apply]

中文:
实例 [代数.是可分
  签名: p.ResidueField q.ResidueField] :
  定义体: by
  refine Algebra.IsSeparable.of_equiv_equiv
    (.symm <| .ofBijective _ p.bijective_algebraMap_quotient_residueField)
    (.symm <| .ofBijective _ q.bijective_algebraMap_quotient_residueField) ?_
  apply RingHom.ext fun x => ?_
  obtain ⟨x, rfl⟩ :=
    (RingEquiv.ofBijective _ p.bijective_algebraMap_quotient_residueField).surjective x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  apply (RingEquiv.ofBijective _ q.bijective_algebraMap_quotient_residueField).injective
  simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, RingEquiv.symm_apply_apply,
    RingEquiv.apply_symm_apply]
  simp [RingHom.algebraMap_toAlgebra, ← IsScalarTower.algebraMap_apply]

Depends on / 依赖: Algebra, Algebra.IsSeparable.of_equiv_equiv, Ideal.Quotient.mk_surjective, IsSeparable, Quotient, RingEquiv, RingEquiv.ofBijective, RingHom, RingHom.coe, RingHom.coe_comp, RingHom.ext, bijective_algebraMap_quotient_residueField, coe_comp, injective, mk_surjective, ofBijective, of_equiv_equiv, p.bijective_algebraMap_quotient_residueField, q.bijective_algebraMap_quotient_residueField, surjective
-/
instance [Algebra.IsSeparable p.ResidueField q.ResidueField] :
    Algebra.IsSeparable (A ⧸ p) (B ⧸ q) := by
  refine Algebra.IsSeparable.of_equiv_equiv
    (.symm <| .ofBijective _ p.bijective_algebraMap_quotient_residueField)
    (.symm <| .ofBijective _ q.bijective_algebraMap_quotient_residueField) ?_
  apply RingHom.ext fun x => ?_
  obtain ⟨x, rfl⟩ :=
    (RingEquiv.ofBijective _ p.bijective_algebraMap_quotient_residueField).surjective x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  apply (RingEquiv.ofBijective _ q.bijective_algebraMap_quotient_residueField).injective
  simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, RingEquiv.symm_apply_apply,
    RingEquiv.apply_symm_apply]
  simp [RingHom.algebraMap_toAlgebra, ← IsScalarTower.algebraMap_apply]

variable {p q} in
/--
lemma `Algebra.isSeparable_residueField_iff` / 引理 `Algebra.isSeparable_residueField_iff`

English:
lemma Algebra.isSeparable_residueField_iff
  proof: ⟨fun _ => inferInstance, fun _ => inferInstance⟩

中文:
引理 代数.isSeparable_residueField_iff
  证明: ⟨fun _ => inferInstance, fun _ => inferInstance⟩
-/
lemma Algebra.isSeparable_residueField_iff :
    Algebra.IsSeparable p.ResidueField q.ResidueField ↔ Algebra.IsSeparable (A ⧸ p) (B ⧸ q) :=
  ⟨fun _ => inferInstance, fun _ => inferInstance⟩

end maximal

section prime

variable [p.IsPrime] [q.IsPrime] [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
  [Localization.AtPrime.IsLiesOverAlgebra p q]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra.IsAlgebraic (A ⧸ p) p.ResidueField
  body: IsLocalization.isAlgebraic _ (nonZeroDivisors (A ⧸ p))

中文:
实例 :
  签名: 代数.是代数 (A ⧸ p) p.ResidueField
  定义体: IsLocalization.isAlgebraic _ (nonZeroDivisors (A ⧸ p))

Depends on / 依赖: IsLocalization, IsLocalization.isAlgebraic, isAlgebraic, nonZeroDivisors
-/
instance : Algebra.IsAlgebraic (A ⧸ p) p.ResidueField :=
  IsLocalization.isAlgebraic _ (nonZeroDivisors (A ⧸ p))

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Algebra.IsIntegral
  signature: A B] :
  body: by
  have : Algebra.IsIntegral (A ⧸ p) (B ⧸ q) :=
    .tower_top A
  let := ((algebraMap (B ⧸ q) q.ResidueField).comp (algebraMap (A ⧸ p) (B ⧸ q))).toAlgebra
  have : IsScalarTower (A ⧸ p) (B ⧸ q) q.ResidueField := .of_algebraMap_eq' rfl
  have : Algebra.IsAlgebraic (A ⧸ p) q.ResidueField := .trans _ (B ⧸ q) _
  have : IsScalarTower (A ⧸ p) p.ResidueField q.ResidueField := by
    refine .of_algebraMap_eq fun x => ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [RingHom.algebraMap_toAlgebra, ← IsScalarTower.algebraMap_apply]
  refine .extendScalars (Ideal.injective_algebraMap_quotient_residueField p)

中文:
实例 [代数.是整
  签名: A B] :
  定义体: by
  have : Algebra.IsIntegral (A ⧸ p) (B ⧸ q) :=
    .tower_top A
  let := ((algebraMap (B ⧸ q) q.ResidueField).comp (algebraMap (A ⧸ p) (B ⧸ q))).toAlgebra
  have : IsScalarTower (A ⧸ p) (B ⧸ q) q.ResidueField := .of_algebraMap_eq' rfl
  have : Algebra.IsAlgebraic (A ⧸ p) q.ResidueField := .trans _ (B ⧸ q) _
  have : IsScalarTower (A ⧸ p) p.ResidueField q.ResidueField := by
    refine .of_algebraMap_eq fun x => ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [RingHom.algebraMap_toAlgebra, ← IsScalarTower.algebraMap_apply]
  refine .extendScalars (Ideal.injective_algebraMap_quotient_residueField p)

Depends on / 依赖: Algebra, Algebra.IsAlgebraic, Algebra.IsIntegral, Ideal.Quotient.mk_surjective, IsAlgebraic, IsIntegral, IsScalarTo, IsScalarTower, Quotient, ResidueField, RingHom, RingHom.algebraMap_toAlgebra, algebraMap, algebraMap_toAlgebra, mk_surjective, of_algebraMap_eq, p.ResidueField, q.ResidueField, toAlgebra, tower_top
-/
instance [Algebra.IsIntegral A B] :
    Algebra.IsAlgebraic p.ResidueField q.ResidueField := by
  have : Algebra.IsIntegral (A ⧸ p) (B ⧸ q) :=
    .tower_top A
  let := ((algebraMap (B ⧸ q) q.ResidueField).comp (algebraMap (A ⧸ p) (B ⧸ q))).toAlgebra
  have : IsScalarTower (A ⧸ p) (B ⧸ q) q.ResidueField := .of_algebraMap_eq' rfl
  have : Algebra.IsAlgebraic (A ⧸ p) q.ResidueField := .trans _ (B ⧸ q) _
  have : IsScalarTower (A ⧸ p) p.ResidueField q.ResidueField := by
    refine .of_algebraMap_eq fun x => ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [RingHom.algebraMap_toAlgebra, ← IsScalarTower.algebraMap_apply]
  refine .extendScalars (Ideal.injective_algebraMap_quotient_residueField p)

end prime

namespace IsLocalRing

variable {R k : Type*} [CommRing R] [IsLocalRing R] [Field k] [Algebra R k]

/--
Instance `ResidueField.algebraOfIsIntegral` / 实例 `ResidueField.algebraOfIsIntegral`

English:
instance ResidueField.algebraOfIsIntegral
  signature: [Algebra.IsIntegral R k]
  body: fast_instance% (Ideal.Quotient.lift (maximalIdeal R) (algebraMap R k)
    (by simp [← eq_maximalIdeal (Algebra.ker_algebraMap_isMaximal_of_isIntegral R k)])).toAlgebra

中文:
实例 ResidueField.algebraOfIs整数egral
  签名: [代数.是整 R k]
  定义体: fast_instance% (Ideal.Quotient.lift (maximalIdeal R) (algebraMap R k)
    (by simp [← eq_maximalIdeal (Algebra.ker_algebraMap_isMaximal_of_isIntegral R k)])).toAlgebra

Depends on / 依赖: Algebra, Algebra.ker_algebraMap_isMaximal_of_isIntegral, Ideal.Quotient.lift, Quotient, algebraMap, eq_maximalIdeal, fast_instance, ker_algebraMap_isMaximal_of_isIntegral, maximalIdeal, toAlgebra
-/
instance ResidueField.algebraOfIsIntegral [Algebra.IsIntegral R k] : Algebra (ResidueField R) k :=
  fast_instance% (Ideal.Quotient.lift (maximalIdeal R) (algebraMap R k)
    (by simp [← eq_maximalIdeal (Algebra.ker_algebraMap_isMaximal_of_isIntegral R k)])).toAlgebra

/--
Instance `ResidueField.isScalarTowerOfIsIntegral` / 实例 `ResidueField.isScalarTowerOfIsIntegral`

English:
instance ResidueField.isScalarTowerOfIsIntegral
  signature: [Algebra.IsIntegral R k]
  body: .of_algebraMap_eq fun _ => rfl

中文:
实例 ResidueField.isScalarTowerOfIs整数egral
  签名: [代数.是整 R k]
  定义体: .of_algebraMap_eq fun _ => rfl

Depends on / 依赖: of_algebraMap_eq
-/
instance ResidueField.isScalarTowerOfIsIntegral [Algebra.IsIntegral R k] :
    IsScalarTower R (ResidueField R) k :=
  .of_algebraMap_eq fun _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Module.Finite
  signature: R k] : Module.Finite (ResidueField R) k
  body: .of_equiv_equiv
  (Ideal.quotEquivOfEq (show Ideal.comap (algebraMap R k) ⊥ = maximalIdeal R by
    rw [← eq_maximalIdeal (Algebra.ker_algebraMap_isMaximal_of_isIntegral R k)]; rw [RingHom.ker]))
  (RingEquiv.quotientBot k) (by ext; rfl)

中文:
实例 [模.有限
  签名: R k] : 模.有限 (ResidueField R) k
  定义体: .of_equiv_equiv
  (Ideal.quotEquivOfEq (show Ideal.comap (algebraMap R k) ⊥ = maximalIdeal R by
    rw [← eq_maximalIdeal (Algebra.ker_algebraMap_isMaximal_of_isIntegral R k)]; rw [RingHom.ker]))
  (RingEquiv.quotientBot k) (by ext; rfl)

Depends on / 依赖: of_equiv_equiv
-/
instance [Module.Finite R k] : Module.Finite (ResidueField R) k := .of_equiv_equiv
  (Ideal.quotEquivOfEq (show Ideal.comap (algebraMap R k) ⊥ = maximalIdeal R by
    rw [← eq_maximalIdeal (Algebra.ker_algebraMap_isMaximal_of_isIntegral R k)]; rw [RingHom.ker]))
  (RingEquiv.quotientBot k) (by ext; rfl)

end IsLocalRing
