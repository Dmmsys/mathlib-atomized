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
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Algebra.IsSeparable (A ⧸ p) (B ⧸ q)] :
    Algebra.IsSeparable p.ResidueField q.ResidueField := by
  refine Algebra.IsSeparable.of_equiv_equiv
    (.ofBijective _ p.bijective_algebraMap_quotient_residueField)
    (.ofBijective _ q.bijective_algebraMap_quotient_residueField) ?_
  ext x
  simp [RingHom.algebraMap_toAlgebra, ← IsScalarTower.algebraMap_apply]

set_option backward.isDefEq.respectTransparency.types false in
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Algebra.IsSeparable p.ResidueField q.ResidueField] :
    Algebra.IsSeparable (A ⧸ p) (B ⧸ q) := by
  refine Algebra.IsSeparable.of_equiv_equiv
    (.symm <| .ofBijective _ p.bijective_algebraMap_quotient_residueField)
    (.symm <| .ofBijective _ q.bijective_algebraMap_quotient_residueField) ?_
  apply RingHom.ext fun x ↦ ?_
  obtain ⟨x, rfl⟩ :=
    (RingEquiv.ofBijective _ p.bijective_algebraMap_quotient_residueField).surjective x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  apply (RingEquiv.ofBijective _ q.bijective_algebraMap_quotient_residueField).injective
  simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, RingEquiv.symm_apply_apply,
    RingEquiv.apply_symm_apply]
  simp [RingHom.algebraMap_toAlgebra, ← IsScalarTower.algebraMap_apply]

variable {p q} in
/-
**Algebra.isSeparable_residueField_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.isSeparable_residueField_iff : Algebra.IsSeparable p.ResidueField 
q.ResidueField ↔ Algebra.IsSeparable (A ⧸ p) (B ⧸ q)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `instIsLocalHomAtPrimeRingHomAlgebraMap`：∀ {R : Type u_1} {A : Type u_3} 
[inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] (I : Ideal R)  
 [inst_3 : I.IsPrime] (J : I…
· 使用定理 `instIsSeparableQuotientIdealOfResidueField`：∀ {A : Type u_2} {B : Type u
_3} [inst : CommRing A] [inst_1 : CommRing B] [inst_2 : Algebra A B] (p : Ideal 
A)   (q : Ideal B) [inst_3 : q.L…
· 使用定理 `instIsSeparableResidueFieldOfQuotientIdeal`：∀ {A : Type u_2} {B : Type u
_3} [inst : CommRing A] [inst_1 : CommRing B] [inst_2 : Algebra A B] (p : Ideal 
A)   (q : Ideal B) [inst_3 : q.L…
-/
lemma Algebra.isSeparable_residueField_iff :
    Algebra.IsSeparable p.ResidueField q.ResidueField ↔ Algebra.IsSeparable (A ⧸ p) (B ⧸ q) :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

end maximal

section prime

variable [p.IsPrime] [q.IsPrime] [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
  [Localization.AtPrime.IsLiesOverAlgebra p q]

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra.IsAlgebraic (A ⧸ p) p.ResidueField :=
  IsLocalization.isAlgebraic _ (nonZeroDivisors (A ⧸ p))

set_option backward.isDefEq.respectTransparency.types false in
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Algebra.IsIntegral A B] :
    Algebra.IsAlgebraic p.ResidueField q.ResidueField := by
  have : Algebra.IsIntegral (A ⧸ p) (B ⧸ q) :=
    .tower_top A
  let := ((algebraMap (B ⧸ q) q.ResidueField).comp (algebraMap (A ⧸ p) (B ⧸ q))).toAlgebra
  have : IsScalarTower (A ⧸ p) (B ⧸ q) q.ResidueField := .of_algebraMap_eq' rfl
  have : Algebra.IsAlgebraic (A ⧸ p) q.ResidueField := .trans _ (B ⧸ q) _
  have : IsScalarTower (A ⧸ p) p.ResidueField q.ResidueField := by
    refine .of_algebraMap_eq fun x ↦ ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [RingHom.algebraMap_toAlgebra, ← IsScalarTower.algebraMap_apply]
  refine .extendScalars (Ideal.injective_algebraMap_quotient_residueField p)

end prime

namespace IsLocalRing

variable {R k : Type*} [CommRing R] [IsLocalRing R] [Field k] [Algebra R k]

/-
**IsLocalRing.ResidueField.algebraOfIsIntegral** 是 Mathlib 中的一个定义，位于命名空间 `IsLoca
lRing.ResidueField`。
形式化陈述：{R : Type u_4} →   {k : Type u_5} →     [inst : CommRing R] →       [inst_
1 : IsLocalRing R] →         [inst_2 : Field k] → [inst_3 : Algebra R k] → [Alge
bra.IsIntegral R k] → Algebra (IsLocalRing.ResidueField R) k
参数：IsLocalRing.ResidueField R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ResidueField.algebraOfIsIntegral [Algebra.IsIntegral R k] : Algebra (ResidueField R) k :=
  fast_instance% (Ideal.Quotient.lift (maximalIdeal R) (algebraMap R k)
    (by simp [← eq_maximalIdeal (Algebra.ker_algebraMap_isMaximal_of_isIntegral R k)])).toAlgebra
/-
**IsLocalRing.ResidueField.isScalarTowerOfIsIntegral** 是 Mathlib 中的一个定理，位于命名空间 `
IsLocalRing.ResidueField`。
形式化陈述：∀ {R : Type u_4} {k : Type u_5} [inst : CommRing R] [inst_1 : IsLocalRing 
R] [inst_2 : Field k] [inst_3 : Algebra R k]   [inst_4 : Algebra.IsIntegral R k]
, IsScalarTower R (IsLocalRing.ResidueField R) k
参数：IsLocalRing.ResidueField R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq`：of_algebraMap_eq [Algebra R A] (h : fora
ll x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S 
A
-/
instance ResidueField.isScalarTowerOfIsIntegral [Algebra.IsIntegral R k] :
    IsScalarTower R (ResidueField R) k :=
  .of_algebraMap_eq fun _ ↦ rfl
/-
**IsLocalRing.** 是 Mathlib 中的一个实例，位于命名空间 `IsLocalRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Module.Finite R k] : Module.Finite (ResidueField R) k := .of_equiv_equiv
  (Ideal.quotEquivOfEq (show Ideal.comap (algebraMap R k) ⊥ = maximalIdeal R by
    rw [← eq_maximalIdeal (Algebra.ker_algebraMap_isMaximal_of_isIntegral R k), RingHom.ker]))
  (RingEquiv.quotientBot k) (by ext; rfl)

end IsLocalRing

