/-
Copyright (c) 2025 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.RingTheory.IsGaloisGroup.Defs

/-!
# Galois Groups of Rings

Given an action of a group `G` on an extension of rings `B/A`, the predicate `IsGaloisGroup G A B`
states that `G` acts faithfully on `B` with fixed ring `A`. This file develops some of the theory
of this predicate without assuming Galois theory for fields.
-/

@[expose] public section

-- this file should not import any field theory beyond the contents of `FieldTheory/Fixed.lean`
-- material involving Galois theory should be placed in `FieldTheory/IsGaloisGroup.lean`
assert_not_exists IntermediateField.adjoin

open Module

section CommRing

variable (G A B : Type*) [Group G] [CommSemiring A] [Semiring B] [Algebra A B]
  [MulSemiringAction G B]

variable {C : Type*} [CommSemiring C] [Algebra C B]

variable {G} in
/--
theorem `Subgroup.smul_algebraMap` / 定理 `Subgroup.smul_algebraMap`

English:
theorem Subgroup.smul_algebraMap
  statement: {H : Subgroup G} [SMulCommClass H C B] {g : G}
  proof: smul_algebraMap (⟨g, hg⟩ : H) x

中文:
定理 子群.smul_algebraMap
  结论: {H : 子群 G} [标量交换类 H C B] {g : G}
  证明: smul_algebraMap (⟨g, hg⟩ : H) x
-/
protected theorem Subgroup.smul_algebraMap {H : Subgroup G} [SMulCommClass H C B] {g : G}
    (hg : g in H) (x : C) :
    g • algebraMap C B x = algebraMap C B x :=
  smul_algebraMap (⟨g, hg⟩ : H) x

/--
theorem `IsGaloisGroup.smul_mem_of_normal` / 定理 `IsGaloisGroup.smul_mem_of_normal`

English:
theorem IsGaloisGroup.smul_mem_of_normal
  statement: (N : Subgroup G) [hN : N.Normal]
  proof: by
  apply hC.isInvariant.isInvariant (g • algebraMap C B x)
  intro n
  rw [← inv_smul_eq_iff]; rw [Subgroup.smul_def]; rw [← mul_smul]; rw [← mul_smul]
  exact Subgroup.smul_algebraMap B (hN.conj_mem' n n.prop g) x

@[deprecated (since := "2026-05-28")] alias smul_eq_self := Subgroup.smul_algebraMap
@[deprecated (since := "2026-05-28")] alias smul_mem_of_normal := IsGaloisGroup.smul_mem_of_normal

中文:
定理 是Galois群.smul_mem_of_normal
  结论: (N : 子群 G) [hN : N.正规]
  证明: by
  apply hC.isInvariant.isInvariant (g • algebraMap C B x)
  intro n
  rw [← inv_smul_eq_iff]; rw [Subgroup.smul_def]; rw [← mul_smul]; rw [← mul_smul]
  exact Subgroup.smul_algebraMap B (hN.conj_mem' n n.prop g) x

@[deprecated (since := "2026-05-28")] alias smul_eq_self := Subgroup.smul_algebraMap
@[deprecated (since := "2026-05-28")] alias smul_mem_of_normal := IsGaloisGroup.smul_mem_of_normal

Depends on / 依赖: Subgroup, Subgroup.smul_algebraMap, Subgroup.smul_def, algebraMap, conj_mem, hC.isInvariant.isInvariant, hN.conj_mem, inv_smul_eq_iff, isInvariant, mul_smul, n.prop, smul_algebraMap, smul_def
-/
theorem IsGaloisGroup.smul_mem_of_normal (N : Subgroup G) [hN : N.Normal]
    [hC : IsGaloisGroup N C B] (g : G) (x : C) :
    g • algebraMap C B x in Set.range (algebraMap C B) := by
  apply hC.isInvariant.isInvariant (g • algebraMap C B x)
  intro n
  rw [← inv_smul_eq_iff]; rw [Subgroup.smul_def]; rw [← mul_smul]; rw [← mul_smul]
  exact Subgroup.smul_algebraMap B (hN.conj_mem' n n.prop g) x

@[deprecated (since := "2026-05-28")] alias smul_eq_self := Subgroup.smul_algebraMap
@[deprecated (since := "2026-05-28")] alias smul_mem_of_normal := IsGaloisGroup.smul_mem_of_normal

end CommRing

section Field

variable (G A B K L : Type*) [Group G] [CommRing A] [CommRing B] [MulSemiringAction G B]
  [Algebra A B] [Field K] [Field L] [Algebra K L] [Algebra A K] [Algebra B L] [Algebra A L]
  [IsFractionRing A K] [IsFractionRing B L] [IsScalarTower A K L] [IsScalarTower A B L]
  [MulSemiringAction G L] [SMulDistribClass G B L]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsGaloisGroup
  signature: G A B] : IsGaloisGroup G (algebraMap A B).range B where
  body: IsGaloisGroup.faithful A
  commutes := ⟨fun g ⟨a', ⟨a, ha⟩⟩ b => by simp [Subring.smul_def, ← ha]⟩
  isInvariant := ⟨fun b hb => by
    obtain ⟨a, ha⟩ := Algebra.IsInvariant.isInvariant (A := A) b hb
    exact ⟨⟨algebraMap A B a, ⟨a, rfl⟩⟩, ha⟩⟩

中文:
实例 [是Galois群
  签名: G A B] : 是Galois群 G (algebraMap A B).range B where
  定义体: IsGaloisGroup.faithful A
  commutes := ⟨fun g ⟨a', ⟨a, ha⟩⟩ b => by simp [Subring.smul_def, ← ha]⟩
  isInvariant := ⟨fun b hb => by
    obtain ⟨a, ha⟩ := Algebra.IsInvariant.isInvariant (A := A) b hb
    exact ⟨⟨algebraMap A B a, ⟨a, rfl⟩⟩, ha⟩⟩

Depends on / 依赖: CofiniteTopology, CofiniteTopology.nhds_eq, Filter, Filter.le_principal_iff, Filter.nonempty_of_mem, IsGaloisGroup, IsGaloisGroup.faithful, Or.inl, Or.inr, Ultrafilter, Ultrafilter.le_sup_iff, f.le_cofinite_or_eq_pure, faithful, isCompact_iff_ultrafilter_le_nhds, le_cofinite_or_eq_pure, le_principal_iff, le_rfl, le_sup_iff, nhds_eq, noetherianSpace_iff_isCompact
-/
instance [IsGaloisGroup G A B] : IsGaloisGroup G (algebraMap A B).range B where
  faithful := IsGaloisGroup.faithful A
  commutes := ⟨fun g ⟨a', ⟨a, ha⟩⟩ b => by simp [Subring.smul_def, ← ha]⟩
  isInvariant := ⟨fun b hb => by
    obtain ⟨a, ha⟩ := Algebra.IsInvariant.isInvariant (A := A) b hb
    exact ⟨⟨algebraMap A B a, ⟨a, rfl⟩⟩, ha⟩⟩

/--
theorem `IsGaloisGroup.to_isFractionRing_of_isIntegral` / 定理 `IsGaloisGroup.to_isFractionRing_of_isIntegral`

English:
theorem IsGaloisGroup.to_isFractionRing_of_isIntegral
  proof: have := hGAB.faithful
    IsFractionRing.faithfulSMul G B L
  commutes := IsFractionRing.smulCommClass G A B K L
  isInvariant := IsFractionRing.isInvariant_of_isIntegral G A B K L

中文:
定理 是Galois群.to_isFractionRing_of_is整数egral
  证明: have := hGAB.faithful
    IsFractionRing.faithfulSMul G B L
  commutes := IsFractionRing.smulCommClass G A B K L
  isInvariant := IsFractionRing.isInvariant_of_isIntegral G A B K L

Depends on / 依赖: IsFractionRing, IsFractionRing.faithfulSMul, IsFractionRing.isInvariant_of_isIntegral, IsFractionRing.smulCommClass, commutes, faithful, faithfulSMul, hGAB.faithful, isInvariant, isInvariant_of_isIntegral, smulCommClass
-/
theorem IsGaloisGroup.to_isFractionRing_of_isIntegral
    [Algebra.IsIntegral A B] [hGAB : IsGaloisGroup G A B] :
    IsGaloisGroup G K L where
  faithful :=
    have := hGAB.faithful
    IsFractionRing.faithfulSMul G B L
  commutes := IsFractionRing.smulCommClass G A B K L
  isInvariant := IsFractionRing.isInvariant_of_isIntegral G A B K L

/--
theorem `IsGaloisGroup.to_isFractionRing` / 定理 `IsGaloisGroup.to_isFractionRing`

English:
theorem IsGaloisGroup.to_isFractionRing
  given: [Finite G] [hGAB : IsGaloisGroup G A B]
  proof: have := hGAB.isInvariant.isIntegral
  IsGaloisGroup.to_isFractionRing_of_isIntegral G A B K L

中文:
定理 是Galois群.to_isFractionRing
  条件: [有限 G] [hGAB : 是Galois群 G A B]
  证明: have := hGAB.isInvariant.isIntegral
  IsGaloisGroup.to_isFractionRing_of_isIntegral G A B K L

Depends on / 依赖: IsGaloisGroup, IsGaloisGroup.to_isFractionRing_of_isIntegral, hGAB.isInvariant.isIntegral, isIntegral, isInvariant, to_isFractionRing_of_isIntegral
-/
theorem IsGaloisGroup.to_isFractionRing [Finite G] [hGAB : IsGaloisGroup G A B] :
    IsGaloisGroup G K L :=
  have := hGAB.isInvariant.isIntegral
  IsGaloisGroup.to_isFractionRing_of_isIntegral G A B K L

/--
theorem `IsGaloisGroup.of_isFractionRing` / 定理 `IsGaloisGroup.of_isFractionRing`

English:
theorem IsGaloisGroup.of_isFractionRing
  statement: [hGKL : IsGaloisGroup G K L]
  proof: by
  have hc (a : A) : (algebraMap K L) (algebraMap A K a) = (algebraMap B L) (algebraMap A B a) := by
    simp_rw [← IsScalarTower.algebraMap_apply]
  refine ⟨⟨fun h => ?_⟩, ⟨fun g x y => IsFractionRing.injective B L ?_⟩, ⟨fun x h => ?_⟩⟩
  · have := hGKL.faithful
    refine eq_of_smul_eq_smul fun (y : L) => ?_
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective B y
    simp only [smul_div₀', ← algebraMap.coe_smul', h]
  · simp [Algebra.smul_def, algebraMap.coe_smul', ← hc]
  · obtain ⟨b, hb⟩ := hGKL.isInvariant.isInvariant (algebraMap B L x)
      (by simpa [← algebraMap.coe_smul'])
    have hx : IsIntegral A (algebraMap B L x) := (Algebra.IsIntegral.isIntegral x).algebraMap
    rw [← hb]; rw [isIntegral_algebraMap_iff (algebraMap K L).injective]; rw [IsIntegrallyClosedIn.isIntegral_iff] at hx
    obtain ⟨a, rfl⟩ := hx
    exact ⟨a, by rwa [hc, IsFractionRing.coe_inj] at hb⟩

中文:
定理 是Galois群.of_isFractionRing
  结论: [hGKL : 是Galois群 G K L]
  证明: by
  have hc (a : A) : (algebraMap K L) (algebraMap A K a) = (algebraMap B L) (algebraMap A B a) := by
    simp_rw [← IsScalarTower.algebraMap_apply]
  refine ⟨⟨fun h => ?_⟩, ⟨fun g x y => IsFractionRing.injective B L ?_⟩, ⟨fun x h => ?_⟩⟩
  · have := hGKL.faithful
    refine eq_of_smul_eq_smul fun (y : L) => ?_
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective B y
    simp only [smul_div₀', ← algebraMap.coe_smul', h]
  · simp [Algebra.smul_def, algebraMap.coe_smul', ← hc]
  · obtain ⟨b, hb⟩ := hGKL.isInvariant.isInvariant (algebraMap B L x)
      (by simpa [← algebraMap.coe_smul'])
    have hx : IsIntegral A (algebraMap B L x) := (Algebra.IsIntegral.isIntegral x).algebraMap
    rw [← hb]; rw [isIntegral_algebraMap_iff (algebraMap K L).injective]; rw [IsIntegrallyClosedIn.isIntegral_iff] at hx
    obtain ⟨a, rfl⟩ := hx
    exact ⟨a, by rwa [hc, IsFractionRing.coe_inj] at hb⟩

Depends on / 依赖: Algebra, Algebra.smul_def, IsFractionRing, IsFractionRing.div_surjective, IsFractionRing.injective, IsScalarTower, IsScalarTower.algebraMap_apply, algebraMap, algebraMap.coe_smul, algebraMap_apply, coe_smul, div_surjective, eq_of_smul_eq_smul, faithful, hGKL.faithful, hGKL.isInvariant, injective, isInvariant, simp_rw, smul_def
-/
theorem IsGaloisGroup.of_isFractionRing [hGKL : IsGaloisGroup G K L]
    [IsIntegrallyClosed A] [Algebra.IsIntegral A B] : IsGaloisGroup G A B := by
  have hc (a : A) : (algebraMap K L) (algebraMap A K a) = (algebraMap B L) (algebraMap A B a) := by
    simp_rw [← IsScalarTower.algebraMap_apply]
  refine ⟨⟨fun h => ?_⟩, ⟨fun g x y => IsFractionRing.injective B L ?_⟩, ⟨fun x h => ?_⟩⟩
  · have := hGKL.faithful
    refine eq_of_smul_eq_smul fun (y : L) => ?_
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective B y
    simp only [smul_div₀', ← algebraMap.coe_smul', h]
  · simp [Algebra.smul_def, algebraMap.coe_smul', ← hc]
  · obtain ⟨b, hb⟩ := hGKL.isInvariant.isInvariant (algebraMap B L x)
      (by simpa [← algebraMap.coe_smul'])
    have hx : IsIntegral A (algebraMap B L x) := (Algebra.IsIntegral.isIntegral x).algebraMap
    rw [← hb]; rw [isIntegral_algebraMap_iff (algebraMap K L).injective]; rw [IsIntegrallyClosedIn.isIntegral_iff] at hx
    obtain ⟨a, rfl⟩ := hx
    exact ⟨a, by rwa [hc, IsFractionRing.coe_inj] at hb⟩

/--
theorem `IsGaloisGroup.iff_isFractionRing` / 定理 `IsGaloisGroup.iff_isFractionRing`

English:
theorem IsGaloisGroup.iff_isFractionRing
  given: [Finite G] [IsIntegrallyClosed A]
  proof: ⟨fun h => ⟨h.isInvariant.isIntegral, h.to_isFractionRing G A B K L⟩,
    fun ⟨_, h⟩ => h.of_isFractionRing G A B K L⟩

@[deprecated (since := "2026-04-20")] alias FractionRing.mulSemiringAction_of_isGaloisGroup :=
  IsFractionRing.mulSemiringAction

中文:
定理 是Galois群.iff_isFractionRing
  条件: [有限 G] [是整闭 A]
  证明: ⟨fun h => ⟨h.isInvariant.isIntegral, h.to_isFractionRing G A B K L⟩,
    fun ⟨_, h⟩ => h.of_isFractionRing G A B K L⟩

@[deprecated (since := "2026-04-20")] alias FractionRing.mulSemiringAction_of_isGaloisGroup :=
  IsFractionRing.mulSemiringAction

Depends on / 依赖: h.isInvariant.isIntegral, h.of_isFractionRing, h.to_isFractionRing, isIntegral, isInvariant, of_isFractionRing, to_isFractionRing
-/
theorem IsGaloisGroup.iff_isFractionRing [Finite G] [IsIntegrallyClosed A] :
    IsGaloisGroup G A B ↔ Algebra.IsIntegral A B ∧ IsGaloisGroup G K L :=
  ⟨fun h => ⟨h.isInvariant.isIntegral, h.to_isFractionRing G A B K L⟩,
    fun ⟨_, h⟩ => h.of_isFractionRing G A B K L⟩

@[deprecated (since := "2026-04-20")] alias FractionRing.mulSemiringAction_of_isGaloisGroup :=
  IsFractionRing.mulSemiringAction

/--
Instance `IsGaloisGroup.toFractionRing` / 实例 `IsGaloisGroup.toFractionRing`

English:
instance IsGaloisGroup.toFractionRing
  signature: [IsDomain A] [IsDomain B] [Finite G]
  body: IsFractionRing.mulSemiringAction G B (FractionRing B)
    IsGaloisGroup G (FractionRing A) (FractionRing B) := by
  let := IsFractionRing.mulSemiringAction G B (FractionRing B)
  apply IsGaloisGroup.to_isFractionRing G A B _ _

中文:
实例 是Galois群.toFractionRing
  签名: [是整环 A] [是整环 B] [有限 G]
  定义体: IsFractionRing.mulSemiringAction G B (FractionRing B)
    IsGaloisGroup G (FractionRing A) (FractionRing B) := by
  let := IsFractionRing.mulSemiringAction G B (FractionRing B)
  apply IsGaloisGroup.to_isFractionRing G A B _ _

Depends on / 依赖: FractionRing, IsFractionRing, IsFractionRing.mulSemiringAction, mulSemiringAction
-/
instance IsGaloisGroup.toFractionRing [IsDomain A] [IsDomain B] [Finite G]
    [IsGaloisGroup G A B] [Algebra (FractionRing A) (FractionRing B)]
    [IsScalarTower A (FractionRing A) (FractionRing B)] :
    letI := IsFractionRing.mulSemiringAction G B (FractionRing B)
    IsGaloisGroup G (FractionRing A) (FractionRing B) := by
  let := IsFractionRing.mulSemiringAction G B (FractionRing B)
  apply IsGaloisGroup.to_isFractionRing G A B _ _

end Field

variable (G : Type*) [Group G]

namespace IsGaloisGroup

section IsDomain

variable (A B : Type*) [CommRing A] [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B]
  [MulSemiringAction G B] [IsGaloisGroup G A B] [Finite G]

attribute [local instance] FractionRing.liftAlgebra in
/--
Definition of `mulEquivAlgEquiv` / `mulEquivAlgEquiv` 的定义

English:
definition mulEquivAlgEquiv
  signature: : G ≃* Gal(B/A)
  body: MulEquiv.ofBijective (MulSemiringAction.toAlgAut G A B) (by
    have := IsDomain.of_faithfulSMul A B
    have : FaithfulSMul G B := IsGaloisGroup.faithful A
    refine ⟨fun _ _ => eq_of_smul_eq_smul ∘ DFunLike.ext_iff.mp, fun φ => ?_⟩
    obtain ⟨g, hg⟩ := Ideal.Quotient.stabilizerHom_surjective G ⊥ ⊥
      (Ideal.Quotient.algEquivOfEqMap (⊥ : Ideal A) φ Ideal.map_bot.symm)
    use g
    rw [AlgEquiv.ext_iff] at hg ⊢
    exact fun x => (AlgEquiv.quotientBot A B).symm.injective (hg x))

中文:
定义 mulEquivAlgEquiv
  签名: : G ≃* Gal(B/A)
  定义体: MulEquiv.ofBijective (MulSemiringAction.toAlgAut G A B) (by
    have := IsDomain.of_faithfulSMul A B
    have : FaithfulSMul G B := IsGaloisGroup.faithful A
    refine ⟨fun _ _ => eq_of_smul_eq_smul ∘ DFunLike.ext_iff.mp, fun φ => ?_⟩
    obtain ⟨g, hg⟩ := Ideal.Quotient.stabilizerHom_surjective G ⊥ ⊥
      (Ideal.Quotient.algEquivOfEqMap (⊥ : Ideal A) φ Ideal.map_bot.symm)
    use g
    rw [AlgEquiv.ext_iff] at hg ⊢
    exact fun x => (AlgEquiv.quotientBot A B).symm.injective (hg x))
-/
@[simps!] noncomputable def mulEquivAlgEquiv : G ≃* Gal(B/A) :=
  MulEquiv.ofBijective (MulSemiringAction.toAlgAut G A B) (by
    have := IsDomain.of_faithfulSMul A B
    have : FaithfulSMul G B := IsGaloisGroup.faithful A
    refine ⟨fun _ _ => eq_of_smul_eq_smul ∘ DFunLike.ext_iff.mp, fun φ => ?_⟩
    obtain ⟨g, hg⟩ := Ideal.Quotient.stabilizerHom_surjective G ⊥ ⊥
      (Ideal.Quotient.algEquivOfEqMap (⊥ : Ideal A) φ Ideal.map_bot.symm)
    use g
    rw [AlgEquiv.ext_iff] at hg ⊢
    exact fun x => (AlgEquiv.quotientBot A B).symm.injective (hg x))

end IsDomain

variable (H : Subgroup G)

instance (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [MulSemiringAction G S] [hGKL : IsGaloisGroup G R S] :
    IsGaloisGroup H (FixedPoints.subalgebra R S H) S where
  faithful := have := hGKL.faithful; inferInstance
  commutes := inferInstance
  isInvariant := ⟨fun x h => ⟨⟨x, h⟩, rfl⟩⟩

section Quotient

section Semiring

variable (A B C : Type*) [CommSemiring A] [Semiring C] [Algebra A C] [MulSemiringAction G C]
variable (N : Subgroup G) [CommSemiring B] [Algebra B C]

/-- If `N` is a normal subgroup of `G` and `IsGaloisGroup N B C`, then `G` acts on `B`.
For `g : G` and `x : B`, `g • x` is the unique element of `B` whose image in `C` is
`g • algebraMap B C x`, see `algebraMap_smulOfNormal`. -/
@[implicit_reducible]
/--
Definition of `smulOfNormal` / `smulOfNormal` 的定义

English:
definition smulOfNormal
  signature: [N.Normal] [IsGaloisGroup N B C]
  body: (smul_mem_of_normal G C N g x).choose

@[simp]

中文:
定义 smulOfNormal
  签名: [N.正规] [是Galois群 N B C]
  定义体: (smul_mem_of_normal G C N g x).choose

@[simp]

Depends on / 依赖: smul_mem_of_normal
-/
noncomputable def smulOfNormal [N.Normal] [IsGaloisGroup N B C] : SMul G B where
  smul g x := (smul_mem_of_normal G C N g x).choose

@[simp]
/--
theorem `algebraMap_smulOfNormal` / 定理 `algebraMap_smulOfNormal`

English:
theorem algebraMap_smulOfNormal
  given: [N.Normal] [IsGaloisGroup N B C] (g : G) (x : B)
  proof: smulOfNormal G B C
    algebraMap B C (g • x) = g • algebraMap B C x :=
  (smul_mem_of_normal G C N g x).choose_spec

中文:
定理 algebraMap_smulOfNormal
  条件: [N.正规] [是Galois群 N B C] (g : G) (x : B)
  证明: smulOfNormal G B C
    algebraMap B C (g • x) = g • algebraMap B C x :=
  (smul_mem_of_normal G C N g x).choose_spec

Depends on / 依赖: smulOfNormal
-/
theorem algebraMap_smulOfNormal [N.Normal] [IsGaloisGroup N B C] (g : G) (x : B) :
    letI := smulOfNormal G B C
    algebraMap B C (g • x) = g • algebraMap B C x :=
  (smul_mem_of_normal G C N g x).choose_spec

/--
Instance `smulDistribClass_smulOfNormal` / 实例 `smulDistribClass_smulOfNormal`

English:
instance smulDistribClass_smulOfNormal
  signature: [N.Normal] [IsGaloisGroup N B C]
  body: smulOfNormal G B C
    SMulDistribClass G B C :=
  let := smulOfNormal G B C
  ⟨fun g b c => by simp [Algebra.smul_def]⟩

中文:
实例 smulDistribClass_smulOfNormal
  签名: [N.正规] [是Galois群 N B C]
  定义体: smulOfNormal G B C
    SMulDistribClass G B C :=
  let := smulOfNormal G B C
  ⟨fun g b c => by simp [Algebra.smul_def]⟩

Depends on / 依赖: Finite, Finite.to_noetherianSpace, NoetherianSpace, smulOfNormal, to_noetherianSpace
-/
instance smulDistribClass_smulOfNormal [N.Normal] [IsGaloisGroup N B C] :
    letI := smulOfNormal G B C
    SMulDistribClass G B C :=
  let := smulOfNormal G B C
  ⟨fun g b c => by simp [Algebra.smul_def]⟩

variable [FaithfulSMul B C]

/-- If `N` is a normal subgroup of `G` and `IsGaloisGroup N B C`, then `G` acts on `B` as a
`MulSemiringAction`, via the action defined in `smulOfNormal`. -/
@[implicit_reducible]
/--
Definition of `mulSemiringActionOfNormal` / `mulSemiringActionOfNormal` 的定义

English:
definition mulSemiringActionOfNormal
  signature: [IsGaloisGroup N B C] [N.Normal]
  body: by
  let : SMul G B := smulOfNormal G B C N
  have : SMulDistribClass G B C := smulDistribClass_smulOfNormal G B C N
  exact mulSemiringActionOfSmulDistribClass B C G

中文:
定义 mulSemiringActionOfNormal
  签名: [是Galois群 N B C] [N.正规]
  定义体: by
  let : SMul G B := smulOfNormal G B C N
  have : SMulDistribClass G B C := smulDistribClass_smulOfNormal G B C N
  exact mulSemiringActionOfSmulDistribClass B C G

Depends on / 依赖: IndiscreteTopology, NoetherianSpace, SMulDistribClass, mulSemiringActionOfSmulDistribClass, smulDistribClass_smulOfNormal, smulOfNormal
-/
noncomputable def mulSemiringActionOfNormal [IsGaloisGroup N B C] [N.Normal] :
    MulSemiringAction G B := by
  let : SMul G B := smulOfNormal G B C N
  have : SMulDistribClass G B C := smulDistribClass_smulOfNormal G B C N
  exact mulSemiringActionOfSmulDistribClass B C G

/-- If `N` is a normal subgroup of `G` and `IsGaloisGroup N B C`, then the quotient group `G ⧸ N`
acts on `B` by `(g : G ⧸ N) • x = g • x`. -/
@[implicit_reducible]
/--
Definition of `mulSemiringActionQuotient` / `mulSemiringActionQuotient` 的定义

English:
definition mulSemiringActionQuotient
  signature: [IsGaloisGroup N B C] [N.Normal]
  body: letI := mulSemiringActionOfNormal G B C N
  { smul q x :=
      Quotient.liftOn' q (· • x) fun g₁ g₂ h => by
      apply FaithfulSMul.algebraMap_injective B C
      rw [algebraMap.smul']; rw [algebraMap.smul']; rw [smul_eq_iff_eq_inv_smul]; rw [← smul_assoc]; rw [smul_eq_mul]; rw [Subgroup.smul_algebraMap C (by rwa [← QuotientGroup.leftRel_apply])]
    one_smul x := one_smul G x
    mul_smul q₁ q₂ x := Quotient.inductionOn₂' q₁ q₂ fun g h => mul_smul g h x
    smul_add q x y := Quotient.inductionOn' q fun g => smul_add g x y
    smul_zero q := Quotient.inductionOn' q fun g => smul_zero g
    smul_one q := Quotient.inductionOn' q fun g => smul_one g
    smul_mul q x y := Quotient.inductionOn' q fun g => smul_mul' g x y }

中文:
定义 mulSemiringActionQuotient
  签名: [是Galois群 N B C] [N.正规]
  定义体: letI := mulSemiringActionOfNormal G B C N
  { smul q x :=
      Quotient.liftOn' q (· • x) fun g₁ g₂ h => by
      apply FaithfulSMul.algebraMap_injective B C
      rw [algebraMap.smul']; rw [algebraMap.smul']; rw [smul_eq_iff_eq_inv_smul]; rw [← smul_assoc]; rw [smul_eq_mul]; rw [Subgroup.smul_algebraMap C (by rwa [← QuotientGroup.leftRel_apply])]
    one_smul x := one_smul G x
    mul_smul q₁ q₂ x := Quotient.inductionOn₂' q₁ q₂ fun g h => mul_smul g h x
    smul_add q x y := Quotient.inductionOn' q fun g => smul_add g x y
    smul_zero q := Quotient.inductionOn' q fun g => smul_zero g
    smul_one q := Quotient.inductionOn' q fun g => smul_one g
    smul_mul q x y := Quotient.inductionOn' q fun g => smul_mul' g x y }

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, Quotient, Quotient.inductionOn, Quotient.liftOn, QuotientGroup, QuotientGroup.leftRel_apply, Subgroup, Subgroup.smul_algebraMap, algebraMap, algebraMap.smul, algebraMap_injective, inductionOn, leftRel_apply, liftOn, mulSemiringActionOfNormal, mul_smul, one_smul, smul_add, smul_algebraMap
-/
noncomputable def mulSemiringActionQuotient [IsGaloisGroup N B C] [N.Normal] :
    MulSemiringAction (G ⧸ N) B :=
  letI := mulSemiringActionOfNormal G B C N
  { smul q x :=
      Quotient.liftOn' q (· • x) fun g₁ g₂ h => by
      apply FaithfulSMul.algebraMap_injective B C
      rw [algebraMap.smul']; rw [algebraMap.smul']; rw [smul_eq_iff_eq_inv_smul]; rw [← smul_assoc]; rw [smul_eq_mul]; rw [Subgroup.smul_algebraMap C (by rwa [← QuotientGroup.leftRel_apply])]
    one_smul x := one_smul G x
    mul_smul q₁ q₂ x := Quotient.inductionOn₂' q₁ q₂ fun g h => mul_smul g h x
    smul_add q x y := Quotient.inductionOn' q fun g => smul_add g x y
    smul_zero q := Quotient.inductionOn' q fun g => smul_zero g
    smul_one q := Quotient.inductionOn' q fun g => smul_one g
    smul_mul q x y := Quotient.inductionOn' q fun g => smul_mul' g x y }

/--
theorem `mulSemiringActionQuotient_smul_def` / 定理 `mulSemiringActionQuotient_smul_def`

English:
theorem mulSemiringActionQuotient_smul_def
  statement: [MulSemiringAction G B] [SMulDistribClass G B C]
  proof: mulSemiringActionQuotient G B C N
    (g : G ⧸ N) • b = g • b := by
  let := mulSemiringActionOfNormal G B C N
  refine (Quotient.liftOn'_mk'' (· • b) _ g).trans (FaithfulSMul.algebraMap_injective B C ?_)
  rw [algebraMap.smul']; rw [algebraMap.smul']

中文:
定理 mulSemiringActionQuotient_smul_def
  结论: [MulSemiring作用 G B] [SMulDistrib类 G B C]
  证明: mulSemiringActionQuotient G B C N
    (g : G ⧸ N) • b = g • b := by
  let := mulSemiringActionOfNormal G B C N
  refine (Quotient.liftOn'_mk'' (· • b) _ g).trans (FaithfulSMul.algebraMap_injective B C ?_)
  rw [algebraMap.smul']; rw [algebraMap.smul']

Depends on / 依赖: mulSemiringActionQuotient
-/
theorem mulSemiringActionQuotient_smul_def [MulSemiringAction G B] [SMulDistribClass G B C]
    [IsGaloisGroup N B C] [N.Normal] (g : G) (b : B) :
    letI := mulSemiringActionQuotient G B C N
    (g : G ⧸ N) • b = g • b := by
  let := mulSemiringActionOfNormal G B C N
  refine (Quotient.liftOn'_mk'' (· • b) _ g).trans (FaithfulSMul.algebraMap_injective B C ?_)
  rw [algebraMap.smul']; rw [algebraMap.smul']

/--
Instance `isScalarTower_mulSemiringActionQuotient` / 实例 `isScalarTower_mulSemiringActionQuotient`

English:
instance isScalarTower_mulSemiringActionQuotient
  signature: [MulSemiringAction G B] [SMulDistribClass G B C]
  body: mulSemiringActionQuotient G B C N
    IsScalarTower G (G ⧸ N) B :=
  let := mulSemiringActionQuotient G B C N
  ⟨fun g q b => Quotient.inductionOn' q fun h => by
    simp [mul_smul, mulSemiringActionQuotient_smul_def]⟩

中文:
实例 isScalarTower_mulSemiringActionQuotient
  签名: [MulSemiring作用 G B] [SMulDistrib类 G B C]
  定义体: mulSemiringActionQuotient G B C N
    IsScalarTower G (G ⧸ N) B :=
  let := mulSemiringActionQuotient G B C N
  ⟨fun g q b => Quotient.inductionOn' q fun h => by
    simp [mul_smul, mulSemiringActionQuotient_smul_def]⟩

Depends on / 依赖: mulSemiringActionQuotient
-/
instance isScalarTower_mulSemiringActionQuotient [MulSemiringAction G B] [SMulDistribClass G B C]
    [IsGaloisGroup N B C] [N.Normal] :
    letI := mulSemiringActionQuotient G B C N
    IsScalarTower G (G ⧸ N) B :=
  let := mulSemiringActionQuotient G B C N
  ⟨fun g q b => Quotient.inductionOn' q fun h => by
    simp [mul_smul, mulSemiringActionQuotient_smul_def]⟩

/--
theorem `smulCommClassQuotient` / 定理 `smulCommClassQuotient`

English:
theorem smulCommClassQuotient
  statement: [N.Normal] [Algebra A B] [IsScalarTower A B C] [SMulCommClass G A C]
  proof: ⟨fun g k x => Quotient.inductionOn' g fun g =>
    FaithfulSMul.algebraMap_injective B C (by
      simp [algebraMap.smul, algebraMap.smul', smul_comm])⟩

中文:
定理 smulCommClassQuotient
  结论: [N.正规] [代数 A B] [标量塔 A B C] [标量交换类 G A C]
  证明: ⟨fun g k x => Quotient.inductionOn' g fun g =>
    FaithfulSMul.algebraMap_injective B C (by
      simp [algebraMap.smul, algebraMap.smul', smul_comm])⟩

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, Quotient, Quotient.inductionOn, algebraMap, algebraMap.smul, algebraMap_injective, inductionOn, smul_comm
-/
theorem smulCommClassQuotient [N.Normal] [Algebra A B] [IsScalarTower A B C] [SMulCommClass G A C]
    [MulSemiringAction G B] [MulAction (G ⧸ N) B] [SMulDistribClass G B C]
    [IsScalarTower G (G ⧸ N) B] :
    SMulCommClass (G ⧸ N) A B :=
  ⟨fun g k x => Quotient.inductionOn' g fun g =>
    FaithfulSMul.algebraMap_injective B C (by
      simp [algebraMap.smul, algebraMap.smul', smul_comm])⟩

end Semiring

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [MulSemiringAction G L]

variable (F : IntermediateField K L) (N : Subgroup G) [N.Normal] [IsGaloisGroup N F L]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulSemiringAction (G ⧸ N) F
  body: letI := smulOfNormal G F L N
  haveI := smulDistribClass_smulOfNormal G F L N
  letI := mulSemiringActionOfSmulDistribClass F L G
  mulSemiringActionQuotient G F L N

中文:
实例 :
  签名: MulSemiring作用 (G ⧸ N) F
  定义体: letI := smulOfNormal G F L N
  haveI := smulDistribClass_smulOfNormal G F L N
  letI := mulSemiringActionOfSmulDistribClass F L G
  mulSemiringActionQuotient G F L N

Depends on / 依赖: mulSemiringActionOfSmulDistribClass, mulSemiringActionQuotient, smulDistribClass_smulOfNormal, smulOfNormal
-/
noncomputable instance : MulSemiringAction (G ⧸ N) F :=
  letI := smulOfNormal G F L N
  haveI := smulDistribClass_smulOfNormal G F L N
  letI := mulSemiringActionOfSmulDistribClass F L G
  mulSemiringActionQuotient G F L N

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMulCommClass
  signature: G K L] [MulSemiringAction G F] [SMulDistribClass G F L]
  body: smulCommClassQuotient G K F L N

中文:
实例 [标量交换类
  签名: G K L] [MulSemiring作用 G F] [SMulDistrib类 G F L]
  定义体: smulCommClassQuotient G K F L N

Depends on / 依赖: smulCommClassQuotient
-/
instance [SMulCommClass G K L] [MulSemiringAction G F] [SMulDistribClass G F L]
    [IsScalarTower G (G ⧸ N) F] : SMulCommClass (G ⧸ N) K F :=
  smulCommClassQuotient G K F L N

end Quotient

end IsGaloisGroup
