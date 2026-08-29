/-
Copyright (c) 2024 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict

/-!
# Invariant Extensions of Rings and Galois Theory

Given an extension of rings `B/A` and an action of `G` on `B`, the predicate
`Algebra.IsInvariant A B G` states that every fixed point of `B` lies in the image of `A`.

This file relates this predicate `Algebra.IsInvariant` to Galois theory.
-/

@[expose] public section

open scoped Pointwise

section Galois

variable (A K L B : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
  [Algebra A K] [Algebra B L] [IsFractionRing A K] [IsFractionRing B L]
  [Algebra A B] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
  [IsIntegrallyClosed A] [IsIntegralClosure B A L]

/-- In the AKLB setup, the Galois group of `L/K` acts on `B`. -/
@[implicit_reducible]
/--
Definition of `IsIntegralClosure.MulSemiringAction` / `IsIntegralClosure.MulSemiringAction` 的定义

English:
definition IsIntegralClosure.MulSemiringAction
  signature: [Algebra.IsAlgebraic K L]
  body: MulSemiringAction.compHom B (galRestrict A K L B).toMonoidHom

中文:
定义 是整闭包.MulSemiring作用
  签名: [代数.是代数 K L]
  定义体: MulSemiringAction.compHom B (galRestrict A K L B).toMonoidHom

Depends on / 依赖: MulSemiringAction, MulSemiringAction.compHom, compHom, galRestrict, toMonoidHom
-/
noncomputable def IsIntegralClosure.MulSemiringAction [Algebra.IsAlgebraic K L] :
    MulSemiringAction Gal(L/K) B :=
  MulSemiringAction.compHom B (galRestrict A K L B).toMonoidHom

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Algebra.IsAlgebraic
  signature: K L] : let
  body: IsIntegralClosure.MulSemiringAction A K L B
    SMulDistribClass Gal(L/K) B L :=
  let := IsIntegralClosure.MulSemiringAction A K L B
  ⟨fun g b l => by
    simp only [Algebra.smul_def, smul_mul', mul_eq_mul_right_iff]
    exact Or.inl (algebraMap_galRestrictHom_apply A K L B g b).symm⟩

中文:
实例 [代数.是代数
  签名: K L] : let
  定义体: IsIntegralClosure.MulSemiringAction A K L B
    SMulDistribClass Gal(L/K) B L :=
  let := IsIntegralClosure.MulSemiringAction A K L B
  ⟨fun g b l => by
    simp only [Algebra.smul_def, smul_mul', mul_eq_mul_right_iff]
    exact Or.inl (algebraMap_galRestrictHom_apply A K L B g b).symm⟩

Depends on / 依赖: IsIntegralClosure, IsIntegralClosure.MulSemiringAction, MulSemiringAction
-/
instance [Algebra.IsAlgebraic K L] : let := IsIntegralClosure.MulSemiringAction A K L B
    SMulDistribClass Gal(L/K) B L :=
  let := IsIntegralClosure.MulSemiringAction A K L B
  ⟨fun g b l => by
    simp only [Algebra.smul_def, smul_mul', mul_eq_mul_right_iff]
    exact Or.inl (algebraMap_galRestrictHom_apply A K L B g b).symm⟩

/--
theorem `Algebra.isInvariant_of_isGalois` / 定理 `Algebra.isInvariant_of_isGalois`

English:
theorem Algebra.isInvariant_of_isGalois
  given: [FiniteDimensional K L] [h : IsGalois K L]
  proof: IsIntegralClosure.MulSemiringAction A K L B
    Algebra.IsInvariant A B Gal(L/K) := by
  replace h := ((IsGalois.tfae (F := K) (E := L)).out 0 1).mp h
  let := IsIntegralClosure.MulSemiringAction A K L B
  refine ⟨fun b hb => ?_⟩
  replace hb : algebraMap B L b in IntermediateField.fixedField (⊤ : Subgroup Gal(L/K)) := by
    rintro ⟨g, -⟩
    exact (algebraMap_galRestrict_apply A g b).symm.trans (congrArg (algebraMap B L) (hb g))
  rw [h]; rw [IntermediateField.mem_bot] at hb
  obtain ⟨k, hk⟩ := hb
  have hb : IsIntegral A b := IsIntegralClosure.isIntegral A L b
  rw [← isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective B L)]; rw [← hk]; rw [isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective K L)] at hb
  obtain ⟨a, rfl⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hb
  rw [← IsScalarTower.algebraMap_apply]; rw [IsScalarTower.algebraMap_apply A B L]; rw [(FaithfulSMul.algebraMap_injective B L).eq_iff] at hk
  exact ⟨a, hk⟩

中文:
定理 代数.isInvariant_of_isGalois
  条件: [有限维 K L] [h : 是Galois K L]
  证明: IsIntegralClosure.MulSemiringAction A K L B
    Algebra.IsInvariant A B Gal(L/K) := by
  replace h := ((IsGalois.tfae (F := K) (E := L)).out 0 1).mp h
  let := IsIntegralClosure.MulSemiringAction A K L B
  refine ⟨fun b hb => ?_⟩
  replace hb : algebraMap B L b in IntermediateField.fixedField (⊤ : Subgroup Gal(L/K)) := by
    rintro ⟨g, -⟩
    exact (algebraMap_galRestrict_apply A g b).symm.trans (congrArg (algebraMap B L) (hb g))
  rw [h]; rw [IntermediateField.mem_bot] at hb
  obtain ⟨k, hk⟩ := hb
  have hb : IsIntegral A b := IsIntegralClosure.isIntegral A L b
  rw [← isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective B L)]; rw [← hk]; rw [isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective K L)] at hb
  obtain ⟨a, rfl⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hb
  rw [← IsScalarTower.algebraMap_apply]; rw [IsScalarTower.algebraMap_apply A B L]; rw [(FaithfulSMul.algebraMap_injective B L).eq_iff] at hk
  exact ⟨a, hk⟩

Depends on / 依赖: IsIntegralClosure, IsIntegralClosure.MulSemiringAction, MulSemiringAction
-/
theorem Algebra.isInvariant_of_isGalois [FiniteDimensional K L] [h : IsGalois K L] :
    letI := IsIntegralClosure.MulSemiringAction A K L B
    Algebra.IsInvariant A B Gal(L/K) := by
  replace h := ((IsGalois.tfae (F := K) (E := L)).out 0 1).mp h
  let := IsIntegralClosure.MulSemiringAction A K L B
  refine ⟨fun b hb => ?_⟩
  replace hb : algebraMap B L b in IntermediateField.fixedField (⊤ : Subgroup Gal(L/K)) := by
    rintro ⟨g, -⟩
    exact (algebraMap_galRestrict_apply A g b).symm.trans (congrArg (algebraMap B L) (hb g))
  rw [h]; rw [IntermediateField.mem_bot] at hb
  obtain ⟨k, hk⟩ := hb
  have hb : IsIntegral A b := IsIntegralClosure.isIntegral A L b
  rw [← isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective B L)]; rw [← hk]; rw [isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective K L)] at hb
  obtain ⟨a, rfl⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hb
  rw [← IsScalarTower.algebraMap_apply]; rw [IsScalarTower.algebraMap_apply A B L]; rw [(FaithfulSMul.algebraMap_injective B L).eq_iff] at hk
  exact ⟨a, hk⟩

/--
theorem `Algebra.isInvariant_of_isGalois'` / 定理 `Algebra.isInvariant_of_isGalois'`

English:
theorem Algebra.isInvariant_of_isGalois'
  given: [FiniteDimensional K L] [IsGalois K L]
  proof: ⟨fun b h => (isInvariant_of_isGalois A K L B).1 b (fun g => h (galRestrict A K L B g))⟩

中文:
定理 代数.isInvariant_of_isGalois'
  条件: [有限维 K L] [是Galois K L]
  证明: ⟨fun b h => (isInvariant_of_isGalois A K L B).1 b (fun g => h (galRestrict A K L B g))⟩

Depends on / 依赖: galRestrict, isInvariant_of_isGalois
-/
theorem Algebra.isInvariant_of_isGalois' [FiniteDimensional K L] [IsGalois K L] :
    Algebra.IsInvariant A B (B ≃ₐ[A] B) :=
  ⟨fun b h => (isInvariant_of_isGalois A K L B).1 b (fun g => h (galRestrict A K L B g))⟩

end Galois

section normal

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (G : Type*) [Finite G] [Group G] [MulSemiringAction G B] [Algebra.IsInvariant A B G]
  (P : Ideal A) (Q : Ideal B) [Q.LiesOver P]

namespace Ideal.IsFractionRing

variable [P.IsPrime] [Q.IsPrime] (K L : Type*) [Field K] [Field L] [Algebra K L]
    [Algebra (A ⧸ P) K] [IsFractionRing (A ⧸ P) K] [Algebra (B ⧸ Q) L] [IsFractionRing (B ⧸ Q) L]
    [Algebra (A ⧸ P) L] [IsScalarTower (A ⧸ P) (B ⧸ Q) L] [IsScalarTower (A ⧸ P) K L]

open Polynomial in
include P Q G in
/--
lemma `normal` / 引理 `normal`

English:
lemma normal
  statement: Normal K L
  proof: by
  have := Algebra.IsInvariant.isIntegral A B G
  have := isAlgebraic_of_isFractionRing (A ⧸ P) (B ⧸ Q) K L
  constructor
  intro x
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (B ⧸ Q) x
  obtain ⟨b, a, ha, h⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := A ⧸ P) y).exists_smul_eq_mul x hy
  obtain ⟨a, rfl⟩ := Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Quotient.mk_surjective b
  simp_rw [← Quotient.algebraMap_eq] at *
  cases nonempty_fintype G
  obtain ⟨p, hp, -, h_monic⟩ := lifts_and_natDegree_eq_and_monic
    (Algebra.IsInvariant.charpoly_mem_lifts A B G b) (MulSemiringAction.monic_charpoly ..)
  have h_eval : p.aeval b = 0 := by
    rw [← eval_map_algebraMap]; rw [hp]; rw [MulSemiringAction.eval_charpoly]
  let q := p.comp (C a * X)
  let d := (algebraMap (B ⧸ Q) L) x / (algebraMap (B ⧸ Q) L) y
  have comm₁ : (algebraMap K L).comp (algebraMap (A ⧸ P) K) =
      (algebraMap (B ⧸ Q) L).comp (algebraMap (A ⧸ P) (B ⧸ Q)) := by
    simp_rw [← IsScalarTower.algebraMap_eq]
  have comm₂ : (algebraMap (A ⧸ P) (B ⧸ Q)).comp (algebraMap A (A ⧸ P)) =
      (algebraMap B (B ⧸ Q)).comp (algebraMap A B) := by
    simp_rw [← IsScalarTower.algebraMap_eq]
  replace h_eval : ((q.map (algebraMap A (A ⧸ P))).map (algebraMap (A ⧸ P) K)).aeval d = 0 := by
    simp_rw [q, map_comp, Polynomial.map_mul, map_C, map_X, aeval_comp, aeval_mul, aeval_C, aeval_X,
      ← RingHom.comp_apply, ← RingHom.comp_assoc, comm₁, RingHom.comp_apply, d, mul_div, ← map_mul]
    rw [← Algebra.smul_def]; rw [h]; rw [map_mul]; rw [mul_div_cancel_left₀ _ (by simpa using hy)]; rw [aeval_map_algebraMap]; rw [aeval_algebraMap_apply]; rw [aeval_map_algebraMap]; rw [aeval_algebraMap_apply]; rw [h_eval]; rw [map_zero]; rw [map_zero]
  replace h_splits : (p.map (algebraMap A B)).Splits := by
    rw [hp]
    exact MulSemiringAction.splits_charpoly G b
  refine .of_dvd ?_ ?_ (map_dvd (algebraMap K L) (minpoly.dvd K d h_eval))
  · simp_rw [q, map_comp, Polynomial.map_mul, map_C, map_X]
    refine .comp_of_degree_le_one ?_ (degree_C_mul_X_le _)
    rw [Polynomial.map_map]; rw [Polynomial.map_map]; rw [comm₁]; rw [RingHom.comp_assoc]; rw [comm₂]; rw [← RingHom.comp_assoc]; rw [← Polynomial.map_map]
    apply h_splits.map
  · simp_rw [q, map_comp, Polynomial.map_mul, map_C, map_X, Polynomial.map_map]
    exact mt (comp_C_mul_X_eq_zero_iff (by simpa)).mp (map_monic_ne_zero h_monic)

include P Q in

中文:
引理 normal
  结论: 正规 K L
  证明: by
  have := Algebra.IsInvariant.isIntegral A B G
  have := isAlgebraic_of_isFractionRing (A ⧸ P) (B ⧸ Q) K L
  constructor
  intro x
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (B ⧸ Q) x
  obtain ⟨b, a, ha, h⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := A ⧸ P) y).exists_smul_eq_mul x hy
  obtain ⟨a, rfl⟩ := Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Quotient.mk_surjective b
  simp_rw [← Quotient.algebraMap_eq] at *
  cases nonempty_fintype G
  obtain ⟨p, hp, -, h_monic⟩ := lifts_and_natDegree_eq_and_monic
    (Algebra.IsInvariant.charpoly_mem_lifts A B G b) (MulSemiringAction.monic_charpoly ..)
  have h_eval : p.aeval b = 0 := by
    rw [← eval_map_algebraMap]; rw [hp]; rw [MulSemiringAction.eval_charpoly]
  let q := p.comp (C a * X)
  let d := (algebraMap (B ⧸ Q) L) x / (algebraMap (B ⧸ Q) L) y
  have comm₁ : (algebraMap K L).comp (algebraMap (A ⧸ P) K) =
      (algebraMap (B ⧸ Q) L).comp (algebraMap (A ⧸ P) (B ⧸ Q)) := by
    simp_rw [← IsScalarTower.algebraMap_eq]
  have comm₂ : (algebraMap (A ⧸ P) (B ⧸ Q)).comp (algebraMap A (A ⧸ P)) =
      (algebraMap B (B ⧸ Q)).comp (algebraMap A B) := by
    simp_rw [← IsScalarTower.algebraMap_eq]
  replace h_eval : ((q.map (algebraMap A (A ⧸ P))).map (algebraMap (A ⧸ P) K)).aeval d = 0 := by
    simp_rw [q, map_comp, Polynomial.map_mul, map_C, map_X, aeval_comp, aeval_mul, aeval_C, aeval_X,
      ← RingHom.comp_apply, ← RingHom.comp_assoc, comm₁, RingHom.comp_apply, d, mul_div, ← map_mul]
    rw [← Algebra.smul_def]; rw [h]; rw [map_mul]; rw [mul_div_cancel_left₀ _ (by simpa using hy)]; rw [aeval_map_algebraMap]; rw [aeval_algebraMap_apply]; rw [aeval_map_algebraMap]; rw [aeval_algebraMap_apply]; rw [h_eval]; rw [map_zero]; rw [map_zero]
  replace h_splits : (p.map (algebraMap A B)).Splits := by
    rw [hp]
    exact MulSemiringAction.splits_charpoly G b
  refine .of_dvd ?_ ?_ (map_dvd (algebraMap K L) (minpoly.dvd K d h_eval))
  · simp_rw [q, map_comp, Polynomial.map_mul, map_C, map_X]
    refine .comp_of_degree_le_one ?_ (degree_C_mul_X_le _)
    rw [Polynomial.map_map]; rw [Polynomial.map_map]; rw [comm₁]; rw [RingHom.comp_assoc]; rw [comm₂]; rw [← RingHom.comp_assoc]; rw [← Polynomial.map_map]
    apply h_splits.map
  · simp_rw [q, map_comp, Polynomial.map_mul, map_C, map_X, Polynomial.map_map]
    exact mt (comp_C_mul_X_eq_zero_iff (by simpa)).mp (map_monic_ne_zero h_monic)

include P Q in

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.isAlgebraic, Algebra.IsInvariant.isIntegral, IsAlgebraic, IsFractionRing, IsFractionRing.div_surjective, IsInvariant, Quotient, Quotient.algebraMap_eq, Quotient.mk_surjective, algebraMap_eq, div_surjective, exists_smul_eq_mul, h_monic, isAlgebraic, isAlgebraic_of_isFractionRing, isIntegral, lifts_and_natDegree_eq_and_m, mk_surjective, nonempty_fintype
-/
lemma normal : Normal K L := by
  have := Algebra.IsInvariant.isIntegral A B G
  have := isAlgebraic_of_isFractionRing (A ⧸ P) (B ⧸ Q) K L
  constructor
  intro x
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (B ⧸ Q) x
  obtain ⟨b, a, ha, h⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := A ⧸ P) y).exists_smul_eq_mul x hy
  obtain ⟨a, rfl⟩ := Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Quotient.mk_surjective b
  simp_rw [← Quotient.algebraMap_eq] at *
  cases nonempty_fintype G
  obtain ⟨p, hp, -, h_monic⟩ := lifts_and_natDegree_eq_and_monic
    (Algebra.IsInvariant.charpoly_mem_lifts A B G b) (MulSemiringAction.monic_charpoly ..)
  have h_eval : p.aeval b = 0 := by
    rw [← eval_map_algebraMap]; rw [hp]; rw [MulSemiringAction.eval_charpoly]
  let q := p.comp (C a * X)
  let d := (algebraMap (B ⧸ Q) L) x / (algebraMap (B ⧸ Q) L) y
  have comm₁ : (algebraMap K L).comp (algebraMap (A ⧸ P) K) =
      (algebraMap (B ⧸ Q) L).comp (algebraMap (A ⧸ P) (B ⧸ Q)) := by
    simp_rw [← IsScalarTower.algebraMap_eq]
  have comm₂ : (algebraMap (A ⧸ P) (B ⧸ Q)).comp (algebraMap A (A ⧸ P)) =
      (algebraMap B (B ⧸ Q)).comp (algebraMap A B) := by
    simp_rw [← IsScalarTower.algebraMap_eq]
  replace h_eval : ((q.map (algebraMap A (A ⧸ P))).map (algebraMap (A ⧸ P) K)).aeval d = 0 := by
    simp_rw [q, map_comp, Polynomial.map_mul, map_C, map_X, aeval_comp, aeval_mul, aeval_C, aeval_X,
      ← RingHom.comp_apply, ← RingHom.comp_assoc, comm₁, RingHom.comp_apply, d, mul_div, ← map_mul]
    rw [← Algebra.smul_def]; rw [h]; rw [map_mul]; rw [mul_div_cancel_left₀ _ (by simpa using hy)]; rw [aeval_map_algebraMap]; rw [aeval_algebraMap_apply]; rw [aeval_map_algebraMap]; rw [aeval_algebraMap_apply]; rw [h_eval]; rw [map_zero]; rw [map_zero]
  replace h_splits : (p.map (algebraMap A B)).Splits := by
    rw [hp]
    exact MulSemiringAction.splits_charpoly G b
  refine .of_dvd ?_ ?_ (map_dvd (algebraMap K L) (minpoly.dvd K d h_eval))
  · simp_rw [q, map_comp, Polynomial.map_mul, map_C, map_X]
    refine .comp_of_degree_le_one ?_ (degree_C_mul_X_le _)
    rw [Polynomial.map_map]; rw [Polynomial.map_map]; rw [comm₁]; rw [RingHom.comp_assoc]; rw [comm₂]; rw [← RingHom.comp_assoc]; rw [← Polynomial.map_map]
    apply h_splits.map
  · simp_rw [q, map_comp, Polynomial.map_mul, map_C, map_X, Polynomial.map_map]
    exact mt (comp_C_mul_X_eq_zero_iff (by simpa)).mp (map_monic_ne_zero h_monic)

include P Q in
/--
lemma `finite_of_isInvariant` / 引理 `finite_of_isInvariant`

English:
lemma finite_of_isInvariant
  given: [SMulCommClass G A B] [Algebra.IsSeparable K L]
  proof: by
  have : IsGalois K L := { __ := normal G P Q K L }
  have := Finite.of_surjective _ (IsFractionRing.stabilizerHom_surjective G P Q K L)
  apply IsGalois.finiteDimensional_of_finite

中文:
引理 finite_of_isInvariant
  条件: [标量交换类 G A B] [代数.是可分 K L]
  证明: by
  have : IsGalois K L := { __ := normal G P Q K L }
  have := Finite.of_surjective _ (IsFractionRing.stabilizerHom_surjective G P Q K L)
  apply IsGalois.finiteDimensional_of_finite

Depends on / 依赖: Finite, Finite.of_surjective, IsFractionRing, IsFractionRing.stabilizerHom_surjective, IsGalois, IsGalois.finiteDimensional_of_finite, finiteDimensional_of_finite, normal, of_surjective, stabilizerHom_surjective
-/
lemma finite_of_isInvariant [SMulCommClass G A B] [Algebra.IsSeparable K L] :
    Module.Finite K L := by
  have : IsGalois K L := { __ := normal G P Q K L }
  have := Finite.of_surjective _ (IsFractionRing.stabilizerHom_surjective G P Q K L)
  apply IsGalois.finiteDimensional_of_finite

end Ideal.IsFractionRing

attribute [local instance] Ideal.Quotient.field in
include G in
/--
lemma `Ideal.Quotient.normal` / 引理 `Ideal.Quotient.normal`

English:
lemma Ideal.Quotient.normal
  given: [P.IsMaximal] [Q.IsMaximal]
  proof: IsFractionRing.normal G P Q (A ⧸ P) (B ⧸ Q)

中文:
引理 理想.商.normal
  条件: [P.是极大] [Q.是极大]
  证明: IsFractionRing.normal G P Q (A ⧸ P) (B ⧸ Q)

Depends on / 依赖: IsFractionRing, IsFractionRing.normal, normal
-/
lemma Ideal.Quotient.normal [P.IsMaximal] [Q.IsMaximal] :
    Normal (A ⧸ P) (B ⧸ Q) :=
  IsFractionRing.normal G P Q (A ⧸ P) (B ⧸ Q)

attribute [local instance] Ideal.Quotient.field in
include G in
/--
lemma `Ideal.Quotient.finite_of_isInvariant` / 引理 `Ideal.Quotient.finite_of_isInvariant`

English:
lemma Ideal.Quotient.finite_of_isInvariant
  statement: [P.IsMaximal] [Q.IsMaximal]
  proof: IsFractionRing.finite_of_isInvariant G P Q (A ⧸ P) (B ⧸ Q)

中文:
引理 理想.商.finite_of_isInvariant
  结论: [P.是极大] [Q.是极大]
  证明: IsFractionRing.finite_of_isInvariant G P Q (A ⧸ P) (B ⧸ Q)

Depends on / 依赖: IsFractionRing, IsFractionRing.finite_of_isInvariant, finite_of_isInvariant
-/
lemma Ideal.Quotient.finite_of_isInvariant [P.IsMaximal] [Q.IsMaximal]
    [SMulCommClass G A B] [Algebra.IsSeparable (A ⧸ P) (B ⧸ Q)] :
    Module.Finite (A ⧸ P) (B ⧸ Q) :=
  IsFractionRing.finite_of_isInvariant G P Q (A ⧸ P) (B ⧸ Q)

end normal
