/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# Smallness of Ext-groups from the existence of enough projectives

Let `C : Type u` be an abelian category (`Category.{v} C`) that has enough projectives.
If `C` is locally `w`-small, i.e. the type of morphisms in `C` are `Small.{w}`,
then we show that the condition `HasExt.{w}` holds, which means that for `X` and `Y` in `C`,
and `n : ℕ`, we may define `Ext X Y n : Type w`. In particular, this holds for `w = v`.

However, the main lemma `hasExt_of_enoughProjectives` is not made an instance:
for a given category `C`, there may be different reasonable choices for the universe `w`,
and if we have two `HasExt.{w₁}` and `HasExt.{w₂}` instances, we would have
to specify the universe explicitly almost everywhere, which would be an inconvenience.
So we must be very selective regarding `HasExt` instances.

-/

public section

universe w v u

open CategoryTheory Category

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace CochainComplex

open HomologicalComplex

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `isSplitEpi_to_singleFunctor_obj_of_projective` / 引理 `isSplitEpi_to_singleFunctor_obj_of_projective`

English:
lemma isSplitEpi_to_singleFunctor_obj_of_projective
  proof: by
  let e := K.iCyclesIso i (i + 1) (by simp)
    ((K.isZero_of_isStrictlyLE i (i + 1) (by simp)).eq_of_tgt _ _)
  let α := e.inv ≫ K.homologyπ i ≫ homologyMap π i ≫ (singleObjHomologySelfIso _ _ _).hom
  have : π.f i = α ≫ (singleObjXSelf (ComplexShape.up Int) i P).inv := by
    rw [← cancel_epi e

中文:
引理 isSplitEpi_to_singleFunctor_obj_of_projective
  证明: by
  let e := K.iCyclesIso i (i + 1) (by simp)
    ((K.isZero_of_isStrictlyLE i (i + 1) (by simp)).eq_of_tgt _ _)
  let α := e.inv ≫ K.homologyπ i ≫ homologyMap π i ≫ (singleObjHomologySelfIso _ _ _).hom
  have : π.f i = α ≫ (singleObjXSelf (ComplexShape.up Int) i P).inv := by
    rw [← cancel_epi e

Depends on / 依赖: ComplexShape, ComplexShape.up, K.homology, K.iCyclesIso, K.isZero_of_isStrictlyLE, cancel_epi, e.hom, e.inv, eq_of_tgt, homologyMap, iCyclesIso, iCyclesIso_hom_inv_id_assoc, isZero_of_isStrictlyLE, singleFunctor, singleFunctors, singleObjHomologySelfIso, singleObjXSelf
-/
lemma isSplitEpi_to_singleFunctor_obj_of_projective
    {P : C} [Projective P] {K : CochainComplex C Int} {i : Int}
    (π : K ⟶ (CochainComplex.singleFunctor C i).obj P) [K.IsStrictlyLE i] [QuasiIsoAt π i] :
    IsSplitEpi π := by
  let e := K.iCyclesIso i (i + 1) (by simp)
    ((K.isZero_of_isStrictlyLE i (i + 1) (by simp)).eq_of_tgt _ _)
  let α := e.inv ≫ K.homologyπ i ≫ homologyMap π i ≫ (singleObjHomologySelfIso _ _ _).hom
  have : π.f i = α ≫ (singleObjXSelf (ComplexShape.up Int) i P).inv := by
    rw [← cancel_epi e.hom]
    dsimp [α, e]
    rw [assoc]; rw [assoc]; rw [assoc]; rw [iCyclesIso_hom_inv_id_assoc]; rw [homologyπ_naturality_assoc]
    dsimp [singleFunctor, singleFunctors]
    rw [homologyπ_singleObjHomologySelfIso_hom_assoc]; rw [← singleObjCyclesSelfIso_inv_iCycles]; rw [Iso.hom_inv_id_assoc]; rw [← cyclesMap_i]
  exact ⟨⟨{
    section_ := mkHomFromSingle (Projective.factorThru (𝟙 P) α) (by
      rintro _ rfl
      apply (K.isZero_of_isStrictlyLE i (i + 1) (by simp)).eq_of_tgt)
    id := by
      apply HomologicalComplex.from_single_hom_ext
      rw [comp_f]; rw [mkHomFromSingle_f]; rw [assoc]; rw [id_f]; rw [this]; rw [Projective.factorThru_comp_assoc]; rw [id_comp]; rw [Iso.hom_inv_id]
      rfl }⟩⟩

end CochainComplex

namespace DerivedCategory

variable [HasDerivedCategory.{w} C]

/--
lemma `from_singleFunctor_obj_eq_zero_of_projective` / 引理 `from_singleFunctor_obj_eq_zero_of_projective`

English:
lemma from_singleFunctor_obj_eq_zero_of_projective
  statement: {P : C} [Projective P]
  proof: by
  obtain ⟨K, _, π, h, g, rfl⟩ := right_fac_of_isStrictlyLE φ i
  have hπ : IsSplitEpi π := by
    rw [isIso_Q_map_iff_quasiIso] at h
    exact CochainComplex.isSplitEpi_to_singleFunctor_obj_of_projective π
  have h₁ : inv (Q.map π) = Q.map (section_ π) := by
    rw [← cancel_mono (Q.map π)]; rw [

中文:
引理 from_singleFunctor_obj_eq_zero_of_projective
  结论: {P : C} [Projective P]
  证明: by
  obtain ⟨K, _, π, h, g, rfl⟩ := right_fac_of_isStrictlyLE φ i
  have hπ : IsSplitEpi π := by
    rw [isIso_Q_map_iff_quasiIso] at h
    exact CochainComplex.isSplitEpi_to_singleFunctor_obj_of_projective π
  have h₁ : inv (Q.map π) = Q.map (section_ π) := by
    rw [← cancel_mono (Q.map π)]; rw [

Depends on / 依赖: CochainComplex, CochainComplex.isSplitEpi_to_singleFunctor_obj_of_projective, HomologicalComplex, HomologicalComplex.from_single_hom_ext, IsIso.inv_hom_id, IsSplitEpi, IsSplitEpi.id, L.isZero_of_isStrictlyLE, Q.map, Q.map_comp, Q.map_id, cancel_mono, eq_of_tgt, from_single_hom_ext, inv_hom_id, isIso_Q_map_iff_quasiIso, isSplitEpi_to_singleFunctor_obj_of_projective, isZero_of_isStrictlyLE, map_comp, map_id
-/
lemma from_singleFunctor_obj_eq_zero_of_projective {P : C} [Projective P]
    {L : CochainComplex C Int} {i : Int}
    (φ : Q.obj ((CochainComplex.singleFunctor C i).obj P) ⟶ Q.obj L)
    (n : Int) (hn : n < i) [L.IsStrictlyLE n] :
    φ = 0 := by
  obtain ⟨K, _, π, h, g, rfl⟩ := right_fac_of_isStrictlyLE φ i
  have hπ : IsSplitEpi π := by
    rw [isIso_Q_map_iff_quasiIso] at h
    exact CochainComplex.isSplitEpi_to_singleFunctor_obj_of_projective π
  have h₁ : inv (Q.map π) = Q.map (section_ π) := by
    rw [← cancel_mono (Q.map π)]; rw [IsIso.inv_hom_id]; rw [← Q.map_comp]; rw [IsSplitEpi.id]; rw [Q.map_id]
  have h₂ : section_ π ≫ g = 0 := by
    apply HomologicalComplex.from_single_hom_ext
    apply (L.isZero_of_isStrictlyLE n i hn).eq_of_tgt
  rw [h₁]; rw [← Q.map_comp]; rw [h₂]; rw [Q.map_zero]

end DerivedCategory

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace Abelian.Ext

open DerivedCategory

set_option backward.isDefEq.respectTransparency false in
/--
lemma `eq_zero_of_projective` / 引理 `eq_zero_of_projective`

English:
lemma eq_zero_of_projective
  statement: [HasExt.{w} C] {P Y : C} {n : Nat} [Projective P]
  proof: by
  let := HasDerivedCategory.standard C
  apply homEquiv.injective
  simp only [← cancel_mono (((singleFunctors C).shiftIso (n + 1) (-(n + 1)) 0
    (by lia)).hom.app _), zero_hom, Limits.zero_comp]
  apply from_singleFunctor_obj_eq_zero_of_projective
    (L := (CochainComplex.singleFunctor C (-(n

中文:
引理 eq_zero_of_projective
  结论: [HasExt.{w} C] {P Y : C} {n : 自然数} [Projective P]
  证明: by
  let := HasDerivedCategory.standard C
  apply homEquiv.injective
  simp only [← cancel_mono (((singleFunctors C).shiftIso (n + 1) (-(n + 1)) 0
    (by lia)).hom.app _), zero_hom, Limits.zero_comp]
  apply from_singleFunctor_obj_eq_zero_of_projective
    (L := (CochainComplex.singleFunctor C (-(n

Depends on / 依赖: CochainComplex, CochainComplex.singleFunctor, HasDerivedCategory, HasDerivedCategory.standard, Limits, Limits.zero_comp, cancel_mono, from_singleFunctor_obj_eq_zero_of_projective, hom.app, homEquiv, homEquiv.injective, injective, shiftIso, singleFunctor, singleFunctors, standard, zero_comp, zero_hom
-/
lemma eq_zero_of_projective [HasExt.{w} C] {P Y : C} {n : Nat} [Projective P]
    (e : Ext P Y (n + 1)) : e = 0 := by
  let := HasDerivedCategory.standard C
  apply homEquiv.injective
  simp only [← cancel_mono (((singleFunctors C).shiftIso (n + 1) (-(n + 1)) 0
    (by lia)).hom.app _), zero_hom, Limits.zero_comp]
  apply from_singleFunctor_obj_eq_zero_of_projective
    (L := (CochainComplex.singleFunctor C (-(n + 1))).obj Y) (n := -(n + 1)) _ (by lia)

/--
lemma `subsingleton_of_projective` / 引理 `subsingleton_of_projective`

English:
lemma subsingleton_of_projective
  statement: [HasExt.{w} C]
  proof: subsingleton_of_forall_eq 0 Ext.eq_zero_of_projective

中文:
引理 subsingleton_of_projective
  结论: [HasExt.{w} C]
  证明: subsingleton_of_forall_eq 0 Ext.eq_zero_of_projective

Depends on / 依赖: Ext.eq_zero_of_projective, eq_zero_of_projective, subsingleton_of_forall_eq
-/
lemma subsingleton_of_projective [HasExt.{w} C]
    (P Y : C) [Projective P] (n : Nat) : Subsingleton (Ext.{w} P Y (n + 1)) :=
  subsingleton_of_forall_eq 0 Ext.eq_zero_of_projective

end Abelian.Ext

variable (C)

open Abelian

/--
lemma `hasExt_of_enoughProjectives` / 引理 `hasExt_of_enoughProjectives`

English:
lemma hasExt_of_enoughProjectives
  given: [LocallySmall.{w} C] [EnoughProjectives C]
  statement: HasExt.{w} C
  proof: by
  let := HasDerivedCategory.standard C
  have := hasExt_of_hasDerivedCategory C
  rw [hasExt_iff_small_ext.{w}]
  intro X Y n
  induction n generalizing X Y with
  | zero =>
    rw [small_congr Ext.homEquiv₀]
    infer_instance
  | succ n hn =>
    let S := ShortComplex.mk _ _ (kernel.condition (

中文:
引理 hasExt_of_enoughProjectives
  条件: [LocallySmall.{w} C] [EnoughProjectives C]
  结论: HasExt.{w} C
  证明: by
  let := HasDerivedCategory.standard C
  have := hasExt_of_hasDerivedCategory C
  rw [hasExt_iff_small_ext.{w}]
  intro X Y n
  induction n generalizing X Y with
  | zero =>
    rw [small_congr Ext.homEquiv₀]
    infer_instance
  | succ n hn =>
    let S := ShortComplex.mk _ _ (kernel.condition (

Depends on / 依赖: Ext.contravariant_sequence_exa, Ext.homEquiv, Ext.precomp, Function, Function.Surjective, HasDerivedCategory, HasDerivedCategory.standard, Projective, S.ShortExact, ShortComplex, ShortComplex.exact_of_f_is_kernel, ShortComplex.mk, ShortExact, Surjective, add_comm, condition, contravariant_sequence_exa, exact_of_f_is_kernel, extClass, generalizing
-/
lemma hasExt_of_enoughProjectives [LocallySmall.{w} C] [EnoughProjectives C] : HasExt.{w} C := by
  let := HasDerivedCategory.standard C
  have := hasExt_of_hasDerivedCategory C
  rw [hasExt_iff_small_ext.{w}]
  intro X Y n
  induction n generalizing X Y with
  | zero =>
    rw [small_congr Ext.homEquiv₀]
    infer_instance
  | succ n hn =>
    let S := ShortComplex.mk _ _ (kernel.condition (Projective.π X))
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel S.g) }
    have : Function.Surjective (Ext.precomp hS.extClass Y (add_comm 1 n)) := fun x₃ =>
      Ext.contravariant_sequence_exact₃ hS Y x₃
        (Ext.eq_zero_of_projective _) (by lia)
    exact small_of_surjective.{w} this

end CategoryTheory
