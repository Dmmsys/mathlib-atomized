/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# Smallness of Ext-groups from the existence of enough injectives

Let `C : Type u` be an abelian category (`Category.{v} C`) that has enough injectives.
If `C` is locally `w`-small, i.e. the type of morphisms in `C` are `Small.{w}`,
then we show that the condition `HasExt.{w}` holds, which means that for `X` and `Y` in `C`,
and `n : ℕ`, we may define `Ext X Y n : Type w`. In particular, this holds for `w = v`.

However, the main lemma `hasExt_of_enoughInjectives` is not made an instance:
for a given category `C`, there may be different reasonable choices for the universe `w`,
and if we have two `HasExt.{w₁}` and `HasExt.{w₂}` instances, we would have
to specify the universe explicitly almost everywhere, which would be an inconvenience.
Then, we must be very selective regarding `HasExt` instances.

Note: this file dualizes the results in `HasEnoughProjectives.lean`.

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
lemma `isSplitMono_from_singleFunctor_obj_of_injective` / 引理 `isSplitMono_from_singleFunctor_obj_of_injective`

English:
lemma isSplitMono_from_singleFunctor_obj_of_injective
  proof: by
  let e := L.pOpcyclesIso (i - 1) i (by simp)
    ((L.isZero_of_isStrictlyGE i (i - 1) (by simp)).eq_of_src _ _)
  let α := (singleObjHomologySelfIso _ _ _).inv ≫ homologyMap ι i ≫ L.homologyι i ≫ e.inv
  have : ι.f i = (singleObjXSelf (ComplexShape.up Int) i I).hom ≫ α := by
    rw [← cancel_mono e.hom]
    dsimp [α, e]
    rw [assoc]; rw [assoc]; rw [assoc]; rw [assoc]; rw [pOpcyclesIso_inv_hom_id]; rw [comp_id]; rw [homologyι_naturality]
    dsimp [singleFunctor, singleFunctors]
    rw [singleObjHomologySelfIso_inv_homologyι_assoc]; rw [← pOpcycles_singleObjOpcyclesSelfIso_inv_assoc]; rw [Iso.inv_hom_id_assoc]; rw [p_opcyclesMap]
  exact ⟨⟨{
    retraction := mkHomToSingle (Injective.factorThru (𝟙 I) α) (by
      rintro j rfl
      apply (L.isZero_of_isStrictlyGE (j + 1) j (by simp)).eq_of_src)
    id := by
      apply HomologicalComplex.to_single_hom_ext
      rw [comp_f]; rw [mkHomToSingle_f]; rw [id_f]; rw [this]; rw [assoc]; rw [Injective.comp_factorThru_assoc]; rw [id_comp]; rw [Iso.hom_inv_id] }⟩⟩

中文:
引理 isSplitMono_from_singleFunctor_obj_of_injective
  证明: by
  let e := L.pOpcyclesIso (i - 1) i (by simp)
    ((L.isZero_of_isStrictlyGE i (i - 1) (by simp)).eq_of_src _ _)
  let α := (singleObjHomologySelfIso _ _ _).inv ≫ homologyMap ι i ≫ L.homologyι i ≫ e.inv
  have : ι.f i = (singleObjXSelf (ComplexShape.up Int) i I).hom ≫ α := by
    rw [← cancel_mono e.hom]
    dsimp [α, e]
    rw [assoc]; rw [assoc]; rw [assoc]; rw [assoc]; rw [pOpcyclesIso_inv_hom_id]; rw [comp_id]; rw [homologyι_naturality]
    dsimp [singleFunctor, singleFunctors]
    rw [singleObjHomologySelfIso_inv_homologyι_assoc]; rw [← pOpcycles_singleObjOpcyclesSelfIso_inv_assoc]; rw [Iso.inv_hom_id_assoc]; rw [p_opcyclesMap]
  exact ⟨⟨{
    retraction := mkHomToSingle (Injective.factorThru (𝟙 I) α) (by
      rintro j rfl
      apply (L.isZero_of_isStrictlyGE (j + 1) j (by simp)).eq_of_src)
    id := by
      apply HomologicalComplex.to_single_hom_ext
      rw [comp_f]; rw [mkHomToSingle_f]; rw [id_f]; rw [this]; rw [assoc]; rw [Injective.comp_factorThru_assoc]; rw [id_comp]; rw [Iso.hom_inv_id] }⟩⟩

Depends on / 依赖: ComplexShape, ComplexShape.up, L.homology, L.isZero_of_isStrictlyGE, L.pOpcyclesIso, cancel_mono, comp_id, e.hom, e.inv, eq_of_src, homologyMap, isZero_of_isStrictlyGE, pOpcyclesIso, pOpcyclesIso_inv_hom_id, singleFunctor, singleFunctors, singleObjHomologySelfIso, singleObjHomologySelfIso_inv_hom, singleObjXSelf
-/
lemma isSplitMono_from_singleFunctor_obj_of_injective
    {I : C} [Injective I] {L : CochainComplex C Int} {i : Int}
    (ι : (CochainComplex.singleFunctor C i).obj I ⟶ L) [L.IsStrictlyGE i] [QuasiIsoAt ι i] :
    IsSplitMono ι := by
  let e := L.pOpcyclesIso (i - 1) i (by simp)
    ((L.isZero_of_isStrictlyGE i (i - 1) (by simp)).eq_of_src _ _)
  let α := (singleObjHomologySelfIso _ _ _).inv ≫ homologyMap ι i ≫ L.homologyι i ≫ e.inv
  have : ι.f i = (singleObjXSelf (ComplexShape.up Int) i I).hom ≫ α := by
    rw [← cancel_mono e.hom]
    dsimp [α, e]
    rw [assoc]; rw [assoc]; rw [assoc]; rw [assoc]; rw [pOpcyclesIso_inv_hom_id]; rw [comp_id]; rw [homologyι_naturality]
    dsimp [singleFunctor, singleFunctors]
    rw [singleObjHomologySelfIso_inv_homologyι_assoc]; rw [← pOpcycles_singleObjOpcyclesSelfIso_inv_assoc]; rw [Iso.inv_hom_id_assoc]; rw [p_opcyclesMap]
  exact ⟨⟨{
    retraction := mkHomToSingle (Injective.factorThru (𝟙 I) α) (by
      rintro j rfl
      apply (L.isZero_of_isStrictlyGE (j + 1) j (by simp)).eq_of_src)
    id := by
      apply HomologicalComplex.to_single_hom_ext
      rw [comp_f]; rw [mkHomToSingle_f]; rw [id_f]; rw [this]; rw [assoc]; rw [Injective.comp_factorThru_assoc]; rw [id_comp]; rw [Iso.hom_inv_id] }⟩⟩

end CochainComplex

namespace DerivedCategory

variable [HasDerivedCategory.{w} C]

/--
lemma `to_singleFunctor_obj_eq_zero_of_injective` / 引理 `to_singleFunctor_obj_eq_zero_of_injective`

English:
lemma to_singleFunctor_obj_eq_zero_of_injective
  statement: {I : C} [Injective I]
  proof: by
  obtain ⟨L, _, g, ι, h, rfl⟩ := left_fac_of_isStrictlyGE φ i
  have hπ : IsSplitMono ι := by
    rw [isIso_Q_map_iff_quasiIso] at h
    exact CochainComplex.isSplitMono_from_singleFunctor_obj_of_injective ι
  have h₁ : inv (Q.map ι) = Q.map (retraction ι) := by
    rw [← cancel_epi (Q.map ι)]; rw [IsIso.hom_inv_id]; rw [← Q.map_comp]; rw [IsSplitMono.id]; rw [Q.map_id]
  have h₂ : g ≫ retraction ι = 0 := by
    apply HomologicalComplex.to_single_hom_ext
    apply (K.isZero_of_isStrictlyGE n i hn).eq_of_src
  rw [h₁]; rw [← Q.map_comp]; rw [h₂]; rw [Q.map_zero]

中文:
引理 to_singleFunctor_obj_eq_zero_of_injective
  结论: {I : C} [单射 I]
  证明: by
  obtain ⟨L, _, g, ι, h, rfl⟩ := left_fac_of_isStrictlyGE φ i
  have hπ : IsSplitMono ι := by
    rw [isIso_Q_map_iff_quasiIso] at h
    exact CochainComplex.isSplitMono_from_singleFunctor_obj_of_injective ι
  have h₁ : inv (Q.map ι) = Q.map (retraction ι) := by
    rw [← cancel_epi (Q.map ι)]; rw [IsIso.hom_inv_id]; rw [← Q.map_comp]; rw [IsSplitMono.id]; rw [Q.map_id]
  have h₂ : g ≫ retraction ι = 0 := by
    apply HomologicalComplex.to_single_hom_ext
    apply (K.isZero_of_isStrictlyGE n i hn).eq_of_src
  rw [h₁]; rw [← Q.map_comp]; rw [h₂]; rw [Q.map_zero]

Depends on / 依赖: CochainComplex, CochainComplex.isSplitMono_from_singleFunctor_obj_of_injective, HomologicalComplex, HomologicalComplex.to_single_hom_ext, IsIso.hom_inv_id, IsSplitMono, IsSplitMono.id, K.isZero_of_isStrictlyGE, Q.map, Q.map_comp, Q.map_id, cancel_epi, eq_of_src, hom_inv_id, isIso_Q_map_iff_quasiIso, isSplitMono_from_singleFunctor_obj_of_injective, isZero_of_isStrictlyGE, left_fac_of_isStrictlyGE, map_comp, map_id
-/
lemma to_singleFunctor_obj_eq_zero_of_injective {I : C} [Injective I]
    {K : CochainComplex C Int} {i : Int}
    (φ : Q.obj K ⟶ Q.obj ((CochainComplex.singleFunctor C i).obj I))
    (n : Int) (hn : i < n) [K.IsStrictlyGE n] :
    φ = 0 := by
  obtain ⟨L, _, g, ι, h, rfl⟩ := left_fac_of_isStrictlyGE φ i
  have hπ : IsSplitMono ι := by
    rw [isIso_Q_map_iff_quasiIso] at h
    exact CochainComplex.isSplitMono_from_singleFunctor_obj_of_injective ι
  have h₁ : inv (Q.map ι) = Q.map (retraction ι) := by
    rw [← cancel_epi (Q.map ι)]; rw [IsIso.hom_inv_id]; rw [← Q.map_comp]; rw [IsSplitMono.id]; rw [Q.map_id]
  have h₂ : g ≫ retraction ι = 0 := by
    apply HomologicalComplex.to_single_hom_ext
    apply (K.isZero_of_isStrictlyGE n i hn).eq_of_src
  rw [h₁]; rw [← Q.map_comp]; rw [h₂]; rw [Q.map_zero]

end DerivedCategory

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace Abelian.Ext

open DerivedCategory

set_option backward.isDefEq.respectTransparency false in
/--
lemma `eq_zero_of_injective` / 引理 `eq_zero_of_injective`

English:
lemma eq_zero_of_injective
  statement: [HasExt.{w} C] {X I : C} {n : Nat} [Injective I]
  proof: by
  let K := (CochainComplex.singleFunctor C 0).obj X
  have := K.isStrictlyGE_of_ge (-n) 0 (by lia)
  let := HasDerivedCategory.standard C
  apply homEquiv.injective
  simp only [← cancel_mono (((singleFunctors C).shiftIso (n + 1) (-(n + 1)) 0
    (by lia)).hom.app _), zero_hom, Limits.zero_comp]
  exact to_singleFunctor_obj_eq_zero_of_injective (K := K) (n := -n) _ (by lia)

中文:
引理 eq_zero_of_injective
  结论: [HasExt.{w} C] {X I : C} {n : 自然数} [单射 I]
  证明: by
  let K := (CochainComplex.singleFunctor C 0).obj X
  have := K.isStrictlyGE_of_ge (-n) 0 (by lia)
  let := HasDerivedCategory.standard C
  apply homEquiv.injective
  simp only [← cancel_mono (((singleFunctors C).shiftIso (n + 1) (-(n + 1)) 0
    (by lia)).hom.app _), zero_hom, Limits.zero_comp]
  exact to_singleFunctor_obj_eq_zero_of_injective (K := K) (n := -n) _ (by lia)

Depends on / 依赖: CochainComplex, CochainComplex.singleFunctor, HasDerivedCategory, HasDerivedCategory.standard, K.isStrictlyGE_of_ge, Limits, Limits.zero_comp, cancel_mono, hom.app, homEquiv, homEquiv.injective, injective, isStrictlyGE_of_ge, shiftIso, singleFunctor, singleFunctors, standard, to_singleFunctor_obj_eq_zero_of_injective, zero_comp, zero_hom
-/
lemma eq_zero_of_injective [HasExt.{w} C] {X I : C} {n : Nat} [Injective I]
    (e : Ext X I (n + 1)) : e = 0 := by
  let K := (CochainComplex.singleFunctor C 0).obj X
  have := K.isStrictlyGE_of_ge (-n) 0 (by lia)
  let := HasDerivedCategory.standard C
  apply homEquiv.injective
  simp only [← cancel_mono (((singleFunctors C).shiftIso (n + 1) (-(n + 1)) 0
    (by lia)).hom.app _), zero_hom, Limits.zero_comp]
  exact to_singleFunctor_obj_eq_zero_of_injective (K := K) (n := -n) _ (by lia)

/--
lemma `subsingleton_of_injective` / 引理 `subsingleton_of_injective`

English:
lemma subsingleton_of_injective
  statement: [HasExt.{w} C]
  proof: subsingleton_of_forall_eq 0 Ext.eq_zero_of_injective

中文:
引理 subsingleton_of_injective
  结论: [HasExt.{w} C]
  证明: subsingleton_of_forall_eq 0 Ext.eq_zero_of_injective

Depends on / 依赖: Ext.eq_zero_of_injective, eq_zero_of_injective, subsingleton_of_forall_eq
-/
lemma subsingleton_of_injective [HasExt.{w} C]
    (X I : C) [Injective I] (n : Nat) : Subsingleton (Ext.{w} X I (n + 1)) :=
  subsingleton_of_forall_eq 0 Ext.eq_zero_of_injective

end Abelian.Ext

variable (C)

open Abelian

/--
lemma `hasExt_of_enoughInjectives` / 引理 `hasExt_of_enoughInjectives`

English:
lemma hasExt_of_enoughInjectives
  given: [LocallySmall.{w} C] [EnoughInjectives C]
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
      let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι Y))
      have hS : S.ShortExact :=
        { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
      have : Function.Surjective (Ext.postcomp hS.extClass X (rfl : n + 1 = _)) :=
        fun y₁ => Ext.covariant_sequence_exact₁ X hS y₁ (Ext.eq_zero_of_injective _) rfl
      exact small_of_surjective.{w} this

中文:
引理 hasExt_of_enoughInjectives
  条件: [LocallySmall.{w} C] [有足够单射 C]
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
      let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι Y))
      have hS : S.ShortExact :=
        { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
      have : Function.Surjective (Ext.postcomp hS.extClass X (rfl : n + 1 = _)) :=
        fun y₁ => Ext.covariant_sequence_exact₁ X hS y₁ (Ext.eq_zero_of_injective _) rfl
      exact small_of_surjective.{w} this

Depends on / 依赖: Ext.covariant_seque, Ext.homEquiv, Ext.postcomp, Function, Function.Surjective, HasDerivedCategory, HasDerivedCategory.standard, Injective, S.ShortExact, ShortComplex, ShortComplex.exact_of_g_is_cokernel, ShortComplex.mk, ShortExact, Surjective, cokernel, cokernel.condition, cokernelIsCokernel, condition, covariant_seque, exact_of_g_is_cokernel
-/
lemma hasExt_of_enoughInjectives [LocallySmall.{w} C] [EnoughInjectives C] : HasExt.{w} C := by
    let := HasDerivedCategory.standard C
    have := hasExt_of_hasDerivedCategory C
    rw [hasExt_iff_small_ext.{w}]
    intro X Y n
    induction n generalizing X Y with
    | zero =>
      rw [small_congr Ext.homEquiv₀]
      infer_instance
    | succ n hn =>
      let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι Y))
      have hS : S.ShortExact :=
        { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
      have : Function.Surjective (Ext.postcomp hS.extClass X (rfl : n + 1 = _)) :=
        fun y₁ => Ext.covariant_sequence_exact₁ X hS y₁ (Ext.eq_zero_of_injective _) rfl
      exact small_of_surjective.{w} this

end CategoryTheory
