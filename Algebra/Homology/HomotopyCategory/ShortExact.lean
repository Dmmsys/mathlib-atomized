/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.Refinements

/-!
# The mapping cone of a monomorphism, up to a quasi-isomorphism

If `S` is a short exact short complex of cochain complexes in an abelian category,
we construct a quasi-isomorphism `descShortComplex S : mappingCone S.f ⟶ S.X₃`.

We obtain this by comparing the homology sequence of `S` and the homology
sequence of the homology functor on the homotopy category, applied to the
distinguished triangle attached to the mapping cone of `S.f`.

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

open CategoryTheory Category ComplexShape HomotopyCategory Limits
  HomologicalComplex.HomologySequence Pretriangulated Preadditive

variable {C : Type*} [Category* C] [Abelian C]

namespace CochainComplex

set_option backward.isDefEq.respectTransparency false in -- Needed in homologySequenceδ_triangleh
@[reassoc]
/--
lemma `homologySequenceδ_quotient_mapTriangle_obj` / 引理 `homologySequenceδ_quotient_mapTriangle_obj`

English:
lemma homologySequenceδ_quotient_mapTriangle_obj
  proof: by
  apply homologyFunctor_shiftMap

中文:
引理 homologySequenceδ_quotient_mapTriangle_obj
  证明: by
  apply homologyFunctor_shiftMap

Depends on / 依赖: homologyFunctor_shiftMap
-/
lemma homologySequenceδ_quotient_mapTriangle_obj
    (T : Triangle (CochainComplex C Int)) (n₀ n₁ : Int) (h : n₀ + 1 = n₁) :
    (homologyFunctor C (up Int) 0).homologySequenceδ
        ((quotient C (up Int)).mapTriangle.obj T) n₀ n₁ h =
      (homologyFunctorFactors C (up Int) n₀).hom.app _ ≫
        (HomologicalComplex.homologyFunctor C (up Int) 0).shiftMap T.mor₃ n₀ n₁ (by lia) ≫
        (homologyFunctorFactors C (up Int) n₁).inv.app _ := by
  apply homologyFunctor_shiftMap

namespace mappingCone

variable (S : ShortComplex (CochainComplex C Int)) (hS : S.ShortExact)

/--
Definition of `descShortComplex` / `descShortComplex` 的定义

English:
definition descShortComplex
  signature: : mappingCone S.f ⟶ S.X₃
  body: desc S.f 0 S.g (by simp)

@[reassoc (attr := simp)]

中文:
定义 descShortComplex
  签名: : mappingCone S.f ⟶ S.X₃
  定义体: desc S.f 0 S.g (by simp)

@[reassoc (attr := simp)]
-/
noncomputable def descShortComplex : mappingCone S.f ⟶ S.X₃ := desc S.f 0 S.g (by simp)

@[reassoc (attr := simp)]
/--
lemma `inr_descShortComplex` / 引理 `inr_descShortComplex`

English:
lemma inr_descShortComplex
  statement: inr S.f ≫ descShortComplex S = S.g
  proof: by
  simp [descShortComplex]

@[reassoc (attr := simp)]

中文:
引理 inr_descShortComplex
  结论: inr S.f ≫ descShortComplex S = S.g
  证明: by
  simp [descShortComplex]

@[reassoc (attr := simp)]

Depends on / 依赖: descShortComplex
-/
lemma inr_descShortComplex : inr S.f ≫ descShortComplex S = S.g := by
  simp [descShortComplex]

@[reassoc (attr := simp)]
/--
lemma `inr_f_descShortComplex_f` / 引理 `inr_f_descShortComplex_f`

English:
lemma inr_f_descShortComplex_f
  given: (n : Int)
  statement: (inr S.f).f n ≫ (descShortComplex S).f n = S.g.f n
  proof: by
  simp [descShortComplex]

@[reassoc (attr := simp)]

中文:
引理 inr_f_descShortComplex_f
  条件: (n : 整数)
  结论: (inr S.f).f n ≫ (descShortComplex S).f n = S.g.f n
  证明: by
  simp [descShortComplex]

@[reassoc (attr := simp)]

Depends on / 依赖: descShortComplex
-/
lemma inr_f_descShortComplex_f (n : Int) : (inr S.f).f n ≫ (descShortComplex S).f n = S.g.f n := by
  simp [descShortComplex]

@[reassoc (attr := simp)]
/--
lemma `inl_v_descShortComplex_f` / 引理 `inl_v_descShortComplex_f`

English:
lemma inl_v_descShortComplex_f
  given: (i j : Int) (h : i + (-1) = j)
  proof: by
  simp [descShortComplex]

中文:
引理 inl_v_descShortComplex_f
  条件: (i j : 整数) (h : i + (-1) = j)
  证明: by
  simp [descShortComplex]

Depends on / 依赖: IsIso.hom_inv_id, _i_assoc, cancel_mono, comp_id, descShortComplex, hom_inv_id, ofEpiOfIsIsoOfMono
-/
lemma inl_v_descShortComplex_f (i j : Int) (h : i + (-1) = j) :
    (inl S.f).v i j h ≫ (descShortComplex S).f j = 0 := by
  simp [descShortComplex]

section

variable (S₁ S₂ : ShortComplex (CochainComplex C Int)) (f : S₁ ⟶ S₂)

/--
lemma `map_descShortComplex` / 引理 `map_descShortComplex`

English:
lemma map_descShortComplex
  statement: map S₁.f S₂.f f.τ₁ f.τ₂ f.comm₁₂.symm ≫ descShortComplex S₂ =
  proof: by
  ext i
  simpa [mappingCone.ext_from_iff _ _ _ rfl, map] using
    congr_fun (congr_arg HomologicalComplex.Hom.f f.comm₂₃) i

中文:
引理 map_descShortComplex
  结论: map S₁.f S₂.f f.τ₁ f.τ₂ f.comm₁₂.symm ≫ descShortComplex S₂ =
  证明: by
  ext i
  simpa [mappingCone.ext_from_iff _ _ _ rfl, map] using
    congr_fun (congr_arg HomologicalComplex.Hom.f f.comm₂₃) i

Depends on / 依赖: HomologicalComplex, HomologicalComplex.Hom.f, congr_arg, congr_fun, ext_from_iff, f.comm, mappingCone, mappingCone.ext_from_iff
-/
lemma map_descShortComplex : map S₁.f S₂.f f.τ₁ f.τ₂ f.comm₁₂.symm ≫ descShortComplex S₂ =
    descShortComplex S₁ ≫ f.τ₃ := by
  ext i
  simpa [mappingCone.ext_from_iff _ _ _ rfl, map] using
    congr_fun (congr_arg HomologicalComplex.Hom.f f.comm₂₃) i

end

variable {S}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `homologySequenceδ_triangleh` / 引理 `homologySequenceδ_triangleh`

English:
lemma homologySequenceδ_triangleh
  given: (n₀ : Int) (n₁ : Int) (h : n₀ + 1 = n₁)
  proof: by
  /- We proceed by diagram chase. We test the identity on
     cocycles `x' : A' ⟶ (mappingCone S.f).X n₀` -/
  dsimp
  rw [← cancel_mono ((homologyFunctorFactors C (up Int) n₁).hom.app _)]; rw [assoc]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id_app]; rw [← cancel_epi ((homologyFunctorFactors C (

中文:
引理 homologySequenceδ_triangleh
  条件: (n₀ : 整数) (n₁ : 整数) (h : n₀ + 1 = n₁)
  证明: by
  /- We proceed by diagram chase. We test the identity on
     cocycles `x' : A' ⟶ (mappingCone S.f).X n₀` -/
  dsimp
  rw [← cancel_mono ((homologyFunctorFactors C (up Int) n₁).hom.app _)]; rw [assoc]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id_app]; rw [← cancel_epi ((homologyFunctorFactors C (
-/
lemma homologySequenceδ_triangleh (n₀ : Int) (n₁ : Int) (h : n₀ + 1 = n₁) :
    (homologyFunctor C (up Int) 0).homologySequenceδ (triangleh S.f) n₀ n₁ h =
      (homologyFunctorFactors C (up Int) n₀).hom.app _ ≫
        HomologicalComplex.homologyMap (descShortComplex S) n₀ ≫ hS.δ n₀ n₁ h ≫
          (homologyFunctorFactors C (up Int) n₁).inv.app _ := by
  /- We proceed by diagram chase. We test the identity on
     cocycles `x' : A' ⟶ (mappingCone S.f).X n₀` -/
  dsimp
  rw [← cancel_mono ((homologyFunctorFactors C (up Int) n₁).hom.app _)]; rw [assoc]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id_app]; rw [← cancel_epi ((homologyFunctorFactors C (up Int) n₀).inv.app _)]; rw [Iso.inv_hom_id_app_assoc]
  apply yoneda.map_injective
  ext ⟨A⟩ (x : A ⟶ _)
  obtain ⟨A', π, _, x', w, hx'⟩ :=
    (mappingCone S.f).eq_liftCycles_homologyπ_up_to_refinements x n₁ (by simpa using h)
  erw [homologySequenceδ_quotient_mapTriangle_obj_assoc _ _ _ h]
  dsimp
  -- simp? says
  simp only [Iso.inv_hom_id_app, HomologicalComplex.homologyFunctor_obj, Iso.inv_hom_id_app_assoc,
    comp_id]
  erw [comp_id]
  rw [← cancel_epi π]; rw [reassoc_of% hx']; rw [reassoc_of% hx']; rw [HomologicalComplex.homologyπ_naturality_assoc]; rw [HomologicalComplex.liftCycles_comp_cyclesMap_assoc]
  /- We decompose the cocycle `x'` into two morphisms `a : A' ⟶ S.X₁.X n₁`
     and `b : A' ⟶ S.X₂.X n₀` satisfying certain relations. -/
  obtain ⟨a, b, hab⟩ := decomp_to _ x' n₁ h
  rw [hab]; rw [ext_to_iff _ n₁ (n₁ + 1) rfl]; rw [add_comp]; rw [assoc]; rw [assoc]; rw [inr_f_d]; rw [add_comp]; rw [assoc]; rw [assoc]; rw [assoc]; rw [assoc]; rw [inr_f_fst_v]; rw [comp_zero]; rw [comp_zero]; rw [add_zero]; rw [zero_comp]; rw [d_fst_v _ _ _ _ h]; rw [comp_neg]; rw [inl_v_fst_v_assoc]; rw [comp_neg]; rw [neg_eq_zero]; rw [add_comp]; rw [assoc]; rw [assoc]; rw [assoc]; rw [assoc]; rw [inr_f_snd_v]; rw [comp_id]; rw [zero_comp]; rw [d_snd_v _ _ _ h]; rw [comp_add]; rw [inl_v_fst_v_assoc]; rw [inl_v_snd_v_assoc]; rw [zero_comp]; rw [add_zero] at w
  /- We simplify the RHS. -/
  conv_rhs => simp only [hab, add_comp, assoc, inr_f_descShortComplex_f,
    inl_v_descShortComplex_f, comp_zero, zero_add]
  rw [hS.δ_eq n₀ n₁ (by simpa using h) (b ≫ S.g.f n₀) _ b rfl (-a)
    (by simp only [neg_comp]; rw [neg_eq_iff_add_eq_zero]; rw [w.2]) (n₁ + 1) (by simp)]
  /- We simplify the LHS. -/
  dsimp [Functor.shiftMap, homologyFunctor_shift]
  rw [HomologicalComplex.homologyπ_naturality_assoc]; rw [HomologicalComplex.liftCycles_comp_cyclesMap_assoc]; rw [S.X₁.liftCycles_shift_homologyπ_assoc _ _ _ _ n₁ (by lia) (n₁ + 1) (by simp)]; rw [Iso.inv_hom_id_app]
  dsimp [homologyFunctor_shift]
  simp only [hab, add_comp, assoc, inl_v_triangle_mor₃_f_assoc,
    shiftFunctorObjXIso, neg_comp, Iso.inv_hom_id, comp_neg, comp_id,
    inr_f_triangle_mor₃_f_assoc, zero_comp, comp_zero, add_zero]

open ComposableArrows

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include hS in
/--
lemma `quasiIso_descShortComplex` / 引理 `quasiIso_descShortComplex`

English:
lemma quasiIso_descShortComplex
  statement: QuasiIso (descShortComplex S) where
  proof: by
    rw [quasiIsoAt_iff_isIso_homologyMap]
    let φ : ((homologyFunctor C (up Int) 0).homologySequenceComposableArrows₅
        (triangleh S.f) n _ rfl).δlast ⟶ (composableArrows₅ hS n _ rfl).δlast :=
      homMk₄ ((homologyFunctorFactors C (up Int) _).hom.app _)
        ((homologyFunctorFactors 

中文:
引理 quasiIso_descShortComplex
  结论: QuasiIso (descShortComplex S) where
  证明: by
    rw [quasiIsoAt_iff_isIso_homologyMap]
    let φ : ((homologyFunctor C (up Int) 0).homologySequenceComposableArrows₅
        (triangleh S.f) n _ rfl).δlast ⟶ (composableArrows₅ hS n _ rfl).δlast :=
      homMk₄ ((homologyFunctorFactors C (up Int) _).hom.app _)
        ((homologyFunctorFactors 

Depends on / 依赖: HomologicalComplex, HomologicalComplex.homologyMap, descShortComplex, hom.app, homologyFunctor, homologyFunctorFactors, homologyMap, quasiIsoAt_iff_isIso_homologyMap, triangleh
-/
lemma quasiIso_descShortComplex : QuasiIso (descShortComplex S) where
  quasiIsoAt n := by
    rw [quasiIsoAt_iff_isIso_homologyMap]
    let φ : ((homologyFunctor C (up Int) 0).homologySequenceComposableArrows₅
        (triangleh S.f) n _ rfl).δlast ⟶ (composableArrows₅ hS n _ rfl).δlast :=
      homMk₄ ((homologyFunctorFactors C (up Int) _).hom.app _)
        ((homologyFunctorFactors C (up Int) _).hom.app _)
        ((homologyFunctorFactors C (up Int) _).hom.app _ ≫
          HomologicalComplex.homologyMap (descShortComplex S) n)
        ((homologyFunctorFactors C (up Int) _).hom.app _)
        ((homologyFunctorFactors C (up Int) _).hom.app _)
        ((homologyFunctorFactors C (up Int) _).hom.naturality S.f)
        (by
          erw [(homologyFunctorFactors C (up Int) n).hom.naturality_assoc]
          -- Disable `Fin.reduceFinMk`, otherwise `Precomp.obj_succ` does not fire. (https://github.com/leanprover-community/mathlib4/issues/27382)
          dsimp [-Fin.reduceFinMk]
          rw [← HomologicalComplex.homologyMap_comp]; rw [inr_descShortComplex])
        (by
          -- Disable `Fin.reduceFinMk`, otherwise `Precomp.obj_succ` does not fire. (https://github.com/leanprover-community/mathlib4/issues/27382)
          dsimp [-Fin.reduceFinMk]
          erw [homologySequenceδ_triangleh hS]
          simp only [Functor.comp_obj, HomologicalComplex.homologyFunctor_obj, assoc,
            Iso.inv_hom_id_app, comp_id])
        ((homologyFunctorFactors C (up Int) _).hom.naturality S.f)
    have : IsIso ((homologyFunctorFactors C (up Int) n).hom.app (mappingCone S.f) ≫
        HomologicalComplex.homologyMap (descShortComplex S) n) := by
      apply Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono
        ((homologyFunctor C (up Int) 0).homologySequenceComposableArrows₅_exact _
          (mappingCone_triangleh_distinguished S.f) n _ rfl).δlast
        (composableArrows₅_exact hS n _ rfl).δlast φ
      all_goals dsimp [φ]; infer_instance
    apply IsIso.of_isIso_comp_left ((homologyFunctorFactors C (up Int) n).hom.app (mappingCone S.f))

@[reassoc]
/--
lemma `descShortComplex_naturality` / 引理 `descShortComplex_naturality`

English:
lemma descShortComplex_naturality
  given: {S₁ S₂ : ShortComplex (CochainComplex C Int)} (f : S₁ ⟶ S₂)
  proof: by
  ext n
  apply ext_from _ (n + 1) n rfl
  · simp [map]
  · simp [map, ← HomologicalComplex.comp_f, f.comm₂₃]

中文:
引理 descShortComplex_naturality
  条件: {S₁ S₂ : ShortComplex (CochainComplex C 整数)} (f : S₁ ⟶ S₂)
  证明: by
  ext n
  apply ext_from _ (n + 1) n rfl
  · simp [map]
  · simp [map, ← HomologicalComplex.comp_f, f.comm₂₃]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.comp_f, comp_f, ext_from, f.comm
-/
lemma descShortComplex_naturality {S₁ S₂ : ShortComplex (CochainComplex C Int)} (f : S₁ ⟶ S₂) :
    map S₁.f S₂.f f.τ₁ f.τ₂ f.comm₁₂.symm ≫ descShortComplex S₂ = descShortComplex S₁ ≫ f.τ₃ := by
  ext n
  apply ext_from _ (n + 1) n rfl
  · simp [map]
  · simp [map, ← HomologicalComplex.comp_f, f.comm₂₃]

variable {D : Type*} [Category* D] [Abelian D]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `mapHomologicalComplexIso_hom_descShortComplex` / 引理 `mapHomologicalComplexIso_hom_descShortComplex`

English:
lemma mapHomologicalComplexIso_hom_descShortComplex
  statement: (F : C ⥤ D) [F.Additive]
  proof: by
  symm
  ext n
  simp [mapHomologicalComplexIso, descShortComplex, mapHomologicalComplexXIso,
    mapHomologicalComplexXIso'_hom, Functor.mapHomologicalComplex_map_f,
    desc_f _ _ _ _ n (n + 1) rfl]

中文:
引理 mapHomologicalComplexIso_hom_descShortComplex
  结论: (F : C ⥤ D) [F.Additive]
  证明: by
  symm
  ext n
  simp [mapHomologicalComplexIso, descShortComplex, mapHomologicalComplexXIso,
    mapHomologicalComplexXIso'_hom, Functor.mapHomologicalComplex_map_f,
    desc_f _ _ _ _ n (n + 1) rfl]

Depends on / 依赖: Functor, Functor.mapHomologicalComplex_map_f, _hom, descShortComplex, desc_f, mapHomologicalComplexIso, mapHomologicalComplexXIso, mapHomologicalComplex_map_f
-/
lemma mapHomologicalComplexIso_hom_descShortComplex (F : C ⥤ D) [F.Additive]
    (S : ShortComplex (CochainComplex C Int)) :
    (mapHomologicalComplexIso _ _).hom ≫
      descShortComplex (S.map (F.mapHomologicalComplex (.up Int))) =
    (F.mapHomologicalComplex (.up Int)).map (descShortComplex S) := by
  symm
  ext n
  simp [mapHomologicalComplexIso, descShortComplex, mapHomologicalComplexXIso,
    mapHomologicalComplexXIso'_hom, Functor.mapHomologicalComplex_map_f,
    desc_f _ _ _ _ n (n + 1) rfl]

end mappingCone

end CochainComplex
