/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Sites.Coherent.ExtensiveTopology
public import Mathlib.CategoryTheory.Sites.Coherent.SheafComparison
public import Mathlib.CategoryTheory.Sites.LocallySurjective
/-!

# Locally surjective morphisms of coherent sheaves

This file characterises locally surjective morphisms of presheaves for the coherent, regular
and extensive topologies.

## Main results

* `regularTopology.isLocallySurjective_iff` A morphism of presheaves `f : F ⟶ G` is locally
  surjective for the regular topology iff for every object `X` of `C`, and every `y : G(X)`, there
  is an effective epimorphism `φ : X' ⟶ X` and an `x : F(X)` such that `f_{X'}(x) = G(φ)(y)`.

* `coherentTopology.isLocallySurjective_iff` a morphism of sheaves for the coherent topology on a
  preregular finitary extensive category is locally surjective if and only if it is
  locally surjective for the regular topology.

* `extensiveTopology.isLocallySurjective_iff` a morphism of sheaves for the extensive topology on a
  finitary extensive category is locally surjective iff it is objectwise surjective.
-/

public section

universe w

open CategoryTheory Sheaf Limits Opposite

namespace CategoryTheory

variable {C : Type*} (D : Type*) [Category* C] [Category* D] {FD : D -> D -> Type*} {CD : D -> Type w}
  [forall X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory.{w} D FD]

/--
lemma `regularTopology.isLocallySurjective_iff` / 引理 `regularTopology.isLocallySurjective_iff`

English:
lemma regularTopology.isLocallySurjective_iff
  given: [Preregular C] {F G : Cᵒᵖ ⥤ D} (f : F ⟶ G)
  proof: by
  constructor
  · intro ⟨h⟩ X y
    specialize h y
    rw [regularTopology.mem_sieves_iff_hasEffectiveEpi] at h
    obtain ⟨X', π, h, h'⟩ := h
    exact ⟨X', π, h, h'⟩
  · intro h
    refine ⟨fun y => ?_⟩
    obtain ⟨X', π, h, h'⟩ := h _ y
    rw [regularTopology.mem_sieves_iff_hasEffectiveEpi]
 

中文:
引理 regularTopology.isLocallySurjective_iff
  条件: [Preregular C] {F G : Cᵒᵖ ⥤ D} (f : F ⟶ G)
  证明: by
  constructor
  · intro ⟨h⟩ X y
    specialize h y
    rw [regularTopology.mem_sieves_iff_hasEffectiveEpi] at h
    obtain ⟨X', π, h, h'⟩ := h
    exact ⟨X', π, h, h'⟩
  · intro h
    refine ⟨fun y => ?_⟩
    obtain ⟨X', π, h, h'⟩ := h _ y
    rw [regularTopology.mem_sieves_iff_hasEffectiveEpi]
 

Depends on / 依赖: mem_sieves_iff_hasEffectiveEpi, regularTopology, regularTopology.mem_sieves_iff_hasEffectiveEpi, specialize
-/
lemma regularTopology.isLocallySurjective_iff [Preregular C] {F G : Cᵒᵖ ⥤ D} (f : F ⟶ G) :
    Presheaf.IsLocallySurjective (regularTopology C) f ↔
      forall (X : C) (y : ToType (G.obj ⟨X⟩)), (exists (X' : C) (φ : X' ⟶ X) (_ : EffectiveEpi φ)
        (x : ToType (F.obj ⟨X'⟩)),
        f.app ⟨X'⟩ x = G.map ⟨φ⟩ y) := by
  constructor
  · intro ⟨h⟩ X y
    specialize h y
    rw [regularTopology.mem_sieves_iff_hasEffectiveEpi] at h
    obtain ⟨X', π, h, h'⟩ := h
    exact ⟨X', π, h, h'⟩
  · intro h
    refine ⟨fun y => ?_⟩
    obtain ⟨X', π, h, h'⟩ := h _ y
    rw [regularTopology.mem_sieves_iff_hasEffectiveEpi]
    exact ⟨X', π, h, h'⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `extensiveTopology.surjective_of_isLocallySurjective_sheaf_of_types` / 引理 `extensiveTopology.surjective_of_isLocallySurjective_sheaf_of_types`

English:
lemma extensiveTopology.surjective_of_isLocallySurjective_sheaf_of_types
  statement: [FinitaryPreExtensive C]
  proof: by
  intro x
  replace h := h.1 x
  rw [mem_sieves_iff_contains_colimit_cofan] at h
  obtain ⟨α, _, Y, π, h, h'⟩ := h
  let y : (a : α) -> (F.obj ⟨Y a⟩) := fun a => (h' a).choose
  let ht := (Types.productLimitCone (fun a => F.obj ⟨Y a⟩)).isLimit
  let ht' := (Functor.Initial.isLimitWhiskerEquiv (Di

中文:
引理 extensiveTopology.surjective_of_isLocallySurjective_sheaf_of_types
  结论: [FinitaryPreExtensive C]
  证明: by
  intro x
  replace h := h.1 x
  rw [mem_sieves_iff_contains_colimit_cofan] at h
  obtain ⟨α, _, Y, π, h, h'⟩ := h
  let y : (a : α) -> (F.obj ⟨Y a⟩) := fun a => (h' a).choose
  let ht := (Types.productLimitCone (fun a => F.obj ⟨Y a⟩)).isLimit
  let ht' := (Functor.Initial.isLimitWhiskerEquiv (Di

Depends on / 依赖: Cocone, Cocone.op, Cofan.mk, Discrete, Discrete.natIso, Discrete.opposite, F.obj, Functor, Functor.Initial.isLimitWhiskerEquiv, Initial, Iso.refl, Types.productLimitCone, conePointsIsoOfNatIso, h.some.op, ht.conePointsIsoOfNatIso, inverse, isLimit, isLimitOfPreserves, isLimitWhiskerEquiv, mem_sieves_iff_contains_colimit_cofan
-/
lemma extensiveTopology.surjective_of_isLocallySurjective_sheaf_of_types [FinitaryPreExtensive C]
    {F G : Cᵒᵖ ⥤ Type w} (f : F ⟶ G) [PreservesFiniteProducts F] [PreservesFiniteProducts G]
      (h : Presheaf.IsLocallySurjective (extensiveTopology C) f) {X : C} :
        Function.Surjective (f.app (op X)) := by
  intro x
  replace h := h.1 x
  rw [mem_sieves_iff_contains_colimit_cofan] at h
  obtain ⟨α, _, Y, π, h, h'⟩ := h
  let y : (a : α) -> (F.obj ⟨Y a⟩) := fun a => (h' a).choose
  let ht := (Types.productLimitCone (fun a => F.obj ⟨Y a⟩)).isLimit
  let ht' := (Functor.Initial.isLimitWhiskerEquiv (Discrete.opposite α).inverse
    (Cocone.op (Cofan.mk X π))).symm h.some.op
  let i : ((a : α) -> (F.obj ⟨Y a⟩)) ≅ (F.obj ⟨X⟩) :=
    ht.conePointsIsoOfNatIso (isLimitOfPreserves F ht')
      (Discrete.natIso (fun _ => (Iso.refl (F.obj ⟨_⟩))))
  refine ⟨i.hom y, ?_⟩
  apply Concrete.isLimit_ext _ (isLimitOfPreserves G ht')
  intro ⟨a⟩
  simp only [Functor.comp_obj, Discrete.opposite_inverse_obj, Functor.op_obj, Discrete.functor_obj,
    Functor.mapCone_pt, Cone.whisker_pt, Cocone.op_pt, Cofan.mk_pt, Functor.const_obj_obj,
    Functor.mapCone_π_app, Cone.whisker_π, Cocone.op_π, Functor.whiskerLeft_app, NatTrans.op_app,
    Cofan.mk_ι_app]
  rw [← (h' a).choose_spec]; rw [← NatTrans.naturality_apply (φ := f)]
  simp only [IsLimit.conePointsIsoOfNatIso_hom, ← comp_apply, i]
  erw [IsLimit.map_π]
  rfl

/--
lemma `extensiveTopology.presheafIsLocallySurjective_iff` / 引理 `extensiveTopology.presheafIsLocallySurjective_iff`

English:
lemma extensiveTopology.presheafIsLocallySurjective_iff
  statement: [FinitaryPreExtensive C] {F G : Cᵒᵖ ⥤ D}
  proof: by
  constructor
  · rw [Presheaf.isLocallySurjective_iff_whisker_forget (J := extensiveTopology C)]
    exact fun h _ =>
      surjective_of_isLocallySurjective_sheaf_of_types (Functor.whiskerRight f (forget D)) h
  · exact fun a =>
      Presheaf.isLocallySurjective_of_surjective _ _ (fun _ => a _

中文:
引理 extensiveTopology.presheafIsLocallySurjective_iff
  结论: [FinitaryPreExtensive C] {F G : Cᵒᵖ ⥤ D}
  证明: by
  constructor
  · rw [Presheaf.isLocallySurjective_iff_whisker_forget (J := extensiveTopology C)]
    exact fun h _ =>
      surjective_of_isLocallySurjective_sheaf_of_types (Functor.whiskerRight f (forget D)) h
  · exact fun a =>
      Presheaf.isLocallySurjective_of_surjective _ _ (fun _ => a _

Depends on / 依赖: Functor, Functor.whiskerRight, Presheaf, Presheaf.isLocallySurjective_iff_whisker_forget, Presheaf.isLocallySurjective_of_surjective, extensiveTopology, forget, isLocallySurjective_iff_whisker_forget, isLocallySurjective_of_surjective, surjective_of_isLocallySurjective_sheaf_of_types, whiskerRight
-/
lemma extensiveTopology.presheafIsLocallySurjective_iff [FinitaryPreExtensive C] {F G : Cᵒᵖ ⥤ D}
    (f : F ⟶ G) [PreservesFiniteProducts F] [PreservesFiniteProducts G]
      [PreservesFiniteProducts (forget D)] : Presheaf.IsLocallySurjective (extensiveTopology C) f ↔
        forall (X : C), Function.Surjective (f.app (op X)) := by
  constructor
  · rw [Presheaf.isLocallySurjective_iff_whisker_forget (J := extensiveTopology C)]
    exact fun h _ =>
      surjective_of_isLocallySurjective_sheaf_of_types (Functor.whiskerRight f (forget D)) h
  · exact fun a =>
      Presheaf.isLocallySurjective_of_surjective _ _ (fun _ => a _)

/--
lemma `extensiveTopology.isLocallySurjective_iff` / 引理 `extensiveTopology.isLocallySurjective_iff`

English:
lemma extensiveTopology.isLocallySurjective_iff
  statement: [FinitaryExtensive C]
  proof: extensiveTopology.presheafIsLocallySurjective_iff _ f.hom

中文:
引理 extensiveTopology.isLocallySurjective_iff
  结论: [FinitaryExtensive C]
  证明: extensiveTopology.presheafIsLocallySurjective_iff _ f.hom

Depends on / 依赖: extensiveTopology, extensiveTopology.presheafIsLocallySurjective_iff, f.hom, presheafIsLocallySurjective_iff
-/
lemma extensiveTopology.isLocallySurjective_iff [FinitaryExtensive C]
    {F G : Sheaf (extensiveTopology C) D} (f : F ⟶ G)
      [PreservesFiniteProducts (forget D)] : IsLocallySurjective f ↔
        forall (X : C), Function.Surjective (f.hom.app (op X)) :=
  extensiveTopology.presheafIsLocallySurjective_iff _ f.hom

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `regularTopology.isLocallySurjective_sheaf_of_types` / 引理 `regularTopology.isLocallySurjective_sheaf_of_types`

English:
lemma regularTopology.isLocallySurjective_sheaf_of_types
  statement: [Preregular C] [FinitaryPreExtensive C]
  proof: by
    replace h := h.1 y
    rw [coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily] at h
    obtain ⟨α, _, Z, π, h, h'⟩ := h
    rw [mem_sieves_iff_hasEffectiveEpi]
    let x : (a : α) -> (F.obj ⟨Z a⟩) := fun a => (h' a).choose
    let i' : ((a : α) -> (F.obj ⟨Z a⟩)) ≅ (F.obj ⟨∐ Z⟩) := (Types.p

中文:
引理 regularTopology.isLocallySurjective_sheaf_of_types
  结论: [Preregular C] [FinitaryPreExtensive C]
  证明: by
    replace h := h.1 y
    rw [coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily] at h
    obtain ⟨α, _, Z, π, h, h'⟩ := h
    rw [mem_sieves_iff_hasEffectiveEpi]
    let x : (a : α) -> (F.obj ⟨Z a⟩) := fun a => (h' a).choose
    let i' : ((a : α) -> (F.obj ⟨Z a⟩)) ≅ (F.obj ⟨∐ Z⟩) := (Types.p

Depends on / 依赖: Discrete, Discrete.opposite, F.mapIso, F.obj, PreservesProduct, PreservesProduct.iso, Sigma.desc, Types.productIso, coherentTopology, coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily, mapIso, mem_sieves_iff_hasEffectiveEpi, mem_sieves_iff_hasEffectiveEpiFamily, opCoproductIsoProduct, opposite, preservesLimitsOfShape_of_equiv, productIso, replace
-/
lemma regularTopology.isLocallySurjective_sheaf_of_types [Preregular C] [FinitaryPreExtensive C]
    {F G : Cᵒᵖ ⥤ Type w} (f : F ⟶ G) [PreservesFiniteProducts F] [PreservesFiniteProducts G]
      (h : Presheaf.IsLocallySurjective (coherentTopology C) f) :
        Presheaf.IsLocallySurjective (regularTopology C) f where
  imageSieve_mem y := by
    replace h := h.1 y
    rw [coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily] at h
    obtain ⟨α, _, Z, π, h, h'⟩ := h
    rw [mem_sieves_iff_hasEffectiveEpi]
    let x : (a : α) -> (F.obj ⟨Z a⟩) := fun a => (h' a).choose
    let i' : ((a : α) -> (F.obj ⟨Z a⟩)) ≅ (F.obj ⟨∐ Z⟩) := (Types.productIso _).symm ≪≫
      (PreservesProduct.iso F _).symm ≪≫ F.mapIso (opCoproductIsoProduct _).symm
    refine ⟨∐ Z, Sigma.desc π, inferInstance, i'.hom x, ?_⟩
    have := preservesLimitsOfShape_of_equiv (Discrete.opposite α).symm G
    apply Concrete.isLimit_ext _ (isLimitOfPreserves G (coproductIsCoproduct Z).op)
    intro ⟨⟨a⟩⟩
    simp only [Functor.comp_obj, Functor.op_obj, Discrete.functor_obj_eq_as, Functor.mapCone_pt,
      Cocone.op_pt, Cofan.mk_pt, Functor.const_obj_obj, Functor.mapCone_π_app, Cocone.op_π,
      NatTrans.op_app, Cofan.mk_ι_app, Functor.mapIso_symm, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_inv, comp_apply, ← f.naturality_apply (Sigma.ι Z a).op, i']
    have : f.app ⟨Z a⟩ (x a) = G.map (π a).op y := (h' a).choose_spec
    convert! this
    · rw [← Functor.map_comp_apply, opCoproductIsoProduct_inv_comp_ι, ← piComparison_comp_π]
      change ((PreservesProduct.iso F _).hom ≫ _) _ = _
      have := Types.productIso_hom_comp_eval (fun a => F.obj (op (Z a))) a
      rw [← Iso.eq_inv_comp] at this
      simp only [types_comp_apply, Iso.inv_hom_id_apply]
      simp [← comp_apply]
    · simp only [← Functor.map_comp_apply, ← op_comp, Sigma.ι_desc]

/--
lemma `coherentTopology.presheafIsLocallySurjective_iff` / 引理 `coherentTopology.presheafIsLocallySurjective_iff`

English:
lemma coherentTopology.presheafIsLocallySurjective_iff
  statement: {F G : Cᵒᵖ ⥤ D} (f : F ⟶ G)
  proof: by
  constructor
  · rw [Presheaf.isLocallySurjective_iff_whisker_forget,
      Presheaf.isLocallySurjective_iff_whisker_forget (J := regularTopology C)]
    exact regularTopology.isLocallySurjective_sheaf_of_types _
  · refine Presheaf.isLocallySurjective_of_le (J := regularTopology C) ?_ _
    rw 

中文:
引理 coherentTopology.presheafIsLocallySurjective_iff
  结论: {F G : Cᵒᵖ ⥤ D} (f : F ⟶ G)
  证明: by
  constructor
  · rw [Presheaf.isLocallySurjective_iff_whisker_forget,
      Presheaf.isLocallySurjective_iff_whisker_forget (J := regularTopology C)]
    exact regularTopology.isLocallySurjective_sheaf_of_types _
  · refine Presheaf.isLocallySurjective_of_le (J := regularTopology C) ?_ _
    rw 

Depends on / 依赖: Coverage, Coverage.gi, Presheaf, Presheaf.isLocallySurjective_iff_whisker_forget, Presheaf.isLocallySurjective_of_le, extensive_regular_generate_coherent, gc.monotone_l, isLocallySurjective_iff_whisker_forget, isLocallySurjective_of_le, isLocallySurjective_sheaf_of_types, le_sup_right, monotone_l, regularTopology, regularTopology.isLocallySurjective_sheaf_of_types
-/
lemma coherentTopology.presheafIsLocallySurjective_iff {F G : Cᵒᵖ ⥤ D} (f : F ⟶ G)
    [Preregular C] [FinitaryPreExtensive C] [PreservesFiniteProducts F] [PreservesFiniteProducts G]
      [PreservesFiniteProducts (forget D)] :
        Presheaf.IsLocallySurjective (coherentTopology C) f ↔
          Presheaf.IsLocallySurjective (regularTopology C) f := by
  constructor
  · rw [Presheaf.isLocallySurjective_iff_whisker_forget,
      Presheaf.isLocallySurjective_iff_whisker_forget (J := regularTopology C)]
    exact regularTopology.isLocallySurjective_sheaf_of_types _
  · refine Presheaf.isLocallySurjective_of_le (J := regularTopology C) ?_ _
    rw [← extensive_regular_generate_coherent]
    exact (Coverage.gi _).gc.monotone_l le_sup_right

/--
lemma `coherentTopology.isLocallySurjective_iff` / 引理 `coherentTopology.isLocallySurjective_iff`

English:
lemma coherentTopology.isLocallySurjective_iff
  statement: [Preregular C] [FinitaryExtensive C]
  proof: presheafIsLocallySurjective_iff _ f.hom

中文:
引理 coherentTopology.isLocallySurjective_iff
  结论: [Preregular C] [FinitaryExtensive C]
  证明: presheafIsLocallySurjective_iff _ f.hom

Depends on / 依赖: f.hom, presheafIsLocallySurjective_iff
-/
lemma coherentTopology.isLocallySurjective_iff [Preregular C] [FinitaryExtensive C]
    {F G : Sheaf (coherentTopology C) D} (f : F ⟶ G) [PreservesFiniteProducts (forget D)] :
      IsLocallySurjective f ↔ Presheaf.IsLocallySurjective (regularTopology C) f.hom :=
  presheafIsLocallySurjective_iff _ f.hom

end CategoryTheory
