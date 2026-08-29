/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Sites.PreservesSheafification

/-!

In this file, we show that an adjunction `G ⊣ F` induces an adjunction between
categories of sheaves. We also show that `G` preserves sheafification.

-/

@[expose] public section


namespace CategoryTheory

open GrothendieckTopology Limits Opposite CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
variable {D : Type u₂} [Category.{v₂} D]
variable {E : Type*} [Category* E]
variable {F : D ⥤ E} {G : E ⥤ D}

/--
Definition of `sheafForget` / `sheafForget` 的定义

English:
abbreviation sheafForget
  signature: {FD : D -> D -> Type*} {CD : D -> Type*}
  body: sheafCompose J (forget D)

中文:
缩写 sheafForget
  签名: {FD : D -> D -> 类型} {CD : D -> 类型}
  定义体: sheafCompose J (forget D)

Depends on / 依赖: forget, sheafCompose
-/
abbrev sheafForget {FD : D -> D -> Type*} {CD : D -> Type*}
    [forall X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory D FD]
    [HasSheafCompose J (forget D)] : Sheaf J D ⥤ Sheaf J (Type _) :=
  sheafCompose J (forget D)

namespace Sheaf

noncomputable section

/--
Definition of `adjunction` / `adjunction` 的定义

English:
definition adjunction
  signature: [HasWeakSheafify J D] [HasSheafCompose J F] (adj : G ⊣ F)
  body: Adjunction.restrictFullyFaithful ((adj.whiskerRight Cᵒᵖ).comp (sheafificationAdjunction J D))
    (fullyFaithfulSheafToPresheaf J E) (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

中文:
定义 adjunction
  签名: [HasWeakSheafify J D] [有SheafCompose J F] (adj : G ⊣ F)
  定义体: Adjunction.restrictFullyFaithful ((adj.whiskerRight Cᵒᵖ).comp (sheafificationAdjunction J D))
    (fullyFaithfulSheafToPresheaf J E) (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

Depends on / 依赖: Adjunction, Adjunction.restrictFullyFaithful, FullyFaithful, Functor, Functor.FullyFaithful.id, Iso.refl, adj.whiskerRight, fullyFaithfulSheafToPresheaf, restrictFullyFaithful, sheafificationAdjunction, whiskerRight
-/
def adjunction [HasWeakSheafify J D] [HasSheafCompose J F] (adj : G ⊣ F) :
    composeAndSheafify J G ⊣ sheafCompose J F :=
  Adjunction.restrictFullyFaithful ((adj.whiskerRight Cᵒᵖ).comp (sheafificationAdjunction J D))
    (fullyFaithfulSheafToPresheaf J E) (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `adjunction_unit_app_hom` / 引理 `adjunction_unit_app_hom`

English:
lemma adjunction_unit_app_hom
  statement: [HasWeakSheafify J D] [HasSheafCompose J F] (adj : G ⊣ F)
  proof: by
  change (sheafToPresheaf _ _).map ((adjunction J adj).unit.app X) = _
  simp only [Functor.id_obj, Functor.comp_obj, whiskeringRight_obj_obj, adjunction,
    Adjunction.map_restrictFullyFaithful_unit_app, Adjunction.comp_unit_app,
    sheafificationAdjunction_unit_app, whiskeringRight_obj_map, Iso.refl_hom, NatTrans.id_app,
    Functor.comp_map, Functor.map_id, whiskerRight_id', Category.comp_id]
  rfl

@[deprecated (since := "2026-03-05")]
alias adjunction_unit_app_val := adjunction_unit_app_hom

中文:
引理 adjunction_unit_app_hom
  结论: [HasWeakSheafify J D] [有SheafCompose J F] (adj : G ⊣ F)
  证明: by
  change (sheafToPresheaf _ _).map ((adjunction J adj).unit.app X) = _
  simp only [Functor.id_obj, Functor.comp_obj, whiskeringRight_obj_obj, adjunction,
    Adjunction.map_restrictFullyFaithful_unit_app, Adjunction.comp_unit_app,
    sheafificationAdjunction_unit_app, whiskeringRight_obj_map, Iso.refl_hom, NatTrans.id_app,
    Functor.comp_map, Functor.map_id, whiskerRight_id', Category.comp_id]
  rfl

@[deprecated (since := "2026-03-05")]
alias adjunction_unit_app_val := adjunction_unit_app_hom

Depends on / 依赖: Adjunction, Adjunction.comp_unit_app, Adjunction.map_restrictFullyFaithful_unit_app, Category, Category.comp_id, Functor, Functor.comp_map, Functor.comp_obj, Functor.id_obj, Functor.map_id, Iso.refl_hom, NatTrans, NatTrans.id_app, adjunction, comp_id, comp_map, comp_obj, comp_unit_app, id_app, id_obj
-/
lemma adjunction_unit_app_hom [HasWeakSheafify J D] [HasSheafCompose J F] (adj : G ⊣ F)
    (X : Sheaf J E) : ((adjunction J adj).unit.app X).hom =
      (adj.whiskerRight Cᵒᵖ).unit.app _ ≫ whiskerRight (toSheafify J (X.obj ⋙ G)) F := by
  change (sheafToPresheaf _ _).map ((adjunction J adj).unit.app X) = _
  simp only [Functor.id_obj, Functor.comp_obj, whiskeringRight_obj_obj, adjunction,
    Adjunction.map_restrictFullyFaithful_unit_app, Adjunction.comp_unit_app,
    sheafificationAdjunction_unit_app, whiskeringRight_obj_map, Iso.refl_hom, NatTrans.id_app,
    Functor.comp_map, Functor.map_id, whiskerRight_id', Category.comp_id]
  rfl

@[deprecated (since := "2026-03-05")]
alias adjunction_unit_app_val := adjunction_unit_app_hom

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `adjunction_counit_app_hom` / 引理 `adjunction_counit_app_hom`

English:
lemma adjunction_counit_app_hom
  statement: [HasWeakSheafify J D] [HasSheafCompose J F] (adj : G ⊣ F)
  proof: ((sheafToPresheaf _ _).congr_map
    (Adjunction.map_restrictFullyFaithful_counit_app _ _ (Functor.FullyFaithful.id _)
      (L := composeAndSheafify J G) (R := sheafCompose J F) _ _ Y)).trans (by cat_disch)

@[deprecated (since := "2026-03-05")]
alias adjunction_counit_app_val := adjunction_counit_app_hom

中文:
引理 adjunction_counit_app_hom
  结论: [HasWeakSheafify J D] [有SheafCompose J F] (adj : G ⊣ F)
  证明: ((sheafToPresheaf _ _).congr_map
    (Adjunction.map_restrictFullyFaithful_counit_app _ _ (Functor.FullyFaithful.id _)
      (L := composeAndSheafify J G) (R := sheafCompose J F) _ _ Y)).trans (by cat_disch)

@[deprecated (since := "2026-03-05")]
alias adjunction_counit_app_val := adjunction_counit_app_hom

Depends on / 依赖: Adjunction, Adjunction.map_restrictFullyFaithful_counit_app, FullyFaithful, Functor, Functor.FullyFaithful.id, cat_disch, composeAndSheafify, congr_map, map_restrictFullyFaithful_counit_app, sheafCompose, sheafToPresheaf
-/
lemma adjunction_counit_app_hom [HasWeakSheafify J D] [HasSheafCompose J F] (adj : G ⊣ F)
    (Y : Sheaf J D) : ((adjunction J adj).counit.app Y).hom =
      sheafifyLift J (((adj.whiskerRight Cᵒᵖ).counit.app Y.obj)) Y.property :=
  ((sheafToPresheaf _ _).congr_map
    (Adjunction.map_restrictFullyFaithful_counit_app _ _ (Functor.FullyFaithful.id _)
      (L := composeAndSheafify J G) (R := sheafCompose J F) _ _ Y)).trans (by cat_disch)

@[deprecated (since := "2026-03-05")]
alias adjunction_counit_app_val := adjunction_counit_app_hom

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasWeakSheafify
  signature: J D] [F.IsRightAdjoint] : (sheafCompose J F).IsRightAdjoint
  body: (adjunction J (Adjunction.ofIsRightAdjoint F)).isRightAdjoint

中文:
实例 [HasWeakSheafify
  签名: J D] [F.是右伴随] : (sheafCompose J F).是右伴随
  定义体: (adjunction J (Adjunction.ofIsRightAdjoint F)).isRightAdjoint

Depends on / 依赖: Adjunction, Adjunction.ofIsRightAdjoint, adjunction, isRightAdjoint, ofIsRightAdjoint
-/
instance [HasWeakSheafify J D] [F.IsRightAdjoint] : (sheafCompose J F).IsRightAdjoint :=
  (adjunction J (Adjunction.ofIsRightAdjoint F)).isRightAdjoint

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasWeakSheafify
  signature: J D] [G.IsLeftAdjoint] : (composeAndSheafify J G).IsLeftAdjoint
  body: (adjunction J (Adjunction.ofIsLeftAdjoint G)).isLeftAdjoint

中文:
实例 [HasWeakSheafify
  签名: J D] [G.是左伴随] : (composeAndSheafify J G).是左伴随
  定义体: (adjunction J (Adjunction.ofIsLeftAdjoint G)).isLeftAdjoint

Depends on / 依赖: Adjunction, Adjunction.ofIsLeftAdjoint, adjunction, isLeftAdjoint, ofIsLeftAdjoint
-/
instance [HasWeakSheafify J D] [G.IsLeftAdjoint] : (composeAndSheafify J G).IsLeftAdjoint :=
  (adjunction J (Adjunction.ofIsLeftAdjoint G)).isLeftAdjoint

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `preservesSheafification_of_adjunction` / 引理 `preservesSheafification_of_adjunction`

English:
lemma preservesSheafification_of_adjunction
  given: (adj : G ⊣ F)
  proof: by
    have := adj.isRightAdjoint
    rw [MorphismProperty.inverseImage_iff]
    dsimp
    intro R hR
    rw [← ((adj.whiskerRight Cᵒᵖ).homEquiv P R).comp_bijective]
    convert!
      (((adj.whiskerRight Cᵒᵖ).homEquiv Q R).trans
          (hf.homEquiv (R ⋙ F) ((sheafCompose J F).obj ⟨R, hR⟩).property)).bijective
    ext g X
    -- The rest of this proof was
    -- `dsimp [Adjunction.whiskerRight, Adjunction.mkOfUnitCounit]; simp` before https://github.com/leanprover-community/mathlib4/pull/16317.
    dsimp
    rw [← NatTrans.comp_app]
    congr
    exact Adjunction.homEquiv_naturality_left _ _ _

中文:
引理 preservesSheafification_of_adjunction
  条件: (adj : G ⊣ F)
  证明: by
    have := adj.isRightAdjoint
    rw [MorphismProperty.inverseImage_iff]
    dsimp
    intro R hR
    rw [← ((adj.whiskerRight Cᵒᵖ).homEquiv P R).comp_bijective]
    convert!
      (((adj.whiskerRight Cᵒᵖ).homEquiv Q R).trans
          (hf.homEquiv (R ⋙ F) ((sheafCompose J F).obj ⟨R, hR⟩).property)).bijective
    ext g X
    -- The rest of this proof was
    -- `dsimp [Adjunction.whiskerRight, Adjunction.mkOfUnitCounit]; simp` before https://github.com/leanprover-community/mathlib4/pull/16317.
    dsimp
    rw [← NatTrans.comp_app]
    congr
    exact Adjunction.homEquiv_naturality_left _ _ _

Depends on / 依赖: MorphismProperty, MorphismProperty.inverseImage_iff, adj.isRightAdjoint, adj.whiskerRight, bijective, comp_bijective, convert, hf.homEquiv, homEquiv, inverseImage_iff, isRightAdjoint, property, sheafCompose, whiskerRight
-/
lemma preservesSheafification_of_adjunction (adj : G ⊣ F) :
    J.PreservesSheafification G where
  le P Q f hf := by
    have := adj.isRightAdjoint
    rw [MorphismProperty.inverseImage_iff]
    dsimp
    intro R hR
    rw [← ((adj.whiskerRight Cᵒᵖ).homEquiv P R).comp_bijective]
    convert!
      (((adj.whiskerRight Cᵒᵖ).homEquiv Q R).trans
          (hf.homEquiv (R ⋙ F) ((sheafCompose J F).obj ⟨R, hR⟩).property)).bijective
    ext g X
    -- The rest of this proof was
    -- `dsimp [Adjunction.whiskerRight, Adjunction.mkOfUnitCounit]; simp` before https://github.com/leanprover-community/mathlib4/pull/16317.
    dsimp
    rw [← NatTrans.comp_app]
    congr
    exact Adjunction.homEquiv_naturality_left _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [G.IsLeftAdjoint]
  signature: : J.PreservesSheafification G
  body: preservesSheafification_of_adjunction J (Adjunction.ofIsLeftAdjoint G)

中文:
实例 [G.是左伴随]
  签名: : J.保持层化 G
  定义体: preservesSheafification_of_adjunction J (Adjunction.ofIsLeftAdjoint G)

Depends on / 依赖: Adjunction, Adjunction.ofIsLeftAdjoint, ofIsLeftAdjoint, preservesSheafification_of_adjunction
-/
instance [G.IsLeftAdjoint] : J.PreservesSheafification G :=
  preservesSheafification_of_adjunction J (Adjunction.ofIsLeftAdjoint G)

section ForgetToType

variable [HasWeakSheafify J D] {FD : D -> D -> Type*} {CD : D -> Type (max u₁ v₁)}
    [forall X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory D FD] [HasSheafCompose J (forget D)]

example [(forget D).IsRightAdjoint] :
    (sheafForget.{_, _, _, _, _, max u₁ v₁} (D := D) J).IsRightAdjoint := by infer_instance

end ForgetToType

end

end Sheaf

end CategoryTheory
