/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.CompatibleSheafification
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Sheafification

/-! # Functors which preserve sheafification

In this file, given a Grothendieck topology `J` on `C` and `F : A ⥤ B`,
we define a type class `J.PreservesSheafification F`. We say that `F` preserves
the sheafification if whenever a morphism of presheaves `P₁ ⟶ P₂` induces
an isomorphism on the associated sheaves, then the induced map `P₁ ⋙ F ⟶ P₂ ⋙ F`
also induces an isomorphism on the associated sheaves. (Note: it suffices to check
this property for the map from any presheaf `P` to its associated sheaf, see
`GrothendieckTopology.preservesSheafification_iff_of_adjunctions`).

In general, we define `Sheaf.composeAndSheafify J F : Sheaf J A ⥤ Sheaf J B` as the functor
which sends a sheaf `G` to the sheafification of the composition `G.val ⋙ F`.
If `J.PreservesSheafification F`, we show that this functor can also be thought of
as the localization of the functor `_ ⋙ F` on presheaves: we construct an isomorphism
`presheafToSheafCompComposeAndSheafifyIso` between
`presheafToSheaf J A ⋙ Sheaf.composeAndSheafify J F` and
`(whiskeringRight Cᵒᵖ A B).obj F ⋙ presheafToSheaf J B`.

Moreover, if we assume `J.HasSheafCompose F`, we obtain an isomorphism
`sheafifyComposeIso J F P : sheafify J (P ⋙ F) ≅ sheafify J P ⋙ F`.

We show that under suitable assumptions, the forgetful functor from a concrete
category preserves sheafification; this holds more generally for
functors between such concrete categories which commute both with
suitable limits and colimits.

## TODO
* construct an isomorphism `Sheaf.composeAndSheafify J F ≅ sheafCompose J F`

-/

@[expose] public section

universe v u

namespace CategoryTheory

open Category Limits CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A B : Type*} [Category* A] [Category* B] (F : A ⥤ B)

namespace GrothendieckTopology

/--
Definition of `PreservesSheafification` / `PreservesSheafification` 的定义

English:
class PreservesSheafification
  parameters: : Prop where
  axioms and operations (1):
    - le : J.W <= J.W.inverseImage ((whiskeringRight Cᵒᵖ A B).obj F)

中文:
类 保持层化
  参数: : 命题 where
  公理与运算 (1 个):
    - le : J.W <= J.W.inverseImage ((whiskeringRight Cᵒᵖ A B).obj F)
-/
class PreservesSheafification : Prop where
  le : J.W <= J.W.inverseImage ((whiskeringRight Cᵒᵖ A B).obj F)

variable [PreservesSheafification J F]

/--
lemma `W_of_preservesSheafification` / 引理 `W_of_preservesSheafification`

English:
lemma W_of_preservesSheafification
  proof: PreservesSheafification.le _ hf

中文:
引理 W_of_preservesSheafification
  证明: PreservesSheafification.le _ hf

Depends on / 依赖: PreservesSheafification, PreservesSheafification.le
-/
lemma W_of_preservesSheafification
    {P₁ P₂ : Cᵒᵖ ⥤ A} (f : P₁ ⟶ P₂) (hf : J.W f) :
    J.W (whiskerRight f F) :=
  PreservesSheafification.le _ hf

variable [HasWeakSheafify J B]

set_option backward.defeqAttrib.useBackward true in
/--
lemma `W_isInvertedBy_whiskeringRight_presheafToSheaf` / 引理 `W_isInvertedBy_whiskeringRight_presheafToSheaf`

English:
lemma W_isInvertedBy_whiskeringRight_presheafToSheaf
  proof: by
  intro P₁ P₂ f hf
  dsimp
  rw [← W_iff]
  exact J.W_of_preservesSheafification F _ hf

中文:
引理 W_isInvertedBy_whiskeringRight_presheafToSheaf
  证明: by
  intro P₁ P₂ f hf
  dsimp
  rw [← W_iff]
  exact J.W_of_preservesSheafification F _ hf

Depends on / 依赖: J.W_of_preservesSheafification, W_iff, W_of_preservesSheafification
-/
lemma W_isInvertedBy_whiskeringRight_presheafToSheaf :
    J.W.IsInvertedBy (((whiskeringRight Cᵒᵖ A B).obj F) ⋙ presheafToSheaf J B) := by
  intro P₁ P₂ f hf
  dsimp
  rw [← W_iff]
  exact J.W_of_preservesSheafification F _ hf

end GrothendieckTopology

section

variable [HasWeakSheafify J B]

/--
Definition of `Sheaf.composeAndSheafify` / `Sheaf.composeAndSheafify` 的定义

English:
abbreviation Sheaf.composeAndSheafify
  signature: : Sheaf J A ⥤ Sheaf J B
  body: sheafToPresheaf J A ⋙ (whiskeringRight _ _ _).obj F ⋙ presheafToSheaf J B

中文:
缩写 层.composeAndSheafify
  签名: : 层 J A ⥤ 层 J B
  定义体: sheafToPresheaf J A ⋙ (whiskeringRight _ _ _).obj F ⋙ presheafToSheaf J B

Depends on / 依赖: presheafToSheaf, sheafToPresheaf, whiskeringRight
-/
noncomputable abbrev Sheaf.composeAndSheafify : Sheaf J A ⥤ Sheaf J B :=
  sheafToPresheaf J A ⋙ (whiskeringRight _ _ _).obj F ⋙ presheafToSheaf J B

variable [HasWeakSheafify J A]

/-- The canonical natural transformation from
`(whiskeringRight Cᵒᵖ A B).obj F ⋙ presheafToSheaf J B` to
`presheafToSheaf J A ⋙ Sheaf.composeAndSheafify J F`. -/
@[simps!]
/--
Definition of `toPresheafToSheafCompComposeAndSheafify` / `toPresheafToSheafCompComposeAndSheafify` 的定义

English:
definition toPresheafToSheafCompComposeAndSheafify
  signature: :
  body: whiskerRight (sheafificationAdjunction J A).unit
    ((whiskeringRight _ _ _).obj F ⋙ presheafToSheaf J B)

中文:
定义 toPresheafToSheafCompComposeAndSheafify
  签名: :
  定义体: whiskerRight (sheafificationAdjunction J A).unit
    ((whiskeringRight _ _ _).obj F ⋙ presheafToSheaf J B)

Depends on / 依赖: presheafToSheaf, sheafificationAdjunction, whiskerRight, whiskeringRight
-/
noncomputable def toPresheafToSheafCompComposeAndSheafify :
    (whiskeringRight Cᵒᵖ A B).obj F ⋙ presheafToSheaf J B ⟶
      presheafToSheaf J A ⋙ Sheaf.composeAndSheafify J F :=
  whiskerRight (sheafificationAdjunction J A).unit
    ((whiskeringRight _ _ _).obj F ⋙ presheafToSheaf J B)

variable [J.PreservesSheafification F]

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIso (toPresheafToSheafCompComposeAndSheafify J F)
  body: by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  dsimp
  simpa only [← J.W_iff] using J.W_of_preservesSheafification F _ (J.W_toSheafify X)

中文:
实例 :
  签名: 是同构 (toPresheafToSheafCompComposeAndSheafify J F)
  定义体: by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  dsimp
  simpa only [← J.W_iff] using J.W_of_preservesSheafification F _ (J.W_toSheafify X)

Depends on / 依赖: J.W_iff, J.W_of_preservesSheafification, J.W_toSheafify, NatTrans, NatTrans.isIso_iff_isIso_app, W_iff, W_of_preservesSheafification, W_toSheafify, isIso_iff_isIso_app
-/
instance : IsIso (toPresheafToSheafCompComposeAndSheafify J F) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  dsimp
  simpa only [← J.W_iff] using J.W_of_preservesSheafification F _ (J.W_toSheafify X)

/-- The canonical isomorphism between `presheafToSheaf J A ⋙ Sheaf.composeAndSheafify J F`
and `(whiskeringRight Cᵒᵖ A B).obj F ⋙ presheafToSheaf J B` when `F : A ⥤ B`
preserves sheafification. -/
@[simps! inv_app]
/--
Definition of `presheafToSheafCompComposeAndSheafifyIso` / `presheafToSheafCompComposeAndSheafifyIso` 的定义

English:
definition presheafToSheafCompComposeAndSheafifyIso
  signature: :
  body: (asIso (toPresheafToSheafCompComposeAndSheafify J F)).symm

中文:
定义 presheafToSheafCompComposeAndSheafifyIso
  签名: :
  定义体: (asIso (toPresheafToSheafCompComposeAndSheafify J F)).symm

Depends on / 依赖: toPresheafToSheafCompComposeAndSheafify
-/
noncomputable def presheafToSheafCompComposeAndSheafifyIso :
    presheafToSheaf J A ⋙ Sheaf.composeAndSheafify J F ≅
      (whiskeringRight Cᵒᵖ A B).obj F ⋙ presheafToSheaf J B :=
  (asIso (toPresheafToSheafCompComposeAndSheafify J F)).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Localization.Lifting (presheafToSheaf J A) J.W
  body: ⟨presheafToSheafCompComposeAndSheafifyIso J F⟩

中文:
实例 :
  签名: Localization.提升 (presheafToSheaf J A) J.W
  定义体: ⟨presheafToSheafCompComposeAndSheafifyIso J F⟩

Depends on / 依赖: presheafToSheafCompComposeAndSheafifyIso
-/
noncomputable instance : Localization.Lifting (presheafToSheaf J A) J.W
    ((whiskeringRight Cᵒᵖ A B).obj F ⋙ presheafToSheaf J B) (Sheaf.composeAndSheafify J F) :=
  ⟨presheafToSheafCompComposeAndSheafifyIso J F⟩

end

section

variable {G₁ : (Cᵒᵖ ⥤ A) ⥤ Sheaf J A} (adj₁ : G₁ ⊣ sheafToPresheaf J A)
  {G₂ : (Cᵒᵖ ⥤ B) ⥤ Sheaf J B}

set_option backward.defeqAttrib.useBackward true in
/--
lemma `GrothendieckTopology.preservesSheafification_iff_of_adjunctions` / 引理 `GrothendieckTopology.preservesSheafification_iff_of_adjunctions`

English:
lemma GrothendieckTopology.preservesSheafification_iff_of_adjunctions
  proof: by
  simp only [← J.W_iff_isIso_map_of_adjunction adj₂]
  constructor
  · intro _ P
    apply W_of_preservesSheafification
    rw [J.W_iff_isIso_map_of_adjunction adj₁]
    infer_instance
  · intro h
    constructor
    intro P₁ P₂ f hf
    rw [J.W_iff_isIso_map_of_adjunction adj₁] at hf
    dsimp [MorphismProperty.inverseImage]
    rw [← (W _).postcomp_iff _ _ (h P₂)]; rw [← whiskerRight_comp]
    erw [adj₁.unit.naturality f]
    dsimp only [Functor.comp_map]
    rw [whiskerRight_comp]; rw [(W _).precomp_iff _ _ (h P₁)]
    apply ObjectProperty.isLocal_of_isIso

中文:
引理 Grothendieck拓扑.preservesSheafification_iff_of_adjunctions
  证明: by
  simp only [← J.W_iff_isIso_map_of_adjunction adj₂]
  constructor
  · intro _ P
    apply W_of_preservesSheafification
    rw [J.W_iff_isIso_map_of_adjunction adj₁]
    infer_instance
  · intro h
    constructor
    intro P₁ P₂ f hf
    rw [J.W_iff_isIso_map_of_adjunction adj₁] at hf
    dsimp [MorphismProperty.inverseImage]
    rw [← (W _).postcomp_iff _ _ (h P₂)]; rw [← whiskerRight_comp]
    erw [adj₁.unit.naturality f]
    dsimp only [Functor.comp_map]
    rw [whiskerRight_comp]; rw [(W _).precomp_iff _ _ (h P₁)]
    apply ObjectProperty.isLocal_of_isIso

Depends on / 依赖: Functor, Functor.comp_map, J.W_iff_isIso_map_of_adjunction, MorphismProperty, MorphismProperty.inverseImage, ObjectProperty, ObjectProperty.isLo, W_iff_isIso_map_of_adjunction, W_of_preservesSheafification, comp_map, infer_instance, inverseImage, naturality, postcomp_iff, precomp_iff, unit.naturality, whiskerRight_comp
-/
lemma GrothendieckTopology.preservesSheafification_iff_of_adjunctions
    (adj₂ : G₂ ⊣ sheafToPresheaf J B) :
    J.PreservesSheafification F ↔ forall (P : Cᵒᵖ ⥤ A),
      IsIso (G₂.map (whiskerRight (adj₁.unit.app P) F)) := by
  simp only [← J.W_iff_isIso_map_of_adjunction adj₂]
  constructor
  · intro _ P
    apply W_of_preservesSheafification
    rw [J.W_iff_isIso_map_of_adjunction adj₁]
    infer_instance
  · intro h
    constructor
    intro P₁ P₂ f hf
    rw [J.W_iff_isIso_map_of_adjunction adj₁] at hf
    dsimp [MorphismProperty.inverseImage]
    rw [← (W _).postcomp_iff _ _ (h P₂)]; rw [← whiskerRight_comp]
    erw [adj₁.unit.naturality f]
    dsimp only [Functor.comp_map]
    rw [whiskerRight_comp]; rw [(W _).precomp_iff _ _ (h P₁)]
    apply ObjectProperty.isLocal_of_isIso

section HasSheafCompose

variable (adj₂ : G₂ ⊣ sheafToPresheaf J B) [J.HasSheafCompose F]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `sheafComposeNatTrans` / `sheafComposeNatTrans` 的定义

English:
definition sheafComposeNatTrans
  signature: :
  body: (adj₂.homEquiv _ _).symm (whiskerRight (adj₁.unit.app P) F)
  naturality {P Q} f := by
    dsimp
    erw [← adj₂.homEquiv_naturality_left_symm,
      ← adj₂.homEquiv_naturality_right_symm]
    congr 1
    ext X
    have := NatTrans.congr_app (adj₁.unit.naturality f) X
    dsimp at this ⊢
    grind

中文:
定义 sheafCompose自然数Trans
  签名: :
  定义体: (adj₂.homEquiv _ _).symm (whiskerRight (adj₁.unit.app P) F)
  naturality {P Q} f := by
    dsimp
    erw [← adj₂.homEquiv_naturality_left_symm,
      ← adj₂.homEquiv_naturality_right_symm]
    congr 1
    ext X
    have := NatTrans.congr_app (adj₁.unit.naturality f) X
    dsimp at this ⊢
    grind

Depends on / 依赖: homEquiv, unit.app, whiskerRight
-/
def sheafComposeNatTrans :
    (whiskeringRight Cᵒᵖ A B).obj F ⋙ G₂ ⟶ G₁ ⋙ sheafCompose J F where
  app P := (adj₂.homEquiv _ _).symm (whiskerRight (adj₁.unit.app P) F)
  naturality {P Q} f := by
    dsimp
    erw [← adj₂.homEquiv_naturality_left_symm,
      ← adj₂.homEquiv_naturality_right_symm]
    congr 1
    ext X
    have := NatTrans.congr_app (adj₁.unit.naturality f) X
    dsimp at this ⊢
    grind

set_option backward.isDefEq.respectTransparency false in
/--
lemma `sheafComposeNatTrans_fac` / 引理 `sheafComposeNatTrans_fac`

English:
lemma sheafComposeNatTrans_fac
  given: (P : Cᵒᵖ ⥤ A)
  proof: by
  simp [sheafComposeNatTrans, -ObjectProperty.ι_obj, -ObjectProperty.ι_map,
    Adjunction.homEquiv_counit]

中文:
引理 sheafCompose自然数Trans_fac
  条件: (P : Cᵒᵖ ⥤ A)
  证明: by
  simp [sheafComposeNatTrans, -ObjectProperty.ι_obj, -ObjectProperty.ι_map,
    Adjunction.homEquiv_counit]

Depends on / 依赖: Adjunction, Adjunction.homEquiv_counit, ObjectProperty, homEquiv_counit, sheafComposeNatTrans
-/
lemma sheafComposeNatTrans_fac (P : Cᵒᵖ ⥤ A) :
    adj₂.unit.app (P ⋙ F) ≫
      (sheafToPresheaf J B).map ((sheafComposeNatTrans J F adj₁ adj₂).app P) =
        whiskerRight (adj₁.unit.app P) F := by
  simp [sheafComposeNatTrans, -ObjectProperty.ι_obj, -ObjectProperty.ι_map,
    Adjunction.homEquiv_counit]

/--
lemma `sheafComposeNatTrans_app_uniq` / 引理 `sheafComposeNatTrans_app_uniq`

English:
lemma sheafComposeNatTrans_app_uniq
  statement: (P : Cᵒᵖ ⥤ A)
  proof: by
  apply (adj₂.homEquiv _ _).injective
  dsimp [ObjectProperty.ι_obj, sheafComposeNatTrans, id_obj]
  erw [Equiv.apply_symm_apply]
  rw [← hα]
  apply adj₂.homEquiv_unit

中文:
引理 sheafCompose自然数Trans_app_uniq
  结论: (P : Cᵒᵖ ⥤ A)
  证明: by
  apply (adj₂.homEquiv _ _).injective
  dsimp [ObjectProperty.ι_obj, sheafComposeNatTrans, id_obj]
  erw [Equiv.apply_symm_apply]
  rw [← hα]
  apply adj₂.homEquiv_unit

Depends on / 依赖: Equiv.apply_symm_apply, ObjectProperty, apply_symm_apply, homEquiv, homEquiv_unit, id_obj, injective, sheafComposeNatTrans
-/
lemma sheafComposeNatTrans_app_uniq (P : Cᵒᵖ ⥤ A)
    (α : G₂.obj (P ⋙ F) ⟶ (sheafCompose J F).obj (G₁.obj P))
    (hα : adj₂.unit.app (P ⋙ F) ≫ (sheafToPresheaf J B).map α =
        whiskerRight (adj₁.unit.app P) F) :
    α = (sheafComposeNatTrans J F adj₁ adj₂).app P := by
  apply (adj₂.homEquiv _ _).injective
  dsimp [ObjectProperty.ι_obj, sheafComposeNatTrans, id_obj]
  erw [Equiv.apply_symm_apply]
  rw [← hα]
  apply adj₂.homEquiv_unit

set_option backward.isDefEq.respectTransparency false in
/--
lemma `GrothendieckTopology.preservesSheafification_iff_of_adjunctions_of_hasSheafCompose` / 引理 `GrothendieckTopology.preservesSheafification_iff_of_adjunctions_of_hasSheafCompose`

English:
lemma GrothendieckTopology.preservesSheafification_iff_of_adjunctions_of_hasSheafCompose
  proof: by
  rw [J.preservesSheafification_iff_of_adjunctions F adj₁ adj₂]; rw [NatTrans.isIso_iff_isIso_app]
  apply forall_congr'
  intro P
  rw [← J.W_iff_isIso_map_of_adjunction adj₂]; rw [← J.W_sheafToPresheaf_map_iff_isIso]; rw [← sheafComposeNatTrans_fac J F adj₁ adj₂]; rw [(W _).precomp_iff _ _ (J.W_adj_unit_app adj₂ (P ⋙ F))]

中文:
引理 Grothendieck拓扑.preservesSheafification_iff_of_adjunctions_of_hasSheafCompose
  证明: by
  rw [J.preservesSheafification_iff_of_adjunctions F adj₁ adj₂]; rw [NatTrans.isIso_iff_isIso_app]
  apply forall_congr'
  intro P
  rw [← J.W_iff_isIso_map_of_adjunction adj₂]; rw [← J.W_sheafToPresheaf_map_iff_isIso]; rw [← sheafComposeNatTrans_fac J F adj₁ adj₂]; rw [(W _).precomp_iff _ _ (J.W_adj_unit_app adj₂ (P ⋙ F))]

Depends on / 依赖: J.W_adj_unit_app, J.W_iff_isIso_map_of_adjunction, J.W_sheafToPresheaf_map_iff_isIso, J.preservesSheafification_iff_of_adjunctions, NatTrans, NatTrans.isIso_iff_isIso_app, W_adj_unit_app, W_iff_isIso_map_of_adjunction, W_sheafToPresheaf_map_iff_isIso, forall_congr, isIso_iff_isIso_app, precomp_iff, preservesSheafification_iff_of_adjunctions, sheafComposeNatTrans_fac
-/
lemma GrothendieckTopology.preservesSheafification_iff_of_adjunctions_of_hasSheafCompose :
    J.PreservesSheafification F ↔ IsIso (sheafComposeNatTrans J F adj₁ adj₂) := by
  rw [J.preservesSheafification_iff_of_adjunctions F adj₁ adj₂]; rw [NatTrans.isIso_iff_isIso_app]
  apply forall_congr'
  intro P
  rw [← J.W_iff_isIso_map_of_adjunction adj₂]; rw [← J.W_sheafToPresheaf_map_iff_isIso]; rw [← sheafComposeNatTrans_fac J F adj₁ adj₂]; rw [(W _).precomp_iff _ _ (J.W_adj_unit_app adj₂ (P ⋙ F))]

variable [J.PreservesSheafification F]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIso (sheafComposeNatTrans J F adj₁ adj₂)
  body: by
  rw [← J.preservesSheafification_iff_of_adjunctions_of_hasSheafCompose]
  infer_instance

中文:
实例 :
  签名: 是同构 (sheafCompose自然数Trans J F adj₁ adj₂)
  定义体: by
  rw [← J.preservesSheafification_iff_of_adjunctions_of_hasSheafCompose]
  infer_instance

Depends on / 依赖: J.preservesSheafification_iff_of_adjunctions_of_hasSheafCompose, infer_instance, preservesSheafification_iff_of_adjunctions_of_hasSheafCompose
-/
instance : IsIso (sheafComposeNatTrans J F adj₁ adj₂) := by
  rw [← J.preservesSheafification_iff_of_adjunctions_of_hasSheafCompose]
  infer_instance

/--
Definition of `sheafComposeNatIso` / `sheafComposeNatIso` 的定义

English:
definition sheafComposeNatIso
  signature: :
  body: asIso (sheafComposeNatTrans J F adj₁ adj₂)

中文:
定义 sheafCompose自然数Iso
  签名: :
  定义体: asIso (sheafComposeNatTrans J F adj₁ adj₂)

Depends on / 依赖: sheafComposeNatTrans
-/
noncomputable def sheafComposeNatIso :
    (whiskeringRight Cᵒᵖ A B).obj F ⋙ G₂ ≅ G₁ ⋙ sheafCompose J F :=
  asIso (sheafComposeNatTrans J F adj₁ adj₂)

end HasSheafCompose

end

section HasSheafCompose

variable [HasWeakSheafify J A] [HasWeakSheafify J B] [J.HasSheafCompose F]
  [J.PreservesSheafification F] (P : Cᵒᵖ ⥤ A)

/--
Definition of `sheafifyComposeIso` / `sheafifyComposeIso` 的定义

English:
definition sheafifyComposeIso
  signature: :
  body: (sheafToPresheaf J B).mapIso
    ((sheafComposeNatIso J F (sheafificationAdjunction J A) (sheafificationAdjunction J B)).app P)

@[reassoc (attr := simp)]

中文:
定义 sheafifyComposeIso
  签名: :
  定义体: (sheafToPresheaf J B).mapIso
    ((sheafComposeNatIso J F (sheafificationAdjunction J A) (sheafificationAdjunction J B)).app P)

@[reassoc (attr := simp)]

Depends on / 依赖: mapIso, sheafComposeNatIso, sheafToPresheaf, sheafificationAdjunction
-/
noncomputable def sheafifyComposeIso :
    sheafify J (P ⋙ F) ≅ sheafify J P ⋙ F :=
  (sheafToPresheaf J B).mapIso
    ((sheafComposeNatIso J F (sheafificationAdjunction J A) (sheafificationAdjunction J B)).app P)

@[reassoc (attr := simp)]
/--
lemma `sheafComposeIso_hom_fac` / 引理 `sheafComposeIso_hom_fac`

English:
lemma sheafComposeIso_hom_fac
  proof: sheafComposeNatTrans_fac J F (sheafificationAdjunction J A) (sheafificationAdjunction J B) P

@[reassoc (attr := simp)]

中文:
引理 sheafComposeIso_hom_fac
  证明: sheafComposeNatTrans_fac J F (sheafificationAdjunction J A) (sheafificationAdjunction J B) P

@[reassoc (attr := simp)]

Depends on / 依赖: sheafComposeNatTrans_fac, sheafificationAdjunction
-/
lemma sheafComposeIso_hom_fac :
    toSheafify J (P ⋙ F) ≫ (sheafifyComposeIso J F P).hom =
      whiskerRight (toSheafify J P) F :=
  sheafComposeNatTrans_fac J F (sheafificationAdjunction J A) (sheafificationAdjunction J B) P

@[reassoc (attr := simp)]
/--
lemma `sheafComposeIso_inv_fac` / 引理 `sheafComposeIso_inv_fac`

English:
lemma sheafComposeIso_inv_fac
  proof: by
  rw [← sheafComposeIso_hom_fac]; rw [assoc]; rw [Iso.hom_inv_id]; rw [comp_id]

中文:
引理 sheafComposeIso_inv_fac
  证明: by
  rw [← sheafComposeIso_hom_fac]; rw [assoc]; rw [Iso.hom_inv_id]; rw [comp_id]

Depends on / 依赖: Iso.hom_inv_id, comp_id, hom_inv_id, sheafComposeIso_hom_fac
-/
lemma sheafComposeIso_inv_fac :
    whiskerRight (toSheafify J P) F ≫ (sheafifyComposeIso J F P).inv =
      toSheafify J (P ⋙ F) := by
  rw [← sheafComposeIso_hom_fac]; rw [assoc]; rw [Iso.hom_inv_id]; rw [comp_id]

end HasSheafCompose

namespace GrothendieckTopology

section

variable {D E : Type*} [Category* D] [Category* E] (F : D ⥤ E)
  [forall (J : MulticospanShape.{max v u, max v u}), HasLimitsOfShape (WalkingMulticospan J) D]
  [forall (J : MulticospanShape.{max v u, max v u}), HasLimitsOfShape (WalkingMulticospan J) E]
  [forall X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]
  [forall X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ E]
  [forall X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ F]
  [forall (X : C) (W : J.Cover X) (P : Cᵒᵖ ⥤ D), PreservesLimit (W.index P).multicospan F]
  {FD : D -> D -> Type*} {CD : D -> Type*} {FE : E -> E -> Type*} {CE : E -> Type*}
  [forall X Y, FunLike (FD X Y) (CD X) (CD Y)] [forall X Y, FunLike (FE X Y) (CE X) (CE Y)]
  [instCCD : ConcreteCategory D FD] [instCCE : ConcreteCategory E FE]
  [forall X, PreservesColimitsOfShape (Cover J X)ᵒᵖ (forget D)]
  [forall X, PreservesColimitsOfShape (Cover J X)ᵒᵖ (forget E)]
  [PreservesLimitsOfSize.{max v u, max v u} (forget D)]
  [PreservesLimitsOfSize.{max v u, max v u} (forget E)]
  [(forget D).ReflectsIsomorphisms] [(forget E).ReflectsIsomorphisms]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include instCCD instCCE in
/--
lemma `sheafToPresheaf_map_sheafComposeNatTrans_eq_sheafifyCompIso_inv` / 引理 `sheafToPresheaf_map_sheafComposeNatTrans_eq_sheafifyCompIso_inv`

English:
lemma sheafToPresheaf_map_sheafComposeNatTrans_eq_sheafifyCompIso_inv
  given: (P : Cᵒᵖ ⥤ D)
  proof: by
  suffices (sheafComposeNatTrans J F (plusPlusAdjunction J D) (plusPlusAdjunction J E)).app P =
    ⟨(sheafifyCompIso J F P).inv⟩ by
    rw [this]
    rfl
  apply ((plusPlusAdjunction J E).homEquiv _ _).injective
  convert! sheafComposeNatTrans_fac J F (plusPlusAdjunction J D) (plusPlusAdjunction J E) P
  dsimp [plusPlusAdjunction]
  simp

中文:
引理 sheafToPresheaf_map_sheafCompose自然数Trans_eq_sheafifyCompIso_inv
  条件: (P : Cᵒᵖ ⥤ D)
  证明: by
  suffices (sheafComposeNatTrans J F (plusPlusAdjunction J D) (plusPlusAdjunction J E)).app P =
    ⟨(sheafifyCompIso J F P).inv⟩ by
    rw [this]
    rfl
  apply ((plusPlusAdjunction J E).homEquiv _ _).injective
  convert! sheafComposeNatTrans_fac J F (plusPlusAdjunction J D) (plusPlusAdjunction J E) P
  dsimp [plusPlusAdjunction]
  simp

Depends on / 依赖: convert, homEquiv, injective, plusPlusAdjunction, sheafComposeNatTrans, sheafComposeNatTrans_fac, sheafifyCompIso
-/
lemma sheafToPresheaf_map_sheafComposeNatTrans_eq_sheafifyCompIso_inv (P : Cᵒᵖ ⥤ D) :
    (sheafToPresheaf J E).map
      ((sheafComposeNatTrans J F (plusPlusAdjunction J D) (plusPlusAdjunction J E)).app P) =
      (sheafifyCompIso J F P).inv := by
  suffices (sheafComposeNatTrans J F (plusPlusAdjunction J D) (plusPlusAdjunction J E)).app P =
    ⟨(sheafifyCompIso J F P).inv⟩ by
    rw [this]
    rfl
  apply ((plusPlusAdjunction J E).homEquiv _ _).injective
  convert! sheafComposeNatTrans_fac J F (plusPlusAdjunction J D) (plusPlusAdjunction J E) P
  dsimp [plusPlusAdjunction]
  simp

set_option backward.isDefEq.respectTransparency.types false in
instance (P : Cᵒᵖ ⥤ D) :
    IsIso ((sheafComposeNatTrans J F (plusPlusAdjunction J D) (plusPlusAdjunction J E)).app P) := by
  rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf J E)]; rw [sheafToPresheaf_map_sheafComposeNatTrans_eq_sheafifyCompIso_inv]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIso (sheafComposeNatTrans J F (plusPlusAdjunction J D) (plusPlusAdjunction J E))
  body: NatIso.isIso_of_isIso_app _

中文:
实例 :
  签名: 是同构 (sheafCompose自然数Trans J F (plusPlusAdjunction J D) (plusPlusAdjunction J E))
  定义体: NatIso.isIso_of_isIso_app _

Depends on / 依赖: NatIso, NatIso.isIso_of_isIso_app, isIso_of_isIso_app
-/
instance : IsIso (sheafComposeNatTrans J F (plusPlusAdjunction J D) (plusPlusAdjunction J E)) :=
  NatIso.isIso_of_isIso_app _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesSheafification J F
  body: by
  rw [preservesSheafification_iff_of_adjunctions_of_hasSheafCompose _ _
    (plusPlusAdjunction J D) (plusPlusAdjunction J E)]
  infer_instance

中文:
实例 :
  签名: 保持层化 J F
  定义体: by
  rw [preservesSheafification_iff_of_adjunctions_of_hasSheafCompose _ _
    (plusPlusAdjunction J D) (plusPlusAdjunction J E)]
  infer_instance

Depends on / 依赖: infer_instance, plusPlusAdjunction, preservesSheafification_iff_of_adjunctions_of_hasSheafCompose
-/
instance : PreservesSheafification J F := by
  rw [preservesSheafification_iff_of_adjunctions_of_hasSheafCompose _ _
    (plusPlusAdjunction J D) (plusPlusAdjunction J E)]
  infer_instance

end

instance {D : Type*} [Category.{max v u} D] {FD : D -> D -> Type*} {CD : D -> Type (max v u)}
    [forall X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory.{max v u} D FD]
    [PreservesLimits (forget D)]
    [forall X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]
    [forall X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget D)]
    [forall (J : MulticospanShape.{max v u, max v u}),
      Limits.HasLimitsOfShape (Limits.WalkingMulticospan J) D]
    [(forget D).ReflectsIsomorphisms] : PreservesSheafification J (forget D) :=
  inferInstance

end GrothendieckTopology

end CategoryTheory
