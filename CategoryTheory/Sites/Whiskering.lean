/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.ConcreteCategory.Forget

/-!

In this file we construct the functor `Sheaf J A ⥤ Sheaf J B` between sheaf categories
obtained by composition with a functor `F : A ⥤ B`.

In order for the sheaf condition to be preserved, `F` must preserve the correct limits.
The lemma `Presheaf.IsSheaf.comp` says that composition with such an `F` indeed preserves the
sheaf condition.

The functor between sheaf categories is called `sheafCompose J F`.
Given a natural transformation `η : F ⟶ G`, we obtain a natural transformation
`sheafCompose J F ⟶ sheafCompose J G`, which we call `sheafCompose_map J η`.

-/

@[expose] public section


namespace CategoryTheory

open CategoryTheory.Limits CategoryTheory.Functor

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]
variable {A : Type u₂} [Category.{v₂} A]
variable {B : Type u₃} [Category.{v₃} B]
variable (J : GrothendieckTopology C)
variable {U : C} (R : Presieve U)
variable (F G H : A ⥤ B) (η : F ⟶ G) (γ : G ⟶ H)

/--
Definition of `GrothendieckTopology.HasSheafCompose` / `GrothendieckTopology.HasSheafCompose` 的定义

English:
class GrothendieckTopology.HasSheafCompose
  parameters: : Prop where
  axioms and operations (1):
    - isSheaf((P : Cᵒᵖ ⥤ A) (hP : Presheaf.IsSheaf J P)) : Presheaf.IsSheaf J (P ⋙ F)

中文:
类 Grothendieck拓扑.有SheafCompose
  参数: : 命题 where
  公理与运算 (1 个):
    - isSheaf((P : Cᵒᵖ ⥤ A) (hP : 预层.是层 J P)) : 预层.是层 J (P ⋙ F)
-/
class GrothendieckTopology.HasSheafCompose : Prop where
  /-- For every sheaf `P`, `P ⋙ F` is a sheaf. -/
  isSheaf (P : Cᵒᵖ ⥤ A) (hP : Presheaf.IsSheaf J P) : Presheaf.IsSheaf J (P ⋙ F)

variable [J.HasSheafCompose F] [J.HasSheafCompose G] [J.HasSheafCompose H]

/-- Composing a functor which `HasSheafCompose`, yields a functor between sheaf categories. -/
@[simps! obj_obj map_hom]
/--
Definition of `sheafCompose` / `sheafCompose` 的定义

English:
definition sheafCompose
  signature: : Sheaf J A ⥤ Sheaf J B
  body: ObjectProperty.lift _
    (sheafToPresheaf _ _ ⋙ (Functor.whiskeringRight _ _ _).obj F)
      (fun P => GrothendieckTopology.HasSheafCompose.isSheaf _ P.property)

中文:
定义 sheafCompose
  签名: : 层 J A ⥤ 层 J B
  定义体: ObjectProperty.lift _
    (sheafToPresheaf _ _ ⋙ (Functor.whiskeringRight _ _ _).obj F)
      (fun P => GrothendieckTopology.HasSheafCompose.isSheaf _ P.property)

Depends on / 依赖: Functor, Functor.whiskeringRight, GrothendieckTopology, GrothendieckTopology.HasSheafCompose.isSheaf, HasSheafCompose, ObjectProperty, ObjectProperty.lift, P.property, isSheaf, property, sheafToPresheaf, whiskeringRight
-/
def sheafCompose : Sheaf J A ⥤ Sheaf J B :=
  ObjectProperty.lift _
    (sheafToPresheaf _ _ ⋙ (Functor.whiskeringRight _ _ _).obj F)
      (fun P => GrothendieckTopology.HasSheafCompose.isSheaf _ P.property)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [F.Faithful]
  signature: : (sheafCompose J F ⋙ sheafToPresheaf _ _).Faithful
  body: show (sheafToPresheaf _ _ ⋙ (whiskeringRight Cᵒᵖ A B).obj F).Faithful from inferInstance

中文:
实例 [F.忠实]
  签名: : (sheafCompose J F ⋙ sheafToPresheaf _ _).忠实
  定义体: show (sheafToPresheaf _ _ ⋙ (whiskeringRight Cᵒᵖ A B).obj F).Faithful from inferInstance

Depends on / 依赖: Faithful, sheafToPresheaf, whiskeringRight
-/
instance [F.Faithful] : (sheafCompose J F ⋙ sheafToPresheaf _ _).Faithful :=
  show (sheafToPresheaf _ _ ⋙ (whiskeringRight Cᵒᵖ A B).obj F).Faithful from inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [F.Faithful]
  signature: [F.Full]
  body: show (sheafToPresheaf _ _ ⋙ (whiskeringRight Cᵒᵖ A B).obj F).Full from inferInstance

中文:
实例 [F.忠实]
  签名: [F.满]
  定义体: show (sheafToPresheaf _ _ ⋙ (whiskeringRight Cᵒᵖ A B).obj F).Full from inferInstance

Depends on / 依赖: sheafToPresheaf, whiskeringRight
-/
instance [F.Faithful] [F.Full] : (sheafCompose J F ⋙ sheafToPresheaf _ _).Full :=
  show (sheafToPresheaf _ _ ⋙ (whiskeringRight Cᵒᵖ A B).obj F).Full from inferInstance

variable {F} in
/--
Definition of `fullyFaithfulSheafComposeCompSheafToPresheaf` / `fullyFaithfulSheafComposeCompSheafToPresheaf` 的定义

English:
definition fullyFaithfulSheafComposeCompSheafToPresheaf
  signature: (hF : F.FullyFaithful)
  body: (fullyFaithfulSheafToPresheaf J A).comp (hF.whiskeringRight Cᵒᵖ)

中文:
定义 fullyFaithfulSheafComposeCompSheafToPresheaf
  签名: (hF : F.满忠实)
  定义体: (fullyFaithfulSheafToPresheaf J A).comp (hF.whiskeringRight Cᵒᵖ)

Depends on / 依赖: fullyFaithfulSheafToPresheaf, hF.whiskeringRight, whiskeringRight
-/
def fullyFaithfulSheafComposeCompSheafToPresheaf (hF : F.FullyFaithful) :
    (sheafCompose J F ⋙ sheafToPresheaf J B).FullyFaithful :=
  (fullyFaithfulSheafToPresheaf J A).comp (hF.whiskeringRight Cᵒᵖ)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [F.Faithful]
  signature: : (sheafCompose J F).Faithful
  body: Functor.Faithful.of_comp (sheafCompose J F) (sheafToPresheaf _ _)

中文:
实例 [F.忠实]
  签名: : (sheafCompose J F).忠实
  定义体: Functor.Faithful.of_comp (sheafCompose J F) (sheafToPresheaf _ _)

Depends on / 依赖: Faithful, Functor, Functor.Faithful.of_comp, of_comp, sheafCompose, sheafToPresheaf
-/
instance [F.Faithful] : (sheafCompose J F).Faithful :=
  Functor.Faithful.of_comp (sheafCompose J F) (sheafToPresheaf _ _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [F.Full]
  signature: [F.Faithful]
  body: Functor.Full.of_comp_faithful (sheafCompose J F) (sheafToPresheaf _ _)

中文:
实例 [F.满]
  签名: [F.忠实]
  定义体: Functor.Full.of_comp_faithful (sheafCompose J F) (sheafToPresheaf _ _)

Depends on / 依赖: Functor, Functor.Full.of_comp_faithful, of_comp_faithful, sheafCompose, sheafToPresheaf
-/
instance [F.Full] [F.Faithful] : (sheafCompose J F).Full :=
  Functor.Full.of_comp_faithful (sheafCompose J F) (sheafToPresheaf _ _)

variable {F} in
/--
Definition of `fullyFaithfulSheafCompose` / `fullyFaithfulSheafCompose` 的定义

English:
definition fullyFaithfulSheafCompose
  signature: (hF : F.FullyFaithful)
  body: (fullyFaithfulSheafComposeCompSheafToPresheaf J hF).ofCompFaithful

中文:
定义 fullyFaithfulSheafCompose
  签名: (hF : F.满忠实)
  定义体: (fullyFaithfulSheafComposeCompSheafToPresheaf J hF).ofCompFaithful

Depends on / 依赖: fullyFaithfulSheafComposeCompSheafToPresheaf, ofCompFaithful
-/
def fullyFaithfulSheafCompose (hF : F.FullyFaithful) :
    (sheafCompose J F).FullyFaithful :=
  (fullyFaithfulSheafComposeCompSheafToPresheaf J hF).ofCompFaithful

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [F.ReflectsIsomorphisms]
  signature: : (sheafCompose J F).ReflectsIsomorphisms where
  body: by
    rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _)]; rw [← isIso_iff_of_reflects_iso _ ((whiskeringRight Cᵒᵖ A B).obj F)]
    change IsIso ((sheafToPresheaf _ _).map ((sheafCompose J F).map f))
    infer_instance

中文:
实例 [F.反映同构]
  签名: : (sheafCompose J F).反映同构 where
  定义体: by
    rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _)]; rw [← isIso_iff_of_reflects_iso _ ((whiskeringRight Cᵒᵖ A B).obj F)]
    change IsIso ((sheafToPresheaf _ _).map ((sheafCompose J F).map f))
    infer_instance

Depends on / 依赖: infer_instance, isIso_iff_of_reflects_iso, sheafCompose, sheafToPresheaf, whiskeringRight
-/
instance [F.ReflectsIsomorphisms] : (sheafCompose J F).ReflectsIsomorphisms where
  reflects {G₁ G₂} f _ := by
    rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _)]; rw [← isIso_iff_of_reflects_iso _ ((whiskeringRight Cᵒᵖ A B).obj F)]
    change IsIso ((sheafToPresheaf _ _).map ((sheafCompose J F).map f))
    infer_instance

variable {F G}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `sheafCompose_map` / `sheafCompose_map` 的定义

English:
definition sheafCompose_map
  signature: : sheafCompose J F ⟶ sheafCompose J G where
  body: fun _ => .mk whiskerLeft _ η

@[simp]

中文:
定义 sheafCompose_map
  签名: : sheafCompose J F ⟶ sheafCompose J G where
  定义体: fun _ => .mk whiskerLeft _ η

@[simp]

Depends on / 依赖: whiskerLeft
-/
def sheafCompose_map : sheafCompose J F ⟶ sheafCompose J G where
app := fun _ => .mk whiskerLeft _ η

@[simp]
/--
lemma `sheafCompose_id` / 引理 `sheafCompose_id`

English:
lemma sheafCompose_id
  statement: sheafCompose_map (F := F) J (𝟙 _) = 𝟙 _
  proof: rfl

@[simp]

中文:
引理 sheafCompose_id
  结论: sheafCompose_map (F := F) J (𝟙 _) = 𝟙 _
  证明: rfl

@[simp]
-/
lemma sheafCompose_id : sheafCompose_map (F := F) J (𝟙 _) = 𝟙 _ := rfl

@[simp]
/--
lemma `sheafCompose_comp` / 引理 `sheafCompose_comp`

English:
lemma sheafCompose_comp
  proof: rfl

中文:
引理 sheafCompose_comp
  证明: rfl
-/
lemma sheafCompose_comp :
    sheafCompose_map J (η ≫ γ) = sheafCompose_map J η ≫ sheafCompose_map J γ := rfl

namespace GrothendieckTopology.Cover

variable (F G) {J}
variable (P : Cᵒᵖ ⥤ A) {X : C} (S : J.Cover X)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The multicospan associated to a cover `S : J.Cover X` and a presheaf of the form `P ⋙ F`
is isomorphic to the composition of the multicospan associated to `S` and `P`,
composed with `F`. -/
@[simps!]
/--
Definition of `multicospanComp` / `multicospanComp` 的定义

English:
definition multicospanComp
  signature: : (S.index (P ⋙ F)).multicospan ≅ (S.index P).multicospan ⋙ F
  body: NatIso.ofComponents
    (fun t =>
      match t with
      | WalkingMulticospan.left _ => Iso.refl _
      | WalkingMulticospan.right _ => Iso.refl _)
    (by
      rintro (a | b) (a | b) (f | f | f)
      all_goals cat_disch)

中文:
定义 multicospanComp
  签名: : (S.index (P ⋙ F)).multicospan ≅ (S.index P).multicospan ⋙ F
  定义体: NatIso.ofComponents
    (fun t =>
      match t with
      | WalkingMulticospan.left _ => Iso.refl _
      | WalkingMulticospan.right _ => Iso.refl _)
    (by
      rintro (a | b) (a | b) (f | f | f)
      all_goals cat_disch)

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, WalkingMulticospan, WalkingMulticospan.left, WalkingMulticospan.right, all_goals, cat_disch, ofComponents
-/
def multicospanComp : (S.index (P ⋙ F)).multicospan ≅ (S.index P).multicospan ⋙ F :=
  NatIso.ofComponents
    (fun t =>
      match t with
      | WalkingMulticospan.left _ => Iso.refl _
      | WalkingMulticospan.right _ => Iso.refl _)
    (by
      rintro (a | b) (a | b) (f | f | f)
      all_goals cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `mapMultifork` / `mapMultifork` 的定义

English:
definition mapMultifork
  signature: :
  body: Cone.ext (Iso.refl _)

中文:
定义 mapMultifork
  签名: :
  定义体: Cone.ext (Iso.refl _)

Depends on / 依赖: Cone.ext, Iso.refl
-/
def mapMultifork :
    F.mapCone (S.multifork P) ≅
      (Limits.Cone.postcompose (S.multicospanComp F P).hom).obj (S.multifork (P ⋙ F)) :=
  Cone.ext (Iso.refl _)

end GrothendieckTopology.Cover

/--
Composing a sheaf with a functor preserving the limit of `(S.index P).multicospan` yields a functor
between sheaf categories.
-/
instance (priority := high) hasSheafCompose_of_preservesMulticospan (F : A ⥤ B)
    [forall (X : C) (S : J.Cover X) (P : Cᵒᵖ ⥤ A), PreservesLimit (S.index P).multicospan F] :
    J.HasSheafCompose F where
  isSheaf P hP := by
    rw [Presheaf.isSheaf_iff_multifork] at hP ⊢
    intro X S
    obtain ⟨h⟩ := hP X S
    replace h := isLimitOfPreserves F h
    replace h := Limits.IsLimit.ofIsoLimit h (S.mapMultifork F P)
    exact ⟨Limits.IsLimit.postcomposeHomEquiv (S.multicospanComp F P) _ h⟩

/--
Instance `hasSheafCompose_of_preservesLimitsOfSize` / 实例 `hasSheafCompose_of_preservesLimitsOfSize`

English:
instance hasSheafCompose_of_preservesLimitsOfSize
  signature: [PreservesLimitsOfSize.{v₁, max u₁ v₁} F]
  body: Presheaf.isSheaf_comp_of_isSheaf J _ F hP

中文:
实例 hasSheafCompose_of_preservesLimitsOfSize
  签名: [保持LimitsOfSize.{v₁, 最大值 u₁ v₁} F]
  定义体: Presheaf.isSheaf_comp_of_isSheaf J _ F hP

Depends on / 依赖: Presheaf, Presheaf.isSheaf_comp_of_isSheaf, isSheaf_comp_of_isSheaf
-/
instance hasSheafCompose_of_preservesLimitsOfSize [PreservesLimitsOfSize.{v₁, max u₁ v₁} F] :
    J.HasSheafCompose F where
  isSheaf _ hP := Presheaf.isSheaf_comp_of_isSheaf J _ F hP

variable {J}

/--
lemma `Sheaf.isSeparated` / 引理 `Sheaf.isSeparated`

English:
lemma Sheaf.isSeparated
  statement: {FA : A -> A -> Type*} {CA : A -> Type*}
  proof: by
  rintro X S hS x y h
  exact (((isSheaf_iff_isSheaf_of_type _ _).1
    ((sheafCompose J (forget A)).obj F).2).isSeparated S hS).ext (fun _ _ hf => h _ _ hf)

中文:
引理 层.isSeparated
  结论: {FA : A -> A -> 类型} {CA : A -> 类型}
  证明: by
  rintro X S hS x y h
  exact (((isSheaf_iff_isSheaf_of_type _ _).1
    ((sheafCompose J (forget A)).obj F).2).isSeparated S hS).ext (fun _ _ hf => h _ _ hf)

Depends on / 依赖: forget, isSeparated, isSheaf_iff_isSheaf_of_type, sheafCompose
-/
lemma Sheaf.isSeparated {FA : A -> A -> Type*} {CA : A -> Type*}
    [forall X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA] [J.HasSheafCompose (forget A)]
    (F : Sheaf J A) : Presheaf.IsSeparated J F.obj := by
  rintro X S hS x y h
  exact (((isSheaf_iff_isSheaf_of_type _ _).1
    ((sheafCompose J (forget A)).obj F).2).isSeparated S hS).ext (fun _ _ hf => h _ _ hf)

/--
lemma `Presheaf.IsSheaf.isSeparated` / 引理 `Presheaf.IsSheaf.isSeparated`

English:
lemma Presheaf.IsSheaf.isSeparated
  statement: {F : Cᵒᵖ ⥤ A} {FA : A -> A -> Type*} {CA : A -> Type*}
  proof: Sheaf.isSeparated ⟨F, hF⟩

中文:
引理 预层.是层.isSeparated
  结论: {F : Cᵒᵖ ⥤ A} {FA : A -> A -> 类型} {CA : A -> 类型}
  证明: Sheaf.isSeparated ⟨F, hF⟩

Depends on / 依赖: Sheaf.isSeparated, isSeparated
-/
lemma Presheaf.IsSheaf.isSeparated {F : Cᵒᵖ ⥤ A} {FA : A -> A -> Type*} {CA : A -> Type*}
    [forall X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
    [J.HasSheafCompose (forget A)] (hF : Presheaf.IsSheaf J F) :
    Presheaf.IsSeparated J F :=
  Sheaf.isSeparated ⟨F, hF⟩

end CategoryTheory
