/-
Copyright (c) 2021 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu, Andrew Yang
-/
module

public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.CategoryTheory.Sites.Pullback

/-!
# functors between categories of sheaves

Show that the pushforward of a sheaf is a sheaf, and define
the pushforward functor from the category of C-valued sheaves
on X to that of sheaves on Y, given a continuous map between
topological spaces X and Y.

## Main definitions
- `TopCat.Sheaf.pushforward`:
    The pushforward functor between sheaf categories over topological spaces.
- `TopCat.Sheaf.pullback`: The pullback functor between sheaf categories over topological spaces.
- `TopCat.Sheaf.pullbackPushforwardAdjunction`:
  The adjunction between pullback and pushforward for sheaves on topological spaces.

-/

@[expose] public section


noncomputable section

universe w v u

open CategoryTheory

open CategoryTheory.Limits

open TopologicalSpace

open scoped AlgebraicGeometry

variable {C : Type u} [Category.{v} C]
variable {X Y : TopCat.{w}} (f : X ⟶ Y)
variable ⦃ι : Type w⦄ {U : ι -> Opens Y}

namespace TopCat

namespace Sheaf

open Presheaf

/--
theorem `pushforward_sheaf_of_sheaf` / 定理 `pushforward_sheaf_of_sheaf`

English:
theorem pushforward_sheaf_of_sheaf
  given: {F : X.Presheaf C} (h : F.IsSheaf)
  statement: (f _* F).IsSheaf
  proof: (Opens.map f).op_comp_isSheaf _ _ ⟨_, h⟩

中文:
定理 pushforward_sheaf_of_sheaf
  条件: {F : X.预层 C} (h : F.是层)
  结论: (f _* F).是层
  证明: (Opens.map f).op_comp_isSheaf _ _ ⟨_, h⟩

Depends on / 依赖: Opens.map, op_comp_isSheaf
-/
theorem pushforward_sheaf_of_sheaf {F : X.Presheaf C} (h : F.IsSheaf) : (f _* F).IsSheaf :=
  (Opens.map f).op_comp_isSheaf _ _ ⟨_, h⟩

variable (C)

/--
Definition of `pushforward` / `pushforward` 的定义

English:
definition pushforward
  signature: (f : X ⟶ Y)
  body: (Opens.map f).sheafPushforwardContinuous _ _ _

中文:
定义 pushforward
  签名: (f : X ⟶ Y)
  定义体: (Opens.map f).sheafPushforwardContinuous _ _ _

Depends on / 依赖: Opens.map, sheafPushforwardContinuous
-/
def pushforward (f : X ⟶ Y) : X.Sheaf C ⥤ Y.Sheaf C :=
  (Opens.map f).sheafPushforwardContinuous _ _ _

/--
lemma `pushforward_forget` / 引理 `pushforward_forget`

English:
lemma pushforward_forget
  given: (f : X ⟶ Y)
  proof: rfl

中文:
引理 pushforward_forget
  条件: (f : X ⟶ Y)
  证明: rfl
-/
lemma pushforward_forget (f : X ⟶ Y) :
    pushforward C f ⋙ forget C Y = forget C X ⋙ Presheaf.pushforward C f := rfl

/--
Definition of `pushforwardForgetIso` / `pushforwardForgetIso` 的定义

English:
definition pushforwardForgetIso
  signature: (f : X ⟶ Y)
  body: Iso.refl _

中文:
定义 pushforwardForgetIso
  签名: (f : X ⟶ Y)
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def pushforwardForgetIso (f : X ⟶ Y) :
    pushforward C f ⋙ forget C Y ≅ forget C X ⋙ Presheaf.pushforward C f := Iso.refl _

variable {C}

/--
lemma `pushforward_obj_val` / 引理 `pushforward_obj_val`

English:
lemma pushforward_obj_val
  given: (f : X ⟶ Y) (F : X.Sheaf C)
  proof: rfl

中文:
引理 pushforward_obj_val
  条件: (f : X ⟶ Y) (F : X.层 C)
  证明: rfl
-/
@[simp] lemma pushforward_obj_val (f : X ⟶ Y) (F : X.Sheaf C) :
    ((pushforward C f).obj F).1 = f _* F.1 := rfl

/--
lemma `pushforward_map` / 引理 `pushforward_map`

English:
lemma pushforward_map
  given: (f : X ⟶ Y) {F F' : X.Sheaf C} (α : F ⟶ F')
  proof: rfl

中文:
引理 pushforward_map
  条件: (f : X ⟶ Y) {F F' : X.层 C} (α : F ⟶ F')
  证明: rfl
-/
@[simp] lemma pushforward_map (f : X ⟶ Y) {F F' : X.Sheaf C} (α : F ⟶ F') :
    ((pushforward C f).map α).1 = (Presheaf.pushforward C f).map α.1 := rfl

variable (A : Type*) [Category.{w} A] {FA : A -> A -> Type*} {CA : A -> Type w}
variable [forall X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w} A FA] [HasColimits A]
variable [HasLimits A] [PreservesLimits (CategoryTheory.forget A)]
variable [PreservesFilteredColimits (CategoryTheory.forget A)]
variable [(CategoryTheory.forget A).ReflectsIsomorphisms]

/--
Definition of `pullback` / `pullback` 的定义

English:
definition pullback
  signature: (f : X ⟶ Y)
  body: (Opens.map f).sheafPullback _ _ _

中文:
定义 pullback
  签名: (f : X ⟶ Y)
  定义体: (Opens.map f).sheafPullback _ _ _

Depends on / 依赖: Opens.map, sheafPullback
-/
def pullback (f : X ⟶ Y) : Y.Sheaf A ⥤ X.Sheaf A :=
  (Opens.map f).sheafPullback _ _ _

/--
Definition of `pullbackIso` / `pullbackIso` 的定义

English:
definition pullbackIso
  signature: (f : X ⟶ Y)
  body: Functor.sheafPullbackConstruction.sheafPullbackIso _ _ _ _

中文:
定义 pullbackIso
  签名: (f : X ⟶ Y)
  定义体: Functor.sheafPullbackConstruction.sheafPullbackIso _ _ _ _

Depends on / 依赖: Functor, Functor.sheafPullbackConstruction.sheafPullbackIso, sheafPullbackConstruction, sheafPullbackIso
-/
def pullbackIso (f : X ⟶ Y) :
    pullback A f ≅ forget A Y ⋙ Presheaf.pullback A f ⋙ presheafToSheaf _ _ :=
  Functor.sheafPullbackConstruction.sheafPullbackIso _ _ _ _

/--
Definition of `pullbackPushforwardAdjunction` / `pullbackPushforwardAdjunction` 的定义

English:
definition pullbackPushforwardAdjunction
  signature: (f : X ⟶ Y)
  body: (Opens.map f).sheafAdjunctionContinuous _ _ _

中文:
定义 pullbackPushforwardAdjunction
  签名: (f : X ⟶ Y)
  定义体: (Opens.map f).sheafAdjunctionContinuous _ _ _

Depends on / 依赖: Opens.map, sheafAdjunctionContinuous
-/
def pullbackPushforwardAdjunction (f : X ⟶ Y) :
    pullback A f ⊣ pushforward A f :=
  (Opens.map f).sheafAdjunctionContinuous _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (pullback A f).IsLeftAdjoint
  body: (pullbackPushforwardAdjunction A f).isLeftAdjoint

中文:
实例 :
  签名: (pullback A f).是左伴随
  定义体: (pullbackPushforwardAdjunction A f).isLeftAdjoint

Depends on / 依赖: isLeftAdjoint, pullbackPushforwardAdjunction
-/
instance : (pullback A f).IsLeftAdjoint := (pullbackPushforwardAdjunction A f).isLeftAdjoint
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (pushforward A f).IsRightAdjoint
  body: (pullbackPushforwardAdjunction A f).isRightAdjoint

中文:
实例 :
  签名: (pushforward A f).是右伴随
  定义体: (pullbackPushforwardAdjunction A f).isRightAdjoint

Depends on / 依赖: isRightAdjoint, pullbackPushforwardAdjunction
-/
instance : (pushforward A f).IsRightAdjoint := (pullbackPushforwardAdjunction A f).isRightAdjoint

end Sheaf

end TopCat

namespace Topology.IsOpenEmbedding

open TopCat Sheaf

variable (A : Type*) [Category.{w} A]
variable {f : X ⟶ Y} (hf : IsOpenEmbedding f)

/--
Definition of `sheafPullback` / `sheafPullback` 的定义

English:
definition sheafPullback
  signature: : Y.Sheaf A ⥤ X.Sheaf A
  body: haveI := Topology.IsOpenEmbedding.functor_isContinuous hf
  hf.functor.sheafPushforwardContinuous _ _ _

中文:
定义 sheafPullback
  签名: : Y.层 A ⥤ X.层 A
  定义体: haveI := Topology.IsOpenEmbedding.functor_isContinuous hf
  hf.functor.sheafPushforwardContinuous _ _ _

Depends on / 依赖: IsOpenEmbedding, Topology, Topology.IsOpenEmbedding.functor_isContinuous, functor, functor_isContinuous, hf.functor.sheafPushforwardContinuous, sheafPushforwardContinuous
-/
def sheafPullback : Y.Sheaf A ⥤ X.Sheaf A :=
  haveI := Topology.IsOpenEmbedding.functor_isContinuous hf
  hf.functor.sheafPushforwardContinuous _ _ _

variable {FA : A -> A -> Type*} {CA : A -> Type w}
variable [forall X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w} A FA] [HasColimits A]
variable [HasLimits A] [PreservesLimits (CategoryTheory.forget A)]
variable [PreservesFilteredColimits (CategoryTheory.forget A)]
variable [(CategoryTheory.forget A).ReflectsIsomorphisms]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `sheafPullbackIso` / `sheafPullbackIso` 的定义

English:
definition sheafPullbackIso
  signature: : Sheaf.pullback A f ≅ hf.sheafPullback A
  body: by
  refine Sheaf.pullbackIso A f ≪≫ NatIso.ofComponents (fun F => ?_) (fun u => ?_)
  · exact (presheafToSheaf (Opens.grothendieckTopology ↑X) A).mapIso
      (hf.isOpenMap.pullbackIso.app _) ≪≫
      (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology X) A).preimageIso
      (isoSheafify (Op

中文:
定义 sheafPullbackIso
  签名: : 层.pullback A f ≅ hf.sheafPullback A
  定义体: by
  refine Sheaf.pullbackIso A f ≪≫ NatIso.ofComponents (fun F => ?_) (fun u => ?_)
  · exact (presheafToSheaf (Opens.grothendieckTopology ↑X) A).mapIso
      (hf.isOpenMap.pullbackIso.app _) ≪≫
      (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology X) A).preimageIso
      (isoSheafify (Op

Depends on / 依赖: Functor, Functor.map_comp_assoc, Functor.whiskerin, NatIso, NatIso.ofComponents, Opens.grothendieckTopology, Presheaf, Sheaf.hom_ext_iff, Sheaf.pullbackIso, TopCat, TopCat.Presheaf.isSheaf_of_isOpenEmbedding, fullyFaithfulSheafToPresheaf, grothendieckTopology, hf.isOpenMap.pullbackIso.app, hf.isOpenMap.pullbackIso.hom.naturality, hom_ext_iff, isOpenMap, isSheaf_of_isOpenEmbedding, isoSheafify, mapIso
-/
def sheafPullbackIso : Sheaf.pullback A f ≅ hf.sheafPullback A := by
  refine Sheaf.pullbackIso A f ≪≫ NatIso.ofComponents (fun F => ?_) (fun u => ?_)
  · exact (presheafToSheaf (Opens.grothendieckTopology ↑X) A).mapIso
      (hf.isOpenMap.pullbackIso.app _) ≪≫
      (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology X) A).preimageIso
      (isoSheafify (Opens.grothendieckTopology X)
      (TopCat.Presheaf.isSheaf_of_isOpenEmbedding hf F.2)).symm
  · dsimp
    rw [← Functor.map_comp_assoc]; rw [hf.isOpenMap.pullbackIso.hom.naturality]; rw [Sheaf.hom_ext_iff]
    simp only [Functor.whiskeringLeft_obj_obj, Functor.whiskeringLeft_obj_map, Functor.map_comp,
      isoSheafify_inv, Category.assoc]
    rw [ObjectProperty.FullSubcategory.comp_hom]; rw [ObjectProperty.FullSubcategory.comp_hom]; rw [ObjectProperty.FullSubcategory.comp_hom]; rw [ObjectProperty.FullSubcategory.comp_hom]
    dsimp [sheafPullback, Functor.sheafPushforwardContinuous, Sheaf.forget]
    simp only [sheafifyMap_sheafifyLift, Category.comp_id, sheafifyMap_sheafifyLift_assoc]
    rw [CategoryTheory.sheafifyLift_comp]

end Topology.IsOpenEmbedding
