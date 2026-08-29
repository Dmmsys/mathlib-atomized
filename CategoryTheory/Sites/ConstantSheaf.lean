/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
/-!

# The constant sheaf

We define the constant sheaf functor (the sheafification of the constant presheaf)
`constantSheaf : D ⥤ Sheaf J D` and prove that it is left adjoint to evaluation at a terminal
object (see `constantSheafAdj`).

We also define a predicate on sheaves, `Sheaf.IsConstant`, saying that a sheaf is in the
essential image of the constant sheaf functor.

## Main results

* `Sheaf.isConstant_iff_isIso_counit_app`: Provided that the constant sheaf functor is fully
  faithful, a sheaf is constant if and only if the counit of the constant sheaf adjunction applied
  to it is an isomorphism.

* `Sheaf.isConstant_iff_of_equivalence` : The property of a sheaf of being constant is invariant
  under equivalence of sheaf categories.

* `Sheaf.isConstant_iff_forget` : Given a "forgetful" functor `U : D ⥤ B` a sheaf `F : Sheaf J D` is
  constant if and only if the sheaf given by postcomposition with `U` is constant.
-/

@[expose] public section

namespace CategoryTheory

open Limits Opposite Category CategoryTheory.Functor Sheaf Adjunction

variable {C : Type*} [Category* C] (J : GrothendieckTopology C)
variable (D : Type*) [Category* D]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The constant presheaf functor is left adjoint to evaluation at a terminal object. -/
@[simps! unit_app counit_app_app]
/--
Definition of `constantPresheafAdj` / `constantPresheafAdj` 的定义

English:
definition constantPresheafAdj
  signature: {T : C} (hT : IsTerminal T)
  body: (Functor.constCompEvaluationObj D (op T)).hom
  counit := {
    app := fun F => {
      app := fun ⟨X⟩ => F.map (IsTerminal.from hT X).op
      naturality := fun _ _ _ => by
        simp only [Functor.comp_obj, Functor.const_obj_obj, Functor.id_obj, Functor.const_obj_map,
          Category.id_comp,

中文:
定义 constantPresheafAdj
  签名: {T : C} (hT : IsTerminal T)
  定义体: (Functor.constCompEvaluationObj D (op T)).hom
  counit := {
    app := fun F => {
      app := fun ⟨X⟩ => F.map (IsTerminal.from hT X).op
      naturality := fun _ _ _ => by
        simp only [Functor.comp_obj, Functor.const_obj_obj, Functor.id_obj, Functor.const_obj_map,
          Category.id_comp,

Depends on / 依赖: Functor, Functor.constCompEvaluationObj, constCompEvaluationObj
-/
noncomputable def constantPresheafAdj {T : C} (hT : IsTerminal T) :
    Functor.const Cᵒᵖ ⊣ (evaluation Cᵒᵖ D).obj (op T) where
  unit := (Functor.constCompEvaluationObj D (op T)).hom
  counit := {
    app := fun F => {
      app := fun ⟨X⟩ => F.map (IsTerminal.from hT X).op
      naturality := fun _ _ _ => by
        simp only [Functor.comp_obj, Functor.const_obj_obj, Functor.id_obj, Functor.const_obj_map,
          Category.id_comp, ← Functor.map_comp]
        congr
        simp }
    naturality := by intros; ext; simp /- Note: `aesop` works but is kind of slow -/ }

variable [HasWeakSheafify J D]

/--
Definition of `constantSheaf` / `constantSheaf` 的定义

English:
definition constantSheaf
  signature: : D ⥤ Sheaf J D
  body: Functor.const Cᵒᵖ ⋙ (presheafToSheaf J D)

中文:
定义 constantSheaf
  签名: : D ⥤ Sheaf J D
  定义体: Functor.const Cᵒᵖ ⋙ (presheafToSheaf J D)

Depends on / 依赖: Functor, Functor.const, presheafToSheaf
-/
noncomputable def constantSheaf : D ⥤ Sheaf J D := Functor.const Cᵒᵖ ⋙ (presheafToSheaf J D)

/-- The constant sheaf functor is left adjoint to evaluation at a terminal object. -/
@[simps! counit_app]
/--
Definition of `constantSheafAdj` / `constantSheafAdj` 的定义

English:
definition constantSheafAdj
  signature: {T : C} (hT : IsTerminal T)
  body: (constantPresheafAdj D hT).comp (sheafificationAdjunction J D)

中文:
定义 constantSheafAdj
  签名: {T : C} (hT : IsTerminal T)
  定义体: (constantPresheafAdj D hT).comp (sheafificationAdjunction J D)

Depends on / 依赖: constantPresheafAdj, sheafificationAdjunction
-/
noncomputable def constantSheafAdj {T : C} (hT : IsTerminal T) :
    constantSheaf J D ⊣ (sheafSections J D).obj (op T) :=
  (constantPresheafAdj D hT).comp (sheafificationAdjunction J D)

variable {D}

namespace Sheaf

/--
Definition of `IsConstant` / `IsConstant` 的定义

English:
class IsConstant
  parameters: (F : Sheaf J D)
  axioms and operations (1):
    - mem_essImage : (constantSheaf J D).essImage F

中文:
类 IsConstant
  参数: (F : Sheaf J D)
  公理与运算 (1 个):
    - mem_essImage : (constantSheaf J D).essImage F
-/
class IsConstant (F : Sheaf J D) : Prop where
  mem_essImage : (constantSheaf J D).essImage F

/--
lemma `mem_essImage_of_isConstant` / 引理 `mem_essImage_of_isConstant`

English:
lemma mem_essImage_of_isConstant
  given: (F : Sheaf J D) [IsConstant J F]
  proof: IsConstant.mem_essImage

中文:
引理 mem_essImage_of_isConstant
  条件: (F : Sheaf J D) [IsConstant J F]
  证明: IsConstant.mem_essImage

Depends on / 依赖: IsConstant, IsConstant.mem_essImage, mem_essImage
-/
lemma mem_essImage_of_isConstant (F : Sheaf J D) [IsConstant J F] :
    (constantSheaf J D).essImage F :=
  IsConstant.mem_essImage

/--
lemma `isConstant_congr` / 引理 `isConstant_congr`

English:
lemma isConstant_congr
  given: {F G : Sheaf J D} (i : F ≅ G) [IsConstant J F]
  statement: IsConstant J G where
  proof: essImage.ofIso i F.mem_essImage_of_isConstant

中文:
引理 isConstant_congr
  条件: {F G : Sheaf J D} (i : F ≅ G) [IsConstant J F]
  结论: IsConstant J G where
  证明: essImage.ofIso i F.mem_essImage_of_isConstant

Depends on / 依赖: F.mem_essImage_of_isConstant, essImage, essImage.ofIso, mem_essImage_of_isConstant
-/
lemma isConstant_congr {F G : Sheaf J D} (i : F ≅ G) [IsConstant J F] : IsConstant J G where
  mem_essImage := essImage.ofIso i F.mem_essImage_of_isConstant

/--
lemma `isConstant_of_iso` / 引理 `isConstant_of_iso`

English:
lemma isConstant_of_iso
  given: {F : Sheaf J D} {X : D} (i : F ≅ (constantSheaf J D).obj X)
  proof: ⟨_, ⟨i.symm⟩⟩

中文:
引理 isConstant_of_iso
  条件: {F : Sheaf J D} {X : D} (i : F ≅ (constantSheaf J D).obj X)
  证明: ⟨_, ⟨i.symm⟩⟩

Depends on / 依赖: i.symm
-/
lemma isConstant_of_iso {F : Sheaf J D} {X : D} (i : F ≅ (constantSheaf J D).obj X) :
    IsConstant J F := ⟨_, ⟨i.symm⟩⟩

/--
lemma `isConstant_iff_mem_essImage` / 引理 `isConstant_iff_mem_essImage`

English:
lemma isConstant_iff_mem_essImage
  statement: {L : D ⥤ Sheaf J D} {T : C} (hT : IsTerminal T)
  proof: by
  rw [essImage_eq_of_natIso (adj.leftAdjointUniq (constantSheafAdj J D hT))]
  exact ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

中文:
引理 isConstant_iff_mem_essImage
  结论: {L : D ⥤ Sheaf J D} {T : C} (hT : IsTerminal T)
  证明: by
  rw [essImage_eq_of_natIso (adj.leftAdjointUniq (constantSheafAdj J D hT))]
  exact ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

Depends on / 依赖: adj.leftAdjointUniq, closure_eq_closure, constantSheafAdj, eRk_union_closure_left_eq, essImage_eq_of_natIso, hIX.closure_eq_closure, leftAdjointUniq
-/
lemma isConstant_iff_mem_essImage {L : D ⥤ Sheaf J D} {T : C} (hT : IsTerminal T)
    (adj : L ⊣ (sheafSections J D).obj ⟨T⟩)
    (F : Sheaf J D) : IsConstant J F ↔ L.essImage F := by
  rw [essImage_eq_of_natIso (adj.leftAdjointUniq (constantSheafAdj J D hT))]
  exact ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

/--
lemma `isConstant_of_isIso_counit_app` / 引理 `isConstant_of_isIso_counit_app`

English:
lemma isConstant_of_isIso_counit_app
  statement: (F : Sheaf J D) [HasTerminal C]
  proof: ⟨_, ⟨asIso (constantSheafAdj J D terminalIsTerminal).counit.app F⟩⟩

中文:
引理 isConstant_of_isIso_counit_app
  结论: (F : Sheaf J D) [HasTerminal C]
  证明: ⟨_, ⟨asIso (constantSheafAdj J D terminalIsTerminal).counit.app F⟩⟩

Depends on / 依赖: constantSheafAdj, counit, counit.app, eRk_eq_eRk_union, hIX.eRk_eq_eRk_union, terminalIsTerminal, union_singleton
-/
lemma isConstant_of_isIso_counit_app (F : Sheaf J D) [HasTerminal C]
    [IsIso <| (constantSheafAdj J D terminalIsTerminal).counit.app F] : IsConstant J F where
mem_essImage := ⟨_, ⟨asIso (constantSheafAdj J D terminalIsTerminal).counit.app F⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [(constantSheaf
  signature: J D).Faithful] [(constantSheaf J D).Full] (F : Sheaf J D)
  body: by
  rw [isIso_counit_app_iff_mem_essImage]
  exact F.mem_essImage_of_isConstant

中文:
实例 [(constantSheaf
  签名: J D).Faithful] [(constantSheaf J D).Full] (F : Sheaf J D)
  定义体: by
  rw [isIso_counit_app_iff_mem_essImage]
  exact F.mem_essImage_of_isConstant

Depends on / 依赖: F.mem_essImage_of_isConstant, isIso_counit_app_iff_mem_essImage, mem_essImage_of_isConstant
-/
instance [(constantSheaf J D).Faithful] [(constantSheaf J D).Full] (F : Sheaf J D)
    [IsConstant J F] {T : C} (hT : IsTerminal T) :
    IsIso ((constantSheafAdj J D hT).counit.app F) := by
  rw [isIso_counit_app_iff_mem_essImage]
  exact F.mem_essImage_of_isConstant

/--
lemma `isConstant_iff_isIso_counit_app` / 引理 `isConstant_iff_isIso_counit_app`

English:
lemma isConstant_iff_isIso_counit_app
  statement: [(constantSheaf J D).Faithful] [(constantSheaf J D).Full]
  proof: ⟨fun _ => inferInstance, fun _ => ⟨_, ⟨asIso (constantSheafAdj J D hT).counit.app F⟩⟩⟩

中文:
引理 isConstant_iff_isIso_counit_app
  结论: [(constantSheaf J D).Faithful] [(constantSheaf J D).Full]
  证明: ⟨fun _ => inferInstance, fun _ => ⟨_, ⟨asIso (constantSheafAdj J D hT).counit.app F⟩⟩⟩

Depends on / 依赖: constantSheafAdj, counit, counit.app
-/
lemma isConstant_iff_isIso_counit_app [(constantSheaf J D).Faithful] [(constantSheaf J D).Full]
    (F : Sheaf J D) {T : C} (hT : IsTerminal T) :
      IsConstant J F ↔ (IsIso <| (constantSheafAdj J D hT).counit.app F) :=
⟨fun _ => inferInstance, fun _ => ⟨_, ⟨asIso (constantSheafAdj J D hT).counit.app F⟩⟩⟩

/--
lemma `isConstant_iff_isIso_counit_app'` / 引理 `isConstant_iff_isIso_counit_app'`

English:
lemma isConstant_iff_isIso_counit_app'
  statement: {L : D ⥤ Sheaf J D} {T : C} (hT : IsTerminal T)
  proof: (isConstant_iff_mem_essImage J hT adj F).trans (isIso_counit_app_iff_mem_essImage adj).symm

中文:
引理 isConstant_iff_isIso_counit_app'
  结论: {L : D ⥤ Sheaf J D} {T : C} (hT : IsTerminal T)
  证明: (isConstant_iff_mem_essImage J hT adj F).trans (isIso_counit_app_iff_mem_essImage adj).symm

Depends on / 依赖: isConstant_iff_mem_essImage, isIso_counit_app_iff_mem_essImage
-/
lemma isConstant_iff_isIso_counit_app' {L : D ⥤ Sheaf J D} {T : C} (hT : IsTerminal T)
    (adj : L ⊣ (sheafSections J D).obj ⟨T⟩)
    [L.Faithful] [L.Full] (F : Sheaf J D) : IsConstant J F ↔ IsIso (adj.counit.app F) :=
  (isConstant_iff_mem_essImage J hT adj F).trans (isIso_counit_app_iff_mem_essImage adj).symm

end Sheaf

section Equivalence
variable {C' : Type*} [Category* C'] (K : GrothendieckTopology C') [HasWeakSheafify K D]
variable (G : C ⥤ C') [forall (X : (C')ᵒᵖ), HasLimitsOfShape (StructuredArrow X G.op) D]
  [G.IsDenseSubsite J K] {T : C} (hT : IsTerminal T) (hT' : IsTerminal (G.obj T))

open IsDenseSubsite

variable (D) in
/--
Definition of `equivCommuteConstant` / `equivCommuteConstant` 的定义

English:
definition equivCommuteConstant
  signature: :
  body: ((constantSheafAdj J D hT).comp (sheafEquiv J K G D).toAdjunction).leftAdjointUniq
    (constantSheafAdj K D hT')

中文:
定义 equivCommuteConstant
  签名: :
  定义体: ((constantSheafAdj J D hT).comp (sheafEquiv J K G D).toAdjunction).leftAdjointUniq
    (constantSheafAdj K D hT')

Depends on / 依赖: constantSheafAdj, leftAdjointUniq, sheafEquiv, toAdjunction
-/
noncomputable def equivCommuteConstant :
    constantSheaf J D ⋙ (sheafEquiv J K G D).functor ≅ constantSheaf K D :=
  ((constantSheafAdj J D hT).comp (sheafEquiv J K G D).toAdjunction).leftAdjointUniq
    (constantSheafAdj K D hT')

variable (D) in
/--
Definition of `equivCommuteConstant'` / `equivCommuteConstant'` 的定义

English:
definition equivCommuteConstant'
  signature: :
  body: isoWhiskerLeft (constantSheaf J D) (sheafEquiv J K G D).unitIso ≪≫
    isoWhiskerRight (equivCommuteConstant J D K G hT hT') (sheafEquiv J K G D).inverse

中文:
定义 equivCommuteConstant'
  签名: :
  定义体: isoWhiskerLeft (constantSheaf J D) (sheafEquiv J K G D).unitIso ≪≫
    isoWhiskerRight (equivCommuteConstant J D K G hT hT') (sheafEquiv J K G D).inverse

Depends on / 依赖: constantSheaf, equivCommuteConstant, inverse, isoWhiskerLeft, isoWhiskerRight, sheafEquiv, unitIso
-/
noncomputable def equivCommuteConstant' :
    constantSheaf J D ≅ constantSheaf K D ⋙ (sheafEquiv J K G D).inverse :=
  isoWhiskerLeft (constantSheaf J D) (sheafEquiv J K G D).unitIso ≪≫
    isoWhiskerRight (equivCommuteConstant J D K G hT hT') (sheafEquiv J K G D).inverse

/- TODO: find suitable assumptions for proving generalizations of `equivCommuteConstant` and
`equivCommuteConstant'` above, to commute `constantSheaf` with pullback/pushforward of sheaves. -/

include hT hT' in
/--
lemma `Sheaf.isConstant_iff_of_equivalence` / 引理 `Sheaf.isConstant_iff_of_equivalence`

English:
lemma Sheaf.isConstant_iff_of_equivalence
  given: (F : Sheaf K D)
  proof: by
  constructor
  · exact fun ⟨Y, ⟨i⟩⟩ => ⟨_, ⟨(equivCommuteConstant J D K G hT hT').symm.app _ ≪≫
      (sheafEquiv J K G D).functor.mapIso i ≪≫ (sheafEquiv J K G D).counitIso.app _⟩⟩
  · exact fun ⟨Y, ⟨i⟩⟩ => ⟨_, ⟨(equivCommuteConstant' J D K G hT hT').app _ ≪≫
      (sheafEquiv J K G D).inverse.

中文:
引理 Sheaf.isConstant_iff_of_equivalence
  条件: (F : Sheaf K D)
  证明: by
  constructor
  · exact fun ⟨Y, ⟨i⟩⟩ => ⟨_, ⟨(equivCommuteConstant J D K G hT hT').symm.app _ ≪≫
      (sheafEquiv J K G D).functor.mapIso i ≪≫ (sheafEquiv J K G D).counitIso.app _⟩⟩
  · exact fun ⟨Y, ⟨i⟩⟩ => ⟨_, ⟨(equivCommuteConstant' J D K G hT hT').app _ ≪≫
      (sheafEquiv J K G D).inverse.

Depends on / 依赖: counitIso, counitIso.app, equivCommuteConstant, functor, functor.mapIso, inverse, inverse.mapIso, mapIso, sheafEquiv, symm.app
-/
lemma Sheaf.isConstant_iff_of_equivalence (F : Sheaf K D) :
    ((sheafEquiv J K G D).inverse.obj F).IsConstant J ↔ IsConstant K F := by
  constructor
  · exact fun ⟨Y, ⟨i⟩⟩ => ⟨_, ⟨(equivCommuteConstant J D K G hT hT').symm.app _ ≪≫
      (sheafEquiv J K G D).functor.mapIso i ≪≫ (sheafEquiv J K G D).counitIso.app _⟩⟩
  · exact fun ⟨Y, ⟨i⟩⟩ => ⟨_, ⟨(equivCommuteConstant' J D K G hT hT').app _ ≪≫
      (sheafEquiv J K G D).inverse.mapIso i⟩⟩

end Equivalence

section Forget

variable {B : Type*} [Category* B] (U : D ⥤ B) [HasWeakSheafify J B]
  [J.PreservesSheafification U] [J.HasSheafCompose U] (F : Sheaf J D)

/--
Definition of `constantCommuteCompose` / `constantCommuteCompose` 的定义

English:
definition constantCommuteCompose
  signature: :
  body: (isoWhiskerLeft (const Cᵒᵖ)
    (sheafComposeNatIso J U (sheafificationAdjunction J D) (sheafificationAdjunction J B)).symm) ≪≫
      isoWhiskerRight (compConstIso _ _).symm _

中文:
定义 constantCommuteCompose
  签名: :
  定义体: (isoWhiskerLeft (const Cᵒᵖ)
    (sheafComposeNatIso J U (sheafificationAdjunction J D) (sheafificationAdjunction J B)).symm) ≪≫
      isoWhiskerRight (compConstIso _ _).symm _

Depends on / 依赖: compConstIso, isoWhiskerLeft, isoWhiskerRight, sheafComposeNatIso, sheafificationAdjunction
-/
noncomputable def constantCommuteCompose :
    constantSheaf J D ⋙ sheafCompose J U ≅ U ⋙ constantSheaf J B :=
  (isoWhiskerLeft (const Cᵒᵖ)
    (sheafComposeNatIso J U (sheafificationAdjunction J D) (sheafificationAdjunction J B)).symm) ≪≫
      isoWhiskerRight (compConstIso _ _).symm _

/--
lemma `constantCommuteCompose_hom_app_hom` / 引理 `constantCommuteCompose_hom_app_hom`

English:
lemma constantCommuteCompose_hom_app_hom
  given: (X : D)
  statement: ((constantCommuteCompose J U).hom.app X).hom =
  proof: rfl

@[deprecated (since := "2026-03-05")]
alias constantCommuteCompose_hom_app_val := constantCommuteCompose_hom_app_hom

中文:
引理 constantCommuteCompose_hom_app_hom
  条件: (X : D)
  结论: ((constantCommuteCompose J U).hom.app X).hom =
  证明: rfl

@[deprecated (since := "2026-03-05")]
alias constantCommuteCompose_hom_app_val := constantCommuteCompose_hom_app_hom
-/
lemma constantCommuteCompose_hom_app_hom (X : D) : ((constantCommuteCompose J U).hom.app X).hom =
    (sheafifyComposeIso J U ((const Cᵒᵖ).obj X)).inv ≫ sheafifyMap J (constComp Cᵒᵖ X U).hom := rfl

@[deprecated (since := "2026-03-05")]
alias constantCommuteCompose_hom_app_val := constantCommuteCompose_hom_app_hom

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `constantSheafAdj_counit_w` / 引理 `constantSheafAdj_counit_w`

English:
lemma constantSheafAdj_counit_w
  given: {T : C} (hT : IsTerminal T)
  proof: by
  apply Sheaf.hom_ext
  dsimp
  rw [constantCommuteCompose_hom_app_hom]; rw [assoc]; rw [Iso.inv_comp_eq]
  apply sheafify_hom_ext _ _ _ ((sheafCompose J U).obj F).property
  ext x
  simp [NatTrans.comp_app] -- simp [NatTrans.comp_app] to unfold some definitions
  simp [← map_comp, ← NatTrans.com

中文:
引理 constantSheafAdj_counit_w
  条件: {T : C} (hT : IsTerminal T)
  证明: by
  apply Sheaf.hom_ext
  dsimp
  rw [constantCommuteCompose_hom_app_hom]; rw [assoc]; rw [Iso.inv_comp_eq]
  apply sheafify_hom_ext _ _ _ ((sheafCompose J U).obj F).property
  ext x
  simp [NatTrans.comp_app] -- simp [NatTrans.comp_app] to unfold some definitions
  simp [← map_comp, ← NatTrans.com

Depends on / 依赖: Iso.inv_comp_eq, NatTrans, NatTrans.comp_app, Sheaf.hom_ext, comp_app, compositions, constantCommuteCompose_hom_app_hom, definitions, hom_ext, inv_comp_eq, map_comp, property, sheafCompose, sheafify_hom_ext, simplify
-/
lemma constantSheafAdj_counit_w {T : C} (hT : IsTerminal T) :
    ((constantCommuteCompose J U).hom.app (F.obj.obj ⟨T⟩)) ≫
      ((constantSheafAdj J B hT).counit.app ((sheafCompose J U).obj F)) =
        ((sheafCompose J U).map ((constantSheafAdj J D hT).counit.app F)) := by
  apply Sheaf.hom_ext
  dsimp
  rw [constantCommuteCompose_hom_app_hom]; rw [assoc]; rw [Iso.inv_comp_eq]
  apply sheafify_hom_ext _ _ _ ((sheafCompose J U).obj F).property
  ext x
  simp [NatTrans.comp_app] -- simp [NatTrans.comp_app] to unfold some definitions
  simp [← map_comp, ← NatTrans.comp_app] -- simp [← NatTrans.comp_app] to simplify some compositions

set_option backward.isDefEq.respectTransparency false in
/--
lemma `Sheaf.isConstant_of_forget` / 引理 `Sheaf.isConstant_of_forget`

English:
lemma Sheaf.isConstant_of_forget
  statement: [constantSheaf J D |>.Faithful] [constantSheaf J D |>.Full]
  proof: by
  have : IsIso ((sheafCompose J U).map ((constantSheafAdj J D hT).counit.app F)) := by
    rw [← constantSheafAdj_counit_w]
    infer_instance
  rw [F.isConstant_iff_isIso_counit_app (hT := hT)]
  exact isIso_of_reflects_iso _ (sheafCompose J U)

中文:
引理 Sheaf.isConstant_of_forget
  结论: [constantSheaf J D |>.Faithful] [constantSheaf J D |>.Full]
  证明: by
  have : IsIso ((sheafCompose J U).map ((constantSheafAdj J D hT).counit.app F)) := by
    rw [← constantSheafAdj_counit_w]
    infer_instance
  rw [F.isConstant_iff_isIso_counit_app (hT := hT)]
  exact isIso_of_reflects_iso _ (sheafCompose J U)

Depends on / 依赖: F.isConstant_iff_isIso_counit_app, constantSheafAdj, constantSheafAdj_counit_w, counit, counit.app, infer_instance, isConstant_iff_isIso_counit_app, isIso_of_reflects_iso, sheafCompose
-/
lemma Sheaf.isConstant_of_forget [constantSheaf J D |>.Faithful] [constantSheaf J D |>.Full]
    [constantSheaf J B |>.Faithful] [constantSheaf J B |>.Full]
    [(sheafCompose J U).ReflectsIsomorphisms] [((sheafCompose J U).obj F).IsConstant J]
    {T : C} (hT : IsTerminal T) : F.IsConstant J := by
  have : IsIso ((sheafCompose J U).map ((constantSheafAdj J D hT).counit.app F)) := by
    rw [← constantSheafAdj_counit_w]
    infer_instance
  rw [F.isConstant_iff_isIso_counit_app (hT := hT)]
  exact isIso_of_reflects_iso _ (sheafCompose J U)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [h
  signature: : F.IsConstant J] : ((sheafCompose J U).obj F).IsConstant J
  body: by
  obtain ⟨Y, ⟨i⟩⟩ := h
  exact ⟨U.obj Y, ⟨(fullyFaithfulSheafToPresheaf _ _).preimageIso
    (((sheafifyComposeIso J U ((const Cᵒᵖ).obj Y)).symm ≪≫
      (presheafToSheaf J B ⋙ sheafToPresheaf J B).mapIso (constComp Cᵒᵖ Y U)).symm ≪≫
        (sheafToPresheaf _ _).mapIso ((sheafCompose J U).mapIso

中文:
实例 [h
  签名: : F.IsConstant J] : ((sheafCompose J U).obj F).IsConstant J
  定义体: by
  obtain ⟨Y, ⟨i⟩⟩ := h
  exact ⟨U.obj Y, ⟨(fullyFaithfulSheafToPresheaf _ _).preimageIso
    (((sheafifyComposeIso J U ((const Cᵒᵖ).obj Y)).symm ≪≫
      (presheafToSheaf J B ⋙ sheafToPresheaf J B).mapIso (constComp Cᵒᵖ Y U)).symm ≪≫
        (sheafToPresheaf _ _).mapIso ((sheafCompose J U).mapIso

Depends on / 依赖: U.obj, constComp, fullyFaithfulSheafToPresheaf, mapIso, preimageIso, presheafToSheaf, sheafCompose, sheafToPresheaf, sheafifyComposeIso
-/
instance [h : F.IsConstant J] : ((sheafCompose J U).obj F).IsConstant J := by
  obtain ⟨Y, ⟨i⟩⟩ := h
  exact ⟨U.obj Y, ⟨(fullyFaithfulSheafToPresheaf _ _).preimageIso
    (((sheafifyComposeIso J U ((const Cᵒᵖ).obj Y)).symm ≪≫
      (presheafToSheaf J B ⋙ sheafToPresheaf J B).mapIso (constComp Cᵒᵖ Y U)).symm ≪≫
        (sheafToPresheaf _ _).mapIso ((sheafCompose J U).mapIso i))⟩⟩

/--
lemma `Sheaf.isConstant_iff_forget` / 引理 `Sheaf.isConstant_iff_forget`

English:
lemma Sheaf.isConstant_iff_forget
  statement: [constantSheaf J D |>.Faithful] [constantSheaf J D |>.Full]
  proof: ⟨fun _ => inferInstance, fun _ => Sheaf.isConstant_of_forget _ U F hT⟩

中文:
引理 Sheaf.isConstant_iff_forget
  结论: [constantSheaf J D |>.Faithful] [constantSheaf J D |>.Full]
  证明: ⟨fun _ => inferInstance, fun _ => Sheaf.isConstant_of_forget _ U F hT⟩

Depends on / 依赖: Sheaf.isConstant_of_forget, isConstant_of_forget
-/
lemma Sheaf.isConstant_iff_forget [constantSheaf J D |>.Faithful] [constantSheaf J D |>.Full]
    [constantSheaf J B |>.Faithful] [constantSheaf J B |>.Full]
      [(sheafCompose J U).ReflectsIsomorphisms] {T : C} (hT : IsTerminal T) :
        F.IsConstant J ↔ ((sheafCompose J U).obj F).IsConstant J :=
  ⟨fun _ => inferInstance, fun _ => Sheaf.isConstant_of_forget _ U F hT⟩

end Forget

end CategoryTheory
