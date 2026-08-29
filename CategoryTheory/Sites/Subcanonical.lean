/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Limits.Shapes.DisjointCoproduct
public import Mathlib.CategoryTheory.Sites.Continuous
/-!

# Subcanonical Grothendieck topologies

This file provides some API for the Yoneda embedding into the category of sheaves for a
subcanonical Grothendieck topology.
-/

@[expose] public section

universe v' v u

namespace CategoryTheory.GrothendieckTopology

open Opposite CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) [Subcanonical J]

/--
Definition of `yonedaEquiv` / `yonedaEquiv` 的定义

English:
definition yonedaEquiv
  signature: {X : C} {F : Sheaf J (Type v)}
  body: (fullyFaithfulSheafToPresheaf _ _).homEquiv.trans CategoryTheory.yonedaEquiv

中文:
定义 yonedaEquiv
  签名: {X : C} {F : 层 J (类型v)}
  定义体: (fullyFaithfulSheafToPresheaf _ _).homEquiv.trans CategoryTheory.yonedaEquiv

Depends on / 依赖: CategoryTheory, CategoryTheory.yonedaEquiv, fullyFaithfulSheafToPresheaf, homEquiv, homEquiv.trans, yonedaEquiv
-/
def yonedaEquiv {X : C} {F : Sheaf J (Type v)} : (J.yoneda.obj X ⟶ F) ≃ F.obj.obj (op X) :=
  (fullyFaithfulSheafToPresheaf _ _).homEquiv.trans CategoryTheory.yonedaEquiv

/--
theorem `yonedaEquiv_apply` / 定理 `yonedaEquiv_apply`

English:
theorem yonedaEquiv_apply
  given: {X : C} {F : Sheaf J (Type v)} (f : J.yoneda.obj X ⟶ F)
  proof: rfl

@[simp]

中文:
定理 yonedaEquiv_apply
  条件: {X : C} {F : 层 J (类型v)} (f : J.yoneda.obj X ⟶ F)
  证明: rfl

@[simp]
-/
theorem yonedaEquiv_apply {X : C} {F : Sheaf J (Type v)} (f : J.yoneda.obj X ⟶ F) :
    yonedaEquiv J f = f.hom.app (op X) (𝟙 X) :=
  rfl

@[simp]
/--
theorem `yonedaEquiv_symm_app_apply` / 定理 `yonedaEquiv_symm_app_apply`

English:
theorem yonedaEquiv_symm_app_apply
  statement: {X : C} {F : Sheaf J (Type v)} (x : F.obj.obj (op X))
  proof: rfl

中文:
定理 yonedaEquiv_symm_app_apply
  结论: {X : C} {F : 层 J (类型v)} (x : F.obj.obj (op X))
  证明: rfl
-/
theorem yonedaEquiv_symm_app_apply {X : C} {F : Sheaf J (Type v)} (x : F.obj.obj (op X))
    (Y : Cᵒᵖ) (f : Y.unop ⟶ X) : dsimp% (J.yonedaEquiv.symm x).hom.app Y f = F.obj.map f.op x :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `yonedaEquiv_naturality` / 引理 `yonedaEquiv_naturality`

English:
lemma yonedaEquiv_naturality
  statement: {X Y : C} {F : Sheaf J (Type v)} (f : J.yoneda.obj X ⟶ F)
  proof: by
  simp [yonedaEquiv, CategoryTheory.yonedaEquiv_naturality]
  rfl

中文:
引理 yonedaEquiv_naturality
  结论: {X Y : C} {F : 层 J (类型v)} (f : J.yoneda.obj X ⟶ F)
  证明: by
  simp [yonedaEquiv, CategoryTheory.yonedaEquiv_naturality]
  rfl

Depends on / 依赖: CategoryTheory, CategoryTheory.yonedaEquiv_naturality, yonedaEquiv, yonedaEquiv_naturality
-/
lemma yonedaEquiv_naturality {X Y : C} {F : Sheaf J (Type v)} (f : J.yoneda.obj X ⟶ F)
    (g : Y ⟶ X) : F.obj.map g.op (J.yonedaEquiv f) = J.yonedaEquiv (J.yoneda.map g ≫ f) := by
  simp [yonedaEquiv, CategoryTheory.yonedaEquiv_naturality]
  rfl

/--
lemma `yonedaEquiv_naturality'` / 引理 `yonedaEquiv_naturality'`

English:
lemma yonedaEquiv_naturality'
  statement: {X Y : Cᵒᵖ} {F : Sheaf J (Type v)} (f : J.yoneda.obj (unop X) ⟶ F)
  proof: J.yonedaEquiv_naturality _ _

中文:
引理 yonedaEquiv_naturality'
  结论: {X Y : Cᵒᵖ} {F : 层 J (类型v)} (f : J.yoneda.obj (unop X) ⟶ F)
  证明: J.yonedaEquiv_naturality _ _

Depends on / 依赖: J.yonedaEquiv_naturality, yonedaEquiv_naturality
-/
lemma yonedaEquiv_naturality' {X Y : Cᵒᵖ} {F : Sheaf J (Type v)} (f : J.yoneda.obj (unop X) ⟶ F)
    (g : X ⟶ Y) : F.obj.map g (J.yonedaEquiv f) = J.yonedaEquiv (J.yoneda.map g.unop ≫ f) :=
  J.yonedaEquiv_naturality _ _

/--
lemma `yonedaEquiv_comp` / 引理 `yonedaEquiv_comp`

English:
lemma yonedaEquiv_comp
  given: {X : C} {F G : Sheaf J (Type v)} (α : J.yoneda.obj X ⟶ F) (β : F ⟶ G)
  proof: rfl

中文:
引理 yonedaEquiv_comp
  条件: {X : C} {F G : 层 J (类型v)} (α : J.yoneda.obj X ⟶ F) (β : F ⟶ G)
  证明: rfl
-/
lemma yonedaEquiv_comp {X : C} {F G : Sheaf J (Type v)} (α : J.yoneda.obj X ⟶ F) (β : F ⟶ G) :
    J.yonedaEquiv (α ≫ β) = β.hom.app _ (J.yonedaEquiv α) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
lemma `yonedaEquiv_yoneda_map` / 引理 `yonedaEquiv_yoneda_map`

English:
lemma yonedaEquiv_yoneda_map
  given: {X Y : C} (f : X ⟶ Y)
  statement: J.yonedaEquiv (J.yoneda.map f) = f
  proof: by
  rw [yonedaEquiv_apply]
  simp

中文:
引理 yonedaEquiv_yoneda_map
  条件: {X Y : C} (f : X ⟶ Y)
  结论: J.yonedaEquiv (J.yoneda.map f) = f
  证明: by
  rw [yonedaEquiv_apply]
  simp

Depends on / 依赖: yonedaEquiv_apply
-/
lemma yonedaEquiv_yoneda_map {X Y : C} (f : X ⟶ Y) : J.yonedaEquiv (J.yoneda.map f) = f := by
  rw [yonedaEquiv_apply]
  simp

set_option backward.defeqAttrib.useBackward true in
/--
lemma `yonedaEquiv_symm_naturality_left` / 引理 `yonedaEquiv_symm_naturality_left`

English:
lemma yonedaEquiv_symm_naturality_left
  statement: {X X' : C} (f : X' ⟶ X) (F : Sheaf J (Type v))
  proof: by
  apply J.yonedaEquiv.injective
  rw [yonedaEquiv_comp]; rw [yonedaEquiv_yoneda_map]
  simp
  rfl

中文:
引理 yonedaEquiv_symm_naturality_left
  结论: {X X' : C} (f : X' ⟶ X) (F : 层 J (类型v))
  证明: by
  apply J.yonedaEquiv.injective
  rw [yonedaEquiv_comp]; rw [yonedaEquiv_yoneda_map]
  simp
  rfl

Depends on / 依赖: J.yonedaEquiv.injective, injective, yonedaEquiv, yonedaEquiv_comp, yonedaEquiv_yoneda_map
-/
lemma yonedaEquiv_symm_naturality_left {X X' : C} (f : X' ⟶ X) (F : Sheaf J (Type v))
    (x : F.obj.obj ⟨X⟩) : J.yoneda.map f ≫ J.yonedaEquiv.symm x = J.yonedaEquiv.symm
      ((F.obj.map f.op) x) := by
  apply J.yonedaEquiv.injective
  rw [yonedaEquiv_comp]; rw [yonedaEquiv_yoneda_map]
  simp
  rfl

/--
lemma `yonedaEquiv_symm_naturality_right` / 引理 `yonedaEquiv_symm_naturality_right`

English:
lemma yonedaEquiv_symm_naturality_right
  statement: (X : C) {F F' : Sheaf J (Type v)} (f : F ⟶ F')
  proof: by
  apply J.yonedaEquiv.injective
  simp [yonedaEquiv_comp]

中文:
引理 yonedaEquiv_symm_naturality_right
  结论: (X : C) {F F' : 层 J (类型v)} (f : F ⟶ F')
  证明: by
  apply J.yonedaEquiv.injective
  simp [yonedaEquiv_comp]

Depends on / 依赖: J.yonedaEquiv.injective, injective, yonedaEquiv, yonedaEquiv_comp
-/
lemma yonedaEquiv_symm_naturality_right (X : C) {F F' : Sheaf J (Type v)} (f : F ⟶ F')
    (x : F.obj.obj ⟨X⟩) : J.yonedaEquiv.symm x ≫ f = J.yonedaEquiv.symm (f.hom.app ⟨X⟩ x) := by
  apply J.yonedaEquiv.injective
  simp [yonedaEquiv_comp]

/--
lemma `map_yonedaEquiv` / 引理 `map_yonedaEquiv`

English:
lemma map_yonedaEquiv
  statement: {X Y : C} {F : Sheaf J (Type v)} (f : J.yoneda.obj X ⟶ F)
  proof: by
  rw [yonedaEquiv_naturality]; rw [yonedaEquiv_comp]; rw [yonedaEquiv_yoneda_map]

中文:
引理 map_yonedaEquiv
  结论: {X Y : C} {F : 层 J (类型v)} (f : J.yoneda.obj X ⟶ F)
  证明: by
  rw [yonedaEquiv_naturality]; rw [yonedaEquiv_comp]; rw [yonedaEquiv_yoneda_map]

Depends on / 依赖: yonedaEquiv_comp, yonedaEquiv_naturality, yonedaEquiv_yoneda_map
-/
lemma map_yonedaEquiv {X Y : C} {F : Sheaf J (Type v)} (f : J.yoneda.obj X ⟶ F)
    (g : Y ⟶ X) : F.obj.map g.op (J.yonedaEquiv f) = f.hom.app (op Y) g := by
  rw [yonedaEquiv_naturality]; rw [yonedaEquiv_comp]; rw [yonedaEquiv_yoneda_map]

/--
lemma `map_yonedaEquiv'` / 引理 `map_yonedaEquiv'`

English:
lemma map_yonedaEquiv'
  statement: {X Y : Cᵒᵖ} {F : Sheaf J (Type v)} (f : J.yoneda.obj (unop X) ⟶ F)
  proof: by
  rw [yonedaEquiv_naturality']; rw [yonedaEquiv_comp]; rw [yonedaEquiv_yoneda_map]

中文:
引理 map_yonedaEquiv'
  结论: {X Y : Cᵒᵖ} {F : 层 J (类型v)} (f : J.yoneda.obj (unop X) ⟶ F)
  证明: by
  rw [yonedaEquiv_naturality']; rw [yonedaEquiv_comp]; rw [yonedaEquiv_yoneda_map]

Depends on / 依赖: yonedaEquiv_comp, yonedaEquiv_naturality, yonedaEquiv_yoneda_map
-/
lemma map_yonedaEquiv' {X Y : Cᵒᵖ} {F : Sheaf J (Type v)} (f : J.yoneda.obj (unop X) ⟶ F)
    (g : X ⟶ Y) : F.obj.map g (J.yonedaEquiv f) = f.hom.app Y g.unop := by
  rw [yonedaEquiv_naturality']; rw [yonedaEquiv_comp]; rw [yonedaEquiv_yoneda_map]

/--
lemma `yonedaEquiv_symm_map` / 引理 `yonedaEquiv_symm_map`

English:
lemma yonedaEquiv_symm_map
  given: {X Y : Cᵒᵖ} (f : X ⟶ Y) {F : Sheaf J (Type v)} (t : F.obj.obj X)
  proof: by
  obtain ⟨u, rfl⟩ := J.yonedaEquiv.surjective t
  rw [yonedaEquiv_naturality']; rw [Equiv.symm_apply_apply]; rw [Equiv.symm_apply_apply]

中文:
引理 yonedaEquiv_symm_map
  条件: {X Y : Cᵒᵖ} (f : X ⟶ Y) {F : 层 J (类型v)} (t : F.obj.obj X)
  证明: by
  obtain ⟨u, rfl⟩ := J.yonedaEquiv.surjective t
  rw [yonedaEquiv_naturality']; rw [Equiv.symm_apply_apply]; rw [Equiv.symm_apply_apply]

Depends on / 依赖: Equiv.symm_apply_apply, J.yonedaEquiv.surjective, surjective, symm_apply_apply, yonedaEquiv, yonedaEquiv_naturality
-/
lemma yonedaEquiv_symm_map {X Y : Cᵒᵖ} (f : X ⟶ Y) {F : Sheaf J (Type v)} (t : F.obj.obj X) :
    J.yonedaEquiv.symm (F.obj.map f t) = J.yoneda.map f.unop ≫ J.yonedaEquiv.symm t := by
  obtain ⟨u, rfl⟩ := J.yonedaEquiv.surjective t
  rw [yonedaEquiv_naturality']; rw [Equiv.symm_apply_apply]; rw [Equiv.symm_apply_apply]

/--
lemma `hom_ext_yoneda` / 引理 `hom_ext_yoneda`

English:
lemma hom_ext_yoneda
  statement: {P Q : Sheaf J (Type v)} {f g : P ⟶ Q}
  proof: by
  ext X x
  simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply]
    using! congr_arg (J.yonedaEquiv) (h _ (J.yonedaEquiv.symm x))

#adaptation_note

中文:
引理 hom_ext_yoneda
  结论: {P Q : 层 J (类型v)} {f g : P ⟶ Q}
  证明: by
  ext X x
  simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply]
    using! congr_arg (J.yonedaEquiv) (h _ (J.yonedaEquiv.symm x))

#adaptation_note

Depends on / 依赖: Equiv.apply_symm_apply, J.yonedaEquiv, J.yonedaEquiv.symm, apply_symm_apply, congr_arg, yonedaEquiv, yonedaEquiv_comp
-/
lemma hom_ext_yoneda {P Q : Sheaf J (Type v)} {f g : P ⟶ Q}
    (h : forall (X : C) (p : J.yoneda.obj X ⟶ P), p ≫ f = p ≫ g) :
    f = g := by
  ext X x
  simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply]
    using! congr_arg (J.yonedaEquiv) (h _ (J.yonedaEquiv.symm x))

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The Yoneda lemma for sheaves. -/
@[simps! +dsimpLhs hom_app_app_hom_apply_down inv_app_app]
/--
Definition of `yonedaOpCompCoyoneda` / `yonedaOpCompCoyoneda` 的定义

English:
definition yonedaOpCompCoyoneda
  signature: :
  body: ((isoWhiskerLeft _ sheafToPresheafCompCoyonedaCompWhiskeringLeftSheafToPresheaf.symm).trans
    (isoWhiskerRight (NatIso.op J.yonedaCompSheafToPresheaf.symm)
    (_ ⋙ (whiskeringLeft _ _ _).obj _))).trans
    (isoWhiskerRight CategoryTheory.largeCurriedYonedaLemma ((whiskeringLeft _ _ _).obj _))

中文:
定义 yonedaOpCompCoyoneda
  签名: :
  定义体: ((isoWhiskerLeft _ sheafToPresheafCompCoyonedaCompWhiskeringLeftSheafToPresheaf.symm).trans
    (isoWhiskerRight (NatIso.op J.yonedaCompSheafToPresheaf.symm)
    (_ ⋙ (whiskeringLeft _ _ _).obj _))).trans
    (isoWhiskerRight CategoryTheory.largeCurriedYonedaLemma ((whiskeringLeft _ _ _).obj _))

Depends on / 依赖: CategoryTheory, CategoryTheory.largeCurriedYonedaLemma, J.yonedaCompSheafToPresheaf.symm, NatIso, NatIso.op, isoWhiskerLeft, isoWhiskerRight, largeCurriedYonedaLemma, sheafToPresheafCompCoyonedaCompWhiskeringLeftSheafToPresheaf, sheafToPresheafCompCoyonedaCompWhiskeringLeftSheafToPresheaf.symm, whiskeringLeft, yonedaCompSheafToPresheaf
-/
def yonedaOpCompCoyoneda :
    J.yoneda.op ⋙ coyoneda ≅
      evaluation Cᵒᵖ (Type v) ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u} ⋙
      (whiskeringLeft _ _ _).obj (sheafToPresheaf _ _) :=
  ((isoWhiskerLeft _ sheafToPresheafCompCoyonedaCompWhiskeringLeftSheafToPresheaf.symm).trans
    (isoWhiskerRight (NatIso.op J.yonedaCompSheafToPresheaf.symm)
    (_ ⋙ (whiskeringLeft _ _ _).obj _))).trans
    (isoWhiskerRight CategoryTheory.largeCurriedYonedaLemma ((whiskeringLeft _ _ _).obj _))

/--
Definition of `uliftYonedaEquiv` / `uliftYonedaEquiv` 的定义

English:
definition uliftYonedaEquiv
  signature: {X : C} {F : Sheaf J (Type (max v v'))}
  body: (fullyFaithfulSheafToPresheaf _ _).homEquiv.trans CategoryTheory.uliftYonedaEquiv

中文:
定义 uliftYonedaEquiv
  签名: {X : C} {F : 层 J (类型 (最大值 v v'))}
  定义体: (fullyFaithfulSheafToPresheaf _ _).homEquiv.trans CategoryTheory.uliftYonedaEquiv

Depends on / 依赖: CategoryTheory, CategoryTheory.uliftYonedaEquiv, fullyFaithfulSheafToPresheaf, homEquiv, homEquiv.trans, uliftYonedaEquiv
-/
def uliftYonedaEquiv {X : C} {F : Sheaf J (Type (max v v'))} :
    ((uliftYoneda.{v'} J).obj X ⟶ F) ≃ F.obj.obj (op X) :=
  (fullyFaithfulSheafToPresheaf _ _).homEquiv.trans CategoryTheory.uliftYonedaEquiv

/--
theorem `uliftYonedaEquiv_apply` / 定理 `uliftYonedaEquiv_apply`

English:
theorem uliftYonedaEquiv_apply
  statement: {X : C} {F : Sheaf J (Type (max v v'))}
  proof: rfl

@[simp]

中文:
定理 uliftYonedaEquiv_apply
  结论: {X : C} {F : 层 J (类型 (最大值 v v'))}
  证明: rfl

@[simp]
-/
theorem uliftYonedaEquiv_apply {X : C} {F : Sheaf J (Type (max v v'))}
    (f : J.uliftYoneda.obj X ⟶ F) : uliftYonedaEquiv.{v'} J f = f.hom.app (op X) ⟨𝟙 X⟩ :=
  rfl

@[simp]
/--
theorem `uliftYonedaEquiv_symm_app_apply` / 定理 `uliftYonedaEquiv_symm_app_apply`

English:
theorem uliftYonedaEquiv_symm_app_apply
  statement: {X : C} {F : Sheaf J (Type (max v v'))}
  proof: rfl

中文:
定理 uliftYonedaEquiv_symm_app_apply
  结论: {X : C} {F : 层 J (类型 (最大值 v v'))}
  证明: rfl
-/
theorem uliftYonedaEquiv_symm_app_apply {X : C} {F : Sheaf J (Type (max v v'))}
    (x : F.obj.obj (op X)) (Y : Cᵒᵖ) (f : Y.unop ⟶ X) :
    dsimp% (J.uliftYonedaEquiv.symm x).hom.app Y ⟨f⟩ = F.obj.map f.op x :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `uliftYonedaEquiv_naturality` / 引理 `uliftYonedaEquiv_naturality`

English:
lemma uliftYonedaEquiv_naturality
  statement: {X Y : C} {F : Sheaf J (Type (max v v'))}
  proof: by
  change (f.hom.app (op X) ≫ F.obj.map g.op) ⟨𝟙 X⟩ = f.hom.app (op Y) ⟨𝟙 Y ≫ g⟩
  rw [← f.hom.naturality]
  simp [uliftYoneda]

中文:
引理 uliftYonedaEquiv_naturality
  结论: {X Y : C} {F : 层 J (类型 (最大值 v v'))}
  证明: by
  change (f.hom.app (op X) ≫ F.obj.map g.op) ⟨𝟙 X⟩ = f.hom.app (op Y) ⟨𝟙 Y ≫ g⟩
  rw [← f.hom.naturality]
  simp [uliftYoneda]

Depends on / 依赖: F.obj.map, f.hom.app, f.hom.naturality, g.op, naturality, uliftYoneda
-/
lemma uliftYonedaEquiv_naturality {X Y : C} {F : Sheaf J (Type (max v v'))}
    (f : J.uliftYoneda.obj X ⟶ F) (g : Y ⟶ X) :
      F.obj.map g.op (J.uliftYonedaEquiv f) = J.uliftYonedaEquiv (J.uliftYoneda.map g ≫ f) := by
  change (f.hom.app (op X) ≫ F.obj.map g.op) ⟨𝟙 X⟩ = f.hom.app (op Y) ⟨𝟙 Y ≫ g⟩
  rw [← f.hom.naturality]
  simp [uliftYoneda]

/--
lemma `uliftYonedaEquiv_naturality'` / 引理 `uliftYonedaEquiv_naturality'`

English:
lemma uliftYonedaEquiv_naturality'
  statement: {X Y : Cᵒᵖ} {F : Sheaf J (Type (max v v'))}
  proof: J.uliftYonedaEquiv_naturality _ _

中文:
引理 uliftYonedaEquiv_naturality'
  结论: {X Y : Cᵒᵖ} {F : 层 J (类型 (最大值 v v'))}
  证明: J.uliftYonedaEquiv_naturality _ _

Depends on / 依赖: J.uliftYonedaEquiv_naturality, uliftYonedaEquiv_naturality
-/
lemma uliftYonedaEquiv_naturality' {X Y : Cᵒᵖ} {F : Sheaf J (Type (max v v'))}
    (f : J.uliftYoneda.obj (unop X) ⟶ F) (g : X ⟶ Y) :
    F.obj.map g (J.uliftYonedaEquiv f) = J.uliftYonedaEquiv (J.uliftYoneda.map g.unop ≫ f) :=
  J.uliftYonedaEquiv_naturality _ _

/--
lemma `uliftYonedaEquiv_comp` / 引理 `uliftYonedaEquiv_comp`

English:
lemma uliftYonedaEquiv_comp
  statement: {X : C} {F G : Sheaf J (Type (max v v'))} (α : J.uliftYoneda.obj X ⟶ F)
  proof: rfl

中文:
引理 uliftYonedaEquiv_comp
  结论: {X : C} {F G : 层 J (类型 (最大值 v v'))} (α : J.uliftYoneda.obj X ⟶ F)
  证明: rfl
-/
lemma uliftYonedaEquiv_comp {X : C} {F G : Sheaf J (Type (max v v'))} (α : J.uliftYoneda.obj X ⟶ F)
    (β : F ⟶ G) : J.uliftYonedaEquiv (α ≫ β) = β.hom.app _ (J.uliftYonedaEquiv α) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
lemma `uliftYonedaEquiv_uliftYoneda_map` / 引理 `uliftYonedaEquiv_uliftYoneda_map`

English:
lemma uliftYonedaEquiv_uliftYoneda_map
  given: {X Y : C} (f : X ⟶ Y)
  proof: by
  rw [uliftYonedaEquiv_apply]
  simp [uliftYoneda]

中文:
引理 uliftYonedaEquiv_uliftYoneda_map
  条件: {X Y : C} (f : X ⟶ Y)
  证明: by
  rw [uliftYonedaEquiv_apply]
  simp [uliftYoneda]

Depends on / 依赖: uliftYoneda, uliftYonedaEquiv_apply
-/
lemma uliftYonedaEquiv_uliftYoneda_map {X Y : C} (f : X ⟶ Y) :
    (uliftYonedaEquiv.{v'} J) (J.uliftYoneda.map f) = ⟨f⟩ := by
  rw [uliftYonedaEquiv_apply]
  simp [uliftYoneda]

/--
lemma `uliftYonedaEquiv_symm_naturality_left` / 引理 `uliftYonedaEquiv_symm_naturality_left`

English:
lemma uliftYonedaEquiv_symm_naturality_left
  statement: {X X' : C} (f : X' ⟶ X) (F : Sheaf J (Type (max v v')))
  proof: by
  apply J.uliftYonedaEquiv.injective
  simp only [uliftYonedaEquiv_comp, Equiv.apply_symm_apply]
  rw [uliftYonedaEquiv_uliftYoneda_map]
  rfl

中文:
引理 uliftYonedaEquiv_symm_naturality_left
  结论: {X X' : C} (f : X' ⟶ X) (F : 层 J (类型 (最大值 v v')))
  证明: by
  apply J.uliftYonedaEquiv.injective
  simp only [uliftYonedaEquiv_comp, Equiv.apply_symm_apply]
  rw [uliftYonedaEquiv_uliftYoneda_map]
  rfl

Depends on / 依赖: Equiv.apply_symm_apply, J.uliftYonedaEquiv.injective, apply_symm_apply, injective, uliftYonedaEquiv, uliftYonedaEquiv_comp, uliftYonedaEquiv_uliftYoneda_map
-/
lemma uliftYonedaEquiv_symm_naturality_left {X X' : C} (f : X' ⟶ X) (F : Sheaf J (Type (max v v')))
    (x : F.obj.obj ⟨X⟩) :
    J.uliftYoneda.map f ≫ J.uliftYonedaEquiv.symm x =
      J.uliftYonedaEquiv.symm ((F.obj.map f.op) x) := by
  apply J.uliftYonedaEquiv.injective
  simp only [uliftYonedaEquiv_comp, Equiv.apply_symm_apply]
  rw [uliftYonedaEquiv_uliftYoneda_map]
  rfl

/--
lemma `uliftYonedaEquiv_symm_naturality_right` / 引理 `uliftYonedaEquiv_symm_naturality_right`

English:
lemma uliftYonedaEquiv_symm_naturality_right
  statement: (X : C) {F F' : Sheaf J (Type (max v v'))}
  proof: by
  apply J.uliftYonedaEquiv.injective
  simp [uliftYonedaEquiv_comp]

中文:
引理 uliftYonedaEquiv_symm_naturality_right
  结论: (X : C) {F F' : 层 J (类型 (最大值 v v'))}
  证明: by
  apply J.uliftYonedaEquiv.injective
  simp [uliftYonedaEquiv_comp]

Depends on / 依赖: J.uliftYonedaEquiv.injective, injective, uliftYonedaEquiv, uliftYonedaEquiv_comp
-/
lemma uliftYonedaEquiv_symm_naturality_right (X : C) {F F' : Sheaf J (Type (max v v'))}
    (f : F ⟶ F') (x : F.obj.obj ⟨X⟩) :
    J.uliftYonedaEquiv.symm x ≫ f = J.uliftYonedaEquiv.symm (f.hom.app ⟨X⟩ x) := by
  apply J.uliftYonedaEquiv.injective
  simp [uliftYonedaEquiv_comp]

/--
lemma `map_uliftYonedaEquiv` / 引理 `map_uliftYonedaEquiv`

English:
lemma map_uliftYonedaEquiv
  statement: {X Y : C} {F : Sheaf J (Type (max v v'))}
  proof: by
  rw [uliftYonedaEquiv_naturality]; rw [uliftYonedaEquiv_comp]; rw [uliftYonedaEquiv_uliftYoneda_map]

中文:
引理 map_uliftYonedaEquiv
  结论: {X Y : C} {F : 层 J (类型 (最大值 v v'))}
  证明: by
  rw [uliftYonedaEquiv_naturality]; rw [uliftYonedaEquiv_comp]; rw [uliftYonedaEquiv_uliftYoneda_map]

Depends on / 依赖: uliftYonedaEquiv_comp, uliftYonedaEquiv_naturality, uliftYonedaEquiv_uliftYoneda_map
-/
lemma map_uliftYonedaEquiv {X Y : C} {F : Sheaf J (Type (max v v'))}
    (f : J.uliftYoneda.obj X ⟶ F) (g : Y ⟶ X) :
    F.obj.map g.op (J.uliftYonedaEquiv f) = f.hom.app (op Y) ⟨g⟩ := by
  rw [uliftYonedaEquiv_naturality]; rw [uliftYonedaEquiv_comp]; rw [uliftYonedaEquiv_uliftYoneda_map]

/--
lemma `map_uliftYonedaEquiv'` / 引理 `map_uliftYonedaEquiv'`

English:
lemma map_uliftYonedaEquiv'
  statement: {X Y : Cᵒᵖ} {F : Sheaf J (Type (max v v'))}
  proof: by
  rw [uliftYonedaEquiv_naturality']; rw [uliftYonedaEquiv_comp]; rw [uliftYonedaEquiv_uliftYoneda_map]

中文:
引理 map_uliftYonedaEquiv'
  结论: {X Y : Cᵒᵖ} {F : 层 J (类型 (最大值 v v'))}
  证明: by
  rw [uliftYonedaEquiv_naturality']; rw [uliftYonedaEquiv_comp]; rw [uliftYonedaEquiv_uliftYoneda_map]

Depends on / 依赖: uliftYonedaEquiv_comp, uliftYonedaEquiv_naturality, uliftYonedaEquiv_uliftYoneda_map
-/
lemma map_uliftYonedaEquiv' {X Y : Cᵒᵖ} {F : Sheaf J (Type (max v v'))}
    (f : J.uliftYoneda.obj (unop X) ⟶ F) (g : X ⟶ Y) :
    F.obj.map g (J.uliftYonedaEquiv f) = f.hom.app Y ⟨g.unop⟩ := by
  rw [uliftYonedaEquiv_naturality']; rw [uliftYonedaEquiv_comp]; rw [uliftYonedaEquiv_uliftYoneda_map]

/--
lemma `uliftYonedaEquiv_symm_map` / 引理 `uliftYonedaEquiv_symm_map`

English:
lemma uliftYonedaEquiv_symm_map
  statement: {X Y : Cᵒᵖ} (f : X ⟶ Y) {F : Sheaf J (Type (max v v'))}
  proof: by
  obtain ⟨u, rfl⟩ := J.uliftYonedaEquiv.surjective t
  rw [uliftYonedaEquiv_naturality']; rw [Equiv.symm_apply_apply]; rw [Equiv.symm_apply_apply]

中文:
引理 uliftYonedaEquiv_symm_map
  结论: {X Y : Cᵒᵖ} (f : X ⟶ Y) {F : 层 J (类型 (最大值 v v'))}
  证明: by
  obtain ⟨u, rfl⟩ := J.uliftYonedaEquiv.surjective t
  rw [uliftYonedaEquiv_naturality']; rw [Equiv.symm_apply_apply]; rw [Equiv.symm_apply_apply]

Depends on / 依赖: Equiv.symm_apply_apply, J.uliftYonedaEquiv.surjective, surjective, symm_apply_apply, uliftYonedaEquiv, uliftYonedaEquiv_naturality
-/
lemma uliftYonedaEquiv_symm_map {X Y : Cᵒᵖ} (f : X ⟶ Y) {F : Sheaf J (Type (max v v'))}
    (t : F.obj.obj X) : J.uliftYonedaEquiv.symm (F.obj.map f t) =
      J.uliftYoneda.map f.unop ≫ J.uliftYonedaEquiv.symm t := by
  obtain ⟨u, rfl⟩ := J.uliftYonedaEquiv.surjective t
  rw [uliftYonedaEquiv_naturality']; rw [Equiv.symm_apply_apply]; rw [Equiv.symm_apply_apply]

/--
lemma `hom_ext_uliftYoneda` / 引理 `hom_ext_uliftYoneda`

English:
lemma hom_ext_uliftYoneda
  statement: {P Q : Sheaf J (Type (max v v'))} {f g : P ⟶ Q}
  proof: by
  ext X x
  simpa only [uliftYonedaEquiv_comp, Equiv.apply_symm_apply]
    using! congr_arg (J.uliftYonedaEquiv) (h _ (J.uliftYonedaEquiv.symm x))

#adaptation_note

中文:
引理 hom_ext_uliftYoneda
  结论: {P Q : 层 J (类型 (最大值 v v'))} {f g : P ⟶ Q}
  证明: by
  ext X x
  simpa only [uliftYonedaEquiv_comp, Equiv.apply_symm_apply]
    using! congr_arg (J.uliftYonedaEquiv) (h _ (J.uliftYonedaEquiv.symm x))

#adaptation_note

Depends on / 依赖: Equiv.apply_symm_apply, J.uliftYonedaEquiv, J.uliftYonedaEquiv.symm, apply_symm_apply, congr_arg, uliftYonedaEquiv, uliftYonedaEquiv_comp
-/
lemma hom_ext_uliftYoneda {P Q : Sheaf J (Type (max v v'))} {f g : P ⟶ Q}
    (h : forall (X : C) (p : J.uliftYoneda.obj X ⟶ P), p ≫ f = p ≫ g) :
    f = g := by
  ext X x
  simpa only [uliftYonedaEquiv_comp, Equiv.apply_symm_apply]
    using! congr_arg (J.uliftYonedaEquiv) (h _ (J.uliftYonedaEquiv.symm x))

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- A variant of the Yoneda lemma for sheaves with a raise in the universe level. -/
@[simps! +dsimpLhs -isSimp]
/--
Definition of `uliftYonedaOpCompCoyoneda` / `uliftYonedaOpCompCoyoneda` 的定义

English:
definition uliftYonedaOpCompCoyoneda
  signature: :
  body: ((isoWhiskerLeft (J.yoneda.op ⋙ (sheafCompose J _).op)
    sheafToPresheafCompCoyonedaCompWhiskeringLeftSheafToPresheaf.symm).trans
    (isoWhiskerRight (NatIso.op (J.uliftYonedaCompSheafToPresheaf.symm))
    (_ ⋙ (whiskeringLeft _ _ _).obj _))).trans
    (isoWhiskerRight CategoryTheory.uliftYonedaO

中文:
定义 uliftYonedaOpCompCoyoneda
  签名: :
  定义体: ((isoWhiskerLeft (J.yoneda.op ⋙ (sheafCompose J _).op)
    sheafToPresheafCompCoyonedaCompWhiskeringLeftSheafToPresheaf.symm).trans
    (isoWhiskerRight (NatIso.op (J.uliftYonedaCompSheafToPresheaf.symm))
    (_ ⋙ (whiskeringLeft _ _ _).obj _))).trans
    (isoWhiskerRight CategoryTheory.uliftYonedaO

Depends on / 依赖: CategoryTheory, CategoryTheory.uliftYonedaOpCompCoyoneda, J.uliftYonedaCompSheafToPresheaf.symm, J.yoneda.op, NatIso, NatIso.op, isoWhiskerLeft, isoWhiskerRight, sheafCompose, sheafToPresheafCompCoyonedaCompWhiskeringLeftSheafToPresheaf, sheafToPresheafCompCoyonedaCompWhiskeringLeftSheafToPresheaf.symm, uliftYonedaCompSheafToPresheaf, uliftYonedaOpCompCoyoneda, whiskeringLeft, yoneda
-/
def uliftYonedaOpCompCoyoneda :
    J.uliftYoneda.op ⋙ coyoneda ≅
      evaluation Cᵒᵖ (Type max v v') ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u} ⋙
      (whiskeringLeft _ _ _).obj (sheafToPresheaf _ _) :=
  ((isoWhiskerLeft (J.yoneda.op ⋙ (sheafCompose J _).op)
    sheafToPresheafCompCoyonedaCompWhiskeringLeftSheafToPresheaf.symm).trans
    (isoWhiskerRight (NatIso.op (J.uliftYonedaCompSheafToPresheaf.symm))
    (_ ⋙ (whiskeringLeft _ _ _).obj _))).trans
    (isoWhiskerRight CategoryTheory.uliftYonedaOpCompCoyoneda
    ((whiskeringLeft _ _ _).obj _))

attribute [simp] uliftYonedaOpCompCoyoneda_hom_app_app_hom_apply_down

-- @[simp]
/--
lemma `uliftYonedaOpCompCoyoneda_inv_app_app` / 引理 `uliftYonedaOpCompCoyoneda_inv_app_app`

English:
lemma uliftYonedaOpCompCoyoneda_inv_app_app
  statement: (X : Cᵒᵖ) (F : Sheaf J (Type max v v'))
  proof: rfl

中文:
引理 uliftYonedaOpCompCoyoneda_inv_app_app
  结论: (X : Cᵒᵖ) (F : 层 J (类型 最大值 v v'))
  证明: rfl
-/
lemma uliftYonedaOpCompCoyoneda_inv_app_app (X : Cᵒᵖ) (F : Sheaf J (Type max v v'))
    (s : ULift.{u} (F.obj.obj X)) :
    dsimp% (J.uliftYonedaOpCompCoyoneda.inv.app X).app F s = J.uliftYonedaEquiv.symm s.down :=
  rfl

/--
lemma `uliftYonedaOpCompCoyoneda_app_app` / 引理 `uliftYonedaOpCompCoyoneda_app_app`

English:
lemma uliftYonedaOpCompCoyoneda_app_app
  given: (X : Cᵒᵖ) (F : Sheaf J (Type (max v v')))
  proof: rfl

中文:
引理 uliftYonedaOpCompCoyoneda_app_app
  条件: (X : Cᵒᵖ) (F : 层 J (类型 (最大值 v v')))
  证明: rfl
-/
lemma uliftYonedaOpCompCoyoneda_app_app (X : Cᵒᵖ) (F : Sheaf J (Type (max v v'))) :
    (J.uliftYonedaOpCompCoyoneda.app X).app F = (J.uliftYonedaEquiv.trans Equiv.ulift.symm).toIso :=
  rfl

open Limits

/--
Instance `preservesLimitsOfSize_yoneda` / 实例 `preservesLimitsOfSize_yoneda`

English:
instance preservesLimitsOfSize_yoneda
  signature: : PreservesLimitsOfSize J.yoneda
  body: by
  refine ⟨fun {I} _ => ?_⟩
  have : PreservesLimitsOfShape I (J.yoneda ⋙ sheafToPresheaf J _) :=
inferInstanceAs PreservesLimitsOfShape I CategoryTheory.yoneda
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (sheafToPresheaf J _)

中文:
实例 preservesLimitsOfSize_yoneda
  签名: : 保持LimitsOfSize J.yoneda
  定义体: by
  refine ⟨fun {I} _ => ?_⟩
  have : PreservesLimitsOfShape I (J.yoneda ⋙ sheafToPresheaf J _) :=
inferInstanceAs PreservesLimitsOfShape I CategoryTheory.yoneda
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (sheafToPresheaf J _)

Depends on / 依赖: CategoryTheory, CategoryTheory.yoneda, J.yoneda, PreservesLimitsOfShape, preservesLimitsOfShape_of_reflects_of_preserves, sheafToPresheaf, yoneda
-/
instance preservesLimitsOfSize_yoneda : PreservesLimitsOfSize J.yoneda := by
  refine ⟨fun {I} _ => ?_⟩
  have : PreservesLimitsOfShape I (J.yoneda ⋙ sheafToPresheaf J _) :=
inferInstanceAs PreservesLimitsOfShape I CategoryTheory.yoneda
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (sheafToPresheaf J _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isColimitCofanMkYoneda` / `isColimitCofanMkYoneda` 的定义

English:
definition isColimitCofanMkYoneda
  signature: {ι : Type*} (X : ι -> C) {c : Cofan X}
  body: by
  have heq (s : Cofan fun i => J.yoneda.obj (X i))
      {Y : C} {i j : ι} (a : Y ⟶ X i) (b : Y ⟶ X j) (hab : a ≫ c.inj i = b ≫ c.inj j) :
      (s.inj i).hom.app (op Y) a = (s.inj j).hom.app (op Y) b := by
    by_cases h : i = j
    · subst h
      rw [(cancel_mono _).mp hab]
    · obtain ⟨h⟩ :=

中文:
定义 isColimitCofanMkYoneda
  签名: {ι : 类型} (X : ι -> C) {c : Cofan X}
  定义体: by
  have heq (s : Cofan fun i => J.yoneda.obj (X i))
      {Y : C} {i j : ι} (a : Y ⟶ X i) (b : Y ⟶ X j) (hab : a ≫ c.inj i = b ≫ c.inj j) :
      (s.inj i).hom.app (op Y) a = (s.inj j).hom.app (op Y) b := by
    by_cases h : i = j
    · subst h
      rw [(cancel_mono _).mp hab]
    · obtain ⟨h⟩ :=

Depends on / 依赖: Cofan.IsColimit.mk, IsColimit, J.yoneda.obj, Sheaf.isTerminalOfBotCover, Subsingleton, Subsingleton.elim, Types.isTerminalEquivUnique, c.inj, cancel_mono, hempty, hom.app, isShea, isTerminalEquivUnique, isTerminalOfBotCover, s.inj, s.pt, yoneda
-/
noncomputable def isColimitCofanMkYoneda {ι : Type*} (X : ι -> C) {c : Cofan X}
    (H : (Sieve.ofArrows _ c.inj) in J c.pt) [forall (i : ι), Mono (c.inj i)]
    (hempty : (Y : C) -> IsInitial Y -> ⊥ in J Y)
    (hdisj : forall {i j : ι} (_ : i != j) {Y : C} (a : Y ⟶ X i)
      (b : Y ⟶ X j), a ≫ c.inj i = b ≫ c.inj j -> Nonempty (IsInitial Y)) :
    IsColimit (Cofan.mk _ fun i => J.yoneda.map (c.inj i)) := by
  have heq (s : Cofan fun i => J.yoneda.obj (X i))
      {Y : C} {i j : ι} (a : Y ⟶ X i) (b : Y ⟶ X j) (hab : a ≫ c.inj i = b ≫ c.inj j) :
      (s.inj i).hom.app (op Y) a = (s.inj j).hom.app (op Y) b := by
    by_cases h : i = j
    · subst h
      rw [(cancel_mono _).mp hab]
    · obtain ⟨h⟩ := hdisj h a b hab
      have := Types.isTerminalEquivUnique _ (Sheaf.isTerminalOfBotCover s.pt _ (hempty Y h))
      exact Subsingleton.elim _ _
  refine Cofan.IsColimit.mk _ (fun s => ⟨?_⟩) (fun s j => ?_) fun s m hm => ?_
  · refine (s.pt.2.isSheafFor _ H).extend ?_
    refine ⟨fun Y => ↾fun g => ((s.inj (Sieve.ofArrows.i g.2)).hom.app Y)
      (Sieve.ofArrows.h g.2), ?_⟩
    intro ⟨Y⟩ ⟨Z⟩ ⟨(g : Z ⟶ Y)⟩
    ext u
    simp only [Sieve.functor_obj, Sieve.generate_apply, Sieve.functor_map, Quiver.Hom.unop_op',
      TypeCat.Fun.toFun_apply, comp_apply, ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk,
      ← heq s (g ≫ Sieve.ofArrows.h u.2)
      (Sieve.ofArrows.h <| Sieve.downward_closed _ u.2 g) (by simp)]
    exact ConcreteCategory.congr_hom ((s.inj _).hom.naturality g.op) _
  · ext : 1
    let u (j : ι) : CategoryTheory.yoneda.obj (X j) ⟶ (Sieve.ofArrows _ c.inj).functor :=
      (Sieve.ofArrows _ c.inj).toFunctor (c.inj j) (Sieve.ofArrows_mk _ _ j)
    have (j : ι) : u j ≫ (Sieve.ofArrows _ c.inj).functorInclusion =
      CategoryTheory.yoneda.map (c.inj j) := rfl
    dsimp
    simp only [← this, Category.assoc, Presieve.IsSheafFor.functorInclusion_comp_extend]
    ext Z (g : Z.unop ⟶ X j)
    have h : Sieve.ofArrows X c.inj (g ≫ c.inj j) :=
      Sieve.downward_closed _ (Sieve.ofArrows_mk _ _ j) _
    exact heq s (Sieve.ofArrows.h h) g (by simp)
  · ext : 1
    dsimp
    apply Presieve.IsSheafFor.unique_extend
    ext Y ⟨g, hg⟩
    simp [← hm (Sieve.ofArrows.i hg)]

/--
lemma `preservesColimitsOfShape_yoneda_of_ofArrows_inj_mem` / 引理 `preservesColimitsOfShape_yoneda_of_ofArrows_inj_mem`

English:
lemma preservesColimitsOfShape_yoneda_of_ofArrows_inj_mem
  statement: {ι : Type*}
  proof: by
  apply (config := { allowSynthFailures := true }) preservesColimitsOfShape_of_discrete
  refine fun X => ⟨fun {c : Cofan X} hc => ⟨(Limits.Cofan.isColimitMapCoconeEquiv _ _ _).symm ?_⟩⟩
  have (i : ι) : Mono (c.inj i) := .of_coproductDisjoint hc _
  refine isColimitCofanMkYoneda _ _ (hcov hc) ht

中文:
引理 preservesColimitsOfShape_yoneda_of_ofArrows_inj_mem
  结论: {ι : 类型}
  证明: by
  apply (config := { allowSynthFailures := true }) preservesColimitsOfShape_of_discrete
  refine fun X => ⟨fun {c : Cofan X} hc => ⟨(Limits.Cofan.isColimitMapCoconeEquiv _ _ _).symm ?_⟩⟩
  have (i : ι) : Mono (c.inj i) := .of_coproductDisjoint hc _
  refine isColimitCofanMkYoneda _ _ (hcov hc) ht

Depends on / 依赖: Limits, Limits.Cofan.isColimitMapCoconeEquiv, allowSynthFailures, c.inj, config, isColimitCofanMkYoneda, isColimitMapCoconeEquiv, ofCoproductDisjointOfCommSq, of_coproductDisjoint, preservesColimitsOfShape_of_discrete
-/
lemma preservesColimitsOfShape_yoneda_of_ofArrows_inj_mem {ι : Type*}
    [CoproductsOfShapeDisjoint C ι] [HasPullbacks C] [HasStrictInitialObjects C]
    (hcov : forall {X : ι -> C} {c : Cofan X} (_ : IsColimit c), Sieve.ofArrows X c.inj in J c.pt)
    (htriv : forall (Y : C), IsInitial Y -> ⊥ in J Y) :
    PreservesColimitsOfShape (Discrete ι) J.yoneda := by
  apply (config := { allowSynthFailures := true }) preservesColimitsOfShape_of_discrete
  refine fun X => ⟨fun {c : Cofan X} hc => ⟨(Limits.Cofan.isColimitMapCoconeEquiv _ _ _).symm ?_⟩⟩
  have (i : ι) : Mono (c.inj i) := .of_coproductDisjoint hc _
  refine isColimitCofanMkYoneda _ _ (hcov hc) htriv fun hij Y a b hab => ⟨?_⟩
  exact .ofCoproductDisjointOfCommSq hij hc _ _ hab

variable {D : Type*} [Category.{v'} D] (F : C ⥤ D) (J : GrothendieckTopology C)
  (K : GrothendieckTopology D)

/--
lemma `subcanonical_of_full_of_faithful` / 引理 `subcanonical_of_full_of_faithful`

English:
lemma subcanonical_of_full_of_faithful
  statement: [F.Full] [F.Faithful]
  proof: by
  refine .of_isSheaf_yoneda_obj _ fun Y => ?_
  suffices h : Presieve.IsSheaf J (CategoryTheory.uliftYoneda.{v'}.obj Y) by
    rwa [Presieve.isSheaf_iff_of_nat_equiv]
    · intro
      exact Equiv.ulift.symm
    · intros
      rfl
  rw [← isSheaf_iff_isSheaf_of_type]; rw [Presheaf.isSheaf_of_iso_

中文:
引理 subcanonical_of_full_of_faithful
  结论: [F.满] [F.忠实]
  证明: by
  refine .of_isSheaf_yoneda_obj _ fun Y => ?_
  suffices h : Presieve.IsSheaf J (CategoryTheory.uliftYoneda.{v'}.obj Y) by
    rwa [Presieve.isSheaf_iff_of_nat_equiv]
    · intro
      exact Equiv.ulift.symm
    · intros
      rfl
  rw [← isSheaf_iff_isSheaf_of_type]; rw [Presheaf.isSheaf_of_iso_

Depends on / 依赖: CategoryTheory, CategoryTheory.uliftYoneda, Equiv.ulift.symm, F.op_comp_isSheaf_of_isSheaf, FullyFaithful, Functor, Functor.FullyFaithful.ofFullyFaithful, GrothendieckTopology, GrothendieckTopology.Subcanonical.isSheaf_of_isRepre, IsSheaf, Presheaf, Presheaf.isSheaf_of_iso_iff, Presieve, Presieve.IsSheaf, Presieve.isSheaf_iff_of_nat_equiv, Subcanonical, compUliftYonedaCompWhiskeringLeft, compUliftYonedaCompWhiskeringLeft.app, intros, isSheaf_iff_isSheaf_of_type
-/
lemma subcanonical_of_full_of_faithful [F.Full] [F.Faithful]
    [Functor.IsContinuous F J K] [K.Subcanonical] :
    J.Subcanonical := by
  refine .of_isSheaf_yoneda_obj _ fun Y => ?_
  suffices h : Presieve.IsSheaf J (CategoryTheory.uliftYoneda.{v'}.obj Y) by
    rwa [Presieve.isSheaf_iff_of_nat_equiv]
    · intro
      exact Equiv.ulift.symm
    · intros
      rfl
  rw [← isSheaf_iff_isSheaf_of_type]; rw [Presheaf.isSheaf_of_iso_iff
    ((Functor.FullyFaithful.ofFullyFaithful F).compUliftYonedaCompWhiskeringLeft.app Y).symm]
  refine F.op_comp_isSheaf_of_isSheaf J K _ ?_
  rw [isSheaf_iff_isSheaf_of_type]
  apply GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable

end CategoryTheory.GrothendieckTopology
