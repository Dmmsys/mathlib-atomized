/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.EssentiallySmall

/-!
# The Yoneda functor for locally small categories

Let `C` be a locally `w`-small category. We define the Yoneda
embedding `shrinkYoneda : C ⥤ Cᵒᵖ ⥤ Type w`. (See the
file `CategoryTheory.Yoneda` for the other variants `yoneda` and
`uliftYoneda`.)

-/

@[expose] public section

universe w w' w'' v u

namespace CategoryTheory

open Opposite

variable {C : Type u} [Category.{v} C]

namespace FunctorToTypes

/-- A functor to types `F : C ⥤ Type w'` is `w`-small if for any `X : C`,
the type `F.obj X` is `w`-small. -/
@[pp_with_univ]
/--
Definition of `Small` / `Small` 的定义

English:
abbreviation Small
  signature: (F : C ⥤ Type w')
  body: forall (X : C), _root_.Small.{w} (F.obj X)

中文:
缩写 Small
  签名: (F : C ⥤ Type w')
  定义体: forall (X : C), _root_.Small.{w} (F.obj X)
-/
protected abbrev Small (F : C ⥤ Type w') := forall (X : C), _root_.Small.{w} (F.obj X)

/-- If a functor `F : C ⥤ Type w'` is `w`-small, this is the functor `C ⥤ Type w`
obtained by shrinking `F.obj X` for all `X : C`. -/
@[implicit_reducible, simps obj map, pp_with_univ]
/--
Definition of `shrink` / `shrink` 的定义

English:
definition shrink
  signature: (F : C ⥤ Type w') [FunctorToTypes.Small.{w} F]
  body: Shrink.{w} (F.obj X)
  map f := ↾(equivShrink.{w} _ ∘ F.map f ∘ (equivShrink.{w} _).symm)

中文:
定义 shrink
  签名: (F : C ⥤ Type w') [FunctorToTypes.Small.{w} F]
  定义体: Shrink.{w} (F.obj X)
  map f := ↾(equivShrink.{w} _ ∘ F.map f ∘ (equivShrink.{w} _).symm)

Depends on / 依赖: F.obj, Shrink
-/
noncomputable def shrink (F : C ⥤ Type w') [FunctorToTypes.Small.{w} F] :
    C ⥤ Type w where
  obj X := Shrink.{w} (F.obj X)
  map f := ↾(equivShrink.{w} _ ∘ F.map f ∘ (equivShrink.{w} _).symm)

/-- The natural transformation `shrink.{w} F ⟶ shrink.{w} G` induces by a natural
transformation `τ : F ⟶ G` between `w`-small functors to types. -/
@[implicit_reducible, simps]
/--
Definition of `shrinkMap` / `shrinkMap` 的定义

English:
definition shrinkMap
  signature: {F G : C ⥤ Type w'} (τ : F ⟶ G) [FunctorToTypes.Small.{w} F]
  body: ↾(equivShrink.{w} _ ∘ τ.app X ∘ (equivShrink.{w} _).symm)

中文:
定义 shrinkMap
  签名: {F G : C ⥤ Type w'} (τ : F ⟶ G) [FunctorToTypes.Small.{w} F]
  定义体: ↾(equivShrink.{w} _ ∘ τ.app X ∘ (equivShrink.{w} _).symm)

Depends on / 依赖: equivShrink
-/
noncomputable def shrinkMap {F G : C ⥤ Type w'} (τ : F ⟶ G) [FunctorToTypes.Small.{w} F]
    [FunctorToTypes.Small.{w} G] :
    shrink.{w} F ⟶ shrink.{w} G where
  app X := ↾(equivShrink.{w} _ ∘ τ.app X ∘ (equivShrink.{w} _).symm)

set_option backward.defeqAttrib.useBackward true in
/-- Shrinking `F` to `Type w` followed by universe lifting is the same as shrinking to
`Type (max w w')`. -/
@[simps! hom_app inv_app]
noncomputable
/--
Definition of `shrinkCompUliftFunctorIso` / `shrinkCompUliftFunctorIso` 的定义

English:
definition shrinkCompUliftFunctorIso
  signature: (F : C ⥤ Type w') [FunctorToTypes.Small.{w} F]
  body: NatIso.ofComponents
    (fun X => Equiv.toIso ((Equiv.ulift.trans (equivShrink _).symm).trans (equivShrink _)))

unif_hint (F : C ⥤ Type w') [FunctorToTypes.Small.{w} F] (X : C) where ⊢
  Shrink (F.obj X) ≟ (FunctorToTypes.shrink F).obj X

中文:
定义 shrinkCompUliftFunctorIso
  签名: (F : C ⥤ Type w') [FunctorToTypes.Small.{w} F]
  定义体: NatIso.ofComponents
    (fun X => Equiv.toIso ((Equiv.ulift.trans (equivShrink _).symm).trans (equivShrink _)))

unif_hint (F : C ⥤ Type w') [FunctorToTypes.Small.{w} F] (X : C) where ⊢
  Shrink (F.obj X) ≟ (FunctorToTypes.shrink F).obj X

Depends on / 依赖: Equiv.toIso, Equiv.ulift.trans, NatIso, NatIso.ofComponents, equivShrink, ofComponents
-/
def shrinkCompUliftFunctorIso (F : C ⥤ Type w') [FunctorToTypes.Small.{w} F]
    [FunctorToTypes.Small.{max w w''} F] :
    shrink.{w} F ⋙ uliftFunctor.{w'', w} ≅ shrink.{max w w''} F :=
  NatIso.ofComponents
    (fun X => Equiv.toIso ((Equiv.ulift.trans (equivShrink _).symm).trans (equivShrink _)))

unif_hint (F : C ⥤ Type w') [FunctorToTypes.Small.{w} F] (X : C) where ⊢
  Shrink (F.obj X) ≟ (FunctorToTypes.shrink F).obj X

end FunctorToTypes

variable [LocallySmall.{w} C]

section Yoneda

set_option backward.defeqAttrib.useBackward true in
instance (X : C) : FunctorToTypes.Small.{w} (yoneda.obj X) :=
  fun _ => by dsimp; infer_instance

/-- The Yoneda embedding `C ⥤ Cᵒᵖ ⥤ Type w` for a locally `w`-small category `C`. -/
@[simps -isSimp obj map, pp_with_univ]
/--
Definition of `shrinkYoneda` / `shrinkYoneda` 的定义

English:
definition shrinkYoneda
  signature: :
  body: FunctorToTypes.shrink (yoneda.obj X)
  map f := FunctorToTypes.shrinkMap (yoneda.map f)

中文:
定义 shrinkYoneda
  签名: :
  定义体: FunctorToTypes.shrink (yoneda.obj X)
  map f := FunctorToTypes.shrinkMap (yoneda.map f)

Depends on / 依赖: FunctorToTypes, FunctorToTypes.shrink, shrink, yoneda, yoneda.obj
-/
noncomputable def shrinkYoneda :
    C ⥤ Cᵒᵖ ⥤ Type w where
  obj X := FunctorToTypes.shrink (yoneda.obj X)
  map f := FunctorToTypes.shrinkMap (yoneda.map f)

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `shrinkYonedaObjObjEquiv` / `shrinkYonedaObjObjEquiv` 的定义

English:
definition shrinkYonedaObjObjEquiv
  signature: {X : C} {Y : Cᵒᵖ}
  body: (equivShrink _).symm

中文:
定义 shrinkYonedaObjObjEquiv
  签名: {X : C} {Y : Cᵒᵖ}
  定义体: (equivShrink _).symm

Depends on / 依赖: equivShrink
-/
noncomputable def shrinkYonedaObjObjEquiv {X : C} {Y : Cᵒᵖ} :
    ((shrinkYoneda.{w}.obj X).obj Y) ≃ (Y.unop ⟶ X) :=
  (equivShrink _).symm

/--
lemma `shrinkYoneda_obj_map` / 引理 `shrinkYoneda_obj_map`

English:
lemma shrinkYoneda_obj_map
  given: {X : C} {Y Y' : Cᵒᵖ} (g : Y ⟶ Y') (f : (shrinkYoneda.obj X).obj Y)
  proof: rfl

中文:
引理 shrinkYoneda_obj_map
  条件: {X : C} {Y Y' : Cᵒᵖ} (g : Y ⟶ Y') (f : (shrinkYoneda.obj X).obj Y)
  证明: rfl
-/
lemma shrinkYoneda_obj_map {X : C} {Y Y' : Cᵒᵖ} (g : Y ⟶ Y') (f : (shrinkYoneda.obj X).obj Y) :
    (shrinkYoneda.obj _).map g f =
      shrinkYonedaObjObjEquiv.symm (g.unop ≫ shrinkYonedaObjObjEquiv f) :=
  rfl

/--
lemma `shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm` / 引理 `shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm`

English:
lemma shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm
  proof: by
  simp [shrinkYoneda_obj_map]

中文:
引理 shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm
  证明: by
  simp [shrinkYoneda_obj_map]

Depends on / 依赖: shrinkYoneda_obj_map
-/
lemma shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm
    {X : C} {Y Y' : Cᵒᵖ} (g : Y ⟶ Y') (f : Y.unop ⟶ X) :
    (shrinkYoneda.obj _).map g (shrinkYonedaObjObjEquiv.symm f) =
      shrinkYonedaObjObjEquiv.symm (g.unop ≫ f) := by
  simp [shrinkYoneda_obj_map]

/--
lemma `shrinkYonedaObjObjEquiv_symm_comp` / 引理 `shrinkYonedaObjObjEquiv_symm_comp`

English:
lemma shrinkYonedaObjObjEquiv_symm_comp
  given: {X Y Y' : C} (g : Y' ⟶ Y) (f : Y ⟶ X)
  proof: (shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm g.op f).symm

中文:
引理 shrinkYonedaObjObjEquiv_symm_comp
  条件: {X Y Y' : C} (g : Y' ⟶ Y) (f : Y ⟶ X)
  证明: (shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm g.op f).symm

Depends on / 依赖: g.op, shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm
-/
lemma shrinkYonedaObjObjEquiv_symm_comp {X Y Y' : C} (g : Y' ⟶ Y) (f : Y ⟶ X) :
    shrinkYonedaObjObjEquiv.symm (g ≫ f) =
    (shrinkYoneda.obj _).map g.op (shrinkYonedaObjObjEquiv.symm f) :=
  (shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm g.op f).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm` / 引理 `shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm`

English:
lemma shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm
  proof: by
  simp [shrinkYoneda, shrinkYonedaObjObjEquiv]

中文:
引理 shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm
  证明: by
  simp [shrinkYoneda, shrinkYonedaObjObjEquiv]

Depends on / 依赖: shrinkYoneda, shrinkYonedaObjObjEquiv
-/
lemma shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm
    {X X' : C} {Y : Cᵒᵖ} (f : Y.unop ⟶ X) (g : X ⟶ X') :
    (shrinkYoneda.map g).app _ (shrinkYonedaObjObjEquiv.symm f) =
      shrinkYonedaObjObjEquiv.symm (f ≫ g) := by
  simp [shrinkYoneda, shrinkYonedaObjObjEquiv]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `shrinkYonedaObjObjEquiv_map_app` / 引理 `shrinkYonedaObjObjEquiv_map_app`

English:
lemma shrinkYonedaObjObjEquiv_map_app
  proof: by
  simp [shrinkYoneda, shrinkYonedaObjObjEquiv]

中文:
引理 shrinkYonedaObjObjEquiv_map_app
  证明: by
  simp [shrinkYoneda, shrinkYonedaObjObjEquiv]

Depends on / 依赖: shrinkYoneda, shrinkYonedaObjObjEquiv
-/
lemma shrinkYonedaObjObjEquiv_map_app
    {X X' : C} {Y : Cᵒᵖ} (f : (shrinkYoneda.{w, v, u}.obj X).obj Y) (g : X ⟶ X') :
    shrinkYonedaObjObjEquiv ((shrinkYoneda.map g).app Y f) =
      shrinkYonedaObjObjEquiv f ≫ g := by
  simp [shrinkYoneda, shrinkYonedaObjObjEquiv]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `shrinkYonedaObjObjEquiv_obj_map` / 引理 `shrinkYonedaObjObjEquiv_obj_map`

English:
lemma shrinkYonedaObjObjEquiv_obj_map
  statement: {X : C} {Y Y' : Cᵒᵖ} (g : Y ⟶ Y')
  proof: by
  simp [shrinkYonedaObjObjEquiv, shrinkYoneda]

中文:
引理 shrinkYonedaObjObjEquiv_obj_map
  结论: {X : C} {Y Y' : Cᵒᵖ} (g : Y ⟶ Y')
  证明: by
  simp [shrinkYonedaObjObjEquiv, shrinkYoneda]

Depends on / 依赖: shrinkYoneda, shrinkYonedaObjObjEquiv
-/
lemma shrinkYonedaObjObjEquiv_obj_map {X : C} {Y Y' : Cᵒᵖ} (g : Y ⟶ Y')
    (f : (shrinkYoneda.{w}.obj X).obj Y) :
    shrinkYonedaObjObjEquiv ((shrinkYoneda.{w}.obj X).map g f) =
      g.unop ≫ shrinkYonedaObjObjEquiv f := by
  simp [shrinkYonedaObjObjEquiv, shrinkYoneda]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `shrinkYonedaEquiv` / `shrinkYonedaEquiv` 的定义

English:
definition shrinkYonedaEquiv
  signature: {X : C} {P : Cᵒᵖ ⥤ Type w}
  body: τ.app _ (equivShrink.{w} _ (𝟙 X))
  invFun x :=
    { app Y := ↾fun f => P.map ((equivShrink.{w} _).symm f).op x
      naturality Y Z g := by ext; simp [shrinkYoneda] }
  left_inv τ := by
    ext Y f
    obtain ⟨f, rfl⟩ := (equivShrink _).surjective f
    simpa [shrinkYoneda] using ((τ.naturality_ap

中文:
定义 shrinkYonedaEquiv
  签名: {X : C} {P : Cᵒᵖ ⥤ Type w}
  定义体: τ.app _ (equivShrink.{w} _ (𝟙 X))
  invFun x :=
    { app Y := ↾fun f => P.map ((equivShrink.{w} _).symm f).op x
      naturality Y Z g := by ext; simp [shrinkYoneda] }
  left_inv τ := by
    ext Y f
    obtain ⟨f, rfl⟩ := (equivShrink _).surjective f
    simpa [shrinkYoneda] using ((τ.naturality_ap

Depends on / 依赖: equivShrink
-/
noncomputable def shrinkYonedaEquiv {X : C} {P : Cᵒᵖ ⥤ Type w} :
    (shrinkYoneda.{w}.obj X ⟶ P) ≃ P.obj (op X) where
  toFun τ := τ.app _ (equivShrink.{w} _ (𝟙 X))
  invFun x :=
    { app Y := ↾fun f => P.map ((equivShrink.{w} _).symm f).op x
      naturality Y Z g := by ext; simp [shrinkYoneda] }
  left_inv τ := by
    ext Y f
    obtain ⟨f, rfl⟩ := (equivShrink _).surjective f
    simpa [shrinkYoneda] using ((τ.naturality_apply f.op) (equivShrink _ (𝟙 X))).symm
  right_inv x := by simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `map_shrinkYonedaEquiv` / 引理 `map_shrinkYonedaEquiv`

English:
lemma map_shrinkYonedaEquiv
  statement: {X Y : C} {P : Cᵒᵖ ⥤ Type w} (f : shrinkYoneda.obj X ⟶ P)
  proof: by
  simp [shrinkYonedaObjObjEquiv, shrinkYonedaEquiv, shrinkYoneda,
    ← comp_apply, ← NatTrans.naturality]

中文:
引理 map_shrinkYonedaEquiv
  结论: {X Y : C} {P : Cᵒᵖ ⥤ Type w} (f : shrinkYoneda.obj X ⟶ P)
  证明: by
  simp [shrinkYonedaObjObjEquiv, shrinkYonedaEquiv, shrinkYoneda,
    ← comp_apply, ← NatTrans.naturality]

Depends on / 依赖: NatTrans, NatTrans.naturality, comp_apply, naturality, shrinkYoneda, shrinkYonedaEquiv, shrinkYonedaObjObjEquiv
-/
lemma map_shrinkYonedaEquiv {X Y : C} {P : Cᵒᵖ ⥤ Type w} (f : shrinkYoneda.obj X ⟶ P)
    (g : Y ⟶ X) : P.map g.op (shrinkYonedaEquiv f) =
      f.app (op Y) (shrinkYonedaObjObjEquiv.symm g) := by
  simp [shrinkYonedaObjObjEquiv, shrinkYonedaEquiv, shrinkYoneda,
    ← comp_apply, ← NatTrans.naturality]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `shrinkYonedaEquiv_shrinkYoneda_map` / 引理 `shrinkYonedaEquiv_shrinkYoneda_map`

English:
lemma shrinkYonedaEquiv_shrinkYoneda_map
  given: {X Y : C} (f : X ⟶ Y)
  proof: by
  simp [shrinkYonedaEquiv, shrinkYoneda, shrinkYonedaObjObjEquiv]

中文:
引理 shrinkYonedaEquiv_shrinkYoneda_map
  条件: {X Y : C} (f : X ⟶ Y)
  证明: by
  simp [shrinkYonedaEquiv, shrinkYoneda, shrinkYonedaObjObjEquiv]

Depends on / 依赖: shrinkYoneda, shrinkYonedaEquiv, shrinkYonedaObjObjEquiv
-/
lemma shrinkYonedaEquiv_shrinkYoneda_map {X Y : C} (f : X ⟶ Y) :
    shrinkYonedaEquiv (shrinkYoneda.{w}.map f) = shrinkYonedaObjObjEquiv.symm f := by
  simp [shrinkYonedaEquiv, shrinkYoneda, shrinkYonedaObjObjEquiv]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `shrinkYonedaEquiv_comp` / 引理 `shrinkYonedaEquiv_comp`

English:
lemma shrinkYonedaEquiv_comp
  statement: {X : C} {P Q : Cᵒᵖ ⥤ Type w} (α : shrinkYoneda.obj X ⟶ P)
  proof: by
  simp [shrinkYonedaEquiv]

中文:
引理 shrinkYonedaEquiv_comp
  结论: {X : C} {P Q : Cᵒᵖ ⥤ Type w} (α : shrinkYoneda.obj X ⟶ P)
  证明: by
  simp [shrinkYonedaEquiv]

Depends on / 依赖: shrinkYonedaEquiv
-/
lemma shrinkYonedaEquiv_comp {X : C} {P Q : Cᵒᵖ ⥤ Type w} (α : shrinkYoneda.obj X ⟶ P)
    (β : P ⟶ Q) :
    shrinkYonedaEquiv (α ≫ β) = β.app _ (shrinkYonedaEquiv α) := by
  simp [shrinkYonedaEquiv]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `shrinkYonedaEquiv_naturality` / 引理 `shrinkYonedaEquiv_naturality`

English:
lemma shrinkYonedaEquiv_naturality
  statement: {X Y : C} {P : Cᵒᵖ ⥤ Type w}
  proof: by
  simpa [shrinkYonedaEquiv, shrinkYoneda]
    using (f.naturality_apply g.op ((equivShrink _) (𝟙 _))).symm

@[reassoc]

中文:
引理 shrinkYonedaEquiv_naturality
  结论: {X Y : C} {P : Cᵒᵖ ⥤ Type w}
  证明: by
  simpa [shrinkYonedaEquiv, shrinkYoneda]
    using (f.naturality_apply g.op ((equivShrink _) (𝟙 _))).symm

@[reassoc]

Depends on / 依赖: equivShrink, f.naturality_apply, g.op, naturality_apply, shrinkYoneda, shrinkYonedaEquiv
-/
lemma shrinkYonedaEquiv_naturality {X Y : C} {P : Cᵒᵖ ⥤ Type w}
    (f : shrinkYoneda.obj X ⟶ P) (g : Y ⟶ X) :
    P.map g.op (shrinkYonedaEquiv f) = shrinkYonedaEquiv (shrinkYoneda.map g ≫ f) := by
  simpa [shrinkYonedaEquiv, shrinkYoneda]
    using (f.naturality_apply g.op ((equivShrink _) (𝟙 _))).symm

@[reassoc]
/--
lemma `shrinkYonedaEquiv_symm_map` / 引理 `shrinkYonedaEquiv_symm_map`

English:
lemma shrinkYonedaEquiv_symm_map
  given: {X Y : Cᵒᵖ} (f : X ⟶ Y) {P : Cᵒᵖ ⥤ Type w} (t : P.obj X)
  proof: shrinkYonedaEquiv.injective (by
    obtain ⟨t, rfl⟩ := shrinkYonedaEquiv.surjective t
    rw [← shrinkYonedaEquiv_naturality]
    simp)

中文:
引理 shrinkYonedaEquiv_symm_map
  条件: {X Y : Cᵒᵖ} (f : X ⟶ Y) {P : Cᵒᵖ ⥤ Type w} (t : P.obj X)
  证明: shrinkYonedaEquiv.injective (by
    obtain ⟨t, rfl⟩ := shrinkYonedaEquiv.surjective t
    rw [← shrinkYonedaEquiv_naturality]
    simp)

Depends on / 依赖: injective, shrinkYonedaEquiv, shrinkYonedaEquiv.injective, shrinkYonedaEquiv.surjective, shrinkYonedaEquiv_naturality, surjective
-/
lemma shrinkYonedaEquiv_symm_map {X Y : Cᵒᵖ} (f : X ⟶ Y) {P : Cᵒᵖ ⥤ Type w} (t : P.obj X) :
    shrinkYonedaEquiv.symm (P.map f t) =
      shrinkYoneda.map f.unop ≫ shrinkYonedaEquiv.symm t :=
  shrinkYonedaEquiv.injective (by
    obtain ⟨t, rfl⟩ := shrinkYonedaEquiv.surjective t
    rw [← shrinkYonedaEquiv_naturality]
    simp)

/--
lemma `shrinkYonedaEquiv_symm_app_shrinkYonedaObjObjEquiv_symm` / 引理 `shrinkYonedaEquiv_symm_app_shrinkYonedaObjObjEquiv_symm`

English:
lemma shrinkYonedaEquiv_symm_app_shrinkYonedaObjObjEquiv_symm
  statement: {X : C} {P : Cᵒᵖ ⥤ Type w}
  proof: by
  obtain ⟨g, rfl⟩ := shrinkYonedaEquiv.surjective s
  simp [map_shrinkYonedaEquiv]

中文:
引理 shrinkYonedaEquiv_symm_app_shrinkYonedaObjObjEquiv_symm
  结论: {X : C} {P : Cᵒᵖ ⥤ Type w}
  证明: by
  obtain ⟨g, rfl⟩ := shrinkYonedaEquiv.surjective s
  simp [map_shrinkYonedaEquiv]

Depends on / 依赖: map_shrinkYonedaEquiv, shrinkYonedaEquiv, shrinkYonedaEquiv.surjective, surjective
-/
lemma shrinkYonedaEquiv_symm_app_shrinkYonedaObjObjEquiv_symm {X : C} {P : Cᵒᵖ ⥤ Type w}
    (s : P.obj (op X)) {Y : C} (f : Y ⟶ X) :
    (shrinkYonedaEquiv.symm s).app (op Y) (shrinkYonedaObjObjEquiv.symm f) =
      P.map f.op s := by
  obtain ⟨g, rfl⟩ := shrinkYonedaEquiv.surjective s
  simp [map_shrinkYonedaEquiv]

set_option backward.isDefEq.respectTransparency.types false in
variable (C) in
/--
Definition of `fullyFaithfulShrinkYoneda` / `fullyFaithfulShrinkYoneda` 的定义

English:
definition fullyFaithfulShrinkYoneda
  signature: :
  body: shrinkYonedaObjObjEquiv (shrinkYonedaEquiv f)
  map_preimage f := by
    obtain ⟨f, rfl⟩ := shrinkYonedaEquiv.symm.surjective f
    cat_disch
  preimage_map f := by simp [shrinkYonedaEquiv_shrinkYoneda_map]

中文:
定义 fullyFaithfulShrinkYoneda
  签名: :
  定义体: shrinkYonedaObjObjEquiv (shrinkYonedaEquiv f)
  map_preimage f := by
    obtain ⟨f, rfl⟩ := shrinkYonedaEquiv.symm.surjective f
    cat_disch
  preimage_map f := by simp [shrinkYonedaEquiv_shrinkYoneda_map]

Depends on / 依赖: FullyFaithful
-/
noncomputable def fullyFaithfulShrinkYoneda :
    (shrinkYoneda.{w} (C := C)).FullyFaithful where
  preimage f := shrinkYonedaObjObjEquiv (shrinkYonedaEquiv f)
  map_preimage f := by
    obtain ⟨f, rfl⟩ := shrinkYonedaEquiv.symm.surjective f
    cat_disch
  preimage_map f := by simp [shrinkYonedaEquiv_shrinkYoneda_map]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (shrinkYoneda.{w} (C := C)).Faithful
  body: (fullyFaithfulShrinkYoneda C).faithful

中文:
实例 :
  签名: (shrinkYoneda.{w} (C := C)).Faithful
  定义体: (fullyFaithfulShrinkYoneda C).faithful

Depends on / 依赖: Faithful, faithful, fullyFaithfulShrinkYoneda
-/
instance : (shrinkYoneda.{w} (C := C)).Faithful := (fullyFaithfulShrinkYoneda C).faithful

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (shrinkYoneda.{w} (C := C)).Full
  body: (fullyFaithfulShrinkYoneda C).full

中文:
实例 :
  签名: (shrinkYoneda.{w} (C := C)).Full
  定义体: (fullyFaithfulShrinkYoneda C).full

Depends on / 依赖: fullyFaithfulShrinkYoneda
-/
instance : (shrinkYoneda.{w} (C := C)).Full := (fullyFaithfulShrinkYoneda C).full

set_option backward.defeqAttrib.useBackward true in
/-- `shrinkYoneda` at the morphism universe level is `yoneda`. -/
@[simps! hom_app inv_app]
noncomputable
/--
Definition of `shrinkYonedaIsoYoneda` / `shrinkYonedaIsoYoneda` 的定义

English:
definition shrinkYonedaIsoYoneda
  signature: : shrinkYoneda.{v} ≅ yoneda (C := C)
  body: NatIso.ofComponents
    (fun X => NatIso.ofComponents (fun Y => shrinkYonedaObjObjEquiv.toIso)
      (by intros; ext; simp [shrinkYonedaObjObjEquiv_obj_map]))
    (by intros; ext; simp [shrinkYonedaObjObjEquiv_map_app])

中文:
定义 shrinkYonedaIsoYoneda
  签名: : shrinkYoneda.{v} ≅ yoneda (C := C)
  定义体: NatIso.ofComponents
    (fun X => NatIso.ofComponents (fun Y => shrinkYonedaObjObjEquiv.toIso)
      (by intros; ext; simp [shrinkYonedaObjObjEquiv_obj_map]))
    (by intros; ext; simp [shrinkYonedaObjObjEquiv_map_app])
-/
def shrinkYonedaIsoYoneda : shrinkYoneda.{v} ≅ yoneda (C := C) :=
  NatIso.ofComponents
    (fun X => NatIso.ofComponents (fun Y => shrinkYonedaObjObjEquiv.toIso)
      (by intros; ext; simp [shrinkYonedaObjObjEquiv_obj_map]))
    (by intros; ext; simp [shrinkYonedaObjObjEquiv_map_app])

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- `shrinkYoneda` is compatible with `uliftFunctor`. -/
noncomputable
/--
Definition of `shrinkYonedaUliftFunctorIso` / `shrinkYonedaUliftFunctorIso` 的定义

English:
definition shrinkYonedaUliftFunctorIso
  signature: [LocallySmall.{max w w'} C]
  body: NatIso.ofComponents
    (fun X => FunctorToTypes.shrinkCompUliftFunctorIso.{w, v} (yoneda.obj X))
    fun _ => by ext; simp [shrinkYoneda]

中文:
定义 shrinkYonedaUliftFunctorIso
  签名: [LocallySmall.{max w w'} C]
  定义体: NatIso.ofComponents
    (fun X => FunctorToTypes.shrinkCompUliftFunctorIso.{w, v} (yoneda.obj X))
    fun _ => by ext; simp [shrinkYoneda]

Depends on / 依赖: FunctorToTypes, FunctorToTypes.shrinkCompUliftFunctorIso, NatIso, NatIso.ofComponents, ofComponents, shrinkCompUliftFunctorIso, shrinkYoneda, yoneda, yoneda.obj
-/
def shrinkYonedaUliftFunctorIso [LocallySmall.{max w w'} C] :
    shrinkYoneda.{w} ⋙ (Functor.whiskeringRight Cᵒᵖ _ _).obj uliftFunctor.{w', w} ≅
      shrinkYoneda :=
  NatIso.ofComponents
    (fun X => FunctorToTypes.shrinkCompUliftFunctorIso.{w, v} (yoneda.obj X))
    fun _ => by ext; simp [shrinkYoneda]

/--
Definition of `uliftYonedaIsoShrinkYoneda` / `uliftYonedaIsoShrinkYoneda` 的定义

English:
definition uliftYonedaIsoShrinkYoneda
  signature: :
  body: NatIso.ofComponents (fun X => NatIso.ofComponents
    (fun Y => (Equiv.ulift.trans shrinkYonedaObjObjEquiv.symm).toIso) (fun f => by
      ext
      exact (shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm _ _).symm)) (fun g => by
      ext
      exact (shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_s

中文:
定义 uliftYonedaIsoShrinkYoneda
  签名: :
  定义体: NatIso.ofComponents (fun X => NatIso.ofComponents
    (fun Y => (Equiv.ulift.trans shrinkYonedaObjObjEquiv.symm).toIso) (fun f => by
      ext
      exact (shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm _ _).symm)) (fun g => by
      ext
      exact (shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_s

Depends on / 依赖: shrinkYoneda
-/
noncomputable def uliftYonedaIsoShrinkYoneda :
    uliftYoneda.{w'} (C := C) ≅ shrinkYoneda.{max w' v} :=
  NatIso.ofComponents (fun X => NatIso.ofComponents
    (fun Y => (Equiv.ulift.trans shrinkYonedaObjObjEquiv.symm).toIso) (fun f => by
      ext
      exact (shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm _ _).symm)) (fun g => by
      ext
      exact (shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm _ _).symm)

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `shrinkYonedaCompEvaluationCompUliftFunctorIsoUliftFunctor` / `shrinkYonedaCompEvaluationCompUliftFunctorIsoUliftFunctor` 的定义

English:
definition shrinkYonedaCompEvaluationCompUliftFunctorIsoUliftFunctor
  signature: (Y : Cᵒᵖ)
  body: NatIso.ofComponents (fun X => (Equiv.ulift.trans
    (shrinkYonedaObjObjEquiv.trans Equiv.ulift.symm)).toIso) (fun f => by
      ext ⟨g⟩
      obtain ⟨g, rfl⟩ := shrinkYonedaObjObjEquiv.symm.surjective g
      simp [shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm])

中文:
定义 shrinkYonedaCompEvaluationCompUliftFunctorIsoUliftFunctor
  签名: (Y : Cᵒᵖ)
  定义体: NatIso.ofComponents (fun X => (Equiv.ulift.trans
    (shrinkYonedaObjObjEquiv.trans Equiv.ulift.symm)).toIso) (fun f => by
      ext ⟨g⟩
      obtain ⟨g, rfl⟩ := shrinkYonedaObjObjEquiv.symm.surjective g
      simp [shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm])

Depends on / 依赖: Equiv.ulift.symm, Equiv.ulift.trans, NatIso, NatIso.ofComponents, ofComponents, shrinkYonedaObjObjEquiv, shrinkYonedaObjObjEquiv.symm.surjective, shrinkYonedaObjObjEquiv.trans, shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm, surjective
-/
noncomputable def shrinkYonedaCompEvaluationCompUliftFunctorIsoUliftFunctor (Y : Cᵒᵖ) :
    shrinkYoneda.{w} ⋙ (evaluation Cᵒᵖ _).obj Y ⋙ uliftFunctor.{v} ≅
      coyoneda.obj Y ⋙ uliftFunctor.{w} :=
  NatIso.ofComponents (fun X => (Equiv.ulift.trans
    (shrinkYonedaObjObjEquiv.trans Equiv.ulift.symm)).toIso) (fun f => by
      ext ⟨g⟩
      obtain ⟨g, rfl⟩ := shrinkYonedaObjObjEquiv.symm.surjective g
      simp [shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm])

/-- `shrinkYoneda.obj X` is represented by `X`. -/
@[simps]
noncomputable
/--
Definition of `shrinkYonedaRepresentableBy` / `shrinkYonedaRepresentableBy` 的定义

English:
definition shrinkYonedaRepresentableBy
  signature: (X : C)
  body: shrinkYonedaObjObjEquiv.symm
  homEquiv_comp := shrinkYonedaObjObjEquiv_symm_comp

中文:
定义 shrinkYonedaRepresentableBy
  签名: (X : C)
  定义体: shrinkYonedaObjObjEquiv.symm
  homEquiv_comp := shrinkYonedaObjObjEquiv_symm_comp

Depends on / 依赖: shrinkYonedaObjObjEquiv, shrinkYonedaObjObjEquiv.symm
-/
def shrinkYonedaRepresentableBy (X : C) : (shrinkYoneda.{w}.obj X).RepresentableBy X where
  homEquiv := shrinkYonedaObjObjEquiv.symm
  homEquiv_comp := shrinkYonedaObjObjEquiv_symm_comp

instance (X : C) : (shrinkYoneda.{w}.obj X).IsRepresentable :=
  (shrinkYonedaRepresentableBy X).isRepresentable

end Yoneda

section Coyoneda

set_option backward.defeqAttrib.useBackward true in
instance (X : Cᵒᵖ) : FunctorToTypes.Small.{w} (coyoneda.obj X) :=
  fun _ => by dsimp; infer_instance

/-- The co-Yoneda embedding `Cᵒᵖ ⥤ C ⥤ Type w` for a locally `w`-small category `C`. -/
@[pp_with_univ]
/--
Definition of `shrinkCoyoneda` / `shrinkCoyoneda` 的定义

English:
abbreviation shrinkCoyoneda
  signature: : Cᵒᵖ ⥤ C ⥤ Type w
  body: shrinkYoneda.flip

中文:
缩写 shrinkCoyoneda
  签名: : Cᵒᵖ ⥤ C ⥤ Type w
  定义体: shrinkYoneda.flip

Depends on / 依赖: shrinkYoneda, shrinkYoneda.flip
-/
noncomputable abbrev shrinkCoyoneda : Cᵒᵖ ⥤ C ⥤ Type w := shrinkYoneda.flip

/--
lemma `shrinkCoyoneda_obj` / 引理 `shrinkCoyoneda_obj`

English:
lemma shrinkCoyoneda_obj
  given: {X : Cᵒᵖ}
  proof: rfl

中文:
引理 shrinkCoyoneda_obj
  条件: {X : Cᵒᵖ}
  证明: rfl
-/
lemma shrinkCoyoneda_obj {X : Cᵒᵖ} :
    shrinkCoyoneda.obj X = FunctorToTypes.shrink (coyoneda.obj X) := rfl

/--
lemma `shrinkCoyoneda_map` / 引理 `shrinkCoyoneda_map`

English:
lemma shrinkCoyoneda_map
  given: {X Y : Cᵒᵖ} {f : X ⟶ Y}
  proof: rfl

中文:
引理 shrinkCoyoneda_map
  条件: {X Y : Cᵒᵖ} {f : X ⟶ Y}
  证明: rfl
-/
lemma shrinkCoyoneda_map {X Y : Cᵒᵖ} {f : X ⟶ Y} :
    shrinkCoyoneda.map f = FunctorToTypes.shrinkMap (coyoneda.map f) := rfl

/--
Definition of `shrinkCoyonedaObjObjEquiv` / `shrinkCoyonedaObjObjEquiv` 的定义

English:
abbreviation shrinkCoyonedaObjObjEquiv
  signature: {X : Cᵒᵖ} {Y : C}
  body: shrinkYonedaObjObjEquiv

中文:
缩写 shrinkCoyonedaObjObjEquiv
  签名: {X : Cᵒᵖ} {Y : C}
  定义体: shrinkYonedaObjObjEquiv

Depends on / 依赖: shrinkYonedaObjObjEquiv
-/
noncomputable abbrev shrinkCoyonedaObjObjEquiv {X : Cᵒᵖ} {Y : C} :
    ((shrinkCoyoneda.{w}.obj X).obj Y) ≃ (X.unop ⟶ Y) :=
  shrinkYonedaObjObjEquiv

/--
lemma `shrinkCoyoneda_obj_map` / 引理 `shrinkCoyoneda_obj_map`

English:
lemma shrinkCoyoneda_obj_map
  given: {X : Cᵒᵖ} {Y Y' : C} (g : Y ⟶ Y') (f : (shrinkCoyoneda.obj X).obj Y)
  proof: rfl

中文:
引理 shrinkCoyoneda_obj_map
  条件: {X : Cᵒᵖ} {Y Y' : C} (g : Y ⟶ Y') (f : (shrinkCoyoneda.obj X).obj Y)
  证明: rfl
-/
lemma shrinkCoyoneda_obj_map {X : Cᵒᵖ} {Y Y' : C} (g : Y ⟶ Y') (f : (shrinkCoyoneda.obj X).obj Y) :
    (shrinkCoyoneda.obj _).map g f =
      shrinkCoyonedaObjObjEquiv.symm (shrinkCoyonedaObjObjEquiv f ≫ g) :=
  rfl

/--
lemma `shrinkCoyoneda_obj_map_shrinkCoyonedaObjObjEquiv_symm` / 引理 `shrinkCoyoneda_obj_map_shrinkCoyonedaObjObjEquiv_symm`

English:
lemma shrinkCoyoneda_obj_map_shrinkCoyonedaObjObjEquiv_symm
  proof: shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm f g

中文:
引理 shrinkCoyoneda_obj_map_shrinkCoyonedaObjObjEquiv_symm
  证明: shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm f g

Depends on / 依赖: shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm
-/
lemma shrinkCoyoneda_obj_map_shrinkCoyonedaObjObjEquiv_symm
    {X : Cᵒᵖ} {Y Y' : C} (g : Y ⟶ Y') (f : X.unop ⟶ Y) :
    (shrinkCoyoneda.obj _).map g (shrinkCoyonedaObjObjEquiv.symm f) =
      shrinkCoyonedaObjObjEquiv.symm (f ≫ g) :=
  shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm f g

/--
lemma `shrinkCoyonedaObjObjEquiv_symm_comp` / 引理 `shrinkCoyonedaObjObjEquiv_symm_comp`

English:
lemma shrinkCoyonedaObjObjEquiv_symm_comp
  given: {X Y Y' : C} (g : Y' ⟶ Y) (f : Y ⟶ X)
  proof: (shrinkCoyoneda_obj_map_shrinkCoyonedaObjObjEquiv_symm f g).symm

中文:
引理 shrinkCoyonedaObjObjEquiv_symm_comp
  条件: {X Y Y' : C} (g : Y' ⟶ Y) (f : Y ⟶ X)
  证明: (shrinkCoyoneda_obj_map_shrinkCoyonedaObjObjEquiv_symm f g).symm

Depends on / 依赖: shrinkCoyoneda_obj_map_shrinkCoyonedaObjObjEquiv_symm
-/
lemma shrinkCoyonedaObjObjEquiv_symm_comp {X Y Y' : C} (g : Y' ⟶ Y) (f : Y ⟶ X) :
    shrinkCoyonedaObjObjEquiv.symm (g ≫ f) =
    (shrinkCoyoneda.obj _).map f (shrinkCoyonedaObjObjEquiv.symm g) :=
  (shrinkCoyoneda_obj_map_shrinkCoyonedaObjObjEquiv_symm f g).symm

/--
lemma `shrinkCoyoneda_map_app_shrinkCoyonedaObjObjEquiv_symm` / 引理 `shrinkCoyoneda_map_app_shrinkCoyonedaObjObjEquiv_symm`

English:
lemma shrinkCoyoneda_map_app_shrinkCoyonedaObjObjEquiv_symm
  proof: shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm g f

@[reassoc]

中文:
引理 shrinkCoyoneda_map_app_shrinkCoyonedaObjObjEquiv_symm
  证明: shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm g f

@[reassoc]

Depends on / 依赖: shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm
-/
lemma shrinkCoyoneda_map_app_shrinkCoyonedaObjObjEquiv_symm
    {X X' : Cᵒᵖ} {Y : C} (f : X.unop ⟶ Y) (g : X ⟶ X') :
    (shrinkCoyoneda.map g).app _ (shrinkCoyonedaObjObjEquiv.symm f) =
      shrinkCoyonedaObjObjEquiv.symm (g.unop ≫ f) :=
  shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm g f

@[reassoc]
/--
lemma `shrinkCoyonedaObjObjEquiv_map_app` / 引理 `shrinkCoyonedaObjObjEquiv_map_app`

English:
lemma shrinkCoyonedaObjObjEquiv_map_app
  proof: shrinkYonedaObjObjEquiv_obj_map g f

@[reassoc]

中文:
引理 shrinkCoyonedaObjObjEquiv_map_app
  证明: shrinkYonedaObjObjEquiv_obj_map g f

@[reassoc]

Depends on / 依赖: shrinkYonedaObjObjEquiv_obj_map
-/
lemma shrinkCoyonedaObjObjEquiv_map_app
    {X X' : Cᵒᵖ} {Y : C} (f : (shrinkCoyoneda.{w, v, u}.obj X).obj Y) (g : X ⟶ X') :
    shrinkCoyonedaObjObjEquiv ((shrinkCoyoneda.map g).app Y f) =
      g.unop ≫ shrinkCoyonedaObjObjEquiv f :=
  shrinkYonedaObjObjEquiv_obj_map g f

@[reassoc]
/--
lemma `shrinkCoyonedaObjObjEquiv_obj_map` / 引理 `shrinkCoyonedaObjObjEquiv_obj_map`

English:
lemma shrinkCoyonedaObjObjEquiv_obj_map
  statement: {X : Cᵒᵖ} {Y Y' : C} (g : Y ⟶ Y')
  proof: shrinkYonedaObjObjEquiv_map_app f g

中文:
引理 shrinkCoyonedaObjObjEquiv_obj_map
  结论: {X : Cᵒᵖ} {Y Y' : C} (g : Y ⟶ Y')
  证明: shrinkYonedaObjObjEquiv_map_app f g

Depends on / 依赖: shrinkYonedaObjObjEquiv_map_app
-/
lemma shrinkCoyonedaObjObjEquiv_obj_map {X : Cᵒᵖ} {Y Y' : C} (g : Y ⟶ Y')
    (f : (shrinkCoyoneda.{w}.obj X).obj Y) :
    shrinkCoyonedaObjObjEquiv ((shrinkCoyoneda.{w}.obj X).map g f) =
      shrinkCoyonedaObjObjEquiv f ≫ g :=
  shrinkYonedaObjObjEquiv_map_app f g

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `shrinkCoyonedaEquiv` / `shrinkCoyonedaEquiv` 的定义

English:
definition shrinkCoyonedaEquiv
  signature: {X : Cᵒᵖ} {P : C ⥤ Type w}
  body: τ.app _ (equivShrink.{w} _ (𝟙 X.unop))
  invFun x :=
    { app Y := ↾fun f => P.map ((equivShrink.{w} _).symm f) x
      naturality Y Z g := by ext; simp [shrinkYoneda] }
  left_inv τ := by
    ext Y f
    obtain ⟨f, rfl⟩ := (equivShrink _).surjective f
    simpa [shrinkYoneda] using ((τ.naturality_

中文:
定义 shrinkCoyonedaEquiv
  签名: {X : Cᵒᵖ} {P : C ⥤ Type w}
  定义体: τ.app _ (equivShrink.{w} _ (𝟙 X.unop))
  invFun x :=
    { app Y := ↾fun f => P.map ((equivShrink.{w} _).symm f) x
      naturality Y Z g := by ext; simp [shrinkYoneda] }
  left_inv τ := by
    ext Y f
    obtain ⟨f, rfl⟩ := (equivShrink _).surjective f
    simpa [shrinkYoneda] using ((τ.naturality_

Depends on / 依赖: X.unop, equivShrink
-/
noncomputable def shrinkCoyonedaEquiv {X : Cᵒᵖ} {P : C ⥤ Type w} :
    (shrinkCoyoneda.{w}.obj X ⟶ P) ≃ P.obj X.unop where
  toFun τ := τ.app _ (equivShrink.{w} _ (𝟙 X.unop))
  invFun x :=
    { app Y := ↾fun f => P.map ((equivShrink.{w} _).symm f) x
      naturality Y Z g := by ext; simp [shrinkYoneda] }
  left_inv τ := by
    ext Y f
    obtain ⟨f, rfl⟩ := (equivShrink _).surjective f
    simpa [shrinkYoneda] using ((τ.naturality_apply f) (equivShrink _ (𝟙 X.unop))).symm
  right_inv x := by simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `map_shrinkCoyonedaEquiv` / 引理 `map_shrinkCoyonedaEquiv`

English:
lemma map_shrinkCoyonedaEquiv
  statement: {X Y : Cᵒᵖ} {P : C ⥤ Type w} (f : shrinkCoyoneda.obj X ⟶ P)
  proof: by
  simp [shrinkYonedaObjObjEquiv, shrinkCoyonedaEquiv, shrinkYoneda,
    ← comp_apply, ← NatTrans.naturality]

中文:
引理 map_shrinkCoyonedaEquiv
  结论: {X Y : Cᵒᵖ} {P : C ⥤ Type w} (f : shrinkCoyoneda.obj X ⟶ P)
  证明: by
  simp [shrinkYonedaObjObjEquiv, shrinkCoyonedaEquiv, shrinkYoneda,
    ← comp_apply, ← NatTrans.naturality]

Depends on / 依赖: NatTrans, NatTrans.naturality, comp_apply, naturality, shrinkCoyonedaEquiv, shrinkYoneda, shrinkYonedaObjObjEquiv
-/
lemma map_shrinkCoyonedaEquiv {X Y : Cᵒᵖ} {P : C ⥤ Type w} (f : shrinkCoyoneda.obj X ⟶ P)
    (g : Y ⟶ X) : P.map g.unop (shrinkCoyonedaEquiv f) =
      f.app Y.unop (shrinkCoyonedaObjObjEquiv.symm g.unop) := by
  simp [shrinkYonedaObjObjEquiv, shrinkCoyonedaEquiv, shrinkYoneda,
    ← comp_apply, ← NatTrans.naturality]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `shrinkCoyonedaEquiv_shrinkCoyoneda_map` / 引理 `shrinkCoyonedaEquiv_shrinkCoyoneda_map`

English:
lemma shrinkCoyonedaEquiv_shrinkCoyoneda_map
  given: {X Y : Cᵒᵖ} (f : X ⟶ Y)
  proof: by
  simp [shrinkCoyonedaEquiv, shrinkYoneda, shrinkYonedaObjObjEquiv]

中文:
引理 shrinkCoyonedaEquiv_shrinkCoyoneda_map
  条件: {X Y : Cᵒᵖ} (f : X ⟶ Y)
  证明: by
  simp [shrinkCoyonedaEquiv, shrinkYoneda, shrinkYonedaObjObjEquiv]

Depends on / 依赖: shrinkCoyonedaEquiv, shrinkYoneda, shrinkYonedaObjObjEquiv
-/
lemma shrinkCoyonedaEquiv_shrinkCoyoneda_map {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    shrinkCoyonedaEquiv (shrinkCoyoneda.{w}.map f) = shrinkCoyonedaObjObjEquiv.symm f.unop := by
  simp [shrinkCoyonedaEquiv, shrinkYoneda, shrinkYonedaObjObjEquiv]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `shrinkCoyonedaEquiv_comp` / 引理 `shrinkCoyonedaEquiv_comp`

English:
lemma shrinkCoyonedaEquiv_comp
  statement: {X : Cᵒᵖ} {P Q : C ⥤ Type w} (α : shrinkCoyoneda.obj X ⟶ P)
  proof: by
  simp [shrinkCoyonedaEquiv]

中文:
引理 shrinkCoyonedaEquiv_comp
  结论: {X : Cᵒᵖ} {P Q : C ⥤ Type w} (α : shrinkCoyoneda.obj X ⟶ P)
  证明: by
  simp [shrinkCoyonedaEquiv]

Depends on / 依赖: shrinkCoyonedaEquiv
-/
lemma shrinkCoyonedaEquiv_comp {X : Cᵒᵖ} {P Q : C ⥤ Type w} (α : shrinkCoyoneda.obj X ⟶ P)
    (β : P ⟶ Q) :
    shrinkCoyonedaEquiv (α ≫ β) = β.app _ (shrinkCoyonedaEquiv α) := by
  simp [shrinkCoyonedaEquiv]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `shrinkCoyonedaEquiv_naturality` / 引理 `shrinkCoyonedaEquiv_naturality`

English:
lemma shrinkCoyonedaEquiv_naturality
  statement: {X Y : Cᵒᵖ} {P : C ⥤ Type w}
  proof: by
  simpa [shrinkCoyonedaEquiv, shrinkYoneda]
    using (f.naturality_apply g.unop ((equivShrink _) (𝟙 _))).symm

@[reassoc]

中文:
引理 shrinkCoyonedaEquiv_naturality
  结论: {X Y : Cᵒᵖ} {P : C ⥤ Type w}
  证明: by
  simpa [shrinkCoyonedaEquiv, shrinkYoneda]
    using (f.naturality_apply g.unop ((equivShrink _) (𝟙 _))).symm

@[reassoc]

Depends on / 依赖: equivShrink, f.naturality_apply, g.unop, naturality_apply, shrinkCoyonedaEquiv, shrinkYoneda
-/
lemma shrinkCoyonedaEquiv_naturality {X Y : Cᵒᵖ} {P : C ⥤ Type w}
    (f : shrinkCoyoneda.obj X ⟶ P) (g : Y ⟶ X) :
    P.map g.unop (shrinkCoyonedaEquiv f) = shrinkCoyonedaEquiv (shrinkCoyoneda.map g ≫ f) := by
  simpa [shrinkCoyonedaEquiv, shrinkYoneda]
    using (f.naturality_apply g.unop ((equivShrink _) (𝟙 _))).symm

@[reassoc]
/--
lemma `shrinkCoyonedaEquiv_symm_map` / 引理 `shrinkCoyonedaEquiv_symm_map`

English:
lemma shrinkCoyonedaEquiv_symm_map
  given: {X Y : C} (f : X ⟶ Y) {P : C ⥤ Type w} (t : P.obj X)
  proof: shrinkCoyonedaEquiv.injective (by
    obtain ⟨t, rfl⟩ := shrinkCoyonedaEquiv.surjective t
    rw [← shrinkCoyonedaEquiv_naturality]
    simp)

中文:
引理 shrinkCoyonedaEquiv_symm_map
  条件: {X Y : C} (f : X ⟶ Y) {P : C ⥤ Type w} (t : P.obj X)
  证明: shrinkCoyonedaEquiv.injective (by
    obtain ⟨t, rfl⟩ := shrinkCoyonedaEquiv.surjective t
    rw [← shrinkCoyonedaEquiv_naturality]
    simp)

Depends on / 依赖: injective, shrinkCoyonedaEquiv, shrinkCoyonedaEquiv.injective, shrinkCoyonedaEquiv.surjective, shrinkCoyonedaEquiv_naturality, surjective
-/
lemma shrinkCoyonedaEquiv_symm_map {X Y : C} (f : X ⟶ Y) {P : C ⥤ Type w} (t : P.obj X) :
    shrinkCoyonedaEquiv.symm (P.map f t) =
      shrinkCoyoneda.map f.op ≫ shrinkCoyonedaEquiv.symm t :=
  shrinkCoyonedaEquiv.injective (by
    obtain ⟨t, rfl⟩ := shrinkCoyonedaEquiv.surjective t
    rw [← shrinkCoyonedaEquiv_naturality]
    simp)

/--
lemma `shrinkCoyonedaEquiv_symm_app_shrinkCoyonedaObjObjEquiv_symm` / 引理 `shrinkCoyonedaEquiv_symm_app_shrinkCoyonedaObjObjEquiv_symm`

English:
lemma shrinkCoyonedaEquiv_symm_app_shrinkCoyonedaObjObjEquiv_symm
  statement: {X : Cᵒᵖ} {P : C ⥤ Type w}
  proof: by
  obtain ⟨g, rfl⟩ := shrinkCoyonedaEquiv.surjective s
  simp [map_shrinkCoyonedaEquiv]

中文:
引理 shrinkCoyonedaEquiv_symm_app_shrinkCoyonedaObjObjEquiv_symm
  结论: {X : Cᵒᵖ} {P : C ⥤ Type w}
  证明: by
  obtain ⟨g, rfl⟩ := shrinkCoyonedaEquiv.surjective s
  simp [map_shrinkCoyonedaEquiv]

Depends on / 依赖: map_shrinkCoyonedaEquiv, shrinkCoyonedaEquiv, shrinkCoyonedaEquiv.surjective, surjective
-/
lemma shrinkCoyonedaEquiv_symm_app_shrinkCoyonedaObjObjEquiv_symm {X : Cᵒᵖ} {P : C ⥤ Type w}
    (s : P.obj X.unop) {Y : Cᵒᵖ} (f : Y ⟶ X) :
    (shrinkCoyonedaEquiv.symm s).app Y.unop (shrinkCoyonedaObjObjEquiv.symm f.unop) =
      P.map f.unop s := by
  obtain ⟨g, rfl⟩ := shrinkCoyonedaEquiv.surjective s
  simp [map_shrinkCoyonedaEquiv]

variable (C) in
/--
Definition of `fullyFaithfulShrinkCoyoneda` / `fullyFaithfulShrinkCoyoneda` 的定义

English:
definition fullyFaithfulShrinkCoyoneda
  signature: :
  body: (shrinkCoyonedaObjObjEquiv (shrinkCoyonedaEquiv f)).op
  map_preimage f := by
    obtain ⟨f, rfl⟩ := shrinkCoyonedaEquiv.symm.surjective f
    cat_disch
  preimage_map f := by
    simp [shrinkCoyonedaEquiv_shrinkCoyoneda_map f]

中文:
定义 fullyFaithfulShrinkCoyoneda
  签名: :
  定义体: (shrinkCoyonedaObjObjEquiv (shrinkCoyonedaEquiv f)).op
  map_preimage f := by
    obtain ⟨f, rfl⟩ := shrinkCoyonedaEquiv.symm.surjective f
    cat_disch
  preimage_map f := by
    simp [shrinkCoyonedaEquiv_shrinkCoyoneda_map f]

Depends on / 依赖: FullyFaithful
-/
noncomputable def fullyFaithfulShrinkCoyoneda :
    (shrinkCoyoneda.{w} (C := C)).FullyFaithful where
  preimage f := (shrinkCoyonedaObjObjEquiv (shrinkCoyonedaEquiv f)).op
  map_preimage f := by
    obtain ⟨f, rfl⟩ := shrinkCoyonedaEquiv.symm.surjective f
    cat_disch
  preimage_map f := by
    simp [shrinkCoyonedaEquiv_shrinkCoyoneda_map f]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (shrinkCoyoneda.{w} (C := C)).Faithful
  body: (fullyFaithfulShrinkCoyoneda C).faithful

中文:
实例 :
  签名: (shrinkCoyoneda.{w} (C := C)).Faithful
  定义体: (fullyFaithfulShrinkCoyoneda C).faithful

Depends on / 依赖: Faithful, faithful, fullyFaithfulShrinkCoyoneda
-/
instance : (shrinkCoyoneda.{w} (C := C)).Faithful := (fullyFaithfulShrinkCoyoneda C).faithful

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (shrinkCoyoneda.{w} (C := C)).Full
  body: (fullyFaithfulShrinkCoyoneda C).full

中文:
实例 :
  签名: (shrinkCoyoneda.{w} (C := C)).Full
  定义体: (fullyFaithfulShrinkCoyoneda C).full

Depends on / 依赖: fullyFaithfulShrinkCoyoneda
-/
instance : (shrinkCoyoneda.{w} (C := C)).Full := (fullyFaithfulShrinkCoyoneda C).full

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- `shrinkCoyoneda` at the morphism universe level is `coyoneda`. -/
@[simps! hom_app inv_app]
noncomputable
/--
Definition of `shrinkCoyonedaIsoCoyoneda` / `shrinkCoyonedaIsoCoyoneda` 的定义

English:
definition shrinkCoyonedaIsoCoyoneda
  signature: : shrinkCoyoneda.{v} ≅ coyoneda (C := C)
  body: NatIso.ofComponents
    (fun X => NatIso.ofComponents (fun Y => shrinkCoyonedaObjObjEquiv.toIso)
      (by intros; ext; simp [shrinkYonedaObjObjEquiv_map_app]))
    (by intros; ext; simp [shrinkYonedaObjObjEquiv_obj_map])

中文:
定义 shrinkCoyonedaIsoCoyoneda
  签名: : shrinkCoyoneda.{v} ≅ coyoneda (C := C)
  定义体: NatIso.ofComponents
    (fun X => NatIso.ofComponents (fun Y => shrinkCoyonedaObjObjEquiv.toIso)
      (by intros; ext; simp [shrinkYonedaObjObjEquiv_map_app]))
    (by intros; ext; simp [shrinkYonedaObjObjEquiv_obj_map])
-/
def shrinkCoyonedaIsoCoyoneda : shrinkCoyoneda.{v} ≅ coyoneda (C := C) :=
  NatIso.ofComponents
    (fun X => NatIso.ofComponents (fun Y => shrinkCoyonedaObjObjEquiv.toIso)
      (by intros; ext; simp [shrinkYonedaObjObjEquiv_map_app]))
    (by intros; ext; simp [shrinkYonedaObjObjEquiv_obj_map])

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- `shrinkCoyoneda` is compatible with `uliftFunctor`. -/
noncomputable
/--
Definition of `shrinkCoyonedaUliftFunctorIso` / `shrinkCoyonedaUliftFunctorIso` 的定义

English:
definition shrinkCoyonedaUliftFunctorIso
  signature: [LocallySmall.{max w w'} C]
  body: NatIso.ofComponents
    (fun X => FunctorToTypes.shrinkCompUliftFunctorIso.{w, v} (coyoneda.obj X))
    fun _ => by ext; simp [shrinkYoneda]

中文:
定义 shrinkCoyonedaUliftFunctorIso
  签名: [LocallySmall.{max w w'} C]
  定义体: NatIso.ofComponents
    (fun X => FunctorToTypes.shrinkCompUliftFunctorIso.{w, v} (coyoneda.obj X))
    fun _ => by ext; simp [shrinkYoneda]

Depends on / 依赖: FunctorToTypes, FunctorToTypes.shrinkCompUliftFunctorIso, NatIso, NatIso.ofComponents, coyoneda, coyoneda.obj, ofComponents, shrinkCompUliftFunctorIso, shrinkYoneda
-/
def shrinkCoyonedaUliftFunctorIso [LocallySmall.{max w w'} C] :
    shrinkCoyoneda.{w} ⋙ (Functor.whiskeringRight Cᵒᵖ _ _).obj uliftFunctor.{w', w} ≅
      shrinkCoyoneda :=
  NatIso.ofComponents
    (fun X => FunctorToTypes.shrinkCompUliftFunctorIso.{w, v} (coyoneda.obj X))
    fun _ => by ext; simp [shrinkYoneda]

/--
Definition of `uliftYonedaIsoShrinkCoyoneda` / `uliftYonedaIsoShrinkCoyoneda` 的定义

English:
definition uliftYonedaIsoShrinkCoyoneda
  signature: :
  body: NatIso.ofComponents (fun X => NatIso.ofComponents
    (fun Y => (Equiv.ulift.trans shrinkCoyonedaObjObjEquiv.symm).toIso) (fun f => by
      ext
      exact (shrinkCoyoneda_obj_map_shrinkCoyonedaObjObjEquiv_symm _ _).symm)) (fun g => by
      ext
      exact (shrinkCoyoneda_map_app_shrinkCoyonedaObj

中文:
定义 uliftYonedaIsoShrinkCoyoneda
  签名: :
  定义体: NatIso.ofComponents (fun X => NatIso.ofComponents
    (fun Y => (Equiv.ulift.trans shrinkCoyonedaObjObjEquiv.symm).toIso) (fun f => by
      ext
      exact (shrinkCoyoneda_obj_map_shrinkCoyonedaObjObjEquiv_symm _ _).symm)) (fun g => by
      ext
      exact (shrinkCoyoneda_map_app_shrinkCoyonedaObj

Depends on / 依赖: shrinkCoyoneda
-/
noncomputable def uliftYonedaIsoShrinkCoyoneda :
    uliftCoyoneda.{w'} (C := C) ≅ shrinkCoyoneda.{max w' v} :=
  NatIso.ofComponents (fun X => NatIso.ofComponents
    (fun Y => (Equiv.ulift.trans shrinkCoyonedaObjObjEquiv.symm).toIso) (fun f => by
      ext
      exact (shrinkCoyoneda_obj_map_shrinkCoyonedaObjObjEquiv_symm _ _).symm)) (fun g => by
      ext
      exact (shrinkCoyoneda_map_app_shrinkCoyonedaObjObjEquiv_symm _ _).symm)

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `shrinkCoyonedaCompEvaluationCompUliftFunctorIsoUliftFunctor` / `shrinkCoyonedaCompEvaluationCompUliftFunctorIsoUliftFunctor` 的定义

English:
definition shrinkCoyonedaCompEvaluationCompUliftFunctorIsoUliftFunctor
  signature: (Y : C)
  body: NatIso.ofComponents (fun X => (Equiv.ulift.trans
    (shrinkCoyonedaObjObjEquiv.trans Equiv.ulift.symm)).toIso) (fun f => by
      ext ⟨g⟩
      obtain ⟨g, rfl⟩ := shrinkCoyonedaObjObjEquiv.symm.surjective g
      simp [shrinkYoneda, shrinkYonedaObjObjEquiv])

中文:
定义 shrinkCoyonedaCompEvaluationCompUliftFunctorIsoUliftFunctor
  签名: (Y : C)
  定义体: NatIso.ofComponents (fun X => (Equiv.ulift.trans
    (shrinkCoyonedaObjObjEquiv.trans Equiv.ulift.symm)).toIso) (fun f => by
      ext ⟨g⟩
      obtain ⟨g, rfl⟩ := shrinkCoyonedaObjObjEquiv.symm.surjective g
      simp [shrinkYoneda, shrinkYonedaObjObjEquiv])

Depends on / 依赖: Equiv.ulift.symm, Equiv.ulift.trans, NatIso, NatIso.ofComponents, ofComponents, shrinkCoyonedaObjObjEquiv, shrinkCoyonedaObjObjEquiv.symm.surjective, shrinkCoyonedaObjObjEquiv.trans, shrinkYoneda, shrinkYonedaObjObjEquiv, surjective
-/
noncomputable def shrinkCoyonedaCompEvaluationCompUliftFunctorIsoUliftFunctor (Y : C) :
    shrinkCoyoneda.{w} ⋙ (evaluation C _).obj Y ⋙ uliftFunctor.{v} ≅
      yoneda.obj Y ⋙ uliftFunctor.{w} :=
  NatIso.ofComponents (fun X => (Equiv.ulift.trans
    (shrinkCoyonedaObjObjEquiv.trans Equiv.ulift.symm)).toIso) (fun f => by
      ext ⟨g⟩
      obtain ⟨g, rfl⟩ := shrinkCoyonedaObjObjEquiv.symm.surjective g
      simp [shrinkYoneda, shrinkYonedaObjObjEquiv])

/-- `shrinkCoyoneda.obj X` is corepresented by `X`. -/
@[simps]
noncomputable
/--
Definition of `shrinkCoyonedaCorepresentableBy` / `shrinkCoyonedaCorepresentableBy` 的定义

English:
definition shrinkCoyonedaCorepresentableBy
  signature: (X : Cᵒᵖ)
  body: shrinkCoyonedaObjObjEquiv.symm
  homEquiv_comp f g := shrinkCoyonedaObjObjEquiv_symm_comp g f

中文:
定义 shrinkCoyonedaCorepresentableBy
  签名: (X : Cᵒᵖ)
  定义体: shrinkCoyonedaObjObjEquiv.symm
  homEquiv_comp f g := shrinkCoyonedaObjObjEquiv_symm_comp g f

Depends on / 依赖: shrinkCoyonedaObjObjEquiv, shrinkCoyonedaObjObjEquiv.symm
-/
def shrinkCoyonedaCorepresentableBy (X : Cᵒᵖ) :
    (shrinkCoyoneda.{w}.obj X).CorepresentableBy X.unop where
  homEquiv := shrinkCoyonedaObjObjEquiv.symm
  homEquiv_comp f g := shrinkCoyonedaObjObjEquiv_symm_comp g f

instance (X : Cᵒᵖ) : (shrinkCoyoneda.{w}.obj X).IsCorepresentable :=
  (shrinkCoyonedaCorepresentableBy X).isCorepresentable

end Coyoneda

end CategoryTheory
