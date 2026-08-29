/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory

/-!
# Functor categories have chosen finite products

If `C` is a category with chosen finite products, then so is `J ⥤ C`.

-/

@[expose] public section

namespace CategoryTheory

open Limits MonoidalCategory Category CartesianMonoidalCategory

universe v
variable {J C D E : Type*} [Category* J] [Category* C] [Category* D] [Category* E]
  [CartesianMonoidalCategory C] [CartesianMonoidalCategory E]

namespace Functor

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `cartesianMonoidalCategory` / 实例 `cartesianMonoidalCategory`

English:
instance cartesianMonoidalCategory
  signature: : CartesianMonoidalCategory (J ⥤ C) where
  body: { app _ := CartesianMonoidalCategory.fst _ _ }
  snd X Y := { app _ := CartesianMonoidalCategory.snd _ _ }
  tensorProductIsBinaryProduct X Y :=
    evaluationJointlyReflectsLimits _ (fun j =>
      (IsLimit.postcomposeHomEquiv
        (mapPairIso (by exact Iso.refl _) (by exact Iso.refl _)) _).1
  

中文:
实例 cartesianMonoidalCategory
  签名: : CartesianMonoidalCategory (J ⥤ C) where
  定义体: { app _ := CartesianMonoidalCategory.fst _ _ }
  snd X Y := { app _ := CartesianMonoidalCategory.snd _ _ }
  tensorProductIsBinaryProduct X Y :=
    evaluationJointlyReflectsLimits _ (fun j =>
      (IsLimit.postcomposeHomEquiv
        (mapPairIso (by exact Iso.refl _) (by exact Iso.refl _)) _).1
  

Depends on / 依赖: CartesianMonoidalCategory, CartesianMonoidalCategory.fst
-/
instance cartesianMonoidalCategory : CartesianMonoidalCategory (J ⥤ C) where
  fst X Y := { app _ := CartesianMonoidalCategory.fst _ _ }
  snd X Y := { app _ := CartesianMonoidalCategory.snd _ _ }
  tensorProductIsBinaryProduct X Y :=
    evaluationJointlyReflectsLimits _ (fun j =>
      (IsLimit.postcomposeHomEquiv
        (mapPairIso (by exact Iso.refl _) (by exact Iso.refl _)) _).1
        (IsLimit.ofIsoLimit
          (tensorProductIsBinaryProduct (X := X.obj j) (Y := Y.obj j))
          (Cone.ext (Iso.refl _) (by rintro ⟨_ | _⟩; all_goals cat_disch))))
  isTerminalTensorUnit :=
    evaluationJointlyReflectsLimits _
      fun _ => isLimitChangeEmptyCone _ isTerminalTensorUnit _ (.refl _)
  fst_def X Y := by
    ext
    simp only [Monoidal.tensorObj_obj, fst_def, asEmptyCone_pt, NatTrans.comp_app,
      Monoidal.tensorUnit_obj, Monoidal.whiskerLeft_app, Monoidal.rightUnitor_hom_app,
      Iso.cancel_iso_hom_right]
    congr
    subsingleton
  snd_def X Y := by
    ext
    simp only [Monoidal.tensorObj_obj, snd_def, asEmptyCone_pt, NatTrans.comp_app,
      Monoidal.tensorUnit_obj, Monoidal.whiskerRight_app, Monoidal.leftUnitor_hom_app,
      Iso.cancel_iso_hom_right]
    congr
    subsingleton

@[deprecated (since := "2026-03-07")] alias chosenTerminal := MonoidalCategory.tensorUnit
@[deprecated (since := "2026-03-07")] alias chosenTerminalIsTerminal :=
  CartesianMonoidalCategory.isTerminalTensorUnit

@[deprecated (since := "2026-03-07")] alias chosenProd := MonoidalCategory.tensorObj
@[deprecated (since := "2026-03-07")] alias chosenProd.fst := CartesianMonoidalCategory.fst
@[deprecated (since := "2026-03-07")] alias chosenProd.snd := CartesianMonoidalCategory.snd
@[deprecated (since := "2026-03-07")] alias chosenProd.isLimit :=
  CartesianMonoidalCategory.tensorProductIsBinaryProduct

namespace Monoidal

open CartesianMonoidalCategory

@[simp]
/--
lemma `tensorObj_obj` / 引理 `tensorObj_obj`

English:
lemma tensorObj_obj
  given: (F₁ F₂ : J ⥤ C) (j : J)
  statement: (F₁ otimes F₂).obj j = (F₁.obj j) otimes (F₂.obj j)
  proof: rfl

@[simp]

中文:
引理 tensorObj_obj
  条件: (F₁ F₂ : J ⥤ C) (j : J)
  结论: (F₁ otimes F₂).obj j = (F₁.obj j) otimes (F₂.obj j)
  证明: rfl

@[simp]
-/
lemma tensorObj_obj (F₁ F₂ : J ⥤ C) (j : J) : (F₁ otimes F₂).obj j = (F₁.obj j) otimes (F₂.obj j) := rfl

@[simp]
/--
lemma `tensorObj_map` / 引理 `tensorObj_map`

English:
lemma tensorObj_map
  given: (F₁ F₂ : J ⥤ C) {j j' : J} (f : j ⟶ j')
  proof: rfl

@[simp]

中文:
引理 tensorObj_map
  条件: (F₁ F₂ : J ⥤ C) {j j' : J} (f : j ⟶ j')
  证明: rfl

@[simp]
-/
lemma tensorObj_map (F₁ F₂ : J ⥤ C) {j j' : J} (f : j ⟶ j') :
    (F₁ otimes F₂).map f = (F₁.map f) otimesₘ (F₂.map f) := rfl

@[simp]
/--
lemma `fst_app` / 引理 `fst_app`

English:
lemma fst_app
  given: (F₁ F₂ : J ⥤ C) (j : J)
  statement: (fst F₁ F₂).app j = fst (F₁.obj j) (F₂.obj j)
  proof: rfl

@[simp]

中文:
引理 fst_app
  条件: (F₁ F₂ : J ⥤ C) (j : J)
  结论: (fst F₁ F₂).app j = fst (F₁.obj j) (F₂.obj j)
  证明: rfl

@[simp]
-/
lemma fst_app (F₁ F₂ : J ⥤ C) (j : J) : (fst F₁ F₂).app j = fst (F₁.obj j) (F₂.obj j) := rfl

@[simp]
/--
lemma `snd_app` / 引理 `snd_app`

English:
lemma snd_app
  given: (F₁ F₂ : J ⥤ C) (j : J)
  statement: (snd F₁ F₂).app j = snd (F₁.obj j) (F₂.obj j)
  proof: rfl

@[simp]

中文:
引理 snd_app
  条件: (F₁ F₂ : J ⥤ C) (j : J)
  结论: (snd F₁ F₂).app j = snd (F₁.obj j) (F₂.obj j)
  证明: rfl

@[simp]
-/
lemma snd_app (F₁ F₂ : J ⥤ C) (j : J) : (snd F₁ F₂).app j = snd (F₁.obj j) (F₂.obj j) := rfl

@[simp]
/--
lemma `leftUnitor_hom_app` / 引理 `leftUnitor_hom_app`

English:
lemma leftUnitor_hom_app
  given: (F : J ⥤ C) (j : J)
  proof: rfl

中文:
引理 leftUnitor_hom_app
  条件: (F : J ⥤ C) (j : J)
  证明: rfl
-/
lemma leftUnitor_hom_app (F : J ⥤ C) (j : J) :
    (fun_ F).hom.app j = (fun_ (F.obj j)).hom := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `leftUnitor_inv_app` / 引理 `leftUnitor_inv_app`

English:
lemma leftUnitor_inv_app
  given: (F : J ⥤ C) (j : J)
  proof: by
  rw [← cancel_mono ((fun_ (F.obj j)).hom)]; rw [Iso.inv_hom_id]; rw [← leftUnitor_hom_app]; rw [Iso.inv_hom_id_app]

@[simp]

中文:
引理 leftUnitor_inv_app
  条件: (F : J ⥤ C) (j : J)
  证明: by
  rw [← cancel_mono ((fun_ (F.obj j)).hom)]; rw [Iso.inv_hom_id]; rw [← leftUnitor_hom_app]; rw [Iso.inv_hom_id_app]

@[simp]

Depends on / 依赖: F.obj, Iso.inv_hom_id, Iso.inv_hom_id_app, cancel_mono, fun_, inv_hom_id, inv_hom_id_app, leftUnitor_hom_app
-/
lemma leftUnitor_inv_app (F : J ⥤ C) (j : J) :
    (fun_ F).inv.app j = (fun_ (F.obj j)).inv := by
  rw [← cancel_mono ((fun_ (F.obj j)).hom)]; rw [Iso.inv_hom_id]; rw [← leftUnitor_hom_app]; rw [Iso.inv_hom_id_app]

@[simp]
/--
lemma `rightUnitor_hom_app` / 引理 `rightUnitor_hom_app`

English:
lemma rightUnitor_hom_app
  given: (F : J ⥤ C) (j : J)
  proof: rfl

中文:
引理 rightUnitor_hom_app
  条件: (F : J ⥤ C) (j : J)
  证明: rfl
-/
lemma rightUnitor_hom_app (F : J ⥤ C) (j : J) :
    (ρ_ F).hom.app j = (ρ_ (F.obj j)).hom := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `rightUnitor_inv_app` / 引理 `rightUnitor_inv_app`

English:
lemma rightUnitor_inv_app
  given: (F : J ⥤ C) (j : J)
  proof: by
  rw [← cancel_mono ((ρ_ (F.obj j)).hom)]; rw [Iso.inv_hom_id]; rw [← rightUnitor_hom_app]; rw [Iso.inv_hom_id_app]

中文:
引理 rightUnitor_inv_app
  条件: (F : J ⥤ C) (j : J)
  证明: by
  rw [← cancel_mono ((ρ_ (F.obj j)).hom)]; rw [Iso.inv_hom_id]; rw [← rightUnitor_hom_app]; rw [Iso.inv_hom_id_app]

Depends on / 依赖: F.obj, Iso.inv_hom_id, Iso.inv_hom_id_app, cancel_mono, inv_hom_id, inv_hom_id_app, rightUnitor_hom_app
-/
lemma rightUnitor_inv_app (F : J ⥤ C) (j : J) :
    (ρ_ F).inv.app j = (ρ_ (F.obj j)).inv := by
  rw [← cancel_mono ((ρ_ (F.obj j)).hom)]; rw [Iso.inv_hom_id]; rw [← rightUnitor_hom_app]; rw [Iso.inv_hom_id_app]

/--
lemma `tensorHom_app_fst` / 引理 `tensorHom_app_fst`

English:
lemma tensorHom_app_fst
  given: {F₁ F₁' F₂ F₂' : J ⥤ C} (f : F₁ ⟶ F₁') (g : F₂ ⟶ F₂') (j : J)
  proof: by
  simp

中文:
引理 tensorHom_app_fst
  条件: {F₁ F₁' F₂ F₂' : J ⥤ C} (f : F₁ ⟶ F₁') (g : F₂ ⟶ F₂') (j : J)
  证明: by
  simp
-/
lemma tensorHom_app_fst {F₁ F₁' F₂ F₂' : J ⥤ C} (f : F₁ ⟶ F₁') (g : F₂ ⟶ F₂') (j : J) :
    (f otimesₘ g).app j ≫ fst _ _ = fst _ _ ≫ f.app j := by
  simp

/--
lemma `tensorHom_app_snd` / 引理 `tensorHom_app_snd`

English:
lemma tensorHom_app_snd
  given: {F₁ F₁' F₂ F₂' : J ⥤ C} (f : F₁ ⟶ F₁') (g : F₂ ⟶ F₂') (j : J)
  proof: by
  simp

中文:
引理 tensorHom_app_snd
  条件: {F₁ F₁' F₂ F₂' : J ⥤ C} (f : F₁ ⟶ F₁') (g : F₂ ⟶ F₂') (j : J)
  证明: by
  simp
-/
lemma tensorHom_app_snd {F₁ F₁' F₂ F₂' : J ⥤ C} (f : F₁ ⟶ F₁') (g : F₂ ⟶ F₂') (j : J) :
    (f otimesₘ g).app j ≫ snd _ _ = snd _ _ ≫ g.app j := by
  simp

/--
lemma `whiskerLeft_app_fst` / 引理 `whiskerLeft_app_fst`

English:
lemma whiskerLeft_app_fst
  given: (F₁ : J ⥤ C) {F₂ F₂' : J ⥤ C} (g : F₂ ⟶ F₂') (j : J)
  proof: by
  simp

中文:
引理 whiskerLeft_app_fst
  条件: (F₁ : J ⥤ C) {F₂ F₂' : J ⥤ C} (g : F₂ ⟶ F₂') (j : J)
  证明: by
  simp
-/
lemma whiskerLeft_app_fst (F₁ : J ⥤ C) {F₂ F₂' : J ⥤ C} (g : F₂ ⟶ F₂') (j : J) :
    (F₁ ◁ g).app j ≫ fst _ _ = fst _ _ := by
  simp

/--
lemma `whiskerLeft_app_snd` / 引理 `whiskerLeft_app_snd`

English:
lemma whiskerLeft_app_snd
  given: (F₁ : J ⥤ C) {F₂ F₂' : J ⥤ C} (g : F₂ ⟶ F₂') (j : J)
  proof: by
  simp

中文:
引理 whiskerLeft_app_snd
  条件: (F₁ : J ⥤ C) {F₂ F₂' : J ⥤ C} (g : F₂ ⟶ F₂') (j : J)
  证明: by
  simp
-/
lemma whiskerLeft_app_snd (F₁ : J ⥤ C) {F₂ F₂' : J ⥤ C} (g : F₂ ⟶ F₂') (j : J) :
    (F₁ ◁ g).app j ≫ snd _ _ = snd _ _ ≫ g.app j := by
  simp

/--
lemma `whiskerRight_app_fst` / 引理 `whiskerRight_app_fst`

English:
lemma whiskerRight_app_fst
  given: {F₁ F₁' : J ⥤ C} (f : F₁ ⟶ F₁') (F₂ : J ⥤ C) (j : J)
  proof: by
  simp

中文:
引理 whiskerRight_app_fst
  条件: {F₁ F₁' : J ⥤ C} (f : F₁ ⟶ F₁') (F₂ : J ⥤ C) (j : J)
  证明: by
  simp
-/
lemma whiskerRight_app_fst {F₁ F₁' : J ⥤ C} (f : F₁ ⟶ F₁') (F₂ : J ⥤ C) (j : J) :
    (f ▷ F₂).app j ≫ fst _ _ = fst _ _ ≫ f.app j := by
  simp

/--
lemma `whiskerRight_app_snd` / 引理 `whiskerRight_app_snd`

English:
lemma whiskerRight_app_snd
  given: {F₁ F₁' : J ⥤ C} (f : F₁ ⟶ F₁') (F₂ : J ⥤ C) (j : J)
  proof: by
  simp

@[simp]

中文:
引理 whiskerRight_app_snd
  条件: {F₁ F₁' : J ⥤ C} (f : F₁ ⟶ F₁') (F₂ : J ⥤ C) (j : J)
  证明: by
  simp

@[simp]
-/
lemma whiskerRight_app_snd {F₁ F₁' : J ⥤ C} (f : F₁ ⟶ F₁') (F₂ : J ⥤ C) (j : J) :
    (f ▷ F₂).app j ≫ snd _ _ = snd _ _ := by
  simp

@[simp]
/--
lemma `associator_hom_app` / 引理 `associator_hom_app`

English:
lemma associator_hom_app
  given: (F₁ F₂ F₃ : J ⥤ C) (j : J)
  proof: by
  simp

中文:
引理 associator_hom_app
  条件: (F₁ F₂ F₃ : J ⥤ C) (j : J)
  证明: by
  simp
-/
lemma associator_hom_app (F₁ F₂ F₃ : J ⥤ C) (j : J) :
    (α_ F₁ F₂ F₃).hom.app j = (α_ _ _ _).hom := by
  simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `associator_inv_app` / 引理 `associator_inv_app`

English:
lemma associator_inv_app
  given: (F₁ F₂ F₃ : J ⥤ C) (j : J)
  proof: by
  rw [← cancel_mono ((α_ _ _ _).hom)]; rw [Iso.inv_hom_id]; rw [← associator_hom_app]; rw [Iso.inv_hom_id_app]

中文:
引理 associator_inv_app
  条件: (F₁ F₂ F₃ : J ⥤ C) (j : J)
  证明: by
  rw [← cancel_mono ((α_ _ _ _).hom)]; rw [Iso.inv_hom_id]; rw [← associator_hom_app]; rw [Iso.inv_hom_id_app]

Depends on / 依赖: Iso.inv_hom_id, Iso.inv_hom_id_app, associator_hom_app, cancel_mono, inv_hom_id, inv_hom_id_app
-/
lemma associator_inv_app (F₁ F₂ F₃ : J ⥤ C) (j : J) :
    (α_ F₁ F₂ F₃).inv.app j = (α_ _ _ _).inv := by
  rw [← cancel_mono ((α_ _ _ _).hom)]; rw [Iso.inv_hom_id]; rw [← associator_hom_app]; rw [Iso.inv_hom_id_app]

set_option backward.defeqAttrib.useBackward true in
instance {K : Type*} [Category* K] [HasColimitsOfShape K C]
    [forall X : C, PreservesColimitsOfShape K (tensorLeft X)] {F : J ⥤ C} :
    PreservesColimitsOfShape K (tensorLeft F) := by
  apply preservesColimitsOfShape_of_evaluation
  intro k
  have : tensorLeft F ⋙ (evaluation J C).obj k ≅ (evaluation J C).obj k ⋙ tensorLeft (F.obj k) :=
    NatIso.ofComponents (fun _ => Iso.refl _)
  exact preservesColimitsOfShape_of_natIso this.symm

set_option backward.defeqAttrib.useBackward true in
/-- A finite-products-preserving functor distributes over the tensor product of functors. -/
@[simps!]
/--
Definition of `tensorObjComp` / `tensorObjComp` 的定义

English:
definition tensorObjComp
  signature: (F G : D ⥤ C) (H : C ⥤ E) [PreservesFiniteProducts H]
  body: NatIso.ofComponents (fun X => prodComparisonIso H (F.obj X) (G.obj X)) fun {X Y} f => by
    dsimp; ext <;> simp [← Functor.map_comp]

中文:
定义 tensorObjComp
  签名: (F G : D ⥤ C) (H : C ⥤ E) [PreservesFiniteProducts H]
  定义体: NatIso.ofComponents (fun X => prodComparisonIso H (F.obj X) (G.obj X)) fun {X Y} f => by
    dsimp; ext <;> simp [← Functor.map_comp]

Depends on / 依赖: F.obj, Functor, Functor.map_comp, G.obj, NatIso, NatIso.ofComponents, map_comp, ofComponents, prodComparisonIso
-/
noncomputable def tensorObjComp (F G : D ⥤ C) (H : C ⥤ E) [PreservesFiniteProducts H] :
    (F otimes G) ⋙ H ≅ (F ⋙ H) otimes (G ⋙ H) :=
  NatIso.ofComponents (fun X => prodComparisonIso H (F.obj X) (G.obj X)) fun {X Y} f => by
    dsimp; ext <;> simp [← Functor.map_comp]

/-- A tensor product of representable functors is representable. -/
@[simps]
/--
Definition of `RepresentableBy.tensorObj` / `RepresentableBy.tensorObj` 的定义

English:
definition RepresentableBy.tensorObj
  signature: {F : Cᵒᵖ ⥤ Type v} {G : Cᵒᵖ ⥤ Type v} {X Y : C}
  body: homEquivToProd.trans (h₁.homEquiv.prodCongr h₂.homEquiv)
  homEquiv_comp {I W} f g := by
    refine Prod.ext ?_ ?_
    · change h₁.homEquiv ((f ≫ g) ≫ fst X Y) = F.map f.op (h₁.homEquiv (g ≫ fst X Y))
      simp [h₁.homEquiv_comp]
    · change h₂.homEquiv ((f ≫ g) ≫ snd X Y) = G.map f.op (h₂.homEqui

中文:
定义 RepresentableBy.tensorObj
  签名: {F : Cᵒᵖ ⥤ 类型v} {G : Cᵒᵖ ⥤ 类型v} {X Y : C}
  定义体: homEquivToProd.trans (h₁.homEquiv.prodCongr h₂.homEquiv)
  homEquiv_comp {I W} f g := by
    refine Prod.ext ?_ ?_
    · change h₁.homEquiv ((f ≫ g) ≫ fst X Y) = F.map f.op (h₁.homEquiv (g ≫ fst X Y))
      simp [h₁.homEquiv_comp]
    · change h₂.homEquiv ((f ≫ g) ≫ snd X Y) = G.map f.op (h₂.homEqui
-/
protected def RepresentableBy.tensorObj {F : Cᵒᵖ ⥤ Type v} {G : Cᵒᵖ ⥤ Type v} {X Y : C}
    (h₁ : F.RepresentableBy X) (h₂ : G.RepresentableBy Y) : (F otimes G).RepresentableBy (X otimes Y) where
  homEquiv {I} := homEquivToProd.trans (h₁.homEquiv.prodCongr h₂.homEquiv)
  homEquiv_comp {I W} f g := by
    refine Prod.ext ?_ ?_
    · change h₁.homEquiv ((f ≫ g) ≫ fst X Y) = F.map f.op (h₁.homEquiv (g ≫ fst X Y))
      simp [h₁.homEquiv_comp]
    · change h₂.homEquiv ((f ≫ g) ≫ snd X Y) = G.map f.op (h₂.homEquiv (g ≫ snd X Y))
      simp [h₂.homEquiv_comp]

end Monoidal

end Functor

end CategoryTheory
