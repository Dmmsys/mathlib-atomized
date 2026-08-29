/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-!
# Transport a monoidal structure along an equivalence.

When `C` and `D` are equivalent as categories,
we can transport a monoidal structure on `C` along the equivalence as
`CategoryTheory.Monoidal.transport`, obtaining a monoidal structure on `D`.

More generally, we can transport the lawfulness of a monoidal structure along a suitable faithful
functor, as `CategoryTheory.Monoidal.induced`.
The comparison is analogous to the difference between `Equiv.monoid` and
`Function.Injective.monoid`.

We then upgrade the original functor and its inverse to monoidal functors
with respect to the new monoidal structure on `D`.
-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section


universe v₁ v₂ u₁ u₂

open CategoryTheory

open CategoryTheory.Category

open CategoryTheory.MonoidalCategory

namespace CategoryTheory.Monoidal

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/--
Definition of `InducingFunctorData` / `InducingFunctorData` 的定义

English:
structure InducingFunctorData
  parameters: [MonoidalCategoryStruct D] (F : D ⥤ C)
  axioms and operations (8):
    - μIso : forall X Y, F.obj X otimes F.obj Y ≅ F.obj (X otimes Y)
    - whiskerLeft_eq : forall (X : D) {Y₁ Y₂ : D} (f : Y₁ ⟶ Y₂), F.map (X ◁ f) = (μIso _ _).inv ≫ (F.obj X ◁ F.map f) ≫ (μIso _ _).hom  [default: by cat_disch]
    - whiskerRight_eq : forall {X₁ X₂ : D} (f : X₁ ⟶ X₂) (Y : D), F.map (f ▷ Y) = (μIso _ _).inv ≫ (F.map f ▷ F.obj Y) ≫ (μIso _ _).hom  [default: by cat_disch]
    - tensorHom_eq : forall {X₁ Y₁ X₂ Y₂ : D} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂), F.map (f otimesₘ g) = (μIso _ _).inv ≫ (F.map f otimesₘ F.map g) ≫ (μIso _ _).hom  [default: by cat_disch]
    - εIso : 𝟙_ _ ≅ F.obj (𝟙_ _)
    - associator_eq : forall X Y Z : D, F.map (α_ X Y Z).hom = (((μIso _ _).symm ≪≫ ((μIso _ _).symm otimesᵢ .refl _)) ≪≫ α_ (F.obj X) (F.obj Y) (F.obj Z) ≪≫ ((.refl _ otimesᵢ μIso _ _) ≪≫ μIso _ _)).hom  [default: by cat_disch]
    - leftUnitor_eq : forall X : D, F.map (fun_ X).hom = (((μIso _ _).symm ≪≫ (εIso.symm otimesᵢ .refl _)) ≪≫ fun_ (F.obj X)).hom  [default: by cat_disch]
    - rightUnitor_eq : forall X : D, F.map (ρ_ X).hom = (((μIso _ _).symm ≪≫ (.refl _ otimesᵢ εIso.symm)) ≪≫ ρ_ (F.obj X)).hom  [default: by cat_disch]

中文:
结构 InducingFunctorData
  参数: [幺半群范畴结构 D] (F : D ⥤ C)
  公理与运算 (8 个):
    - μIso : 对任意 X Y, F.obj X otimes F.obj Y ≅ F.obj (X otimes Y)
    - whiskerLeft_eq : 对任意 (X : D) {Y₁ Y₂ : D} (f : Y₁ ⟶ Y₂), F.map (X ◁ f) = (μIso _ _).inv ≫ (F.obj X ◁ F.map f) ≫ (μIso _ _).hom  [默认: by cat_disch]
    - whiskerRight_eq : 对任意 {X₁ X₂ : D} (f : X₁ ⟶ X₂) (Y : D), F.map (f ▷ Y) = (μIso _ _).inv ≫ (F.map f ▷ F.obj Y) ≫ (μIso _ _).hom  [默认: by cat_disch]
    - tensorHom_eq : 对任意 {X₁ Y₁ X₂ Y₂ : D} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂), F.map (f otimesₘ g) = (μIso _ _).inv ≫ (F.map f otimesₘ F.map g) ≫ (μIso _ _).hom  [默认: by cat_disch]
    - εIso : 𝟙_ _ ≅ F.obj (𝟙_ _)
    - associator_eq : 对任意 X Y Z : D, F.map (α_ X Y Z).hom = (((μIso _ _).symm ≪≫ ((μIso _ _).symm otimesᵢ .refl _)) ≪≫ α_ (F.obj X) (F.obj Y) (F.obj Z) ≪≫ ((.refl _ otimesᵢ μIso _ _) ≪≫ μIso _ _)).hom  [默认: by cat_disch]
    - leftUnitor_eq : 对任意 X : D, F.map (fun_ X).hom = (((μIso _ _).symm ≪≫ (εIso.symm otimesᵢ .refl _)) ≪≫ fun_ (F.obj X)).hom  [默认: by cat_disch]
    - rightUnitor_eq : 对任意 X : D, F.map (ρ_ X).hom = (((μIso _ _).symm ≪≫ (.refl _ otimesᵢ εIso.symm)) ≪≫ ρ_ (F.obj X)).hom  [默认: by cat_disch]

Depends on / 依赖: F.map, F.obj, cat_disch, tensorHom_eq, whiskerRight_eq
-/
structure InducingFunctorData [MonoidalCategoryStruct D] (F : D ⥤ C) where
  /-- Analogous to `CategoryTheory.LaxMonoidalFunctor.μIso` -/
  μIso : forall X Y,
    F.obj X otimes F.obj Y ≅ F.obj (X otimes Y)
  whiskerLeft_eq : forall (X : D) {Y₁ Y₂ : D} (f : Y₁ ⟶ Y₂),
    F.map (X ◁ f) = (μIso _ _).inv ≫ (F.obj X ◁ F.map f) ≫ (μIso _ _).hom := by
    cat_disch
  whiskerRight_eq : forall {X₁ X₂ : D} (f : X₁ ⟶ X₂) (Y : D),
    F.map (f ▷ Y) = (μIso _ _).inv ≫ (F.map f ▷ F.obj Y) ≫ (μIso _ _).hom := by
    cat_disch
  tensorHom_eq : forall {X₁ Y₁ X₂ Y₂ : D} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂),
    F.map (f otimesₘ g) = (μIso _ _).inv ≫ (F.map f otimesₘ F.map g) ≫ (μIso _ _).hom := by
    cat_disch
  /-- Analogous to `CategoryTheory.LaxMonoidalFunctor.εIso` -/
  εIso : 𝟙_ _ ≅ F.obj (𝟙_ _)
  associator_eq : forall X Y Z : D,
    F.map (α_ X Y Z).hom =
      (((μIso _ _).symm ≪≫ ((μIso _ _).symm otimesᵢ .refl _))
        ≪≫ α_ (F.obj X) (F.obj Y) (F.obj Z)
        ≪≫ ((.refl _ otimesᵢ μIso _ _) ≪≫ μIso _ _)).hom := by
    cat_disch
  leftUnitor_eq : forall X : D,
    F.map (fun_ X).hom =
      (((μIso _ _).symm ≪≫ (εIso.symm otimesᵢ .refl _)) ≪≫ fun_ (F.obj X)).hom := by
    cat_disch
  rightUnitor_eq : forall X : D,
    F.map (ρ_ X).hom =
      (((μIso _ _).symm ≪≫ (.refl _ otimesᵢ εIso.symm)) ≪≫ ρ_ (F.obj X)).hom := by
    cat_disch

/--
Induce the lawfulness of the monoidal structure along a faithful functor of (plain) categories,
where the operations are already defined on the destination type `D`.

The functor `F` must preserve all the data parts of the monoidal structure between the two
categories.
-/
@[instance_reducible]
/--
Definition of `induced` / `induced` 的定义

English:
definition induced
  signature: [MonoidalCategoryStruct D] (F : D ⥤ C) [F.Faithful]
  body: F.map_injective by
    rw [fData.tensorHom_eq]; rw [Functor.map_comp]; rw [fData.whiskerRight_eq]; rw [fData.whiskerLeft_eq]
    simp only [tensorHom_def, assoc, Iso.hom_inv_id_assoc]
id_tensorHom_id X₁ X₂ := F.map_injective by cases fData; cat_disch
tensorHom_comp_tensorHom f₁ f₂ g₁ g₂ := F.map_injective by cases fData; cat_disch
whiskerLeft_id X Y := F.map_injective by simp [fData.whiskerLeft_eq]
id_whiskerRight X Y := F.map_injective by simp [fData.whiskerRight_eq]
triangle X Y := F.map_injective by cases fData; cat_disch
pentagon W X Y Z := F.map_injective by
    simp only [Functor.map_comp, fData.whiskerRight_eq, fData.associator_eq, Iso.trans_assoc,
      Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom, tensorHom_id, id_tensorHom,
      comp_whiskerRight, whisker_assoc, assoc, fData.whiskerLeft_eq, whiskerLeft_comp,
      Iso.hom_inv_id_assoc, whiskerLeft_hom_inv_assoc, hom_inv_whiskerRight_assoc,
      Iso.inv_hom_id_assoc, Iso.cancel_iso_inv_left]
    slice_lhs 5 6 =>
      rw [← whiskerLeft_comp]; rw [hom_inv_whiskerRight]
    rw [whisker_exchange_assoc]
    simp
leftUnitor_naturality {X Y : D} f := F.map_injective by
    simp [fData.leftUnitor_eq, fData.whiskerLeft_eq, whisker_exchange_assoc]
rightUnitor_naturality {X Y : D} f := F.map_injective by
    simp [fData.rightUnitor_eq, fData.whiskerRight_eq, ← whisker_exchange_assoc]
associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} f₁ f₂ f₃ := F.map_injective by
    simp [fData.tensorHom_eq, fData.associator_eq, tensorHom_def, whisker_exchange_assoc]

中文:
定义 induced
  签名: [幺半群范畴结构 D] (F : D ⥤ C) [F.忠实]
  定义体: F.map_injective by
    rw [fData.tensorHom_eq]; rw [Functor.map_comp]; rw [fData.whiskerRight_eq]; rw [fData.whiskerLeft_eq]
    simp only [tensorHom_def, assoc, Iso.hom_inv_id_assoc]
id_tensorHom_id X₁ X₂ := F.map_injective by cases fData; cat_disch
tensorHom_comp_tensorHom f₁ f₂ g₁ g₂ := F.map_injective by cases fData; cat_disch
whiskerLeft_id X Y := F.map_injective by simp [fData.whiskerLeft_eq]
id_whiskerRight X Y := F.map_injective by simp [fData.whiskerRight_eq]
triangle X Y := F.map_injective by cases fData; cat_disch
pentagon W X Y Z := F.map_injective by
    simp only [Functor.map_comp, fData.whiskerRight_eq, fData.associator_eq, Iso.trans_assoc,
      Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom, tensorHom_id, id_tensorHom,
      comp_whiskerRight, whisker_assoc, assoc, fData.whiskerLeft_eq, whiskerLeft_comp,
      Iso.hom_inv_id_assoc, whiskerLeft_hom_inv_assoc, hom_inv_whiskerRight_assoc,
      Iso.inv_hom_id_assoc, Iso.cancel_iso_inv_left]
    slice_lhs 5 6 =>
      rw [← whiskerLeft_comp]; rw [hom_inv_whiskerRight]
    rw [whisker_exchange_assoc]
    simp
leftUnitor_naturality {X Y : D} f := F.map_injective by
    simp [fData.leftUnitor_eq, fData.whiskerLeft_eq, whisker_exchange_assoc]
rightUnitor_naturality {X Y : D} f := F.map_injective by
    simp [fData.rightUnitor_eq, fData.whiskerRight_eq, ← whisker_exchange_assoc]
associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} f₁ f₂ f₃ := F.map_injective by
    simp [fData.tensorHom_eq, fData.associator_eq, tensorHom_def, whisker_exchange_assoc]

Depends on / 依赖: F.map_injective, Functor, Functor.map_comp, Iso.hom_inv_id_assoc, Subobject, Subobject.semilatticeInf, Subobject.semilatticeSup, cat_disch, fData.tensorHom_eq, fData.whiskerLeft_eq, fData.whiskerRight_eq, hom_inv_id_assoc, id_tensorHom_id, id_whiskerRight, map_comp, map_injective, semilatticeInf, semilatticeSup, tensorHom_comp_tensorHom, tensorHom_def
-/
def induced [MonoidalCategoryStruct D] (F : D ⥤ C) [F.Faithful]
    (fData : InducingFunctorData F) :
    MonoidalCategory.{v₂} D where
tensorHom_def {X₁ Y₁ X₂ Y₂} f g := F.map_injective by
    rw [fData.tensorHom_eq]; rw [Functor.map_comp]; rw [fData.whiskerRight_eq]; rw [fData.whiskerLeft_eq]
    simp only [tensorHom_def, assoc, Iso.hom_inv_id_assoc]
id_tensorHom_id X₁ X₂ := F.map_injective by cases fData; cat_disch
tensorHom_comp_tensorHom f₁ f₂ g₁ g₂ := F.map_injective by cases fData; cat_disch
whiskerLeft_id X Y := F.map_injective by simp [fData.whiskerLeft_eq]
id_whiskerRight X Y := F.map_injective by simp [fData.whiskerRight_eq]
triangle X Y := F.map_injective by cases fData; cat_disch
pentagon W X Y Z := F.map_injective by
    simp only [Functor.map_comp, fData.whiskerRight_eq, fData.associator_eq, Iso.trans_assoc,
      Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom, tensorHom_id, id_tensorHom,
      comp_whiskerRight, whisker_assoc, assoc, fData.whiskerLeft_eq, whiskerLeft_comp,
      Iso.hom_inv_id_assoc, whiskerLeft_hom_inv_assoc, hom_inv_whiskerRight_assoc,
      Iso.inv_hom_id_assoc, Iso.cancel_iso_inv_left]
    slice_lhs 5 6 =>
      rw [← whiskerLeft_comp]; rw [hom_inv_whiskerRight]
    rw [whisker_exchange_assoc]
    simp
leftUnitor_naturality {X Y : D} f := F.map_injective by
    simp [fData.leftUnitor_eq, fData.whiskerLeft_eq, whisker_exchange_assoc]
rightUnitor_naturality {X Y : D} f := F.map_injective by
    simp [fData.rightUnitor_eq, fData.whiskerRight_eq, ← whisker_exchange_assoc]
associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} f₁ f₂ f₃ := F.map_injective by
    simp [fData.tensorHom_eq, fData.associator_eq, tensorHom_def, whisker_exchange_assoc]

/--
Definition of `fromInducedCoreMonoidal` / `fromInducedCoreMonoidal` 的定义

English:
definition fromInducedCoreMonoidal
  signature: [MonoidalCategoryStruct D] (F : D ⥤ C) [F.Faithful]
  body: induced F fData
    F.CoreMonoidal := by
  letI := induced F fData
  exact
    { εIso := fData.εIso
      μIso := fData.μIso
      μIso_hom_natural_left := fun _ => by simp [fData.whiskerRight_eq]
      μIso_hom_natural_right := fun _ => by simp [fData.whiskerLeft_eq]
      associativity := fun _ _ _ => by simp [fData.associator_eq]
      left_unitality := fun _ => by simp [fData.leftUnitor_eq]
      right_unitality := fun _ => by simp [fData.rightUnitor_eq] }

中文:
定义 fromInducedCoreMonoidal
  签名: [幺半群范畴结构 D] (F : D ⥤ C) [F.忠实]
  定义体: induced F fData
    F.CoreMonoidal := by
  letI := induced F fData
  exact
    { εIso := fData.εIso
      μIso := fData.μIso
      μIso_hom_natural_left := fun _ => by simp [fData.whiskerRight_eq]
      μIso_hom_natural_right := fun _ => by simp [fData.whiskerLeft_eq]
      associativity := fun _ _ _ => by simp [fData.associator_eq]
      left_unitality := fun _ => by simp [fData.leftUnitor_eq]
      right_unitality := fun _ => by simp [fData.rightUnitor_eq] }

Depends on / 依赖: induced
-/
def fromInducedCoreMonoidal [MonoidalCategoryStruct D] (F : D ⥤ C) [F.Faithful]
    (fData : InducingFunctorData F) :
    letI := induced F fData
    F.CoreMonoidal := by
  letI := induced F fData
  exact
    { εIso := fData.εIso
      μIso := fData.μIso
      μIso_hom_natural_left := fun _ => by simp [fData.whiskerRight_eq]
      μIso_hom_natural_right := fun _ => by simp [fData.whiskerLeft_eq]
      associativity := fun _ _ _ => by simp [fData.associator_eq]
      left_unitality := fun _ => by simp [fData.leftUnitor_eq]
      right_unitality := fun _ => by simp [fData.rightUnitor_eq] }

/--
Instance `fromInducedMonoidal` / 实例 `fromInducedMonoidal`

English:
instance fromInducedMonoidal
  signature: [MonoidalCategoryStruct D] (F : D ⥤ C) [F.Faithful]
  body: induced F fData
    F.Monoidal :=
  letI := induced F fData
  (fromInducedCoreMonoidal F fData).toMonoidal

中文:
实例 fromInducedMonoidal
  签名: [幺半群范畴结构 D] (F : D ⥤ C) [F.忠实]
  定义体: induced F fData
    F.Monoidal :=
  letI := induced F fData
  (fromInducedCoreMonoidal F fData).toMonoidal

Depends on / 依赖: induced
-/
instance fromInducedMonoidal [MonoidalCategoryStruct D] (F : D ⥤ C) [F.Faithful]
    (fData : InducingFunctorData F) :
    letI := induced F fData
    F.Monoidal :=
  letI := induced F fData
  (fromInducedCoreMonoidal F fData).toMonoidal

/-- Transport a monoidal structure along an equivalence of (plain) categories.
-/
@[simps -isSimp, instance_reducible]
/--
Definition of `transportStruct` / `transportStruct` 的定义

English:
definition transportStruct
  signature: (e : C ≌ D)
  body: e.functor.obj (e.inverse.obj X otimes e.inverse.obj Y)
  whiskerLeft X _ _ f := e.functor.map (e.inverse.obj X ◁ e.inverse.map f)
  whiskerRight f X := e.functor.map (e.inverse.map f ▷ e.inverse.obj X)
  tensorHom f g := e.functor.map (e.inverse.map f otimesₘ e.inverse.map g)
  tensorUnit := e.functor.obj (𝟙_ C)
  associator X Y Z :=
    e.functor.mapIso
      (whiskerRightIso (e.unitIso.app _).symm _ ≪≫
        α_ (e.inverse.obj X) (e.inverse.obj Y) (e.inverse.obj Z) ≪≫
        whiskerLeftIso _ (e.unitIso.app _))
  leftUnitor X :=
    e.functor.mapIso ((whiskerRightIso (e.unitIso.app _).symm _) ≪≫ fun_ (e.inverse.obj X)) ≪≫
      e.counitIso.app _
  rightUnitor X :=
    e.functor.mapIso ((whiskerLeftIso _ (e.unitIso.app _).symm) ≪≫ ρ_ (e.inverse.obj X)) ≪≫
      e.counitIso.app _

#adaptation_note /-- Prior to https://github.com/leanprover/lean4/pull/12244
the fields `whiskerLeft_eq` and following were all filled by the `cat_disch` auto_param. -/

中文:
定义 transportStruct
  签名: (e : C ≌ D)
  定义体: e.functor.obj (e.inverse.obj X otimes e.inverse.obj Y)
  whiskerLeft X _ _ f := e.functor.map (e.inverse.obj X ◁ e.inverse.map f)
  whiskerRight f X := e.functor.map (e.inverse.map f ▷ e.inverse.obj X)
  tensorHom f g := e.functor.map (e.inverse.map f otimesₘ e.inverse.map g)
  tensorUnit := e.functor.obj (𝟙_ C)
  associator X Y Z :=
    e.functor.mapIso
      (whiskerRightIso (e.unitIso.app _).symm _ ≪≫
        α_ (e.inverse.obj X) (e.inverse.obj Y) (e.inverse.obj Z) ≪≫
        whiskerLeftIso _ (e.unitIso.app _))
  leftUnitor X :=
    e.functor.mapIso ((whiskerRightIso (e.unitIso.app _).symm _) ≪≫ fun_ (e.inverse.obj X)) ≪≫
      e.counitIso.app _
  rightUnitor X :=
    e.functor.mapIso ((whiskerLeftIso _ (e.unitIso.app _).symm) ≪≫ ρ_ (e.inverse.obj X)) ≪≫
      e.counitIso.app _

#adaptation_note /-- Prior to https://github.com/leanprover/lean4/pull/12244
the fields `whiskerLeft_eq` and following were all filled by the `cat_disch` auto_param. -/

Depends on / 依赖: e.functor.obj, e.inverse.obj, functor, inverse, otimes
-/
def transportStruct (e : C ≌ D) : MonoidalCategoryStruct.{v₂} D where
  tensorObj X Y := e.functor.obj (e.inverse.obj X otimes e.inverse.obj Y)
  whiskerLeft X _ _ f := e.functor.map (e.inverse.obj X ◁ e.inverse.map f)
  whiskerRight f X := e.functor.map (e.inverse.map f ▷ e.inverse.obj X)
  tensorHom f g := e.functor.map (e.inverse.map f otimesₘ e.inverse.map g)
  tensorUnit := e.functor.obj (𝟙_ C)
  associator X Y Z :=
    e.functor.mapIso
      (whiskerRightIso (e.unitIso.app _).symm _ ≪≫
        α_ (e.inverse.obj X) (e.inverse.obj Y) (e.inverse.obj Z) ≪≫
        whiskerLeftIso _ (e.unitIso.app _))
  leftUnitor X :=
    e.functor.mapIso ((whiskerRightIso (e.unitIso.app _).symm _) ≪≫ fun_ (e.inverse.obj X)) ≪≫
      e.counitIso.app _
  rightUnitor X :=
    e.functor.mapIso ((whiskerLeftIso _ (e.unitIso.app _).symm) ≪≫ ρ_ (e.inverse.obj X)) ≪≫
      e.counitIso.app _

#adaptation_note /-- Prior to https://github.com/leanprover/lean4/pull/12244
the fields `whiskerLeft_eq` and following were all filled by the `cat_disch` auto_param. -/
attribute [local simp] transportStruct in
/-- Transport a monoidal structure along an equivalence of (plain) categories.
-/
@[instance_reducible]
/--
Definition of `transport` / `transport` 的定义

English:
definition transport
  signature: (e : C ≌ D)
  body: letI : MonoidalCategoryStruct.{v₂} D := transportStruct e
  induced e.inverse
    { μIso := fun _ _ => e.unitIso.app _
      εIso := e.unitIso.app _
      whiskerLeft_eq := by simp +zetaDelta +instances
      whiskerRight_eq := by simp +zetaDelta +instances
      tensorHom_eq := by simp +zetaDelta +instances
      associator_eq := by simp +zetaDelta +instances
      leftUnitor_eq := by simp +zetaDelta +instances
      rightUnitor_eq := by simp +zetaDelta +instances }

中文:
定义 transport
  签名: (e : C ≌ D)
  定义体: letI : MonoidalCategoryStruct.{v₂} D := transportStruct e
  induced e.inverse
    { μIso := fun _ _ => e.unitIso.app _
      εIso := e.unitIso.app _
      whiskerLeft_eq := by simp +zetaDelta +instances
      whiskerRight_eq := by simp +zetaDelta +instances
      tensorHom_eq := by simp +zetaDelta +instances
      associator_eq := by simp +zetaDelta +instances
      leftUnitor_eq := by simp +zetaDelta +instances
      rightUnitor_eq := by simp +zetaDelta +instances }

Depends on / 依赖: MonoidalCategoryStruct, associator_eq, e.inverse, e.unitIso.app, induced, instances, inverse, leftUnitor_eq, rightUnitor_eq, tensorHom_eq, transportStruct, unitIso, whiskerLeft_eq, whiskerRight_eq, zetaDelta
-/
def transport (e : C ≌ D) : MonoidalCategory.{v₂} D :=
  letI : MonoidalCategoryStruct.{v₂} D := transportStruct e
  induced e.inverse
    { μIso := fun _ _ => e.unitIso.app _
      εIso := e.unitIso.app _
      whiskerLeft_eq := by simp +zetaDelta +instances
      whiskerRight_eq := by simp +zetaDelta +instances
      tensorHom_eq := by simp +zetaDelta +instances
      associator_eq := by simp +zetaDelta +instances
      leftUnitor_eq := by simp +zetaDelta +instances
      rightUnitor_eq := by simp +zetaDelta +instances }

/-- A type synonym for `D`, which will carry the transported monoidal structure. -/
@[nolint unusedArguments]
/--
Definition of `Transported` / `Transported` 的定义

English:
definition Transported
  signature: (_ : C ≌ D)
  body: D

中文:
定义 Transported
  签名: (_ : C ≌ D)
  定义体: D
-/
def Transported (_ : C ≌ D) := D

instance (e : C ≌ D) : Category (Transported e) := (inferInstance : Category D)

/--
Instance `Transported.instMonoidalCategoryStruct` / 实例 `Transported.instMonoidalCategoryStruct`

English:
instance Transported.instMonoidalCategoryStruct
  signature: (e : C ≌ D)
  body: transportStruct e

中文:
实例 Transported.instMonoidalCategoryStruct
  签名: (e : C ≌ D)
  定义体: transportStruct e

Depends on / 依赖: transportStruct
-/
instance Transported.instMonoidalCategoryStruct (e : C ≌ D) :
    MonoidalCategoryStruct (Transported e) :=
  transportStruct e

/--
Instance `Transported.instMonoidalCategory` / 实例 `Transported.instMonoidalCategory`

English:
instance Transported.instMonoidalCategory
  signature: (e : C ≌ D)
  body: transport e

中文:
实例 Transported.instMonoidalCategory
  签名: (e : C ≌ D)
  定义体: transport e

Depends on / 依赖: transport
-/
instance Transported.instMonoidalCategory (e : C ≌ D) : MonoidalCategory (Transported e) :=
  transport e

instance (e : C ≌ D) : Inhabited (Transported e) :=
  ⟨𝟙_ _⟩

section

variable (e : C ≌ D)

/--
Definition of `equivalenceTransported` / `equivalenceTransported` 的定义

English:
abbreviation equivalenceTransported
  signature: : C ≌ Transported e
  body: e

中文:
缩写 equivalenceTransported
  签名: : C ≌ Transported e
  定义体: e
-/
abbrev equivalenceTransported : C ≌ Transported e := e

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (equivalenceTransported e).inverse.Monoidal
  body: by
  dsimp +instances only [Transported.instMonoidalCategory]
  infer_instance

中文:
实例 :
  签名: (equivalenceTransported e).inverse.幺半群
  定义体: by
  dsimp +instances only [Transported.instMonoidalCategory]
  infer_instance

Depends on / 依赖: Transported, Transported.instMonoidalCategory, infer_instance, instMonoidalCategory, instances
-/
instance : (equivalenceTransported e).inverse.Monoidal := by
  dsimp +instances only [Transported.instMonoidalCategory]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (equivalenceTransported e).symm.functor.Monoidal
  body: inferInstanceAs (equivalenceTransported e).inverse.Monoidal

中文:
实例 :
  签名: (equivalenceTransported e).symm.functor.幺半群
  定义体: inferInstanceAs (equivalenceTransported e).inverse.Monoidal

Depends on / 依赖: Monoidal, equivalenceTransported, inverse, inverse.Monoidal
-/
instance : (equivalenceTransported e).symm.functor.Monoidal :=
  inferInstanceAs (equivalenceTransported e).inverse.Monoidal

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (equivalenceTransported e).functor.Monoidal
  body: (equivalenceTransported e).symm.inverseMonoidal

中文:
实例 :
  签名: (equivalenceTransported e).functor.幺半群
  定义体: (equivalenceTransported e).symm.inverseMonoidal

Depends on / 依赖: equivalenceTransported, inverseMonoidal, symm.inverseMonoidal
-/
noncomputable instance : (equivalenceTransported e).functor.Monoidal :=
  (equivalenceTransported e).symm.inverseMonoidal

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (equivalenceTransported e).symm.inverse.Monoidal
  body: inferInstanceAs (equivalenceTransported e).functor.Monoidal

中文:
实例 :
  签名: (equivalenceTransported e).symm.inverse.幺半群
  定义体: inferInstanceAs (equivalenceTransported e).functor.Monoidal

Depends on / 依赖: Monoidal, equivalenceTransported, functor, functor.Monoidal
-/
noncomputable instance : (equivalenceTransported e).symm.inverse.Monoidal :=
  inferInstanceAs (equivalenceTransported e).functor.Monoidal

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (equivalenceTransported e).symm.IsMonoidal
  body: by
  infer_instance

中文:
实例 :
  签名: (equivalenceTransported e).symm.是幺半群
  定义体: by
  infer_instance

Depends on / 依赖: infer_instance
-/
instance : (equivalenceTransported e).symm.IsMonoidal := by
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NatTrans.IsMonoidal (equivalenceTransported e).unit
  body: inferInstanceAs (NatTrans.IsMonoidal (equivalenceTransported e).symm.counitIso.inv)

中文:
实例 :
  签名: 自然变换.是幺半群 (equivalenceTransported e).unit
  定义体: inferInstanceAs (NatTrans.IsMonoidal (equivalenceTransported e).symm.counitIso.inv)

Depends on / 依赖: IsMonoidal, NatTrans, NatTrans.IsMonoidal, counitIso, equivalenceTransported, symm.counitIso.inv
-/
instance : NatTrans.IsMonoidal (equivalenceTransported e).unit :=
  inferInstanceAs (NatTrans.IsMonoidal (equivalenceTransported e).symm.counitIso.inv)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NatTrans.IsMonoidal (equivalenceTransported e).counit
  body: inferInstanceAs (NatTrans.IsMonoidal (equivalenceTransported e).symm.unitIso.inv)

中文:
实例 :
  签名: 自然变换.是幺半群 (equivalenceTransported e).counit
  定义体: inferInstanceAs (NatTrans.IsMonoidal (equivalenceTransported e).symm.unitIso.inv)

Depends on / 依赖: IsMonoidal, NatTrans, NatTrans.IsMonoidal, equivalenceTransported, symm.unitIso.inv, unitIso
-/
instance : NatTrans.IsMonoidal (equivalenceTransported e).counit :=
  inferInstanceAs (NatTrans.IsMonoidal (equivalenceTransported e).symm.unitIso.inv)

end

end CategoryTheory.Monoidal
