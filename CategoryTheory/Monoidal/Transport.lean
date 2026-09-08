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

/-- The data needed to induce a `MonoidalCategory` via the functor `F`; namely, pre-existing
definitions of `⊗`, `𝟙_`, `▷`, `◁` that are preserved by `F`.
-/
/-
**CategoryTheory.Monoidal.InducingFunctorData** 是 Mathlib 中的一个结构，位于命名空间 `Categor
yTheory.Monoidal`。
形式化陈述：InducingFunctorData [MonoidalCategoryStruct D] (F : D ⥤ C) where /-- Analo
gous to `CategoryTheory.LaxMonoidalFunctor.μIso` -/ μIso : forall X Y, F.obj X o
times F.obj Y ≅ F.obj (X otimes Y) whiskerLeft_eq : forall (X : D) {Y₁ Y₂ : D} (
f : Y₁ ⟶ Y₂), F.map (X ◁ f) = (μIso _ _).inv ≫ (F.obj X ◁ F.map f) ≫ (μIso _ _).
hom
参数：F : D ⥤ C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The data needed to induce a `MonoidalCategory` via the functor `F`; namely, pre-
existing
definitions of `⊗`, `𝟙_`, `▷`, `◁` that are preserved by `F`.
-/
structure InducingFunctorData [MonoidalCategoryStruct D] (F : D ⥤ C) where
  /-- Analogous to `CategoryTheory.LaxMonoidalFunctor.μIso` -/
  μIso : ∀ X Y,
    F.obj X ⊗ F.obj Y ≅ F.obj (X ⊗ Y)
  whiskerLeft_eq : ∀ (X : D) {Y₁ Y₂ : D} (f : Y₁ ⟶ Y₂),
    F.map (X ◁ f) = (μIso _ _).inv ≫ (F.obj X ◁ F.map f) ≫ (μIso _ _).hom := by
    cat_disch
  whiskerRight_eq : ∀ {X₁ X₂ : D} (f : X₁ ⟶ X₂) (Y : D),
    F.map (f ▷ Y) = (μIso _ _).inv ≫ (F.map f ▷ F.obj Y) ≫ (μIso _ _).hom := by
    cat_disch
  tensorHom_eq : ∀ {X₁ Y₁ X₂ Y₂ : D} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂),
    F.map (f ⊗ₘ g) = (μIso _ _).inv ≫ (F.map f ⊗ₘ F.map g) ≫ (μIso _ _).hom := by
    cat_disch
  /-- Analogous to `CategoryTheory.LaxMonoidalFunctor.εIso` -/
  εIso : 𝟙_ _ ≅ F.obj (𝟙_ _)
  associator_eq : ∀ X Y Z : D,
    F.map (α_ X Y Z).hom =
      (((μIso _ _).symm ≪≫ ((μIso _ _).symm ⊗ᵢ .refl _))
        ≪≫ α_ (F.obj X) (F.obj Y) (F.obj Z)
        ≪≫ ((.refl _ ⊗ᵢ μIso _ _) ≪≫ μIso _ _)).hom := by
    cat_disch
  leftUnitor_eq : ∀ X : D,
    F.map (λ_ X).hom =
      (((μIso _ _).symm ≪≫ (εIso.symm ⊗ᵢ .refl _)) ≪≫ λ_ (F.obj X)).hom := by
    cat_disch
  rightUnitor_eq : ∀ X : D,
    F.map (ρ_ X).hom =
      (((μIso _ _).symm ≪≫ (.refl _ ⊗ᵢ εIso.symm)) ≪≫ ρ_ (F.obj X)).hom := by
    cat_disch

/--
Induce the lawfulness of the monoidal structure along a faithful functor of (plain) categories,
where the operations are already defined on the destination type `D`.

The functor `F` must preserve all the data parts of the monoidal structure between the two
categories.
-/
@[instance_reducible]
/-
**CategoryTheory.Monoidal.induced** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Mono
idal`。
形式化陈述：induced [MonoidalCategoryStruct D] (F : D ⥤ C) [F.Faithful] (fData : Induc
ingFunctorData F) : MonoidalCategory.{v₂} D where tensorHom_def {X₁ Y₁ X₂ Y₂} f 
g
参数：F : D ⥤ C；fData : InducingFunctorData F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Induce the lawfulness of the monoidal structure along a faithful functor of (pla
in) categories,
where the operations are already defined on the destination type `D`.

The functor `F` must preserve all the data parts of the monoidal structure betwe
en the two
categories.
-/
def induced [MonoidalCategoryStruct D] (F : D ⥤ C) [F.Faithful]
    (fData : InducingFunctorData F) :
    MonoidalCategory.{v₂} D where
  tensorHom_def {X₁ Y₁ X₂ Y₂} f g := F.map_injective <| by
    rw [fData.tensorHom_eq, Functor.map_comp, fData.whiskerRight_eq, fData.whiskerLeft_eq]
    simp only [tensorHom_def, assoc, Iso.hom_inv_id_assoc]
  id_tensorHom_id X₁ X₂ := F.map_injective <| by cases fData; cat_disch
  tensorHom_comp_tensorHom f₁ f₂ g₁ g₂ := F.map_injective <| by cases fData; cat_disch
  whiskerLeft_id X Y := F.map_injective <| by simp [fData.whiskerLeft_eq]
  id_whiskerRight X Y := F.map_injective <| by simp [fData.whiskerRight_eq]
  triangle X Y := F.map_injective <| by cases fData; cat_disch
  pentagon W X Y Z := F.map_injective <| by
    simp only [Functor.map_comp, fData.whiskerRight_eq, fData.associator_eq, Iso.trans_assoc,
      Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom, tensorHom_id, id_tensorHom,
      comp_whiskerRight, whisker_assoc, assoc, fData.whiskerLeft_eq, whiskerLeft_comp,
      Iso.hom_inv_id_assoc, whiskerLeft_hom_inv_assoc, hom_inv_whiskerRight_assoc,
      Iso.inv_hom_id_assoc, Iso.cancel_iso_inv_left]
    slice_lhs 5 6 =>
      rw [← whiskerLeft_comp, hom_inv_whiskerRight]
    rw [whisker_exchange_assoc]
    simp
  leftUnitor_naturality {X Y : D} f := F.map_injective <| by
    simp [fData.leftUnitor_eq, fData.whiskerLeft_eq, whisker_exchange_assoc]
  rightUnitor_naturality {X Y : D} f := F.map_injective <| by
    simp [fData.rightUnitor_eq, fData.whiskerRight_eq, ← whisker_exchange_assoc]
  associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} f₁ f₂ f₃ := F.map_injective <| by
    simp [fData.tensorHom_eq, fData.associator_eq, tensorHom_def, whisker_exchange_assoc]

/-- A faithful functor equipped with a `InducingFunctorData` structure is monoidal. -/
/-
**CategoryTheory.Monoidal.fromInducedCoreMonoidal** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Monoidal`。
形式化陈述：fromInducedCoreMonoidal [MonoidalCategoryStruct D] (F : D ⥤ C) [F.Faithful
] (fData : InducingFunctorData F) : letI
参数：F : D ⥤ C；fData : InducingFunctorData F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A faithful functor equipped with a `InducingFunctorData` structure is monoidal.
-/
def fromInducedCoreMonoidal [MonoidalCategoryStruct D] (F : D ⥤ C) [F.Faithful]
    (fData : InducingFunctorData F) :
    letI := induced F fData
    F.CoreMonoidal := by
  letI := induced F fData
  exact
    { εIso := fData.εIso
      μIso := fData.μIso
      μIso_hom_natural_left := fun _ ↦ by simp [fData.whiskerRight_eq]
      μIso_hom_natural_right := fun _ ↦ by simp [fData.whiskerLeft_eq]
      associativity := fun _ _ _ ↦ by simp [fData.associator_eq]
      left_unitality := fun _ ↦ by simp [fData.leftUnitor_eq]
      right_unitality := fun _ ↦ by simp [fData.rightUnitor_eq] }
/-
**CategoryTheory.Monoidal.fromInducedMonoidal** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.Monoidal`。
形式化陈述：fromInducedMonoidal [MonoidalCategoryStruct D] (F : D ⥤ C) [F.Faithful] (f
Data : InducingFunctorData F) : letI
参数：F : D ⥤ C；fData : InducingFunctorData F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**CategoryTheory.Monoidal.transportStruct** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Monoidal`。
形式化陈述：transportStruct (e : C ≌ D) : MonoidalCategoryStruct.{v₂} D where tensorOb
j X Y
参数：e : C ≌ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transport a monoidal structure along an equivalence of (plain) categories.
-/
def transportStruct (e : C ≌ D) : MonoidalCategoryStruct.{v₂} D where
  tensorObj X Y := e.functor.obj (e.inverse.obj X ⊗ e.inverse.obj Y)
  whiskerLeft X _ _ f := e.functor.map (e.inverse.obj X ◁ e.inverse.map f)
  whiskerRight f X := e.functor.map (e.inverse.map f ▷ e.inverse.obj X)
  tensorHom f g := e.functor.map (e.inverse.map f ⊗ₘ e.inverse.map g)
  tensorUnit := e.functor.obj (𝟙_ C)
  associator X Y Z :=
    e.functor.mapIso
      (whiskerRightIso (e.unitIso.app _).symm _ ≪≫
        α_ (e.inverse.obj X) (e.inverse.obj Y) (e.inverse.obj Z) ≪≫
        whiskerLeftIso _ (e.unitIso.app _))
  leftUnitor X :=
    e.functor.mapIso ((whiskerRightIso (e.unitIso.app _).symm _) ≪≫ λ_ (e.inverse.obj X)) ≪≫
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
/-
**CategoryTheory.Monoidal.transport** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Mo
noidal`。
形式化陈述：transport (e : C ≌ D) : MonoidalCategory.{v₂} D
参数：e : C ≌ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transport a monoidal structure along an equivalence of (plain) categories.
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
/-
**CategoryTheory.Monoidal.Transported** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Monoidal`。
形式化陈述：Transported (_ : C ≌ D)
参数：_ : C ≌ D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type synonym for `D`, which will carry the transported monoidal structure.
-/
def Transported (_ : C ≌ D) := D
/-
**CategoryTheory.Monoidal.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (e : C ≌ D) : Category (Transported e) := (inferInstance : Category D)
/-
**CategoryTheory.Monoidal.Transported.instMonoidalCategoryStruct** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.Monoidal.Transported`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [Categ
oryTheory.MonoidalCategory C] →       {D : Type u₂} →         [inst_2 : Category
Theory.Category.{v₂, u₂} D] →           (e : C ≌ D) → CategoryTheory.MonoidalCat
egoryStruct (CategoryTheory.Monoidal.Transported e)
参数：e : C ≌ D；CategoryTheory.Monoidal.Transported e。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Transported.instMonoidalCategoryStruct (e : C ≌ D) :
    MonoidalCategoryStruct (Transported e) :=
  transportStruct e
/-
**CategoryTheory.Monoidal.Transported.instMonoidalCategory** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.Monoidal.Transported`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [Categ
oryTheory.MonoidalCategory C] →       {D : Type u₂} →         [inst_2 : Category
Theory.Category.{v₂, u₂} D] →           (e : C ≌ D) → CategoryTheory.MonoidalCat
egory (CategoryTheory.Monoidal.Transported e)
参数：e : C ≌ D；CategoryTheory.Monoidal.Transported e。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Transported.instMonoidalCategory (e : C ≌ D) : MonoidalCategory (Transported e) :=
  transport e
/-
**CategoryTheory.Monoidal.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (e : C ≌ D) : Inhabited (Transported e) :=
  ⟨𝟙_ _⟩

section

variable (e : C ≌ D)

/-- We upgrade the equivalence of categories `e : C ≌ D` to a monoidal category
equivalence `C ≌ Transported e`. -/
/-
**CategoryTheory.Monoidal.equivalenceTransported** 是 Mathlib 中的一个缩写定义，位于命名空间 `Ca
tegoryTheory.Monoidal`。
形式化陈述：equivalenceTransported : C ≌ Transported e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We upgrade the equivalence of categories `e : C ≌ D` to a monoidal category
equivalence `C ≌ Transported e`.
-/
abbrev equivalenceTransported : C ≌ Transported e := e
/-
**CategoryTheory.Monoidal.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (equivalenceTransported e).inverse.Monoidal := by
  dsimp +instances only [Transported.instMonoidalCategory]
  infer_instance
/-
**CategoryTheory.Monoidal.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (equivalenceTransported e).symm.functor.Monoidal :=
  inferInstanceAs (equivalenceTransported e).inverse.Monoidal
/-
**CategoryTheory.Monoidal.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : (equivalenceTransported e).functor.Monoidal :=
  (equivalenceTransported e).symm.inverseMonoidal
/-
**CategoryTheory.Monoidal.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : (equivalenceTransported e).symm.inverse.Monoidal :=
  inferInstanceAs (equivalenceTransported e).functor.Monoidal

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Monoidal.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (equivalenceTransported e).symm.IsMonoidal := by
  infer_instance

/-- The unit isomorphism upgrades to a monoidal isomorphism. -/
/-
**CategoryTheory.Monoidal.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unit isomorphism upgrades to a monoidal isomorphism.
-/
instance : NatTrans.IsMonoidal (equivalenceTransported e).unit :=
  inferInstanceAs (NatTrans.IsMonoidal (equivalenceTransported e).symm.counitIso.inv)

/-- The counit isomorphism upgrades to a monoidal isomorphism. -/
/-
**CategoryTheory.Monoidal.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The counit isomorphism upgrades to a monoidal isomorphism.
-/
instance : NatTrans.IsMonoidal (equivalenceTransported e).counit :=
  inferInstanceAs (NatTrans.IsMonoidal (equivalenceTransported e).symm.unitIso.inv)

end

end CategoryTheory.Monoidal

