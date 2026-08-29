/-
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.CategoryTheory.Monoidal.Transport
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Full monoidal subcategories

Given a monoidal category `C` and a property of objects `P : ObjectProperty C`
that is monoidal (i.e. it holds for the unit and is stable by `⊗`),
we can put a monoidal structure on `P.FullSubcategory` (the category
structure is defined in `Mathlib/CategoryTheory/ObjectProperty/FullSubcategory.lean`).

When `C` is also braided/symmetric, the full monoidal subcategory also inherits the
braided/symmetric structure.

## TODO
* Add monoidal/braided versions of `ObjectProperty.Lift`
-/

public section


universe u v

namespace CategoryTheory

open MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

namespace ObjectProperty

/--
Definition of `TensorLE` / `TensorLE` 的定义

English:
class TensorLE
  parameters: (P₁ P₂ Q : ObjectProperty C)
  axioms and operations (1):
    - prop_tensor((X₁ X₂ : C) (h₁ : P₁ X₁) (h₂ : P₂ X₂)) : Q (X₁ otimes X₂)

中文:
类 TensorLE
  参数: (P₁ P₂ Q : Object命题erty C)
  公理与运算 (1 个):
    - prop_tensor((X₁ X₂ : C) (h₁ : P₁ X₁) (h₂ : P₂ X₂)) : Q (X₁ otimes X₂)
-/
class TensorLE (P₁ P₂ Q : ObjectProperty C) : Prop where
  prop_tensor (X₁ X₂ : C) (h₁ : P₁ X₁) (h₂ : P₂ X₂) : Q (X₁ otimes X₂)

/--
lemma `prop_tensor` / 引理 `prop_tensor`

English:
lemma prop_tensor
  statement: {P₁ P₂ Q : ObjectProperty C} [TensorLE P₁ P₂ Q]
  proof: TensorLE.prop_tensor _ _ h₁ h₂

中文:
引理 prop_tensor
  结论: {P₁ P₂ Q : Object命题erty C} [TensorLE P₁ P₂ Q]
  证明: TensorLE.prop_tensor _ _ h₁ h₂

Depends on / 依赖: TensorLE, TensorLE.prop_tensor, prop_tensor
-/
lemma prop_tensor {P₁ P₂ Q : ObjectProperty C} [TensorLE P₁ P₂ Q]
    {X₁ X₂ : C} (h₁ : P₁ X₁) (h₂ : P₂ X₂) : Q (X₁ otimes X₂) :=
  TensorLE.prop_tensor _ _ h₁ h₂

/--
Definition of `ContainsUnit` / `ContainsUnit` 的定义

English:
class ContainsUnit
  parameters: (P : ObjectProperty C)
  axioms and operations (1):
    - prop_unit : P (𝟙_ C)

中文:
类 ContainsUnit
  参数: (P : Object命题erty C)
  公理与运算 (1 个):
    - prop_unit : P (𝟙_ C)
-/
class ContainsUnit (P : ObjectProperty C) : Prop where
  prop_unit : P (𝟙_ C)

/--
lemma `prop_unit` / 引理 `prop_unit`

English:
lemma prop_unit
  given: (P : ObjectProperty C) [ContainsUnit P]
  statement: P (𝟙_ C)
  proof: ContainsUnit.prop_unit

中文:
引理 prop_unit
  条件: (P : Object命题erty C) [ContainsUnit P]
  结论: P (𝟙_ C)
  证明: ContainsUnit.prop_unit

Depends on / 依赖: ContainsUnit, ContainsUnit.prop_unit, prop_unit
-/
lemma prop_unit (P : ObjectProperty C) [ContainsUnit P] : P (𝟙_ C) :=
  ContainsUnit.prop_unit

/--
Definition of `IsMonoidal` / `IsMonoidal` 的定义

English:
class IsMonoidal
  parameters: (P : ObjectProperty C)
  (no additional axioms)

中文:
类 IsMonoidal
  参数: (P : Object命题erty C)
  (无附加公理)
-/
class IsMonoidal (P : ObjectProperty C) : Prop extends
  ContainsUnit P, TensorLE P P P where

/--
Definition of `IsMonoidalClosed` / `IsMonoidalClosed` 的定义

English:
class IsMonoidalClosed
  parameters: (P : ObjectProperty C) [MonoidalClosed C]
  axioms and operations (1):
    - prop_ihom((X Y : C)) : P X -> P Y -> P ((ihom X).obj Y)  [default: by cat_disch]

中文:
类 IsMonoidalClosed
  参数: (P : Object命题erty C) [MonoidalClosed C]
  公理与运算 (1 个):
    - prop_ihom((X Y : C)) : P X -> P Y -> P ((ihom X).obj Y)  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
class IsMonoidalClosed (P : ObjectProperty C) [MonoidalClosed C] : Prop where
  prop_ihom (X Y : C) : P X -> P Y -> P ((ihom X).obj Y) := by cat_disch

/--
lemma `prop_ihom` / 引理 `prop_ihom`

English:
lemma prop_ihom
  statement: (P : ObjectProperty C) [MonoidalClosed C] [P.IsMonoidalClosed]
  proof: IsMonoidalClosed.prop_ihom _ _ hX hY

中文:
引理 prop_ihom
  结论: (P : Object命题erty C) [MonoidalClosed C] [P.IsMonoidalClosed]
  证明: IsMonoidalClosed.prop_ihom _ _ hX hY

Depends on / 依赖: IsMonoidalClosed, IsMonoidalClosed.prop_ihom, prop_ihom
-/
lemma prop_ihom (P : ObjectProperty C) [MonoidalClosed C] [P.IsMonoidalClosed]
    {X Y : C} (hX : P X) (hY : P Y) : P ((ihom X).obj Y) :=
  IsMonoidalClosed.prop_ihom _ _ hX hY

variable (P : ObjectProperty C) [P.IsMonoidal]

@[simps]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonoidalCategoryStruct P.FullSubcategory
  body: ⟨X.1 otimes Y.1, prop_tensor X.2 Y.2⟩
  whiskerLeft X _ _ f := ObjectProperty.homMk (X.1 ◁ f.hom)
  whiskerRight f Y := ObjectProperty.homMk (f.hom ▷ Y.1)
  tensorHom f g := ObjectProperty.homMk (f.hom otimesₘ g.hom)
  tensorUnit := ⟨𝟙_ C, P.prop_unit⟩
  associator X Y Z := P.isoMk (α_ X.1 Y.1 Z.1)


中文:
实例 :
  签名: MonoidalCategoryStruct P.FullSubcategory
  定义体: ⟨X.1 otimes Y.1, prop_tensor X.2 Y.2⟩
  whiskerLeft X _ _ f := ObjectProperty.homMk (X.1 ◁ f.hom)
  whiskerRight f Y := ObjectProperty.homMk (f.hom ▷ Y.1)
  tensorHom f g := ObjectProperty.homMk (f.hom otimesₘ g.hom)
  tensorUnit := ⟨𝟙_ C, P.prop_unit⟩
  associator X Y Z := P.isoMk (α_ X.1 Y.1 Z.1)


Depends on / 依赖: otimes, prop_tensor
-/
instance : MonoidalCategoryStruct P.FullSubcategory where
  tensorObj X Y := ⟨X.1 otimes Y.1, prop_tensor X.2 Y.2⟩
  whiskerLeft X _ _ f := ObjectProperty.homMk (X.1 ◁ f.hom)
  whiskerRight f Y := ObjectProperty.homMk (f.hom ▷ Y.1)
  tensorHom f g := ObjectProperty.homMk (f.hom otimesₘ g.hom)
  tensorUnit := ⟨𝟙_ C, P.prop_unit⟩
  associator X Y Z := P.isoMk (α_ X.1 Y.1 Z.1)
  leftUnitor X := P.isoMk (fun_ X.1)
  rightUnitor X := P.isoMk (ρ_ X.1)

/--
Instance `fullMonoidalSubcategory` / 实例 `fullMonoidalSubcategory`

English:
instance fullMonoidalSubcategory
  signature: : MonoidalCategory (FullSubcategory P)
  body: Monoidal.induced P.ι
    { μIso _ _ := Iso.refl _
      εIso := Iso.refl _ }

中文:
实例 fullMonoidalSubcategory
  签名: : MonoidalCategory (FullSubcategory P)
  定义体: Monoidal.induced P.ι
    { μIso _ _ := Iso.refl _
      εIso := Iso.refl _ }

Depends on / 依赖: Iso.refl, Monoidal, Monoidal.induced, induced
-/
instance fullMonoidalSubcategory : MonoidalCategory (FullSubcategory P) :=
  Monoidal.induced P.ι
    { μIso _ _ := Iso.refl _
      εIso := Iso.refl _ }

/--
Instance `monoidalι` / 实例 `monoidalι`

English:
instance monoidalι
  signature: : P.ι.Monoidal
  body: Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ => Iso.refl _ }

中文:
实例 monoidalι
  签名: : P.ι.Monoidal
  定义体: Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ => Iso.refl _ }

Depends on / 依赖: CoreMonoidal, Functor, Functor.CoreMonoidal.toMonoidal, Iso.refl, toMonoidal
-/
instance monoidalι : P.ι.Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ => Iso.refl _ }

open Functor.LaxMonoidal Functor.OplaxMonoidal

/--
lemma `ι_ε` / 引理 `ι_ε`

English:
lemma ι_ε
  statement: ε P.ι = 𝟙 _
  proof: rfl

中文:
引理 ι_ε
  结论: ε P.ι = 𝟙 _
  证明: rfl
-/
@[simp] lemma ι_ε : ε P.ι = 𝟙 _ := rfl
/--
lemma `ι_η` / 引理 `ι_η`

English:
lemma ι_η
  statement: ε P.ι = 𝟙 _
  proof: rfl

中文:
引理 ι_η
  结论: ε P.ι = 𝟙 _
  证明: rfl
-/
@[simp] lemma ι_η : ε P.ι = 𝟙 _ := rfl
/--
lemma `ι_μ` / 引理 `ι_μ`

English:
lemma ι_μ
  given: (X Y : FullSubcategory P)
  statement: μ P.ι X Y = 𝟙 _
  proof: rfl

中文:
引理 ι_μ
  条件: (X Y : FullSubcategory P)
  结论: μ P.ι X Y = 𝟙 _
  证明: rfl
-/
@[simp] lemma ι_μ (X Y : FullSubcategory P) : μ P.ι X Y = 𝟙 _ := rfl
/--
lemma `ι_δ` / 引理 `ι_δ`

English:
lemma ι_δ
  given: (X Y : FullSubcategory P)
  statement: δ P.ι X Y = 𝟙 _
  proof: rfl

中文:
引理 ι_δ
  条件: (X Y : FullSubcategory P)
  结论: δ P.ι X Y = 𝟙 _
  证明: rfl
-/
@[simp] lemma ι_δ (X Y : FullSubcategory P) : δ P.ι X Y = 𝟙 _ := rfl

section

variable [Preadditive C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MonoidalPreadditive
  signature: C] : MonoidalPreadditive P.FullSubcategory
  body: monoidalPreadditive_of_faithful P.ι

中文:
实例 [MonoidalPreadditive
  签名: C] : MonoidalPreadditive P.FullSubcategory
  定义体: monoidalPreadditive_of_faithful P.ι

Depends on / 依赖: monoidalPreadditive_of_faithful
-/
instance [MonoidalPreadditive C] : MonoidalPreadditive P.FullSubcategory :=
  monoidalPreadditive_of_faithful P.ι

variable (R : Type*) [Ring R] [Linear R C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MonoidalPreadditive
  signature: C] [MonoidalLinear R C] : MonoidalLinear R P.FullSubcategory
  body: .ofFaithful R P.ι

中文:
实例 [MonoidalPreadditive
  签名: C] [MonoidalLinear R C] : MonoidalLinear R P.FullSubcategory
  定义体: .ofFaithful R P.ι

Depends on / 依赖: ofFaithful
-/
instance [MonoidalPreadditive C] [MonoidalLinear R C] : MonoidalLinear R P.FullSubcategory :=
  .ofFaithful R P.ι

end

section

variable {P} {P' : ObjectProperty C} [P'.IsMonoidal] (h : P <= P')

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (ιOfLE h).Monoidal
  body: Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ => Iso.refl _ }

中文:
实例 :
  签名: (ιOfLE h).Monoidal
  定义体: Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ => Iso.refl _ }

Depends on / 依赖: CoreMonoidal, Functor, Functor.CoreMonoidal.toMonoidal, Iso.refl, toMonoidal
-/
instance : (ιOfLE h).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ => Iso.refl _ }

/--
lemma `ιOfLE_ε` / 引理 `ιOfLE_ε`

English:
lemma ιOfLE_ε
  statement: ε (ιOfLE h) = 𝟙 _
  proof: rfl

中文:
引理 ιOfLE_ε
  结论: ε (ιOfLE h) = 𝟙 _
  证明: rfl
-/
@[simp] lemma ιOfLE_ε : ε (ιOfLE h) = 𝟙 _ := rfl
/--
lemma `ιOfLE_η` / 引理 `ιOfLE_η`

English:
lemma ιOfLE_η
  statement: η (ιOfLE h) = 𝟙 _
  proof: rfl

中文:
引理 ιOfLE_η
  结论: η (ιOfLE h) = 𝟙 _
  证明: rfl
-/
@[simp] lemma ιOfLE_η : η (ιOfLE h) = 𝟙 _ := rfl
/--
lemma `ιOfLE_μ` / 引理 `ιOfLE_μ`

English:
lemma ιOfLE_μ
  given: (X Y : P.FullSubcategory)
  statement: μ (ιOfLE h) X Y = 𝟙 _
  proof: rfl

中文:
引理 ιOfLE_μ
  条件: (X Y : P.FullSubcategory)
  结论: μ (ιOfLE h) X Y = 𝟙 _
  证明: rfl
-/
@[simp] lemma ιOfLE_μ (X Y : P.FullSubcategory) : μ (ιOfLE h) X Y = 𝟙 _ := rfl
/--
lemma `ιOfLE_δ` / 引理 `ιOfLE_δ`

English:
lemma ιOfLE_δ
  given: (X Y : FullSubcategory P)
  statement: δ (ιOfLE h) X Y = 𝟙 _
  proof: rfl

中文:
引理 ιOfLE_δ
  条件: (X Y : FullSubcategory P)
  结论: δ (ιOfLE h) X Y = 𝟙 _
  证明: rfl
-/
@[simp] lemma ιOfLE_δ (X Y : FullSubcategory P) : δ (ιOfLE h) X Y = 𝟙 _ := rfl

end

section Braided

variable [BraidedCategory C]

/--
Instance `fullBraidedSubcategory` / 实例 `fullBraidedSubcategory`

English:
instance fullBraidedSubcategory
  signature: : BraidedCategory (FullSubcategory P)
  body: .ofFaithful P.ι fun X Y => P.isoMk (β_ X.1 Y.1)

中文:
实例 fullBraidedSubcategory
  签名: : BraidedCategory (FullSubcategory P)
  定义体: .ofFaithful P.ι fun X Y => P.isoMk (β_ X.1 Y.1)

Depends on / 依赖: P.isoMk, ofFaithful
-/
instance fullBraidedSubcategory : BraidedCategory (FullSubcategory P) :=
  .ofFaithful P.ι fun X Y => P.isoMk (β_ X.1 Y.1)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: P.ι.Braided

中文:
实例 :
  签名: P.ι.Braided
-/
instance : P.ι.Braided where

variable {P}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- An inequality `P ≤ P'` between monoidal properties of objects induces
a braided functor between full braided subcategories. -/
instance {P' : ObjectProperty C} [P'.IsMonoidal] (h : P <= P') :
    (ιOfLE h).Braided where

end Braided

section Symmetric

variable [SymmetricCategory C]

/--
Instance `fullSymmetricSubcategory` / 实例 `fullSymmetricSubcategory`

English:
instance fullSymmetricSubcategory
  signature: : SymmetricCategory P.FullSubcategory
  body: .ofFaithful P.ι

中文:
实例 fullSymmetricSubcategory
  签名: : SymmetricCategory P.FullSubcategory
  定义体: .ofFaithful P.ι

Depends on / 依赖: ofFaithful
-/
instance fullSymmetricSubcategory : SymmetricCategory P.FullSubcategory :=
  .ofFaithful P.ι

end Symmetric

section Closed

variable [MonoidalClosed C] [P.IsMonoidalClosed]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `fullMonoidalClosedSubcategory` / 实例 `fullMonoidalClosedSubcategory`

English:
instance fullMonoidalClosedSubcategory
  signature: : MonoidalClosed (FullSubcategory P) where
  body: { rightAdj := P.lift (P.ι ⋙ ihom X.1) (fun Y => P.prop_ihom X.2 Y.2)
      adj :=
        { unit := { app Y := ObjectProperty.homMk ((ihom.coev X.1).app Y.1) }
          counit := { app Y := ObjectProperty.homMk ((ihom.ev X.1).app Y.1) } } }

@[simp]

中文:
实例 fullMonoidalClosedSubcategory
  签名: : MonoidalClosed (FullSubcategory P) where
  定义体: { rightAdj := P.lift (P.ι ⋙ ihom X.1) (fun Y => P.prop_ihom X.2 Y.2)
      adj :=
        { unit := { app Y := ObjectProperty.homMk ((ihom.coev X.1).app Y.1) }
          counit := { app Y := ObjectProperty.homMk ((ihom.ev X.1).app Y.1) } } }

@[simp]

Depends on / 依赖: ObjectProperty, ObjectProperty.homMk, P.lift, P.prop_ihom, counit, ihom.coev, ihom.ev, prop_ihom, rightAdj
-/
instance fullMonoidalClosedSubcategory : MonoidalClosed (FullSubcategory P) where
  closed X :=
    { rightAdj := P.lift (P.ι ⋙ ihom X.1) (fun Y => P.prop_ihom X.2 Y.2)
      adj :=
        { unit := { app Y := ObjectProperty.homMk ((ihom.coev X.1).app Y.1) }
          counit := { app Y := ObjectProperty.homMk ((ihom.ev X.1).app Y.1) } } }

@[simp]
/--
theorem `ihom_obj` / 定理 `ihom_obj`

English:
theorem ihom_obj
  given: (X Y : P.FullSubcategory)
  proof: rfl

@[simp]

中文:
定理 ihom_obj
  条件: (X Y : P.FullSubcategory)
  证明: rfl

@[simp]
-/
theorem ihom_obj (X Y : P.FullSubcategory) :
    ((ihom X).obj Y).obj = (ihom X.obj).obj Y.obj :=
  rfl

@[simp]
/--
theorem `ihom_map_hom` / 定理 `ihom_map_hom`

English:
theorem ihom_map_hom
  statement: (X : P.FullSubcategory) {Y Z : P.FullSubcategory}
  proof: rfl

中文:
定理 ihom_map_hom
  结论: (X : P.FullSubcategory) {Y Z : P.FullSubcategory}
  证明: rfl
-/
theorem ihom_map_hom (X : P.FullSubcategory) {Y Z : P.FullSubcategory}
    (f : Y ⟶ Z) : ((ihom X).map f).hom = (ihom X.obj).map f.hom :=
  rfl

end Closed

end ObjectProperty

end CategoryTheory
