/-
Copyright (c) 2024 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Dialectica.Basic

/-!
# The Dialectica category is symmetric monoidal

We show that the category `Dial` has a symmetric monoidal category structure.
-/

@[expose] public section

noncomputable section

namespace CategoryTheory

open MonoidalCategory Limits

universe v u
variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] [HasPullbacks C]

namespace Dial

local notation "π₁" => prod.fst
local notation "π₂" => prod.snd
local notation "π(" a ", " b ")" => prod.lift a b

/--
Definition of `tensorObjImpl` / `tensorObjImpl` 的定义

English:
definition tensorObjImpl
  signature: (X Y : Dial C)
  body: X.src ⨯ Y.src
  tgt := X.tgt ⨯ Y.tgt
  rel :=
    (Subobject.pullback (prod.map π₁ π₁)).obj X.rel ⊓
    (Subobject.pullback (prod.map π₂ π₂)).obj Y.rel

中文:
定义 tensorObjImpl
  签名: (X Y : Dial C)
  定义体: X.src ⨯ Y.src
  tgt := X.tgt ⨯ Y.tgt
  rel :=
    (Subobject.pullback (prod.map π₁ π₁)).obj X.rel ⊓
    (Subobject.pullback (prod.map π₂ π₂)).obj Y.rel
-/
@[simps] def tensorObjImpl (X Y : Dial C) : Dial C where
  src := X.src ⨯ Y.src
  tgt := X.tgt ⨯ Y.tgt
  rel :=
    (Subobject.pullback (prod.map π₁ π₁)).obj X.rel ⊓
    (Subobject.pullback (prod.map π₂ π₂)).obj Y.rel

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `tensorHomImpl` / `tensorHomImpl` 的定义

English:
definition tensorHomImpl
  signature: {X₁ X₂ Y₁ Y₂ : Dial C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂)
  body: prod.map f.f g.f
  F := π(prod.map π₁ π₁ ≫ f.F, prod.map π₂ π₂ ≫ g.F)
  le := by
    simp only [tensorObjImpl, Subobject.inf_pullback]
    apply inf_le_inf <;> rw [← Subobject.pullback_comp, ← Subobject.pullback_comp]
    · have := (Subobject.pullback (prod.map π₁ π₁ :
        (X₁.src ⨯ Y₁.src) ⨯ X₂

中文:
定义 tensorHomImpl
  签名: {X₁ X₂ Y₁ Y₂ : Dial C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂)
  定义体: prod.map f.f g.f
  F := π(prod.map π₁ π₁ ≫ f.F, prod.map π₂ π₂ ≫ g.F)
  le := by
    simp only [tensorObjImpl, Subobject.inf_pullback]
    apply inf_le_inf <;> rw [← Subobject.pullback_comp, ← Subobject.pullback_comp]
    · have := (Subobject.pullback (prod.map π₁ π₁ :
        (X₁.src ⨯ Y₁.src) ⨯ X₂
-/
@[simps] def tensorHomImpl {X₁ X₂ Y₁ Y₂ : Dial C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
    tensorObjImpl X₁ Y₁ ⟶ tensorObjImpl X₂ Y₂ where
  f := prod.map f.f g.f
  F := π(prod.map π₁ π₁ ≫ f.F, prod.map π₂ π₂ ≫ g.F)
  le := by
    simp only [tensorObjImpl, Subobject.inf_pullback]
    apply inf_le_inf <;> rw [← Subobject.pullback_comp, ← Subobject.pullback_comp]
    · have := (Subobject.pullback (prod.map π₁ π₁ :
        (X₁.src ⨯ Y₁.src) ⨯ X₂.tgt ⨯ Y₂.tgt ⟶ _)).monotone (Hom.le f)
      rw [← Subobject.pullback_comp]; rw [← Subobject.pullback_comp] at this
      convert! this using 3 <;> simp
    · have := (Subobject.pullback (prod.map π₂ π₂ :
        (X₁.src ⨯ Y₁.src) ⨯ X₂.tgt ⨯ Y₂.tgt ⟶ _)).monotone (Hom.le g)
      rw [← Subobject.pullback_comp]; rw [← Subobject.pullback_comp] at this
      convert! this using 3 <;> simp

/--
Definition of `tensorUnitImpl` / `tensorUnitImpl` 的定义

English:
definition tensorUnitImpl
  signature: : Dial C
  body: { src := ⊤_ _, tgt := ⊤_ _, rel := ⊤ }

中文:
定义 tensorUnitImpl
  签名: : Dial C
  定义体: { src := ⊤_ _, tgt := ⊤_ _, rel := ⊤ }
-/
@[simps] def tensorUnitImpl : Dial C := { src := ⊤_ _, tgt := ⊤_ _, rel := ⊤ }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `leftUnitorImpl` / `leftUnitorImpl` 的定义

English:
definition leftUnitorImpl
  signature: (X : Dial C)
  body: isoMk (Limits.prod.leftUnitor _) (Limits.prod.leftUnitor _) by simp [Subobject.pullback_top]

中文:
定义 leftUnitorImpl
  签名: (X : Dial C)
  定义体: isoMk (Limits.prod.leftUnitor _) (Limits.prod.leftUnitor _) by simp [Subobject.pullback_top]
-/
@[simps!] def leftUnitorImpl (X : Dial C) : tensorObjImpl tensorUnitImpl X ≅ X :=
isoMk (Limits.prod.leftUnitor _) (Limits.prod.leftUnitor _) by simp [Subobject.pullback_top]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `rightUnitorImpl` / `rightUnitorImpl` 的定义

English:
definition rightUnitorImpl
  signature: (X : Dial C)
  body: isoMk (Limits.prod.rightUnitor _) (Limits.prod.rightUnitor _) by simp [Subobject.pullback_top]

中文:
定义 rightUnitorImpl
  签名: (X : Dial C)
  定义体: isoMk (Limits.prod.rightUnitor _) (Limits.prod.rightUnitor _) by simp [Subobject.pullback_top]
-/
@[simps!] def rightUnitorImpl (X : Dial C) : tensorObjImpl X tensorUnitImpl ≅ X :=
isoMk (Limits.prod.rightUnitor _) (Limits.prod.rightUnitor _) by simp [Subobject.pullback_top]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The associator for tensor, `(X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z)` in `Dial C`. -/
@[simps!]
/--
Definition of `associatorImpl` / `associatorImpl` 的定义

English:
definition associatorImpl
  signature: (X Y Z : Dial C)
  body: isoMk (prod.associator ..) (prod.associator ..) by
    simp [Subobject.inf_pullback, ← Subobject.pullback_comp, inf_assoc]

#adaptation_note

中文:
定义 associatorImpl
  签名: (X Y Z : Dial C)
  定义体: isoMk (prod.associator ..) (prod.associator ..) by
    simp [Subobject.inf_pullback, ← Subobject.pullback_comp, inf_assoc]

#adaptation_note

Depends on / 依赖: Subobject, Subobject.inf_pullback, Subobject.pullback_comp, associator, inf_assoc, inf_pullback, prod.associator, pullback_comp
-/
def associatorImpl (X Y Z : Dial C) :
    tensorObjImpl (tensorObjImpl X Y) Z ≅ tensorObjImpl X (tensorObjImpl Y Z) :=
isoMk (prod.associator ..) (prod.associator ..) by
    simp [Subobject.inf_pullback, ← Subobject.pullback_comp, inf_assoc]

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[simps!]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonoidalCategoryStruct (Dial C)
  body: tensorUnitImpl
  tensorObj := tensorObjImpl
  whiskerLeft X _ _ f := tensorHomImpl (𝟙 X) f
  whiskerRight f Y := tensorHomImpl f (𝟙 Y)
  tensorHom := tensorHomImpl
  leftUnitor := leftUnitorImpl
  rightUnitor := rightUnitorImpl
  associator := associatorImpl

中文:
实例 :
  签名: MonoidalCategoryStruct (Dial C)
  定义体: tensorUnitImpl
  tensorObj := tensorObjImpl
  whiskerLeft X _ _ f := tensorHomImpl (𝟙 X) f
  whiskerRight f Y := tensorHomImpl f (𝟙 Y)
  tensorHom := tensorHomImpl
  leftUnitor := leftUnitorImpl
  rightUnitor := rightUnitorImpl
  associator := associatorImpl

Depends on / 依赖: tensorUnitImpl
-/
instance : MonoidalCategoryStruct (Dial C) where
  tensorUnit := tensorUnitImpl
  tensorObj := tensorObjImpl
  whiskerLeft X _ _ f := tensorHomImpl (𝟙 X) f
  whiskerRight f Y := tensorHomImpl f (𝟙 Y)
  tensorHom := tensorHomImpl
  leftUnitor := leftUnitorImpl
  rightUnitor := rightUnitorImpl
  associator := associatorImpl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `id_tensorHom_id` / 定理 `id_tensorHom_id`

English:
theorem id_tensorHom_id
  given: (X₁ X₂ : Dial C)
  statement: (𝟙 X₁ otimesₘ 𝟙 X₂ : _ ⟶ _) = 𝟙 (X₁ otimes X₂ : Dial C)
  proof: by
  cat_disch

中文:
定理 id_tensorHom_id
  条件: (X₁ X₂ : Dial C)
  结论: (𝟙 X₁ otimesₘ 𝟙 X₂ : _ ⟶ _) = 𝟙 (X₁ otimes X₂ : Dial C)
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
theorem id_tensorHom_id (X₁ X₂ : Dial C) : (𝟙 X₁ otimesₘ 𝟙 X₂ : _ ⟶ _) = 𝟙 (X₁ otimes X₂ : Dial C) := by
  cat_disch

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
-- TODO: fix the non-terminal simp
set_option linter.flexible false in
/--
theorem `tensorHom_comp_tensorHom` / 定理 `tensorHom_comp_tensorHom`

English:
theorem tensorHom_comp_tensorHom
  statement: {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : Dial C}
  proof: by
  ext <;> simp; ext <;> simp <;> (rw [← Category.assoc]; congr 1; simp)

中文:
定理 tensorHom_comp_tensorHom
  结论: {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : Dial C}
  证明: by
  ext <;> simp; ext <;> simp <;> (rw [← Category.assoc]; congr 1; simp)

Depends on / 依赖: Category, Category.assoc
-/
theorem tensorHom_comp_tensorHom {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : Dial C}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
    (f₁ otimesₘ f₂) ≫ (g₁ otimesₘ g₂) = (f₁ ≫ g₁) otimesₘ (f₂ ≫ g₂) := by
  ext <;> simp; ext <;> simp <;> (rw [← Category.assoc]; congr 1; simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `associator_naturality` / 定理 `associator_naturality`

English:
theorem associator_naturality
  statement: {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Dial C}
  proof: by cat_disch

中文:
定理 associator_naturality
  结论: {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Dial C}
  证明: by cat_disch

Depends on / 依赖: cat_disch
-/
theorem associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Dial C}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    tensorHom (tensorHom f₁ f₂) f₃ ≫ (associator Y₁ Y₂ Y₃).hom =
    (associator X₁ X₂ X₃).hom ≫ tensorHom f₁ (tensorHom f₂ f₃) := by cat_disch

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
-- TODO: fix the non-terminal simp
set_option linter.flexible false in
/--
theorem `leftUnitor_naturality` / 定理 `leftUnitor_naturality`

English:
theorem leftUnitor_naturality
  given: {X Y : Dial C} (f : X ⟶ Y)
  proof: by
  ext <;> simp; ext; simp; congr 1; ext <;> simp

中文:
定理 leftUnitor_naturality
  条件: {X Y : Dial C} (f : X ⟶ Y)
  证明: by
  ext <;> simp; ext; simp; congr 1; ext <;> simp
-/
theorem leftUnitor_naturality {X Y : Dial C} (f : X ⟶ Y) :
    (𝟙 (𝟙_ (Dial C)) otimesₘ f) ≫ (fun_ Y).hom = (fun_ X).hom ≫ f := by
  ext <;> simp; ext; simp; congr 1; ext <;> simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
-- TODO: fix the non-terminal simp
set_option linter.flexible false in
/--
theorem `rightUnitor_naturality` / 定理 `rightUnitor_naturality`

English:
theorem rightUnitor_naturality
  given: {X Y : Dial C} (f : X ⟶ Y)
  proof: by
  ext <;> simp; ext; simp; congr 1; ext <;> simp

中文:
定理 rightUnitor_naturality
  条件: {X Y : Dial C} (f : X ⟶ Y)
  证明: by
  ext <;> simp; ext; simp; congr 1; ext <;> simp
-/
theorem rightUnitor_naturality {X Y : Dial C} (f : X ⟶ Y) :
    (f otimesₘ 𝟙 (𝟙_ (Dial C))) ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f := by
  ext <;> simp; ext; simp; congr 1; ext <;> simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `pentagon` / 定理 `pentagon`

English:
theorem pentagon
  given: (W X Y Z : Dial C)
  proof: by
  ext <;> simp

中文:
定理 pentagon
  条件: (W X Y Z : Dial C)
  证明: by
  ext <;> simp
-/
theorem pentagon (W X Y Z : Dial C) :
    (tensorHom (associator W X Y).hom (𝟙 Z)) ≫ (associator W (tensorObj X Y) Z).hom ≫
      (tensorHom (𝟙 W) (associator X Y Z).hom) =
    (associator (tensorObj W X) Y Z).hom ≫ (associator W X (tensorObj Y Z)).hom := by
  ext <;> simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `triangle` / 定理 `triangle`

English:
theorem triangle
  given: (X Y : Dial C)
  proof: by cat_disch

中文:
定理 triangle
  条件: (X Y : Dial C)
  证明: by cat_disch

Depends on / 依赖: cat_disch
-/
theorem triangle (X Y : Dial C) :
    (associator X (𝟙_ (Dial C)) Y).hom ≫ tensorHom (𝟙 X) (leftUnitor Y).hom =
    tensorHom (rightUnitor X).hom (𝟙 Y) := by cat_disch

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonoidalCategory (Dial C)
  body: .ofTensorHom
    (id_tensorHom_id := id_tensorHom_id)
    (tensorHom_comp_tensorHom := tensorHom_comp_tensorHom)
    (associator_naturality := associator_naturality)
    (leftUnitor_naturality := leftUnitor_naturality)
    (rightUnitor_naturality := rightUnitor_naturality)
    (pentagon := pentagon)

中文:
实例 :
  签名: MonoidalCategory (Dial C)
  定义体: .ofTensorHom
    (id_tensorHom_id := id_tensorHom_id)
    (tensorHom_comp_tensorHom := tensorHom_comp_tensorHom)
    (associator_naturality := associator_naturality)
    (leftUnitor_naturality := leftUnitor_naturality)
    (rightUnitor_naturality := rightUnitor_naturality)
    (pentagon := pentagon)

Depends on / 依赖: associator_naturality, id_tensorHom_id, leftUnitor_naturality, ofTensorHom, pentagon, rightUnitor_naturality, tensorHom_comp_tensorHom, triangle
-/
instance : MonoidalCategory (Dial C) :=
  .ofTensorHom
    (id_tensorHom_id := id_tensorHom_id)
    (tensorHom_comp_tensorHom := tensorHom_comp_tensorHom)
    (associator_naturality := associator_naturality)
    (leftUnitor_naturality := leftUnitor_naturality)
    (rightUnitor_naturality := rightUnitor_naturality)
    (pentagon := pentagon)
    (triangle := triangle)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `braiding` / `braiding` 的定义

English:
definition braiding
  signature: (X Y : Dial C)
  body: isoMk (prod.braiding ..) (prod.braiding ..) by
    simp [Subobject.inf_pullback, ← Subobject.pullback_comp, inf_comm]

中文:
定义 braiding
  签名: (X Y : Dial C)
  定义体: isoMk (prod.braiding ..) (prod.braiding ..) by
    simp [Subobject.inf_pullback, ← Subobject.pullback_comp, inf_comm]
-/
@[simps!] def braiding (X Y : Dial C) : tensorObj X Y ≅ tensorObj Y X :=
isoMk (prod.braiding ..) (prod.braiding ..) by
    simp [Subobject.inf_pullback, ← Subobject.pullback_comp, inf_comm]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `symmetry` / 定理 `symmetry`

English:
theorem symmetry
  given: (X Y : Dial C)
  proof: by cat_disch

中文:
定理 symmetry
  条件: (X Y : Dial C)
  证明: by cat_disch

Depends on / 依赖: cat_disch
-/
theorem symmetry (X Y : Dial C) :
    (braiding X Y).hom ≫ (braiding Y X).hom = 𝟙 (tensorObj X Y) := by cat_disch

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `braiding_naturality_right` / 定理 `braiding_naturality_right`

English:
theorem braiding_naturality_right
  given: (X : Dial C) {Y Z : Dial C} (f : Y ⟶ Z)
  proof: by cat_disch

中文:
定理 braiding_naturality_right
  条件: (X : Dial C) {Y Z : Dial C} (f : Y ⟶ Z)
  证明: by cat_disch

Depends on / 依赖: cat_disch
-/
theorem braiding_naturality_right (X : Dial C) {Y Z : Dial C} (f : Y ⟶ Z) :
    tensorHom (𝟙 X) f ≫ (braiding X Z).hom = (braiding X Y).hom ≫ tensorHom f (𝟙 X) := by cat_disch

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `braiding_naturality_left` / 定理 `braiding_naturality_left`

English:
theorem braiding_naturality_left
  given: {X Y : Dial C} (f : X ⟶ Y) (Z : Dial C)
  proof: by cat_disch

中文:
定理 braiding_naturality_left
  条件: {X Y : Dial C} (f : X ⟶ Y) (Z : Dial C)
  证明: by cat_disch

Depends on / 依赖: cat_disch
-/
theorem braiding_naturality_left {X Y : Dial C} (f : X ⟶ Y) (Z : Dial C) :
    tensorHom f (𝟙 Z) ≫ (braiding Y Z).hom = (braiding X Z).hom ≫ tensorHom (𝟙 Z) f := by cat_disch

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `hexagon_forward` / 定理 `hexagon_forward`

English:
theorem hexagon_forward
  given: (X Y Z : Dial C)
  proof: by cat_disch

中文:
定理 hexagon_forward
  条件: (X Y Z : Dial C)
  证明: by cat_disch

Depends on / 依赖: cat_disch
-/
theorem hexagon_forward (X Y Z : Dial C) :
    (associator X Y Z).hom ≫ (braiding X (Y otimes Z)).hom ≫ (associator Y Z X).hom =
      tensorHom (braiding X Y).hom (𝟙 Z) ≫ (associator Y X Z).hom ≫
      tensorHom (𝟙 Y) (braiding X Z).hom := by cat_disch

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `hexagon_reverse` / 定理 `hexagon_reverse`

English:
theorem hexagon_reverse
  given: (X Y Z : Dial C)
  proof: by cat_disch

中文:
定理 hexagon_reverse
  条件: (X Y Z : Dial C)
  证明: by cat_disch

Depends on / 依赖: cat_disch
-/
theorem hexagon_reverse (X Y Z : Dial C) :
    (associator X Y Z).inv ≫ (braiding (X otimes Y) Z).hom ≫ (associator Z X Y).inv =
      tensorHom (𝟙 X) (braiding Y Z).hom ≫ (associator X Z Y).inv ≫
      tensorHom (braiding X Z).hom (𝟙 Y) := by cat_disch

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SymmetricCategory (Dial C)
  body: braiding
  braiding_naturality_right := braiding_naturality_right
  braiding_naturality_left := braiding_naturality_left
  hexagon_forward := hexagon_forward
  hexagon_reverse := hexagon_reverse
  symmetry := symmetry

中文:
实例 :
  签名: SymmetricCategory (Dial C)
  定义体: braiding
  braiding_naturality_right := braiding_naturality_right
  braiding_naturality_left := braiding_naturality_left
  hexagon_forward := hexagon_forward
  hexagon_reverse := hexagon_reverse
  symmetry := symmetry

Depends on / 依赖: braiding
-/
instance : SymmetricCategory (Dial C) where
  braiding := braiding
  braiding_naturality_right := braiding_naturality_right
  braiding_naturality_left := braiding_naturality_left
  hexagon_forward := hexagon_forward
  hexagon_reverse := hexagon_reverse
  symmetry := symmetry

end Dial

end CategoryTheory
