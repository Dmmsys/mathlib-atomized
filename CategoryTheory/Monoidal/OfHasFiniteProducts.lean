/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Simon Hudon
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# The natural monoidal structure on any category with finite (co)products.

A category with a monoidal structure provided in this way
is sometimes called a (co-)Cartesian category,
although this is also sometimes used to mean a finitely complete category.
(See <https://ncatlab.org/nlab/show/cartesian+category>.)

As this works with either products or coproducts,
and sometimes we want to think of a different monoidal structure entirely,
we don't set up either construct as an instance.

## TODO

Once we have cocartesian-monoidal categories, replace `monoidalOfHasFiniteCoproducts` and
`symmetricOfHasFiniteCoproducts` with `CocartesianMonoidalCategory.ofHasFiniteCoproducts`.
-/

@[expose] public section


universe v u

noncomputable section

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] {X Y : C}

open CategoryTheory.Limits

section

#adaptation_note /-- prior to nightly-2026-02-05
the four fields starting from `id_tensorHom_id` were provided by the auto_param -/
/-- A category with an initial object and binary coproducts has a natural monoidal structure. -/
@[instance_reducible]
/--
Definition of `monoidalOfHasFiniteCoproducts` / `monoidalOfHasFiniteCoproducts` 的定义

English:
definition monoidalOfHasFiniteCoproducts
  signature: [HasInitial C] [HasBinaryCoproducts C]
  body: letI : MonoidalCategoryStruct C := {
    tensorObj := fun X Y => X ⨿ Y
    whiskerLeft := fun _ _ _ g => Limits.coprod.map (𝟙 _) g
    whiskerRight := fun {_ _} f _ => Limits.coprod.map f (𝟙 _)
    tensorHom := fun f g => Limits.coprod.map f g
    tensorUnit := ⊥_ C
    associator := coprod.associat

中文:
定义 monoidalOfHasFiniteCoproducts
  签名: [HasInitial C] [HasBinaryCoproducts C]
  定义体: letI : MonoidalCategoryStruct C := {
    tensorObj := fun X Y => X ⨿ Y
    whiskerLeft := fun _ _ _ g => Limits.coprod.map (𝟙 _) g
    whiskerRight := fun {_ _} f _ => Limits.coprod.map f (𝟙 _)
    tensorHom := fun f g => Limits.coprod.map f g
    tensorUnit := ⊥_ C
    associator := coprod.associat

Depends on / 依赖: Limits, Limits.coprod.map, MonoidalCategoryStruct, associator, associator_naturality, coprod, coprod.associator, coprod.associator_naturality, coprod.leftUnitor, coprod.pentagon, coprod.rightUnitor, coprod.triangle, id_tensorHom_id, leftUnitor, ofTensorHom, pentagon, rightUnitor, tensorHom, tensorObj, tensorUnit
-/
def monoidalOfHasFiniteCoproducts [HasInitial C] [HasBinaryCoproducts C] : MonoidalCategory C :=
  letI : MonoidalCategoryStruct C := {
    tensorObj := fun X Y => X ⨿ Y
    whiskerLeft := fun _ _ _ g => Limits.coprod.map (𝟙 _) g
    whiskerRight := fun {_ _} f _ => Limits.coprod.map f (𝟙 _)
    tensorHom := fun f g => Limits.coprod.map f g
    tensorUnit := ⊥_ C
    associator := coprod.associator
    leftUnitor := coprod.leftUnitor
    rightUnitor := coprod.rightUnitor
  }
  .ofTensorHom
    (pentagon := coprod.pentagon)
    (triangle := coprod.triangle)
    (associator_naturality := @coprod.associator_naturality _ _ _)
    (id_tensorHom_id := fun _ _ => coprod.map_id_id)
    (tensorHom_comp_tensorHom := coprod.map_map)
    (leftUnitor_naturality := coprod.leftUnitor_naturality)
    (rightUnitor_naturality := coprod.rightUnitor_naturality)

end

namespace monoidalOfHasFiniteCoproducts

variable [HasInitial C] [HasBinaryCoproducts C]

attribute [local instance] monoidalOfHasFiniteCoproducts

open scoped MonoidalCategory

@[simp]
/--
theorem `tensorObj` / 定理 `tensorObj`

English:
theorem tensorObj
  given: (X Y : C)
  statement: X otimes Y = (X ⨿ Y)
  proof: rfl

@[simp]

中文:
定理 tensorObj
  条件: (X Y : C)
  结论: X otimes Y = (X ⨿ Y)
  证明: rfl

@[simp]
-/
theorem tensorObj (X Y : C) : X otimes Y = (X ⨿ Y) :=
  rfl

@[simp]
/--
theorem `tensorHom` / 定理 `tensorHom`

English:
theorem tensorHom
  given: {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z)
  statement: f otimesₘ g = Limits.coprod.map f g
  proof: rfl

@[simp]

中文:
定理 tensorHom
  条件: {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z)
  结论: f otimesₘ g = Limits.coprod.map f g
  证明: rfl

@[simp]
-/
theorem tensorHom {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) : f otimesₘ g = Limits.coprod.map f g :=
  rfl

@[simp]
/--
theorem `whiskerLeft` / 定理 `whiskerLeft`

English:
theorem whiskerLeft
  given: (X : C) {Y Z : C} (f : Y ⟶ Z)
  statement: X ◁ f = Limits.coprod.map (𝟙 X) f
  proof: rfl

@[simp]

中文:
定理 whiskerLeft
  条件: (X : C) {Y Z : C} (f : Y ⟶ Z)
  结论: X ◁ f = Limits.coprod.map (𝟙 X) f
  证明: rfl

@[simp]
-/
theorem whiskerLeft (X : C) {Y Z : C} (f : Y ⟶ Z) : X ◁ f = Limits.coprod.map (𝟙 X) f :=
  rfl

@[simp]
/--
theorem `whiskerRight` / 定理 `whiskerRight`

English:
theorem whiskerRight
  given: {X Y : C} (f : X ⟶ Y) (Z : C)
  statement: f ▷ Z = Limits.coprod.map f (𝟙 Z)
  proof: rfl

@[simp]

中文:
定理 whiskerRight
  条件: {X Y : C} (f : X ⟶ Y) (Z : C)
  结论: f ▷ Z = Limits.coprod.map f (𝟙 Z)
  证明: rfl

@[simp]
-/
theorem whiskerRight {X Y : C} (f : X ⟶ Y) (Z : C) : f ▷ Z = Limits.coprod.map f (𝟙 Z) :=
  rfl

@[simp]
/--
theorem `leftUnitor_hom` / 定理 `leftUnitor_hom`

English:
theorem leftUnitor_hom
  given: (X : C)
  statement: (fun_ X).hom = coprod.desc (initial.to X) (𝟙 _)
  proof: rfl

@[simp]

中文:
定理 leftUnitor_hom
  条件: (X : C)
  结论: (fun_ X).hom = coprod.desc (initial.to X) (𝟙 _)
  证明: rfl

@[simp]
-/
theorem leftUnitor_hom (X : C) : (fun_ X).hom = coprod.desc (initial.to X) (𝟙 _) :=
  rfl

@[simp]
/--
theorem `rightUnitor_hom` / 定理 `rightUnitor_hom`

English:
theorem rightUnitor_hom
  given: (X : C)
  statement: (ρ_ X).hom = coprod.desc (𝟙 _) (initial.to X)
  proof: rfl

@[simp]

中文:
定理 rightUnitor_hom
  条件: (X : C)
  结论: (ρ_ X).hom = coprod.desc (𝟙 _) (initial.to X)
  证明: rfl

@[simp]
-/
theorem rightUnitor_hom (X : C) : (ρ_ X).hom = coprod.desc (𝟙 _) (initial.to X) :=
  rfl

@[simp]
/--
theorem `leftUnitor_inv` / 定理 `leftUnitor_inv`

English:
theorem leftUnitor_inv
  given: (X : C)
  statement: (fun_ X).inv = Limits.coprod.inr
  proof: rfl

@[simp]

中文:
定理 leftUnitor_inv
  条件: (X : C)
  结论: (fun_ X).inv = Limits.coprod.inr
  证明: rfl

@[simp]
-/
theorem leftUnitor_inv (X : C) : (fun_ X).inv = Limits.coprod.inr :=
  rfl

@[simp]
/--
theorem `rightUnitor_inv` / 定理 `rightUnitor_inv`

English:
theorem rightUnitor_inv
  given: (X : C)
  statement: (ρ_ X).inv = Limits.coprod.inl
  proof: rfl

中文:
定理 rightUnitor_inv
  条件: (X : C)
  结论: (ρ_ X).inv = Limits.coprod.inl
  证明: rfl
-/
theorem rightUnitor_inv (X : C) : (ρ_ X).inv = Limits.coprod.inl :=
  rfl

-- We don't mark this as a simp lemma, even though in many particular
-- categories the right-hand side will simplify significantly further.
-- For now, we'll plan to create specialised simp lemmas in each particular category.
/--
theorem `associator_hom` / 定理 `associator_hom`

English:
theorem associator_hom
  given: (X Y Z : C)
  proof: rfl

中文:
定理 associator_hom
  条件: (X Y Z : C)
  证明: rfl

Depends on / 依赖: equalizer_le, homOfLe
-/
theorem associator_hom (X Y Z : C) :
    (α_ X Y Z).hom =
      coprod.desc (coprod.desc coprod.inl (coprod.inl ≫ coprod.inr)) (coprod.inr ≫ coprod.inr) :=
  rfl

/--
theorem `associator_inv` / 定理 `associator_inv`

English:
theorem associator_inv
  given: (X Y Z : C)
  proof: rfl

中文:
定理 associator_inv
  条件: (X Y Z : C)
  证明: rfl
-/
theorem associator_inv (X Y Z : C) :
    (α_ X Y Z).inv =
      coprod.desc (coprod.inl ≫ coprod.inl) (coprod.desc (coprod.inr ≫ coprod.inl) coprod.inr) :=
  rfl

end monoidalOfHasFiniteCoproducts

section

attribute [local instance] monoidalOfHasFiniteCoproducts

open MonoidalCategory

set_option backward.isDefEq.respectTransparency false in
/-- The monoidal structure coming from finite coproducts is symmetric.
-/
@[simps, instance_reducible]
/--
Definition of `symmetricOfHasFiniteCoproducts` / `symmetricOfHasFiniteCoproducts` 的定义

English:
definition symmetricOfHasFiniteCoproducts
  signature: [HasInitial C] [HasBinaryCoproducts C]
  body: Limits.coprod.braiding
  braiding_naturality_left f g := by simp
  braiding_naturality_right f g := by simp
  hexagon_forward X Y Z := by dsimp [monoidalOfHasFiniteCoproducts.associator_hom]; simp
  hexagon_reverse X Y Z := by dsimp [monoidalOfHasFiniteCoproducts.associator_inv]; simp
  symmetry X Y

中文:
定义 symmetricOfHasFiniteCoproducts
  签名: [HasInitial C] [HasBinaryCoproducts C]
  定义体: Limits.coprod.braiding
  braiding_naturality_left f g := by simp
  braiding_naturality_right f g := by simp
  hexagon_forward X Y Z := by dsimp [monoidalOfHasFiniteCoproducts.associator_hom]; simp
  hexagon_reverse X Y Z := by dsimp [monoidalOfHasFiniteCoproducts.associator_inv]; simp
  symmetry X Y

Depends on / 依赖: Limits, Limits.coprod.braiding, braiding, coprod
-/
def symmetricOfHasFiniteCoproducts [HasInitial C] [HasBinaryCoproducts C] :
    SymmetricCategory C where
  braiding := Limits.coprod.braiding
  braiding_naturality_left f g := by simp
  braiding_naturality_right f g := by simp
  hexagon_forward X Y Z := by dsimp [monoidalOfHasFiniteCoproducts.associator_hom]; simp
  hexagon_reverse X Y Z := by dsimp [monoidalOfHasFiniteCoproducts.associator_inv]; simp
  symmetry X Y := by simp

end

end CategoryTheory
