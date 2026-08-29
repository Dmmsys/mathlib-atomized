/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Limits.Cones
public import Mathlib.CategoryTheory.FinCategory.Basic
public import Mathlib.Data.Finset.Lattice.Lemmas

/-!
# Bicones

Given a category `J`, a walking `Bicone J` is a category whose objects are the objects of `J` and
two extra vertices `Bicone.left` and `Bicone.right`. The morphisms are the morphisms of `J` and
`left ⟶ j`, `right ⟶ j` for each `j : J` such that `(· ⟶ j)` and `(· ⟶ k)` commutes with each
`f : j ⟶ k`.

Given a diagram `F : J ⥤ C` and two `Cone F`s, we can join them into a diagram `Bicone J ⥤ C` via
`biconeMk`.

This is used in `CategoryTheory.Functor.Flat`.
-/

@[expose] public section


universe v₁ u₁

noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory

section Bicone

/--
Inductive type `Bicone` / 归纳类型 `Bicone`

English:
inductive Bicone
  parameters: (J : Type u₁)
  constructors (3):
    - left: Bicone J
    - right: Bicone J
    - diagram: (val : J) : Bicone J

中文:
归纳类型 Bicone
  参数: (J : 类型u₁)
  构造子 (3 个):
    - left: Bicone J
    - right: Bicone J
    - diagram: (val : J) : Bicone J
-/
inductive Bicone (J : Type u₁)
  | left : Bicone J
  | right : Bicone J
  | diagram (val : J) : Bicone J
  deriving DecidableEq

variable (J : Type u₁)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Bicone J)
  body: ⟨Bicone.left⟩

中文:
实例 :
  签名: 可居 (Bicone J)
  定义体: ⟨Bicone.left⟩

Depends on / 依赖: Bicone, Bicone.left
-/
instance : Inhabited (Bicone J) :=
  ⟨Bicone.left⟩

open scoped Classical in
/--
Instance `finBicone` / 实例 `finBicone`

English:
instance finBicone
  signature: [Fintype J]
  body: [Bicone.left, Bicone.right].toFinset union Finset.image Bicone.diagram Fintype.elems
  complete j := by
    cases j <;> simp [Fintype.complete]

中文:
实例 finBicone
  签名: [有限类型 J]
  定义体: [Bicone.left, Bicone.right].toFinset union Finset.image Bicone.diagram Fintype.elems
  complete j := by
    cases j <;> simp [Fintype.complete]

Depends on / 依赖: Bicone, Bicone.diagram, Bicone.left, Bicone.right, Finset, Finset.image, Fintype, Fintype.elems, diagram, toFinset
-/
instance finBicone [Fintype J] : Fintype (Bicone J) where
  elems := [Bicone.left, Bicone.right].toFinset union Finset.image Bicone.diagram Fintype.elems
  complete j := by
    cases j <;> simp [Fintype.complete]

variable [Category.{v₁} J]

/--
Inductive type `BiconeHom` / 归纳类型 `BiconeHom`

English:
inductive BiconeHom
  parameters: : Bicone J -> Bicone J -> Type max u₁ v₁
  constructors (5):
    - left_id: BiconeHom Bicone.left Bicone.left
    - right_id: BiconeHom Bicone.right Bicone.right
    - left: (j : J) : BiconeHom Bicone.left (Bicone.diagram j)
    - right: (j : J) : BiconeHom Bicone.right (Bicone.diagram j)
    - diagram: {j k : J} (f : j ⟶ k) : BiconeHom (Bicone.diagram j) (Bicone.diagram k)

中文:
归纳类型 Bicone态射
  参数: : Bicone J -> Bicone J -> 类型 最大值 u₁ v₁
  构造子 (5 个):
    - left_id: Bicone态射 Bicone.left Bicone.left
    - right_id: Bicone态射 Bicone.right Bicone.right
    - left: (j : J) : Bicone态射 Bicone.left (Bicone.diagram j)
    - right: (j : J) : Bicone态射 Bicone.right (Bicone.diagram j)
    - diagram: {j k : J} (f : j ⟶ k) : Bicone态射 (Bicone.diagram j) (Bicone.diagram k)
-/
inductive BiconeHom : Bicone J -> Bicone J -> Type max u₁ v₁
  | left_id : BiconeHom Bicone.left Bicone.left
  | right_id : BiconeHom Bicone.right Bicone.right
  | left (j : J) : BiconeHom Bicone.left (Bicone.diagram j)
  | right (j : J) : BiconeHom Bicone.right (Bicone.diagram j)
  | diagram {j k : J} (f : j ⟶ k) : BiconeHom (Bicone.diagram j) (Bicone.diagram k)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (BiconeHom J Bicone.left Bicone.left)
  body: ⟨BiconeHom.left_id⟩

中文:
实例 :
  签名: 可居 (Bicone态射 J Bicone.left Bicone.left)
  定义体: ⟨BiconeHom.left_id⟩

Depends on / 依赖: BiconeHom, BiconeHom.left_id, left_id
-/
instance : Inhabited (BiconeHom J Bicone.left Bicone.left) :=
  ⟨BiconeHom.left_id⟩

/--
Instance `BiconeHom.decidableEq` / 实例 `BiconeHom.decidableEq`

English:
instance BiconeHom.decidableEq
  signature: {j k : Bicone J}
  body: fun f g => by
  classical cases f <;> cases g <;> simp only [diagram.injEq] <;> infer_instance

@[simps]

中文:
实例 Bicone态射.decidableEq
  签名: {j k : Bicone J}
  定义体: fun f g => by
  classical cases f <;> cases g <;> simp only [diagram.injEq] <;> infer_instance

@[simps]

Depends on / 依赖: classical, diagram, diagram.injEq, infer_instance
-/
instance BiconeHom.decidableEq {j k : Bicone J} : DecidableEq (BiconeHom J j k) := fun f g => by
  classical cases f <;> cases g <;> simp only [diagram.injEq] <;> infer_instance

@[simps]
/--
Instance `biconeCategoryStruct` / 实例 `biconeCategoryStruct`

English:
instance biconeCategoryStruct
  signature: : CategoryStruct (Bicone J) where
  body: BiconeHom J
  id j := Bicone.casesOn j BiconeHom.left_id BiconeHom.right_id fun k => BiconeHom.diagram (𝟙 k)
  comp f g := by
    rcases f with (_ | _ | _ | _ | f)
    · exact g
    · exact g
    · cases g
      apply BiconeHom.left
    · cases g
      apply BiconeHom.right
    · rcases g with (_ | 

中文:
实例 biconeCategoryStruct
  签名: : CategoryStruct (Bicone J) where
  定义体: BiconeHom J
  id j := Bicone.casesOn j BiconeHom.left_id BiconeHom.right_id fun k => BiconeHom.diagram (𝟙 k)
  comp f g := by
    rcases f with (_ | _ | _ | _ | f)
    · exact g
    · exact g
    · cases g
      apply BiconeHom.left
    · cases g
      apply BiconeHom.right
    · rcases g with (_ | 

Depends on / 依赖: BiconeHom
-/
instance biconeCategoryStruct : CategoryStruct (Bicone J) where
  Hom := BiconeHom J
  id j := Bicone.casesOn j BiconeHom.left_id BiconeHom.right_id fun k => BiconeHom.diagram (𝟙 k)
  comp f g := by
    rcases f with (_ | _ | _ | _ | f)
    · exact g
    · exact g
    · cases g
      apply BiconeHom.left
    · cases g
      apply BiconeHom.right
    · rcases g with (_ | _ | _ | _ | g)
      exact BiconeHom.diagram (f ≫ g)

/--
Instance `biconeCategory` / 实例 `biconeCategory`

English:
instance biconeCategory
  signature: : Category (Bicone J) where
  body: by cases f <;> simp
  comp_id f := by cases f <;> simp
  assoc f g h := by cases f <;> cases g <;> cases h <;> simp

中文:
实例 biconeCategory
  签名: : 范畴 (Bicone J) where
  定义体: by cases f <;> simp
  comp_id f := by cases f <;> simp
  assoc f g h := by cases f <;> cases g <;> cases h <;> simp

Depends on / 依赖: comp_id
-/
instance biconeCategory : Category (Bicone J) where
  id_comp f := by cases f <;> simp
  comp_id f := by cases f <;> simp
  assoc f g h := by cases f <;> cases g <;> cases h <;> simp

end Bicone

section SmallCategory

variable (J : Type v₁) [SmallCategory J]

/-- Given a diagram `F : J ⥤ C` and two `Cone F`s, we can join them into a diagram `Bicone J ⥤ C`.
-/
@[simps]
/--
Definition of `biconeMk` / `biconeMk` 的定义

English:
definition biconeMk
  signature: {C : Type u₁} [Category.{v₁} C] {F : J ⥤ C} (c₁ c₂ : Cone F)
  body: Bicone.casesOn X c₁.pt c₂.pt fun j => F.obj j
  map f := by
    rcases f with (_ | _ | _ | _ | f)
    · exact 𝟙 _
    · exact 𝟙 _
    · exact c₁.π.app _
    · exact c₂.π.app _
    · exact F.map f
  map_id X := by cases X <;> simp
  map_comp f g := by
    rcases f with (_ | _ | _ | _ | _)
    · exact

中文:
定义 biconeMk
  签名: {C : 类型u₁} [范畴.{v₁} C] {F : J ⥤ C} (c₁ c₂ : 锥 F)
  定义体: Bicone.casesOn X c₁.pt c₂.pt fun j => F.obj j
  map f := by
    rcases f with (_ | _ | _ | _ | f)
    · exact 𝟙 _
    · exact 𝟙 _
    · exact c₁.π.app _
    · exact c₂.π.app _
    · exact F.map f
  map_id X := by cases X <;> simp
  map_comp f g := by
    rcases f with (_ | _ | _ | _ | _)
    · exact

Depends on / 依赖: Bicone, Bicone.casesOn, F.obj, casesOn
-/
def biconeMk {C : Type u₁} [Category.{v₁} C] {F : J ⥤ C} (c₁ c₂ : Cone F) : Bicone J ⥤ C where
  obj X := Bicone.casesOn X c₁.pt c₂.pt fun j => F.obj j
  map f := by
    rcases f with (_ | _ | _ | _ | f)
    · exact 𝟙 _
    · exact 𝟙 _
    · exact c₁.π.app _
    · exact c₂.π.app _
    · exact F.map f
  map_id X := by cases X <;> simp
  map_comp f g := by
    rcases f with (_ | _ | _ | _ | _)
    · exact (Category.id_comp _).symm
    · exact (Category.id_comp _).symm
    · cases g
      exact (Category.id_comp _).symm.trans (c₁.π.naturality _)
    · cases g
      exact (Category.id_comp _).symm.trans (c₂.π.naturality _)
    · cases g
      apply F.map_comp

open scoped Classical in
/--
Instance `finBiconeHom` / 实例 `finBiconeHom`

English:
instance finBiconeHom
  signature: [FinCategory J] (j k : Bicone J)
  body: by
  cases j <;> cases k
  · exact
      { elems := {BiconeHom.left_id}
        complete := fun f => by cases f; simp }
  · exact
    { elems := ∅
      complete := fun f => by cases f }
  · exact
    { elems := {BiconeHom.left _}
      complete := fun f => by cases f; simp }
  · exact
    { elems :

中文:
实例 finBiconeHom
  签名: [有限范畴 J] (j k : Bicone J)
  定义体: by
  cases j <;> cases k
  · exact
      { elems := {BiconeHom.left_id}
        complete := fun f => by cases f; simp }
  · exact
    { elems := ∅
      complete := fun f => by cases f }
  · exact
    { elems := {BiconeHom.left _}
      complete := fun f => by cases f; simp }
  · exact
    { elems :

Depends on / 依赖: BiconeHom, BiconeHom.left, BiconeHom.left_id, BiconeHom.right, BiconeHom.right_id, complete, left_id, right_id
-/
instance finBiconeHom [FinCategory J] (j k : Bicone J) : Fintype (j ⟶ k) := by
  cases j <;> cases k
  · exact
      { elems := {BiconeHom.left_id}
        complete := fun f => by cases f; simp }
  · exact
    { elems := ∅
      complete := fun f => by cases f }
  · exact
    { elems := {BiconeHom.left _}
      complete := fun f => by cases f; simp }
  · exact
    { elems := ∅
      complete := fun f => by cases f }
  · exact
      { elems := {BiconeHom.right_id}
        complete := fun f => by cases f; simp }
  · exact
    { elems := {BiconeHom.right _}
      complete := fun f => by cases f; simp }
  · exact
    { elems := ∅
      complete := fun f => by cases f }
  · exact
    { elems := ∅
      complete := fun f => by cases f }
  · exact
    { elems := Finset.image BiconeHom.diagram Fintype.elems
      complete := fun f => by
        rcases f with (_ | _ | _ | _ | f)
        simp only [Finset.mem_image]
        use f
        simpa using Fintype.complete _ }

/--
Instance `biconeSmallCategory` / 实例 `biconeSmallCategory`

English:
instance biconeSmallCategory
  signature: : SmallCategory (Bicone J)
  body: CategoryTheory.biconeCategory J

中文:
实例 biconeSmallCategory
  签名: : 小范畴 (Bicone J)
  定义体: CategoryTheory.biconeCategory J

Depends on / 依赖: CategoryTheory, CategoryTheory.biconeCategory, biconeCategory
-/
instance biconeSmallCategory : SmallCategory (Bicone J) :=
  CategoryTheory.biconeCategory J

/--
Instance `biconeFinCategory` / 实例 `biconeFinCategory`

English:
instance biconeFinCategory
  signature: [FinCategory J]

中文:
实例 biconeFinCategory
  签名: [有限范畴 J]
-/
instance biconeFinCategory [FinCategory J] : FinCategory (Bicone J) where

end SmallCategory

end CategoryTheory
