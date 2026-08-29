/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.PEmpty
public import Mathlib.CategoryTheory.Limits.IsLimit
public import Mathlib.CategoryTheory.EpiMono
public import Mathlib.CategoryTheory.Category.Preorder

/-!
# Initial and terminal objects in a category.

In this file we define the predicates `IsTerminal` and `IsInitial` as well as the class
`InitialMonoClass`.

The classes `HasTerminal` and `HasInitial` and the associated notations for terminal and initial
objects are defined in `Terminal.lean`.

## References
* [Stacks: Initial and final objects](https://stacks.math.columbia.edu/tag/002B)
-/

@[expose] public section

assert_not_exists CategoryTheory.Limits.HasLimit

noncomputable section

universe w w' v v₁ v₂ u u₁ u₂

open CategoryTheory Opposite

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
/-- Construct a cone for the empty diagram given an object. -/
@[simps, implicit_reducible]
/--
Definition of `asEmptyCone` / `asEmptyCone` 的定义

English:
definition asEmptyCone
  signature: (X : C)
  body: { pt := X
    π :=
    { app := by cat_disch } }

#adaptation_note

中文:
定义 asEmptyCone
  签名: (X : C)
  定义体: { pt := X
    π :=
    { app := by cat_disch } }

#adaptation_note

Depends on / 依赖: cat_disch
-/
def asEmptyCone (X : C) : Cone (Functor.empty.{0} C) :=
  { pt := X
    π :=
    { app := by cat_disch } }

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
/-- Construct a cocone for the empty diagram given an object. -/
@[implicit_reducible, simps]
/--
Definition of `asEmptyCocone` / `asEmptyCocone` 的定义

English:
definition asEmptyCocone
  signature: (X : C)
  body: { pt := X
    ι :=
    { app := by cat_disch } }

中文:
定义 asEmptyCocone
  签名: (X : C)
  定义体: { pt := X
    ι :=
    { app := by cat_disch } }

Depends on / 依赖: cat_disch
-/
def asEmptyCocone (X : C) : Cocone (Functor.empty.{0} C) :=
  { pt := X
    ι :=
    { app := by cat_disch } }

/--
Definition of `IsTerminal` / `IsTerminal` 的定义

English:
abbreviation IsTerminal
  signature: (X : C)
  body: IsLimit (asEmptyCone X)

中文:
缩写 IsTerminal
  签名: (X : C)
  定义体: IsLimit (asEmptyCone X)

Depends on / 依赖: IsLimit, asEmptyCone
-/
abbrev IsTerminal (X : C) :=
  IsLimit (asEmptyCone X)

/--
Definition of `IsInitial` / `IsInitial` 的定义

English:
abbreviation IsInitial
  signature: (X : C)
  body: IsColimit (asEmptyCocone X)

中文:
缩写 IsInitial
  签名: (X : C)
  定义体: IsColimit (asEmptyCocone X)

Depends on / 依赖: IsColimit, asEmptyCocone
-/
abbrev IsInitial (X : C) :=
  IsColimit (asEmptyCocone X)

/--
Definition of `isTerminalEquivUnique` / `isTerminalEquivUnique` 的定义

English:
definition isTerminalEquivUnique
  signature: (F : Discrete.{0} PEmpty.{1} ⥤ C) (Y : C)
  body: { default := t.lift ⟨X, ⟨by cat_disch, by simp⟩⟩
      uniq := fun f =>
        t.uniq ⟨X, ⟨by cat_disch, by simp⟩⟩ f (by simp) }
  invFun u :=
    { lift := fun s => (u s.pt).default
      uniq := fun s _ _ => (u s.pt).2 _ }
  left_inv := by dsimp [Function.LeftInverse]; intro x; simp only [eq_iff_

中文:
定义 isTerminalEquivUnique
  签名: (F : Discrete.{0} PEmpty.{1} ⥤ C) (Y : C)
  定义体: { default := t.lift ⟨X, ⟨by cat_disch, by simp⟩⟩
      uniq := fun f =>
        t.uniq ⟨X, ⟨by cat_disch, by simp⟩⟩ f (by simp) }
  invFun u :=
    { lift := fun s => (u s.pt).default
      uniq := fun s _ _ => (u s.pt).2 _ }
  left_inv := by dsimp [Function.LeftInverse]; intro x; simp only [eq_iff_

Depends on / 依赖: Function, Function.LeftInverse, Function.RightInverse, LeftInverse, RightInverse, cat_disch, eq_iff_true_of_subsingleton, invFun, left_inv, right_inv, s.pt, subsingleton, t.lift, t.uniq
-/
def isTerminalEquivUnique (F : Discrete.{0} PEmpty.{1} ⥤ C) (Y : C) :
    IsLimit (⟨Y, by cat_disch, by simp⟩ : Cone F) ≃ forall X : C, Unique (X ⟶ Y) where
  toFun t X :=
    { default := t.lift ⟨X, ⟨by cat_disch, by simp⟩⟩
      uniq := fun f =>
        t.uniq ⟨X, ⟨by cat_disch, by simp⟩⟩ f (by simp) }
  invFun u :=
    { lift := fun s => (u s.pt).default
      uniq := fun s _ _ => (u s.pt).2 _ }
  left_inv := by dsimp [Function.LeftInverse]; intro x; simp only [eq_iff_true_of_subsingleton]
  right_inv := by
    dsimp [Function.RightInverse, Function.LeftInverse]
    subsingleton

/--
Definition of `IsTerminal.ofUnique` / `IsTerminal.ofUnique` 的定义

English:
definition IsTerminal.ofUnique
  signature: (Y : C) [h : forall X : C, Unique (X ⟶ Y)]
  body: (h s.pt).default
  fac := fun _ ⟨j⟩ => j.elim

中文:
定义 IsTerminal.ofUnique
  签名: (Y : C) [h : 对任意 X : C, Unique (X ⟶ Y)]
  定义体: (h s.pt).default
  fac := fun _ ⟨j⟩ => j.elim

Depends on / 依赖: s.pt
-/
def IsTerminal.ofUnique (Y : C) [h : forall X : C, Unique (X ⟶ Y)] : IsTerminal Y where
  lift s := (h s.pt).default
  fac := fun _ ⟨j⟩ => j.elim

/--
Definition of `IsTerminal.ofUniqueHom` / `IsTerminal.ofUniqueHom` 的定义

English:
definition IsTerminal.ofUniqueHom
  signature: {Y : C} (h : forall X : C, X ⟶ Y) (uniq : forall (X : C) (m : X ⟶ Y), m = h X)
  body: have : forall X : C, Unique (X ⟶ Y) := fun X => ⟨⟨h X⟩, uniq X⟩
  IsTerminal.ofUnique Y

中文:
定义 IsTerminal.ofUniqueHom
  签名: {Y : C} (h : 对任意 X : C, X ⟶ Y) (uniq : 对任意 (X : C) (m : X ⟶ Y), m = h X)
  定义体: have : forall X : C, Unique (X ⟶ Y) := fun X => ⟨⟨h X⟩, uniq X⟩
  IsTerminal.ofUnique Y

Depends on / 依赖: IsTerminal, IsTerminal.ofUnique, Unique, ofUnique
-/
def IsTerminal.ofUniqueHom {Y : C} (h : forall X : C, X ⟶ Y) (uniq : forall (X : C) (m : X ⟶ Y), m = h X) :
    IsTerminal Y :=
  have : forall X : C, Unique (X ⟶ Y) := fun X => ⟨⟨h X⟩, uniq X⟩
  IsTerminal.ofUnique Y

/--
Definition of `isTerminalTop` / `isTerminalTop` 的定义

English:
definition isTerminalTop
  signature: {α : Type*} [Preorder α] [OrderTop α]
  body: IsTerminal.ofUnique _

中文:
定义 isTerminalTop
  签名: {α : 类型} [Preorder α] [OrderTop α]
  定义体: IsTerminal.ofUnique _

Depends on / 依赖: IsTerminal, IsTerminal.ofUnique, ofUnique
-/
def isTerminalTop {α : Type*} [Preorder α] [OrderTop α] : IsTerminal (⊤ : α) :=
  IsTerminal.ofUnique _

/--
Definition of `IsTerminal.ofIso` / `IsTerminal.ofIso` 的定义

English:
definition IsTerminal.ofIso
  signature: {Y Z : C} (hY : IsTerminal Y) (i : Y ≅ Z)
  body: IsLimit.ofIsoLimit hY
    { hom := { hom := i.hom }
      inv := { hom := i.inv } }

中文:
定义 IsTerminal.ofIso
  签名: {Y Z : C} (hY : IsTerminal Y) (i : Y ≅ Z)
  定义体: IsLimit.ofIsoLimit hY
    { hom := { hom := i.hom }
      inv := { hom := i.inv } }

Depends on / 依赖: IsLimit, IsLimit.ofIsoLimit, i.hom, i.inv, ofIsoLimit
-/
def IsTerminal.ofIso {Y Z : C} (hY : IsTerminal Y) (i : Y ≅ Z) : IsTerminal Z :=
  IsLimit.ofIsoLimit hY
    { hom := { hom := i.hom }
      inv := { hom := i.inv } }

/--
Definition of `IsTerminal.equivOfIso` / `IsTerminal.equivOfIso` 的定义

English:
definition IsTerminal.equivOfIso
  signature: {X Y : C} (e : X ≅ Y)
  body: IsTerminal.ofIso h e
  invFun h := IsTerminal.ofIso h e.symm
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

中文:
定义 IsTerminal.equivOfIso
  签名: {X Y : C} (e : X ≅ Y)
  定义体: IsTerminal.ofIso h e
  invFun h := IsTerminal.ofIso h e.symm
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

Depends on / 依赖: IsTerminal, IsTerminal.ofIso
-/
def IsTerminal.equivOfIso {X Y : C} (e : X ≅ Y) :
    IsTerminal X ≃ IsTerminal Y where
  toFun h := IsTerminal.ofIso h e
  invFun h := IsTerminal.ofIso h e.symm
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/--
Definition of `isInitialEquivUnique` / `isInitialEquivUnique` 的定义

English:
definition isInitialEquivUnique
  signature: (F : Discrete.{0} PEmpty.{1} ⥤ C) (X : C)
  body: { default := t.desc ⟨X, ⟨by cat_disch, by simp⟩⟩
      uniq := fun f => t.uniq ⟨X, ⟨by cat_disch, by simp⟩⟩ f (by simp) }
  invFun u :=
    { desc := fun s => (u s.pt).default
      uniq := fun s _ _ => (u s.pt).2 _ }
  left_inv := by dsimp [Function.LeftInverse]; intro; simp only [eq_iff_true_of_su

中文:
定义 isInitialEquivUnique
  签名: (F : Discrete.{0} PEmpty.{1} ⥤ C) (X : C)
  定义体: { default := t.desc ⟨X, ⟨by cat_disch, by simp⟩⟩
      uniq := fun f => t.uniq ⟨X, ⟨by cat_disch, by simp⟩⟩ f (by simp) }
  invFun u :=
    { desc := fun s => (u s.pt).default
      uniq := fun s _ _ => (u s.pt).2 _ }
  left_inv := by dsimp [Function.LeftInverse]; intro; simp only [eq_iff_true_of_su

Depends on / 依赖: Function, Function.LeftInverse, LeftInverse, cat_disch, eq_iff_true_of_subsingleton, invFun, left_inv, right_inv, s.pt, t.desc, t.uniq
-/
def isInitialEquivUnique (F : Discrete.{0} PEmpty.{1} ⥤ C) (X : C) :
    IsColimit (⟨X, ⟨by cat_disch, by simp⟩⟩ : Cocone F) ≃ forall Y : C, Unique (X ⟶ Y) where
  toFun t X :=
    { default := t.desc ⟨X, ⟨by cat_disch, by simp⟩⟩
      uniq := fun f => t.uniq ⟨X, ⟨by cat_disch, by simp⟩⟩ f (by simp) }
  invFun u :=
    { desc := fun s => (u s.pt).default
      uniq := fun s _ _ => (u s.pt).2 _ }
  left_inv := by dsimp [Function.LeftInverse]; intro; simp only [eq_iff_true_of_subsingleton]
  right_inv := by grind

/--
Definition of `IsInitial.ofUnique` / `IsInitial.ofUnique` 的定义

English:
definition IsInitial.ofUnique
  signature: (X : C) [h : forall Y : C, Unique (X ⟶ Y)]
  body: (h s.pt).default
  fac := fun _ ⟨j⟩ => j.elim

中文:
定义 IsInitial.ofUnique
  签名: (X : C) [h : 对任意 Y : C, Unique (X ⟶ Y)]
  定义体: (h s.pt).default
  fac := fun _ ⟨j⟩ => j.elim

Depends on / 依赖: s.pt
-/
def IsInitial.ofUnique (X : C) [h : forall Y : C, Unique (X ⟶ Y)] : IsInitial X where
  desc s := (h s.pt).default
  fac := fun _ ⟨j⟩ => j.elim

/--
Definition of `IsInitial.ofUniqueHom` / `IsInitial.ofUniqueHom` 的定义

English:
definition IsInitial.ofUniqueHom
  signature: {X : C} (h : forall Y : C, X ⟶ Y) (uniq : forall (Y : C) (m : X ⟶ Y), m = h Y)
  body: have : forall Y : C, Unique (X ⟶ Y) := fun Y => ⟨⟨h Y⟩, uniq Y⟩
  IsInitial.ofUnique X

中文:
定义 IsInitial.ofUniqueHom
  签名: {X : C} (h : 对任意 Y : C, X ⟶ Y) (uniq : 对任意 (Y : C) (m : X ⟶ Y), m = h Y)
  定义体: have : forall Y : C, Unique (X ⟶ Y) := fun Y => ⟨⟨h Y⟩, uniq Y⟩
  IsInitial.ofUnique X

Depends on / 依赖: IsInitial, IsInitial.ofUnique, Unique, ofUnique
-/
def IsInitial.ofUniqueHom {X : C} (h : forall Y : C, X ⟶ Y) (uniq : forall (Y : C) (m : X ⟶ Y), m = h Y) :
    IsInitial X :=
  have : forall Y : C, Unique (X ⟶ Y) := fun Y => ⟨⟨h Y⟩, uniq Y⟩
  IsInitial.ofUnique X

/--
Definition of `isInitialBot` / `isInitialBot` 的定义

English:
definition isInitialBot
  signature: {α : Type*} [Preorder α] [OrderBot α]
  body: IsInitial.ofUnique _

中文:
定义 isInitialBot
  签名: {α : 类型} [Preorder α] [OrderBot α]
  定义体: IsInitial.ofUnique _

Depends on / 依赖: IsInitial, IsInitial.ofUnique, ofUnique
-/
def isInitialBot {α : Type*} [Preorder α] [OrderBot α] : IsInitial (⊥ : α) :=
  IsInitial.ofUnique _

/--
Definition of `IsInitial.ofIso` / `IsInitial.ofIso` 的定义

English:
definition IsInitial.ofIso
  signature: {X Y : C} (hX : IsInitial X) (i : X ≅ Y)
  body: IsColimit.ofIsoColimit hX
    { hom := { hom := i.hom }
      inv := { hom := i.inv } }

中文:
定义 IsInitial.ofIso
  签名: {X Y : C} (hX : IsInitial X) (i : X ≅ Y)
  定义体: IsColimit.ofIsoColimit hX
    { hom := { hom := i.hom }
      inv := { hom := i.inv } }

Depends on / 依赖: IsColimit, IsColimit.ofIsoColimit, i.hom, i.inv, ofIsoColimit
-/
def IsInitial.ofIso {X Y : C} (hX : IsInitial X) (i : X ≅ Y) : IsInitial Y :=
  IsColimit.ofIsoColimit hX
    { hom := { hom := i.hom }
      inv := { hom := i.inv } }

/--
Definition of `IsInitial.equivOfIso` / `IsInitial.equivOfIso` 的定义

English:
definition IsInitial.equivOfIso
  signature: {X Y : C} (e : X ≅ Y)
  body: IsInitial.ofIso h e
  invFun h := IsInitial.ofIso h e.symm
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

中文:
定义 IsInitial.equivOfIso
  签名: {X Y : C} (e : X ≅ Y)
  定义体: IsInitial.ofIso h e
  invFun h := IsInitial.ofIso h e.symm
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

Depends on / 依赖: IsInitial, IsInitial.ofIso
-/
def IsInitial.equivOfIso {X Y : C} (e : X ≅ Y) :
    IsInitial X ≃ IsInitial Y where
  toFun h := IsInitial.ofIso h e
  invFun h := IsInitial.ofIso h e.symm
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/--
Definition of `IsTerminal.from` / `IsTerminal.from` 的定义

English:
definition IsTerminal.from
  signature: {X : C} (t : IsTerminal X) (Y : C)
  body: t.lift (asEmptyCone Y)

中文:
定义 IsTerminal.from
  签名: {X : C} (t : IsTerminal X) (Y : C)
  定义体: t.lift (asEmptyCone Y)

Depends on / 依赖: asEmptyCone, t.lift
-/
def IsTerminal.from {X : C} (t : IsTerminal X) (Y : C) : Y ⟶ X :=
  t.lift (asEmptyCone Y)

/--
theorem `IsTerminal.hom_ext` / 定理 `IsTerminal.hom_ext`

English:
theorem IsTerminal.hom_ext
  given: {X Y : C} (t : IsTerminal X) (f g : Y ⟶ X)
  statement: f = g
  proof: IsLimit.hom_ext t (by simp)

@[simp]

中文:
定理 IsTerminal.hom_ext
  条件: {X Y : C} (t : IsTerminal X) (f g : Y ⟶ X)
  结论: f = g
  证明: IsLimit.hom_ext t (by simp)

@[simp]

Depends on / 依赖: IsLimit, IsLimit.hom_ext, hom_ext
-/
theorem IsTerminal.hom_ext {X Y : C} (t : IsTerminal X) (f g : Y ⟶ X) : f = g :=
  IsLimit.hom_ext t (by simp)

@[simp]
/--
theorem `IsTerminal.comp_from` / 定理 `IsTerminal.comp_from`

English:
theorem IsTerminal.comp_from
  given: {Z : C} (t : IsTerminal Z) {X Y : C} (f : X ⟶ Y)
  proof: t.hom_ext _ _

@[simp]

中文:
定理 IsTerminal.comp_from
  条件: {Z : C} (t : IsTerminal Z) {X Y : C} (f : X ⟶ Y)
  证明: t.hom_ext _ _

@[simp]

Depends on / 依赖: hom_ext, t.hom_ext
-/
theorem IsTerminal.comp_from {Z : C} (t : IsTerminal Z) {X Y : C} (f : X ⟶ Y) :
    f ≫ t.from Y = t.from X :=
  t.hom_ext _ _

@[simp]
/--
theorem `IsTerminal.from_self` / 定理 `IsTerminal.from_self`

English:
theorem IsTerminal.from_self
  given: {X : C} (t : IsTerminal X)
  statement: t.from X = 𝟙 X
  proof: t.hom_ext _ _

中文:
定理 IsTerminal.from_self
  条件: {X : C} (t : IsTerminal X)
  结论: t.from X = 𝟙 X
  证明: t.hom_ext _ _

Depends on / 依赖: hom_ext, t.hom_ext
-/
theorem IsTerminal.from_self {X : C} (t : IsTerminal X) : t.from X = 𝟙 X :=
  t.hom_ext _ _

/--
Definition of `IsInitial.to` / `IsInitial.to` 的定义

English:
definition IsInitial.to
  signature: {X : C} (t : IsInitial X) (Y : C)
  body: t.desc (asEmptyCocone Y)

中文:
定义 IsInitial.to
  签名: {X : C} (t : IsInitial X) (Y : C)
  定义体: t.desc (asEmptyCocone Y)

Depends on / 依赖: asEmptyCocone, t.desc
-/
def IsInitial.to {X : C} (t : IsInitial X) (Y : C) : X ⟶ Y :=
  t.desc (asEmptyCocone Y)

/--
theorem `IsInitial.hom_ext` / 定理 `IsInitial.hom_ext`

English:
theorem IsInitial.hom_ext
  given: {X Y : C} (t : IsInitial X) (f g : X ⟶ Y)
  statement: f = g
  proof: IsColimit.hom_ext t (by simp)

@[simp]

中文:
定理 IsInitial.hom_ext
  条件: {X Y : C} (t : IsInitial X) (f g : X ⟶ Y)
  结论: f = g
  证明: IsColimit.hom_ext t (by simp)

@[simp]

Depends on / 依赖: IsColimit, IsColimit.hom_ext, hom_ext
-/
theorem IsInitial.hom_ext {X Y : C} (t : IsInitial X) (f g : X ⟶ Y) : f = g :=
  IsColimit.hom_ext t (by simp)

@[simp]
/--
theorem `IsInitial.to_comp` / 定理 `IsInitial.to_comp`

English:
theorem IsInitial.to_comp
  given: {X : C} (t : IsInitial X) {Y Z : C} (f : Y ⟶ Z)
  statement: t.to Y ≫ f = t.to Z
  proof: t.hom_ext _ _

@[simp]

中文:
定理 IsInitial.to_comp
  条件: {X : C} (t : IsInitial X) {Y Z : C} (f : Y ⟶ Z)
  结论: t.to Y ≫ f = t.to Z
  证明: t.hom_ext _ _

@[simp]

Depends on / 依赖: hom_ext, t.hom_ext
-/
theorem IsInitial.to_comp {X : C} (t : IsInitial X) {Y Z : C} (f : Y ⟶ Z) : t.to Y ≫ f = t.to Z :=
  t.hom_ext _ _

@[simp]
/--
theorem `IsInitial.to_self` / 定理 `IsInitial.to_self`

English:
theorem IsInitial.to_self
  given: {X : C} (t : IsInitial X)
  statement: t.to X = 𝟙 X
  proof: t.hom_ext _ _

中文:
定理 IsInitial.to_self
  条件: {X : C} (t : IsInitial X)
  结论: t.to X = 𝟙 X
  证明: t.hom_ext _ _

Depends on / 依赖: hom_ext, t.hom_ext
-/
theorem IsInitial.to_self {X : C} (t : IsInitial X) : t.to X = 𝟙 X :=
  t.hom_ext _ _

/--
theorem `IsTerminal.isSplitMono_from` / 定理 `IsTerminal.isSplitMono_from`

English:
theorem IsTerminal.isSplitMono_from
  given: {X Y : C} (t : IsTerminal X) (f : X ⟶ Y)
  statement: IsSplitMono f
  proof: IsSplitMono.mk' ⟨t.from _, t.hom_ext _ _⟩

中文:
定理 IsTerminal.isSplitMono_from
  条件: {X Y : C} (t : IsTerminal X) (f : X ⟶ Y)
  结论: IsSplitMono f
  证明: IsSplitMono.mk' ⟨t.from _, t.hom_ext _ _⟩

Depends on / 依赖: IsSplitMono, IsSplitMono.mk, hom_ext, t.from, t.hom_ext
-/
theorem IsTerminal.isSplitMono_from {X Y : C} (t : IsTerminal X) (f : X ⟶ Y) : IsSplitMono f :=
  IsSplitMono.mk' ⟨t.from _, t.hom_ext _ _⟩

/--
theorem `IsInitial.isSplitEpi_to` / 定理 `IsInitial.isSplitEpi_to`

English:
theorem IsInitial.isSplitEpi_to
  given: {X Y : C} (t : IsInitial X) (f : Y ⟶ X)
  statement: IsSplitEpi f
  proof: IsSplitEpi.mk' ⟨t.to _, t.hom_ext _ _⟩

中文:
定理 IsInitial.isSplitEpi_to
  条件: {X Y : C} (t : IsInitial X) (f : Y ⟶ X)
  结论: IsSplitEpi f
  证明: IsSplitEpi.mk' ⟨t.to _, t.hom_ext _ _⟩

Depends on / 依赖: IsSplitEpi, IsSplitEpi.mk, hom_ext, t.hom_ext, t.to
-/
theorem IsInitial.isSplitEpi_to {X Y : C} (t : IsInitial X) (f : Y ⟶ X) : IsSplitEpi f :=
  IsSplitEpi.mk' ⟨t.to _, t.hom_ext _ _⟩

/--
theorem `IsTerminal.mono_from` / 定理 `IsTerminal.mono_from`

English:
theorem IsTerminal.mono_from
  given: {X Y : C} (t : IsTerminal X) (f : X ⟶ Y)
  statement: Mono f
  proof: by
  have := t.isSplitMono_from f; infer_instance

中文:
定理 IsTerminal.mono_from
  条件: {X Y : C} (t : IsTerminal X) (f : X ⟶ Y)
  结论: Mono f
  证明: by
  have := t.isSplitMono_from f; infer_instance

Depends on / 依赖: infer_instance, isSplitMono_from, t.isSplitMono_from
-/
theorem IsTerminal.mono_from {X Y : C} (t : IsTerminal X) (f : X ⟶ Y) : Mono f := by
  have := t.isSplitMono_from f; infer_instance

/--
theorem `IsInitial.epi_to` / 定理 `IsInitial.epi_to`

English:
theorem IsInitial.epi_to
  given: {X Y : C} (t : IsInitial X) (f : Y ⟶ X)
  statement: Epi f
  proof: by
  have := t.isSplitEpi_to f; infer_instance

中文:
定理 IsInitial.epi_to
  条件: {X Y : C} (t : IsInitial X) (f : Y ⟶ X)
  结论: Epi f
  证明: by
  have := t.isSplitEpi_to f; infer_instance

Depends on / 依赖: infer_instance, isSplitEpi_to, t.isSplitEpi_to
-/
theorem IsInitial.epi_to {X Y : C} (t : IsInitial X) (f : Y ⟶ X) : Epi f := by
  have := t.isSplitEpi_to f; infer_instance

/-- If `T` and `T'` are terminal, they are isomorphic. -/
@[simps]
/--
Definition of `IsTerminal.uniqueUpToIso` / `IsTerminal.uniqueUpToIso` 的定义

English:
definition IsTerminal.uniqueUpToIso
  signature: {T T' : C} (hT : IsTerminal T) (hT' : IsTerminal T')
  body: hT'.from _
  inv := hT.from _

中文:
定义 IsTerminal.uniqueUpToIso
  签名: {T T' : C} (hT : IsTerminal T) (hT' : IsTerminal T')
  定义体: hT'.from _
  inv := hT.from _
-/
def IsTerminal.uniqueUpToIso {T T' : C} (hT : IsTerminal T) (hT' : IsTerminal T') : T ≅ T' where
  hom := hT'.from _
  inv := hT.from _

/-- If `I` and `I'` are initial, they are isomorphic. -/
@[simps]
/--
Definition of `IsInitial.uniqueUpToIso` / `IsInitial.uniqueUpToIso` 的定义

English:
definition IsInitial.uniqueUpToIso
  signature: {I I' : C} (hI : IsInitial I) (hI' : IsInitial I')
  body: hI.to _
  inv := hI'.to _

中文:
定义 IsInitial.uniqueUpToIso
  签名: {I I' : C} (hI : IsInitial I) (hI' : IsInitial I')
  定义体: hI.to _
  inv := hI'.to _

Depends on / 依赖: hI.to
-/
def IsInitial.uniqueUpToIso {I I' : C} (hI : IsInitial I) (hI' : IsInitial I') : I ≅ I' where
  hom := hI.to _
  inv := hI'.to _

variable (C)

section Univ

variable (X : C) {F₁ : Discrete.{w} PEmpty ⥤ C} {F₂ : Discrete.{w'} PEmpty ⥤ C}

/--
Definition of `isLimitChangeEmptyCone` / `isLimitChangeEmptyCone` 的定义

English:
definition isLimitChangeEmptyCone
  signature: {c₁ : Cone F₁} (hl : IsLimit c₁) (c₂ : Cone F₂) (hi : c₁.pt ≅ c₂.pt)
  body: hl.lift ⟨c.pt, by cat_disch, by simp⟩ ≫ hi.hom
  uniq c f _ := by
    dsimp
    rw [← hl.uniq _ (f ≫ hi.inv) _]
    · simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    · simp

中文:
定义 isLimitChangeEmptyCone
  签名: {c₁ : Cone F₁} (hl : IsLimit c₁) (c₂ : Cone F₂) (hi : c₁.pt ≅ c₂.pt)
  定义体: hl.lift ⟨c.pt, by cat_disch, by simp⟩ ≫ hi.hom
  uniq c f _ := by
    dsimp
    rw [← hl.uniq _ (f ≫ hi.inv) _]
    · simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    · simp

Depends on / 依赖: c.pt, cat_disch, hi.hom, hl.lift
-/
def isLimitChangeEmptyCone {c₁ : Cone F₁} (hl : IsLimit c₁) (c₂ : Cone F₂) (hi : c₁.pt ≅ c₂.pt) :
    IsLimit c₂ where
  lift c := hl.lift ⟨c.pt, by cat_disch, by simp⟩ ≫ hi.hom
  uniq c f _ := by
    dsimp
    rw [← hl.uniq _ (f ≫ hi.inv) _]
    · simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    · simp

/--
Definition of `isLimitEmptyConeEquiv` / `isLimitEmptyConeEquiv` 的定义

English:
definition isLimitEmptyConeEquiv
  signature: (c₁ : Cone F₁) (c₂ : Cone F₂) (h : c₁.pt ≅ c₂.pt)
  body: isLimitChangeEmptyCone C hl c₂ h
  invFun hl := isLimitChangeEmptyCone C hl c₁ h.symm
  left_inv := by dsimp [Function.LeftInverse]; intro; simp only [eq_iff_true_of_subsingleton]
  right_inv := by
    dsimp [Function.LeftInverse, Function.RightInverse]; intro
    simp only [eq_iff_true_of_subsingle

中文:
定义 isLimitEmptyConeEquiv
  签名: (c₁ : Cone F₁) (c₂ : Cone F₂) (h : c₁.pt ≅ c₂.pt)
  定义体: isLimitChangeEmptyCone C hl c₂ h
  invFun hl := isLimitChangeEmptyCone C hl c₁ h.symm
  left_inv := by dsimp [Function.LeftInverse]; intro; simp only [eq_iff_true_of_subsingleton]
  right_inv := by
    dsimp [Function.LeftInverse, Function.RightInverse]; intro
    simp only [eq_iff_true_of_subsingle

Depends on / 依赖: isLimitChangeEmptyCone
-/
def isLimitEmptyConeEquiv (c₁ : Cone F₁) (c₂ : Cone F₂) (h : c₁.pt ≅ c₂.pt) :
    IsLimit c₁ ≃ IsLimit c₂ where
  toFun hl := isLimitChangeEmptyCone C hl c₂ h
  invFun hl := isLimitChangeEmptyCone C hl c₁ h.symm
  left_inv := by dsimp [Function.LeftInverse]; intro; simp only [eq_iff_true_of_subsingleton]
  right_inv := by
    dsimp [Function.LeftInverse, Function.RightInverse]; intro
    simp only [eq_iff_true_of_subsingleton]

/-- If `F` is an empty diagram, then a cone over `F` is limiting iff the cone point is terminal. -/
noncomputable
/--
Definition of `isLimitEquivIsTerminalOfIsEmpty` / `isLimitEquivIsTerminalOfIsEmpty` 的定义

English:
definition isLimitEquivIsTerminalOfIsEmpty
  signature: {J : Type*} [Category* J] [IsEmpty J] {F : J ⥤ C} (c : Cone F)
  body: (IsLimit.whiskerEquivalenceEquiv (equivalenceOfIsEmpty (Discrete PEmpty.{1}) _)).trans
    (isLimitEmptyConeEquiv _ _ _ (.refl _))

中文:
定义 isLimitEquivIsTerminalOfIsEmpty
  签名: {J : 类型} [Category* J] [IsEmpty J] {F : J ⥤ C} (c : Cone F)
  定义体: (IsLimit.whiskerEquivalenceEquiv (equivalenceOfIsEmpty (Discrete PEmpty.{1}) _)).trans
    (isLimitEmptyConeEquiv _ _ _ (.refl _))

Depends on / 依赖: Discrete, IsLimit, IsLimit.whiskerEquivalenceEquiv, PEmpty, equivalenceOfIsEmpty, isLimitEmptyConeEquiv, whiskerEquivalenceEquiv
-/
def isLimitEquivIsTerminalOfIsEmpty {J : Type*} [Category* J] [IsEmpty J] {F : J ⥤ C} (c : Cone F) :
    IsLimit c ≃ IsTerminal c.pt :=
  (IsLimit.whiskerEquivalenceEquiv (equivalenceOfIsEmpty (Discrete PEmpty.{1}) _)).trans
    (isLimitEmptyConeEquiv _ _ _ (.refl _))

/--
Definition of `isColimitChangeEmptyCocone` / `isColimitChangeEmptyCocone` 的定义

English:
definition isColimitChangeEmptyCocone
  signature: {c₁ : Cocone F₁} (hl : IsColimit c₁) (c₂ : Cocone F₂)
  body: hi.inv ≫ hl.desc ⟨c.pt, by cat_disch, by simp⟩
  uniq c f _ := by
    dsimp
    rw [← hl.uniq _ (hi.hom ≫ f) _]
    · simp only [Iso.inv_hom_id_assoc]
    · simp

中文:
定义 isColimitChangeEmptyCocone
  签名: {c₁ : Cocone F₁} (hl : IsColimit c₁) (c₂ : Cocone F₂)
  定义体: hi.inv ≫ hl.desc ⟨c.pt, by cat_disch, by simp⟩
  uniq c f _ := by
    dsimp
    rw [← hl.uniq _ (hi.hom ≫ f) _]
    · simp only [Iso.inv_hom_id_assoc]
    · simp

Depends on / 依赖: c.pt, cat_disch, hi.inv, hl.desc
-/
def isColimitChangeEmptyCocone {c₁ : Cocone F₁} (hl : IsColimit c₁) (c₂ : Cocone F₂)
    (hi : c₁.pt ≅ c₂.pt) : IsColimit c₂ where
  desc c := hi.inv ≫ hl.desc ⟨c.pt, by cat_disch, by simp⟩
  uniq c f _ := by
    dsimp
    rw [← hl.uniq _ (hi.hom ≫ f) _]
    · simp only [Iso.inv_hom_id_assoc]
    · simp

/--
Definition of `isColimitEmptyCoconeEquiv` / `isColimitEmptyCoconeEquiv` 的定义

English:
definition isColimitEmptyCoconeEquiv
  signature: (c₁ : Cocone F₁) (c₂ : Cocone F₂) (h : c₁.pt ≅ c₂.pt)
  body: isColimitChangeEmptyCocone C hl c₂ h
  invFun hl := isColimitChangeEmptyCocone C hl c₁ h.symm
  left_inv := by dsimp [Function.LeftInverse]; intro; simp only [eq_iff_true_of_subsingleton]
  right_inv := by
    dsimp [Function.LeftInverse, Function.RightInverse]; intro
    simp only [eq_iff_true_of_s

中文:
定义 isColimitEmptyCoconeEquiv
  签名: (c₁ : Cocone F₁) (c₂ : Cocone F₂) (h : c₁.pt ≅ c₂.pt)
  定义体: isColimitChangeEmptyCocone C hl c₂ h
  invFun hl := isColimitChangeEmptyCocone C hl c₁ h.symm
  left_inv := by dsimp [Function.LeftInverse]; intro; simp only [eq_iff_true_of_subsingleton]
  right_inv := by
    dsimp [Function.LeftInverse, Function.RightInverse]; intro
    simp only [eq_iff_true_of_s

Depends on / 依赖: isColimitChangeEmptyCocone
-/
def isColimitEmptyCoconeEquiv (c₁ : Cocone F₁) (c₂ : Cocone F₂) (h : c₁.pt ≅ c₂.pt) :
    IsColimit c₁ ≃ IsColimit c₂ where
  toFun hl := isColimitChangeEmptyCocone C hl c₂ h
  invFun hl := isColimitChangeEmptyCocone C hl c₁ h.symm
  left_inv := by dsimp [Function.LeftInverse]; intro; simp only [eq_iff_true_of_subsingleton]
  right_inv := by
    dsimp [Function.LeftInverse, Function.RightInverse]; intro
    simp only [eq_iff_true_of_subsingleton]

/-- If `F` is an empty diagram,
then a cocone over `F` is colimiting iff the cocone point is initial. -/
noncomputable
/--
Definition of `isColimitEquivIsInitialOfIsEmpty` / `isColimitEquivIsInitialOfIsEmpty` 的定义

English:
definition isColimitEquivIsInitialOfIsEmpty
  signature: {J : Type*} [Category* J] [IsEmpty J]
  body: (IsColimit.whiskerEquivalenceEquiv (equivalenceOfIsEmpty (Discrete PEmpty.{1}) _)).trans
    (isColimitEmptyCoconeEquiv _ _ _ (.refl _))

中文:
定义 isColimitEquivIsInitialOfIsEmpty
  签名: {J : 类型} [Category* J] [IsEmpty J]
  定义体: (IsColimit.whiskerEquivalenceEquiv (equivalenceOfIsEmpty (Discrete PEmpty.{1}) _)).trans
    (isColimitEmptyCoconeEquiv _ _ _ (.refl _))

Depends on / 依赖: Discrete, IsColimit, IsColimit.whiskerEquivalenceEquiv, PEmpty, equivalenceOfIsEmpty, isColimitEmptyCoconeEquiv, whiskerEquivalenceEquiv
-/
def isColimitEquivIsInitialOfIsEmpty {J : Type*} [Category* J] [IsEmpty J]
    {F : J ⥤ C} (c : Cocone F) : IsColimit c ≃ IsInitial c.pt :=
  (IsColimit.whiskerEquivalenceEquiv (equivalenceOfIsEmpty (Discrete PEmpty.{1}) _)).trans
    (isColimitEmptyCoconeEquiv _ _ _ (.refl _))

end Univ

section

variable {C}

/--
Definition of `terminalOpOfInitial` / `terminalOpOfInitial` 的定义

English:
definition terminalOpOfInitial
  signature: {X : C} (t : IsInitial X)
  body: (t.to s.pt.unop).op
  uniq _ _ _ := Quiver.Hom.unop_inj (t.hom_ext _ _)

中文:
定义 terminalOpOfInitial
  签名: {X : C} (t : IsInitial X)
  定义体: (t.to s.pt.unop).op
  uniq _ _ _ := Quiver.Hom.unop_inj (t.hom_ext _ _)

Depends on / 依赖: s.pt.unop, t.to
-/
def terminalOpOfInitial {X : C} (t : IsInitial X) : IsTerminal (Opposite.op X) where
  lift s := (t.to s.pt.unop).op
  uniq _ _ _ := Quiver.Hom.unop_inj (t.hom_ext _ _)

/--
Definition of `terminalUnopOfInitial` / `terminalUnopOfInitial` 的定义

English:
definition terminalUnopOfInitial
  signature: {X : Cᵒᵖ} (t : IsInitial X)
  body: (t.to (Opposite.op s.pt)).unop
  uniq _ _ _ := Quiver.Hom.op_inj (t.hom_ext _ _)

中文:
定义 terminalUnopOfInitial
  签名: {X : Cᵒᵖ} (t : IsInitial X)
  定义体: (t.to (Opposite.op s.pt)).unop
  uniq _ _ _ := Quiver.Hom.op_inj (t.hom_ext _ _)

Depends on / 依赖: Opposite, Opposite.op, s.pt, t.to
-/
def terminalUnopOfInitial {X : Cᵒᵖ} (t : IsInitial X) : IsTerminal X.unop where
  lift s := (t.to (Opposite.op s.pt)).unop
  uniq _ _ _ := Quiver.Hom.op_inj (t.hom_ext _ _)

/--
Definition of `initialOpOfTerminal` / `initialOpOfTerminal` 的定义

English:
definition initialOpOfTerminal
  signature: {X : C} (t : IsTerminal X)
  body: (t.from s.pt.unop).op
  uniq _ _ _ := Quiver.Hom.unop_inj (t.hom_ext _ _)

中文:
定义 initialOpOfTerminal
  签名: {X : C} (t : IsTerminal X)
  定义体: (t.from s.pt.unop).op
  uniq _ _ _ := Quiver.Hom.unop_inj (t.hom_ext _ _)

Depends on / 依赖: s.pt.unop, t.from
-/
def initialOpOfTerminal {X : C} (t : IsTerminal X) : IsInitial (Opposite.op X) where
  desc s := (t.from s.pt.unop).op
  uniq _ _ _ := Quiver.Hom.unop_inj (t.hom_ext _ _)

/--
Definition of `initialUnopOfTerminal` / `initialUnopOfTerminal` 的定义

English:
definition initialUnopOfTerminal
  signature: {X : Cᵒᵖ} (t : IsTerminal X)
  body: (t.from (Opposite.op s.pt)).unop
  uniq _ _ _ := Quiver.Hom.op_inj (t.hom_ext _ _)

中文:
定义 initialUnopOfTerminal
  签名: {X : Cᵒᵖ} (t : IsTerminal X)
  定义体: (t.from (Opposite.op s.pt)).unop
  uniq _ _ _ := Quiver.Hom.op_inj (t.hom_ext _ _)

Depends on / 依赖: Opposite, Opposite.op, s.pt, t.from
-/
def initialUnopOfTerminal {X : Cᵒᵖ} (t : IsTerminal X) : IsInitial X.unop where
  desc s := (t.from (Opposite.op s.pt)).unop
  uniq _ _ _ := Quiver.Hom.op_inj (t.hom_ext _ _)

/--
Definition of `InitialMonoClass` / `InitialMonoClass` 的定义

English:
class InitialMonoClass
  parameters: (C : Type u₁) [Category.{v₁} C]
  axioms and operations (1):
    - isInitial_mono_from : forall {I} (X : C) (hI : IsInitial I), Mono (hI.to X)

中文:
类 InitialMonoClass
  参数: (C : 类型u₁) [Category.{v₁} C]
  公理与运算 (1 个):
    - isInitial_mono_from : 对任意 {I} (X : C) (hI : IsInitial I), Mono (hI.to X)
-/
class InitialMonoClass (C : Type u₁) [Category.{v₁} C] : Prop where
  /-- The map from the (any as stated) initial object to any other object is a
    monomorphism -/
  isInitial_mono_from : forall {I} (X : C) (hI : IsInitial I), Mono (hI.to X)

/--
theorem `IsInitial.mono_from` / 定理 `IsInitial.mono_from`

English:
theorem IsInitial.mono_from
  given: [InitialMonoClass C] {I} {X : C} (hI : IsInitial I) (f : I ⟶ X)
  proof: by
  rw [hI.hom_ext f (hI.to X)]
  apply InitialMonoClass.isInitial_mono_from

中文:
定理 IsInitial.mono_from
  条件: [InitialMonoClass C] {I} {X : C} (hI : IsInitial I) (f : I ⟶ X)
  证明: by
  rw [hI.hom_ext f (hI.to X)]
  apply InitialMonoClass.isInitial_mono_from

Depends on / 依赖: InitialMonoClass, InitialMonoClass.isInitial_mono_from, fun_, hI.hom_ext, hI.to, hom_ext, isInitial_mono_from, toUnit_unique
-/
theorem IsInitial.mono_from [InitialMonoClass C] {I} {X : C} (hI : IsInitial I) (f : I ⟶ X) :
    Mono f := by
  rw [hI.hom_ext f (hI.to X)]
  apply InitialMonoClass.isInitial_mono_from

/--
theorem `InitialMonoClass.of_isInitial` / 定理 `InitialMonoClass.of_isInitial`

English:
theorem InitialMonoClass.of_isInitial
  given: {I : C} (hI : IsInitial I) (h : forall X, Mono (hI.to X))
  proof: by
    rw [hI'.hom_ext (hI'.to X) ((hI'.uniqueUpToIso hI).hom ≫ hI.to X)]
    apply mono_comp

中文:
定理 InitialMonoClass.of_isInitial
  条件: {I : C} (hI : IsInitial I) (h : 对任意 X, Mono (hI.to X))
  证明: by
    rw [hI'.hom_ext (hI'.to X) ((hI'.uniqueUpToIso hI).hom ≫ hI.to X)]
    apply mono_comp

Depends on / 依赖: IsTerminal, Limits, Limits.IsTerminal.mono_from, hI.to, hom_ext, isTerminalTensorUnit, mono_comp, mono_from, uniqueUpToIso
-/
theorem InitialMonoClass.of_isInitial {I : C} (hI : IsInitial I) (h : forall X, Mono (hI.to X)) :
    InitialMonoClass C where
  isInitial_mono_from {I'} X hI' := by
    rw [hI'.hom_ext (hI'.to X) ((hI'.uniqueUpToIso hI).hom ≫ hI.to X)]
    apply mono_comp

/--
theorem `InitialMonoClass.of_isTerminal` / 定理 `InitialMonoClass.of_isTerminal`

English:
theorem InitialMonoClass.of_isTerminal
  statement: {I T : C} (hI : IsInitial I) (hT : IsTerminal T)
  proof: InitialMonoClass.of_isInitial hI fun X => mono_of_mono_fac (hI.hom_ext (_ ≫ hT.from X) (hI.to T))

中文:
定理 InitialMonoClass.of_isTerminal
  结论: {I T : C} (hI : IsInitial I) (hT : IsTerminal T)
  证明: InitialMonoClass.of_isInitial hI fun X => mono_of_mono_fac (hI.hom_ext (_ ≫ hT.from X) (hI.to T))

Depends on / 依赖: InitialMonoClass, InitialMonoClass.of_isInitial, hI.hom_ext, hI.to, hT.from, hom_ext, mono_of_mono_fac, of_isInitial
-/
theorem InitialMonoClass.of_isTerminal {I T : C} (hI : IsInitial I) (hT : IsTerminal T)
    (_ : Mono (hI.to T)) : InitialMonoClass C :=
  InitialMonoClass.of_isInitial hI fun X => mono_of_mono_fac (hI.hom_ext (_ ≫ hT.from X) (hI.to T))

variable {J : Type u} [Category.{v} J]

/-- From a functor `F : J ⥤ C`, given an initial object of `J`, construct a cone for `J`.
In `limitOfDiagramInitial` we show it is a limit cone. -/
@[implicit_reducible, simps]
/--
Definition of `coneOfDiagramInitial` / `coneOfDiagramInitial` 的定义

English:
definition coneOfDiagramInitial
  signature: {X : J} (tX : IsInitial X) (F : J ⥤ C)
  body: F.obj X
  π :=
    { app := fun j => F.map (tX.to j)
      naturality := fun j j' k => by
        dsimp
        rw [← F.map_comp]; rw [Category.id_comp]; rw [tX.hom_ext (tX.to j ≫ k) (tX.to j')] }

中文:
定义 coneOfDiagramInitial
  签名: {X : J} (tX : IsInitial X) (F : J ⥤ C)
  定义体: F.obj X
  π :=
    { app := fun j => F.map (tX.to j)
      naturality := fun j j' k => by
        dsimp
        rw [← F.map_comp]; rw [Category.id_comp]; rw [tX.hom_ext (tX.to j ≫ k) (tX.to j')] }

Depends on / 依赖: F.obj
-/
def coneOfDiagramInitial {X : J} (tX : IsInitial X) (F : J ⥤ C) : Cone F where
  pt := F.obj X
  π :=
    { app := fun j => F.map (tX.to j)
      naturality := fun j j' k => by
        dsimp
        rw [← F.map_comp]; rw [Category.id_comp]; rw [tX.hom_ext (tX.to j ≫ k) (tX.to j')] }

/--
Definition of `limitOfDiagramInitial` / `limitOfDiagramInitial` 的定义

English:
definition limitOfDiagramInitial
  signature: {X : J} (tX : IsInitial X) (F : J ⥤ C)
  body: s.π.app X
  uniq s m w := by
    simp_rw [← w X, coneOfDiagramInitial_π_app, tX.hom_ext (tX.to X) (𝟙 _)]
    simp

中文:
定义 limitOfDiagramInitial
  签名: {X : J} (tX : IsInitial X) (F : J ⥤ C)
  定义体: s.π.app X
  uniq s m w := by
    simp_rw [← w X, coneOfDiagramInitial_π_app, tX.hom_ext (tX.to X) (𝟙 _)]
    simp
-/
def limitOfDiagramInitial {X : J} (tX : IsInitial X) (F : J ⥤ C) :
    IsLimit (coneOfDiagramInitial tX F) where
  lift s := s.π.app X
  uniq s m w := by
    simp_rw [← w X, coneOfDiagramInitial_π_app, tX.hom_ext (tX.to X) (𝟙 _)]
    simp

/-- From a functor `F : J ⥤ C`, given a terminal object of `J`, construct a cone for `J`,
provided that the morphisms in the diagram are isomorphisms.
In `limitOfDiagramTerminal` we show it is a limit cone. -/
@[implicit_reducible, simps]
/--
Definition of `coneOfDiagramTerminal` / `coneOfDiagramTerminal` 的定义

English:
definition coneOfDiagramTerminal
  signature: {X : J} (hX : IsTerminal X) (F : J ⥤ C)
  body: F.obj X
  π :=
    { app := fun _ => inv (F.map (hX.from _))
      naturality := by
        intro i j f
        dsimp
        simp only [IsIso.eq_inv_comp, IsIso.comp_inv_eq, Category.id_comp, ← F.map_comp,
          hX.hom_ext (hX.from i) (f ≫ hX.from j)] }

中文:
定义 coneOfDiagramTerminal
  签名: {X : J} (hX : IsTerminal X) (F : J ⥤ C)
  定义体: F.obj X
  π :=
    { app := fun _ => inv (F.map (hX.from _))
      naturality := by
        intro i j f
        dsimp
        simp only [IsIso.eq_inv_comp, IsIso.comp_inv_eq, Category.id_comp, ← F.map_comp,
          hX.hom_ext (hX.from i) (f ≫ hX.from j)] }

Depends on / 依赖: F.obj, toUnit
-/
def coneOfDiagramTerminal {X : J} (hX : IsTerminal X) (F : J ⥤ C)
    [forall (i j : J) (f : i ⟶ j), IsIso (F.map f)] : Cone F where
  pt := F.obj X
  π :=
    { app := fun _ => inv (F.map (hX.from _))
      naturality := by
        intro i j f
        dsimp
        simp only [IsIso.eq_inv_comp, IsIso.comp_inv_eq, Category.id_comp, ← F.map_comp,
          hX.hom_ext (hX.from i) (f ≫ hX.from j)] }

/--
Definition of `limitOfDiagramTerminal` / `limitOfDiagramTerminal` 的定义

English:
definition limitOfDiagramTerminal
  signature: {X : J} (hX : IsTerminal X) (F : J ⥤ C)
  body: S.π.app _

中文:
定义 limitOfDiagramTerminal
  签名: {X : J} (hX : IsTerminal X) (F : J ⥤ C)
  定义体: S.π.app _
-/
def limitOfDiagramTerminal {X : J} (hX : IsTerminal X) (F : J ⥤ C)
    [forall (i j : J) (f : i ⟶ j), IsIso (F.map f)] : IsLimit (coneOfDiagramTerminal hX F) where
  lift S := S.π.app _

/-- From a functor `F : J ⥤ C`, given a terminal object of `J`, construct a cocone for `J`.
In `colimitOfDiagramTerminal` we show it is a colimit cocone. -/
@[implicit_reducible, simps]
/--
Definition of `coconeOfDiagramTerminal` / `coconeOfDiagramTerminal` 的定义

English:
definition coconeOfDiagramTerminal
  signature: {X : J} (tX : IsTerminal X) (F : J ⥤ C)
  body: F.obj X
  ι :=
    { app := fun j => F.map (tX.from j)
      naturality := fun j j' k => by
        dsimp
        rw [← F.map_comp]; rw [Category.comp_id]; rw [tX.hom_ext (k ≫ tX.from j') (tX.from j)] }

中文:
定义 coconeOfDiagramTerminal
  签名: {X : J} (tX : IsTerminal X) (F : J ⥤ C)
  定义体: F.obj X
  ι :=
    { app := fun j => F.map (tX.from j)
      naturality := fun j j' k => by
        dsimp
        rw [← F.map_comp]; rw [Category.comp_id]; rw [tX.hom_ext (k ≫ tX.from j') (tX.from j)] }

Depends on / 依赖: F.obj
-/
def coconeOfDiagramTerminal {X : J} (tX : IsTerminal X) (F : J ⥤ C) : Cocone F where
  pt := F.obj X
  ι :=
    { app := fun j => F.map (tX.from j)
      naturality := fun j j' k => by
        dsimp
        rw [← F.map_comp]; rw [Category.comp_id]; rw [tX.hom_ext (k ≫ tX.from j') (tX.from j)] }

/--
Definition of `colimitOfDiagramTerminal` / `colimitOfDiagramTerminal` 的定义

English:
definition colimitOfDiagramTerminal
  signature: {X : J} (tX : IsTerminal X) (F : J ⥤ C)
  body: s.ι.app X
  uniq s m w := by simp [← w X]

中文:
定义 colimitOfDiagramTerminal
  签名: {X : J} (tX : IsTerminal X) (F : J ⥤ C)
  定义体: s.ι.app X
  uniq s m w := by simp [← w X]
-/
def colimitOfDiagramTerminal {X : J} (tX : IsTerminal X) (F : J ⥤ C) :
    IsColimit (coconeOfDiagramTerminal tX F) where
  desc s := s.ι.app X
  uniq s m w := by simp [← w X]

/--
lemma `IsColimit.isIso_ι_app_of_isTerminal` / 引理 `IsColimit.isIso_ι_app_of_isTerminal`

English:
lemma IsColimit.isIso_ι_app_of_isTerminal
  statement: {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c)
  proof: by
  change IsIso (coconePointUniqueUpToIso (colimitOfDiagramTerminal hX F) hc).hom
  infer_instance

中文:
引理 IsColimit.isIso_ι_app_of_isTerminal
  结论: {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c)
  证明: by
  change IsIso (coconePointUniqueUpToIso (colimitOfDiagramTerminal hX F) hc).hom
  infer_instance

Depends on / 依赖: coconePointUniqueUpToIso, colimitOfDiagramTerminal, infer_instance
-/
lemma IsColimit.isIso_ι_app_of_isTerminal {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c)
    (X : J) (hX : IsTerminal X) :
    IsIso (c.ι.app X) := by
  change IsIso (coconePointUniqueUpToIso (colimitOfDiagramTerminal hX F) hc).hom
  infer_instance

/-- From a functor `F : J ⥤ C`, given an initial object of `J`, construct a cocone for `J`,
provided that the morphisms in the diagram are isomorphisms.
In `colimitOfDiagramInitial` we show it is a colimit cocone. -/
@[implicit_reducible, simps]
/--
Definition of `coconeOfDiagramInitial` / `coconeOfDiagramInitial` 的定义

English:
definition coconeOfDiagramInitial
  signature: {X : J} (hX : IsInitial X) (F : J ⥤ C)
  body: F.obj X
  ι :=
    { app := fun _ => inv (F.map (hX.to _))
      naturality := by
        intro i j f
        dsimp
        simp only [IsIso.eq_inv_comp, IsIso.comp_inv_eq, Category.comp_id, ← F.map_comp,
          hX.hom_ext (hX.to i ≫ f) (hX.to j)] }

中文:
定义 coconeOfDiagramInitial
  签名: {X : J} (hX : IsInitial X) (F : J ⥤ C)
  定义体: F.obj X
  ι :=
    { app := fun _ => inv (F.map (hX.to _))
      naturality := by
        intro i j f
        dsimp
        simp only [IsIso.eq_inv_comp, IsIso.comp_inv_eq, Category.comp_id, ← F.map_comp,
          hX.hom_ext (hX.to i ≫ f) (hX.to j)] }

Depends on / 依赖: F.obj
-/
def coconeOfDiagramInitial {X : J} (hX : IsInitial X) (F : J ⥤ C)
    [forall (i j : J) (f : i ⟶ j), IsIso (F.map f)] : Cocone F where
  pt := F.obj X
  ι :=
    { app := fun _ => inv (F.map (hX.to _))
      naturality := by
        intro i j f
        dsimp
        simp only [IsIso.eq_inv_comp, IsIso.comp_inv_eq, Category.comp_id, ← F.map_comp,
          hX.hom_ext (hX.to i ≫ f) (hX.to j)] }

/--
Definition of `colimitOfDiagramInitial` / `colimitOfDiagramInitial` 的定义

English:
definition colimitOfDiagramInitial
  signature: {X : J} (hX : IsInitial X) (F : J ⥤ C)
  body: S.ι.app _

中文:
定义 colimitOfDiagramInitial
  签名: {X : J} (hX : IsInitial X) (F : J ⥤ C)
  定义体: S.ι.app _
-/
def colimitOfDiagramInitial {X : J} (hX : IsInitial X) (F : J ⥤ C)
    [forall (i j : J) (f : i ⟶ j), IsIso (F.map f)] : IsColimit (coconeOfDiagramInitial hX F) where
  desc S := S.ι.app _

/--
lemma `IsLimit.isIso_π_app_of_isInitial` / 引理 `IsLimit.isIso_π_app_of_isInitial`

English:
lemma IsLimit.isIso_π_app_of_isInitial
  statement: {F : J ⥤ C} {c : Cone F} (hc : IsLimit c)
  proof: by
  change IsIso (conePointUniqueUpToIso hc (limitOfDiagramInitial hX F)).hom
  infer_instance

中文:
引理 IsLimit.isIso_π_app_of_isInitial
  结论: {F : J ⥤ C} {c : Cone F} (hc : IsLimit c)
  证明: by
  change IsIso (conePointUniqueUpToIso hc (limitOfDiagramInitial hX F)).hom
  infer_instance

Depends on / 依赖: conePointUniqueUpToIso, infer_instance, limitOfDiagramInitial
-/
lemma IsLimit.isIso_π_app_of_isInitial {F : J ⥤ C} {c : Cone F} (hc : IsLimit c)
    (X : J) (hX : IsInitial X) :
    IsIso (c.π.app X) := by
  change IsIso (conePointUniqueUpToIso hc (limitOfDiagramInitial hX F)).hom
  infer_instance

/--
lemma `isIso_of_isTerminal` / 引理 `isIso_of_isTerminal`

English:
lemma isIso_of_isTerminal
  given: {X Y : C} (hX : IsTerminal X) (hY : IsTerminal Y) (f : X ⟶ Y)
  proof: by
  refine ⟨⟨IsTerminal.from hX Y, ?_⟩⟩
  simp only [IsTerminal.comp_from, IsTerminal.from_self, true_and]
  apply IsTerminal.hom_ext hY

中文:
引理 isIso_of_isTerminal
  条件: {X Y : C} (hX : IsTerminal X) (hY : IsTerminal Y) (f : X ⟶ Y)
  证明: by
  refine ⟨⟨IsTerminal.from hX Y, ?_⟩⟩
  simp only [IsTerminal.comp_from, IsTerminal.from_self, true_and]
  apply IsTerminal.hom_ext hY

Depends on / 依赖: IsTerminal, IsTerminal.comp_from, IsTerminal.from, IsTerminal.from_self, IsTerminal.hom_ext, comp_from, from_self, hom_ext, true_and
-/
lemma isIso_of_isTerminal {X Y : C} (hX : IsTerminal X) (hY : IsTerminal Y) (f : X ⟶ Y) :
    IsIso f := by
  refine ⟨⟨IsTerminal.from hX Y, ?_⟩⟩
  simp only [IsTerminal.comp_from, IsTerminal.from_self, true_and]
  apply IsTerminal.hom_ext hY

/--
lemma `isIso_of_isInitial` / 引理 `isIso_of_isInitial`

English:
lemma isIso_of_isInitial
  given: {X Y : C} (hX : IsInitial X) (hY : IsInitial Y) (f : X ⟶ Y)
  proof: by
  refine ⟨⟨IsInitial.to hY X, ?_⟩⟩
  simp only [IsInitial.to_comp, IsInitial.to_self, and_true]
  apply IsInitial.hom_ext hX

中文:
引理 isIso_of_isInitial
  条件: {X Y : C} (hX : IsInitial X) (hY : IsInitial Y) (f : X ⟶ Y)
  证明: by
  refine ⟨⟨IsInitial.to hY X, ?_⟩⟩
  simp only [IsInitial.to_comp, IsInitial.to_self, and_true]
  apply IsInitial.hom_ext hX

Depends on / 依赖: IsInitial, IsInitial.hom_ext, IsInitial.to, IsInitial.to_comp, IsInitial.to_self, and_true, hom_ext, to_comp, to_self
-/
lemma isIso_of_isInitial {X Y : C} (hX : IsInitial X) (hY : IsInitial Y) (f : X ⟶ Y) :
    IsIso f := by
  refine ⟨⟨IsInitial.to hY X, ?_⟩⟩
  simp only [IsInitial.to_comp, IsInitial.to_self, and_true]
  apply IsInitial.hom_ext hX

end

/--
Definition of `IsInitial.op` / `IsInitial.op` 的定义

English:
definition IsInitial.op
  signature: {X : C} (hX : IsInitial X)
  body: IsTerminal.ofUniqueHom (fun _ => (hX.to _).op)
    (fun _ _ => Quiver.Hom.unop_inj (hX.hom_ext _ _))

中文:
定义 IsInitial.op
  签名: {X : C} (hX : IsInitial X)
  定义体: IsTerminal.ofUniqueHom (fun _ => (hX.to _).op)
    (fun _ _ => Quiver.Hom.unop_inj (hX.hom_ext _ _))

Depends on / 依赖: IsTerminal, IsTerminal.ofUniqueHom, Quiver, Quiver.Hom.unop_inj, hX.hom_ext, hX.to, hom_ext, ofUniqueHom, unop_inj
-/
def IsInitial.op {X : C} (hX : IsInitial X) : IsTerminal (op X) :=
  IsTerminal.ofUniqueHom (fun _ => (hX.to _).op)
    (fun _ _ => Quiver.Hom.unop_inj (hX.hom_ext _ _))

/--
Definition of `IsInitial.unop` / `IsInitial.unop` 的定义

English:
definition IsInitial.unop
  signature: {X : Cᵒᵖ} (hX : IsInitial X)
  body: IsTerminal.ofUniqueHom (fun _ => (hX.to _).unop)
    (fun _ _ => Quiver.Hom.op_inj (hX.hom_ext _ _))

中文:
定义 IsInitial.unop
  签名: {X : Cᵒᵖ} (hX : IsInitial X)
  定义体: IsTerminal.ofUniqueHom (fun _ => (hX.to _).unop)
    (fun _ _ => Quiver.Hom.op_inj (hX.hom_ext _ _))

Depends on / 依赖: IsTerminal, IsTerminal.ofUniqueHom, Quiver, Quiver.Hom.op_inj, hX.hom_ext, hX.to, hom_ext, ofUniqueHom, op_inj
-/
def IsInitial.unop {X : Cᵒᵖ} (hX : IsInitial X) : IsTerminal X.unop :=
  IsTerminal.ofUniqueHom (fun _ => (hX.to _).unop)
    (fun _ _ => Quiver.Hom.op_inj (hX.hom_ext _ _))

/--
Definition of `IsTerminal.op` / `IsTerminal.op` 的定义

English:
definition IsTerminal.op
  signature: {X : C} (hX : IsTerminal X)
  body: IsInitial.ofUniqueHom (fun _ => (hX.from _).op)
    (fun _ _ => Quiver.Hom.unop_inj (hX.hom_ext _ _))

中文:
定义 IsTerminal.op
  签名: {X : C} (hX : IsTerminal X)
  定义体: IsInitial.ofUniqueHom (fun _ => (hX.from _).op)
    (fun _ _ => Quiver.Hom.unop_inj (hX.hom_ext _ _))

Depends on / 依赖: IsInitial, IsInitial.ofUniqueHom, Quiver, Quiver.Hom.unop_inj, hX.from, hX.hom_ext, hom_ext, ofUniqueHom, unop_inj
-/
def IsTerminal.op {X : C} (hX : IsTerminal X) : IsInitial (op X) :=
  IsInitial.ofUniqueHom (fun _ => (hX.from _).op)
    (fun _ _ => Quiver.Hom.unop_inj (hX.hom_ext _ _))

/--
Definition of `IsTerminal.unop` / `IsTerminal.unop` 的定义

English:
definition IsTerminal.unop
  signature: {X : Cᵒᵖ} (hX : IsTerminal X)
  body: IsInitial.ofUniqueHom (fun _ => (hX.from _).unop)
    (fun _ _ => Quiver.Hom.op_inj (hX.hom_ext _ _))

中文:
定义 IsTerminal.unop
  签名: {X : Cᵒᵖ} (hX : IsTerminal X)
  定义体: IsInitial.ofUniqueHom (fun _ => (hX.from _).unop)
    (fun _ _ => Quiver.Hom.op_inj (hX.hom_ext _ _))

Depends on / 依赖: IsInitial, IsInitial.ofUniqueHom, Quiver, Quiver.Hom.op_inj, hX.from, hX.hom_ext, hom_ext, ofUniqueHom, op_inj
-/
def IsTerminal.unop {X : Cᵒᵖ} (hX : IsTerminal X) : IsInitial X.unop :=
  IsInitial.ofUniqueHom (fun _ => (hX.from _).unop)
    (fun _ _ => Quiver.Hom.op_inj (hX.hom_ext _ _))

end Limits

namespace Functor
open Limits
variable (C : Type*) [Category* C] {D : Type*} [Category* D]

/--
Definition of `isTerminalConst` / `isTerminalConst` 的定义

English:
definition isTerminalConst
  signature: {X : D} (hX : IsTerminal X)
  body: .ofUniqueHom (fun Y => { app Z := hX.from (Y.obj Z) }) (by intros; ext; apply hX.hom_ext)

@[simp]

中文:
定义 isTerminalConst
  签名: {X : D} (hX : IsTerminal X)
  定义体: .ofUniqueHom (fun Y => { app Z := hX.from (Y.obj Z) }) (by intros; ext; apply hX.hom_ext)

@[simp]

Depends on / 依赖: Y.obj, hX.from, hX.hom_ext, hom_ext, intros, ofUniqueHom
-/
def isTerminalConst {X : D} (hX : IsTerminal X) :
    IsTerminal ((Functor.const C).obj X) :=
  .ofUniqueHom (fun Y => { app Z := hX.from (Y.obj Z) }) (by intros; ext; apply hX.hom_ext)

@[simp]
/--
lemma `isTerminalConst_from_app` / 引理 `isTerminalConst_from_app`

English:
lemma isTerminalConst_from_app
  statement: {X : D} (hX : IsTerminal X)
  proof: rfl

中文:
引理 isTerminalConst_from_app
  结论: {X : D} (hX : IsTerminal X)
  证明: rfl
-/
lemma isTerminalConst_from_app {X : D} (hX : IsTerminal X)
    (F : C ⥤ D) (Y : C) : ((isTerminalConst C hX).from F).app Y = hX.from (F.obj Y) := rfl

/--
Definition of `isInitialConst` / `isInitialConst` 的定义

English:
definition isInitialConst
  signature: {X : D} (hX : IsInitial X)
  body: .ofUniqueHom (fun Y => { app Z := hX.to (Y.obj Z) }) (by intros; ext; apply hX.hom_ext)

@[simp]

中文:
定义 isInitialConst
  签名: {X : D} (hX : IsInitial X)
  定义体: .ofUniqueHom (fun Y => { app Z := hX.to (Y.obj Z) }) (by intros; ext; apply hX.hom_ext)

@[simp]

Depends on / 依赖: Y.obj, hX.hom_ext, hX.to, hom_ext, intros, ofUniqueHom
-/
def isInitialConst {X : D} (hX : IsInitial X) :
    IsInitial ((Functor.const C).obj X) :=
  .ofUniqueHom (fun Y => { app Z := hX.to (Y.obj Z) }) (by intros; ext; apply hX.hom_ext)

@[simp]
/--
lemma `isInitialConst_to_app` / 引理 `isInitialConst_to_app`

English:
lemma isInitialConst_to_app
  statement: {X : D} (hX : IsInitial X)
  proof: rfl

中文:
引理 isInitialConst_to_app
  结论: {X : D} (hX : IsInitial X)
  证明: rfl
-/
lemma isInitialConst_to_app {X : D} (hX : IsInitial X)
    (F : C ⥤ D) (Y : C) : ((isInitialConst C hX).to F).app Y = hX.to (F.obj Y) := rfl

end Functor

end CategoryTheory
