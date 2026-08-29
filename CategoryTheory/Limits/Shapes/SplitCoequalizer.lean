/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Split coequalizers

We define what it means for a triple of morphisms `f g : X ⟶ Y`, `π : Y ⟶ Z` to be a split
coequalizer: there is a section `s` of `π` and a section `t` of `g`, which additionally satisfy
`t ≫ f = π ≫ s`.

In addition, we show that every split coequalizer is a coequalizer
(`CategoryTheory.IsSplitCoequalizer.isCoequalizer`) and absolute
(`CategoryTheory.IsSplitCoequalizer.map`)

A pair `f g : X ⟶ Y` has a split coequalizer if there is a `Z` and `π : Y ⟶ Z` making `f,g,π` a
split coequalizer.
A pair `f g : X ⟶ Y` has a `G`-split coequalizer if `G f, G g` has a split coequalizer.

These definitions and constructions are useful in particular for the monadicity theorems.

This file has been adapted to `Mathlib/CategoryTheory/Limits/Shapes/SplitEqualizer.lean`. Please try
to keep them in sync.

-/

@[expose] public section


namespace CategoryTheory

universe v v₂ u u₂

variable {C : Type u} [Category.{v} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (G : C ⥤ D)
variable {X Y : C} (f g : X ⟶ Y)

/--
Definition of `IsSplitCoequalizer` / `IsSplitCoequalizer` 的定义

English:
structure IsSplitCoequalizer
  parameters: {Z : C} (π : Y ⟶ Z)
  axioms and operations (6):
    - rightSection : Z ⟶ Y
    - leftSection : Y ⟶ X
    - condition : f ≫ π = g ≫ π  [default: by cat_disch]
    - rightSection_π : rightSection ≫ π = 𝟙 Z  [default: by cat_disch]
    - leftSection_bottom : leftSection ≫ g = 𝟙 Y  [default: by cat_disch]
    - leftSection_top : leftSection ≫ f = π ≫ rightSection  [default: by cat_disch]

中文:
结构 是SplitCoequalizer
  参数: {Z : C} (π : Y ⟶ Z)
  公理与运算 (6 个):
    - rightSection : Z ⟶ Y
    - leftSection : Y ⟶ X
    - condition : f ≫ π = g ≫ π  [默认: by cat_disch]
    - rightSection_π : rightSection ≫ π = 𝟙 Z  [默认: by cat_disch]
    - leftSection_bottom : leftSection ≫ g = 𝟙 Y  [默认: by cat_disch]
    - leftSection_top : leftSection ≫ f = π ≫ rightSection  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure IsSplitCoequalizer {Z : C} (π : Y ⟶ Z) where
  /-- A map from the coequalizer to `Y` -/
  rightSection : Z ⟶ Y
  /-- A map in the opposite direction to `f` and `g` -/
  leftSection : Y ⟶ X
  /-- Composition of `π` with `f` and with `g` agree -/
  condition : f ≫ π = g ≫ π := by cat_disch
  /-- `rightSection` splits `π` -/
  rightSection_π : rightSection ≫ π = 𝟙 Z := by cat_disch
  /-- `leftSection` splits `g` -/
  leftSection_bottom : leftSection ≫ g = 𝟙 Y := by cat_disch
  /-- `leftSection` composed with `f` is `pi` composed with `rightSection` -/
  leftSection_top : leftSection ≫ f = π ≫ rightSection := by cat_disch

instance {X : C} : Inhabited (IsSplitCoequalizer (𝟙 X) (𝟙 X) (𝟙 X)) where
  default := { rightSection := 𝟙 X, leftSection := 𝟙 X }

open IsSplitCoequalizer

attribute [reassoc] condition

attribute [reassoc (attr := simp)] rightSection_π leftSection_bottom leftSection_top

variable {f g}

/-- Split coequalizers are absolute: they are preserved by any functor. -/
@[simps]
/--
Definition of `IsSplitCoequalizer.map` / `IsSplitCoequalizer.map` 的定义

English:
definition IsSplitCoequalizer.map
  signature: {Z : C} {π : Y ⟶ Z} (q : IsSplitCoequalizer f g π) (F : C ⥤ D)
  body: F.map q.rightSection
  leftSection := F.map q.leftSection
  condition := by rw [← F.map_comp, q.condition, F.map_comp]
  rightSection_π := by rw [← F.map_comp, q.rightSection_π, F.map_id]
  leftSection_bottom := by rw [← F.map_comp, q.leftSection_bottom, F.map_id]
  leftSection_top := by rw [← F.map_comp, q.leftSection_top, F.map_comp]

中文:
定义 是SplitCoequalizer.map
  签名: {Z : C} {π : Y ⟶ Z} (q : 是SplitCoequalizer f g π) (F : C ⥤ D)
  定义体: F.map q.rightSection
  leftSection := F.map q.leftSection
  condition := by rw [← F.map_comp, q.condition, F.map_comp]
  rightSection_π := by rw [← F.map_comp, q.rightSection_π, F.map_id]
  leftSection_bottom := by rw [← F.map_comp, q.leftSection_bottom, F.map_id]
  leftSection_top := by rw [← F.map_comp, q.leftSection_top, F.map_comp]

Depends on / 依赖: F.map, q.rightSection, rightSection
-/
def IsSplitCoequalizer.map {Z : C} {π : Y ⟶ Z} (q : IsSplitCoequalizer f g π) (F : C ⥤ D) :
    IsSplitCoequalizer (F.map f) (F.map g) (F.map π) where
  rightSection := F.map q.rightSection
  leftSection := F.map q.leftSection
  condition := by rw [← F.map_comp, q.condition, F.map_comp]
  rightSection_π := by rw [← F.map_comp, q.rightSection_π, F.map_id]
  leftSection_bottom := by rw [← F.map_comp, q.leftSection_bottom, F.map_id]
  leftSection_top := by rw [← F.map_comp, q.leftSection_top, F.map_comp]

section

open Limits

/-- A split coequalizer clearly induces a cofork. -/
@[simps! pt]
/--
Definition of `IsSplitCoequalizer.asCofork` / `IsSplitCoequalizer.asCofork` 的定义

English:
definition IsSplitCoequalizer.asCofork
  signature: {Z : C} {h : Y ⟶ Z} (t : IsSplitCoequalizer f g h)
  body: Cofork.ofπ h t.condition

@[simp]

中文:
定义 是SplitCoequalizer.asCofork
  签名: {Z : C} {h : Y ⟶ Z} (t : 是SplitCoequalizer f g h)
  定义体: Cofork.ofπ h t.condition

@[simp]

Depends on / 依赖: Cofork, Cofork.of, condition, t.condition
-/
def IsSplitCoequalizer.asCofork {Z : C} {h : Y ⟶ Z} (t : IsSplitCoequalizer f g h) :
    Cofork f g := Cofork.ofπ h t.condition

@[simp]
/--
theorem `IsSplitCoequalizer.asCofork_π` / 定理 `IsSplitCoequalizer.asCofork_π`

English:
theorem IsSplitCoequalizer.asCofork_π
  given: {Z : C} {h : Y ⟶ Z} (t : IsSplitCoequalizer f g h)
  proof: rfl

中文:
定理 是SplitCoequalizer.asCofork_π
  条件: {Z : C} {h : Y ⟶ Z} (t : 是SplitCoequalizer f g h)
  证明: rfl
-/
theorem IsSplitCoequalizer.asCofork_π {Z : C} {h : Y ⟶ Z} (t : IsSplitCoequalizer f g h) :
    t.asCofork.π = h := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `IsSplitCoequalizer.isCoequalizer` / `IsSplitCoequalizer.isCoequalizer` 的定义

English:
definition IsSplitCoequalizer.isCoequalizer
  signature: {Z : C} {h : Y ⟶ Z} (t : IsSplitCoequalizer f g h)
  body: Cofork.IsColimit.mk' _ fun s =>
    ⟨t.rightSection ≫ s.π, by
      dsimp
      rw [← t.leftSection_top_assoc]; rw [s.condition]; rw [t.leftSection_bottom_assoc], fun hm => by
      simp [← hm]⟩

中文:
定义 是SplitCoequalizer.isCoequalizer
  签名: {Z : C} {h : Y ⟶ Z} (t : 是SplitCoequalizer f g h)
  定义体: Cofork.IsColimit.mk' _ fun s =>
    ⟨t.rightSection ≫ s.π, by
      dsimp
      rw [← t.leftSection_top_assoc]; rw [s.condition]; rw [t.leftSection_bottom_assoc], fun hm => by
      simp [← hm]⟩

Depends on / 依赖: Cofork, Cofork.IsColimit.mk, IsColimit, condition, leftSection_bottom_assoc, leftSection_top_assoc, rightSection, s.condition, t.leftSection_bottom_assoc, t.leftSection_top_assoc, t.rightSection
-/
def IsSplitCoequalizer.isCoequalizer {Z : C} {h : Y ⟶ Z} (t : IsSplitCoequalizer f g h) :
    IsColimit t.asCofork :=
  Cofork.IsColimit.mk' _ fun s =>
    ⟨t.rightSection ≫ s.π, by
      dsimp
      rw [← t.leftSection_top_assoc]; rw [s.condition]; rw [t.leftSection_bottom_assoc], fun hm => by
      simp [← hm]⟩

end

variable (f g)

/--
Definition of `HasSplitCoequalizer` / `HasSplitCoequalizer` 的定义

English:
class HasSplitCoequalizer
  parameters: : Prop where
  axioms and operations (1):
    - splittable : exists (Z : C) (h : Y ⟶ Z), Nonempty (IsSplitCoequalizer f g h)

中文:
类 有SplitCoequalizer
  参数: : 命题 where
  公理与运算 (1 个):
    - splittable : 存在 (Z : C) (h : Y ⟶ Z), 非空 (是SplitCoequalizer f g h)
-/
class HasSplitCoequalizer : Prop where
  /-- There is some split coequalizer -/
  splittable : exists (Z : C) (h : Y ⟶ Z), Nonempty (IsSplitCoequalizer f g h)

/--
Definition of `Functor.IsSplitPair` / `Functor.IsSplitPair` 的定义

English:
abbreviation Functor.IsSplitPair
  signature: : Prop
  body: HasSplitCoequalizer (G.map f) (G.map g)

中文:
缩写 函子.IsSplitPair
  签名: : 命题
  定义体: HasSplitCoequalizer (G.map f) (G.map g)

Depends on / 依赖: G.map, HasSplitCoequalizer
-/
abbrev Functor.IsSplitPair : Prop :=
  HasSplitCoequalizer (G.map f) (G.map g)

/--
Definition of `HasSplitCoequalizer.coequalizerOfSplit` / `HasSplitCoequalizer.coequalizerOfSplit` 的定义

English:
definition HasSplitCoequalizer.coequalizerOfSplit
  signature: [HasSplitCoequalizer f g]
  body: (splittable (f := f) (g := g)).choose

中文:
定义 有SplitCoequalizer.coequalizerOfSplit
  签名: [有SplitCoequalizer f g]
  定义体: (splittable (f := f) (g := g)).choose

Depends on / 依赖: splittable
-/
noncomputable def HasSplitCoequalizer.coequalizerOfSplit [HasSplitCoequalizer f g] : C :=
  (splittable (f := f) (g := g)).choose

/--
Definition of `HasSplitCoequalizer.coequalizerπ` / `HasSplitCoequalizer.coequalizerπ` 的定义

English:
definition HasSplitCoequalizer.coequalizerπ
  signature: [HasSplitCoequalizer f g]
  body: (splittable (f := f) (g := g)).choose_spec.choose

中文:
定义 有SplitCoequalizer.coequalizerπ
  签名: [有SplitCoequalizer f g]
  定义体: (splittable (f := f) (g := g)).choose_spec.choose

Depends on / 依赖: choose_spec, choose_spec.choose, splittable
-/
noncomputable def HasSplitCoequalizer.coequalizerπ [HasSplitCoequalizer f g] :
    Y ⟶ HasSplitCoequalizer.coequalizerOfSplit f g :=
  (splittable (f := f) (g := g)).choose_spec.choose

/--
Definition of `HasSplitCoequalizer.isSplitCoequalizer` / `HasSplitCoequalizer.isSplitCoequalizer` 的定义

English:
definition HasSplitCoequalizer.isSplitCoequalizer
  signature: [HasSplitCoequalizer f g]
  body: Classical.choice (splittable (f := f) (g := g)).choose_spec.choose_spec

中文:
定义 有SplitCoequalizer.isSplitCoequalizer
  签名: [有SplitCoequalizer f g]
  定义体: Classical.choice (splittable (f := f) (g := g)).choose_spec.choose_spec

Depends on / 依赖: Classical, Classical.choice, choice, choose_spec, choose_spec.choose_spec, splittable
-/
noncomputable def HasSplitCoequalizer.isSplitCoequalizer [HasSplitCoequalizer f g] :
    IsSplitCoequalizer f g (HasSplitCoequalizer.coequalizerπ f g) :=
  Classical.choice (splittable (f := f) (g := g)).choose_spec.choose_spec

/--
Instance `map_is_split_pair` / 实例 `map_is_split_pair`

English:
instance map_is_split_pair
  signature: [HasSplitCoequalizer f g]
  body: ⟨_, _, ⟨IsSplitCoequalizer.map (HasSplitCoequalizer.isSplitCoequalizer f g) _⟩⟩

中文:
实例 map_is_split_pair
  签名: [有SplitCoequalizer f g]
  定义体: ⟨_, _, ⟨IsSplitCoequalizer.map (HasSplitCoequalizer.isSplitCoequalizer f g) _⟩⟩

Depends on / 依赖: HasSplitCoequalizer, HasSplitCoequalizer.isSplitCoequalizer, IsSplitCoequalizer, IsSplitCoequalizer.map, isSplitCoequalizer
-/
instance map_is_split_pair [HasSplitCoequalizer f g] : HasSplitCoequalizer (G.map f) (G.map g) where
  splittable :=
    ⟨_, _, ⟨IsSplitCoequalizer.map (HasSplitCoequalizer.isSplitCoequalizer f g) _⟩⟩

namespace Limits

/-- If a pair has a split coequalizer, it has a coequalizer. -/
instance (priority := 1) hasCoequalizer_of_hasSplitCoequalizer [HasSplitCoequalizer f g] :
    HasCoequalizer f g :=
  HasColimit.mk ⟨_, (HasSplitCoequalizer.isSplitCoequalizer f g).isCoequalizer⟩

end Limits

end CategoryTheory
