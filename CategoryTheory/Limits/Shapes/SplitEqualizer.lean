/-
Copyright (c) 2024 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Split Equalizers

We define what it means for a triple of morphisms `f g : X ⟶ Y`, `ι : W ⟶ X` to be a split
equalizer: there is a retraction `r` of `ι` and a retraction `t` of `g`, which additionally satisfy
`t ≫ f = r ≫ ι`.

In addition, we show that every split equalizer is an equalizer
(`CategoryTheory.IsSplitEqualizer.isEqualizer`) and absolute
(`CategoryTheory.IsSplitEqualizer.map`)

A pair `f g : X ⟶ Y` has a split equalizer if there is a `W` and `ι : W ⟶ X` making `f,g,ι` a
split equalizer.
A pair `f g : X ⟶ Y` has a `G`-split equalizer if `G f, G g` has a split equalizer.

These definitions and constructions are useful in particular for the comonadicity theorems.

This file was adapted from `Mathlib/CategoryTheory/Limits/Shapes/SplitCoequalizer.lean`. Please try
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
Definition of `IsSplitEqualizer` / `IsSplitEqualizer` 的定义

English:
structure IsSplitEqualizer
  parameters: {W : C} (ι : W ⟶ X)
  axioms and operations (6):
    - leftRetraction : X ⟶ W
    - rightRetraction : Y ⟶ X
    - condition : ι ≫ f = ι ≫ g  [default: by cat_disch]
    - ι_leftRetraction : ι ≫ leftRetraction = 𝟙 W  [default: by cat_disch]
    - bottom_rightRetraction : g ≫ rightRetraction = 𝟙 X  [default: by cat_disch]
    - top_rightRetraction : f ≫ rightRetraction = leftRetraction ≫ ι  [default: by cat_disch]

中文:
结构 是SplitEqualizer
  参数: {W : C} (ι : W ⟶ X)
  公理与运算 (6 个):
    - leftRetraction : X ⟶ W
    - rightRetraction : Y ⟶ X
    - condition : ι ≫ f = ι ≫ g  [默认: by cat_disch]
    - ι_leftRetraction : ι ≫ leftRetraction = 𝟙 W  [默认: by cat_disch]
    - bottom_rightRetraction : g ≫ rightRetraction = 𝟙 X  [默认: by cat_disch]
    - top_rightRetraction : f ≫ rightRetraction = leftRetraction ≫ ι  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure IsSplitEqualizer {W : C} (ι : W ⟶ X) where
  /-- A map from `X` to the equalizer -/
  leftRetraction : X ⟶ W
  /-- A map in the opposite direction to `f` and `g` -/
  rightRetraction : Y ⟶ X
  /-- Composition of `ι` with `f` and with `g` agree -/
  condition : ι ≫ f = ι ≫ g := by cat_disch
  /-- `leftRetraction` splits `ι` -/
  ι_leftRetraction : ι ≫ leftRetraction = 𝟙 W := by cat_disch
  /-- `rightRetraction` splits `g` -/
  bottom_rightRetraction : g ≫ rightRetraction = 𝟙 X := by cat_disch
  /-- `f` composed with `rightRetraction` is `leftRetraction` composed with `ι` -/
  top_rightRetraction : f ≫ rightRetraction = leftRetraction ≫ ι := by cat_disch

instance {X : C} : Inhabited (IsSplitEqualizer (𝟙 X) (𝟙 X) (𝟙 X)) where
  default := { leftRetraction := 𝟙 X, rightRetraction := 𝟙 X }

open IsSplitEqualizer

attribute [reassoc] condition

attribute [reassoc (attr := simp)] ι_leftRetraction bottom_rightRetraction top_rightRetraction

variable {f g}

/-- Split equalizers are absolute: they are preserved by any functor. -/
@[simps]
/--
Definition of `IsSplitEqualizer.map` / `IsSplitEqualizer.map` 的定义

English:
definition IsSplitEqualizer.map
  signature: {W : C} {ι : W ⟶ X} (q : IsSplitEqualizer f g ι) (F : C ⥤ D)
  body: F.map q.leftRetraction
  rightRetraction := F.map q.rightRetraction
  condition := by rw [← F.map_comp, q.condition, F.map_comp]
  ι_leftRetraction := by rw [← F.map_comp, q.ι_leftRetraction, F.map_id]
  bottom_rightRetraction := by rw [← F.map_comp, q.bottom_rightRetraction, F.map_id]
  top_rightRetraction := by rw [← F.map_comp, q.top_rightRetraction, F.map_comp]

中文:
定义 是SplitEqualizer.map
  签名: {W : C} {ι : W ⟶ X} (q : 是SplitEqualizer f g ι) (F : C ⥤ D)
  定义体: F.map q.leftRetraction
  rightRetraction := F.map q.rightRetraction
  condition := by rw [← F.map_comp, q.condition, F.map_comp]
  ι_leftRetraction := by rw [← F.map_comp, q.ι_leftRetraction, F.map_id]
  bottom_rightRetraction := by rw [← F.map_comp, q.bottom_rightRetraction, F.map_id]
  top_rightRetraction := by rw [← F.map_comp, q.top_rightRetraction, F.map_comp]

Depends on / 依赖: F.map, leftRetraction, q.leftRetraction
-/
def IsSplitEqualizer.map {W : C} {ι : W ⟶ X} (q : IsSplitEqualizer f g ι) (F : C ⥤ D) :
    IsSplitEqualizer (F.map f) (F.map g) (F.map ι) where
  leftRetraction := F.map q.leftRetraction
  rightRetraction := F.map q.rightRetraction
  condition := by rw [← F.map_comp, q.condition, F.map_comp]
  ι_leftRetraction := by rw [← F.map_comp, q.ι_leftRetraction, F.map_id]
  bottom_rightRetraction := by rw [← F.map_comp, q.bottom_rightRetraction, F.map_id]
  top_rightRetraction := by rw [← F.map_comp, q.top_rightRetraction, F.map_comp]

section

open Limits

/-- A split equalizer clearly induces a fork. -/
@[simps! pt]
/--
Definition of `IsSplitEqualizer.asFork` / `IsSplitEqualizer.asFork` 的定义

English:
definition IsSplitEqualizer.asFork
  signature: {W : C} {h : W ⟶ X} (t : IsSplitEqualizer f g h)
  body: Fork.ofι h t.condition

@[simp]

中文:
定义 是SplitEqualizer.asFork
  签名: {W : C} {h : W ⟶ X} (t : 是SplitEqualizer f g h)
  定义体: Fork.ofι h t.condition

@[simp]

Depends on / 依赖: Fork.of, condition, t.condition
-/
def IsSplitEqualizer.asFork {W : C} {h : W ⟶ X} (t : IsSplitEqualizer f g h) :
    Fork f g := Fork.ofι h t.condition

@[simp]
/--
theorem `IsSplitEqualizer.asFork_ι` / 定理 `IsSplitEqualizer.asFork_ι`

English:
theorem IsSplitEqualizer.asFork_ι
  given: {W : C} {h : W ⟶ X} (t : IsSplitEqualizer f g h)
  proof: rfl

中文:
定理 是SplitEqualizer.asFork_ι
  条件: {W : C} {h : W ⟶ X} (t : 是SplitEqualizer f g h)
  证明: rfl
-/
theorem IsSplitEqualizer.asFork_ι {W : C} {h : W ⟶ X} (t : IsSplitEqualizer f g h) :
    t.asFork.ι = h := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `IsSplitEqualizer.isEqualizer` / `IsSplitEqualizer.isEqualizer` 的定义

English:
definition IsSplitEqualizer.isEqualizer
  signature: {W : C} {h : W ⟶ X} (t : IsSplitEqualizer f g h)
  body: Fork.IsLimit.mk' _ fun s =>
    ⟨ s.ι ≫ t.leftRetraction,
      by simp [-top_rightRetraction, ← t.top_rightRetraction, s.condition_assoc],
      fun hm => by simp [← hm] ⟩

中文:
定义 是SplitEqualizer.isEqualizer
  签名: {W : C} {h : W ⟶ X} (t : 是SplitEqualizer f g h)
  定义体: Fork.IsLimit.mk' _ fun s =>
    ⟨ s.ι ≫ t.leftRetraction,
      by simp [-top_rightRetraction, ← t.top_rightRetraction, s.condition_assoc],
      fun hm => by simp [← hm] ⟩

Depends on / 依赖: Cone.mk, Fork.IsLimit.mk, IsLimit, condition_assoc, hom_ext, isLimit, leftRetraction, naturality, p.isLimit.fac, p.isLimit.hom_ext, p.isLimit.lift, p.prop_diag_obj, prop_diag_obj, reassoc_of, s.condition_assoc, t.leftRetraction, t.top_rightRetraction, top_rightRetraction
-/
def IsSplitEqualizer.isEqualizer {W : C} {h : W ⟶ X} (t : IsSplitEqualizer f g h) :
    IsLimit t.asFork :=
  Fork.IsLimit.mk' _ fun s =>
    ⟨ s.ι ≫ t.leftRetraction,
      by simp [-top_rightRetraction, ← t.top_rightRetraction, s.condition_assoc],
      fun hm => by simp [← hm] ⟩

end
variable (f g)

/--
Definition of `HasSplitEqualizer` / `HasSplitEqualizer` 的定义

English:
class HasSplitEqualizer
  parameters: : Prop where
  axioms and operations (1):
    - splittable : exists (W : C) (h : W ⟶ X), Nonempty (IsSplitEqualizer f g h)

中文:
类 有SplitEqualizer
  参数: : 命题 where
  公理与运算 (1 个):
    - splittable : 存在 (W : C) (h : W ⟶ X), 非空 (是SplitEqualizer f g h)

Depends on / 依赖: Cocone, Cocone.mk, fac_assoc, hom_ext, isColimit, naturality, p.isColimit.desc, p.isColimit.fac_assoc, p.isColimit.hom_ext, p.prop_diag_obj, prop_diag_obj
-/
class HasSplitEqualizer : Prop where
  /-- There is some split equalizer -/
  splittable : exists (W : C) (h : W ⟶ X), Nonempty (IsSplitEqualizer f g h)

/--
Definition of `Functor.IsCosplitPair` / `Functor.IsCosplitPair` 的定义

English:
abbreviation Functor.IsCosplitPair
  signature: : Prop
  body: HasSplitEqualizer (G.map f) (G.map g)

中文:
缩写 函子.IsCosplitPair
  签名: : 命题
  定义体: HasSplitEqualizer (G.map f) (G.map g)

Depends on / 依赖: G.map, HasSplitEqualizer
-/
abbrev Functor.IsCosplitPair : Prop :=
  HasSplitEqualizer (G.map f) (G.map g)

/--
Definition of `HasSplitEqualizer.equalizerOfSplit` / `HasSplitEqualizer.equalizerOfSplit` 的定义

English:
definition HasSplitEqualizer.equalizerOfSplit
  signature: [HasSplitEqualizer f g]
  body: (splittable (f := f) (g := g)).choose

中文:
定义 有SplitEqualizer.equalizerOfSplit
  签名: [有SplitEqualizer f g]
  定义体: (splittable (f := f) (g := g)).choose

Depends on / 依赖: splittable
-/
noncomputable def HasSplitEqualizer.equalizerOfSplit [HasSplitEqualizer f g] : C :=
  (splittable (f := f) (g := g)).choose

/--
Definition of `HasSplitEqualizer.equalizerι` / `HasSplitEqualizer.equalizerι` 的定义

English:
definition HasSplitEqualizer.equalizerι
  signature: [HasSplitEqualizer f g]
  body: (splittable (f := f) (g := g)).choose_spec.choose

中文:
定义 有SplitEqualizer.equalizerι
  签名: [有SplitEqualizer f g]
  定义体: (splittable (f := f) (g := g)).choose_spec.choose

Depends on / 依赖: choose_spec, choose_spec.choose, splittable
-/
noncomputable def HasSplitEqualizer.equalizerι [HasSplitEqualizer f g] :
    HasSplitEqualizer.equalizerOfSplit f g ⟶ X :=
  (splittable (f := f) (g := g)).choose_spec.choose

/--
Definition of `HasSplitEqualizer.isSplitEqualizer` / `HasSplitEqualizer.isSplitEqualizer` 的定义

English:
definition HasSplitEqualizer.isSplitEqualizer
  signature: [HasSplitEqualizer f g]
  body: Classical.choice (splittable (f := f) (g := g)).choose_spec.choose_spec

中文:
定义 有SplitEqualizer.isSplitEqualizer
  签名: [有SplitEqualizer f g]
  定义体: Classical.choice (splittable (f := f) (g := g)).choose_spec.choose_spec

Depends on / 依赖: Classical, Classical.choice, choice, choose_spec, choose_spec.choose_spec, splittable
-/
noncomputable def HasSplitEqualizer.isSplitEqualizer [HasSplitEqualizer f g] :
    IsSplitEqualizer f g (HasSplitEqualizer.equalizerι f g) :=
  Classical.choice (splittable (f := f) (g := g)).choose_spec.choose_spec

/--
Instance `map_is_cosplit_pair` / 实例 `map_is_cosplit_pair`

English:
instance map_is_cosplit_pair
  signature: [HasSplitEqualizer f g]
  body: ⟨_, _, ⟨IsSplitEqualizer.map (HasSplitEqualizer.isSplitEqualizer f g) _⟩⟩

中文:
实例 map_is_cosplit_pair
  签名: [有SplitEqualizer f g]
  定义体: ⟨_, _, ⟨IsSplitEqualizer.map (HasSplitEqualizer.isSplitEqualizer f g) _⟩⟩

Depends on / 依赖: HasSplitEqualizer, HasSplitEqualizer.isSplitEqualizer, IsSplitEqualizer, IsSplitEqualizer.map, isSplitEqualizer
-/
instance map_is_cosplit_pair [HasSplitEqualizer f g] : HasSplitEqualizer (G.map f) (G.map g) where
  splittable :=
    ⟨_, _, ⟨IsSplitEqualizer.map (HasSplitEqualizer.isSplitEqualizer f g) _⟩⟩

namespace Limits

/-- If a pair has a split equalizer, it has an equalizer. -/
instance (priority := 1) hasEqualizer_of_hasSplitEqualizer [HasSplitEqualizer f g] :
    HasEqualizer f g :=
  HasLimit.mk ⟨_, (HasSplitEqualizer.isSplitEqualizer f g).isEqualizer⟩

end Limits

end CategoryTheory
