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

/-- A split coequalizer diagram consists of morphisms

      f   π
    X ⇉ Y → Z
      g

satisfying `f ≫ π = g ≫ π` together with morphisms

      t   s
    X ← Y ← Z

satisfying `s ≫ π = 𝟙 Z`, `t ≫ g = 𝟙 Y` and `t ≫ f = π ≫ s`.

The name "coequalizer" is appropriate, since any split coequalizer is a coequalizer, see
`CategoryTheory.IsSplitCoequalizer.isCoequalizer`.
Split coequalizers are also absolute, since a functor preserves all the structure above.
-/
/-
**CategoryTheory.IsSplitCoequalizer** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory`。
形式化陈述：IsSplitCoequalizer {Z : C} (π : Y ⟶ Z) where /-- A map from the coequalize
r to `Y` -/ rightSection : Z ⟶ Y /-- A map in the opposite direction to `f` and 
`g` -/ leftSection : Y ⟶ X /-- Composition of `π` with `f` and with `g` agree -/
 condition : f ≫ π = g ≫ π
参数：π : Y ⟶ Z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A split coequalizer diagram consists of morphisms

      f   π
    X ⇉ Y → Z
      g

satisfying `f ≫ π = g ≫ π` together with morphisms

      t   s
    X ← Y ← Z

satisfying `s ≫ π = 𝟙 Z`, `t ≫ g = 𝟙 Y` and `t ≫ f = π ≫ s`.

The name "coequalizer" is appropriate, since any split coequalizer is a coequali
zer, see
`CategoryTheory.IsSplitCoequalizer.isCoequalizer`.
Split coequalizers are also absolute, since a functor preserves all the structur
e above.
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
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : C} : Inhabited (IsSplitCoequalizer (𝟙 X) (𝟙 X) (𝟙 X)) where
  default := { rightSection := 𝟙 X, leftSection := 𝟙 X }

open IsSplitCoequalizer

attribute [reassoc] condition

attribute [reassoc (attr := simp)] rightSection_π leftSection_bottom leftSection_top

variable {f g}

/-- Split coequalizers are absolute: they are preserved by any functor. -/
@[simps]
/-
**CategoryTheory.IsSplitCoequalizer.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.IsSplitCoequalizer`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {D : Type
 u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         {X Y : C} →
           {f g : X ⟶ Y} →             {Z : C} →               {π : Y ⟶ Z} →    
             CategoryTheory.IsSplitCoequalizer f g π →                   (F : Ca
tegoryTheory.Functor C D) → CategoryTheory.IsSplitCoequalizer (F.map f) (F.map g
) (F.map π)
参数：F : CategoryTheory.Functor C D；F.map f；F.map g；F.map π。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Split coequalizers are absolute: they are preserved by any functor.
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
/-
**CategoryTheory.IsSplitCoequalizer.asCofork** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.IsSplitCoequalizer`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 →       {f g : X ⟶ Y} → {Z : C} → {h : Y ⟶ Z} → CategoryTheory.IsSplitCoequaliz
er f g h → CategoryTheory.Limits.Cofork f g
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsSplitCoequalizer.condition`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y : C} {f g : X ⟶ Y} {Z : C} {π : Y ⟶ Z}   (sel
f : CategoryTheory.IsSplitCoequal…

--- 原说明 ---
A split coequalizer clearly induces a cofork.
-/
def IsSplitCoequalizer.asCofork {Z : C} {h : Y ⟶ Z} (t : IsSplitCoequalizer f g h) :
    Cofork f g := Cofork.ofπ h t.condition

@[simp]
/-
**CategoryTheory.IsSplitCoequalizer.asCofork_** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsSplitCoequalizer.asCofork_π {Z : C} {h : Y ⟶ Z} (t : IsSplitCoequalizer f g h) :
    t.asCofork.π = h := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
The cofork induced by a split coequalizer is a coequalizer, justifying the name. In some cases it
is more convenient to show a given cofork is a coequalizer by showing it is split.
-/
/-
**CategoryTheory.IsSplitCoequalizer.isCoequalizer** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.IsSplitCoequalizer`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 →       {f g : X ⟶ Y} →         {Z : C} →           {h : Y ⟶ Z} → (t : Category
Theory.IsSplitCoequalizer f g h) → CategoryTheory.Limits.IsColimit t.asCofork
参数：t : CategoryTheory.IsSplitCoequalizer f g h。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cofork induced by a split coequalizer is a coequalizer, justifying the name.
 In some cases it
is more convenient to show a given cofork is a coequalizer by showing it is spli
t.
-/
def IsSplitCoequalizer.isCoequalizer {Z : C} {h : Y ⟶ Z} (t : IsSplitCoequalizer f g h) :
    IsColimit t.asCofork :=
  Cofork.IsColimit.mk' _ fun s =>
    ⟨t.rightSection ≫ s.π, by
      dsimp
      rw [← t.leftSection_top_assoc, s.condition, t.leftSection_bottom_assoc], fun hm => by
      simp [← hm]⟩

end

variable (f g)

/--
The pair `f,g` is a split pair if there is an `h : Y ⟶ Z` so that `f, g, h` forms a split
coequalizer in `C`.
-/
/-
**CategoryTheory.HasSplitCoequalizer** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory
`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → {X Y : C} → (X 
⟶ Y) → (X ⟶ Y) → Prop
参数：X ⟶ Y；X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pair `f,g` is a split pair if there is an `h : Y ⟶ Z` so that `f, g, h` form
s a split
coequalizer in `C`.
-/
class HasSplitCoequalizer : Prop where
  /-- There is some split coequalizer -/
  splittable : ∃ (Z : C) (h : Y ⟶ Z), Nonempty (IsSplitCoequalizer f g h)

/--
The pair `f,g` is a `G`-split pair if there is an `h : G Y ⟶ Z` so that `G f, G g, h` forms a split
coequalizer in `D`.
-/
/-
**CategoryTheory.Functor.IsSplitPair** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.F
unctor`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {D : Type
 u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] → CategoryTheory.Func
tor C D → {X Y : C} → (X ⟶ Y) → (X ⟶ Y) → Prop
参数：X ⟶ Y；X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pair `f,g` is a `G`-split pair if there is an `h : G Y ⟶ Z` so that `G f, G 
g, h` forms a split
coequalizer in `D`.
-/
abbrev Functor.IsSplitPair : Prop :=
  HasSplitCoequalizer (G.map f) (G.map g)

/-- Get the coequalizer object from the typeclass `IsSplitPair`. -/
/-
**CategoryTheory.HasSplitCoequalizer.coequalizerOfSplit** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.HasSplitCoequalizer`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] → {X Y : C} → (
f g : X ⟶ Y) → [CategoryTheory.HasSplitCoequalizer f g] → C
参数：f g : X ⟶ Y。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.HasSplitCoequalizer.splittable`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} {X Y : C} {f g : X ⟶ Y}   [self : CategoryTheory
.HasSplitCoequalizer f g], ∃ Z h, N…

--- 原说明 ---
Get the coequalizer object from the typeclass `IsSplitPair`.
-/
noncomputable def HasSplitCoequalizer.coequalizerOfSplit [HasSplitCoequalizer f g] : C :=
  (splittable (f := f) (g := g)).choose

/-- Get the coequalizer morphism from the typeclass `IsSplitPair`. -/
/-
**CategoryTheory.HasSplitCoequalizer.coequalizer** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Get the coequalizer morphism from the typeclass `IsSplitPair`.
-/
noncomputable def HasSplitCoequalizer.coequalizerπ [HasSplitCoequalizer f g] :
    Y ⟶ HasSplitCoequalizer.coequalizerOfSplit f g :=
  (splittable (f := f) (g := g)).choose_spec.choose

/-- The coequalizer morphism `coequalizerπ` gives a split coequalizer on `f,g`. -/
/-
**CategoryTheory.HasSplitCoequalizer.isSplitCoequalizer** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.HasSplitCoequalizer`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 →       (f g : X ⟶ Y) →         [inst_1 : CategoryTheory.HasSplitCoequalizer f 
g] →           CategoryTheory.IsSplitCoequalizer f g (CategoryTheory.HasSplitCoe
qualizer.coequalizerπ f g)
参数：f g : X ⟶ Y；CategoryTheory.HasSplitCoequalizer.coequalizerπ f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coequalizer morphism `coequalizerπ` gives a split coequalizer on `f,g`.
-/
noncomputable def HasSplitCoequalizer.isSplitCoequalizer [HasSplitCoequalizer f g] :
    IsSplitCoequalizer f g (HasSplitCoequalizer.coequalizerπ f g) :=
  Classical.choice (splittable (f := f) (g := g)).choose_spec.choose_spec

/-- If `f, g` is split, then `G f, G g` is split. -/
/-
**CategoryTheory.map_is_split_pair** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：map_is_split_pair [HasSplitCoequalizer f g] : HasSplitCoequalizer (G.map f
) (G.map g) where splittable
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f, g` is split, then `G f, G g` is split.
-/
instance map_is_split_pair [HasSplitCoequalizer f g] : HasSplitCoequalizer (G.map f) (G.map g) where
  splittable :=
    ⟨_, _, ⟨IsSplitCoequalizer.map (HasSplitCoequalizer.isSplitCoequalizer f g) _⟩⟩

namespace Limits

/-- If a pair has a split coequalizer, it has a coequalizer. -/
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a pair has a split coequalizer, it has a coequalizer.
-/
instance (priority := 1) hasCoequalizer_of_hasSplitCoequalizer [HasSplitCoequalizer f g] :
    HasCoequalizer f g :=
  HasColimit.mk ⟨_, (HasSplitCoequalizer.isSplitCoequalizer f g).isCoequalizer⟩

end Limits

end CategoryTheory

