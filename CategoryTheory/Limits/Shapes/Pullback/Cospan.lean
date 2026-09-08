/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Markus Himmel, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

/-!
# Cospan & Span

We define a category `WalkingCospan` (resp. `WalkingSpan`), which is the index category
for the given data for a pullback (resp. pushout) diagram. Convenience methods `cospan f g`
and `span f g` construct functors from the walking (co)span, hitting the given morphisms.

## References
* [Stacks: Fibre products](https://stacks.math.columbia.edu/tag/001U)
* [Stacks: Pushouts](https://stacks.math.columbia.edu/tag/0025)
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe w v₁ v₂ v u u₂

namespace CategoryTheory.Limits

-- Porting note: `aesop cases` does not work on type synonyms like `WidePullbackShape`
-- attribute [local aesop safe cases] WidePullbackShape WalkingPair

/-- The type of objects for the diagram indexing a pullback, defined as a special case of
`WidePullbackShape`. -/
/-
**CategoryTheory.Limits.WalkingCospan** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheor
y.Limits`。
形式化陈述：WalkingCospan : Type
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of objects for the diagram indexing a pullback, defined as a special ca
se of
`WidePullbackShape`.
-/
abbrev WalkingCospan : Type :=
  WidePullbackShape WalkingPair

/-- The left point of the walking cospan. -/
@[match_pattern]
/-
**CategoryTheory.Limits.WalkingCospan.left** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits.WalkingCospan`。
形式化陈述：CategoryTheory.Limits.WalkingCospan
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left point of the walking cospan.
-/
abbrev WalkingCospan.left : WalkingCospan :=
  some WalkingPair.left

/-- The right point of the walking cospan. -/
@[match_pattern]
/-
**CategoryTheory.Limits.WalkingCospan.right** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits.WalkingCospan`。
形式化陈述：CategoryTheory.Limits.WalkingCospan
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right point of the walking cospan.
-/
abbrev WalkingCospan.right : WalkingCospan :=
  some WalkingPair.right

/-- The central point of the walking cospan. -/
@[match_pattern]
/-
**CategoryTheory.Limits.WalkingCospan.one** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Limits.WalkingCospan`。
形式化陈述：CategoryTheory.Limits.WalkingCospan
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The central point of the walking cospan.
-/
abbrev WalkingCospan.one : WalkingCospan :=
  none

/-- The type of objects for the diagram indexing a pushout, defined as a special case of
`WidePushoutShape`.
-/
/-
**CategoryTheory.Limits.WalkingSpan** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.
Limits`。
形式化陈述：WalkingSpan : Type
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of objects for the diagram indexing a pushout, defined as a special cas
e of
`WidePushoutShape`.
-/
abbrev WalkingSpan : Type :=
  WidePushoutShape WalkingPair

/-- The left point of the walking span. -/
@[match_pattern]
/-
**CategoryTheory.Limits.WalkingSpan.left** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits.WalkingSpan`。
形式化陈述：CategoryTheory.Limits.WalkingSpan
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left point of the walking span.
-/
abbrev WalkingSpan.left : WalkingSpan :=
  some WalkingPair.left

/-- The right point of the walking span. -/
@[match_pattern]
/-
**CategoryTheory.Limits.WalkingSpan.right** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Limits.WalkingSpan`。
形式化陈述：CategoryTheory.Limits.WalkingSpan
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right point of the walking span.
-/
abbrev WalkingSpan.right : WalkingSpan :=
  some WalkingPair.right

/-- The central point of the walking span. -/
@[match_pattern]
/-
**CategoryTheory.Limits.WalkingSpan.zero** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits.WalkingSpan`。
形式化陈述：CategoryTheory.Limits.WalkingSpan
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The central point of the walking span.
-/
abbrev WalkingSpan.zero : WalkingSpan :=
  none

namespace WalkingCospan

/-- The type of arrows for the diagram indexing a pullback. -/
/-
**CategoryTheory.Limits.WalkingCospan.Hom** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryT
heory.Limits.WalkingCospan`。
形式化陈述：Hom : WalkingCospan -> WalkingCospan -> Type
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of arrows for the diagram indexing a pullback.
-/
abbrev Hom : WalkingCospan → WalkingCospan → Type :=
  WidePullbackShape.Hom

/-- The left arrow of the walking cospan. -/
@[match_pattern]
/-
**CategoryTheory.Limits.WalkingCospan.Hom.inl** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits.WalkingCospan.Hom`。
形式化陈述：CategoryTheory.Limits.WalkingCospan.left ⟶ CategoryTheory.Limits.WalkingCo
span.one
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left arrow of the walking cospan.
-/
abbrev Hom.inl : left ⟶ one :=
  WidePullbackShape.Hom.term _

/-- The right arrow of the walking cospan. -/
@[match_pattern]
/-
**CategoryTheory.Limits.WalkingCospan.Hom.inr** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits.WalkingCospan.Hom`。
形式化陈述：CategoryTheory.Limits.WalkingCospan.right ⟶ CategoryTheory.Limits.WalkingC
ospan.one
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right arrow of the walking cospan.
-/
abbrev Hom.inr : right ⟶ one :=
  WidePullbackShape.Hom.term _

/-- The identity arrows of the walking cospan. -/
@[match_pattern]
/-
**CategoryTheory.Limits.WalkingCospan.Hom.id** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits.WalkingCospan.Hom`。
形式化陈述：(X : CategoryTheory.Limits.WalkingCospan) → X ⟶ X
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity arrows of the walking cospan.
-/
abbrev Hom.id (X : WalkingCospan) : X ⟶ X :=
  WidePullbackShape.Hom.id X
/-
**CategoryTheory.Limits.WalkingCospan.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.Limits.WalkingCospan`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X Y : WalkingCospan) : Subsingleton (X ⟶ Y) := by
  constructor; intros; simp [eq_iff_true_of_subsingleton]

end WalkingCospan

namespace WalkingSpan

/-- The type of arrows for the diagram indexing a pushout. -/
/-
**CategoryTheory.Limits.WalkingSpan.Hom** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryThe
ory.Limits.WalkingSpan`。
形式化陈述：Hom : WalkingSpan -> WalkingSpan -> Type
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of arrows for the diagram indexing a pushout.
-/
abbrev Hom : WalkingSpan → WalkingSpan → Type :=
  WidePushoutShape.Hom

/-- The left arrow of the walking span. -/
@[match_pattern]
/-
**CategoryTheory.Limits.WalkingSpan.Hom.fst** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits.WalkingSpan.Hom`。
形式化陈述：CategoryTheory.Limits.WalkingSpan.zero ⟶ CategoryTheory.Limits.WalkingSpan
.left
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left arrow of the walking span.
-/
abbrev Hom.fst : zero ⟶ left :=
  WidePushoutShape.Hom.init _

/-- The right arrow of the walking span. -/
@[match_pattern]
/-
**CategoryTheory.Limits.WalkingSpan.Hom.snd** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits.WalkingSpan.Hom`。
形式化陈述：CategoryTheory.Limits.WalkingSpan.zero ⟶ CategoryTheory.Limits.WalkingSpan
.right
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right arrow of the walking span.
-/
abbrev Hom.snd : zero ⟶ right :=
  WidePushoutShape.Hom.init _

/-- The identity arrows of the walking span. -/
@[match_pattern]
/-
**CategoryTheory.Limits.WalkingSpan.Hom.id** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits.WalkingSpan.Hom`。
形式化陈述：(X : CategoryTheory.Limits.WalkingSpan) → X ⟶ X
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity arrows of the walking span.
-/
abbrev Hom.id (X : WalkingSpan) : X ⟶ X :=
  WidePushoutShape.Hom.id X
/-
**CategoryTheory.Limits.WalkingSpan.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.L
imits.WalkingSpan`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X Y : WalkingSpan) : Subsingleton (X ⟶ Y) := by
  constructor; intro a b; simp [eq_iff_true_of_subsingleton]

end WalkingSpan

open WalkingSpan.Hom WalkingCospan.Hom WidePullbackShape.Hom WidePushoutShape.Hom

variable {C : Type u} [Category.{v} C]

set_option backward.defeqAttrib.useBackward true in
/-- To construct an isomorphism of cones over the walking cospan,
it suffices to construct an isomorphism
of the cone points and check it commutes with the legs to `left` and `right`. -/
/-
**CategoryTheory.Limits.WalkingCospan.ext** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Limits.WalkingCospan`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {F : Cate
goryTheory.Functor CategoryTheory.Limits.WalkingCospan C} →       {s t : Categor
yTheory.Limits.Cone F} →         (i : s.pt ≅ t.pt) →           s.π.app CategoryT
heory.Limits.WalkingCospan.left =               CategoryTheory.CategoryStruct.co
mp i.hom (t.π.app CategoryTheory.Limits.WalkingCospan.left) →             s.π.ap
p CategoryTheory.Limits.WalkingCospan.right =                 CategoryTheory.Cat
egoryStruct.comp i.hom (t.π.app CategoryTheory.Limits.WalkingCospan.right) →    
           (s ≅ t)
参数：i : s.pt ≅ t.pt；t.π.app CategoryTheory.Limits.WalkingCospan.left；t.π.app Cate
goryTheory.Limits.WalkingCospan.right；s ≅ t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To construct an isomorphism of cones over the walking cospan,
it suffices to construct an isomorphism
of the cone points and check it commutes with the legs to `left` and `right`.
-/
def WalkingCospan.ext {F : WalkingCospan ⥤ C} {s t : Cone F} (i : s.pt ≅ t.pt)
    (w₁ : s.π.app WalkingCospan.left = i.hom ≫ t.π.app WalkingCospan.left)
    (w₂ : s.π.app WalkingCospan.right = i.hom ≫ t.π.app WalkingCospan.right) : s ≅ t := by
  apply Cone.ext i _
  rintro (⟨⟩ | ⟨⟨⟩⟩)
  · have h₁ := s.π.naturality WalkingCospan.Hom.inl
    dsimp at h₁
    simp only [Category.id_comp] at h₁
    have h₂ := t.π.naturality WalkingCospan.Hom.inl
    dsimp at h₂
    simp only [Category.id_comp] at h₂
    simp_rw [h₂, ← Category.assoc, ← w₁, ← h₁]
  · exact w₁
  · exact w₂

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- To construct an isomorphism of cocones over the walking span,
it suffices to construct an isomorphism
of the cocone points and check it commutes with the legs from `left` and `right`. -/
/-
**CategoryTheory.Limits.WalkingSpan.ext** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Limits.WalkingSpan`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {F : Cate
goryTheory.Functor CategoryTheory.Limits.WalkingSpan C} →       {s t : CategoryT
heory.Limits.Cocone F} →         (i : s.pt ≅ t.pt) →           CategoryTheory.Ca
tegoryStruct.comp (s.ι.app CategoryTheory.Limits.WalkingCospan.left) i.hom =    
           t.ι.app CategoryTheory.Limits.WalkingCospan.left →             Catego
ryTheory.CategoryStruct.comp (s.ι.app CategoryTheory.Limits.WalkingCospan.right)
 i.hom =                 t.ι.app CategoryTheory.Limits.WalkingCospan.right →    
           (s ≅ t)
参数：i : s.pt ≅ t.pt；s.ι.app CategoryTheory.Limits.WalkingCospan.left；s.ι.app Cate
goryTheory.Limits.WalkingCospan.right；s ≅ t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To construct an isomorphism of cocones over the walking span,
it suffices to construct an isomorphism
of the cocone points and check it commutes with the legs from `left` and `right`
.
-/
def WalkingSpan.ext {F : WalkingSpan ⥤ C} {s t : Cocone F} (i : s.pt ≅ t.pt)
    (w₁ : s.ι.app WalkingCospan.left ≫ i.hom = t.ι.app WalkingCospan.left)
    (w₂ : s.ι.app WalkingCospan.right ≫ i.hom = t.ι.app WalkingCospan.right) : s ≅ t := by
  apply Cocone.ext i _
  rintro (⟨⟩ | ⟨⟨⟩⟩)
  · have h₁ := s.ι.naturality WalkingSpan.Hom.fst
    dsimp at h₁
    simp only [Category.comp_id] at h₁
    have h₂ := t.ι.naturality WalkingSpan.Hom.fst
    dsimp at h₂
    simp only [Category.comp_id] at h₂
    simp_rw [← h₁, Category.assoc, w₁, h₂]
  · exact w₁
  · exact w₂

/-- `cospan f g` is the functor from the walking cospan hitting `f` and `g`. -/
@[implicit_reducible]
/-
**CategoryTheory.Limits.cospan** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits`
。
形式化陈述：cospan {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : WalkingCospan ⥤ C
参数：f : X ⟶ Z；g : Y ⟶ Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`cospan f g` is the functor from the walking cospan hitting `f` and `g`.
-/
def cospan {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : WalkingCospan ⥤ C :=
  WidePullbackShape.wideCospan Z (fun j => WalkingPair.casesOn j X Y) fun j =>
    WalkingPair.casesOn j f g

/-- `span f g` is the functor from the walking span hitting `f` and `g`. -/
@[implicit_reducible]
/-
**CategoryTheory.Limits.span** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：span {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : WalkingSpan ⥤ C
参数：f : X ⟶ Y；g : X ⟶ Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`span f g` is the functor from the walking span hitting `f` and `g`.
-/
def span {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : WalkingSpan ⥤ C :=
  WidePushoutShape.wideSpan X (fun j => WalkingPair.casesOn j Y Z) fun j =>
    WalkingPair.casesOn j f g

@[simp]
/-
**CategoryTheory.Limits.cospan_left** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Li
mits`。
形式化陈述：cospan_left {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : (cospan f g).obj Walking
Cospan.left = X
参数：f : X ⟶ Z；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cospan_left {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : (cospan f g).obj WalkingCospan.left = X :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.span_left** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limi
ts`。
形式化陈述：span_left {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : (span f g).obj WalkingSpan
.left = Y
参数：f : X ⟶ Y；g : X ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem span_left {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : (span f g).obj WalkingSpan.left = Y :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.cospan_right** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.L
imits`。
形式化陈述：cospan_right {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : (cospan f g).obj Walkin
gCospan.right = Y
参数：f : X ⟶ Z；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cospan_right {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (cospan f g).obj WalkingCospan.right = Y := rfl

@[simp]
/-
**CategoryTheory.Limits.span_right** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Lim
its`。
形式化陈述：span_right {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : (span f g).obj WalkingSpa
n.right = Z
参数：f : X ⟶ Y；g : X ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem span_right {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : (span f g).obj WalkingSpan.right = Z :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.cospan_one** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Lim
its`。
形式化陈述：cospan_one {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : (cospan f g).obj WalkingC
ospan.one = Z
参数：f : X ⟶ Z；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cospan_one {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : (cospan f g).obj WalkingCospan.one = Z :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.span_zero** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limi
ts`。
形式化陈述：span_zero {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : (span f g).obj WalkingSpan
.zero = X
参数：f : X ⟶ Y；g : X ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem span_zero {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : (span f g).obj WalkingSpan.zero = X :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.cospan_map_inl** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits`。
形式化陈述：cospan_map_inl {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : (cospan f g).map Walk
ingCospan.Hom.inl = f
参数：f : X ⟶ Z；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cospan_map_inl {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (cospan f g).map WalkingCospan.Hom.inl = f := rfl

@[simp]
/-
**CategoryTheory.Limits.span_map_fst** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.L
imits`。
形式化陈述：span_map_fst {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : (span f g).map WalkingS
pan.Hom.fst = f
参数：f : X ⟶ Y；g : X ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem span_map_fst {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : (span f g).map WalkingSpan.Hom.fst = f :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.cospan_map_inr** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits`。
形式化陈述：cospan_map_inr {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : (cospan f g).map Walk
ingCospan.Hom.inr = g
参数：f : X ⟶ Z；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cospan_map_inr {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (cospan f g).map WalkingCospan.Hom.inr = g := rfl

@[simp]
/-
**CategoryTheory.Limits.span_map_snd** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.L
imits`。
形式化陈述：span_map_snd {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : (span f g).map WalkingS
pan.Hom.snd = g
参数：f : X ⟶ Y；g : X ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem span_map_snd {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : (span f g).map WalkingSpan.Hom.snd = g :=
  rfl
/-
**CategoryTheory.Limits.cospan_map_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Limits`。
形式化陈述：cospan_map_id {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (w : WalkingCospan) : (c
ospan f g).map (WalkingCospan.Hom.id w) = 𝟙 _
参数：f : X ⟶ Z；g : Y ⟶ Z；w : WalkingCospan。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cospan_map_id {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (w : WalkingCospan) :
    (cospan f g).map (WalkingCospan.Hom.id w) = 𝟙 _ := rfl
/-
**CategoryTheory.Limits.span_map_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Li
mits`。
形式化陈述：span_map_id {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) (w : WalkingSpan) : (span 
f g).map (WalkingSpan.Hom.id w) = 𝟙 _
参数：f : X ⟶ Y；g : X ⟶ Z；w : WalkingSpan。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem span_map_id {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) (w : WalkingSpan) :
    (span f g).map (WalkingSpan.Hom.id w) = 𝟙 _ := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Every diagram indexing a pullback is naturally isomorphic (actually, equal) to a `cospan` -/
@[simps (rhsMd := default)]
/-
**CategoryTheory.Limits.diagramIsoCospan** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits`。
形式化陈述：diagramIsoCospan (F : WalkingCospan ⥤ C) : F ≅ cospan (F.map inl) (F.map i
nr)
参数：F : WalkingCospan ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every diagram indexing a pullback is naturally isomorphic (actually, equal) to a
 `cospan`
-/
def diagramIsoCospan (F : WalkingCospan ⥤ C) : F ≅ cospan (F.map inl) (F.map inr) :=
  NatIso.ofComponents
  (fun j => eqToIso (by rcases j with (⟨⟩ | ⟨⟨⟩⟩) <;> rfl))
  (by rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) f <;> cases f <;> simp)

set_option backward.isDefEq.respectTransparency.types false in
/-- Every diagram indexing a pushout is naturally isomorphic (actually, equal) to a `span` -/
@[simps (rhsMd := default)]
/-
**CategoryTheory.Limits.diagramIsoSpan** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits`。
形式化陈述：diagramIsoSpan (F : WalkingSpan ⥤ C) : F ≅ span (F.map fst) (F.map snd)
参数：F : WalkingSpan ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every diagram indexing a pushout is naturally isomorphic (actually, equal) to a 
`span`
-/
def diagramIsoSpan (F : WalkingSpan ⥤ C) : F ≅ span (F.map fst) (F.map snd) :=
  NatIso.ofComponents
  (fun j => eqToIso (by rcases j with (⟨⟩ | ⟨⟨⟩⟩) <;> rfl))
  (by rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) f <;> cases f <;> simp)

variable {D : Type u₂} [Category.{v₂} D]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A functor applied to a cospan is a cospan. -/
/-
**CategoryTheory.Limits.cospanCompIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits`。
形式化陈述：cospanCompIso (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : cospan f g
 ⋙ F ≅ cospan (F.map f) (F.map g)
参数：F : C ⥤ D；f : X ⟶ Z；g : Y ⟶ Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor applied to a cospan is a cospan.
-/
def cospanCompIso (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    cospan f g ⋙ F ≅ cospan (F.map f) (F.map g) :=
  NatIso.ofComponents (by rintro (⟨⟩ | ⟨⟨⟩⟩) <;> exact Iso.refl _)
    (by rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) f <;> cases f <;> simp)

section

variable (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)

@[simp]
/-
**CategoryTheory.Limits.cospanCompIso_app_left** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：cospanCompIso_app_left : (cospanCompIso F f g).app WalkingCospan.left = Is
o.refl _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cospanCompIso_app_left : (cospanCompIso F f g).app WalkingCospan.left = Iso.refl _ := rfl

@[simp]
/-
**CategoryTheory.Limits.cospanCompIso_app_right** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：cospanCompIso_app_right : (cospanCompIso F f g).app WalkingCospan.right = 
Iso.refl _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cospanCompIso_app_right : (cospanCompIso F f g).app WalkingCospan.right = Iso.refl _ :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.cospanCompIso_app_one** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：cospanCompIso_app_one : (cospanCompIso F f g).app WalkingCospan.one = Iso.
refl _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cospanCompIso_app_one : (cospanCompIso F f g).app WalkingCospan.one = Iso.refl _ := rfl

@[simp]
/-
**CategoryTheory.Limits.cospanCompIso_hom_app_left** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：cospanCompIso_hom_app_left : (cospanCompIso F f g).hom.app WalkingCospan.l
eft = 𝟙 _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cospanCompIso_hom_app_left : (cospanCompIso F f g).hom.app WalkingCospan.left = 𝟙 _ :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.cospanCompIso_hom_app_right** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：cospanCompIso_hom_app_right : (cospanCompIso F f g).hom.app WalkingCospan.
right = 𝟙 _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cospanCompIso_hom_app_right : (cospanCompIso F f g).hom.app WalkingCospan.right = 𝟙 _ :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.cospanCompIso_hom_app_one** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：cospanCompIso_hom_app_one : (cospanCompIso F f g).hom.app WalkingCospan.on
e = 𝟙 _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cospanCompIso_hom_app_one : (cospanCompIso F f g).hom.app WalkingCospan.one = 𝟙 _ := rfl

@[simp]
/-
**CategoryTheory.Limits.cospanCompIso_inv_app_left** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：cospanCompIso_inv_app_left : (cospanCompIso F f g).inv.app WalkingCospan.l
eft = 𝟙 _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cospanCompIso_inv_app_left : (cospanCompIso F f g).inv.app WalkingCospan.left = 𝟙 _ :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.cospanCompIso_inv_app_right** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：cospanCompIso_inv_app_right : (cospanCompIso F f g).inv.app WalkingCospan.
right = 𝟙 _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cospanCompIso_inv_app_right : (cospanCompIso F f g).inv.app WalkingCospan.right = 𝟙 _ :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.cospanCompIso_inv_app_one** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：cospanCompIso_inv_app_one : (cospanCompIso F f g).inv.app WalkingCospan.on
e = 𝟙 _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cospanCompIso_inv_app_one : (cospanCompIso F f g).inv.app WalkingCospan.one = 𝟙 _ := rfl

end

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A functor applied to a span is a span. -/
/-
**CategoryTheory.Limits.spanCompIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Li
mits`。
形式化陈述：spanCompIso (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : span f g ⋙ F
 ≅ span (F.map f) (F.map g)
参数：F : C ⥤ D；f : X ⟶ Y；g : X ⟶ Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor applied to a span is a span.
-/
def spanCompIso (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
    span f g ⋙ F ≅ span (F.map f) (F.map g) :=
  NatIso.ofComponents (by rintro (⟨⟩ | ⟨⟨⟩⟩) <;> exact Iso.refl _)
    (by rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) f <;> cases f <;> simp)

section

variable (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)

@[simp]
/-
**CategoryTheory.Limits.spanCompIso_app_left** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits`。
形式化陈述：spanCompIso_app_left : (spanCompIso F f g).app WalkingSpan.left = Iso.refl
 _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem spanCompIso_app_left : (spanCompIso F f g).app WalkingSpan.left = Iso.refl _ := rfl

@[simp]
/-
**CategoryTheory.Limits.spanCompIso_app_right** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：spanCompIso_app_right : (spanCompIso F f g).app WalkingSpan.right = Iso.re
fl _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem spanCompIso_app_right : (spanCompIso F f g).app WalkingSpan.right = Iso.refl _ := rfl

@[simp]
/-
**CategoryTheory.Limits.spanCompIso_app_zero** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits`。
形式化陈述：spanCompIso_app_zero : (spanCompIso F f g).app WalkingSpan.zero = Iso.refl
 _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem spanCompIso_app_zero : (spanCompIso F f g).app WalkingSpan.zero = Iso.refl _ := rfl

@[simp]
/-
**CategoryTheory.Limits.spanCompIso_hom_app_left** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：spanCompIso_hom_app_left : (spanCompIso F f g).hom.app WalkingSpan.left = 
𝟙 _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem spanCompIso_hom_app_left : (spanCompIso F f g).hom.app WalkingSpan.left = 𝟙 _ := rfl

@[simp]
/-
**CategoryTheory.Limits.spanCompIso_hom_app_right** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：spanCompIso_hom_app_right : (spanCompIso F f g).hom.app WalkingSpan.right 
= 𝟙 _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem spanCompIso_hom_app_right : (spanCompIso F f g).hom.app WalkingSpan.right = 𝟙 _ := rfl

@[simp]
/-
**CategoryTheory.Limits.spanCompIso_hom_app_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：spanCompIso_hom_app_zero : (spanCompIso F f g).hom.app WalkingSpan.zero = 
𝟙 _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem spanCompIso_hom_app_zero : (spanCompIso F f g).hom.app WalkingSpan.zero = 𝟙 _ := rfl

@[simp]
/-
**CategoryTheory.Limits.spanCompIso_inv_app_left** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：spanCompIso_inv_app_left : (spanCompIso F f g).inv.app WalkingSpan.left = 
𝟙 _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem spanCompIso_inv_app_left : (spanCompIso F f g).inv.app WalkingSpan.left = 𝟙 _ := rfl

@[simp]
/-
**CategoryTheory.Limits.spanCompIso_inv_app_right** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：spanCompIso_inv_app_right : (spanCompIso F f g).inv.app WalkingSpan.right 
= 𝟙 _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem spanCompIso_inv_app_right : (spanCompIso F f g).inv.app WalkingSpan.right = 𝟙 _ := rfl

@[simp]
/-
**CategoryTheory.Limits.spanCompIso_inv_app_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：spanCompIso_inv_app_zero : (spanCompIso F f g).inv.app WalkingSpan.zero = 
𝟙 _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem spanCompIso_inv_app_zero : (spanCompIso F f g).inv.app WalkingSpan.zero = 𝟙 _ := rfl

end

section

variable {X Y Z X' Y' Z' : C} (iX : X ≅ X') (iY : Y ≅ Y') (iZ : Z ≅ Z')

section

set_option backward.isDefEq.respectTransparency.types false in
/-- Constructor for natural transformations between cospans. -/
@[simps]
/-
**CategoryTheory.Limits.cospanHomMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Li
mits`。
形式化陈述：cospanHomMk {F G : WalkingCospan ⥤ C} (z : F.obj .one ⟶ G.obj .one) (l : F
.obj .left ⟶ G.obj .left) (r : F.obj .right ⟶ G.obj .right) (hl : F.map inl ≫ z 
= l ≫ G.map inl
参数：z : F.obj .one ⟶ G.obj .one；l : F.obj .left ⟶ G.obj .left；r : F.obj .right ⟶ 
G.obj .right。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for natural transformations between cospans.
-/
def cospanHomMk {F G : WalkingCospan ⥤ C}
    (z : F.obj .one ⟶ G.obj .one) (l : F.obj .left ⟶ G.obj .left)
    (r : F.obj .right ⟶ G.obj .right)
    (hl : F.map inl ≫ z = l ≫ G.map inl := by cat_disch)
    (hr : F.map inr ≫ z = r ≫ G.map inr := by cat_disch) : F ⟶ G where
  app := by rintro (_ | _ | _); exacts [z, l, r]
  naturality := by rintro (_ | _ | _) (_ | _ | _) (_ | _); all_goals cat_disch

set_option backward.isDefEq.respectTransparency.types false in
/-- Constructor for natural isomorphisms between cospans. -/
@[simps!]
/-
**CategoryTheory.Limits.cospanIsoMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Li
mits`。
形式化陈述：cospanIsoMk {F G : WalkingCospan ⥤ C} (z : F.obj .one ≅ G.obj .one) (l : F
.obj .left ≅ G.obj .left) (r : F.obj .right ≅ G.obj .right) (hl : F.map inl ≫ z.
hom = l.hom ≫ G.map inl
参数：z : F.obj .one ≅ G.obj .one；l : F.obj .left ≅ G.obj .left；r : F.obj .right ≅ 
G.obj .right。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for natural isomorphisms between cospans.
-/
def cospanIsoMk {F G : WalkingCospan ⥤ C}
    (z : F.obj .one ≅ G.obj .one) (l : F.obj .left ≅ G.obj .left)
    (r : F.obj .right ≅ G.obj .right)
    (hl : F.map inl ≫ z.hom = l.hom ≫ G.map inl := by cat_disch)
    (hr : F.map inr ≫ z.hom = r.hom ≫ G.map inr := by cat_disch) : F ≅ G :=
  NatIso.ofComponents (by rintro (_ | _ | _); exacts [z, l, r])
    (by rintro (_ | _ | _) (_ | _ | _) (_ | _); all_goals cat_disch)

variable {f : X ⟶ Z} {g : Y ⟶ Z} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'}

/-- Construct an isomorphism of cospans from components. -/
/-
**CategoryTheory.Limits.cospanExt** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limi
ts`。
形式化陈述：cospanExt (wf : iX.hom ≫ f' = f ≫ iZ.hom) (wg : iY.hom ≫ g' = g ≫ iZ.hom) 
: cospan f g ≅ cospan f' g'
参数：wf : iX.hom ≫ f' = f ≫ iZ.hom；wg : iY.hom ≫ g' = g ≫ iZ.hom。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an isomorphism of cospans from components.
-/
def cospanExt (wf : iX.hom ≫ f' = f ≫ iZ.hom) (wg : iY.hom ≫ g' = g ≫ iZ.hom) :
    cospan f g ≅ cospan f' g' :=
  cospanIsoMk iZ iX iY

variable (wf : iX.hom ≫ f' = f ≫ iZ.hom) (wg : iY.hom ≫ g' = g ≫ iZ.hom)

@[simp]
/-
**CategoryTheory.Limits.cospanExt_app_left** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：cospanExt_app_left : (cospanExt iX iY iZ wf wg).app WalkingCospan.left = i
X
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cospanExt_app_left : (cospanExt iX iY iZ wf wg).app WalkingCospan.left = iX := rfl

@[simp]
/-
**CategoryTheory.Limits.cospanExt_app_right** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：cospanExt_app_right : (cospanExt iX iY iZ wf wg).app WalkingCospan.right =
 iY
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cospanExt_app_right : (cospanExt iX iY iZ wf wg).app WalkingCospan.right = iY := rfl

@[simp]
/-
**CategoryTheory.Limits.cospanExt_app_one** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：cospanExt_app_one : (cospanExt iX iY iZ wf wg).app WalkingCospan.one = iZ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cospanExt_app_one : (cospanExt iX iY iZ wf wg).app WalkingCospan.one = iZ := rfl

@[simp]
/-
**CategoryTheory.Limits.cospanExt_hom_app_left** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：cospanExt_hom_app_left : (cospanExt iX iY iZ wf wg).hom.app WalkingCospan.
left = iX.hom
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cospanExt_hom_app_left :
    (cospanExt iX iY iZ wf wg).hom.app WalkingCospan.left = iX.hom := rfl

@[simp]
/-
**CategoryTheory.Limits.cospanExt_hom_app_right** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：cospanExt_hom_app_right : (cospanExt iX iY iZ wf wg).hom.app WalkingCospan
.right = iY.hom
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cospanExt_hom_app_right :
    (cospanExt iX iY iZ wf wg).hom.app WalkingCospan.right = iY.hom := rfl

@[simp]
/-
**CategoryTheory.Limits.cospanExt_hom_app_one** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：cospanExt_hom_app_one : (cospanExt iX iY iZ wf wg).hom.app WalkingCospan.o
ne = iZ.hom
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cospanExt_hom_app_one : (cospanExt iX iY iZ wf wg).hom.app WalkingCospan.one = iZ.hom := rfl

@[simp]
/-
**CategoryTheory.Limits.cospanExt_inv_app_left** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：cospanExt_inv_app_left : (cospanExt iX iY iZ wf wg).inv.app WalkingCospan.
left = iX.inv
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cospanExt_inv_app_left :
    (cospanExt iX iY iZ wf wg).inv.app WalkingCospan.left = iX.inv := rfl

@[simp]
/-
**CategoryTheory.Limits.cospanExt_inv_app_right** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：cospanExt_inv_app_right : (cospanExt iX iY iZ wf wg).inv.app WalkingCospan
.right = iY.inv
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cospanExt_inv_app_right :
    (cospanExt iX iY iZ wf wg).inv.app WalkingCospan.right = iY.inv :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.cospanExt_inv_app_one** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：cospanExt_inv_app_one : (cospanExt iX iY iZ wf wg).inv.app WalkingCospan.o
ne = iZ.inv
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cospanExt_inv_app_one : (cospanExt iX iY iZ wf wg).inv.app WalkingCospan.one = iZ.inv := by
  rfl

end

section

set_option backward.isDefEq.respectTransparency.types false in
/-- Constructor for natural transformations between spans. -/
@[simps]
/-
**CategoryTheory.Limits.spanHomMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limi
ts`。
形式化陈述：spanHomMk {F G : WalkingSpan ⥤ C} (z : F.obj .zero ⟶ G.obj .zero) (l : F.o
bj .left ⟶ G.obj .left) (r : F.obj .right ⟶ G.obj .right) (hl : F.map fst ≫ l = 
z ≫ G.map fst
参数：z : F.obj .zero ⟶ G.obj .zero；l : F.obj .left ⟶ G.obj .left；r : F.obj .right 
⟶ G.obj .right。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for natural transformations between spans.
-/
def spanHomMk {F G : WalkingSpan ⥤ C}
    (z : F.obj .zero ⟶ G.obj .zero) (l : F.obj .left ⟶ G.obj .left)
    (r : F.obj .right ⟶ G.obj .right)
    (hl : F.map fst ≫ l = z ≫ G.map fst := by cat_disch)
    (hr : F.map snd ≫ r = z ≫ G.map snd := by cat_disch) : F ⟶ G where
  app := by rintro (_ | _ | _); exacts [z, l, r]
  naturality := by rintro (_ | _ | _) (_ | _ | _) (_ | _); all_goals cat_disch

set_option backward.isDefEq.respectTransparency.types false in
/-- Constructor for natural isomorphisms between spans. -/
@[simps!]
/-
**CategoryTheory.Limits.spanIsoMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limi
ts`。
形式化陈述：spanIsoMk {F G : WalkingSpan ⥤ C} (z : F.obj .zero ≅ G.obj .zero) (l : F.o
bj .left ≅ G.obj .left) (r : F.obj .right ≅ G.obj .right) (hl : F.map fst ≫ l.ho
m = z.hom ≫ G.map fst
参数：z : F.obj .zero ≅ G.obj .zero；l : F.obj .left ≅ G.obj .left；r : F.obj .right 
≅ G.obj .right。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for natural isomorphisms between spans.
-/
def spanIsoMk {F G : WalkingSpan ⥤ C}
    (z : F.obj .zero ≅ G.obj .zero) (l : F.obj .left ≅ G.obj .left)
    (r : F.obj .right ≅ G.obj .right)
    (hl : F.map fst ≫ l.hom = z.hom ≫ G.map fst := by cat_disch)
    (hr : F.map snd ≫ r.hom = z.hom ≫ G.map snd := by cat_disch) : F ≅ G :=
  NatIso.ofComponents (by rintro (_ | _ | _); exacts [z, l, r])
    (by rintro (_ | _ | _) (_ | _ | _) (_ | _); all_goals cat_disch)

variable {f : X ⟶ Y} {g : X ⟶ Z} {f' : X' ⟶ Y'} {g' : X' ⟶ Z'}

/-- Construct an isomorphism of spans from components. -/
/-
**CategoryTheory.Limits.spanExt** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits
`。
形式化陈述：spanExt (wf : iX.hom ≫ f' = f ≫ iY.hom) (wg : iX.hom ≫ g' = g ≫ iZ.hom) : 
span f g ≅ span f' g'
参数：wf : iX.hom ≫ f' = f ≫ iY.hom；wg : iX.hom ≫ g' = g ≫ iZ.hom。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an isomorphism of spans from components.
-/
def spanExt (wf : iX.hom ≫ f' = f ≫ iY.hom) (wg : iX.hom ≫ g' = g ≫ iZ.hom) :
    span f g ≅ span f' g' :=
  spanIsoMk iX iY iZ

variable (wf : iX.hom ≫ f' = f ≫ iY.hom) (wg : iX.hom ≫ g' = g ≫ iZ.hom)

@[simp]
/-
**CategoryTheory.Limits.spanExt_app_left** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits`。
形式化陈述：spanExt_app_left : (spanExt iX iY iZ wf wg).app WalkingSpan.left = iY
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem spanExt_app_left : (spanExt iX iY iZ wf wg).app WalkingSpan.left = iY := rfl

@[simp]
/-
**CategoryTheory.Limits.spanExt_app_right** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：spanExt_app_right : (spanExt iX iY iZ wf wg).app WalkingSpan.right = iZ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem spanExt_app_right : (spanExt iX iY iZ wf wg).app WalkingSpan.right = iZ := rfl

@[simp]
/-
**CategoryTheory.Limits.spanExt_app_one** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits`。
形式化陈述：spanExt_app_one : (spanExt iX iY iZ wf wg).app WalkingSpan.zero = iX
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem spanExt_app_one : (spanExt iX iY iZ wf wg).app WalkingSpan.zero = iX := rfl

@[simp]
/-
**CategoryTheory.Limits.spanExt_hom_app_left** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits`。
形式化陈述：spanExt_hom_app_left : (spanExt iX iY iZ wf wg).hom.app WalkingSpan.left =
 iY.hom
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem spanExt_hom_app_left : (spanExt iX iY iZ wf wg).hom.app WalkingSpan.left = iY.hom := rfl

@[simp]
/-
**CategoryTheory.Limits.spanExt_hom_app_right** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：spanExt_hom_app_right : (spanExt iX iY iZ wf wg).hom.app WalkingSpan.right
 = iZ.hom
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem spanExt_hom_app_right : (spanExt iX iY iZ wf wg).hom.app WalkingSpan.right = iZ.hom := rfl

@[simp]
/-
**CategoryTheory.Limits.spanExt_hom_app_zero** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits`。
形式化陈述：spanExt_hom_app_zero : (spanExt iX iY iZ wf wg).hom.app WalkingSpan.zero =
 iX.hom
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem spanExt_hom_app_zero : (spanExt iX iY iZ wf wg).hom.app WalkingSpan.zero = iX.hom := rfl

@[simp]
/-
**CategoryTheory.Limits.spanExt_inv_app_left** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits`。
形式化陈述：spanExt_inv_app_left : (spanExt iX iY iZ wf wg).inv.app WalkingSpan.left =
 iY.inv
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem spanExt_inv_app_left : (spanExt iX iY iZ wf wg).inv.app WalkingSpan.left = iY.inv := rfl

@[simp]
/-
**CategoryTheory.Limits.spanExt_inv_app_right** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：spanExt_inv_app_right : (spanExt iX iY iZ wf wg).inv.app WalkingSpan.right
 = iZ.inv
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem spanExt_inv_app_right : (spanExt iX iY iZ wf wg).inv.app WalkingSpan.right = iZ.inv := rfl

@[simp]
/-
**CategoryTheory.Limits.spanExt_inv_app_zero** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits`。
形式化陈述：spanExt_inv_app_zero : (spanExt iX iY iZ wf wg).inv.app WalkingSpan.zero =
 iX.inv
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem spanExt_inv_app_zero : (spanExt iX iY iZ wf wg).inv.app WalkingSpan.zero = iX.inv := rfl

end

end

end CategoryTheory.Limits

