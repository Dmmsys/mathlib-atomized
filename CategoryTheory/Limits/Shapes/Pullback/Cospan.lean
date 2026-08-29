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

/--
Definition of `WalkingCospan` / `WalkingCospan` 的定义

English:
abbreviation WalkingCospan
  signature: : Type
  body: WidePullbackShape WalkingPair

中文:
缩写 WalkingCospan
  签名: : 类型
  定义体: WidePullbackShape WalkingPair

Depends on / 依赖: F.map, W.of_postcomp, WalkingPair, WidePullbackShape, of_postcomp
-/
abbrev WalkingCospan : Type :=
  WidePullbackShape WalkingPair

/-- The left point of the walking cospan. -/
@[match_pattern]
/--
Definition of `WalkingCospan.left` / `WalkingCospan.left` 的定义

English:
abbreviation WalkingCospan.left
  signature: : WalkingCospan
  body: some WalkingPair.left

中文:
缩写 WalkingCospan.left
  签名: : WalkingCospan
  定义体: some WalkingPair.left

Depends on / 依赖: WalkingPair, WalkingPair.left
-/
abbrev WalkingCospan.left : WalkingCospan :=
  some WalkingPair.left

/-- The right point of the walking cospan. -/
@[match_pattern]
/--
Definition of `WalkingCospan.right` / `WalkingCospan.right` 的定义

English:
abbreviation WalkingCospan.right
  signature: : WalkingCospan
  body: some WalkingPair.right

中文:
缩写 WalkingCospan.right
  签名: : WalkingCospan
  定义体: some WalkingPair.right

Depends on / 依赖: WalkingPair, WalkingPair.right
-/
abbrev WalkingCospan.right : WalkingCospan :=
  some WalkingPair.right

/-- The central point of the walking cospan. -/
@[match_pattern]
/--
Definition of `WalkingCospan.one` / `WalkingCospan.one` 的定义

English:
abbreviation WalkingCospan.one
  signature: : WalkingCospan
  body: none

中文:
缩写 WalkingCospan.one
  签名: : WalkingCospan
  定义体: none
-/
abbrev WalkingCospan.one : WalkingCospan :=
  none

/--
Definition of `WalkingSpan` / `WalkingSpan` 的定义

English:
abbreviation WalkingSpan
  signature: : Type
  body: WidePushoutShape WalkingPair

中文:
缩写 WalkingSpan
  签名: : 类型
  定义体: WidePushoutShape WalkingPair

Depends on / 依赖: WalkingPair, WidePushoutShape
-/
abbrev WalkingSpan : Type :=
  WidePushoutShape WalkingPair

/-- The left point of the walking span. -/
@[match_pattern]
/--
Definition of `WalkingSpan.left` / `WalkingSpan.left` 的定义

English:
abbreviation WalkingSpan.left
  signature: : WalkingSpan
  body: some WalkingPair.left

中文:
缩写 WalkingSpan.left
  签名: : WalkingSpan
  定义体: some WalkingPair.left

Depends on / 依赖: WalkingPair, WalkingPair.left
-/
abbrev WalkingSpan.left : WalkingSpan :=
  some WalkingPair.left

/-- The right point of the walking span. -/
@[match_pattern]
/--
Definition of `WalkingSpan.right` / `WalkingSpan.right` 的定义

English:
abbreviation WalkingSpan.right
  signature: : WalkingSpan
  body: some WalkingPair.right

中文:
缩写 WalkingSpan.right
  签名: : WalkingSpan
  定义体: some WalkingPair.right

Depends on / 依赖: WalkingPair, WalkingPair.right
-/
abbrev WalkingSpan.right : WalkingSpan :=
  some WalkingPair.right

/-- The central point of the walking span. -/
@[match_pattern]
/--
Definition of `WalkingSpan.zero` / `WalkingSpan.zero` 的定义

English:
abbreviation WalkingSpan.zero
  signature: : WalkingSpan
  body: none

中文:
缩写 WalkingSpan.zero
  签名: : WalkingSpan
  定义体: none
-/
abbrev WalkingSpan.zero : WalkingSpan :=
  none

namespace WalkingCospan

/--
Definition of `Hom` / `Hom` 的定义

English:
abbreviation Hom
  signature: : WalkingCospan -> WalkingCospan -> Type
  body: WidePullbackShape.Hom

中文:
缩写 态射
  签名: : WalkingCospan -> WalkingCospan -> 类型
  定义体: WidePullbackShape.Hom

Depends on / 依赖: WidePullbackShape, WidePullbackShape.Hom
-/
abbrev Hom : WalkingCospan -> WalkingCospan -> Type :=
  WidePullbackShape.Hom

/-- The left arrow of the walking cospan. -/
@[match_pattern]
/--
Definition of `Hom.inl` / `Hom.inl` 的定义

English:
abbreviation Hom.inl
  signature: : left ⟶ one
  body: WidePullbackShape.Hom.term _

中文:
缩写 态射.inl
  签名: : left ⟶ one
  定义体: WidePullbackShape.Hom.term _

Depends on / 依赖: WidePullbackShape, WidePullbackShape.Hom.term
-/
abbrev Hom.inl : left ⟶ one :=
  WidePullbackShape.Hom.term _

/-- The right arrow of the walking cospan. -/
@[match_pattern]
/--
Definition of `Hom.inr` / `Hom.inr` 的定义

English:
abbreviation Hom.inr
  signature: : right ⟶ one
  body: WidePullbackShape.Hom.term _

中文:
缩写 态射.inr
  签名: : right ⟶ one
  定义体: WidePullbackShape.Hom.term _

Depends on / 依赖: WidePullbackShape, WidePullbackShape.Hom.term
-/
abbrev Hom.inr : right ⟶ one :=
  WidePullbackShape.Hom.term _

/-- The identity arrows of the walking cospan. -/
@[match_pattern]
/--
Definition of `Hom.id` / `Hom.id` 的定义

English:
abbreviation Hom.id
  signature: (X : WalkingCospan)
  body: WidePullbackShape.Hom.id X

中文:
缩写 态射.id
  签名: (X : WalkingCospan)
  定义体: WidePullbackShape.Hom.id X
-/
abbrev Hom.id (X : WalkingCospan) : X ⟶ X :=
  WidePullbackShape.Hom.id X

instance (X Y : WalkingCospan) : Subsingleton (X ⟶ Y) := by
  constructor; intros; simp [eq_iff_true_of_subsingleton]

end WalkingCospan

namespace WalkingSpan

/--
Definition of `Hom` / `Hom` 的定义

English:
abbreviation Hom
  signature: : WalkingSpan -> WalkingSpan -> Type
  body: WidePushoutShape.Hom

中文:
缩写 态射
  签名: : WalkingSpan -> WalkingSpan -> 类型
  定义体: WidePushoutShape.Hom

Depends on / 依赖: WidePushoutShape, WidePushoutShape.Hom
-/
abbrev Hom : WalkingSpan -> WalkingSpan -> Type :=
  WidePushoutShape.Hom

/-- The left arrow of the walking span. -/
@[match_pattern]
/--
Definition of `Hom.fst` / `Hom.fst` 的定义

English:
abbreviation Hom.fst
  signature: : zero ⟶ left
  body: WidePushoutShape.Hom.init _

中文:
缩写 态射.fst
  签名: : zero ⟶ left
  定义体: WidePushoutShape.Hom.init _

Depends on / 依赖: WidePushoutShape, WidePushoutShape.Hom.init
-/
abbrev Hom.fst : zero ⟶ left :=
  WidePushoutShape.Hom.init _

/-- The right arrow of the walking span. -/
@[match_pattern]
/--
Definition of `Hom.snd` / `Hom.snd` 的定义

English:
abbreviation Hom.snd
  signature: : zero ⟶ right
  body: WidePushoutShape.Hom.init _

中文:
缩写 态射.snd
  签名: : zero ⟶ right
  定义体: WidePushoutShape.Hom.init _

Depends on / 依赖: WidePushoutShape, WidePushoutShape.Hom.init
-/
abbrev Hom.snd : zero ⟶ right :=
  WidePushoutShape.Hom.init _

/-- The identity arrows of the walking span. -/
@[match_pattern]
/--
Definition of `Hom.id` / `Hom.id` 的定义

English:
abbreviation Hom.id
  signature: (X : WalkingSpan)
  body: WidePushoutShape.Hom.id X

中文:
缩写 态射.id
  签名: (X : WalkingSpan)
  定义体: WidePushoutShape.Hom.id X
-/
abbrev Hom.id (X : WalkingSpan) : X ⟶ X :=
  WidePushoutShape.Hom.id X

instance (X Y : WalkingSpan) : Subsingleton (X ⟶ Y) := by
  constructor; intro a b; simp [eq_iff_true_of_subsingleton]

end WalkingSpan

open WalkingSpan.Hom WalkingCospan.Hom WidePullbackShape.Hom WidePushoutShape.Hom

variable {C : Type u} [Category.{v} C]

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `WalkingCospan.ext` / `WalkingCospan.ext` 的定义

English:
definition WalkingCospan.ext
  signature: {F : WalkingCospan ⥤ C} {s t : Cone F} (i : s.pt ≅ t.pt)
  body: by
  apply Cone.ext i _
  rintro (⟨⟩ | ⟨⟨⟩⟩)
  · have h₁ := s.π.naturality WalkingCospan.Hom.inl
    dsimp at h₁
    simp only [Category.id_comp] at h₁
    have h₂ := t.π.naturality WalkingCospan.Hom.inl
    dsimp at h₂
    simp only [Category.id_comp] at h₂
    simp_rw [h₂, ← Category.assoc, ← w₁, 

中文:
定义 WalkingCospan.ext
  签名: {F : WalkingCospan ⥤ C} {s t : 锥 F} (i : s.pt ≅ t.pt)
  定义体: by
  apply Cone.ext i _
  rintro (⟨⟩ | ⟨⟨⟩⟩)
  · have h₁ := s.π.naturality WalkingCospan.Hom.inl
    dsimp at h₁
    simp only [Category.id_comp] at h₁
    have h₂ := t.π.naturality WalkingCospan.Hom.inl
    dsimp at h₂
    simp only [Category.id_comp] at h₂
    simp_rw [h₂, ← Category.assoc, ← w₁, 

Depends on / 依赖: Category, Category.assoc, Category.id_comp, Cone.ext, WalkingCospan, WalkingCospan.Hom.inl, id_comp, naturality, simp_rw
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
/--
Definition of `WalkingSpan.ext` / `WalkingSpan.ext` 的定义

English:
definition WalkingSpan.ext
  signature: {F : WalkingSpan ⥤ C} {s t : Cocone F} (i : s.pt ≅ t.pt)
  body: by
  apply Cocone.ext i _
  rintro (⟨⟩ | ⟨⟨⟩⟩)
  · have h₁ := s.ι.naturality WalkingSpan.Hom.fst
    dsimp at h₁
    simp only [Category.comp_id] at h₁
    have h₂ := t.ι.naturality WalkingSpan.Hom.fst
    dsimp at h₂
    simp only [Category.comp_id] at h₂
    simp_rw [← h₁, Category.assoc, w₁, h₂]


中文:
定义 WalkingSpan.ext
  签名: {F : WalkingSpan ⥤ C} {s t : 余锥 F} (i : s.pt ≅ t.pt)
  定义体: by
  apply Cocone.ext i _
  rintro (⟨⟩ | ⟨⟨⟩⟩)
  · have h₁ := s.ι.naturality WalkingSpan.Hom.fst
    dsimp at h₁
    simp only [Category.comp_id] at h₁
    have h₂ := t.ι.naturality WalkingSpan.Hom.fst
    dsimp at h₂
    simp only [Category.comp_id] at h₂
    simp_rw [← h₁, Category.assoc, w₁, h₂]


Depends on / 依赖: Category, Category.assoc, Category.comp_id, Cocone, Cocone.ext, WalkingSpan, WalkingSpan.Hom.fst, comp_id, naturality, simp_rw
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
/--
Definition of `cospan` / `cospan` 的定义

English:
definition cospan
  signature: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  body: WidePullbackShape.wideCospan Z (fun j => WalkingPair.casesOn j X Y) fun j =>
    WalkingPair.casesOn j f g

中文:
定义 cospan
  签名: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  定义体: WidePullbackShape.wideCospan Z (fun j => WalkingPair.casesOn j X Y) fun j =>
    WalkingPair.casesOn j f g

Depends on / 依赖: WalkingPair, WalkingPair.casesOn, WidePullbackShape, WidePullbackShape.wideCospan, casesOn, wideCospan
-/
def cospan {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : WalkingCospan ⥤ C :=
  WidePullbackShape.wideCospan Z (fun j => WalkingPair.casesOn j X Y) fun j =>
    WalkingPair.casesOn j f g

/-- `span f g` is the functor from the walking span hitting `f` and `g`. -/
@[implicit_reducible]
/--
Definition of `span` / `span` 的定义

English:
definition span
  signature: {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)
  body: WidePushoutShape.wideSpan X (fun j => WalkingPair.casesOn j Y Z) fun j =>
    WalkingPair.casesOn j f g

@[simp]

中文:
定义 span
  签名: {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)
  定义体: WidePushoutShape.wideSpan X (fun j => WalkingPair.casesOn j Y Z) fun j =>
    WalkingPair.casesOn j f g

@[simp]

Depends on / 依赖: WalkingPair, WalkingPair.casesOn, WidePushoutShape, WidePushoutShape.wideSpan, casesOn, wideSpan
-/
def span {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : WalkingSpan ⥤ C :=
  WidePushoutShape.wideSpan X (fun j => WalkingPair.casesOn j Y Z) fun j =>
    WalkingPair.casesOn j f g

@[simp]
/--
theorem `cospan_left` / 定理 `cospan_left`

English:
theorem cospan_left
  given: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  statement: (cospan f g).obj WalkingCospan.left = X
  proof: rfl

@[simp]

中文:
定理 cospan_left
  条件: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  结论: (cospan f g).obj WalkingCospan.left = X
  证明: rfl

@[simp]
-/
theorem cospan_left {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : (cospan f g).obj WalkingCospan.left = X :=
  rfl

@[simp]
/--
theorem `span_left` / 定理 `span_left`

English:
theorem span_left
  given: {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)
  statement: (span f g).obj WalkingSpan.left = Y
  proof: rfl

@[simp]

中文:
定理 span_left
  条件: {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)
  结论: (span f g).obj WalkingSpan.left = Y
  证明: rfl

@[simp]
-/
theorem span_left {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : (span f g).obj WalkingSpan.left = Y :=
  rfl

@[simp]
/--
theorem `cospan_right` / 定理 `cospan_right`

English:
theorem cospan_right
  given: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  proof: rfl

@[simp]

中文:
定理 cospan_right
  条件: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  证明: rfl

@[simp]
-/
theorem cospan_right {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (cospan f g).obj WalkingCospan.right = Y := rfl

@[simp]
/--
theorem `span_right` / 定理 `span_right`

English:
theorem span_right
  given: {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)
  statement: (span f g).obj WalkingSpan.right = Z
  proof: rfl

@[simp]

中文:
定理 span_right
  条件: {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)
  结论: (span f g).obj WalkingSpan.right = Z
  证明: rfl

@[simp]
-/
theorem span_right {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : (span f g).obj WalkingSpan.right = Z :=
  rfl

@[simp]
/--
theorem `cospan_one` / 定理 `cospan_one`

English:
theorem cospan_one
  given: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  statement: (cospan f g).obj WalkingCospan.one = Z
  proof: rfl

@[simp]

中文:
定理 cospan_one
  条件: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  结论: (cospan f g).obj WalkingCospan.one = Z
  证明: rfl

@[simp]
-/
theorem cospan_one {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : (cospan f g).obj WalkingCospan.one = Z :=
  rfl

@[simp]
/--
theorem `span_zero` / 定理 `span_zero`

English:
theorem span_zero
  given: {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)
  statement: (span f g).obj WalkingSpan.zero = X
  proof: rfl

@[simp]

中文:
定理 span_zero
  条件: {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)
  结论: (span f g).obj WalkingSpan.zero = X
  证明: rfl

@[simp]
-/
theorem span_zero {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : (span f g).obj WalkingSpan.zero = X :=
  rfl

@[simp]
/--
theorem `cospan_map_inl` / 定理 `cospan_map_inl`

English:
theorem cospan_map_inl
  given: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  proof: rfl

@[simp]

中文:
定理 cospan_map_inl
  条件: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  证明: rfl

@[simp]
-/
theorem cospan_map_inl {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (cospan f g).map WalkingCospan.Hom.inl = f := rfl

@[simp]
/--
theorem `span_map_fst` / 定理 `span_map_fst`

English:
theorem span_map_fst
  given: {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)
  statement: (span f g).map WalkingSpan.Hom.fst = f
  proof: rfl

@[simp]

中文:
定理 span_map_fst
  条件: {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)
  结论: (span f g).map WalkingSpan.态射.fst = f
  证明: rfl

@[simp]
-/
theorem span_map_fst {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : (span f g).map WalkingSpan.Hom.fst = f :=
  rfl

@[simp]
/--
theorem `cospan_map_inr` / 定理 `cospan_map_inr`

English:
theorem cospan_map_inr
  given: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  proof: rfl

@[simp]

中文:
定理 cospan_map_inr
  条件: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  证明: rfl

@[simp]
-/
theorem cospan_map_inr {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (cospan f g).map WalkingCospan.Hom.inr = g := rfl

@[simp]
/--
theorem `span_map_snd` / 定理 `span_map_snd`

English:
theorem span_map_snd
  given: {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)
  statement: (span f g).map WalkingSpan.Hom.snd = g
  proof: rfl

中文:
定理 span_map_snd
  条件: {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)
  结论: (span f g).map WalkingSpan.态射.snd = g
  证明: rfl
-/
theorem span_map_snd {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : (span f g).map WalkingSpan.Hom.snd = g :=
  rfl

/--
theorem `cospan_map_id` / 定理 `cospan_map_id`

English:
theorem cospan_map_id
  given: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (w : WalkingCospan)
  proof: rfl

中文:
定理 cospan_map_id
  条件: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (w : WalkingCospan)
  证明: rfl
-/
theorem cospan_map_id {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (w : WalkingCospan) :
    (cospan f g).map (WalkingCospan.Hom.id w) = 𝟙 _ := rfl

/--
theorem `span_map_id` / 定理 `span_map_id`

English:
theorem span_map_id
  given: {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) (w : WalkingSpan)
  proof: rfl

中文:
定理 span_map_id
  条件: {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) (w : WalkingSpan)
  证明: rfl
-/
theorem span_map_id {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) (w : WalkingSpan) :
    (span f g).map (WalkingSpan.Hom.id w) = 𝟙 _ := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Every diagram indexing a pullback is naturally isomorphic (actually, equal) to a `cospan` -/
@[simps (rhsMd := default)]
/--
Definition of `diagramIsoCospan` / `diagramIsoCospan` 的定义

English:
definition diagramIsoCospan
  signature: (F : WalkingCospan ⥤ C)
  body: NatIso.ofComponents
  (fun j => eqToIso (by rcases j with (⟨⟩ | ⟨⟨⟩⟩) <;> rfl))
  (by rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) f <;> cases f <;> simp)

中文:
定义 diagramIsoCospan
  签名: (F : WalkingCospan ⥤ C)
  定义体: NatIso.ofComponents
  (fun j => eqToIso (by rcases j with (⟨⟩ | ⟨⟨⟩⟩) <;> rfl))
  (by rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) f <;> cases f <;> simp)

Depends on / 依赖: NatIso, NatIso.ofComponents, eqToIso, ofComponents
-/
def diagramIsoCospan (F : WalkingCospan ⥤ C) : F ≅ cospan (F.map inl) (F.map inr) :=
  NatIso.ofComponents
  (fun j => eqToIso (by rcases j with (⟨⟩ | ⟨⟨⟩⟩) <;> rfl))
  (by rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) f <;> cases f <;> simp)

set_option backward.isDefEq.respectTransparency.types false in
/-- Every diagram indexing a pushout is naturally isomorphic (actually, equal) to a `span` -/
@[simps (rhsMd := default)]
/--
Definition of `diagramIsoSpan` / `diagramIsoSpan` 的定义

English:
definition diagramIsoSpan
  signature: (F : WalkingSpan ⥤ C)
  body: NatIso.ofComponents
  (fun j => eqToIso (by rcases j with (⟨⟩ | ⟨⟨⟩⟩) <;> rfl))
  (by rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) f <;> cases f <;> simp)

中文:
定义 diagramIsoSpan
  签名: (F : WalkingSpan ⥤ C)
  定义体: NatIso.ofComponents
  (fun j => eqToIso (by rcases j with (⟨⟩ | ⟨⟨⟩⟩) <;> rfl))
  (by rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) f <;> cases f <;> simp)

Depends on / 依赖: NatIso, NatIso.ofComponents, eqToIso, ofComponents
-/
def diagramIsoSpan (F : WalkingSpan ⥤ C) : F ≅ span (F.map fst) (F.map snd) :=
  NatIso.ofComponents
  (fun j => eqToIso (by rcases j with (⟨⟩ | ⟨⟨⟩⟩) <;> rfl))
  (by rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) f <;> cases f <;> simp)

variable {D : Type u₂} [Category.{v₂} D]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `cospanCompIso` / `cospanCompIso` 的定义

English:
definition cospanCompIso
  signature: (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  body: NatIso.ofComponents (by rintro (⟨⟩ | ⟨⟨⟩⟩) <;> exact Iso.refl _)
    (by rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) f <;> cases f <;> simp)

中文:
定义 cospanCompIso
  签名: (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  定义体: NatIso.ofComponents (by rintro (⟨⟩ | ⟨⟨⟩⟩) <;> exact Iso.refl _)
    (by rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) f <;> cases f <;> simp)

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def cospanCompIso (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    cospan f g ⋙ F ≅ cospan (F.map f) (F.map g) :=
  NatIso.ofComponents (by rintro (⟨⟩ | ⟨⟨⟩⟩) <;> exact Iso.refl _)
    (by rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) f <;> cases f <;> simp)

section

variable (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)

@[simp]
/--
theorem `cospanCompIso_app_left` / 定理 `cospanCompIso_app_left`

English:
theorem cospanCompIso_app_left
  statement: (cospanCompIso F f g).app WalkingCospan.left = Iso.refl _
  proof: rfl

@[simp]

中文:
定理 cospanCompIso_app_left
  结论: (cospanCompIso F f g).app WalkingCospan.left = 同构.refl _
  证明: rfl

@[simp]
-/
theorem cospanCompIso_app_left : (cospanCompIso F f g).app WalkingCospan.left = Iso.refl _ := rfl

@[simp]
/--
theorem `cospanCompIso_app_right` / 定理 `cospanCompIso_app_right`

English:
theorem cospanCompIso_app_right
  statement: (cospanCompIso F f g).app WalkingCospan.right = Iso.refl _
  proof: rfl

@[simp]

中文:
定理 cospanCompIso_app_right
  结论: (cospanCompIso F f g).app WalkingCospan.right = 同构.refl _
  证明: rfl

@[simp]
-/
theorem cospanCompIso_app_right : (cospanCompIso F f g).app WalkingCospan.right = Iso.refl _ :=
  rfl

@[simp]
/--
theorem `cospanCompIso_app_one` / 定理 `cospanCompIso_app_one`

English:
theorem cospanCompIso_app_one
  statement: (cospanCompIso F f g).app WalkingCospan.one = Iso.refl _
  proof: rfl

@[simp]

中文:
定理 cospanCompIso_app_one
  结论: (cospanCompIso F f g).app WalkingCospan.one = 同构.refl _
  证明: rfl

@[simp]
-/
theorem cospanCompIso_app_one : (cospanCompIso F f g).app WalkingCospan.one = Iso.refl _ := rfl

@[simp]
/--
theorem `cospanCompIso_hom_app_left` / 定理 `cospanCompIso_hom_app_left`

English:
theorem cospanCompIso_hom_app_left
  statement: (cospanCompIso F f g).hom.app WalkingCospan.left = 𝟙 _
  proof: rfl

@[simp]

中文:
定理 cospanCompIso_hom_app_left
  结论: (cospanCompIso F f g).hom.app WalkingCospan.left = 𝟙 _
  证明: rfl

@[simp]
-/
theorem cospanCompIso_hom_app_left : (cospanCompIso F f g).hom.app WalkingCospan.left = 𝟙 _ :=
  rfl

@[simp]
/--
theorem `cospanCompIso_hom_app_right` / 定理 `cospanCompIso_hom_app_right`

English:
theorem cospanCompIso_hom_app_right
  statement: (cospanCompIso F f g).hom.app WalkingCospan.right = 𝟙 _
  proof: rfl

@[simp]

中文:
定理 cospanCompIso_hom_app_right
  结论: (cospanCompIso F f g).hom.app WalkingCospan.right = 𝟙 _
  证明: rfl

@[simp]
-/
theorem cospanCompIso_hom_app_right : (cospanCompIso F f g).hom.app WalkingCospan.right = 𝟙 _ :=
  rfl

@[simp]
/--
theorem `cospanCompIso_hom_app_one` / 定理 `cospanCompIso_hom_app_one`

English:
theorem cospanCompIso_hom_app_one
  statement: (cospanCompIso F f g).hom.app WalkingCospan.one = 𝟙 _
  proof: rfl

@[simp]

中文:
定理 cospanCompIso_hom_app_one
  结论: (cospanCompIso F f g).hom.app WalkingCospan.one = 𝟙 _
  证明: rfl

@[simp]
-/
theorem cospanCompIso_hom_app_one : (cospanCompIso F f g).hom.app WalkingCospan.one = 𝟙 _ := rfl

@[simp]
/--
theorem `cospanCompIso_inv_app_left` / 定理 `cospanCompIso_inv_app_left`

English:
theorem cospanCompIso_inv_app_left
  statement: (cospanCompIso F f g).inv.app WalkingCospan.left = 𝟙 _
  proof: rfl

@[simp]

中文:
定理 cospanCompIso_inv_app_left
  结论: (cospanCompIso F f g).inv.app WalkingCospan.left = 𝟙 _
  证明: rfl

@[simp]
-/
theorem cospanCompIso_inv_app_left : (cospanCompIso F f g).inv.app WalkingCospan.left = 𝟙 _ :=
  rfl

@[simp]
/--
theorem `cospanCompIso_inv_app_right` / 定理 `cospanCompIso_inv_app_right`

English:
theorem cospanCompIso_inv_app_right
  statement: (cospanCompIso F f g).inv.app WalkingCospan.right = 𝟙 _
  proof: rfl

@[simp]

中文:
定理 cospanCompIso_inv_app_right
  结论: (cospanCompIso F f g).inv.app WalkingCospan.right = 𝟙 _
  证明: rfl

@[simp]
-/
theorem cospanCompIso_inv_app_right : (cospanCompIso F f g).inv.app WalkingCospan.right = 𝟙 _ :=
  rfl

@[simp]
/--
theorem `cospanCompIso_inv_app_one` / 定理 `cospanCompIso_inv_app_one`

English:
theorem cospanCompIso_inv_app_one
  statement: (cospanCompIso F f g).inv.app WalkingCospan.one = 𝟙 _
  proof: rfl

中文:
定理 cospanCompIso_inv_app_one
  结论: (cospanCompIso F f g).inv.app WalkingCospan.one = 𝟙 _
  证明: rfl
-/
theorem cospanCompIso_inv_app_one : (cospanCompIso F f g).inv.app WalkingCospan.one = 𝟙 _ := rfl

end

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `spanCompIso` / `spanCompIso` 的定义

English:
definition spanCompIso
  signature: (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)
  body: NatIso.ofComponents (by rintro (⟨⟩ | ⟨⟨⟩⟩) <;> exact Iso.refl _)
    (by rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) f <;> cases f <;> simp)

中文:
定义 spanCompIso
  签名: (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)
  定义体: NatIso.ofComponents (by rintro (⟨⟩ | ⟨⟨⟩⟩) <;> exact Iso.refl _)
    (by rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) f <;> cases f <;> simp)

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def spanCompIso (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
    span f g ⋙ F ≅ span (F.map f) (F.map g) :=
  NatIso.ofComponents (by rintro (⟨⟩ | ⟨⟨⟩⟩) <;> exact Iso.refl _)
    (by rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) f <;> cases f <;> simp)

section

variable (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)

@[simp]
/--
theorem `spanCompIso_app_left` / 定理 `spanCompIso_app_left`

English:
theorem spanCompIso_app_left
  statement: (spanCompIso F f g).app WalkingSpan.left = Iso.refl _
  proof: rfl

@[simp]

中文:
定理 spanCompIso_app_left
  结论: (spanCompIso F f g).app WalkingSpan.left = 同构.refl _
  证明: rfl

@[simp]
-/
theorem spanCompIso_app_left : (spanCompIso F f g).app WalkingSpan.left = Iso.refl _ := rfl

@[simp]
/--
theorem `spanCompIso_app_right` / 定理 `spanCompIso_app_right`

English:
theorem spanCompIso_app_right
  statement: (spanCompIso F f g).app WalkingSpan.right = Iso.refl _
  proof: rfl

@[simp]

中文:
定理 spanCompIso_app_right
  结论: (spanCompIso F f g).app WalkingSpan.right = 同构.refl _
  证明: rfl

@[simp]
-/
theorem spanCompIso_app_right : (spanCompIso F f g).app WalkingSpan.right = Iso.refl _ := rfl

@[simp]
/--
theorem `spanCompIso_app_zero` / 定理 `spanCompIso_app_zero`

English:
theorem spanCompIso_app_zero
  statement: (spanCompIso F f g).app WalkingSpan.zero = Iso.refl _
  proof: rfl

@[simp]

中文:
定理 spanCompIso_app_zero
  结论: (spanCompIso F f g).app WalkingSpan.zero = 同构.refl _
  证明: rfl

@[simp]
-/
theorem spanCompIso_app_zero : (spanCompIso F f g).app WalkingSpan.zero = Iso.refl _ := rfl

@[simp]
/--
theorem `spanCompIso_hom_app_left` / 定理 `spanCompIso_hom_app_left`

English:
theorem spanCompIso_hom_app_left
  statement: (spanCompIso F f g).hom.app WalkingSpan.left = 𝟙 _
  proof: rfl

@[simp]

中文:
定理 spanCompIso_hom_app_left
  结论: (spanCompIso F f g).hom.app WalkingSpan.left = 𝟙 _
  证明: rfl

@[simp]
-/
theorem spanCompIso_hom_app_left : (spanCompIso F f g).hom.app WalkingSpan.left = 𝟙 _ := rfl

@[simp]
/--
theorem `spanCompIso_hom_app_right` / 定理 `spanCompIso_hom_app_right`

English:
theorem spanCompIso_hom_app_right
  statement: (spanCompIso F f g).hom.app WalkingSpan.right = 𝟙 _
  proof: rfl

@[simp]

中文:
定理 spanCompIso_hom_app_right
  结论: (spanCompIso F f g).hom.app WalkingSpan.right = 𝟙 _
  证明: rfl

@[simp]
-/
theorem spanCompIso_hom_app_right : (spanCompIso F f g).hom.app WalkingSpan.right = 𝟙 _ := rfl

@[simp]
/--
theorem `spanCompIso_hom_app_zero` / 定理 `spanCompIso_hom_app_zero`

English:
theorem spanCompIso_hom_app_zero
  statement: (spanCompIso F f g).hom.app WalkingSpan.zero = 𝟙 _
  proof: rfl

@[simp]

中文:
定理 spanCompIso_hom_app_zero
  结论: (spanCompIso F f g).hom.app WalkingSpan.zero = 𝟙 _
  证明: rfl

@[simp]
-/
theorem spanCompIso_hom_app_zero : (spanCompIso F f g).hom.app WalkingSpan.zero = 𝟙 _ := rfl

@[simp]
/--
theorem `spanCompIso_inv_app_left` / 定理 `spanCompIso_inv_app_left`

English:
theorem spanCompIso_inv_app_left
  statement: (spanCompIso F f g).inv.app WalkingSpan.left = 𝟙 _
  proof: rfl

@[simp]

中文:
定理 spanCompIso_inv_app_left
  结论: (spanCompIso F f g).inv.app WalkingSpan.left = 𝟙 _
  证明: rfl

@[simp]
-/
theorem spanCompIso_inv_app_left : (spanCompIso F f g).inv.app WalkingSpan.left = 𝟙 _ := rfl

@[simp]
/--
theorem `spanCompIso_inv_app_right` / 定理 `spanCompIso_inv_app_right`

English:
theorem spanCompIso_inv_app_right
  statement: (spanCompIso F f g).inv.app WalkingSpan.right = 𝟙 _
  proof: rfl

@[simp]

中文:
定理 spanCompIso_inv_app_right
  结论: (spanCompIso F f g).inv.app WalkingSpan.right = 𝟙 _
  证明: rfl

@[simp]
-/
theorem spanCompIso_inv_app_right : (spanCompIso F f g).inv.app WalkingSpan.right = 𝟙 _ := rfl

@[simp]
/--
theorem `spanCompIso_inv_app_zero` / 定理 `spanCompIso_inv_app_zero`

English:
theorem spanCompIso_inv_app_zero
  statement: (spanCompIso F f g).inv.app WalkingSpan.zero = 𝟙 _
  proof: rfl

中文:
定理 spanCompIso_inv_app_zero
  结论: (spanCompIso F f g).inv.app WalkingSpan.zero = 𝟙 _
  证明: rfl
-/
theorem spanCompIso_inv_app_zero : (spanCompIso F f g).inv.app WalkingSpan.zero = 𝟙 _ := rfl

end

section

variable {X Y Z X' Y' Z' : C} (iX : X ≅ X') (iY : Y ≅ Y') (iZ : Z ≅ Z')

section

set_option backward.isDefEq.respectTransparency.types false in
/-- Constructor for natural transformations between cospans. -/
@[simps]
/--
Definition of `cospanHomMk` / `cospanHomMk` 的定义

English:
definition cospanHomMk
  signature: {F G : WalkingCospan ⥤ C}
  body: by rintro (_ | _ | _); exacts [z, l, r]
  naturality := by rintro (_ | _ | _) (_ | _ | _) (_ | _); all_goals cat_disch

中文:
定义 cospanHomMk
  签名: {F G : WalkingCospan ⥤ C}
  定义体: by rintro (_ | _ | _); exacts [z, l, r]
  naturality := by rintro (_ | _ | _) (_ | _ | _) (_ | _); all_goals cat_disch

Depends on / 依赖: F.map, G.map, all_goals, cat_disch, exacts, naturality
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
/--
Definition of `cospanIsoMk` / `cospanIsoMk` 的定义

English:
definition cospanIsoMk
  signature: {F G : WalkingCospan ⥤ C}
  body: NatIso.ofComponents (by rintro (_ | _ | _); exacts [z, l, r])
    (by rintro (_ | _ | _) (_ | _ | _) (_ | _); all_goals cat_disch)

中文:
定义 cospanIsoMk
  签名: {F G : WalkingCospan ⥤ C}
  定义体: NatIso.ofComponents (by rintro (_ | _ | _); exacts [z, l, r])
    (by rintro (_ | _ | _) (_ | _ | _) (_ | _); all_goals cat_disch)

Depends on / 依赖: F.map, G.map, NatIso, NatIso.ofComponents, all_goals, cat_disch, exacts, ofComponents, r.hom, z.hom
-/
def cospanIsoMk {F G : WalkingCospan ⥤ C}
    (z : F.obj .one ≅ G.obj .one) (l : F.obj .left ≅ G.obj .left)
    (r : F.obj .right ≅ G.obj .right)
    (hl : F.map inl ≫ z.hom = l.hom ≫ G.map inl := by cat_disch)
    (hr : F.map inr ≫ z.hom = r.hom ≫ G.map inr := by cat_disch) : F ≅ G :=
  NatIso.ofComponents (by rintro (_ | _ | _); exacts [z, l, r])
    (by rintro (_ | _ | _) (_ | _ | _) (_ | _); all_goals cat_disch)

variable {f : X ⟶ Z} {g : Y ⟶ Z} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'}

/--
Definition of `cospanExt` / `cospanExt` 的定义

English:
definition cospanExt
  signature: (wf : iX.hom ≫ f' = f ≫ iZ.hom) (wg : iY.hom ≫ g' = g ≫ iZ.hom)
  body: cospanIsoMk iZ iX iY

中文:
定义 cospanExt
  签名: (wf : iX.hom ≫ f' = f ≫ iZ.hom) (wg : iY.hom ≫ g' = g ≫ iZ.hom)
  定义体: cospanIsoMk iZ iX iY

Depends on / 依赖: cospanIsoMk
-/
def cospanExt (wf : iX.hom ≫ f' = f ≫ iZ.hom) (wg : iY.hom ≫ g' = g ≫ iZ.hom) :
    cospan f g ≅ cospan f' g' :=
  cospanIsoMk iZ iX iY

variable (wf : iX.hom ≫ f' = f ≫ iZ.hom) (wg : iY.hom ≫ g' = g ≫ iZ.hom)

@[simp]
/--
theorem `cospanExt_app_left` / 定理 `cospanExt_app_left`

English:
theorem cospanExt_app_left
  statement: (cospanExt iX iY iZ wf wg).app WalkingCospan.left = iX
  proof: rfl

@[simp]

中文:
定理 cospanExt_app_left
  结论: (cospanExt iX iY iZ wf wg).app WalkingCospan.left = iX
  证明: rfl

@[simp]
-/
theorem cospanExt_app_left : (cospanExt iX iY iZ wf wg).app WalkingCospan.left = iX := rfl

@[simp]
/--
theorem `cospanExt_app_right` / 定理 `cospanExt_app_right`

English:
theorem cospanExt_app_right
  statement: (cospanExt iX iY iZ wf wg).app WalkingCospan.right = iY
  proof: rfl

@[simp]

中文:
定理 cospanExt_app_right
  结论: (cospanExt iX iY iZ wf wg).app WalkingCospan.right = iY
  证明: rfl

@[simp]
-/
theorem cospanExt_app_right : (cospanExt iX iY iZ wf wg).app WalkingCospan.right = iY := rfl

@[simp]
/--
theorem `cospanExt_app_one` / 定理 `cospanExt_app_one`

English:
theorem cospanExt_app_one
  statement: (cospanExt iX iY iZ wf wg).app WalkingCospan.one = iZ
  proof: rfl

@[simp]

中文:
定理 cospanExt_app_one
  结论: (cospanExt iX iY iZ wf wg).app WalkingCospan.one = iZ
  证明: rfl

@[simp]
-/
theorem cospanExt_app_one : (cospanExt iX iY iZ wf wg).app WalkingCospan.one = iZ := rfl

@[simp]
/--
theorem `cospanExt_hom_app_left` / 定理 `cospanExt_hom_app_left`

English:
theorem cospanExt_hom_app_left
  proof: rfl

@[simp]

中文:
定理 cospanExt_hom_app_left
  证明: rfl

@[simp]
-/
theorem cospanExt_hom_app_left :
    (cospanExt iX iY iZ wf wg).hom.app WalkingCospan.left = iX.hom := rfl

@[simp]
/--
theorem `cospanExt_hom_app_right` / 定理 `cospanExt_hom_app_right`

English:
theorem cospanExt_hom_app_right
  proof: rfl

@[simp]

中文:
定理 cospanExt_hom_app_right
  证明: rfl

@[simp]
-/
theorem cospanExt_hom_app_right :
    (cospanExt iX iY iZ wf wg).hom.app WalkingCospan.right = iY.hom := rfl

@[simp]
/--
theorem `cospanExt_hom_app_one` / 定理 `cospanExt_hom_app_one`

English:
theorem cospanExt_hom_app_one
  statement: (cospanExt iX iY iZ wf wg).hom.app WalkingCospan.one = iZ.hom
  proof: rfl

@[simp]

中文:
定理 cospanExt_hom_app_one
  结论: (cospanExt iX iY iZ wf wg).hom.app WalkingCospan.one = iZ.hom
  证明: rfl

@[simp]
-/
theorem cospanExt_hom_app_one : (cospanExt iX iY iZ wf wg).hom.app WalkingCospan.one = iZ.hom := rfl

@[simp]
/--
theorem `cospanExt_inv_app_left` / 定理 `cospanExt_inv_app_left`

English:
theorem cospanExt_inv_app_left
  proof: rfl

@[simp]

中文:
定理 cospanExt_inv_app_left
  证明: rfl

@[simp]

Depends on / 依赖: F.map, factorizationData, ofIsEquivalence
-/
theorem cospanExt_inv_app_left :
    (cospanExt iX iY iZ wf wg).inv.app WalkingCospan.left = iX.inv := rfl

@[simp]
/--
theorem `cospanExt_inv_app_right` / 定理 `cospanExt_inv_app_right`

English:
theorem cospanExt_inv_app_right
  proof: rfl

@[simp]

中文:
定理 cospanExt_inv_app_right
  证明: rfl

@[simp]
-/
theorem cospanExt_inv_app_right :
    (cospanExt iX iY iZ wf wg).inv.app WalkingCospan.right = iY.inv :=
  rfl

@[simp]
/--
theorem `cospanExt_inv_app_one` / 定理 `cospanExt_inv_app_one`

English:
theorem cospanExt_inv_app_one
  statement: (cospanExt iX iY iZ wf wg).inv.app WalkingCospan.one = iZ.inv
  proof: by
  rfl

中文:
定理 cospanExt_inv_app_one
  结论: (cospanExt iX iY iZ wf wg).inv.app WalkingCospan.one = iZ.inv
  证明: by
  rfl
-/
theorem cospanExt_inv_app_one : (cospanExt iX iY iZ wf wg).inv.app WalkingCospan.one = iZ.inv := by
  rfl

end

section

set_option backward.isDefEq.respectTransparency.types false in
/-- Constructor for natural transformations between spans. -/
@[simps]
/--
Definition of `spanHomMk` / `spanHomMk` 的定义

English:
definition spanHomMk
  signature: {F G : WalkingSpan ⥤ C}
  body: by rintro (_ | _ | _); exacts [z, l, r]
  naturality := by rintro (_ | _ | _) (_ | _ | _) (_ | _); all_goals cat_disch

中文:
定义 spanHomMk
  签名: {F G : WalkingSpan ⥤ C}
  定义体: by rintro (_ | _ | _); exacts [z, l, r]
  naturality := by rintro (_ | _ | _) (_ | _ | _) (_ | _); all_goals cat_disch

Depends on / 依赖: F.map, G.map, all_goals, cat_disch, exacts, naturality
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
/--
Definition of `spanIsoMk` / `spanIsoMk` 的定义

English:
definition spanIsoMk
  signature: {F G : WalkingSpan ⥤ C}
  body: NatIso.ofComponents (by rintro (_ | _ | _); exacts [z, l, r])
    (by rintro (_ | _ | _) (_ | _ | _) (_ | _); all_goals cat_disch)

中文:
定义 spanIsoMk
  签名: {F G : WalkingSpan ⥤ C}
  定义体: NatIso.ofComponents (by rintro (_ | _ | _); exacts [z, l, r])
    (by rintro (_ | _ | _) (_ | _ | _) (_ | _); all_goals cat_disch)

Depends on / 依赖: F.map, G.map, NatIso, NatIso.ofComponents, all_goals, cat_disch, exacts, ofComponents, r.hom, z.hom
-/
def spanIsoMk {F G : WalkingSpan ⥤ C}
    (z : F.obj .zero ≅ G.obj .zero) (l : F.obj .left ≅ G.obj .left)
    (r : F.obj .right ≅ G.obj .right)
    (hl : F.map fst ≫ l.hom = z.hom ≫ G.map fst := by cat_disch)
    (hr : F.map snd ≫ r.hom = z.hom ≫ G.map snd := by cat_disch) : F ≅ G :=
  NatIso.ofComponents (by rintro (_ | _ | _); exacts [z, l, r])
    (by rintro (_ | _ | _) (_ | _ | _) (_ | _); all_goals cat_disch)

variable {f : X ⟶ Y} {g : X ⟶ Z} {f' : X' ⟶ Y'} {g' : X' ⟶ Z'}

/--
Definition of `spanExt` / `spanExt` 的定义

English:
definition spanExt
  signature: (wf : iX.hom ≫ f' = f ≫ iY.hom) (wg : iX.hom ≫ g' = g ≫ iZ.hom)
  body: spanIsoMk iX iY iZ

中文:
定义 spanExt
  签名: (wf : iX.hom ≫ f' = f ≫ iY.hom) (wg : iX.hom ≫ g' = g ≫ iZ.hom)
  定义体: spanIsoMk iX iY iZ

Depends on / 依赖: spanIsoMk
-/
def spanExt (wf : iX.hom ≫ f' = f ≫ iY.hom) (wg : iX.hom ≫ g' = g ≫ iZ.hom) :
    span f g ≅ span f' g' :=
  spanIsoMk iX iY iZ

variable (wf : iX.hom ≫ f' = f ≫ iY.hom) (wg : iX.hom ≫ g' = g ≫ iZ.hom)

@[simp]
/--
theorem `spanExt_app_left` / 定理 `spanExt_app_left`

English:
theorem spanExt_app_left
  statement: (spanExt iX iY iZ wf wg).app WalkingSpan.left = iY
  proof: rfl

@[simp]

中文:
定理 spanExt_app_left
  结论: (spanExt iX iY iZ wf wg).app WalkingSpan.left = iY
  证明: rfl

@[simp]

Depends on / 依赖: W.functorCategory, W.inverseImage, W.transfiniteCompositionsOfShape_le, evaluation, functorCategory, hf.ofLE, inverseImage, transfiniteCompositionsOfShape_le
-/
theorem spanExt_app_left : (spanExt iX iY iZ wf wg).app WalkingSpan.left = iY := rfl

@[simp]
/--
theorem `spanExt_app_right` / 定理 `spanExt_app_right`

English:
theorem spanExt_app_right
  statement: (spanExt iX iY iZ wf wg).app WalkingSpan.right = iZ
  proof: rfl

@[simp]

中文:
定理 spanExt_app_right
  结论: (spanExt iX iY iZ wf wg).app WalkingSpan.right = iZ
  证明: rfl

@[simp]
-/
theorem spanExt_app_right : (spanExt iX iY iZ wf wg).app WalkingSpan.right = iZ := rfl

@[simp]
/--
theorem `spanExt_app_one` / 定理 `spanExt_app_one`

English:
theorem spanExt_app_one
  statement: (spanExt iX iY iZ wf wg).app WalkingSpan.zero = iX
  proof: rfl

@[simp]

中文:
定理 spanExt_app_one
  结论: (spanExt iX iY iZ wf wg).app WalkingSpan.zero = iX
  证明: rfl

@[simp]
-/
theorem spanExt_app_one : (spanExt iX iY iZ wf wg).app WalkingSpan.zero = iX := rfl

@[simp]
/--
theorem `spanExt_hom_app_left` / 定理 `spanExt_hom_app_left`

English:
theorem spanExt_hom_app_left
  statement: (spanExt iX iY iZ wf wg).hom.app WalkingSpan.left = iY.hom
  proof: rfl

@[simp]

中文:
定理 spanExt_hom_app_left
  结论: (spanExt iX iY iZ wf wg).hom.app WalkingSpan.left = iY.hom
  证明: rfl

@[simp]
-/
theorem spanExt_hom_app_left : (spanExt iX iY iZ wf wg).hom.app WalkingSpan.left = iY.hom := rfl

@[simp]
/--
theorem `spanExt_hom_app_right` / 定理 `spanExt_hom_app_right`

English:
theorem spanExt_hom_app_right
  statement: (spanExt iX iY iZ wf wg).hom.app WalkingSpan.right = iZ.hom
  proof: rfl

@[simp]

中文:
定理 spanExt_hom_app_right
  结论: (spanExt iX iY iZ wf wg).hom.app WalkingSpan.right = iZ.hom
  证明: rfl

@[simp]

Depends on / 依赖: functorCategory_monomorphisms, infer_instance
-/
theorem spanExt_hom_app_right : (spanExt iX iY iZ wf wg).hom.app WalkingSpan.right = iZ.hom := rfl

@[simp]
/--
theorem `spanExt_hom_app_zero` / 定理 `spanExt_hom_app_zero`

English:
theorem spanExt_hom_app_zero
  statement: (spanExt iX iY iZ wf wg).hom.app WalkingSpan.zero = iX.hom
  proof: rfl

@[simp]

中文:
定理 spanExt_hom_app_zero
  结论: (spanExt iX iY iZ wf wg).hom.app WalkingSpan.zero = iX.hom
  证明: rfl

@[simp]

Depends on / 依赖: functorCategory_monomorphisms, infer_instance
-/
theorem spanExt_hom_app_zero : (spanExt iX iY iZ wf wg).hom.app WalkingSpan.zero = iX.hom := rfl

@[simp]
/--
theorem `spanExt_inv_app_left` / 定理 `spanExt_inv_app_left`

English:
theorem spanExt_inv_app_left
  statement: (spanExt iX iY iZ wf wg).inv.app WalkingSpan.left = iY.inv
  proof: rfl

@[simp]

中文:
定理 spanExt_inv_app_left
  结论: (spanExt iX iY iZ wf wg).inv.app WalkingSpan.left = iY.inv
  证明: rfl

@[simp]
-/
theorem spanExt_inv_app_left : (spanExt iX iY iZ wf wg).inv.app WalkingSpan.left = iY.inv := rfl

@[simp]
/--
theorem `spanExt_inv_app_right` / 定理 `spanExt_inv_app_right`

English:
theorem spanExt_inv_app_right
  statement: (spanExt iX iY iZ wf wg).inv.app WalkingSpan.right = iZ.inv
  proof: rfl

@[simp]

中文:
定理 spanExt_inv_app_right
  结论: (spanExt iX iY iZ wf wg).inv.app WalkingSpan.right = iZ.inv
  证明: rfl

@[simp]
-/
theorem spanExt_inv_app_right : (spanExt iX iY iZ wf wg).inv.app WalkingSpan.right = iZ.inv := rfl

@[simp]
/--
theorem `spanExt_inv_app_zero` / 定理 `spanExt_inv_app_zero`

English:
theorem spanExt_inv_app_zero
  statement: (spanExt iX iY iZ wf wg).inv.app WalkingSpan.zero = iX.inv
  proof: rfl

中文:
定理 spanExt_inv_app_zero
  结论: (spanExt iX iY iZ wf wg).inv.app WalkingSpan.zero = iX.inv
  证明: rfl
-/
theorem spanExt_inv_app_zero : (spanExt iX iY iZ wf wg).inv.app WalkingSpan.zero = iX.inv := rfl

end

end

end CategoryTheory.Limits
