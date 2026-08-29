/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!

# Equifibered natural transformation

## Main definition
- `CategoryTheory.NatTrans.Equifibered`:
  A natural transformation `α : F ⟶ G` is equifibered if every commutative square of the following
  form is a pullback.
  ```
  F(X) → F(Y)
   ↓ ↓
  G(X) → G(Y)
  ```
- `CategoryTheory.NatTrans.Coequifibered`: The dual notion.

-/

@[expose] public section


open CategoryTheory.Limits CategoryTheory.Functor

namespace CategoryTheory

variable {J K C D ι : Type*} [Category* J] [Category* C] [Category* K] [Category* D]

namespace NatTrans

/--
Definition of `Equifibered` / `Equifibered` 的定义

English:
definition Equifibered
  signature: : MorphismProperty (J ⥤ C)
  body: fun {F G} α => forall ⦃i j : J⦄ (f : i ⟶ j), IsPullback (F.map f) (α.app i) (α.app j) (G.map f)

中文:
定义 Equifibered
  签名: : MorphismProperty (J ⥤ C)
  定义体: fun {F G} α => forall ⦃i j : J⦄ (f : i ⟶ j), IsPullback (F.map f) (α.app i) (α.app j) (G.map f)

Depends on / 依赖: F.map, G.map, IsPullback
-/
def Equifibered : MorphismProperty (J ⥤ C) :=
  fun {F G} α => forall ⦃i j : J⦄ (f : i ⟶ j), IsPullback (F.map f) (α.app i) (α.app j) (G.map f)

/--
theorem `Equifibered.of_isIso` / 定理 `Equifibered.of_isIso`

English:
theorem Equifibered.of_isIso
  given: {F G : J ⥤ C} (α : F ⟶ G) [IsIso α]
  statement: Equifibered α
  proof: fun _ _ f => IsPullback.of_vert_isIso ⟨naturality _ f⟩

@[deprecated (since := "2026-02-01")] alias equifibered_of_isIso := Equifibered.of_isIso

中文:
定理 Equifibered.of_isIso
  条件: {F G : J ⥤ C} (α : F ⟶ G) [是同构 α]
  结论: Equifibered α
  证明: fun _ _ f => IsPullback.of_vert_isIso ⟨naturality _ f⟩

@[deprecated (since := "2026-02-01")] alias equifibered_of_isIso := Equifibered.of_isIso

Depends on / 依赖: IsPullback, IsPullback.of_vert_isIso, naturality, of_vert_isIso
-/
theorem Equifibered.of_isIso {F G : J ⥤ C} (α : F ⟶ G) [IsIso α] : Equifibered α :=
  fun _ _ f => IsPullback.of_vert_isIso ⟨naturality _ f⟩

@[deprecated (since := "2026-02-01")] alias equifibered_of_isIso := Equifibered.of_isIso

/--
theorem `Equifibered.comp` / 定理 `Equifibered.comp`

English:
theorem Equifibered.comp
  statement: {F G H : J ⥤ C} {α : F ⟶ G} {β : G ⟶ H} (hα : Equifibered α)
  proof: fun _ _ f => (hα f).paste_vert (hβ f)

中文:
定理 Equifibered.comp
  结论: {F G H : J ⥤ C} {α : F ⟶ G} {β : G ⟶ H} (hα : Equifibered α)
  证明: fun _ _ f => (hα f).paste_vert (hβ f)

Depends on / 依赖: paste_vert
-/
theorem Equifibered.comp {F G H : J ⥤ C} {α : F ⟶ G} {β : G ⟶ H} (hα : Equifibered α)
    (hβ : Equifibered β) : Equifibered (α ≫ β) :=
  fun _ _ f => (hα f).paste_vert (hβ f)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Equifibered (J := J) (C := C)).IsMultiplicative
  body: .of_isIso _
  comp_mem _ _ := .comp

中文:
实例 :
  签名: (Equifibered (J := J) (C := C)).是Multiplicative
  定义体: .of_isIso _
  comp_mem _ _ := .comp

Depends on / 依赖: IsMultiplicative
-/
instance : (Equifibered (J := J) (C := C)).IsMultiplicative where
  id_mem _ := .of_isIso _
  comp_mem _ _ := .comp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Equifibered (J := J) (C := C)).RespectsIso
  body: MorphismProperty.respectsIso_of_isStableUnderComposition fun _ _ => .of_isIso

中文:
实例 :
  签名: (Equifibered (J := J) (C := C)).RespectsIso
  定义体: MorphismProperty.respectsIso_of_isStableUnderComposition fun _ _ => .of_isIso

Depends on / 依赖: RespectsIso
-/
instance : (Equifibered (J := J) (C := C)).RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition fun _ _ => .of_isIso

/--
theorem `Equifibered.whiskerRight` / 定理 `Equifibered.whiskerRight`

English:
theorem Equifibered.whiskerRight
  statement: {F G : J ⥤ C} {α : F ⟶ G} (hα : Equifibered α)
  proof: fun _ _ f => (hα f).map H

中文:
定理 Equifibered.whiskerRight
  结论: {F G : J ⥤ C} {α : F ⟶ G} (hα : Equifibered α)
  证明: fun _ _ f => (hα f).map H
-/
theorem Equifibered.whiskerRight {F G : J ⥤ C} {α : F ⟶ G} (hα : Equifibered α)
    (H : C ⥤ D) [forall (i j : J) (f : j ⟶ i), PreservesLimit (cospan (α.app i) (G.map f)) H] :
    Equifibered (whiskerRight α H) :=
  fun _ _ f => (hα f).map H

/--
theorem `Equifibered.whiskerLeft` / 定理 `Equifibered.whiskerLeft`

English:
theorem Equifibered.whiskerLeft
  given: {F G : J ⥤ C} {α : F ⟶ G} (hα : Equifibered α) (H : K ⥤ J)
  proof: fun _ _ f => hα (H.map f)

中文:
定理 Equifibered.whiskerLeft
  条件: {F G : J ⥤ C} {α : F ⟶ G} (hα : Equifibered α) (H : K ⥤ J)
  证明: fun _ _ f => hα (H.map f)

Depends on / 依赖: H.map
-/
theorem Equifibered.whiskerLeft {F G : J ⥤ C} {α : F ⟶ G} (hα : Equifibered α) (H : K ⥤ J) :
    Equifibered (whiskerLeft H α) :=
  fun _ _ f => hα (H.map f)

/--
theorem `Equifibered.of_discrete` / 定理 `Equifibered.of_discrete`

English:
theorem Equifibered.of_discrete
  given: {F G : Discrete ι ⥤ C} (α : F ⟶ G)
  statement: Equifibered α
  proof: by
  rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩
  simp only [Discrete.functor_map_id]
  exact IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩

@[deprecated (since := "2026-01-23")]
alias _root_.CategoryTheory.mapPair_equifibered := Equifibered.of_discrete

@[deprecated (since := "2026-01-23")] alias equifibered_of_discrete := Equifibered.of_discrete

中文:
定理 Equifibered.of_discrete
  条件: {F G : 离散 ι ⥤ C} (α : F ⟶ G)
  结论: Equifibered α
  证明: by
  rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩
  simp only [Discrete.functor_map_id]
  exact IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩

@[deprecated (since := "2026-01-23")]
alias _root_.CategoryTheory.mapPair_equifibered := Equifibered.of_discrete

@[deprecated (since := "2026-01-23")] alias equifibered_of_discrete := Equifibered.of_discrete

Depends on / 依赖: Category, Category.comp_id, Category.id_comp, Discrete, Discrete.functor_map_id, IsPullback, IsPullback.of_horiz_isIso, comp_id, functor_map_id, id_comp, of_horiz_isIso
-/
theorem Equifibered.of_discrete {F G : Discrete ι ⥤ C} (α : F ⟶ G) : Equifibered α := by
  rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩
  simp only [Discrete.functor_map_id]
  exact IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩

@[deprecated (since := "2026-01-23")]
alias _root_.CategoryTheory.mapPair_equifibered := Equifibered.of_discrete

@[deprecated (since := "2026-01-23")] alias equifibered_of_discrete := Equifibered.of_discrete

/--
Definition of `Coequifibered` / `Coequifibered` 的定义

English:
definition Coequifibered
  signature: : MorphismProperty (J ⥤ C)
  body: fun {F G} α => forall ⦃i j : J⦄ (f : i ⟶ j), IsPushout (F.map f) (α.app i) (α.app j) (G.map f)

中文:
定义 Coequifibered
  签名: : MorphismProperty (J ⥤ C)
  定义体: fun {F G} α => forall ⦃i j : J⦄ (f : i ⟶ j), IsPushout (F.map f) (α.app i) (α.app j) (G.map f)

Depends on / 依赖: F.map, G.map, IsPushout
-/
def Coequifibered : MorphismProperty (J ⥤ C) :=
  fun {F G} α => forall ⦃i j : J⦄ (f : i ⟶ j), IsPushout (F.map f) (α.app i) (α.app j) (G.map f)

/--
theorem `Coequifibered.of_isIso` / 定理 `Coequifibered.of_isIso`

English:
theorem Coequifibered.of_isIso
  given: {F G : J ⥤ C} (α : F ⟶ G) [IsIso α]
  statement: Coequifibered α
  proof: fun _ _ f => .of_vert_isIso ⟨naturality _ f⟩

@[deprecated (since := "2026-02-01")] alias Coequifibered_of_isIso := Coequifibered.of_isIso

中文:
定理 Coequifibered.of_isIso
  条件: {F G : J ⥤ C} (α : F ⟶ G) [是同构 α]
  结论: Coequifibered α
  证明: fun _ _ f => .of_vert_isIso ⟨naturality _ f⟩

@[deprecated (since := "2026-02-01")] alias Coequifibered_of_isIso := Coequifibered.of_isIso

Depends on / 依赖: naturality, of_vert_isIso
-/
theorem Coequifibered.of_isIso {F G : J ⥤ C} (α : F ⟶ G) [IsIso α] : Coequifibered α :=
  fun _ _ f => .of_vert_isIso ⟨naturality _ f⟩

@[deprecated (since := "2026-02-01")] alias Coequifibered_of_isIso := Coequifibered.of_isIso

/--
theorem `Coequifibered.comp` / 定理 `Coequifibered.comp`

English:
theorem Coequifibered.comp
  statement: {F G H : J ⥤ C} {α : F ⟶ G} {β : G ⟶ H} (hα : Coequifibered α)
  proof: fun _ _ f => (hα f).paste_vert (hβ f)

中文:
定理 Coequifibered.comp
  结论: {F G H : J ⥤ C} {α : F ⟶ G} {β : G ⟶ H} (hα : Coequifibered α)
  证明: fun _ _ f => (hα f).paste_vert (hβ f)

Depends on / 依赖: paste_vert
-/
theorem Coequifibered.comp {F G H : J ⥤ C} {α : F ⟶ G} {β : G ⟶ H} (hα : Coequifibered α)
    (hβ : Coequifibered β) : Coequifibered (α ≫ β) :=
  fun _ _ f => (hα f).paste_vert (hβ f)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Coequifibered (J := J) (C := C)).IsMultiplicative
  body: .of_isIso _
  comp_mem _ _ := .comp

中文:
实例 :
  签名: (Coequifibered (J := J) (C := C)).是Multiplicative
  定义体: .of_isIso _
  comp_mem _ _ := .comp

Depends on / 依赖: IsMultiplicative
-/
instance : (Coequifibered (J := J) (C := C)).IsMultiplicative where
  id_mem _ := .of_isIso _
  comp_mem _ _ := .comp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Coequifibered (J := J) (C := C)).RespectsIso
  body: MorphismProperty.respectsIso_of_isStableUnderComposition fun _ _ => .of_isIso

中文:
实例 :
  签名: (Coequifibered (J := J) (C := C)).RespectsIso
  定义体: MorphismProperty.respectsIso_of_isStableUnderComposition fun _ _ => .of_isIso

Depends on / 依赖: RespectsIso
-/
instance : (Coequifibered (J := J) (C := C)).RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition fun _ _ => .of_isIso

/--
theorem `Coequifibered.whiskerRight` / 定理 `Coequifibered.whiskerRight`

English:
theorem Coequifibered.whiskerRight
  statement: {F G : J ⥤ C} {α : F ⟶ G} (hα : Coequifibered α)
  proof: fun _ _ f => (hα f).map H

中文:
定理 Coequifibered.whiskerRight
  结论: {F G : J ⥤ C} {α : F ⟶ G} (hα : Coequifibered α)
  证明: fun _ _ f => (hα f).map H
-/
theorem Coequifibered.whiskerRight {F G : J ⥤ C} {α : F ⟶ G} (hα : Coequifibered α)
    (H : C ⥤ D) [forall (i j : J) (f : j ⟶ i), PreservesColimit (span (F.map f) (α.app j)) H] :
    Coequifibered (whiskerRight α H) :=
  fun _ _ f => (hα f).map H

/--
theorem `Coequifibered.whiskerLeft` / 定理 `Coequifibered.whiskerLeft`

English:
theorem Coequifibered.whiskerLeft
  given: {F G : J ⥤ C} {α : F ⟶ G} (hα : Coequifibered α) (H : K ⥤ J)
  proof: fun _ _ f => hα (H.map f)

中文:
定理 Coequifibered.whiskerLeft
  条件: {F G : J ⥤ C} {α : F ⟶ G} (hα : Coequifibered α) (H : K ⥤ J)
  证明: fun _ _ f => hα (H.map f)

Depends on / 依赖: H.map
-/
theorem Coequifibered.whiskerLeft {F G : J ⥤ C} {α : F ⟶ G} (hα : Coequifibered α) (H : K ⥤ J) :
    Coequifibered (whiskerLeft H α) :=
  fun _ _ f => hα (H.map f)

/--
theorem `Coequifibered.of_discrete` / 定理 `Coequifibered.of_discrete`

English:
theorem Coequifibered.of_discrete
  statement: {ι : Type*} {F G : Discrete ι ⥤ C}
  proof: by
  rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩
  simp only [Discrete.functor_map_id]
  exact IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩

中文:
定理 Coequifibered.of_discrete
  结论: {ι : 类型} {F G : 离散 ι ⥤ C}
  证明: by
  rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩
  simp only [Discrete.functor_map_id]
  exact IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩

Depends on / 依赖: Category, Category.comp_id, Category.id_comp, Discrete, Discrete.functor_map_id, IsPullback, IsPullback.of_horiz_isIso, comp_id, functor_map_id, id_comp, of_horiz_isIso
-/
theorem Coequifibered.of_discrete {ι : Type*} {F G : Discrete ι ⥤ C}
    (α : F ⟶ G) : Equifibered α := by
  rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩
  simp only [Discrete.functor_map_id]
  exact IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩

section Opposite

/--
theorem `Coequifibered.op` / 定理 `Coequifibered.op`

English:
theorem Coequifibered.op
  given: {F G : J ⥤ C} {α : F ⟶ G} (hα : Coequifibered α)
  proof: fun _ _ f => (hα f.unop).op

中文:
定理 Coequifibered.op
  条件: {F G : J ⥤ C} {α : F ⟶ G} (hα : Coequifibered α)
  证明: fun _ _ f => (hα f.unop).op

Depends on / 依赖: f.unop
-/
theorem Coequifibered.op {F G : J ⥤ C} {α : F ⟶ G} (hα : Coequifibered α) :
    Equifibered (NatTrans.op α) := fun _ _ f => (hα f.unop).op

/--
theorem `Equifibered.op` / 定理 `Equifibered.op`

English:
theorem Equifibered.op
  given: {F G : J ⥤ C} {α : F ⟶ G} (hα : Equifibered α)
  proof: fun _ _ f => (hα f.unop).op

中文:
定理 Equifibered.op
  条件: {F G : J ⥤ C} {α : F ⟶ G} (hα : Equifibered α)
  证明: fun _ _ f => (hα f.unop).op

Depends on / 依赖: f.unop
-/
theorem Equifibered.op {F G : J ⥤ C} {α : F ⟶ G} (hα : Equifibered α) :
    Coequifibered (NatTrans.op α) := fun _ _ f => (hα f.unop).op

/--
theorem `Coequifibered.unop` / 定理 `Coequifibered.unop`

English:
theorem Coequifibered.unop
  given: {F G : Jᵒᵖ ⥤ Cᵒᵖ} {α : F ⟶ G} (hα : Coequifibered α)
  proof: fun _ _ f => (hα f.op).unop

中文:
定理 Coequifibered.unop
  条件: {F G : Jᵒᵖ ⥤ Cᵒᵖ} {α : F ⟶ G} (hα : Coequifibered α)
  证明: fun _ _ f => (hα f.op).unop

Depends on / 依赖: f.op
-/
theorem Coequifibered.unop {F G : Jᵒᵖ ⥤ Cᵒᵖ} {α : F ⟶ G} (hα : Coequifibered α) :
    Equifibered (NatTrans.unop α) := fun _ _ f => (hα f.op).unop

/--
theorem `Equifibered.unop` / 定理 `Equifibered.unop`

English:
theorem Equifibered.unop
  given: {F G : Jᵒᵖ ⥤ Cᵒᵖ} {α : F ⟶ G} (hα : Equifibered α)
  proof: fun _ _ f => (hα f.op).unop

中文:
定理 Equifibered.unop
  条件: {F G : Jᵒᵖ ⥤ Cᵒᵖ} {α : F ⟶ G} (hα : Equifibered α)
  证明: fun _ _ f => (hα f.op).unop

Depends on / 依赖: FullSubcategory, ObjectProperty, ObjectProperty.FullSubcategory.category, category, f.op
-/
theorem Equifibered.unop {F G : Jᵒᵖ ⥤ Cᵒᵖ} {α : F ⟶ G} (hα : Equifibered α) :
    Coequifibered (NatTrans.unop α) := fun _ _ f => (hα f.op).unop

/--
theorem `Equifibered.rightOp` / 定理 `Equifibered.rightOp`

English:
theorem Equifibered.rightOp
  given: {F G : Jᵒᵖ ⥤ C} {α : F ⟶ G} (hα : Equifibered α)
  proof: fun _ _ f => (hα f.op).op

中文:
定理 Equifibered.rightOp
  条件: {F G : Jᵒᵖ ⥤ C} {α : F ⟶ G} (hα : Equifibered α)
  证明: fun _ _ f => (hα f.op).op

Depends on / 依赖: f.op
-/
theorem Equifibered.rightOp {F G : Jᵒᵖ ⥤ C} {α : F ⟶ G} (hα : Equifibered α) :
    Coequifibered α.rightOp := fun _ _ f => (hα f.op).op

/--
theorem `Coequifibered.rightOp` / 定理 `Coequifibered.rightOp`

English:
theorem Coequifibered.rightOp
  given: {F G : Jᵒᵖ ⥤ C} {α : F ⟶ G} (hα : Coequifibered α)
  proof: fun _ _ f => (hα f.op).op

中文:
定理 Coequifibered.rightOp
  条件: {F G : Jᵒᵖ ⥤ C} {α : F ⟶ G} (hα : Coequifibered α)
  证明: fun _ _ f => (hα f.op).op

Depends on / 依赖: f.op
-/
theorem Coequifibered.rightOp {F G : Jᵒᵖ ⥤ C} {α : F ⟶ G} (hα : Coequifibered α) :
    Equifibered α.rightOp := fun _ _ f => (hα f.op).op

/--
theorem `coequifibered_op_iff` / 定理 `coequifibered_op_iff`

English:
theorem coequifibered_op_iff
  given: {F G : J ⥤ C} {α : F ⟶ G}
  proof: ⟨Coequifibered.unop, Equifibered.op⟩

中文:
定理 coequifibered_op_iff
  条件: {F G : J ⥤ C} {α : F ⟶ G}
  证明: ⟨Coequifibered.unop, Equifibered.op⟩

Depends on / 依赖: Coequifibered, Coequifibered.unop, Equifibered, Equifibered.op
-/
theorem coequifibered_op_iff {F G : J ⥤ C} {α : F ⟶ G} :
    Coequifibered (NatTrans.op α) ↔ Equifibered α := ⟨Coequifibered.unop, Equifibered.op⟩

/--
theorem `equifibered_op_iff` / 定理 `equifibered_op_iff`

English:
theorem equifibered_op_iff
  given: {F G : J ⥤ C} {α : F ⟶ G}
  proof: ⟨Equifibered.unop, Coequifibered.op⟩

中文:
定理 equifibered_op_iff
  条件: {F G : J ⥤ C} {α : F ⟶ G}
  证明: ⟨Equifibered.unop, Coequifibered.op⟩

Depends on / 依赖: Coequifibered, Coequifibered.op, Equifibered, Equifibered.unop
-/
theorem equifibered_op_iff {F G : J ⥤ C} {α : F ⟶ G} :
    Equifibered (NatTrans.op α) ↔ Coequifibered α := ⟨Equifibered.unop, Coequifibered.op⟩

/--
theorem `coequifibered_unop_iff` / 定理 `coequifibered_unop_iff`

English:
theorem coequifibered_unop_iff
  given: {F G : Jᵒᵖ ⥤ Cᵒᵖ} {α : F ⟶ G}
  proof: ⟨Coequifibered.op, Equifibered.unop⟩

中文:
定理 coequifibered_unop_iff
  条件: {F G : Jᵒᵖ ⥤ Cᵒᵖ} {α : F ⟶ G}
  证明: ⟨Coequifibered.op, Equifibered.unop⟩

Depends on / 依赖: Coequifibered, Coequifibered.op, Equifibered, Equifibered.unop
-/
theorem coequifibered_unop_iff {F G : Jᵒᵖ ⥤ Cᵒᵖ} {α : F ⟶ G} :
    Coequifibered (NatTrans.unop α) ↔ Equifibered α := ⟨Coequifibered.op, Equifibered.unop⟩

/--
theorem `equifibered_unop_iff` / 定理 `equifibered_unop_iff`

English:
theorem equifibered_unop_iff
  given: {F G : Jᵒᵖ ⥤ Cᵒᵖ} {α : F ⟶ G}
  proof: ⟨Equifibered.op, Coequifibered.unop⟩

中文:
定理 equifibered_unop_iff
  条件: {F G : Jᵒᵖ ⥤ Cᵒᵖ} {α : F ⟶ G}
  证明: ⟨Equifibered.op, Coequifibered.unop⟩

Depends on / 依赖: Coequifibered, Coequifibered.unop, Equifibered, Equifibered.op
-/
theorem equifibered_unop_iff {F G : Jᵒᵖ ⥤ Cᵒᵖ} {α : F ⟶ G} :
    Equifibered (NatTrans.unop α) ↔ Coequifibered α := ⟨Equifibered.op, Coequifibered.unop⟩

end Opposite

end NatTrans

end CategoryTheory
