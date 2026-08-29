/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.CategoryTheory.Limits.Presentation

import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Objects that are colimits of objects satisfying a certain property

Given a property of objects `P : ObjectProperty C` and a category `J`,
we introduce two properties of objects `P.strictColimitsOfShape J`
and `P.colimitsOfShape J`. The former contains exactly the objects
of the form `colimit F` for any functor `F : J ⥤ C` that has
a colimit and such that `F.obj j` satisfies `P` for any `j`, while
the latter contains all the objects that are isomorphic to
these "chosen" objects `colimit F`.

Under certain circumstances, the type of objects satisfying
`P.strictColimitsOfShape J` is small: the main reason this variant is
introduced is to deduce that the full subcategory of `P.colimitsOfShape J`
is essentially small.

By requiring `P.colimitsOfShape J ≤ P`, we introduce a typeclass
`P.IsClosedUnderColimitsOfShape J`.

We also show that `colimitsOfShape` in a category `C` is related
to `limitsOfShape` in the opposite category `Cᵒᵖ` and vice versa.

## TODO

* refactor `ObjectProperty.ind` by saying that it is the supremum
  of `P.colimitsOfShape J` for a filtered category `J`
  (generalize also to `κ`-filtered categories?)
* formalize the closure of `P` under finite colimits (which require
  iterating over `ℕ`), and more generally the closure under colimits
  indexed by a category whose type of arrows has a cardinality
  that is bounded by a certain regular cardinal (@joelriou)

-/

@[expose] public section

universe w v'' v' u'' u' v u

namespace CategoryTheory.ObjectProperty

open Limits

variable {C D : Type*} [Category* C] [Category* D] (P : ObjectProperty C)
  (J : Type u') [Category.{v'} J]
  {J' : Type u''} [Category.{v''} J']

/--
Inductive type `strictColimitsOfShape` / 归纳类型 `strictColimitsOfShape`

English:
inductive strictColimitsOfShape
  parameters: : ObjectProperty C
  constructors (1):
    - colimit: (F : J ⥤ C) [HasColimit F] (hF : forall j, P (F.obj j)) : strictColimitsOfShape (colimit F)

中文:
归纳类型 strictColimitsOfShape
  参数: : Object命题erty C
  构造子 (1 个):
    - colimit: (F : J ⥤ C) [HasColimit F] (hF : 对任意 j, P (F.obj j)) : strictColimitsOfShape (colimit F)
-/
inductive strictColimitsOfShape : ObjectProperty C
  | colimit (F : J ⥤ C) [HasColimit F] (hF : forall j, P (F.obj j)) :
    strictColimitsOfShape (colimit F)

variable {P} in
/--
lemma `strictColimitsOfShape_monotone` / 引理 `strictColimitsOfShape_monotone`

English:
lemma strictColimitsOfShape_monotone
  given: {Q : ObjectProperty C} (h : P <= Q)
  proof: by
  rintro _ ⟨F, hF⟩
  exact ⟨F, fun j => h _ (hF j)⟩

@[simp]

中文:
引理 strictColimitsOfShape_monotone
  条件: {Q : Object命题erty C} (h : P <= Q)
  证明: by
  rintro _ ⟨F, hF⟩
  exact ⟨F, fun j => h _ (hF j)⟩

@[simp]
-/
lemma strictColimitsOfShape_monotone {Q : ObjectProperty C} (h : P <= Q) :
    P.strictColimitsOfShape J <= Q.strictColimitsOfShape J := by
  rintro _ ⟨F, hF⟩
  exact ⟨F, fun j => h _ (hF j)⟩

@[simp]
/--
lemma `strictColimitsOfShape_bot` / 引理 `strictColimitsOfShape_bot`

English:
lemma strictColimitsOfShape_bot
  given: [Nonempty J]
  proof: by
  rw [eq_bot_iff]
  rintro _ ⟨_, h⟩
  exact h (Classical.arbitrary J)

中文:
引理 strictColimitsOfShape_bot
  条件: [Nonempty J]
  证明: by
  rw [eq_bot_iff]
  rintro _ ⟨_, h⟩
  exact h (Classical.arbitrary J)

Depends on / 依赖: Classical, Classical.arbitrary, arbitrary, eq_bot_iff
-/
lemma strictColimitsOfShape_bot [Nonempty J] :
    strictColimitsOfShape (⊥ : ObjectProperty C) J = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨_, h⟩
  exact h (Classical.arbitrary J)

/--
Definition of `ColimitOfShape` / `ColimitOfShape` 的定义

English:
structure ColimitOfShape
  parameters: (X : C)
  extends: ColimitPresentation J X
  axioms and operations (1):
    - prop_diag_obj((j : J)) : P (diag.obj j)

中文:
结构 ColimitOfShape
  参数: (X : C)
  继承: ColimitPresentation J X
  公理与运算 (1 个):
    - prop_diag_obj((j : J)) : P (diag.obj j)

Depends on / 依赖: infer_instance, truncLE
-/
structure ColimitOfShape (X : C) extends ColimitPresentation J X where
  prop_diag_obj (j : J) : P (diag.obj j)

namespace ColimitOfShape

variable {P J}

/-- If `F : J ⥤ C` is a functor that has a colimit and is such that for all `j`,
`F.obj j` satisfies a property `P`, then this structure expresses that `colimit F`
is indeed a colimit of objects satisfying `P`. -/
@[simps toColimitPresentation]
/--
Definition of `colimit` / `colimit` 的定义

English:
definition colimit
  signature: (F : J ⥤ C) [HasColimit F] (hF : forall j, P (F.obj j))
  body: .colimit F
  prop_diag_obj := hF

中文:
定义 colimit
  签名: (F : J ⥤ C) [HasColimit F] (hF : 对任意 j, P (F.obj j))
  定义体: .colimit F
  prop_diag_obj := hF

Depends on / 依赖: colimit, infer_instance, truncGT
-/
noncomputable def colimit (F : J ⥤ C) [HasColimit F] (hF : forall j, P (F.obj j)) :
    P.ColimitOfShape J (colimit F) where
  toColimitPresentation := .colimit F
  prop_diag_obj := hF

/-- If `X` is a colimit indexed by `J` of objects satisfying a property `P`, then
any object that is isomorphic to `X` also is. -/
@[simps toColimitPresentation]
/--
Definition of `ofIso` / `ofIso` 的定义

English:
definition ofIso
  signature: {X : C} (h : P.ColimitOfShape J X) {Y : C} (e : X ≅ Y)
  body: .ofIso h.toColimitPresentation e
  prop_diag_obj := h.prop_diag_obj

中文:
定义 ofIso
  签名: {X : C} (h : P.ColimitOfShape J X) {Y : C} (e : X ≅ Y)
  定义体: .ofIso h.toColimitPresentation e
  prop_diag_obj := h.prop_diag_obj

Depends on / 依赖: h.toColimitPresentation, infer_instance, toColimitPresentation, truncLE
-/
def ofIso {X : C} (h : P.ColimitOfShape J X) {Y : C} (e : X ≅ Y) :
    P.ColimitOfShape J Y where
  toColimitPresentation := .ofIso h.toColimitPresentation e
  prop_diag_obj := h.prop_diag_obj

/-- If `X` is a colimit indexed by `J` of objects satisfying a property `P`,
it is also a colimit indexed by `J` of objects satisfying `Q` if `P ≤ Q`. -/
@[simps toColimitPresentation]
/--
Definition of `ofLE` / `ofLE` 的定义

English:
definition ofLE
  signature: {X : C} (h : P.ColimitOfShape J X) {Q : ObjectProperty C} (hPQ : P <= Q)
  body: h.toColimitPresentation
  prop_diag_obj j := hPQ _ (h.prop_diag_obj j)

中文:
定义 ofLE
  签名: {X : C} (h : P.ColimitOfShape J X) {Q : Object命题erty C} (hPQ : P <= Q)
  定义体: h.toColimitPresentation
  prop_diag_obj j := hPQ _ (h.prop_diag_obj j)

Depends on / 依赖: h.toColimitPresentation, infer_instance, toColimitPresentation
-/
def ofLE {X : C} (h : P.ColimitOfShape J X) {Q : ObjectProperty C} (hPQ : P <= Q) :
    Q.ColimitOfShape J X where
  toColimitPresentation := h.toColimitPresentation
  prop_diag_obj j := hPQ _ (h.prop_diag_obj j)

/-- Change the index category for `ObjectProperty.ColimitOfShape`. -/
@[simps toColimitPresentation]
/--
Definition of `reindex` / `reindex` 的定义

English:
definition reindex
  signature: {X : C} (h : P.ColimitOfShape J X) (G : J' ⥤ J) [G.Final]
  body: h.toColimitPresentation.reindex G
  prop_diag_obj _ := h.prop_diag_obj _

中文:
定义 reindex
  签名: {X : C} (h : P.ColimitOfShape J X) (G : J' ⥤ J) [G.Final]
  定义体: h.toColimitPresentation.reindex G
  prop_diag_obj _ := h.prop_diag_obj _

Depends on / 依赖: h.toColimitPresentation.reindex, reindex, toColimitPresentation
-/
noncomputable def reindex {X : C} (h : P.ColimitOfShape J X) (G : J' ⥤ J) [G.Final] :
    P.ColimitOfShape J' X where
  toColimitPresentation := h.toColimitPresentation.reindex G
  prop_diag_obj _ := h.prop_diag_obj _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given `P : ObjectProperty C`, and a presentation `P.ColimitOfShape J X`
of an object `X : C`, this is the induced functor `J ⥤ CostructuredArrow P.ι X`. -/
@[simps]
/--
Definition of `toCostructuredArrow` / `toCostructuredArrow` 的定义

English:
definition toCostructuredArrow
  body: CostructuredArrow.mk (Y := ⟨_, p.prop_diag_obj j⟩) (by exact p.ι.app j)
  map f := CostructuredArrow.homMk (ObjectProperty.homMk (by exact p.diag.map f))

中文:
定义 toCostructuredArrow
  定义体: CostructuredArrow.mk (Y := ⟨_, p.prop_diag_obj j⟩) (by exact p.ι.app j)
  map f := CostructuredArrow.homMk (ObjectProperty.homMk (by exact p.diag.map f))

Depends on / 依赖: CostructuredArrow, CostructuredArrow.mk, p.prop_diag_obj, prop_diag_obj
-/
def toCostructuredArrow
    {X : C} (p : P.ColimitOfShape J X) :
    J ⥤ CostructuredArrow P.ι X where
  obj j := CostructuredArrow.mk (Y := ⟨_, p.prop_diag_obj j⟩) (by exact p.ι.app j)
  map f := CostructuredArrow.homMk (ObjectProperty.homMk (by exact p.diag.map f))

end ColimitOfShape

/--
Definition of `colimitsOfShape` / `colimitsOfShape` 的定义

English:
definition colimitsOfShape
  signature: : ObjectProperty C
  body: fun X => Nonempty (P.ColimitOfShape J X)

中文:
定义 colimitsOfShape
  签名: : Object命题erty C
  定义体: fun X => Nonempty (P.ColimitOfShape J X)

Depends on / 依赖: ColimitOfShape, Nonempty, P.ColimitOfShape, t.isIso_truncLE_map_truncLE
-/
def colimitsOfShape : ObjectProperty C :=
  fun X => Nonempty (P.ColimitOfShape J X)

variable {P J} in
/--
lemma `ColimitOfShape.colimitsOfShape` / 引理 `ColimitOfShape.colimitsOfShape`

English:
lemma ColimitOfShape.colimitsOfShape
  given: {X : C} (h : P.ColimitOfShape J X)
  proof: ⟨h⟩

中文:
引理 ColimitOfShape.colimitsOfShape
  条件: {X : C} (h : P.ColimitOfShape J X)
  证明: ⟨h⟩
-/
lemma ColimitOfShape.colimitsOfShape {X : C} (h : P.ColimitOfShape J X) :
    P.colimitsOfShape J X :=
  ⟨h⟩

/--
lemma `strictColimitsOfShape_le_colimitsOfShape` / 引理 `strictColimitsOfShape_le_colimitsOfShape`

English:
lemma strictColimitsOfShape_le_colimitsOfShape
  proof: by
  rintro X ⟨F, hF⟩
  exact ⟨.colimit F hF⟩

@[simp]

中文:
引理 strictColimitsOfShape_le_colimitsOfShape
  证明: by
  rintro X ⟨F, hF⟩
  exact ⟨.colimit F hF⟩

@[simp]

Depends on / 依赖: colimit
-/
lemma strictColimitsOfShape_le_colimitsOfShape :
    P.strictColimitsOfShape J <= P.colimitsOfShape J := by
  rintro X ⟨F, hF⟩
  exact ⟨.colimit F hF⟩

@[simp]
/--
lemma `colimitsOfShape_bot` / 引理 `colimitsOfShape_bot`

English:
lemma colimitsOfShape_bot
  given: [Nonempty J]
  statement: colimitsOfShape (⊥ : ObjectProperty C) J = ⊥
  proof: by
  rw [eq_bot_iff]
  rintro X ⟨⟨_, h⟩⟩
  exact h (Classical.arbitrary J)

中文:
引理 colimitsOfShape_bot
  条件: [Nonempty J]
  结论: colimitsOfShape (⊥ : Object命题erty C) J = ⊥
  证明: by
  rw [eq_bot_iff]
  rintro X ⟨⟨_, h⟩⟩
  exact h (Classical.arbitrary J)

Depends on / 依赖: Classical, Classical.arbitrary, arbitrary, eq_bot_iff
-/
lemma colimitsOfShape_bot [Nonempty J] : colimitsOfShape (⊥ : ObjectProperty C) J = ⊥ := by
  rw [eq_bot_iff]
  rintro X ⟨⟨_, h⟩⟩
  exact h (Classical.arbitrary J)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (P.colimitsOfShape J).IsClosedUnderIsomorphisms
  body: by rintro _ _ e ⟨h⟩; exact ⟨h.ofIso e⟩

@[simp]

中文:
实例 :
  签名: (P.colimitsOfShape J).IsClosedUnderIsomorphisms
  定义体: by rintro _ _ e ⟨h⟩; exact ⟨h.ofIso e⟩

@[simp]

Depends on / 依赖: h.ofIso
-/
instance : (P.colimitsOfShape J).IsClosedUnderIsomorphisms where
  of_iso := by rintro _ _ e ⟨h⟩; exact ⟨h.ofIso e⟩

@[simp]
/--
lemma `isoClosure_strictColimitsOfShape` / 引理 `isoClosure_strictColimitsOfShape`

English:
lemma isoClosure_strictColimitsOfShape
  proof: by
  refine le_antisymm ?_ ?_
  · rw [isoClosure_le_iff]
    apply strictColimitsOfShape_le_colimitsOfShape
  · intro X ⟨h⟩
    have := h.hasColimit
    exact ⟨colimit h.diag, strictColimitsOfShape.colimit h.diag h.prop_diag_obj,
      ⟨h.isColimit.coconePointUniqueUpToIso (colimit.isColimit _)⟩⟩

中文:
引理 isoClosure_strictColimitsOfShape
  证明: by
  refine le_antisymm ?_ ?_
  · rw [isoClosure_le_iff]
    apply strictColimitsOfShape_le_colimitsOfShape
  · intro X ⟨h⟩
    have := h.hasColimit
    exact ⟨colimit h.diag, strictColimitsOfShape.colimit h.diag h.prop_diag_obj,
      ⟨h.isColimit.coconePointUniqueUpToIso (colimit.isColimit _)⟩⟩

Depends on / 依赖: coconePointUniqueUpToIso, colimit, colimit.isColimit, h.diag, h.hasColimit, h.isColimit.coconePointUniqueUpToIso, h.prop_diag_obj, hasColimit, isColimit, isoClosure_le_iff, le_antisymm, prop_diag_obj, strictColimitsOfShape, strictColimitsOfShape.colimit, strictColimitsOfShape_le_colimitsOfShape
-/
lemma isoClosure_strictColimitsOfShape :
    (P.strictColimitsOfShape J).isoClosure = P.colimitsOfShape J := by
  refine le_antisymm ?_ ?_
  · rw [isoClosure_le_iff]
    apply strictColimitsOfShape_le_colimitsOfShape
  · intro X ⟨h⟩
    have := h.hasColimit
    exact ⟨colimit h.diag, strictColimitsOfShape.colimit h.diag h.prop_diag_obj,
      ⟨h.isColimit.coconePointUniqueUpToIso (colimit.isColimit _)⟩⟩

variable {P} in
/--
lemma `colimitsOfShape_monotone` / 引理 `colimitsOfShape_monotone`

English:
lemma colimitsOfShape_monotone
  given: {Q : ObjectProperty C} (hPQ : P <= Q)
  proof: by
  intro X ⟨h⟩
  exact ⟨h.ofLE hPQ⟩

@[simp]

中文:
引理 colimitsOfShape_monotone
  条件: {Q : Object命题erty C} (hPQ : P <= Q)
  证明: by
  intro X ⟨h⟩
  exact ⟨h.ofLE hPQ⟩

@[simp]

Depends on / 依赖: h.ofLE
-/
lemma colimitsOfShape_monotone {Q : ObjectProperty C} (hPQ : P <= Q) :
    P.colimitsOfShape J <= Q.colimitsOfShape J := by
  intro X ⟨h⟩
  exact ⟨h.ofLE hPQ⟩

@[simp]
/--
lemma `colimitsOfShape_isoClosure` / 引理 `colimitsOfShape_isoClosure`

English:
lemma colimitsOfShape_isoClosure
  proof: by
  refine le_antisymm ?_ (colimitsOfShape_monotone _ (P.le_isoClosure))
  intro X ⟨h⟩
  choose obj h₁ h₂ using h.prop_diag_obj
  exact
   ⟨{ toColimitPresentation := h.changeDiag (h.diag.isoCopyObj obj (fun j => (h₂ j).some)).symm
      prop_diag_obj := h₁ }⟩

中文:
引理 colimitsOfShape_isoClosure
  证明: by
  refine le_antisymm ?_ (colimitsOfShape_monotone _ (P.le_isoClosure))
  intro X ⟨h⟩
  choose obj h₁ h₂ using h.prop_diag_obj
  exact
   ⟨{ toColimitPresentation := h.changeDiag (h.diag.isoCopyObj obj (fun j => (h₂ j).some)).symm
      prop_diag_obj := h₁ }⟩

Depends on / 依赖: P.le_isoClosure, changeDiag, colimitsOfShape_monotone, h.changeDiag, h.diag.isoCopyObj, h.prop_diag_obj, isoCopyObj, le_antisymm, le_isoClosure, prop_diag_obj, toColimitPresentation
-/
lemma colimitsOfShape_isoClosure :
    P.isoClosure.colimitsOfShape J = P.colimitsOfShape J := by
  refine le_antisymm ?_ (colimitsOfShape_monotone _ (P.le_isoClosure))
  intro X ⟨h⟩
  choose obj h₁ h₂ using h.prop_diag_obj
  exact
   ⟨{ toColimitPresentation := h.changeDiag (h.diag.isoCopyObj obj (fun j => (h₂ j).some)).symm
      prop_diag_obj := h₁ }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [ObjectProperty.Small.{w}
  signature: P] [LocallySmall.{w} C] [Small.{w} J] [LocallySmall.{w} J] :
  body: by
  refine small_of_surjective
    (f := fun (F : { F : J ⥤ P.FullSubcategory // HasColimit (F ⋙ P.ι) }) =>
      (⟨_, letI := F.2; ⟨F.1 ⋙ P.ι, fun j => (F.1.obj j).2⟩⟩)) ?_
  rintro ⟨_, ⟨F, hF⟩⟩
  exact ⟨⟨P.lift F hF, by assumption⟩, rfl⟩

中文:
实例 [ObjectProperty.Small.{w}
  签名: P] [LocallySmall.{w} C] [Small.{w} J] [LocallySmall.{w} J] :
  定义体: by
  refine small_of_surjective
    (f := fun (F : { F : J ⥤ P.FullSubcategory // HasColimit (F ⋙ P.ι) }) =>
      (⟨_, letI := F.2; ⟨F.1 ⋙ P.ι, fun j => (F.1.obj j).2⟩⟩)) ?_
  rintro ⟨_, ⟨F, hF⟩⟩
  exact ⟨⟨P.lift F hF, by assumption⟩, rfl⟩

Depends on / 依赖: FullSubcategory, HasColimit, P.FullSubcategory, P.lift, small_of_surjective
-/
instance [ObjectProperty.Small.{w} P] [LocallySmall.{w} C] [Small.{w} J] [LocallySmall.{w} J] :
    ObjectProperty.Small.{w} (P.strictColimitsOfShape J) := by
  refine small_of_surjective
    (f := fun (F : { F : J ⥤ P.FullSubcategory // HasColimit (F ⋙ P.ι) }) =>
      (⟨_, letI := F.2; ⟨F.1 ⋙ P.ι, fun j => (F.1.obj j).2⟩⟩)) ?_
  rintro ⟨_, ⟨F, hF⟩⟩
  exact ⟨⟨P.lift F hF, by assumption⟩, rfl⟩

/-- A property of objects satisfies `P.IsClosedUnderColimitsOfShape J` if it
is stable by colimits of shape `J`. -/
@[mk_iff]
/--
Definition of `IsClosedUnderColimitsOfShape` / `IsClosedUnderColimitsOfShape` 的定义

English:
class IsClosedUnderColimitsOfShape
  parameters: (P : ObjectProperty C) (J : Type u') [Category.{v'} J]
  axioms and operations (1):
    - colimitsOfShape_le((P J)) : P.colimitsOfShape J <= P

中文:
类 IsClosedUnderColimitsOfShape
  参数: (P : Object命题erty C) (J : 类型u') [Category.{v'} J]
  公理与运算 (1 个):
    - colimitsOfShape_le((P J)) : P.colimitsOfShape J <= P
-/
class IsClosedUnderColimitsOfShape (P : ObjectProperty C) (J : Type u') [Category.{v'} J] where
  colimitsOfShape_le (P J) : P.colimitsOfShape J <= P

variable {P J} in
/--
lemma `IsClosedUnderColimitsOfShape.mk'` / 引理 `IsClosedUnderColimitsOfShape.mk'`

English:
lemma IsClosedUnderColimitsOfShape.mk'
  statement: [P.IsClosedUnderIsomorphisms]
  proof: by
    conv_rhs => rw [← P.isoClosure_eq_self]
    rw [← isoClosure_strictColimitsOfShape]
    exact monotone_isoClosure h

中文:
引理 IsClosedUnderColimitsOfShape.mk'
  结论: [P.IsClosedUnderIsomorphisms]
  证明: by
    conv_rhs => rw [← P.isoClosure_eq_self]
    rw [← isoClosure_strictColimitsOfShape]
    exact monotone_isoClosure h

Depends on / 依赖: P.isoClosure_eq_self, conv_rhs, isoClosure_eq_self, isoClosure_strictColimitsOfShape, monotone_isoClosure
-/
lemma IsClosedUnderColimitsOfShape.mk' [P.IsClosedUnderIsomorphisms]
    (h : P.strictColimitsOfShape J <= P) :
    P.IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    conv_rhs => rw [← P.isoClosure_eq_self]
    rw [← isoClosure_strictColimitsOfShape]
    exact monotone_isoClosure h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: J] : IsClosedUnderColimitsOfShape (⊥
  body: by rw [colimitsOfShape_bot]

中文:
实例 [Nonempty
  签名: J] : IsClosedUnderColimitsOfShape (⊥
  定义体: by rw [colimitsOfShape_bot]

Depends on / 依赖: colimitsOfShape_bot
-/
instance [Nonempty J] : IsClosedUnderColimitsOfShape (⊥ : ObjectProperty C) J where
  colimitsOfShape_le := by rw [colimitsOfShape_bot]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsClosedUnderColimitsOfShape (⊤ : ObjectProperty C) J
  body: by trivial

中文:
实例 :
  签名: IsClosedUnderColimitsOfShape (⊤ : Object命题erty C) J
  定义体: by trivial
-/
instance : IsClosedUnderColimitsOfShape (⊤ : ObjectProperty C) J where
  colimitsOfShape_le _ _ := by trivial

export IsClosedUnderColimitsOfShape (colimitsOfShape_le)

section

variable {J} [P.IsClosedUnderColimitsOfShape J]

variable {P} in
/--
lemma `ColimitOfShape.prop` / 引理 `ColimitOfShape.prop`

English:
lemma ColimitOfShape.prop
  given: {X : C} (h : P.ColimitOfShape J X)
  statement: P X
  proof: P.colimitsOfShape_le J _ ⟨h⟩

中文:
引理 ColimitOfShape.prop
  条件: {X : C} (h : P.ColimitOfShape J X)
  结论: P X
  证明: P.colimitsOfShape_le J _ ⟨h⟩

Depends on / 依赖: P.colimitsOfShape_le, colimitsOfShape_le
-/
lemma ColimitOfShape.prop {X : C} (h : P.ColimitOfShape J X) : P X :=
  P.colimitsOfShape_le J _ ⟨h⟩

/--
lemma `prop_of_isColimit` / 引理 `prop_of_isColimit`

English:
lemma prop_of_isColimit
  statement: {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c)
  proof: P.colimitsOfShape_le J _ ⟨{ diag := _, ι := _, isColimit := hc, prop_diag_obj := hF }⟩

中文:
引理 prop_of_isColimit
  结论: {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c)
  证明: P.colimitsOfShape_le J _ ⟨{ diag := _, ι := _, isColimit := hc, prop_diag_obj := hF }⟩

Depends on / 依赖: P.colimitsOfShape_le, colimitsOfShape_le, isColimit, prop_diag_obj
-/
lemma prop_of_isColimit {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c)
    (hF : forall (j : J), P (F.obj j)) : P c.pt :=
  P.colimitsOfShape_le J _ ⟨{ diag := _, ι := _, isColimit := hc, prop_diag_obj := hF }⟩

/--
lemma `prop_colimit` / 引理 `prop_colimit`

English:
lemma prop_colimit
  given: (F : J ⥤ C) [HasColimit F] (hF : forall (j : J), P (F.obj j))
  proof: P.prop_of_isColimit (colimit.isColimit F) hF

中文:
引理 prop_colimit
  条件: (F : J ⥤ C) [HasColimit F] (hF : 对任意 (j : J), P (F.obj j))
  证明: P.prop_of_isColimit (colimit.isColimit F) hF

Depends on / 依赖: P.prop_of_isColimit, colimit, colimit.isColimit, isColimit, prop_of_isColimit
-/
lemma prop_colimit (F : J ⥤ C) [HasColimit F] (hF : forall (j : J), P (F.obj j)) :
    P (colimit F) :=
  P.prop_of_isColimit (colimit.isColimit F) hF

end

variable {J} in
/--
lemma `colimitsOfShape_le_of_final` / 引理 `colimitsOfShape_le_of_final`

English:
lemma colimitsOfShape_le_of_final
  given: (G : J ⥤ J') [G.Final]
  proof: fun _h ⟨h⟩ => ⟨h.reindex G⟩

中文:
引理 colimitsOfShape_le_of_final
  条件: (G : J ⥤ J') [G.Final]
  证明: fun _h ⟨h⟩ => ⟨h.reindex G⟩

Depends on / 依赖: h.reindex, reindex
-/
lemma colimitsOfShape_le_of_final (G : J ⥤ J') [G.Final] :
    P.colimitsOfShape J' <= P.colimitsOfShape J :=
  fun _h ⟨h⟩ => ⟨h.reindex G⟩

variable {J} in
/--
lemma `colimitsOfShape_congr` / 引理 `colimitsOfShape_congr`

English:
lemma colimitsOfShape_congr
  given: (e : J ≌ J')
  proof: le_antisymm (P.colimitsOfShape_le_of_final e.inverse)
    (P.colimitsOfShape_le_of_final e.functor)

中文:
引理 colimitsOfShape_congr
  条件: (e : J ≌ J')
  证明: le_antisymm (P.colimitsOfShape_le_of_final e.inverse)
    (P.colimitsOfShape_le_of_final e.functor)

Depends on / 依赖: P.colimitsOfShape_le_of_final, colimitsOfShape_le_of_final, e.functor, e.inverse, functor, inverse, le_antisymm
-/
lemma colimitsOfShape_congr (e : J ≌ J') :
    P.colimitsOfShape J = P.colimitsOfShape J' :=
  le_antisymm (P.colimitsOfShape_le_of_final e.inverse)
    (P.colimitsOfShape_le_of_final e.functor)

variable {J} in
/--
lemma `isClosedUnderColimitsOfShape_iff_of_equivalence` / 引理 `isClosedUnderColimitsOfShape_iff_of_equivalence`

English:
lemma isClosedUnderColimitsOfShape_iff_of_equivalence
  given: (e : J ≌ J')
  proof: by
  simp [isClosedUnderColimitsOfShape_iff, P.colimitsOfShape_congr e]

中文:
引理 isClosedUnderColimitsOfShape_iff_of_equivalence
  条件: (e : J ≌ J')
  证明: by
  simp [isClosedUnderColimitsOfShape_iff, P.colimitsOfShape_congr e]

Depends on / 依赖: Functor, Functor.comp_map, Functor.map_add, P.colimitsOfShape_congr, colimitsOfShape_congr, comp_map, isClosedUnderColimitsOfShape_iff, map_add, truncLT
-/
lemma isClosedUnderColimitsOfShape_iff_of_equivalence (e : J ≌ J') :
    P.IsClosedUnderColimitsOfShape J ↔
      P.IsClosedUnderColimitsOfShape J' := by
  simp [isClosedUnderColimitsOfShape_iff, P.colimitsOfShape_congr e]

variable {P J} in
/--
lemma `IsClosedUnderColimitsOfShape.of_equivalence` / 引理 `IsClosedUnderColimitsOfShape.of_equivalence`

English:
lemma IsClosedUnderColimitsOfShape.of_equivalence
  statement: (e : J ≌ J')
  proof: by
  rwa [← P.isClosedUnderColimitsOfShape_iff_of_equivalence e]

中文:
引理 IsClosedUnderColimitsOfShape.of_equivalence
  结论: (e : J ≌ J')
  证明: by
  rwa [← P.isClosedUnderColimitsOfShape_iff_of_equivalence e]

Depends on / 依赖: P.isClosedUnderColimitsOfShape_iff_of_equivalence, isClosedUnderColimitsOfShape_iff_of_equivalence
-/
lemma IsClosedUnderColimitsOfShape.of_equivalence (e : J ≌ J')
    [P.IsClosedUnderColimitsOfShape J] :
    P.IsClosedUnderColimitsOfShape J' := by
  rwa [← P.isClosedUnderColimitsOfShape_iff_of_equivalence e]

/--
Instance `IsClosedUnderColimitsOfShape.inverseImage` / 实例 `IsClosedUnderColimitsOfShape.inverseImage`

English:
instance IsClosedUnderColimitsOfShape.inverseImage
  body: ⟨fun _ ⟨c, H⟩ => ColimitOfShape.prop (P := P) ⟨c.map F, H⟩⟩

中文:
实例 IsClosedUnderColimitsOfShape.inverseImage
  定义体: ⟨fun _ ⟨c, H⟩ => ColimitOfShape.prop (P := P) ⟨c.map F, H⟩⟩

Depends on / 依赖: ColimitOfShape, ColimitOfShape.prop, c.map
-/
instance IsClosedUnderColimitsOfShape.inverseImage
    (P : ObjectProperty D) (F : C ⥤ D) [P.IsClosedUnderColimitsOfShape J]
    [PreservesColimitsOfShape J F] : (P.inverseImage F).IsClosedUnderColimitsOfShape J :=
  ⟨fun _ ⟨c, H⟩ => ColimitOfShape.prop (P := P) ⟨c.map F, H⟩⟩

/--
lemma `isClosedUnderColimitsOfShape_inverseImage_iff` / 引理 `isClosedUnderColimitsOfShape_inverseImage_iff`

English:
lemma isClosedUnderColimitsOfShape_inverseImage_iff
  statement: (P : ObjectProperty D)
  proof: by
  refine ⟨fun H => ?_, fun _ => inferInstance⟩
  convert!
    (inferInstance :
      ((P.inverseImage e.functor).inverseImage e.inverse).IsClosedUnderColimitsOfShape J)
  ext X
  simpa using P.prop_iff_of_iso (e.counitIso.app X).symm

中文:
引理 isClosedUnderColimitsOfShape_inverseImage_iff
  结论: (P : Object命题erty D)
  证明: by
  refine ⟨fun H => ?_, fun _ => inferInstance⟩
  convert!
    (inferInstance :
      ((P.inverseImage e.functor).inverseImage e.inverse).IsClosedUnderColimitsOfShape J)
  ext X
  simpa using P.prop_iff_of_iso (e.counitIso.app X).symm

Depends on / 依赖: Functor, Functor.comp_map, Functor.map_add, IsClosedUnderColimitsOfShape, P.inverseImage, P.prop_iff_of_iso, comp_map, convert, counitIso, e.counitIso.app, e.functor, e.inverse, functor, inverse, inverseImage, map_add, prop_iff_of_iso, truncGE
-/
lemma isClosedUnderColimitsOfShape_inverseImage_iff (P : ObjectProperty D)
    [P.IsClosedUnderIsomorphisms] (e : C ≌ D) :
    (P.inverseImage e.functor).IsClosedUnderColimitsOfShape J ↔
      P.IsClosedUnderColimitsOfShape J := by
  refine ⟨fun H => ?_, fun _ => inferInstance⟩
  convert!
    (inferInstance :
      ((P.inverseImage e.functor).inverseImage e.inverse).IsClosedUnderColimitsOfShape J)
  ext X
  simpa using P.prop_iff_of_iso (e.counitIso.app X).symm

/--
lemma `colimitsOfShape_eq_unop_limitsOfShape` / 引理 `colimitsOfShape_eq_unop_limitsOfShape`

English:
lemma colimitsOfShape_eq_unop_limitsOfShape
  proof: by
  ext X
  refine ⟨fun ⟨h⟩ => ⟨?_⟩, fun ⟨h⟩ => ⟨?_⟩⟩
  · exact
      { diag := h.diag.op
        π := NatTrans.op h.ι
        isLimit := isLimitOfUnop h.isColimit
        prop_diag_obj _ := h.prop_diag_obj _ }
  · exact
      { diag := h.diag.unop
        ι := NatTrans.unop h.π
        isColimit :

中文:
引理 colimitsOfShape_eq_unop_limitsOfShape
  证明: by
  ext X
  refine ⟨fun ⟨h⟩ => ⟨?_⟩, fun ⟨h⟩ => ⟨?_⟩⟩
  · exact
      { diag := h.diag.op
        π := NatTrans.op h.ι
        isLimit := isLimitOfUnop h.isColimit
        prop_diag_obj _ := h.prop_diag_obj _ }
  · exact
      { diag := h.diag.unop
        ι := NatTrans.unop h.π
        isColimit :

Depends on / 依赖: NatTrans, NatTrans.op, NatTrans.unop, h.diag.op, h.diag.unop, h.isColimit, h.isLimit, h.prop_diag_obj, isColimit, isColimitOfOp, isLimit, isLimitOfUnop, prop_diag_obj
-/
lemma colimitsOfShape_eq_unop_limitsOfShape :
    P.colimitsOfShape J = (P.op.limitsOfShape Jᵒᵖ).unop := by
  ext X
  refine ⟨fun ⟨h⟩ => ⟨?_⟩, fun ⟨h⟩ => ⟨?_⟩⟩
  · exact
      { diag := h.diag.op
        π := NatTrans.op h.ι
        isLimit := isLimitOfUnop h.isColimit
        prop_diag_obj _ := h.prop_diag_obj _ }
  · exact
      { diag := h.diag.unop
        ι := NatTrans.unop h.π
        isColimit := isColimitOfOp h.isLimit
        prop_diag_obj _ := h.prop_diag_obj _ }

/--
lemma `limitsOfShape_eq_unop_colimitsOfShape` / 引理 `limitsOfShape_eq_unop_colimitsOfShape`

English:
lemma limitsOfShape_eq_unop_colimitsOfShape
  proof: by
  ext X
  refine ⟨fun ⟨h⟩ => ⟨?_⟩, fun ⟨h⟩ => ⟨?_⟩⟩
  · exact
      { diag := h.diag.op
        ι := NatTrans.op h.π
        isColimit := isColimitOfUnop h.isLimit
        prop_diag_obj _ := h.prop_diag_obj _ }
  · exact
      { diag := h.diag.unop
        π := NatTrans.unop h.ι
        isLimit :

中文:
引理 limitsOfShape_eq_unop_colimitsOfShape
  证明: by
  ext X
  refine ⟨fun ⟨h⟩ => ⟨?_⟩, fun ⟨h⟩ => ⟨?_⟩⟩
  · exact
      { diag := h.diag.op
        ι := NatTrans.op h.π
        isColimit := isColimitOfUnop h.isLimit
        prop_diag_obj _ := h.prop_diag_obj _ }
  · exact
      { diag := h.diag.unop
        π := NatTrans.unop h.ι
        isLimit :

Depends on / 依赖: NatTrans, NatTrans.op, NatTrans.unop, h.diag.op, h.diag.unop, h.isColimit, h.isLimit, h.prop_diag_obj, isColimit, isColimitOfUnop, isLimit, isLimitOfOp, prop_diag_obj
-/
lemma limitsOfShape_eq_unop_colimitsOfShape :
    P.limitsOfShape J = (P.op.colimitsOfShape Jᵒᵖ).unop := by
  ext X
  refine ⟨fun ⟨h⟩ => ⟨?_⟩, fun ⟨h⟩ => ⟨?_⟩⟩
  · exact
      { diag := h.diag.op
        ι := NatTrans.op h.π
        isColimit := isColimitOfUnop h.isLimit
        prop_diag_obj _ := h.prop_diag_obj _ }
  · exact
      { diag := h.diag.unop
        π := NatTrans.unop h.ι
        isLimit := isLimitOfOp h.isColimit
        prop_diag_obj _ := h.prop_diag_obj _ }

/--
lemma `limitsOfShape_op` / 引理 `limitsOfShape_op`

English:
lemma limitsOfShape_op
  proof: by
  rw [colimitsOfShape_eq_unop_limitsOfShape]; rw [op_unop]; rw [P.op.limitsOfShape_congr (opOpEquivalence J)]

中文:
引理 limitsOfShape_op
  证明: by
  rw [colimitsOfShape_eq_unop_limitsOfShape]; rw [op_unop]; rw [P.op.limitsOfShape_congr (opOpEquivalence J)]

Depends on / 依赖: P.op.limitsOfShape_congr, colimitsOfShape_eq_unop_limitsOfShape, limitsOfShape_congr, opOpEquivalence, op_unop
-/
lemma limitsOfShape_op :
    P.op.limitsOfShape J = (P.colimitsOfShape Jᵒᵖ).op := by
  rw [colimitsOfShape_eq_unop_limitsOfShape]; rw [op_unop]; rw [P.op.limitsOfShape_congr (opOpEquivalence J)]

/--
lemma `colimitsOfShape_op` / 引理 `colimitsOfShape_op`

English:
lemma colimitsOfShape_op
  proof: by
  rw [limitsOfShape_eq_unop_colimitsOfShape]; rw [op_unop]; rw [P.op.colimitsOfShape_congr (opOpEquivalence J)]

中文:
引理 colimitsOfShape_op
  证明: by
  rw [limitsOfShape_eq_unop_colimitsOfShape]; rw [op_unop]; rw [P.op.colimitsOfShape_congr (opOpEquivalence J)]

Depends on / 依赖: P.op.colimitsOfShape_congr, colimitsOfShape_congr, isLE_truncLT_obj, limitsOfShape_eq_unop_colimitsOfShape, opOpEquivalence, op_unop, t.isLE_truncLT_obj
-/
lemma colimitsOfShape_op :
    P.op.colimitsOfShape J = (P.limitsOfShape Jᵒᵖ).op := by
  rw [limitsOfShape_eq_unop_colimitsOfShape]; rw [op_unop]; rw [P.op.colimitsOfShape_congr (opOpEquivalence J)]

/--
lemma `isClosedUnderColimitsOfShape_iff_op` / 引理 `isClosedUnderColimitsOfShape_iff_op`

English:
lemma isClosedUnderColimitsOfShape_iff_op
  proof: by
  rw [isClosedUnderColimitsOfShape_iff]; rw [isClosedUnderLimitsOfShape_iff]; rw [colimitsOfShape_eq_unop_limitsOfShape]; rw [← op_monotone_iff]; rw [op_unop]

中文:
引理 isClosedUnderColimitsOfShape_iff_op
  证明: by
  rw [isClosedUnderColimitsOfShape_iff]; rw [isClosedUnderLimitsOfShape_iff]; rw [colimitsOfShape_eq_unop_limitsOfShape]; rw [← op_monotone_iff]; rw [op_unop]

Depends on / 依赖: colimitsOfShape_eq_unop_limitsOfShape, isClosedUnderColimitsOfShape_iff, isClosedUnderLimitsOfShape_iff, isLE_truncLT_obj, op_monotone_iff, op_unop, t.isLE_truncLT_obj
-/
lemma isClosedUnderColimitsOfShape_iff_op :
    P.IsClosedUnderColimitsOfShape J ↔
      P.op.IsClosedUnderLimitsOfShape Jᵒᵖ := by
  rw [isClosedUnderColimitsOfShape_iff]; rw [isClosedUnderLimitsOfShape_iff]; rw [colimitsOfShape_eq_unop_limitsOfShape]; rw [← op_monotone_iff]; rw [op_unop]

/--
lemma `isClosedUnderLimitsOfShape_iff_op` / 引理 `isClosedUnderLimitsOfShape_iff_op`

English:
lemma isClosedUnderLimitsOfShape_iff_op
  proof: by
  rw [isClosedUnderColimitsOfShape_iff]; rw [isClosedUnderLimitsOfShape_iff]; rw [limitsOfShape_eq_unop_colimitsOfShape]; rw [← op_monotone_iff]; rw [op_unop]

中文:
引理 isClosedUnderLimitsOfShape_iff_op
  证明: by
  rw [isClosedUnderColimitsOfShape_iff]; rw [isClosedUnderLimitsOfShape_iff]; rw [limitsOfShape_eq_unop_colimitsOfShape]; rw [← op_monotone_iff]; rw [op_unop]

Depends on / 依赖: isClosedUnderColimitsOfShape_iff, isClosedUnderLimitsOfShape_iff, limitsOfShape_eq_unop_colimitsOfShape, op_monotone_iff, op_unop
-/
lemma isClosedUnderLimitsOfShape_iff_op :
    P.IsClosedUnderLimitsOfShape J ↔
      P.op.IsClosedUnderColimitsOfShape Jᵒᵖ := by
  rw [isClosedUnderColimitsOfShape_iff]; rw [isClosedUnderLimitsOfShape_iff]; rw [limitsOfShape_eq_unop_colimitsOfShape]; rw [← op_monotone_iff]; rw [op_unop]

/--
lemma `isClosedUnderColimitsOfShape_op_iff_op` / 引理 `isClosedUnderColimitsOfShape_op_iff_op`

English:
lemma isClosedUnderColimitsOfShape_op_iff_op
  proof: by
  rw [isClosedUnderColimitsOfShape_iff]; rw [isClosedUnderLimitsOfShape_iff]; rw [limitsOfShape_op]; rw [op_monotone_iff]

中文:
引理 isClosedUnderColimitsOfShape_op_iff_op
  证明: by
  rw [isClosedUnderColimitsOfShape_iff]; rw [isClosedUnderLimitsOfShape_iff]; rw [limitsOfShape_op]; rw [op_monotone_iff]

Depends on / 依赖: isClosedUnderColimitsOfShape_iff, isClosedUnderLimitsOfShape_iff, isGE_truncGE_obj, limitsOfShape_op, op_monotone_iff, t.isGE_truncGE_obj
-/
lemma isClosedUnderColimitsOfShape_op_iff_op :
    P.IsClosedUnderColimitsOfShape Jᵒᵖ ↔
      P.op.IsClosedUnderLimitsOfShape J := by
  rw [isClosedUnderColimitsOfShape_iff]; rw [isClosedUnderLimitsOfShape_iff]; rw [limitsOfShape_op]; rw [op_monotone_iff]

/--
lemma `isClosedUnderLimitsOfShape_op_iff_op` / 引理 `isClosedUnderLimitsOfShape_op_iff_op`

English:
lemma isClosedUnderLimitsOfShape_op_iff_op
  proof: by
  rw [isClosedUnderColimitsOfShape_iff]; rw [isClosedUnderLimitsOfShape_iff]; rw [colimitsOfShape_op]; rw [op_monotone_iff]

中文:
引理 isClosedUnderLimitsOfShape_op_iff_op
  证明: by
  rw [isClosedUnderColimitsOfShape_iff]; rw [isClosedUnderLimitsOfShape_iff]; rw [colimitsOfShape_op]; rw [op_monotone_iff]

Depends on / 依赖: colimitsOfShape_op, isClosedUnderColimitsOfShape_iff, isClosedUnderLimitsOfShape_iff, op_monotone_iff
-/
lemma isClosedUnderLimitsOfShape_op_iff_op :
    P.IsClosedUnderLimitsOfShape Jᵒᵖ ↔
      P.op.IsClosedUnderColimitsOfShape J := by
  rw [isClosedUnderColimitsOfShape_iff]; rw [isClosedUnderLimitsOfShape_iff]; rw [colimitsOfShape_op]; rw [op_monotone_iff]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsClosedUnderColimitsOfShape
  signature: J] :
  body: by
  rwa [← isClosedUnderColimitsOfShape_iff_op]

中文:
实例 [P.IsClosedUnderColimitsOfShape
  签名: J] :
  定义体: by
  rwa [← isClosedUnderColimitsOfShape_iff_op]

Depends on / 依赖: isClosedUnderColimitsOfShape_iff_op
-/
instance [P.IsClosedUnderColimitsOfShape J] :
    P.op.IsClosedUnderLimitsOfShape Jᵒᵖ := by
  rwa [← isClosedUnderColimitsOfShape_iff_op]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsClosedUnderLimitsOfShape
  signature: J] :
  body: by
  rwa [← isClosedUnderLimitsOfShape_iff_op]

中文:
实例 [P.IsClosedUnderLimitsOfShape
  签名: J] :
  定义体: by
  rwa [← isClosedUnderLimitsOfShape_iff_op]

Depends on / 依赖: isClosedUnderLimitsOfShape_iff_op
-/
instance [P.IsClosedUnderLimitsOfShape J] :
    P.op.IsClosedUnderColimitsOfShape Jᵒᵖ := by
  rwa [← isClosedUnderLimitsOfShape_iff_op]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsClosedUnderColimitsOfShape
  signature: Jᵒᵖ] :
  body: by
  rwa [← isClosedUnderColimitsOfShape_op_iff_op]

中文:
实例 [P.IsClosedUnderColimitsOfShape
  签名: Jᵒᵖ] :
  定义体: by
  rwa [← isClosedUnderColimitsOfShape_op_iff_op]

Depends on / 依赖: infer_instance, isClosedUnderColimitsOfShape_op_iff_op
-/
instance [P.IsClosedUnderColimitsOfShape Jᵒᵖ] :
    P.op.IsClosedUnderLimitsOfShape J := by
  rwa [← isClosedUnderColimitsOfShape_op_iff_op]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsClosedUnderLimitsOfShape
  signature: Jᵒᵖ] :
  body: by
  rwa [← isClosedUnderLimitsOfShape_op_iff_op]

中文:
实例 [P.IsClosedUnderLimitsOfShape
  签名: Jᵒᵖ] :
  定义体: by
  rwa [← isClosedUnderLimitsOfShape_op_iff_op]

Depends on / 依赖: infer_instance, isClosedUnderLimitsOfShape_op_iff_op
-/
instance [P.IsClosedUnderLimitsOfShape Jᵒᵖ] :
    P.op.IsClosedUnderColimitsOfShape J := by
  rwa [← isClosedUnderLimitsOfShape_op_iff_op]

section

variable (Q : ObjectProperty Cᵒᵖ)

/--
lemma `isClosedUnderColimitsOfShape_iff_unop` / 引理 `isClosedUnderColimitsOfShape_iff_unop`

English:
lemma isClosedUnderColimitsOfShape_iff_unop
  proof: (Q.unop.isClosedUnderLimitsOfShape_op_iff_op J).symm

中文:
引理 isClosedUnderColimitsOfShape_iff_unop
  证明: (Q.unop.isClosedUnderLimitsOfShape_op_iff_op J).symm

Depends on / 依赖: Q.unop.isClosedUnderLimitsOfShape_op_iff_op, isClosedUnderLimitsOfShape_op_iff_op
-/
lemma isClosedUnderColimitsOfShape_iff_unop :
    Q.IsClosedUnderColimitsOfShape J ↔
      Q.unop.IsClosedUnderLimitsOfShape Jᵒᵖ :=
  (Q.unop.isClosedUnderLimitsOfShape_op_iff_op J).symm

/--
lemma `isClosedUnderLimitsOfShape_iff_unop` / 引理 `isClosedUnderLimitsOfShape_iff_unop`

English:
lemma isClosedUnderLimitsOfShape_iff_unop
  proof: (Q.unop.isClosedUnderColimitsOfShape_op_iff_op J).symm

中文:
引理 isClosedUnderLimitsOfShape_iff_unop
  证明: (Q.unop.isClosedUnderColimitsOfShape_op_iff_op J).symm

Depends on / 依赖: Q.unop.isClosedUnderColimitsOfShape_op_iff_op, isClosedUnderColimitsOfShape_op_iff_op
-/
lemma isClosedUnderLimitsOfShape_iff_unop :
    Q.IsClosedUnderLimitsOfShape J ↔
      Q.unop.IsClosedUnderColimitsOfShape Jᵒᵖ :=
  (Q.unop.isClosedUnderColimitsOfShape_op_iff_op J).symm

/--
lemma `isClosedUnderColimitsOfShape_op_iff_unop` / 引理 `isClosedUnderColimitsOfShape_op_iff_unop`

English:
lemma isClosedUnderColimitsOfShape_op_iff_unop
  proof: (Q.unop.isClosedUnderLimitsOfShape_iff_op J).symm

中文:
引理 isClosedUnderColimitsOfShape_op_iff_unop
  证明: (Q.unop.isClosedUnderLimitsOfShape_iff_op J).symm

Depends on / 依赖: Q.unop.isClosedUnderLimitsOfShape_iff_op, isClosedUnderLimitsOfShape_iff_op
-/
lemma isClosedUnderColimitsOfShape_op_iff_unop :
    Q.IsClosedUnderColimitsOfShape Jᵒᵖ ↔
      Q.unop.IsClosedUnderLimitsOfShape J :=
  (Q.unop.isClosedUnderLimitsOfShape_iff_op J).symm

/--
lemma `isClosedUnderLimitsOfShape_op_iff_unop` / 引理 `isClosedUnderLimitsOfShape_op_iff_unop`

English:
lemma isClosedUnderLimitsOfShape_op_iff_unop
  proof: (Q.unop.isClosedUnderColimitsOfShape_iff_op J).symm

中文:
引理 isClosedUnderLimitsOfShape_op_iff_unop
  证明: (Q.unop.isClosedUnderColimitsOfShape_iff_op J).symm

Depends on / 依赖: Q.unop.isClosedUnderColimitsOfShape_iff_op, isClosedUnderColimitsOfShape_iff_op
-/
lemma isClosedUnderLimitsOfShape_op_iff_unop :
    Q.IsClosedUnderLimitsOfShape Jᵒᵖ ↔
      Q.unop.IsClosedUnderColimitsOfShape J :=
  (Q.unop.isClosedUnderColimitsOfShape_iff_op J).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Q.IsClosedUnderColimitsOfShape
  signature: J] :
  body: by
  rwa [← isClosedUnderColimitsOfShape_iff_unop]

中文:
实例 [Q.IsClosedUnderColimitsOfShape
  签名: J] :
  定义体: by
  rwa [← isClosedUnderColimitsOfShape_iff_unop]

Depends on / 依赖: isClosedUnderColimitsOfShape_iff_unop
-/
instance [Q.IsClosedUnderColimitsOfShape J] :
    Q.unop.IsClosedUnderLimitsOfShape Jᵒᵖ := by
  rwa [← isClosedUnderColimitsOfShape_iff_unop]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Q.IsClosedUnderLimitsOfShape
  signature: J] :
  body: by
  rwa [← isClosedUnderLimitsOfShape_iff_unop]

中文:
实例 [Q.IsClosedUnderLimitsOfShape
  签名: J] :
  定义体: by
  rwa [← isClosedUnderLimitsOfShape_iff_unop]

Depends on / 依赖: isClosedUnderLimitsOfShape_iff_unop
-/
instance [Q.IsClosedUnderLimitsOfShape J] :
    Q.unop.IsClosedUnderColimitsOfShape Jᵒᵖ := by
  rwa [← isClosedUnderLimitsOfShape_iff_unop]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Q.IsClosedUnderColimitsOfShape
  signature: Jᵒᵖ] :
  body: by
  rwa [← isClosedUnderColimitsOfShape_op_iff_unop]

中文:
实例 [Q.IsClosedUnderColimitsOfShape
  签名: Jᵒᵖ] :
  定义体: by
  rwa [← isClosedUnderColimitsOfShape_op_iff_unop]

Depends on / 依赖: isClosedUnderColimitsOfShape_op_iff_unop
-/
instance [Q.IsClosedUnderColimitsOfShape Jᵒᵖ] :
    Q.unop.IsClosedUnderLimitsOfShape J := by
  rwa [← isClosedUnderColimitsOfShape_op_iff_unop]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Q.IsClosedUnderLimitsOfShape
  signature: Jᵒᵖ] :
  body: by
  rwa [← isClosedUnderLimitsOfShape_op_iff_unop]

中文:
实例 [Q.IsClosedUnderLimitsOfShape
  签名: Jᵒᵖ] :
  定义体: by
  rwa [← isClosedUnderLimitsOfShape_op_iff_unop]

Depends on / 依赖: isClosedUnderLimitsOfShape_op_iff_unop
-/
instance [Q.IsClosedUnderLimitsOfShape Jᵒᵖ] :
    Q.unop.IsClosedUnderColimitsOfShape J := by
  rwa [← isClosedUnderLimitsOfShape_op_iff_unop]

end

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsClosedUnderColimitsOfShape
  signature: WalkingParallelPair] :
  body: by
    let c : Cofork (h.r ≫ h.i) (𝟙 Y) := Cofork.ofπ h.r (by simp)
    have hc : IsColimit c :=
      Cofork.IsColimit.mk _ (fun s => h.i ≫ s.π)
        (fun s => by simpa using! s.condition)
        (fun s m hm => by dsimp [c] at hm; simp [← hm])
    exact P.prop_of_isColimit hc (by rintro (_ | _)

中文:
实例 [P.IsClosedUnderColimitsOfShape
  签名: WalkingParallelPair] :
  定义体: by
    let c : Cofork (h.r ≫ h.i) (𝟙 Y) := Cofork.ofπ h.r (by simp)
    have hc : IsColimit c :=
      Cofork.IsColimit.mk _ (fun s => h.i ≫ s.π)
        (fun s => by simpa using! s.condition)
        (fun s m hm => by dsimp [c] at hm; simp [← hm])
    exact P.prop_of_isColimit hc (by rintro (_ | _)

Depends on / 依赖: Cofork, Cofork.IsColimit.mk, Cofork.of, IsColimit, P.prop_of_isColimit, condition, prop_of_isColimit, s.condition
-/
instance [P.IsClosedUnderColimitsOfShape WalkingParallelPair] :
    P.IsStableUnderRetracts where
  of_retract {X Y} h hY := by
    let c : Cofork (h.r ≫ h.i) (𝟙 Y) := Cofork.ofπ h.r (by simp)
    have hc : IsColimit c :=
      Cofork.IsColimit.mk _ (fun s => h.i ≫ s.π)
        (fun s => by simpa using! s.condition)
        (fun s m hm => by dsimp [c] at hm; simp [← hm])
    exact P.prop_of_isColimit hc (by rintro (_ | _) <;> exact hY)

/--
lemma `limitsOfShape_isEmpty_iff` / 引理 `limitsOfShape_isEmpty_iff`

English:
lemma limitsOfShape_isEmpty_iff
  given: [IsEmpty J] (X : C)
  proof: ⟨fun ⟨⟨f, p, q⟩, d⟩ => .intro isLimitEquivIsTerminalOfIsEmpty _ _ q, fun ⟨h⟩ =>
    ⟨⟨(Functor.const _).obj X, 𝟙 _, (isLimitEquivIsTerminalOfIsEmpty _ _).symm h⟩, by simp⟩⟩

中文:
引理 limitsOfShape_isEmpty_iff
  条件: [IsEmpty J] (X : C)
  证明: ⟨fun ⟨⟨f, p, q⟩, d⟩ => .intro isLimitEquivIsTerminalOfIsEmpty _ _ q, fun ⟨h⟩ =>
    ⟨⟨(Functor.const _).obj X, 𝟙 _, (isLimitEquivIsTerminalOfIsEmpty _ _).symm h⟩, by simp⟩⟩

Depends on / 依赖: Functor, Functor.const, isLimitEquivIsTerminalOfIsEmpty
-/
lemma limitsOfShape_isEmpty_iff [IsEmpty J] (X : C) :
    P.limitsOfShape J X ↔ Nonempty (IsTerminal X) :=
⟨fun ⟨⟨f, p, q⟩, d⟩ => .intro isLimitEquivIsTerminalOfIsEmpty _ _ q, fun ⟨h⟩ =>
    ⟨⟨(Functor.const _).obj X, 𝟙 _, (isLimitEquivIsTerminalOfIsEmpty _ _).symm h⟩, by simp⟩⟩

/--
lemma `colimitsOfShape_isEmpty_iff` / 引理 `colimitsOfShape_isEmpty_iff`

English:
lemma colimitsOfShape_isEmpty_iff
  given: [IsEmpty J] (X : C)
  proof: ⟨fun ⟨⟨f, p, q⟩, d⟩ => .intro isColimitEquivIsInitialOfIsEmpty _ _ q, fun ⟨h⟩ =>
    ⟨⟨(Functor.const _).obj X, 𝟙 _, (isColimitEquivIsInitialOfIsEmpty _ _).symm h⟩, by simp⟩⟩

中文:
引理 colimitsOfShape_isEmpty_iff
  条件: [IsEmpty J] (X : C)
  证明: ⟨fun ⟨⟨f, p, q⟩, d⟩ => .intro isColimitEquivIsInitialOfIsEmpty _ _ q, fun ⟨h⟩ =>
    ⟨⟨(Functor.const _).obj X, 𝟙 _, (isColimitEquivIsInitialOfIsEmpty _ _).symm h⟩, by simp⟩⟩

Depends on / 依赖: Functor, Functor.const, isColimitEquivIsInitialOfIsEmpty
-/
lemma colimitsOfShape_isEmpty_iff [IsEmpty J] (X : C) :
    P.colimitsOfShape J X ↔ Nonempty (IsInitial X) :=
⟨fun ⟨⟨f, p, q⟩, d⟩ => .intro isColimitEquivIsInitialOfIsEmpty _ _ q, fun ⟨h⟩ =>
    ⟨⟨(Functor.const _).obj X, 𝟙 _, (isColimitEquivIsInitialOfIsEmpty _ _).symm h⟩, by simp⟩⟩

end ObjectProperty

end CategoryTheory
