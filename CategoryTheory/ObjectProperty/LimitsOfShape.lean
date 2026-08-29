/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.Limits.Presentation

import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Objects that are limits of objects satisfying a certain property

Given a property of objects `P : ObjectProperty C` and a category `J`,
we introduce two properties of objects `P.strictLimitsOfShape J`
and `P.limitsOfShape J`. The former contains exactly the objects
of the form `limit F` for any functor `F : J ⥤ C` that has
a limit and such that `F.obj j` satisfies `P` for any `j`, while
the latter contains all the objects that are isomorphic to
these "chosen" objects `limit F`.

Under certain circumstances, the type of objects satisfying
`P.strictLimitsOfShape J` is small: the main reason this variant is
introduced is to deduce that the full subcategory of `P.limitsOfShape J`
is essentially small.

By requiring `P.limitsOfShape J ≤ P`, we introduce a typeclass
`P.IsClosedUnderLimitsOfShape J`.


## TODO

* formalize the closure of `P` under finite limits (which require
  iterating over `ℕ`), and more generally the closure under limits
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
Inductive type `strictLimitsOfShape` / 归纳类型 `strictLimitsOfShape`

English:
inductive strictLimitsOfShape
  parameters: : ObjectProperty C
  constructors (1):
    - limit: (F : J ⥤ C) [HasLimit F] (hF : forall j, P (F.obj j)) : strictLimitsOfShape (limit F)

中文:
归纳类型 strictLimitsOfShape
  参数: : Object命题erty C
  构造子 (1 个):
    - limit: (F : J ⥤ C) [HasLimit F] (hF : 对任意 j, P (F.obj j)) : strictLimitsOfShape (limit F)

Depends on / 依赖: Under.hasColimit_of_hasColimit_liftFromUnder, hasColimit_of_hasColimit_liftFromUnder
-/
inductive strictLimitsOfShape : ObjectProperty C
  | limit (F : J ⥤ C) [HasLimit F] (hF : forall j, P (F.obj j)) :
    strictLimitsOfShape (limit F)

variable {P} in
/--
lemma `strictLimitsOfShape_monotone` / 引理 `strictLimitsOfShape_monotone`

English:
lemma strictLimitsOfShape_monotone
  given: {Q : ObjectProperty C} (h : P <= Q)
  proof: by
  rintro _ ⟨F, hF⟩
  exact ⟨F, fun j => h _ (hF j)⟩

@[simp]

中文:
引理 strictLimitsOfShape_monotone
  条件: {Q : Object命题erty C} (h : P <= Q)
  证明: by
  rintro _ ⟨F, hF⟩
  exact ⟨F, fun j => h _ (hF j)⟩

@[simp]
-/
lemma strictLimitsOfShape_monotone {Q : ObjectProperty C} (h : P <= Q) :
    P.strictLimitsOfShape J <= Q.strictLimitsOfShape J := by
  rintro _ ⟨F, hF⟩
  exact ⟨F, fun j => h _ (hF j)⟩

@[simp]
/--
lemma `strictLimitsOfShape_bot` / 引理 `strictLimitsOfShape_bot`

English:
lemma strictLimitsOfShape_bot
  given: [Nonempty J]
  proof: by
  rw [eq_bot_iff]
  rintro _ ⟨_, h⟩
  exact h (Classical.arbitrary J)

中文:
引理 strictLimitsOfShape_bot
  条件: [Nonempty J]
  证明: by
  rw [eq_bot_iff]
  rintro _ ⟨_, h⟩
  exact h (Classical.arbitrary J)

Depends on / 依赖: Classical, Classical.arbitrary, arbitrary, eq_bot_iff
-/
lemma strictLimitsOfShape_bot [Nonempty J] :
    strictLimitsOfShape (⊥ : ObjectProperty C) J = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨_, h⟩
  exact h (Classical.arbitrary J)

/--
Definition of `LimitOfShape` / `LimitOfShape` 的定义

English:
structure LimitOfShape
  parameters: (X : C)
  extends: LimitPresentation J X
  axioms and operations (1):
    - prop_diag_obj((j : J)) : P (diag.obj j)

中文:
结构 LimitOfShape
  参数: (X : C)
  继承: LimitPresentation J X
  公理与运算 (1 个):
    - prop_diag_obj((j : J)) : P (diag.obj j)
-/
structure LimitOfShape (X : C) extends LimitPresentation J X where
  prop_diag_obj (j : J) : P (diag.obj j)

namespace LimitOfShape

variable {P J}

/--
Definition of `limit` / `limit` 的定义

English:
definition limit
  signature: (F : J ⥤ C) [HasLimit F] (hF : forall j, P (F.obj j))
  body: .limit F
  prop_diag_obj := hF

中文:
定义 limit
  签名: (F : J ⥤ C) [HasLimit F] (hF : 对任意 j, P (F.obj j))
  定义体: .limit F
  prop_diag_obj := hF
-/
noncomputable def limit (F : J ⥤ C) [HasLimit F] (hF : forall j, P (F.obj j)) :
    P.LimitOfShape J (limit F) where
  toLimitPresentation := .limit F
  prop_diag_obj := hF

/-- If `X` is a limit indexed by `J` of objects satisfying a property `P`, then
any object that is isomorphic to `X` also is. -/
@[simps toLimitPresentation]
/--
Definition of `ofIso` / `ofIso` 的定义

English:
definition ofIso
  signature: {X : C} (h : P.LimitOfShape J X) {Y : C} (e : X ≅ Y)
  body: .ofIso h.toLimitPresentation e
  prop_diag_obj := h.prop_diag_obj

中文:
定义 ofIso
  签名: {X : C} (h : P.LimitOfShape J X) {Y : C} (e : X ≅ Y)
  定义体: .ofIso h.toLimitPresentation e
  prop_diag_obj := h.prop_diag_obj

Depends on / 依赖: h.toLimitPresentation, toLimitPresentation
-/
def ofIso {X : C} (h : P.LimitOfShape J X) {Y : C} (e : X ≅ Y) :
    P.LimitOfShape J Y where
  toLimitPresentation := .ofIso h.toLimitPresentation e
  prop_diag_obj := h.prop_diag_obj

/-- If `X` is a limit indexed by `J` of objects satisfying a property `P`,
it is also a limit indexed by `J` of objects satisfying `Q` if `P ≤ Q`. -/
@[simps toLimitPresentation]
/--
Definition of `ofLE` / `ofLE` 的定义

English:
definition ofLE
  signature: {X : C} (h : P.LimitOfShape J X) {Q : ObjectProperty C} (hPQ : P <= Q)
  body: h.toLimitPresentation
  prop_diag_obj j := hPQ _ (h.prop_diag_obj j)

中文:
定义 ofLE
  签名: {X : C} (h : P.LimitOfShape J X) {Q : Object命题erty C} (hPQ : P <= Q)
  定义体: h.toLimitPresentation
  prop_diag_obj j := hPQ _ (h.prop_diag_obj j)

Depends on / 依赖: h.toLimitPresentation, toLimitPresentation
-/
def ofLE {X : C} (h : P.LimitOfShape J X) {Q : ObjectProperty C} (hPQ : P <= Q) :
    Q.LimitOfShape J X where
  toLimitPresentation := h.toLimitPresentation
  prop_diag_obj j := hPQ _ (h.prop_diag_obj j)

/-- Change the index category for `ObjectProperty.LimitOfShape`. -/
@[simps toLimitPresentation]
/--
Definition of `reindex` / `reindex` 的定义

English:
definition reindex
  signature: {X : C} (h : P.LimitOfShape J X) (G : J' ⥤ J) [G.Initial]
  body: h.toLimitPresentation.reindex G
  prop_diag_obj _ := h.prop_diag_obj _

中文:
定义 reindex
  签名: {X : C} (h : P.LimitOfShape J X) (G : J' ⥤ J) [G.Initial]
  定义体: h.toLimitPresentation.reindex G
  prop_diag_obj _ := h.prop_diag_obj _

Depends on / 依赖: h.toLimitPresentation.reindex, reindex, toLimitPresentation
-/
noncomputable def reindex {X : C} (h : P.LimitOfShape J X) (G : J' ⥤ J) [G.Initial] :
    P.LimitOfShape J' X where
  toLimitPresentation := h.toLimitPresentation.reindex G
  prop_diag_obj _ := h.prop_diag_obj _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Given `P : ObjectProperty C`, and a presentation `P.LimitOfShape J X`
of an object `X : C`, this is the induced functor `J ⥤ StructuredArrow P.ι X`. -/
@[simps]
/--
Definition of `toStructuredArrow` / `toStructuredArrow` 的定义

English:
definition toStructuredArrow
  body: StructuredArrow.mk (Y := ⟨_, p.prop_diag_obj j⟩) (by exact p.π.app j)
  map f := StructuredArrow.homMk (ObjectProperty.homMk (by exact p.diag.map f))
    (by simpa using (p.π.naturality f).symm)

中文:
定义 toStructuredArrow
  定义体: StructuredArrow.mk (Y := ⟨_, p.prop_diag_obj j⟩) (by exact p.π.app j)
  map f := StructuredArrow.homMk (ObjectProperty.homMk (by exact p.diag.map f))
    (by simpa using (p.π.naturality f).symm)

Depends on / 依赖: StructuredArrow, StructuredArrow.mk, p.prop_diag_obj, prop_diag_obj
-/
def toStructuredArrow
    {X : C} (p : P.LimitOfShape J X) :
    J ⥤ StructuredArrow X P.ι where
  obj j := StructuredArrow.mk (Y := ⟨_, p.prop_diag_obj j⟩) (by exact p.π.app j)
  map f := StructuredArrow.homMk (ObjectProperty.homMk (by exact p.diag.map f))
    (by simpa using (p.π.naturality f).symm)

end LimitOfShape

/--
Definition of `limitsOfShape` / `limitsOfShape` 的定义

English:
definition limitsOfShape
  signature: : ObjectProperty C
  body: fun X => Nonempty (P.LimitOfShape J X)

中文:
定义 limitsOfShape
  签名: : Object命题erty C
  定义体: fun X => Nonempty (P.LimitOfShape J X)

Depends on / 依赖: LimitOfShape, Nonempty, P.LimitOfShape
-/
def limitsOfShape : ObjectProperty C :=
  fun X => Nonempty (P.LimitOfShape J X)

variable {P J} in
/--
lemma `LimitOfShape.limitsOfShape` / 引理 `LimitOfShape.limitsOfShape`

English:
lemma LimitOfShape.limitsOfShape
  given: {X : C} (h : P.LimitOfShape J X)
  proof: ⟨h⟩

中文:
引理 LimitOfShape.limitsOfShape
  条件: {X : C} (h : P.LimitOfShape J X)
  证明: ⟨h⟩
-/
lemma LimitOfShape.limitsOfShape {X : C} (h : P.LimitOfShape J X) :
    P.limitsOfShape J X :=
  ⟨h⟩

/--
lemma `strictLimitsOfShape_le_limitsOfShape` / 引理 `strictLimitsOfShape_le_limitsOfShape`

English:
lemma strictLimitsOfShape_le_limitsOfShape
  proof: by
  rintro X ⟨F, hF⟩
  exact ⟨.limit F hF⟩

@[simp]

中文:
引理 strictLimitsOfShape_le_limitsOfShape
  证明: by
  rintro X ⟨F, hF⟩
  exact ⟨.limit F hF⟩

@[simp]
-/
lemma strictLimitsOfShape_le_limitsOfShape :
    P.strictLimitsOfShape J <= P.limitsOfShape J := by
  rintro X ⟨F, hF⟩
  exact ⟨.limit F hF⟩

@[simp]
/--
lemma `limitsOfShape_bot` / 引理 `limitsOfShape_bot`

English:
lemma limitsOfShape_bot
  given: [Nonempty J]
  statement: limitsOfShape (⊥ : ObjectProperty C) J = ⊥
  proof: by
  rw [eq_bot_iff]
  rintro X ⟨⟨_, h⟩⟩
  exact h (Classical.arbitrary J)

中文:
引理 limitsOfShape_bot
  条件: [Nonempty J]
  结论: limitsOfShape (⊥ : Object命题erty C) J = ⊥
  证明: by
  rw [eq_bot_iff]
  rintro X ⟨⟨_, h⟩⟩
  exact h (Classical.arbitrary J)

Depends on / 依赖: Classical, Classical.arbitrary, arbitrary, eq_bot_iff
-/
lemma limitsOfShape_bot [Nonempty J] : limitsOfShape (⊥ : ObjectProperty C) J = ⊥ := by
  rw [eq_bot_iff]
  rintro X ⟨⟨_, h⟩⟩
  exact h (Classical.arbitrary J)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (P.limitsOfShape J).IsClosedUnderIsomorphisms
  body: by rintro _ _ e ⟨h⟩; exact ⟨h.ofIso e⟩

@[simp]

中文:
实例 :
  签名: (P.limitsOfShape J).IsClosedUnderIsomorphisms
  定义体: by rintro _ _ e ⟨h⟩; exact ⟨h.ofIso e⟩

@[simp]

Depends on / 依赖: h.ofIso
-/
instance : (P.limitsOfShape J).IsClosedUnderIsomorphisms where
  of_iso := by rintro _ _ e ⟨h⟩; exact ⟨h.ofIso e⟩

@[simp]
/--
lemma `isoClosure_strictLimitsOfShape` / 引理 `isoClosure_strictLimitsOfShape`

English:
lemma isoClosure_strictLimitsOfShape
  proof: by
  refine le_antisymm ?_ ?_
  · rw [isoClosure_le_iff]
    apply strictLimitsOfShape_le_limitsOfShape
  · intro X ⟨h⟩
    have := h.hasLimit
    exact ⟨limit h.diag, strictLimitsOfShape.limit h.diag h.prop_diag_obj,
      ⟨h.isLimit.conePointUniqueUpToIso (limit.isLimit _)⟩⟩

中文:
引理 isoClosure_strictLimitsOfShape
  证明: by
  refine le_antisymm ?_ ?_
  · rw [isoClosure_le_iff]
    apply strictLimitsOfShape_le_limitsOfShape
  · intro X ⟨h⟩
    have := h.hasLimit
    exact ⟨limit h.diag, strictLimitsOfShape.limit h.diag h.prop_diag_obj,
      ⟨h.isLimit.conePointUniqueUpToIso (limit.isLimit _)⟩⟩

Depends on / 依赖: conePointUniqueUpToIso, h.diag, h.hasLimit, h.isLimit.conePointUniqueUpToIso, h.prop_diag_obj, hasLimit, isLimit, isoClosure_le_iff, le_antisymm, limit.isLimit, prop_diag_obj, strictLimitsOfShape, strictLimitsOfShape.limit, strictLimitsOfShape_le_limitsOfShape
-/
lemma isoClosure_strictLimitsOfShape :
    (P.strictLimitsOfShape J).isoClosure = P.limitsOfShape J := by
  refine le_antisymm ?_ ?_
  · rw [isoClosure_le_iff]
    apply strictLimitsOfShape_le_limitsOfShape
  · intro X ⟨h⟩
    have := h.hasLimit
    exact ⟨limit h.diag, strictLimitsOfShape.limit h.diag h.prop_diag_obj,
      ⟨h.isLimit.conePointUniqueUpToIso (limit.isLimit _)⟩⟩

variable {P} in
/--
lemma `limitsOfShape_monotone` / 引理 `limitsOfShape_monotone`

English:
lemma limitsOfShape_monotone
  given: {Q : ObjectProperty C} (hPQ : P <= Q)
  proof: by
  intro X ⟨h⟩
  exact ⟨h.ofLE hPQ⟩

@[simp]

中文:
引理 limitsOfShape_monotone
  条件: {Q : Object命题erty C} (hPQ : P <= Q)
  证明: by
  intro X ⟨h⟩
  exact ⟨h.ofLE hPQ⟩

@[simp]

Depends on / 依赖: h.ofLE
-/
lemma limitsOfShape_monotone {Q : ObjectProperty C} (hPQ : P <= Q) :
    P.limitsOfShape J <= Q.limitsOfShape J := by
  intro X ⟨h⟩
  exact ⟨h.ofLE hPQ⟩

@[simp]
/--
lemma `limitsOfShape_isoClosure` / 引理 `limitsOfShape_isoClosure`

English:
lemma limitsOfShape_isoClosure
  proof: by
  refine le_antisymm ?_ (limitsOfShape_monotone _ P.le_isoClosure)
  intro X ⟨h⟩
  choose obj h₁ h₂ using h.prop_diag_obj
  exact
   ⟨{ toLimitPresentation := h.changeDiag (h.diag.isoCopyObj obj (fun j => (h₂ j).some)).symm
      prop_diag_obj := h₁ }⟩

中文:
引理 limitsOfShape_isoClosure
  证明: by
  refine le_antisymm ?_ (limitsOfShape_monotone _ P.le_isoClosure)
  intro X ⟨h⟩
  choose obj h₁ h₂ using h.prop_diag_obj
  exact
   ⟨{ toLimitPresentation := h.changeDiag (h.diag.isoCopyObj obj (fun j => (h₂ j).some)).symm
      prop_diag_obj := h₁ }⟩

Depends on / 依赖: P.le_isoClosure, changeDiag, h.changeDiag, h.diag.isoCopyObj, h.prop_diag_obj, isoCopyObj, le_antisymm, le_isoClosure, limitsOfShape_monotone, prop_diag_obj, toLimitPresentation
-/
lemma limitsOfShape_isoClosure :
    P.isoClosure.limitsOfShape J = P.limitsOfShape J := by
  refine le_antisymm ?_ (limitsOfShape_monotone _ P.le_isoClosure)
  intro X ⟨h⟩
  choose obj h₁ h₂ using h.prop_diag_obj
  exact
   ⟨{ toLimitPresentation := h.changeDiag (h.diag.isoCopyObj obj (fun j => (h₂ j).some)).symm
      prop_diag_obj := h₁ }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [ObjectProperty.Small.{w}
  signature: P] [LocallySmall.{w} C] [Small.{w} J] [LocallySmall.{w} J] :
  body: by
  refine small_of_surjective
    (f := fun (F : { F : J ⥤ P.FullSubcategory // HasLimit (F ⋙ P.ι) }) =>
      (⟨_, letI := F.2; ⟨F.1 ⋙ P.ι, fun j => (F.1.obj j).2⟩⟩)) ?_
  rintro ⟨_, ⟨F, hF⟩⟩
  exact ⟨⟨P.lift F hF, by assumption⟩, rfl⟩

中文:
实例 [ObjectProperty.Small.{w}
  签名: P] [LocallySmall.{w} C] [Small.{w} J] [LocallySmall.{w} J] :
  定义体: by
  refine small_of_surjective
    (f := fun (F : { F : J ⥤ P.FullSubcategory // HasLimit (F ⋙ P.ι) }) =>
      (⟨_, letI := F.2; ⟨F.1 ⋙ P.ι, fun j => (F.1.obj j).2⟩⟩)) ?_
  rintro ⟨_, ⟨F, hF⟩⟩
  exact ⟨⟨P.lift F hF, by assumption⟩, rfl⟩

Depends on / 依赖: FullSubcategory, HasLimit, P.FullSubcategory, P.lift, small_of_surjective
-/
instance [ObjectProperty.Small.{w} P] [LocallySmall.{w} C] [Small.{w} J] [LocallySmall.{w} J] :
    ObjectProperty.Small.{w} (P.strictLimitsOfShape J) := by
  refine small_of_surjective
    (f := fun (F : { F : J ⥤ P.FullSubcategory // HasLimit (F ⋙ P.ι) }) =>
      (⟨_, letI := F.2; ⟨F.1 ⋙ P.ι, fun j => (F.1.obj j).2⟩⟩)) ?_
  rintro ⟨_, ⟨F, hF⟩⟩
  exact ⟨⟨P.lift F hF, by assumption⟩, rfl⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [ObjectProperty.Small.{w}
  signature: P] [LocallySmall.{w} C] [Small.{w} J] [LocallySmall.{w} J] :
  body: by
  rw [← isoClosure_strictLimitsOfShape]
  infer_instance

中文:
实例 [ObjectProperty.Small.{w}
  签名: P] [LocallySmall.{w} C] [Small.{w} J] [LocallySmall.{w} J] :
  定义体: by
  rw [← isoClosure_strictLimitsOfShape]
  infer_instance

Depends on / 依赖: infer_instance, isoClosure_strictLimitsOfShape
-/
instance [ObjectProperty.Small.{w} P] [LocallySmall.{w} C] [Small.{w} J] [LocallySmall.{w} J] :
    ObjectProperty.EssentiallySmall.{w} (P.limitsOfShape J) := by
  rw [← isoClosure_strictLimitsOfShape]
  infer_instance

/-- A property of objects satisfies `P.IsClosedUnderLimitsOfShape J` if it
is stable by limits of shape `J`. -/
@[mk_iff]
/--
Definition of `IsClosedUnderLimitsOfShape` / `IsClosedUnderLimitsOfShape` 的定义

English:
class IsClosedUnderLimitsOfShape
  parameters: (P : ObjectProperty C) (J : Type u') [Category.{v'} J]
  axioms and operations (1):
    - limitsOfShape_le((P J)) : P.limitsOfShape J <= P

中文:
类 IsClosedUnderLimitsOfShape
  参数: (P : Object命题erty C) (J : 类型u') [Category.{v'} J]
  公理与运算 (1 个):
    - limitsOfShape_le((P J)) : P.limitsOfShape J <= P
-/
class IsClosedUnderLimitsOfShape (P : ObjectProperty C) (J : Type u') [Category.{v'} J] where
  limitsOfShape_le (P J) : P.limitsOfShape J <= P

variable {P J} in
/--
lemma `IsClosedUnderLimitsOfShape.mk'` / 引理 `IsClosedUnderLimitsOfShape.mk'`

English:
lemma IsClosedUnderLimitsOfShape.mk'
  statement: [P.IsClosedUnderIsomorphisms]
  proof: by
    conv_rhs => rw [← P.isoClosure_eq_self]
    rw [← isoClosure_strictLimitsOfShape]
    exact monotone_isoClosure h

中文:
引理 IsClosedUnderLimitsOfShape.mk'
  结论: [P.IsClosedUnderIsomorphisms]
  证明: by
    conv_rhs => rw [← P.isoClosure_eq_self]
    rw [← isoClosure_strictLimitsOfShape]
    exact monotone_isoClosure h

Depends on / 依赖: P.isoClosure_eq_self, conv_rhs, isoClosure_eq_self, isoClosure_strictLimitsOfShape, monotone_isoClosure
-/
lemma IsClosedUnderLimitsOfShape.mk' [P.IsClosedUnderIsomorphisms]
    (h : P.strictLimitsOfShape J <= P) :
    P.IsClosedUnderLimitsOfShape J where
  limitsOfShape_le := by
    conv_rhs => rw [← P.isoClosure_eq_self]
    rw [← isoClosure_strictLimitsOfShape]
    exact monotone_isoClosure h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: J] : IsClosedUnderLimitsOfShape (⊥
  body: by rw [limitsOfShape_bot]

中文:
实例 [Nonempty
  签名: J] : IsClosedUnderLimitsOfShape (⊥
  定义体: by rw [limitsOfShape_bot]

Depends on / 依赖: limitsOfShape_bot
-/
instance [Nonempty J] : IsClosedUnderLimitsOfShape (⊥ : ObjectProperty C) J where
  limitsOfShape_le := by rw [limitsOfShape_bot]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsClosedUnderLimitsOfShape (⊤ : ObjectProperty C) J
  body: by trivial

中文:
实例 :
  签名: IsClosedUnderLimitsOfShape (⊤ : Object命题erty C) J
  定义体: by trivial
-/
instance : IsClosedUnderLimitsOfShape (⊤ : ObjectProperty C) J where
  limitsOfShape_le _ _ := by trivial

export IsClosedUnderLimitsOfShape (limitsOfShape_le)

section

variable {J} [P.IsClosedUnderLimitsOfShape J]

variable {P} in
/--
lemma `LimitOfShape.prop` / 引理 `LimitOfShape.prop`

English:
lemma LimitOfShape.prop
  given: {X : C} (h : P.LimitOfShape J X)
  statement: P X
  proof: P.limitsOfShape_le J _ ⟨h⟩

中文:
引理 LimitOfShape.prop
  条件: {X : C} (h : P.LimitOfShape J X)
  结论: P X
  证明: P.limitsOfShape_le J _ ⟨h⟩

Depends on / 依赖: P.limitsOfShape_le, limitsOfShape_le
-/
lemma LimitOfShape.prop {X : C} (h : P.LimitOfShape J X) : P X :=
  P.limitsOfShape_le J _ ⟨h⟩

/--
lemma `prop_of_isLimit` / 引理 `prop_of_isLimit`

English:
lemma prop_of_isLimit
  statement: {F : J ⥤ C} {c : Cone F} (hc : IsLimit c)
  proof: P.limitsOfShape_le J _ ⟨{ diag := _, π := _, isLimit := hc, prop_diag_obj := hF }⟩

中文:
引理 prop_of_isLimit
  结论: {F : J ⥤ C} {c : Cone F} (hc : IsLimit c)
  证明: P.limitsOfShape_le J _ ⟨{ diag := _, π := _, isLimit := hc, prop_diag_obj := hF }⟩

Depends on / 依赖: P.limitsOfShape_le, isLimit, limitsOfShape_le, prop_diag_obj
-/
lemma prop_of_isLimit {F : J ⥤ C} {c : Cone F} (hc : IsLimit c)
    (hF : forall (j : J), P (F.obj j)) : P c.pt :=
  P.limitsOfShape_le J _ ⟨{ diag := _, π := _, isLimit := hc, prop_diag_obj := hF }⟩

/--
lemma `prop_limit` / 引理 `prop_limit`

English:
lemma prop_limit
  given: (F : J ⥤ C) [HasLimit F] (hF : forall (j : J), P (F.obj j))
  proof: P.prop_of_isLimit (limit.isLimit F) hF

中文:
引理 prop_limit
  条件: (F : J ⥤ C) [HasLimit F] (hF : 对任意 (j : J), P (F.obj j))
  证明: P.prop_of_isLimit (limit.isLimit F) hF

Depends on / 依赖: P.prop_of_isLimit, isLimit, limit.isLimit, prop_of_isLimit
-/
lemma prop_limit (F : J ⥤ C) [HasLimit F] (hF : forall (j : J), P (F.obj j)) :
    P (limit F) :=
  P.prop_of_isLimit (limit.isLimit F) hF

end

/--
lemma `prop_pi` / 引理 `prop_pi`

English:
lemma prop_pi
  statement: {J : Type*} [P.IsClosedUnderLimitsOfShape (Discrete J)] (X : J -> C)
  proof: P.prop_of_isLimit (productIsProduct X) (fun _ => hF _)

中文:
引理 prop_pi
  结论: {J : 类型} [P.IsClosedUnderLimitsOfShape (Discrete J)] (X : J -> C)
  证明: P.prop_of_isLimit (productIsProduct X) (fun _ => hF _)

Depends on / 依赖: P.prop_of_isLimit, productIsProduct, prop_of_isLimit
-/
lemma prop_pi {J : Type*} [P.IsClosedUnderLimitsOfShape (Discrete J)] (X : J -> C)
    [HasProduct X] (hF : forall (j : J), P (X j)) :
    P (∏ᶜ X) :=
  P.prop_of_isLimit (productIsProduct X) (fun _ => hF _)

variable {J} in
/--
lemma `limitsOfShape_le_of_initial` / 引理 `limitsOfShape_le_of_initial`

English:
lemma limitsOfShape_le_of_initial
  given: (G : J ⥤ J') [G.Initial]
  proof: fun _h ⟨h⟩ => ⟨h.reindex G⟩

中文:
引理 limitsOfShape_le_of_initial
  条件: (G : J ⥤ J') [G.Initial]
  证明: fun _h ⟨h⟩ => ⟨h.reindex G⟩

Depends on / 依赖: h.reindex, reindex
-/
lemma limitsOfShape_le_of_initial (G : J ⥤ J') [G.Initial] :
    P.limitsOfShape J' <= P.limitsOfShape J :=
  fun _h ⟨h⟩ => ⟨h.reindex G⟩

variable {J} in
/--
lemma `limitsOfShape_congr` / 引理 `limitsOfShape_congr`

English:
lemma limitsOfShape_congr
  given: (e : J ≌ J')
  proof: le_antisymm (P.limitsOfShape_le_of_initial e.inverse)
    (P.limitsOfShape_le_of_initial e.functor)

中文:
引理 limitsOfShape_congr
  条件: (e : J ≌ J')
  证明: le_antisymm (P.limitsOfShape_le_of_initial e.inverse)
    (P.limitsOfShape_le_of_initial e.functor)

Depends on / 依赖: P.limitsOfShape_le_of_initial, e.functor, e.inverse, functor, inverse, le_antisymm, limitsOfShape_le_of_initial
-/
lemma limitsOfShape_congr (e : J ≌ J') :
    P.limitsOfShape J = P.limitsOfShape J' :=
  le_antisymm (P.limitsOfShape_le_of_initial e.inverse)
    (P.limitsOfShape_le_of_initial e.functor)

variable {J} in
/--
lemma `isClosedUnderLimitsOfShape_iff_of_equivalence` / 引理 `isClosedUnderLimitsOfShape_iff_of_equivalence`

English:
lemma isClosedUnderLimitsOfShape_iff_of_equivalence
  given: (e : J ≌ J')
  proof: by
  simp only [isClosedUnderLimitsOfShape_iff, P.limitsOfShape_congr e]

中文:
引理 isClosedUnderLimitsOfShape_iff_of_equivalence
  条件: (e : J ≌ J')
  证明: by
  simp only [isClosedUnderLimitsOfShape_iff, P.limitsOfShape_congr e]

Depends on / 依赖: P.limitsOfShape_congr, isClosedUnderLimitsOfShape_iff, limitsOfShape_congr
-/
lemma isClosedUnderLimitsOfShape_iff_of_equivalence (e : J ≌ J') :
    P.IsClosedUnderLimitsOfShape J ↔
      P.IsClosedUnderLimitsOfShape J' := by
  simp only [isClosedUnderLimitsOfShape_iff, P.limitsOfShape_congr e]

variable {P J} in
/--
lemma `IsClosedUnderLimitsOfShape.of_equivalence` / 引理 `IsClosedUnderLimitsOfShape.of_equivalence`

English:
lemma IsClosedUnderLimitsOfShape.of_equivalence
  statement: (e : J ≌ J')
  proof: by
  rwa [← P.isClosedUnderLimitsOfShape_iff_of_equivalence e]

中文:
引理 IsClosedUnderLimitsOfShape.of_equivalence
  结论: (e : J ≌ J')
  证明: by
  rwa [← P.isClosedUnderLimitsOfShape_iff_of_equivalence e]

Depends on / 依赖: P.isClosedUnderLimitsOfShape_iff_of_equivalence, isClosedUnderLimitsOfShape_iff_of_equivalence
-/
lemma IsClosedUnderLimitsOfShape.of_equivalence (e : J ≌ J')
    [P.IsClosedUnderLimitsOfShape J] :
    P.IsClosedUnderLimitsOfShape J' := by
  rwa [← P.isClosedUnderLimitsOfShape_iff_of_equivalence e]

/--
Instance `IsClosedUnderLimitsOfShape.inverseImage` / 实例 `IsClosedUnderLimitsOfShape.inverseImage`

English:
instance IsClosedUnderLimitsOfShape.inverseImage
  body: ⟨fun _ ⟨c, H⟩ => ObjectProperty.LimitOfShape.prop (P := P) ⟨c.map F, H⟩⟩

中文:
实例 IsClosedUnderLimitsOfShape.inverseImage
  定义体: ⟨fun _ ⟨c, H⟩ => ObjectProperty.LimitOfShape.prop (P := P) ⟨c.map F, H⟩⟩

Depends on / 依赖: LimitOfShape, ObjectProperty, ObjectProperty.LimitOfShape.prop, c.map
-/
instance IsClosedUnderLimitsOfShape.inverseImage
    (P : ObjectProperty D) (F : C ⥤ D) [P.IsClosedUnderLimitsOfShape J]
    [PreservesLimitsOfShape J F] : (P.inverseImage F).IsClosedUnderLimitsOfShape J :=
  ⟨fun _ ⟨c, H⟩ => ObjectProperty.LimitOfShape.prop (P := P) ⟨c.map F, H⟩⟩

/--
lemma `isClosedUnderLimitsOfShape_inverseImage_iff` / 引理 `isClosedUnderLimitsOfShape_inverseImage_iff`

English:
lemma isClosedUnderLimitsOfShape_inverseImage_iff
  statement: (P : ObjectProperty D)
  proof: by
  refine ⟨fun H => ?_, fun _ => inferInstance⟩
  convert!
    (inferInstance :
      ((P.inverseImage e.functor).inverseImage e.inverse).IsClosedUnderLimitsOfShape J)
  ext X
  simpa using P.prop_iff_of_iso (e.counitIso.app X).symm

中文:
引理 isClosedUnderLimitsOfShape_inverseImage_iff
  结论: (P : Object命题erty D)
  证明: by
  refine ⟨fun H => ?_, fun _ => inferInstance⟩
  convert!
    (inferInstance :
      ((P.inverseImage e.functor).inverseImage e.inverse).IsClosedUnderLimitsOfShape J)
  ext X
  simpa using P.prop_iff_of_iso (e.counitIso.app X).symm

Depends on / 依赖: IsClosedUnderLimitsOfShape, P.inverseImage, P.prop_iff_of_iso, convert, counitIso, e.counitIso.app, e.functor, e.inverse, functor, inverse, inverseImage, prop_iff_of_iso
-/
lemma isClosedUnderLimitsOfShape_inverseImage_iff (P : ObjectProperty D)
    [P.IsClosedUnderIsomorphisms] (e : C ≌ D) :
    (P.inverseImage e.functor).IsClosedUnderLimitsOfShape J ↔ P.IsClosedUnderLimitsOfShape J := by
  refine ⟨fun H => ?_, fun _ => inferInstance⟩
  convert!
    (inferInstance :
      ((P.inverseImage e.functor).inverseImage e.inverse).IsClosedUnderLimitsOfShape J)
  ext X
  simpa using P.prop_iff_of_iso (e.counitIso.app X).symm

end ObjectProperty

end CategoryTheory
