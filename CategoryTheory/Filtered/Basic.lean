/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.Data.Fin.VecNotation

/-!
# Filtered categories

A category is filtered if every finite diagram admits a cocone.
We give a simple characterisation of this condition as
1. for every pair of objects there exists another object "to the right",
2. for every pair of parallel morphisms there exists a morphism to the right so the compositions
   are equal, and
3. there exists some object.

An important example of filtered category is given by nonempty directed types;
actually, filtered categories may be considered as a generalization of nonempty directed types.
In the file `CategoryTheory.Presentable.Directed`, we show that "conversely"
if `C` is a filtered category, there exists a final functor `α ⥤ C` from
a nonempty directed type (`IsFiltered.isDirected`).

Filtered colimits are often better behaved than arbitrary colimits.
See `Mathlib/CategoryTheory/Limits/Types/` for some details.

Filtered categories are nice because colimits indexed by filtered categories tend to be
easier to describe than general colimits (and more often preserved by functors).

In this file we show that any functor from a finite category to a filtered category admits a cocone:
* `cocone_nonempty [FinCategory J] [IsFiltered C] (F : J ⥤ C) : Nonempty (Cocone F)`

More generally,
for any finite collection of objects and morphisms between them in a filtered category
(even if not closed under composition) there exists some object `Z` receiving maps from all of them,
so that all the triangles (one edge from the finite set, two from morphisms to `Z`) commute.
This formulation is often more useful in practice and is available via `sup_exists`,
which takes a finset of objects, and an indexed family (indexed by source and target)
of finsets of morphisms.

We also prove the converse of `cocone_nonempty` as `of_cocone_nonempty`.

Furthermore, we give special support for two diagram categories: The `bowtie` and the `tulip`.
This is because these shapes show up in the proofs that forgetful functors of algebraic categories
(e.g. `MonCat`, `CommRingCat`, ...) preserve filtered colimits.

All of the above API, except for the `bowtie` and the `tulip`, is also provided for cofiltered
categories.

## See also
In `Mathlib/CategoryTheory/Limits/FilteredColimitCommutesFiniteLimit.lean` we show that filtered
colimits commute with finite limits.

There is another characterization of filtered categories, namely that whenever `F : J ⥤ C` is a
functor from a finite category, there is `X : C` such that `Nonempty (limit (F.op ⋙ yoneda.obj X))`.
This is shown in `Mathlib/CategoryTheory/Limits/Filtered.lean`.

-/

@[expose] public section


open Function

-- declare the `v`'s first; see `CategoryTheory.Category` for an explanation
universe w v v₁ v₂ u u₁ u₂

namespace CategoryTheory

attribute [local instance] uliftCategory

variable (C : Type u) [Category.{v} C]

/--
Definition of `IsFilteredOrEmpty` / `IsFilteredOrEmpty` 的定义

English:
class IsFilteredOrEmpty
  parameters: : Prop where
  axioms and operations (2):
    - cocone_objs : forall X Y : C, exists (Z : _) (_ : X ⟶ Z) (_ : Y ⟶ Z), True
    - cocone_maps : forall ⦃X Y : C⦄ (f g : X ⟶ Y), exists (Z : _) (h : Y ⟶ Z), f ≫ h = g ≫ h

中文:
类 是FilteredOrEmpty
  参数: : 命题 where
  公理与运算 (2 个):
    - cocone_objs : 对任意 X Y : C, 存在 (Z : _) (_ : X ⟶ Z) (_ : Y ⟶ Z), 真
    - cocone_maps : 对任意 ⦃X Y : C⦄ (f g : X ⟶ Y), 存在 (Z : _) (h : Y ⟶ Z), f ≫ h = g ≫ h
-/
class IsFilteredOrEmpty : Prop where
  /-- for every pair of objects there exists another object "to the right" -/
  cocone_objs : forall X Y : C, exists (Z : _) (_ : X ⟶ Z) (_ : Y ⟶ Z), True
  /-- for every pair of parallel morphisms there exists a morphism to the right
  so the compositions are equal -/
  cocone_maps : forall ⦃X Y : C⦄ (f g : X ⟶ Y), exists (Z : _) (h : Y ⟶ Z), f ≫ h = g ≫ h

/-- A category `IsFiltered` if
1. for every pair of objects there exists another object "to the right",
2. for every pair of parallel morphisms there exists a morphism to the right so the compositions
   are equal, and
3. there exists some object. -/
@[stacks 002V "They also define a diagram being filtered."]
/--
Definition of `IsFiltered` / `IsFiltered` 的定义

English:
class IsFiltered
  parameters: : Prop extends IsFilteredOrEmpty C where
  extends: IsFilteredOrEmpty C
  axioms and operations (1):
    - [nonempty : Nonempty C]

中文:
类 是Filtered
  参数: : 命题 extends 是FilteredOrEmpty C where
  继承: 是FilteredOrEmpty C
  公理与运算 (1 个):
    - [nonempty : 非空 C]
-/
class IsFiltered : Prop extends IsFilteredOrEmpty C where
  /-- a filtered category must be non-empty -/
  -- This should be an instance but it causes significant slowdown
  [nonempty : Nonempty C]

instance (priority := 100) isFilteredOrEmpty_of_semilatticeSup (α : Type u) [SemilatticeSup α] :
    IsFilteredOrEmpty α where
  cocone_objs X Y := ⟨X ⊔ Y, homOfLE le_sup_left, homOfLE le_sup_right, trivial⟩
  cocone_maps X Y f g := ⟨Y, 𝟙 _, by subsingleton⟩

instance (priority := 100) isFiltered_of_semilatticeSup_nonempty (α : Type u) [SemilatticeSup α]
    [Nonempty α] : IsFiltered α where

instance (priority := 100) isFilteredOrEmpty_of_directed_le (α : Type u) [Preorder α]
    [IsDirectedOrder α] : IsFilteredOrEmpty α where
  cocone_objs X Y :=
    let ⟨Z, h1, h2⟩ := exists_ge_ge X Y
    ⟨Z, homOfLE h1, homOfLE h2, trivial⟩
  cocone_maps X Y f g := ⟨Y, 𝟙 _, by subsingleton⟩

instance (priority := 100) isFiltered_of_directed_le_nonempty (α : Type u) [Preorder α]
    [IsDirectedOrder α] [Nonempty α] : IsFiltered α where

-- Sanity checks
example (α : Type u) [SemilatticeSup α] [OrderBot α] : IsFiltered α := by infer_instance

example (α : Type u) [SemilatticeSup α] [OrderTop α] : IsFiltered α := by infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsFiltered (Discrete PUnit)
  body: ⟨⟨PUnit.unit⟩, ⟨⟨by trivial⟩⟩, ⟨⟨by subsingleton⟩⟩, trivial⟩
  cocone_maps X Y f g := ⟨⟨PUnit.unit⟩, ⟨⟨by trivial⟩⟩, by subsingleton⟩

中文:
实例 :
  签名: 是Filtered (离散 命题单元)
  定义体: ⟨⟨PUnit.unit⟩, ⟨⟨by trivial⟩⟩, ⟨⟨by subsingleton⟩⟩, trivial⟩
  cocone_maps X Y f g := ⟨⟨PUnit.unit⟩, ⟨⟨by trivial⟩⟩, by subsingleton⟩
-/
instance : IsFiltered (Discrete PUnit) where
  cocone_objs X Y := ⟨⟨PUnit.unit⟩, ⟨⟨by trivial⟩⟩, ⟨⟨by subsingleton⟩⟩, trivial⟩
  cocone_maps X Y f g := ⟨⟨PUnit.unit⟩, ⟨⟨by trivial⟩⟩, by subsingleton⟩

namespace IsFiltered

section AllowEmpty

variable {C}
variable [IsFilteredOrEmpty C]

/--
Definition of `max` / `max` 的定义

English:
definition max
  signature: (j j' : C)
  body: (IsFilteredOrEmpty.cocone_objs j j').choose

中文:
定义 最大值
  签名: (j j' : C)
  定义体: (IsFilteredOrEmpty.cocone_objs j j').choose

Depends on / 依赖: IsFilteredOrEmpty, IsFilteredOrEmpty.cocone_objs, cocone_objs
-/
noncomputable def max (j j' : C) : C :=
  (IsFilteredOrEmpty.cocone_objs j j').choose

/--
Definition of `leftToMax` / `leftToMax` 的定义

English:
definition leftToMax
  signature: (j j' : C)
  body: (IsFilteredOrEmpty.cocone_objs j j').choose_spec.choose

中文:
定义 leftToMax
  签名: (j j' : C)
  定义体: (IsFilteredOrEmpty.cocone_objs j j').choose_spec.choose

Depends on / 依赖: IsFilteredOrEmpty, IsFilteredOrEmpty.cocone_objs, choose_spec, choose_spec.choose, cocone_objs
-/
noncomputable def leftToMax (j j' : C) : j ⟶ max j j' :=
  (IsFilteredOrEmpty.cocone_objs j j').choose_spec.choose

/--
Definition of `rightToMax` / `rightToMax` 的定义

English:
definition rightToMax
  signature: (j j' : C)
  body: (IsFilteredOrEmpty.cocone_objs j j').choose_spec.choose_spec.choose

中文:
定义 rightToMax
  签名: (j j' : C)
  定义体: (IsFilteredOrEmpty.cocone_objs j j').choose_spec.choose_spec.choose

Depends on / 依赖: HasFiniteBiproducts, IsFilteredOrEmpty, IsFilteredOrEmpty.cocone_objs, choose_spec, choose_spec.choose_spec.choose, cocone_objs, hasZeroObject_of_hasFiniteBiproducts
-/
noncomputable def rightToMax (j j' : C) : j' ⟶ max j j' :=
  (IsFilteredOrEmpty.cocone_objs j j').choose_spec.choose_spec.choose

/--
Definition of `coeq` / `coeq` 的定义

English:
definition coeq
  signature: {j j' : C} (f f' : j ⟶ j')
  body: (IsFilteredOrEmpty.cocone_maps f f').choose

中文:
定义 coeq
  签名: {j j' : C} (f f' : j ⟶ j')
  定义体: (IsFilteredOrEmpty.cocone_maps f f').choose

Depends on / 依赖: IsFilteredOrEmpty, IsFilteredOrEmpty.cocone_maps, cocone_maps
-/
noncomputable def coeq {j j' : C} (f f' : j ⟶ j') : C :=
  (IsFilteredOrEmpty.cocone_maps f f').choose

/--
Definition of `coeqHom` / `coeqHom` 的定义

English:
definition coeqHom
  signature: {j j' : C} (f f' : j ⟶ j')
  body: (IsFilteredOrEmpty.cocone_maps f f').choose_spec.choose

中文:
定义 coeqHom
  签名: {j j' : C} (f f' : j ⟶ j')
  定义体: (IsFilteredOrEmpty.cocone_maps f f').choose_spec.choose

Depends on / 依赖: IsFilteredOrEmpty, IsFilteredOrEmpty.cocone_maps, Nonempty, Subsingleton, choose_spec, choose_spec.choose, cocone_maps, hasBiproduct_unique
-/
noncomputable def coeqHom {j j' : C} (f f' : j ⟶ j') : j' ⟶ coeq f f' :=
  (IsFilteredOrEmpty.cocone_maps f f').choose_spec.choose

/-- `coeq_condition f f'`, for morphisms `f f' : j ⟶ j'`, is the proof that
`f ≫ coeqHom f f' = f' ≫ coeqHom f f'`.
-/
@[reassoc] -- Not `@[simp]` as it does not fire.
/--
theorem `coeq_condition` / 定理 `coeq_condition`

English:
theorem coeq_condition
  given: {j j' : C} (f f' : j ⟶ j')
  statement: f ≫ coeqHom f f' = f' ≫ coeqHom f f'
  proof: (IsFilteredOrEmpty.cocone_maps f f').choose_spec.choose_spec

中文:
定理 coeq_condition
  条件: {j j' : C} (f f' : j ⟶ j')
  结论: f ≫ coeqHom f f' = f' ≫ coeqHom f f'
  证明: (IsFilteredOrEmpty.cocone_maps f f').choose_spec.choose_spec

Depends on / 依赖: IsFilteredOrEmpty, IsFilteredOrEmpty.cocone_maps, choose_spec, choose_spec.choose_spec, cocone_maps
-/
theorem coeq_condition {j j' : C} (f f' : j ⟶ j') : f ≫ coeqHom f f' = f' ≫ coeqHom f f' :=
  (IsFilteredOrEmpty.cocone_maps f f').choose_spec.choose_spec

end AllowEmpty

/--
lemma `isDirectedOrder` / 引理 `isDirectedOrder`

English:
lemma isDirectedOrder
  given: (α : Type u) [Preorder α] [IsFiltered α]
  proof: ⟨max i j, leOfHom (leftToMax i j), leOfHom (rightToMax i j)⟩

中文:
引理 isDirectedOrder
  条件: (α : 类型u) [预序 α] [是Filtered α]
  证明: ⟨max i j, leOfHom (leftToMax i j), leOfHom (rightToMax i j)⟩

Depends on / 依赖: leOfHom, leftToMax, rightToMax
-/
lemma isDirectedOrder (α : Type u) [Preorder α] [IsFiltered α] :
    IsDirectedOrder α where
  directed i j := ⟨max i j, leOfHom (leftToMax i j), leOfHom (rightToMax i j)⟩

end IsFiltered

namespace IsFilteredOrEmpty
open IsFiltered

variable {C}
variable [IsFilteredOrEmpty C]
variable {D : Type u₁} [Category.{v₁} D]

/--
theorem `of_right_adjoint` / 定理 `of_right_adjoint`

English:
theorem of_right_adjoint
  given: {L : D ⥤ C} {R : C ⥤ D} (h : L ⊣ R)
  statement: IsFilteredOrEmpty D
  proof: { cocone_objs := fun X Y =>
      ⟨R.obj (max (L.obj X) (L.obj Y)),
        h.homEquiv _ _ (leftToMax _ _), h.homEquiv _ _ (rightToMax _ _), ⟨⟩⟩
    cocone_maps := fun X Y f g =>
      ⟨R.obj (coeq (L.map f) (L.map g)), h.homEquiv _ _ (coeqHom _ _), by
        rw [← h.homEquiv_naturality_left]; rw [← h.homEquiv_naturality_left]; rw [coeq_condition]⟩ }

中文:
定理 of_right_adjoint
  条件: {L : D ⥤ C} {R : C ⥤ D} (h : L ⊣ R)
  结论: 是FilteredOrEmpty D
  证明: { cocone_objs := fun X Y =>
      ⟨R.obj (max (L.obj X) (L.obj Y)),
        h.homEquiv _ _ (leftToMax _ _), h.homEquiv _ _ (rightToMax _ _), ⟨⟩⟩
    cocone_maps := fun X Y f g =>
      ⟨R.obj (coeq (L.map f) (L.map g)), h.homEquiv _ _ (coeqHom _ _), by
        rw [← h.homEquiv_naturality_left]; rw [← h.homEquiv_naturality_left]; rw [coeq_condition]⟩ }

Depends on / 依赖: L.map, L.obj, R.obj, cocone_maps, cocone_objs, coeqHom, coeq_condition, h.homEquiv, h.homEquiv_naturality_left, homEquiv, homEquiv_naturality_left, leftToMax, rightToMax
-/
theorem of_right_adjoint {L : D ⥤ C} {R : C ⥤ D} (h : L ⊣ R) : IsFilteredOrEmpty D :=
  { cocone_objs := fun X Y =>
      ⟨R.obj (max (L.obj X) (L.obj Y)),
        h.homEquiv _ _ (leftToMax _ _), h.homEquiv _ _ (rightToMax _ _), ⟨⟩⟩
    cocone_maps := fun X Y f g =>
      ⟨R.obj (coeq (L.map f) (L.map g)), h.homEquiv _ _ (coeqHom _ _), by
        rw [← h.homEquiv_naturality_left]; rw [← h.homEquiv_naturality_left]; rw [coeq_condition]⟩ }

/--
theorem `of_isRightAdjoint` / 定理 `of_isRightAdjoint`

English:
theorem of_isRightAdjoint
  given: (R : C ⥤ D) [R.IsRightAdjoint]
  statement: IsFilteredOrEmpty D
  proof: of_right_adjoint (Adjunction.ofIsRightAdjoint R)

中文:
定理 of_isRightAdjoint
  条件: (R : C ⥤ D) [R.是右伴随]
  结论: 是FilteredOrEmpty D
  证明: of_right_adjoint (Adjunction.ofIsRightAdjoint R)

Depends on / 依赖: Adjunction, Adjunction.ofIsRightAdjoint, ofIsRightAdjoint, of_right_adjoint
-/
theorem of_isRightAdjoint (R : C ⥤ D) [R.IsRightAdjoint] : IsFilteredOrEmpty D :=
  of_right_adjoint (Adjunction.ofIsRightAdjoint R)

/--
theorem `of_equivalence` / 定理 `of_equivalence`

English:
theorem of_equivalence
  given: (h : C ≌ D)
  statement: IsFilteredOrEmpty D
  proof: of_right_adjoint h.symm.toAdjunction

中文:
定理 of_equivalence
  条件: (h : C ≌ D)
  结论: 是FilteredOrEmpty D
  证明: of_right_adjoint h.symm.toAdjunction

Depends on / 依赖: h.symm.toAdjunction, of_right_adjoint, toAdjunction
-/
theorem of_equivalence (h : C ≌ D) : IsFilteredOrEmpty D :=
  of_right_adjoint h.symm.toAdjunction

end IsFilteredOrEmpty

namespace IsFiltered

section Nonempty

open CategoryTheory.Limits

variable {C}
variable [IsFiltered C]

/--
theorem `sup_objs_exists` / 定理 `sup_objs_exists`

English:
theorem sup_objs_exists
  given: (O : Finset C)
  statement: exists S : C, forall {X}, X in O -> Nonempty (X ⟶ S)
  proof: by
  classical
  induction O using Finset.induction with
  | empty => exact ⟨Classical.choice IsFiltered.nonempty, by simp⟩
  | insert X O' nm h =>
    obtain ⟨S', w'⟩ := h
    use max X S'
    rintro Y mY
    obtain rfl | h := eq_or_ne Y X
    · exact ⟨leftToMax _ _⟩
    · exact ⟨(w' (Finset.mem_of_mem_insert_of_ne mY h)).some ≫ rightToMax _ _⟩

中文:
定理 sup_objs_存在
  条件: (O : 有限集 C)
  结论: 存在 S : C, 对任意 {X}, X in O -> 非空 (X ⟶ S)
  证明: by
  classical
  induction O using Finset.induction with
  | empty => exact ⟨Classical.choice IsFiltered.nonempty, by simp⟩
  | insert X O' nm h =>
    obtain ⟨S', w'⟩ := h
    use max X S'
    rintro Y mY
    obtain rfl | h := eq_or_ne Y X
    · exact ⟨leftToMax _ _⟩
    · exact ⟨(w' (Finset.mem_of_mem_insert_of_ne mY h)).some ≫ rightToMax _ _⟩

Depends on / 依赖: Classical, Classical.choice, Finset, Finset.induction, Finset.mem_of_mem_insert_of_ne, IsFiltered, IsFiltered.nonempty, choice, classical, eq_or_ne, insert, leftToMax, mem_of_mem_insert_of_ne, nonempty, rightToMax
-/
theorem sup_objs_exists (O : Finset C) : exists S : C, forall {X}, X in O -> Nonempty (X ⟶ S) := by
  classical
  induction O using Finset.induction with
  | empty => exact ⟨Classical.choice IsFiltered.nonempty, by simp⟩
  | insert X O' nm h =>
    obtain ⟨S', w'⟩ := h
    use max X S'
    rintro Y mY
    obtain rfl | h := eq_or_ne Y X
    · exact ⟨leftToMax _ _⟩
    · exact ⟨(w' (Finset.mem_of_mem_insert_of_ne mY h)).some ≫ rightToMax _ _⟩

variable (O : Finset C) (H : Finset (Σ' (X Y : C) (_ : X in O) (_ : Y in O), X ⟶ Y))

/--
theorem `sup_exists` / 定理 `sup_exists`

English:
theorem sup_exists
  proof: by
  classical
  induction H using Finset.induction with
  | empty =>
    obtain ⟨S, f⟩ := sup_objs_exists O
    exact ⟨S, fun mX => (f mX).some, by rintro - - - - - ⟨⟩⟩
  | insert h' H' nmf h'' =>
    obtain ⟨X, Y, mX, mY, f⟩ := h'
    obtain ⟨S', T', w'⟩ := h''
    refine ⟨coeq (f ≫ T' mY) (T' mX), fun mZ => T' mZ ≫ coeqHom (f ≫ T' mY) (T' mX), ?_⟩
    intro X' Y' mX' mY' f' mf'
    rw [← Category.assoc]
    by_cases h : X = X' ∧ Y = Y'
    · rcases h with ⟨rfl, rfl⟩
      grind [coeq_condition]
    · rw [@w' _ _ mX' mY' f' _]
      apply Finset.mem_of_mem_insert_of_ne mf'
      contrapose h
      obtain ⟨rfl, h⟩ := h
      trivial

中文:
定理 sup_存在
  证明: by
  classical
  induction H using Finset.induction with
  | empty =>
    obtain ⟨S, f⟩ := sup_objs_exists O
    exact ⟨S, fun mX => (f mX).some, by rintro - - - - - ⟨⟩⟩
  | insert h' H' nmf h'' =>
    obtain ⟨X, Y, mX, mY, f⟩ := h'
    obtain ⟨S', T', w'⟩ := h''
    refine ⟨coeq (f ≫ T' mY) (T' mX), fun mZ => T' mZ ≫ coeqHom (f ≫ T' mY) (T' mX), ?_⟩
    intro X' Y' mX' mY' f' mf'
    rw [← Category.assoc]
    by_cases h : X = X' ∧ Y = Y'
    · rcases h with ⟨rfl, rfl⟩
      grind [coeq_condition]
    · rw [@w' _ _ mX' mY' f' _]
      apply Finset.mem_of_mem_insert_of_ne mf'
      contrapose h
      obtain ⟨rfl, h⟩ := h
      trivial

Depends on / 依赖: Category, Category.assoc, Finset, Finset.induction, Finset.mem_of, classical, coeqHom, coeq_condition, insert, mem_of, sup_objs_exists
-/
theorem sup_exists :
    exists (S : C) (T : forall {X : C}, X in O -> (X ⟶ S)),
      forall {X Y : C} (mX : X in O) (mY : Y in O) {f : X ⟶ Y},
        (⟨X, Y, mX, mY, f⟩ : Σ' (X Y : C) (_ : X in O) (_ : Y in O), X ⟶ Y) in H ->
          f ≫ T mY = T mX := by
  classical
  induction H using Finset.induction with
  | empty =>
    obtain ⟨S, f⟩ := sup_objs_exists O
    exact ⟨S, fun mX => (f mX).some, by rintro - - - - - ⟨⟩⟩
  | insert h' H' nmf h'' =>
    obtain ⟨X, Y, mX, mY, f⟩ := h'
    obtain ⟨S', T', w'⟩ := h''
    refine ⟨coeq (f ≫ T' mY) (T' mX), fun mZ => T' mZ ≫ coeqHom (f ≫ T' mY) (T' mX), ?_⟩
    intro X' Y' mX' mY' f' mf'
    rw [← Category.assoc]
    by_cases h : X = X' ∧ Y = Y'
    · rcases h with ⟨rfl, rfl⟩
      grind [coeq_condition]
    · rw [@w' _ _ mX' mY' f' _]
      apply Finset.mem_of_mem_insert_of_ne mf'
      contrapose h
      obtain ⟨rfl, h⟩ := h
      trivial

/--
Definition of `sup` / `sup` 的定义

English:
definition sup
  signature: : C
  body: (sup_exists O H).choose

中文:
定义 上确界
  签名: : C
  定义体: (sup_exists O H).choose

Depends on / 依赖: sup_exists
-/
noncomputable def sup : C :=
  (sup_exists O H).choose

/--
Definition of `toSup` / `toSup` 的定义

English:
definition toSup
  signature: {X : C} (m : X in O)
  body: (sup_exists O H).choose_spec.choose m

中文:
定义 toSup
  签名: {X : C} (m : X in O)
  定义体: (sup_exists O H).choose_spec.choose m

Depends on / 依赖: choose_spec, choose_spec.choose, sup_exists
-/
noncomputable def toSup {X : C} (m : X in O) : X ⟶ sup O H :=
  (sup_exists O H).choose_spec.choose m

/--
theorem `toSup_commutes` / 定理 `toSup_commutes`

English:
theorem toSup_commutes
  statement: {X Y : C} (mX : X in O) (mY : Y in O) {f : X ⟶ Y}
  proof: (sup_exists O H).choose_spec.choose_spec mX mY mf

中文:
定理 toSup_commutes
  结论: {X Y : C} (mX : X in O) (mY : Y in O) {f : X ⟶ Y}
  证明: (sup_exists O H).choose_spec.choose_spec mX mY mf

Depends on / 依赖: choose_spec, choose_spec.choose_spec, sup_exists
-/
theorem toSup_commutes {X Y : C} (mX : X in O) (mY : Y in O) {f : X ⟶ Y}
    (mf : (⟨X, Y, mX, mY, f⟩ : Σ' (X Y : C) (_ : X in O) (_ : Y in O), X ⟶ Y) in H) :
    f ≫ toSup O H mY = toSup O H mX :=
  (sup_exists O H).choose_spec.choose_spec mX mY mf

variable {J : Type w} [SmallCategory J] [FinCategory J]

set_option backward.defeqAttrib.useBackward true in
/--
theorem `cocone_nonempty` / 定理 `cocone_nonempty`

English:
theorem cocone_nonempty
  given: (F : J ⥤ C)
  statement: Nonempty (Cocone F)
  proof: by
  classical
  let O := Finset.univ.image F.obj
  let H : Finset (Σ' (X Y : C) (_ : X in O) (_ : Y in O), X ⟶ Y) :=
    Finset.univ.biUnion fun X : J => Finset.univ.biUnion fun Y : J =>
      Finset.univ.image fun f : X ⟶ Y => ⟨F.obj X, F.obj Y, by simp [O], by simp [O], F.map f⟩
  obtain ⟨Z, f, w⟩ := sup_exists O H
  refine ⟨⟨Z, ⟨fun X => f (by simp [O]), ?_⟩⟩⟩
  intro j j' g
  dsimp
  simp only [Category.comp_id]
  apply w
  simp only [O, H, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_image, PSigma.mk.injEq,
    true_and, exists_and_left]
  exact ⟨j, rfl, j', g, by simp⟩

中文:
定理 cocone_nonempty
  条件: (F : J ⥤ C)
  结论: 非空 (余锥 F)
  证明: by
  classical
  let O := Finset.univ.image F.obj
  let H : Finset (Σ' (X Y : C) (_ : X in O) (_ : Y in O), X ⟶ Y) :=
    Finset.univ.biUnion fun X : J => Finset.univ.biUnion fun Y : J =>
      Finset.univ.image fun f : X ⟶ Y => ⟨F.obj X, F.obj Y, by simp [O], by simp [O], F.map f⟩
  obtain ⟨Z, f, w⟩ := sup_exists O H
  refine ⟨⟨Z, ⟨fun X => f (by simp [O]), ?_⟩⟩⟩
  intro j j' g
  dsimp
  simp only [Category.comp_id]
  apply w
  simp only [O, H, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_image, PSigma.mk.injEq,
    true_and, exists_and_left]
  exact ⟨j, rfl, j', g, by simp⟩

Depends on / 依赖: Category, Category.comp_id, F.map, F.obj, Finset, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, Finset.univ.biUnion, Finset.univ.image, PSigma, PSigma.mk.injEq, biUnion, classical, comp_id, mem_biUnion, mem_image, mem_univ, sup_exists, true_and
-/
theorem cocone_nonempty (F : J ⥤ C) : Nonempty (Cocone F) := by
  classical
  let O := Finset.univ.image F.obj
  let H : Finset (Σ' (X Y : C) (_ : X in O) (_ : Y in O), X ⟶ Y) :=
    Finset.univ.biUnion fun X : J => Finset.univ.biUnion fun Y : J =>
      Finset.univ.image fun f : X ⟶ Y => ⟨F.obj X, F.obj Y, by simp [O], by simp [O], F.map f⟩
  obtain ⟨Z, f, w⟩ := sup_exists O H
  refine ⟨⟨Z, ⟨fun X => f (by simp [O]), ?_⟩⟩⟩
  intro j j' g
  dsimp
  simp only [Category.comp_id]
  apply w
  simp only [O, H, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_image, PSigma.mk.injEq,
    true_and, exists_and_left]
  exact ⟨j, rfl, j', g, by simp⟩

/--
Definition of `cocone` / `cocone` 的定义

English:
definition cocone
  signature: (F : J ⥤ C)
  body: (cocone_nonempty F).some

中文:
定义 cocone
  签名: (F : J ⥤ C)
  定义体: (cocone_nonempty F).some

Depends on / 依赖: cocone_nonempty
-/
noncomputable def cocone (F : J ⥤ C) : Cocone F :=
  (cocone_nonempty F).some

variable {D : Type u₁} [Category.{v₁} D]

/--
theorem `of_right_adjoint` / 定理 `of_right_adjoint`

English:
theorem of_right_adjoint
  given: {L : D ⥤ C} {R : C ⥤ D} (h : L ⊣ R)
  statement: IsFiltered D
  proof: { IsFilteredOrEmpty.of_right_adjoint h with
    nonempty := IsFiltered.nonempty.map R.obj }

中文:
定理 of_right_adjoint
  条件: {L : D ⥤ C} {R : C ⥤ D} (h : L ⊣ R)
  结论: 是Filtered D
  证明: { IsFilteredOrEmpty.of_right_adjoint h with
    nonempty := IsFiltered.nonempty.map R.obj }

Depends on / 依赖: IsFiltered, IsFiltered.nonempty.map, IsFilteredOrEmpty, IsFilteredOrEmpty.of_right_adjoint, R.obj, nonempty, of_right_adjoint
-/
theorem of_right_adjoint {L : D ⥤ C} {R : C ⥤ D} (h : L ⊣ R) : IsFiltered D :=
  { IsFilteredOrEmpty.of_right_adjoint h with
    nonempty := IsFiltered.nonempty.map R.obj }

/--
theorem `of_isRightAdjoint` / 定理 `of_isRightAdjoint`

English:
theorem of_isRightAdjoint
  given: (R : C ⥤ D) [R.IsRightAdjoint]
  statement: IsFiltered D
  proof: of_right_adjoint (Adjunction.ofIsRightAdjoint R)

中文:
定理 of_isRightAdjoint
  条件: (R : C ⥤ D) [R.是右伴随]
  结论: 是Filtered D
  证明: of_right_adjoint (Adjunction.ofIsRightAdjoint R)

Depends on / 依赖: Adjunction, Adjunction.ofIsRightAdjoint, ofIsRightAdjoint, of_right_adjoint
-/
theorem of_isRightAdjoint (R : C ⥤ D) [R.IsRightAdjoint] : IsFiltered D :=
  of_right_adjoint (Adjunction.ofIsRightAdjoint R)

/--
theorem `of_equivalence` / 定理 `of_equivalence`

English:
theorem of_equivalence
  given: (h : C ≌ D)
  statement: IsFiltered D
  proof: of_right_adjoint h.symm.toAdjunction

omit [IsFiltered C] in

中文:
定理 of_equivalence
  条件: (h : C ≌ D)
  结论: 是Filtered D
  证明: of_right_adjoint h.symm.toAdjunction

omit [IsFiltered C] in

Depends on / 依赖: h.symm.toAdjunction, of_right_adjoint, toAdjunction
-/
theorem of_equivalence (h : C ≌ D) : IsFiltered D :=
  of_right_adjoint h.symm.toAdjunction

omit [IsFiltered C] in
/--
lemma `iff_of_equivalence` / 引理 `iff_of_equivalence`

English:
lemma iff_of_equivalence
  given: (e : C ≌ D)
  statement: IsFiltered C ↔ IsFiltered D
  proof: ⟨fun _ => .of_equivalence e, fun _ => .of_equivalence e.symm⟩

中文:
引理 iff_of_equivalence
  条件: (e : C ≌ D)
  结论: 是Filtered C ↔ 是Filtered D
  证明: ⟨fun _ => .of_equivalence e, fun _ => .of_equivalence e.symm⟩

Depends on / 依赖: e.symm, of_equivalence
-/
lemma iff_of_equivalence (e : C ≌ D) : IsFiltered C ↔ IsFiltered D :=
  ⟨fun _ => .of_equivalence e, fun _ => .of_equivalence e.symm⟩

end Nonempty

section OfCocone

open CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false in
/--
theorem `of_cocone_nonempty` / 定理 `of_cocone_nonempty`

English:
theorem of_cocone_nonempty
  statement: (h : forall {J : Type w} [SmallCategory J] [FinCategory J] (F : J ⥤ C),
  proof: by
  have : Nonempty C := by
    obtain ⟨c⟩ := h (Functor.empty _)
    exact ⟨c.pt⟩
  have : IsFilteredOrEmpty C := by
    refine ⟨?_, ?_⟩
    · intro X Y
      obtain ⟨c⟩ := h (ULiftHom.down ⋙ ULift.downFunctor ⋙ pair X Y)
      exact ⟨c.pt, c.ι.app ⟨⟨WalkingPair.left⟩⟩, c.ι.app ⟨⟨WalkingPair.right⟩⟩, trivial⟩
    · intro X Y f g
      obtain ⟨c⟩ := h (ULiftHom.down ⋙ ULift.downFunctor ⋙ parallelPair f g)
      refine ⟨c.pt, c.ι.app ⟨WalkingParallelPair.one⟩, ?_⟩
      have h₁ := c.ι.naturality ⟨WalkingParallelPairHom.left⟩
      have h₂ := c.ι.naturality ⟨WalkingParallelPairHom.right⟩
      simp_all
  apply IsFiltered.mk

中文:
定理 of_cocone_nonempty
  结论: (h : 对任意 {J : 类型 w} [小范畴 J] [有限范畴 J] (F : J ⥤ C),
  证明: by
  have : Nonempty C := by
    obtain ⟨c⟩ := h (Functor.empty _)
    exact ⟨c.pt⟩
  have : IsFilteredOrEmpty C := by
    refine ⟨?_, ?_⟩
    · intro X Y
      obtain ⟨c⟩ := h (ULiftHom.down ⋙ ULift.downFunctor ⋙ pair X Y)
      exact ⟨c.pt, c.ι.app ⟨⟨WalkingPair.left⟩⟩, c.ι.app ⟨⟨WalkingPair.right⟩⟩, trivial⟩
    · intro X Y f g
      obtain ⟨c⟩ := h (ULiftHom.down ⋙ ULift.downFunctor ⋙ parallelPair f g)
      refine ⟨c.pt, c.ι.app ⟨WalkingParallelPair.one⟩, ?_⟩
      have h₁ := c.ι.naturality ⟨WalkingParallelPairHom.left⟩
      have h₂ := c.ι.naturality ⟨WalkingParallelPairHom.right⟩
      simp_all
  apply IsFiltered.mk

Depends on / 依赖: Functor, Functor.empty, IsFilteredOrEmpty, Nonempty, ULift.downFunctor, ULiftHom, ULiftHom.down, WalkingPair, WalkingPair.left, WalkingPair.right, WalkingParallelPair, WalkingParallelPair.one, WalkingParallelPairHom, WalkingParallelPairHom.left, c.pt, downFunctor, naturali, naturality, parallelPair
-/
theorem of_cocone_nonempty (h : forall {J : Type w} [SmallCategory J] [FinCategory J] (F : J ⥤ C),
    Nonempty (Cocone F)) : IsFiltered C := by
  have : Nonempty C := by
    obtain ⟨c⟩ := h (Functor.empty _)
    exact ⟨c.pt⟩
  have : IsFilteredOrEmpty C := by
    refine ⟨?_, ?_⟩
    · intro X Y
      obtain ⟨c⟩ := h (ULiftHom.down ⋙ ULift.downFunctor ⋙ pair X Y)
      exact ⟨c.pt, c.ι.app ⟨⟨WalkingPair.left⟩⟩, c.ι.app ⟨⟨WalkingPair.right⟩⟩, trivial⟩
    · intro X Y f g
      obtain ⟨c⟩ := h (ULiftHom.down ⋙ ULift.downFunctor ⋙ parallelPair f g)
      refine ⟨c.pt, c.ι.app ⟨WalkingParallelPair.one⟩, ?_⟩
      have h₁ := c.ι.naturality ⟨WalkingParallelPairHom.left⟩
      have h₂ := c.ι.naturality ⟨WalkingParallelPairHom.right⟩
      simp_all
  apply IsFiltered.mk

/--
theorem `of_hasFiniteColimits` / 定理 `of_hasFiniteColimits`

English:
theorem of_hasFiniteColimits
  given: [HasFiniteColimits C]
  statement: IsFiltered C
  proof: of_cocone_nonempty.{v} C fun F => ⟨colimit.cocone F⟩

中文:
定理 of_hasFiniteColimits
  条件: [有有限余极限 C]
  结论: 是Filtered C
  证明: of_cocone_nonempty.{v} C fun F => ⟨colimit.cocone F⟩

Depends on / 依赖: cocone, colimit, colimit.cocone, of_cocone_nonempty
-/
theorem of_hasFiniteColimits [HasFiniteColimits C] : IsFiltered C :=
  of_cocone_nonempty.{v} C fun F => ⟨colimit.cocone F⟩

/--
theorem `of_isTerminal` / 定理 `of_isTerminal`

English:
theorem of_isTerminal
  given: {X : C} (h : IsTerminal X)
  statement: IsFiltered C
  proof: of_cocone_nonempty.{v} _ fun {_} _ _ _ => ⟨⟨X, ⟨fun _ => h.from _, fun _ _ _ => h.hom_ext _ _⟩⟩⟩

中文:
定理 of_isTerminal
  条件: {X : C} (h : 是终止 X)
  结论: 是Filtered C
  证明: of_cocone_nonempty.{v} _ fun {_} _ _ _ => ⟨⟨X, ⟨fun _ => h.from _, fun _ _ _ => h.hom_ext _ _⟩⟩⟩

Depends on / 依赖: h.from, h.hom_ext, hom_ext, of_cocone_nonempty
-/
theorem of_isTerminal {X : C} (h : IsTerminal X) : IsFiltered C :=
  of_cocone_nonempty.{v} _ fun {_} _ _ _ => ⟨⟨X, ⟨fun _ => h.from _, fun _ _ _ => h.hom_ext _ _⟩⟩⟩

instance (priority := 100) of_hasTerminal [HasTerminal C] : IsFiltered C :=
  of_isTerminal _ terminalIsTerminal

/--
theorem `iff_cocone_nonempty` / 定理 `iff_cocone_nonempty`

English:
theorem iff_cocone_nonempty
  statement: IsFiltered C ↔
  proof: ⟨fun _ _ _ _ F => cocone_nonempty F, of_cocone_nonempty C⟩

中文:
定理 iff_cocone_nonempty
  结论: 是Filtered C ↔
  证明: ⟨fun _ _ _ _ F => cocone_nonempty F, of_cocone_nonempty C⟩

Depends on / 依赖: cocone_nonempty, of_cocone_nonempty
-/
theorem iff_cocone_nonempty : IsFiltered C ↔
    forall {J : Type w} [SmallCategory J] [FinCategory J] (F : J ⥤ C), Nonempty (Cocone F) :=
  ⟨fun _ _ _ _ F => cocone_nonempty F, of_cocone_nonempty C⟩

end OfCocone

section SpecialShapes

variable {C}
variable [IsFilteredOrEmpty C]

/--
Definition of `max₃` / `max₃` 的定义

English:
definition max₃
  signature: (j₁ j₂ j₃ : C)
  body: max (max j₁ j₂) j₃

中文:
定义 max₃
  签名: (j₁ j₂ j₃ : C)
  定义体: max (max j₁ j₂) j₃
-/
noncomputable def max₃ (j₁ j₂ j₃ : C) : C :=
  max (max j₁ j₂) j₃

/--
Definition of `firstToMax₃` / `firstToMax₃` 的定义

English:
definition firstToMax₃
  signature: (j₁ j₂ j₃ : C)
  body: leftToMax j₁ j₂ ≫ leftToMax (max j₁ j₂) j₃

中文:
定义 firstToMax₃
  签名: (j₁ j₂ j₃ : C)
  定义体: leftToMax j₁ j₂ ≫ leftToMax (max j₁ j₂) j₃

Depends on / 依赖: leftToMax
-/
noncomputable def firstToMax₃ (j₁ j₂ j₃ : C) : j₁ ⟶ max₃ j₁ j₂ j₃ :=
  leftToMax j₁ j₂ ≫ leftToMax (max j₁ j₂) j₃

/--
Definition of `secondToMax₃` / `secondToMax₃` 的定义

English:
definition secondToMax₃
  signature: (j₁ j₂ j₃ : C)
  body: rightToMax j₁ j₂ ≫ leftToMax (max j₁ j₂) j₃

中文:
定义 secondToMax₃
  签名: (j₁ j₂ j₃ : C)
  定义体: rightToMax j₁ j₂ ≫ leftToMax (max j₁ j₂) j₃

Depends on / 依赖: leftToMax, rightToMax
-/
noncomputable def secondToMax₃ (j₁ j₂ j₃ : C) : j₂ ⟶ max₃ j₁ j₂ j₃ :=
  rightToMax j₁ j₂ ≫ leftToMax (max j₁ j₂) j₃

/--
Definition of `thirdToMax₃` / `thirdToMax₃` 的定义

English:
definition thirdToMax₃
  signature: (j₁ j₂ j₃ : C)
  body: rightToMax (max j₁ j₂) j₃

中文:
定义 thirdToMax₃
  签名: (j₁ j₂ j₃ : C)
  定义体: rightToMax (max j₁ j₂) j₃

Depends on / 依赖: rightToMax
-/
noncomputable def thirdToMax₃ (j₁ j₂ j₃ : C) : j₃ ⟶ max₃ j₁ j₂ j₃ :=
  rightToMax (max j₁ j₂) j₃

/--
Definition of `coeq₃` / `coeq₃` 的定义

English:
definition coeq₃
  signature: {j₁ j₂ : C} (f g h : j₁ ⟶ j₂)
  body: coeq (coeqHom f g ≫ leftToMax (coeq f g) (coeq g h))
    (coeqHom g h ≫ rightToMax (coeq f g) (coeq g h))

中文:
定义 coeq₃
  签名: {j₁ j₂ : C} (f g h : j₁ ⟶ j₂)
  定义体: coeq (coeqHom f g ≫ leftToMax (coeq f g) (coeq g h))
    (coeqHom g h ≫ rightToMax (coeq f g) (coeq g h))

Depends on / 依赖: coeqHom, leftToMax, rightToMax
-/
noncomputable def coeq₃ {j₁ j₂ : C} (f g h : j₁ ⟶ j₂) : C :=
  coeq (coeqHom f g ≫ leftToMax (coeq f g) (coeq g h))
    (coeqHom g h ≫ rightToMax (coeq f g) (coeq g h))

/--
Definition of `coeq₃Hom` / `coeq₃Hom` 的定义

English:
definition coeq₃Hom
  signature: {j₁ j₂ : C} (f g h : j₁ ⟶ j₂)
  body: coeqHom f g ≫
    leftToMax (coeq f g) (coeq g h) ≫
      coeqHom (coeqHom f g ≫ leftToMax (coeq f g) (coeq g h))
        (coeqHom g h ≫ rightToMax (coeq f g) (coeq g h))

中文:
定义 coeq₃Hom
  签名: {j₁ j₂ : C} (f g h : j₁ ⟶ j₂)
  定义体: coeqHom f g ≫
    leftToMax (coeq f g) (coeq g h) ≫
      coeqHom (coeqHom f g ≫ leftToMax (coeq f g) (coeq g h))
        (coeqHom g h ≫ rightToMax (coeq f g) (coeq g h))

Depends on / 依赖: coeqHom, leftToMax, rightToMax
-/
noncomputable def coeq₃Hom {j₁ j₂ : C} (f g h : j₁ ⟶ j₂) : j₂ ⟶ coeq₃ f g h :=
  coeqHom f g ≫
    leftToMax (coeq f g) (coeq g h) ≫
      coeqHom (coeqHom f g ≫ leftToMax (coeq f g) (coeq g h))
        (coeqHom g h ≫ rightToMax (coeq f g) (coeq g h))

/--
theorem `coeq₃_condition₁` / 定理 `coeq₃_condition₁`

English:
theorem coeq₃_condition₁
  given: {j₁ j₂ : C} (f g h : j₁ ⟶ j₂)
  proof: by
  simp only [coeq₃Hom, ← Category.assoc, coeq_condition f g]

中文:
定理 coeq₃_condition₁
  条件: {j₁ j₂ : C} (f g h : j₁ ⟶ j₂)
  证明: by
  simp only [coeq₃Hom, ← Category.assoc, coeq_condition f g]

Depends on / 依赖: Category, Category.assoc, coeq_condition
-/
theorem coeq₃_condition₁ {j₁ j₂ : C} (f g h : j₁ ⟶ j₂) :
    f ≫ coeq₃Hom f g h = g ≫ coeq₃Hom f g h := by
  simp only [coeq₃Hom, ← Category.assoc, coeq_condition f g]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `coeq₃_condition₂` / 定理 `coeq₃_condition₂`

English:
theorem coeq₃_condition₂
  given: {j₁ j₂ : C} (f g h : j₁ ⟶ j₂)
  proof: by
  dsimp [coeq₃Hom]
  slice_lhs 2 4 => rw [← Category.assoc, coeq_condition _ _]
  slice_rhs 2 4 => rw [← Category.assoc, coeq_condition _ _]
  slice_lhs 1 3 => rw [← Category.assoc, coeq_condition _ _]
  simp only [Category.assoc]

中文:
定理 coeq₃_condition₂
  条件: {j₁ j₂ : C} (f g h : j₁ ⟶ j₂)
  证明: by
  dsimp [coeq₃Hom]
  slice_lhs 2 4 => rw [← Category.assoc, coeq_condition _ _]
  slice_rhs 2 4 => rw [← Category.assoc, coeq_condition _ _]
  slice_lhs 1 3 => rw [← Category.assoc, coeq_condition _ _]
  simp only [Category.assoc]

Depends on / 依赖: Category, Category.assoc, coeq_condition, slice_lhs, slice_rhs
-/
theorem coeq₃_condition₂ {j₁ j₂ : C} (f g h : j₁ ⟶ j₂) :
    g ≫ coeq₃Hom f g h = h ≫ coeq₃Hom f g h := by
  dsimp [coeq₃Hom]
  slice_lhs 2 4 => rw [← Category.assoc, coeq_condition _ _]
  slice_rhs 2 4 => rw [← Category.assoc, coeq_condition _ _]
  slice_lhs 1 3 => rw [← Category.assoc, coeq_condition _ _]
  simp only [Category.assoc]

/--
theorem `coeq₃_condition₃` / 定理 `coeq₃_condition₃`

English:
theorem coeq₃_condition₃
  given: {j₁ j₂ : C} (f g h : j₁ ⟶ j₂)
  statement: f ≫ coeq₃Hom f g h = h ≫ coeq₃Hom f g h
  proof: Eq.trans (coeq₃_condition₁ f g h) (coeq₃_condition₂ f g h)

中文:
定理 coeq₃_condition₃
  条件: {j₁ j₂ : C} (f g h : j₁ ⟶ j₂)
  结论: f ≫ coeq₃Hom f g h = h ≫ coeq₃Hom f g h
  证明: Eq.trans (coeq₃_condition₁ f g h) (coeq₃_condition₂ f g h)

Depends on / 依赖: Eq.trans
-/
theorem coeq₃_condition₃ {j₁ j₂ : C} (f g h : j₁ ⟶ j₂) : f ≫ coeq₃Hom f g h = h ≫ coeq₃Hom f g h :=
  Eq.trans (coeq₃_condition₁ f g h) (coeq₃_condition₂ f g h)

/--
theorem `span` / 定理 `span`

English:
theorem span
  given: {i j j' : C} (f : i ⟶ j) (f' : i ⟶ j')
  proof: let ⟨K, G, G', _⟩ := IsFilteredOrEmpty.cocone_objs j j'
  let ⟨k, e, he⟩ := IsFilteredOrEmpty.cocone_maps (f ≫ G) (f' ≫ G')
  ⟨k, G ≫ e, G' ≫ e, by simpa only [← Category.assoc] ⟩

中文:
定理 span
  条件: {i j j' : C} (f : i ⟶ j) (f' : i ⟶ j')
  证明: let ⟨K, G, G', _⟩ := IsFilteredOrEmpty.cocone_objs j j'
  let ⟨k, e, he⟩ := IsFilteredOrEmpty.cocone_maps (f ≫ G) (f' ≫ G')
  ⟨k, G ≫ e, G' ≫ e, by simpa only [← Category.assoc] ⟩

Depends on / 依赖: Category, Category.assoc, IsFilteredOrEmpty, IsFilteredOrEmpty.cocone_maps, IsFilteredOrEmpty.cocone_objs, cocone_maps, cocone_objs
-/
theorem span {i j j' : C} (f : i ⟶ j) (f' : i ⟶ j') :
    exists (k : C) (g : j ⟶ k) (g' : j' ⟶ k), f ≫ g = f' ≫ g' :=
  let ⟨K, G, G', _⟩ := IsFilteredOrEmpty.cocone_objs j j'
  let ⟨k, e, he⟩ := IsFilteredOrEmpty.cocone_maps (f ≫ G) (f' ≫ G')
  ⟨k, G ≫ e, G' ≫ e, by simpa only [← Category.assoc] ⟩

/--
theorem `bowtie` / 定理 `bowtie`

English:
theorem bowtie
  given: {j₁ j₂ k₁ k₂ : C} (f₁ : j₁ ⟶ k₁) (g₁ : j₁ ⟶ k₂) (f₂ : j₂ ⟶ k₁) (g₂ : j₂ ⟶ k₂)
  proof: by
  obtain ⟨t, k₁t, k₂t, ht⟩ := span f₁ g₁
  obtain ⟨s, ts, hs⟩ := IsFilteredOrEmpty.cocone_maps (f₂ ≫ k₁t) (g₂ ≫ k₂t)
  simp_rw [Category.assoc] at hs
  exact ⟨s, k₁t ≫ ts, k₂t ≫ ts, by simp only [← Category.assoc, ht], hs⟩

中文:
定理 bowtie
  条件: {j₁ j₂ k₁ k₂ : C} (f₁ : j₁ ⟶ k₁) (g₁ : j₁ ⟶ k₂) (f₂ : j₂ ⟶ k₁) (g₂ : j₂ ⟶ k₂)
  证明: by
  obtain ⟨t, k₁t, k₂t, ht⟩ := span f₁ g₁
  obtain ⟨s, ts, hs⟩ := IsFilteredOrEmpty.cocone_maps (f₂ ≫ k₁t) (g₂ ≫ k₂t)
  simp_rw [Category.assoc] at hs
  exact ⟨s, k₁t ≫ ts, k₂t ≫ ts, by simp only [← Category.assoc, ht], hs⟩

Depends on / 依赖: Category, Category.assoc, IsFilteredOrEmpty, IsFilteredOrEmpty.cocone_maps, cocone_maps, simp_rw
-/
theorem bowtie {j₁ j₂ k₁ k₂ : C} (f₁ : j₁ ⟶ k₁) (g₁ : j₁ ⟶ k₂) (f₂ : j₂ ⟶ k₁) (g₂ : j₂ ⟶ k₂) :
    exists (s : C) (α : k₁ ⟶ s) (β : k₂ ⟶ s), f₁ ≫ α = g₁ ≫ β ∧ f₂ ≫ α = g₂ ≫ β := by
  obtain ⟨t, k₁t, k₂t, ht⟩ := span f₁ g₁
  obtain ⟨s, ts, hs⟩ := IsFilteredOrEmpty.cocone_maps (f₂ ≫ k₁t) (g₂ ≫ k₂t)
  simp_rw [Category.assoc] at hs
  exact ⟨s, k₁t ≫ ts, k₂t ≫ ts, by simp only [← Category.assoc, ht], hs⟩

/--
theorem `crown` / 定理 `crown`

English:
theorem crown
  proof: by
  induction ι using Finite.induction_empty_option with
  | @of_equiv ι₁ ι₂ e IH =>
    obtain ⟨s, α, β, H⟩ := IH (j ∘ e) (f <| e ·) (g <| e ·)
    exact ⟨s, α, β, e.forall_congr_right.mp H⟩
  | h_empty => exact ⟨max k₁ k₂, leftToMax k₁ k₂, rightToMax k₁ k₂, by simp⟩
  | @h_option ι _ IH =>
    obtain ⟨s₁, α₁, β₁, H₁⟩ := IH (j ·) (f ·) (g ·)
    obtain ⟨s₂, α₂, β₂, H₂⟩ := span (f .none) (g .none)
    obtain ⟨t, α, β, h₁, h₂⟩ := bowtie α₁ α₂ β₁ β₂
    exact ⟨t, α₁ ≫ α, β₁ ≫ α, Option.rec (by grind) (by grind)⟩

中文:
定理 crown
  证明: by
  induction ι using Finite.induction_empty_option with
  | @of_equiv ι₁ ι₂ e IH =>
    obtain ⟨s, α, β, H⟩ := IH (j ∘ e) (f <| e ·) (g <| e ·)
    exact ⟨s, α, β, e.forall_congr_right.mp H⟩
  | h_empty => exact ⟨max k₁ k₂, leftToMax k₁ k₂, rightToMax k₁ k₂, by simp⟩
  | @h_option ι _ IH =>
    obtain ⟨s₁, α₁, β₁, H₁⟩ := IH (j ·) (f ·) (g ·)
    obtain ⟨s₂, α₂, β₂, H₂⟩ := span (f .none) (g .none)
    obtain ⟨t, α, β, h₁, h₂⟩ := bowtie α₁ α₂ β₁ β₂
    exact ⟨t, α₁ ≫ α, β₁ ≫ α, Option.rec (by grind) (by grind)⟩

Depends on / 依赖: Finite, Finite.induction_empty_option, Option.rec, bowtie, e.forall_congr_right.mp, forall_congr_right, h_empty, h_option, induction_empty_option, leftToMax, of_equiv, rightToMax
-/
theorem crown
    {ι : Type*} [Finite ι] (j : ι -> C) {k₁ k₂ : C} (f : forall i, j i ⟶ k₁) (g : forall i, j i ⟶ k₂) :
    exists (s : C) (α : k₁ ⟶ s) (β : k₂ ⟶ s), forall i, f i ≫ α = g i ≫ β := by
  induction ι using Finite.induction_empty_option with
  | @of_equiv ι₁ ι₂ e IH =>
    obtain ⟨s, α, β, H⟩ := IH (j ∘ e) (f <| e ·) (g <| e ·)
    exact ⟨s, α, β, e.forall_congr_right.mp H⟩
  | h_empty => exact ⟨max k₁ k₂, leftToMax k₁ k₂, rightToMax k₁ k₂, by simp⟩
  | @h_option ι _ IH =>
    obtain ⟨s₁, α₁, β₁, H₁⟩ := IH (j ·) (f ·) (g ·)
    obtain ⟨s₂, α₂, β₂, H₂⟩ := span (f .none) (g .none)
    obtain ⟨t, α, β, h₁, h₂⟩ := bowtie α₁ α₂ β₁ β₂
    exact ⟨t, α₁ ≫ α, β₁ ≫ α, Option.rec (by grind) (by grind)⟩

/--
theorem `crown₃` / 定理 `crown₃`

English:
theorem crown₃
  proof: by
  obtain ⟨s, α, β, H⟩ := crown ![j₁, j₂, j₃] (Fin.cons f₁ (Fin.cons f₂ (Fin.cons f₃ nofun)))
     (Fin.cons g₁ (Fin.cons g₂ (Fin.cons g₃ nofun)))
  exact ⟨s, α, β, H 0, H 1, H 2⟩

中文:
定理 crown₃
  证明: by
  obtain ⟨s, α, β, H⟩ := crown ![j₁, j₂, j₃] (Fin.cons f₁ (Fin.cons f₂ (Fin.cons f₃ nofun)))
     (Fin.cons g₁ (Fin.cons g₂ (Fin.cons g₃ nofun)))
  exact ⟨s, α, β, H 0, H 1, H 2⟩

Depends on / 依赖: Fin.cons
-/
theorem crown₃
    {j₁ j₂ j₃ k₁ k₂ : C} (f₁ : j₁ ⟶ k₁) (g₁ : j₁ ⟶ k₂) (f₂ : j₂ ⟶ k₁)
    (g₂ : j₂ ⟶ k₂) (f₃ : j₃ ⟶ k₁) (g₃ : j₃ ⟶ k₂) :
    exists (s : C) (α : k₁ ⟶ s) (β : k₂ ⟶ s),
      f₁ ≫ α = g₁ ≫ β ∧ f₂ ≫ α = g₂ ≫ β ∧ f₃ ≫ α = g₃ ≫ β := by
  obtain ⟨s, α, β, H⟩ := crown ![j₁, j₂, j₃] (Fin.cons f₁ (Fin.cons f₂ (Fin.cons f₃ nofun)))
     (Fin.cons g₁ (Fin.cons g₂ (Fin.cons g₃ nofun)))
  exact ⟨s, α, β, H 0, H 1, H 2⟩

/--
theorem `crown₄` / 定理 `crown₄`

English:
theorem crown₄
  proof: by
  obtain ⟨s, α, β, H⟩ := crown ![j₁, j₂, j₃, j₄]
      (Fin.cons f₁ (Fin.cons f₂ (Fin.cons f₃ (Fin.cons f₄ nofun))))
     (Fin.cons g₁ (Fin.cons g₂ (Fin.cons g₃ (Fin.cons g₄ nofun))))
  exact ⟨s, α, β, H 0, H 1, H 2, H 3⟩

中文:
定理 crown₄
  证明: by
  obtain ⟨s, α, β, H⟩ := crown ![j₁, j₂, j₃, j₄]
      (Fin.cons f₁ (Fin.cons f₂ (Fin.cons f₃ (Fin.cons f₄ nofun))))
     (Fin.cons g₁ (Fin.cons g₂ (Fin.cons g₃ (Fin.cons g₄ nofun))))
  exact ⟨s, α, β, H 0, H 1, H 2, H 3⟩

Depends on / 依赖: Fin.cons
-/
theorem crown₄
    {j₁ j₂ j₃ j₄ k₁ k₂ : C} (f₁ : j₁ ⟶ k₁) (g₁ : j₁ ⟶ k₂) (f₂ : j₂ ⟶ k₁)
    (g₂ : j₂ ⟶ k₂) (f₃ : j₃ ⟶ k₁) (g₃ : j₃ ⟶ k₂) (f₄ : j₄ ⟶ k₁) (g₄ : j₄ ⟶ k₂) :
    exists (s : C) (α : k₁ ⟶ s) (β : k₂ ⟶ s),
      f₁ ≫ α = g₁ ≫ β ∧ f₂ ≫ α = g₂ ≫ β ∧ f₃ ≫ α = g₃ ≫ β ∧ f₄ ≫ α = g₄ ≫ β := by
  obtain ⟨s, α, β, H⟩ := crown ![j₁, j₂, j₃, j₄]
      (Fin.cons f₁ (Fin.cons f₂ (Fin.cons f₃ (Fin.cons f₄ nofun))))
     (Fin.cons g₁ (Fin.cons g₂ (Fin.cons g₃ (Fin.cons g₄ nofun))))
  exact ⟨s, α, β, H 0, H 1, H 2, H 3⟩

/--
theorem `tulip` / 定理 `tulip`

English:
theorem tulip
  statement: {j₁ j₂ j₃ k₁ k₂ l : C} (f₁ : j₁ ⟶ k₁) (f₂ : j₂ ⟶ k₁) (f₃ : j₂ ⟶ k₂) (f₄ : j₃ ⟶ k₂)
  proof: by
  obtain ⟨l', k₁l, k₂l, hl⟩ := span f₂ f₃
  obtain ⟨s, ls, l's, hs₁, hs₂⟩ := bowtie g₁ (f₁ ≫ k₁l) g₂ (f₄ ≫ k₂l)
  refine ⟨s, k₁l ≫ l's, ls, k₂l ≫ l's, ?_, by simp only [← Category.assoc, hl], ?_⟩ <;>
    simp only [hs₁, hs₂, Category.assoc]

中文:
定理 tulip
  结论: {j₁ j₂ j₃ k₁ k₂ l : C} (f₁ : j₁ ⟶ k₁) (f₂ : j₂ ⟶ k₁) (f₃ : j₂ ⟶ k₂) (f₄ : j₃ ⟶ k₂)
  证明: by
  obtain ⟨l', k₁l, k₂l, hl⟩ := span f₂ f₃
  obtain ⟨s, ls, l's, hs₁, hs₂⟩ := bowtie g₁ (f₁ ≫ k₁l) g₂ (f₄ ≫ k₂l)
  refine ⟨s, k₁l ≫ l's, ls, k₂l ≫ l's, ?_, by simp only [← Category.assoc, hl], ?_⟩ <;>
    simp only [hs₁, hs₂, Category.assoc]

Depends on / 依赖: Category, Category.assoc, IsConnected, IsConnected.of_constant_of_preserves_morphisms, bowtie, exacts, of_constant_of_preserves_morphisms
-/
theorem tulip {j₁ j₂ j₃ k₁ k₂ l : C} (f₁ : j₁ ⟶ k₁) (f₂ : j₂ ⟶ k₁) (f₃ : j₂ ⟶ k₂) (f₄ : j₃ ⟶ k₂)
    (g₁ : j₁ ⟶ l) (g₂ : j₃ ⟶ l) :
    exists (s : C) (α : k₁ ⟶ s) (β : l ⟶ s) (γ : k₂ ⟶ s),
      f₁ ≫ α = g₁ ≫ β ∧ f₂ ≫ α = f₃ ≫ γ ∧ f₄ ≫ γ = g₂ ≫ β := by
  obtain ⟨l', k₁l, k₂l, hl⟩ := span f₂ f₃
  obtain ⟨s, ls, l's, hs₁, hs₂⟩ := bowtie g₁ (f₁ ≫ k₁l) g₂ (f₄ ≫ k₂l)
  refine ⟨s, k₁l ≫ l's, ls, k₂l ≫ l's, ?_, by simp only [← Category.assoc, hl], ?_⟩ <;>
    simp only [hs₁, hs₂, Category.assoc]

/--
lemma `wideSpan` / 引理 `wideSpan`

English:
lemma wideSpan
  given: {I : Type*} [Finite I] {i : C} {j : I -> C} (f : forall x, i ⟶ j x)
  proof: by
  have : IsFiltered C := { nonempty := ⟨i⟩ }
  classical
  cases nonempty_fintype I
  obtain ⟨k, fk, hk⟩ := sup_exists (insert i (Finset.univ.image j))
    (Finset.univ.image fun x => ⟨i, j x, by simp, by simp, f x⟩)
  exact ⟨k, _, _, fun x => hk _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))⟩

中文:
引理 wideSpan
  条件: {I : 类型} [有限 I] {i : C} {j : I -> C} (f : 对任意 x, i ⟶ j x)
  证明: by
  have : IsFiltered C := { nonempty := ⟨i⟩ }
  classical
  cases nonempty_fintype I
  obtain ⟨k, fk, hk⟩ := sup_exists (insert i (Finset.univ.image j))
    (Finset.univ.image fun x => ⟨i, j x, by simp, by simp, f x⟩)
  exact ⟨k, _, _, fun x => hk _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))⟩

Depends on / 依赖: Finset, Finset.mem_image_of_mem, Finset.mem_univ, Finset.univ.image, IsConnected, IsConnected.of_constant_of_preserves_morphisms, IsFiltered, classical, exacts, insert, mem_image_of_mem, mem_univ, nonempty, nonempty_fintype, of_constant_of_preserves_morphisms, sup_exists
-/
lemma wideSpan {I : Type*} [Finite I] {i : C} {j : I -> C} (f : forall x, i ⟶ j x) :
    exists k fik, exists g : forall x, j x ⟶ k, forall x, f x ≫ g x = fik := by
  have : IsFiltered C := { nonempty := ⟨i⟩ }
  classical
  cases nonempty_fintype I
  obtain ⟨k, fk, hk⟩ := sup_exists (insert i (Finset.univ.image j))
    (Finset.univ.image fun x => ⟨i, j x, by simp, by simp, f x⟩)
  exact ⟨k, _, _, fun x => hk _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))⟩

end SpecialShapes

end IsFiltered

/--
Definition of `IsCofilteredOrEmpty` / `IsCofilteredOrEmpty` 的定义

English:
class IsCofilteredOrEmpty
  parameters: : Prop where
  axioms and operations (2):
    - cone_objs : forall X Y : C, exists (W : _) (_ : W ⟶ X) (_ : W ⟶ Y), True
    - cone_maps : forall ⦃X Y : C⦄ (f g : X ⟶ Y), exists (W : _) (h : W ⟶ X), h ≫ f = h ≫ g

中文:
类 是余filteredOrEmpty
  参数: : 命题 where
  公理与运算 (2 个):
    - cone_objs : 对任意 X Y : C, 存在 (W : _) (_ : W ⟶ X) (_ : W ⟶ Y), 真
    - cone_maps : 对任意 ⦃X Y : C⦄ (f g : X ⟶ Y), 存在 (W : _) (h : W ⟶ X), h ≫ f = h ≫ g
-/
class IsCofilteredOrEmpty : Prop where
  /-- for every pair of objects there exists another object "to the left" -/
  cone_objs : forall X Y : C, exists (W : _) (_ : W ⟶ X) (_ : W ⟶ Y), True
  /-- for every pair of parallel morphisms there exists a morphism to the left
  so the compositions are equal -/
  cone_maps : forall ⦃X Y : C⦄ (f g : X ⟶ Y), exists (W : _) (h : W ⟶ X), h ≫ f = h ≫ g

/-- A category `IsCofiltered` if
1. for every pair of objects there exists another object "to the left",
2. for every pair of parallel morphisms there exists a morphism to the left so the compositions
   are equal, and
3. there exists some object. -/
@[stacks 04AZ]
/--
Definition of `IsCofiltered` / `IsCofiltered` 的定义

English:
class IsCofiltered
  parameters: : Prop extends IsCofilteredOrEmpty C where
  extends: IsCofilteredOrEmpty C
  axioms and operations (1):
    - [nonempty : Nonempty C]

中文:
类 是余filtered
  参数: : 命题 extends 是余filteredOrEmpty C where
  继承: 是余filteredOrEmpty C
  公理与运算 (1 个):
    - [nonempty : 非空 C]

Depends on / 依赖: HasCountableLimits, hasFiniteLimits_of_hasCountableLimits
-/
class IsCofiltered : Prop extends IsCofilteredOrEmpty C where
  /-- a cofiltered category must be non-empty -/
  -- This should be an instance but it causes significant slowdown
  [nonempty : Nonempty C]

instance (priority := 100) isCofilteredOrEmpty_of_semilatticeInf (α : Type u) [SemilatticeInf α] :
    IsCofilteredOrEmpty α where
  cone_objs X Y := ⟨X ⊓ Y, homOfLE inf_le_left, homOfLE inf_le_right, trivial⟩
  cone_maps X Y f g := ⟨X, 𝟙 _, by
    apply ULift.ext
    subsingleton⟩

instance (priority := 100) isCofiltered_of_semilatticeInf_nonempty (α : Type u) [SemilatticeInf α]
    [Nonempty α] : IsCofiltered α where

instance (priority := 100) isCofilteredOrEmpty_of_directed_ge (α : Type u) [Preorder α]
    [IsCodirectedOrder α] : IsCofilteredOrEmpty α where
  cone_objs X Y :=
    let ⟨Z, hX, hY⟩ := exists_le_le X Y
    ⟨Z, homOfLE hX, homOfLE hY, trivial⟩
  cone_maps X Y f g := ⟨X, 𝟙 _, by
    apply ULift.ext
    subsingleton⟩

instance (priority := 100) isCofiltered_of_directed_ge_nonempty (α : Type u) [Preorder α]
    [IsCodirectedOrder α] [Nonempty α] : IsCofiltered α where

-- Sanity checks
example (α : Type u) [SemilatticeInf α] [OrderBot α] : IsCofiltered α := by infer_instance

example (α : Type u) [SemilatticeInf α] [OrderTop α] : IsCofiltered α := by infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsCofiltered (Discrete PUnit)
  body: ⟨⟨PUnit.unit⟩, ⟨⟨by trivial⟩⟩, ⟨⟨by subsingleton⟩⟩, trivial⟩
  cone_maps X Y f g := ⟨⟨PUnit.unit⟩, ⟨⟨by trivial⟩⟩, by
    apply ULift.ext
    subsingleton⟩

中文:
实例 :
  签名: 是余filtered (离散 命题单元)
  定义体: ⟨⟨PUnit.unit⟩, ⟨⟨by trivial⟩⟩, ⟨⟨by subsingleton⟩⟩, trivial⟩
  cone_maps X Y f g := ⟨⟨PUnit.unit⟩, ⟨⟨by trivial⟩⟩, by
    apply ULift.ext
    subsingleton⟩

Depends on / 依赖: HasLimits, PUnit.unit, hasCountableLimits_of_hasLimits, subsingleton
-/
instance : IsCofiltered (Discrete PUnit) where
  cone_objs _ Y := ⟨⟨PUnit.unit⟩, ⟨⟨by trivial⟩⟩, ⟨⟨by subsingleton⟩⟩, trivial⟩
  cone_maps X Y f g := ⟨⟨PUnit.unit⟩, ⟨⟨by trivial⟩⟩, by
    apply ULift.ext
    subsingleton⟩

namespace IsCofiltered

section AllowEmpty

variable {C}
variable [IsCofilteredOrEmpty C]

/--
Definition of `min` / `min` 的定义

English:
definition min
  signature: (j j' : C)
  body: (IsCofilteredOrEmpty.cone_objs j j').choose

中文:
定义 最小值
  签名: (j j' : C)
  定义体: (IsCofilteredOrEmpty.cone_objs j j').choose

Depends on / 依赖: IsCofilteredOrEmpty, IsCofilteredOrEmpty.cone_objs, cone_objs
-/
noncomputable def min (j j' : C) : C :=
  (IsCofilteredOrEmpty.cone_objs j j').choose

/--
Definition of `minToLeft` / `minToLeft` 的定义

English:
definition minToLeft
  signature: (j j' : C)
  body: (IsCofilteredOrEmpty.cone_objs j j').choose_spec.choose

中文:
定义 minToLeft
  签名: (j j' : C)
  定义体: (IsCofilteredOrEmpty.cone_objs j j').choose_spec.choose

Depends on / 依赖: IsCofilteredOrEmpty, IsCofilteredOrEmpty.cone_objs, choose_spec, choose_spec.choose, cone_objs
-/
noncomputable def minToLeft (j j' : C) : min j j' ⟶ j :=
  (IsCofilteredOrEmpty.cone_objs j j').choose_spec.choose

/--
Definition of `minToRight` / `minToRight` 的定义

English:
definition minToRight
  signature: (j j' : C)
  body: (IsCofilteredOrEmpty.cone_objs j j').choose_spec.choose_spec.choose

中文:
定义 minToRight
  签名: (j j' : C)
  定义体: (IsCofilteredOrEmpty.cone_objs j j').choose_spec.choose_spec.choose

Depends on / 依赖: HasProducts, IsCofilteredOrEmpty, IsCofilteredOrEmpty.cone_objs, choose_spec, choose_spec.choose_spec.choose, cone_objs, hasCountableProducts_of_hasProducts
-/
noncomputable def minToRight (j j' : C) : min j j' ⟶ j' :=
  (IsCofilteredOrEmpty.cone_objs j j').choose_spec.choose_spec.choose

/--
Definition of `eq` / `eq` 的定义

English:
definition eq
  signature: {j j' : C} (f f' : j ⟶ j')
  body: (IsCofilteredOrEmpty.cone_maps f f').choose

中文:
定义 eq
  签名: {j j' : C} (f f' : j ⟶ j')
  定义体: (IsCofilteredOrEmpty.cone_maps f f').choose

Depends on / 依赖: HasCountableLimits, IsCofilteredOrEmpty, IsCofilteredOrEmpty.cone_maps, cone_maps, hasCountableProducts_of_hasCountableLimits
-/
noncomputable def eq {j j' : C} (f f' : j ⟶ j') : C :=
  (IsCofilteredOrEmpty.cone_maps f f').choose

/--
Definition of `eqHom` / `eqHom` 的定义

English:
definition eqHom
  signature: {j j' : C} (f f' : j ⟶ j')
  body: (IsCofilteredOrEmpty.cone_maps f f').choose_spec.choose

中文:
定义 eqHom
  签名: {j j' : C} (f f' : j ⟶ j')
  定义体: (IsCofilteredOrEmpty.cone_maps f f').choose_spec.choose

Depends on / 依赖: HasCountableProducts, IsCofilteredOrEmpty, IsCofilteredOrEmpty.cone_maps, choose_spec, choose_spec.choose, cone_maps, hasFiniteProducts_of_hasCountableProducts
-/
noncomputable def eqHom {j j' : C} (f f' : j ⟶ j') : eq f f' ⟶ j :=
  (IsCofilteredOrEmpty.cone_maps f f').choose_spec.choose

/-- `eq_condition f f'`, for morphisms `f f' : j ⟶ j'`, is the proof that
`eqHom f f' ≫ f = eqHom f f' ≫ f'`.
-/
@[reassoc] -- Not `@[simp]` as it does not fire.
/--
theorem `eq_condition` / 定理 `eq_condition`

English:
theorem eq_condition
  given: {j j' : C} (f f' : j ⟶ j')
  statement: eqHom f f' ≫ f = eqHom f f' ≫ f'
  proof: (IsCofilteredOrEmpty.cone_maps f f').choose_spec.choose_spec

中文:
定理 eq_condition
  条件: {j j' : C} (f f' : j ⟶ j')
  结论: eqHom f f' ≫ f = eqHom f f' ≫ f'
  证明: (IsCofilteredOrEmpty.cone_maps f f').choose_spec.choose_spec

Depends on / 依赖: HasCountableColimits, IsCofilteredOrEmpty, IsCofilteredOrEmpty.cone_maps, choose_spec, choose_spec.choose_spec, cone_maps, hasFiniteColimits_of_hasCountableColimits
-/
theorem eq_condition {j j' : C} (f f' : j ⟶ j') : eqHom f f' ≫ f = eqHom f f' ≫ f' :=
  (IsCofilteredOrEmpty.cone_maps f f').choose_spec.choose_spec

/--
theorem `cospan` / 定理 `cospan`

English:
theorem cospan
  given: {i j j' : C} (f : j ⟶ i) (f' : j' ⟶ i)
  proof: let ⟨K, G, G', _⟩ := IsCofilteredOrEmpty.cone_objs j j'
  let ⟨k, e, he⟩ := IsCofilteredOrEmpty.cone_maps (G ≫ f) (G' ≫ f')
  ⟨k, e ≫ G, e ≫ G', by simpa only [Category.assoc] using he⟩

中文:
定理 cospan
  条件: {i j j' : C} (f : j ⟶ i) (f' : j' ⟶ i)
  证明: let ⟨K, G, G', _⟩ := IsCofilteredOrEmpty.cone_objs j j'
  let ⟨k, e, he⟩ := IsCofilteredOrEmpty.cone_maps (G ≫ f) (G' ≫ f')
  ⟨k, e ≫ G, e ≫ G', by simpa only [Category.assoc] using he⟩

Depends on / 依赖: Category, Category.assoc, HasColimits, IsCofilteredOrEmpty, IsCofilteredOrEmpty.cone_maps, IsCofilteredOrEmpty.cone_objs, cone_maps, cone_objs, hasCountableColimits_of_hasColimits
-/
theorem cospan {i j j' : C} (f : j ⟶ i) (f' : j' ⟶ i) :
    exists (k : C) (g : k ⟶ j) (g' : k ⟶ j'), g ≫ f = g' ≫ f' :=
  let ⟨K, G, G', _⟩ := IsCofilteredOrEmpty.cone_objs j j'
  let ⟨k, e, he⟩ := IsCofilteredOrEmpty.cone_maps (G ≫ f) (G' ≫ f')
  ⟨k, e ≫ G, e ≫ G', by simpa only [Category.assoc] using he⟩

/--
theorem `_root_.CategoryTheory.Functor.ranges_directed` / 定理 `_root_.CategoryTheory.Functor.ranges_directed`

English:
theorem _root_.CategoryTheory.Functor.ranges_directed
  given: (F : C ⥤ Type*) (j : C)
  proof: fun ⟨i, ij⟩ ⟨k, kj⟩ => by
  let ⟨l, li, lk, e⟩ := cospan ij kj
  refine ⟨⟨l, lk ≫ kj⟩, e ▸ ?_, ?_⟩ <;>
    simp_rw [F.map_comp] <;>
    convert! Set.range_comp_subset_range _ _

中文:
定理 _root_.范畴论.函子.ranges_directed
  条件: (F : C ⥤ 类型) (j : C)
  证明: fun ⟨i, ij⟩ ⟨k, kj⟩ => by
  let ⟨l, li, lk, e⟩ := cospan ij kj
  refine ⟨⟨l, lk ≫ kj⟩, e ▸ ?_, ?_⟩ <;>
    simp_rw [F.map_comp] <;>
    convert! Set.range_comp_subset_range _ _

Depends on / 依赖: F.map_comp, Set.range_comp_subset_range, convert, cospan, map_comp, range_comp_subset_range, simp_rw
-/
theorem _root_.CategoryTheory.Functor.ranges_directed (F : C ⥤ Type*) (j : C) :
    Directed (· ⊇ ·) fun f : Σ' i, i ⟶ j => Set.range (F.map f.2) := fun ⟨i, ij⟩ ⟨k, kj⟩ => by
  let ⟨l, li, lk, e⟩ := cospan ij kj
  refine ⟨⟨l, lk ≫ kj⟩, e ▸ ?_, ?_⟩ <;>
    simp_rw [F.map_comp] <;>
    convert! Set.range_comp_subset_range _ _

/--
theorem `bowtie` / 定理 `bowtie`

English:
theorem bowtie
  given: {j₁ j₂ k₁ k₂ : C} (f₁ : k₁ ⟶ j₁) (g₁ : k₂ ⟶ j₁) (f₂ : k₁ ⟶ j₂) (g₂ : k₂ ⟶ j₂)
  proof: by
  obtain ⟨t, k₁t, k₂t, ht⟩ := cospan f₁ g₁
  obtain ⟨s, ts, hs⟩ := IsCofilteredOrEmpty.cone_maps (k₁t ≫ f₂) (k₂t ≫ g₂)
  exact ⟨s, ts ≫ k₁t, ts ≫ k₂t, by simp only [Category.assoc, ht],
    by simp only [Category.assoc, hs]⟩

中文:
定理 bowtie
  条件: {j₁ j₂ k₁ k₂ : C} (f₁ : k₁ ⟶ j₁) (g₁ : k₂ ⟶ j₁) (f₂ : k₁ ⟶ j₂) (g₂ : k₂ ⟶ j₂)
  证明: by
  obtain ⟨t, k₁t, k₂t, ht⟩ := cospan f₁ g₁
  obtain ⟨s, ts, hs⟩ := IsCofilteredOrEmpty.cone_maps (k₁t ≫ f₂) (k₂t ≫ g₂)
  exact ⟨s, ts ≫ k₁t, ts ≫ k₂t, by simp only [Category.assoc, ht],
    by simp only [Category.assoc, hs]⟩

Depends on / 依赖: Category, Category.assoc, HasCoproducts, IsCofilteredOrEmpty, IsCofilteredOrEmpty.cone_maps, cone_maps, cospan, hasCountableCoproducts_of_hasCoproducts
-/
theorem bowtie {j₁ j₂ k₁ k₂ : C} (f₁ : k₁ ⟶ j₁) (g₁ : k₂ ⟶ j₁) (f₂ : k₁ ⟶ j₂) (g₂ : k₂ ⟶ j₂) :
    exists (s : C) (α : s ⟶ k₁) (β : s ⟶ k₂), α ≫ f₁ = β ≫ g₁ ∧ α ≫ f₂ = β ≫ g₂ := by
  obtain ⟨t, k₁t, k₂t, ht⟩ := cospan f₁ g₁
  obtain ⟨s, ts, hs⟩ := IsCofilteredOrEmpty.cone_maps (k₁t ≫ f₂) (k₂t ≫ g₂)
  exact ⟨s, ts ≫ k₁t, ts ≫ k₂t, by simp only [Category.assoc, ht],
    by simp only [Category.assoc, hs]⟩

end AllowEmpty

end IsCofiltered

namespace IsCofilteredOrEmpty
open IsCofiltered

variable {C}
variable [IsCofilteredOrEmpty C]
variable {D : Type u₁} [Category.{v₁} D]

/--
theorem `of_left_adjoint` / 定理 `of_left_adjoint`

English:
theorem of_left_adjoint
  given: {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R)
  statement: IsCofilteredOrEmpty D
  proof: { cone_objs := fun X Y =>
      ⟨L.obj (min (R.obj X) (R.obj Y)), (h.homEquiv _ X).symm (minToLeft _ _),
        (h.homEquiv _ Y).symm (minToRight _ _), ⟨⟩⟩
    cone_maps := fun X Y f g =>
      ⟨L.obj (eq (R.map f) (R.map g)), (h.homEquiv _ _).symm (eqHom _ _), by
        rw [← h.homEquiv_naturality_right_symm]; rw [← h.homEquiv_naturality_right_symm]; rw [eq_condition]⟩ }

中文:
定理 of_left_adjoint
  条件: {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R)
  结论: 是余filteredOrEmpty D
  证明: { cone_objs := fun X Y =>
      ⟨L.obj (min (R.obj X) (R.obj Y)), (h.homEquiv _ X).symm (minToLeft _ _),
        (h.homEquiv _ Y).symm (minToRight _ _), ⟨⟩⟩
    cone_maps := fun X Y f g =>
      ⟨L.obj (eq (R.map f) (R.map g)), (h.homEquiv _ _).symm (eqHom _ _), by
        rw [← h.homEquiv_naturality_right_symm]; rw [← h.homEquiv_naturality_right_symm]; rw [eq_condition]⟩ }

Depends on / 依赖: L.obj, R.map, R.obj, cone_maps, cone_objs, eq_condition, h.homEquiv, h.homEquiv_naturality_right_symm, homEquiv, homEquiv_naturality_right_symm, minToLeft, minToRight
-/
theorem of_left_adjoint {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R) : IsCofilteredOrEmpty D :=
  { cone_objs := fun X Y =>
      ⟨L.obj (min (R.obj X) (R.obj Y)), (h.homEquiv _ X).symm (minToLeft _ _),
        (h.homEquiv _ Y).symm (minToRight _ _), ⟨⟩⟩
    cone_maps := fun X Y f g =>
      ⟨L.obj (eq (R.map f) (R.map g)), (h.homEquiv _ _).symm (eqHom _ _), by
        rw [← h.homEquiv_naturality_right_symm]; rw [← h.homEquiv_naturality_right_symm]; rw [eq_condition]⟩ }

/--
theorem `of_isLeftAdjoint` / 定理 `of_isLeftAdjoint`

English:
theorem of_isLeftAdjoint
  given: (L : C ⥤ D) [L.IsLeftAdjoint]
  statement: IsCofilteredOrEmpty D
  proof: of_left_adjoint (Adjunction.ofIsLeftAdjoint L)

中文:
定理 of_isLeftAdjoint
  条件: (L : C ⥤ D) [L.是左伴随]
  结论: 是余filteredOrEmpty D
  证明: of_left_adjoint (Adjunction.ofIsLeftAdjoint L)

Depends on / 依赖: Adjunction, Adjunction.ofIsLeftAdjoint, HasCountableColimits, hasCountableCoproducts_of_hasCountableColimits, ofIsLeftAdjoint, of_left_adjoint
-/
theorem of_isLeftAdjoint (L : C ⥤ D) [L.IsLeftAdjoint] : IsCofilteredOrEmpty D :=
  of_left_adjoint (Adjunction.ofIsLeftAdjoint L)

/--
theorem `of_equivalence` / 定理 `of_equivalence`

English:
theorem of_equivalence
  given: (h : C ≌ D)
  statement: IsCofilteredOrEmpty D
  proof: of_left_adjoint h.toAdjunction

中文:
定理 of_equivalence
  条件: (h : C ≌ D)
  结论: 是余filteredOrEmpty D
  证明: of_left_adjoint h.toAdjunction

Depends on / 依赖: h.toAdjunction, hasFiniteCoproducts_of_hasCountableCoproducts, of_left_adjoint, toAdjunction
-/
theorem of_equivalence (h : C ≌ D) : IsCofilteredOrEmpty D :=
  of_left_adjoint h.toAdjunction

end IsCofilteredOrEmpty

namespace IsCofiltered

section Nonempty

open CategoryTheory.Limits

variable {C}
variable [IsCofiltered C]

/--
theorem `inf_objs_exists` / 定理 `inf_objs_exists`

English:
theorem inf_objs_exists
  given: (O : Finset C)
  statement: exists S : C, forall {X}, X in O -> Nonempty (S ⟶ X)
  proof: by
  classical
  induction O using Finset.induction with
  | empty => exact ⟨Classical.choice IsCofiltered.nonempty, by simp⟩
  | insert X O' nm h =>
    obtain ⟨S', w'⟩ := h
    use min X S'
    rintro Y mY
    obtain rfl | h := eq_or_ne Y X
    · exact ⟨minToLeft _ _⟩
    · exact ⟨minToRight _ _ ≫ (w' (Finset.mem_of_mem_insert_of_ne mY h)).some⟩

中文:
定理 inf_objs_存在
  条件: (O : 有限集 C)
  结论: 存在 S : C, 对任意 {X}, X in O -> 非空 (S ⟶ X)
  证明: by
  classical
  induction O using Finset.induction with
  | empty => exact ⟨Classical.choice IsCofiltered.nonempty, by simp⟩
  | insert X O' nm h =>
    obtain ⟨S', w'⟩ := h
    use min X S'
    rintro Y mY
    obtain rfl | h := eq_or_ne Y X
    · exact ⟨minToLeft _ _⟩
    · exact ⟨minToRight _ _ ≫ (w' (Finset.mem_of_mem_insert_of_ne mY h)).some⟩

Depends on / 依赖: Classical, Classical.choice, Finset, Finset.induction, Finset.mem_of_mem_insert_of_ne, IsCofiltered, IsCofiltered.nonempty, choice, classical, eq_or_ne, insert, mem_of_mem_insert_of_ne, minToLeft, minToRight, nonempty
-/
theorem inf_objs_exists (O : Finset C) : exists S : C, forall {X}, X in O -> Nonempty (S ⟶ X) := by
  classical
  induction O using Finset.induction with
  | empty => exact ⟨Classical.choice IsCofiltered.nonempty, by simp⟩
  | insert X O' nm h =>
    obtain ⟨S', w'⟩ := h
    use min X S'
    rintro Y mY
    obtain rfl | h := eq_or_ne Y X
    · exact ⟨minToLeft _ _⟩
    · exact ⟨minToRight _ _ ≫ (w' (Finset.mem_of_mem_insert_of_ne mY h)).some⟩

variable (O : Finset C) (H : Finset (Σ' (X Y : C) (_ : X in O) (_ : Y in O), X ⟶ Y))

/--
theorem `inf_exists` / 定理 `inf_exists`

English:
theorem inf_exists
  proof: by
  classical
  induction H using Finset.induction with
  | empty =>
    obtain ⟨S, f⟩ := inf_objs_exists O
    exact ⟨S, fun mX => (f mX).some, by rintro - - - - - ⟨⟩⟩
  | insert h' H' nmf h'' =>
    obtain ⟨X, Y, mX, mY, f⟩ := h'
    obtain ⟨S', T', w'⟩ := h''
    refine ⟨eq (T' mX ≫ f) (T' mY), fun mZ => eqHom (T' mX ≫ f) (T' mY) ≫ T' mZ, ?_⟩
    intro X' Y' mX' mY' f' mf'
    rw [Category.assoc]
    by_cases h : X = X' ∧ Y = Y'
    · rcases h with ⟨rfl, rfl⟩
      grind [eq_condition]
    · rw [@w' _ _ mX' mY' f' _]
      apply Finset.mem_of_mem_insert_of_ne mf'
      contrapose h
      obtain ⟨rfl, h⟩ := h
      trivial

中文:
定理 inf_存在
  证明: by
  classical
  induction H using Finset.induction with
  | empty =>
    obtain ⟨S, f⟩ := inf_objs_exists O
    exact ⟨S, fun mX => (f mX).some, by rintro - - - - - ⟨⟩⟩
  | insert h' H' nmf h'' =>
    obtain ⟨X, Y, mX, mY, f⟩ := h'
    obtain ⟨S', T', w'⟩ := h''
    refine ⟨eq (T' mX ≫ f) (T' mY), fun mZ => eqHom (T' mX ≫ f) (T' mY) ≫ T' mZ, ?_⟩
    intro X' Y' mX' mY' f' mf'
    rw [Category.assoc]
    by_cases h : X = X' ∧ Y = Y'
    · rcases h with ⟨rfl, rfl⟩
      grind [eq_condition]
    · rw [@w' _ _ mX' mY' f' _]
      apply Finset.mem_of_mem_insert_of_ne mf'
      contrapose h
      obtain ⟨rfl, h⟩ := h
      trivial

Depends on / 依赖: Category, Category.assoc, Finset, Finset.induction, Finset.mem_of_mem_ins, classical, eq_condition, inf_objs_exists, insert, mem_of_mem_ins
-/
theorem inf_exists :
    exists (S : C) (T : forall {X : C}, X in O -> (S ⟶ X)),
      forall {X Y : C} (mX : X in O) (mY : Y in O) {f : X ⟶ Y},
        (⟨X, Y, mX, mY, f⟩ : Σ' (X Y : C) (_ : X in O) (_ : Y in O), X ⟶ Y) in H ->
          T mX ≫ f = T mY := by
  classical
  induction H using Finset.induction with
  | empty =>
    obtain ⟨S, f⟩ := inf_objs_exists O
    exact ⟨S, fun mX => (f mX).some, by rintro - - - - - ⟨⟩⟩
  | insert h' H' nmf h'' =>
    obtain ⟨X, Y, mX, mY, f⟩ := h'
    obtain ⟨S', T', w'⟩ := h''
    refine ⟨eq (T' mX ≫ f) (T' mY), fun mZ => eqHom (T' mX ≫ f) (T' mY) ≫ T' mZ, ?_⟩
    intro X' Y' mX' mY' f' mf'
    rw [Category.assoc]
    by_cases h : X = X' ∧ Y = Y'
    · rcases h with ⟨rfl, rfl⟩
      grind [eq_condition]
    · rw [@w' _ _ mX' mY' f' _]
      apply Finset.mem_of_mem_insert_of_ne mf'
      contrapose h
      obtain ⟨rfl, h⟩ := h
      trivial

/--
Definition of `inf` / `inf` 的定义

English:
definition inf
  signature: : C
  body: (inf_exists O H).choose

中文:
定义 下确界
  签名: : C
  定义体: (inf_exists O H).choose

Depends on / 依赖: inf_exists
-/
noncomputable def inf : C :=
  (inf_exists O H).choose

/--
Definition of `infTo` / `infTo` 的定义

English:
definition infTo
  signature: {X : C} (m : X in O)
  body: (inf_exists O H).choose_spec.choose m

中文:
定义 infTo
  签名: {X : C} (m : X in O)
  定义体: (inf_exists O H).choose_spec.choose m

Depends on / 依赖: choose_spec, choose_spec.choose, inf_exists
-/
noncomputable def infTo {X : C} (m : X in O) : inf O H ⟶ X :=
  (inf_exists O H).choose_spec.choose m

/--
theorem `infTo_commutes` / 定理 `infTo_commutes`

English:
theorem infTo_commutes
  statement: {X Y : C} (mX : X in O) (mY : Y in O) {f : X ⟶ Y}
  proof: (inf_exists O H).choose_spec.choose_spec mX mY mf

中文:
定理 infTo_commutes
  结论: {X Y : C} (mX : X in O) (mY : Y in O) {f : X ⟶ Y}
  证明: (inf_exists O H).choose_spec.choose_spec mX mY mf

Depends on / 依赖: choose_spec, choose_spec.choose_spec, inf_exists
-/
theorem infTo_commutes {X Y : C} (mX : X in O) (mY : Y in O) {f : X ⟶ Y}
    (mf : (⟨X, Y, mX, mY, f⟩ : Σ' (X Y : C) (_ : X in O) (_ : Y in O), X ⟶ Y) in H) :
    infTo O H mX ≫ f = infTo O H mY :=
  (inf_exists O H).choose_spec.choose_spec mX mY mf

variable {J : Type w} [SmallCategory J] [FinCategory J]

set_option backward.defeqAttrib.useBackward true in
/--
theorem `cone_nonempty` / 定理 `cone_nonempty`

English:
theorem cone_nonempty
  given: (F : J ⥤ C)
  statement: Nonempty (Cone F)
  proof: by
  classical
  let O := Finset.univ.image F.obj
  let H : Finset (Σ' (X Y : C) (_ : X in O) (_ : Y in O), X ⟶ Y) :=
    Finset.univ.biUnion fun X : J =>
      Finset.univ.biUnion fun Y : J =>
        Finset.univ.image fun f : X ⟶ Y => ⟨F.obj X, F.obj Y, by simp [O], by simp [O], F.map f⟩
  obtain ⟨Z, f, w⟩ := inf_exists O H
  refine ⟨⟨Z, ⟨fun X => f (by simp [O]), ?_⟩⟩⟩
  intro j j' g
  dsimp
  simp only [Category.id_comp]
  symm
  apply w
  simp only [O, H, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_image,
    PSigma.mk.injEq, true_and, exists_and_left]
  exact ⟨j, rfl, j', g, by simp⟩

中文:
定理 cone_nonempty
  条件: (F : J ⥤ C)
  结论: 非空 (锥 F)
  证明: by
  classical
  let O := Finset.univ.image F.obj
  let H : Finset (Σ' (X Y : C) (_ : X in O) (_ : Y in O), X ⟶ Y) :=
    Finset.univ.biUnion fun X : J =>
      Finset.univ.biUnion fun Y : J =>
        Finset.univ.image fun f : X ⟶ Y => ⟨F.obj X, F.obj Y, by simp [O], by simp [O], F.map f⟩
  obtain ⟨Z, f, w⟩ := inf_exists O H
  refine ⟨⟨Z, ⟨fun X => f (by simp [O]), ?_⟩⟩⟩
  intro j j' g
  dsimp
  simp only [Category.id_comp]
  symm
  apply w
  simp only [O, H, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_image,
    PSigma.mk.injEq, true_and, exists_and_left]
  exact ⟨j, rfl, j', g, by simp⟩

Depends on / 依赖: Category, Category.id_comp, F.map, F.obj, Finset, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, Finset.univ.biUnion, Finset.univ.image, PSigma, PSigma.mk.injEq, biUnion, classical, id_comp, inf_exists, mem_biUnion, mem_image, mem_univ
-/
theorem cone_nonempty (F : J ⥤ C) : Nonempty (Cone F) := by
  classical
  let O := Finset.univ.image F.obj
  let H : Finset (Σ' (X Y : C) (_ : X in O) (_ : Y in O), X ⟶ Y) :=
    Finset.univ.biUnion fun X : J =>
      Finset.univ.biUnion fun Y : J =>
        Finset.univ.image fun f : X ⟶ Y => ⟨F.obj X, F.obj Y, by simp [O], by simp [O], F.map f⟩
  obtain ⟨Z, f, w⟩ := inf_exists O H
  refine ⟨⟨Z, ⟨fun X => f (by simp [O]), ?_⟩⟩⟩
  intro j j' g
  dsimp
  simp only [Category.id_comp]
  symm
  apply w
  simp only [O, H, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_image,
    PSigma.mk.injEq, true_and, exists_and_left]
  exact ⟨j, rfl, j', g, by simp⟩

/--
Definition of `cone` / `cone` 的定义

English:
definition cone
  signature: (F : J ⥤ C)
  body: (cone_nonempty F).some

中文:
定义 cone
  签名: (F : J ⥤ C)
  定义体: (cone_nonempty F).some

Depends on / 依赖: cone_nonempty
-/
noncomputable def cone (F : J ⥤ C) : Cone F :=
  (cone_nonempty F).some

variable {D : Type u₁} [Category.{v₁} D]

/--
theorem `of_left_adjoint` / 定理 `of_left_adjoint`

English:
theorem of_left_adjoint
  given: {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R)
  statement: IsCofiltered D
  proof: { IsCofilteredOrEmpty.of_left_adjoint h with
    nonempty := IsCofiltered.nonempty.map L.obj }

中文:
定理 of_left_adjoint
  条件: {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R)
  结论: 是余filtered D
  证明: { IsCofilteredOrEmpty.of_left_adjoint h with
    nonempty := IsCofiltered.nonempty.map L.obj }

Depends on / 依赖: IsCofiltered, IsCofiltered.nonempty.map, IsCofilteredOrEmpty, IsCofilteredOrEmpty.of_left_adjoint, L.obj, nonempty, of_left_adjoint
-/
theorem of_left_adjoint {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R) : IsCofiltered D :=
  { IsCofilteredOrEmpty.of_left_adjoint h with
    nonempty := IsCofiltered.nonempty.map L.obj }

/--
theorem `of_isLeftAdjoint` / 定理 `of_isLeftAdjoint`

English:
theorem of_isLeftAdjoint
  given: (L : C ⥤ D) [L.IsLeftAdjoint]
  statement: IsCofiltered D
  proof: of_left_adjoint (Adjunction.ofIsLeftAdjoint L)

中文:
定理 of_isLeftAdjoint
  条件: (L : C ⥤ D) [L.是左伴随]
  结论: 是余filtered D
  证明: of_left_adjoint (Adjunction.ofIsLeftAdjoint L)

Depends on / 依赖: Adjunction, Adjunction.ofIsLeftAdjoint, ofIsLeftAdjoint, of_left_adjoint
-/
theorem of_isLeftAdjoint (L : C ⥤ D) [L.IsLeftAdjoint] : IsCofiltered D :=
  of_left_adjoint (Adjunction.ofIsLeftAdjoint L)

/--
theorem `of_equivalence` / 定理 `of_equivalence`

English:
theorem of_equivalence
  given: (h : C ≌ D)
  statement: IsCofiltered D
  proof: of_left_adjoint h.toAdjunction

omit [IsCofiltered C] in

中文:
定理 of_equivalence
  条件: (h : C ≌ D)
  结论: 是余filtered D
  证明: of_left_adjoint h.toAdjunction

omit [IsCofiltered C] in

Depends on / 依赖: h.toAdjunction, of_left_adjoint, toAdjunction
-/
theorem of_equivalence (h : C ≌ D) : IsCofiltered D :=
  of_left_adjoint h.toAdjunction

omit [IsCofiltered C] in
/--
lemma `iff_of_equivalence` / 引理 `iff_of_equivalence`

English:
lemma iff_of_equivalence
  given: (e : C ≌ D)
  statement: IsCofiltered C ↔ IsCofiltered D
  proof: ⟨fun _ => .of_equivalence e, fun _ => .of_equivalence e.symm⟩

omit [IsCofiltered C] in

中文:
引理 iff_of_equivalence
  条件: (e : C ≌ D)
  结论: 是余filtered C ↔ 是余filtered D
  证明: ⟨fun _ => .of_equivalence e, fun _ => .of_equivalence e.symm⟩

omit [IsCofiltered C] in

Depends on / 依赖: e.symm, of_equivalence
-/
lemma iff_of_equivalence (e : C ≌ D) : IsCofiltered C ↔ IsCofiltered D :=
  ⟨fun _ => .of_equivalence e, fun _ => .of_equivalence e.symm⟩

omit [IsCofiltered C] in
/--
lemma `wideCospan` / 引理 `wideCospan`

English:
lemma wideCospan
  statement: [IsCofilteredOrEmpty C]
  proof: by
  have : IsCofiltered C := { nonempty := ⟨i⟩ }
  classical
  cases nonempty_fintype I
  obtain ⟨k, fk, hk⟩ := IsCofiltered.inf_exists (insert i (Finset.univ.image j))
    (Finset.univ.image fun x => ⟨j x, i, by simp, by simp, f x⟩)
  exact ⟨k, _, _, fun x => hk _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))⟩

中文:
引理 wideCospan
  结论: [是余filteredOrEmpty C]
  证明: by
  have : IsCofiltered C := { nonempty := ⟨i⟩ }
  classical
  cases nonempty_fintype I
  obtain ⟨k, fk, hk⟩ := IsCofiltered.inf_exists (insert i (Finset.univ.image j))
    (Finset.univ.image fun x => ⟨j x, i, by simp, by simp, f x⟩)
  exact ⟨k, _, _, fun x => hk _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))⟩

Depends on / 依赖: Finset, Finset.mem_image_of_mem, Finset.mem_univ, Finset.univ.image, IsCofiltered, IsCofiltered.inf_exists, classical, inf_exists, insert, mem_image_of_mem, mem_univ, nonempty, nonempty_fintype
-/
lemma wideCospan [IsCofilteredOrEmpty C]
    {I : Type*} [Finite I] {i : C} {j : I -> C} (f : forall x, j x ⟶ i) :
    exists k fki, exists g : forall x, k ⟶ j x, forall x, g x ≫ f x = fki := by
  have : IsCofiltered C := { nonempty := ⟨i⟩ }
  classical
  cases nonempty_fintype I
  obtain ⟨k, fk, hk⟩ := IsCofiltered.inf_exists (insert i (Finset.univ.image j))
    (Finset.univ.image fun x => ⟨j x, i, by simp, by simp, f x⟩)
  exact ⟨k, _, _, fun x => hk _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))⟩

end Nonempty


section OfCone

open CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false in
/--
theorem `of_cone_nonempty` / 定理 `of_cone_nonempty`

English:
theorem of_cone_nonempty
  statement: (h : forall {J : Type w} [SmallCategory J] [FinCategory J] (F : J ⥤ C),
  proof: by
  have : Nonempty C := by
    obtain ⟨c⟩ := h (Functor.empty _)
    exact ⟨c.pt⟩
  have : IsCofilteredOrEmpty C := by
    refine ⟨?_, ?_⟩
    · intro X Y
      obtain ⟨c⟩ := h (ULiftHom.down ⋙ ULift.downFunctor ⋙ pair X Y)
      exact ⟨c.pt, c.π.app ⟨⟨WalkingPair.left⟩⟩, c.π.app ⟨⟨WalkingPair.right⟩⟩, trivial⟩
    · intro X Y f g
      obtain ⟨c⟩ := h (ULiftHom.down ⋙ ULift.downFunctor ⋙ parallelPair f g)
      refine ⟨c.pt, c.π.app ⟨WalkingParallelPair.zero⟩, ?_⟩
      have h₁ := c.π.naturality ⟨WalkingParallelPairHom.left⟩
      have h₂ := c.π.naturality ⟨WalkingParallelPairHom.right⟩
      simp_all
  apply IsCofiltered.mk

中文:
定理 of_cone_nonempty
  结论: (h : 对任意 {J : 类型 w} [小范畴 J] [有限范畴 J] (F : J ⥤ C),
  证明: by
  have : Nonempty C := by
    obtain ⟨c⟩ := h (Functor.empty _)
    exact ⟨c.pt⟩
  have : IsCofilteredOrEmpty C := by
    refine ⟨?_, ?_⟩
    · intro X Y
      obtain ⟨c⟩ := h (ULiftHom.down ⋙ ULift.downFunctor ⋙ pair X Y)
      exact ⟨c.pt, c.π.app ⟨⟨WalkingPair.left⟩⟩, c.π.app ⟨⟨WalkingPair.right⟩⟩, trivial⟩
    · intro X Y f g
      obtain ⟨c⟩ := h (ULiftHom.down ⋙ ULift.downFunctor ⋙ parallelPair f g)
      refine ⟨c.pt, c.π.app ⟨WalkingParallelPair.zero⟩, ?_⟩
      have h₁ := c.π.naturality ⟨WalkingParallelPairHom.left⟩
      have h₂ := c.π.naturality ⟨WalkingParallelPairHom.right⟩
      simp_all
  apply IsCofiltered.mk

Depends on / 依赖: Functor, Functor.empty, IsCofilteredOrEmpty, Nonempty, ULift.downFunctor, ULiftHom, ULiftHom.down, WalkingPair, WalkingPair.left, WalkingPair.right, WalkingParallelPair, WalkingParallelPair.zero, WalkingParallelPairHom, WalkingParallelPairHom.left, c.pt, downFunctor, naturality, parallelPair
-/
theorem of_cone_nonempty (h : forall {J : Type w} [SmallCategory J] [FinCategory J] (F : J ⥤ C),
    Nonempty (Cone F)) : IsCofiltered C := by
  have : Nonempty C := by
    obtain ⟨c⟩ := h (Functor.empty _)
    exact ⟨c.pt⟩
  have : IsCofilteredOrEmpty C := by
    refine ⟨?_, ?_⟩
    · intro X Y
      obtain ⟨c⟩ := h (ULiftHom.down ⋙ ULift.downFunctor ⋙ pair X Y)
      exact ⟨c.pt, c.π.app ⟨⟨WalkingPair.left⟩⟩, c.π.app ⟨⟨WalkingPair.right⟩⟩, trivial⟩
    · intro X Y f g
      obtain ⟨c⟩ := h (ULiftHom.down ⋙ ULift.downFunctor ⋙ parallelPair f g)
      refine ⟨c.pt, c.π.app ⟨WalkingParallelPair.zero⟩, ?_⟩
      have h₁ := c.π.naturality ⟨WalkingParallelPairHom.left⟩
      have h₂ := c.π.naturality ⟨WalkingParallelPairHom.right⟩
      simp_all
  apply IsCofiltered.mk

/--
theorem `of_hasFiniteLimits` / 定理 `of_hasFiniteLimits`

English:
theorem of_hasFiniteLimits
  given: [HasFiniteLimits C]
  statement: IsCofiltered C
  proof: of_cone_nonempty.{v} C fun F => ⟨limit.cone F⟩

中文:
定理 of_hasFiniteLimits
  条件: [有有限极限 C]
  结论: 是余filtered C
  证明: of_cone_nonempty.{v} C fun F => ⟨limit.cone F⟩

Depends on / 依赖: limit.cone, of_cone_nonempty
-/
theorem of_hasFiniteLimits [HasFiniteLimits C] : IsCofiltered C :=
  of_cone_nonempty.{v} C fun F => ⟨limit.cone F⟩

/--
theorem `of_isInitial` / 定理 `of_isInitial`

English:
theorem of_isInitial
  given: {X : C} (h : IsInitial X)
  statement: IsCofiltered C
  proof: of_cone_nonempty.{v} _ fun {_} _ _ _ => ⟨⟨X, ⟨fun _ => h.to _, fun _ _ _ => h.hom_ext _ _⟩⟩⟩

中文:
定理 of_isInitial
  条件: {X : C} (h : IsInitial X)
  结论: 是余filtered C
  证明: of_cone_nonempty.{v} _ fun {_} _ _ _ => ⟨⟨X, ⟨fun _ => h.to _, fun _ _ _ => h.hom_ext _ _⟩⟩⟩

Depends on / 依赖: h.hom_ext, h.to, hom_ext, of_cone_nonempty
-/
theorem of_isInitial {X : C} (h : IsInitial X) : IsCofiltered C :=
  of_cone_nonempty.{v} _ fun {_} _ _ _ => ⟨⟨X, ⟨fun _ => h.to _, fun _ _ _ => h.hom_ext _ _⟩⟩⟩

instance (priority := 100) of_hasInitial [HasInitial C] : IsCofiltered C :=
  of_isInitial _ initialIsInitial

/--
theorem `iff_cone_nonempty` / 定理 `iff_cone_nonempty`

English:
theorem iff_cone_nonempty
  statement: IsCofiltered C ↔
  proof: ⟨fun _ _ _ _ F => cone_nonempty F, of_cone_nonempty C⟩

中文:
定理 iff_cone_nonempty
  结论: 是余filtered C ↔
  证明: ⟨fun _ _ _ _ F => cone_nonempty F, of_cone_nonempty C⟩

Depends on / 依赖: cone_nonempty, of_cone_nonempty
-/
theorem iff_cone_nonempty : IsCofiltered C ↔
    forall {J : Type w} [SmallCategory J] [FinCategory J] (F : J ⥤ C), Nonempty (Cone F) :=
  ⟨fun _ _ _ _ F => cone_nonempty F, of_cone_nonempty C⟩

end OfCone

end IsCofiltered

section Opposite

open Opposite

/--
Instance `isCofilteredOrEmpty_op_of_isFilteredOrEmpty` / 实例 `isCofilteredOrEmpty_op_of_isFilteredOrEmpty`

English:
instance isCofilteredOrEmpty_op_of_isFilteredOrEmpty
  signature: [IsFilteredOrEmpty C]
  body: ⟨op (IsFiltered.max X.unop Y.unop), (IsFiltered.leftToMax _ _).op,
      (IsFiltered.rightToMax _ _).op, trivial⟩
  cone_maps X Y f g :=
    ⟨op (IsFiltered.coeq f.unop g.unop), (IsFiltered.coeqHom _ _).op, by
      rw [show f = f.unop.op by simp]; rw [show g = g.unop.op by simp]; rw [← op_comp]; rw [← op_comp]
      congr 1
      exact IsFiltered.coeq_condition f.unop g.unop⟩

中文:
实例 isCofilteredOrEmpty_op_of_isFilteredOrEmpty
  签名: [是FilteredOrEmpty C]
  定义体: ⟨op (IsFiltered.max X.unop Y.unop), (IsFiltered.leftToMax _ _).op,
      (IsFiltered.rightToMax _ _).op, trivial⟩
  cone_maps X Y f g :=
    ⟨op (IsFiltered.coeq f.unop g.unop), (IsFiltered.coeqHom _ _).op, by
      rw [show f = f.unop.op by simp]; rw [show g = g.unop.op by simp]; rw [← op_comp]; rw [← op_comp]
      congr 1
      exact IsFiltered.coeq_condition f.unop g.unop⟩

Depends on / 依赖: IsFiltered, IsFiltered.coeq, IsFiltered.coeqHom, IsFiltered.coeq_condition, IsFiltered.leftToMax, IsFiltered.max, IsFiltered.rightToMax, X.unop, Y.unop, coeqHom, coeq_condition, cone_maps, f.unop, f.unop.op, g.unop, g.unop.op, leftToMax, op_comp, rightToMax
-/
instance isCofilteredOrEmpty_op_of_isFilteredOrEmpty [IsFilteredOrEmpty C] :
    IsCofilteredOrEmpty Cᵒᵖ where
  cone_objs X Y :=
    ⟨op (IsFiltered.max X.unop Y.unop), (IsFiltered.leftToMax _ _).op,
      (IsFiltered.rightToMax _ _).op, trivial⟩
  cone_maps X Y f g :=
    ⟨op (IsFiltered.coeq f.unop g.unop), (IsFiltered.coeqHom _ _).op, by
      rw [show f = f.unop.op by simp]; rw [show g = g.unop.op by simp]; rw [← op_comp]; rw [← op_comp]
      congr 1
      exact IsFiltered.coeq_condition f.unop g.unop⟩

/--
Instance `isCofiltered_op_of_isFiltered` / 实例 `isCofiltered_op_of_isFiltered`

English:
instance isCofiltered_op_of_isFiltered
  signature: [IsFiltered C]
  body: letI : Nonempty C := IsFiltered.nonempty; inferInstance

中文:
实例 isCofiltered_op_of_isFiltered
  签名: [是Filtered C]
  定义体: letI : Nonempty C := IsFiltered.nonempty; inferInstance

Depends on / 依赖: IsFiltered, IsFiltered.nonempty, Nonempty, nonempty
-/
instance isCofiltered_op_of_isFiltered [IsFiltered C] : IsCofiltered Cᵒᵖ where
  nonempty := letI : Nonempty C := IsFiltered.nonempty; inferInstance

/--
Instance `isFilteredOrEmpty_op_of_isCofilteredOrEmpty` / 实例 `isFilteredOrEmpty_op_of_isCofilteredOrEmpty`

English:
instance isFilteredOrEmpty_op_of_isCofilteredOrEmpty
  signature: [IsCofilteredOrEmpty C]
  body: ⟨op (IsCofiltered.min X.unop Y.unop), (IsCofiltered.minToLeft X.unop Y.unop).op,
      (IsCofiltered.minToRight X.unop Y.unop).op, trivial⟩
  cocone_maps X Y f g :=
    ⟨op (IsCofiltered.eq f.unop g.unop), (IsCofiltered.eqHom f.unop g.unop).op, by
      rw [show f = f.unop.op by simp]; rw [show g = g.unop.op by simp]; rw [← op_comp]; rw [← op_comp]
      congr 1
      exact IsCofiltered.eq_condition f.unop g.unop⟩

中文:
实例 isFilteredOrEmpty_op_of_isCofilteredOrEmpty
  签名: [是余filteredOrEmpty C]
  定义体: ⟨op (IsCofiltered.min X.unop Y.unop), (IsCofiltered.minToLeft X.unop Y.unop).op,
      (IsCofiltered.minToRight X.unop Y.unop).op, trivial⟩
  cocone_maps X Y f g :=
    ⟨op (IsCofiltered.eq f.unop g.unop), (IsCofiltered.eqHom f.unop g.unop).op, by
      rw [show f = f.unop.op by simp]; rw [show g = g.unop.op by simp]; rw [← op_comp]; rw [← op_comp]
      congr 1
      exact IsCofiltered.eq_condition f.unop g.unop⟩

Depends on / 依赖: IsCofiltered, IsCofiltered.eq, IsCofiltered.eqHom, IsCofiltered.eq_condition, IsCofiltered.min, IsCofiltered.minToLeft, IsCofiltered.minToRight, X.unop, Y.unop, cocone_maps, eq_condition, f.unop, f.unop.op, g.unop, g.unop.op, minToLeft, minToRight, op_comp
-/
instance isFilteredOrEmpty_op_of_isCofilteredOrEmpty [IsCofilteredOrEmpty C] :
    IsFilteredOrEmpty Cᵒᵖ where
  cocone_objs X Y :=
    ⟨op (IsCofiltered.min X.unop Y.unop), (IsCofiltered.minToLeft X.unop Y.unop).op,
      (IsCofiltered.minToRight X.unop Y.unop).op, trivial⟩
  cocone_maps X Y f g :=
    ⟨op (IsCofiltered.eq f.unop g.unop), (IsCofiltered.eqHom f.unop g.unop).op, by
      rw [show f = f.unop.op by simp]; rw [show g = g.unop.op by simp]; rw [← op_comp]; rw [← op_comp]
      congr 1
      exact IsCofiltered.eq_condition f.unop g.unop⟩

/--
Instance `isFiltered_op_of_isCofiltered` / 实例 `isFiltered_op_of_isCofiltered`

English:
instance isFiltered_op_of_isCofiltered
  signature: [IsCofiltered C]
  body: letI : Nonempty C := IsCofiltered.nonempty; inferInstance

中文:
实例 isFiltered_op_of_isCofiltered
  签名: [是余filtered C]
  定义体: letI : Nonempty C := IsCofiltered.nonempty; inferInstance

Depends on / 依赖: IsCofiltered, IsCofiltered.nonempty, Nonempty, nonempty
-/
instance isFiltered_op_of_isCofiltered [IsCofiltered C] : IsFiltered Cᵒᵖ where
  nonempty := letI : Nonempty C := IsCofiltered.nonempty; inferInstance

/--
lemma `isCofilteredOrEmpty_of_isFilteredOrEmpty_op` / 引理 `isCofilteredOrEmpty_of_isFilteredOrEmpty_op`

English:
lemma isCofilteredOrEmpty_of_isFilteredOrEmpty_op
  given: [IsFilteredOrEmpty Cᵒᵖ]
  statement: IsCofilteredOrEmpty C
  proof: IsCofilteredOrEmpty.of_equivalence (opOpEquivalence _)

中文:
引理 isCofilteredOrEmpty_of_isFilteredOrEmpty_op
  条件: [是FilteredOrEmpty Cᵒᵖ]
  结论: 是余filteredOrEmpty C
  证明: IsCofilteredOrEmpty.of_equivalence (opOpEquivalence _)

Depends on / 依赖: IsCofilteredOrEmpty, IsCofilteredOrEmpty.of_equivalence, of_equivalence, opOpEquivalence
-/
lemma isCofilteredOrEmpty_of_isFilteredOrEmpty_op [IsFilteredOrEmpty Cᵒᵖ] : IsCofilteredOrEmpty C :=
  IsCofilteredOrEmpty.of_equivalence (opOpEquivalence _)

/--
lemma `isFilteredOrEmpty_of_isCofilteredOrEmpty_op` / 引理 `isFilteredOrEmpty_of_isCofilteredOrEmpty_op`

English:
lemma isFilteredOrEmpty_of_isCofilteredOrEmpty_op
  given: [IsCofilteredOrEmpty Cᵒᵖ]
  statement: IsFilteredOrEmpty C
  proof: IsFilteredOrEmpty.of_equivalence (opOpEquivalence _)

中文:
引理 isFilteredOrEmpty_of_isCofilteredOrEmpty_op
  条件: [是余filteredOrEmpty Cᵒᵖ]
  结论: 是FilteredOrEmpty C
  证明: IsFilteredOrEmpty.of_equivalence (opOpEquivalence _)

Depends on / 依赖: IsFilteredOrEmpty, IsFilteredOrEmpty.of_equivalence, of_equivalence, opOpEquivalence
-/
lemma isFilteredOrEmpty_of_isCofilteredOrEmpty_op [IsCofilteredOrEmpty Cᵒᵖ] : IsFilteredOrEmpty C :=
  IsFilteredOrEmpty.of_equivalence (opOpEquivalence _)

/--
lemma `isCofiltered_of_isFiltered_op` / 引理 `isCofiltered_of_isFiltered_op`

English:
lemma isCofiltered_of_isFiltered_op
  given: [IsFiltered Cᵒᵖ]
  statement: IsCofiltered C
  proof: IsCofiltered.of_equivalence (opOpEquivalence _)

中文:
引理 isCofiltered_of_isFiltered_op
  条件: [是Filtered Cᵒᵖ]
  结论: 是余filtered C
  证明: IsCofiltered.of_equivalence (opOpEquivalence _)

Depends on / 依赖: IsCofiltered, IsCofiltered.of_equivalence, of_equivalence, opOpEquivalence
-/
lemma isCofiltered_of_isFiltered_op [IsFiltered Cᵒᵖ] : IsCofiltered C :=
  IsCofiltered.of_equivalence (opOpEquivalence _)

/--
lemma `isFiltered_of_isCofiltered_op` / 引理 `isFiltered_of_isCofiltered_op`

English:
lemma isFiltered_of_isCofiltered_op
  given: [IsCofiltered Cᵒᵖ]
  statement: IsFiltered C
  proof: IsFiltered.of_equivalence (opOpEquivalence _)

中文:
引理 isFiltered_of_isCofiltered_op
  条件: [是余filtered Cᵒᵖ]
  结论: 是Filtered C
  证明: IsFiltered.of_equivalence (opOpEquivalence _)

Depends on / 依赖: IsFiltered, IsFiltered.of_equivalence, of_equivalence, opOpEquivalence
-/
lemma isFiltered_of_isCofiltered_op [IsCofiltered Cᵒᵖ] : IsFiltered C :=
  IsFiltered.of_equivalence (opOpEquivalence _)

/--
lemma `isCofiltered_op_iff_isFiltered` / 引理 `isCofiltered_op_iff_isFiltered`

English:
lemma isCofiltered_op_iff_isFiltered
  statement: IsCofiltered Cᵒᵖ ↔ IsFiltered C
  proof: ⟨fun _ => isFiltered_of_isCofiltered_op _, fun _ => inferInstance⟩

中文:
引理 isCofiltered_op_iff_isFiltered
  结论: 是余filtered Cᵒᵖ ↔ 是Filtered C
  证明: ⟨fun _ => isFiltered_of_isCofiltered_op _, fun _ => inferInstance⟩

Depends on / 依赖: isFiltered_of_isCofiltered_op
-/
lemma isCofiltered_op_iff_isFiltered : IsCofiltered Cᵒᵖ ↔ IsFiltered C :=
  ⟨fun _ => isFiltered_of_isCofiltered_op _, fun _ => inferInstance⟩

/--
lemma `isFiltered_op_iff_isCofiltered` / 引理 `isFiltered_op_iff_isCofiltered`

English:
lemma isFiltered_op_iff_isCofiltered
  statement: IsFiltered Cᵒᵖ ↔ IsCofiltered C
  proof: ⟨fun _ => isCofiltered_of_isFiltered_op _, fun _ => inferInstance⟩

中文:
引理 isFiltered_op_iff_isCofiltered
  结论: 是Filtered Cᵒᵖ ↔ 是余filtered C
  证明: ⟨fun _ => isCofiltered_of_isFiltered_op _, fun _ => inferInstance⟩

Depends on / 依赖: isCofiltered_of_isFiltered_op
-/
lemma isFiltered_op_iff_isCofiltered : IsFiltered Cᵒᵖ ↔ IsCofiltered C :=
  ⟨fun _ => isCofiltered_of_isFiltered_op _, fun _ => inferInstance⟩

end Opposite

section ULift

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsFiltered
  signature: C] : IsFiltered (ULift.{u₂} C)
  body: IsFiltered.of_equivalence ULift.equivalence

中文:
实例 [是Filtered
  签名: C] : 是Filtered (类型层提升.{u₂} C)
  定义体: IsFiltered.of_equivalence ULift.equivalence

Depends on / 依赖: IsFiltered, IsFiltered.of_equivalence, ULift.equivalence, equivalence, of_equivalence
-/
instance [IsFiltered C] : IsFiltered (ULift.{u₂} C) :=
  IsFiltered.of_equivalence ULift.equivalence

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsCofiltered
  signature: C] : IsCofiltered (ULift.{u₂} C)
  body: IsCofiltered.of_equivalence ULift.equivalence

中文:
实例 [是余filtered
  签名: C] : 是余filtered (类型层提升.{u₂} C)
  定义体: IsCofiltered.of_equivalence ULift.equivalence

Depends on / 依赖: IsCofiltered, IsCofiltered.of_equivalence, ULift.equivalence, equivalence, of_equivalence
-/
instance [IsCofiltered C] : IsCofiltered (ULift.{u₂} C) :=
  IsCofiltered.of_equivalence ULift.equivalence

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsFiltered
  signature: C] : IsFiltered (ULiftHom C)
  body: IsFiltered.of_equivalence ULiftHom.equiv

中文:
实例 [是Filtered
  签名: C] : 是Filtered (ULiftHom C)
  定义体: IsFiltered.of_equivalence ULiftHom.equiv

Depends on / 依赖: IsFiltered, IsFiltered.of_equivalence, ULiftHom, ULiftHom.equiv, of_equivalence
-/
instance [IsFiltered C] : IsFiltered (ULiftHom C) :=
  IsFiltered.of_equivalence ULiftHom.equiv

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsCofiltered
  signature: C] : IsCofiltered (ULiftHom C)
  body: IsCofiltered.of_equivalence ULiftHom.equiv

中文:
实例 [是余filtered
  签名: C] : 是余filtered (ULiftHom C)
  定义体: IsCofiltered.of_equivalence ULiftHom.equiv

Depends on / 依赖: IsCofiltered, IsCofiltered.of_equivalence, ULiftHom, ULiftHom.equiv, of_equivalence
-/
instance [IsCofiltered C] : IsCofiltered (ULiftHom C) :=
  IsCofiltered.of_equivalence ULiftHom.equiv

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsFiltered
  signature: C] : IsFiltered (AsSmall C)
  body: IsFiltered.of_equivalence AsSmall.equiv

中文:
实例 [是Filtered
  签名: C] : 是Filtered (AsSmall C)
  定义体: IsFiltered.of_equivalence AsSmall.equiv

Depends on / 依赖: AsSmall, AsSmall.equiv, IsFiltered, IsFiltered.of_equivalence, of_equivalence
-/
instance [IsFiltered C] : IsFiltered (AsSmall C) :=
  IsFiltered.of_equivalence AsSmall.equiv

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsCofiltered
  signature: C] : IsCofiltered (AsSmall C)
  body: IsCofiltered.of_equivalence AsSmall.equiv

中文:
实例 [是余filtered
  签名: C] : 是余filtered (AsSmall C)
  定义体: IsCofiltered.of_equivalence AsSmall.equiv

Depends on / 依赖: AsSmall, AsSmall.equiv, IsCofiltered, IsCofiltered.of_equivalence, of_equivalence
-/
instance [IsCofiltered C] : IsCofiltered (AsSmall C) :=
  IsCofiltered.of_equivalence AsSmall.equiv

end ULift

section Pi

variable {α : Type w} {I : α -> Type u₁} [forall i, Category.{v₁} (I i)]

open IsFiltered in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, IsFilteredOrEmpty (I i)] : IsFilteredOrEmpty (forall i, I i) where
  body: ⟨fun s => max (k s) (l s), fun s => leftToMax (k s) (l s),
    fun s => rightToMax (k s) (l s), trivial⟩
  cocone_maps k l f g := ⟨fun s => coeq (f s) (g s), fun s => coeqHom (f s) (g s),
    funext fun s => by simp [coeq_condition (f s) (g s)]⟩

中文:
实例 [对任意
  签名: i, 是FilteredOrEmpty (I i)] : 是FilteredOrEmpty (对任意 i, I i) where
  定义体: ⟨fun s => max (k s) (l s), fun s => leftToMax (k s) (l s),
    fun s => rightToMax (k s) (l s), trivial⟩
  cocone_maps k l f g := ⟨fun s => coeq (f s) (g s), fun s => coeqHom (f s) (g s),
    funext fun s => by simp [coeq_condition (f s) (g s)]⟩

Depends on / 依赖: leftToMax
-/
instance [forall i, IsFilteredOrEmpty (I i)] : IsFilteredOrEmpty (forall i, I i) where
  cocone_objs k l := ⟨fun s => max (k s) (l s), fun s => leftToMax (k s) (l s),
    fun s => rightToMax (k s) (l s), trivial⟩
  cocone_maps k l f g := ⟨fun s => coeq (f s) (g s), fun s => coeqHom (f s) (g s),
    funext fun s => by simp [coeq_condition (f s) (g s)]⟩

attribute [local instance] IsFiltered.nonempty in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, IsFiltered (I i)] : IsFiltered (forall i, I i) where

中文:
实例 [对任意
  签名: i, 是Filtered (I i)] : 是Filtered (对任意 i, I i) where
-/
instance [forall i, IsFiltered (I i)] : IsFiltered (forall i, I i) where

open IsCofiltered in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, IsCofilteredOrEmpty (I i)] : IsCofilteredOrEmpty (forall i, I i) where
  body: ⟨fun s => min (k s) (l s), fun s => minToLeft (k s) (l s),
    fun s => minToRight (k s) (l s), trivial⟩
  cone_maps k l f g := ⟨fun s => eq (f s) (g s), fun s => eqHom (f s) (g s),
    funext fun s => by simp [eq_condition (f s) (g s)]⟩

中文:
实例 [对任意
  签名: i, 是余filteredOrEmpty (I i)] : 是余filteredOrEmpty (对任意 i, I i) where
  定义体: ⟨fun s => min (k s) (l s), fun s => minToLeft (k s) (l s),
    fun s => minToRight (k s) (l s), trivial⟩
  cone_maps k l f g := ⟨fun s => eq (f s) (g s), fun s => eqHom (f s) (g s),
    funext fun s => by simp [eq_condition (f s) (g s)]⟩

Depends on / 依赖: minToLeft
-/
instance [forall i, IsCofilteredOrEmpty (I i)] : IsCofilteredOrEmpty (forall i, I i) where
  cone_objs k l := ⟨fun s => min (k s) (l s), fun s => minToLeft (k s) (l s),
    fun s => minToRight (k s) (l s), trivial⟩
  cone_maps k l f g := ⟨fun s => eq (f s) (g s), fun s => eqHom (f s) (g s),
    funext fun s => by simp [eq_condition (f s) (g s)]⟩

attribute [local instance] IsCofiltered.nonempty in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, IsCofiltered (I i)] : IsCofiltered (forall i, I i) where

中文:
实例 [对任意
  签名: i, 是余filtered (I i)] : 是余filtered (对任意 i, I i) where
-/
instance [forall i, IsCofiltered (I i)] : IsCofiltered (forall i, I i) where

end Pi

section Prod

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

set_option backward.isDefEq.respectTransparency false in
open IsFiltered in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsFilteredOrEmpty
  signature: C] [IsFilteredOrEmpty D] : IsFilteredOrEmpty (C × D) where
  body: ⟨(max k.1 l.1, max k.2 l.2), (leftToMax k.1 l.1, leftToMax k.2 l.2),
    (rightToMax k.1 l.1, rightToMax k.2 l.2), trivial⟩
  cocone_maps k l f g := ⟨(coeq f.1 g.1, coeq f.2 g.2), (coeqHom f.1 g.1, coeqHom f.2 g.2),
    by simp [coeq_condition]⟩

中文:
实例 [是FilteredOrEmpty
  签名: C] [是FilteredOrEmpty D] : 是FilteredOrEmpty (C × D) where
  定义体: ⟨(max k.1 l.1, max k.2 l.2), (leftToMax k.1 l.1, leftToMax k.2 l.2),
    (rightToMax k.1 l.1, rightToMax k.2 l.2), trivial⟩
  cocone_maps k l f g := ⟨(coeq f.1 g.1, coeq f.2 g.2), (coeqHom f.1 g.1, coeqHom f.2 g.2),
    by simp [coeq_condition]⟩

Depends on / 依赖: leftToMax
-/
instance [IsFilteredOrEmpty C] [IsFilteredOrEmpty D] : IsFilteredOrEmpty (C × D) where
  cocone_objs k l := ⟨(max k.1 l.1, max k.2 l.2), (leftToMax k.1 l.1, leftToMax k.2 l.2),
    (rightToMax k.1 l.1, rightToMax k.2 l.2), trivial⟩
  cocone_maps k l f g := ⟨(coeq f.1 g.1, coeq f.2 g.2), (coeqHom f.1 g.1, coeqHom f.2 g.2),
    by simp [coeq_condition]⟩

attribute [local instance] IsFiltered.nonempty in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsFiltered
  signature: C] [IsFiltered D] : IsFiltered (C × D) where

中文:
实例 [是Filtered
  签名: C] [是Filtered D] : 是Filtered (C × D) where
-/
instance [IsFiltered C] [IsFiltered D] : IsFiltered (C × D) where

set_option backward.isDefEq.respectTransparency false in
open IsCofiltered in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsCofilteredOrEmpty
  signature: C] [IsCofilteredOrEmpty D] : IsCofilteredOrEmpty (C × D) where
  body: ⟨(min k.1 l.1, min k.2 l.2), (minToLeft k.1 l.1, minToLeft k.2 l.2),
    (minToRight k.1 l.1, minToRight k.2 l.2), trivial⟩
  cone_maps k l f g := ⟨(eq f.1 g.1, eq f.2 g.2), (eqHom f.1 g.1, eqHom f.2 g.2),
    by simp [eq_condition]⟩

中文:
实例 [是余filteredOrEmpty
  签名: C] [是余filteredOrEmpty D] : 是余filteredOrEmpty (C × D) where
  定义体: ⟨(min k.1 l.1, min k.2 l.2), (minToLeft k.1 l.1, minToLeft k.2 l.2),
    (minToRight k.1 l.1, minToRight k.2 l.2), trivial⟩
  cone_maps k l f g := ⟨(eq f.1 g.1, eq f.2 g.2), (eqHom f.1 g.1, eqHom f.2 g.2),
    by simp [eq_condition]⟩

Depends on / 依赖: minToLeft
-/
instance [IsCofilteredOrEmpty C] [IsCofilteredOrEmpty D] : IsCofilteredOrEmpty (C × D) where
  cone_objs k l := ⟨(min k.1 l.1, min k.2 l.2), (minToLeft k.1 l.1, minToLeft k.2 l.2),
    (minToRight k.1 l.1, minToRight k.2 l.2), trivial⟩
  cone_maps k l f g := ⟨(eq f.1 g.1, eq f.2 g.2), (eqHom f.1 g.1, eqHom f.2 g.2),
    by simp [eq_condition]⟩

attribute [local instance] IsCofiltered.nonempty in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsCofiltered
  signature: C] [IsCofiltered D] : IsCofiltered (C × D) where

中文:
实例 [是余filtered
  签名: C] [是余filtered D] : 是余filtered (C × D) where
-/
instance [IsCofiltered C] [IsCofiltered D] : IsCofiltered (C × D) where

end Prod

end CategoryTheory
