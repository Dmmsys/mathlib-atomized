/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Limits.Filtered
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.CategoryTheory.Presentable.Basic

/-!
# Finitely Presentable Objects

We define finitely presentable objects as a synonym for `ℵ₀`-presentable objects,
and link this definition with the preservation of filtered colimits.

-/

@[expose] public section


universe w v' v u' u

namespace CategoryTheory

open Limits Opposite Cardinal

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

attribute [local instance] fact_isRegular_aleph0

/--
Definition of `Functor.IsFinitelyAccessible` / `Functor.IsFinitelyAccessible` 的定义

English:
abbreviation Functor.IsFinitelyAccessible
  signature: (F : C ⥤ D)
  body: IsCardinalAccessible.{w} F ℵ₀

中文:
缩写 函子.IsFinitelyAccessible
  签名: (F : C ⥤ D)
  定义体: IsCardinalAccessible.{w} F ℵ₀

Depends on / 依赖: IsCardinalAccessible
-/
abbrev Functor.IsFinitelyAccessible (F : C ⥤ D) : Prop := IsCardinalAccessible.{w} F ℵ₀

/--
lemma `Functor.IsFinitelyAccessible_iff_preservesFilteredColimitsOfSize` / 引理 `Functor.IsFinitelyAccessible_iff_preservesFilteredColimitsOfSize`

English:
lemma Functor.IsFinitelyAccessible_iff_preservesFilteredColimitsOfSize
  given: {F : C ⥤ D}
  proof: by
  refine ⟨fun ⟨H⟩ => ⟨?_⟩, fun ⟨H⟩ => ⟨?_⟩⟩ <;>
    simp only [isCardinalFiltered_aleph0_iff] at * <;>
    exact H

中文:
引理 函子.IsFinitelyAccessible_iff_preservesFilteredColimitsOfSize
  条件: {F : C ⥤ D}
  证明: by
  refine ⟨fun ⟨H⟩ => ⟨?_⟩, fun ⟨H⟩ => ⟨?_⟩⟩ <;>
    simp only [isCardinalFiltered_aleph0_iff] at * <;>
    exact H

Depends on / 依赖: isCardinalFiltered_aleph0_iff
-/
lemma Functor.IsFinitelyAccessible_iff_preservesFilteredColimitsOfSize {F : C ⥤ D} :
    IsFinitelyAccessible.{w} F ↔ PreservesFilteredColimitsOfSize.{w, w} F := by
  refine ⟨fun ⟨H⟩ => ⟨?_⟩, fun ⟨H⟩ => ⟨?_⟩⟩ <;>
    simp only [isCardinalFiltered_aleph0_iff] at * <;>
    exact H

/--
lemma `Functor.isFinitelyAccessible_iff_preservesFilteredColimits` / 引理 `Functor.isFinitelyAccessible_iff_preservesFilteredColimits`

English:
lemma Functor.isFinitelyAccessible_iff_preservesFilteredColimits
  given: {F : C ⥤ D}
  proof: IsFinitelyAccessible_iff_preservesFilteredColimitsOfSize

中文:
引理 函子.isFinitelyAccessible_iff_preservesFilteredColimits
  条件: {F : C ⥤ D}
  证明: IsFinitelyAccessible_iff_preservesFilteredColimitsOfSize

Depends on / 依赖: IsFinitelyAccessible_iff_preservesFilteredColimitsOfSize
-/
lemma Functor.isFinitelyAccessible_iff_preservesFilteredColimits {F : C ⥤ D} :
    IsFinitelyAccessible.{v'} F ↔ PreservesFilteredColimits F :=
  IsFinitelyAccessible_iff_preservesFilteredColimitsOfSize

/--
Definition of `IsFinitelyPresentable` / `IsFinitelyPresentable` 的定义

English:
abbreviation IsFinitelyPresentable
  signature: (X : C)
  body: IsCardinalPresentable.{w} X ℵ₀

中文:
缩写 IsFinitelyPresentable
  签名: (X : C)
  定义体: IsCardinalPresentable.{w} X ℵ₀

Depends on / 依赖: IsCardinalPresentable
-/
abbrev IsFinitelyPresentable (X : C) : Prop :=
  IsCardinalPresentable.{w} X ℵ₀

variable (C) in
/--
Definition of `ObjectProperty.isFinitelyPresentable` / `ObjectProperty.isFinitelyPresentable` 的定义

English:
definition ObjectProperty.isFinitelyPresentable
  signature: : ObjectProperty C
  body: fun X => IsFinitelyPresentable.{w} X

中文:
定义 ObjectProperty.isFinitelyPresentable
  签名: : ObjectProperty C
  定义体: fun X => IsFinitelyPresentable.{w} X

Depends on / 依赖: IsFinitelyPresentable
-/
def ObjectProperty.isFinitelyPresentable : ObjectProperty C := fun X => IsFinitelyPresentable.{w} X

/--
lemma `ObjectProperty.isFinitelyPresentable_eq_isCardinalPresentable` / 引理 `ObjectProperty.isFinitelyPresentable_eq_isCardinalPresentable`

English:
lemma ObjectProperty.isFinitelyPresentable_eq_isCardinalPresentable
  proof: rfl

中文:
引理 ObjectProperty.isFinitelyPresentable_eq_isCardinalPresentable
  证明: rfl
-/
lemma ObjectProperty.isFinitelyPresentable_eq_isCardinalPresentable :
    isFinitelyPresentable.{w} C = isCardinalPresentable.{w} C ℵ₀ :=
  rfl

variable (C) in
/--
Definition of `MorphismProperty.isFinitelyPresentable` / `MorphismProperty.isFinitelyPresentable` 的定义

English:
definition MorphismProperty.isFinitelyPresentable
  signature: : MorphismProperty C
  body: fun _ _ f => ObjectProperty.isFinitelyPresentable.{w} _ (CategoryTheory.Under.mk f)

中文:
定义 MorphismProperty.isFinitelyPresentable
  签名: : MorphismProperty C
  定义体: fun _ _ f => ObjectProperty.isFinitelyPresentable.{w} _ (CategoryTheory.Under.mk f)

Depends on / 依赖: CategoryTheory, CategoryTheory.Under.mk, ObjectProperty, ObjectProperty.isFinitelyPresentable, isFinitelyPresentable
-/
def MorphismProperty.isFinitelyPresentable : MorphismProperty C :=
  fun _ _ f => ObjectProperty.isFinitelyPresentable.{w} _ (CategoryTheory.Under.mk f)

/--
lemma `isFinitelyPresentable_iff_preservesFilteredColimitsOfSize` / 引理 `isFinitelyPresentable_iff_preservesFilteredColimitsOfSize`

English:
lemma isFinitelyPresentable_iff_preservesFilteredColimitsOfSize
  given: {X : C}
  proof: Functor.IsFinitelyAccessible_iff_preservesFilteredColimitsOfSize

中文:
引理 isFinitelyPresentable_iff_preservesFilteredColimitsOfSize
  条件: {X : C}
  证明: Functor.IsFinitelyAccessible_iff_preservesFilteredColimitsOfSize

Depends on / 依赖: Functor, Functor.IsFinitelyAccessible_iff_preservesFilteredColimitsOfSize, IsFinitelyAccessible_iff_preservesFilteredColimitsOfSize
-/
lemma isFinitelyPresentable_iff_preservesFilteredColimitsOfSize {X : C} :
    IsFinitelyPresentable.{w} X ↔ PreservesFilteredColimitsOfSize.{w, w} (coyoneda.obj (op X)) :=
  Functor.IsFinitelyAccessible_iff_preservesFilteredColimitsOfSize

/--
lemma `isFinitelyPresentable_iff_preservesFilteredColimits` / 引理 `isFinitelyPresentable_iff_preservesFilteredColimits`

English:
lemma isFinitelyPresentable_iff_preservesFilteredColimits
  given: {X : C}
  proof: Functor.IsFinitelyAccessible_iff_preservesFilteredColimitsOfSize

中文:
引理 isFinitelyPresentable_iff_preservesFilteredColimits
  条件: {X : C}
  证明: Functor.IsFinitelyAccessible_iff_preservesFilteredColimitsOfSize

Depends on / 依赖: Functor, Functor.IsFinitelyAccessible_iff_preservesFilteredColimitsOfSize, IsFinitelyAccessible_iff_preservesFilteredColimitsOfSize
-/
lemma isFinitelyPresentable_iff_preservesFilteredColimits {X : C} :
    IsFinitelyPresentable.{v} X ↔ PreservesFilteredColimits (coyoneda.obj (op X)) :=
  Functor.IsFinitelyAccessible_iff_preservesFilteredColimitsOfSize

instance (X : C) [IsFinitelyPresentable.{w} X] :
    PreservesFilteredColimitsOfSize.{w, w} (coyoneda.obj (op X)) := by
  rw [← isFinitelyPresentable_iff_preservesFilteredColimitsOfSize]
  infer_instance

instance (X : (ObjectProperty.isFinitelyPresentable.{w} C).FullSubcategory) :
    IsFinitelyPresentable.{w} ((ObjectProperty.isFinitelyPresentable.{w} C).ι.obj X) :=
  X.property

/--
lemma `IsFinitelyPresentable.exists_hom_of_isColimit` / 引理 `IsFinitelyPresentable.exists_hom_of_isColimit`

English:
lemma IsFinitelyPresentable.exists_hom_of_isColimit
  statement: {J : Type w} [SmallCategory J] [IsFiltered J]
  proof: Types.jointly_surjective_of_isColimit (isColimitOfPreserves (coyoneda.obj (op X)) hc) f

中文:
引理 IsFinitelyPresentable.存在_hom_of_isColimit
  结论: {J : 类型 w} [小范畴 J] [是Filtered J]
  证明: Types.jointly_surjective_of_isColimit (isColimitOfPreserves (coyoneda.obj (op X)) hc) f

Depends on / 依赖: Types.jointly_surjective_of_isColimit, coyoneda, coyoneda.obj, isColimitOfPreserves, jointly_surjective_of_isColimit
-/
lemma IsFinitelyPresentable.exists_hom_of_isColimit {J : Type w} [SmallCategory J] [IsFiltered J]
    {D : J ⥤ C} {c : Cocone D} (hc : IsColimit c) {X : C} [IsFinitelyPresentable.{w} X]
    (f : X ⟶ c.pt) :
    exists (j : J) (p : X ⟶ D.obj j), p ≫ c.ι.app j = f :=
  Types.jointly_surjective_of_isColimit (isColimitOfPreserves (coyoneda.obj (op X)) hc) f

/--
lemma `IsFinitelyPresentable.exists_eq_of_isColimit` / 引理 `IsFinitelyPresentable.exists_eq_of_isColimit`

English:
lemma IsFinitelyPresentable.exists_eq_of_isColimit
  statement: {J : Type w} [SmallCategory J] [IsFiltered J]
  proof: (Types.FilteredColimit.isColimit_eq_iff _ (isColimitOfPreserves (coyoneda.obj (op X)) hc)).mp h

中文:
引理 IsFinitelyPresentable.存在_eq_of_isColimit
  结论: {J : 类型 w} [小范畴 J] [是Filtered J]
  证明: (Types.FilteredColimit.isColimit_eq_iff _ (isColimitOfPreserves (coyoneda.obj (op X)) hc)).mp h

Depends on / 依赖: FilteredColimit, Types.FilteredColimit.isColimit_eq_iff, coyoneda, coyoneda.obj, isColimitOfPreserves, isColimit_eq_iff
-/
lemma IsFinitelyPresentable.exists_eq_of_isColimit {J : Type w} [SmallCategory J] [IsFiltered J]
    {D : J ⥤ C} {c : Cocone D} (hc : IsColimit c) {X : C} [IsFinitelyPresentable.{w} X]
    {i j : J} (f : X ⟶ D.obj i) (g : X ⟶ D.obj j) (h : f ≫ c.ι.app i = g ≫ c.ι.app j) :
    exists (k : J) (u : i ⟶ k) (v : j ⟶ k), f ≫ D.map u = g ≫ D.map v :=
  (Types.FilteredColimit.isColimit_eq_iff _ (isColimitOfPreserves (coyoneda.obj (op X)) hc)).mp h

/--
lemma `IsFinitelyPresentable.exists_hom_of_isColimit_under` / 引理 `IsFinitelyPresentable.exists_hom_of_isColimit_under`

English:
lemma IsFinitelyPresentable.exists_hom_of_isColimit_under
  proof: by
  have : Nonempty J := IsFiltered.nonempty
  let hc' := Under.isColimitLiftCocone D s c (p ≫ f) h hc
  obtain ⟨j, q, hq⟩ := exists_hom_of_isColimit (X := Under.mk p) hc' (Under.homMk f rfl)
  use j, q.right, Under.w q, congr($(hq).right)

中文:
引理 IsFinitelyPresentable.存在_hom_of_isColimit_under
  证明: by
  have : Nonempty J := IsFiltered.nonempty
  let hc' := Under.isColimitLiftCocone D s c (p ≫ f) h hc
  obtain ⟨j, q, hq⟩ := exists_hom_of_isColimit (X := Under.mk p) hc' (Under.homMk f rfl)
  use j, q.right, Under.w q, congr($(hq).right)

Depends on / 依赖: IsFiltered, IsFiltered.nonempty, Nonempty, Under.homMk, Under.isColimitLiftCocone, Under.mk, Under.w, exists_hom_of_isColimit, isColimitLiftCocone, nonempty, q.right
-/
lemma IsFinitelyPresentable.exists_hom_of_isColimit_under
    {J : Type w} [SmallCategory J] [IsFiltered J] {D : J ⥤ C} {c : Cocone D} (hc : IsColimit c)
    {X A : C} (p : X ⟶ A) (s : (Functor.const J).obj X ⟶ D)
    [IsFinitelyPresentable.{w} (Under.mk p)]
    (f : A ⟶ c.pt) (h : forall (j : J), s.app j ≫ c.ι.app j = p ≫ f) :
    exists (j : J) (q : A ⟶ D.obj j), p ≫ q = s.app j ∧ q ≫ c.ι.app j = f := by
  have : Nonempty J := IsFiltered.nonempty
  let hc' := Under.isColimitLiftCocone D s c (p ≫ f) h hc
  obtain ⟨j, q, hq⟩ := exists_hom_of_isColimit (X := Under.mk p) hc' (Under.homMk f rfl)
  use j, q.right, Under.w q, congr($(hq).right)

/--
lemma `HasCardinalFilteredColimits_iff_hasFilteredColimitsOfSize` / 引理 `HasCardinalFilteredColimits_iff_hasFilteredColimitsOfSize`

English:
lemma HasCardinalFilteredColimits_iff_hasFilteredColimitsOfSize
  proof: by
  refine ⟨fun ⟨H⟩ => ⟨?_⟩, fun ⟨H⟩ => ⟨?_⟩⟩ <;>
    simp only [isCardinalFiltered_aleph0_iff] at * <;>
    exact H

中文:
引理 HasCardinalFilteredColimits_iff_hasFilteredColimitsOfSize
  证明: by
  refine ⟨fun ⟨H⟩ => ⟨?_⟩, fun ⟨H⟩ => ⟨?_⟩⟩ <;>
    simp only [isCardinalFiltered_aleph0_iff] at * <;>
    exact H

Depends on / 依赖: isCardinalFiltered_aleph0_iff
-/
lemma HasCardinalFilteredColimits_iff_hasFilteredColimitsOfSize :
    HasCardinalFilteredColimits.{w} C ℵ₀ ↔ HasFilteredColimitsOfSize.{w, w} C := by
  refine ⟨fun ⟨H⟩ => ⟨?_⟩, fun ⟨H⟩ => ⟨?_⟩⟩ <;>
    simp only [isCardinalFiltered_aleph0_iff] at * <;>
    exact H

/--
lemma `HasCardinalFilteredColimits_iff_hasFilteredColimits` / 引理 `HasCardinalFilteredColimits_iff_hasFilteredColimits`

English:
lemma HasCardinalFilteredColimits_iff_hasFilteredColimits
  proof: HasCardinalFilteredColimits_iff_hasFilteredColimitsOfSize

中文:
引理 HasCardinalFilteredColimits_iff_hasFilteredColimits
  证明: HasCardinalFilteredColimits_iff_hasFilteredColimitsOfSize

Depends on / 依赖: HasCardinalFilteredColimits_iff_hasFilteredColimitsOfSize
-/
lemma HasCardinalFilteredColimits_iff_hasFilteredColimits :
    HasCardinalFilteredColimits.{v} C ℵ₀ ↔ HasFilteredColimits C :=
  HasCardinalFilteredColimits_iff_hasFilteredColimitsOfSize

end CategoryTheory
