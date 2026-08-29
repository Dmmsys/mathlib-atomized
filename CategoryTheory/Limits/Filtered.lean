/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Types.Yoneda

/-!
# Filtered categories and limits

In this file, we show that `C` is filtered if and only if for every functor `F : J ⥤ C` from a
finite category there is some `X : C` such that `lim Hom(F·, X)` is nonempty.

Furthermore, we define the type classes `HasCofilteredLimitsOfSize` and `HasFilteredColimitsOfSize`.
-/

public section


universe w' w w₂' w₂ v u

noncomputable section

open CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace CategoryTheory

section NonemptyLimit

open CategoryTheory.Limits Opposite

/--
theorem `IsFiltered.iff_nonempty_limit` / 定理 `IsFiltered.iff_nonempty_limit`

English:
theorem IsFiltered.iff_nonempty_limit
  statement: IsFiltered C ↔
  proof: by
  rw [IsFiltered.iff_cocone_nonempty.{v}]
  refine ⟨fun h J _ _ F => ?_, fun h J _ _ F => ?_⟩
  · obtain ⟨c⟩ := h F
    exact ⟨c.pt, ⟨(limitCompYonedaIsoCocone F c.pt).inv c.ι⟩⟩
  · obtain ⟨pt, ⟨ι⟩⟩ := h F
    exact ⟨⟨pt, (limitCompYonedaIsoCocone F pt).hom ι⟩⟩

中文:
定理 是Filtered.iff_nonempty_limit
  结论: 是Filtered C ↔
  证明: by
  rw [IsFiltered.iff_cocone_nonempty.{v}]
  refine ⟨fun h J _ _ F => ?_, fun h J _ _ F => ?_⟩
  · obtain ⟨c⟩ := h F
    exact ⟨c.pt, ⟨(limitCompYonedaIsoCocone F c.pt).inv c.ι⟩⟩
  · obtain ⟨pt, ⟨ι⟩⟩ := h F
    exact ⟨⟨pt, (limitCompYonedaIsoCocone F pt).hom ι⟩⟩

Depends on / 依赖: IsFiltered, IsFiltered.iff_cocone_nonempty, c.pt, iff_cocone_nonempty, limitCompYonedaIsoCocone
-/
theorem IsFiltered.iff_nonempty_limit : IsFiltered C ↔
    forall {J : Type v} [SmallCategory J] [FinCategory J] (F : J ⥤ C),
      exists (X : C), Nonempty (limit (F.op ⋙ yoneda.obj X)) := by
  rw [IsFiltered.iff_cocone_nonempty.{v}]
  refine ⟨fun h J _ _ F => ?_, fun h J _ _ F => ?_⟩
  · obtain ⟨c⟩ := h F
    exact ⟨c.pt, ⟨(limitCompYonedaIsoCocone F c.pt).inv c.ι⟩⟩
  · obtain ⟨pt, ⟨ι⟩⟩ := h F
    exact ⟨⟨pt, (limitCompYonedaIsoCocone F pt).hom ι⟩⟩

/--
theorem `IsCofiltered.iff_nonempty_limit` / 定理 `IsCofiltered.iff_nonempty_limit`

English:
theorem IsCofiltered.iff_nonempty_limit
  statement: IsCofiltered C ↔
  proof: by
  rw [IsCofiltered.iff_cone_nonempty.{v}]
  refine ⟨fun h J _ _ F => ?_, fun h J _ _ F => ?_⟩
  · obtain ⟨c⟩ := h F
    exact ⟨c.pt, ⟨(limitCompCoyonedaIsoCone F c.pt).inv c.π⟩⟩
  · obtain ⟨pt, ⟨π⟩⟩ := h F
    exact ⟨⟨pt, (limitCompCoyonedaIsoCone F pt).hom π⟩⟩

中文:
定理 是余filtered.iff_nonempty_limit
  结论: 是余filtered C ↔
  证明: by
  rw [IsCofiltered.iff_cone_nonempty.{v}]
  refine ⟨fun h J _ _ F => ?_, fun h J _ _ F => ?_⟩
  · obtain ⟨c⟩ := h F
    exact ⟨c.pt, ⟨(limitCompCoyonedaIsoCone F c.pt).inv c.π⟩⟩
  · obtain ⟨pt, ⟨π⟩⟩ := h F
    exact ⟨⟨pt, (limitCompCoyonedaIsoCone F pt).hom π⟩⟩

Depends on / 依赖: IsCofiltered, IsCofiltered.iff_cone_nonempty, c.pt, iff_cone_nonempty, limitCompCoyonedaIsoCone
-/
theorem IsCofiltered.iff_nonempty_limit : IsCofiltered C ↔
    forall {J : Type v} [SmallCategory J] [FinCategory J] (F : J ⥤ C),
      exists (X : C), Nonempty (limit (F ⋙ coyoneda.obj (op X))) := by
  rw [IsCofiltered.iff_cone_nonempty.{v}]
  refine ⟨fun h J _ _ F => ?_, fun h J _ _ F => ?_⟩
  · obtain ⟨c⟩ := h F
    exact ⟨c.pt, ⟨(limitCompCoyonedaIsoCone F c.pt).inv c.π⟩⟩
  · obtain ⟨pt, ⟨π⟩⟩ := h F
    exact ⟨⟨pt, (limitCompCoyonedaIsoCone F pt).hom π⟩⟩

end NonemptyLimit

namespace Limits

section

variable (C)

/-- Class for having all cofiltered limits of a given size. -/
-- After https://github.com/leanprover/lean4/pull/12286 and
-- https://github.com/leanprover/lean4/pull/12423, the shape universes in
-- `HasCofilteredLimitsOfSize` and `HasFilteredColimitsOfSize` would default to universe
-- output parameters. See Note [universe output parameters and typeclass caching].
@[univ_out_params, pp_with_univ]
/--
Definition of `HasCofilteredLimitsOfSize` / `HasCofilteredLimitsOfSize` 的定义

English:
class HasCofilteredLimitsOfSize
  parameters: : Prop where
  axioms and operations (1):
    - HasLimitsOfShape : forall (I : Type w) [Category.{w'} I] [IsCofiltered I], HasLimitsOfShape I C

中文:
类 有余filteredLimitsOfSize
  参数: : 命题 where
  公理与运算 (1 个):
    - HasLimitsOfShape : 对任意 (I : 类型 w) [范畴.{w'} I] [是余filtered I], 有形状极限 I C
-/
class HasCofilteredLimitsOfSize : Prop where
  /-- For all filtered types of size `w`, we have limits -/
  HasLimitsOfShape : forall (I : Type w) [Category.{w'} I] [IsCofiltered I], HasLimitsOfShape I C

/-- Class for having all filtered colimits of a given size. -/
@[univ_out_params, pp_with_univ]
/--
Definition of `HasFilteredColimitsOfSize` / `HasFilteredColimitsOfSize` 的定义

English:
class HasFilteredColimitsOfSize
  parameters: : Prop where
  axioms and operations (1):
    - HasColimitsOfShape : forall (I : Type w) [Category.{w'} I] [IsFiltered I], HasColimitsOfShape I C

中文:
类 有FilteredColimitsOfSize
  参数: : 命题 where
  公理与运算 (1 个):
    - HasColimitsOfShape : 对任意 (I : 类型 w) [范畴.{w'} I] [是Filtered I], 有形状余极限 I C
-/
class HasFilteredColimitsOfSize : Prop where
  /-- For all filtered types of a size `w`, we have colimits -/
  HasColimitsOfShape : forall (I : Type w) [Category.{w'} I] [IsFiltered I], HasColimitsOfShape I C

/--
Definition of `HasCofilteredLimits` / `HasCofilteredLimits` 的定义

English:
abbreviation HasCofilteredLimits
  body: HasCofilteredLimitsOfSize.{v, v} C

中文:
缩写 HasCofilteredLimits
  定义体: HasCofilteredLimitsOfSize.{v, v} C

Depends on / 依赖: HasCofilteredLimitsOfSize
-/
abbrev HasCofilteredLimits := HasCofilteredLimitsOfSize.{v, v} C

/--
Definition of `HasFilteredColimits` / `HasFilteredColimits` 的定义

English:
abbreviation HasFilteredColimits
  body: HasFilteredColimitsOfSize.{v, v} C

中文:
缩写 HasFilteredColimits
  定义体: HasFilteredColimitsOfSize.{v, v} C

Depends on / 依赖: HasFilteredColimitsOfSize
-/
abbrev HasFilteredColimits := HasFilteredColimitsOfSize.{v, v} C

end

instance (priority := 100) hasFilteredColimitsOfSize_of_hasColimitsOfSize
    [HasColimitsOfSize.{w', w} C] : HasFilteredColimitsOfSize.{w', w} C where
  HasColimitsOfShape _ _ _ := inferInstance

instance (priority := 100) hasCofilteredLimitsOfSize_of_hasLimitsOfSize
    [HasLimitsOfSize.{w', w} C] : HasCofilteredLimitsOfSize.{w', w} C where
  HasLimitsOfShape _ _ _ := inferInstance

instance (priority := 100) hasLimitsOfShape_of_has_cofiltered_limits
    [HasCofilteredLimitsOfSize.{w', w} C] (I : Type w) [Category.{w'} I] [IsCofiltered I] :
    HasLimitsOfShape I C :=
  HasCofilteredLimitsOfSize.HasLimitsOfShape _

instance (priority := 100) hasColimitsOfShape_of_has_filtered_colimits
    [HasFilteredColimitsOfSize.{w', w} C] (I : Type w) [Category.{w'} I] [IsFiltered I] :
    HasColimitsOfShape I C :=
  HasFilteredColimitsOfSize.HasColimitsOfShape _

/--
lemma `hasCofilteredLimitsOfSize_of_univLE` / 引理 `hasCofilteredLimitsOfSize_of_univLE`

English:
lemma hasCofilteredLimitsOfSize_of_univLE
  statement: [UnivLE.{w, w₂}] [UnivLE.{w', w₂'}]
  proof: haveI := IsCofiltered.of_equivalence ((ShrinkHoms.equivalence.{w₂'} J).trans <|
      Shrink.equivalence.{w₂, w₂'} (ShrinkHoms.{w} J))
    hasLimitsOfShape_of_equivalence ((ShrinkHoms.equivalence.{w₂'} J).trans <|
      Shrink.equivalence.{w₂, w₂'} (ShrinkHoms.{w} J)).symm

中文:
引理 hasCofilteredLimitsOfSize_of_univLE
  结论: [UnivLE.{w, w₂}] [UnivLE.{w', w₂'}]
  证明: haveI := IsCofiltered.of_equivalence ((ShrinkHoms.equivalence.{w₂'} J).trans <|
      Shrink.equivalence.{w₂, w₂'} (ShrinkHoms.{w} J))
    hasLimitsOfShape_of_equivalence ((ShrinkHoms.equivalence.{w₂'} J).trans <|
      Shrink.equivalence.{w₂, w₂'} (ShrinkHoms.{w} J)).symm

Depends on / 依赖: IsCofiltered, IsCofiltered.of_equivalence, Shrink, Shrink.equivalence, ShrinkHoms, ShrinkHoms.equivalence, equivalence, hasLimitsOfShape_of_equivalence, of_equivalence
-/
lemma hasCofilteredLimitsOfSize_of_univLE [UnivLE.{w, w₂}] [UnivLE.{w', w₂'}]
    [HasCofilteredLimitsOfSize.{w₂', w₂} C] :
    HasCofilteredLimitsOfSize.{w', w} C where
  HasLimitsOfShape J :=
    haveI := IsCofiltered.of_equivalence ((ShrinkHoms.equivalence.{w₂'} J).trans <|
      Shrink.equivalence.{w₂, w₂'} (ShrinkHoms.{w} J))
    hasLimitsOfShape_of_equivalence ((ShrinkHoms.equivalence.{w₂'} J).trans <|
      Shrink.equivalence.{w₂, w₂'} (ShrinkHoms.{w} J)).symm

/--
lemma `hasCofilteredLimitsOfSize_shrink` / 引理 `hasCofilteredLimitsOfSize_shrink`

English:
lemma hasCofilteredLimitsOfSize_shrink
  given: [HasCofilteredLimitsOfSize.{max w' w₂', max w w₂} C]
  proof: hasCofilteredLimitsOfSize_of_univLE.{w', w, max w' w₂', max w w₂}

中文:
引理 hasCofilteredLimitsOfSize_shrink
  条件: [有余filteredLimitsOfSize.{最大值 w' w₂', 最大值 w w₂} C]
  证明: hasCofilteredLimitsOfSize_of_univLE.{w', w, max w' w₂', max w w₂}

Depends on / 依赖: hasCofilteredLimitsOfSize_of_univLE
-/
lemma hasCofilteredLimitsOfSize_shrink [HasCofilteredLimitsOfSize.{max w' w₂', max w w₂} C] :
    HasCofilteredLimitsOfSize.{w', w} C :=
  hasCofilteredLimitsOfSize_of_univLE.{w', w, max w' w₂', max w w₂}

/--
lemma `hasFilteredColimitsOfSize_of_univLE` / 引理 `hasFilteredColimitsOfSize_of_univLE`

English:
lemma hasFilteredColimitsOfSize_of_univLE
  statement: [UnivLE.{w, w₂}] [UnivLE.{w', w₂'}]
  proof: haveI := IsFiltered.of_equivalence ((ShrinkHoms.equivalence.{w₂'} J).trans <|
      Shrink.equivalence.{w₂, w₂'} (ShrinkHoms.{w} J))
    hasColimitsOfShape_of_equivalence ((ShrinkHoms.equivalence.{w₂'} J).trans <|
      Shrink.equivalence.{w₂, w₂'} (ShrinkHoms.{w} J)).symm

中文:
引理 hasFilteredColimitsOfSize_of_univLE
  结论: [UnivLE.{w, w₂}] [UnivLE.{w', w₂'}]
  证明: haveI := IsFiltered.of_equivalence ((ShrinkHoms.equivalence.{w₂'} J).trans <|
      Shrink.equivalence.{w₂, w₂'} (ShrinkHoms.{w} J))
    hasColimitsOfShape_of_equivalence ((ShrinkHoms.equivalence.{w₂'} J).trans <|
      Shrink.equivalence.{w₂, w₂'} (ShrinkHoms.{w} J)).symm

Depends on / 依赖: IsFiltered, IsFiltered.of_equivalence, Shrink, Shrink.equivalence, ShrinkHoms, ShrinkHoms.equivalence, equivalence, hasColimitsOfShape_of_equivalence, of_equivalence
-/
lemma hasFilteredColimitsOfSize_of_univLE [UnivLE.{w, w₂}] [UnivLE.{w', w₂'}]
    [HasFilteredColimitsOfSize.{w₂', w₂} C] :
    HasFilteredColimitsOfSize.{w', w} C where
  HasColimitsOfShape J :=
    haveI := IsFiltered.of_equivalence ((ShrinkHoms.equivalence.{w₂'} J).trans <|
      Shrink.equivalence.{w₂, w₂'} (ShrinkHoms.{w} J))
    hasColimitsOfShape_of_equivalence ((ShrinkHoms.equivalence.{w₂'} J).trans <|
      Shrink.equivalence.{w₂, w₂'} (ShrinkHoms.{w} J)).symm

/--
lemma `hasFilteredColimitsOfSize_shrink` / 引理 `hasFilteredColimitsOfSize_shrink`

English:
lemma hasFilteredColimitsOfSize_shrink
  given: [HasFilteredColimitsOfSize.{max w' w₂', max w w₂} C]
  proof: hasFilteredColimitsOfSize_of_univLE.{w', w, max w' w₂', max w w₂}

中文:
引理 hasFilteredColimitsOfSize_shrink
  条件: [有FilteredColimitsOfSize.{最大值 w' w₂', 最大值 w w₂} C]
  证明: hasFilteredColimitsOfSize_of_univLE.{w', w, max w' w₂', max w w₂}

Depends on / 依赖: hasFilteredColimitsOfSize_of_univLE
-/
lemma hasFilteredColimitsOfSize_shrink [HasFilteredColimitsOfSize.{max w' w₂', max w w₂} C] :
    HasFilteredColimitsOfSize.{w', w} C :=
  hasFilteredColimitsOfSize_of_univLE.{w', w, max w' w₂', max w w₂}

end Limits

end CategoryTheory
