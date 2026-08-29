/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Justus Springer
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Filtered.Basic

/-!
# Preservation of filtered colimits and cofiltered limits.

Typically forgetful functors from algebraic categories preserve filtered colimits
(although not general colimits). See e.g. `Mathlib/Algebra/Category/MonCat/FilteredColimits.lean`.

Note also that using the results in the file `Mathlib/CategoryTheory/Presentable/Directed.lean`,
in order to show that a functor preserves filtered colimits, it would be
sufficient to check that it preserves colimits indexed by nonempty directed
types.

-/

public section


open CategoryTheory

open CategoryTheory.Functor

namespace CategoryTheory.Limits

universe w' w₂' w w₂ v₁ v₂ v₃ u₁ u₂ u₃

-- declare the `v`'s first; see `CategoryTheory.Category` for an explanation
variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]

section FilteredColimits

section Preserves

-- This should be used with explicit universe variables.
/-- `PreservesFilteredColimitsOfSize.{w', w} F` means that `F` sends all colimit cocones over any
filtered diagram `J ⥤ C` to colimit cocones, where `J : Type w` with `[Category.{w'} J]`. -/
-- After https://github.com/leanprover/lean4/pull/12286 and
-- https://github.com/leanprover/lean4/pull/12423, the shape universes in
-- `PreservesFilteredColimitsOfSize`, `ReflectsFilteredColimitsOfSize`,
-- `PreservesCofilteredLimitsOfSize`, and `ReflectsCofilteredLimitsOfSize` would default to
-- universe output parameters. See Note [universe output parameters and typeclass caching].
@[univ_out_params, pp_with_univ]
/--
Definition of `PreservesFilteredColimitsOfSize` / `PreservesFilteredColimitsOfSize` 的定义

English:
class PreservesFilteredColimitsOfSize
  parameters: (F : C ⥤ D)
  axioms and operations (1):
    - preserves_filtered_colimits : forall (J : Type w) [Category.{w'} J] [IsFiltered J], PreservesColimitsOfShape J F

中文:
类 保持FilteredColimitsOfSize
  参数: (F : C ⥤ D)
  公理与运算 (1 个):
    - preserves_filtered_colimits : 对任意 (J : 类型 w) [范畴.{w'} J] [是Filtered J], 保持形状余极限 J F
-/
class PreservesFilteredColimitsOfSize (F : C ⥤ D) : Prop where
  preserves_filtered_colimits :
    forall (J : Type w) [Category.{w'} J] [IsFiltered J], PreservesColimitsOfShape J F

/--
Definition of `PreservesFilteredColimits` / `PreservesFilteredColimits` 的定义

English:
abbreviation PreservesFilteredColimits
  signature: (F : C ⥤ D)
  body: PreservesFilteredColimitsOfSize.{v₂, v₂} F

中文:
缩写 PreservesFilteredColimits
  签名: (F : C ⥤ D)
  定义体: PreservesFilteredColimitsOfSize.{v₂, v₂} F

Depends on / 依赖: PreservesFilteredColimitsOfSize
-/
abbrev PreservesFilteredColimits (F : C ⥤ D) : Prop :=
  PreservesFilteredColimitsOfSize.{v₂, v₂} F

attribute [instance 100] PreservesFilteredColimitsOfSize.preserves_filtered_colimits

instance (priority := 100) PreservesColimits.preservesFilteredColimits (F : C ⥤ D)
    [PreservesColimitsOfSize.{w, w'} F] : PreservesFilteredColimitsOfSize.{w, w'} F where
  preserves_filtered_colimits _ := inferInstance

/--
Instance `comp_preservesFilteredColimits` / 实例 `comp_preservesFilteredColimits`

English:
instance comp_preservesFilteredColimits
  signature: (F : C ⥤ D) (G : D ⥤ E)
  body: inferInstance

中文:
实例 comp_preservesFilteredColimits
  签名: (F : C ⥤ D) (G : D ⥤ E)
  定义体: inferInstance
-/
instance comp_preservesFilteredColimits (F : C ⥤ D) (G : D ⥤ E)
    [PreservesFilteredColimitsOfSize.{w, w'} F] [PreservesFilteredColimitsOfSize.{w, w'} G] :
      PreservesFilteredColimitsOfSize.{w, w'} (F ⋙ G) where
  preserves_filtered_colimits _ := inferInstance

/--
lemma `preservesFilteredColimitsOfSize_of_univLE` / 引理 `preservesFilteredColimitsOfSize_of_univLE`

English:
lemma preservesFilteredColimitsOfSize_of_univLE
  statement: (F : C ⥤ D) [UnivLE.{w, w'}]
  proof: by
    let e := ((ShrinkHoms.equivalence.{w'} J).trans <| Shrink.equivalence _).symm
    have := IsFiltered.of_equivalence e.symm
    exact preservesColimitsOfShape_of_equiv e F

中文:
引理 preservesFilteredColimitsOfSize_of_univLE
  结论: (F : C ⥤ D) [UnivLE.{w, w'}]
  证明: by
    let e := ((ShrinkHoms.equivalence.{w'} J).trans <| Shrink.equivalence _).symm
    have := IsFiltered.of_equivalence e.symm
    exact preservesColimitsOfShape_of_equiv e F

Depends on / 依赖: IsFiltered, IsFiltered.of_equivalence, Shrink, Shrink.equivalence, ShrinkHoms, ShrinkHoms.equivalence, e.symm, equivalence, of_equivalence, preservesColimitsOfShape_of_equiv
-/
lemma preservesFilteredColimitsOfSize_of_univLE (F : C ⥤ D) [UnivLE.{w, w'}]
    [UnivLE.{w₂, w₂'}] [PreservesFilteredColimitsOfSize.{w', w₂'} F] :
      PreservesFilteredColimitsOfSize.{w, w₂} F where
  preserves_filtered_colimits J _ _ := by
    let e := ((ShrinkHoms.equivalence.{w'} J).trans <| Shrink.equivalence _).symm
    have := IsFiltered.of_equivalence e.symm
    exact preservesColimitsOfShape_of_equiv e F

/--
lemma `preservesFilteredColimitsOfSize_shrink` / 引理 `preservesFilteredColimitsOfSize_shrink`

English:
lemma preservesFilteredColimitsOfSize_shrink
  statement: (F : C ⥤ D)
  proof: preservesFilteredColimitsOfSize_of_univLE.{max w w₂, max w' w₂'} F

中文:
引理 preservesFilteredColimitsOfSize_shrink
  结论: (F : C ⥤ D)
  证明: preservesFilteredColimitsOfSize_of_univLE.{max w w₂, max w' w₂'} F

Depends on / 依赖: preservesFilteredColimitsOfSize_of_univLE
-/
lemma preservesFilteredColimitsOfSize_shrink (F : C ⥤ D)
    [PreservesFilteredColimitsOfSize.{max w w₂, max w' w₂'} F] :
      PreservesFilteredColimitsOfSize.{w, w'} F :=
  preservesFilteredColimitsOfSize_of_univLE.{max w w₂, max w' w₂'} F

/--
lemma `preservesSmallestFilteredColimits_of_preservesFilteredColimits` / 引理 `preservesSmallestFilteredColimits_of_preservesFilteredColimits`

English:
lemma preservesSmallestFilteredColimits_of_preservesFilteredColimits
  statement: (F : C ⥤ D)
  proof: preservesFilteredColimitsOfSize_shrink F

中文:
引理 preservesSmallestFilteredColimits_of_preservesFilteredColimits
  结论: (F : C ⥤ D)
  证明: preservesFilteredColimitsOfSize_shrink F

Depends on / 依赖: preservesFilteredColimitsOfSize_shrink
-/
lemma preservesSmallestFilteredColimits_of_preservesFilteredColimits (F : C ⥤ D)
    [PreservesFilteredColimitsOfSize.{w', w} F] : PreservesFilteredColimitsOfSize.{0, 0} F :=
  preservesFilteredColimitsOfSize_shrink F

end Preserves

section Reflects

-- This should be used with explicit universe variables.
/-- `ReflectsFilteredColimitsOfSize.{w', w} F` means that whenever the image of a filtered cocone
under `F` is a colimit cocone, the original cocone was already a colimit. -/
@[univ_out_params, pp_with_univ]
/--
Definition of `ReflectsFilteredColimitsOfSize` / `ReflectsFilteredColimitsOfSize` 的定义

English:
class ReflectsFilteredColimitsOfSize
  parameters: (F : C ⥤ D)
  axioms and operations (1):
    - reflects_filtered_colimits : forall (J : Type w) [Category.{w'} J] [IsFiltered J], ReflectsColimitsOfShape J F

中文:
类 ReflectsFilteredColimitsOfSize
  参数: (F : C ⥤ D)
  公理与运算 (1 个):
    - reflects_filtered_colimits : 对任意 (J : 类型 w) [范畴.{w'} J] [是Filtered J], 反映形状余极限 J F
-/
class ReflectsFilteredColimitsOfSize (F : C ⥤ D) : Prop where
  reflects_filtered_colimits :
    forall (J : Type w) [Category.{w'} J] [IsFiltered J], ReflectsColimitsOfShape J F

/--
Definition of `ReflectsFilteredColimits` / `ReflectsFilteredColimits` 的定义

English:
abbreviation ReflectsFilteredColimits
  signature: (F : C ⥤ D)
  body: ReflectsFilteredColimitsOfSize.{v₂, v₂} F

中文:
缩写 ReflectsFilteredColimits
  签名: (F : C ⥤ D)
  定义体: ReflectsFilteredColimitsOfSize.{v₂, v₂} F

Depends on / 依赖: ReflectsFilteredColimitsOfSize
-/
abbrev ReflectsFilteredColimits (F : C ⥤ D) : Prop :=
  ReflectsFilteredColimitsOfSize.{v₂, v₂} F

attribute [instance 100] ReflectsFilteredColimitsOfSize.reflects_filtered_colimits

instance (priority := 100) ReflectsColimits.reflectsFilteredColimits (F : C ⥤ D)
    [ReflectsColimitsOfSize.{w, w'} F] : ReflectsFilteredColimitsOfSize.{w, w'} F where
  reflects_filtered_colimits _ := inferInstance

/--
Instance `comp_reflectsFilteredColimits` / 实例 `comp_reflectsFilteredColimits`

English:
instance comp_reflectsFilteredColimits
  signature: (F : C ⥤ D) (G : D ⥤ E)
  body: inferInstance

中文:
实例 comp_reflectsFilteredColimits
  签名: (F : C ⥤ D) (G : D ⥤ E)
  定义体: inferInstance
-/
instance comp_reflectsFilteredColimits (F : C ⥤ D) (G : D ⥤ E)
    [ReflectsFilteredColimitsOfSize.{w, w'} F] [ReflectsFilteredColimitsOfSize.{w, w'} G] :
      ReflectsFilteredColimitsOfSize.{w, w'} (F ⋙ G) where
  reflects_filtered_colimits _ := inferInstance

/--
lemma `reflectsFilteredColimitsOfSize_of_univLE` / 引理 `reflectsFilteredColimitsOfSize_of_univLE`

English:
lemma reflectsFilteredColimitsOfSize_of_univLE
  statement: (F : C ⥤ D) [UnivLE.{w, w'}]
  proof: by
    let e := ((ShrinkHoms.equivalence.{w'} J).trans <| Shrink.equivalence _).symm
    have := IsFiltered.of_equivalence e.symm
    exact reflectsColimitsOfShape_of_equiv e F

中文:
引理 reflectsFilteredColimitsOfSize_of_univLE
  结论: (F : C ⥤ D) [UnivLE.{w, w'}]
  证明: by
    let e := ((ShrinkHoms.equivalence.{w'} J).trans <| Shrink.equivalence _).symm
    have := IsFiltered.of_equivalence e.symm
    exact reflectsColimitsOfShape_of_equiv e F

Depends on / 依赖: IsFiltered, IsFiltered.of_equivalence, Shrink, Shrink.equivalence, ShrinkHoms, ShrinkHoms.equivalence, e.symm, equivalence, of_equivalence, reflectsColimitsOfShape_of_equiv
-/
lemma reflectsFilteredColimitsOfSize_of_univLE (F : C ⥤ D) [UnivLE.{w, w'}]
    [UnivLE.{w₂, w₂'}] [ReflectsFilteredColimitsOfSize.{w', w₂'} F] :
      ReflectsFilteredColimitsOfSize.{w, w₂} F where
  reflects_filtered_colimits J _ _ := by
    let e := ((ShrinkHoms.equivalence.{w'} J).trans <| Shrink.equivalence _).symm
    have := IsFiltered.of_equivalence e.symm
    exact reflectsColimitsOfShape_of_equiv e F

/--
lemma `reflectsFilteredColimitsOfSize_shrink` / 引理 `reflectsFilteredColimitsOfSize_shrink`

English:
lemma reflectsFilteredColimitsOfSize_shrink
  statement: (F : C ⥤ D)
  proof: reflectsFilteredColimitsOfSize_of_univLE.{max w w₂, max w' w₂'} F

中文:
引理 reflectsFilteredColimitsOfSize_shrink
  结论: (F : C ⥤ D)
  证明: reflectsFilteredColimitsOfSize_of_univLE.{max w w₂, max w' w₂'} F

Depends on / 依赖: reflectsFilteredColimitsOfSize_of_univLE
-/
lemma reflectsFilteredColimitsOfSize_shrink (F : C ⥤ D)
    [ReflectsFilteredColimitsOfSize.{max w w₂, max w' w₂'} F] :
      ReflectsFilteredColimitsOfSize.{w, w'} F :=
  reflectsFilteredColimitsOfSize_of_univLE.{max w w₂, max w' w₂'} F

/--
lemma `reflectsSmallestFilteredColimits_of_reflectsFilteredColimits` / 引理 `reflectsSmallestFilteredColimits_of_reflectsFilteredColimits`

English:
lemma reflectsSmallestFilteredColimits_of_reflectsFilteredColimits
  statement: (F : C ⥤ D)
  proof: reflectsFilteredColimitsOfSize_shrink F

中文:
引理 reflectsSmallestFilteredColimits_of_reflectsFilteredColimits
  结论: (F : C ⥤ D)
  证明: reflectsFilteredColimitsOfSize_shrink F

Depends on / 依赖: reflectsFilteredColimitsOfSize_shrink
-/
lemma reflectsSmallestFilteredColimits_of_reflectsFilteredColimits (F : C ⥤ D)
    [ReflectsFilteredColimitsOfSize.{w', w} F] : ReflectsFilteredColimitsOfSize.{0, 0} F :=
  reflectsFilteredColimitsOfSize_shrink F

end Reflects

end FilteredColimits

section CofilteredLimits

section Preserves

-- This should be used with explicit universe variables.
/-- `PreservesCofilteredLimitsOfSize.{w', w} F` means that `F` sends all limit cones over any
cofiltered diagram `J ⥤ C` to limit cones, where `J : Type w` with `[Category.{w'} J]`. -/
@[univ_out_params, pp_with_univ]
/--
Definition of `PreservesCofilteredLimitsOfSize` / `PreservesCofilteredLimitsOfSize` 的定义

English:
class PreservesCofilteredLimitsOfSize
  parameters: (F : C ⥤ D)
  axioms and operations (1):
    - preserves_cofiltered_limits : forall (J : Type w) [Category.{w'} J] [IsCofiltered J], PreservesLimitsOfShape J F

中文:
类 保持余filteredLimitsOfSize
  参数: (F : C ⥤ D)
  公理与运算 (1 个):
    - preserves_cofiltered_limits : 对任意 (J : 类型 w) [范畴.{w'} J] [是余filtered J], 保持形状极限 J F
-/
class PreservesCofilteredLimitsOfSize (F : C ⥤ D) : Prop where
  preserves_cofiltered_limits :
    forall (J : Type w) [Category.{w'} J] [IsCofiltered J], PreservesLimitsOfShape J F

/--
Definition of `PreservesCofilteredLimits` / `PreservesCofilteredLimits` 的定义

English:
abbreviation PreservesCofilteredLimits
  signature: (F : C ⥤ D)
  body: PreservesCofilteredLimitsOfSize.{v₂, v₂} F

中文:
缩写 PreservesCofilteredLimits
  签名: (F : C ⥤ D)
  定义体: PreservesCofilteredLimitsOfSize.{v₂, v₂} F

Depends on / 依赖: PreservesCofilteredLimitsOfSize
-/
abbrev PreservesCofilteredLimits (F : C ⥤ D) : Prop :=
  PreservesCofilteredLimitsOfSize.{v₂, v₂} F

attribute [instance 100] PreservesCofilteredLimitsOfSize.preserves_cofiltered_limits

instance (priority := 100) PreservesLimits.preservesCofilteredLimits (F : C ⥤ D)
    [PreservesLimitsOfSize.{w, w'} F] : PreservesCofilteredLimitsOfSize.{w, w'} F where
  preserves_cofiltered_limits _ := inferInstance

/--
Instance `comp_preservesCofilteredLimits` / 实例 `comp_preservesCofilteredLimits`

English:
instance comp_preservesCofilteredLimits
  signature: (F : C ⥤ D) (G : D ⥤ E)
  body: inferInstance

中文:
实例 comp_preservesCofilteredLimits
  签名: (F : C ⥤ D) (G : D ⥤ E)
  定义体: inferInstance
-/
instance comp_preservesCofilteredLimits (F : C ⥤ D) (G : D ⥤ E)
    [PreservesCofilteredLimitsOfSize.{w, w'} F] [PreservesCofilteredLimitsOfSize.{w, w'} G] :
      PreservesCofilteredLimitsOfSize.{w, w'} (F ⋙ G) where
  preserves_cofiltered_limits _ := inferInstance

/--
lemma `preservesCofilteredLimitsOfSize_of_univLE` / 引理 `preservesCofilteredLimitsOfSize_of_univLE`

English:
lemma preservesCofilteredLimitsOfSize_of_univLE
  statement: (F : C ⥤ D) [UnivLE.{w, w'}]
  proof: by
    let e := ((ShrinkHoms.equivalence.{w'} J).trans <| Shrink.equivalence _).symm
    have := IsCofiltered.of_equivalence e.symm
    exact preservesLimitsOfShape_of_equiv e F

中文:
引理 preservesCofilteredLimitsOfSize_of_univLE
  结论: (F : C ⥤ D) [UnivLE.{w, w'}]
  证明: by
    let e := ((ShrinkHoms.equivalence.{w'} J).trans <| Shrink.equivalence _).symm
    have := IsCofiltered.of_equivalence e.symm
    exact preservesLimitsOfShape_of_equiv e F

Depends on / 依赖: IsCofiltered, IsCofiltered.of_equivalence, Shrink, Shrink.equivalence, ShrinkHoms, ShrinkHoms.equivalence, e.symm, equivalence, of_equivalence, preservesLimitsOfShape_of_equiv
-/
lemma preservesCofilteredLimitsOfSize_of_univLE (F : C ⥤ D) [UnivLE.{w, w'}]
    [UnivLE.{w₂, w₂'}] [PreservesCofilteredLimitsOfSize.{w', w₂'} F] :
      PreservesCofilteredLimitsOfSize.{w, w₂} F where
  preserves_cofiltered_limits J _ _ := by
    let e := ((ShrinkHoms.equivalence.{w'} J).trans <| Shrink.equivalence _).symm
    have := IsCofiltered.of_equivalence e.symm
    exact preservesLimitsOfShape_of_equiv e F

/--
lemma `preservesCofilteredLimitsOfSize_shrink` / 引理 `preservesCofilteredLimitsOfSize_shrink`

English:
lemma preservesCofilteredLimitsOfSize_shrink
  statement: (F : C ⥤ D)
  proof: preservesCofilteredLimitsOfSize_of_univLE.{max w w₂, max w' w₂'} F

中文:
引理 preservesCofilteredLimitsOfSize_shrink
  结论: (F : C ⥤ D)
  证明: preservesCofilteredLimitsOfSize_of_univLE.{max w w₂, max w' w₂'} F

Depends on / 依赖: preservesCofilteredLimitsOfSize_of_univLE
-/
lemma preservesCofilteredLimitsOfSize_shrink (F : C ⥤ D)
    [PreservesCofilteredLimitsOfSize.{max w w₂, max w' w₂'} F] :
      PreservesCofilteredLimitsOfSize.{w, w'} F :=
  preservesCofilteredLimitsOfSize_of_univLE.{max w w₂, max w' w₂'} F

/--
lemma `preservesSmallestCofilteredLimits_of_preservesCofilteredLimits` / 引理 `preservesSmallestCofilteredLimits_of_preservesCofilteredLimits`

English:
lemma preservesSmallestCofilteredLimits_of_preservesCofilteredLimits
  statement: (F : C ⥤ D)
  proof: preservesCofilteredLimitsOfSize_shrink F

中文:
引理 preservesSmallestCofilteredLimits_of_preservesCofilteredLimits
  结论: (F : C ⥤ D)
  证明: preservesCofilteredLimitsOfSize_shrink F

Depends on / 依赖: preservesCofilteredLimitsOfSize_shrink
-/
lemma preservesSmallestCofilteredLimits_of_preservesCofilteredLimits (F : C ⥤ D)
    [PreservesCofilteredLimitsOfSize.{w', w} F] : PreservesCofilteredLimitsOfSize.{0, 0} F :=
  preservesCofilteredLimitsOfSize_shrink F

end Preserves

section Reflects

-- This should be used with explicit universe variables.
/-- `ReflectsCofilteredLimitsOfSize.{w', w} F` means that whenever the image of a cofiltered cone
under `F` is a limit cone, the original cone was already a limit. -/
@[univ_out_params, pp_with_univ]
/--
Definition of `ReflectsCofilteredLimitsOfSize` / `ReflectsCofilteredLimitsOfSize` 的定义

English:
class ReflectsCofilteredLimitsOfSize
  parameters: (F : C ⥤ D)
  axioms and operations (1):
    - reflects_cofiltered_limits : forall (J : Type w) [Category.{w'} J] [IsCofiltered J], ReflectsLimitsOfShape J F

中文:
类 ReflectsCofilteredLimitsOfSize
  参数: (F : C ⥤ D)
  公理与运算 (1 个):
    - reflects_cofiltered_limits : 对任意 (J : 类型 w) [范畴.{w'} J] [是余filtered J], 反映形状极限 J F
-/
class ReflectsCofilteredLimitsOfSize (F : C ⥤ D) : Prop where
  reflects_cofiltered_limits :
    forall (J : Type w) [Category.{w'} J] [IsCofiltered J], ReflectsLimitsOfShape J F

/--
Definition of `ReflectsCofilteredLimits` / `ReflectsCofilteredLimits` 的定义

English:
abbreviation ReflectsCofilteredLimits
  signature: (F : C ⥤ D)
  body: ReflectsCofilteredLimitsOfSize.{v₂, v₂} F

中文:
缩写 ReflectsCofilteredLimits
  签名: (F : C ⥤ D)
  定义体: ReflectsCofilteredLimitsOfSize.{v₂, v₂} F

Depends on / 依赖: ReflectsCofilteredLimitsOfSize
-/
abbrev ReflectsCofilteredLimits (F : C ⥤ D) : Prop :=
  ReflectsCofilteredLimitsOfSize.{v₂, v₂} F

attribute [instance 100] ReflectsCofilteredLimitsOfSize.reflects_cofiltered_limits

instance (priority := 100) ReflectsLimits.reflectsCofilteredLimits (F : C ⥤ D)
    [ReflectsLimitsOfSize.{w, w'} F] : ReflectsCofilteredLimitsOfSize.{w, w'} F where
  reflects_cofiltered_limits _ := inferInstance

/--
Instance `comp_reflectsCofilteredLimits` / 实例 `comp_reflectsCofilteredLimits`

English:
instance comp_reflectsCofilteredLimits
  signature: (F : C ⥤ D) (G : D ⥤ E)
  body: inferInstance

中文:
实例 comp_reflectsCofilteredLimits
  签名: (F : C ⥤ D) (G : D ⥤ E)
  定义体: inferInstance
-/
instance comp_reflectsCofilteredLimits (F : C ⥤ D) (G : D ⥤ E)
    [ReflectsCofilteredLimitsOfSize.{w, w'} F] [ReflectsCofilteredLimitsOfSize.{w, w'} G] :
      ReflectsCofilteredLimitsOfSize.{w, w'} (F ⋙ G) where
  reflects_cofiltered_limits _ := inferInstance

/--
lemma `reflectsCofilteredLimitsOfSize_of_univLE` / 引理 `reflectsCofilteredLimitsOfSize_of_univLE`

English:
lemma reflectsCofilteredLimitsOfSize_of_univLE
  statement: (F : C ⥤ D) [UnivLE.{w, w'}]
  proof: by
    let e := ((ShrinkHoms.equivalence.{w'} J).trans <| Shrink.equivalence _).symm
    have := IsCofiltered.of_equivalence e.symm
    exact reflectsLimitsOfShape_of_equiv e F

中文:
引理 reflectsCofilteredLimitsOfSize_of_univLE
  结论: (F : C ⥤ D) [UnivLE.{w, w'}]
  证明: by
    let e := ((ShrinkHoms.equivalence.{w'} J).trans <| Shrink.equivalence _).symm
    have := IsCofiltered.of_equivalence e.symm
    exact reflectsLimitsOfShape_of_equiv e F

Depends on / 依赖: IsCofiltered, IsCofiltered.of_equivalence, Shrink, Shrink.equivalence, ShrinkHoms, ShrinkHoms.equivalence, e.symm, equivalence, of_equivalence, reflectsLimitsOfShape_of_equiv
-/
lemma reflectsCofilteredLimitsOfSize_of_univLE (F : C ⥤ D) [UnivLE.{w, w'}]
    [UnivLE.{w₂, w₂'}] [ReflectsCofilteredLimitsOfSize.{w', w₂'} F] :
      ReflectsCofilteredLimitsOfSize.{w, w₂} F where
  reflects_cofiltered_limits J _ _ := by
    let e := ((ShrinkHoms.equivalence.{w'} J).trans <| Shrink.equivalence _).symm
    have := IsCofiltered.of_equivalence e.symm
    exact reflectsLimitsOfShape_of_equiv e F

/--
lemma `reflectsCofilteredLimitsOfSize_shrink` / 引理 `reflectsCofilteredLimitsOfSize_shrink`

English:
lemma reflectsCofilteredLimitsOfSize_shrink
  statement: (F : C ⥤ D)
  proof: reflectsCofilteredLimitsOfSize_of_univLE.{max w w₂, max w' w₂'} F

中文:
引理 reflectsCofilteredLimitsOfSize_shrink
  结论: (F : C ⥤ D)
  证明: reflectsCofilteredLimitsOfSize_of_univLE.{max w w₂, max w' w₂'} F

Depends on / 依赖: reflectsCofilteredLimitsOfSize_of_univLE
-/
lemma reflectsCofilteredLimitsOfSize_shrink (F : C ⥤ D)
    [ReflectsCofilteredLimitsOfSize.{max w w₂, max w' w₂'} F] :
      ReflectsCofilteredLimitsOfSize.{w, w'} F :=
  reflectsCofilteredLimitsOfSize_of_univLE.{max w w₂, max w' w₂'} F

/--
lemma `reflectsSmallestCofilteredLimits_of_reflectsCofilteredLimits` / 引理 `reflectsSmallestCofilteredLimits_of_reflectsCofilteredLimits`

English:
lemma reflectsSmallestCofilteredLimits_of_reflectsCofilteredLimits
  statement: (F : C ⥤ D)
  proof: reflectsCofilteredLimitsOfSize_shrink F

中文:
引理 reflectsSmallestCofilteredLimits_of_reflectsCofilteredLimits
  结论: (F : C ⥤ D)
  证明: reflectsCofilteredLimitsOfSize_shrink F

Depends on / 依赖: reflectsCofilteredLimitsOfSize_shrink
-/
lemma reflectsSmallestCofilteredLimits_of_reflectsCofilteredLimits (F : C ⥤ D)
    [ReflectsCofilteredLimitsOfSize.{w', w} F] : ReflectsCofilteredLimitsOfSize.{0, 0} F :=
  reflectsCofilteredLimitsOfSize_shrink F

end Reflects

end CofilteredLimits

end CategoryTheory.Limits
