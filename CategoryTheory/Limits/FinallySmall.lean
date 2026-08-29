/-
Copyright (c) 2023 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.Logic.Small.Set
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small

/-!
# Finally small categories

A category given by `(J : Type u) [Category.{v} J]` is `w`-finally small if there exists a
`FinalModel J : Type w` equipped with `[SmallCategory (FinalModel J)]` and a final functor
`FinalModel J ⥤ J`.

This means that if a category `C` has colimits of size `w` and `J` is `w`-finally small, then
`C` has colimits of shape `J`. In this way, the notion of "finally small" can be seen as a
generalization of the notion of "essentially small" for indexing categories of colimits.

Dually, we have a notion of initially small category.

We show that a finally small category admits a small weakly terminal set, i.e., a small set `s` of
objects such that from every object there is a morphism to a member of `s`. We also show that the
converse holds if `J` is filtered.
-/

@[expose] public section

universe w w' v v₁ u u₁

open CategoryTheory Functor

namespace CategoryTheory

section FinallySmall

variable (J : Type u) [Category.{v} J]

/--
Definition of `FinallySmall` / `FinallySmall` 的定义

English:
class FinallySmall
  parameters: : Prop where
  axioms and operations (1):
    - final_smallCategory : exists (S : Type w) (_ : SmallCategory S) (F : S ⥤ J), Final F

中文:
类 FinallySmall
  参数: : 命题 where
  公理与运算 (1 个):
    - final_smallCategory : 存在 (S : Type w) (_ : SmallCategory S) (F : S ⥤ J), Final F
-/
class FinallySmall : Prop where
  /-- There is a final functor from a small category. -/
  final_smallCategory : exists (S : Type w) (_ : SmallCategory S) (F : S ⥤ J), Final F

/--
theorem `FinallySmall.mk'` / 定理 `FinallySmall.mk'`

English:
theorem FinallySmall.mk'
  statement: {J : Type u} [Category.{v} J] {S : Type w} [SmallCategory S]
  proof: ⟨S, _, F, inferInstance⟩

中文:
定理 FinallySmall.mk'
  结论: {J : 类型u} [Category.{v} J] {S : Type w} [SmallCategory S]
  证明: ⟨S, _, F, inferInstance⟩
-/
theorem FinallySmall.mk' {J : Type u} [Category.{v} J] {S : Type w} [SmallCategory S]
    (F : S ⥤ J) [Final F] : FinallySmall.{w} J :=
  ⟨S, _, F, inferInstance⟩

/--
Definition of `FinalModel` / `FinalModel` 的定义

English:
definition FinalModel
  signature: [FinallySmall.{w} J]
  body: Classical.choose (@FinallySmall.final_smallCategory J _ _)

中文:
定义 FinalModel
  签名: [FinallySmall.{w} J]
  定义体: Classical.choose (@FinallySmall.final_smallCategory J _ _)

Depends on / 依赖: Classical, Classical.choose, FinallySmall, FinallySmall.final_smallCategory, final_smallCategory
-/
def FinalModel [FinallySmall.{w} J] : Type w :=
  Classical.choose (@FinallySmall.final_smallCategory J _ _)

/--
Instance `smallCategoryFinalModel` / 实例 `smallCategoryFinalModel`

English:
instance smallCategoryFinalModel
  signature: [FinallySmall.{w} J]
  body: Classical.choose (Classical.choose_spec (@FinallySmall.final_smallCategory J _ _))

中文:
实例 smallCategoryFinalModel
  签名: [FinallySmall.{w} J]
  定义体: Classical.choose (Classical.choose_spec (@FinallySmall.final_smallCategory J _ _))

Depends on / 依赖: Classical, Classical.choose, Classical.choose_spec, FinallySmall, FinallySmall.final_smallCategory, choose_spec, final_smallCategory
-/
noncomputable instance smallCategoryFinalModel [FinallySmall.{w} J] :
    SmallCategory (FinalModel J) :=
  Classical.choose (Classical.choose_spec (@FinallySmall.final_smallCategory J _ _))

/--
Definition of `fromFinalModel` / `fromFinalModel` 的定义

English:
definition fromFinalModel
  signature: [FinallySmall.{w} J]
  body: Classical.choose (Classical.choose_spec (Classical.choose_spec
    (@FinallySmall.final_smallCategory J _ _)))

中文:
定义 fromFinalModel
  签名: [FinallySmall.{w} J]
  定义体: Classical.choose (Classical.choose_spec (Classical.choose_spec
    (@FinallySmall.final_smallCategory J _ _)))

Depends on / 依赖: Classical, Classical.choose, Classical.choose_spec, FinallySmall, FinallySmall.final_smallCategory, choose_spec, final_smallCategory
-/
noncomputable def fromFinalModel [FinallySmall.{w} J] : FinalModel J ⥤ J :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec
    (@FinallySmall.final_smallCategory J _ _)))

/--
Instance `final_fromFinalModel` / 实例 `final_fromFinalModel`

English:
instance final_fromFinalModel
  signature: [FinallySmall.{w} J]
  body: Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (@FinallySmall.final_smallCategory J _ _)))

中文:
实例 final_fromFinalModel
  签名: [FinallySmall.{w} J]
  定义体: Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (@FinallySmall.final_smallCategory J _ _)))

Depends on / 依赖: Classical, Classical.choose_spec, FinallySmall, FinallySmall.final_smallCategory, choose_spec, final_smallCategory
-/
instance final_fromFinalModel [FinallySmall.{w} J] : Final (fromFinalModel J) :=
  Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (@FinallySmall.final_smallCategory J _ _)))

/--
theorem `finallySmall_of_essentiallySmall` / 定理 `finallySmall_of_essentiallySmall`

English:
theorem finallySmall_of_essentiallySmall
  given: [EssentiallySmall.{w} J]
  statement: FinallySmall.{w} J
  proof: FinallySmall.mk' (equivSmallModel.{w} J).inverse

中文:
定理 finallySmall_of_essentiallySmall
  条件: [EssentiallySmall.{w} J]
  结论: FinallySmall.{w} J
  证明: FinallySmall.mk' (equivSmallModel.{w} J).inverse

Depends on / 依赖: FinallySmall, FinallySmall.mk, equivSmallModel, inverse
-/
theorem finallySmall_of_essentiallySmall [EssentiallySmall.{w} J] : FinallySmall.{w} J :=
  FinallySmall.mk' (equivSmallModel.{w} J).inverse

variable {J}
variable {K : Type u₁} [Category.{v₁} K]

/--
theorem `finallySmall_of_final_of_finallySmall` / 定理 `finallySmall_of_final_of_finallySmall`

English:
theorem finallySmall_of_final_of_finallySmall
  given: [FinallySmall.{w} K] (F : K ⥤ J) [Final F]
  proof: suffices Final ((fromFinalModel K) ⋙ F) from .mk' ((fromFinalModel K) ⋙ F)
  final_comp _ _

中文:
定理 finallySmall_of_final_of_finallySmall
  条件: [FinallySmall.{w} K] (F : K ⥤ J) [Final F]
  证明: suffices Final ((fromFinalModel K) ⋙ F) from .mk' ((fromFinalModel K) ⋙ F)
  final_comp _ _

Depends on / 依赖: final_comp, fromFinalModel
-/
theorem finallySmall_of_final_of_finallySmall [FinallySmall.{w} K] (F : K ⥤ J) [Final F] :
    FinallySmall.{w} J :=
  suffices Final ((fromFinalModel K) ⋙ F) from .mk' ((fromFinalModel K) ⋙ F)
  final_comp _ _

/--
theorem `finallySmall_of_final_of_essentiallySmall` / 定理 `finallySmall_of_final_of_essentiallySmall`

English:
theorem finallySmall_of_final_of_essentiallySmall
  given: [EssentiallySmall.{w} K] (F : K ⥤ J) [Final F]
  proof: have := finallySmall_of_essentiallySmall K
  finallySmall_of_final_of_finallySmall F

中文:
定理 finallySmall_of_final_of_essentiallySmall
  条件: [EssentiallySmall.{w} K] (F : K ⥤ J) [Final F]
  证明: have := finallySmall_of_essentiallySmall K
  finallySmall_of_final_of_finallySmall F

Depends on / 依赖: finallySmall_of_essentiallySmall, finallySmall_of_final_of_finallySmall
-/
theorem finallySmall_of_final_of_essentiallySmall [EssentiallySmall.{w} K] (F : K ⥤ J) [Final F] :
    FinallySmall.{w} J :=
  have := finallySmall_of_essentiallySmall K
  finallySmall_of_final_of_finallySmall F

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Limits.HasTerminal
  signature: J] : FinallySmall.{w} J
  body: have := Functor.final_const_terminal (C := PUnit.{w + 1}) (D := J)
  .mk' ((Functor.const PUnit.{w + 1}).obj (⊤_ J))

中文:
实例 [Limits.HasTerminal
  签名: J] : FinallySmall.{w} J
  定义体: have := Functor.final_const_terminal (C := PUnit.{w + 1}) (D := J)
  .mk' ((Functor.const PUnit.{w + 1}).obj (⊤_ J))

Depends on / 依赖: Functor, Functor.const, Functor.final_const_terminal, final_const_terminal
-/
instance [Limits.HasTerminal J] : FinallySmall.{w} J :=
  have := Functor.final_const_terminal (C := PUnit.{w + 1}) (D := J)
  .mk' ((Functor.const PUnit.{w + 1}).obj (⊤_ J))

instance {J' : Type*} [Category* J'] [FinallySmall.{w} J] [FinallySmall.{w'} J'] :
    FinallySmall.{max w w'} (J × J') :=
  finallySmall_of_final_of_essentiallySmall
    ((fromFinalModel.{w} J).prod (fromFinalModel.{w'} J'))

end FinallySmall

section InitiallySmall

variable (J : Type u) [Category.{v} J]

/--
Definition of `InitiallySmall` / `InitiallySmall` 的定义

English:
class InitiallySmall
  parameters: : Prop where
  axioms and operations (1):
    - initial_smallCategory : exists (S : Type w) (_ : SmallCategory S) (F : S ⥤ J), Initial F

中文:
类 InitiallySmall
  参数: : 命题 where
  公理与运算 (1 个):
    - initial_smallCategory : 存在 (S : Type w) (_ : SmallCategory S) (F : S ⥤ J), Initial F
-/
class InitiallySmall : Prop where
  /-- There is an initial functor from a small category. -/
  initial_smallCategory : exists (S : Type w) (_ : SmallCategory S) (F : S ⥤ J), Initial F

/--
theorem `InitiallySmall.mk'` / 定理 `InitiallySmall.mk'`

English:
theorem InitiallySmall.mk'
  statement: {J : Type u} [Category.{v} J] {S : Type w} [SmallCategory S]
  proof: ⟨S, _, F, inferInstance⟩

中文:
定理 InitiallySmall.mk'
  结论: {J : 类型u} [Category.{v} J] {S : Type w} [SmallCategory S]
  证明: ⟨S, _, F, inferInstance⟩
-/
theorem InitiallySmall.mk' {J : Type u} [Category.{v} J] {S : Type w} [SmallCategory S]
    (F : S ⥤ J) [Initial F] : InitiallySmall.{w} J :=
  ⟨S, _, F, inferInstance⟩

/--
Definition of `InitialModel` / `InitialModel` 的定义

English:
definition InitialModel
  signature: [InitiallySmall.{w} J]
  body: Classical.choose (@InitiallySmall.initial_smallCategory J _ _)

中文:
定义 InitialModel
  签名: [InitiallySmall.{w} J]
  定义体: Classical.choose (@InitiallySmall.initial_smallCategory J _ _)

Depends on / 依赖: Classical, Classical.choose, InitiallySmall, InitiallySmall.initial_smallCategory, initial_smallCategory
-/
def InitialModel [InitiallySmall.{w} J] : Type w :=
  Classical.choose (@InitiallySmall.initial_smallCategory J _ _)

/--
Instance `smallCategoryInitialModel` / 实例 `smallCategoryInitialModel`

English:
instance smallCategoryInitialModel
  signature: [InitiallySmall.{w} J]
  body: Classical.choose (Classical.choose_spec (@InitiallySmall.initial_smallCategory J _ _))

中文:
实例 smallCategoryInitialModel
  签名: [InitiallySmall.{w} J]
  定义体: Classical.choose (Classical.choose_spec (@InitiallySmall.initial_smallCategory J _ _))

Depends on / 依赖: Classical, Classical.choose, Classical.choose_spec, InitiallySmall, InitiallySmall.initial_smallCategory, choose_spec, initial_smallCategory
-/
noncomputable instance smallCategoryInitialModel [InitiallySmall.{w} J] :
    SmallCategory (InitialModel J) :=
  Classical.choose (Classical.choose_spec (@InitiallySmall.initial_smallCategory J _ _))

/--
Definition of `fromInitialModel` / `fromInitialModel` 的定义

English:
definition fromInitialModel
  signature: [InitiallySmall.{w} J]
  body: Classical.choose (Classical.choose_spec (Classical.choose_spec
    (@InitiallySmall.initial_smallCategory J _ _)))

中文:
定义 fromInitialModel
  签名: [InitiallySmall.{w} J]
  定义体: Classical.choose (Classical.choose_spec (Classical.choose_spec
    (@InitiallySmall.initial_smallCategory J _ _)))

Depends on / 依赖: Classical, Classical.choose, Classical.choose_spec, InitiallySmall, InitiallySmall.initial_smallCategory, choose_spec, initial_smallCategory
-/
noncomputable def fromInitialModel [InitiallySmall.{w} J] : InitialModel J ⥤ J :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec
    (@InitiallySmall.initial_smallCategory J _ _)))

/--
Instance `initial_fromInitialModel` / 实例 `initial_fromInitialModel`

English:
instance initial_fromInitialModel
  signature: [InitiallySmall.{w} J]
  body: Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (@InitiallySmall.initial_smallCategory J _ _)))

中文:
实例 initial_fromInitialModel
  签名: [InitiallySmall.{w} J]
  定义体: Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (@InitiallySmall.initial_smallCategory J _ _)))

Depends on / 依赖: Classical, Classical.choose_spec, InitiallySmall, InitiallySmall.initial_smallCategory, choose_spec, initial_smallCategory
-/
instance initial_fromInitialModel [InitiallySmall.{w} J] : Initial (fromInitialModel J) :=
  Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (@InitiallySmall.initial_smallCategory J _ _)))

/--
theorem `initiallySmall_of_essentiallySmall` / 定理 `initiallySmall_of_essentiallySmall`

English:
theorem initiallySmall_of_essentiallySmall
  given: [EssentiallySmall.{w} J]
  statement: InitiallySmall.{w} J
  proof: InitiallySmall.mk' (equivSmallModel.{w} J).inverse

中文:
定理 initiallySmall_of_essentiallySmall
  条件: [EssentiallySmall.{w} J]
  结论: InitiallySmall.{w} J
  证明: InitiallySmall.mk' (equivSmallModel.{w} J).inverse

Depends on / 依赖: InitiallySmall, InitiallySmall.mk, equivSmallModel, inverse
-/
theorem initiallySmall_of_essentiallySmall [EssentiallySmall.{w} J] : InitiallySmall.{w} J :=
  InitiallySmall.mk' (equivSmallModel.{w} J).inverse

variable {J}
variable {K : Type u₁} [Category.{v₁} K]

/--
theorem `initiallySmall_of_initial_of_initiallySmall` / 定理 `initiallySmall_of_initial_of_initiallySmall`

English:
theorem initiallySmall_of_initial_of_initiallySmall
  statement: [InitiallySmall.{w} K]
  proof: suffices Initial ((fromInitialModel K) ⋙ F) from .mk' ((fromInitialModel K) ⋙ F)
  initial_comp _ _

中文:
定理 initiallySmall_of_initial_of_initiallySmall
  结论: [InitiallySmall.{w} K]
  证明: suffices Initial ((fromInitialModel K) ⋙ F) from .mk' ((fromInitialModel K) ⋙ F)
  initial_comp _ _

Depends on / 依赖: Initial, fromInitialModel, initial_comp
-/
theorem initiallySmall_of_initial_of_initiallySmall [InitiallySmall.{w} K]
    (F : K ⥤ J) [Initial F] : InitiallySmall.{w} J :=
  suffices Initial ((fromInitialModel K) ⋙ F) from .mk' ((fromInitialModel K) ⋙ F)
  initial_comp _ _

/--
theorem `initiallySmall_of_initial_of_essentiallySmall` / 定理 `initiallySmall_of_initial_of_essentiallySmall`

English:
theorem initiallySmall_of_initial_of_essentiallySmall
  statement: [EssentiallySmall.{w} K]
  proof: have := initiallySmall_of_essentiallySmall K
  initiallySmall_of_initial_of_initiallySmall F

中文:
定理 initiallySmall_of_initial_of_essentiallySmall
  结论: [EssentiallySmall.{w} K]
  证明: have := initiallySmall_of_essentiallySmall K
  initiallySmall_of_initial_of_initiallySmall F

Depends on / 依赖: initiallySmall_of_essentiallySmall, initiallySmall_of_initial_of_initiallySmall
-/
theorem initiallySmall_of_initial_of_essentiallySmall [EssentiallySmall.{w} K]
    (F : K ⥤ J) [Initial F] : InitiallySmall.{w} J :=
  have := initiallySmall_of_essentiallySmall K
  initiallySmall_of_initial_of_initiallySmall F

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Limits.HasInitial
  signature: J] : InitiallySmall.{w} J
  body: have := Functor.initial_const_initial (C := PUnit.{w + 1}) (D := J)
  .mk' ((Functor.const PUnit.{w + 1}).obj (⊥_ J))

中文:
实例 [Limits.HasInitial
  签名: J] : InitiallySmall.{w} J
  定义体: have := Functor.initial_const_initial (C := PUnit.{w + 1}) (D := J)
  .mk' ((Functor.const PUnit.{w + 1}).obj (⊥_ J))

Depends on / 依赖: Functor, Functor.const, Functor.initial_const_initial, initial_const_initial
-/
instance [Limits.HasInitial J] : InitiallySmall.{w} J :=
  have := Functor.initial_const_initial (C := PUnit.{w + 1}) (D := J)
  .mk' ((Functor.const PUnit.{w + 1}).obj (⊥_ J))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LocallySmall.{w}
  signature: J] [InitiallySmall.{w} J] (X
  body: by
  have : InitiallySmall.{w} (CostructuredArrow (fromInitialModel.{w} J) X) :=
    initiallySmall_of_essentiallySmall _
  exact initiallySmall_of_initial_of_initiallySmall
    (CostructuredArrow.toOver (fromInitialModel.{w} J) X)

中文:
实例 [LocallySmall.{w}
  签名: J] [InitiallySmall.{w} J] (X
  定义体: by
  have : InitiallySmall.{w} (CostructuredArrow (fromInitialModel.{w} J) X) :=
    initiallySmall_of_essentiallySmall _
  exact initiallySmall_of_initial_of_initiallySmall
    (CostructuredArrow.toOver (fromInitialModel.{w} J) X)

Depends on / 依赖: CostructuredArrow, CostructuredArrow.toOver, InitiallySmall, fromInitialModel, initiallySmall_of_essentiallySmall, initiallySmall_of_initial_of_initiallySmall, toOver
-/
instance [LocallySmall.{w} J] [InitiallySmall.{w} J] (X : J) :
    InitiallySmall.{w} (Over X) := by
  have : InitiallySmall.{w} (CostructuredArrow (fromInitialModel.{w} J) X) :=
    initiallySmall_of_essentiallySmall _
  exact initiallySmall_of_initial_of_initiallySmall
    (CostructuredArrow.toOver (fromInitialModel.{w} J) X)

instance {J' : Type*} [Category* J'] [InitiallySmall.{w} J] [InitiallySmall.{w'} J'] :
    InitiallySmall.{max w w'} (J × J') :=
  initiallySmall_of_initial_of_essentiallySmall
    ((fromInitialModel.{w} J).prod (fromInitialModel.{w'} J'))

end InitiallySmall

instance {J : Type u} [Category.{v} J] [InitiallySmall.{w} J] : FinallySmall.{w} Jᵒᵖ where
  final_smallCategory := ⟨_, _, (fromInitialModel.{w} J).op, inferInstance⟩

instance {J : Type u} [Category.{v} J] [FinallySmall.{w} J] : InitiallySmall.{w} Jᵒᵖ where
  initial_smallCategory := ⟨_, _, (fromFinalModel.{w} J).op, inferInstance⟩

section WeaklyTerminal

variable (J : Type u) [Category.{v} J]

/--
theorem `FinallySmall.exists_small_weakly_terminal_set` / 定理 `FinallySmall.exists_small_weakly_terminal_set`

English:
theorem FinallySmall.exists_small_weakly_terminal_set
  given: [FinallySmall.{w} J]
  proof: by
  refine ⟨Set.range (fromFinalModel J).obj, inferInstance, fun i => ?_⟩
  obtain ⟨f⟩ : Nonempty (StructuredArrow i (fromFinalModel J)) := IsConnected.is_nonempty
  exact ⟨(fromFinalModel J).obj f.right, Set.mem_range_self _, ⟨f.hom⟩⟩

中文:
定理 FinallySmall.exists_small_weakly_terminal_set
  条件: [FinallySmall.{w} J]
  证明: by
  refine ⟨Set.range (fromFinalModel J).obj, inferInstance, fun i => ?_⟩
  obtain ⟨f⟩ : Nonempty (StructuredArrow i (fromFinalModel J)) := IsConnected.is_nonempty
  exact ⟨(fromFinalModel J).obj f.right, Set.mem_range_self _, ⟨f.hom⟩⟩

Depends on / 依赖: IsConnected, IsConnected.is_nonempty, Nonempty, Set.mem_range_self, Set.range, StructuredArrow, f.hom, f.right, fromFinalModel, is_nonempty, mem_range_self
-/
theorem FinallySmall.exists_small_weakly_terminal_set [FinallySmall.{w} J] :
    exists (s : Set J) (_ : Small.{w} s), forall i, exists j in s, Nonempty (i ⟶ j) := by
  refine ⟨Set.range (fromFinalModel J).obj, inferInstance, fun i => ?_⟩
  obtain ⟨f⟩ : Nonempty (StructuredArrow i (fromFinalModel J)) := IsConnected.is_nonempty
  exact ⟨(fromFinalModel J).obj f.right, Set.mem_range_self _, ⟨f.hom⟩⟩

variable {J} in
/--
theorem `finallySmall_of_small_weakly_terminal_set` / 定理 `finallySmall_of_small_weakly_terminal_set`

English:
theorem finallySmall_of_small_weakly_terminal_set
  statement: [IsFilteredOrEmpty J] (s : Set J) [Small.{v} s]
  proof: by
  suffices Functor.Final (ObjectProperty.ι (· in s)) from
    finallySmall_of_final_of_essentiallySmall (ObjectProperty.ι (· in s))
  refine Functor.final_of_exists_of_isFiltered_of_fullyFaithful _ (fun i => ?_)
  obtain ⟨j, hj₁, hj₂⟩ := hs i
  exact ⟨⟨j, hj₁⟩, hj₂⟩

中文:
定理 finallySmall_of_small_weakly_terminal_set
  结论: [IsFilteredOrEmpty J] (s : Set J) [Small.{v} s]
  证明: by
  suffices Functor.Final (ObjectProperty.ι (· in s)) from
    finallySmall_of_final_of_essentiallySmall (ObjectProperty.ι (· in s))
  refine Functor.final_of_exists_of_isFiltered_of_fullyFaithful _ (fun i => ?_)
  obtain ⟨j, hj₁, hj₂⟩ := hs i
  exact ⟨⟨j, hj₁⟩, hj₂⟩

Depends on / 依赖: Functor, Functor.Final, Functor.final_of_exists_of_isFiltered_of_fullyFaithful, ObjectProperty, final_of_exists_of_isFiltered_of_fullyFaithful, finallySmall_of_final_of_essentiallySmall
-/
theorem finallySmall_of_small_weakly_terminal_set [IsFilteredOrEmpty J] (s : Set J) [Small.{v} s]
    (hs : forall i, exists j in s, Nonempty (i ⟶ j)) : FinallySmall.{v} J := by
  suffices Functor.Final (ObjectProperty.ι (· in s)) from
    finallySmall_of_final_of_essentiallySmall (ObjectProperty.ι (· in s))
  refine Functor.final_of_exists_of_isFiltered_of_fullyFaithful _ (fun i => ?_)
  obtain ⟨j, hj₁, hj₂⟩ := hs i
  exact ⟨⟨j, hj₁⟩, hj₂⟩

/--
theorem `finallySmall_iff_exists_small_weakly_terminal_set` / 定理 `finallySmall_iff_exists_small_weakly_terminal_set`

English:
theorem finallySmall_iff_exists_small_weakly_terminal_set
  given: [IsFilteredOrEmpty J]
  proof: by
  refine ⟨fun _ => FinallySmall.exists_small_weakly_terminal_set _, fun h => ?_⟩
  rcases h with ⟨s, hs, hs'⟩
  exact finallySmall_of_small_weakly_terminal_set s hs'

中文:
定理 finallySmall_iff_exists_small_weakly_terminal_set
  条件: [IsFilteredOrEmpty J]
  证明: by
  refine ⟨fun _ => FinallySmall.exists_small_weakly_terminal_set _, fun h => ?_⟩
  rcases h with ⟨s, hs, hs'⟩
  exact finallySmall_of_small_weakly_terminal_set s hs'

Depends on / 依赖: FinallySmall, FinallySmall.exists_small_weakly_terminal_set, exists_small_weakly_terminal_set, finallySmall_of_small_weakly_terminal_set
-/
theorem finallySmall_iff_exists_small_weakly_terminal_set [IsFilteredOrEmpty J] :
    FinallySmall.{v} J ↔ exists (s : Set J) (_ : Small.{v} s), forall i, exists j in s, Nonempty (i ⟶ j) := by
  refine ⟨fun _ => FinallySmall.exists_small_weakly_terminal_set _, fun h => ?_⟩
  rcases h with ⟨s, hs, hs'⟩
  exact finallySmall_of_small_weakly_terminal_set s hs'

end WeaklyTerminal

section WeaklyInitial

variable (J : Type u) [Category.{v} J]

/--
theorem `InitiallySmall.exists_small_weakly_initial_set` / 定理 `InitiallySmall.exists_small_weakly_initial_set`

English:
theorem InitiallySmall.exists_small_weakly_initial_set
  given: [InitiallySmall.{w} J]
  proof: by
  refine ⟨Set.range (fromInitialModel J).obj, inferInstance, fun i => ?_⟩
  obtain ⟨f⟩ : Nonempty (CostructuredArrow (fromInitialModel J) i) := IsConnected.is_nonempty
  exact ⟨(fromInitialModel J).obj f.left, Set.mem_range_self _, ⟨f.hom⟩⟩

中文:
定理 InitiallySmall.exists_small_weakly_initial_set
  条件: [InitiallySmall.{w} J]
  证明: by
  refine ⟨Set.range (fromInitialModel J).obj, inferInstance, fun i => ?_⟩
  obtain ⟨f⟩ : Nonempty (CostructuredArrow (fromInitialModel J) i) := IsConnected.is_nonempty
  exact ⟨(fromInitialModel J).obj f.left, Set.mem_range_self _, ⟨f.hom⟩⟩

Depends on / 依赖: CostructuredArrow, IsConnected, IsConnected.is_nonempty, Nonempty, Set.mem_range_self, Set.range, f.hom, f.left, fromInitialModel, is_nonempty, mem_range_self
-/
theorem InitiallySmall.exists_small_weakly_initial_set [InitiallySmall.{w} J] :
    exists (s : Set J) (_ : Small.{w} s), forall i, exists j in s, Nonempty (j ⟶ i) := by
  refine ⟨Set.range (fromInitialModel J).obj, inferInstance, fun i => ?_⟩
  obtain ⟨f⟩ : Nonempty (CostructuredArrow (fromInitialModel J) i) := IsConnected.is_nonempty
  exact ⟨(fromInitialModel J).obj f.left, Set.mem_range_self _, ⟨f.hom⟩⟩

variable {J} in
/--
theorem `initiallySmall_of_small_weakly_initial_set` / 定理 `initiallySmall_of_small_weakly_initial_set`

English:
theorem initiallySmall_of_small_weakly_initial_set
  statement: [IsCofilteredOrEmpty J] (s : Set J) [Small.{v} s]
  proof: by
  suffices Functor.Initial (ObjectProperty.ι (· in s)) from
    initiallySmall_of_initial_of_essentiallySmall (ObjectProperty.ι (· in s))
  refine Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful _ (fun i => ?_)
  obtain ⟨j, hj₁, hj₂⟩ := hs i
  exact ⟨⟨j, hj₁⟩, hj₂⟩

中文:
定理 initiallySmall_of_small_weakly_initial_set
  结论: [IsCofilteredOrEmpty J] (s : Set J) [Small.{v} s]
  证明: by
  suffices Functor.Initial (ObjectProperty.ι (· in s)) from
    initiallySmall_of_initial_of_essentiallySmall (ObjectProperty.ι (· in s))
  refine Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful _ (fun i => ?_)
  obtain ⟨j, hj₁, hj₂⟩ := hs i
  exact ⟨⟨j, hj₁⟩, hj₂⟩

Depends on / 依赖: Functor, Functor.Initial, Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful, Initial, ObjectProperty, initial_of_exists_of_isCofiltered_of_fullyFaithful, initiallySmall_of_initial_of_essentiallySmall
-/
theorem initiallySmall_of_small_weakly_initial_set [IsCofilteredOrEmpty J] (s : Set J) [Small.{v} s]
    (hs : forall i, exists j in s, Nonempty (j ⟶ i)) : InitiallySmall.{v} J := by
  suffices Functor.Initial (ObjectProperty.ι (· in s)) from
    initiallySmall_of_initial_of_essentiallySmall (ObjectProperty.ι (· in s))
  refine Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful _ (fun i => ?_)
  obtain ⟨j, hj₁, hj₂⟩ := hs i
  exact ⟨⟨j, hj₁⟩, hj₂⟩

variable {J} in
/--
theorem `initiallySmall_of_essentiallySmall_weakly_initial_objectProperty` / 定理 `initiallySmall_of_essentiallySmall_weakly_initial_objectProperty`

English:
theorem initiallySmall_of_essentiallySmall_weakly_initial_objectProperty
  proof: by
  obtain ⟨Q, H, hQ⟩ := ObjectProperty.EssentiallySmall.exists_small_le'.{v} P
  have : Small.{v} (show Set _ from Q) := by assumption
  refine initiallySmall_of_small_weakly_initial_set Q (fun i => ?_)
  obtain ⟨j, hj, ⟨f⟩⟩ := hP i
  obtain ⟨k, hk, ⟨e⟩⟩ := hQ _ hj
  exact ⟨k, hk, ⟨e.inv ≫ f⟩⟩

中文:
定理 initiallySmall_of_essentiallySmall_weakly_initial_objectProperty
  证明: by
  obtain ⟨Q, H, hQ⟩ := ObjectProperty.EssentiallySmall.exists_small_le'.{v} P
  have : Small.{v} (show Set _ from Q) := by assumption
  refine initiallySmall_of_small_weakly_initial_set Q (fun i => ?_)
  obtain ⟨j, hj, ⟨f⟩⟩ := hP i
  obtain ⟨k, hk, ⟨e⟩⟩ := hQ _ hj
  exact ⟨k, hk, ⟨e.inv ≫ f⟩⟩

Depends on / 依赖: EssentiallySmall, ObjectProperty, ObjectProperty.EssentiallySmall.exists_small_le, e.inv, exists_small_le, initiallySmall_of_small_weakly_initial_set
-/
theorem initiallySmall_of_essentiallySmall_weakly_initial_objectProperty
    [IsCofilteredOrEmpty J] (P : ObjectProperty J) [ObjectProperty.EssentiallySmall.{v} P]
    (hP : forall i, exists j, P j ∧ Nonempty (j ⟶ i)) : InitiallySmall.{v} J := by
  obtain ⟨Q, H, hQ⟩ := ObjectProperty.EssentiallySmall.exists_small_le'.{v} P
  have : Small.{v} (show Set _ from Q) := by assumption
  refine initiallySmall_of_small_weakly_initial_set Q (fun i => ?_)
  obtain ⟨j, hj, ⟨f⟩⟩ := hP i
  obtain ⟨k, hk, ⟨e⟩⟩ := hQ _ hj
  exact ⟨k, hk, ⟨e.inv ≫ f⟩⟩

/--
theorem `initiallySmall_iff_exists_small_weakly_initial_set` / 定理 `initiallySmall_iff_exists_small_weakly_initial_set`

English:
theorem initiallySmall_iff_exists_small_weakly_initial_set
  given: [IsCofilteredOrEmpty J]
  proof: by
  refine ⟨fun _ => InitiallySmall.exists_small_weakly_initial_set _, fun h => ?_⟩
  rcases h with ⟨s, hs, hs'⟩
  exact initiallySmall_of_small_weakly_initial_set s hs'

中文:
定理 initiallySmall_iff_exists_small_weakly_initial_set
  条件: [IsCofilteredOrEmpty J]
  证明: by
  refine ⟨fun _ => InitiallySmall.exists_small_weakly_initial_set _, fun h => ?_⟩
  rcases h with ⟨s, hs, hs'⟩
  exact initiallySmall_of_small_weakly_initial_set s hs'

Depends on / 依赖: InitiallySmall, InitiallySmall.exists_small_weakly_initial_set, exists_small_weakly_initial_set, initiallySmall_of_small_weakly_initial_set
-/
theorem initiallySmall_iff_exists_small_weakly_initial_set [IsCofilteredOrEmpty J] :
    InitiallySmall.{v} J ↔ exists (s : Set J) (_ : Small.{v} s), forall i, exists j in s, Nonempty (j ⟶ i) := by
  refine ⟨fun _ => InitiallySmall.exists_small_weakly_initial_set _, fun h => ?_⟩
  rcases h with ⟨s, hs, hs'⟩
  exact initiallySmall_of_small_weakly_initial_set s hs'

end WeaklyInitial

namespace Limits

/--
theorem `hasColimitsOfShape_of_finallySmall` / 定理 `hasColimitsOfShape_of_finallySmall`

English:
theorem hasColimitsOfShape_of_finallySmall
  statement: (J : Type u) [Category.{v} J] [FinallySmall.{w} J]
  proof: Final.hasColimitsOfShape_of_final (fromFinalModel J)

中文:
定理 hasColimitsOfShape_of_finallySmall
  结论: (J : 类型u) [Category.{v} J] [FinallySmall.{w} J]
  证明: Final.hasColimitsOfShape_of_final (fromFinalModel J)

Depends on / 依赖: Final.hasColimitsOfShape_of_final, fromFinalModel, hasColimitsOfShape_of_final
-/
theorem hasColimitsOfShape_of_finallySmall (J : Type u) [Category.{v} J] [FinallySmall.{w} J]
    (C : Type u₁) [Category.{v₁} C] [HasColimitsOfSize.{w, w} C] : HasColimitsOfShape J C :=
  Final.hasColimitsOfShape_of_final (fromFinalModel J)

/--
theorem `hasLimitsOfShape_of_initiallySmall` / 定理 `hasLimitsOfShape_of_initiallySmall`

English:
theorem hasLimitsOfShape_of_initiallySmall
  statement: (J : Type u) [Category.{v} J] [InitiallySmall.{w} J]
  proof: Initial.hasLimitsOfShape_of_initial (fromInitialModel J)

中文:
定理 hasLimitsOfShape_of_initiallySmall
  结论: (J : 类型u) [Category.{v} J] [InitiallySmall.{w} J]
  证明: Initial.hasLimitsOfShape_of_initial (fromInitialModel J)

Depends on / 依赖: Initial, Initial.hasLimitsOfShape_of_initial, fromInitialModel, hasLimitsOfShape_of_initial
-/
theorem hasLimitsOfShape_of_initiallySmall (J : Type u) [Category.{v} J] [InitiallySmall.{w} J]
    (C : Type u₁) [Category.{v₁} C] [HasLimitsOfSize.{w, w} C] : HasLimitsOfShape J C :=
  Initial.hasLimitsOfShape_of_initial (fromInitialModel J)

end Limits

end CategoryTheory
