/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.Transfer
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Action.Basic

/-!
# Categorical properties of `Action V G`

We show:

* When `V` has (co)limits so does `Action V G`.
* When `V` is preadditive, linear, or abelian so is `Action V G`.
* The forgetful functor `Action V G ⥤ V` preserves any (co)limit whose image in `V` exists,
  and reflects all (co)limits.
-/

@[expose] public section

universe u v w₁ w₂ t₁ t₂

open CategoryTheory Limits

variable {V : Type*} [Category* V] {G : Type*} [Monoid G]

namespace Action

section Limits

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasFiniteProducts
  signature: V] : HasFiniteProducts (Action V G) where
  body: Adjunction.hasLimitsOfShape_of_equivalence (Action.functorCategoryEquivalence _ _).functor

中文:
实例 [有FiniteProducts
  签名: V] : 有FiniteProducts (作用 V G) where
  定义体: Adjunction.hasLimitsOfShape_of_equivalence (Action.functorCategoryEquivalence _ _).functor

Depends on / 依赖: Action, Action.functorCategoryEquivalence, Adjunction, Adjunction.hasLimitsOfShape_of_equivalence, functor, functorCategoryEquivalence, hasLimitsOfShape_of_equivalence
-/
instance [HasFiniteProducts V] : HasFiniteProducts (Action V G) where
  out _ :=
    Adjunction.hasLimitsOfShape_of_equivalence (Action.functorCategoryEquivalence _ _).functor

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasFiniteLimits
  signature: V] : HasFiniteLimits (Action V G) where
  body: Adjunction.hasLimitsOfShape_of_equivalence (Action.functorCategoryEquivalence _ _).functor

中文:
实例 [有有限极限
  签名: V] : 有有限极限 (作用 V G) where
  定义体: Adjunction.hasLimitsOfShape_of_equivalence (Action.functorCategoryEquivalence _ _).functor

Depends on / 依赖: Action, Action.functorCategoryEquivalence, Adjunction, Adjunction.hasLimitsOfShape_of_equivalence, functor, functorCategoryEquivalence, hasLimitsOfShape_of_equivalence
-/
instance [HasFiniteLimits V] : HasFiniteLimits (Action V G) where
  out _ _ _ :=
    Adjunction.hasLimitsOfShape_of_equivalence (Action.functorCategoryEquivalence _ _).functor

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasLimits
  signature: V] : HasLimits (Action V G)
  body: Adjunction.has_limits_of_equivalence (Action.functorCategoryEquivalence _ _).functor

中文:
实例 [有极限
  签名: V] : 有极限 (作用 V G)
  定义体: Adjunction.has_limits_of_equivalence (Action.functorCategoryEquivalence _ _).functor

Depends on / 依赖: Action, Action.functorCategoryEquivalence, Adjunction, Adjunction.has_limits_of_equivalence, functor, functorCategoryEquivalence, has_limits_of_equivalence
-/
instance [HasLimits V] : HasLimits (Action V G) :=
  Adjunction.has_limits_of_equivalence (Action.functorCategoryEquivalence _ _).functor

/--
Instance `hasLimitsOfShape` / 实例 `hasLimitsOfShape`

English:
instance hasLimitsOfShape
  signature: {J : Type*} [Category* J] [HasLimitsOfShape J V]
  body: Adjunction.hasLimitsOfShape_of_equivalence (Action.functorCategoryEquivalence _ _).functor

中文:
实例 hasLimitsOfShape
  签名: {J : 类型} [范畴* J] [有形状极限 J V]
  定义体: Adjunction.hasLimitsOfShape_of_equivalence (Action.functorCategoryEquivalence _ _).functor

Depends on / 依赖: Action, Action.functorCategoryEquivalence, Adjunction, Adjunction.hasLimitsOfShape_of_equivalence, functor, functorCategoryEquivalence, hasLimitsOfShape_of_equivalence
-/
instance hasLimitsOfShape {J : Type*} [Category* J] [HasLimitsOfShape J V] :
    HasLimitsOfShape J (Action V G) :=
  Adjunction.hasLimitsOfShape_of_equivalence (Action.functorCategoryEquivalence _ _).functor

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasFiniteCoproducts
  signature: V] : HasFiniteCoproducts (Action V G) where
  body: Adjunction.hasColimitsOfShape_of_equivalence (Action.functorCategoryEquivalence _ _).functor

中文:
实例 [有FiniteCoproducts
  签名: V] : 有FiniteCoproducts (作用 V G) where
  定义体: Adjunction.hasColimitsOfShape_of_equivalence (Action.functorCategoryEquivalence _ _).functor

Depends on / 依赖: Action, Action.functorCategoryEquivalence, Adjunction, Adjunction.hasColimitsOfShape_of_equivalence, functor, functorCategoryEquivalence, hasColimitsOfShape_of_equivalence
-/
instance [HasFiniteCoproducts V] : HasFiniteCoproducts (Action V G) where
  out _ :=
    Adjunction.hasColimitsOfShape_of_equivalence (Action.functorCategoryEquivalence _ _).functor

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasFiniteColimits
  signature: V] : HasFiniteColimits (Action V G) where
  body: Adjunction.hasColimitsOfShape_of_equivalence (Action.functorCategoryEquivalence _ _).functor

中文:
实例 [有有限余极限
  签名: V] : 有有限余极限 (作用 V G) where
  定义体: Adjunction.hasColimitsOfShape_of_equivalence (Action.functorCategoryEquivalence _ _).functor

Depends on / 依赖: Action, Action.functorCategoryEquivalence, Adjunction, Adjunction.hasColimitsOfShape_of_equivalence, functor, functorCategoryEquivalence, hasColimitsOfShape_of_equivalence
-/
instance [HasFiniteColimits V] : HasFiniteColimits (Action V G) where
  out _ _ _ :=
    Adjunction.hasColimitsOfShape_of_equivalence (Action.functorCategoryEquivalence _ _).functor

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasColimits
  signature: V] : HasColimits (Action V G)
  body: Adjunction.has_colimits_of_equivalence (Action.functorCategoryEquivalence _ _).functor

中文:
实例 [有余极限
  签名: V] : 有余极限 (作用 V G)
  定义体: Adjunction.has_colimits_of_equivalence (Action.functorCategoryEquivalence _ _).functor

Depends on / 依赖: Action, Action.functorCategoryEquivalence, Adjunction, Adjunction.has_colimits_of_equivalence, functor, functorCategoryEquivalence, has_colimits_of_equivalence
-/
instance [HasColimits V] : HasColimits (Action V G) :=
  Adjunction.has_colimits_of_equivalence (Action.functorCategoryEquivalence _ _).functor

/--
Instance `hasColimitsOfShape` / 实例 `hasColimitsOfShape`

English:
instance hasColimitsOfShape
  signature: {J : Type*} [Category* J]
  body: Adjunction.hasColimitsOfShape_of_equivalence (Action.functorCategoryEquivalence _ _).functor

中文:
实例 hasColimitsOfShape
  签名: {J : 类型} [范畴* J]
  定义体: Adjunction.hasColimitsOfShape_of_equivalence (Action.functorCategoryEquivalence _ _).functor

Depends on / 依赖: Action, Action.functorCategoryEquivalence, Adjunction, Adjunction.hasColimitsOfShape_of_equivalence, functor, functorCategoryEquivalence, hasColimitsOfShape_of_equivalence
-/
instance hasColimitsOfShape {J : Type*} [Category* J]
    [HasColimitsOfShape J V] : HasColimitsOfShape J (Action V G) :=
  Adjunction.hasColimitsOfShape_of_equivalence (Action.functorCategoryEquivalence _ _).functor

end Limits

section Preservation

variable {C : Type*} [Category* C]

/--
lemma `SingleObj.preservesLimit` / 引理 `SingleObj.preservesLimit`

English:
lemma SingleObj.preservesLimit
  statement: (F : C ⥤ SingleObj G ⥤ V)
  proof: by
  apply preservesLimit_of_evaluation
  intro _
  exact h

中文:
引理 SingleObj.preservesLimit
  结论: (F : C ⥤ SingleObj G ⥤ V)
  证明: by
  apply preservesLimit_of_evaluation
  intro _
  exact h
-/
private lemma SingleObj.preservesLimit (F : C ⥤ SingleObj G ⥤ V)
    {J : Type*} [Category* J] (K : J ⥤ C)
    (h : PreservesLimit K (F ⋙ (evaluation (SingleObj G) V).obj (SingleObj.star G))) :
    PreservesLimit K F := by
  apply preservesLimit_of_evaluation
  intro _
  exact h

/--
lemma `preservesLimit_of_preserves` / 引理 `preservesLimit_of_preserves`

English:
lemma preservesLimit_of_preserves
  statement: (F : C ⥤ Action V G) {J : Type*}
  proof: by
  let F' : C ⥤ SingleObj G ⥤ V := F ⋙ (Action.functorCategoryEquivalence V G).functor
  have : PreservesLimit K F' := SingleObj.preservesLimit _ _ h
  apply preservesLimit_of_reflects_of_preserves F (Action.functorCategoryEquivalence V G).functor

中文:
引理 preservesLimit_of_preserves
  结论: (F : C ⥤ 作用 V G) {J : 类型}
  证明: by
  let F' : C ⥤ SingleObj G ⥤ V := F ⋙ (Action.functorCategoryEquivalence V G).functor
  have : PreservesLimit K F' := SingleObj.preservesLimit _ _ h
  apply preservesLimit_of_reflects_of_preserves F (Action.functorCategoryEquivalence V G).functor

Depends on / 依赖: Action, Action.functorCategoryEquivalence, PreservesLimit, SingleObj, SingleObj.preservesLimit, functor, functorCategoryEquivalence, preservesLimit, preservesLimit_of_reflects_of_preserves
-/
lemma preservesLimit_of_preserves (F : C ⥤ Action V G) {J : Type*}
    [Category* J] (K : J ⥤ C)
    (h : PreservesLimit K (F ⋙ Action.forget V G)) : PreservesLimit K F := by
  let F' : C ⥤ SingleObj G ⥤ V := F ⋙ (Action.functorCategoryEquivalence V G).functor
  have : PreservesLimit K F' := SingleObj.preservesLimit _ _ h
  apply preservesLimit_of_reflects_of_preserves F (Action.functorCategoryEquivalence V G).functor

/--
lemma `preservesLimitsOfShape_of_preserves` / 引理 `preservesLimitsOfShape_of_preserves`

English:
lemma preservesLimitsOfShape_of_preserves
  statement: (F : C ⥤ Action V G) {J : Type*}
  proof: by
  constructor
  intro K
  apply Action.preservesLimit_of_preserves
  exact PreservesLimitsOfShape.preservesLimit

中文:
引理 preservesLimitsOfShape_of_preserves
  结论: (F : C ⥤ 作用 V G) {J : 类型}
  证明: by
  constructor
  intro K
  apply Action.preservesLimit_of_preserves
  exact PreservesLimitsOfShape.preservesLimit

Depends on / 依赖: Action, Action.preservesLimit_of_preserves, PreservesLimitsOfShape, PreservesLimitsOfShape.preservesLimit, preservesLimit, preservesLimit_of_preserves
-/
lemma preservesLimitsOfShape_of_preserves (F : C ⥤ Action V G) {J : Type*}
    [Category* J] (h : PreservesLimitsOfShape J (F ⋙ Action.forget V G)) :
    PreservesLimitsOfShape J F := by
  constructor
  intro K
  apply Action.preservesLimit_of_preserves
  exact PreservesLimitsOfShape.preservesLimit

/--
lemma `preservesLimitsOfSize_of_preserves` / 引理 `preservesLimitsOfSize_of_preserves`

English:
lemma preservesLimitsOfSize_of_preserves
  statement: (F : C ⥤ Action V G)
  proof: by
  constructor
  intro J _
  apply Action.preservesLimitsOfShape_of_preserves
  exact PreservesLimitsOfSize.preservesLimitsOfShape

中文:
引理 preservesLimitsOfSize_of_preserves
  结论: (F : C ⥤ 作用 V G)
  证明: by
  constructor
  intro J _
  apply Action.preservesLimitsOfShape_of_preserves
  exact PreservesLimitsOfSize.preservesLimitsOfShape

Depends on / 依赖: Action, Action.preservesLimitsOfShape_of_preserves, PreservesLimitsOfSize, PreservesLimitsOfSize.preservesLimitsOfShape, preservesLimitsOfShape, preservesLimitsOfShape_of_preserves
-/
lemma preservesLimitsOfSize_of_preserves (F : C ⥤ Action V G)
    (h : PreservesLimitsOfSize.{w₂, w₁} (F ⋙ Action.forget V G)) :
    PreservesLimitsOfSize.{w₂, w₁} F := by
  constructor
  intro J _
  apply Action.preservesLimitsOfShape_of_preserves
  exact PreservesLimitsOfSize.preservesLimitsOfShape

/--
lemma `SingleObj.preservesColimit` / 引理 `SingleObj.preservesColimit`

English:
lemma SingleObj.preservesColimit
  statement: (F : C ⥤ SingleObj G ⥤ V)
  proof: by
  apply preservesColimit_of_evaluation
  intro _
  exact h

中文:
引理 SingleObj.preservesColimit
  结论: (F : C ⥤ SingleObj G ⥤ V)
  证明: by
  apply preservesColimit_of_evaluation
  intro _
  exact h
-/
private lemma SingleObj.preservesColimit (F : C ⥤ SingleObj G ⥤ V)
    {J : Type*} [Category* J] (K : J ⥤ C)
    (h : PreservesColimit K (F ⋙ (evaluation (SingleObj G) V).obj (SingleObj.star G))) :
    PreservesColimit K F := by
  apply preservesColimit_of_evaluation
  intro _
  exact h

/--
lemma `preservesColimit_of_preserves` / 引理 `preservesColimit_of_preserves`

English:
lemma preservesColimit_of_preserves
  statement: (F : C ⥤ Action V G) {J : Type*}
  proof: by
  let F' : C ⥤ SingleObj G ⥤ V := F ⋙ (Action.functorCategoryEquivalence V G).functor
  have : PreservesColimit K F' := SingleObj.preservesColimit _ _ h
  apply preservesColimit_of_reflects_of_preserves F (Action.functorCategoryEquivalence V G).functor

中文:
引理 preservesColimit_of_preserves
  结论: (F : C ⥤ 作用 V G) {J : 类型}
  证明: by
  let F' : C ⥤ SingleObj G ⥤ V := F ⋙ (Action.functorCategoryEquivalence V G).functor
  have : PreservesColimit K F' := SingleObj.preservesColimit _ _ h
  apply preservesColimit_of_reflects_of_preserves F (Action.functorCategoryEquivalence V G).functor

Depends on / 依赖: Action, Action.functorCategoryEquivalence, PreservesColimit, SingleObj, SingleObj.preservesColimit, functor, functorCategoryEquivalence, preservesColimit, preservesColimit_of_reflects_of_preserves
-/
lemma preservesColimit_of_preserves (F : C ⥤ Action V G) {J : Type*}
    [Category* J] (K : J ⥤ C)
    (h : PreservesColimit K (F ⋙ Action.forget V G)) : PreservesColimit K F := by
  let F' : C ⥤ SingleObj G ⥤ V := F ⋙ (Action.functorCategoryEquivalence V G).functor
  have : PreservesColimit K F' := SingleObj.preservesColimit _ _ h
  apply preservesColimit_of_reflects_of_preserves F (Action.functorCategoryEquivalence V G).functor

/--
lemma `preservesColimitsOfShape_of_preserves` / 引理 `preservesColimitsOfShape_of_preserves`

English:
lemma preservesColimitsOfShape_of_preserves
  statement: (F : C ⥤ Action V G) {J : Type*}
  proof: by
  constructor
  intro K
  apply Action.preservesColimit_of_preserves
  exact PreservesColimitsOfShape.preservesColimit

中文:
引理 preservesColimitsOfShape_of_preserves
  结论: (F : C ⥤ 作用 V G) {J : 类型}
  证明: by
  constructor
  intro K
  apply Action.preservesColimit_of_preserves
  exact PreservesColimitsOfShape.preservesColimit

Depends on / 依赖: Action, Action.preservesColimit_of_preserves, PreservesColimitsOfShape, PreservesColimitsOfShape.preservesColimit, preservesColimit, preservesColimit_of_preserves
-/
lemma preservesColimitsOfShape_of_preserves (F : C ⥤ Action V G) {J : Type*}
    [Category* J] (h : PreservesColimitsOfShape J (F ⋙ Action.forget V G)) :
    PreservesColimitsOfShape J F := by
  constructor
  intro K
  apply Action.preservesColimit_of_preserves
  exact PreservesColimitsOfShape.preservesColimit

/--
lemma `preservesColimitsOfSize_of_preserves` / 引理 `preservesColimitsOfSize_of_preserves`

English:
lemma preservesColimitsOfSize_of_preserves
  statement: (F : C ⥤ Action V G)
  proof: by
  constructor
  intro J _
  apply Action.preservesColimitsOfShape_of_preserves
  exact PreservesColimitsOfSize.preservesColimitsOfShape

中文:
引理 preservesColimitsOfSize_of_preserves
  结论: (F : C ⥤ 作用 V G)
  证明: by
  constructor
  intro J _
  apply Action.preservesColimitsOfShape_of_preserves
  exact PreservesColimitsOfSize.preservesColimitsOfShape

Depends on / 依赖: Action, Action.preservesColimitsOfShape_of_preserves, PreservesColimitsOfSize, PreservesColimitsOfSize.preservesColimitsOfShape, preservesColimitsOfShape, preservesColimitsOfShape_of_preserves
-/
lemma preservesColimitsOfSize_of_preserves (F : C ⥤ Action V G)
    (h : PreservesColimitsOfSize.{w₂, w₁} (F ⋙ Action.forget V G)) :
    PreservesColimitsOfSize.{w₂, w₁} F := by
  constructor
  intro J _
  apply Action.preservesColimitsOfShape_of_preserves
  exact PreservesColimitsOfSize.preservesColimitsOfShape

end Preservation

section Forget

/-- `Action.forget V G : Action V G ⥤ V` preserves the limit of some `K : J ⥤ Action V G` if
`K ⋙ Action.forget V G` has a limit. -/
noncomputable instance {J : Type*} [Category* J] (K : J ⥤ Action V G) [HasLimit (K ⋙ forget V G)] :
    PreservesLimit K (Action.forget V G) := by
  change PreservesLimit K ((Action.functorCategoryEquivalence V G).functor ⋙
    (evaluation (SingleObj G) V).obj (SingleObj.star G))
  have (k : SingleObj G) :
      HasLimit ((K ⋙ (functorCategoryEquivalence V G).functor).flip.obj k) :=
    inferInstanceAs (HasLimit (K ⋙ forget V G))
  infer_instance

noncomputable instance {J : Type*} [Category* J] [HasLimitsOfShape J V] :
    PreservesLimitsOfShape J (Action.forget V G) where

/-- `Action.forget V G : Action V G ⥤ V` preserves the colimit of some `K : J ⥤ Action V G` if
`K ⋙ Action.forget V G` has a colimit. -/
noncomputable instance {J : Type*} [Category* J]
    (K : J ⥤ Action V G) [HasColimit (K ⋙ forget V G)] :
    PreservesColimit K (Action.forget V G) := by
  change PreservesColimit K ((Action.functorCategoryEquivalence V G).functor ⋙
    (evaluation (SingleObj G) V).obj (SingleObj.star G))
  have (k : SingleObj G) :
      HasColimit ((K ⋙ (functorCategoryEquivalence V G).functor).flip.obj k) :=
    inferInstanceAs (HasColimit (K ⋙ forget V G))
  infer_instance

noncomputable instance {J : Type*} [Category* J] [HasColimitsOfShape J V] :
    PreservesColimitsOfShape J (Action.forget V G) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasFiniteLimits
  signature: V] : PreservesFiniteLimits (Action.forget V G)
  body: by
  change PreservesFiniteLimits ((Action.functorCategoryEquivalence V G).functor ⋙
    (evaluation (SingleObj G) V).obj (SingleObj.star G))
  have : PreservesFiniteLimits ((evaluation (SingleObj G) V).obj (SingleObj.star G)) := by
    constructor
    intro _ _ _
    infer_instance
  apply comp_pre

中文:
实例 [有有限极限
  签名: V] : 保持FiniteLimits (作用.forget V G)
  定义体: by
  change PreservesFiniteLimits ((Action.functorCategoryEquivalence V G).functor ⋙
    (evaluation (SingleObj G) V).obj (SingleObj.star G))
  have : PreservesFiniteLimits ((evaluation (SingleObj G) V).obj (SingleObj.star G)) := by
    constructor
    intro _ _ _
    infer_instance
  apply comp_pre

Depends on / 依赖: Action, Action.functorCategoryEquivalence, PreservesFiniteLimits, SingleObj, SingleObj.star, comp_preservesFiniteLimits, evaluation, functor, functorCategoryEquivalence, infer_instance
-/
noncomputable instance [HasFiniteLimits V] : PreservesFiniteLimits (Action.forget V G) := by
  change PreservesFiniteLimits ((Action.functorCategoryEquivalence V G).functor ⋙
    (evaluation (SingleObj G) V).obj (SingleObj.star G))
  have : PreservesFiniteLimits ((evaluation (SingleObj G) V).obj (SingleObj.star G)) := by
    constructor
    intro _ _ _
    infer_instance
  apply comp_preservesFiniteLimits

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasFiniteColimits
  signature: V] : PreservesFiniteColimits (Action.forget V G)
  body: by
  change PreservesFiniteColimits ((Action.functorCategoryEquivalence V G).functor ⋙
    (evaluation (SingleObj G) V).obj (SingleObj.star G))
  have : PreservesFiniteColimits ((evaluation (SingleObj G) V).obj (SingleObj.star G)) := by
    constructor
    intro _ _ _
    infer_instance
  apply comp

中文:
实例 [有有限余极限
  签名: V] : 保持FiniteColimits (作用.forget V G)
  定义体: by
  change PreservesFiniteColimits ((Action.functorCategoryEquivalence V G).functor ⋙
    (evaluation (SingleObj G) V).obj (SingleObj.star G))
  have : PreservesFiniteColimits ((evaluation (SingleObj G) V).obj (SingleObj.star G)) := by
    constructor
    intro _ _ _
    infer_instance
  apply comp

Depends on / 依赖: Action, Action.functorCategoryEquivalence, PreservesFiniteColimits, SingleObj, SingleObj.star, comp_preservesFiniteColimits, evaluation, functor, functorCategoryEquivalence, infer_instance
-/
noncomputable instance [HasFiniteColimits V] : PreservesFiniteColimits (Action.forget V G) := by
  change PreservesFiniteColimits ((Action.functorCategoryEquivalence V G).functor ⋙
    (evaluation (SingleObj G) V).obj (SingleObj.star G))
  have : PreservesFiniteColimits ((evaluation (SingleObj G) V).obj (SingleObj.star G)) := by
    constructor
    intro _ _ _
    infer_instance
  apply comp_preservesFiniteColimits

instance {J : Type*} [Category* J] (F : J ⥤ Action V G) :
    ReflectsLimit F (Action.forget V G) where
  reflects h := ⟨by
    apply isLimitOfReflects ((Action.functorCategoryEquivalence V G).functor)
    exact evaluationJointlyReflectsLimits _ (fun _ => h)⟩

instance {J : Type*} [Category* J] :
    ReflectsLimitsOfShape J (Action.forget V G) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ReflectsLimits (Action.forget V G)

中文:
实例 :
  签名: ReflectsLimits (作用.forget V G)
-/
instance : ReflectsLimits (Action.forget V G) where

instance {J : Type*} [Category* J] (F : J ⥤ Action V G) :
    ReflectsColimit F (Action.forget V G) where
  reflects h := ⟨by
    apply isColimitOfReflects ((Action.functorCategoryEquivalence V G).functor)
    exact evaluationJointlyReflectsColimits _ (fun _ => h)⟩

noncomputable instance {J : Type*} [Category* J] :
    ReflectsColimitsOfShape J (Action.forget V G) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ReflectsColimits (Action.forget V G)

中文:
实例 :
  签名: ReflectsColimits (作用.forget V G)
-/
noncomputable instance : ReflectsColimits (Action.forget V G) where

end Forget

namespace Functor

variable {W : Type*} [Category* W] (F : V ⥤ W) (G : Type*) [Monoid G] {J : Type*} [Category* J]

/--
Instance `mapActionPreservesLimit_of_preserves` / 实例 `mapActionPreservesLimit_of_preserves`

English:
instance mapActionPreservesLimit_of_preserves
  signature: (K : J ⥤ Action V G) [HasLimit (K ⋙ forget V G)]
  body: Action.preservesLimit_of_preserves (F.mapAction G) K
    inferInstanceAs (PreservesLimit K (forget V G ⋙ F))

中文:
实例 mapActionPreservesLimit_of_preserves
  签名: (K : J ⥤ 作用 V G) [有极限 (K ⋙ forget V G)]
  定义体: Action.preservesLimit_of_preserves (F.mapAction G) K
    inferInstanceAs (PreservesLimit K (forget V G ⋙ F))

Depends on / 依赖: Action, Action.preservesLimit_of_preserves, F.mapAction, PreservesLimit, forget, mapAction, preservesLimit_of_preserves
-/
instance mapActionPreservesLimit_of_preserves (K : J ⥤ Action V G) [HasLimit (K ⋙ forget V G)]
    [PreservesLimit (K ⋙ Action.forget V G) F] : PreservesLimit K (F.mapAction G) :=
Action.preservesLimit_of_preserves (F.mapAction G) K
    inferInstanceAs (PreservesLimit K (forget V G ⋙ F))

/--
Instance `mapActionPreservesLimitsOfShapeOfPreserves` / 实例 `mapActionPreservesLimitsOfShapeOfPreserves`

English:
instance mapActionPreservesLimitsOfShapeOfPreserves
  signature: [PreservesLimitsOfShape J F]

中文:
实例 mapActionPreservesLimitsOfShapeOfPreserves
  签名: [保持形状极限 J F]
-/
instance mapActionPreservesLimitsOfShapeOfPreserves [PreservesLimitsOfShape J F]
    [HasLimitsOfShape J V] : PreservesLimitsOfShape J (F.mapAction G) where

/--
Instance `preservesLimitsOfSize_of_preserves` / 实例 `preservesLimitsOfSize_of_preserves`

English:
instance preservesLimitsOfSize_of_preserves
  signature: [PreservesLimitsOfSize.{w₂, w₁} F]

中文:
实例 preservesLimitsOfSize_of_preserves
  签名: [保持LimitsOfSize.{w₂, w₁} F]
-/
instance preservesLimitsOfSize_of_preserves [PreservesLimitsOfSize.{w₂, w₁} F]
    [HasLimitsOfSize.{w₂, w₁} V] : PreservesLimitsOfSize.{w₂, w₁} (F.mapAction G) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [PreservesFiniteLimits
  signature: F] [HasFiniteLimits V] :
  body: inferInstance

中文:
实例 [保持FiniteLimits
  签名: F] [有有限极限 V] :
  定义体: inferInstance
-/
instance [PreservesFiniteLimits F] [HasFiniteLimits V] :
    PreservesFiniteLimits (F.mapAction G) where
  preservesFiniteLimits _ _ _ := inferInstance

/--
Instance `mapActionPreservesColimit_of_preserves` / 实例 `mapActionPreservesColimit_of_preserves`

English:
instance mapActionPreservesColimit_of_preserves
  signature: (K : J ⥤ Action V G) [HasColimit (K ⋙ forget V G)]
  body: Action.preservesColimit_of_preserves (F.mapAction G) K
    inferInstanceAs (PreservesColimit K (forget V G ⋙ F))

中文:
实例 mapActionPreservesColimit_of_preserves
  签名: (K : J ⥤ 作用 V G) [有余极限 (K ⋙ forget V G)]
  定义体: Action.preservesColimit_of_preserves (F.mapAction G) K
    inferInstanceAs (PreservesColimit K (forget V G ⋙ F))

Depends on / 依赖: Action, Action.preservesColimit_of_preserves, F.mapAction, PreservesColimit, forget, mapAction, preservesColimit_of_preserves
-/
instance mapActionPreservesColimit_of_preserves (K : J ⥤ Action V G) [HasColimit (K ⋙ forget V G)]
    [PreservesColimit (K ⋙ Action.forget V G) F] : PreservesColimit K (F.mapAction G) :=
Action.preservesColimit_of_preserves (F.mapAction G) K
    inferInstanceAs (PreservesColimit K (forget V G ⋙ F))

/--
Instance `mapActionPreservesColimitsOfShapeOfPreserves` / 实例 `mapActionPreservesColimitsOfShapeOfPreserves`

English:
instance mapActionPreservesColimitsOfShapeOfPreserves
  signature: [PreservesColimitsOfShape J F]

中文:
实例 mapActionPreservesColimitsOfShapeOfPreserves
  签名: [保持形状余极限 J F]
-/
instance mapActionPreservesColimitsOfShapeOfPreserves [PreservesColimitsOfShape J F]
    [HasColimitsOfShape J V] : PreservesColimitsOfShape J (F.mapAction G) where

/--
Instance `preservesColimitsOfSize_of_preserves` / 实例 `preservesColimitsOfSize_of_preserves`

English:
instance preservesColimitsOfSize_of_preserves
  signature: [PreservesColimitsOfSize.{w₂, w₁} F]

中文:
实例 preservesColimitsOfSize_of_preserves
  签名: [保持余limitsOfSize.{w₂, w₁} F]

Depends on / 依赖: isPretransitive_of_surjective, surjective, toAut_bijective
-/
instance preservesColimitsOfSize_of_preserves [PreservesColimitsOfSize.{w₂, w₁} F]
    [HasColimitsOfSize.{w₂, w₁} V] : PreservesColimitsOfSize.{w₂, w₁} (F.mapAction G) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [PreservesFiniteColimits
  signature: F] [HasFiniteColimits V] :
  body: inferInstance

中文:
实例 [保持FiniteColimits
  签名: F] [有有限余极限 V] :
  定义体: inferInstance
-/
instance [PreservesFiniteColimits F] [HasFiniteColimits V] :
    PreservesFiniteColimits (F.mapAction G) where
  preservesFiniteColimits _ _ _ := inferInstance

end Functor

section HasZeroMorphisms

variable [HasZeroMorphisms V]

instance {X Y : Action V G} : Zero (X ⟶ Y) := ⟨0, by simp⟩

@[simp]
/--
theorem `zero_hom` / 定理 `zero_hom`

English:
theorem zero_hom
  given: {X Y : Action V G}
  statement: (0 : X ⟶ Y).hom = 0
  proof: rfl

中文:
定理 zero_hom
  条件: {X Y : 作用 V G}
  结论: (0 : X ⟶ Y).hom = 0
  证明: rfl
-/
theorem zero_hom {X Y : Action V G} : (0 : X ⟶ Y).hom = 0 :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasZeroMorphisms (Action V G)

中文:
实例 :
  签名: 有ZeroMorphisms (作用 V G)
-/
instance : HasZeroMorphisms (Action V G) where

/--
Instance `forget_preservesZeroMorphisms` / 实例 `forget_preservesZeroMorphisms`

English:
instance forget_preservesZeroMorphisms
  signature: : Functor.PreservesZeroMorphisms (forget V G) where

中文:
实例 forget_preservesZeroMorphisms
  签名: : 函子.保持ZeroMorphisms (forget V G) where
-/
instance forget_preservesZeroMorphisms : Functor.PreservesZeroMorphisms (forget V G) where

/--
Instance `forget₂_preservesZeroMorphisms` / 实例 `forget₂_preservesZeroMorphisms`

English:
instance forget₂_preservesZeroMorphisms
  signature: {FV : V -> V -> Type*} {CV : V -> Type*}

中文:
实例 forget₂_preservesZeroMorphisms
  签名: {FV : V -> V -> 类型} {CV : V -> 类型}
-/
instance forget₂_preservesZeroMorphisms {FV : V -> V -> Type*} {CV : V -> Type*}
    [forall X Y, FunLike (FV X Y) (CV X) (CV Y)] [ConcreteCategory V FV] :
    Functor.PreservesZeroMorphisms (forget₂ (Action V G) V) where

/--
Instance `functorCategoryEquivalence_preservesZeroMorphisms` / 实例 `functorCategoryEquivalence_preservesZeroMorphisms`

English:
instance functorCategoryEquivalence_preservesZeroMorphisms
  signature: :

中文:
实例 functorCategoryEquivalence_preservesZeroMorphisms
  签名: :
-/
instance functorCategoryEquivalence_preservesZeroMorphisms :
    Functor.PreservesZeroMorphisms (functorCategoryEquivalence V G).functor where

end HasZeroMorphisms

section Preadditive

variable [Preadditive V] {X Y : Action V G}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (X ⟶ Y)
  body: ⟨f.hom + g.hom, by simp [f.comm, g.comm]⟩

中文:
实例 :
  签名: 加法 (X ⟶ Y)
  定义体: ⟨f.hom + g.hom, by simp [f.comm, g.comm]⟩

Depends on / 依赖: f.comm, f.hom, g.comm, g.hom
-/
instance : Add (X ⟶ Y) where
  add f g := ⟨f.hom + g.hom, by simp [f.comm, g.comm]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg (X ⟶ Y)
  body: ⟨-f.hom, by simp [f.comm]⟩

中文:
实例 :
  签名: 取负 (X ⟶ Y)
  定义体: ⟨-f.hom, by simp [f.comm]⟩

Depends on / 依赖: X.obj, f.comm, f.hom
-/
instance : Neg (X ⟶ Y) where
  neg f := ⟨-f.hom, by simp [f.comm]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub (X ⟶ Y)
  body: ⟨f.hom - g.hom, by simp [f.comm, g.comm]⟩

中文:
实例 :
  签名: 减法 (X ⟶ Y)
  定义体: ⟨f.hom - g.hom, by simp [f.comm, g.comm]⟩

Depends on / 依赖: f.comm, f.hom, g.comm, g.hom
-/
instance : Sub (X ⟶ Y) where
  sub f g := ⟨f.hom - g.hom, by simp [f.comm, g.comm]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul Nat (X ⟶ Y)
  body: ⟨n • f.hom, by simp [f.comm]⟩

中文:
实例 :
  签名: 标量乘法 自然数 (X ⟶ Y)
  定义体: ⟨n • f.hom, by simp [f.comm]⟩

Depends on / 依赖: f.comm, f.hom
-/
instance : SMul Nat (X ⟶ Y) where
  smul n f := ⟨n • f.hom, by simp [f.comm]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul Int (X ⟶ Y)
  body: ⟨n • f.hom, by simp [f.comm]⟩

中文:
实例 :
  签名: 标量乘法 整数 (X ⟶ Y)
  定义体: ⟨n • f.hom, by simp [f.comm]⟩

Depends on / 依赖: f.comm, f.hom, f.val
-/
instance : SMul Int (X ⟶ Y) where
  smul n f := ⟨n • f.hom, by simp [f.comm]⟩

/--
lemma `add_hom` / 引理 `add_hom`

English:
lemma add_hom
  given: (f g : X ⟶ Y)
  statement: (f + g).hom = f.hom + g.hom
  proof: rfl

中文:
引理 add_hom
  条件: (f g : X ⟶ Y)
  结论: (f + g).hom = f.hom + g.hom
  证明: rfl
-/
@[simp] lemma add_hom (f g : X ⟶ Y) : (f + g).hom = f.hom + g.hom := rfl
/--
lemma `neg_hom` / 引理 `neg_hom`

English:
lemma neg_hom
  given: (f : X ⟶ Y)
  statement: (-f).hom = -f.hom
  proof: rfl

中文:
引理 neg_hom
  条件: (f : X ⟶ Y)
  结论: (-f).hom = -f.hom
  证明: rfl
-/
@[simp] lemma neg_hom (f : X ⟶ Y) : (-f).hom = -f.hom := rfl
/--
lemma `sub_hom` / 引理 `sub_hom`

English:
lemma sub_hom
  given: (f g : X ⟶ Y)
  statement: (f - g).hom = f.hom - g.hom
  proof: rfl

中文:
引理 sub_hom
  条件: (f g : X ⟶ Y)
  结论: (f - g).hom = f.hom - g.hom
  证明: rfl
-/
@[simp] lemma sub_hom (f g : X ⟶ Y) : (f - g).hom = f.hom - g.hom := rfl
/--
lemma `nsmul_hom` / 引理 `nsmul_hom`

English:
lemma nsmul_hom
  given: (n : Nat) (f : X ⟶ Y)
  statement: (n • f).hom = n • f.hom
  proof: rfl

中文:
引理 nsmul_hom
  条件: (n : 自然数) (f : X ⟶ Y)
  结论: (n • f).hom = n • f.hom
  证明: rfl
-/
@[simp] lemma nsmul_hom (n : Nat) (f : X ⟶ Y) : (n • f).hom = n • f.hom := rfl
/--
lemma `zsmul_hom` / 引理 `zsmul_hom`

English:
lemma zsmul_hom
  given: (n : Int) (f : X ⟶ Y)
  statement: (n • f).hom = n • f.hom
  proof: rfl

中文:
引理 zsmul_hom
  条件: (n : 整数) (f : X ⟶ Y)
  结论: (n • f).hom = n • f.hom
  证明: rfl
-/
@[simp] lemma zsmul_hom (n : Int) (f : X ⟶ Y) : (n • f).hom = n • f.hom := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preadditive (Action V G)
  body: hom_injective.addCommGroup (M₂ := X.V ⟶ Y.V) _ zero_hom add_hom neg_hom sub_hom
      (fun _ _ => rfl) (fun _ _ => rfl)
  add_comp := by intros; ext; exact Preadditive.add_comp _ _ _ _ _ _
  comp_add := by intros; ext; exact Preadditive.comp_add _ _ _ _ _ _

中文:
实例 :
  签名: 预加性 (作用 V G)
  定义体: hom_injective.addCommGroup (M₂ := X.V ⟶ Y.V) _ zero_hom add_hom neg_hom sub_hom
      (fun _ _ => rfl) (fun _ _ => rfl)
  add_comp := by intros; ext; exact Preadditive.add_comp _ _ _ _ _ _
  comp_add := by intros; ext; exact Preadditive.comp_add _ _ _ _ _ _

Depends on / 依赖: Preadditive, Preadditive.add_comp, Preadditive.comp_add, addCommGroup, add_comp, add_hom, comp_add, hom_injective, hom_injective.addCommGroup, intros, neg_hom, sub_hom, zero_hom
-/
instance : Preadditive (Action V G) where
  homGroup X Y :=
    hom_injective.addCommGroup (M₂ := X.V ⟶ Y.V) _ zero_hom add_hom neg_hom sub_hom
      (fun _ _ => rfl) (fun _ _ => rfl)
  add_comp := by intros; ext; exact Preadditive.add_comp _ _ _ _ _ _
  comp_add := by intros; ext; exact Preadditive.comp_add _ _ _ _ _ _

/--
Instance `forget_additive` / 实例 `forget_additive`

English:
instance forget_additive
  signature: : Functor.Additive (forget V G) where

中文:
实例 forget_additive
  签名: : 函子.加性 (forget V G) where
-/
instance forget_additive : Functor.Additive (forget V G) where

/--
Instance `forget₂_additive` / 实例 `forget₂_additive`

English:
instance forget₂_additive
  signature: {FV : V -> V -> Type*} {CV : V -> Type*}

中文:
实例 forget₂_additive
  签名: {FV : V -> V -> 类型} {CV : V -> 类型}
-/
instance forget₂_additive {FV : V -> V -> Type*} {CV : V -> Type*}
    [forall X Y, FunLike (FV X Y) (CV X) (CV Y)] [ConcreteCategory V FV] :
    Functor.Additive (forget₂ (Action V G) V) where

/--
Instance `functorCategoryEquivalence_additive` / 实例 `functorCategoryEquivalence_additive`

English:
instance functorCategoryEquivalence_additive
  signature: :

中文:
实例 functorCategoryEquivalence_additive
  签名: :
-/
instance functorCategoryEquivalence_additive :
    Functor.Additive (functorCategoryEquivalence V G).functor where

@[simp]
/--
theorem `sum_hom` / 定理 `sum_hom`

English:
theorem sum_hom
  given: {ι : Type*} (f : ι -> (X ⟶ Y)) (s : Finset ι)
  proof: (forget V G).map_sum f s

中文:
定理 sum_hom
  条件: {ι : 类型} (f : ι -> (X ⟶ Y)) (s : 有限集 ι)
  证明: (forget V G).map_sum f s

Depends on / 依赖: forget, map_sum
-/
theorem sum_hom {ι : Type*} (f : ι -> (X ⟶ Y)) (s : Finset ι) :
    (s.sum f).hom = s.sum fun i => (f i).hom :=
  (forget V G).map_sum f s

end Preadditive

section Linear

variable [Preadditive V] {R : Type*} [Semiring R] [Linear R V]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Linear R (Action V G)
  body: { smul := fun r f => ⟨r • f.hom, by simp [f.comm]⟩
      one_smul := by intros; ext; exact one_smul _ _
      smul_zero := by intros; ext; exact smul_zero _
      zero_smul := by intros; ext; exact zero_smul _ _
      add_smul := by intros; ext; exact add_smul _ _ _
      smul_add := by intros; ext;

中文:
实例 :
  签名: 线性 R (作用 V G)
  定义体: { smul := fun r f => ⟨r • f.hom, by simp [f.comm]⟩
      one_smul := by intros; ext; exact one_smul _ _
      smul_zero := by intros; ext; exact smul_zero _
      zero_smul := by intros; ext; exact zero_smul _ _
      add_smul := by intros; ext; exact add_smul _ _ _
      smul_add := by intros; ext;

Depends on / 依赖: Linear, Linear.comp_smul, Linear.smul_comp, add_smul, comp_smul, f.comm, f.hom, intros, mul_smul, one_smul, smul_add, smul_comp, smul_zero, zero_smul
-/
instance : Linear R (Action V G) where
  homModule X Y :=
    { smul := fun r f => ⟨r • f.hom, by simp [f.comm]⟩
      one_smul := by intros; ext; exact one_smul _ _
      smul_zero := by intros; ext; exact smul_zero _
      zero_smul := by intros; ext; exact zero_smul _ _
      add_smul := by intros; ext; exact add_smul _ _ _
      smul_add := by intros; ext; exact smul_add _ _ _
      mul_smul := by intros; ext; exact mul_smul _ _ _ }
  smul_comp := by intros; ext; exact Linear.smul_comp _ _ _ _ _ _
  comp_smul := by intros; ext; exact Linear.comp_smul _ _ _ _ _ _

/--
Instance `forget_linear` / 实例 `forget_linear`

English:
instance forget_linear
  signature: : Functor.Linear R (forget V G) where

中文:
实例 forget_linear
  签名: : 函子.线性 R (forget V G) where
-/
instance forget_linear : Functor.Linear R (forget V G) where

/--
Instance `forget₂_linear` / 实例 `forget₂_linear`

English:
instance forget₂_linear
  signature: {FV : V -> V -> Type*} {CV : V -> Type*}

中文:
实例 forget₂_linear
  签名: {FV : V -> V -> 类型} {CV : V -> 类型}
-/
instance forget₂_linear {FV : V -> V -> Type*} {CV : V -> Type*}
    [forall X Y, FunLike (FV X Y) (CV X) (CV Y)] [ConcreteCategory V FV] :
    Functor.Linear R (forget₂ (Action V G) V) where

/--
Instance `functorCategoryEquivalence_linear` / 实例 `functorCategoryEquivalence_linear`

English:
instance functorCategoryEquivalence_linear
  signature: :

中文:
实例 functorCategoryEquivalence_linear
  签名: :
-/
instance functorCategoryEquivalence_linear :
    Functor.Linear R (functorCategoryEquivalence V G).functor where

@[simp]
/--
theorem `smul_hom` / 定理 `smul_hom`

English:
theorem smul_hom
  given: {X Y : Action V G} (r : R) (f : X ⟶ Y)
  statement: (r • f).hom = r • f.hom
  proof: rfl

中文:
定理 smul_hom
  条件: {X Y : 作用 V G} (r : R) (f : X ⟶ Y)
  结论: (r • f).hom = r • f.hom
  证明: rfl
-/
theorem smul_hom {X Y : Action V G} (r : R) (f : X ⟶ Y) : (r • f).hom = r • f.hom :=
  rfl

variable {H : Type*} [Monoid H] (f : G ->* H)

/--
Instance `res_additive` / 实例 `res_additive`

English:
instance res_additive
  signature: : (res V f).Additive where

中文:
实例 res_additive
  签名: : (res V f).加性 where
-/
instance res_additive : (res V f).Additive where

/--
Instance `res_linear` / 实例 `res_linear`

English:
instance res_linear
  signature: : (res V f).Linear R where

中文:
实例 res_linear
  签名: : (res V f).线性 R where
-/
instance res_linear : (res V f).Linear R where

end Linear

section Abelian

/--
Definition of `abelianAux` / `abelianAux` 的定义

English:
definition abelianAux
  signature: : Action V G ≌ (SingleObj G) ⥤ V
  body: functorCategoryEquivalence V G

中文:
定义 abelianAux
  签名: : 作用 V G ≌ (SingleObj G) ⥤ V
  定义体: functorCategoryEquivalence V G

Depends on / 依赖: functorCategoryEquivalence
-/
def abelianAux : Action V G ≌ (SingleObj G) ⥤ V :=
  functorCategoryEquivalence V G

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Abelian
  signature: V] : Abelian (Action V G)
  body: abelianOfEquivalence abelianAux.functor

中文:
实例 [交换
  签名: V] : 交换 (作用 V G)
  定义体: abelianOfEquivalence abelianAux.functor

Depends on / 依赖: abelianAux, abelianAux.functor, abelianOfEquivalence, functor
-/
noncomputable instance [Abelian V] : Abelian (Action V G) :=
  abelianOfEquivalence abelianAux.functor

end Abelian

end Action

namespace CategoryTheory.Functor

variable {W : Type*} [Category* W] (F : V ⥤ W) (G : Type*) [Monoid G] [Preadditive V]
  [Preadditive W]

/--
Instance `mapAction_preadditive` / 实例 `mapAction_preadditive`

English:
instance mapAction_preadditive
  signature: [F.Additive]

中文:
实例 mapAction_preadditive
  签名: [F.加性]
-/
instance mapAction_preadditive [F.Additive] : (F.mapAction G).Additive where

variable {R : Type*} [Semiring R] [CategoryTheory.Linear R V] [CategoryTheory.Linear R W]

/--
Instance `mapAction_linear` / 实例 `mapAction_linear`

English:
instance mapAction_linear
  signature: [F.Linear R]

中文:
实例 mapAction_linear
  签名: [F.线性 R]
-/
instance mapAction_linear [F.Linear R] : (F.mapAction G).Linear R where

end CategoryTheory.Functor
