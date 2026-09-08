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

/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasFiniteProducts V] : HasFiniteProducts (Action V G) where
  out _ :=
    Adjunction.hasLimitsOfShape_of_equivalence (Action.functorCategoryEquivalence _ _).functor
/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasFiniteLimits V] : HasFiniteLimits (Action V G) where
  out _ _ _ :=
    Adjunction.hasLimitsOfShape_of_equivalence (Action.functorCategoryEquivalence _ _).functor
/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasLimits V] : HasLimits (Action V G) :=
  Adjunction.has_limits_of_equivalence (Action.functorCategoryEquivalence _ _).functor

/-- If `V` has limits of shape `J`, so does `Action V G`. -/
/-
**Action.hasLimitsOfShape** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
形式化陈述：hasLimitsOfShape {J : Type*} [Category* J] [HasLimitsOfShape J V] : HasLim
itsOfShape J (Action V G)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.hasLimitsOfShape_of_equivalence`：hasLimitsOfSh
ape_of_equivalence (E : D ⥤ C) [E.IsEquivalence] [HasLimitsOfShape J C] : HasLim
itsOfShape J D
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…

--- 原说明 ---
If `V` has limits of shape `J`, so does `Action V G`.
-/
instance hasLimitsOfShape {J : Type*} [Category* J] [HasLimitsOfShape J V] :
    HasLimitsOfShape J (Action V G) :=
  Adjunction.hasLimitsOfShape_of_equivalence (Action.functorCategoryEquivalence _ _).functor
/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasFiniteCoproducts V] : HasFiniteCoproducts (Action V G) where
  out _ :=
    Adjunction.hasColimitsOfShape_of_equivalence (Action.functorCategoryEquivalence _ _).functor
/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasFiniteColimits V] : HasFiniteColimits (Action V G) where
  out _ _ _ :=
    Adjunction.hasColimitsOfShape_of_equivalence (Action.functorCategoryEquivalence _ _).functor
/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasColimits V] : HasColimits (Action V G) :=
  Adjunction.has_colimits_of_equivalence (Action.functorCategoryEquivalence _ _).functor

/-- If `V` has colimits of shape `J`, so does `Action V G`. -/
/-
**Action.hasColimitsOfShape** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
形式化陈述：hasColimitsOfShape {J : Type*} [Category* J] [HasColimitsOfShape J V] : Ha
sColimitsOfShape J (Action V G)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.hasColimitsOfShape_of_equivalence`：hasColimits
OfShape_of_equivalence (E : C ⥤ D) [E.IsEquivalence] [HasColimitsOfShape J D] : 
HasColimitsOfShape J C
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…

--- 原说明 ---
If `V` has colimits of shape `J`, so does `Action V G`.
-/
instance hasColimitsOfShape {J : Type*} [Category* J]
    [HasColimitsOfShape J V] : HasColimitsOfShape J (Action V G) :=
  Adjunction.hasColimitsOfShape_of_equivalence (Action.functorCategoryEquivalence _ _).functor

end Limits

section Preservation

variable {C : Type*} [Category* C]

/-- `F : C ⥤ SingleObj G ⥤ V` preserves the limit of some `K : J ⥤ C` if it does
evaluated at `SingleObj.star G`. -/
/-
**Action.SingleObj.preservesLimit** 是 Mathlib 中的一个引理，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`F : C ⥤ SingleObj G ⥤ V` preserves the limit of some `K : J ⥤ C` if it does
evaluated at `SingleObj.star G`.
-/
private lemma SingleObj.preservesLimit (F : C ⥤ SingleObj G ⥤ V)
    {J : Type*} [Category* J] (K : J ⥤ C)
    (h : PreservesLimit K (F ⋙ (evaluation (SingleObj G) V).obj (SingleObj.star G))) :
    PreservesLimit K F := by
  apply preservesLimit_of_evaluation
  intro _
  exact h

/-- `F : C ⥤ Action V G` preserves the limit of some `K : J ⥤ C` if
it does after postcomposing with the forgetful functor `Action V G ⥤ V`. -/
/-
**Action.preservesLimit_of_preserves** 是 Mathlib 中的一个引理，位于命名空间 `Action`。
形式化陈述：preservesLimit_of_preserves (F : C ⥤ Action V G) {J : Type*} [Category* J]
 (K : J ⥤ C) (h : PreservesLimit K (F ⋙ Action.forget V G)) : PreservesLimit K F
参数：F : C ⥤ Action V G；K : J ⥤ C；h : PreservesLimit K (F ⋙ Action.forget V G)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.CategoryTheory.Action.Limits.0.Action.SingleObj.preserv
esLimit`：∀ {V : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} V] {G : Typ
e u_2} [inst_1 : Monoid G] {C : Type u_3}   [inst_2 : CategoryTheory.…
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_reflects_of_preserves`：preserves
Limit_of_reflects_of_preserves [PreservesLimit K (F ⋙ G)] [ReflectsLimit (K ⋙ F)
 G] : PreservesLimit K F
· 使用定理 `CategoryTheory.CreatesLimit.toReflectsLimit`：∀ {C : Type u₁} {inst : Cat
egoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category
.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…

--- 原说明 ---
`F : C ⥤ Action V G` preserves the limit of some `K : J ⥤ C` if
it does after postcomposing with the forgetful functor `Action V G ⥤ V`.
-/
lemma preservesLimit_of_preserves (F : C ⥤ Action V G) {J : Type*}
    [Category* J] (K : J ⥤ C)
    (h : PreservesLimit K (F ⋙ Action.forget V G)) : PreservesLimit K F := by
  let F' : C ⥤ SingleObj G ⥤ V := F ⋙ (Action.functorCategoryEquivalence V G).functor
  have : PreservesLimit K F' := SingleObj.preservesLimit _ _ h
  apply preservesLimit_of_reflects_of_preserves F (Action.functorCategoryEquivalence V G).functor

/-- `F : C ⥤ Action V G` preserves limits of some shape `J`
if it does after postcomposing with the forgetful functor `Action V G ⥤ V`. -/
/-
**Action.preservesLimitsOfShape_of_preserves** 是 Mathlib 中的一个引理，位于命名空间 `Action`。
形式化陈述：preservesLimitsOfShape_of_preserves (F : C ⥤ Action V G) {J : Type*} [Cate
gory* J] (h : PreservesLimitsOfShape J (F ⋙ Action.forget V G)) : PreservesLimit
sOfShape J F
参数：F : C ⥤ Action V G；h : PreservesLimitsOfShape J (F ⋙ Action.forget V G)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Action.preservesLimit_of_preserves`：preservesLimit_of_preserves (F : C ⥤
 Action V G) {J : Type*} [Category* J] (K : J ⥤ C) (h : PreservesLimit K (F ⋙ Ac
tion.forget V G)) : Pres…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…

--- 原说明 ---
`F : C ⥤ Action V G` preserves limits of some shape `J`
if it does after postcomposing with the forgetful functor `Action V G ⥤ V`.
-/
lemma preservesLimitsOfShape_of_preserves (F : C ⥤ Action V G) {J : Type*}
    [Category* J] (h : PreservesLimitsOfShape J (F ⋙ Action.forget V G)) :
    PreservesLimitsOfShape J F := by
  constructor
  intro K
  apply Action.preservesLimit_of_preserves
  exact PreservesLimitsOfShape.preservesLimit

/-- `F : C ⥤ Action V G` preserves limits of some size
if it does after postcomposing with the forgetful functor `Action V G ⥤ V`. -/
/-
**Action.preservesLimitsOfSize_of_preserves** 是 Mathlib 中的一个引理，位于命名空间 `Action`。
形式化陈述：preservesLimitsOfSize_of_preserves (F : C ⥤ Action V G) (h : PreservesLimi
tsOfSize.{w₂, w₁} (F ⋙ Action.forget V G)) : PreservesLimitsOfSize.{w₂, w₁} F
参数：F : C ⥤ Action V G；h : PreservesLimitsOfSize.{w₂, w₁} (F ⋙ Action.forget V G)
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Action.preservesLimitsOfShape_of_preserves`：preservesLimitsOfShape_of_pr
eserves (F : C ⥤ Action V G) {J : Type*} [Category* J] (h : PreservesLimitsOfSha
pe J (F ⋙ Action.forget V G)) : …
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
`F : C ⥤ Action V G` preserves limits of some size
if it does after postcomposing with the forgetful functor `Action V G ⥤ V`.
-/
lemma preservesLimitsOfSize_of_preserves (F : C ⥤ Action V G)
    (h : PreservesLimitsOfSize.{w₂, w₁} (F ⋙ Action.forget V G)) :
    PreservesLimitsOfSize.{w₂, w₁} F := by
  constructor
  intro J _
  apply Action.preservesLimitsOfShape_of_preserves
  exact PreservesLimitsOfSize.preservesLimitsOfShape

/-- `F : C ⥤ SingleObj G ⥤ V` preserves the colimit of some `K : J ⥤ C` if it does
evaluated at `SingleObj.star G`. -/
/-
**Action.SingleObj.preservesColimit** 是 Mathlib 中的一个引理，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`F : C ⥤ SingleObj G ⥤ V` preserves the colimit of some `K : J ⥤ C` if it does
evaluated at `SingleObj.star G`.
-/
private lemma SingleObj.preservesColimit (F : C ⥤ SingleObj G ⥤ V)
    {J : Type*} [Category* J] (K : J ⥤ C)
    (h : PreservesColimit K (F ⋙ (evaluation (SingleObj G) V).obj (SingleObj.star G))) :
    PreservesColimit K F := by
  apply preservesColimit_of_evaluation
  intro _
  exact h

/-- `F : C ⥤ Action V G` preserves the colimit of some `K : J ⥤ C` if
it does after postcomposing with the forgetful functor `Action V G ⥤ V`. -/
/-
**Action.preservesColimit_of_preserves** 是 Mathlib 中的一个引理，位于命名空间 `Action`。
形式化陈述：preservesColimit_of_preserves (F : C ⥤ Action V G) {J : Type*} [Category* 
J] (K : J ⥤ C) (h : PreservesColimit K (F ⋙ Action.forget V G)) : PreservesColim
it K F
参数：F : C ⥤ Action V G；K : J ⥤ C；h : PreservesColimit K (F ⋙ Action.forget V G)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.CategoryTheory.Action.Limits.0.Action.SingleObj.preserv
esColimit`：∀ {V : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} V] {G : T
ype u_2} [inst_1 : Monoid G] {C : Type u_3}   [inst_2 : CategoryTheory.…
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_reflects_of_preserves`：preserv
esColimit_of_reflects_of_preserves [PreservesColimit K (F ⋙ G)] [ReflectsColimit
 (K ⋙ F) G] : PreservesColimit K F
· 使用定理 `CategoryTheory.CreatesColimit.toReflectsColimit`：∀ {C : Type u₁} {inst :
 CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Cate
gory.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…

--- 原说明 ---
`F : C ⥤ Action V G` preserves the colimit of some `K : J ⥤ C` if
it does after postcomposing with the forgetful functor `Action V G ⥤ V`.
-/
lemma preservesColimit_of_preserves (F : C ⥤ Action V G) {J : Type*}
    [Category* J] (K : J ⥤ C)
    (h : PreservesColimit K (F ⋙ Action.forget V G)) : PreservesColimit K F := by
  let F' : C ⥤ SingleObj G ⥤ V := F ⋙ (Action.functorCategoryEquivalence V G).functor
  have : PreservesColimit K F' := SingleObj.preservesColimit _ _ h
  apply preservesColimit_of_reflects_of_preserves F (Action.functorCategoryEquivalence V G).functor

/-- `F : C ⥤ Action V G` preserves colimits of some shape `J`
if it does after postcomposing with the forgetful functor `Action V G ⥤ V`. -/
/-
**Action.preservesColimitsOfShape_of_preserves** 是 Mathlib 中的一个引理，位于命名空间 `Action
`。
形式化陈述：preservesColimitsOfShape_of_preserves (F : C ⥤ Action V G) {J : Type*} [Ca
tegory* J] (h : PreservesColimitsOfShape J (F ⋙ Action.forget V G)) : PreservesC
olimitsOfShape J F
参数：F : C ⥤ Action V G；h : PreservesColimitsOfShape J (F ⋙ Action.forget V G)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Action.preservesColimit_of_preserves`：preservesColimit_of_preserves (F :
 C ⥤ Action V G) {J : Type*} [Category* J] (K : J ⥤ C) (h : PreservesColimit K (
F ⋙ Action.forget V G)) : …
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…

--- 原说明 ---
`F : C ⥤ Action V G` preserves colimits of some shape `J`
if it does after postcomposing with the forgetful functor `Action V G ⥤ V`.
-/
lemma preservesColimitsOfShape_of_preserves (F : C ⥤ Action V G) {J : Type*}
    [Category* J] (h : PreservesColimitsOfShape J (F ⋙ Action.forget V G)) :
    PreservesColimitsOfShape J F := by
  constructor
  intro K
  apply Action.preservesColimit_of_preserves
  exact PreservesColimitsOfShape.preservesColimit

/-- `F : C ⥤ Action V G` preserves colimits of some size
if it does after postcomposing with the forgetful functor `Action V G ⥤ V`. -/
/-
**Action.preservesColimitsOfSize_of_preserves** 是 Mathlib 中的一个引理，位于命名空间 `Action`
。
形式化陈述：preservesColimitsOfSize_of_preserves (F : C ⥤ Action V G) (h : PreservesCo
limitsOfSize.{w₂, w₁} (F ⋙ Action.forget V G)) : PreservesColimitsOfSize.{w₂, w₁
} F
参数：F : C ⥤ Action V G；h : PreservesColimitsOfSize.{w₂, w₁} (F ⋙ Action.forget V 
G)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Action.preservesColimitsOfShape_of_preserves`：preservesColimitsOfShape_o
f_preserves (F : C ⥤ Action V G) {J : Type*} [Category* J] (h : PreservesColimit
sOfShape J (F ⋙ Action.forget V G)…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfSize.preservesColimitsOfShape`：
∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_
1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
`F : C ⥤ Action V G` preserves colimits of some size
if it does after postcomposing with the forgetful functor `Action V G ⥤ V`.
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
/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Action.forget V G : Action V G ⥤ V` preserves the limit of some `K : J ⥤ Action
 V G` if
`K ⋙ Action.forget V G` has a limit.
-/
noncomputable instance {J : Type*} [Category* J] (K : J ⥤ Action V G) [HasLimit (K ⋙ forget V G)] :
    PreservesLimit K (Action.forget V G) := by
  change PreservesLimit K ((Action.functorCategoryEquivalence V G).functor ⋙
    (evaluation (SingleObj G) V).obj (SingleObj.star G))
  have (k : SingleObj G) :
      HasLimit ((K ⋙ (functorCategoryEquivalence V G).functor).flip.obj k) :=
    inferInstanceAs (HasLimit (K ⋙ forget V G))
  infer_instance
/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance {J : Type*} [Category* J] [HasLimitsOfShape J V] :
    PreservesLimitsOfShape J (Action.forget V G) where

/-- `Action.forget V G : Action V G ⥤ V` preserves the colimit of some `K : J ⥤ Action V G` if
`K ⋙ Action.forget V G` has a colimit. -/
/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Action.forget V G : Action V G ⥤ V` preserves the colimit of some `K : J ⥤ Acti
on V G` if
`K ⋙ Action.forget V G` has a colimit.
-/
noncomputable instance {J : Type*} [Category* J]
    (K : J ⥤ Action V G) [HasColimit (K ⋙ forget V G)] :
    PreservesColimit K (Action.forget V G) := by
  change PreservesColimit K ((Action.functorCategoryEquivalence V G).functor ⋙
    (evaluation (SingleObj G) V).obj (SingleObj.star G))
  have (k : SingleObj G) :
      HasColimit ((K ⋙ (functorCategoryEquivalence V G).functor).flip.obj k) :=
    inferInstanceAs (HasColimit (K ⋙ forget V G))
  infer_instance
/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance {J : Type*} [Category* J] [HasColimitsOfShape J V] :
    PreservesColimitsOfShape J (Action.forget V G) where
/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [HasFiniteLimits V] : PreservesFiniteLimits (Action.forget V G) := by
  change PreservesFiniteLimits ((Action.functorCategoryEquivalence V G).functor ⋙
    (evaluation (SingleObj G) V).obj (SingleObj.star G))
  have : PreservesFiniteLimits ((evaluation (SingleObj G) V).obj (SingleObj.star G)) := by
    constructor
    intro _ _ _
    infer_instance
  apply comp_preservesFiniteLimits
/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [HasFiniteColimits V] : PreservesFiniteColimits (Action.forget V G) := by
  change PreservesFiniteColimits ((Action.functorCategoryEquivalence V G).functor ⋙
    (evaluation (SingleObj G) V).obj (SingleObj.star G))
  have : PreservesFiniteColimits ((evaluation (SingleObj G) V).obj (SingleObj.star G)) := by
    constructor
    intro _ _ _
    infer_instance
  apply comp_preservesFiniteColimits
/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {J : Type*} [Category* J] (F : J ⥤ Action V G) :
    ReflectsLimit F (Action.forget V G) where
  reflects h := ⟨by
    apply isLimitOfReflects ((Action.functorCategoryEquivalence V G).functor)
    exact evaluationJointlyReflectsLimits _ (fun _ => h)⟩
/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {J : Type*} [Category* J] :
    ReflectsLimitsOfShape J (Action.forget V G) where
/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ReflectsLimits (Action.forget V G) where
/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {J : Type*} [Category* J] (F : J ⥤ Action V G) :
    ReflectsColimit F (Action.forget V G) where
  reflects h := ⟨by
    apply isColimitOfReflects ((Action.functorCategoryEquivalence V G).functor)
    exact evaluationJointlyReflectsColimits _ (fun _ => h)⟩
/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance {J : Type*} [Category* J] :
    ReflectsColimitsOfShape J (Action.forget V G) where
/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : ReflectsColimits (Action.forget V G) where

end Forget

namespace Functor

variable {W : Type*} [Category* W] (F : V ⥤ W) (G : Type*) [Monoid G] {J : Type*} [Category* J]

/-- `F.mapAction : Action V G ⥤ Action W G` preserves the limit of some `K : J ⥤ Action V G` if
`K ⋙ forget V G` has a limit and `F` preserves the limit of `K ⋙ forget V G`. -/
/-
**Action.Functor.mapActionPreservesLimit_of_preserves** 是 Mathlib 中的一个实例，位于命名空间 
`Action.Functor`。
形式化陈述：mapActionPreservesLimit_of_preserves (K : J ⥤ Action V G) [HasLimit (K ⋙ f
orget V G)] [PreservesLimit (K ⋙ Action.forget V G) F] : PreservesLimit K (F.map
Action G)
参数：K : J ⥤ Action V G；K ⋙ forget V G；K ⋙ Action.forget V G。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Action.preservesLimit_of_preserves`：preservesLimit_of_preserves (F : C ⥤
 Action V G) {J : Type*} [Category* J] (K : J ⥤ C) (h : PreservesLimit K (F ⋙ Ac
tion.forget V G)) : Pres…

--- 原说明 ---
`F.mapAction : Action V G ⥤ Action W G` preserves the limit of some `K : J ⥤ Act
ion V G` if
`K ⋙ forget V G` has a limit and `F` preserves the limit of `K ⋙ forget V G`.
-/
instance mapActionPreservesLimit_of_preserves (K : J ⥤ Action V G) [HasLimit (K ⋙ forget V G)]
    [PreservesLimit (K ⋙ Action.forget V G) F] : PreservesLimit K (F.mapAction G) :=
  Action.preservesLimit_of_preserves (F.mapAction G) K <|
    inferInstanceAs (PreservesLimit K (forget V G ⋙ F))

/-- `F.mapAction : Action V G ⥤ Action W G` preserves limits of some shape `J` if
`V` has limits of shape `J` and `F` preserves limits of shape `J`. -/
/-
**Action.Functor.mapActionPreservesLimitsOfShapeOfPreserves** 是 Mathlib 中的一个定理，位
于命名空间 `Action.Functor`。
形式化陈述：∀ {V : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} V] {W : Type u
_3}   [inst_1 : CategoryTheory.Category.{v_2, u_3} W] (F : CategoryTheory.Functo
r V W) (G : Type u_4) [inst_2 : Monoid G]   {J : Type u_5} [inst_3 : CategoryThe
ory.Category.{v_3, u_5} J] [CategoryTheory.Limits.PreservesLimitsOfShape J F]   
[CategoryTheory.Limits.HasLimitsOfShape J V], CategoryTheory.Limits.PreservesLim
itsOfShape J (F.mapAction G)
参数：F : CategoryTheory.Functor V W；G : Type u_4；F.mapAction G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitCompOfPreservesLimit`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `Action.instPreservesLimitsOfShapeForgetOfHasLimitsOfShape`：∀ {V : Type u
_1} [inst : CategoryTheory.Category.{v_1, u_1} V] {G : Type u_2} [inst_1 : Monoi
d G] {J : Type u_3}   [inst_2 : CategoryTheory.…

--- 原说明 ---
`F.mapAction : Action V G ⥤ Action W G` preserves limits of some shape `J` if
`V` has limits of shape `J` and `F` preserves limits of shape `J`.
-/
instance mapActionPreservesLimitsOfShapeOfPreserves [PreservesLimitsOfShape J F]
    [HasLimitsOfShape J V] : PreservesLimitsOfShape J (F.mapAction G) where

/-- `F.mapAction : Action V G ⥤ Action W G` preserves limits of some size if
`V` has limits of that size and `F` preserves limits of that size. -/
/-
**Action.Functor.preservesLimitsOfSize_of_preserves** 是 Mathlib 中的一个定理，位于命名空间 `A
ction.Functor`。
形式化陈述：∀ {V : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} V] {W : Type u
_3}   [inst_1 : CategoryTheory.Category.{v_2, u_3} W] (F : CategoryTheory.Functo
r V W) (G : Type u_4) [inst_2 : Monoid G]   [CategoryTheory.Limits.PreservesLimi
tsOfSize.{w₂, w₁, v_1, v_2, u_1, u_3} F]   [CategoryTheory.Limits.HasLimitsOfSiz
e.{w₂, w₁, v_1, u_1} V],   CategoryTheory.Limits.PreservesLimitsOfSize.{w₂, w₁, 
v_1, v_2, max (max u_1 u_4) v_1, max (max u_3 u_4) v_2}     (F.mapAction G)
参数：F : CategoryTheory.Functor V W；G : Type u_4；max u_1 u_4；max u_3 u_4；F.mapActi
on G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Action.Functor.mapActionPreservesLimitsOfShapeOfPreserves`：∀ {V : Type u
_1} [inst : CategoryTheory.Category.{v_1, u_1} V] {W : Type u_3}   [inst_1 : Cat
egoryTheory.Category.{v_2, u_3} W] (F : Categor…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasLimitsOfSize`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTh
eory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…

--- 原说明 ---
`F.mapAction : Action V G ⥤ Action W G` preserves limits of some size if
`V` has limits of that size and `F` preserves limits of that size.
-/
instance preservesLimitsOfSize_of_preserves [PreservesLimitsOfSize.{w₂, w₁} F]
    [HasLimitsOfSize.{w₂, w₁} V] : PreservesLimitsOfSize.{w₂, w₁} (F.mapAction G) where

/-- `F.mapAction : Action V G ⥤ Action W G` preserves finite limits if
`V` has finite limits and `F` preserves finite limits. -/
/-
**Action.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `Action.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`F.mapAction : Action V G ⥤ Action W G` preserves finite limits if
`V` has finite limits and `F` preserves finite limits.
-/
instance [PreservesFiniteLimits F] [HasFiniteLimits V] :
    PreservesFiniteLimits (F.mapAction G) where
  preservesFiniteLimits _ _ _ := inferInstance

/-- `F.mapAction : Action V G ⥤ Action W G` preserves the colimit of some `K : J ⥤ Action V G` if
`K ⋙ forget V G` has a colimit and `F` preserves the colimit of `K ⋙ forget V G`. -/
/-
**Action.Functor.mapActionPreservesColimit_of_preserves** 是 Mathlib 中的一个实例，位于命名空
间 `Action.Functor`。
形式化陈述：mapActionPreservesColimit_of_preserves (K : J ⥤ Action V G) [HasColimit (K
 ⋙ forget V G)] [PreservesColimit (K ⋙ Action.forget V G) F] : PreservesColimit 
K (F.mapAction G)
参数：K : J ⥤ Action V G；K ⋙ forget V G；K ⋙ Action.forget V G。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Action.preservesColimit_of_preserves`：preservesColimit_of_preserves (F :
 C ⥤ Action V G) {J : Type*} [Category* J] (K : J ⥤ C) (h : PreservesColimit K (
F ⋙ Action.forget V G)) : …

--- 原说明 ---
`F.mapAction : Action V G ⥤ Action W G` preserves the colimit of some `K : J ⥤ A
ction V G` if
`K ⋙ forget V G` has a colimit and `F` preserves the colimit of `K ⋙ forget V G`
.
-/
instance mapActionPreservesColimit_of_preserves (K : J ⥤ Action V G) [HasColimit (K ⋙ forget V G)]
    [PreservesColimit (K ⋙ Action.forget V G) F] : PreservesColimit K (F.mapAction G) :=
  Action.preservesColimit_of_preserves (F.mapAction G) K <|
    inferInstanceAs (PreservesColimit K (forget V G ⋙ F))

/-- `F.mapAction : Action V G ⥤ Action W G` preserves colimits of some shape `J` if
`V` has colimits of shape `J` and `F` preserves colimits of shape `J`. -/
/-
**Action.Functor.mapActionPreservesColimitsOfShapeOfPreserves** 是 Mathlib 中的一个定理
，位于命名空间 `Action.Functor`。
形式化陈述：∀ {V : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} V] {W : Type u
_3}   [inst_1 : CategoryTheory.Category.{v_2, u_3} W] (F : CategoryTheory.Functo
r V W) (G : Type u_4) [inst_2 : Monoid G]   {J : Type u_5} [inst_3 : CategoryThe
ory.Category.{v_3, u_5} J] [CategoryTheory.Limits.PreservesColimitsOfShape J F] 
  [CategoryTheory.Limits.HasColimitsOfShape J V], CategoryTheory.Limits.Preserve
sColimitsOfShape J (F.mapAction G)
参数：F : CategoryTheory.Functor V W；G : Type u_4；F.mapAction G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitCompOfPreservesColimit`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `Action.instPreservesColimitsOfShapeForgetOfHasColimitsOfShape`：∀ {V : Ty
pe u_1} [inst : CategoryTheory.Category.{v_1, u_1} V] {G : Type u_2} [inst_1 : M
onoid G] {J : Type u_3}   [inst_2 : CategoryTheory.…

--- 原说明 ---
`F.mapAction : Action V G ⥤ Action W G` preserves colimits of some shape `J` if
`V` has colimits of shape `J` and `F` preserves colimits of shape `J`.
-/
instance mapActionPreservesColimitsOfShapeOfPreserves [PreservesColimitsOfShape J F]
    [HasColimitsOfShape J V] : PreservesColimitsOfShape J (F.mapAction G) where

/-- `F.mapAction : Action V G ⥤ Action W G` preserves colimits of some size if
`V` has colimits of that size and `F` preserves colimits of that size. -/
/-
**Action.Functor.preservesColimitsOfSize_of_preserves** 是 Mathlib 中的一个定理，位于命名空间 
`Action.Functor`。
形式化陈述：∀ {V : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} V] {W : Type u
_3}   [inst_1 : CategoryTheory.Category.{v_2, u_3} W] (F : CategoryTheory.Functo
r V W) (G : Type u_4) [inst_2 : Monoid G]   [CategoryTheory.Limits.PreservesColi
mitsOfSize.{w₂, w₁, v_1, v_2, u_1, u_3} F]   [CategoryTheory.Limits.HasColimitsO
fSize.{w₂, w₁, v_1, u_1} V],   CategoryTheory.Limits.PreservesColimitsOfSize.{w₂
, w₁, v_1, v_2, max (max u_1 u_4) v_1, max (max u_3 u_4) v_2}     (F.mapAction G
)
参数：F : CategoryTheory.Functor V W；G : Type u_4；max u_1 u_4；max u_3 u_4；F.mapActi
on G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Action.Functor.mapActionPreservesColimitsOfShapeOfPreserves`：∀ {V : Type
 u_1} [inst : CategoryTheory.Category.{v_1, u_1} V] {W : Type u_3}   [inst_1 : C
ategoryTheory.Category.{v_2, u_3} W] (F : Categor…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfSize.preservesColimitsOfShape`：
∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_
1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…

--- 原说明 ---
`F.mapAction : Action V G ⥤ Action W G` preserves colimits of some size if
`V` has colimits of that size and `F` preserves colimits of that size.
-/
instance preservesColimitsOfSize_of_preserves [PreservesColimitsOfSize.{w₂, w₁} F]
    [HasColimitsOfSize.{w₂, w₁} V] : PreservesColimitsOfSize.{w₂, w₁} (F.mapAction G) where

/-- `F.mapAction : Action V G ⥤ Action W G` preserves finite colimits if
`V` has finite colimits and `F` preserves finite colimits. -/
/-
**Action.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `Action.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`F.mapAction : Action V G ⥤ Action W G` preserves finite colimits if
`V` has finite colimits and `F` preserves finite colimits.
-/
instance [PreservesFiniteColimits F] [HasFiniteColimits V] :
    PreservesFiniteColimits (F.mapAction G) where
  preservesFiniteColimits _ _ _ := inferInstance

end Functor

section HasZeroMorphisms

variable [HasZeroMorphisms V]

/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : Action V G} : Zero (X ⟶ Y) := ⟨0, by simp⟩

@[simp]
/-
**Action.zero_hom** 是 Mathlib 中的一个定理，位于命名空间 `Action`。
形式化陈述：zero_hom {X Y : Action V G} : (0 : X ⟶ Y).hom = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_hom {X Y : Action V G} : (0 : X ⟶ Y).hom = 0 :=
  rfl
/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasZeroMorphisms (Action V G) where
/-
**Action.forget_preservesZeroMorphisms** 是 Mathlib 中的一个定理，位于命名空间 `Action`。
形式化陈述：∀ {V : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} V] {G : Type u
_2} [inst_1 : Monoid G]   [inst_2 : CategoryTheory.Limits.HasZeroMorphisms V], (
Action.forget V G).PreservesZeroMorphisms
参数：Action.forget V G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Action.forget_map`：∀ (V : Type u_1) [inst : CategoryTheory.Category.{v_1
, u_1} V] (G : Type u_2) [inst_1 : Monoid G] {X Y : Action V G}   (f : X ⟶ Y), (
Action.…
-/
instance forget_preservesZeroMorphisms : Functor.PreservesZeroMorphisms (forget V G) where
/-
**Action.forget** 是 Mathlib 中的一个定义，位于命名空间 `Action`。
形式化陈述：forget : Action V G ⥤ V where obj M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance forget₂_preservesZeroMorphisms {FV : V → V → Type*} {CV : V → Type*}
    [∀ X Y, FunLike (FV X Y) (CV X) (CV Y)] [ConcreteCategory V FV] :
    Functor.PreservesZeroMorphisms (forget₂ (Action V G) V) where
/-
**Action.functorCategoryEquivalence_preservesZeroMorphisms** 是 Mathlib 中的一个定理，位于
命名空间 `Action`。
形式化陈述：∀ {V : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} V] {G : Type u
_2} [inst_1 : Monoid G]   [inst_2 : CategoryTheory.Limits.HasZeroMorphisms V],  
 (Action.functorCategoryEquivalence V G).functor.PreservesZeroMorphisms
参数：Action.functorCategoryEquivalence V G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_full`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   [inst_2 : Category…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance functorCategoryEquivalence_preservesZeroMorphisms :
    Functor.PreservesZeroMorphisms (functorCategoryEquivalence V G).functor where

end HasZeroMorphisms

section Preadditive

variable [Preadditive V] {X Y : Action V G}

/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add (X ⟶ Y) where
  add f g := ⟨f.hom + g.hom, by simp [f.comm, g.comm]⟩
/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg (X ⟶ Y) where
  neg f := ⟨-f.hom, by simp [f.comm]⟩
/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sub (X ⟶ Y) where
  sub f g := ⟨f.hom - g.hom, by simp [f.comm, g.comm]⟩
/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul ℕ (X ⟶ Y) where
  smul n f := ⟨n • f.hom, by simp [f.comm]⟩
/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul ℤ (X ⟶ Y) where
  smul n f := ⟨n • f.hom, by simp [f.comm]⟩
/-
**Action.add_hom** 是 Mathlib 中的一个定理，位于命名空间 `Action`。
形式化陈述：∀ {V : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} V] {G : Type u
_2} [inst_1 : Monoid G]   [inst_2 : CategoryTheory.Preadditive V] {X Y : Action 
V G} (f g : X ⟶ Y), (f + g).hom = f.hom + g.hom
参数：f g : X ⟶ Y；f + g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma add_hom (f g : X ⟶ Y) : (f + g).hom = f.hom + g.hom := rfl
/-
**Action.neg_hom** 是 Mathlib 中的一个定理，位于命名空间 `Action`。
形式化陈述：∀ {V : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} V] {G : Type u
_2} [inst_1 : Monoid G]   [inst_2 : CategoryTheory.Preadditive V] {X Y : Action 
V G} (f : X ⟶ Y), (-f).hom = -f.hom
参数：f : X ⟶ Y；-f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma neg_hom (f : X ⟶ Y) : (-f).hom = -f.hom := rfl
/-
**Action.sub_hom** 是 Mathlib 中的一个定理，位于命名空间 `Action`。
形式化陈述：∀ {V : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} V] {G : Type u
_2} [inst_1 : Monoid G]   [inst_2 : CategoryTheory.Preadditive V] {X Y : Action 
V G} (f g : X ⟶ Y), (f - g).hom = f.hom - g.hom
参数：f g : X ⟶ Y；f - g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma sub_hom (f g : X ⟶ Y) : (f - g).hom = f.hom - g.hom := rfl
/-
**Action.nsmul_hom** 是 Mathlib 中的一个定理，位于命名空间 `Action`。
形式化陈述：∀ {V : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} V] {G : Type u
_2} [inst_1 : Monoid G]   [inst_2 : CategoryTheory.Preadditive V] {X Y : Action 
V G} (n : ℕ) (f : X ⟶ Y), (n • f).hom = n • f.hom
参数：n : ℕ；f : X ⟶ Y；n • f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma nsmul_hom (n : ℕ) (f : X ⟶ Y) : (n • f).hom = n • f.hom := rfl
/-
**Action.zsmul_hom** 是 Mathlib 中的一个定理，位于命名空间 `Action`。
形式化陈述：∀ {V : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} V] {G : Type u
_2} [inst_1 : Monoid G]   [inst_2 : CategoryTheory.Preadditive V] {X Y : Action 
V G} (n : ℤ) (f : X ⟶ Y), (n • f).hom = n • f.hom
参数：n : ℤ；f : X ⟶ Y；n • f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma zsmul_hom (n : ℤ) (f : X ⟶ Y) : (n • f).hom = n • f.hom := rfl
/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Preadditive (Action V G) where
  homGroup X Y :=
    hom_injective.addCommGroup (M₂ := X.V ⟶ Y.V) _ zero_hom add_hom neg_hom sub_hom
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
  add_comp := by intros; ext; exact Preadditive.add_comp _ _ _ _ _ _
  comp_add := by intros; ext; exact Preadditive.comp_add _ _ _ _ _ _
/-
**Action.forget_additive** 是 Mathlib 中的一个定理，位于命名空间 `Action`。
形式化陈述：∀ {V : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} V] {G : Type u
_2} [inst_1 : Monoid G]   [inst_2 : CategoryTheory.Preadditive V], (Action.forge
t V G).Additive
参数：Action.forget V G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance forget_additive : Functor.Additive (forget V G) where
/-
**Action.forget** 是 Mathlib 中的一个定义，位于命名空间 `Action`。
形式化陈述：forget : Action V G ⥤ V where obj M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance forget₂_additive {FV : V → V → Type*} {CV : V → Type*}
    [∀ X Y, FunLike (FV X Y) (CV X) (CV Y)] [ConcreteCategory V FV] :
    Functor.Additive (forget₂ (Action V G) V) where
/-
**Action.functorCategoryEquivalence_additive** 是 Mathlib 中的一个定理，位于命名空间 `Action`。
形式化陈述：∀ {V : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} V] {G : Type u
_2} [inst_1 : Monoid G]   [inst_2 : CategoryTheory.Preadditive V], (Action.funct
orCategoryEquivalence V G).functor.Additive
参数：Action.functorCategoryEquivalence V G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance functorCategoryEquivalence_additive :
    Functor.Additive (functorCategoryEquivalence V G).functor where

@[simp]
/-
**Action.sum_hom** 是 Mathlib 中的一个定理，位于命名空间 `Action`。
形式化陈述：sum_hom {ι : Type*} (f : ι -> (X ⟶ Y)) (s : Finset ι) : (s.sum f).hom = s.
sum fun i => (f i).hom
参数：f : ι -> (X ⟶ Y)；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_sum`：∀ {C : Type u_1} {D : Type u_2} [inst : 
CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, 
u_2} D] [inst_2 : Ca…
· 使用定理 `Action.forget_additive`：∀ {V : Type u_1} [inst : CategoryTheory.Category
.{v_1, u_1} V] {G : Type u_2} [inst_1 : Monoid G]   [inst_2 : CategoryTheory.Pre
additive V],…
-/
theorem sum_hom {ι : Type*} (f : ι → (X ⟶ Y)) (s : Finset ι) :
    (s.sum f).hom = s.sum fun i => (f i).hom :=
  (forget V G).map_sum f s

end Preadditive

section Linear

variable [Preadditive V] {R : Type*} [Semiring R] [Linear R V]

/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**Action.forget_linear** 是 Mathlib 中的一个定理，位于命名空间 `Action`。
形式化陈述：∀ {V : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} V] {G : Type u
_2} [inst_1 : Monoid G]   [inst_2 : CategoryTheory.Preadditive V] {R : Type u_3}
 [inst_3 : Semiring R] [inst_4 : CategoryTheory.Linear R V],   CategoryTheory.Fu
nctor.Linear R (Action.forget V G)
参数：Action.forget V G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance forget_linear : Functor.Linear R (forget V G) where
/-
**Action.forget** 是 Mathlib 中的一个定义，位于命名空间 `Action`。
形式化陈述：forget : Action V G ⥤ V where obj M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance forget₂_linear {FV : V → V → Type*} {CV : V → Type*}
    [∀ X Y, FunLike (FV X Y) (CV X) (CV Y)] [ConcreteCategory V FV] :
    Functor.Linear R (forget₂ (Action V G) V) where
/-
**Action.functorCategoryEquivalence_linear** 是 Mathlib 中的一个定理，位于命名空间 `Action`。
形式化陈述：∀ {V : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} V] {G : Type u
_2} [inst_1 : Monoid G]   [inst_2 : CategoryTheory.Preadditive V] {R : Type u_3}
 [inst_3 : Semiring R] [inst_4 : CategoryTheory.Linear R V],   CategoryTheory.Fu
nctor.Linear R (Action.functorCategoryEquivalence V G).functor
参数：Action.functorCategoryEquivalence V G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance functorCategoryEquivalence_linear :
    Functor.Linear R (functorCategoryEquivalence V G).functor where

@[simp]
/-
**Action.smul_hom** 是 Mathlib 中的一个定理，位于命名空间 `Action`。
形式化陈述：smul_hom {X Y : Action V G} (r : R) (f : X ⟶ Y) : (r • f).hom = r • f.hom
参数：r : R；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_hom {X Y : Action V G} (r : R) (f : X ⟶ Y) : (r • f).hom = r • f.hom :=
  rfl

variable {H : Type*} [Monoid H] (f : G →* H)
/-
**Action.res_additive** 是 Mathlib 中的一个定理，位于命名空间 `Action`。
形式化陈述：∀ {V : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} V] {G : Type u
_2} [inst_1 : Monoid G]   [inst_2 : CategoryTheory.Preadditive V] {H : Type u_4}
 [inst_3 : Monoid H] (f : G →* H), (Action.res V f).Additive
参数：f : G →* H；Action.res V f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance res_additive : (res V f).Additive where
/-
**Action.res_linear** 是 Mathlib 中的一个定理，位于命名空间 `Action`。
形式化陈述：∀ {V : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} V] {G : Type u
_2} [inst_1 : Monoid G]   [inst_2 : CategoryTheory.Preadditive V] {R : Type u_3}
 [inst_3 : Semiring R] [inst_4 : CategoryTheory.Linear R V]   {H : Type u_4} [in
st_5 : Monoid H] (f : G →* H), CategoryTheory.Functor.Linear R (Action.res V f)
参数：f : G →* H；Action.res V f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance res_linear : (res V f).Linear R where

end Linear

section Abelian

/-- Auxiliary construction for the `Abelian (Action V G)` instance. -/
/-
**Action.abelianAux** 是 Mathlib 中的一个定义，位于命名空间 `Action`。
形式化陈述：abelianAux : Action V G ≌ (SingleObj G) ⥤ V
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary construction for the `Abelian (Action V G)` instance.
-/
def abelianAux : Action V G ≌ (SingleObj G) ⥤ V :=
  functorCategoryEquivalence V G
/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [Abelian V] : Abelian (Action V G) :=
  abelianOfEquivalence abelianAux.functor

end Abelian

end Action

namespace CategoryTheory.Functor

variable {W : Type*} [Category* W] (F : V ⥤ W) (G : Type*) [Monoid G] [Preadditive V]
  [Preadditive W]

/-
**CategoryTheory.Functor.mapAction_preadditive** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Functor`。
形式化陈述：∀ {V : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} V] {W : Type u
_3}   [inst_1 : CategoryTheory.Category.{v_2, u_3} W] (F : CategoryTheory.Functo
r V W) (G : Type u_4) [inst_2 : Monoid G]   [inst_3 : CategoryTheory.Preadditive
 V] [inst_4 : CategoryTheory.Preadditive W] [F.Additive], (F.mapAction G).Additi
ve
参数：F : CategoryTheory.Functor V W；G : Type u_4；F.mapAction G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Action.hom_ext`：hom_ext {M N : Action V G} (φ₁ φ₂ : M ⟶ N) (h : φ₁.hom =
 φ₂.hom) : φ₁ = φ₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Functor.mapAction_map_hom`：∀ {V : Type u_1} [inst : Categ
oryTheory.Category.{v_1, u_1} V] {W : Type u_2}   [inst_1 : CategoryTheory.Categ
ory.{v_2, u_2} W] (F : Categor…
· 使用定理 `CategoryTheory.Functor.map_add`：map_add {X Y : C} {f g : X ⟶ Y} : F.map 
(f + g) = F.map f + F.map g
-/
instance mapAction_preadditive [F.Additive] : (F.mapAction G).Additive where

variable {R : Type*} [Semiring R] [CategoryTheory.Linear R V] [CategoryTheory.Linear R W]
/-
**CategoryTheory.Functor.mapAction_linear** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Functor`。
形式化陈述：∀ {V : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} V] {W : Type u
_3}   [inst_1 : CategoryTheory.Category.{v_2, u_3} W] (F : CategoryTheory.Functo
r V W) (G : Type u_4) [inst_2 : Monoid G]   [inst_3 : CategoryTheory.Preadditive
 V] [inst_4 : CategoryTheory.Preadditive W] {R : Type u_5} [inst_5 : Semiring R]
   [inst_6 : CategoryTheory.Linear R V] [inst_7 : CategoryTheory.Linear R W] [Ca
tegoryTheory.Functor.Linear R F],   CategoryTheory.Functor.Linear R (F.mapAction
 G)
参数：F : CategoryTheory.Functor V W；G : Type u_4；F.mapAction G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Action.hom_ext`：hom_ext {M N : Action V G} (φ₁ φ₂ : M ⟶ N) (h : φ₁.hom =
 φ₂.hom) : φ₁ = φ₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Functor.mapAction_map_hom`：∀ {V : Type u_1} [inst : Categ
oryTheory.Category.{v_1, u_1} V] {W : Type u_2}   [inst_1 : CategoryTheory.Categ
ory.{v_2, u_2} W] (F : Categor…
· 使用定理 `CategoryTheory.Functor.map_smul`：map_smul {X Y : C} (r : R) (f : X ⟶ Y) 
: F.map (r • f) = r • F.map f
-/
instance mapAction_linear [F.Linear R] : (F.mapAction G).Linear R where

end CategoryTheory.Functor

