/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.FinCategory.AsType
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback -- shake: keep (`example`)
public import Mathlib.Data.Fintype.Option

/-!
# Categories with finite limits.

A typeclass for categories with all finite (co)limits.
-/

public section


universe w' w v' u' v u

noncomputable section

open CategoryTheory

namespace CategoryTheory.Limits

variable (C : Type u) [Category.{v} C]

-- We can't just made this an `abbrev`
-- because of https://github.com/leanprover-community/lean/issues/429
/--
Definition of `HasFiniteLimits` / `HasFiniteLimits` 的定义

English:
class HasFiniteLimits
  parameters: : Prop where
  axioms and operations (1):
    - out((J : Type) [𝒥 : SmallCategory J] [@FinCategory J 𝒥]) : @HasLimitsOfShape J 𝒥 C _

中文:
类 有有限极限
  参数: : 命题 where
  公理与运算 (1 个):
    - out((J : 类型) [𝒥 : 小范畴 J] [@有限范畴 J 𝒥]) : @有形状极限 J 𝒥 C _
-/
class HasFiniteLimits : Prop where
  /-- `C` has all limits over any type `J` whose objects and morphisms lie in the same universe
  and which has `FinType` objects and morphisms -/
  out (J : Type) [𝒥 : SmallCategory J] [@FinCategory J 𝒥] : @HasLimitsOfShape J 𝒥 C _

instance (priority := 100) hasLimitsOfShape_of_hasFiniteLimits [HasFiniteLimits C] (J : Type w)
    [SmallCategory J] [FinCategory J] : HasLimitsOfShape J C := by
  apply @hasLimitsOfShape_of_equivalence _ _ _ _ _ _ (FinCategory.equivAsType J) ?_
  apply HasFiniteLimits.out

/--
lemma `hasFiniteLimits_of_hasLimitsOfSize` / 引理 `hasFiniteLimits_of_hasLimitsOfSize`

English:
lemma hasFiniteLimits_of_hasLimitsOfSize
  given: [HasLimitsOfSize.{v', u'} C]
  proof: fun J hJ hJ' =>
    haveI := hasLimitsOfSizeShrink.{0, 0} C
    let F := @FinCategory.equivAsType J (@FinCategory.fintypeObj J hJ hJ') hJ hJ'
    @hasLimitsOfShape_of_equivalence (@FinCategory.AsType J (@FinCategory.fintypeObj J hJ hJ'))
    (@FinCategory.categoryAsType J (@FinCategory.fintypeObj J 

中文:
引理 hasFiniteLimits_of_hasLimitsOfSize
  条件: [有LimitsOfSize.{v', u'} C]
  证明: fun J hJ hJ' =>
    haveI := hasLimitsOfSizeShrink.{0, 0} C
    let F := @FinCategory.equivAsType J (@FinCategory.fintypeObj J hJ hJ') hJ hJ'
    @hasLimitsOfShape_of_equivalence (@FinCategory.AsType J (@FinCategory.fintypeObj J hJ hJ'))
    (@FinCategory.categoryAsType J (@FinCategory.fintypeObj J 
-/
lemma hasFiniteLimits_of_hasLimitsOfSize [HasLimitsOfSize.{v', u'} C] :
    HasFiniteLimits C where
  out := fun J hJ hJ' =>
    haveI := hasLimitsOfSizeShrink.{0, 0} C
    let F := @FinCategory.equivAsType J (@FinCategory.fintypeObj J hJ hJ') hJ hJ'
    @hasLimitsOfShape_of_equivalence (@FinCategory.AsType J (@FinCategory.fintypeObj J hJ hJ'))
    (@FinCategory.categoryAsType J (@FinCategory.fintypeObj J hJ hJ') hJ hJ') _ _ J hJ F _

/-- If `C` has all limits, it has finite limits. -/
instance (priority := 100) hasFiniteLimits_of_hasLimits [HasLimits C] : HasFiniteLimits C :=
  hasFiniteLimits_of_hasLimitsOfSize C

instance (priority := 90) hasFiniteLimits_of_hasLimitsOfSize₀ [HasLimitsOfSize.{0, 0} C] :
    HasFiniteLimits C :=
  hasFiniteLimits_of_hasLimitsOfSize C

instance (J : Type) [hJ : SmallCategory J] : Category (ULiftHom (ULift J)) :=
  (@ULiftHom.category (ULift J) (@uliftCategory J hJ))

/--
theorem `hasFiniteLimits_of_hasFiniteLimits_of_size` / 定理 `hasFiniteLimits_of_hasFiniteLimits_of_size`

English:
theorem hasFiniteLimits_of_hasFiniteLimits_of_size
  proof: fun J hJ hhJ => by
have := h (ULiftHom.{w} (ULift.{w} J)) @CategoryTheory.finCategoryUlift J hJ hhJ
    have l : @Equivalence J (ULiftHom (ULift J)) hJ
                          (@ULiftHom.category (ULift J) (@uliftCategory J hJ)) :=
      @ULiftHomULiftCategory.equiv J hJ
    apply @hasLimitsOfShap

中文:
定理 hasFiniteLimits_of_hasFiniteLimits_of_size
  证明: fun J hJ hhJ => by
have := h (ULiftHom.{w} (ULift.{w} J)) @CategoryTheory.finCategoryUlift J hJ hhJ
    have l : @Equivalence J (ULiftHom (ULift J)) hJ
                          (@ULiftHom.category (ULift J) (@uliftCategory J hJ)) :=
      @ULiftHomULiftCategory.equiv J hJ
    apply @hasLimitsOfShap

Depends on / 依赖: CategoryTheory, CategoryTheory.finCategoryUlift, Equivalence, ULiftHom, ULiftHom.category, ULiftHomULiftCategory, ULiftHomULiftCategory.equiv, category, finCategoryUlift, hasLimitsOfShape_of_equivalence, l.symm, uliftCategory
-/
theorem hasFiniteLimits_of_hasFiniteLimits_of_size
    (h : forall (J : Type w) {𝒥 : SmallCategory J} (_ : @FinCategory J 𝒥), HasLimitsOfShape J C) :
    HasFiniteLimits C where
  out := fun J hJ hhJ => by
have := h (ULiftHom.{w} (ULift.{w} J)) @CategoryTheory.finCategoryUlift J hJ hhJ
    have l : @Equivalence J (ULiftHom (ULift J)) hJ
                          (@ULiftHom.category (ULift J) (@uliftCategory J hJ)) :=
      @ULiftHomULiftCategory.equiv J hJ
    apply @hasLimitsOfShape_of_equivalence (ULiftHom (ULift J))
      (@ULiftHom.category (ULift J) (@uliftCategory J hJ)) C _ J hJ l.symm _

/--
Definition of `HasFiniteColimits` / `HasFiniteColimits` 的定义

English:
class HasFiniteColimits
  parameters: : Prop where
  axioms and operations (1):
    - out((J : Type) [𝒥 : SmallCategory J] [@FinCategory J 𝒥]) : @HasColimitsOfShape J 𝒥 C _

中文:
类 有有限余极限
  参数: : 命题 where
  公理与运算 (1 个):
    - out((J : 类型) [𝒥 : 小范畴 J] [@有限范畴 J 𝒥]) : @有形状余极限 J 𝒥 C _
-/
class HasFiniteColimits : Prop where
  /-- `C` has all colimits over any type `J` whose objects and morphisms lie in the same universe
  and which has `Fintype` objects and morphisms -/
  out (J : Type) [𝒥 : SmallCategory J] [@FinCategory J 𝒥] : @HasColimitsOfShape J 𝒥 C _

-- See note [instance argument order]
instance (priority := 100) hasColimitsOfShape_of_hasFiniteColimits [HasFiniteColimits C]
    (J : Type w) [SmallCategory J] [FinCategory J] : HasColimitsOfShape J C := by
  refine @hasColimitsOfShape_of_equivalence _ _ _ _ _ _ (FinCategory.equivAsType J) ?_
  apply HasFiniteColimits.out

/--
lemma `hasFiniteColimits_of_hasColimitsOfSize` / 引理 `hasFiniteColimits_of_hasColimitsOfSize`

English:
lemma hasFiniteColimits_of_hasColimitsOfSize
  given: [HasColimitsOfSize.{v', u'} C]
  proof: fun J hJ hJ' =>
    haveI := hasColimitsOfSizeShrink.{0, 0} C
    let F := @FinCategory.equivAsType J (@FinCategory.fintypeObj J hJ hJ') hJ hJ'
    @hasColimitsOfShape_of_equivalence (@FinCategory.AsType J (@FinCategory.fintypeObj J hJ hJ'))
    (@FinCategory.categoryAsType J (@FinCategory.fintypeOb

中文:
引理 hasFiniteColimits_of_hasColimitsOfSize
  条件: [有余limitsOfSize.{v', u'} C]
  证明: fun J hJ hJ' =>
    haveI := hasColimitsOfSizeShrink.{0, 0} C
    let F := @FinCategory.equivAsType J (@FinCategory.fintypeObj J hJ hJ') hJ hJ'
    @hasColimitsOfShape_of_equivalence (@FinCategory.AsType J (@FinCategory.fintypeObj J hJ hJ'))
    (@FinCategory.categoryAsType J (@FinCategory.fintypeOb
-/
lemma hasFiniteColimits_of_hasColimitsOfSize [HasColimitsOfSize.{v', u'} C] :
    HasFiniteColimits C where
  out := fun J hJ hJ' =>
    haveI := hasColimitsOfSizeShrink.{0, 0} C
    let F := @FinCategory.equivAsType J (@FinCategory.fintypeObj J hJ hJ') hJ hJ'
    @hasColimitsOfShape_of_equivalence (@FinCategory.AsType J (@FinCategory.fintypeObj J hJ hJ'))
    (@FinCategory.categoryAsType J (@FinCategory.fintypeObj J hJ hJ') hJ hJ') _ _ J hJ F _

instance (priority := 100) hasFiniteColimits_of_hasColimits [HasColimits C] : HasFiniteColimits C :=
  hasFiniteColimits_of_hasColimitsOfSize C

instance (priority := 90) hasFiniteColimits_of_hasColimitsOfSize₀ [HasColimitsOfSize.{0, 0} C] :
    HasFiniteColimits C :=
  hasFiniteColimits_of_hasColimitsOfSize C

/--
theorem `hasFiniteColimits_of_hasFiniteColimits_of_size` / 定理 `hasFiniteColimits_of_hasFiniteColimits_of_size`

English:
theorem hasFiniteColimits_of_hasFiniteColimits_of_size
  proof: fun J hJ hhJ => by
have := h (ULiftHom.{w} (ULift.{w} J)) @CategoryTheory.finCategoryUlift J hJ hhJ
    have l : @Equivalence J (ULiftHom (ULift J)) hJ
                           (@ULiftHom.category (ULift J) (@uliftCategory J hJ)) :=
      @ULiftHomULiftCategory.equiv J hJ
    apply @hasColimitsOfS

中文:
定理 hasFiniteColimits_of_hasFiniteColimits_of_size
  证明: fun J hJ hhJ => by
have := h (ULiftHom.{w} (ULift.{w} J)) @CategoryTheory.finCategoryUlift J hJ hhJ
    have l : @Equivalence J (ULiftHom (ULift J)) hJ
                           (@ULiftHom.category (ULift J) (@uliftCategory J hJ)) :=
      @ULiftHomULiftCategory.equiv J hJ
    apply @hasColimitsOfS

Depends on / 依赖: CategoryTheory, CategoryTheory.finCategoryUlift, Equivalence, Equivalence.symm, ULiftHom, ULiftHom.category, ULiftHomULiftCategory, ULiftHomULiftCategory.equiv, category, finCategoryUlift, hasColimitsOfShape_of_equivalence, uliftCategory
-/
theorem hasFiniteColimits_of_hasFiniteColimits_of_size
    (h : forall (J : Type w) {𝒥 : SmallCategory J} (_ : @FinCategory J 𝒥), HasColimitsOfShape J C) :
    HasFiniteColimits C where
  out := fun J hJ hhJ => by
have := h (ULiftHom.{w} (ULift.{w} J)) @CategoryTheory.finCategoryUlift J hJ hhJ
    have l : @Equivalence J (ULiftHom (ULift J)) hJ
                           (@ULiftHom.category (ULift J) (@uliftCategory J hJ)) :=
      @ULiftHomULiftCategory.equiv J hJ
    apply @hasColimitsOfShape_of_equivalence (ULiftHom (ULift J))
      (@ULiftHom.category (ULift J) (@uliftCategory J hJ)) C _ J hJ
      (@Equivalence.symm J hJ (ULiftHom (ULift J))
      (@ULiftHom.category (ULift J) (@uliftCategory J hJ)) l) _

section

open WalkingParallelPair WalkingParallelPairHom

/--
Instance `fintypeWalkingParallelPair` / 实例 `fintypeWalkingParallelPair`

English:
instance fintypeWalkingParallelPair
  signature: : Fintype WalkingParallelPair where
  body: [WalkingParallelPair.zero, WalkingParallelPair.one].toFinset
  complete x := by cases x <;> simp

中文:
实例 fintypeWalkingParallelPair
  签名: : 有限类型 WalkingParallelPair where
  定义体: [WalkingParallelPair.zero, WalkingParallelPair.one].toFinset
  complete x := by cases x <;> simp

Depends on / 依赖: WalkingParallelPair, WalkingParallelPair.one, WalkingParallelPair.zero, toFinset
-/
instance fintypeWalkingParallelPair : Fintype WalkingParallelPair where
  elems := [WalkingParallelPair.zero, WalkingParallelPair.one].toFinset
  complete x := by cases x <;> simp

attribute [local aesop safe cases] WalkingParallelPair WalkingParallelPairHom

/--
Instance `instFintypeWalkingParallelPairHom` / 实例 `instFintypeWalkingParallelPairHom`

English:
instance instFintypeWalkingParallelPairHom
  signature: (j j' : WalkingParallelPair)
  body: WalkingParallelPair.recOn j
      (WalkingParallelPair.recOn j' [WalkingParallelPairHom.id zero].toFinset
        [left, right].toFinset)
      (WalkingParallelPair.recOn j' ∅ [WalkingParallelPairHom.id one].toFinset)
  complete := by aesop

中文:
实例 instFintypeWalkingParallelPairHom
  签名: (j j' : WalkingParallelPair)
  定义体: WalkingParallelPair.recOn j
      (WalkingParallelPair.recOn j' [WalkingParallelPairHom.id zero].toFinset
        [left, right].toFinset)
      (WalkingParallelPair.recOn j' ∅ [WalkingParallelPairHom.id one].toFinset)
  complete := by aesop

Depends on / 依赖: WalkingParallelPair, WalkingParallelPair.recOn, WalkingParallelPairHom, WalkingParallelPairHom.id, complete, toFinset
-/
instance instFintypeWalkingParallelPairHom (j j' : WalkingParallelPair) :
    Fintype (WalkingParallelPairHom j j') where
  elems :=
    WalkingParallelPair.recOn j
      (WalkingParallelPair.recOn j' [WalkingParallelPairHom.id zero].toFinset
        [left, right].toFinset)
      (WalkingParallelPair.recOn j' ∅ [WalkingParallelPairHom.id one].toFinset)
  complete := by aesop
end

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FinCategory WalkingParallelPair
  body: fintypeWalkingParallelPair
  fintypeHom := instFintypeWalkingParallelPairHom

中文:
实例 :
  签名: 有限范畴 WalkingParallelPair
  定义体: fintypeWalkingParallelPair
  fintypeHom := instFintypeWalkingParallelPairHom

Depends on / 依赖: fintypeWalkingParallelPair
-/
instance : FinCategory WalkingParallelPair where
  fintypeObj := fintypeWalkingParallelPair
  fintypeHom := instFintypeWalkingParallelPairHom

/-- Equalizers are finite limits, so if `C` has all finite limits, it also has all equalizers -/
example [HasFiniteLimits C] : HasEqualizers C := by infer_instance

/-- Coequalizers are finite colimits, of if `C` has all finite colimits, it also has all
coequalizers -/
example [HasFiniteColimits C] : HasCoequalizers C := by infer_instance

variable {J : Type v}

-- Porting note: we would like to write something like:
-- attribute [local aesop safe cases] WidePullbackShape WidePushoutShape
-- But aesop can't add a `cases` attribute to type synonyms.

namespace WidePullbackShape

/--
Instance `fintypeObj` / 实例 `fintypeObj`

English:
instance fintypeObj
  signature: [Fintype J]
  body: inferInstanceAs Fintype (Option _)

中文:
实例 fintypeObj
  签名: [有限类型 J]
  定义体: inferInstanceAs Fintype (Option _)

Depends on / 依赖: Fintype
-/
instance fintypeObj [Fintype J] : Fintype (WidePullbackShape J) :=
inferInstanceAs Fintype (Option _)

/--
Instance `fintypeHom` / 实例 `fintypeHom`

English:
instance fintypeHom
  signature: (j j' : WidePullbackShape J)
  body: by
    obtain - | j' := j'
    · obtain - | j := j
      · exact {Hom.id none}
      · exact {Hom.term j}
    · by_cases h : some j' = j
      · rw [h]
        exact {Hom.id j}
      · exact ∅
  complete := by
    rintro (_ | _)
    · cases j <;> simp
    · simp

中文:
实例 fintypeHom
  签名: (j j' : WidePullbackShape J)
  定义体: by
    obtain - | j' := j'
    · obtain - | j := j
      · exact {Hom.id none}
      · exact {Hom.term j}
    · by_cases h : some j' = j
      · rw [h]
        exact {Hom.id j}
      · exact ∅
  complete := by
    rintro (_ | _)
    · cases j <;> simp
    · simp

Depends on / 依赖: Hom.id, Hom.term, complete
-/
instance fintypeHom (j j' : WidePullbackShape J) : Fintype (j ⟶ j') where
  elems := by
    obtain - | j' := j'
    · obtain - | j := j
      · exact {Hom.id none}
      · exact {Hom.term j}
    · by_cases h : some j' = j
      · rw [h]
        exact {Hom.id j}
      · exact ∅
  complete := by
    rintro (_ | _)
    · cases j <;> simp
    · simp

end WidePullbackShape

namespace WidePushoutShape

/--
Instance `fintypeObj` / 实例 `fintypeObj`

English:
instance fintypeObj
  signature: [Fintype J]
  body: inferInstanceAs Fintype (Option _)

中文:
实例 fintypeObj
  签名: [有限类型 J]
  定义体: inferInstanceAs Fintype (Option _)

Depends on / 依赖: Fintype
-/
instance fintypeObj [Fintype J] : Fintype (WidePushoutShape J) :=
inferInstanceAs Fintype (Option _)

/--
Instance `fintypeHom` / 实例 `fintypeHom`

English:
instance fintypeHom
  signature: (j j' : WidePushoutShape J)
  body: by
    obtain - | j := j
    · obtain - | j' := j'
      · exact {Hom.id none}
      · exact {Hom.init j'}
    · by_cases h : some j = j'
      · rw [h]
        exact {Hom.id j'}
      · exact ∅
  complete := by
    rintro (_ | _)
    · cases j <;> simp
    · simp

中文:
实例 fintypeHom
  签名: (j j' : WidePushoutShape J)
  定义体: by
    obtain - | j := j
    · obtain - | j' := j'
      · exact {Hom.id none}
      · exact {Hom.init j'}
    · by_cases h : some j = j'
      · rw [h]
        exact {Hom.id j'}
      · exact ∅
  complete := by
    rintro (_ | _)
    · cases j <;> simp
    · simp

Depends on / 依赖: Hom.id, Hom.init, complete
-/
instance fintypeHom (j j' : WidePushoutShape J) : Fintype (j ⟶ j') where
  elems := by
    obtain - | j := j
    · obtain - | j' := j'
      · exact {Hom.id none}
      · exact {Hom.init j'}
    · by_cases h : some j = j'
      · rw [h]
        exact {Hom.id j'}
      · exact ∅
  complete := by
    rintro (_ | _)
    · cases j <;> simp
    · simp

end WidePushoutShape

/--
Instance `finCategoryWidePullback` / 实例 `finCategoryWidePullback`

English:
instance finCategoryWidePullback
  signature: [Fintype J]
  body: WidePullbackShape.fintypeHom

中文:
实例 finCategoryWidePullback
  签名: [有限类型 J]
  定义体: WidePullbackShape.fintypeHom

Depends on / 依赖: WidePullbackShape, WidePullbackShape.fintypeHom, fintypeHom
-/
instance finCategoryWidePullback [Fintype J] : FinCategory (WidePullbackShape J) where
  fintypeHom := WidePullbackShape.fintypeHom

/--
Instance `finCategoryWidePushout` / 实例 `finCategoryWidePushout`

English:
instance finCategoryWidePushout
  signature: [Fintype J]
  body: WidePushoutShape.fintypeHom

中文:
实例 finCategoryWidePushout
  签名: [有限类型 J]
  定义体: WidePushoutShape.fintypeHom

Depends on / 依赖: WidePushoutShape, WidePushoutShape.fintypeHom, fintypeHom
-/
instance finCategoryWidePushout [Fintype J] : FinCategory (WidePushoutShape J) where
  fintypeHom := WidePushoutShape.fintypeHom

-- We can't just made this an `abbrev`
-- because of https://github.com/leanprover-community/lean/issues/429
/--
Definition of `HasFiniteWidePullbacks` / `HasFiniteWidePullbacks` 的定义

English:
class HasFiniteWidePullbacks
  parameters: : Prop where
  axioms and operations (1):
    - out((J : Type) [Finite J]) : HasLimitsOfShape (WidePullbackShape J) C

中文:
类 有FiniteWidePullbacks
  参数: : 命题 where
  公理与运算 (1 个):
    - out((J : 类型) [有限 J]) : 有形状极限 (WidePullbackShape J) C
-/
class HasFiniteWidePullbacks : Prop where
  /-- `C` has all wide pullbacks for any Finite `J` -/
  out (J : Type) [Finite J] : HasLimitsOfShape (WidePullbackShape J) C

/--
Instance `hasLimitsOfShape_widePullbackShape` / 实例 `hasLimitsOfShape_widePullbackShape`

English:
instance hasLimitsOfShape_widePullbackShape
  signature: (J : Type) [Finite J] [HasFiniteWidePullbacks C]
  body: by
  have := @HasFiniteWidePullbacks.out C _ _ J
  infer_instance

中文:
实例 hasLimitsOfShape_widePullbackShape
  签名: (J : 类型) [有限 J] [有FiniteWidePullbacks C]
  定义体: by
  have := @HasFiniteWidePullbacks.out C _ _ J
  infer_instance

Depends on / 依赖: HasFiniteWidePullbacks, HasFiniteWidePullbacks.out, infer_instance
-/
instance hasLimitsOfShape_widePullbackShape (J : Type) [Finite J] [HasFiniteWidePullbacks C] :
    HasLimitsOfShape (WidePullbackShape J) C := by
  have := @HasFiniteWidePullbacks.out C _ _ J
  infer_instance

/--
Definition of `HasFiniteWidePushouts` / `HasFiniteWidePushouts` 的定义

English:
class HasFiniteWidePushouts
  parameters: : Prop where
  axioms and operations (1):
    - out((J : Type) [Finite J]) : HasColimitsOfShape (WidePushoutShape J) C

中文:
类 有FiniteWidePushouts
  参数: : 命题 where
  公理与运算 (1 个):
    - out((J : 类型) [有限 J]) : 有形状余极限 (WidePushoutShape J) C
-/
class HasFiniteWidePushouts : Prop where
  /-- `C` has all wide pushouts for any Finite `J` -/
  out (J : Type) [Finite J] : HasColimitsOfShape (WidePushoutShape J) C

/--
Instance `hasColimitsOfShape_widePushoutShape` / 实例 `hasColimitsOfShape_widePushoutShape`

English:
instance hasColimitsOfShape_widePushoutShape
  signature: (J : Type) [Finite J] [HasFiniteWidePushouts C]
  body: by
  have := @HasFiniteWidePushouts.out C _ _ J
  infer_instance

中文:
实例 hasColimitsOfShape_widePushoutShape
  签名: (J : 类型) [有限 J] [有FiniteWidePushouts C]
  定义体: by
  have := @HasFiniteWidePushouts.out C _ _ J
  infer_instance

Depends on / 依赖: HasFiniteWidePushouts, HasFiniteWidePushouts.out, infer_instance
-/
instance hasColimitsOfShape_widePushoutShape (J : Type) [Finite J] [HasFiniteWidePushouts C] :
    HasColimitsOfShape (WidePushoutShape J) C := by
  have := @HasFiniteWidePushouts.out C _ _ J
  infer_instance

/-- Finite wide pullbacks are finite limits, so if `C` has all finite limits,
it also has finite wide pullbacks
-/
instance (priority := 900) hasFiniteWidePullbacks_of_hasFiniteLimits [HasFiniteLimits C] :
    HasFiniteWidePullbacks C :=
  ⟨fun J _ => by cases nonempty_fintype J; exact HasFiniteLimits.out _⟩

/-- Finite wide pushouts are finite colimits, so if `C` has all finite colimits,
it also has finite wide pushouts
-/
instance (priority := 900) hasFiniteWidePushouts_of_has_finite_limits [HasFiniteColimits C] :
    HasFiniteWidePushouts C :=
  ⟨fun J _ => by cases nonempty_fintype J; exact HasFiniteColimits.out _⟩

/--
Instance `fintypeWalkingPair` / 实例 `fintypeWalkingPair`

English:
instance fintypeWalkingPair
  signature: : Fintype WalkingPair where
  body: {WalkingPair.left, WalkingPair.right}
  complete x := by cases x <;> simp

中文:
实例 fintypeWalkingPair
  签名: : 有限类型 WalkingPair where
  定义体: {WalkingPair.left, WalkingPair.right}
  complete x := by cases x <;> simp

Depends on / 依赖: WalkingPair, WalkingPair.left, WalkingPair.right
-/
instance fintypeWalkingPair : Fintype WalkingPair where
  elems := {WalkingPair.left, WalkingPair.right}
  complete x := by cases x <;> simp

/-- Pullbacks are finite limits, so if `C` has all finite limits, it also has all pullbacks -/
example [HasFiniteWidePullbacks C] : HasPullbacks C := by infer_instance

/-- Pushouts are finite colimits, so if `C` has all finite colimits, it also has all pushouts -/
example [HasFiniteWidePushouts C] : HasPushouts C := by infer_instance

end CategoryTheory.Limits
