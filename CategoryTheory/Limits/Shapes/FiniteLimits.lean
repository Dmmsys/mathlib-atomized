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
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback  -- shake: keep (`example`)
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
/-- A category has all finite limits if every functor `J ⥤ C` with a `FinCategory J`
instance and `J : Type` has a limit.

This is often called 'finitely complete'.
-/
/-
**CategoryTheory.Limits.HasFiniteLimits** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：(C : Type u) → [CategoryTheory.Category.{v, u} C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category has all finite limits if every functor `J ⥤ C` with a `FinCategory J`
instance and `J : Type` has a limit.

This is often called 'finitely complete'.
-/
class HasFiniteLimits : Prop where
  /-- `C` has all limits over any type `J` whose objects and morphisms lie in the same universe
  and which has `FinType` objects and morphisms -/
  out (J : Type) [𝒥 : SmallCategory J] [@FinCategory J 𝒥] : @HasLimitsOfShape J 𝒥 C _
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) hasLimitsOfShape_of_hasFiniteLimits [HasFiniteLimits C] (J : Type w)
    [SmallCategory J] [FinCategory J] : HasLimitsOfShape J C := by
  apply @hasLimitsOfShape_of_equivalence _ _ _ _ _ _ (FinCategory.equivAsType J) ?_
  apply HasFiniteLimits.out
/-
**CategoryTheory.Limits.hasFiniteLimits_of_hasLimitsOfSize** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Limits`。
形式化陈述：hasFiniteLimits_of_hasLimitsOfSize [HasLimitsOfSize.{v', u'} C] : HasFinit
eLimits C where out
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_equivalence`：hasLimitsOfShape_
of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J') [HasLimitsOfShape 
J C] : HasLimitsOfShape J' C
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasLimitsOfSize`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTh
eory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.hasLimitsOfSizeShrink`：hasLimitsOfSizeShrink [HasL
imitsOfSize.{max v₁ v₂, max u₁ u₂} C] : HasLimitsOfSize.{v₁, u₁} C
-/
lemma hasFiniteLimits_of_hasLimitsOfSize [HasLimitsOfSize.{v', u'} C] :
    HasFiniteLimits C where
  out := fun J hJ hJ' =>
    haveI := hasLimitsOfSizeShrink.{0, 0} C
    let F := @FinCategory.equivAsType J (@FinCategory.fintypeObj J hJ hJ') hJ hJ'
    @hasLimitsOfShape_of_equivalence (@FinCategory.AsType J (@FinCategory.fintypeObj J hJ hJ'))
    (@FinCategory.categoryAsType J (@FinCategory.fintypeObj J hJ hJ') hJ hJ') _ _ J hJ F _

/-- If `C` has all limits, it has finite limits. -/
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `C` has all limits, it has finite limits.
-/
instance (priority := 100) hasFiniteLimits_of_hasLimits [HasLimits C] : HasFiniteLimits C :=
  hasFiniteLimits_of_hasLimitsOfSize C
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 90) hasFiniteLimits_of_hasLimitsOfSize₀ [HasLimitsOfSize.{0, 0} C] :
    HasFiniteLimits C :=
  hasFiniteLimits_of_hasLimitsOfSize C
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (J : Type) [hJ : SmallCategory J] : Category (ULiftHom (ULift J)) :=
  (@ULiftHom.category (ULift J) (@uliftCategory J hJ))

/-- We can always derive `HasFiniteLimits C` by providing limits at an
arbitrary universe. -/
/-
**CategoryTheory.Limits.hasFiniteLimits_of_hasFiniteLimits_of_size** 是 Mathlib 中
的一个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：hasFiniteLimits_of_hasFiniteLimits_of_size (h : forall (J : Type w) {𝒥 : S
mallCategory J} (_ : @FinCategory J 𝒥), HasLimitsOfShape J C) : HasFiniteLimits 
C where out
参数：h : forall (J : Type w) {𝒥 : SmallCategory J} (_ : @FinCategory J 𝒥), HasLimi
tsOfShape J C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_equivalence`：hasLimitsOfShape_
of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J') [HasLimitsOfShape 
J C] : HasLimitsOfShape J' C

--- 原说明 ---
We can always derive `HasFiniteLimits C` by providing limits at an
arbitrary universe.
-/
theorem hasFiniteLimits_of_hasFiniteLimits_of_size
    (h : ∀ (J : Type w) {𝒥 : SmallCategory J} (_ : @FinCategory J 𝒥), HasLimitsOfShape J C) :
    HasFiniteLimits C where
  out := fun J hJ hhJ => by
    have := h (ULiftHom.{w} (ULift.{w} J)) <| @CategoryTheory.finCategoryUlift J hJ hhJ
    have l : @Equivalence J (ULiftHom (ULift J)) hJ
                          (@ULiftHom.category (ULift J) (@uliftCategory J hJ)) :=
      @ULiftHomULiftCategory.equiv J hJ
    apply @hasLimitsOfShape_of_equivalence (ULiftHom (ULift J))
      (@ULiftHom.category (ULift J) (@uliftCategory J hJ)) C _ J hJ l.symm _

/-- A category has all finite colimits if every functor `J ⥤ C` with a `FinCategory J`
instance and `J : Type` has a colimit.

This is often called 'finitely cocomplete'.
-/
/-
**CategoryTheory.Limits.HasFiniteColimits** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：(C : Type u) → [CategoryTheory.Category.{v, u} C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category has all finite colimits if every functor `J ⥤ C` with a `FinCategory 
J`
instance and `J : Type` has a colimit.

This is often called 'finitely cocomplete'.
-/
class HasFiniteColimits : Prop where
  /-- `C` has all colimits over any type `J` whose objects and morphisms lie in the same universe
  and which has `Fintype` objects and morphisms -/
  out (J : Type) [𝒥 : SmallCategory J] [@FinCategory J 𝒥] : @HasColimitsOfShape J 𝒥 C _

-- See note [instance argument order]
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) hasColimitsOfShape_of_hasFiniteColimits [HasFiniteColimits C]
    (J : Type w) [SmallCategory J] [FinCategory J] : HasColimitsOfShape J C := by
  refine @hasColimitsOfShape_of_equivalence _ _ _ _ _ _ (FinCategory.equivAsType J) ?_
  apply HasFiniteColimits.out
/-
**CategoryTheory.Limits.hasFiniteColimits_of_hasColimitsOfSize** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：hasFiniteColimits_of_hasColimitsOfSize [HasColimitsOfSize.{v', u'} C] : Ha
sFiniteColimits C where out
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_equivalence`：hasColimitsOfSh
ape_of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J') [HasColimitsOf
Shape J C] : HasColimitsOfShape J' C
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.hasColimitsOfSizeShrink`：hasColimitsOfSizeShrink [
HasColimitsOfSize.{max v₁ v₂, max u₁ u₂} C] : HasColimitsOfSize.{v₁, u₁} C
-/
lemma hasFiniteColimits_of_hasColimitsOfSize [HasColimitsOfSize.{v', u'} C] :
    HasFiniteColimits C where
  out := fun J hJ hJ' =>
    haveI := hasColimitsOfSizeShrink.{0, 0} C
    let F := @FinCategory.equivAsType J (@FinCategory.fintypeObj J hJ hJ') hJ hJ'
    @hasColimitsOfShape_of_equivalence (@FinCategory.AsType J (@FinCategory.fintypeObj J hJ hJ'))
    (@FinCategory.categoryAsType J (@FinCategory.fintypeObj J hJ hJ') hJ hJ') _ _ J hJ F _
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) hasFiniteColimits_of_hasColimits [HasColimits C] : HasFiniteColimits C :=
  hasFiniteColimits_of_hasColimitsOfSize C
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 90) hasFiniteColimits_of_hasColimitsOfSize₀ [HasColimitsOfSize.{0, 0} C] :
    HasFiniteColimits C :=
  hasFiniteColimits_of_hasColimitsOfSize C

/-- We can always derive `HasFiniteColimits C` by providing colimits at an
arbitrary universe. -/
/-
**CategoryTheory.Limits.hasFiniteColimits_of_hasFiniteColimits_of_size** 是 Mathl
ib 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：hasFiniteColimits_of_hasFiniteColimits_of_size (h : forall (J : Type w) {𝒥
 : SmallCategory J} (_ : @FinCategory J 𝒥), HasColimitsOfShape J C) : HasFiniteC
olimits C where out
参数：h : forall (J : Type w) {𝒥 : SmallCategory J} (_ : @FinCategory J 𝒥), HasColi
mitsOfShape J C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_equivalence`：hasColimitsOfSh
ape_of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J') [HasColimitsOf
Shape J C] : HasColimitsOfShape J' C

--- 原说明 ---
We can always derive `HasFiniteColimits C` by providing colimits at an
arbitrary universe.
-/
theorem hasFiniteColimits_of_hasFiniteColimits_of_size
    (h : ∀ (J : Type w) {𝒥 : SmallCategory J} (_ : @FinCategory J 𝒥), HasColimitsOfShape J C) :
    HasFiniteColimits C where
  out := fun J hJ hhJ => by
    have := h (ULiftHom.{w} (ULift.{w} J)) <| @CategoryTheory.finCategoryUlift J hJ hhJ
    have l : @Equivalence J (ULiftHom (ULift J)) hJ
                           (@ULiftHom.category (ULift J) (@uliftCategory J hJ)) :=
      @ULiftHomULiftCategory.equiv J hJ
    apply @hasColimitsOfShape_of_equivalence (ULiftHom (ULift J))
      (@ULiftHom.category (ULift J) (@uliftCategory J hJ)) C _ J hJ
      (@Equivalence.symm J hJ (ULiftHom (ULift J))
      (@ULiftHom.category (ULift J) (@uliftCategory J hJ)) l) _

section

open WalkingParallelPair WalkingParallelPairHom

/-
**CategoryTheory.Limits.fintypeWalkingParallelPair** 是 Mathlib 中的一个实例，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：fintypeWalkingParallelPair : Fintype WalkingParallelPair where elems
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fintypeWalkingParallelPair : Fintype WalkingParallelPair where
  elems := [WalkingParallelPair.zero, WalkingParallelPair.one].toFinset
  complete x := by cases x <;> simp

attribute [local aesop safe cases] WalkingParallelPair WalkingParallelPairHom
/-
**CategoryTheory.Limits.instFintypeWalkingParallelPairHom** 是 Mathlib 中的一个实例，位于命
名空间 `CategoryTheory.Limits`。
形式化陈述：instFintypeWalkingParallelPairHom (j j' : WalkingParallelPair) : Fintype (
WalkingParallelPairHom j j') where elems
参数：j j' : WalkingParallelPair。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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

/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FinCategory WalkingParallelPair where
  fintypeObj := fintypeWalkingParallelPair
  fintypeHom := instFintypeWalkingParallelPairHom

/-- Equalizers are finite limits, so if `C` has all finite limits, it also has all equalizers -/
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equalizers are finite limits, so if `C` has all finite limits, it also has all e
qualizers
-/
example [HasFiniteLimits C] : HasEqualizers C := by infer_instance

/-- Coequalizers are finite colimits, of if `C` has all finite colimits, it also has all
coequalizers -/
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coequalizers are finite colimits, of if `C` has all finite colimits, it also has
 all
coequalizers
-/
example [HasFiniteColimits C] : HasCoequalizers C := by infer_instance

variable {J : Type v}

-- Porting note: we would like to write something like:
-- attribute [local aesop safe cases] WidePullbackShape WidePushoutShape
-- But aesop can't add a `cases` attribute to type synonyms.

namespace WidePullbackShape

/-
**CategoryTheory.Limits.WidePullbackShape.fintypeObj** 是 Mathlib 中的一个实例，位于命名空间 `
CategoryTheory.Limits.WidePullbackShape`。
形式化陈述：fintypeObj [Fintype J] : Fintype (WidePullbackShape J)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fintypeObj [Fintype J] : Fintype (WidePullbackShape J) :=
  inferInstanceAs <| Fintype (Option _)
/-
**CategoryTheory.Limits.WidePullbackShape.fintypeHom** 是 Mathlib 中的一个实例，位于命名空间 `
CategoryTheory.Limits.WidePullbackShape`。
形式化陈述：fintypeHom (j j' : WidePullbackShape J) : Fintype (j ⟶ j') where elems
参数：j j' : WidePullbackShape J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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

/-
**CategoryTheory.Limits.WidePushoutShape.fintypeObj** 是 Mathlib 中的一个实例，位于命名空间 `C
ategoryTheory.Limits.WidePushoutShape`。
形式化陈述：fintypeObj [Fintype J] : Fintype (WidePushoutShape J)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fintypeObj [Fintype J] : Fintype (WidePushoutShape J) :=
  inferInstanceAs <| Fintype (Option _)
/-
**CategoryTheory.Limits.WidePushoutShape.fintypeHom** 是 Mathlib 中的一个实例，位于命名空间 `C
ategoryTheory.Limits.WidePushoutShape`。
形式化陈述：fintypeHom (j j' : WidePushoutShape J) : Fintype (j ⟶ j') where elems
参数：j j' : WidePushoutShape J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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

/-
**CategoryTheory.Limits.finCategoryWidePullback** 是 Mathlib 中的一个实例，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：finCategoryWidePullback [Fintype J] : FinCategory (WidePullbackShape J) wh
ere fintypeHom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance finCategoryWidePullback [Fintype J] : FinCategory (WidePullbackShape J) where
  fintypeHom := WidePullbackShape.fintypeHom
/-
**CategoryTheory.Limits.finCategoryWidePushout** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：finCategoryWidePushout [Fintype J] : FinCategory (WidePushoutShape J) wher
e fintypeHom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance finCategoryWidePushout [Fintype J] : FinCategory (WidePushoutShape J) where
  fintypeHom := WidePushoutShape.fintypeHom

-- We can't just made this an `abbrev`
-- because of https://github.com/leanprover-community/lean/issues/429
/-- A category `HasFiniteWidePullbacks` if it has all limits of shape `WidePullbackShape J` for
finite `J`, i.e. if it has a wide pullback for every finite collection of morphisms with the same
codomain. -/
/-
**CategoryTheory.Limits.HasFiniteWidePullbacks** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：(C : Type u) → [CategoryTheory.Category.{v, u} C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category `HasFiniteWidePullbacks` if it has all limits of shape `WidePullbackS
hape J` for
finite `J`, i.e. if it has a wide pullback for every finite collection of morphi
sms with the same
codomain.
-/
class HasFiniteWidePullbacks : Prop where
  /-- `C` has all wide pullbacks for any Finite `J` -/
  out (J : Type) [Finite J] : HasLimitsOfShape (WidePullbackShape J) C
/-
**CategoryTheory.Limits.hasLimitsOfShape_widePullbackShape** 是 Mathlib 中的一个实例，位于
命名空间 `CategoryTheory.Limits`。
形式化陈述：hasLimitsOfShape_widePullbackShape (J : Type) [Finite J] [HasFiniteWidePul
lbacks C] : HasLimitsOfShape (WidePullbackShape J) C
参数：J : Type。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasFiniteWidePullbacks.out`：∀ {C : Type u} {inst :
 CategoryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasFiniteWidePu
llbacks C]   (J : Type) [Finite J], Ca…
-/
instance hasLimitsOfShape_widePullbackShape (J : Type) [Finite J] [HasFiniteWidePullbacks C] :
    HasLimitsOfShape (WidePullbackShape J) C := by
  have := @HasFiniteWidePullbacks.out C _ _ J
  infer_instance

/-- A category `HasFiniteWidePushouts` if it has all colimits of shape `WidePushoutShape J` for
finite `J`, i.e. if it has a wide pushout for every finite collection of morphisms with the same
domain. -/
/-
**CategoryTheory.Limits.HasFiniteWidePushouts** 是 Mathlib 中的一个归纳类型，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：(C : Type u) → [CategoryTheory.Category.{v, u} C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category `HasFiniteWidePushouts` if it has all colimits of shape `WidePushoutS
hape J` for
finite `J`, i.e. if it has a wide pushout for every finite collection of morphis
ms with the same
domain.
-/
class HasFiniteWidePushouts : Prop where
  /-- `C` has all wide pushouts for any Finite `J` -/
  out (J : Type) [Finite J] : HasColimitsOfShape (WidePushoutShape J) C
/-
**CategoryTheory.Limits.hasColimitsOfShape_widePushoutShape** 是 Mathlib 中的一个实例，位
于命名空间 `CategoryTheory.Limits`。
形式化陈述：hasColimitsOfShape_widePushoutShape (J : Type) [Finite J] [HasFiniteWidePu
shouts C] : HasColimitsOfShape (WidePushoutShape J) C
参数：J : Type。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasFiniteWidePushouts.out`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasFiniteWidePus
houts C]   (J : Type) [Finite J], Cat…
-/
instance hasColimitsOfShape_widePushoutShape (J : Type) [Finite J] [HasFiniteWidePushouts C] :
    HasColimitsOfShape (WidePushoutShape J) C := by
  have := @HasFiniteWidePushouts.out C _ _ J
  infer_instance

/-- Finite wide pullbacks are finite limits, so if `C` has all finite limits,
it also has finite wide pullbacks
-/
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Finite wide pullbacks are finite limits, so if `C` has all finite limits,
it also has finite wide pullbacks
-/
instance (priority := 900) hasFiniteWidePullbacks_of_hasFiniteLimits [HasFiniteLimits C] :
    HasFiniteWidePullbacks C :=
  ⟨fun J _ => by cases nonempty_fintype J; exact HasFiniteLimits.out _⟩

/-- Finite wide pushouts are finite colimits, so if `C` has all finite colimits,
it also has finite wide pushouts
-/
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Finite wide pushouts are finite colimits, so if `C` has all finite colimits,
it also has finite wide pushouts
-/
instance (priority := 900) hasFiniteWidePushouts_of_has_finite_limits [HasFiniteColimits C] :
    HasFiniteWidePushouts C :=
  ⟨fun J _ => by cases nonempty_fintype J; exact HasFiniteColimits.out _⟩
/-
**CategoryTheory.Limits.fintypeWalkingPair** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：fintypeWalkingPair : Fintype WalkingPair where elems
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fintypeWalkingPair : Fintype WalkingPair where
  elems := {WalkingPair.left, WalkingPair.right}
  complete x := by cases x <;> simp

/-- Pullbacks are finite limits, so if `C` has all finite limits, it also has all pullbacks -/
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pullbacks are finite limits, so if `C` has all finite limits, it also has all pu
llbacks
-/
example [HasFiniteWidePullbacks C] : HasPullbacks C := by infer_instance

/-- Pushouts are finite colimits, so if `C` has all finite colimits, it also has all pushouts -/
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pushouts are finite colimits, so if `C` has all finite colimits, it also has all
 pushouts
-/
example [HasFiniteWidePushouts C] : HasPushouts C := by infer_instance

end CategoryTheory.Limits

