/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.ConeCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Localization.Adjunction
public import Mathlib.CategoryTheory.Localization.HasLocalization
public import Mathlib.CategoryTheory.Localization.Pi
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-! # The localized category has finite products

In this file, it is shown that if `L : C ⥤ D` is
a localization functor for `W : MorphismProperty C` and that
`W` is stable under finite products, then `D` has finite
products, and `L` preserves finite products.

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits CategoryTheory.Functor

namespace Localization

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] (L : C ⥤ D)
  (W : MorphismProperty C) [L.IsLocalization W]

namespace HasProductsOfShapeAux

variable (J : Type) [HasProductsOfShape J C] [W.IsStableUnderProductsOfShape J]

/-
**CategoryTheory.Localization.HasProductsOfShapeAux.inverts** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Localization.HasProductsOfShapeAux`。
形式化陈述：inverts : (W.functorCategory (Discrete J)).IsInvertedBy (lim ⋙ L)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用定理 `CategoryTheory.MorphismProperty.limMap`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {W : CategoryTheory.MorphismProperty C} {J : Type u_1} 
  [inst_1 : CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
lemma inverts :
    (W.functorCategory (Discrete J)).IsInvertedBy (lim ⋙ L) :=
  fun _ _ f hf => Localization.inverts L W _ (MorphismProperty.limMap f hf)

variable [W.ContainsIdentities] [Finite J]

/-- The (candidate) limit functor for the localized category.
It is induced by `lim ⋙ L : (Discrete J ⥤ C) ⥤ D`. -/
/-
**CategoryTheory.Localization.HasProductsOfShapeAux.limitFunctor** 是 Mathlib 中的一
个缩写定义，位于命名空间 `CategoryTheory.Localization.HasProductsOfShapeAux`。
形式化陈述：limitFunctor : (Discrete J ⥤ D) ⥤ D
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Localization.HasProductsOfShapeAux.inverts`：inverts : (W.
functorCategory (Discrete J)).IsInvertedBy (lim ⋙ L)
· 使用定理 `CategoryTheory.Functor.IsLocalization.instDiscreteObjWhiskeringRightFunc
torCategoryOfFiniteOfContainsIdentities`：∀ {J : Type} [Finite J] {C : Type u₁} {
D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C]   [inst_1 : CategoryThe
ory.Category.{v₂, u₂}…

--- 原说明 ---
The (candidate) limit functor for the localized category.
It is induced by `lim ⋙ L : (Discrete J ⥤ C) ⥤ D`.
-/
noncomputable abbrev limitFunctor :
    (Discrete J ⥤ D) ⥤ D :=
  Localization.lift _ (inverts L W J)
    ((whiskeringRight (Discrete J) C D).obj L)

/-- The functor `limitFunctor L W J` is induced by `lim ⋙ L`. -/
/-
**CategoryTheory.Localization.HasProductsOfShapeAux.compLimitFunctorIso** 是 Math
lib 中的一个定义，位于命名空间 `CategoryTheory.Localization.HasProductsOfShapeAux`。
形式化陈述：compLimitFunctorIso : ((whiskeringRight (Discrete J) C D).obj L) ⋙ limitFu
nctor L W J ≅ lim ⋙ L
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Localization.HasProductsOfShapeAux.inverts`：inverts : (W.
functorCategory (Discrete J)).IsInvertedBy (lim ⋙ L)
· 使用定理 `CategoryTheory.Functor.IsLocalization.instDiscreteObjWhiskeringRightFunc
torCategoryOfFiniteOfContainsIdentities`：∀ {J : Type} [Finite J] {C : Type u₁} {
D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C]   [inst_1 : CategoryThe
ory.Category.{v₂, u₂}…

--- 原说明 ---
The functor `limitFunctor L W J` is induced by `lim ⋙ L`.
-/
noncomputable def compLimitFunctorIso :
    ((whiskeringRight (Discrete J) C D).obj L) ⋙ limitFunctor L W J ≅
      lim ⋙ L := by
  apply Localization.fac
/-
**CategoryTheory.Localization.HasProductsOfShapeAux.** 是 Mathlib 中的一个实例，位于命名空间 `
CategoryTheory.Localization.HasProductsOfShapeAux`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance :
    CatCommSq (Functor.const (Discrete J)) L
      ((whiskeringRight (Discrete J) C D).obj L) (Functor.const (Discrete J)) where
  iso := (Functor.compConstIso _ _).symm
/-
**CategoryTheory.Localization.HasProductsOfShapeAux.** 是 Mathlib 中的一个实例，位于命名空间 `
CategoryTheory.Localization.HasProductsOfShapeAux`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance :
    CatCommSq lim ((whiskeringRight (Discrete J) C D).obj L) L (limitFunctor L W J) where
  iso := (compLimitFunctorIso L W J).symm

/-- The adjunction between the constant functor `D ⥤ (Discrete J ⥤ D)`
and `limitFunctor L W J`. -/
/-
**CategoryTheory.Localization.HasProductsOfShapeAux.adj** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Localization.HasProductsOfShapeAux`。
形式化陈述：adj : Functor.const _ ⊣ limitFunctor L W J
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsLocalization.instDiscreteObjWhiskeringRightFunc
torCategoryOfFiniteOfContainsIdentities`：∀ {J : Type} [Finite J] {C : Type u₁} {
D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C]   [inst_1 : CategoryThe
ory.Category.{v₂, u₂}…

--- 原说明 ---
The adjunction between the constant functor `D ⥤ (Discrete J ⥤ D)`
and `limitFunctor L W J`.
-/
noncomputable def adj :
    Functor.const _ ⊣ limitFunctor L W J :=
  constLimAdj.localization L W ((whiskeringRight (Discrete J) C D).obj L)
    (W.functorCategory (Discrete J)) (Functor.const _) (limitFunctor L W J)
/-
**CategoryTheory.Localization.HasProductsOfShapeAux.adj_counit_app** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.Localization.HasProductsOfShapeAux`。
形式化陈述：adj_counit_app (F : Discrete J ⥤ C) : (adj L W J).counit.app (F ⋙ L) = (Fu
nctor.const (Discrete J)).map ((compLimitFunctorIso L W J).hom.app F) ≫ (Functor
.compConstIso (Discrete J) L).hom.app (lim.obj F) ≫ whiskerRight (constLimAdj.co
unit.app F) L
参数：F : Discrete J ⥤ C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.localization_counit_app`：localization_counit_a
pp (X₂ : C₂) : (adj.localization L₁ W₁ L₂ W₂ G' F').counit.app (L₂.obj X₂) = G'.
map ((CatCommSq.iso F L₂ L₁ F').inv.app…
· 使用定理 `CategoryTheory.Functor.IsLocalization.instDiscreteObjWhiskeringRightFunc
torCategoryOfFiniteOfContainsIdentities`：∀ {J : Type} [Finite J] {C : Type u₁} {
D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C]   [inst_1 : CategoryThe
ory.Category.{v₂, u₂}…
-/
lemma adj_counit_app (F : Discrete J ⥤ C) :
    (adj L W J).counit.app (F ⋙ L) =
      (Functor.const (Discrete J)).map ((compLimitFunctorIso L W J).hom.app F) ≫
        (Functor.compConstIso (Discrete J) L).hom.app (lim.obj F) ≫
        whiskerRight (constLimAdj.counit.app F) L := by
  apply constLimAdj.localization_counit_app

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Auxiliary definition for `Localization.preservesProductsOfShape`. -/
/-
**CategoryTheory.Localization.HasProductsOfShapeAux.isLimitMapCone** 是 Mathlib 中
的一个定义，位于命名空间 `CategoryTheory.Localization.HasProductsOfShapeAux`。
形式化陈述：isLimitMapCone (F : Discrete J ⥤ C) : IsLimit (L.mapCone (limit.cone F))
参数：F : Discrete J ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `Localization.preservesProductsOfShape`.
-/
noncomputable def isLimitMapCone (F : Discrete J ⥤ C) :
    IsLimit (L.mapCone (limit.cone F)) :=
  IsLimit.ofIsoLimit (isLimitConeOfAdj (adj L W J) (F ⋙ L))
    (Cone.ext ((compLimitFunctorIso L W J).app F) (by simp [adj_counit_app, constLimAdj]))

end HasProductsOfShapeAux

variable [W.ContainsIdentities]

include L
/-
**CategoryTheory.Localization.hasProductsOfShape** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Localization`。
形式化陈述：hasProductsOfShape (J : Type) [Finite J] [HasProductsOfShape J C] [W.IsSta
bleUnderProductsOfShape J] : HasProductsOfShape J D
参数：J : Type。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_iff_isLeftAdjoint_const`：hasLimit
sOfShape_iff_isLeftAdjoint_const : HasLimitsOfShape J C ↔ IsLeftAdjoint (const J
 : C ⥤ _)
· 使用引理 `CategoryTheory.Adjunction.isLeftAdjoint`：isLeftAdjoint (adj : F ⊣ G) : F
.IsLeftAdjoint
-/
lemma hasProductsOfShape (J : Type) [Finite J] [HasProductsOfShape J C]
    [W.IsStableUnderProductsOfShape J] :
    HasProductsOfShape J D :=
  hasLimitsOfShape_iff_isLeftAdjoint_const.2
    (HasProductsOfShapeAux.adj L W J).isLeftAdjoint

/-- When `C` has finite products indexed by `J`, `W : MorphismProperty C` contains
identities and is stable under products indexed by `J`,
then any localization functor for `W` preserves finite products indexed by `J`. -/
/-
**CategoryTheory.Localization.preservesProductsOfShape** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Localization`。
形式化陈述：preservesProductsOfShape (J : Type) [Finite J] [HasProductsOfShape J C] [W
.IsStableUnderProductsOfShape J] : PreservesLimitsOfShape (Discrete J) L where p
reservesLimit {F}
参数：J : Type。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone`：preservesL
imit_of_preserves_limit_cone {F : C ⥤ D} {t : Cone K} (h : IsLimit t) (hF : IsLi
mit (F.mapCone t)) : PreservesLimit K F where pres…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…

--- 原说明 ---
When `C` has finite products indexed by `J`, `W : MorphismProperty C` contains
identities and is stable under products indexed by `J`,
then any localization functor for `W` preserves finite products indexed by `J`.
-/
lemma preservesProductsOfShape (J : Type) [Finite J]
    [HasProductsOfShape J C] [W.IsStableUnderProductsOfShape J] :
    PreservesLimitsOfShape (Discrete J) L where
  preservesLimit {F} := preservesLimit_of_preserves_limit_cone (limit.isLimit F)
    (HasProductsOfShapeAux.isLimitMapCone L W J F)

variable [HasFiniteProducts C] [W.IsStableUnderFiniteProducts]

include W in
/-
**CategoryTheory.Localization.hasFiniteProducts** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Localization`。
形式化陈述：hasFiniteProducts : HasFiniteProducts D
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Localization.hasProductsOfShape`：hasProductsOfShape (J : 
Type) [Finite J] [HasProductsOfShape J C] [W.IsStableUnderProductsOfShape J] : H
asProductsOfShape J D
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderFiniteProducts.isStableUnde
rProductsOfShape`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : 
CategoryTheory.MorphismProperty C}   [self : W.IsStableUnderFiniteProducts] (J…
-/
lemma hasFiniteProducts : HasFiniteProducts D :=
  ⟨fun _ => hasProductsOfShape L W _⟩

include W in
/-- When `C` has finite products and `W : MorphismProperty C` contains
identities and is stable under finite products,
then any localization functor for `W` preserves finite products. -/
/-
**CategoryTheory.Localization.preservesFiniteProducts** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Localization`。
形式化陈述：preservesFiniteProducts : PreservesFiniteProducts L where preserves _
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Localization.preservesProductsOfShape`：preservesProductsO
fShape (J : Type) [Finite J] [HasProductsOfShape J C] [W.IsStableUnderProductsOf
Shape J] : PreservesLimitsOfShape (Discret…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderFiniteProducts.isStableUnde
rProductsOfShape`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : 
CategoryTheory.MorphismProperty C}   [self : W.IsStableUnderFiniteProducts] (J…

--- 原说明 ---
When `C` has finite products and `W : MorphismProperty C` contains
identities and is stable under finite products,
then any localization functor for `W` preserves finite products.
-/
lemma preservesFiniteProducts :
    PreservesFiniteProducts L where
  preserves _ := preservesProductsOfShape L W _
/-
**CategoryTheory.Localization.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Localiz
ation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasFiniteProducts (W.Localization) := hasFiniteProducts W.Q W
/-
**CategoryTheory.Localization.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Localiz
ation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : PreservesFiniteProducts W.Q := preservesFiniteProducts W.Q W
/-
**CategoryTheory.Localization.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Localiz
ation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [W.HasLocalization] :
    HasFiniteProducts (W.Localization') :=
  hasFiniteProducts W.Q' W
/-
**CategoryTheory.Localization.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Localiz
ation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [W.HasLocalization] :
    PreservesFiniteProducts W.Q' :=
  preservesFiniteProducts W.Q' W

end Localization

end CategoryTheory

