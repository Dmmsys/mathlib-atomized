/-
Copyright (c) 2025 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster, Dagur Asgeirsson, Emily Riehl
-/
module

public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
public import Mathlib.CategoryTheory.Limits.Final

/-!
# Existence of conical limits

This file contains different statements about the (non-constructive) existence of conical limits.

The main constructions are the following.

- `HasConicalLimit`: there exists a conical limit for `F : J ⥤ C`.
- `HasConicalLimitsOfShape J`: All functors `F : J ⥤ C` have conical limits.
- `HasConicalLimitsOfSize.{v₁, u₁}`: For all small `J` all functors `F : J ⥤ C` have conical limits.
- `HasConicalLimits`: `C` has all (small) conical limits.

## References

* [Kelly G.M., *Basic concepts of enriched category theory*][kelly2005]:
  See section 3.8 for a similar treatment, although the content of this file is not directly
  adapted from there.

## Implementation notes

`V` has been made an `(V : outParam <| Type u')` in the classes below as it seems instance
inference prefers this. Otherwise it failed with
`cannot find synthesization order` on the instances below.
However, it is not fully clear yet whether this could lead to potential issues, for example
if there are multiple `MonoidalCategory _` instances in scope.
-/

public section

universe v₁ u₁ v₂ u₂ w v' v u u'

namespace CategoryTheory.Enriched

open Limits

section Definitions

variable {J : Type u₁} [Category.{v₁} J]
variable (V : outParam <| Type u') [Category.{v'} V] [MonoidalCategory V]
variable (C : Type u) [Category.{v} C] [EnrichedOrdinaryCategory V C]

variable {C} in
/--
`HasConicalLimit F` represents the mere existence of a conical limit for `F`.
-/
/-
**CategoryTheory.Enriched.HasConicalLimit** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheo
ry.Enriched`。
形式化陈述：HasConicalLimit (F : J ⥤ C) : Prop extends HasLimit F where preservesLimit
_eCoyoneda (X : C) : PreservesLimit F (eCoyoneda V X)
参数：F : J ⥤ C。
继承自：HasLimit F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`HasConicalLimit F` represents the mere existence of a conical limit for `F`.
-/
class HasConicalLimit (F : J ⥤ C) : Prop extends HasLimit F where
  preservesLimit_eCoyoneda (X : C) : PreservesLimit F (eCoyoneda V X) := by infer_instance

attribute [instance] HasConicalLimit.preservesLimit_eCoyoneda

variable (J) in
/--
`C` has conical limits of shape `J` if there exists a conical limit for every functor `F : J ⥤ C`.
-/
/-
**CategoryTheory.Enriched.HasConicalLimitsOfShape** 是 Mathlib 中的一个类，位于命名空间 `Cate
goryTheory.Enriched`。
形式化陈述：HasConicalLimitsOfShape : Prop where /-- All functors `F : J ⥤ C` from `J`
 have limits. -/ hasConicalLimit : forall F : J ⥤ C, HasConicalLimit V F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`C` has conical limits of shape `J` if there exists a conical limit for every fu
nctor `F : J ⥤ C`.
-/
class HasConicalLimitsOfShape : Prop where
  /-- All functors `F : J ⥤ C` from `J` have limits. -/
  hasConicalLimit : ∀ F : J ⥤ C, HasConicalLimit V F := by infer_instance

attribute [instance] HasConicalLimitsOfShape.hasConicalLimit

/--
`C` has all conical limits of size `v₁ u₁` (`HasLimitsOfSize.{v₁ u₁} C`)
if it has conical limits of every shape `J : Type u₁` with `[Category.{v₁} J]`.
-/
-- After https://github.com/leanprover/lean4/pull/12286 and
-- https://github.com/leanprover/lean4/pull/12423, the shape universes `v₁, u₁` would default
-- to universe output parameters. See Note [universe output parameters and typeclass caching].
@[univ_out_params, pp_with_univ]
/-
**CategoryTheory.Enriched.HasConicalLimitsOfSize** 是 Mathlib 中的一个类，位于命名空间 `Categ
oryTheory.Enriched`。
形式化陈述：HasConicalLimitsOfSize : Prop where /-- All functors `F : J ⥤ C` from all 
small `J` have conical limits -/ hasConicalLimitsOfShape : forall (J : Type u₁) 
[Category.{v₁} J], HasConicalLimitsOfShape J V C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
class HasConicalLimitsOfSize : Prop where
  /-- All functors `F : J ⥤ C` from all small `J` have conical limits -/
  hasConicalLimitsOfShape : ∀ (J : Type u₁) [Category.{v₁} J], HasConicalLimitsOfShape J V C := by
    infer_instance

attribute [instance] HasConicalLimitsOfSize.hasConicalLimitsOfShape

/-- `C` has all (small) conical limits if it has limits of every shape that is as big as its
hom-sets. -/
/-
**CategoryTheory.Enriched.HasConicalLimits** 是 Mathlib 中的一个缩写定义，位于命名空间 `Category
Theory.Enriched`。
形式化陈述：HasConicalLimits : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`C` has all (small) conical limits if it has limits of every shape that is as bi
g as its
hom-sets.
-/
abbrev HasConicalLimits : Prop := HasConicalLimitsOfSize.{v, v} V C

end Definitions

section Results

variable {J : Type u₁} [Category.{v₁} J] {J' : Type u₂} [Category.{v₂} J']
variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]
variable {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory V C]

/-- ensure existence of a conical limit implies existence of a limit -/
/-
**CategoryTheory.Enriched.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Enriched`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
ensure existence of a conical limit implies existence of a limit
-/
example (F : J ⥤ C) [HasConicalLimit V F] : HasLimit F := inferInstance

/-- If a functor `F` has a conical limit, so does any naturally isomorphic functor. -/
/-
**CategoryTheory.Enriched.HasConicalLimit.of_iso** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Enriched.HasConicalLimit`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] (V : Type u') 
[inst_1 : CategoryTheory.Category.{v', u'} V]   [inst_2 : CategoryTheory.Monoida
lCategory V] {C : Type u} [inst_3 : CategoryTheory.Category.{v, u} C]   [inst_4 
: CategoryTheory.EnrichedOrdinaryCategory V C] {F G : CategoryTheory.Functor J C
}   [CategoryTheory.Enriched.HasConicalLimit V F] (e : F ≅ G), CategoryTheory.En
riched.HasConicalLimit V G
参数：V : Type u'；e : F ≅ G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimit_of_iso`：hasLimit_of_iso {F G : J ⥤ C} [Ha
sLimit F] (α : F ≅ G) : HasLimit G
· 使用定理 `CategoryTheory.Enriched.HasConicalLimit.toHasLimit`：∀ {J : Type u₁} {ins
t : CategoryTheory.Category.{v₁, u₁} J} {V : outParam (Type u')}   {inst_1 : Cat
egoryTheory.Category.{v', u'} V} {inst_2…
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_iso_diagram`：preservesLimit_of_i
so_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [PreservesLimit K₁ F] : Pre
servesLimit K₂ F where preserves {c} t
· 使用定理 `CategoryTheory.Enriched.HasConicalLimit.preservesLimit_eCoyoneda`：∀ {J :
 Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} J} {V : outParam (Type u')}  
 {inst_1 : CategoryTheory.Category.{v', u'} V} {inst_2…

--- 原说明 ---
If a functor `F` has a conical limit, so does any naturally isomorphic functor.
-/
lemma HasConicalLimit.of_iso {F G : J ⥤ C} [HasConicalLimit V F] (e : F ≅ G) :
    HasConicalLimit V G where
  toHasLimit := hasLimit_of_iso e
  preservesLimit_eCoyoneda X := preservesLimit_of_iso_diagram (eCoyoneda V X) e
/-
**CategoryTheory.Enriched.HasConicalLimit.of_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Enriched.HasConicalLimit`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {J' : Type u₂}
   [inst_1 : CategoryTheory.Category.{v₂, u₂} J'] (V : Type u') [inst_2 : Catego
ryTheory.Category.{v', u'} V]   [inst_3 : CategoryTheory.MonoidalCategory V] {C 
: Type u} [inst_4 : CategoryTheory.Category.{v, u} C]   [inst_5 : CategoryTheory
.EnrichedOrdinaryCategory V C] (F : CategoryTheory.Functor J C)   [CategoryTheor
y.Enriched.HasConicalLimit V F] (G : CategoryTheory.Functor J' J) [G.IsEquivalen
ce],   CategoryTheory.Enriched.HasConicalLimit V (G.comp F)
参数：V : Type u'；F : CategoryTheory.Functor J C；G : CategoryTheory.Functor J' J；G.
comp F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Initial.comp_hasLimit`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.initial_of_isLeftAdjoint`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cate
gory.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.isLeftAdjoint_of_isEquivalence`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Enriched.HasConicalLimit.toHasLimit`：∀ {J : Type u₁} {ins
t : CategoryTheory.Category.{v₁, u₁} J} {V : outParam (Type u')}   {inst_1 : Cat
egoryTheory.Category.{v', u'} V} {inst_2…
· 使用定理 `CategoryTheory.Functor.Initial.comp_preservesLimit`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.C
ategory.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Enriched.HasConicalLimit.preservesLimit_eCoyoneda`：∀ {J :
 Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} J} {V : outParam (Type u')}  
 {inst_1 : CategoryTheory.Category.{v', u'} V} {inst_2…
-/
instance HasConicalLimit.of_equiv (F : J ⥤ C) [HasConicalLimit V F]
    (G : J' ⥤ J) [G.IsEquivalence] : HasConicalLimit V (G ⋙ F) where

/-- If a `G ⋙ F` has a limit, and `G` is an equivalence, we can construct a limit of `F`. -/
/-
**CategoryTheory.Enriched.HasConicalLimit.of_equiv_comp** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Enriched.HasConicalLimit`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {J' : Type u₂}
   [inst_1 : CategoryTheory.Category.{v₂, u₂} J'] (V : Type u') [inst_2 : Catego
ryTheory.Category.{v', u'} V]   [inst_3 : CategoryTheory.MonoidalCategory V] {C 
: Type u} [inst_4 : CategoryTheory.Category.{v, u} C]   [inst_5 : CategoryTheory
.EnrichedOrdinaryCategory V C] (F : CategoryTheory.Functor J C)   (G : CategoryT
heory.Functor J' J) [G.IsEquivalence] [CategoryTheory.Enriched.HasConicalLimit V
 (G.comp F)],   CategoryTheory.Enriched.HasConicalLimit V F
参数：V : Type u'；F : CategoryTheory.Functor J C；G : CategoryTheory.Functor J' J；G.
comp F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Enriched.HasConicalLimit.of_iso`：∀ {J : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} J] (V : Type u') [inst_1 : CategoryTheory.Categ
ory.{v', u'} V]   [inst_2 : Category…
· 使用定理 `CategoryTheory.Enriched.HasConicalLimit.of_equiv`：∀ {J : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} J] {J' : Type u₂}   [inst_1 : CategoryTheory.
Category.{v₂, u₂} J'] (V : Type u') [i…

--- 原说明 ---
If a `G ⋙ F` has a limit, and `G` is an equivalence, we can construct a limit of
 `F`.
-/
lemma HasConicalLimit.of_equiv_comp (F : J ⥤ C) (G : J' ⥤ J) [G.IsEquivalence]
    [HasConicalLimit V (G ⋙ F)] : HasConicalLimit V F :=
  have e : G.inv ⋙ G ⋙ F ≅ F := G.asEquivalence.invFunIdAssoc F
  HasConicalLimit.of_iso V e

variable (C)

variable (J) in
/-- existence of conical limits (of shape) implies existence of limits (of shape) -/
/-
**CategoryTheory.Enriched.HasConicalLimitsOfShape.hasLimitsOfShape** 是 Mathlib 中
的一个定理，位于命名空间 `CategoryTheory.Enriched.HasConicalLimitsOfShape`。
形式化陈述：∀ (J : Type u₁) [inst : CategoryTheory.Category.{v₁, u₁} J] (V : Type u') 
[inst_1 : CategoryTheory.Category.{v', u'} V]   [inst_2 : CategoryTheory.Monoida
lCategory V] (C : Type u) [inst_3 : CategoryTheory.Category.{v, u} C]   [inst_4 
: CategoryTheory.EnrichedOrdinaryCategory V C] [CategoryTheory.Enriched.HasConic
alLimitsOfShape J V C],   CategoryTheory.Limits.HasLimitsOfShape J C
参数：J : Type u₁；V : Type u'；C : Type u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Enriched.HasConicalLimit.toHasLimit`：∀ {J : Type u₁} {ins
t : CategoryTheory.Category.{v₁, u₁} J} {V : outParam (Type u')}   {inst_1 : Cat
egoryTheory.Category.{v', u'} V} {inst_2…
· 使用定理 `CategoryTheory.Enriched.HasConicalLimitsOfShape.hasConicalLimit`：∀ {J : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} J} {V : outParam (Type u')}   
{inst_1 : CategoryTheory.Category.{v', u'} V} {inst_2…

--- 原说明 ---
existence of conical limits (of shape) implies existence of limits (of shape)
-/
instance HasConicalLimitsOfShape.hasLimitsOfShape [HasConicalLimitsOfShape J V C] :
    HasLimitsOfShape J C where

/-- We can transport conical limits of shape `J'` along an equivalence `J' ≌ J`. -/
/-
**CategoryTheory.Enriched.HasConicalLimitsOfShape.of_equiv** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Enriched.HasConicalLimitsOfShape`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {J' : Type u₂}
   [inst_1 : CategoryTheory.Category.{v₂, u₂} J'] (V : Type u') [inst_2 : Catego
ryTheory.Category.{v', u'} V]   [inst_3 : CategoryTheory.MonoidalCategory V] (C 
: Type u) [inst_4 : CategoryTheory.Category.{v, u} C]   [inst_5 : CategoryTheory
.EnrichedOrdinaryCategory V C] [CategoryTheory.Enriched.HasConicalLimitsOfShape 
J' V C]   (G : CategoryTheory.Functor J' J) [G.IsEquivalence], CategoryTheory.En
riched.HasConicalLimitsOfShape J V C
参数：V : Type u'；C : Type u；G : CategoryTheory.Functor J' J。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Enriched.HasConicalLimit.of_equiv_comp`：∀ {J : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} J] {J' : Type u₂}   [inst_1 : CategoryTh
eory.Category.{v₂, u₂} J'] (V : Type u') [i…
· 使用定理 `CategoryTheory.Enriched.HasConicalLimitsOfShape.hasConicalLimit`：∀ {J : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} J} {V : outParam (Type u')}   
{inst_1 : CategoryTheory.Category.{v', u'} V} {inst_2…

--- 原说明 ---
We can transport conical limits of shape `J'` along an equivalence `J' ≌ J`.
-/
lemma HasConicalLimitsOfShape.of_equiv [HasConicalLimitsOfShape J' V C]
    (G : J' ⥤ J) [G.IsEquivalence] : HasConicalLimitsOfShape J V C where
  hasConicalLimit F := HasConicalLimit.of_equiv_comp V F G

/-- existence of conical limits (of size) implies existence of limits (of size) -/
/-
**CategoryTheory.Enriched.HasConicalLimitsOfSize.hasLimitsOfSize** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.Enriched.HasConicalLimitsOfSize`。
形式化陈述：∀ (V : Type u') [inst : CategoryTheory.Category.{v', u'} V] [inst_1 : Cate
goryTheory.MonoidalCategory V] (C : Type u)   [inst_2 : CategoryTheory.Category.
{v, u} C] [inst_3 : CategoryTheory.EnrichedOrdinaryCategory V C]   [CategoryTheo
ry.Enriched.HasConicalLimitsOfSize.{v₁, u₁, v', v, u, u'} V C],   CategoryTheory
.Limits.HasLimitsOfSize.{v₁, u₁, v, u} C
参数：V : Type u'；C : Type u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Enriched.HasConicalLimitsOfShape.hasLimitsOfShape`：∀ (J :
 Type u₁) [inst : CategoryTheory.Category.{v₁, u₁} J] (V : Type u') [inst_1 : Ca
tegoryTheory.Category.{v', u'} V]   [inst_2 : Category…
· 使用定理 `CategoryTheory.Enriched.HasConicalLimitsOfSize.hasConicalLimitsOfShape`：
∀ {V : outParam (Type u')} {inst : CategoryTheory.Category.{v', u'} V} {inst_1 :
 CategoryTheory.MonoidalCategory V}   {C : Type u} {inst_2 :…

--- 原说明 ---
existence of conical limits (of size) implies existence of limits (of size)
-/
instance HasConicalLimitsOfSize.hasLimitsOfSize [HasConicalLimitsOfSize.{v₁, u₁} V C] :
    HasLimitsOfSize.{v₁, u₁} C where

/-- ensure existence of (small) conical limits implies existence of (small) limits -/
/-
**CategoryTheory.Enriched.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Enriched`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
ensure existence of (small) conical limits implies existence of (small) limits
-/
example [HasConicalLimits V C] : HasLimits C := inferInstance

end Results

end CategoryTheory.Enriched

