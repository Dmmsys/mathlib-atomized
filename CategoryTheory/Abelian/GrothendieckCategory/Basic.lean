/-
Copyright (c) 2024 Paul Reichert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Abelian.Subobject
public import Mathlib.CategoryTheory.Abelian.Transfer
public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.Limits.HasLimits

/-!

# Grothendieck categories

This file defines Grothendieck categories and proves basic facts about them.

## Definitions

A Grothendieck category according to the Stacks project is an abelian category provided that it
has `AB5` and a separator. However, this definition is not invariant under equivalences of
categories. Therefore, if `C` is an abelian category, the class `IsGrothendieckAbelian.{w} C` has a
weaker definition that is also satisfied for categories that are merely equivalent to a
Grothendieck category in the former strict sense.

## Theorems

The invariance under equivalences of categories is established in
`IsGrothendieckAbelian.of_equivalence`.

In particular, `ShrinkHoms.isGrothendieckAbelian C` shows that `ShrinkHoms C` satisfies our
definition of a Grothendieck category after shrinking its hom sets, which coincides with the strict
definition in this case.

Relevant implications of `IsGrothendieckAbelian` are established in
`IsGrothendieckAbelian.hasLimits` and `IsGrothendieckAbelian.hasColimits`.

## References

* [Stacks: Grothendieck's AB conditions](https://stacks.math.columbia.edu/tag/079A)

-/

public section

namespace CategoryTheory

open Limits

universe w v u w₂ v₂ u₂
variable (C : Type u) [Category.{v} C] (D : Type u₂) [Category.{v₂} D]

/--
If `C` is an abelian category, we shall say that it satisfies `IsGrothendieckAbelian.{w} C`
if it is locally small (relative to `w`), has exact filtered colimits of size `w` (AB5) and has a
separator.
If `[Category.{v} C]` and `w = v`, this means that `C` satisfies `AB5` and has a separator;
general results about Grothendieck abelian categories can be
reduced to this case using the instance `ShrinkHoms.isGrothendieckAbelian` below.

The introduction of the auxiliary universe `w` shall be needed for certain
applications to categories of sheaves. That the present definition still preserves essential
properties of Grothendieck categories is ensured by `IsGrothendieckAbelian.of_equivalence`,
which shows that every instance for `C` implies an instance for `ShrinkHoms C` with hom sets in
`Type w`.
-/
@[stacks 079B, pp_with_univ]
/-
**CategoryTheory.IsGrothendieckAbelian** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory`
。
形式化陈述：IsGrothendieckAbelian [Abelian C] : Prop where locallySmall : LocallySmall
.{w} C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `C` is an abelian category, we shall say that it satisfies `IsGrothendieckAbe
lian.{w} C`
if it is locally small (relative to `w`), has exact filtered colimits of size `w
` (AB5) and has a
separator.
If `[Category.{v} C]` and `w = v`, this means that `C` satisfies `AB5` and has a
 separator;
general results about Grothendieck abelian categories can be
reduced to this case using the instance `ShrinkHoms.isGrothendieckAbelian` below
.

The introduction of the auxiliary universe `w` shall be needed for certain
applications to categories of sheaves. That the present definition still preserv
es essential
properties of Grothendieck categories is ensured by `IsGrothendieckAbelian.of_eq
uivalence`,
which shows that every instance for `C` implies an instance for `ShrinkHoms C` w
ith hom sets in
`Type w`.
-/
class IsGrothendieckAbelian [Abelian C] : Prop where
  locallySmall : LocallySmall.{w} C := by infer_instance
  hasFilteredColimitsOfSize : HasFilteredColimitsOfSize.{w, w} C := by infer_instance
  ab5OfSize : AB5OfSize.{w, w} C := by infer_instance
  hasSeparator : HasSeparator C := by infer_instance

attribute [instance] IsGrothendieckAbelian.locallySmall
  IsGrothendieckAbelian.hasFilteredColimitsOfSize IsGrothendieckAbelian.ab5OfSize
  IsGrothendieckAbelian.hasSeparator

variable {C} {D} in
/-
**CategoryTheory.IsGrothendieckAbelian.of_equivalence** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.IsGrothendieckAbelian`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u₂} [in
st_1 : CategoryTheory.Category.{v₂, u₂} D]   [inst_2 : CategoryTheory.Abelian C]
 [inst_3 : CategoryTheory.Abelian D]   [CategoryTheory.IsGrothendieckAbelian.{w,
 v, u} C] (α : C ≌ D), CategoryTheory.IsGrothendieckAbelian.{w, v₂, u₂} D
参数：α : C ≌ D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.hasColimitsOfShape_of_equivalence`：hasColimits
OfShape_of_equivalence (E : C ⥤ D) [E.IsEquivalence] [HasColimitsOfShape J D] : 
HasColimitsOfShape J C
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_has_filtered_colimits`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C]   [CategoryTheory.Limits.Has
FilteredColimitsOfSize.{w', w, v, u} C] (I : Type w)   …
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.hasFilteredColimitsOfSize`：∀ {C : T
ype u} {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Abelia
n C}   [self : CategoryTheory.IsGrothendieckAbelian.…
· 使用定理 `CategoryTheory.locallySmall_of_faithful`：locallySmall_of_faithful {C : T
ype u} [Category.{v} C] {D : Type u'} [Category.{v'} D] (F : C ⥤ D) [F.Faithful]
 [LocallySmall.{w} D] : Local…
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.locallySmall`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Abelian C}   [self 
: CategoryTheory.IsGrothendieckAbelian.…
· 使用定理 `CategoryTheory.HasExactColimitsOfShape.of_codomain_equivalence`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] (J : Type u_1) [inst_1 : Catego
ryTheory.Category.{v_1, u_1} J]   {D : Type u_2} [in…
· 使用定理 `CategoryTheory.AB5OfSize.ofShape`：∀ {C : Type u} {inst : CategoryTheory.
Category.{v, u} C}   {inst_1 : CategoryTheory.Limits.HasFilteredColimitsOfSize.{
w, w', v, u} C}   [sel…
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.ab5OfSize`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Abelian C}   [self : C
ategoryTheory.IsGrothendieckAbelian.…
· 使用定理 `CategoryTheory.HasSeparator.of_equivalence`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.
{v₂, u₂} D]   [CategoryTheory.Ha…
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.hasSeparator`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Abelian C}   [self 
: CategoryTheory.IsGrothendieckAbelian.…
-/
theorem IsGrothendieckAbelian.of_equivalence [Abelian C] [Abelian D]
    [IsGrothendieckAbelian.{w} C] (α : C ≌ D) : IsGrothendieckAbelian.{w} D := by
  have hasFilteredColimits : HasFilteredColimitsOfSize.{w, w, v₂, u₂} D :=
    ⟨fun _ _ _ => Adjunction.hasColimitsOfShape_of_equivalence α.inverse⟩
  refine ⟨?_, hasFilteredColimits, ?_, ?_⟩
  · exact locallySmall_of_faithful α.inverse
  · refine ⟨fun _ _ _ => ?_⟩
    exact HasExactColimitsOfShape.of_codomain_equivalence _ α
  · exact HasSeparator.of_equivalence α
/-
**CategoryTheory.ShrinkHoms.isGrothendieckAbelian** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.ShrinkHoms`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Abelian C]   [inst_2 : CategoryTheory.IsGrothendieckAbelian.{w, v, u} C]
,   CategoryTheory.IsGrothendieckAbelian.{w, w, u} (CategoryTheory.ShrinkHoms.{u
} C)
参数：C : Type u；CategoryTheory.ShrinkHoms.{u} C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.of_equivalence`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   [inst_2 : CategoryThe…
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.locallySmall`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Abelian C}   [self 
: CategoryTheory.IsGrothendieckAbelian.…
-/
instance ShrinkHoms.isGrothendieckAbelian [Abelian C] [IsGrothendieckAbelian.{w} C] :
    IsGrothendieckAbelian.{w, w} (ShrinkHoms C) :=
  IsGrothendieckAbelian.of_equivalence <| ShrinkHoms.equivalence C

section Instances

variable [Abelian C] [IsGrothendieckAbelian.{w} C]

/-
**CategoryTheory.IsGrothendieckAbelian.hasColimits** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.IsGrothendieckAbelian`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Abelian C]   [CategoryTheory.IsGrothendieckAbelian.{w, v, u} C], Categor
yTheory.Limits.HasColimitsOfSize.{w, w, v, u} C
参数：C : Type u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.has_colimits_of_finite_and_filtered`：has_colimits_
of_finite_and_filtered [HasFiniteColimits C] [HasFilteredColimitsOfSize.{w, w} C
] : HasColimitsOfSize.{w, w} C
· 使用定理 `CategoryTheory.Abelian.hasFiniteColimits`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.H
asFiniteColimits C
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.hasFilteredColimitsOfSize`：∀ {C : T
ype u} {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Abelia
n C}   [self : CategoryTheory.IsGrothendieckAbelian.…
-/
instance IsGrothendieckAbelian.hasColimits : HasColimitsOfSize.{w, w} C :=
  has_colimits_of_finite_and_filtered
/-
**CategoryTheory.IsGrothendieckAbelian.hasLimits** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.IsGrothendieckAbelian`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Abelian C]   [CategoryTheory.IsGrothendieckAbelian.{w, v, u} C], Categor
yTheory.Limits.HasLimitsOfSize.{w, w, v, u} C
参数：C : Type u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.locallySmall`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Abelian C}   [self 
: CategoryTheory.IsGrothendieckAbelian.…
· 使用定理 `CategoryTheory.Limits.hasLimits_of_hasColimits_of_hasSeparator`：hasLimit
s_of_hasColimits_of_hasSeparator [HasColimits C] [HasSeparator C] [WellPowered.{
v} Cᵒᵖ] : HasLimits C
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.hasColimits`：∀ (C : Type u) [inst :
 CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [Catego
ryTheory.IsGrothendieckAbelian.{w, v, …
· 使用定理 `CategoryTheory.ShrinkHoms.isGrothendieckAbelian`：∀ (C : Type u) [inst : 
CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 
: CategoryTheory.IsGrothendieckAbelia…
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.hasSeparator`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Abelian C}   [self 
: CategoryTheory.IsGrothendieckAbelian.…
· 使用定理 `CategoryTheory.HasSeparator.wellPowered`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] [CategoryTheory.Limits.HasPullbacks C]   [CategoryT
heory.Balanced C] [CategoryTh…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Abelian.hasFiniteLimits`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.Has
FiniteLimits C
· 使用定理 `CategoryTheory.balanced_of_strongMonoCategory`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [CategoryTheory.StrongMonoCategory C],   Categor
yTheory.Balanced C
· 使用定理 `CategoryTheory.strongMonoCategory_of_regularMonoCategory`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheory.IsRegularMonoCateg
ory C],   CategoryTheory.StrongMonoCategory C
· 使用定理 `CategoryTheory.regularMonoCategoryOfNormalMonoCategory`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasZ
eroMorphisms C]   [CategoryTheory.IsNormalMo…
· 使用定理 `CategoryTheory.Abelian.toIsNormalMonoCategory`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryThe
ory.IsNormalMonoCategory C
· 使用定理 `CategoryTheory.Adjunction.has_limits_of_equivalence`：has_limits_of_equiv
alence (E : D ⥤ C) [E.IsEquivalence] [HasLimitsOfSize.{v, u} C] : HasLimitsOfSiz
e.{v, u} D
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
-/
instance IsGrothendieckAbelian.hasLimits : HasLimitsOfSize.{w, w} C :=
  have : HasLimits.{w, u} (ShrinkHoms C) := hasLimits_of_hasColimits_of_hasSeparator
  Adjunction.has_limits_of_equivalence (ShrinkHoms.equivalence C |>.functor)
/-
**CategoryTheory.IsGrothendieckAbelian.wellPowered** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.IsGrothendieckAbelian`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Abelian C]   [inst_2 : CategoryTheory.IsGrothendieckAbelian.{w, v, u} C]
, CategoryTheory.WellPowered.{w, v, u} C
参数：C : Type u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.wellPowered_of_equiv`：wellPowered_of_equiv (e : C ≌ D) [L
ocallySmall.{w} C] [LocallySmall.{w} D] [WellPowered.{w} C] : WellPowered.{w} D
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.locallySmall`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Abelian C}   [self 
: CategoryTheory.IsGrothendieckAbelian.…
· 使用定理 `CategoryTheory.ShrinkHoms.isGrothendieckAbelian`：∀ (C : Type u) [inst : 
CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 
: CategoryTheory.IsGrothendieckAbelia…
· 使用定理 `CategoryTheory.HasSeparator.wellPowered`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] [CategoryTheory.Limits.HasPullbacks C]   [CategoryT
heory.Balanced C] [CategoryTh…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Abelian.hasFiniteLimits`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.Has
FiniteLimits C
· 使用定理 `CategoryTheory.balanced_of_strongMonoCategory`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [CategoryTheory.StrongMonoCategory C],   Categor
yTheory.Balanced C
· 使用定理 `CategoryTheory.strongMonoCategory_of_regularMonoCategory`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheory.IsRegularMonoCateg
ory C],   CategoryTheory.StrongMonoCategory C
· 使用定理 `CategoryTheory.regularMonoCategoryOfNormalMonoCategory`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasZ
eroMorphisms C]   [CategoryTheory.IsNormalMo…
· 使用定理 `CategoryTheory.Abelian.toIsNormalMonoCategory`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryThe
ory.IsNormalMonoCategory C
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.hasSeparator`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Abelian C}   [self 
: CategoryTheory.IsGrothendieckAbelian.…
-/
instance IsGrothendieckAbelian.wellPowered : WellPowered.{w} C :=
  wellPowered_of_equiv.{w} (ShrinkHoms.equivalence.{w} C).symm
/-
**CategoryTheory.IsGrothendieckAbelian.ab4OfSize** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.IsGrothendieckAbelian`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Abelian C]   [inst_2 : CategoryTheory.IsGrothendieckAbelian.{w, v, u} C]
, CategoryTheory.AB4OfSize.{w, v, u} C
参数：C : Type u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadd
itive C]   [CategoryTheory.Limits.HasFiniteProducts …
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasCountableProducts`：∀ (C : 
Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Limits.H
asCountableProducts C],   CategoryTheory.Limits.HasFi…
· 使用定理 `CategoryTheory.Limits.hasCountableProducts_of_hasProducts`：∀ (C : Type u
_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Limits.HasProd
ucts C],   CategoryTheory.Limits.HasCountablePr…
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasLimitsOfSize`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTh
eory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.hasLimits`：∀ (C : Type u) [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [Category
Theory.IsGrothendieckAbelian.{w, v, …
· 使用定理 `CategoryTheory.AB4.of_AB5`：∀ (C : Type u) [inst : CategoryTheory.Categor
y.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   [inst_2 : Cate
goryTheory.Limi…
· 使用定理 `CategoryTheory.Abelian.hasFiniteLimits`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.Has
FiniteLimits C
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.hasFilteredColimitsOfSize`：∀ {C : T
ype u} {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Abelia
n C}   [self : CategoryTheory.IsGrothendieckAbelian.…
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.ab5OfSize`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Abelian C}   [self : C
ategoryTheory.IsGrothendieckAbelian.…
-/
instance IsGrothendieckAbelian.ab4OfSize : AB4OfSize.{w} C := by
  have : HasFiniteBiproducts C := HasFiniteBiproducts.of_hasFiniteProducts
  apply AB4.of_AB5

end Instances

end CategoryTheory

