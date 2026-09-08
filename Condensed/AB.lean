/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Sites.Coherent.ExtensiveColimits
public import Mathlib.Condensed.Equivalence
public import Mathlib.Condensed.Limits
/-!

# AB axioms in condensed modules

This file proves that the category of condensed modules over a ring satisfies Grothendieck's axioms
AB5, AB4, and AB4`*`.
-/

public section

universe u

open Condensed CategoryTheory Limits

namespace Condensed

variable (A J : Type*) [Category* A] [Category* J] [Preadditive A]
  [∀ X, HasLimitsOfShape (StructuredArrow X Stonean.toCompHaus.op) A]
  [HasWeakSheafify (coherentTopology CompHaus.{u}) A]
  [HasWeakSheafify (extensiveTopology Stonean.{u}) A]
-- One of the `HasWeakSheafify` instances could be deduced from the other using the dense subsite
-- API, but when `A` is a concrete category, these will both be synthesized anyway.

set_option Elab.async false in  -- TODO: universe levels from type are unified in proof
/-
**Condensed.hasExactColimitsOfShape** 是 Mathlib 中的一个引理，位于命名空间 `Condensed`。
形式化陈述：hasExactColimitsOfShape [HasColimitsOfShape J A] [HasExactColimitsOfShape 
J A] [HasFiniteLimits A] : HasExactColimitsOfShape J (Condensed.{u} A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instPrecoherentOfFinitaryPreExtensiveOfPreregular`：∀ (C :
 Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Finitar
yPreExtensive C]   [CategoryTheory.Preregular C], Cate…
· 使用定理 `CategoryTheory.FinitaryExtensive.toFinitaryPreExtensive`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.FinitaryExtensive C], 
  CategoryTheory.FinitaryPreExtensive C
· 使用定理 `CompHausLike.instFinitaryExtensiveOfHasExplicitPullbacksOfInclusions`：∀ 
{P : TopCat → Prop} [inst : CompHausLike.HasExplicitFiniteCoproducts P]   [CompH
ausLike.HasExplicitPullbacksOfInclusions P], CategoryTheor…
· 使用定理 `CompHaus.instHasExplicitFiniteCoproductsTrue`：CompHausLike.HasExplicitFi
niteCoproducts fun x => True
· 使用定理 `CompHausLike.instHasExplicitPullbacksOfInclusionsOfHasExplicitPullbacks`
：∀ {P : TopCat → Prop} [CompHausLike.HasExplicitPullbacks P] [inst : CompHausLik
e.HasExplicitFiniteCoproducts P],   CompHausLike.HasExplicitP…
· 使用定理 `CompHaus.instHasExplicitPullbacksTrue`：CompHausLike.HasExplicitPullbacks
 fun x => True
· 使用定理 `CompHaus.instPreregular`：CategoryTheory.Preregular CompHaus
· 使用定理 `Stonean.instHasExplicitFiniteCoproductsExtremallyDisconnectedCarrier`：Co
mpHausLike.HasExplicitFiniteCoproducts fun Y => ExtremallyDisconnected ↑Y
· 使用定理 `Stonean.instHasExplicitPullbacksOfInclusionsExtremallyDisconnectedCarrie
r`：CompHausLike.HasExplicitPullbacksOfInclusions fun Y => ExtremallyDisconnected
 ↑Y
· 使用定理 `Stonean.instPreregular`：CategoryTheory.Preregular Stonean
· 使用定理 `Stonean.instProjective`：∀ (X : Stonean), CategoryTheory.Projective X
· 使用定理 `CategoryTheory.HasExactColimitsOfShape.domain_of_functor`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {D : Type u_1} (J : Type u_2)   [inst
_1 : CategoryTheory.Category.{v_1, u_2} J] [in…
· 使用定理 `instHasColimitsOfShapeCondensedOfHasWeakSheafifyCompHausCoherentTopology
`：∀ {A : Type u_1} {J : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} A] 
  [inst_1 : CategoryTheory.Category.{v_2, u_2} J] [CategoryThe…
· 使用定理 `CategoryTheory.Sheaf.instHasColimitsOfShape`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopology C} {D : T
ype w}   [inst_1 : CategoryTheory…
· 使用定理 `CategoryTheory.Sheaf.instHasExactColimitsOfShapeOfHasFiniteLimitsOfPrese
rvesColimitsOfShapeFunctorOppositeSheafToPresheaf`：∀ {C : Type u} {A : Type u₁} 
{K : Type u₂} [inst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheo
ry.Category.{v₁, u₁} A] [inst_2…
· 使用定理 `CategoryTheory.instPreservesColimitsOfShapeSheafExtensiveTopologyFunctor
OppositeSheafToPresheafOfPreservesFiniteProductsColim`：∀ {A : Type u_1} {C : Typ
e u_2} {J : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1} A]   [inst_1 : 
CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.instPreservesFiniteProductsFunctorColimOfPreadditive`：∀ {
A : Type u_1} {J : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1} A]   [in
st_1 : CategoryTheory.Category.{v_3, u_3} J] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categor
yTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfSizeOfIsRightAdjoint`：∀ {C :
 Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_2, u_2} C]   [inst_
1 : CategoryTheory.Category.{v_3, u_3} D] (F : Categor…
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
· 使用定理 `CategoryTheory.reflectsIsomorphisms_of_full_and_faithful`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `instHasFiniteLimitsCondensed`：∀ {A : Type u_1} [inst : CategoryTheory.Ca
tegory.{v_1, u_1} A] [CategoryTheory.Limits.HasFiniteLimits A],   CategoryTheory
.Limits.HasFiniteL…
· 使用定理 `CategoryTheory.Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint`：∀ {J
 : Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1,
 u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.isLeftAdjoint_of_isEquivalence`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   {F : CategoryTheor…
-/
lemma hasExactColimitsOfShape [HasColimitsOfShape J A] [HasExactColimitsOfShape J A]
    [HasFiniteLimits A] : HasExactColimitsOfShape J (Condensed.{u} A) := by
  let e : Condensed.{u} A ≌ Sheaf (extensiveTopology Stonean.{u}) A :=
    (StoneanCompHaus.equivalence A).symm.trans Presheaf.coherentExtensiveEquivalence
  exact HasExactColimitsOfShape.domain_of_functor _ e.functor

set_option Elab.async false in  -- TODO: universe levels from type are unified in proof
/-
**Condensed.hasExactLimitsOfShape** 是 Mathlib 中的一个引理，位于命名空间 `Condensed`。
形式化陈述：hasExactLimitsOfShape [HasLimitsOfShape J A] [HasExactLimitsOfShape J A] [
HasFiniteColimits A] : HasExactLimitsOfShape J (Condensed.{u} A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instPrecoherentOfFinitaryPreExtensiveOfPreregular`：∀ (C :
 Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Finitar
yPreExtensive C]   [CategoryTheory.Preregular C], Cate…
· 使用定理 `CategoryTheory.FinitaryExtensive.toFinitaryPreExtensive`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.FinitaryExtensive C], 
  CategoryTheory.FinitaryPreExtensive C
· 使用定理 `CompHausLike.instFinitaryExtensiveOfHasExplicitPullbacksOfInclusions`：∀ 
{P : TopCat → Prop} [inst : CompHausLike.HasExplicitFiniteCoproducts P]   [CompH
ausLike.HasExplicitPullbacksOfInclusions P], CategoryTheor…
· 使用定理 `CompHaus.instHasExplicitFiniteCoproductsTrue`：CompHausLike.HasExplicitFi
niteCoproducts fun x => True
· 使用定理 `CompHausLike.instHasExplicitPullbacksOfInclusionsOfHasExplicitPullbacks`
：∀ {P : TopCat → Prop} [CompHausLike.HasExplicitPullbacks P] [inst : CompHausLik
e.HasExplicitFiniteCoproducts P],   CompHausLike.HasExplicitP…
· 使用定理 `CompHaus.instHasExplicitPullbacksTrue`：CompHausLike.HasExplicitPullbacks
 fun x => True
· 使用定理 `CompHaus.instPreregular`：CategoryTheory.Preregular CompHaus
· 使用定理 `Stonean.instHasExplicitFiniteCoproductsExtremallyDisconnectedCarrier`：Co
mpHausLike.HasExplicitFiniteCoproducts fun Y => ExtremallyDisconnected ↑Y
· 使用定理 `Stonean.instHasExplicitPullbacksOfInclusionsExtremallyDisconnectedCarrie
r`：CompHausLike.HasExplicitPullbacksOfInclusions fun Y => ExtremallyDisconnected
 ↑Y
· 使用定理 `Stonean.instPreregular`：CategoryTheory.Preregular Stonean
· 使用定理 `Stonean.instProjective`：∀ (X : Stonean), CategoryTheory.Projective X
· 使用定理 `CategoryTheory.HasExactLimitsOfShape.domain_of_functor`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {D : Type u_1} (J : Type u_2)   [inst_1
 : CategoryTheory.Category.{v_1, u_1} D] [in…
· 使用定理 `instHasLimitsOfShapeCondensed`：∀ {A : Type u_1} {J : Type u_2} [inst : C
ategoryTheory.Category.{v_1, u_1} A]   [inst_1 : CategoryTheory.Category.{v_2, u
_2} J] [CategoryThe…
· 使用定理 `CategoryTheory.Sheaf.instHasLimitsOfShape`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopology C} {D : Typ
e w}   [inst_1 : CategoryTheory…
· 使用定理 `CategoryTheory.Sheaf.instHasExactLimitsOfShapeOfHasFiniteColimitsOfPrese
rvesFiniteColimitsFunctorOppositeSheafToPresheaf`：∀ {C : Type u} {A : Type u₁} {
K : Type u₂} [inst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheor
y.Category.{v₁, u₁} A] [inst_2…
· 使用定理 `CategoryTheory.instPreservesFiniteColimitsSheafExtensiveTopologyFunctorO
ppositeSheafToPresheafOfPreadditiveOfHasFiniteColimits`：∀ {A : Type u_1} {C : Ty
pe u_2} [inst : CategoryTheory.Category.{v_1, u_1} A]   [inst_1 : CategoryTheory
.Category.{v_2, u_2} C] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Limits.PreservesColimits.preservesFiniteColimits`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instPreservesColimitsOfSizeOfIsLeftAdjoint`：∀ {C 
: Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_2, u_2} C]   [inst
_1 : CategoryTheory.Category.{v_3, u_3} D] (F : Categor…
· 使用定理 `CategoryTheory.Functor.isLeftAdjoint_of_isEquivalence`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
· 使用定理 `CategoryTheory.reflectsIsomorphisms_of_full_and_faithful`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `instHasFiniteColimitsCondensedOfHasWeakSheafifyCompHausCoherentTopology`
：∀ {A : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} A] [CategoryTheory.
Limits.HasFiniteColimits A]   [CategoryTheory.HasWeakSheafify…
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfShapeOfIsRightAdjoint`：∀ {J 
: Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1, 
u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
-/
lemma hasExactLimitsOfShape [HasLimitsOfShape J A] [HasExactLimitsOfShape J A]
    [HasFiniteColimits A] : HasExactLimitsOfShape J (Condensed.{u} A) := by
  let e : Condensed.{u} A ≌ Sheaf (extensiveTopology Stonean.{u}) A :=
    (StoneanCompHaus.equivalence A).symm.trans Presheaf.coherentExtensiveEquivalence
  exact HasExactLimitsOfShape.domain_of_functor _ e.functor

section Module

variable (R : Type (u + 1)) [Ring R]

local instance : HasLimitsOfSize.{u, u + 1} (ModuleCat.{u + 1} R) :=
  hasLimitsOfSizeShrink.{u, u + 1, u + 1, u} _

variable (X Y : CondensedMod.{u} R)

/-
**Condensed.** 是 Mathlib 中的一个实例，位于命名空间 `Condensed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AB5 (CondensedMod.{u} R) where
  ofShape J _ _ := hasExactColimitsOfShape (ModuleCat R) J

attribute [local instance] Abelian.hasFiniteBiproducts
/-
**Condensed.** 是 Mathlib 中的一个实例，位于命名空间 `Condensed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AB4 (CondensedMod.{u} R) := AB4.of_AB5 _
/-
**Condensed.** 是 Mathlib 中的一个实例，位于命名空间 `Condensed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AB4Star (CondensedMod.{u} R) where
  ofShape J := hasExactLimitsOfShape (ModuleCat R) (Discrete J)

end Module

end Condensed

