/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Generator.Sheaf
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Equivalence

/-!

# AB axioms in sheaf categories

If `J` is a Grothendieck topology on a small category `C : Type v`,
and `A : Type u₁` (with `Category.{v} A`) is a Grothendieck abelian category,
then `Sheaf J A` is a Grothendieck abelian category.

-/

public section

universe v v₁ v₂ u u₁ u₂

namespace CategoryTheory

open Limits

namespace Sheaf

variable {C : Type u} {A : Type u₁} {K : Type u₂}
  [Category.{v} C] [Category.{v₁} A] [Category.{v₂} K]
  (J : GrothendieckTopology C)

section

/- The two instances in this section apply in very rare situations, as they assume
that the forgetful functor from sheaves to presheaves commutes with certain colimits.
This does apply for sheaves for the extensive topology --- condensed modules over a
ring are examples of such sheaves.  -/

variable [HasWeakSheafify J A]

/-
**CategoryTheory.Sheaf.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasFiniteLimits A] [HasColimitsOfShape K A] [HasExactColimitsOfShape K A]
    [PreservesColimitsOfShape K (sheafToPresheaf J A)] : HasExactColimitsOfShape K (Sheaf J A) :=
  HasExactColimitsOfShape.domain_of_functor K (sheafToPresheaf J A)
/-
**CategoryTheory.Sheaf.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasFiniteColimits A] [HasLimitsOfShape K A] [HasExactLimitsOfShape K A]
    [PreservesFiniteColimits (sheafToPresheaf J A)] : HasExactLimitsOfShape K (Sheaf J A) :=
  HasExactLimitsOfShape.domain_of_functor K (sheafToPresheaf J A)

end

/-
**CategoryTheory.Sheaf.hasFilteredColimitsOfSize** 是 Mathlib 中的一个实例，位于命名空间 `Cate
goryTheory.Sheaf`。
形式化陈述：hasFilteredColimitsOfSize [HasSheafify J A] [HasFilteredColimitsOfSize.{v₂
, u₂} A] : HasFilteredColimitsOfSize.{v₂, u₂} (Sheaf J A) where HasColimitsOfSha
pe K
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sheaf.instHasColimitsOfShape`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopology C} {D : T
ype w}   [inst_1 : CategoryTheory…
· 使用定理 `CategoryTheory.instHasWeakSheafifyOfHasSheafify`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C)
 (A : Type u₂)   [inst_1 : CategoryTh…
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_has_filtered_colimits`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C]   [CategoryTheory.Limits.Has
FilteredColimitsOfSize.{w', w, v, u} C] (I : Type w)   …
-/
instance hasFilteredColimitsOfSize
    [HasSheafify J A] [HasFilteredColimitsOfSize.{v₂, u₂} A] :
    HasFilteredColimitsOfSize.{v₂, u₂} (Sheaf J A) where
  HasColimitsOfShape K := by infer_instance
/-
**CategoryTheory.Sheaf.hasExactColimitsOfShape** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.Sheaf`。
形式化陈述：hasExactColimitsOfShape [HasFiniteLimits A] [HasSheafify J A] [HasColimits
OfShape K A] [HasExactColimitsOfShape K A] : HasExactColimitsOfShape K (Sheaf J 
A)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.hasExactColimitsOfShape`：hasExactColimitsOfSha
pe (adj : F ⊣ G) [G.Full] [G.Faithful] (J : Type u') [Category.{v'} J] [HasColim
itsOfShape J C] [HasColimitsOfShape J D…
· 使用定理 `CategoryTheory.instHasWeakSheafifyOfHasSheafify`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C)
 (A : Type u₂)   [inst_1 : CategoryTh…
· 使用定理 `CategoryTheory.Sheaf.instHasColimitsOfShape`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopology C} {D : T
ype w}   [inst_1 : CategoryTheory…
· 使用定理 `CategoryTheory.instHasExactColimitsOfShapeFunctorOfHasFiniteLimits`：∀ {A
 : Type u_1} {C : Type u_2} {J : Type u_3} [inst : CategoryTheory.Category.{v_1,
 u_1} A]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Sheaf.instHasFiniteLimits`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopology C} {D : Type
 w}   [inst_1 : CategoryTheory…
· 使用定理 `CategoryTheory.instPreservesFiniteLimitsFunctorOppositeSheafPresheafToSh
eaf`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTh
eory.GrothendieckTopology C) (A : Type u₂)   [inst_1 : CategoryTh…
-/
instance hasExactColimitsOfShape [HasFiniteLimits A] [HasSheafify J A]
    [HasColimitsOfShape K A] [HasExactColimitsOfShape K A] :
    HasExactColimitsOfShape K (Sheaf J A) :=
  (sheafificationAdjunction J A).hasExactColimitsOfShape K
/-
**CategoryTheory.Sheaf.ab5ofSize** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sheaf
`。
形式化陈述：ab5ofSize [HasFiniteLimits A] [HasSheafify J A] [HasFilteredColimitsOfSize
.{v₂, u₂} A] [AB5OfSize.{v₂, u₂} A] : AB5OfSize.{v₂, u₂} (Sheaf J A) where ofSha
pe K _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_has_filtered_colimits`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C]   [CategoryTheory.Limits.Has
FilteredColimitsOfSize.{w', w, v, u} C] (I : Type w)   …
· 使用定理 `CategoryTheory.AB5OfSize.ofShape`：∀ {C : Type u} {inst : CategoryTheory.
Category.{v, u} C}   {inst_1 : CategoryTheory.Limits.HasFilteredColimitsOfSize.{
w, w', v, u} C}   [sel…
-/
instance ab5ofSize [HasFiniteLimits A] [HasSheafify J A]
    [HasFilteredColimitsOfSize.{v₂, u₂} A] [AB5OfSize.{v₂, u₂} A] :
    AB5OfSize.{v₂, u₂} (Sheaf J A) where
  ofShape K _ _ := by infer_instance
/-
**CategoryTheory.Sheaf.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {C : Type v} [SmallCategory.{v} C] (J : GrothendieckTopology C)
    (A : Type u₁) [Category.{v₁} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
    [HasSheafify J A] : IsGrothendieckAbelian.{v} (Sheaf J A) where

attribute [local instance] hasSheafifyEssentiallySmallSite in
/-
**CategoryTheory.Sheaf.isGrothendieckAbelian_of_essentiallySmall** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.Sheaf`。
形式化陈述：isGrothendieckAbelian_of_essentiallySmall {C : Type u₂} [Category.{v₂} C] 
[EssentiallySmall.{v} C] (J : GrothendieckTopology C) (A : Type u₁) [Category.{v
₁} A] [Abelian A] [IsGrothendieckAbelian.{v} A] [forall (X : Cᵒᵖ), HasLimitsOfSh
ape (StructuredArrow X (equivSmallModel C).inverse.op) A] [HasSheafify ((equivSm
allModel C).inverse.inducedTopology J) A] : IsGrothendieckAbelian.{v} (Sheaf J A
)
参数：J : GrothendieckTopology C；A : Type u₁；X : Cᵒᵖ；StructuredArrow X (equivSmallM
odel C).inverse.op；(equivSmallModel C).inverse.inducedTopology J。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.of_equivalence`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   [inst_2 : CategoryThe…
· 使用引理 `CategoryTheory.hasSheafifyEssentiallySmallSite`：hasSheafifyEssentiallySm
allSite : HasSheafify J A
· 使用定理 `CategoryTheory.Sheaf.instIsGrothendieckAbelian`：∀ {C : Type v} [inst : C
ategoryTheory.SmallCategory C] (J : CategoryTheory.GrothendieckTopology C) (A : 
Type u₁)   [inst_1 : CategoryTheory.…
· 使用定理 `CategoryTheory.Functor.locallyCoverDense_of_isCoverDense`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} D] (G : Categor…
· 使用定理 `CategoryTheory.Functor.IsLocallyFull.of_full`：∀ {C : Type uC} [inst : Ca
tegoryTheory.Category.{vC, uC} C] {D : Type uD} [inst_1 : CategoryTheory.Categor
y.{vD, uD} D]   {K : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.instIsCoverDenseOfIsEquivalence`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.Grothendieck
Topology C) {D : Type u₂}   [inst_1 : CategoryTh…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
· 使用定理 `CategoryTheory.Functor.IsLocallyFaithful.of_faithful`：∀ {C : Type uC} [i
nst : CategoryTheory.Category.{vC, uC} C] {D : Type uD} [inst_1 : CategoryTheory
.Category.{vD, uD} D]   {K : CategoryTheor…
-/
lemma isGrothendieckAbelian_of_essentiallySmall
    {C : Type u₂} [Category.{v₂} C] [EssentiallySmall.{v} C]
    (J : GrothendieckTopology C)
    (A : Type u₁) [Category.{v₁} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
    [∀ (X : Cᵒᵖ), HasLimitsOfShape (StructuredArrow X (equivSmallModel C).inverse.op) A]
    [HasSheafify ((equivSmallModel C).inverse.inducedTopology J) A] :
      IsGrothendieckAbelian.{v} (Sheaf J A) :=
  IsGrothendieckAbelian.of_equivalence
    ((equivSmallModel C).inverse.sheafInducedTopologyEquivOfIsCoverDense J A)

end Sheaf

end CategoryTheory

