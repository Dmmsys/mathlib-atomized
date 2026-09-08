/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Nikolas Kuhn, Dagur Asgeirsson
-/
module

public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import Mathlib.Topology.Category.Stonean.EffectiveEpi
public import Mathlib.Condensed.Basic
public import Mathlib.CategoryTheory.Sites.Coherent.SheafComparison
/-!

# Sheaves on CompHaus are equivalent to sheaves on Stonean

The forgetful functor from extremally disconnected spaces `Stonean` to compact
Hausdorff spaces `CompHaus` has the marvellous property that it induces an equivalence of categories
between sheaves on these two sites. With the terminology of nLab, `Stonean` is a
*dense subsite* of `CompHaus`: see https://ncatlab.org/nlab/show/dense+sub-site

Since Stonean spaces are the projective objects in `CompHaus`, which has enough projectives,
and the notions of effective epimorphism, epimorphism and surjective continuous map are equivalent
in `CompHaus` and `Stonean`, we can use the general setup in
`Mathlib/CategoryTheory/Sites/Coherent/SheafComparison.lean` to deduce the equivalence of
categories. We give the corresponding statements for `Profinite` as well.

## Main results

* `Condensed.StoneanCompHaus.equivalence`: the equivalence from coherent sheaves on `Stonean` to
  coherent sheaves on `CompHaus` (i.e. condensed sets).
* `Condensed.StoneanProfinite.equivalence`: the equivalence from coherent sheaves on `Stonean` to
  coherent sheaves on `Profinite`.
* `Condensed.ProfiniteCompHaus.equivalence`: the equivalence from coherent sheaves on `Profinite` to
  coherent sheaves on `CompHaus` (i.e. condensed sets).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace Condensed

namespace StoneanCompHaus

/-- The equivalence from coherent sheaves on `Stonean` to coherent sheaves on `CompHaus`
    (i.e. condensed sets). -/
noncomputable
/-
**Condensed.StoneanCompHaus.equivalence** 是 Mathlib 中的一个定义，位于命名空间 `Condensed.Sto
neanCompHaus`。
形式化陈述：equivalence (A : Type*) [Category* A] [forall X, HasLimitsOfShape (Structu
redArrow X Stonean.toCompHaus.op) A] : Sheaf (coherentTopology Stonean) A ≌ Cond
ensed.{u} A
参数：A : Type*；StructuredArrow X Stonean.toCompHaus.op。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Stonean.instPreservesEffectiveEpisCompHausToCompHaus`：Stonean.toCompHaus
.PreservesEffectiveEpis
· 使用定理 `Stonean.instReflectsEffectiveEpisCompHausToCompHaus`：Stonean.toCompHaus.
ReflectsEffectiveEpis
· 使用定理 `CompHaus.instPreregular`：CategoryTheory.Preregular CompHaus
· 使用定理 `Stonean.instEffectivelyEnoughCompHausToCompHaus`：Stonean.toCompHaus.Effe
ctivelyEnough
-/
def equivalence (A : Type*) [Category* A]
    [∀ X, HasLimitsOfShape (StructuredArrow X Stonean.toCompHaus.op) A] :
    Sheaf (coherentTopology Stonean) A ≌ Condensed.{u} A :=
  coherentTopology.equivalence' Stonean.toCompHaus A

end StoneanCompHaus

namespace StoneanProfinite

/-
**Condensed.StoneanProfinite.** 是 Mathlib 中的一个实例，位于命名空间 `Condensed.StoneanProfin
ite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Stonean.toProfinite.PreservesEffectiveEpis where
  preserves f h :=
    ((Profinite.effectiveEpi_tfae _).out 0 2).mpr (((Stonean.effectiveEpi_tfae _).out 0 2).mp h)
/-
**Condensed.StoneanProfinite.** 是 Mathlib 中的一个实例，位于命名空间 `Condensed.StoneanProfin
ite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Stonean.toProfinite.ReflectsEffectiveEpis where
  reflects f h :=
    ((Stonean.effectiveEpi_tfae f).out 0 2).mpr (((Profinite.effectiveEpi_tfae _).out 0 2).mp h)

/--
An effective presentation of an `X : Profinite` with respect to the inclusion functor from `Stonean`
-/
/-
**Condensed.StoneanProfinite.stoneanToProfiniteEffectivePresentation** 是 Mathlib
 中的一个定义，位于命名空间 `Condensed.StoneanProfinite`。
形式化陈述：stoneanToProfiniteEffectivePresentation (X : Profinite) : Stonean.toProfin
ite.EffectivePresentation X where p
参数：X : Profinite。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An effective presentation of an `X : Profinite` with respect to the inclusion fu
nctor from `Stonean`
-/
noncomputable def stoneanToProfiniteEffectivePresentation (X : Profinite) :
    Stonean.toProfinite.EffectivePresentation X where
  p := X.presentation
  f := Profinite.presentation.π X
  effectiveEpi := ((Profinite.effectiveEpi_tfae _).out 0 1).mpr (inferInstance : Epi _)
/-
**Condensed.StoneanProfinite.** 是 Mathlib 中的一个实例，位于命名空间 `Condensed.StoneanProfin
ite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Stonean.toProfinite.EffectivelyEnough where
  presentation X := ⟨stoneanToProfiniteEffectivePresentation X⟩

/-- The equivalence from coherent sheaves on `Stonean` to coherent sheaves on `Profinite`. -/
noncomputable
/-
**Condensed.StoneanProfinite.equivalence** 是 Mathlib 中的一个定义，位于命名空间 `Condensed.St
oneanProfinite`。
形式化陈述：equivalence (A : Type*) [Category* A] [forall X, HasLimitsOfShape (Structu
redArrow X Stonean.toProfinite.op) A] : Sheaf (coherentTopology Stonean) A ≌ She
af (coherentTopology Profinite) A
参数：A : Type*；StructuredArrow X Stonean.toProfinite.op。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Condensed.StoneanProfinite.instPreservesEffectiveEpisStoneanProfiniteToP
rofinite`：Stonean.toProfinite.PreservesEffectiveEpis
· 使用定理 `Condensed.StoneanProfinite.instReflectsEffectiveEpisStoneanProfiniteToPr
ofinite`：Stonean.toProfinite.ReflectsEffectiveEpis
· 使用定理 `Profinite.instPreregular`：CategoryTheory.Preregular Profinite
· 使用定理 `Condensed.StoneanProfinite.instEffectivelyEnoughStoneanProfiniteToProfin
ite`：Stonean.toProfinite.EffectivelyEnough
-/
def equivalence (A : Type*) [Category* A]
    [∀ X, HasLimitsOfShape (StructuredArrow X Stonean.toProfinite.op) A] :
    Sheaf (coherentTopology Stonean) A ≌ Sheaf (coherentTopology Profinite) A :=
  coherentTopology.equivalence' Stonean.toProfinite A

end StoneanProfinite

namespace ProfiniteCompHaus

/-- The equivalence from coherent sheaves on `Profinite` to coherent sheaves on `CompHaus`
(i.e. condensed sets). -/
noncomputable
/-
**Condensed.ProfiniteCompHaus.equivalence** 是 Mathlib 中的一个定义，位于命名空间 `Condensed.P
rofiniteCompHaus`。
形式化陈述：equivalence (A : Type*) [Category* A] [forall X, HasLimitsOfShape (Structu
redArrow X profiniteToCompHaus.op) A] : Sheaf (coherentTopology Profinite) A ≌ C
ondensed.{u} A
参数：A : Type*；StructuredArrow X profiniteToCompHaus.op。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Profinite.instPreservesEffectiveEpisCompHausProfiniteToCompHaus`：profini
teToCompHaus.PreservesEffectiveEpis
· 使用定理 `Profinite.instReflectsEffectiveEpisCompHausProfiniteToCompHaus`：profinit
eToCompHaus.ReflectsEffectiveEpis
· 使用定理 `CompHaus.instPreregular`：CategoryTheory.Preregular CompHaus
· 使用定理 `Profinite.instEffectivelyEnoughCompHausProfiniteToCompHaus`：profiniteToC
ompHaus.EffectivelyEnough
-/
def equivalence (A : Type*) [Category* A]
    [∀ X, HasLimitsOfShape (StructuredArrow X profiniteToCompHaus.op) A] :
    Sheaf (coherentTopology Profinite) A ≌ Condensed.{u} A :=
  coherentTopology.equivalence' profiniteToCompHaus A

end ProfiniteCompHaus

variable {A : Type*} [Category* A] (X : Condensed.{u} A)

/-
**Condensed.isSheafProfinite** 是 Mathlib 中的一个引理，位于命名空间 `Condensed`。
形式化陈述：isSheafProfinite [forall Y, HasLimitsOfShape (StructuredArrow Y profiniteT
oCompHaus.{u}.op) A] : Presheaf.IsSheaf (coherentTopology Profinite) (profiniteT
oCompHaus.op ⋙ X.obj)
参数：StructuredArrow Y profiniteToCompHaus.{u}.op。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
· 使用定理 `CategoryTheory.instPrecoherentOfFinitaryPreExtensiveOfPreregular`：∀ (C :
 Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Finitar
yPreExtensive C]   [CategoryTheory.Preregular C], Cate…
· 使用定理 `CategoryTheory.FinitaryExtensive.toFinitaryPreExtensive`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.FinitaryExtensive C], 
  CategoryTheory.FinitaryPreExtensive C
· 使用定理 `CompHausLike.instFinitaryExtensiveOfHasExplicitPullbacksOfInclusions`：∀ 
{P : TopCat → Prop} [inst : CompHausLike.HasExplicitFiniteCoproducts P]   [CompH
ausLike.HasExplicitPullbacksOfInclusions P], CategoryTheor…
· 使用定理 `Profinite.instHasExplicitFiniteCoproductsTotallyDisconnectedSpaceCarrier
`：CompHausLike.HasExplicitFiniteCoproducts fun Y => TotallyDisconnectedSpace ↑Y
· 使用定理 `CompHausLike.instHasExplicitPullbacksOfInclusionsOfHasExplicitPullbacks`
：∀ {P : TopCat → Prop} [CompHausLike.HasExplicitPullbacks P] [inst : CompHausLik
e.HasExplicitFiniteCoproducts P],   CompHausLike.HasExplicitP…
· 使用定理 `Profinite.instHasExplicitPullbacksTotallyDisconnectedSpaceCarrier`：CompH
ausLike.HasExplicitPullbacks fun Y => TotallyDisconnectedSpace ↑Y
· 使用定理 `Profinite.instPreregular`：CategoryTheory.Preregular Profinite
-/
lemma isSheafProfinite
    [∀ Y, HasLimitsOfShape (StructuredArrow Y profiniteToCompHaus.{u}.op) A] :
    Presheaf.IsSheaf (coherentTopology Profinite)
    (profiniteToCompHaus.op ⋙ X.obj) :=
  ((ProfiniteCompHaus.equivalence A).inverse.obj X).property
/-
**Condensed.isSheafStonean** 是 Mathlib 中的一个引理，位于命名空间 `Condensed`。
形式化陈述：isSheafStonean [forall Y, HasLimitsOfShape (StructuredArrow Y Stonean.toCo
mpHaus.{u}.op) A] : Presheaf.IsSheaf (coherentTopology Stonean) (Stonean.toCompH
aus.op ⋙ X.obj)
参数：StructuredArrow Y Stonean.toCompHaus.{u}.op。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
· 使用定理 `CategoryTheory.instPrecoherentOfFinitaryPreExtensiveOfPreregular`：∀ (C :
 Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Finitar
yPreExtensive C]   [CategoryTheory.Preregular C], Cate…
· 使用定理 `CategoryTheory.FinitaryExtensive.toFinitaryPreExtensive`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.FinitaryExtensive C], 
  CategoryTheory.FinitaryPreExtensive C
· 使用定理 `CompHausLike.instFinitaryExtensiveOfHasExplicitPullbacksOfInclusions`：∀ 
{P : TopCat → Prop} [inst : CompHausLike.HasExplicitFiniteCoproducts P]   [CompH
ausLike.HasExplicitPullbacksOfInclusions P], CategoryTheor…
· 使用定理 `Stonean.instHasExplicitFiniteCoproductsExtremallyDisconnectedCarrier`：Co
mpHausLike.HasExplicitFiniteCoproducts fun Y => ExtremallyDisconnected ↑Y
· 使用定理 `Stonean.instHasExplicitPullbacksOfInclusionsExtremallyDisconnectedCarrie
r`：CompHausLike.HasExplicitPullbacksOfInclusions fun Y => ExtremallyDisconnected
 ↑Y
· 使用定理 `Stonean.instPreregular`：CategoryTheory.Preregular Stonean
-/
lemma isSheafStonean
    [∀ Y, HasLimitsOfShape (StructuredArrow Y Stonean.toCompHaus.{u}.op) A] :
    Presheaf.IsSheaf (coherentTopology Stonean)
    (Stonean.toCompHaus.op ⋙ X.obj) :=
  ((StoneanCompHaus.equivalence A).inverse.obj X).property

end Condensed

