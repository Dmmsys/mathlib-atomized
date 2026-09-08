/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.ColimitsClosure
public import Mathlib.CategoryTheory.SmallRepresentatives
public import Mathlib.CategoryTheory.Comma.CardinalArrow

/-!
# Closure of a property of objects under colimits of bounded cardinality

In this file, given `P : ObjectProperty C` and `κ : Cardinal.{w}`,
we introduce the closure `P.colimitsCardinalClosure κ`
of `P` under colimits of shapes given by categories `J` such
that `Arrow J` is of cardinality `< κ`.

If `C` is locally `w`-small and `P` is essentially `w`-small,
we show that this closure `P.colimitsCardinalClosure κ` is
also essentially `w`-small.

-/

@[expose] public section

universe w v' v u' u

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] (P : ObjectProperty C) (κ : Cardinal.{w})

/-- Given `P : ObjectProperty C` and `κ : Cardinal.{w}`, this is the closure
of `P` under colimits of shape given by categories `J` such that
`Arrow J` is of cardinality `< κ`. -/
/-
**CategoryTheory.ObjectProperty.colimitsCardinalClosure** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.ObjectProperty`。
形式化陈述：colimitsCardinalClosure : ObjectProperty C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `P : ObjectProperty C` and `κ : Cardinal.{w}`, this is the closure
of `P` under colimits of shape given by categories `J` such that
`Arrow J` is of cardinality `< κ`.
-/
def colimitsCardinalClosure : ObjectProperty C :=
  P.colimitsClosure (SmallCategoryCardinalLT.categoryFamily κ)
/-
**CategoryTheory.ObjectProperty.le_colimitsCardinalClosure** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：le_colimitsCardinalClosure : P <= P.colimitsCardinalClosure κ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.le_colimitsClosure`：le_colimitsClosure : P
 <= P.colimitsClosure J
-/
lemma le_colimitsCardinalClosure : P ≤ P.colimitsCardinalClosure κ :=
  P.le_colimitsClosure _
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (P.colimitsCardinalClosure κ).IsClosedUnderIsomorphisms := by
  dsimp [colimitsCardinalClosure]
  infer_instance
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [ObjectProperty.EssentiallySmall.{w} P] [LocallySmall.{w} C] :
    ObjectProperty.EssentiallySmall.{w} (P.colimitsCardinalClosure κ) := by
  dsimp [colimitsCardinalClosure]
  infer_instance
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (S : SmallCategoryCardinalLT κ) :
    (P.colimitsCardinalClosure κ).IsClosedUnderColimitsOfShape
      (SmallCategoryCardinalLT.categoryFamily κ S) := by
  dsimp [colimitsCardinalClosure]
  infer_instance
/-
**CategoryTheory.ObjectProperty.isClosedUnderColimitsOfShape_colimitsCardinalClo
sure** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：isClosedUnderColimitsOfShape_colimitsCardinalClosure (J : Type u') [Catego
ry.{v'} J] (hJ : HasCardinalLT (Arrow J) κ) : (P.colimitsCardinalClosure κ).IsCl
osedUnderColimitsOfShape J
参数：J : Type u'；hJ : HasCardinalLT (Arrow J) κ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.SmallCategoryCardinalLT.exists_equivalence`：exists_equiva
lence (C : Type u) [Category.{v} C] (hC : HasCardinalLT (Arrow C) κ) : exists (S
 : SmallCategoryCardinalLT κ), Nonempty (catego…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.isClosedUnderColimitsOfShape_iff_of_equiva
lence`：isClosedUnderColimitsOfShape_iff_of_equivalence (e : J ≌ J') : P.IsClosed
UnderColimitsOfShape J ↔ P.IsClosedUnderColimitsOfShape J'
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderColimitsOfShapeColimitsCa
rdinalClosureCategoryFamily`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, 
u} C] (P : CategoryTheory.ObjectProperty C) (κ : Cardinal.{w})   (S : CategoryTh
eory.Smal…
-/
lemma isClosedUnderColimitsOfShape_colimitsCardinalClosure
    (J : Type u') [Category.{v'} J] (hJ : HasCardinalLT (Arrow J) κ) :
    (P.colimitsCardinalClosure κ).IsClosedUnderColimitsOfShape J := by
  obtain ⟨S, ⟨e⟩⟩ := SmallCategoryCardinalLT.exists_equivalence κ J hJ
  rw [isClosedUnderColimitsOfShape_iff_of_equivalence _ e.symm]
  infer_instance
/-
**CategoryTheory.ObjectProperty.colimitsCardinalClosure_le** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：colimitsCardinalClosure_le {Q : ObjectProperty C} [Q.IsClosedUnderIsomorph
isms] (hQ : forall (J : Type w) [SmallCategory J] (_ : HasCardinalLT (Arrow J) κ
), Q.IsClosedUnderColimitsOfShape J) (h : P <= Q) : P.colimitsCardinalClosure κ 
<= Q
参数：hQ : forall (J : Type w) [SmallCategory J] (_ : HasCardinalLT (Arrow J) κ), Q
.IsClosedUnderColimitsOfShape J；h : P <= Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.SmallCategoryCardinalLT.hasCardinalLT`：hasCardinalLT (S :
 SmallCategoryCardinalLT κ) : HasCardinalLT (Arrow (categoryFamily κ S)) κ
· 使用引理 `CategoryTheory.ObjectProperty.colimitsClosure_le`：colimitsClosure_le {Q 
: ObjectProperty C} [Q.IsClosedUnderIsomorphisms] [forall (a : α), Q.IsClosedUnd
erColimitsOfShape (J a)] (h : P <= Q) …
-/
lemma colimitsCardinalClosure_le {Q : ObjectProperty C} [Q.IsClosedUnderIsomorphisms]
    (hQ : ∀ (J : Type w) [SmallCategory J] (_ : HasCardinalLT (Arrow J) κ),
      Q.IsClosedUnderColimitsOfShape J) (h : P ≤ Q) :
    P.colimitsCardinalClosure κ ≤ Q := by
  have (i : SmallCategoryCardinalLT κ) := hQ _ i.hasCardinalLT
  exact colimitsClosure_le h

section

open Limits

/-
**CategoryTheory.ObjectProperty.isStableUnderRetracts_colimitsCardinalClosure** 
是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：isStableUnderRetracts_colimitsCardinalClosure [Fact κ.IsRegular] : (P.coli
mitsCardinalClosure κ).IsStableUnderRetracts
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.isClosedUnderColimitsOfShape_colimitsCardi
nalClosure`：isClosedUnderColimitsOfShape_colimitsCardinalClosure (J : Type u') [
Category.{v'} J] (hJ : HasCardinalLT (Arrow J) κ) : (P.colimitsCardinalC…
· 使用引理 `HasCardinalLT.of_le`：of_le {κ' : Cardinal.{v}} (hκ' : κ <= κ') : HasCard
inalLT X κ'
· 使用定理 `CategoryTheory.Arrow.finite`：∀ {C : Type u} [inst : CategoryTheory.Small
Category C] [CategoryTheory.FinCategory C], Finite (CategoryTheory.Arrow C)
· 使用定理 `Cardinal.IsRegular.aleph0_le`：∀ {c : Cardinal.{u_1}}, c.IsRegular → Card
inal.aleph0 ≤ c
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `CategoryTheory.ObjectProperty.instIsStableUnderRetractsOfIsClosedUnderCo
limitsOfShapeWalkingParallelPair`：∀ {C : Type u_1} [inst : CategoryTheory.Catego
ry.{v_1, u_1} C] (P : CategoryTheory.ObjectProperty C)   [P.IsClosedUnderColimit
sOfShape Categ…
-/
instance isStableUnderRetracts_colimitsCardinalClosure [Fact κ.IsRegular] :
    (P.colimitsCardinalClosure κ).IsStableUnderRetracts := by
  have := P.isClosedUnderColimitsOfShape_colimitsCardinalClosure κ
    WalkingParallelPair (HasCardinalLT.of_le (by
      simp only [hasCardinalLT_aleph0_iff]
      infer_instance)
    (Cardinal.IsRegular.aleph0_le Fact.out))
  infer_instance

end

end CategoryTheory.ObjectProperty

