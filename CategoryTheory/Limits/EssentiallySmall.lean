/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.EssentiallySmall

/-!
# Limits over essentially small indexing categories

If `C` has limits of size `w` and `J` is `w`-essentially small, then `C` has limits of shape `J`.

See also the file `FinallySmall.lean` for more general results.

-/

public section


universe w₁ w₂ v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory

namespace CategoryTheory.Limits

variable (J : Type u₂) [Category.{v₂} J] (C : Type u₁) [Category.{v₁} C]

/-
**CategoryTheory.Limits.hasLimitsOfShape_of_essentiallySmall** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Limits`。
形式化陈述：hasLimitsOfShape_of_essentiallySmall [EssentiallySmall.{w₁} J] [HasLimitsO
fSize.{w₁, w₁} C] : HasLimitsOfShape J C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_equivalence`：hasLimitsOfShape_
of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J') [HasLimitsOfShape 
J C] : HasLimitsOfShape J' C
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasLimitsOfSize`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTh
eory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
theorem hasLimitsOfShape_of_essentiallySmall [EssentiallySmall.{w₁} J]
    [HasLimitsOfSize.{w₁, w₁} C] : HasLimitsOfShape J C :=
  hasLimitsOfShape_of_equivalence <| Equivalence.symm <| equivSmallModel.{w₁} J
/-
**CategoryTheory.Limits.hasColimitsOfShape_of_essentiallySmall** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：hasColimitsOfShape_of_essentiallySmall [EssentiallySmall.{w₁} J] [HasColim
itsOfSize.{w₁, w₁} C] : HasColimitsOfShape J C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_equivalence`：hasColimitsOfSh
ape_of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J') [HasColimitsOf
Shape J C] : HasColimitsOfShape J' C
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
theorem hasColimitsOfShape_of_essentiallySmall [EssentiallySmall.{w₁} J]
    [HasColimitsOfSize.{w₁, w₁} C] : HasColimitsOfShape J C :=
  hasColimitsOfShape_of_equivalence <| Equivalence.symm <| equivSmallModel.{w₁} J
/-
**CategoryTheory.Limits.hasProductsOfShape_of_small** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：hasProductsOfShape_of_small (β : Type w₂) [Small.{w₁} β] [HasProducts.{w₁}
 C] : HasProductsOfShape β C
参数：β : Type w₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_equivalence`：hasLimitsOfShape_
of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J') [HasLimitsOfShape 
J C] : HasLimitsOfShape J' C
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem hasProductsOfShape_of_small (β : Type w₂) [Small.{w₁} β] [HasProducts.{w₁} C] :
    HasProductsOfShape β C :=
  hasLimitsOfShape_of_equivalence <| Discrete.equivalence <| Equiv.symm <| equivShrink β
/-
**CategoryTheory.Limits.hasCoproductsOfShape_of_small** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：hasCoproductsOfShape_of_small (β : Type w₂) [Small.{w₁} β] [HasCoproducts.
{w₁} C] : HasCoproductsOfShape β C
参数：β : Type w₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_equivalence`：hasColimitsOfSh
ape_of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J') [HasColimitsOf
Shape J C] : HasColimitsOfShape J' C
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem hasCoproductsOfShape_of_small (β : Type w₂) [Small.{w₁} β] [HasCoproducts.{w₁} C] :
    HasCoproductsOfShape β C :=
  hasColimitsOfShape_of_equivalence <| Discrete.equivalence <| Equiv.symm <| equivShrink β

end CategoryTheory.Limits

