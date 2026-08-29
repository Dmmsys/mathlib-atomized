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

/--
theorem `hasLimitsOfShape_of_essentiallySmall` / 定理 `hasLimitsOfShape_of_essentiallySmall`

English:
theorem hasLimitsOfShape_of_essentiallySmall
  statement: [EssentiallySmall.{w₁} J]
  proof: hasLimitsOfShape_of_equivalence Equivalence.symm equivSmallModel.{w₁} J

中文:
定理 hasLimitsOfShape_of_essentiallySmall
  结论: [EssentiallySmall.{w₁} J]
  证明: hasLimitsOfShape_of_equivalence Equivalence.symm equivSmallModel.{w₁} J

Depends on / 依赖: Equivalence, Equivalence.symm, equivSmallModel, hasLimitsOfShape_of_equivalence
-/
theorem hasLimitsOfShape_of_essentiallySmall [EssentiallySmall.{w₁} J]
    [HasLimitsOfSize.{w₁, w₁} C] : HasLimitsOfShape J C :=
hasLimitsOfShape_of_equivalence Equivalence.symm equivSmallModel.{w₁} J

/--
theorem `hasColimitsOfShape_of_essentiallySmall` / 定理 `hasColimitsOfShape_of_essentiallySmall`

English:
theorem hasColimitsOfShape_of_essentiallySmall
  statement: [EssentiallySmall.{w₁} J]
  proof: hasColimitsOfShape_of_equivalence Equivalence.symm equivSmallModel.{w₁} J

中文:
定理 hasColimitsOfShape_of_essentiallySmall
  结论: [EssentiallySmall.{w₁} J]
  证明: hasColimitsOfShape_of_equivalence Equivalence.symm equivSmallModel.{w₁} J

Depends on / 依赖: Equivalence, Equivalence.symm, equivSmallModel, hasColimitsOfShape_of_equivalence
-/
theorem hasColimitsOfShape_of_essentiallySmall [EssentiallySmall.{w₁} J]
    [HasColimitsOfSize.{w₁, w₁} C] : HasColimitsOfShape J C :=
hasColimitsOfShape_of_equivalence Equivalence.symm equivSmallModel.{w₁} J

/--
theorem `hasProductsOfShape_of_small` / 定理 `hasProductsOfShape_of_small`

English:
theorem hasProductsOfShape_of_small
  given: (β : Type w₂) [Small.{w₁} β] [HasProducts.{w₁} C]
  proof: hasLimitsOfShape_of_equivalence Discrete.equivalence Equiv.symm equivShrink β

中文:
定理 hasProductsOfShape_of_small
  条件: (β : 类型 w₂) [Small.{w₁} β] [HasProducts.{w₁} C]
  证明: hasLimitsOfShape_of_equivalence Discrete.equivalence Equiv.symm equivShrink β

Depends on / 依赖: Discrete, Discrete.equivalence, Equiv.symm, equivShrink, equivalence, hasLimitsOfShape_of_equivalence
-/
theorem hasProductsOfShape_of_small (β : Type w₂) [Small.{w₁} β] [HasProducts.{w₁} C] :
    HasProductsOfShape β C :=
hasLimitsOfShape_of_equivalence Discrete.equivalence Equiv.symm equivShrink β

/--
theorem `hasCoproductsOfShape_of_small` / 定理 `hasCoproductsOfShape_of_small`

English:
theorem hasCoproductsOfShape_of_small
  given: (β : Type w₂) [Small.{w₁} β] [HasCoproducts.{w₁} C]
  proof: hasColimitsOfShape_of_equivalence Discrete.equivalence Equiv.symm equivShrink β

中文:
定理 hasCoproductsOfShape_of_small
  条件: (β : 类型 w₂) [Small.{w₁} β] [HasCoproducts.{w₁} C]
  证明: hasColimitsOfShape_of_equivalence Discrete.equivalence Equiv.symm equivShrink β

Depends on / 依赖: Discrete, Discrete.equivalence, Equiv.symm, equivShrink, equivalence, hasColimitsOfShape_of_equivalence
-/
theorem hasCoproductsOfShape_of_small (β : Type w₂) [Small.{w₁} β] [HasCoproducts.{w₁} C] :
    HasCoproductsOfShape β C :=
hasColimitsOfShape_of_equivalence Discrete.equivalence Equiv.symm equivShrink β

end CategoryTheory.Limits
