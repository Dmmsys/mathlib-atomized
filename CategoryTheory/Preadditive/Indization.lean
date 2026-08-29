/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.Indization.Category
public import Mathlib.CategoryTheory.Preadditive.Transfer
public import Mathlib.CategoryTheory.Preadditive.Opposite
public import Mathlib.Algebra.Category.Grp.LeftExactFunctor

/-!
# The category of ind-objects is preadditive
-/

public section

universe v u

open CategoryTheory Limits

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] [Preadditive C] [HasFiniteColimits C]

attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preadditive (Ind C)
  body: .ofFullyFaithful (((Ind.leftExactFunctorEquivalence C).trans
    (AddCommGrpCat.leftExactFunctorForgetEquivalence _).symm).fullyFaithfulFunctor.comp
      (ObjectProperty.fullyFaithfulι _))

中文:
实例 :
  签名: 预加性 (Ind C)
  定义体: .ofFullyFaithful (((Ind.leftExactFunctorEquivalence C).trans
    (AddCommGrpCat.leftExactFunctorForgetEquivalence _).symm).fullyFaithfulFunctor.comp
      (ObjectProperty.fullyFaithfulι _))

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.leftExactFunctorForgetEquivalence, Ind.leftExactFunctorEquivalence, ObjectProperty, ObjectProperty.fullyFaithful, fullyFaithfulFunctor, fullyFaithfulFunctor.comp, leftExactFunctorEquivalence, leftExactFunctorForgetEquivalence, ofFullyFaithful
-/
noncomputable instance : Preadditive (Ind C) :=
  .ofFullyFaithful (((Ind.leftExactFunctorEquivalence C).trans
    (AddCommGrpCat.leftExactFunctorForgetEquivalence _).symm).fullyFaithfulFunctor.comp
      (ObjectProperty.fullyFaithfulι _))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasFiniteBiproducts (Ind C)
  body: HasFiniteBiproducts.of_hasFiniteCoproducts

中文:
实例 :
  签名: 有FiniteBiproducts (Ind C)
  定义体: HasFiniteBiproducts.of_hasFiniteCoproducts

Depends on / 依赖: HasFiniteBiproducts, HasFiniteBiproducts.of_hasFiniteCoproducts, of_hasFiniteCoproducts
-/
instance : HasFiniteBiproducts (Ind C) :=
  HasFiniteBiproducts.of_hasFiniteCoproducts

end CategoryTheory
