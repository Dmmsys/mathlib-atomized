/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Reid Barton, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Limits.Constructions.Equalizers

/-!
# Limits in the over category

Declare instances for limits in the over category: If `C` has finite wide pullbacks, `Over B` has
finite limits, and if `C` has arbitrary wide pullbacks then `Over B` has limits.
-/

public section


universe w v u

-- morphism levels before object levels. See note [category_theory universes].
open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
variable {X : C}

namespace CategoryTheory.Over

/-- Make sure we can derive pullbacks in `Over B`. -/
instance {B : C} [HasPullbacks C] : HasPullbacks (Over B) := inferInstance

/-- Make sure we can derive equalizers in `Over B`. -/
instance {B : C} [HasEqualizers C] : HasEqualizers (Over B) := inferInstance

/--
Instance `hasFiniteLimits` / 实例 `hasFiniteLimits`

English:
instance hasFiniteLimits
  signature: {B : C} [HasFiniteWidePullbacks C]
  body: by
  have := ConstructProducts.over_finiteProducts_of_finiteWidePullbacks (B := B)
  have := hasEqualizers_of_hasPullbacks_and_binary_products (C := Over B)
  apply hasFiniteLimits_of_hasEqualizers_and_finite_products

中文:
实例 hasFiniteLimits
  签名: {B : C} [有FiniteWidePullbacks C]
  定义体: by
  have := ConstructProducts.over_finiteProducts_of_finiteWidePullbacks (B := B)
  have := hasEqualizers_of_hasPullbacks_and_binary_products (C := Over B)
  apply hasFiniteLimits_of_hasEqualizers_and_finite_products

Depends on / 依赖: ConstructProducts, ConstructProducts.over_finiteProducts_of_finiteWidePullbacks, hasEqualizers_of_hasPullbacks_and_binary_products, hasFiniteLimits_of_hasEqualizers_and_finite_products, over_finiteProducts_of_finiteWidePullbacks
-/
instance hasFiniteLimits {B : C} [HasFiniteWidePullbacks C] : HasFiniteLimits (Over B) := by
  have := ConstructProducts.over_finiteProducts_of_finiteWidePullbacks (B := B)
  have := hasEqualizers_of_hasPullbacks_and_binary_products (C := Over B)
  apply hasFiniteLimits_of_hasEqualizers_and_finite_products

/--
Instance `hasLimits` / 实例 `hasLimits`

English:
instance hasLimits
  signature: {B : C} [HasWidePullbacks.{w} C]
  body: by
  have := ConstructProducts.over_binaryProduct_of_pullback (B := B)
  have := hasEqualizers_of_hasPullbacks_and_binary_products (C := Over B)
  have := ConstructProducts.over_products_of_widePullbacks (B := B)
  apply has_limits_of_hasEqualizers_and_products

中文:
实例 hasLimits
  签名: {B : C} [HasWidePullbacks.{w} C]
  定义体: by
  have := ConstructProducts.over_binaryProduct_of_pullback (B := B)
  have := hasEqualizers_of_hasPullbacks_and_binary_products (C := Over B)
  have := ConstructProducts.over_products_of_widePullbacks (B := B)
  apply has_limits_of_hasEqualizers_and_products

Depends on / 依赖: ConstructProducts, ConstructProducts.over_binaryProduct_of_pullback, ConstructProducts.over_products_of_widePullbacks, hasEqualizers_of_hasPullbacks_and_binary_products, has_limits_of_hasEqualizers_and_products, over_binaryProduct_of_pullback, over_products_of_widePullbacks
-/
instance hasLimits {B : C} [HasWidePullbacks.{w} C] : HasLimitsOfSize.{w, w} (Over B) := by
  have := ConstructProducts.over_binaryProduct_of_pullback (B := B)
  have := hasEqualizers_of_hasPullbacks_and_binary_products (C := Over B)
  have := ConstructProducts.over_products_of_widePullbacks (B := B)
  apply has_limits_of_hasEqualizers_and_products

end Over

namespace Under

instance {B : C} [HasFiniteWidePushouts C] : HasFiniteColimits (Under B) := by
  rw [← hasFiniteLimits_opposite_iff]
  exact hasFiniteLimits_of_hasLimitsLimits_of_createsFiniteLimits (Over.opEquivOpUnder _).inverse

instance {B : C} [HasWidePushouts.{w} C] : HasColimitsOfSize.{w, w} (Under B) := by
  rw [← hasLimitsOfSize_opposite_iff]
  exact hasLimits_of_hasLimits_createsLimits (Over.opEquivOpUnder _).inverse

end CategoryTheory.Under
