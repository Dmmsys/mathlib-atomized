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
/-
**CategoryTheory.Over.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Over`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Make sure we can derive pullbacks in `Over B`.
-/
instance {B : C} [HasPullbacks C] : HasPullbacks (Over B) := inferInstance

/-- Make sure we can derive equalizers in `Over B`. -/
/-
**CategoryTheory.Over.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Over`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Make sure we can derive equalizers in `Over B`.
-/
instance {B : C} [HasEqualizers C] : HasEqualizers (Over B) := inferInstance
/-
**CategoryTheory.Over.hasFiniteLimits** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
Over`。
形式化陈述：hasFiniteLimits {B : C} [HasFiniteWidePullbacks C] : HasFiniteLimits (Over
 B)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Over.ConstructProducts.over_finiteProducts_of_finiteWideP
ullbacks`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheo
ry.Limits.HasFiniteWidePullbacks C] {B : C},   CategoryTheory.Limits.H…
· 使用定理 `CategoryTheory.Limits.hasEqualizers_of_hasPullbacks_and_binary_products`
：hasEqualizers_of_hasPullbacks_and_binary_products [HasBinaryProducts C] [HasPul
lbacks C] : HasEqualizers C
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Over.instHasPullbacks`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {B : C} [CategoryTheory.Limits.HasPullbacks C],   Categor
yTheory.Limits.HasPullback…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasEqualizers_and_finite_produc
ts`：hasFiniteLimits_of_hasEqualizers_and_finite_products [HasFiniteProducts C] [
HasEqualizers C] : HasFiniteLimits C where out _
-/
instance hasFiniteLimits {B : C} [HasFiniteWidePullbacks C] : HasFiniteLimits (Over B) := by
  have := ConstructProducts.over_finiteProducts_of_finiteWidePullbacks (B := B)
  have := hasEqualizers_of_hasPullbacks_and_binary_products (C := Over B)
  apply hasFiniteLimits_of_hasEqualizers_and_finite_products
/-
**CategoryTheory.Over.hasLimits** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Over`。
形式化陈述：hasLimits {B : C} [HasWidePullbacks.{w} C] : HasLimitsOfSize.{w, w} (Over 
B)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Over.ConstructProducts.over_binaryProduct_of_pullback`：∀ 
{C : Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.Ha
sPullbacks C] {B : C},   CategoryTheory.Limits.HasBinaryPr…
· 使用定理 `CategoryTheory.Limits.hasPullbacks_of_hasWidePullbacks`：∀ (D : Type u) [
inst : CategoryTheory.Category.{v, u} D] [CategoryTheory.Limits.HasWidePullbacks
 D],   CategoryTheory.Limits.HasPullbacks D
· 使用定理 `CategoryTheory.Limits.hasEqualizers_of_hasPullbacks_and_binary_products`
：hasEqualizers_of_hasPullbacks_and_binary_products [HasBinaryProducts C] [HasPul
lbacks C] : HasEqualizers C
· 使用定理 `CategoryTheory.Over.instHasPullbacks`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {B : C} [CategoryTheory.Limits.HasPullbacks C],   Categor
yTheory.Limits.HasPullback…
· 使用定理 `CategoryTheory.Over.ConstructProducts.over_products_of_widePullbacks`：∀ 
{C : Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.Ha
sWidePullbacks C] {B : C},   CategoryTheory.Limits.HasProd…
· 使用定理 `CategoryTheory.Limits.has_limits_of_hasEqualizers_and_products`：has_limi
ts_of_hasEqualizers_and_products [HasProducts.{w} C] [HasEqualizers C] : HasLimi
tsOfSize.{w, w} C
-/
instance hasLimits {B : C} [HasWidePullbacks.{w} C] : HasLimitsOfSize.{w, w} (Over B) := by
  have := ConstructProducts.over_binaryProduct_of_pullback (B := B)
  have := hasEqualizers_of_hasPullbacks_and_binary_products (C := Over B)
  have := ConstructProducts.over_products_of_widePullbacks (B := B)
  apply has_limits_of_hasEqualizers_and_products

end Over

namespace Under

/-
**CategoryTheory.Under.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Under`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {B : C} [HasFiniteWidePushouts C] : HasFiniteColimits (Under B) := by
  rw [← hasFiniteLimits_opposite_iff]
  exact hasFiniteLimits_of_hasLimitsLimits_of_createsFiniteLimits (Over.opEquivOpUnder _).inverse
/-
**CategoryTheory.Under.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Under`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {B : C} [HasWidePushouts.{w} C] : HasColimitsOfSize.{w, w} (Under B) := by
  rw [← hasLimitsOfSize_opposite_iff]
  exact hasLimits_of_hasLimits_createsLimits (Over.opEquivOpUnder _).inverse

end CategoryTheory.Under

