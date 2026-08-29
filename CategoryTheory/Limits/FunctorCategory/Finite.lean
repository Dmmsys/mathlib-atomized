/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!

# Functor categories have finite limits when the target category does

These declarations cannot be in `Mathlib/CategoryTheory/Limits/FunctorCategory/Basic.lean` because
that file shouldn't import `Mathlib/CategoryTheory/Limits/Shapes/FiniteProducts.lean`.
-/

public section

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] {K : Type*} [Category* K]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasFiniteLimits
  signature: C] : HasFiniteLimits (K ⥤ C)
  body: ⟨fun _ => inferInstance⟩

中文:
实例 [有有限极限
  签名: C] : 有有限极限 (K ⥤ C)
  定义体: ⟨fun _ => inferInstance⟩
-/
instance [HasFiniteLimits C] : HasFiniteLimits (K ⥤ C) := ⟨fun _ => inferInstance⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasFiniteProducts
  signature: C] : HasFiniteProducts (K ⥤ C)
  body: ⟨inferInstance⟩

中文:
实例 [有FiniteProducts
  签名: C] : 有FiniteProducts (K ⥤ C)
  定义体: ⟨inferInstance⟩
-/
instance [HasFiniteProducts C] : HasFiniteProducts (K ⥤ C) := ⟨inferInstance⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasFiniteColimits
  signature: C] : HasFiniteColimits (K ⥤ C)
  body: ⟨fun _ => inferInstance⟩

中文:
实例 [有有限余极限
  签名: C] : 有有限余极限 (K ⥤ C)
  定义体: ⟨fun _ => inferInstance⟩
-/
instance [HasFiniteColimits C] : HasFiniteColimits (K ⥤ C) := ⟨fun _ => inferInstance⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasFiniteCoproducts
  signature: C] : HasFiniteCoproducts (K ⥤ C)
  body: ⟨inferInstance⟩

中文:
实例 [有FiniteCoproducts
  签名: C] : 有FiniteCoproducts (K ⥤ C)
  定义体: ⟨inferInstance⟩
-/
instance [HasFiniteCoproducts C] : HasFiniteCoproducts (K ⥤ C) := ⟨inferInstance⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasFiniteLimits
  signature: C] (k
  body: inferInstance

中文:
实例 [有有限极限
  签名: C] (k
  定义体: inferInstance
-/
instance [HasFiniteLimits C] (k : K) : PreservesFiniteLimits ((evaluation K C).obj k) where
  preservesFiniteLimits _ _ _ := inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasFiniteColimits
  signature: C] (k
  body: inferInstance

中文:
实例 [有有限余极限
  签名: C] (k
  定义体: inferInstance
-/
instance [HasFiniteColimits C] (k : K) : PreservesFiniteColimits ((evaluation K C).obj k) where
  preservesFiniteColimits _ _ _ := inferInstance

end CategoryTheory.Limits
