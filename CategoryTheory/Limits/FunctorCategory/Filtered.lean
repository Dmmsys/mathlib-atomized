/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Filtered

/-!
# Functor categories have filtered colimits when the target category does

These declarations cannot be in `Mathlib/CategoryTheory/Limits/FunctorCategory/Basic.lean` because
that file shouldn't import `Mathlib/CategoryTheory/Limits/Filtered.lean`.
-/

public section

universe w' w v₁ v₂ u₁ u₂

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] {K : Type u₂} [Category.{v₂} K]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasFilteredColimitsOfSize.{w',
  signature: w} C] : HasFilteredColimitsOfSize.{w', w} (K ⥤ C)
  body: ⟨fun _ => inferInstance⟩

中文:
实例 [有FilteredColimitsOfSize.{w',
  签名: w} C] : 有FilteredColimitsOfSize.{w', w} (K ⥤ C)
  定义体: ⟨fun _ => inferInstance⟩
-/
instance [HasFilteredColimitsOfSize.{w', w} C] : HasFilteredColimitsOfSize.{w', w} (K ⥤ C) :=
  ⟨fun _ => inferInstance⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasCofilteredLimitsOfSize.{w',
  signature: w} C] : HasCofilteredLimitsOfSize.{w', w} (K ⥤ C)
  body: ⟨fun _ => inferInstance⟩

中文:
实例 [有余filteredLimitsOfSize.{w',
  签名: w} C] : 有余filteredLimitsOfSize.{w', w} (K ⥤ C)
  定义体: ⟨fun _ => inferInstance⟩
-/
instance [HasCofilteredLimitsOfSize.{w', w} C] : HasCofilteredLimitsOfSize.{w', w} (K ⥤ C) :=
  ⟨fun _ => inferInstance⟩

end CategoryTheory.Limits
