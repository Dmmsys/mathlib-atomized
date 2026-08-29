/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.ObjectProperty.Basic

/-!
# Properties of objects that are closed under extensions

Given a category `C` and `P : ObjectProperty C`, we define a type
class `P.IsClosedUnderExtensions` expressing that the property
is closed under extensions.

-/

public section

universe v v' u u'

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

namespace ObjectProperty

variable (P : ObjectProperty C)

section

variable [HasZeroMorphisms C]

/--
Definition of `IsClosedUnderExtensions` / `IsClosedUnderExtensions` 的定义

English:
class IsClosedUnderExtensions
  parameters: : Prop where
  axioms and operations (1):
    - prop_X₂_of_shortExact({S : ShortComplex C} (hS : S.ShortExact) (h₁ : P S.X₁) (h₃ : P S.X₃)) : P S.X₂

中文:
类 IsClosedUnderExtensions
  参数: : 命题 where
  公理与运算 (1 个):
    - prop_X₂_of_shortExact({S : ShortComplex C} (hS : S.ShortExact) (h₁ : P S.X₁) (h₃ : P S.X₃)) : P S.X₂
-/
class IsClosedUnderExtensions : Prop where
  prop_X₂_of_shortExact {S : ShortComplex C} (hS : S.ShortExact)
      (h₁ : P S.X₁) (h₃ : P S.X₃) : P S.X₂

/--
lemma `prop_X₂_of_shortExact` / 引理 `prop_X₂_of_shortExact`

English:
lemma prop_X₂_of_shortExact
  statement: [P.IsClosedUnderExtensions]
  proof: IsClosedUnderExtensions.prop_X₂_of_shortExact hS h₁ h₃

中文:
引理 prop_X₂_of_shortExact
  结论: [P.IsClosedUnderExtensions]
  证明: IsClosedUnderExtensions.prop_X₂_of_shortExact hS h₁ h₃

Depends on / 依赖: IsClosedUnderExtensions, IsClosedUnderExtensions.prop_X
-/
lemma prop_X₂_of_shortExact [P.IsClosedUnderExtensions]
    {S : ShortComplex C} (hS : S.ShortExact)
    (h₁ : P S.X₁) (h₃ : P S.X₃) : P S.X₂ :=
  IsClosedUnderExtensions.prop_X₂_of_shortExact hS h₁ h₃

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (⊤ : ObjectProperty C).IsClosedUnderExtensions
  body: by simp

中文:
实例 :
  签名: (⊤ : Object命题erty C).IsClosedUnderExtensions
  定义体: by simp
-/
instance : (⊤ : ObjectProperty C).IsClosedUnderExtensions where
  prop_X₂_of_shortExact := by simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsClosedUnderExtensions (IsZero (C := C))
  body: hS.exact.isZero_of_both_isZero h₁ h₃

中文:
实例 :
  签名: IsClosedUnderExtensions (IsZero (C := C))
  定义体: hS.exact.isZero_of_both_isZero h₁ h₃

Depends on / 依赖: t.isIso_truncGE_map_truncGE
-/
instance : IsClosedUnderExtensions (IsZero (C := C)) where
  prop_X₂_of_shortExact hS h₁ h₃ :=
    hS.exact.isZero_of_both_isZero h₁ h₃

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsClosedUnderExtensions]
  signature: (F : D ⥤ C)
  body: by
    have := hS.mono_f
    have := hS.epi_g
    exact P.prop_X₂_of_shortExact (hS.map F) h₁ h₃

中文:
实例 [P.IsClosedUnderExtensions]
  签名: (F : D ⥤ C)
  定义体: by
    have := hS.mono_f
    have := hS.epi_g
    exact P.prop_X₂_of_shortExact (hS.map F) h₁ h₃

Depends on / 依赖: P.prop_X, epi_g, hS.epi_g, hS.map, hS.mono_f, infer_instance, mono_f, t.isLE_iff_isIso_truncLT
-/
instance [P.IsClosedUnderExtensions] (F : D ⥤ C)
    [HasZeroMorphisms D] [F.PreservesZeroMorphisms]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (P.inverseImage F).IsClosedUnderExtensions where
  prop_X₂_of_shortExact hS h₁ h₃ := by
    have := hS.mono_f
    have := hS.epi_g
    exact P.prop_X₂_of_shortExact (hS.map F) h₁ h₃

end

/--
lemma `prop_biprod` / 引理 `prop_biprod`

English:
lemma prop_biprod
  statement: {X₁ X₂ : C} (h₁ : P X₁) (h₂ : P X₂) [Preadditive C] [HasZeroObject C]
  proof: P.prop_X₂_of_shortExact
    (ShortComplex.Splitting.ofHasBinaryBiproduct X₁ X₂).shortExact h₁ h₂

中文:
引理 prop_biprod
  结论: {X₁ X₂ : C} (h₁ : P X₁) (h₂ : P X₂) [Preadditive C] [HasZeroObject C]
  证明: P.prop_X₂_of_shortExact
    (ShortComplex.Splitting.ofHasBinaryBiproduct X₁ X₂).shortExact h₁ h₂

Depends on / 依赖: P.prop_X, ShortComplex, ShortComplex.Splitting.ofHasBinaryBiproduct, Splitting, ofHasBinaryBiproduct, shortExact
-/
lemma prop_biprod {X₁ X₂ : C} (h₁ : P X₁) (h₂ : P X₂) [Preadditive C] [HasZeroObject C]
    [P.IsClosedUnderExtensions] [HasBinaryBiproduct X₁ X₂] :
    P (X₁ ⊞ X₂) :=
  P.prop_X₂_of_shortExact
    (ShortComplex.Splitting.ofHasBinaryBiproduct X₁ X₂).shortExact h₁ h₂

end ObjectProperty

end CategoryTheory
