/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.EpiMono
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Serre classes

For any abelian category `C`, we introduce a type class `IsSerreClass C` for
Serre classes in `C` (also known as "Serre subcategories"). A Serre class is
a property `P : ObjectProperty C` of objects in `C` which holds for a zero object,
and is closed under subobjects, quotients and extensions.

## Future work

* Show that the localization of `C` with respect to a Serre class is an abelian category.

## References

* [Jean-Pierre Serre, *Groupes d'homotopie et classes de groupes abéliens*][serre1958]

-/

public section

universe v v' u u'

namespace CategoryTheory

open Limits ZeroObject

variable {C : Type u} [Category.{v} C] [Abelian C] (P : ObjectProperty C)
  {D : Type u'} [Category.{v'} D] [Abelian D]

namespace ObjectProperty

/--
Definition of `IsSerreClass` / `IsSerreClass` 的定义

English:
class IsSerreClass
  parameters: : Prop extends P.ContainsZero,
  extends: P.ContainsZero, 
  (no additional axioms)

中文:
类 是Serre类
  参数: : 命题 extends P.余ntainsZero,
  继承: P.余ntainsZero, 
  (无附加公理)
-/
class IsSerreClass : Prop extends P.ContainsZero,
    P.IsClosedUnderSubobjects, P.IsClosedUnderQuotients,
    P.IsClosedUnderExtensions where

variable [P.IsSerreClass]

example : P.IsClosedUnderIsomorphisms := inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (⊤ : ObjectProperty C).IsSerreClass

中文:
实例 :
  签名: (⊤ : ObjectProperty C).是Serre类
-/
instance : (⊤ : ObjectProperty C).IsSerreClass where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSerreClass (IsZero (C := C))

中文:
实例 :
  签名: 是Serre类 (是零 (C := C))
-/
instance : IsSerreClass (IsZero (C := C)) where

/--
lemma `prop_iff_of_shortExact` / 引理 `prop_iff_of_shortExact`

English:
lemma prop_iff_of_shortExact
  given: {S : ShortComplex C} (hS : S.ShortExact)
  proof: ⟨fun h => ⟨P.prop_X₁_of_shortExact hS h, P.prop_X₃_of_shortExact hS h⟩,
    fun h => P.prop_X₂_of_shortExact hS h.1 h.2⟩

中文:
引理 prop_iff_of_shortExact
  条件: {S : 短复形 C} (hS : S.短正合)
  证明: ⟨fun h => ⟨P.prop_X₁_of_shortExact hS h, P.prop_X₃_of_shortExact hS h⟩,
    fun h => P.prop_X₂_of_shortExact hS h.1 h.2⟩

Depends on / 依赖: P.prop_X
-/
lemma prop_iff_of_shortExact {S : ShortComplex C} (hS : S.ShortExact) :
    P S.X₂ ↔ P S.X₁ ∧ P S.X₃ :=
  ⟨fun h => ⟨P.prop_X₁_of_shortExact hS h, P.prop_X₃_of_shortExact hS h⟩,
    fun h => P.prop_X₂_of_shortExact hS h.1 h.2⟩

/--
lemma `prop_X₂_of_exact` / 引理 `prop_X₂_of_exact`

English:
lemma prop_X₂_of_exact
  statement: {S : ShortComplex C} (hS : S.Exact)
  proof: by
  let d := S.homologyData
  have := hS.epi_f' d.left
  have := hS.mono_g' d.right
  exact (P.prop_X₂_of_shortExact (hS.shortExact d)
    (P.prop_of_epi d.left.f' h₁) (P.prop_of_mono d.right.g' h₃) :)

中文:
引理 prop_X₂_of_exact
  结论: {S : 短复形 C} (hS : S.正合)
  证明: by
  let d := S.homologyData
  have := hS.epi_f' d.left
  have := hS.mono_g' d.right
  exact (P.prop_X₂_of_shortExact (hS.shortExact d)
    (P.prop_of_epi d.left.f' h₁) (P.prop_of_mono d.right.g' h₃) :)

Depends on / 依赖: P.prop_X, P.prop_of_epi, P.prop_of_mono, S.homologyData, d.left, d.left.f, d.right, d.right.g, epi_f, hS.epi_f, hS.mono_g, hS.shortExact, homologyData, mono_g, prop_of_epi, prop_of_mono, shortExact
-/
lemma prop_X₂_of_exact {S : ShortComplex C} (hS : S.Exact)
    (h₁ : P S.X₁) (h₃ : P S.X₃) : P S.X₂ := by
  let d := S.homologyData
  have := hS.epi_f' d.left
  have := hS.mono_g' d.right
  exact (P.prop_X₂_of_shortExact (hS.shortExact d)
    (P.prop_of_epi d.left.f' h₁) (P.prop_of_mono d.right.g' h₃) :)

instance (F : D ⥤ C) [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] :
    (P.inverseImage F).IsSerreClass where

end ObjectProperty

end CategoryTheory
