/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Properties of objects that are closed under subobjects and quotients

Given a category `C` and `P : ObjectProperty C`, we define type classes
`P.IsClosedUnderSubobjects` and `P.IsClosedUnderQuotients` expressing
that `P` is closed under subobjects (resp. quotients).

-/

public section

universe v v' u u'

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

namespace ObjectProperty

variable (P : ObjectProperty C)

/--
Definition of `IsClosedUnderSubobjects` / `IsClosedUnderSubobjects` 的定义

English:
class IsClosedUnderSubobjects
  parameters: : Prop where
  axioms and operations (1):
    - prop_of_mono({X Y : C} (f : X ⟶ Y) [Mono f] (hY : P Y)) : P X

中文:
类 IsClosedUnderSubobjects
  参数: : 命题 where
  公理与运算 (1 个):
    - prop_of_mono({X Y : C} (f : X ⟶ Y) [Mono f] (hY : P Y)) : P X
-/
class IsClosedUnderSubobjects : Prop where
  prop_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] (hY : P Y) : P X

section

variable [P.IsClosedUnderSubobjects]

/--
lemma `prop_of_mono` / 引理 `prop_of_mono`

English:
lemma prop_of_mono
  given: {X Y : C} (f : X ⟶ Y) [Mono f] (hY : P Y)
  statement: P X
  proof: IsClosedUnderSubobjects.prop_of_mono f hY

中文:
引理 prop_of_mono
  条件: {X Y : C} (f : X ⟶ Y) [Mono f] (hY : P Y)
  结论: P X
  证明: IsClosedUnderSubobjects.prop_of_mono f hY

Depends on / 依赖: IsClosedUnderSubobjects, IsClosedUnderSubobjects.prop_of_mono, prop_of_mono
-/
lemma prop_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] (hY : P Y) : P X :=
  IsClosedUnderSubobjects.prop_of_mono f hY

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: P.IsClosedUnderIsomorphisms
  body: P.prop_of_mono e.inv

中文:
实例 :
  签名: P.IsClosedUnderIsomorphisms
  定义体: P.prop_of_mono e.inv

Depends on / 依赖: P.prop_of_mono, e.inv, prop_of_mono
-/
instance : P.IsClosedUnderIsomorphisms where
  of_iso e := P.prop_of_mono e.inv

/--
lemma `prop_X₁_of_shortExact` / 引理 `prop_X₁_of_shortExact`

English:
lemma prop_X₁_of_shortExact
  statement: [HasZeroMorphisms C] {S : ShortComplex C} (hS : S.ShortExact)
  proof: by
  have := hS.mono_f
  exact P.prop_of_mono S.f h₂

中文:
引理 prop_X₁_of_shortExact
  结论: [HasZeroMorphisms C] {S : ShortComplex C} (hS : S.ShortExact)
  证明: by
  have := hS.mono_f
  exact P.prop_of_mono S.f h₂

Depends on / 依赖: P.prop_of_mono, hS.mono_f, mono_f, prop_of_mono
-/
lemma prop_X₁_of_shortExact [HasZeroMorphisms C] {S : ShortComplex C} (hS : S.ShortExact)
    (h₂ : P S.X₂) : P S.X₁ := by
  have := hS.mono_f
  exact P.prop_of_mono S.f h₂

instance (F : D ⥤ C) [F.PreservesMonomorphisms] :
    (P.inverseImage F).IsClosedUnderSubobjects where
  prop_of_mono f _ h := P.prop_of_mono (F.map f) h

end

section

/--
Definition of `IsClosedUnderQuotients` / `IsClosedUnderQuotients` 的定义

English:
class IsClosedUnderQuotients
  parameters: : Prop where
  axioms and operations (1):
    - prop_of_epi({X Y : C} (f : X ⟶ Y) [Epi f] (hX : P X)) : P Y

中文:
类 IsClosedUnderQuotients
  参数: : 命题 where
  公理与运算 (1 个):
    - prop_of_epi({X Y : C} (f : X ⟶ Y) [Epi f] (hX : P X)) : P Y
-/
class IsClosedUnderQuotients : Prop where
  prop_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] (hX : P X) : P Y

variable [P.IsClosedUnderQuotients]

/--
lemma `prop_of_epi` / 引理 `prop_of_epi`

English:
lemma prop_of_epi
  given: {X Y : C} (f : X ⟶ Y) [Epi f] (hX : P X)
  statement: P Y
  proof: IsClosedUnderQuotients.prop_of_epi f hX

中文:
引理 prop_of_epi
  条件: {X Y : C} (f : X ⟶ Y) [Epi f] (hX : P X)
  结论: P Y
  证明: IsClosedUnderQuotients.prop_of_epi f hX

Depends on / 依赖: IsClosedUnderQuotients, IsClosedUnderQuotients.prop_of_epi, isLE_of_iso, isLE_of_le, isLE_truncLT_obj, prop_of_epi, t.isLE_iff_isIso_truncLT, t.isLE_of_iso, t.isLE_of_le, t.isLE_truncLT_obj, t.truncLT
-/
lemma prop_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] (hX : P X) : P Y :=
  IsClosedUnderQuotients.prop_of_epi f hX

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: P.IsClosedUnderIsomorphisms
  body: P.prop_of_epi e.hom

中文:
实例 :
  签名: P.IsClosedUnderIsomorphisms
  定义体: P.prop_of_epi e.hom

Depends on / 依赖: P.prop_of_epi, e.hom, isGE_of_ge, isGE_of_iso, isGE_truncGE_obj, prop_of_epi, t.IsGE, t.isGE_of_ge, t.isGE_of_iso, t.isGE_truncGE_obj, t.truncGE
-/
instance : P.IsClosedUnderIsomorphisms where
  of_iso e := P.prop_of_epi e.hom

/--
lemma `prop_X₃_of_shortExact` / 引理 `prop_X₃_of_shortExact`

English:
lemma prop_X₃_of_shortExact
  statement: [HasZeroMorphisms C] {S : ShortComplex C} (hS : S.ShortExact)
  proof: by
  have := hS.epi_g
  exact P.prop_of_epi S.g h₂

中文:
引理 prop_X₃_of_shortExact
  结论: [HasZeroMorphisms C] {S : ShortComplex C} (hS : S.ShortExact)
  证明: by
  have := hS.epi_g
  exact P.prop_of_epi S.g h₂

Depends on / 依赖: P.prop_of_epi, epi_g, hS.epi_g, prop_of_epi
-/
lemma prop_X₃_of_shortExact [HasZeroMorphisms C] {S : ShortComplex C} (hS : S.ShortExact)
    (h₂ : P S.X₂) : P S.X₃ := by
  have := hS.epi_g
  exact P.prop_of_epi S.g h₂

instance (F : D ⥤ C) [F.PreservesEpimorphisms] :
    (P.inverseImage F).IsClosedUnderQuotients where
  prop_of_epi f _ h := P.prop_of_epi (F.map f) h

end

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (⊤ : ObjectProperty C).IsClosedUnderSubobjects
  body: by simp

中文:
实例 :
  签名: (⊤ : Object命题erty C).IsClosedUnderSubobjects
  定义体: by simp
-/
instance : (⊤ : ObjectProperty C).IsClosedUnderSubobjects where
  prop_of_mono := by simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (⊤ : ObjectProperty C).IsClosedUnderQuotients
  body: by simp

中文:
实例 :
  签名: (⊤ : Object命题erty C).IsClosedUnderQuotients
  定义体: by simp

Depends on / 依赖: infer_instance
-/
instance : (⊤ : ObjectProperty C).IsClosedUnderQuotients where
  prop_of_epi := by simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasZeroMorphisms
  signature: C] : IsClosedUnderSubobjects (IsZero (C := C)) where
  body: IsZero.of_mono f hX

中文:
实例 [HasZeroMorphisms
  签名: C] : IsClosedUnderSubobjects (IsZero (C := C)) where
  定义体: IsZero.of_mono f hX

Depends on / 依赖: infer_instance
-/
instance [HasZeroMorphisms C] : IsClosedUnderSubobjects (IsZero (C := C)) where
  prop_of_mono f _ hX := IsZero.of_mono f hX

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasZeroMorphisms
  signature: C] : IsClosedUnderQuotients (IsZero (C := C)) where
  body: IsZero.of_epi f hX

中文:
实例 [HasZeroMorphisms
  签名: C] : IsClosedUnderQuotients (IsZero (C := C)) where
  定义体: IsZero.of_epi f hX
-/
instance [HasZeroMorphisms C] : IsClosedUnderQuotients (IsZero (C := C)) where
  prop_of_epi f _ hX := IsZero.of_epi f hX

end ObjectProperty

end CategoryTheory
