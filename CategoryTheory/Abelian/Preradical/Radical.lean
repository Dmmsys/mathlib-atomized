/-
Copyright (c) 2026 Blake Farman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Blake Farman
-/
module

public import Mathlib.CategoryTheory.Abelian.Preradical.Basic
public import Mathlib.CategoryTheory.Abelian.Preradical.Colon
public import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-!
# Radicals

In this file we define what it means for a preradical `Φ : Preradical C` on an
abelian category `C` to be *radical*, and we define `Radical C` as the full
subcategory of `Preradical C` consisting of radicals.

Following Stenström, a preradical `Φ` is called radical if it coincides with its self colon.
We encode this as the property that the natural transformation `toColon Φ Φ : Φ ⟶ Φ.colon Φ`
is an isomorphism, and we prove a basic characterization of radicals in terms
of the vanishing of `Φ.r` on `Φ.quotient`.


## Main definitions

* `Preradical.IsRadical` :
  The property that a preradical `Φ` is radical, i.e. that `(Φ.colon Φ) ≅ Φ`.

* `Radical C` :
  The type of radicals on `C`, as a full subcategory of `Preradical C`.

## Main results

* `Preradical.isRadical_iff_isZero` :
  A preradical `Φ` is radical if and only if `Φ.quotient ⋙ Φ.r` is the zero object.

## References

* [Bo Stenström, Rings and Modules of Quotients][stenstrom1971]
* [Bo Stenström, *Rings of Quotients*][stenstrom1975]

## Tags

preradical, radical, torsion theory, abelian
-/

@[expose] public section

namespace CategoryTheory.Abelian
open CategoryTheory.Limits

variable {C : Type*} [Category* C] [Abelian C]

namespace Preradical

variable (C)
/--
Definition of `isRadical` / `isRadical` 的定义

English:
definition isRadical
  signature: : ObjectProperty (Preradical C)
  body: fun Φ => IsIso (toColon Φ Φ)

中文:
定义 isRadical
  签名: : ObjectProperty (Preradical C)
  定义体: fun Φ => IsIso (toColon Φ Φ)

Depends on / 依赖: toColon
-/
def isRadical : ObjectProperty (Preradical C) :=
  fun Φ => IsIso (toColon Φ Φ)

/--
lemma `isRadical_iff_isIso` / 引理 `isRadical_iff_isIso`

English:
lemma isRadical_iff_isIso
  given: (Φ : Preradical C)
  proof: Iff.rfl

中文:
引理 isRadical_iff_isIso
  条件: (Φ : Preradical C)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma isRadical_iff_isIso (Φ : Preradical C) :
    isRadical C Φ ↔ IsIso (toColon Φ Φ) :=
  Iff.rfl

/--
lemma `isRadical_iff_isZero` / 引理 `isRadical_iff_isZero`

English:
lemma isRadical_iff_isZero
  given: (Φ : Preradical C)
  proof: by
  rw [isRadical_iff_isIso]; rw [isIso_toColon_iff]

中文:
引理 isRadical_iff_isZero
  条件: (Φ : Preradical C)
  证明: by
  rw [isRadical_iff_isIso]; rw [isIso_toColon_iff]

Depends on / 依赖: isIso_toColon_iff, isRadical_iff_isIso
-/
lemma isRadical_iff_isZero (Φ : Preradical C) :
    isRadical C Φ ↔ IsZero (Φ.quotient ⋙ Φ.r) := by
  rw [isRadical_iff_isIso]; rw [isIso_toColon_iff]

end Preradical

variable (C) in
/--
Definition of `Radical` / `Radical` 的定义

English:
abbreviation Radical
  body: (Preradical.isRadical C).FullSubcategory

中文:
缩写 Radical
  定义体: (Preradical.isRadical C).FullSubcategory

Depends on / 依赖: FullSubcategory, Preradical, Preradical.isRadical, isRadical
-/
abbrev Radical := (Preradical.isRadical C).FullSubcategory

namespace Radical

instance (Φ : Radical C) : IsIso (Preradical.toColon Φ.obj Φ.obj) := Φ.property

/--
lemma `isZero` / 引理 `isZero`

English:
lemma isZero
  given: (Φ : Radical C)
  statement: IsZero (Φ.obj.quotient ⋙ Φ.obj.r)
  proof: by
  rw [← Preradical.isRadical_iff_isZero]; rw [Preradical.isRadical_iff_isIso]
  infer_instance

中文:
引理 isZero
  条件: (Φ : Radical C)
  结论: 是零 (Φ.obj.quotient ⋙ Φ.obj.r)
  证明: by
  rw [← Preradical.isRadical_iff_isZero]; rw [Preradical.isRadical_iff_isIso]
  infer_instance

Depends on / 依赖: Preradical, Preradical.isRadical_iff_isIso, Preradical.isRadical_iff_isZero, infer_instance, isRadical_iff_isIso, isRadical_iff_isZero
-/
lemma isZero (Φ : Radical C) : IsZero (Φ.obj.quotient ⋙ Φ.obj.r) := by
  rw [← Preradical.isRadical_iff_isZero]; rw [Preradical.isRadical_iff_isIso]
  infer_instance

end Radical

end CategoryTheory.Abelian
