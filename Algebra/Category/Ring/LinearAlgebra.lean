/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Results on the category of rings requiring linear algebra

## Results

- `CommRingCat.nontrivial_of_isPushout_of_isField`: the pushout of non-trivial rings over a field
  is non-trivial.

-/

public section

universe u

open CategoryTheory Limits TensorProduct

namespace CommRingCat

/--
lemma `nontrivial_of_isPushout_of_isField` / 引理 `nontrivial_of_isPushout_of_isField`

English:
lemma nontrivial_of_isPushout_of_isField
  statement: {A B C D : CommRingCat.{u}}
  proof: by
  let : Field A := hA.toField
  algebraize [f.hom, g.hom]
  let e : D ≅ .of (B otimes[A] C) :=
    IsColimit.coconePointUniqueUpToIso h.isColimit (CommRingCat.pushoutCoconeIsColimit A B C)
  let e' : D ≃ B otimes[A] C := e.commRingCatIsoToRingEquiv.toEquiv
  exact e'.nontrivial

中文:
引理 nontrivial_of_isPushout_of_isField
  结论: {A B C D : CommRingCat.{u}}
  证明: by
  let : Field A := hA.toField
  algebraize [f.hom, g.hom]
  let e : D ≅ .of (B otimes[A] C) :=
    IsColimit.coconePointUniqueUpToIso h.isColimit (CommRingCat.pushoutCoconeIsColimit A B C)
  let e' : D ≃ B otimes[A] C := e.commRingCatIsoToRingEquiv.toEquiv
  exact e'.nontrivial

Depends on / 依赖: CommRingCat, CommRingCat.pushoutCoconeIsColimit, IsColimit, IsColimit.coconePointUniqueUpToIso, algebraize, coconePointUniqueUpToIso, commRingCatIsoToRingEquiv, e.commRingCatIsoToRingEquiv.toEquiv, f.hom, g.hom, h.isColimit, hA.toField, isColimit, nontrivial, otimes, pushoutCoconeIsColimit, toEquiv, toField
-/
lemma nontrivial_of_isPushout_of_isField {A B C D : CommRingCat.{u}}
    (hA : IsField A) {f : A ⟶ B} {g : A ⟶ C} {inl : B ⟶ D} {inr : C ⟶ D}
    [Nontrivial B] [Nontrivial C]
    (h : IsPushout f g inl inr) : Nontrivial D := by
  let : Field A := hA.toField
  algebraize [f.hom, g.hom]
  let e : D ≅ .of (B otimes[A] C) :=
    IsColimit.coconePointUniqueUpToIso h.isColimit (CommRingCat.pushoutCoconeIsColimit A B C)
  let e' : D ≃ B otimes[A] C := e.commRingCatIsoToRingEquiv.toEquiv
  exact e'.nontrivial

end CommRingCat
