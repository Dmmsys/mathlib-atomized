/-
Copyright (c) 2022 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
module

public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Projective
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Projective objects in abelian categories

In an abelian category, an object `P` is projective iff the functor
`preadditiveCoyonedaObj P` preserves finite colimits.

-/

public section

universe v u

namespace CategoryTheory

open Limits Projective Opposite

variable {C : Type u} [Category.{v} C] [Abelian C]

/--
Instance `preservesHomology_preadditiveCoyonedaObj_of_projective` / 实例 `preservesHomology_preadditiveCoyonedaObj_of_projective`

English:
instance preservesHomology_preadditiveCoyonedaObj_of_projective
  body: by
  have := (projective_iff_preservesEpimorphisms_preadditiveCoyonedaObj P).mp hP
  apply Functor.preservesHomology_of_preservesEpis_and_kernels

中文:
实例 preservesHomology_preadditiveCoyonedaObj_of_projective
  定义体: by
  have := (projective_iff_preservesEpimorphisms_preadditiveCoyonedaObj P).mp hP
  apply Functor.preservesHomology_of_preservesEpis_and_kernels

Depends on / 依赖: Functor, Functor.preservesHomology_of_preservesEpis_and_kernels, preservesHomology_of_preservesEpis_and_kernels, projective_iff_preservesEpimorphisms_preadditiveCoyonedaObj
-/
noncomputable instance preservesHomology_preadditiveCoyonedaObj_of_projective
    (P : C) [hP : Projective P] :
    (preadditiveCoyonedaObj P).PreservesHomology := by
  have := (projective_iff_preservesEpimorphisms_preadditiveCoyonedaObj P).mp hP
  apply Functor.preservesHomology_of_preservesEpis_and_kernels

/--
Instance `preservesFiniteColimits_preadditiveCoyonedaObj_of_projective` / 实例 `preservesFiniteColimits_preadditiveCoyonedaObj_of_projective`

English:
instance preservesFiniteColimits_preadditiveCoyonedaObj_of_projective
  body: by
  apply Functor.preservesFiniteColimits_of_preservesHomology

中文:
实例 preservesFiniteColimits_preadditiveCoyonedaObj_of_projective
  定义体: by
  apply Functor.preservesFiniteColimits_of_preservesHomology

Depends on / 依赖: Functor, Functor.preservesFiniteColimits_of_preservesHomology, preservesFiniteColimits_of_preservesHomology
-/
noncomputable instance preservesFiniteColimits_preadditiveCoyonedaObj_of_projective
    (P : C) [hP : Projective P] :
    PreservesFiniteColimits (preadditiveCoyonedaObj P) := by
  apply Functor.preservesFiniteColimits_of_preservesHomology

/--
theorem `projective_of_preservesFiniteColimits_preadditiveCoyonedaObj` / 定理 `projective_of_preservesFiniteColimits_preadditiveCoyonedaObj`

English:
theorem projective_of_preservesFiniteColimits_preadditiveCoyonedaObj
  statement: (P : C)
  proof: by
  rw [projective_iff_preservesEpimorphisms_preadditiveCoyonedaObj]
  have := Functor.preservesHomologyOfExact (preadditiveCoyonedaObj P)
  infer_instance

中文:
定理 projective_of_preservesFiniteColimits_preadditiveCoyonedaObj
  结论: (P : C)
  证明: by
  rw [projective_iff_preservesEpimorphisms_preadditiveCoyonedaObj]
  have := Functor.preservesHomologyOfExact (preadditiveCoyonedaObj P)
  infer_instance

Depends on / 依赖: Functor, Functor.preservesHomologyOfExact, infer_instance, preadditiveCoyonedaObj, preservesHomologyOfExact, projective_iff_preservesEpimorphisms_preadditiveCoyonedaObj
-/
theorem projective_of_preservesFiniteColimits_preadditiveCoyonedaObj (P : C)
    [hP : PreservesFiniteColimits (preadditiveCoyonedaObj P)] : Projective P := by
  rw [projective_iff_preservesEpimorphisms_preadditiveCoyonedaObj]
  have := Functor.preservesHomologyOfExact (preadditiveCoyonedaObj P)
  infer_instance

end CategoryTheory
