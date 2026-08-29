/-
Copyright (c) 2022 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
module

public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Injective
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Injective objects in abelian categories

* Objects in an abelian category are injective if and only if the preadditive Yoneda functor
  on them preserves finite colimits.
-/

public section


noncomputable section

open CategoryTheory Limits Injective Opposite

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/--
Instance `preservesHomology_preadditiveYonedaObj_of_injective` / 实例 `preservesHomology_preadditiveYonedaObj_of_injective`

English:
instance preservesHomology_preadditiveYonedaObj_of_injective
  signature: (J : C) [hJ : Injective J]
  body: by
  let := (injective_iff_preservesEpimorphisms_preadditive_yoneda_obj' J).mp hJ
  apply Functor.preservesHomology_of_preservesEpis_and_kernels

中文:
实例 preservesHomology_preadditiveYonedaObj_of_injective
  签名: (J : C) [hJ : Injective J]
  定义体: by
  let := (injective_iff_preservesEpimorphisms_preadditive_yoneda_obj' J).mp hJ
  apply Functor.preservesHomology_of_preservesEpis_and_kernels

Depends on / 依赖: Functor, Functor.preservesHomology_of_preservesEpis_and_kernels, injective_iff_preservesEpimorphisms_preadditive_yoneda_obj, preservesHomology_of_preservesEpis_and_kernels
-/
instance preservesHomology_preadditiveYonedaObj_of_injective (J : C) [hJ : Injective J] :
    (preadditiveYonedaObj J).PreservesHomology := by
  let := (injective_iff_preservesEpimorphisms_preadditive_yoneda_obj' J).mp hJ
  apply Functor.preservesHomology_of_preservesEpis_and_kernels

/--
Instance `preservesFiniteColimits_preadditiveYonedaObj_of_injective` / 实例 `preservesFiniteColimits_preadditiveYonedaObj_of_injective`

English:
instance preservesFiniteColimits_preadditiveYonedaObj_of_injective
  signature: (J : C) [hP : Injective J]
  body: by
  apply Functor.preservesFiniteColimits_of_preservesHomology

中文:
实例 preservesFiniteColimits_preadditiveYonedaObj_of_injective
  签名: (J : C) [hP : Injective J]
  定义体: by
  apply Functor.preservesFiniteColimits_of_preservesHomology

Depends on / 依赖: Functor, Functor.preservesFiniteColimits_of_preservesHomology, preservesFiniteColimits_of_preservesHomology
-/
instance preservesFiniteColimits_preadditiveYonedaObj_of_injective (J : C) [hP : Injective J] :
    PreservesFiniteColimits (preadditiveYonedaObj J) := by
  apply Functor.preservesFiniteColimits_of_preservesHomology

/--
theorem `injective_of_preservesFiniteColimits_preadditiveYonedaObj` / 定理 `injective_of_preservesFiniteColimits_preadditiveYonedaObj`

English:
theorem injective_of_preservesFiniteColimits_preadditiveYonedaObj
  statement: (J : C)
  proof: by
  rw [injective_iff_preservesEpimorphisms_preadditive_yoneda_obj']
  have := Functor.preservesHomologyOfExact (preadditiveYonedaObj J)
  infer_instance

中文:
定理 injective_of_preservesFiniteColimits_preadditiveYonedaObj
  结论: (J : C)
  证明: by
  rw [injective_iff_preservesEpimorphisms_preadditive_yoneda_obj']
  have := Functor.preservesHomologyOfExact (preadditiveYonedaObj J)
  infer_instance

Depends on / 依赖: Functor, Functor.preservesHomologyOfExact, infer_instance, injective_iff_preservesEpimorphisms_preadditive_yoneda_obj, preadditiveYonedaObj, preservesHomologyOfExact
-/
theorem injective_of_preservesFiniteColimits_preadditiveYonedaObj (J : C)
    [hP : PreservesFiniteColimits (preadditiveYonedaObj J)] : Injective J := by
  rw [injective_iff_preservesEpimorphisms_preadditive_yoneda_obj']
  have := Functor.preservesHomologyOfExact (preadditiveYonedaObj J)
  infer_instance

end CategoryTheory
