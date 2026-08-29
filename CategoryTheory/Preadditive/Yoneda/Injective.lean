/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-!
An object is injective iff the preadditive yoneda functor on it preserves epimorphisms.
-/

public section


universe v u

open Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

section Preadditive

variable [Preadditive C]

namespace Injective

/--
theorem `injective_iff_preservesEpimorphisms_preadditiveYoneda_obj` / 定理 `injective_iff_preservesEpimorphisms_preadditiveYoneda_obj`

English:
theorem injective_iff_preservesEpimorphisms_preadditiveYoneda_obj
  given: (J : C)
  proof: by
  rw [injective_iff_preservesEpimorphisms_yoneda_obj]
  refine
    ⟨fun h : (preadditiveYoneda.obj J ⋙ (forget AddCommGrpCat)).PreservesEpimorphisms => ?_, ?_⟩
  · exact
      Functor.preservesEpimorphisms_of_preserves_of_reflects (preadditiveYoneda.obj J) (forget _)
  · intro
    exact (inferIns

中文:
定理 injective_iff_preservesEpimorphisms_preadditiveYoneda_obj
  条件: (J : C)
  证明: by
  rw [injective_iff_preservesEpimorphisms_yoneda_obj]
  refine
    ⟨fun h : (preadditiveYoneda.obj J ⋙ (forget AddCommGrpCat)).PreservesEpimorphisms => ?_, ?_⟩
  · exact
      Functor.preservesEpimorphisms_of_preserves_of_reflects (preadditiveYoneda.obj J) (forget _)
  · intro
    exact (inferIns

Depends on / 依赖: AddCommGrpCat, Functor, Functor.preservesEpimorphisms_of_preserves_of_reflects, PreservesEpimorphisms, forget, injective_iff_preservesEpimorphisms_yoneda_obj, preadditiveYoneda, preadditiveYoneda.obj, preservesEpimorphisms_of_preserves_of_reflects
-/
theorem injective_iff_preservesEpimorphisms_preadditiveYoneda_obj (J : C) :
    Injective J ↔ (preadditiveYoneda.obj J).PreservesEpimorphisms := by
  rw [injective_iff_preservesEpimorphisms_yoneda_obj]
  refine
    ⟨fun h : (preadditiveYoneda.obj J ⋙ (forget AddCommGrpCat)).PreservesEpimorphisms => ?_, ?_⟩
  · exact
      Functor.preservesEpimorphisms_of_preserves_of_reflects (preadditiveYoneda.obj J) (forget _)
  · intro
    exact (inferInstance : (preadditiveYoneda.obj J ⋙ forget _).PreservesEpimorphisms)

/--
theorem `injective_iff_preservesEpimorphisms_preadditive_yoneda_obj'` / 定理 `injective_iff_preservesEpimorphisms_preadditive_yoneda_obj'`

English:
theorem injective_iff_preservesEpimorphisms_preadditive_yoneda_obj'
  given: (J : C)
  proof: by
  rw [injective_iff_preservesEpimorphisms_yoneda_obj]
  refine ⟨fun h : (preadditiveYonedaObj J ⋙ (forget <| ModuleCat (End J))).PreservesEpimorphisms =>
    ?_, ?_⟩
  · exact
      Functor.preservesEpimorphisms_of_preserves_of_reflects (preadditiveYonedaObj J) (forget _)
  · intro
    exact (inf

中文:
定理 injective_iff_preservesEpimorphisms_preadditive_yoneda_obj'
  条件: (J : C)
  证明: by
  rw [injective_iff_preservesEpimorphisms_yoneda_obj]
  refine ⟨fun h : (preadditiveYonedaObj J ⋙ (forget <| ModuleCat (End J))).PreservesEpimorphisms =>
    ?_, ?_⟩
  · exact
      Functor.preservesEpimorphisms_of_preserves_of_reflects (preadditiveYonedaObj J) (forget _)
  · intro
    exact (inf

Depends on / 依赖: Functor, Functor.preservesEpimorphisms_of_preserves_of_reflects, ModuleCat, PreservesEpimorphisms, forget, injective_iff_preservesEpimorphisms_yoneda_obj, preadditiveYonedaObj, preservesEpimorphisms_of_preserves_of_reflects
-/
theorem injective_iff_preservesEpimorphisms_preadditive_yoneda_obj' (J : C) :
    Injective J ↔ (preadditiveYonedaObj J).PreservesEpimorphisms := by
  rw [injective_iff_preservesEpimorphisms_yoneda_obj]
  refine ⟨fun h : (preadditiveYonedaObj J ⋙ (forget <| ModuleCat (End J))).PreservesEpimorphisms =>
    ?_, ?_⟩
  · exact
      Functor.preservesEpimorphisms_of_preserves_of_reflects (preadditiveYonedaObj J) (forget _)
  · intro
    exact (inferInstance : (preadditiveYonedaObj J ⋙ forget _).PreservesEpimorphisms)

end Injective

end Preadditive

end CategoryTheory
