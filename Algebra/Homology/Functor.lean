/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Joël Riou
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-!
# Complexes in functor categories

We can view a complex valued in a functor category `T ⥤ V` as
a functor from `T` to complexes valued in `V`.

When `V` is abelian, a morphism of short complexes or homological
complexes in the category `T ⥤ V` is a quasi-isomorphism iff
it is so after evaluation at any `t : T`.

## Future work
In fact there is an equivalence of categories
`HomologicalComplex (T ⥤ V) c ≌ T ⥤ HomologicalComplex V c`.

-/

@[expose] public section


universe v u

open CategoryTheory Limits

variable {T : Type*} [Category* T] {V : Type*} [Category* V]

namespace HomologicalComplex

variable [HasZeroMorphisms V] {ι : Type*} {c : ComplexShape ι}

/-- A complex of functors gives a functor to complexes. -/
@[simps]
/--
Definition of `asFunctor` / `asFunctor` 的定义

English:
definition asFunctor
  signature: (C : HomologicalComplex (T ⥤ V) c)
  body: { X := fun i => (C.X i).obj t
      d := fun i j => (C.d i j).app t
      d_comp_d' := fun i j k _ _ => by
        have := C.d_comp_d i j k
        rw [NatTrans.ext_iff]; rw [funext_iff] at this
        exact this t
      shape := fun i j h => by
        have := C.shape _ _ h
        rw [NatTrans.ex

中文:
定义 asFunctor
  签名: (C : 同调复形 (T ⥤ V) c)
  定义体: { X := fun i => (C.X i).obj t
      d := fun i j => (C.d i j).app t
      d_comp_d' := fun i j k _ _ => by
        have := C.d_comp_d i j k
        rw [NatTrans.ext_iff]; rw [funext_iff] at this
        exact this t
      shape := fun i j h => by
        have := C.shape _ _ h
        rw [NatTrans.ex

Depends on / 依赖: C.d_comp_d, C.shape, Functor, Functor.map_comp, NatTrans, NatTrans.ext_iff, NatTrans.naturality, d_comp_d, ext_iff, funext_iff, map_comp, map_id, naturality
-/
def asFunctor (C : HomologicalComplex (T ⥤ V) c) :
    T ⥤ HomologicalComplex V c where
  obj t :=
    { X := fun i => (C.X i).obj t
      d := fun i j => (C.d i j).app t
      d_comp_d' := fun i j k _ _ => by
        have := C.d_comp_d i j k
        rw [NatTrans.ext_iff]; rw [funext_iff] at this
        exact this t
      shape := fun i j h => by
        have := C.shape _ _ h
        rw [NatTrans.ext_iff]; rw [funext_iff] at this
        exact this t }
  map h :=
    { f := fun i => (C.X i).map h
      comm' := fun _ _ _ => NatTrans.naturality _ _ }
  map_id t := by
    ext i
    dsimp
    rw [(C.X i).map_id]
  map_comp h₁ h₂ := by
    ext i
    dsimp
    rw [Functor.map_comp]

-- TODO in fact, this is an equivalence of categories.
/-- The functorial version of `HomologicalComplex.asFunctor`. -/
@[simps]
/--
Definition of `complexOfFunctorsToFunctorToComplex` / `complexOfFunctorsToFunctorToComplex` 的定义

English:
definition complexOfFunctorsToFunctorToComplex
  signature: :
  body: C.asFunctor
  map f :=
    { app := fun t =>
        { f := fun i => (f.f i).app t
          comm' := fun i j _ => NatTrans.congr_app (f.comm i j) t }
      naturality := fun t t' g => by
        ext i
        exact (f.f i).naturality g }

中文:
定义 complexOfFunctorsToFunctorToComplex
  签名: :
  定义体: C.asFunctor
  map f :=
    { app := fun t =>
        { f := fun i => (f.f i).app t
          comm' := fun i j _ => NatTrans.congr_app (f.comm i j) t }
      naturality := fun t t' g => by
        ext i
        exact (f.f i).naturality g }

Depends on / 依赖: C.asFunctor, asFunctor
-/
def complexOfFunctorsToFunctorToComplex :
    HomologicalComplex (T ⥤ V) c ⥤ T ⥤ HomologicalComplex V c where
  obj C := C.asFunctor
  map f :=
    { app := fun t =>
        { f := fun i => (f.f i).app t
          comm' := fun i j _ => NatTrans.congr_app (f.comm i j) t }
      naturality := fun t t' g => by
        ext i
        exact (f.f i).naturality g }

end HomologicalComplex

namespace CategoryTheory.ShortComplex

variable [Abelian V] {S₁ S₂ : ShortComplex (T ⥤ V)} (f : S₁ ⟶ S₂)

/--
lemma `quasiIso_iff_evaluation` / 引理 `quasiIso_iff_evaluation`

English:
lemma quasiIso_iff_evaluation
  proof: ⟨fun _ => inferInstance, fun hf => by
    rw [quasiIso_iff]; rw [NatTrans.isIso_iff_isIso_app]
    exact fun j => ((MorphismProperty.isomorphisms V).arrow_mk_iso_iff
      (((Functor.mapArrowFunctor _ _).mapIso
      ((homologyFunctorIso ((evaluation T V).obj j)))).app (Arrow.mk f))).1
        ((qua

中文:
引理 quasiIso_iff_evaluation
  证明: ⟨fun _ => inferInstance, fun hf => by
    rw [quasiIso_iff]; rw [NatTrans.isIso_iff_isIso_app]
    exact fun j => ((MorphismProperty.isomorphisms V).arrow_mk_iso_iff
      (((Functor.mapArrowFunctor _ _).mapIso
      ((homologyFunctorIso ((evaluation T V).obj j)))).app (Arrow.mk f))).1
        ((qua

Depends on / 依赖: Arrow.mk, Functor, Functor.mapArrowFunctor, MorphismProperty, MorphismProperty.isomorphisms, NatTrans, NatTrans.isIso_iff_isIso_app, arrow_mk_iso_iff, evaluation, homologyFunctorIso, isIso_iff_isIso_app, isomorphisms, mapArrowFunctor, mapIso, quasiIso_iff
-/
lemma quasiIso_iff_evaluation :
    QuasiIso f ↔ forall (j : T),
      QuasiIso (((evaluation T V).obj j).mapShortComplex.map f) :=
  ⟨fun _ => inferInstance, fun hf => by
    rw [quasiIso_iff]; rw [NatTrans.isIso_iff_isIso_app]
    exact fun j => ((MorphismProperty.isomorphisms V).arrow_mk_iso_iff
      (((Functor.mapArrowFunctor _ _).mapIso
      ((homologyFunctorIso ((evaluation T V).obj j)))).app (Arrow.mk f))).1
        ((quasiIso_iff _).1 (hf j))⟩

end CategoryTheory.ShortComplex

namespace HomologicalComplex

variable [Abelian V] {ι : Type*} {c : ComplexShape ι} {K₁ K₂ : HomologicalComplex (T ⥤ V) c}
  (f : K₁ ⟶ K₂)

/--
lemma `quasiIsoAt_iff_evaluation` / 引理 `quasiIsoAt_iff_evaluation`

English:
lemma quasiIsoAt_iff_evaluation
  given: (i : ι)
  proof: by
  simp only [quasiIsoAt_iff, ShortComplex.quasiIso_iff_evaluation]
  rfl

中文:
引理 quasiIsoAt_iff_evaluation
  条件: (i : ι)
  证明: by
  simp only [quasiIsoAt_iff, ShortComplex.quasiIso_iff_evaluation]
  rfl

Depends on / 依赖: ShortComplex, ShortComplex.quasiIso_iff_evaluation, quasiIsoAt_iff, quasiIso_iff_evaluation
-/
lemma quasiIsoAt_iff_evaluation (i : ι) :
    QuasiIsoAt f i ↔ forall (t : T),
      QuasiIsoAt ((((evaluation T V).obj t).mapHomologicalComplex c).map f) i := by
  simp only [quasiIsoAt_iff, ShortComplex.quasiIso_iff_evaluation]
  rfl

/--
lemma `quasiIso_iff_evaluation` / 引理 `quasiIso_iff_evaluation`

English:
lemma quasiIso_iff_evaluation
  proof: by
  simp only [quasiIso_iff, quasiIsoAt_iff_evaluation]
  tauto

中文:
引理 quasiIso_iff_evaluation
  证明: by
  simp only [quasiIso_iff, quasiIsoAt_iff_evaluation]
  tauto

Depends on / 依赖: quasiIsoAt_iff_evaluation, quasiIso_iff
-/
lemma quasiIso_iff_evaluation :
    QuasiIso f ↔ forall (t : T),
      QuasiIso ((((evaluation T V).obj t).mapHomologicalComplex c).map f) := by
  simp only [quasiIso_iff, quasiIsoAt_iff_evaluation]
  tauto

end HomologicalComplex
