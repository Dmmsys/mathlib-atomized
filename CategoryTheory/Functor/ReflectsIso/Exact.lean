/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Exactness properties of functors which jointly reflect isomorphisms

Let `Fᵢ : C ⥤ Dᵢ` be a family of exact functors between abelian categories.
Assume that they jointly reflect isomorphisms. We show that a short complex in `C`
is exact (resp. short exact) iff it is so after applying the functor `Fᵢ`.
Similar results are obtained for the detection of quasi-isomorphisms
between short complexes or homological complexes in `C`.
(Corresponding results for a single functor are
`HomologicalComplex.quasiIsoAt_map_iff_of_preservesHomology` and
`HomologicalComplex.quasiIso_map_iff_of_preservesHomology` in the files
`Mathlib/Algebra/Homology/QuasiIso.lean` and
`ShortComplex.quasiIso_map_iff_of_preservesLeftHomology`
`Mathlib/Algebra/Homology/ShortComplex/PreservesHomology.lean`.)

-/

public section

namespace CategoryTheory

open Category Limits ZeroObject

variable {C : Type*} [Category* C] {I : Type*} {D : I -> Type*} [forall i, Category* (D i)]
  {F : forall i, C ⥤ D i}

namespace JointlyReflectIsomorphisms

variable (hP : JointlyReflectIsomorphisms F)

include hP

section

variable [HasZeroMorphisms C] [forall i, HasZeroMorphisms (D i)]
  [forall i, (F i).PreservesZeroMorphisms]

/--
lemma `isZero_iff` / 引理 `isZero_iff`

English:
lemma isZero_iff
  given: [HasZeroObject C] {X : C}
  proof: by
  refine ⟨fun hX _ => Functor.map_isZero _ hX, fun hX => ?_⟩
  let φ : 0 ⟶ X := 0
  have : IsIso φ := by
    rw [hP.isIso_iff]
    exact fun i => (Functor.map_isZero _ (isZero_zero _)).isIso (hX i) _
  exact (isZero_zero C).of_iso (asIso φ).symm

中文:
引理 isZero_iff
  条件: [HasZeroObject C] {X : C}
  证明: by
  refine ⟨fun hX _ => Functor.map_isZero _ hX, fun hX => ?_⟩
  let φ : 0 ⟶ X := 0
  have : IsIso φ := by
    rw [hP.isIso_iff]
    exact fun i => (Functor.map_isZero _ (isZero_zero _)).isIso (hX i) _
  exact (isZero_zero C).of_iso (asIso φ).symm

Depends on / 依赖: Functor, Functor.map_isZero, hP.isIso_iff, isIso_iff, isZero_zero, map_isZero, of_iso
-/
lemma isZero_iff [HasZeroObject C] {X : C} :
    IsZero X ↔ forall (i : I), IsZero ((F i).obj X) := by
  refine ⟨fun hX _ => Functor.map_isZero _ hX, fun hX => ?_⟩
  let φ : 0 ⟶ X := 0
  have : IsIso φ := by
    rw [hP.isIso_iff]
    exact fun i => (Functor.map_isZero _ (isZero_zero _)).isIso (hX i) _
  exact (isZero_zero C).of_iso (asIso φ).symm

variable [CategoryWithHomology C] [forall i, (F i).PreservesHomology]

/--
lemma `exact_iff` / 引理 `exact_iff`

English:
lemma exact_iff
  given: [HasZeroObject C] (S : ShortComplex C)
  proof: by
  refine ⟨fun hS i => hS.map _, fun hS => ?_⟩
  simp only [ShortComplex.exact_iff_isZero_homology] at hS ⊢
  rw [hP.isZero_iff]
  exact fun i => (hS i).of_iso (S.mapHomologyIso (F i)).symm

中文:
引理 exact_iff
  条件: [HasZeroObject C] (S : ShortComplex C)
  证明: by
  refine ⟨fun hS i => hS.map _, fun hS => ?_⟩
  simp only [ShortComplex.exact_iff_isZero_homology] at hS ⊢
  rw [hP.isZero_iff]
  exact fun i => (hS i).of_iso (S.mapHomologyIso (F i)).symm

Depends on / 依赖: S.mapHomologyIso, ShortComplex, ShortComplex.exact_iff_isZero_homology, exact_iff_isZero_homology, hP.isZero_iff, hS.map, isZero_iff, mapHomologyIso, of_iso
-/
lemma exact_iff [HasZeroObject C] (S : ShortComplex C) :
    S.Exact ↔ forall (i : I), (S.map (F i)).Exact := by
  refine ⟨fun hS i => hS.map _, fun hS => ?_⟩
  simp only [ShortComplex.exact_iff_isZero_homology] at hS ⊢
  rw [hP.isZero_iff]
  exact fun i => (hS i).of_iso (S.mapHomologyIso (F i)).symm

/--
lemma `exactAt_iff` / 引理 `exactAt_iff`

English:
lemma exactAt_iff
  statement: [HasZeroObject C] {α : Type*} {c : ComplexShape α}
  proof: hP.exact_iff _

中文:
引理 exactAt_iff
  结论: [HasZeroObject C] {α : 类型} {c : ComplexShape α}
  证明: hP.exact_iff _

Depends on / 依赖: exact_iff, hP.exact_iff
-/
lemma exactAt_iff [HasZeroObject C] {α : Type*} {c : ComplexShape α}
    (K : HomologicalComplex C c) (a : α) :
    K.ExactAt a ↔ forall (i : I), (((F i).mapHomologicalComplex c).obj K).ExactAt a :=
  hP.exact_iff _

end

section

variable [Abelian C] [forall i, Abelian (D i)] [CategoryWithHomology C]
  [forall i, PreservesFiniteLimits (F i)] [forall i, PreservesFiniteColimits (F i)]

/--
lemma `shortExact_iff` / 引理 `shortExact_iff`

English:
lemma shortExact_iff
  given: (S : ShortComplex C)
  proof: by
  refine ⟨fun hS i => ?_, fun hS => ?_⟩
  · have := hS.mono_f
    have := hS.epi_g
    exact hS.map (F i)
  · have : Mono S.f := by
      rw [hP.jointlyReflectMonomorphisms.mono_iff]
      exact fun i => (hS i).mono_f
    have : Epi S.g := by
      rw [hP.jointlyReflectEpimorphisms.epi_iff]
     

中文:
引理 shortExact_iff
  条件: (S : ShortComplex C)
  证明: by
  refine ⟨fun hS i => ?_, fun hS => ?_⟩
  · have := hS.mono_f
    have := hS.epi_g
    exact hS.map (F i)
  · have : Mono S.f := by
      rw [hP.jointlyReflectMonomorphisms.mono_iff]
      exact fun i => (hS i).mono_f
    have : Epi S.g := by
      rw [hP.jointlyReflectEpimorphisms.epi_iff]
     

Depends on / 依赖: epi_g, epi_iff, exact_iff, hP.exact_iff, hP.jointlyReflectEpimorphisms.epi_iff, hP.jointlyReflectMonomorphisms.mono_iff, hS.epi_g, hS.map, hS.mono_f, jointlyReflectEpimorphisms, jointlyReflectMonomorphisms, mono_f, mono_iff
-/
lemma shortExact_iff (S : ShortComplex C) :
    S.ShortExact ↔ forall (i : I), (S.map (F i)).ShortExact := by
  refine ⟨fun hS i => ?_, fun hS => ?_⟩
  · have := hS.mono_f
    have := hS.epi_g
    exact hS.map (F i)
  · have : Mono S.f := by
      rw [hP.jointlyReflectMonomorphisms.mono_iff]
      exact fun i => (hS i).mono_f
    have : Epi S.g := by
      rw [hP.jointlyReflectEpimorphisms.epi_iff]
      exact fun i => (hS i).epi_g
    exact { exact := (hP.exact_iff S).2 (fun i => (hS i).exact) }

/--
lemma `shortComplexQuasiIso_iff` / 引理 `shortComplexQuasiIso_iff`

English:
lemma shortComplexQuasiIso_iff
  given: {S₁ S₂ : ShortComplex C} (f : S₁ ⟶ S₂)
  proof: by
  refine ⟨fun hf i => inferInstance, fun hf => ?_⟩
  simp only [ShortComplex.quasiIso_iff] at hf ⊢
  rw [hP.isIso_iff]
  exact fun i => ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
    (((Functor.mapArrowFunctor _ _).mapIso (ShortComplex.homologyFunctorIso (F i))).app
      (Arrow.mk f))).

中文:
引理 shortComplexQuasiIso_iff
  条件: {S₁ S₂ : ShortComplex C} (f : S₁ ⟶ S₂)
  证明: by
  refine ⟨fun hf i => inferInstance, fun hf => ?_⟩
  simp only [ShortComplex.quasiIso_iff] at hf ⊢
  rw [hP.isIso_iff]
  exact fun i => ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
    (((Functor.mapArrowFunctor _ _).mapIso (ShortComplex.homologyFunctorIso (F i))).app
      (Arrow.mk f))).

Depends on / 依赖: Arrow.mk, Functor, Functor.mapArrowFunctor, MorphismProperty, MorphismProperty.isomorphisms, ShortComplex, ShortComplex.homologyFunctorIso, ShortComplex.quasiIso_iff, arrow_mk_iso_iff, hP.isIso_iff, homologyFunctorIso, isIso_iff, isomorphisms, mapArrowFunctor, mapIso, quasiIso_iff
-/
lemma shortComplexQuasiIso_iff {S₁ S₂ : ShortComplex C} (f : S₁ ⟶ S₂) :
    ShortComplex.QuasiIso f ↔
      forall (i : I), ShortComplex.QuasiIso ((F i).mapShortComplex.map f) := by
  refine ⟨fun hf i => inferInstance, fun hf => ?_⟩
  simp only [ShortComplex.quasiIso_iff] at hf ⊢
  rw [hP.isIso_iff]
  exact fun i => ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
    (((Functor.mapArrowFunctor _ _).mapIso (ShortComplex.homologyFunctorIso (F i))).app
      (Arrow.mk f))).1 (hf i)

section

variable {α : Type*} {c : ComplexShape α} {K L : HomologicalComplex C c}

/--
lemma `quasiIsoAt_iff` / 引理 `quasiIsoAt_iff`

English:
lemma quasiIsoAt_iff
  given: (f : K ⟶ L) (a : α)
  proof: by
  simpa only [quasiIsoAt_iff' _ _ _ _ rfl rfl] using!
    hP.shortComplexQuasiIso_iff _

中文:
引理 quasiIsoAt_iff
  条件: (f : K ⟶ L) (a : α)
  证明: by
  simpa only [quasiIsoAt_iff' _ _ _ _ rfl rfl] using!
    hP.shortComplexQuasiIso_iff _

Depends on / 依赖: hP.shortComplexQuasiIso_iff, quasiIsoAt_iff, shortComplexQuasiIso_iff
-/
lemma quasiIsoAt_iff (f : K ⟶ L) (a : α) :
    QuasiIsoAt f a ↔ forall (i : I), QuasiIsoAt (((F i).mapHomologicalComplex c).map f) a := by
  simpa only [quasiIsoAt_iff' _ _ _ _ rfl rfl] using!
    hP.shortComplexQuasiIso_iff _

/--
lemma `quasiIso_iff` / 引理 `quasiIso_iff`

English:
lemma quasiIso_iff
  given: (f : K ⟶ L)
  proof: by
  simp only [_root_.quasiIso_iff, hP.quasiIsoAt_iff]
  tauto

中文:
引理 quasiIso_iff
  条件: (f : K ⟶ L)
  证明: by
  simp only [_root_.quasiIso_iff, hP.quasiIsoAt_iff]
  tauto

Depends on / 依赖: _root_, _root_.quasiIso_iff, hP.quasiIsoAt_iff, quasiIsoAt_iff, quasiIso_iff
-/
lemma quasiIso_iff (f : K ⟶ L) :
    QuasiIso f ↔ forall (i : I), QuasiIso (((F i).mapHomologicalComplex c).map f) := by
  simp only [_root_.quasiIso_iff, hP.quasiIsoAt_iff]
  tauto

end

end

end JointlyReflectIsomorphisms

end CategoryTheory
