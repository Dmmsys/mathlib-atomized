/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Images
public import Mathlib.CategoryTheory.MorphismProperty.Concrete
public import Mathlib.CategoryTheory.Types.Basic

/-!
# Epi and mono in concrete categories

In this file, we relate epimorphisms and monomorphisms in a concrete category `C`
to surjective and injective morphisms, and we show that if `C` has
strong epi mono factorizations and is such that `forget C` preserves
both epi and mono, then any morphism in `C` can be factored in a
functorial manner as a composition of a surjective morphism followed
by an injective morphism.

-/

@[expose] public section

universe w v v' u u'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {FC : C -> C -> Type*} {CC : C -> Type w}
variable [forall X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{w} C FC]

open Limits MorphismProperty

namespace ConcreteCategory

section

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [(forget
  signature: C).PreservesMonomorphisms] {X Y : C} (f : X ⟶ Y) [Mono f] :
  body: Functor.map_mono (forget C) f

中文:
实例 [(forget
  签名: C).PreservesMonomorphisms] {X Y : C} (f : X ⟶ Y) [Mono f] :
  定义体: Functor.map_mono (forget C) f

Depends on / 依赖: Functor, Functor.map_mono, forget, map_mono
-/
instance [(forget C).PreservesMonomorphisms] {X Y : C} (f : X ⟶ Y) [Mono f] :
    Mono (↾f) := Functor.map_mono (forget C) f

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [(forget
  signature: C).PreservesEpimorphisms] {X Y : C} (f : X ⟶ Y) [Epi f] :
  body: Functor.map_epi (forget C) f

中文:
实例 [(forget
  签名: C).PreservesEpimorphisms] {X Y : C} (f : X ⟶ Y) [Epi f] :
  定义体: Functor.map_epi (forget C) f

Depends on / 依赖: Functor, Functor.map_epi, forget, map_epi
-/
instance [(forget C).PreservesEpimorphisms] {X Y : C} (f : X ⟶ Y) [Epi f] :
    Epi (↾f) := Functor.map_epi (forget C) f

/--
theorem `mono_of_injective` / 定理 `mono_of_injective`

English:
theorem mono_of_injective
  given: {X Y : C} (f : X ⟶ Y) (i : Function.Injective f)
  proof: (forget C).mono_of_mono_map ((mono_iff_injective ((forget C).map f)).2 i)

中文:
定理 mono_of_injective
  条件: {X Y : C} (f : X ⟶ Y) (i : Function.Injective f)
  证明: (forget C).mono_of_mono_map ((mono_iff_injective ((forget C).map f)).2 i)

Depends on / 依赖: forget, mono_iff_injective, mono_of_mono_map
-/
theorem mono_of_injective {X Y : C} (f : X ⟶ Y) (i : Function.Injective f) :
    Mono f :=
  (forget C).mono_of_mono_map ((mono_iff_injective ((forget C).map f)).2 i)

/--
Instance `forget₂_preservesMonomorphisms` / 实例 `forget₂_preservesMonomorphisms`

English:
instance forget₂_preservesMonomorphisms
  signature: (C : Type u) (D : Type u')
  body: have : (forget₂ C D ⋙ forget D).PreservesMonomorphisms := by
    simp only [HasForget₂.forget_comp]
    infer_instance
  Functor.preservesMonomorphisms_of_preserves_of_reflects _ (forget D)

中文:
实例 forget₂_preservesMonomorphisms
  签名: (C : 类型u) (D : 类型u')
  定义体: have : (forget₂ C D ⋙ forget D).PreservesMonomorphisms := by
    simp only [HasForget₂.forget_comp]
    infer_instance
  Functor.preservesMonomorphisms_of_preserves_of_reflects _ (forget D)

Depends on / 依赖: Functor, Functor.preservesMonomorphisms_of_preserves_of_reflects, PreservesMonomorphisms, ReflectsColimitsOfSize, forget, forget_comp, infer_instance, preservesMonomorphisms_of_preserves_of_reflects
-/
instance forget₂_preservesMonomorphisms (C : Type u) (D : Type u')
    [Category.{v} C] [Category.{v'} D]
    {FC : C -> C -> Type*} {CC : C -> Type w}
    [forall X Y, FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory C FC]
    {FD : D -> D -> Type*} {CD : D -> Type w}
    [forall X Y, FunLike (FD X Y) (CD X) (CD Y)]
    [ConcreteCategory D FD]
    [HasForget₂ C D] [(forget C).PreservesMonomorphisms] :
    (forget₂ C D).PreservesMonomorphisms :=
  have : (forget₂ C D ⋙ forget D).PreservesMonomorphisms := by
    simp only [HasForget₂.forget_comp]
    infer_instance
  Functor.preservesMonomorphisms_of_preserves_of_reflects _ (forget D)

/--
Instance `forget₂_preservesEpimorphisms` / 实例 `forget₂_preservesEpimorphisms`

English:
instance forget₂_preservesEpimorphisms
  signature: (C : Type u) (D : Type u')
  body: have : (forget₂ C D ⋙ forget D).PreservesEpimorphisms := by
    simp only [HasForget₂.forget_comp]
    infer_instance
  Functor.preservesEpimorphisms_of_preserves_of_reflects _ (forget D)

中文:
实例 forget₂_preservesEpimorphisms
  签名: (C : 类型u) (D : 类型u')
  定义体: have : (forget₂ C D ⋙ forget D).PreservesEpimorphisms := by
    simp only [HasForget₂.forget_comp]
    infer_instance
  Functor.preservesEpimorphisms_of_preserves_of_reflects _ (forget D)

Depends on / 依赖: Functor, Functor.preservesEpimorphisms_of_preserves_of_reflects, PreservesEpimorphisms, forget, forget_comp, infer_instance, preservesEpimorphisms_of_preserves_of_reflects
-/
instance forget₂_preservesEpimorphisms (C : Type u) (D : Type u')
    [Category.{v} C] [Category.{v'} D]
    {FC : C -> C -> Type*} {CC : C -> Type w}
    [forall X Y, FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory C FC]
    {FD : D -> D -> Type*} {CD : D -> Type w}
    [forall X Y, FunLike (FD X Y) (CD X) (CD Y)]
    [ConcreteCategory D FD]
    [HasForget₂ C D] [(forget C).PreservesEpimorphisms] :
    (forget₂ C D).PreservesEpimorphisms :=
  have : (forget₂ C D ⋙ forget D).PreservesEpimorphisms := by
    simp only [HasForget₂.forget_comp]
    infer_instance
  Functor.preservesEpimorphisms_of_preserves_of_reflects _ (forget D)

variable (C)

/--
lemma `surjective_le_epimorphisms` / 引理 `surjective_le_epimorphisms`

English:
lemma surjective_le_epimorphisms
  proof: fun _ _ _ hf => (forget C).epi_of_epi_map ((epi_iff_surjective _).2 hf)

中文:
引理 surjective_le_epimorphisms
  证明: fun _ _ _ hf => (forget C).epi_of_epi_map ((epi_iff_surjective _).2 hf)

Depends on / 依赖: Finite, ReflectsFiniteCoproducts, epi_iff_surjective, epi_of_epi_map, forget
-/
lemma surjective_le_epimorphisms :
    MorphismProperty.surjective C <= epimorphisms C :=
  fun _ _ _ hf => (forget C).epi_of_epi_map ((epi_iff_surjective _).2 hf)

/--
lemma `injective_le_monomorphisms` / 引理 `injective_le_monomorphisms`

English:
lemma injective_le_monomorphisms
  proof: fun _ _ _ hf => (forget C).mono_of_mono_map ((mono_iff_injective _).2 hf)

中文:
引理 injective_le_monomorphisms
  证明: fun _ _ _ hf => (forget C).mono_of_mono_map ((mono_iff_injective _).2 hf)

Depends on / 依赖: forget, mono_iff_injective, mono_of_mono_map
-/
lemma injective_le_monomorphisms :
    MorphismProperty.injective C <= monomorphisms C :=
  fun _ _ _ hf => (forget C).mono_of_mono_map ((mono_iff_injective _).2 hf)

/--
lemma `surjective_eq_epimorphisms_iff` / 引理 `surjective_eq_epimorphisms_iff`

English:
lemma surjective_eq_epimorphisms_iff
  proof: by
  constructor
  · intro h
    constructor
    rintro _ _ f (hf : epimorphisms C f)
    rw [epi_iff_surjective]
    rw [← h] at hf
    exact hf
  · intro
    apply le_antisymm (surjective_le_epimorphisms C)
    intro _ _ f hf
    have : Epi f := hf
    change Function.Surjective ((forget C).map f)

中文:
引理 surjective_eq_epimorphisms_iff
  证明: by
  constructor
  · intro h
    constructor
    rintro _ _ f (hf : epimorphisms C f)
    rw [epi_iff_surjective]
    rw [← h] at hf
    exact hf
  · intro
    apply le_antisymm (surjective_le_epimorphisms C)
    intro _ _ f hf
    have : Epi f := hf
    change Function.Surjective ((forget C).map f)

Depends on / 依赖: Function, Function.Surjective, Surjective, epi_iff_surjective, epimorphisms, forget, infer_instance, le_antisymm, surjective_le_epimorphisms
-/
lemma surjective_eq_epimorphisms_iff :
    MorphismProperty.surjective C = epimorphisms C ↔ (forget C).PreservesEpimorphisms := by
  constructor
  · intro h
    constructor
    rintro _ _ f (hf : epimorphisms C f)
    rw [epi_iff_surjective]
    rw [← h] at hf
    exact hf
  · intro
    apply le_antisymm (surjective_le_epimorphisms C)
    intro _ _ f hf
    have : Epi f := hf
    change Function.Surjective ((forget C).map f)
    rw [← epi_iff_surjective]
    infer_instance

/--
lemma `injective_eq_monomorphisms_iff` / 引理 `injective_eq_monomorphisms_iff`

English:
lemma injective_eq_monomorphisms_iff
  proof: by
  constructor
  · intro h
    constructor
    rintro _ _ f (hf : monomorphisms C f)
    rw [mono_iff_injective]
    rw [← h] at hf
    exact hf
  · intro
    apply le_antisymm (injective_le_monomorphisms C)
    intro _ _ f hf
    have : Mono f := hf
    change Function.Injective ((forget C).map f

中文:
引理 injective_eq_monomorphisms_iff
  证明: by
  constructor
  · intro h
    constructor
    rintro _ _ f (hf : monomorphisms C f)
    rw [mono_iff_injective]
    rw [← h] at hf
    exact hf
  · intro
    apply le_antisymm (injective_le_monomorphisms C)
    intro _ _ f hf
    have : Mono f := hf
    change Function.Injective ((forget C).map f

Depends on / 依赖: Function, Function.Injective, Injective, forget, infer_instance, injective_le_monomorphisms, le_antisymm, mono_iff_injective, monomorphisms
-/
lemma injective_eq_monomorphisms_iff :
    MorphismProperty.injective C = monomorphisms C ↔ (forget C).PreservesMonomorphisms := by
  constructor
  · intro h
    constructor
    rintro _ _ f (hf : monomorphisms C f)
    rw [mono_iff_injective]
    rw [← h] at hf
    exact hf
  · intro
    apply le_antisymm (injective_le_monomorphisms C)
    intro _ _ f hf
    have : Mono f := hf
    change Function.Injective ((forget C).map f)
    rw [← mono_iff_injective]
    infer_instance

/--
lemma `injective_eq_monomorphisms` / 引理 `injective_eq_monomorphisms`

English:
lemma injective_eq_monomorphisms
  given: [(forget C).PreservesMonomorphisms]
  proof: by
  rw [injective_eq_monomorphisms_iff]
  infer_instance

中文:
引理 injective_eq_monomorphisms
  条件: [(forget C).PreservesMonomorphisms]
  证明: by
  rw [injective_eq_monomorphisms_iff]
  infer_instance

Depends on / 依赖: infer_instance, injective_eq_monomorphisms_iff
-/
lemma injective_eq_monomorphisms [(forget C).PreservesMonomorphisms] :
    MorphismProperty.injective C = monomorphisms C := by
  rw [injective_eq_monomorphisms_iff]
  infer_instance

/--
lemma `surjective_eq_epimorphisms` / 引理 `surjective_eq_epimorphisms`

English:
lemma surjective_eq_epimorphisms
  given: [(forget C).PreservesEpimorphisms]
  proof: by
  rw [surjective_eq_epimorphisms_iff]
  infer_instance

中文:
引理 surjective_eq_epimorphisms
  条件: [(forget C).PreservesEpimorphisms]
  证明: by
  rw [surjective_eq_epimorphisms_iff]
  infer_instance

Depends on / 依赖: infer_instance, surjective_eq_epimorphisms_iff
-/
lemma surjective_eq_epimorphisms [(forget C).PreservesEpimorphisms] :
    MorphismProperty.surjective C = epimorphisms C := by
  rw [surjective_eq_epimorphisms_iff]
  infer_instance

variable [HasStrongEpiMonoFactorisations C] [(forget C).PreservesMonomorphisms]
  [(forget C).PreservesEpimorphisms]

/--
Definition of `functorialSurjectiveInjectiveFactorizationData` / `functorialSurjectiveInjectiveFactorizationData` 的定义

English:
definition functorialSurjectiveInjectiveFactorizationData
  signature: :
  body: (functorialEpiMonoFactorizationData C).ofLE
    (by rw [surjective_eq_epimorphisms])
    (by rw [injective_eq_monomorphisms])

中文:
定义 functorialSurjectiveInjectiveFactorizationData
  签名: :
  定义体: (functorialEpiMonoFactorizationData C).ofLE
    (by rw [surjective_eq_epimorphisms])
    (by rw [injective_eq_monomorphisms])

Depends on / 依赖: functorialEpiMonoFactorizationData, injective_eq_monomorphisms, surjective_eq_epimorphisms
-/
noncomputable def functorialSurjectiveInjectiveFactorizationData :
    FunctorialSurjectiveInjectiveFactorizationData C :=
  (functorialEpiMonoFactorizationData C).ofLE
    (by rw [surjective_eq_epimorphisms])
    (by rw [injective_eq_monomorphisms])

instance (priority := 100) : HasFunctorialSurjectiveInjectiveFactorization C where
  nonempty_functorialFactorizationData :=
    ⟨functorialSurjectiveInjectiveFactorizationData C⟩

end

section

open CategoryTheory.Limits

/--
theorem `injective_of_mono_of_preservesPullback` / 定理 `injective_of_mono_of_preservesPullback`

English:
theorem injective_of_mono_of_preservesPullback
  statement: {X Y : C} (f : X ⟶ Y) [Mono f]
  proof: (mono_iff_injective ((forget C).map f)).mp inferInstance

中文:
定理 injective_of_mono_of_preservesPullback
  结论: {X Y : C} (f : X ⟶ Y) [Mono f]
  证明: (mono_iff_injective ((forget C).map f)).mp inferInstance

Depends on / 依赖: forget, mono_iff_injective
-/
theorem injective_of_mono_of_preservesPullback {X Y : C} (f : X ⟶ Y) [Mono f]
    [PreservesLimitsOfShape WalkingCospan (forget C)] : Function.Injective f :=
  (mono_iff_injective ((forget C).map f)).mp inferInstance

/--
theorem `mono_iff_injective_of_preservesPullback` / 定理 `mono_iff_injective_of_preservesPullback`

English:
theorem mono_iff_injective_of_preservesPullback
  statement: {X Y : C} (f : X ⟶ Y)
  proof: ((forget C).mono_map_iff_mono _).symm.trans (mono_iff_injective _)

中文:
定理 mono_iff_injective_of_preservesPullback
  结论: {X Y : C} (f : X ⟶ Y)
  证明: ((forget C).mono_map_iff_mono _).symm.trans (mono_iff_injective _)

Depends on / 依赖: forget, mono_iff_injective, mono_map_iff_mono, symm.trans
-/
theorem mono_iff_injective_of_preservesPullback {X Y : C} (f : X ⟶ Y)
    [PreservesLimitsOfShape WalkingCospan (forget C)] : Mono f ↔ Function.Injective f :=
  ((forget C).mono_map_iff_mono _).symm.trans (mono_iff_injective _)

/--
theorem `epi_of_surjective` / 定理 `epi_of_surjective`

English:
theorem epi_of_surjective
  given: {X Y : C} (f : X ⟶ Y) (s : Function.Surjective f)
  proof: (forget C).epi_of_epi_map ((epi_iff_surjective ((forget C).map f)).2 s)

中文:
定理 epi_of_surjective
  条件: {X Y : C} (f : X ⟶ Y) (s : Function.Surjective f)
  证明: (forget C).epi_of_epi_map ((epi_iff_surjective ((forget C).map f)).2 s)

Depends on / 依赖: epi_iff_surjective, epi_of_epi_map, forget
-/
theorem epi_of_surjective {X Y : C} (f : X ⟶ Y) (s : Function.Surjective f) :
    Epi f :=
  (forget C).epi_of_epi_map ((epi_iff_surjective ((forget C).map f)).2 s)

/--
theorem `surjective_of_epi_of_preservesPushout` / 定理 `surjective_of_epi_of_preservesPushout`

English:
theorem surjective_of_epi_of_preservesPushout
  statement: {X Y : C} (f : X ⟶ Y) [Epi f]
  proof: (epi_iff_surjective ((forget C).map f)).mp inferInstance

中文:
定理 surjective_of_epi_of_preservesPushout
  结论: {X Y : C} (f : X ⟶ Y) [Epi f]
  证明: (epi_iff_surjective ((forget C).map f)).mp inferInstance

Depends on / 依赖: epi_iff_surjective, forget
-/
theorem surjective_of_epi_of_preservesPushout {X Y : C} (f : X ⟶ Y) [Epi f]
    [PreservesColimitsOfShape WalkingSpan (forget C)] : Function.Surjective f :=
  (epi_iff_surjective ((forget C).map f)).mp inferInstance

/--
theorem `epi_iff_surjective_of_preservesPushout` / 定理 `epi_iff_surjective_of_preservesPushout`

English:
theorem epi_iff_surjective_of_preservesPushout
  statement: {X Y : C} (f : X ⟶ Y)
  proof: ((forget C).epi_map_iff_epi _).symm.trans (epi_iff_surjective _)

中文:
定理 epi_iff_surjective_of_preservesPushout
  结论: {X Y : C} (f : X ⟶ Y)
  证明: ((forget C).epi_map_iff_epi _).symm.trans (epi_iff_surjective _)

Depends on / 依赖: epi_iff_surjective, epi_map_iff_epi, forget, symm.trans
-/
theorem epi_iff_surjective_of_preservesPushout {X Y : C} (f : X ⟶ Y)
    [PreservesColimitsOfShape WalkingSpan (forget C)] : Epi f ↔ Function.Surjective f :=
  ((forget C).epi_map_iff_epi _).symm.trans (epi_iff_surjective _)

/--
theorem `bijective_of_isIso` / 定理 `bijective_of_isIso`

English:
theorem bijective_of_isIso
  given: {X Y : C} (f : X ⟶ Y) [IsIso f]
  proof: by
  rw [bijective_iff_isIso_ofHom]
  infer_instance

中文:
定理 bijective_of_isIso
  条件: {X Y : C} (f : X ⟶ Y) [IsIso f]
  证明: by
  rw [bijective_iff_isIso_ofHom]
  infer_instance

Depends on / 依赖: bijective_iff_isIso_ofHom, infer_instance
-/
theorem bijective_of_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] :
    Function.Bijective f := by
  rw [bijective_iff_isIso_ofHom]
  infer_instance

/--
theorem `isIso_iff_bijective` / 定理 `isIso_iff_bijective`

English:
theorem isIso_iff_bijective
  statement: [(forget C).ReflectsIsomorphisms]
  proof: by
  rw [bijective_iff_isIso_ofHom]
  refine ⟨fun _ => inferInstance, fun h => ?_⟩
  have : IsIso ((forget C).map f) := h
  exact isIso_of_reflects_iso f (forget C)

中文:
定理 isIso_iff_bijective
  结论: [(forget C).ReflectsIsomorphisms]
  证明: by
  rw [bijective_iff_isIso_ofHom]
  refine ⟨fun _ => inferInstance, fun h => ?_⟩
  have : IsIso ((forget C).map f) := h
  exact isIso_of_reflects_iso f (forget C)

Depends on / 依赖: bijective_iff_isIso_ofHom, forget, isIso_of_reflects_iso
-/
theorem isIso_iff_bijective [(forget C).ReflectsIsomorphisms]
    {X Y : C} (f : X ⟶ Y) : IsIso f ↔ Function.Bijective f := by
  rw [bijective_iff_isIso_ofHom]
  refine ⟨fun _ => inferInstance, fun h => ?_⟩
  have : IsIso ((forget C).map f) := h
  exact isIso_of_reflects_iso f (forget C)

end

end ConcreteCategory

end CategoryTheory
