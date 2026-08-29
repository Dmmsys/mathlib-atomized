/-
Copyright (c) 2026 Ziyan Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ziyan Wei, Anatole Dedecker
-/
module

public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.Homeomorph.Quotient
public import Mathlib.Topology.Constructions
public import Mathlib.Data.Setoid.Basic

/-!
# Bourbaki Strict Maps

This file defines Bourbaki strict maps (`Topology.IsStrictMap`) and proves some of their
basic properties.

A map `f : X → Y` between topological spaces is called *strict* in the sense of Bourbaki
if the natural corestriction to its image (i.e., `Set.rangeFactorization f`) is a quotient map.
Equivalently, these are precisely the maps for which the first isomorphism
theorem yields a homeomorphism: the canonical bijection `X ⧸ ker f ≃ range f`
is a homeomorphism if and only if `f` is strict. This provides a natural
generalization of quotient maps to non-surjective maps.

Many important classes of maps are automatically continuous strict maps, including:
- continuous open maps (`IsOpenMap.isStrictMap`);
- continuous closed maps (`IsClosedMap.isStrictMap`).

## Equivalent characterizations

We provide several equivalent ways to characterize a strict map `f`:
* `Topology.isStrictMap_iff_isHomeomorph_quotientKerEquivRange`: `f` is strict if and only if
  the canonical bijection `Quotient (Setoid.ker f) ≃ Set.range f` is a homeomorphism.
* `Topology.isStrictMap_iff_isEmbedding_kerLift`: `f` is strict if and only if
  the canonical injection `Quotient (Setoid.ker f) → Y` (`Setoid.kerLift f`) is an embedding.
-/

@[expose] public section

open Function Set Topology Setoid

namespace Topology

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {f : X -> Y} {g : Y -> Z}

variable (f) in
/--
Definition of `IsStrictMap` / `IsStrictMap` 的定义

English:
definition IsStrictMap
  signature: : Prop
  body: IsQuotientMap (Set.rangeFactorization f)

中文:
定义 IsStrictMap
  签名: : 命题
  定义体: IsQuotientMap (Set.rangeFactorization f)

Depends on / 依赖: IsQuotientMap, Set.rangeFactorization, rangeFactorization
-/
def IsStrictMap : Prop :=
  IsQuotientMap (Set.rangeFactorization f)

/--
lemma `isStrictMap_iff_isQuotientMap_rangeFactorization` / 引理 `isStrictMap_iff_isQuotientMap_rangeFactorization`

English:
lemma isStrictMap_iff_isQuotientMap_rangeFactorization
  proof: Iff.rfl

中文:
引理 isStrictMap_iff_isQuotientMap_rangeFactorization
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma isStrictMap_iff_isQuotientMap_rangeFactorization :
    IsStrictMap f ↔ IsQuotientMap (Set.rangeFactorization f) :=
  Iff.rfl

/--
theorem `isStrictMap_iff_isHomeomorph_quotientKerEquivRange` / 定理 `isStrictMap_iff_isHomeomorph_quotientKerEquivRange`

English:
theorem isStrictMap_iff_isHomeomorph_quotientKerEquivRange
  proof: by
  simp only [IsStrictMap, isHomeomorph_iff_isQuotientMap_injective, Equiv.injective, and_true]
  exact ⟨fun h => IsQuotientMap.of_comp_isQuotientMap isQuotientMap_quotient_mk' h,
         fun h => h.comp isQuotientMap_quotient_mk'⟩

中文:
定理 isStrictMap_iff_isHomeomorph_quotientKerEquivRange
  证明: by
  simp only [IsStrictMap, isHomeomorph_iff_isQuotientMap_injective, Equiv.injective, and_true]
  exact ⟨fun h => IsQuotientMap.of_comp_isQuotientMap isQuotientMap_quotient_mk' h,
         fun h => h.comp isQuotientMap_quotient_mk'⟩

Depends on / 依赖: Equiv.injective, IsQuotientMap, IsQuotientMap.of_comp_isQuotientMap, IsStrictMap, and_true, h.comp, injective, isHomeomorph_iff_isQuotientMap_injective, isQuotientMap_quotient_mk, of_comp_isQuotientMap
-/
theorem isStrictMap_iff_isHomeomorph_quotientKerEquivRange :
    IsStrictMap f ↔
      IsHomeomorph (Setoid.quotientKerEquivRange f : Quotient (Setoid.ker f) -> Set.range f) := by
  simp only [IsStrictMap, isHomeomorph_iff_isQuotientMap_injective, Equiv.injective, and_true]
  exact ⟨fun h => IsQuotientMap.of_comp_isQuotientMap isQuotientMap_quotient_mk' h,
         fun h => h.comp isQuotientMap_quotient_mk'⟩

/--
Definition of `_root_.Homeomorph.quotientKerEquivRange` / `_root_.Homeomorph.quotientKerEquivRange` 的定义

English:
definition _root_.Homeomorph.quotientKerEquivRange
  signature: (hf : IsStrictMap f)
  body: (isStrictMap_iff_isHomeomorph_quotientKerEquivRange.mp hf).homeomorph

@[deprecated (since := "2026-07-10")] protected alias Homeomorph.quotientKerEquivRange :=
  Homeomorph.quotientKerEquivRange

中文:
定义 _root_.Homeomorph.quotientKerEquivRange
  签名: (hf : IsStrictMap f)
  定义体: (isStrictMap_iff_isHomeomorph_quotientKerEquivRange.mp hf).homeomorph

@[deprecated (since := "2026-07-10")] protected alias Homeomorph.quotientKerEquivRange :=
  Homeomorph.quotientKerEquivRange

Depends on / 依赖: homeomorph, isStrictMap_iff_isHomeomorph_quotientKerEquivRange, isStrictMap_iff_isHomeomorph_quotientKerEquivRange.mp
-/
noncomputable def _root_.Homeomorph.quotientKerEquivRange (hf : IsStrictMap f) :
    Quotient (Setoid.ker f) ≃ₜ Set.range f :=
  (isStrictMap_iff_isHomeomorph_quotientKerEquivRange.mp hf).homeomorph

@[deprecated (since := "2026-07-10")] protected alias Homeomorph.quotientKerEquivRange :=
  Homeomorph.quotientKerEquivRange

/--
theorem `isStrictMap_iff_isEmbedding_kerLift` / 定理 `isStrictMap_iff_isEmbedding_kerLift`

English:
theorem isStrictMap_iff_isEmbedding_kerLift
  proof: by
  simp only [isStrictMap_iff_isHomeomorph_quotientKerEquivRange,
    isHomeomorph_iff_isEmbedding_surjective, Equiv.surjective, and_true]
  exact (IsEmbedding.of_comp_iff .subtypeVal).symm

中文:
定理 isStrictMap_iff_isEmbedding_kerLift
  证明: by
  simp only [isStrictMap_iff_isHomeomorph_quotientKerEquivRange,
    isHomeomorph_iff_isEmbedding_surjective, Equiv.surjective, and_true]
  exact (IsEmbedding.of_comp_iff .subtypeVal).symm

Depends on / 依赖: Equiv.surjective, IsEmbedding, IsEmbedding.of_comp_iff, and_true, isHomeomorph_iff_isEmbedding_surjective, isStrictMap_iff_isHomeomorph_quotientKerEquivRange, of_comp_iff, subtypeVal, surjective
-/
theorem isStrictMap_iff_isEmbedding_kerLift :
    IsStrictMap f ↔ IsEmbedding (Setoid.kerLift f) := by
  simp only [isStrictMap_iff_isHomeomorph_quotientKerEquivRange,
    isHomeomorph_iff_isEmbedding_surjective, Equiv.surjective, and_true]
  exact (IsEmbedding.of_comp_iff .subtypeVal).symm

/--
lemma `IsStrictMap.continuous` / 引理 `IsStrictMap.continuous`

English:
lemma IsStrictMap.continuous
  given: {f : X -> Y} (hf : IsStrictMap f)
  statement: Continuous f
  proof: by
  rw [isStrictMap_iff_isQuotientMap_rangeFactorization] at hf
  exact continuous_rangeFactorization_iff.mp hf.continuous

中文:
引理 IsStrictMap.continuous
  条件: {f : X -> Y} (hf : IsStrictMap f)
  结论: Continuous f
  证明: by
  rw [isStrictMap_iff_isQuotientMap_rangeFactorization] at hf
  exact continuous_rangeFactorization_iff.mp hf.continuous

Depends on / 依赖: continuous, continuous_rangeFactorization_iff, continuous_rangeFactorization_iff.mp, hf.continuous, isStrictMap_iff_isQuotientMap_rangeFactorization
-/
lemma IsStrictMap.continuous {f : X -> Y} (hf : IsStrictMap f) : Continuous f := by
  rw [isStrictMap_iff_isQuotientMap_rangeFactorization] at hf
  exact continuous_rangeFactorization_iff.mp hf.continuous

/--
lemma `_root_.IsOpenMap.isStrictMap` / 引理 `_root_.IsOpenMap.isStrictMap`

English:
lemma _root_.IsOpenMap.isStrictMap
  given: (ho : IsOpenMap f) (h_cont : Continuous f)
  proof: by
  rw [isStrictMap_iff_isQuotientMap_rangeFactorization]
  exact (ho.subtype_mk fun x => ⟨x, rfl⟩).isQuotientMap
    h_cont.rangeFactorization Set.rangeFactorization_surjective

@[deprecated (since := "2026-07-10")] protected alias IsOpenMap.isStrictMap :=
  IsOpenMap.isStrictMap

中文:
引理 _root_.IsOpenMap.isStrictMap
  条件: (ho : IsOpenMap f) (h_cont : Continuous f)
  证明: by
  rw [isStrictMap_iff_isQuotientMap_rangeFactorization]
  exact (ho.subtype_mk fun x => ⟨x, rfl⟩).isQuotientMap
    h_cont.rangeFactorization Set.rangeFactorization_surjective

@[deprecated (since := "2026-07-10")] protected alias IsOpenMap.isStrictMap :=
  IsOpenMap.isStrictMap

Depends on / 依赖: Set.rangeFactorization_surjective, h_cont, h_cont.rangeFactorization, ho.subtype_mk, isQuotientMap, isStrictMap_iff_isQuotientMap_rangeFactorization, rangeFactorization, rangeFactorization_surjective, subtype_mk
-/
lemma _root_.IsOpenMap.isStrictMap (ho : IsOpenMap f) (h_cont : Continuous f) :
    IsStrictMap f := by
  rw [isStrictMap_iff_isQuotientMap_rangeFactorization]
  exact (ho.subtype_mk fun x => ⟨x, rfl⟩).isQuotientMap
    h_cont.rangeFactorization Set.rangeFactorization_surjective

@[deprecated (since := "2026-07-10")] protected alias IsOpenMap.isStrictMap :=
  IsOpenMap.isStrictMap

/--
lemma `_root_.IsClosedMap.isStrictMap` / 引理 `_root_.IsClosedMap.isStrictMap`

English:
lemma _root_.IsClosedMap.isStrictMap
  given: (hc : IsClosedMap f) (h_cont : Continuous f)
  proof: by
  rw [isStrictMap_iff_isQuotientMap_rangeFactorization]
  exact (hc.subtype_mk fun x => ⟨x, rfl⟩).isQuotientMap
    h_cont.rangeFactorization Set.rangeFactorization_surjective

@[deprecated (since := "2026-07-10")] protected alias IsClosedMap.isStrictMap :=
  IsClosedMap.isStrictMap

中文:
引理 _root_.IsClosedMap.isStrictMap
  条件: (hc : IsClosedMap f) (h_cont : Continuous f)
  证明: by
  rw [isStrictMap_iff_isQuotientMap_rangeFactorization]
  exact (hc.subtype_mk fun x => ⟨x, rfl⟩).isQuotientMap
    h_cont.rangeFactorization Set.rangeFactorization_surjective

@[deprecated (since := "2026-07-10")] protected alias IsClosedMap.isStrictMap :=
  IsClosedMap.isStrictMap

Depends on / 依赖: Set.rangeFactorization_surjective, h_cont, h_cont.rangeFactorization, hc.subtype_mk, isQuotientMap, isStrictMap_iff_isQuotientMap_rangeFactorization, rangeFactorization, rangeFactorization_surjective, subtype_mk
-/
lemma _root_.IsClosedMap.isStrictMap (hc : IsClosedMap f) (h_cont : Continuous f) :
    IsStrictMap f := by
  rw [isStrictMap_iff_isQuotientMap_rangeFactorization]
  exact (hc.subtype_mk fun x => ⟨x, rfl⟩).isQuotientMap
    h_cont.rangeFactorization Set.rangeFactorization_surjective

@[deprecated (since := "2026-07-10")] protected alias IsClosedMap.isStrictMap :=
  IsClosedMap.isStrictMap

/--
lemma `_root_.IsHomeomorph.isStrictMap` / 引理 `_root_.IsHomeomorph.isStrictMap`

English:
lemma _root_.IsHomeomorph.isStrictMap
  given: (f_homeo : IsHomeomorph f)
  proof: f_homeo.isOpenMap.isStrictMap f_homeo.continuous

@[deprecated (since := "2026-07-10")] protected alias IsHomeomorph.isStrictMap :=
  IsHomeomorph.isStrictMap

中文:
引理 _root_.IsHomeomorph.isStrictMap
  条件: (f_homeo : IsHomeomorph f)
  证明: f_homeo.isOpenMap.isStrictMap f_homeo.continuous

@[deprecated (since := "2026-07-10")] protected alias IsHomeomorph.isStrictMap :=
  IsHomeomorph.isStrictMap

Depends on / 依赖: continuous, f_homeo, f_homeo.continuous, f_homeo.isOpenMap.isStrictMap, isOpenMap, isStrictMap
-/
lemma _root_.IsHomeomorph.isStrictMap (f_homeo : IsHomeomorph f) :
    IsStrictMap f :=
  f_homeo.isOpenMap.isStrictMap f_homeo.continuous

@[deprecated (since := "2026-07-10")] protected alias IsHomeomorph.isStrictMap :=
  IsHomeomorph.isStrictMap

/--
lemma `IsStrictMap.id` / 引理 `IsStrictMap.id`

English:
lemma IsStrictMap.id
  statement: IsStrictMap (id : X -> X)
  proof: IsHomeomorph.id.isStrictMap

中文:
引理 IsStrictMap.id
  结论: IsStrictMap (id : X -> X)
  证明: IsHomeomorph.id.isStrictMap

Depends on / 依赖: IsHomeomorph, IsHomeomorph.id.isStrictMap, isStrictMap
-/
lemma IsStrictMap.id : IsStrictMap (id : X -> X) := IsHomeomorph.id.isStrictMap

/--
lemma `IsQuotientMap.isStrictMap_iff` / 引理 `IsQuotientMap.isStrictMap_iff`

English:
lemma IsQuotientMap.isStrictMap_iff
  given: (f_quot : IsQuotientMap f)
  proof: by
set Φ : range (g ∘ f) ≃ₜ range g := .setCongr f_quot.surjective.range_comp g
  have key : rangeFactorization g ∘ f = Φ ∘ rangeFactorization (g ∘ f) := rfl
  simp_rw [isStrictMap_iff_isQuotientMap_rangeFactorization, ← f_quot.of_comp_iff, key]
  exact ⟨fun H => by simpa using! Φ.symm.isQuotientMap

中文:
引理 IsQuotientMap.isStrictMap_iff
  条件: (f_quot : IsQuotientMap f)
  证明: by
set Φ : range (g ∘ f) ≃ₜ range g := .setCongr f_quot.surjective.range_comp g
  have key : rangeFactorization g ∘ f = Φ ∘ rangeFactorization (g ∘ f) := rfl
  simp_rw [isStrictMap_iff_isQuotientMap_rangeFactorization, ← f_quot.of_comp_iff, key]
  exact ⟨fun H => by simpa using! Φ.symm.isQuotientMap

Depends on / 依赖: f_quot, f_quot.of_comp_iff, f_quot.surjective.range_comp, isQuotientMap, isQuotientMap.comp, isStrictMap_iff_isQuotientMap_rangeFactorization, of_comp_iff, rangeFactorization, range_comp, setCongr, simp_rw, surjective, symm.isQuotientMap.comp
-/
lemma IsQuotientMap.isStrictMap_iff (f_quot : IsQuotientMap f) :
    IsStrictMap g ↔ IsStrictMap (g ∘ f) := by
set Φ : range (g ∘ f) ≃ₜ range g := .setCongr f_quot.surjective.range_comp g
  have key : rangeFactorization g ∘ f = Φ ∘ rangeFactorization (g ∘ f) := rfl
  simp_rw [isStrictMap_iff_isQuotientMap_rangeFactorization, ← f_quot.of_comp_iff, key]
  exact ⟨fun H => by simpa using! Φ.symm.isQuotientMap.comp H, fun H => Φ.isQuotientMap.comp H⟩

/--
lemma `IsQuotientMap.isStrictMap` / 引理 `IsQuotientMap.isStrictMap`

English:
lemma IsQuotientMap.isStrictMap
  given: (f_quot : IsQuotientMap f)
  proof: f_quot.isStrictMap_iff.mp .id

中文:
引理 IsQuotientMap.isStrictMap
  条件: (f_quot : IsQuotientMap f)
  证明: f_quot.isStrictMap_iff.mp .id

Depends on / 依赖: f_quot, f_quot.isStrictMap_iff.mp, isStrictMap_iff
-/
lemma IsQuotientMap.isStrictMap (f_quot : IsQuotientMap f) :
    IsStrictMap f :=
  f_quot.isStrictMap_iff.mp .id

/--
lemma `IsEmbedding.isStrictMap_iff` / 引理 `IsEmbedding.isStrictMap_iff`

English:
lemma IsEmbedding.isStrictMap_iff
  given: (g_emb : IsEmbedding g)
  proof: by
  set Φ : Quotient (Setoid.ker (g ∘ f)) ≃ₜ Quotient (Setoid.ker (f)) :=
    Homeomorph.Quotient.congrRight (fun _ _ => by simp [g_emb.injective.eq_iff])
  have key : g ∘ kerLift f ∘ Φ = kerLift (g ∘ f) :=
funext Quotient.ind fun _ => rfl
  simp_rw [isStrictMap_iff_isEmbedding_kerLift, ← g_emb.of_

中文:
引理 IsEmbedding.isStrictMap_iff
  条件: (g_emb : IsEmbedding g)
  证明: by
  set Φ : Quotient (Setoid.ker (g ∘ f)) ≃ₜ Quotient (Setoid.ker (f)) :=
    Homeomorph.Quotient.congrRight (fun _ _ => by simp [g_emb.injective.eq_iff])
  have key : g ∘ kerLift f ∘ Φ = kerLift (g ∘ f) :=
funext Quotient.ind fun _ => rfl
  simp_rw [isStrictMap_iff_isEmbedding_kerLift, ← g_emb.of_

Depends on / 依赖: H.comp, Homeomorph, Homeomorph.Quotient.congrRight, Quotient, Quotient.ind, Setoid, Setoid.ker, comp_assoc, congrRight, eq_iff, g_emb, g_emb.injective.eq_iff, g_emb.of_comp_iff, injective, isEmbedding, isStrictMap_iff_isEmbedding_kerLift, kerLift, of_comp_iff, simp_rw, symm.isEmbedding
-/
lemma IsEmbedding.isStrictMap_iff (g_emb : IsEmbedding g) :
    IsStrictMap f ↔ IsStrictMap (g ∘ f) := by
  set Φ : Quotient (Setoid.ker (g ∘ f)) ≃ₜ Quotient (Setoid.ker (f)) :=
    Homeomorph.Quotient.congrRight (fun _ _ => by simp [g_emb.injective.eq_iff])
  have key : g ∘ kerLift f ∘ Φ = kerLift (g ∘ f) :=
funext Quotient.ind fun _ => rfl
  simp_rw [isStrictMap_iff_isEmbedding_kerLift, ← g_emb.of_comp_iff, ← key]
  exact ⟨fun H => H.comp Φ.isEmbedding,
    fun H => by simpa [comp_assoc] using H.comp Φ.symm.isEmbedding⟩

/--
lemma `IsEmbedding.isStrictMap` / 引理 `IsEmbedding.isStrictMap`

English:
lemma IsEmbedding.isStrictMap
  given: (f_emb : IsEmbedding f)
  proof: f_emb.isStrictMap_iff.mp .id

中文:
引理 IsEmbedding.isStrictMap
  条件: (f_emb : IsEmbedding f)
  证明: f_emb.isStrictMap_iff.mp .id

Depends on / 依赖: f_emb, f_emb.isStrictMap_iff.mp, isStrictMap_iff
-/
lemma IsEmbedding.isStrictMap (f_emb : IsEmbedding f) :
    IsStrictMap f :=
  f_emb.isStrictMap_iff.mp .id

/--
lemma `isQuotientMap_iff_isStrictMap_surjective` / 引理 `isQuotientMap_iff_isStrictMap_surjective`

English:
lemma isQuotientMap_iff_isStrictMap_surjective
  proof: by
  refine ⟨fun H => ⟨H.isStrictMap, H.surjective⟩, fun ⟨f_strict, f_surj⟩ => ?_⟩
  rw [isStrictMap_iff_isQuotientMap_rangeFactorization] at f_strict
  set Φ : range f ≃ₜ Y := .trans (.setCongr f_surj.range_eq) (Homeomorph.Set.univ Y)
  exact Φ.isQuotientMap.comp f_strict

中文:
引理 isQuotientMap_iff_isStrictMap_surjective
  证明: by
  refine ⟨fun H => ⟨H.isStrictMap, H.surjective⟩, fun ⟨f_strict, f_surj⟩ => ?_⟩
  rw [isStrictMap_iff_isQuotientMap_rangeFactorization] at f_strict
  set Φ : range f ≃ₜ Y := .trans (.setCongr f_surj.range_eq) (Homeomorph.Set.univ Y)
  exact Φ.isQuotientMap.comp f_strict

Depends on / 依赖: H.isStrictMap, H.surjective, Homeomorph, Homeomorph.Set.univ, f_strict, f_surj, f_surj.range_eq, isQuotientMap, isQuotientMap.comp, isStrictMap, isStrictMap_iff_isQuotientMap_rangeFactorization, range_eq, setCongr, surjective
-/
lemma isQuotientMap_iff_isStrictMap_surjective :
    IsQuotientMap f ↔ IsStrictMap f ∧ Surjective f := by
  refine ⟨fun H => ⟨H.isStrictMap, H.surjective⟩, fun ⟨f_strict, f_surj⟩ => ?_⟩
  rw [isStrictMap_iff_isQuotientMap_rangeFactorization] at f_strict
  set Φ : range f ≃ₜ Y := .trans (.setCongr f_surj.range_eq) (Homeomorph.Set.univ Y)
  exact Φ.isQuotientMap.comp f_strict

/--
lemma `isEmbedding_iff_isStrictMap_injective` / 引理 `isEmbedding_iff_isStrictMap_injective`

English:
lemma isEmbedding_iff_isStrictMap_injective
  proof: by
  refine ⟨fun H => ⟨H.isStrictMap, H.injective⟩, fun ⟨f_strict, f_inj⟩ => ?_⟩
  rw [isStrictMap_iff_isEmbedding_kerLift] at f_strict
  set Φ : Quotient (ker f) ≃ₜ X :=
    (Homeomorph.Quotient.congrRight <| by simp [f_inj.eq_iff]).trans Homeomorph.quotientBot
  exact f_strict.comp Φ.symm.isEmbedd

中文:
引理 isEmbedding_iff_isStrictMap_injective
  证明: by
  refine ⟨fun H => ⟨H.isStrictMap, H.injective⟩, fun ⟨f_strict, f_inj⟩ => ?_⟩
  rw [isStrictMap_iff_isEmbedding_kerLift] at f_strict
  set Φ : Quotient (ker f) ≃ₜ X :=
    (Homeomorph.Quotient.congrRight <| by simp [f_inj.eq_iff]).trans Homeomorph.quotientBot
  exact f_strict.comp Φ.symm.isEmbedd

Depends on / 依赖: H.injective, H.isStrictMap, Homeomorph, Homeomorph.Quotient.congrRight, Homeomorph.quotientBot, Quotient, congrRight, eq_iff, f_inj, f_inj.eq_iff, f_strict, f_strict.comp, injective, isEmbedding, isStrictMap, isStrictMap_iff_isEmbedding_kerLift, quotientBot, symm.isEmbedding
-/
lemma isEmbedding_iff_isStrictMap_injective :
    IsEmbedding f ↔ IsStrictMap f ∧ Injective f := by
  refine ⟨fun H => ⟨H.isStrictMap, H.injective⟩, fun ⟨f_strict, f_inj⟩ => ?_⟩
  rw [isStrictMap_iff_isEmbedding_kerLift] at f_strict
  set Φ : Quotient (ker f) ≃ₜ X :=
    (Homeomorph.Quotient.congrRight <| by simp [f_inj.eq_iff]).trans Homeomorph.quotientBot
  exact f_strict.comp Φ.symm.isEmbedding

/--
lemma `isHomeomorph_iff_isStrictMap_bijective` / 引理 `isHomeomorph_iff_isStrictMap_bijective`

English:
lemma isHomeomorph_iff_isStrictMap_bijective
  proof: by
  simp [isHomeomorph_iff_isEmbedding_surjective, isEmbedding_iff_isStrictMap_injective, Bijective,
    and_assoc]

中文:
引理 isHomeomorph_iff_isStrictMap_bijective
  证明: by
  simp [isHomeomorph_iff_isEmbedding_surjective, isEmbedding_iff_isStrictMap_injective, Bijective,
    and_assoc]

Depends on / 依赖: Bijective, and_assoc, isEmbedding_iff_isStrictMap_injective, isHomeomorph_iff_isEmbedding_surjective
-/
lemma isHomeomorph_iff_isStrictMap_bijective :
    IsHomeomorph f ↔ IsStrictMap f ∧ Bijective f := by
  simp [isHomeomorph_iff_isEmbedding_surjective, isEmbedding_iff_isStrictMap_injective, Bijective,
    and_assoc]

/--
lemma `_root_.Homeomorph.isStrictMap_comp_iff` / 引理 `_root_.Homeomorph.isStrictMap_comp_iff`

English:
lemma _root_.Homeomorph.isStrictMap_comp_iff
  given: (e : X ≃ₜ Y) {f : Y -> Z}
  proof: e.isQuotientMap.isStrictMap_iff.symm

@[deprecated (since := "2026-07-10")] protected alias Homeomorph.isStrictMap_comp_iff :=
  Homeomorph.isStrictMap_comp_iff

中文:
引理 _root_.Homeomorph.isStrictMap_comp_iff
  条件: (e : X ≃ₜ Y) {f : Y -> Z}
  证明: e.isQuotientMap.isStrictMap_iff.symm

@[deprecated (since := "2026-07-10")] protected alias Homeomorph.isStrictMap_comp_iff :=
  Homeomorph.isStrictMap_comp_iff

Depends on / 依赖: e.isQuotientMap.isStrictMap_iff.symm, isQuotientMap, isStrictMap_iff
-/
lemma _root_.Homeomorph.isStrictMap_comp_iff (e : X ≃ₜ Y) {f : Y -> Z} :
    IsStrictMap (f ∘ e) ↔ IsStrictMap f :=
  e.isQuotientMap.isStrictMap_iff.symm

@[deprecated (since := "2026-07-10")] protected alias Homeomorph.isStrictMap_comp_iff :=
  Homeomorph.isStrictMap_comp_iff

/--
lemma `_root_.Homeomorph.comp_isStrictMap_iff` / 引理 `_root_.Homeomorph.comp_isStrictMap_iff`

English:
lemma _root_.Homeomorph.comp_isStrictMap_iff
  given: (e : Y ≃ₜ Z) {f : X -> Y}
  proof: e.isEmbedding.isStrictMap_iff.symm

@[deprecated (since := "2026-07-10")] protected alias Homeomorph.comp_isStrictMap_iff :=
  Homeomorph.comp_isStrictMap_iff

中文:
引理 _root_.Homeomorph.comp_isStrictMap_iff
  条件: (e : Y ≃ₜ Z) {f : X -> Y}
  证明: e.isEmbedding.isStrictMap_iff.symm

@[deprecated (since := "2026-07-10")] protected alias Homeomorph.comp_isStrictMap_iff :=
  Homeomorph.comp_isStrictMap_iff

Depends on / 依赖: e.isEmbedding.isStrictMap_iff.symm, isEmbedding, isStrictMap_iff
-/
lemma _root_.Homeomorph.comp_isStrictMap_iff (e : Y ≃ₜ Z) {f : X -> Y} :
    IsStrictMap (e ∘ f) ↔ IsStrictMap f :=
  e.isEmbedding.isStrictMap_iff.symm

@[deprecated (since := "2026-07-10")] protected alias Homeomorph.comp_isStrictMap_iff :=
  Homeomorph.comp_isStrictMap_iff

end Topology
