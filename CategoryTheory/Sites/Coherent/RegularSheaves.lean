/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Filippo A. E. Nuccio, Riccardo Brasca
-/
module

public import Mathlib.CategoryTheory.EffectiveEpi.Preserves
public import Mathlib.CategoryTheory.Limits.Final.ParallelPair
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Sites.Coherent.Basic
public import Mathlib.CategoryTheory.Sites.EffectiveEpimorphic
/-!

# Sheaves for the regular topology

This file characterises sheaves for the regular topology.

## Main results

* `equalizerCondition_iff_isSheaf`: In a preregular category with pullbacks, the sheaves for the
  regular topology are precisely the presheaves satisfying an equaliser condition with respect to
  effective epimorphisms.

* `isSheaf_of_projective`: In a preregular category in which every object is projective, every
  presheaf is a sheaf for the regular topology.
-/

@[expose] public section

namespace CategoryTheory

open Limits

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]

open Opposite Presieve CategoryTheory.Functor

/--
Definition of `Presieve.regular` / `Presieve.regular` 的定义

English:
class Presieve.regular
  parameters: {X : C} (R : Presieve X)
  axioms and operations (1):
    - single_epi : exists (Y : C) (f : Y ⟶ X), R = Presieve.ofArrows (fun (_ : Unit) => Y) (fun (_ : Unit) => f) ∧ EffectiveEpi f

中文:
类 Presieve.regular
  参数: {X : C} (R : Presieve X)
  公理与运算 (1 个):
    - single_epi : 存在 (Y : C) (f : Y ⟶ X), R = Presieve.ofArrows (fun (_ : 单元) => Y) (fun (_ : 单元) => f) ∧ 有效满态射 f
-/
class Presieve.regular {X : C} (R : Presieve X) : Prop where
  /-- `R` consists of a single epimorphism. -/
  single_epi : exists (Y : C) (f : Y ⟶ X), R = Presieve.ofArrows (fun (_ : Unit) => Y)
    (fun (_ : Unit) => f) ∧ EffectiveEpi f

namespace regularTopology

/--
lemma `equalizerCondition_w` / 引理 `equalizerCondition_w`

English:
lemma equalizerCondition_w
  given: (P : Cᵒᵖ ⥤ D) {X B : C} {π : X ⟶ B} (c : PullbackCone π π)
  proof: by
  simp only [← Functor.map_comp, ← op_comp, c.condition]

中文:
引理 equalizerCondition_w
  条件: (P : Cᵒᵖ ⥤ D) {X B : C} {π : X ⟶ B} (c : PullbackCone π π)
  证明: by
  simp only [← Functor.map_comp, ← op_comp, c.condition]

Depends on / 依赖: Functor, Functor.map_comp, c.condition, condition, isBase_restrict_iff, map_comp, op_comp
-/
lemma equalizerCondition_w (P : Cᵒᵖ ⥤ D) {X B : C} {π : X ⟶ B} (c : PullbackCone π π) :
    P.map π.op ≫ P.map c.fst.op = P.map π.op ≫ P.map c.snd.op := by
  simp only [← Functor.map_comp, ← op_comp, c.condition]

/--
Definition of `SingleEqualizerCondition` / `SingleEqualizerCondition` 的定义

English:
definition SingleEqualizerCondition
  signature: (P : Cᵒᵖ ⥤ D) ⦃X B
  body: forall (c : PullbackCone π π) (_ : IsLimit c),
    Nonempty (IsLimit (Fork.ofι (P.map π.op) (equalizerCondition_w P c)))

中文:
定义 SingleEqualizerCondition
  签名: (P : Cᵒᵖ ⥤ D) ⦃X B
  定义体: forall (c : PullbackCone π π) (_ : IsLimit c),
    Nonempty (IsLimit (Fork.ofι (P.map π.op) (equalizerCondition_w P c)))

Depends on / 依赖: Fork.of, IsLimit, Nonempty, P.map, PullbackCone, equalizerCondition_w
-/
def SingleEqualizerCondition (P : Cᵒᵖ ⥤ D) ⦃X B : C⦄ (π : X ⟶ B) : Prop :=
  forall (c : PullbackCone π π) (_ : IsLimit c),
    Nonempty (IsLimit (Fork.ofι (P.map π.op) (equalizerCondition_w P c)))

/--
Definition of `EqualizerCondition` / `EqualizerCondition` 的定义

English:
definition EqualizerCondition
  signature: (P : Cᵒᵖ ⥤ D)
  body: forall ⦃X B : C⦄ (π : X ⟶ B) [EffectiveEpi π], SingleEqualizerCondition P π

中文:
定义 EqualizerCondition
  签名: (P : Cᵒᵖ ⥤ D)
  定义体: forall ⦃X B : C⦄ (π : X ⟶ B) [EffectiveEpi π], SingleEqualizerCondition P π

Depends on / 依赖: EffectiveEpi, SingleEqualizerCondition
-/
def EqualizerCondition (P : Cᵒᵖ ⥤ D) : Prop :=
  forall ⦃X B : C⦄ (π : X ⟶ B) [EffectiveEpi π], SingleEqualizerCondition P π

set_option backward.defeqAttrib.useBackward true in
/--
theorem `equalizerCondition_of_natIso` / 定理 `equalizerCondition_of_natIso`

English:
theorem equalizerCondition_of_natIso
  statement: {P P' : Cᵒᵖ ⥤ D} (i : P ≅ P')
  proof: fun X B π _ c hc =>
  ⟨Fork.isLimitOfIsos _ (hP π c hc).some _ (i.app _) (i.app _) (i.app _)⟩

中文:
定理 equalizerCondition_of_natIso
  结论: {P P' : Cᵒᵖ ⥤ D} (i : P ≅ P')
  证明: fun X B π _ c hc =>
  ⟨Fork.isLimitOfIsos _ (hP π c hc).some _ (i.app _) (i.app _) (i.app _)⟩
-/
theorem equalizerCondition_of_natIso {P P' : Cᵒᵖ ⥤ D} (i : P ≅ P')
    (hP : EqualizerCondition P) : EqualizerCondition P' := fun X B π _ c hc =>
  ⟨Fork.isLimitOfIsos _ (hP π c hc).some _ (i.app _) (i.app _) (i.app _)⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `equalizerCondition_precomp_of_preservesPullback` / 定理 `equalizerCondition_precomp_of_preservesPullback`

English:
theorem equalizerCondition_precomp_of_preservesPullback
  statement: (P : Cᵒᵖ ⥤ D) (F : E ⥤ C)
  proof: by
  intro X B π _ c hc
  have h : P.map (F.map π).op = (F.op ⋙ P).map π.op := by simp
  refine ⟨(IsLimit.equivIsoLimit (ForkOfι.ext ?_ _ h)) ?_⟩
  · simp only [Functor.comp_map, op_map, Quiver.Hom.unop_op, ← map_comp, ← op_comp, c.condition]
  · refine (hP (F.map π) (PullbackCone.mk (F.map c.fst) (F.map c.snd) ?_) ?_).some
    · simp only [← map_comp, c.condition]
    · exact (isLimitMapConePullbackConeEquiv F c.condition)
        (isLimitOfPreserves F (hc.ofIsoLimit (PullbackCone.ext (Iso.refl _) (by simp) (by simp))))

中文:
定理 equalizerCondition_precomp_of_preservesPullback
  结论: (P : Cᵒᵖ ⥤ D) (F : E ⥤ C)
  证明: by
  intro X B π _ c hc
  have h : P.map (F.map π).op = (F.op ⋙ P).map π.op := by simp
  refine ⟨(IsLimit.equivIsoLimit (ForkOfι.ext ?_ _ h)) ?_⟩
  · simp only [Functor.comp_map, op_map, Quiver.Hom.unop_op, ← map_comp, ← op_comp, c.condition]
  · refine (hP (F.map π) (PullbackCone.mk (F.map c.fst) (F.map c.snd) ?_) ?_).some
    · simp only [← map_comp, c.condition]
    · exact (isLimitMapConePullbackConeEquiv F c.condition)
        (isLimitOfPreserves F (hc.ofIsoLimit (PullbackCone.ext (Iso.refl _) (by simp) (by simp))))

Depends on / 依赖: F.map, F.op, Functor, Functor.comp_map, IsLimit, IsLimit.equivIsoLimit, Iso.refl, P.map, PullbackCone, PullbackCone.ext, PullbackCone.mk, Quiver, Quiver.Hom.unop_op, c.condition, c.fst, c.snd, comp_map, condition, equivIsoLimit, hc.ofIsoLimit
-/
theorem equalizerCondition_precomp_of_preservesPullback (P : Cᵒᵖ ⥤ D) (F : E ⥤ C)
    [forall {X B} (π : X ⟶ B) [EffectiveEpi π], PreservesLimit (cospan π π) F]
    [F.PreservesEffectiveEpis] (hP : EqualizerCondition P) : EqualizerCondition (F.op ⋙ P) := by
  intro X B π _ c hc
  have h : P.map (F.map π).op = (F.op ⋙ P).map π.op := by simp
  refine ⟨(IsLimit.equivIsoLimit (ForkOfι.ext ?_ _ h)) ?_⟩
  · simp only [Functor.comp_map, op_map, Quiver.Hom.unop_op, ← map_comp, ← op_comp, c.condition]
  · refine (hP (F.map π) (PullbackCone.mk (F.map c.fst) (F.map c.snd) ?_) ?_).some
    · simp only [← map_comp, c.condition]
    · exact (isLimitMapConePullbackConeEquiv F c.condition)
        (isLimitOfPreserves F (hc.ofIsoLimit (PullbackCone.ext (Iso.refl _) (by simp) (by simp))))

/--
Definition of `mapToEqualizer` / `mapToEqualizer` 的定义

English:
definition mapToEqualizer
  signature: (P : Cᵒᵖ ⥤ Type*) {W X B : C} (f : X ⟶ B)
  body: ↾fun t =>
    ⟨P.map f.op t, by simp only [Set.mem_ofPred_eq, ← comp_apply, ← Functor.map_comp, ← op_comp, w]⟩

中文:
定义 mapToEqualizer
  签名: (P : Cᵒᵖ ⥤ 类型) {W X B : C} (f : X ⟶ B)
  定义体: ↾fun t =>
    ⟨P.map f.op t, by simp only [Set.mem_ofPred_eq, ← comp_apply, ← Functor.map_comp, ← op_comp, w]⟩

Depends on / 依赖: Functor, Functor.map_comp, IsBasis, P.map, Set.mem_ofPred_eq, and_imp, comp_apply, f.op, map_comp, maximal_iff, mem_ofPred_eq, op_comp, restrict_indep_iff, simp_rw, subset_inter_iff
-/
def mapToEqualizer (P : Cᵒᵖ ⥤ Type*) {W X B : C} (f : X ⟶ B)
    (g₁ g₂ : W ⟶ X) (w : g₁ ≫ f = g₂ ≫ f) :
    P.obj (op B) ⟶ { x : P.obj (op X) | P.map g₁.op x = P.map g₂.op x } :=
  ↾fun t =>
    ⟨P.map f.op t, by simp only [Set.mem_ofPred_eq, ← comp_apply, ← Functor.map_comp, ← op_comp, w]⟩

/--
theorem `EqualizerCondition.bijective_mapToEqualizer_pullback'` / 定理 `EqualizerCondition.bijective_mapToEqualizer_pullback'`

English:
theorem EqualizerCondition.bijective_mapToEqualizer_pullback'
  statement: {P : Cᵒᵖ ⥤ Type*}
  proof: by
  specialize hP π _ hc
  rw [Types.type_equalizer_iff_unique] at hP
  rw [Function.bijective_iff_existsUnique]
  intro ⟨b, hb⟩
  obtain ⟨a, ha₁, ha₂⟩ := hP b hb
  refine ⟨a, ?_, ?_⟩
  · ext
    simpa [mapToEqualizer] using! ha₁
  · intro y h
    apply ha₂ y
    simpa [mapToEqualizer] using Subtype.ext_iff.1 h

中文:
定理 EqualizerCondition.bijective_mapToEqualizer_pullback'
  结论: {P : Cᵒᵖ ⥤ 类型}
  证明: by
  specialize hP π _ hc
  rw [Types.type_equalizer_iff_unique] at hP
  rw [Function.bijective_iff_existsUnique]
  intro ⟨b, hb⟩
  obtain ⟨a, ha₁, ha₂⟩ := hP b hb
  refine ⟨a, ?_, ?_⟩
  · ext
    simpa [mapToEqualizer] using! ha₁
  · intro y h
    apply ha₂ y
    simpa [mapToEqualizer] using Subtype.ext_iff.1 h

Depends on / 依赖: Function, Function.bijective_iff_existsUnique, Subtype, Subtype.ext_iff, Types.type_equalizer_iff_unique, bijective_iff_existsUnique, ext_iff, mapToEqualizer, specialize, type_equalizer_iff_unique
-/
theorem EqualizerCondition.bijective_mapToEqualizer_pullback' {P : Cᵒᵖ ⥤ Type*}
    (hP : EqualizerCondition P) {X B : C} {π : X ⟶ B} [EffectiveEpi π]
    (c : PullbackCone π π) (hc : IsLimit c) :
    Function.Bijective (mapToEqualizer P π c.fst c.snd c.condition) := by
  specialize hP π _ hc
  rw [Types.type_equalizer_iff_unique] at hP
  rw [Function.bijective_iff_existsUnique]
  intro ⟨b, hb⟩
  obtain ⟨a, ha₁, ha₂⟩ := hP b hb
  refine ⟨a, ?_, ?_⟩
  · ext
    simpa [mapToEqualizer] using! ha₁
  · intro y h
    apply ha₂ y
    simpa [mapToEqualizer] using Subtype.ext_iff.1 h

/--
theorem `EqualizerCondition.bijective_mapToEqualizer_pullback` / 定理 `EqualizerCondition.bijective_mapToEqualizer_pullback`

English:
theorem EqualizerCondition.bijective_mapToEqualizer_pullback
  statement: {P : Cᵒᵖ ⥤ Type*}
  proof: bijective_mapToEqualizer_pullback' hP _ (pullback.isLimit _ _)

中文:
定理 EqualizerCondition.bijective_mapToEqualizer_pullback
  结论: {P : Cᵒᵖ ⥤ 类型}
  证明: bijective_mapToEqualizer_pullback' hP _ (pullback.isLimit _ _)

Depends on / 依赖: bijective_mapToEqualizer_pullback, isLimit, pullback, pullback.isLimit
-/
theorem EqualizerCondition.bijective_mapToEqualizer_pullback {P : Cᵒᵖ ⥤ Type*}
    (hP : EqualizerCondition P) {X B : C} (π : X ⟶ B) [EffectiveEpi π] [HasPullback π π] :
    Function.Bijective
      (mapToEqualizer P π (pullback.fst π π) (pullback.snd π π) pullback.condition) :=
  bijective_mapToEqualizer_pullback' hP _ (pullback.isLimit _ _)

/--
theorem `EqualizerCondition.mk'` / 定理 `EqualizerCondition.mk'`

English:
theorem EqualizerCondition.mk'
  statement: (P : Cᵒᵖ ⥤ Type*)
  proof: by
  intro X B π _ c hc
  specialize hP X B π c hc
  rw [Types.type_equalizer_iff_unique]
  rw [Function.bijective_iff_existsUnique] at hP
  intro b hb
  obtain ⟨a, ha₁, ha₂⟩ := hP ⟨b, hb⟩
  refine ⟨a, ?_, ?_⟩
  · simpa [mapToEqualizer] using Subtype.ext_iff.1 ha₁
  · intro y h
    apply ha₂ y
    ext
    simpa [mapToEqualizer] using h

中文:
定理 EqualizerCondition.mk'
  结论: (P : Cᵒᵖ ⥤ 类型)
  证明: by
  intro X B π _ c hc
  specialize hP X B π c hc
  rw [Types.type_equalizer_iff_unique]
  rw [Function.bijective_iff_existsUnique] at hP
  intro b hb
  obtain ⟨a, ha₁, ha₂⟩ := hP ⟨b, hb⟩
  refine ⟨a, ?_, ?_⟩
  · simpa [mapToEqualizer] using Subtype.ext_iff.1 ha₁
  · intro y h
    apply ha₂ y
    ext
    simpa [mapToEqualizer] using h

Depends on / 依赖: Function, Function.bijective_iff_existsUnique, Subtype, Subtype.ext_iff, Types.type_equalizer_iff_unique, _iff_isBasis_inter_ground, and_iff_left, bijective_iff_existsUnique, ext_iff, isBasis, isBasis_restrict_iff, mapToEqualizer, specialize, subset_univ, type_equalizer_iff_unique
-/
theorem EqualizerCondition.mk' (P : Cᵒᵖ ⥤ Type*)
    (hP : forall (X B : C) (π : X ⟶ B) [EffectiveEpi π] (c : PullbackCone π π) (_ : IsLimit c),
      Function.Bijective (mapToEqualizer P π c.fst c.snd c.condition)) :
    EqualizerCondition P := by
  intro X B π _ c hc
  specialize hP X B π c hc
  rw [Types.type_equalizer_iff_unique]
  rw [Function.bijective_iff_existsUnique] at hP
  intro b hb
  obtain ⟨a, ha₁, ha₂⟩ := hP ⟨b, hb⟩
  refine ⟨a, ?_, ?_⟩
  · simpa [mapToEqualizer] using Subtype.ext_iff.1 ha₁
  · intro y h
    apply ha₂ y
    ext
    simpa [mapToEqualizer] using h

set_option backward.isDefEq.respectTransparency false in
/--
theorem `EqualizerCondition.mk` / 定理 `EqualizerCondition.mk`

English:
theorem EqualizerCondition.mk
  statement: (P : Cᵒᵖ ⥤ Type*)
  proof: by
  intro X B π _ c hc
  have : HasPullback π π := ⟨c, hc⟩
  specialize hP X B π
  rw [Types.type_equalizer_iff_unique]
  rw [Function.bijective_iff_existsUnique] at hP
  intro b hb
  have h₁ : ((pullbackIsPullback π π).conePointUniqueUpToIso hc).hom ≫ c.fst =
    pullback.fst π π := by simp
  have hb' : P.map (pullback.fst π π).op b = P.map (pullback.snd _ _).op b := by
    rw [← h₁]; rw [op_comp]; rw [Functor.map_comp]; rw [comp_apply]; rw [hb]
    simp [← comp_apply, ← Functor.map_comp, ← op_comp]
  obtain ⟨a, ha₁, ha₂⟩ := hP ⟨b, hb'⟩
  refine ⟨a, ?_, ?_⟩
  · simpa [mapToEqualizer] using ha₁
  · simpa [mapToEqualizer] using ha₂

中文:
定理 EqualizerCondition.mk
  结论: (P : Cᵒᵖ ⥤ 类型)
  证明: by
  intro X B π _ c hc
  have : HasPullback π π := ⟨c, hc⟩
  specialize hP X B π
  rw [Types.type_equalizer_iff_unique]
  rw [Function.bijective_iff_existsUnique] at hP
  intro b hb
  have h₁ : ((pullbackIsPullback π π).conePointUniqueUpToIso hc).hom ≫ c.fst =
    pullback.fst π π := by simp
  have hb' : P.map (pullback.fst π π).op b = P.map (pullback.snd _ _).op b := by
    rw [← h₁]; rw [op_comp]; rw [Functor.map_comp]; rw [comp_apply]; rw [hb]
    simp [← comp_apply, ← Functor.map_comp, ← op_comp]
  obtain ⟨a, ha₁, ha₂⟩ := hP ⟨b, hb'⟩
  refine ⟨a, ?_, ?_⟩
  · simpa [mapToEqualizer] using ha₁
  · simpa [mapToEqualizer] using ha₂

Depends on / 依赖: Function, Function.bijective_iff_existsUnique, Functor, Functor.map_comp, HasPullback, P.map, Types.type_equalizer_iff_unique, bijective_iff_existsUnique, c.fst, comp_apply, conePointUniqueUpToIso, map_comp, op_comp, pullback, pullback.fst, pullback.snd, pullbackIsPullback, specialize, type_equalizer_iff_unique
-/
theorem EqualizerCondition.mk (P : Cᵒᵖ ⥤ Type*)
    (hP : forall (X B : C) (π : X ⟶ B) [EffectiveEpi π] [HasPullback π π], Function.Bijective
    (mapToEqualizer P π (pullback.fst π π) (pullback.snd π π)
    pullback.condition)) : EqualizerCondition P := by
  intro X B π _ c hc
  have : HasPullback π π := ⟨c, hc⟩
  specialize hP X B π
  rw [Types.type_equalizer_iff_unique]
  rw [Function.bijective_iff_existsUnique] at hP
  intro b hb
  have h₁ : ((pullbackIsPullback π π).conePointUniqueUpToIso hc).hom ≫ c.fst =
    pullback.fst π π := by simp
  have hb' : P.map (pullback.fst π π).op b = P.map (pullback.snd _ _).op b := by
    rw [← h₁]; rw [op_comp]; rw [Functor.map_comp]; rw [comp_apply]; rw [hb]
    simp [← comp_apply, ← Functor.map_comp, ← op_comp]
  obtain ⟨a, ha₁, ha₂⟩ := hP ⟨b, hb'⟩
  refine ⟨a, ?_, ?_⟩
  · simpa [mapToEqualizer] using ha₁
  · simpa [mapToEqualizer] using ha₂

/--
lemma `equalizerCondition_w'` / 引理 `equalizerCondition_w'`

English:
lemma equalizerCondition_w'
  statement: (P : Cᵒᵖ ⥤ Type*) {X B : C} (π : X ⟶ B)
  proof: by
  simp only [← Functor.map_comp, ← op_comp, pullback.condition]

中文:
引理 equalizerCondition_w'
  结论: (P : Cᵒᵖ ⥤ 类型) {X B : C} (π : X ⟶ B)
  证明: by
  simp only [← Functor.map_comp, ← op_comp, pullback.condition]

Depends on / 依赖: Functor, Functor.map_comp, condition, map_comp, op_comp, pullback, pullback.condition
-/
lemma equalizerCondition_w' (P : Cᵒᵖ ⥤ Type*) {X B : C} (π : X ⟶ B)
    [HasPullback π π] : P.map π.op ≫ P.map (pullback.fst π π).op =
    P.map π.op ≫ P.map (pullback.snd π π).op := by
  simp only [← Functor.map_comp, ← op_comp, pullback.condition]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `mapToEqualizer_eq_comp` / 引理 `mapToEqualizer_eq_comp`

English:
lemma mapToEqualizer_eq_comp
  given: (P : Cᵒᵖ ⥤ Type*) {X B : C} (π : X ⟶ B) [HasPullback π π]
  proof: by
  rw [← Iso.comp_inv_eq (α := Types.equalizerIso _ _)]
  apply equalizer.hom_ext
  aesop

中文:
引理 mapToEqualizer_eq_comp
  条件: (P : Cᵒᵖ ⥤ 类型) {X B : C} (π : X ⟶ B) [HasPullback π π]
  证明: by
  rw [← Iso.comp_inv_eq (α := Types.equalizerIso _ _)]
  apply equalizer.hom_ext
  aesop

Depends on / 依赖: Iso.comp_inv_eq, Types.equalizerIso, comp_inv_eq, equalizer, equalizer.hom_ext, equalizerIso, hom_ext
-/
lemma mapToEqualizer_eq_comp (P : Cᵒᵖ ⥤ Type*) {X B : C} (π : X ⟶ B) [HasPullback π π] :
    mapToEqualizer P π (pullback.fst π π) (pullback.snd π π) pullback.condition =
    equalizer.lift (P.map π.op) (equalizerCondition_w' P π) ≫
    (Types.equalizerIso _ _).hom := by
  rw [← Iso.comp_inv_eq (α := Types.equalizerIso _ _)]
  apply equalizer.hom_ext
  aesop

set_option backward.isDefEq.respectTransparency false in
/--
theorem `equalizerCondition_iff_isIso_lift` / 定理 `equalizerCondition_iff_isIso_lift`

English:
theorem equalizerCondition_iff_isIso_lift
  given: (P : Cᵒᵖ ⥤ Type*)
  statement: EqualizerCondition P ↔
  proof: by
  constructor
  · intro hP X B π _ _
    have h := hP.bijective_mapToEqualizer_pullback π
    rw [← isIso_iff_bijective]; rw [mapToEqualizer_eq_comp] at h
    exact IsIso.of_isIso_comp_right (equalizer.lift (P.map π.op)
      (equalizerCondition_w' P π))
      (Types.equalizerIso _ _).hom
  · intro hP
    apply EqualizerCondition.mk
    intro X B π _ _
    rw [mapToEqualizer_eq_comp]; rw [← isIso_iff_bijective]
    infer_instance

中文:
定理 equalizerCondition_iff_isIso_lift
  条件: (P : Cᵒᵖ ⥤ 类型)
  结论: EqualizerCondition P ↔
  证明: by
  constructor
  · intro hP X B π _ _
    have h := hP.bijective_mapToEqualizer_pullback π
    rw [← isIso_iff_bijective]; rw [mapToEqualizer_eq_comp] at h
    exact IsIso.of_isIso_comp_right (equalizer.lift (P.map π.op)
      (equalizerCondition_w' P π))
      (Types.equalizerIso _ _).hom
  · intro hP
    apply EqualizerCondition.mk
    intro X B π _ _
    rw [mapToEqualizer_eq_comp]; rw [← isIso_iff_bijective]
    infer_instance

Depends on / 依赖: EqualizerCondition, EqualizerCondition.mk, IsIso.of_isIso_comp_right, P.map, Types.equalizerIso, bijective_mapToEqualizer_pullback, equalizer, equalizer.lift, equalizerCondition_w, equalizerIso, hP.bijective_mapToEqualizer_pullback, infer_instance, isIso_iff_bijective, mapToEqualizer_eq_comp, of_isIso_comp_right, toMatroid
-/
theorem equalizerCondition_iff_isIso_lift (P : Cᵒᵖ ⥤ Type*) : EqualizerCondition P ↔
    forall (X B : C) (π : X ⟶ B) [EffectiveEpi π] [HasPullback π π],
      IsIso (equalizer.lift (P.map π.op) (equalizerCondition_w' P π)) := by
  constructor
  · intro hP X B π _ _
    have h := hP.bijective_mapToEqualizer_pullback π
    rw [← isIso_iff_bijective]; rw [mapToEqualizer_eq_comp] at h
    exact IsIso.of_isIso_comp_right (equalizer.lift (P.map π.op)
      (equalizerCondition_w' P π))
      (Types.equalizerIso _ _).hom
  · intro hP
    apply EqualizerCondition.mk
    intro X B π _ _
    rw [mapToEqualizer_eq_comp]; rw [← isIso_iff_bijective]
    infer_instance

/--
theorem `equalizerCondition_iff_of_equivalence` / 定理 `equalizerCondition_iff_of_equivalence`

English:
theorem equalizerCondition_iff_of_equivalence
  statement: (P : Cᵒᵖ ⥤ D)
  proof: ⟨fun h => equalizerCondition_precomp_of_preservesPullback P e.inverse h, fun h =>
    equalizerCondition_of_natIso (e.op.funInvIdAssoc P)
      (equalizerCondition_precomp_of_preservesPullback (e.op.inverse ⋙ P) e.functor h)⟩

中文:
定理 equalizerCondition_iff_of_equivalence
  结论: (P : Cᵒᵖ ⥤ D)
  证明: ⟨fun h => equalizerCondition_precomp_of_preservesPullback P e.inverse h, fun h =>
    equalizerCondition_of_natIso (e.op.funInvIdAssoc P)
      (equalizerCondition_precomp_of_preservesPullback (e.op.inverse ⋙ P) e.functor h)⟩

Depends on / 依赖: e.functor, e.inverse, e.op.funInvIdAssoc, e.op.inverse, equalizerCondition_of_natIso, equalizerCondition_precomp_of_preservesPullback, funInvIdAssoc, functor, inverse
-/
theorem equalizerCondition_iff_of_equivalence (P : Cᵒᵖ ⥤ D)
    (e : C ≌ E) : EqualizerCondition P ↔ EqualizerCondition (e.op.inverse ⋙ P) :=
  ⟨fun h => equalizerCondition_precomp_of_preservesPullback P e.inverse h, fun h =>
    equalizerCondition_of_natIso (e.op.funInvIdAssoc P)
      (equalizerCondition_precomp_of_preservesPullback (e.op.inverse ⋙ P) e.functor h)⟩

set_option backward.isDefEq.respectTransparency false in
open WalkingParallelPair WalkingParallelPairHom in
/--
theorem `parallelPair_pullback_initial` / 定理 `parallelPair_pullback_initial`

English:
theorem parallelPair_pullback_initial
  statement: {X B : C} (π : X ⟶ B)
  proof: by
  apply Limits.parallelPair_initial_mk
  · intro ⟨Z⟩
    obtain ⟨_, f, g, ⟨⟩, hh⟩ := Z.property
    let X' : (Presieve.ofArrows (fun () => X) (fun () => π)).category :=
      Presieve.categoryMk _ π (ofArrows.mk ())
    let f' : Z.obj.left ⟶ X'.obj.left := f
    exact ⟨(ObjectProperty.homMk (Over.homMk f')).op⟩
  · intro ⟨Z⟩ ⟨i⟩ ⟨j⟩
    have hi := Over.w i.hom
    have hj := Over.w j.hom
    dsimp at hi hj
    let ij := PullbackCone.IsLimit.lift hc i.hom.left j.hom.left (by simp [hi, hj])
    refine ⟨Quiver.Hom.op (ObjectProperty.homMk (Over.homMk ij)), ?_, ?_⟩
    all_goals congr; aesop

中文:
定理 parallelPair_pullback_initial
  结论: {X B : C} (π : X ⟶ B)
  证明: by
  apply Limits.parallelPair_initial_mk
  · intro ⟨Z⟩
    obtain ⟨_, f, g, ⟨⟩, hh⟩ := Z.property
    let X' : (Presieve.ofArrows (fun () => X) (fun () => π)).category :=
      Presieve.categoryMk _ π (ofArrows.mk ())
    let f' : Z.obj.left ⟶ X'.obj.left := f
    exact ⟨(ObjectProperty.homMk (Over.homMk f')).op⟩
  · intro ⟨Z⟩ ⟨i⟩ ⟨j⟩
    have hi := Over.w i.hom
    have hj := Over.w j.hom
    dsimp at hi hj
    let ij := PullbackCone.IsLimit.lift hc i.hom.left j.hom.left (by simp [hi, hj])
    refine ⟨Quiver.Hom.op (ObjectProperty.homMk (Over.homMk ij)), ?_, ?_⟩
    all_goals congr; aesop

Depends on / 依赖: Sieve.ofArrows, arrows, arrows.category, ofArrows
-/
theorem parallelPair_pullback_initial {X B : C} (π : X ⟶ B)
    (c : PullbackCone π π) (hc : IsLimit c) :
    (parallelPair (C := (Sieve.ofArrows (fun (_ : Unit) => X) (fun _ => π)).arrows.categoryᵒᵖ)
    (Y := op ((Presieve.categoryMk _ (c.fst ≫ π) ⟨_, c.fst, π, ofArrows.mk (), rfl⟩)))
    (X := op ((Presieve.categoryMk _ π (Sieve.ofArrows_mk _ _ Unit.unit))))
    ((ObjectProperty.homMk (Over.homMk c.fst)).op)
    ((ObjectProperty.homMk (Over.homMk c.snd c.condition.symm)).op)).Initial := by
  apply Limits.parallelPair_initial_mk
  · intro ⟨Z⟩
    obtain ⟨_, f, g, ⟨⟩, hh⟩ := Z.property
    let X' : (Presieve.ofArrows (fun () => X) (fun () => π)).category :=
      Presieve.categoryMk _ π (ofArrows.mk ())
    let f' : Z.obj.left ⟶ X'.obj.left := f
    exact ⟨(ObjectProperty.homMk (Over.homMk f')).op⟩
  · intro ⟨Z⟩ ⟨i⟩ ⟨j⟩
    have hi := Over.w i.hom
    have hj := Over.w j.hom
    dsimp at hi hj
    let ij := PullbackCone.IsLimit.lift hc i.hom.left j.hom.left (by simp [hi, hj])
    refine ⟨Quiver.Hom.op (ObjectProperty.homMk (Over.homMk ij)), ?_, ?_⟩
    all_goals congr; aesop

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `isLimit_forkOfι_equiv` / `isLimit_forkOfι_equiv` 的定义

English:
definition isLimit_forkOfι_equiv
  signature: (P : Cᵒᵖ ⥤ D) {X B : C} (π : X ⟶ B)
  body: by
  let S := (Sieve.ofArrows (fun (_ : Unit) => X) (fun _ => π)).arrows
  let X' := S.categoryMk π ⟨_, 𝟙 _, π, ofArrows.mk (), Category.id_comp _⟩
  let P' := S.categoryMk (c.fst ≫ π) ⟨_, c.fst, π, ofArrows.mk (), rfl⟩
  let fst : P' ⟶ X' := ObjectProperty.homMk (Over.homMk c.fst)
  let snd : P' ⟶ X' := ObjectProperty.homMk (Over.homMk c.snd c.condition.symm)
  let F : S.categoryᵒᵖ ⥤ D := S.diagram.op ⋙ P
  let G := parallelPair (P.map c.fst.op) (P.map c.snd.op)
  let H := parallelPair fst.op snd.op
  have : H.Initial := parallelPair_pullback_initial π c hc
  let i : H ⋙ F ≅ G := parallelPair.ext (Iso.refl _) (Iso.refl _) (by aesop) (by aesop)
  refine (IsLimit.equivOfNatIsoOfIso i.symm _ _ ?_).trans (Functor.Initial.isLimitWhiskerEquiv H _)
  refine Cone.ext (Iso.refl _) ?_
  rintro ⟨_ | _⟩
  all_goals aesop

中文:
定义 isLimit_forkOfι_equiv
  签名: (P : Cᵒᵖ ⥤ D) {X B : C} (π : X ⟶ B)
  定义体: by
  let S := (Sieve.ofArrows (fun (_ : Unit) => X) (fun _ => π)).arrows
  let X' := S.categoryMk π ⟨_, 𝟙 _, π, ofArrows.mk (), Category.id_comp _⟩
  let P' := S.categoryMk (c.fst ≫ π) ⟨_, c.fst, π, ofArrows.mk (), rfl⟩
  let fst : P' ⟶ X' := ObjectProperty.homMk (Over.homMk c.fst)
  let snd : P' ⟶ X' := ObjectProperty.homMk (Over.homMk c.snd c.condition.symm)
  let F : S.categoryᵒᵖ ⥤ D := S.diagram.op ⋙ P
  let G := parallelPair (P.map c.fst.op) (P.map c.snd.op)
  let H := parallelPair fst.op snd.op
  have : H.Initial := parallelPair_pullback_initial π c hc
  let i : H ⋙ F ≅ G := parallelPair.ext (Iso.refl _) (Iso.refl _) (by aesop) (by aesop)
  refine (IsLimit.equivOfNatIsoOfIso i.symm _ _ ?_).trans (Functor.Initial.isLimitWhiskerEquiv H _)
  refine Cone.ext (Iso.refl _) ?_
  rintro ⟨_ | _⟩
  all_goals aesop

Depends on / 依赖: Category, Category.id_comp, ObjectProperty, ObjectProperty.homMk, Over.homMk, P.map, S.category, S.categoryMk, S.diagram.op, Sieve.ofArrows, arrows, c.condition.symm, c.fst, c.fst.op, c.snd, c.snd.op, categoryMk, condition, diagram, fst.op
-/
noncomputable def isLimit_forkOfι_equiv (P : Cᵒᵖ ⥤ D) {X B : C} (π : X ⟶ B)
    (c : PullbackCone π π) (hc : IsLimit c) :
    IsLimit (Fork.ofι (P.map π.op) (equalizerCondition_w P c)) ≃
    IsLimit (P.mapCone (Sieve.ofArrows (fun (_ : Unit) => X) fun _ => π).arrows.cocone.op) := by
  let S := (Sieve.ofArrows (fun (_ : Unit) => X) (fun _ => π)).arrows
  let X' := S.categoryMk π ⟨_, 𝟙 _, π, ofArrows.mk (), Category.id_comp _⟩
  let P' := S.categoryMk (c.fst ≫ π) ⟨_, c.fst, π, ofArrows.mk (), rfl⟩
  let fst : P' ⟶ X' := ObjectProperty.homMk (Over.homMk c.fst)
  let snd : P' ⟶ X' := ObjectProperty.homMk (Over.homMk c.snd c.condition.symm)
  let F : S.categoryᵒᵖ ⥤ D := S.diagram.op ⋙ P
  let G := parallelPair (P.map c.fst.op) (P.map c.snd.op)
  let H := parallelPair fst.op snd.op
  have : H.Initial := parallelPair_pullback_initial π c hc
  let i : H ⋙ F ≅ G := parallelPair.ext (Iso.refl _) (Iso.refl _) (by aesop) (by aesop)
  refine (IsLimit.equivOfNatIsoOfIso i.symm _ _ ?_).trans (Functor.Initial.isLimitWhiskerEquiv H _)
  refine Cone.ext (Iso.refl _) ?_
  rintro ⟨_ | _⟩
  all_goals aesop

/--
lemma `equalizerConditionMap_iff_nonempty_isLimit` / 引理 `equalizerConditionMap_iff_nonempty_isLimit`

English:
lemma equalizerConditionMap_iff_nonempty_isLimit
  given: (P : Cᵒᵖ ⥤ D) ⦃X B
  statement: C⦄ (π : X ⟶ B)
  proof: by
  constructor
  · intro h
    exact ⟨isLimit_forkOfι_equiv _ _ _ (pullbackIsPullback π π) (h _ (pullbackIsPullback π π)).some⟩
  · intro ⟨h⟩
    exact fun c hc => ⟨(isLimit_forkOfι_equiv _ _ _ hc).symm h⟩

中文:
引理 equalizerConditionMap_iff_nonempty_isLimit
  条件: (P : Cᵒᵖ ⥤ D) ⦃X B
  结论: C⦄ (π : X ⟶ B)
  证明: by
  constructor
  · intro h
    exact ⟨isLimit_forkOfι_equiv _ _ _ (pullbackIsPullback π π) (h _ (pullbackIsPullback π π)).some⟩
  · intro ⟨h⟩
    exact fun c hc => ⟨(isLimit_forkOfι_equiv _ _ _ hc).symm h⟩

Depends on / 依赖: pullbackIsPullback
-/
lemma equalizerConditionMap_iff_nonempty_isLimit (P : Cᵒᵖ ⥤ D) ⦃X B : C⦄ (π : X ⟶ B)
    [HasPullback π π] : SingleEqualizerCondition P π ↔
      Nonempty (IsLimit (P.mapCone
        (Sieve.ofArrows (fun (_ : Unit) => X) (fun _ => π)).arrows.cocone.op)) := by
  constructor
  · intro h
    exact ⟨isLimit_forkOfι_equiv _ _ _ (pullbackIsPullback π π) (h _ (pullbackIsPullback π π)).some⟩
  · intro ⟨h⟩
    exact fun c hc => ⟨(isLimit_forkOfι_equiv _ _ _ hc).symm h⟩

/--
lemma `equalizerCondition_iff_isSheaf` / 引理 `equalizerCondition_iff_isSheaf`

English:
lemma equalizerCondition_iff_isSheaf
  statement: (F : Cᵒᵖ ⥤ D) [Preregular C]
  proof: by
  dsimp [regularTopology]
  rw [Presheaf.isSheaf_iff_isLimit_coverage]
  constructor
  · rintro hF X _ ⟨Y, f, rfl, _⟩
    exact (equalizerConditionMap_iff_nonempty_isLimit F f).1 (hF f)
  · intro hF Y X f _
    exact (equalizerConditionMap_iff_nonempty_isLimit F f).2 (hF _ ⟨_, f, rfl, inferInstance⟩)

中文:
引理 equalizerCondition_iff_isSheaf
  结论: (F : Cᵒᵖ ⥤ D) [Preregular C]
  证明: by
  dsimp [regularTopology]
  rw [Presheaf.isSheaf_iff_isLimit_coverage]
  constructor
  · rintro hF X _ ⟨Y, f, rfl, _⟩
    exact (equalizerConditionMap_iff_nonempty_isLimit F f).1 (hF f)
  · intro hF Y X f _
    exact (equalizerConditionMap_iff_nonempty_isLimit F f).2 (hF _ ⟨_, f, rfl, inferInstance⟩)

Depends on / 依赖: Presheaf, Presheaf.isSheaf_iff_isLimit_coverage, equalizerConditionMap_iff_nonempty_isLimit, isSheaf_iff_isLimit_coverage, regularTopology
-/
lemma equalizerCondition_iff_isSheaf (F : Cᵒᵖ ⥤ D) [Preregular C]
    [forall {Y X : C} (f : Y ⟶ X) [EffectiveEpi f], HasPullback f f] :
    EqualizerCondition F ↔ Presheaf.IsSheaf (regularTopology C) F := by
  dsimp [regularTopology]
  rw [Presheaf.isSheaf_iff_isLimit_coverage]
  constructor
  · rintro hF X _ ⟨Y, f, rfl, _⟩
    exact (equalizerConditionMap_iff_nonempty_isLimit F f).1 (hF f)
  · intro hF Y X f _
    exact (equalizerConditionMap_iff_nonempty_isLimit F f).2 (hF _ ⟨_, f, rfl, inferInstance⟩)

/--
lemma `isSheafFor_regular_of_projective` / 引理 `isSheafFor_regular_of_projective`

English:
lemma isSheafFor_regular_of_projective
  statement: {X : C} (S : Presieve X) [S.regular] [Projective X]
  proof: by
  obtain ⟨Y, f, rfl, hf⟩ := Presieve.regular.single_epi (R := S)
  rw [isSheafFor_arrows_iff]
refine fun x hx => ⟨F.map (Projective.factorThru (𝟙 _) f).op x (), fun _ => ?_, fun y h => ?_⟩
  · simpa using (hx () () Y (𝟙 Y) (f ≫ (Projective.factorThru (𝟙 _) f)) (by simp)).symm
  · simp [← h (), ← comp_apply, ← Functor.map_comp, ← op_comp]

中文:
引理 isSheafFor_regular_of_projective
  结论: {X : C} (S : Presieve X) [S.regular] [投射 X]
  证明: by
  obtain ⟨Y, f, rfl, hf⟩ := Presieve.regular.single_epi (R := S)
  rw [isSheafFor_arrows_iff]
refine fun x hx => ⟨F.map (Projective.factorThru (𝟙 _) f).op x (), fun _ => ?_, fun y h => ?_⟩
  · simpa using (hx () () Y (𝟙 Y) (f ≫ (Projective.factorThru (𝟙 _) f)) (by simp)).symm
  · simp [← h (), ← comp_apply, ← Functor.map_comp, ← op_comp]

Depends on / 依赖: F.map, Functor, Functor.map_comp, Presieve, Presieve.regular.single_epi, Projective, Projective.factorThru, comp_apply, factorThru, isSheafFor_arrows_iff, map_comp, op_comp, regular, single_epi
-/
lemma isSheafFor_regular_of_projective {X : C} (S : Presieve X) [S.regular] [Projective X]
    (F : Cᵒᵖ ⥤ Type*) : S.IsSheafFor F := by
  obtain ⟨Y, f, rfl, hf⟩ := Presieve.regular.single_epi (R := S)
  rw [isSheafFor_arrows_iff]
refine fun x hx => ⟨F.map (Projective.factorThru (𝟙 _) f).op x (), fun _ => ?_, fun y h => ?_⟩
  · simpa using (hx () () Y (𝟙 Y) (f ≫ (Projective.factorThru (𝟙 _) f)) (by simp)).symm
  · simp [← h (), ← comp_apply, ← Functor.map_comp, ← op_comp]

/--
theorem `isSheaf_of_projective` / 定理 `isSheaf_of_projective`

English:
theorem isSheaf_of_projective
  given: (F : Cᵒᵖ ⥤ D) [Preregular C] [forall (X : C), Projective X]
  proof: fun _ => (isSheaf_coverage _ _).mpr fun S ⟨_, h⟩ => have : S.regular := ⟨_, h⟩
    isSheafFor_regular_of_projective _ _

中文:
定理 isSheaf_of_projective
  条件: (F : Cᵒᵖ ⥤ D) [Preregular C] [对任意 (X : C), 投射 X]
  证明: fun _ => (isSheaf_coverage _ _).mpr fun S ⟨_, h⟩ => have : S.regular := ⟨_, h⟩
    isSheafFor_regular_of_projective _ _

Depends on / 依赖: S.regular, isSheafFor_regular_of_projective, isSheaf_coverage, regular
-/
theorem isSheaf_of_projective (F : Cᵒᵖ ⥤ D) [Preregular C] [forall (X : C), Projective X] :
    Presheaf.IsSheaf (regularTopology C) F :=
  fun _ => (isSheaf_coverage _ _).mpr fun S ⟨_, h⟩ => have : S.regular := ⟨_, h⟩
    isSheafFor_regular_of_projective _ _

/--
lemma `isSheaf_yoneda_obj` / 引理 `isSheaf_yoneda_obj`

English:
lemma isSheaf_yoneda_obj
  given: [Preregular C] (W : C)
  proof: by
  rw [regularTopology]; rw [isSheaf_coverage]
  intro X S ⟨_, hS⟩
  have : S.regular := ⟨_, hS⟩
  obtain ⟨Y, f, rfl, hf⟩ := Presieve.regular.single_epi (R := S)
  have h_colim := isColimitOfEffectiveEpiStruct f hf.effectiveEpi.some
  rw [← Sieve.generateSingleton_eq]; rw [← Presieve.ofArrows_pUnit] at h_colim
  intro x hx
  let x_ext := Presieve.FamilyOfElements.sieveExtend x
  have hx_ext := Presieve.FamilyOfElements.Compatible.sieveExtend hx
  let S := Sieve.generate (Presieve.ofArrows (fun () => Y) (fun () => f))
  obtain ⟨t, t_amalg, t_uniq⟩ :=
    (Sieve.forallYonedaIsSheaf_iff_colimit S).mpr ⟨h_colim⟩ W x_ext hx_ext
  refine ⟨t, ?_, ?_⟩
  · convert!
    Presieve.isAmalgamation_restrict
      (Sieve.le_generate (Presieve.ofArrows (fun () => Y) (fun () => f))) _ _ t_amalg
    exact (Presieve.restrict_extend hx).symm
· exact fun y hy => t_uniq y Presieve.isAmalgamation_sieveExtend x y hy

中文:
引理 isSheaf_yoneda_obj
  条件: [Preregular C] (W : C)
  证明: by
  rw [regularTopology]; rw [isSheaf_coverage]
  intro X S ⟨_, hS⟩
  have : S.regular := ⟨_, hS⟩
  obtain ⟨Y, f, rfl, hf⟩ := Presieve.regular.single_epi (R := S)
  have h_colim := isColimitOfEffectiveEpiStruct f hf.effectiveEpi.some
  rw [← Sieve.generateSingleton_eq]; rw [← Presieve.ofArrows_pUnit] at h_colim
  intro x hx
  let x_ext := Presieve.FamilyOfElements.sieveExtend x
  have hx_ext := Presieve.FamilyOfElements.Compatible.sieveExtend hx
  let S := Sieve.generate (Presieve.ofArrows (fun () => Y) (fun () => f))
  obtain ⟨t, t_amalg, t_uniq⟩ :=
    (Sieve.forallYonedaIsSheaf_iff_colimit S).mpr ⟨h_colim⟩ W x_ext hx_ext
  refine ⟨t, ?_, ?_⟩
  · convert!
    Presieve.isAmalgamation_restrict
      (Sieve.le_generate (Presieve.ofArrows (fun () => Y) (fun () => f))) _ _ t_amalg
    exact (Presieve.restrict_extend hx).symm
· exact fun y hy => t_uniq y Presieve.isAmalgamation_sieveExtend x y hy

Depends on / 依赖: Compatible, FamilyOfElements, Presieve, Presieve.FamilyOfElements.Compatible.sieveExtend, Presieve.FamilyOfElements.sieveExtend, Presieve.ofArrows, Presieve.ofArrows_pUnit, Presieve.regular.single_epi, S.regular, Sieve.generate, Sieve.generateSingleton_eq, effectiveEpi, generate, generateSingleton_eq, h_colim, hf.effectiveEpi.some, hx_ext, isColimitOfEffectiveEpiStruct, isSheaf_coverage, ofArrows
-/
lemma isSheaf_yoneda_obj [Preregular C] (W : C) :
    Presieve.IsSheaf (regularTopology C) (yoneda.obj W) := by
  rw [regularTopology]; rw [isSheaf_coverage]
  intro X S ⟨_, hS⟩
  have : S.regular := ⟨_, hS⟩
  obtain ⟨Y, f, rfl, hf⟩ := Presieve.regular.single_epi (R := S)
  have h_colim := isColimitOfEffectiveEpiStruct f hf.effectiveEpi.some
  rw [← Sieve.generateSingleton_eq]; rw [← Presieve.ofArrows_pUnit] at h_colim
  intro x hx
  let x_ext := Presieve.FamilyOfElements.sieveExtend x
  have hx_ext := Presieve.FamilyOfElements.Compatible.sieveExtend hx
  let S := Sieve.generate (Presieve.ofArrows (fun () => Y) (fun () => f))
  obtain ⟨t, t_amalg, t_uniq⟩ :=
    (Sieve.forallYonedaIsSheaf_iff_colimit S).mpr ⟨h_colim⟩ W x_ext hx_ext
  refine ⟨t, ?_, ?_⟩
  · convert!
    Presieve.isAmalgamation_restrict
      (Sieve.le_generate (Presieve.ofArrows (fun () => Y) (fun () => f))) _ _ t_amalg
    exact (Presieve.restrict_extend hx).symm
· exact fun y hy => t_uniq y Presieve.isAmalgamation_sieveExtend x y hy

/--
Instance `subcanonical` / 实例 `subcanonical`

English:
instance subcanonical
  signature: [Preregular C]
  body: GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj _ isSheaf_yoneda_obj

中文:
实例 subcanonical
  签名: [Preregular C]
  定义体: GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj _ isSheaf_yoneda_obj

Depends on / 依赖: GrothendieckTopology, GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj, Subcanonical, isSheaf_yoneda_obj, of_isSheaf_yoneda_obj
-/
instance subcanonical [Preregular C] : (regularTopology C).Subcanonical :=
  GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj _ isSheaf_yoneda_obj

end regularTopology

end CategoryTheory
