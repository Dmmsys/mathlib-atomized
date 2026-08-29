/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Hypercover.ZeroFamily
public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Mathlib.AlgebraicGeometry.Cover.QuasiCompact

/-!
# Quasi-compact precoverage

In this file we define the quasi-compact precoverage. A cover is covering in the quasi-compact
precoverage if it is a quasi-compact cover, i.e., if every affine open of the base can be covered
by a finite union of images of quasi-compact opens of the components.

The fpqc precoverage is the precoverage by flat covers that are quasi-compact in this sense.
-/

@[expose] public section

universe w' w v u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}}

@[simp]
/--
lemma `quasiCompactCover_shrink_iff` / 引理 `quasiCompactCover_shrink_iff`

English:
lemma quasiCompactCover_shrink_iff
  given: (E : PreZeroHypercover.{w} S)
  proof: ⟨fun _ => .of_hom E.fromShrink, fun _ => .of_hom E.toShrink⟩

中文:
引理 quasiCompactCover_shrink_iff
  条件: (E : PreZeroHypercover.{w} S)
  证明: ⟨fun _ => .of_hom E.fromShrink, fun _ => .of_hom E.toShrink⟩

Depends on / 依赖: E.fromShrink, E.toShrink, fromShrink, of_hom, toShrink
-/
lemma quasiCompactCover_shrink_iff (E : PreZeroHypercover.{w} S) :
    QuasiCompactCover E.shrink ↔ QuasiCompactCover E :=
  ⟨fun _ => .of_hom E.fromShrink, fun _ => .of_hom E.toShrink⟩

/-- The pre-`0`-hypercover family on the category of schemes underlying the fpqc precoverage. -/
@[simps]
/--
Definition of `qcCoverFamily` / `qcCoverFamily` 的定义

English:
definition qcCoverFamily
  signature: : PreZeroHypercoverFamily Scheme.{u} where
  body: X.quasiCompactCover
  iff_shrink {_} E := (quasiCompactCover_shrink_iff E).symm

中文:
定义 qcCoverFamily
  签名: : PreZeroHypercoverFamily Scheme.{u} where
  定义体: X.quasiCompactCover
  iff_shrink {_} E := (quasiCompactCover_shrink_iff E).symm

Depends on / 依赖: X.quasiCompactCover, quasiCompactCover
-/
def qcCoverFamily : PreZeroHypercoverFamily Scheme.{u} where
  property X := X.quasiCompactCover
  iff_shrink {_} E := (quasiCompactCover_shrink_iff E).symm

/--
Definition of `qcPrecoverage` / `qcPrecoverage` 的定义

English:
definition qcPrecoverage
  signature: : Precoverage Scheme.{u}
  body: qcCoverFamily.precoverage

@[simp]

中文:
定义 qcPrecoverage
  签名: : Precoverage Scheme.{u}
  定义体: qcCoverFamily.precoverage

@[simp]

Depends on / 依赖: precoverage, qcCoverFamily, qcCoverFamily.precoverage
-/
def qcPrecoverage : Precoverage Scheme.{u} :=
  qcCoverFamily.precoverage

@[simp]
/--
lemma `presieve₀_mem_qcPrecoverage_iff` / 引理 `presieve₀_mem_qcPrecoverage_iff`

English:
lemma presieve₀_mem_qcPrecoverage_iff
  given: {E : PreZeroHypercover.{w} S}
  proof: by
  rw [← PreZeroHypercover.presieve₀_shrink]; rw [Scheme.qcPrecoverage]; rw [E.shrink.presieve₀_mem_precoverage_iff]
  simp

中文:
引理 presieve₀_mem_qcPrecoverage_iff
  条件: {E : PreZeroHypercover.{w} S}
  证明: by
  rw [← PreZeroHypercover.presieve₀_shrink]; rw [Scheme.qcPrecoverage]; rw [E.shrink.presieve₀_mem_precoverage_iff]
  simp

Depends on / 依赖: E.shrink.presieve, PreZeroHypercover, PreZeroHypercover.presieve, Scheme, Scheme.qcPrecoverage, qcPrecoverage, shrink
-/
lemma presieve₀_mem_qcPrecoverage_iff {E : PreZeroHypercover.{w} S} :
    E.presieve₀ in Scheme.qcPrecoverage S ↔ QuasiCompactCover E := by
  rw [← PreZeroHypercover.presieve₀_shrink]; rw [Scheme.qcPrecoverage]; rw [E.shrink.presieve₀_mem_precoverage_iff]
  simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: qcPrecoverage.HasIsos
  body: .of_preZeroHypercoverFamily fun X Y f hf => by
  rw [qcCoverFamily_property]; rw [Scheme.quasiCompactCover_iff]
  infer_instance

中文:
实例 :
  签名: qcPrecoverage.HasIsos
  定义体: .of_preZeroHypercoverFamily fun X Y f hf => by
  rw [qcCoverFamily_property]; rw [Scheme.quasiCompactCover_iff]
  infer_instance

Depends on / 依赖: Scheme, Scheme.quasiCompactCover_iff, infer_instance, of_preZeroHypercoverFamily, qcCoverFamily_property, quasiCompactCover_iff
-/
instance : qcPrecoverage.HasIsos := .of_preZeroHypercoverFamily fun X Y f hf => by
  rw [qcCoverFamily_property]; rw [Scheme.quasiCompactCover_iff]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: qcPrecoverage.IsStableUnderBaseChange
  body: by
  refine .of_preZeroHypercoverFamily_of_isClosedUnderIsomorphisms ?_ ?_
  · intro X
    exact X.isClosedUnderIsomorphisms_quasiCompactCover
  · intro X Y f E h hE
    simp only [qcCoverFamily_property, Scheme.quasiCompactCover_iff] at hE ⊢
    infer_instance

中文:
实例 :
  签名: qcPrecoverage.IsStableUnderBaseChange
  定义体: by
  refine .of_preZeroHypercoverFamily_of_isClosedUnderIsomorphisms ?_ ?_
  · intro X
    exact X.isClosedUnderIsomorphisms_quasiCompactCover
  · intro X Y f E h hE
    simp only [qcCoverFamily_property, Scheme.quasiCompactCover_iff] at hE ⊢
    infer_instance

Depends on / 依赖: Scheme, Scheme.quasiCompactCover_iff, X.isClosedUnderIsomorphisms_quasiCompactCover, infer_instance, isClosedUnderIsomorphisms_quasiCompactCover, of_preZeroHypercoverFamily_of_isClosedUnderIsomorphisms, qcCoverFamily_property, quasiCompactCover_iff
-/
instance : qcPrecoverage.IsStableUnderBaseChange := by
  refine .of_preZeroHypercoverFamily_of_isClosedUnderIsomorphisms ?_ ?_
  · intro X
    exact X.isClosedUnderIsomorphisms_quasiCompactCover
  · intro X Y f E h hE
    simp only [qcCoverFamily_property, Scheme.quasiCompactCover_iff] at hE ⊢
    infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: qcPrecoverage.IsStableUnderComposition
  body: by
  refine .of_preZeroHypercoverFamily fun {X} E F hE hF => ?_
  simp only [qcCoverFamily_property, Scheme.quasiCompactCover_iff] at hE hF ⊢
  infer_instance

中文:
实例 :
  签名: qcPrecoverage.IsStableUnderComposition
  定义体: by
  refine .of_preZeroHypercoverFamily fun {X} E F hE hF => ?_
  simp only [qcCoverFamily_property, Scheme.quasiCompactCover_iff] at hE hF ⊢
  infer_instance

Depends on / 依赖: Scheme, Scheme.quasiCompactCover_iff, infer_instance, of_preZeroHypercoverFamily, qcCoverFamily_property, quasiCompactCover_iff
-/
instance : qcPrecoverage.IsStableUnderComposition := by
  refine .of_preZeroHypercoverFamily fun {X} E F hE hF => ?_
  simp only [qcCoverFamily_property, Scheme.quasiCompactCover_iff] at hE hF ⊢
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: qcPrecoverage.IsStableUnderSup
  body: by
  refine .of_preZeroHypercoverFamily fun {X} E F hE hF => ?_
  simp only [qcCoverFamily_property, Scheme.quasiCompactCover_iff] at hE hF ⊢
  infer_instance

中文:
实例 :
  签名: qcPrecoverage.IsStableUnderSup
  定义体: by
  refine .of_preZeroHypercoverFamily fun {X} E F hE hF => ?_
  simp only [qcCoverFamily_property, Scheme.quasiCompactCover_iff] at hE hF ⊢
  infer_instance

Depends on / 依赖: Scheme, Scheme.quasiCompactCover_iff, infer_instance, of_preZeroHypercoverFamily, qcCoverFamily_property, quasiCompactCover_iff
-/
instance : qcPrecoverage.IsStableUnderSup := by
  refine .of_preZeroHypercoverFamily fun {X} E F hE hF => ?_
  simp only [qcCoverFamily_property, Scheme.quasiCompactCover_iff] at hE hF ⊢
  infer_instance

/--
lemma `bot_mem_qcPrecoverage` / 引理 `bot_mem_qcPrecoverage`

English:
lemma bot_mem_qcPrecoverage
  given: (X : Scheme.{u}) [IsEmpty X]
  statement: ⊥ in qcPrecoverage X
  proof: by
  rw [← PreZeroHypercover.presieve₀_empty.{0}]; rw [presieve₀_mem_qcPrecoverage_iff]
  infer_instance

中文:
引理 bot_mem_qcPrecoverage
  条件: (X : Scheme.{u}) [IsEmpty X]
  结论: ⊥ in qcPrecoverage X
  证明: by
  rw [← PreZeroHypercover.presieve₀_empty.{0}]; rw [presieve₀_mem_qcPrecoverage_iff]
  infer_instance

Depends on / 依赖: PreZeroHypercover, PreZeroHypercover.presieve, infer_instance
-/
lemma bot_mem_qcPrecoverage (X : Scheme.{u}) [IsEmpty X] : ⊥ in qcPrecoverage X := by
  rw [← PreZeroHypercover.presieve₀_empty.{0}]; rw [presieve₀_mem_qcPrecoverage_iff]
  infer_instance

/--
lemma `precoverage_le_qcPrecoverage_of_isOpenMap` / 引理 `precoverage_le_qcPrecoverage_of_isOpenMap`

English:
lemma precoverage_le_qcPrecoverage_of_isOpenMap
  statement: {P : MorphismProperty Scheme.{u}}
  proof: by
  refine Precoverage.le_of_zeroHypercover fun X E => ?_
  rw [presieve₀_mem_qcPrecoverage_iff]
  exact .of_isOpenMap fun i => hP _ (Scheme.Cover.map_prop E i)

中文:
引理 precoverage_le_qcPrecoverage_of_isOpenMap
  结论: {P : Morphism命题erty Scheme.{u}}
  证明: by
  refine Precoverage.le_of_zeroHypercover fun X E => ?_
  rw [presieve₀_mem_qcPrecoverage_iff]
  exact .of_isOpenMap fun i => hP _ (Scheme.Cover.map_prop E i)

Depends on / 依赖: Precoverage, Precoverage.le_of_zeroHypercover, Scheme, Scheme.Cover.map_prop, le_of_zeroHypercover, map_prop, of_isOpenMap
-/
lemma precoverage_le_qcPrecoverage_of_isOpenMap {P : MorphismProperty Scheme.{u}}
    (hP : P <= fun _ _ f => IsOpenMap f.base) :
    precoverage P <= qcPrecoverage := by
  refine Precoverage.le_of_zeroHypercover fun X E => ?_
  rw [presieve₀_mem_qcPrecoverage_iff]
  exact .of_isOpenMap fun i => hP _ (Scheme.Cover.map_prop E i)

/--
lemma `zariskiPrecoverage_le_qcPrecoverage` / 引理 `zariskiPrecoverage_le_qcPrecoverage`

English:
lemma zariskiPrecoverage_le_qcPrecoverage
  proof: precoverage_le_qcPrecoverage_of_isOpenMap fun _ _ f _ => f.isOpenEmbedding.isOpenMap

中文:
引理 zariskiPrecoverage_le_qcPrecoverage
  证明: precoverage_le_qcPrecoverage_of_isOpenMap fun _ _ f _ => f.isOpenEmbedding.isOpenMap

Depends on / 依赖: f.isOpenEmbedding.isOpenMap, isOpenEmbedding, isOpenMap, precoverage_le_qcPrecoverage_of_isOpenMap
-/
lemma zariskiPrecoverage_le_qcPrecoverage :
    zariskiPrecoverage <= qcPrecoverage :=
  precoverage_le_qcPrecoverage_of_isOpenMap fun _ _ f _ => f.isOpenEmbedding.isOpenMap

/--
lemma `Hom.singleton_mem_qcPrecoverage` / 引理 `Hom.singleton_mem_qcPrecoverage`

English:
lemma Hom.singleton_mem_qcPrecoverage
  statement: {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f]
  proof: by
  let E : Cover.{u} _ _ := f.cover (P := ⊤) trivial
  rw [qcPrecoverage]; rw [PreZeroHypercoverFamily.mem_precoverage_iff]
  refine ⟨(f.cover (P := ⊤) trivial).toPreZeroHypercover, ?_, by simp⟩
  simp only [qcCoverFamily_property, quasiCompactCover_iff]
  infer_instance

中文:
引理 Hom.singleton_mem_qcPrecoverage
  结论: {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f]
  证明: by
  let E : Cover.{u} _ _ := f.cover (P := ⊤) trivial
  rw [qcPrecoverage]; rw [PreZeroHypercoverFamily.mem_precoverage_iff]
  refine ⟨(f.cover (P := ⊤) trivial).toPreZeroHypercover, ?_, by simp⟩
  simp only [qcCoverFamily_property, quasiCompactCover_iff]
  infer_instance

Depends on / 依赖: PreZeroHypercoverFamily, PreZeroHypercoverFamily.mem_precoverage_iff, f.cover, infer_instance, mem_precoverage_iff, qcCoverFamily_property, qcPrecoverage, quasiCompactCover_iff, toPreZeroHypercover
-/
lemma Hom.singleton_mem_qcPrecoverage {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f]
    [QuasiCompact f] : Presieve.singleton f in qcPrecoverage Y := by
  let E : Cover.{u} _ _ := f.cover (P := ⊤) trivial
  rw [qcPrecoverage]; rw [PreZeroHypercoverFamily.mem_precoverage_iff]
  refine ⟨(f.cover (P := ⊤) trivial).toPreZeroHypercover, ?_, by simp⟩
  simp only [qcCoverFamily_property, quasiCompactCover_iff]
  infer_instance

section Property

variable {P : MorphismProperty Scheme.{u}}

/--
Definition of `propQCPrecoverage` / `propQCPrecoverage` 的定义

English:
abbreviation propQCPrecoverage
  signature: (P : MorphismProperty Scheme.{u})
  body: qcPrecoverage ⊓ Scheme.precoverage P

@[grind .]

中文:
缩写 propQCPrecoverage
  签名: (P : Morphism命题erty Scheme.{u})
  定义体: qcPrecoverage ⊓ Scheme.precoverage P

@[grind .]

Depends on / 依赖: Scheme, Scheme.precoverage, precoverage, qcPrecoverage
-/
abbrev propQCPrecoverage (P : MorphismProperty Scheme.{u}) : Precoverage Scheme.{u} :=
  qcPrecoverage ⊓ Scheme.precoverage P

@[grind .]
/--
lemma `propQCPrecoverage_le_precoverage` / 引理 `propQCPrecoverage_le_precoverage`

English:
lemma propQCPrecoverage_le_precoverage
  statement: propQCPrecoverage P <= precoverage P
  proof: inf_le_right

中文:
引理 propQCPrecoverage_le_precoverage
  结论: propQCPrecoverage P <= precoverage P
  证明: inf_le_right

Depends on / 依赖: inf_le_right
-/
lemma propQCPrecoverage_le_precoverage : propQCPrecoverage P <= precoverage P :=
  inf_le_right

/--
lemma `propQCPrecoverage_monotone` / 引理 `propQCPrecoverage_monotone`

English:
lemma propQCPrecoverage_monotone
  statement: Monotone propQCPrecoverage
  proof: by
  intro P Q h
  rw [propQCPrecoverage]; rw [propQCPrecoverage]
  gcongr
  exact precoverage_mono h

中文:
引理 propQCPrecoverage_monotone
  结论: Monotone propQCPrecoverage
  证明: by
  intro P Q h
  rw [propQCPrecoverage]; rw [propQCPrecoverage]
  gcongr
  exact precoverage_mono h

Depends on / 依赖: precoverage_mono, propQCPrecoverage
-/
lemma propQCPrecoverage_monotone : Monotone propQCPrecoverage := by
  intro P Q h
  rw [propQCPrecoverage]; rw [propQCPrecoverage]
  gcongr
  exact precoverage_mono h

/--
lemma `zariskiPrecoverage_le_propQCPrecoverage` / 引理 `zariskiPrecoverage_le_propQCPrecoverage`

English:
lemma zariskiPrecoverage_le_propQCPrecoverage
  given: [P.ContainsIdentities] [IsZariskiLocalAtSource P]
  proof: by
  rw [propQCPrecoverage]; rw [le_inf_iff]
  refine ⟨zariskiPrecoverage_le_qcPrecoverage, precoverage_mono fun X Y f hf => ?_⟩
  apply IsZariskiLocalAtSource.of_isOpenImmersion

中文:
引理 zariskiPrecoverage_le_propQCPrecoverage
  条件: [P.ContainsIdentities] [IsZariskiLocalAtSource P]
  证明: by
  rw [propQCPrecoverage]; rw [le_inf_iff]
  refine ⟨zariskiPrecoverage_le_qcPrecoverage, precoverage_mono fun X Y f hf => ?_⟩
  apply IsZariskiLocalAtSource.of_isOpenImmersion

Depends on / 依赖: IsZariskiLocalAtSource, IsZariskiLocalAtSource.of_isOpenImmersion, le_inf_iff, of_isOpenImmersion, precoverage_mono, propQCPrecoverage, zariskiPrecoverage_le_qcPrecoverage
-/
lemma zariskiPrecoverage_le_propQCPrecoverage [P.ContainsIdentities] [IsZariskiLocalAtSource P] :
    zariskiPrecoverage <= propQCPrecoverage P := by
  rw [propQCPrecoverage]; rw [le_inf_iff]
  refine ⟨zariskiPrecoverage_le_qcPrecoverage, precoverage_mono fun X Y f hf => ?_⟩
  apply IsZariskiLocalAtSource.of_isOpenImmersion

instance {S : Scheme.{u}} (𝒰 : Scheme.Cover (propQCPrecoverage P) S) :
    QuasiCompactCover 𝒰.toPreZeroHypercover := by
  rw [← Scheme.presieve₀_mem_qcPrecoverage_iff]
  exact 𝒰.mem₀.1

/--
lemma `bot_mem_propQCPrecoverage` / 引理 `bot_mem_propQCPrecoverage`

English:
lemma bot_mem_propQCPrecoverage
  given: (X : Scheme.{u}) [IsEmpty X]
  statement: ⊥ in propQCPrecoverage P X
  proof: ⟨bot_mem_qcPrecoverage _, bot_mem_precoverage _ _⟩

中文:
引理 bot_mem_propQCPrecoverage
  条件: (X : Scheme.{u}) [IsEmpty X]
  结论: ⊥ in propQCPrecoverage P X
  证明: ⟨bot_mem_qcPrecoverage _, bot_mem_precoverage _ _⟩

Depends on / 依赖: bot_mem_precoverage, bot_mem_qcPrecoverage
-/
lemma bot_mem_propQCPrecoverage (X : Scheme.{u}) [IsEmpty X] : ⊥ in propQCPrecoverage P X :=
  ⟨bot_mem_qcPrecoverage _, bot_mem_precoverage _ _⟩

/-- Forget being quasi-compact. -/
@[simps toPreZeroHypercover]
/--
Definition of `Cover.forgetQc` / `Cover.forgetQc` 的定义

English:
abbreviation Cover.forgetQc
  signature: {S : Scheme.{u}} (𝒰 : Scheme.Cover (propQCPrecoverage P) S)
  body: 𝒰.toPreZeroHypercover
  mem₀ := 𝒰.mem₀.2

中文:
缩写 Cover.forgetQc
  签名: {S : Scheme.{u}} (𝒰 : Scheme.Cover (propQCPrecoverage P) S)
  定义体: 𝒰.toPreZeroHypercover
  mem₀ := 𝒰.mem₀.2

Depends on / 依赖: toPreZeroHypercover
-/
abbrev Cover.forgetQc {S : Scheme.{u}} (𝒰 : Scheme.Cover (propQCPrecoverage P) S) :
    S.Cover (precoverage P) where
  __ := 𝒰.toPreZeroHypercover
  mem₀ := 𝒰.mem₀.2

instance {S : Scheme.{u}} (𝒰 : Scheme.Cover (propQCPrecoverage P) S) :
    QuasiCompactCover 𝒰.forgetQc.toPreZeroHypercover := by
  dsimp; infer_instance

/-- Construct a cover in the `P`-qc topology from a quasi-compact cover in the `P`-topology. -/
@[simps toPreZeroHypercover]
/--
Definition of `Cover.ofQuasiCompactCover` / `Cover.ofQuasiCompactCover` 的定义

English:
definition Cover.ofQuasiCompactCover
  signature: {S : Scheme.{u}} (𝒰 : Scheme.Cover (precoverage P) S)
  body: 𝒰.toPreZeroHypercover
  mem₀ := ⟨Scheme.presieve₀_mem_qcPrecoverage_iff.mpr ‹_›, 𝒰.mem₀⟩

中文:
定义 Cover.ofQuasiCompactCover
  签名: {S : Scheme.{u}} (𝒰 : Scheme.Cover (precoverage P) S)
  定义体: 𝒰.toPreZeroHypercover
  mem₀ := ⟨Scheme.presieve₀_mem_qcPrecoverage_iff.mpr ‹_›, 𝒰.mem₀⟩

Depends on / 依赖: toPreZeroHypercover
-/
def Cover.ofQuasiCompactCover {S : Scheme.{u}} (𝒰 : Scheme.Cover (precoverage P) S)
    [qc : QuasiCompactCover 𝒰.1] :
    Scheme.Cover (propQCPrecoverage P) S where
  __ := 𝒰.toPreZeroHypercover
  mem₀ := ⟨Scheme.presieve₀_mem_qcPrecoverage_iff.mpr ‹_›, 𝒰.mem₀⟩

/--
Definition of `Cover.qculift` / `Cover.qculift` 的定义

English:
definition Cover.qculift
  signature: {S : Scheme.{u}} (𝒰 : Cover.{w} (precoverage P) S)
  body: 𝒰.ulift.toPreZeroHypercover.sum (QuasiCompactCover.ulift 𝒰.1)
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ⟨.inl x, 𝒰.covers _⟩, fun i => ?_⟩
    induction i <;> exact 𝒰.map_prop _

中文:
定义 Cover.qculift
  签名: {S : Scheme.{u}} (𝒰 : Cover.{w} (precoverage P) S)
  定义体: 𝒰.ulift.toPreZeroHypercover.sum (QuasiCompactCover.ulift 𝒰.1)
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ⟨.inl x, 𝒰.covers _⟩, fun i => ?_⟩
    induction i <;> exact 𝒰.map_prop _

Depends on / 依赖: QuasiCompactCover, QuasiCompactCover.ulift, toPreZeroHypercover, ulift.toPreZeroHypercover.sum
-/
noncomputable def Cover.qculift {S : Scheme.{u}} (𝒰 : Cover.{w} (precoverage P) S)
    [QuasiCompactCover 𝒰.1] : Scheme.Cover.{u} (precoverage P) S where
  __ := 𝒰.ulift.toPreZeroHypercover.sum (QuasiCompactCover.ulift 𝒰.1)
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ⟨.inl x, 𝒰.covers _⟩, fun i => ?_⟩
    induction i <;> exact 𝒰.map_prop _

instance {S : Scheme.{u}} (𝒰 : S.Cover (precoverage P)) [QuasiCompactCover 𝒰.1] :
    QuasiCompactCover (Scheme.Cover.qculift 𝒰).1 :=
  .of_hom (PreZeroHypercover.sumInr _ _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Precoverage.Small.{u} (propQCPrecoverage P)
  body: by
    refine ⟨𝒰.forgetQc.qculift.I₀, Sum.elim 𝒰.forgetQc.idx (QuasiCompactCover.uliftHom _).s₀,
      ⟨?_, ?_⟩⟩
    · rw [Scheme.presieve₀_mem_qcPrecoverage_iff]
      exact .of_hom (𝒱 := QuasiCompactCover.ulift 𝒰.1) ⟨Sum.inr, fun i => 𝟙 _, by cat_disch⟩
    · rw [Scheme.presieve₀_mem_precoverage_i

中文:
实例 :
  签名: Precoverage.Small.{u} (propQCPrecoverage P)
  定义体: by
    refine ⟨𝒰.forgetQc.qculift.I₀, Sum.elim 𝒰.forgetQc.idx (QuasiCompactCover.uliftHom _).s₀,
      ⟨?_, ?_⟩⟩
    · rw [Scheme.presieve₀_mem_qcPrecoverage_iff]
      exact .of_hom (𝒱 := QuasiCompactCover.ulift 𝒰.1) ⟨Sum.inr, fun i => 𝟙 _, by cat_disch⟩
    · rw [Scheme.presieve₀_mem_precoverage_i

Depends on / 依赖: QuasiCompactCover, QuasiCompactCover.ulift, QuasiCompactCover.uliftHom, Scheme, Scheme.presieve, Sum.elim, Sum.inl, Sum.inr, cat_disch, covers, forgetQc, forgetQc.covers, forgetQc.idx, forgetQc.map_prop, forgetQc.qculift.I, map_prop, of_hom, qculift, uliftHom
-/
instance : Precoverage.Small.{u} (propQCPrecoverage P) where
  zeroHypercoverSmall {S} (𝒰 : S.Cover _) := by
    refine ⟨𝒰.forgetQc.qculift.I₀, Sum.elim 𝒰.forgetQc.idx (QuasiCompactCover.uliftHom _).s₀,
      ⟨?_, ?_⟩⟩
    · rw [Scheme.presieve₀_mem_qcPrecoverage_iff]
      exact .of_hom (𝒱 := QuasiCompactCover.ulift 𝒰.1) ⟨Sum.inr, fun i => 𝟙 _, by cat_disch⟩
    · rw [Scheme.presieve₀_mem_precoverage_iff]
      exact ⟨fun x => ⟨Sum.inl x, 𝒰.forgetQc.covers _⟩, fun i => 𝒰.forgetQc.map_prop _⟩

/--
lemma `mem_propQCPrecoverage_iff_exists_quasiCompactCover` / 引理 `mem_propQCPrecoverage_iff_exists_quasiCompactCover`

English:
lemma mem_propQCPrecoverage_iff_exists_quasiCompactCover
  given: {S : Scheme.{u}} {R : Presieve S}
  proof: by
  rw [Precoverage.mem_iff_exists_zeroHypercover]
  refine ⟨fun ⟨𝒰, h⟩ => ⟨𝒰.weaken propQCPrecoverage_le_precoverage, ?_, h⟩,
    fun ⟨𝒰, _, h⟩ => ⟨⟨𝒰.1, ⟨by simpa, 𝒰.mem₀⟩⟩, h⟩⟩
  rw [← Scheme.presieve₀_mem_qcPrecoverage_iff]
  exact 𝒰.mem₀.1

@[grind .]

中文:
引理 mem_propQCPrecoverage_iff_exists_quasiCompactCover
  条件: {S : Scheme.{u}} {R : Presieve S}
  证明: by
  rw [Precoverage.mem_iff_exists_zeroHypercover]
  refine ⟨fun ⟨𝒰, h⟩ => ⟨𝒰.weaken propQCPrecoverage_le_precoverage, ?_, h⟩,
    fun ⟨𝒰, _, h⟩ => ⟨⟨𝒰.1, ⟨by simpa, 𝒰.mem₀⟩⟩, h⟩⟩
  rw [← Scheme.presieve₀_mem_qcPrecoverage_iff]
  exact 𝒰.mem₀.1

@[grind .]

Depends on / 依赖: Precoverage, Precoverage.mem_iff_exists_zeroHypercover, Scheme, Scheme.presieve, mem_iff_exists_zeroHypercover, propQCPrecoverage_le_precoverage, weaken
-/
lemma mem_propQCPrecoverage_iff_exists_quasiCompactCover {S : Scheme.{u}} {R : Presieve S} :
    R in propQCPrecoverage P S ↔ exists (𝒰 : Scheme.Cover.{u + 1} (precoverage P) S),
      QuasiCompactCover 𝒰.toPreZeroHypercover ∧ R = 𝒰.presieve₀ := by
  rw [Precoverage.mem_iff_exists_zeroHypercover]
  refine ⟨fun ⟨𝒰, h⟩ => ⟨𝒰.weaken propQCPrecoverage_le_precoverage, ?_, h⟩,
    fun ⟨𝒰, _, h⟩ => ⟨⟨𝒰.1, ⟨by simpa, 𝒰.mem₀⟩⟩, h⟩⟩
  rw [← Scheme.presieve₀_mem_qcPrecoverage_iff]
  exact 𝒰.mem₀.1

@[grind .]
/--
lemma `Hom.singleton_mem_propQCPrecoverage` / 引理 `Hom.singleton_mem_propQCPrecoverage`

English:
lemma Hom.singleton_mem_propQCPrecoverage
  statement: {X Y : Scheme.{u}} {f : X ⟶ Y} (hf : P f) [Surjective f]
  proof: by
  refine ⟨f.singleton_mem_qcPrecoverage, ?_⟩
  grind [singleton_mem_precoverage_iff]

中文:
引理 Hom.singleton_mem_propQCPrecoverage
  结论: {X Y : Scheme.{u}} {f : X ⟶ Y} (hf : P f) [Surjective f]
  证明: by
  refine ⟨f.singleton_mem_qcPrecoverage, ?_⟩
  grind [singleton_mem_precoverage_iff]

Depends on / 依赖: f.singleton_mem_qcPrecoverage, singleton_mem_precoverage_iff, singleton_mem_qcPrecoverage
-/
lemma Hom.singleton_mem_propQCPrecoverage {X Y : Scheme.{u}} {f : X ⟶ Y} (hf : P f) [Surjective f]
    [QuasiCompact f] : Presieve.singleton f in propQCPrecoverage P Y := by
  refine ⟨f.singleton_mem_qcPrecoverage, ?_⟩
  grind [singleton_mem_precoverage_iff]

/--
Definition of `propQCTopology` / `propQCTopology` 的定义

English:
abbreviation propQCTopology
  signature: (P : MorphismProperty Scheme.{u})
  body: (propQCPrecoverage P).toGrothendieck

中文:
缩写 propQCTopology
  签名: (P : Morphism命题erty Scheme.{u})
  定义体: (propQCPrecoverage P).toGrothendieck

Depends on / 依赖: propQCPrecoverage, toGrothendieck
-/
abbrev propQCTopology (P : MorphismProperty Scheme.{u}) : GrothendieckTopology Scheme.{u} :=
  (propQCPrecoverage P).toGrothendieck

/--
lemma `bot_mem_propQCTopology` / 引理 `bot_mem_propQCTopology`

English:
lemma bot_mem_propQCTopology
  given: (X : Scheme.{u}) [IsEmpty X]
  statement: ⊥ in propQCTopology P X
  proof: by
  rw [← Sieve.generate_bot]
  exact Precoverage.generate_mem_toGrothendieck (bot_mem_propQCPrecoverage X)

@[grind .]

中文:
引理 bot_mem_propQCTopology
  条件: (X : Scheme.{u}) [IsEmpty X]
  结论: ⊥ in propQCTopology P X
  证明: by
  rw [← Sieve.generate_bot]
  exact Precoverage.generate_mem_toGrothendieck (bot_mem_propQCPrecoverage X)

@[grind .]

Depends on / 依赖: Precoverage, Precoverage.generate_mem_toGrothendieck, Sieve.generate_bot, bot_mem_propQCPrecoverage, generate_bot, generate_mem_toGrothendieck
-/
lemma bot_mem_propQCTopology (X : Scheme.{u}) [IsEmpty X] : ⊥ in propQCTopology P X := by
  rw [← Sieve.generate_bot]
  exact Precoverage.generate_mem_toGrothendieck (bot_mem_propQCPrecoverage X)

@[grind .]
/--
lemma `Hom.generate_singleton_mem_propQCTopology` / 引理 `Hom.generate_singleton_mem_propQCTopology`

English:
lemma Hom.generate_singleton_mem_propQCTopology
  statement: {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : P f)
  proof: by
  apply Precoverage.generate_mem_toGrothendieck
  exact f.singleton_mem_propQCPrecoverage hf

@[simp, grind .]

中文:
引理 Hom.generate_singleton_mem_propQCTopology
  结论: {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : P f)
  证明: by
  apply Precoverage.generate_mem_toGrothendieck
  exact f.singleton_mem_propQCPrecoverage hf

@[simp, grind .]

Depends on / 依赖: Precoverage, Precoverage.generate_mem_toGrothendieck, f.singleton_mem_propQCPrecoverage, generate_mem_toGrothendieck, singleton_mem_propQCPrecoverage
-/
lemma Hom.generate_singleton_mem_propQCTopology {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : P f)
    [Surjective f] [QuasiCompact f] :
    .generate (.singleton f) in propQCTopology P Y := by
  apply Precoverage.generate_mem_toGrothendieck
  exact f.singleton_mem_propQCPrecoverage hf

@[simp, grind .]
/--
lemma `Cover.mem_propQCTopology` / 引理 `Cover.mem_propQCTopology`

English:
lemma Cover.mem_propQCTopology
  statement: {S : Scheme.{u}} (𝒰 : Cover.{u} (precoverage P) S)
  proof: by
  refine Precoverage.generate_mem_toGrothendieck ⟨?_, 𝒰.mem₀⟩
  rwa [presieve₀_mem_qcPrecoverage_iff]

中文:
引理 Cover.mem_propQCTopology
  结论: {S : Scheme.{u}} (𝒰 : Cover.{u} (precoverage P) S)
  证明: by
  refine Precoverage.generate_mem_toGrothendieck ⟨?_, 𝒰.mem₀⟩
  rwa [presieve₀_mem_qcPrecoverage_iff]

Depends on / 依赖: Precoverage, Precoverage.generate_mem_toGrothendieck, generate_mem_toGrothendieck
-/
lemma Cover.mem_propQCTopology {S : Scheme.{u}} (𝒰 : Cover.{u} (precoverage P) S)
    [QuasiCompactCover 𝒰.1] :
    .ofArrows 𝒰.X 𝒰.f in propQCTopology P S := by
  refine Precoverage.generate_mem_toGrothendieck ⟨?_, 𝒰.mem₀⟩
  rwa [presieve₀_mem_qcPrecoverage_iff]

/--
lemma `zariskiTopology_le_propQCTopology` / 引理 `zariskiTopology_le_propQCTopology`

English:
lemma zariskiTopology_le_propQCTopology
  given: [P.IsMultiplicative] [IsZariskiLocalAtSource P]
  proof: Precoverage.toGrothendieck_mono zariskiPrecoverage_le_propQCPrecoverage

中文:
引理 zariskiTopology_le_propQCTopology
  条件: [P.IsMultiplicative] [IsZariskiLocalAtSource P]
  证明: Precoverage.toGrothendieck_mono zariskiPrecoverage_le_propQCPrecoverage

Depends on / 依赖: Precoverage, Precoverage.toGrothendieck_mono, toGrothendieck_mono, zariskiPrecoverage_le_propQCPrecoverage
-/
lemma zariskiTopology_le_propQCTopology [P.IsMultiplicative] [IsZariskiLocalAtSource P] :
    zariskiTopology <= propQCTopology P :=
  Precoverage.toGrothendieck_mono zariskiPrecoverage_le_propQCPrecoverage

end Property

end AlgebraicGeometry.Scheme
