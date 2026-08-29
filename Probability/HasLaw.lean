/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Probability.Density
public import Mathlib.Probability.Moments.Variance

/-!
# Law of a random variable

We introduce a predicate `HasLaw X μ P` stating that the random variable `X` has law `μ` under
the measure `P`. This is expressed as `P.map X = μ`. We also require `X` to be `P`-almost-everywhere
measurable. Indeed, if `X` is not almost-everywhere measurable then `P.map X` is defined to be `0`,
so that `HasLaw X 0 P` would be true. The measurability hypothesis ensures nice interactions with
operations on the codomain of `X`.
See for instance `HasLaw.comp`, `IndepFun.hasLaw_mul` and `IndepFun.hasLaw_add`.
-/

public section

open MeasureTheory Measure

open scoped ENNReal

namespace ProbabilityTheory

variable {Ω 𝓧 : Type*} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X Y : Ω -> 𝓧}
  {μ : Measure 𝓧} {P : Measure Ω}

variable (X μ) in
/-- The predicate `HasLaw X μ P` registers the fact that the random variable `X` has law `μ` under
the measure `P`, in other words that `P.map X = μ`. We also require `X` to be `AEMeasurable`,
to allow for nice interactions with operations on the codomain of `X`. See for instance
`HasLaw.comp`, `IndepFun.hasLaw_mul` and `IndepFun.hasLaw_add`. -/
@[fun_prop]
/--
Definition of `HasLaw` / `HasLaw` 的定义

English:
structure HasLaw
  parameters: (P : Measure Ω := by volume_tac)
  axioms and operations (2):
    - aemeasurable : AEMeasurable X P  [default: by fun_prop]
    - map_eq : P.map X = μ

中文:
结构 HasLaw
  参数: (P : Measure Ω := by volume_tac)
  公理与运算 (2 个):
    - aemeasurable : AEMeasurable X P  [默认: by fun_prop]
    - map_eq : P.map X = μ

Depends on / 依赖: AEMeasurable, P.map, aemeasurable, fun_prop, map_eq, protected, volume_tac
-/
structure HasLaw (P : Measure Ω := by volume_tac) : Prop where
  protected aemeasurable : AEMeasurable X P := by fun_prop
  protected map_eq : P.map X = μ

attribute [fun_prop] HasLaw.aemeasurable

/--
lemma `HasLaw.measure_eq` / 引理 `HasLaw.measure_eq`

English:
lemma HasLaw.measure_eq
  given: (hX : HasLaw X μ P) {p : 𝓧 -> Prop} (hp : MeasurableSet {x | p x})
  proof: by
  rw [← hX.map_eq]; rw [map_apply_of_aemeasurable hX.aemeasurable hp]
  simp

中文:
引理 HasLaw.measure_eq
  条件: (hX : HasLaw X μ P) {p : 𝓧 -> 命题} (hp : MeasurableSet {x | p x})
  证明: by
  rw [← hX.map_eq]; rw [map_apply_of_aemeasurable hX.aemeasurable hp]
  simp

Depends on / 依赖: aemeasurable, hX.aemeasurable, hX.map_eq, map_apply_of_aemeasurable, map_eq
-/
lemma HasLaw.measure_eq (hX : HasLaw X μ P) {p : 𝓧 -> Prop} (hp : MeasurableSet {x | p x}) :
    P {ω | p (X ω)} = μ {x | p x} := by
  rw [← hX.map_eq]; rw [map_apply_of_aemeasurable hX.aemeasurable hp]
  simp

/--
lemma `HasLaw.measureReal_eq` / 引理 `HasLaw.measureReal_eq`

English:
lemma HasLaw.measureReal_eq
  given: (hX : HasLaw X μ P) {p : 𝓧 -> Prop} (hp : MeasurableSet {x | p x})
  proof: by
  rw [← hX.map_eq]; rw [map_measureReal_apply_of_aemeasurable hX.aemeasurable hp]
  simp

中文:
引理 HasLaw.measureReal_eq
  条件: (hX : HasLaw X μ P) {p : 𝓧 -> 命题} (hp : MeasurableSet {x | p x})
  证明: by
  rw [← hX.map_eq]; rw [map_measureReal_apply_of_aemeasurable hX.aemeasurable hp]
  simp

Depends on / 依赖: aemeasurable, hX.aemeasurable, hX.map_eq, map_eq, map_measureReal_apply_of_aemeasurable
-/
lemma HasLaw.measureReal_eq (hX : HasLaw X μ P) {p : 𝓧 -> Prop} (hp : MeasurableSet {x | p x}) :
    P.real {ω | p (X ω)} = μ.real {x | p x} := by
  rw [← hX.map_eq]; rw [map_measureReal_apply_of_aemeasurable hX.aemeasurable hp]
  simp

/--
lemma `HasLaw.comp_of_hasLaw_comp` / 引理 `HasLaw.comp_of_hasLaw_comp`

English:
lemma HasLaw.comp_of_hasLaw_comp
  statement: {Ω' 𝓨 : Type*} {m' : MeasurableSpace Ω'} {m𝓨 : MeasurableSpace 𝓨}
  proof: (hY.map_eq ▸ hf).comp_aemeasurable hY.aemeasurable
  map_eq := by
    rw [← Function.comp_def]; rw [← AEMeasurable.map_map_of_aemeasurable (hY.map_eq ▸ hf) hY.aemeasurable]; rw [hY.map_eq]; rw [← hX.map_eq]; rw [AEMeasurable.map_map_of_aemeasurable (hX.map_eq ▸ hf) hX.aemeasurable]; rw [Function.com

中文:
引理 HasLaw.comp_of_hasLaw_comp
  结论: {Ω' 𝓨 : 类型} {m' : MeasurableSpace Ω'} {m𝓨 : MeasurableSpace 𝓨}
  证明: (hY.map_eq ▸ hf).comp_aemeasurable hY.aemeasurable
  map_eq := by
    rw [← Function.comp_def]; rw [← AEMeasurable.map_map_of_aemeasurable (hY.map_eq ▸ hf) hY.aemeasurable]; rw [hY.map_eq]; rw [← hX.map_eq]; rw [AEMeasurable.map_map_of_aemeasurable (hX.map_eq ▸ hf) hX.aemeasurable]; rw [Function.com

Depends on / 依赖: aemeasurable, comp_aemeasurable, hY.aemeasurable, hY.map_eq, map_eq
-/
lemma HasLaw.comp_of_hasLaw_comp {Ω' 𝓨 : Type*} {m' : MeasurableSpace Ω'} {m𝓨 : MeasurableSpace 𝓨}
    {P' : Measure Ω'} {ν : Measure 𝓨} {f : 𝓧 -> 𝓨} {Y : Ω' -> 𝓧} (hf : AEMeasurable f μ)
    (hX : HasLaw X μ P) (hY : HasLaw Y μ P') (h : HasLaw (fun ω => f (X ω)) ν P) :
    HasLaw (fun ω => f (Y ω)) ν P' where
  aemeasurable := (hY.map_eq ▸ hf).comp_aemeasurable hY.aemeasurable
  map_eq := by
    rw [← Function.comp_def]; rw [← AEMeasurable.map_map_of_aemeasurable (hY.map_eq ▸ hf) hY.aemeasurable]; rw [hY.map_eq]; rw [← hX.map_eq]; rw [AEMeasurable.map_map_of_aemeasurable (hX.map_eq ▸ hf) hX.aemeasurable]; rw [Function.comp_def]; rw [h.map_eq]

/--
lemma `HasLaw.congr` / 引理 `HasLaw.congr`

English:
lemma HasLaw.congr
  given: (hX : HasLaw X μ P) (hY : Y =ᵐ[P] X)
  statement: HasLaw Y μ P where
  proof: hX.aemeasurable.congr hY.symm
  map_eq := by rw [map_congr hY, hX.map_eq]

中文:
引理 HasLaw.congr
  条件: (hX : HasLaw X μ P) (hY : Y =ᵐ[P] X)
  结论: HasLaw Y μ P where
  证明: hX.aemeasurable.congr hY.symm
  map_eq := by rw [map_congr hY, hX.map_eq]

Depends on / 依赖: aemeasurable, hX.aemeasurable.congr, hY.symm
-/
lemma HasLaw.congr (hX : HasLaw X μ P) (hY : Y =ᵐ[P] X) : HasLaw Y μ P where
  aemeasurable := hX.aemeasurable.congr hY.symm
  map_eq := by rw [map_congr hY, hX.map_eq]

/--
lemma `hasLaw_congr` / 引理 `hasLaw_congr`

English:
lemma hasLaw_congr
  given: (hXY : X =ᵐ[P] Y)
  statement: HasLaw X μ P ↔ HasLaw Y μ P where
  proof: h.congr hXY.symm
  mpr h := h.congr hXY

中文:
引理 hasLaw_congr
  条件: (hXY : X =ᵐ[P] Y)
  结论: HasLaw X μ P ↔ HasLaw Y μ P where
  证明: h.congr hXY.symm
  mpr h := h.congr hXY

Depends on / 依赖: h.congr, hXY.symm
-/
lemma hasLaw_congr (hXY : X =ᵐ[P] Y) : HasLaw X μ P ↔ HasLaw Y μ P where
  mp h := h.congr hXY.symm
  mpr h := h.congr hXY

/--
lemma `_root_.MeasureTheory.MeasurePreserving.hasLaw` / 引理 `_root_.MeasureTheory.MeasurePreserving.hasLaw`

English:
lemma _root_.MeasureTheory.MeasurePreserving.hasLaw
  given: (h : MeasurePreserving X P μ)
  proof: h.measurable.aemeasurable
  map_eq := h.map_eq

中文:
引理 _root_.MeasureTheory.MeasurePreserving.hasLaw
  条件: (h : MeasurePreserving X P μ)
  证明: h.measurable.aemeasurable
  map_eq := h.map_eq

Depends on / 依赖: aemeasurable, h.measurable.aemeasurable, measurable
-/
lemma _root_.MeasureTheory.MeasurePreserving.hasLaw (h : MeasurePreserving X P μ) :
    HasLaw X μ P where
  aemeasurable := h.measurable.aemeasurable
  map_eq := h.map_eq

/--
lemma `HasLaw.measurePreserving` / 引理 `HasLaw.measurePreserving`

English:
lemma HasLaw.measurePreserving
  given: (h₁ : HasLaw X μ P) (h₂ : Measurable X)
  proof: h₂
  map_eq := h₁.map_eq

中文:
引理 HasLaw.measurePreserving
  条件: (h₁ : HasLaw X μ P) (h₂ : Measurable X)
  证明: h₂
  map_eq := h₁.map_eq
-/
lemma HasLaw.measurePreserving (h₁ : HasLaw X μ P) (h₂ : Measurable X) :
    MeasurePreserving X P μ where
  measurable := h₂
  map_eq := h₁.map_eq

/--
lemma `HasLaw.id` / 引理 `HasLaw.id`

English:
lemma HasLaw.id
  statement: HasLaw id μ μ where
  proof: map_id

中文:
引理 HasLaw.id
  结论: HasLaw id μ μ where
  证明: map_id
-/
protected lemma HasLaw.id : HasLaw id μ μ where
  map_eq := map_id

/--
lemma `HasLaw.ae_iff` / 引理 `HasLaw.ae_iff`

English:
lemma HasLaw.ae_iff
  given: (hX : HasLaw X μ P) {p : 𝓧 -> Prop} (hp : Measurable p)
  proof: by
  rw [← hX.map_eq]; rw [ae_map_iff hX.aemeasurable (measurableSet_setOfPred.2 hp)]

中文:
引理 HasLaw.ae_iff
  条件: (hX : HasLaw X μ P) {p : 𝓧 -> 命题} (hp : Measurable p)
  证明: by
  rw [← hX.map_eq]; rw [ae_map_iff hX.aemeasurable (measurableSet_setOfPred.2 hp)]
-/
protected lemma HasLaw.ae_iff (hX : HasLaw X μ P) {p : 𝓧 -> Prop} (hp : Measurable p) :
    (forallᵐ ω ∂P, p (X ω)) ↔ forallᵐ x ∂μ, p x := by
  rw [← hX.map_eq]; rw [ae_map_iff hX.aemeasurable (measurableSet_setOfPred.2 hp)]

/--
theorem `HasLaw.isFiniteMeasure_iff` / 定理 `HasLaw.isFiniteMeasure_iff`

English:
theorem HasLaw.isFiniteMeasure_iff
  given: (hX : HasLaw X μ P)
  proof: by
  rw [← hX.map_eq]; rw [isFiniteMeasure_map_iff hX.aemeasurable]

中文:
定理 HasLaw.isFiniteMeasure_iff
  条件: (hX : HasLaw X μ P)
  证明: by
  rw [← hX.map_eq]; rw [isFiniteMeasure_map_iff hX.aemeasurable]
-/
protected theorem HasLaw.isFiniteMeasure_iff (hX : HasLaw X μ P) :
    IsFiniteMeasure P ↔ IsFiniteMeasure μ := by
  rw [← hX.map_eq]; rw [isFiniteMeasure_map_iff hX.aemeasurable]

/--
theorem `HasLaw.isProbabilityMeasure_iff` / 定理 `HasLaw.isProbabilityMeasure_iff`

English:
theorem HasLaw.isProbabilityMeasure_iff
  given: (hX : HasLaw X μ P)
  proof: by
  rw [← hX.map_eq]; rw [isProbabilityMeasure_map_iff hX.aemeasurable]

中文:
定理 HasLaw.isProbabilityMeasure_iff
  条件: (hX : HasLaw X μ P)
  证明: by
  rw [← hX.map_eq]; rw [isProbabilityMeasure_map_iff hX.aemeasurable]
-/
protected theorem HasLaw.isProbabilityMeasure_iff (hX : HasLaw X μ P) :
    IsProbabilityMeasure P ↔ IsProbabilityMeasure μ := by
  rw [← hX.map_eq]; rw [isProbabilityMeasure_map_iff hX.aemeasurable]

/--
lemma `HasLaw.isFiniteMeasure` / 引理 `HasLaw.isFiniteMeasure`

English:
lemma HasLaw.isFiniteMeasure
  given: [IsFiniteMeasure μ] (hX : HasLaw X μ P)
  statement: IsFiniteMeasure P
  proof: hX.isFiniteMeasure_iff.2 ‹_›

中文:
引理 HasLaw.isFiniteMeasure
  条件: [IsFiniteMeasure μ] (hX : HasLaw X μ P)
  结论: IsFiniteMeasure P
  证明: hX.isFiniteMeasure_iff.2 ‹_›

Depends on / 依赖: hX.isFiniteMeasure_iff, isFiniteMeasure_iff
-/
lemma HasLaw.isFiniteMeasure [IsFiniteMeasure μ] (hX : HasLaw X μ P) : IsFiniteMeasure P :=
  hX.isFiniteMeasure_iff.2 ‹_›

/--
lemma `HasLaw.isProbabilityMeasure` / 引理 `HasLaw.isProbabilityMeasure`

English:
lemma HasLaw.isProbabilityMeasure
  given: [IsProbabilityMeasure μ] (hX : HasLaw X μ P)
  proof: hX.isProbabilityMeasure_iff.2 ‹_›

@[fun_prop]

中文:
引理 HasLaw.isProbabilityMeasure
  条件: [IsProbabilityMeasure μ] (hX : HasLaw X μ P)
  证明: hX.isProbabilityMeasure_iff.2 ‹_›

@[fun_prop]

Depends on / 依赖: hX.isProbabilityMeasure_iff, isProbabilityMeasure_iff
-/
lemma HasLaw.isProbabilityMeasure [IsProbabilityMeasure μ] (hX : HasLaw X μ P) :
    IsProbabilityMeasure P := hX.isProbabilityMeasure_iff.2 ‹_›

@[fun_prop]
/--
lemma `HasLaw.comp` / 引理 `HasLaw.comp`

English:
lemma HasLaw.comp
  statement: {𝓨 : Type*} {m𝓨 : MeasurableSpace 𝓨} {ν : Measure 𝓨} {Y : 𝓧 -> 𝓨}
  proof: (hX.map_eq ▸ hY.aemeasurable).comp_aemeasurable hX.aemeasurable
  map_eq := by
    rw [← AEMeasurable.map_map_of_aemeasurable _ hX.aemeasurable]; rw [hX.map_eq]; rw [hY.map_eq]
    rw [hX.map_eq]; exact hY.aemeasurable

@[fun_prop]

中文:
引理 HasLaw.comp
  结论: {𝓨 : 类型} {m𝓨 : MeasurableSpace 𝓨} {ν : Measure 𝓨} {Y : 𝓧 -> 𝓨}
  证明: (hX.map_eq ▸ hY.aemeasurable).comp_aemeasurable hX.aemeasurable
  map_eq := by
    rw [← AEMeasurable.map_map_of_aemeasurable _ hX.aemeasurable]; rw [hX.map_eq]; rw [hY.map_eq]
    rw [hX.map_eq]; exact hY.aemeasurable

@[fun_prop]

Depends on / 依赖: aemeasurable, comp_aemeasurable, hX.aemeasurable, hX.map_eq, hY.aemeasurable, map_eq
-/
lemma HasLaw.comp {𝓨 : Type*} {m𝓨 : MeasurableSpace 𝓨} {ν : Measure 𝓨} {Y : 𝓧 -> 𝓨}
    (hY : HasLaw Y ν μ) (hX : HasLaw X μ P) : HasLaw (Y ∘ X) ν P where
  aemeasurable := (hX.map_eq ▸ hY.aemeasurable).comp_aemeasurable hX.aemeasurable
  map_eq := by
    rw [← AEMeasurable.map_map_of_aemeasurable _ hX.aemeasurable]; rw [hX.map_eq]; rw [hY.map_eq]
    rw [hX.map_eq]; exact hY.aemeasurable

@[fun_prop]
/--
lemma `HasLaw.fun_comp` / 引理 `HasLaw.fun_comp`

English:
lemma HasLaw.fun_comp
  statement: {𝓨 : Type*} {m𝓨 : MeasurableSpace 𝓨} {ν : Measure 𝓨} {Y : 𝓧 -> 𝓨}
  proof: hY.comp hX

中文:
引理 HasLaw.fun_comp
  结论: {𝓨 : 类型} {m𝓨 : MeasurableSpace 𝓨} {ν : Measure 𝓨} {Y : 𝓧 -> 𝓨}
  证明: hY.comp hX

Depends on / 依赖: hY.comp
-/
lemma HasLaw.fun_comp {𝓨 : Type*} {m𝓨 : MeasurableSpace 𝓨} {ν : Measure 𝓨} {Y : 𝓧 -> 𝓨}
    (hY : HasLaw Y ν μ) (hX : HasLaw X μ P) : HasLaw (fun ω => Y (X ω)) ν P :=
  hY.comp hX

/--
lemma `_root_.MeasureTheory.MeasurePreserving.comp_hasLaw` / 引理 `_root_.MeasureTheory.MeasurePreserving.comp_hasLaw`

English:
lemma _root_.MeasureTheory.MeasurePreserving.comp_hasLaw
  statement: {𝓨 : Type*} {m𝓨 : MeasurableSpace 𝓨}
  proof: hY.hasLaw.comp hX

中文:
引理 _root_.MeasureTheory.MeasurePreserving.comp_hasLaw
  结论: {𝓨 : 类型} {m𝓨 : MeasurableSpace 𝓨}
  证明: hY.hasLaw.comp hX

Depends on / 依赖: hY.hasLaw.comp, hasLaw
-/
lemma _root_.MeasureTheory.MeasurePreserving.comp_hasLaw {𝓨 : Type*} {m𝓨 : MeasurableSpace 𝓨}
    {ν : Measure 𝓨} {Y : 𝓧 -> 𝓨} (hY : MeasurePreserving Y μ ν) (hX : HasLaw X μ P) :
    HasLaw (Y ∘ X) ν P :=
  hY.hasLaw.comp hX

/--
lemma `_root_.MeasureTheory.MeasurePreserving.fun_comp_hasLaw` / 引理 `_root_.MeasureTheory.MeasurePreserving.fun_comp_hasLaw`

English:
lemma _root_.MeasureTheory.MeasurePreserving.fun_comp_hasLaw
  statement: {𝓨 : Type*} {m𝓨 : MeasurableSpace 𝓨}
  proof: hY.comp_hasLaw hX

@[to_additive]

中文:
引理 _root_.MeasureTheory.MeasurePreserving.fun_comp_hasLaw
  结论: {𝓨 : 类型} {m𝓨 : MeasurableSpace 𝓨}
  证明: hY.comp_hasLaw hX

@[to_additive]

Depends on / 依赖: comp_hasLaw, hY.comp_hasLaw
-/
lemma _root_.MeasureTheory.MeasurePreserving.fun_comp_hasLaw {𝓨 : Type*} {m𝓨 : MeasurableSpace 𝓨}
    {ν : Measure 𝓨} {Y : 𝓧 -> 𝓨} (hY : MeasurePreserving Y μ ν) (hX : HasLaw X μ P) :
    HasLaw (fun ω => Y (X ω)) ν P :=
  hY.comp_hasLaw hX

@[to_additive]
/--
lemma `IndepFun.hasLaw_mul` / 引理 `IndepFun.hasLaw_mul`

English:
lemma IndepFun.hasLaw_mul
  statement: {M : Type*} [Monoid M] {mM : MeasurableSpace M} [MeasurableMul₂ M]
  proof: by
    rw [hXY.map_mul_eq_map_mconv_map₀' hX.aemeasurable hY.aemeasurable]; rw [hX.map_eq]; rw [hY.map_eq]
    · rwa [hX.map_eq]
    · rwa [hY.map_eq]

@[to_additive]

中文:
引理 IndepFun.hasLaw_mul
  结论: {M : 类型} [Monoid M] {mM : MeasurableSpace M} [MeasurableMul₂ M]
  证明: by
    rw [hXY.map_mul_eq_map_mconv_map₀' hX.aemeasurable hY.aemeasurable]; rw [hX.map_eq]; rw [hY.map_eq]
    · rwa [hX.map_eq]
    · rwa [hY.map_eq]

@[to_additive]

Depends on / 依赖: aemeasurable, hX.aemeasurable, hX.map_eq, hXY.map_mul_eq_map_mconv_map, hY.aemeasurable, hY.map_eq, map_eq
-/
lemma IndepFun.hasLaw_mul {M : Type*} [Monoid M] {mM : MeasurableSpace M} [MeasurableMul₂ M]
    {μ ν : Measure M} [SigmaFinite μ] [SigmaFinite ν] {X Y : Ω -> M}
    (hX : HasLaw X μ P) (hY : HasLaw Y ν P) (hXY : X ⟂ᵢ[P] Y) :
    HasLaw (X * Y) (μ ∗ₘ ν) P where
  map_eq := by
    rw [hXY.map_mul_eq_map_mconv_map₀' hX.aemeasurable hY.aemeasurable]; rw [hX.map_eq]; rw [hY.map_eq]
    · rwa [hX.map_eq]
    · rwa [hY.map_eq]

@[to_additive]
/--
lemma `IndepFun.hasLaw_fun_mul` / 引理 `IndepFun.hasLaw_fun_mul`

English:
lemma IndepFun.hasLaw_fun_mul
  statement: {M : Type*} [Monoid M] {mM : MeasurableSpace M} [MeasurableMul₂ M]
  proof: hXY.hasLaw_mul hX hY

中文:
引理 IndepFun.hasLaw_fun_mul
  结论: {M : 类型} [Monoid M] {mM : MeasurableSpace M} [MeasurableMul₂ M]
  证明: hXY.hasLaw_mul hX hY

Depends on / 依赖: hXY.hasLaw_mul, hasLaw_mul
-/
lemma IndepFun.hasLaw_fun_mul {M : Type*} [Monoid M] {mM : MeasurableSpace M} [MeasurableMul₂ M]
    {μ ν : Measure M} [SigmaFinite μ] [SigmaFinite ν] {X Y : Ω -> M}
    (hX : HasLaw X μ P) (hY : HasLaw Y ν P) (hXY : X ⟂ᵢ[P] Y) :
    HasLaw (fun ω => X ω * Y ω) (μ ∗ₘ ν) P := hXY.hasLaw_mul hX hY

/--
lemma `HasLaw.integral_comp` / 引理 `HasLaw.integral_comp`

English:
lemma HasLaw.integral_comp
  statement: {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  proof: by
  rw [← hX.map_eq]; rw [integral_map hX.aemeasurable]; rw [Function.comp_def]
  rwa [hX.map_eq]

中文:
引理 HasLaw.integral_comp
  结论: {E : 类型} [NormedAddCommGroup E] [NormedSpace 实数 E]
  证明: by
  rw [← hX.map_eq]; rw [integral_map hX.aemeasurable]; rw [Function.comp_def]
  rwa [hX.map_eq]

Depends on / 依赖: Function, Function.comp_def, aemeasurable, comp_def, hX.aemeasurable, hX.map_eq, integral_map, map_eq
-/
lemma HasLaw.integral_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {X : Ω -> 𝓧} (hX : HasLaw X μ P) {f : 𝓧 -> E} (hf : AEStronglyMeasurable f μ) :
    P[f ∘ X] = ∫ x, f x ∂μ := by
  rw [← hX.map_eq]; rw [integral_map hX.aemeasurable]; rw [Function.comp_def]
  rwa [hX.map_eq]

/--
lemma `HasLaw.lintegral_comp` / 引理 `HasLaw.lintegral_comp`

English:
lemma HasLaw.lintegral_comp
  statement: {X : Ω -> 𝓧} (hX : HasLaw X μ P) {f : 𝓧 -> Real>=0∞}
  proof: by
  rw [← hX.map_eq]; rw [lintegral_map' _ hX.aemeasurable]
  rwa [hX.map_eq]

中文:
引理 HasLaw.lintegral_comp
  结论: {X : Ω -> 𝓧} (hX : HasLaw X μ P) {f : 𝓧 -> 实数>=0∞}
  证明: by
  rw [← hX.map_eq]; rw [lintegral_map' _ hX.aemeasurable]
  rwa [hX.map_eq]

Depends on / 依赖: aemeasurable, hX.aemeasurable, hX.map_eq, lintegral_map, map_eq
-/
lemma HasLaw.lintegral_comp {X : Ω -> 𝓧} (hX : HasLaw X μ P) {f : 𝓧 -> Real>=0∞}
    (hf : AEMeasurable f μ) : ∫⁻ ω, f (X ω) ∂P = ∫⁻ x, f x ∂μ := by
  rw [← hX.map_eq]; rw [lintegral_map' _ hX.aemeasurable]
  rwa [hX.map_eq]

/--
lemma `HasLaw.integral_eq` / 引理 `HasLaw.integral_eq`

English:
lemma HasLaw.integral_eq
  statement: {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  proof: by
  rw [← Function.id_comp X]; rw [hX.integral_comp aestronglyMeasurable_id]
  simp

中文:
引理 HasLaw.integral_eq
  结论: {E : 类型} [NormedAddCommGroup E] [NormedSpace 实数 E]
  证明: by
  rw [← Function.id_comp X]; rw [hX.integral_comp aestronglyMeasurable_id]
  simp

Depends on / 依赖: Function, Function.id_comp, aestronglyMeasurable_id, hX.integral_comp, id_comp, integral_comp
-/
lemma HasLaw.integral_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [SecondCountableTopology E] {mE : MeasurableSpace E} [OpensMeasurableSpace E] {μ : Measure E}
    {X : Ω -> E} (hX : HasLaw X μ P) : P[X] = ∫ x, x ∂μ := by
  rw [← Function.id_comp X]; rw [hX.integral_comp aestronglyMeasurable_id]
  simp

/--
lemma `HasLaw.covariance_comp` / 引理 `HasLaw.covariance_comp`

English:
lemma HasLaw.covariance_comp
  statement: (hX : HasLaw X μ P) {f g : 𝓧 -> Real}
  proof: by
  rw [← hX.map_eq]; rw [covariance_map]
  · rw [hX.map_eq]
    exact hf.aestronglyMeasurable
  · rw [hX.map_eq]
    exact hg.aestronglyMeasurable
  · exact hX.aemeasurable

中文:
引理 HasLaw.covariance_comp
  结论: (hX : HasLaw X μ P) {f g : 𝓧 -> 实数}
  证明: by
  rw [← hX.map_eq]; rw [covariance_map]
  · rw [hX.map_eq]
    exact hf.aestronglyMeasurable
  · rw [hX.map_eq]
    exact hg.aestronglyMeasurable
  · exact hX.aemeasurable

Depends on / 依赖: aemeasurable, aestronglyMeasurable, covariance_map, hX.aemeasurable, hX.map_eq, hf.aestronglyMeasurable, hg.aestronglyMeasurable, map_eq
-/
lemma HasLaw.covariance_comp (hX : HasLaw X μ P) {f g : 𝓧 -> Real}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    cov[f ∘ X, g ∘ X; P] = cov[f, g; μ] := by
  rw [← hX.map_eq]; rw [covariance_map]
  · rw [hX.map_eq]
    exact hf.aestronglyMeasurable
  · rw [hX.map_eq]
    exact hg.aestronglyMeasurable
  · exact hX.aemeasurable

/--
lemma `HasLaw.covariance_fun_comp` / 引理 `HasLaw.covariance_fun_comp`

English:
lemma HasLaw.covariance_fun_comp
  statement: (hX : HasLaw X μ P) {f g : 𝓧 -> Real}
  proof: hX.covariance_comp hf hg

中文:
引理 HasLaw.covariance_fun_comp
  结论: (hX : HasLaw X μ P) {f g : 𝓧 -> 实数}
  证明: hX.covariance_comp hf hg

Depends on / 依赖: covariance_comp, hX.covariance_comp
-/
lemma HasLaw.covariance_fun_comp (hX : HasLaw X μ P) {f g : 𝓧 -> Real}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    cov[fun ω => f (X ω), fun ω => g (X ω); P] = cov[f, g; μ] :=
  hX.covariance_comp hf hg

/--
lemma `HasLaw.variance_eq` / 引理 `HasLaw.variance_eq`

English:
lemma HasLaw.variance_eq
  given: {μ : Measure Real} {X : Ω -> Real} (hX : HasLaw X μ P)
  proof: by
  rw [← hX.map_eq]; rw [variance_map aemeasurable_id hX.aemeasurable]; rw [Function.id_comp]

中文:
引理 HasLaw.variance_eq
  条件: {μ : Measure 实数} {X : Ω -> 实数} (hX : HasLaw X μ P)
  证明: by
  rw [← hX.map_eq]; rw [variance_map aemeasurable_id hX.aemeasurable]; rw [Function.id_comp]

Depends on / 依赖: Function, Function.id_comp, aemeasurable, aemeasurable_id, hX.aemeasurable, hX.map_eq, id_comp, map_eq, variance_map
-/
lemma HasLaw.variance_eq {μ : Measure Real} {X : Ω -> Real} (hX : HasLaw X μ P) :
    Var[X; P] = Var[id; μ] := by
  rw [← hX.map_eq]; rw [variance_map aemeasurable_id hX.aemeasurable]; rw [Function.id_comp]

/--
lemma `HasPDF.hasLaw` / 引理 `HasPDF.hasLaw`

English:
lemma HasPDF.hasLaw
  given: [h : HasPDF X P μ]
  statement: HasLaw X (μ.withDensity (pdf X P μ)) P where
  proof: h.aemeasurable
  map_eq := map_eq_withDensity_pdf X P μ

中文:
引理 HasPDF.hasLaw
  条件: [h : HasPDF X P μ]
  结论: HasLaw X (μ.withDensity (pdf X P μ)) P where
  证明: h.aemeasurable
  map_eq := map_eq_withDensity_pdf X P μ

Depends on / 依赖: aemeasurable, h.aemeasurable
-/
lemma HasPDF.hasLaw [h : HasPDF X P μ] : HasLaw X (μ.withDensity (pdf X P μ)) P where
  aemeasurable := h.aemeasurable
  map_eq := map_eq_withDensity_pdf X P μ

/--
lemma `HasLaw.ae_eq_of_smul_dirac` / 引理 `HasLaw.ae_eq_of_smul_dirac`

English:
lemma HasLaw.ae_eq_of_smul_dirac
  statement: {c : Real>=0∞} [MeasurableSingletonClass 𝓧] {x : 𝓧}
  proof: by
  apply ae_of_ae_map (p := fun y => y = x) hX.aemeasurable
  rw [hX.map_eq]
  apply Measure.ae_smul_measure (by simp)

中文:
引理 HasLaw.ae_eq_of_smul_dirac
  结论: {c : 实数>=0∞} [MeasurableSingletonClass 𝓧] {x : 𝓧}
  证明: by
  apply ae_of_ae_map (p := fun y => y = x) hX.aemeasurable
  rw [hX.map_eq]
  apply Measure.ae_smul_measure (by simp)

Depends on / 依赖: Measure, Measure.ae_smul_measure, ae_of_ae_map, ae_smul_measure, aemeasurable, hX.aemeasurable, hX.map_eq, map_eq
-/
lemma HasLaw.ae_eq_of_smul_dirac {c : Real>=0∞} [MeasurableSingletonClass 𝓧] {x : 𝓧}
    (hX : HasLaw X (c • .dirac x) P) :
    X =ᵐ[P] (fun _ => x) := by
  apply ae_of_ae_map (p := fun y => y = x) hX.aemeasurable
  rw [hX.map_eq]
  apply Measure.ae_smul_measure (by simp)

/--
lemma `HasLaw.ae_eq_of_dirac` / 引理 `HasLaw.ae_eq_of_dirac`

English:
lemma HasLaw.ae_eq_of_dirac
  given: [MeasurableSingletonClass 𝓧] {x : 𝓧} (hX : HasLaw X (.dirac x) P)
  proof: HasLaw.ae_eq_of_smul_dirac (c := 1) (by simpa)

中文:
引理 HasLaw.ae_eq_of_dirac
  条件: [MeasurableSingletonClass 𝓧] {x : 𝓧} (hX : HasLaw X (.dirac x) P)
  证明: HasLaw.ae_eq_of_smul_dirac (c := 1) (by simpa)

Depends on / 依赖: HasLaw, HasLaw.ae_eq_of_smul_dirac, ae_eq_of_smul_dirac
-/
lemma HasLaw.ae_eq_of_dirac [MeasurableSingletonClass 𝓧] {x : 𝓧} (hX : HasLaw X (.dirac x) P) :
    X =ᵐ[P] (fun _ => x) :=
  HasLaw.ae_eq_of_smul_dirac (c := 1) (by simpa)

/--
lemma `hasLaw_smul_dirac_of_ae_eq` / 引理 `hasLaw_smul_dirac_of_ae_eq`

English:
lemma hasLaw_smul_dirac_of_ae_eq
  given: {x : 𝓧} (hX : X =ᵐ[P] fun _ => x)
  proof: aemeasurable_const.congr hX.symm
  map_eq := by
    rw [map_congr hX]
    simp

中文:
引理 hasLaw_smul_dirac_of_ae_eq
  条件: {x : 𝓧} (hX : X =ᵐ[P] fun _ => x)
  证明: aemeasurable_const.congr hX.symm
  map_eq := by
    rw [map_congr hX]
    simp

Depends on / 依赖: aemeasurable_const, aemeasurable_const.congr, hX.symm
-/
lemma hasLaw_smul_dirac_of_ae_eq {x : 𝓧} (hX : X =ᵐ[P] fun _ => x) :
    HasLaw X ((P Set.univ) • .dirac x) P where
  aemeasurable := aemeasurable_const.congr hX.symm
  map_eq := by
    rw [map_congr hX]
    simp

/--
lemma `hasLaw_dirac_of_ae_eq` / 引理 `hasLaw_dirac_of_ae_eq`

English:
lemma hasLaw_dirac_of_ae_eq
  given: [IsProbabilityMeasure P] {x : 𝓧} (hX : X =ᵐ[P] fun _ => x)
  proof: by
  simpa using hasLaw_smul_dirac_of_ae_eq hX

中文:
引理 hasLaw_dirac_of_ae_eq
  条件: [IsProbabilityMeasure P] {x : 𝓧} (hX : X =ᵐ[P] fun _ => x)
  证明: by
  simpa using hasLaw_smul_dirac_of_ae_eq hX

Depends on / 依赖: hasLaw_smul_dirac_of_ae_eq
-/
lemma hasLaw_dirac_of_ae_eq [IsProbabilityMeasure P] {x : 𝓧} (hX : X =ᵐ[P] fun _ => x) :
    HasLaw X (.dirac x) P := by
  simpa using hasLaw_smul_dirac_of_ae_eq hX

/--
lemma `hasLaw_smul_dirac_iff` / 引理 `hasLaw_smul_dirac_iff`

English:
lemma hasLaw_smul_dirac_iff
  given: [MeasurableSingletonClass 𝓧] {x : 𝓧}
  proof: HasLaw.ae_eq_of_smul_dirac
  mpr := hasLaw_smul_dirac_of_ae_eq

中文:
引理 hasLaw_smul_dirac_iff
  条件: [MeasurableSingletonClass 𝓧] {x : 𝓧}
  证明: HasLaw.ae_eq_of_smul_dirac
  mpr := hasLaw_smul_dirac_of_ae_eq

Depends on / 依赖: HasLaw, HasLaw.ae_eq_of_smul_dirac, ae_eq_of_smul_dirac
-/
lemma hasLaw_smul_dirac_iff [MeasurableSingletonClass 𝓧] {x : 𝓧} :
    HasLaw X ((P Set.univ) • .dirac x) P ↔ X =ᵐ[P] (fun _ => x) where
  mp := HasLaw.ae_eq_of_smul_dirac
  mpr := hasLaw_smul_dirac_of_ae_eq

/--
lemma `hasLaw_dirac_iff` / 引理 `hasLaw_dirac_iff`

English:
lemma hasLaw_dirac_iff
  given: [IsProbabilityMeasure P] [MeasurableSingletonClass 𝓧] {x : 𝓧}
  proof: HasLaw.ae_eq_of_dirac
  mpr := hasLaw_dirac_of_ae_eq

中文:
引理 hasLaw_dirac_iff
  条件: [IsProbabilityMeasure P] [MeasurableSingletonClass 𝓧] {x : 𝓧}
  证明: HasLaw.ae_eq_of_dirac
  mpr := hasLaw_dirac_of_ae_eq

Depends on / 依赖: HasLaw, HasLaw.ae_eq_of_dirac, ae_eq_of_dirac
-/
lemma hasLaw_dirac_iff [IsProbabilityMeasure P] [MeasurableSingletonClass 𝓧] {x : 𝓧} :
    HasLaw X (.dirac x) P ↔ X =ᵐ[P] (fun _ => x) where
  mp := HasLaw.ae_eq_of_dirac
  mpr := hasLaw_dirac_of_ae_eq

/--
lemma `indepFun_iff_hasLaw_prodMk_prod` / 引理 `indepFun_iff_hasLaw_prodMk_prod`

English:
lemma indepFun_iff_hasLaw_prodMk_prod
  statement: [IsFiniteMeasure P] {𝓨 : Type*} {m𝓨 : MeasurableSpace 𝓨}
  proof: { map_eq := by
        rw [h.map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)]; rw [hX.map_eq]; rw [hY.map_eq] }
  mpr h := by
    rw [indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)]; rw [h.map_eq]; rw [hX.map_eq]; rw [hY.map_eq]

alias ⟨IndepFun.hasLaw_prod, _⟩ := indepFun_if

中文:
引理 indepFun_iff_hasLaw_prodMk_prod
  结论: [IsFiniteMeasure P] {𝓨 : 类型} {m𝓨 : MeasurableSpace 𝓨}
  证明: { map_eq := by
        rw [h.map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)]; rw [hX.map_eq]; rw [hY.map_eq] }
  mpr h := by
    rw [indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)]; rw [h.map_eq]; rw [hX.map_eq]; rw [hY.map_eq]

alias ⟨IndepFun.hasLaw_prod, _⟩ := indepFun_if

Depends on / 依赖: fun_prop, h.map_eq, h.map_prod_eq_prod_map_map, hX.map_eq, hY.map_eq, indepFun_iff_map_prod_eq_prod_map_map, map_eq, map_prod_eq_prod_map_map
-/
lemma indepFun_iff_hasLaw_prodMk_prod [IsFiniteMeasure P] {𝓨 : Type*} {m𝓨 : MeasurableSpace 𝓨}
    {ν : Measure 𝓨} {Y : Ω -> 𝓨} (hX : HasLaw X μ P) (hY : HasLaw Y ν P) :
    X ⟂ᵢ[P] Y ↔ HasLaw (fun ω => (X ω, Y ω)) (μ.prod ν) P where
  mp h :=
    { map_eq := by
        rw [h.map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)]; rw [hX.map_eq]; rw [hY.map_eq] }
  mpr h := by
    rw [indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)]; rw [h.map_eq]; rw [hX.map_eq]; rw [hY.map_eq]

alias ⟨IndepFun.hasLaw_prod, _⟩ := indepFun_iff_hasLaw_prodMk_prod

/--
lemma `iIndepFun.hasLaw_pi` / 引理 `iIndepFun.hasLaw_pi`

English:
lemma iIndepFun.hasLaw_pi
  statement: {ι : Type*} [Fintype ι] {𝓧 : ι -> Type*} {m𝓧 : forall i, MeasurableSpace (𝓧 i)}
  proof: by
    rw [h.map_fun_eq_pi_map (by fun_prop)]
    simp_rw [fun i => (hX i).map_eq]

中文:
引理 iIndepFun.hasLaw_pi
  结论: {ι : 类型} [Fintype ι] {𝓧 : ι -> 类型} {m𝓧 : 对任意 i, MeasurableSpace (𝓧 i)}
  证明: by
    rw [h.map_fun_eq_pi_map (by fun_prop)]
    simp_rw [fun i => (hX i).map_eq]

Depends on / 依赖: fun_prop, h.map_fun_eq_pi_map, map_eq, map_fun_eq_pi_map, simp_rw
-/
lemma iIndepFun.hasLaw_pi {ι : Type*} [Fintype ι] {𝓧 : ι -> Type*} {m𝓧 : forall i, MeasurableSpace (𝓧 i)}
    {μ : (i : ι) -> Measure (𝓧 i)} {X : (i : ι) -> Ω -> 𝓧 i} (hX : forall i, HasLaw (X i) (μ i) P)
    (h : iIndepFun X P) :
    HasLaw (fun ω i => X i ω) (Measure.pi μ) P where
  map_eq := by
    rw [h.map_fun_eq_pi_map (by fun_prop)]
    simp_rw [fun i => (hX i).map_eq]

/--
lemma `iIndepFun_iff_hasLaw_pi_pi` / 引理 `iIndepFun_iff_hasLaw_pi_pi`

English:
lemma iIndepFun_iff_hasLaw_pi_pi
  statement: [IsProbabilityMeasure P] {ι : Type*} [Fintype ι] {𝓧 : ι -> Type*}
  proof: h.hasLaw_pi hX
  mpr h := by
    rw [iIndepFun_iff_map_fun_eq_pi_map (by fun_prop)]; rw [h.map_eq]
    simp_rw [fun i => (hX i).map_eq]

中文:
引理 iIndepFun_iff_hasLaw_pi_pi
  结论: [IsProbabilityMeasure P] {ι : 类型} [Fintype ι] {𝓧 : ι -> 类型}
  证明: h.hasLaw_pi hX
  mpr h := by
    rw [iIndepFun_iff_map_fun_eq_pi_map (by fun_prop)]; rw [h.map_eq]
    simp_rw [fun i => (hX i).map_eq]

Depends on / 依赖: h.hasLaw_pi, hasLaw_pi
-/
lemma iIndepFun_iff_hasLaw_pi_pi [IsProbabilityMeasure P] {ι : Type*} [Fintype ι] {𝓧 : ι -> Type*}
    {m𝓧 : forall i, MeasurableSpace (𝓧 i)} {μ : (i : ι) -> Measure (𝓧 i)}
    {X : (i : ι) -> Ω -> 𝓧 i} (hX : forall i, HasLaw (X i) (μ i) P) :
    iIndepFun X P ↔ HasLaw (fun ω i => X i ω) (Measure.pi μ) P where
  mp h := h.hasLaw_pi hX
  mpr h := by
    rw [iIndepFun_iff_map_fun_eq_pi_map (by fun_prop)]; rw [h.map_eq]
    simp_rw [fun i => (hX i).map_eq]

end ProbabilityTheory
