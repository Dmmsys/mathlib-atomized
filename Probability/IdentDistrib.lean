/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
# Identically distributed random variables

Two random variables defined on two (possibly different) probability spaces but taking value in
the same space are *identically distributed* if their distributions (i.e., the image probability
measures on the target space) coincide. We define this concept and establish its basic properties
in this file.

## Main definitions and results

* `IdentDistrib f g μ ν` registers that the image of `μ` under `f` coincides with the image of `ν`
  under `g` (and that `f` and `g` are almost everywhere measurable, as otherwise the image measures
  don't make sense). The measures can be kept implicit as in `IdentDistrib f g` if the spaces
  are registered as measure spaces.
* `IdentDistrib.comp`: being identically distributed is stable under composition with measurable
  maps.

There are two main kinds of lemmas, under the assumption that `f` and `g` are identically
distributed: lemmas saying that two quantities computed for `f` and `g` are the same, and lemmas
saying that if `f` has some property then `g` also has it. The first kind is registered as
`IdentDistrib.foo_fst`, the second one as `IdentDistrib.foo_snd` (in the latter case, to deduce
a property of `f` from one of `g`, use `h.symm.foo_snd` where `h : IdentDistrib f g μ ν`). For
instance:

* `IdentDistrib.measure_mem_eq`: if `f` and `g` are identically distributed, then the probabilities
  that they belong to a given measurable set are the same.
* `IdentDistrib.integral_eq`: if `f` and `g` are identically distributed, then their integrals
  are the same.
* `IdentDistrib.variance_eq`: if `f` and `g` are identically distributed, then their variances
  are the same.

* `IdentDistrib.aestronglyMeasurable_snd`: if `f` and `g` are identically distributed and `f`
  is almost everywhere strongly measurable, then so is `g`.
* `IdentDistrib.memLp_snd`: if `f` and `g` are identically distributed and `f`
  belongs to `ℒp`, then so does `g`.

We also register several dot notation shortcuts for convenience.
For instance, if `h : IdentDistrib f g μ ν`, then `h.sq` states that `f^2` and `g^2` are
identically distributed, and `h.norm` states that `‖f‖` and `‖g‖` are identically distributed, and
so on.
-/

public section


open MeasureTheory Filter Finset

noncomputable section

open scoped Topology MeasureTheory ENNReal NNReal

variable {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSpace δ]

namespace ProbabilityTheory

/--
Definition of `IdentDistrib` / `IdentDistrib` 的定义

English:
structure IdentDistrib
  parameters: (f : α -> γ) (g : β -> γ)
  axioms and operations (3):
    - aemeasurable_fst : AEMeasurable f μ
    - aemeasurable_snd : AEMeasurable g ν
    - map_eq : Measure.map f μ = Measure.map g ν

中文:
结构 同分布
  参数: (f : α -> γ) (g : β -> γ)
  公理与运算 (3 个):
    - aemeasurable_fst : 几乎处处可测 f μ
    - aemeasurable_snd : 几乎处处可测 g ν
    - map_eq : 测度.map f μ = 测度.map g ν

Depends on / 依赖: AEMeasurable, Measure, Measure.map, aemeasurable_fst, aemeasurable_snd, map_eq, volume_tac
-/
structure IdentDistrib (f : α -> γ) (g : β -> γ)
    (μ : Measure α := by volume_tac)
    (ν : Measure β := by volume_tac) : Prop where
  aemeasurable_fst : AEMeasurable f μ
  aemeasurable_snd : AEMeasurable g ν
  map_eq : Measure.map f μ = Measure.map g ν

namespace IdentDistrib

open TopologicalSpace

variable {μ : Measure α} {ν : Measure β} {f : α -> γ} {g : β -> γ}

/--
theorem `refl` / 定理 `refl`

English:
theorem refl
  given: (hf : AEMeasurable f μ)
  statement: IdentDistrib f f μ μ
  proof: { aemeasurable_fst := hf
    aemeasurable_snd := hf
    map_eq := rfl }

中文:
定理 refl
  条件: (hf : 几乎处处可测 f μ)
  结论: 同分布 f f μ μ
  证明: { aemeasurable_fst := hf
    aemeasurable_snd := hf
    map_eq := rfl }
-/
protected theorem refl (hf : AEMeasurable f μ) : IdentDistrib f f μ μ :=
  { aemeasurable_fst := hf
    aemeasurable_snd := hf
    map_eq := rfl }

/--
theorem `symm` / 定理 `symm`

English:
theorem symm
  given: (h : IdentDistrib f g μ ν)
  statement: IdentDistrib g f ν μ
  proof: { aemeasurable_fst := h.aemeasurable_snd
    aemeasurable_snd := h.aemeasurable_fst
    map_eq := h.map_eq.symm }

中文:
定理 symm
  条件: (h : 同分布 f g μ ν)
  结论: 同分布 g f ν μ
  证明: { aemeasurable_fst := h.aemeasurable_snd
    aemeasurable_snd := h.aemeasurable_fst
    map_eq := h.map_eq.symm }
-/
protected theorem symm (h : IdentDistrib f g μ ν) : IdentDistrib g f ν μ :=
  { aemeasurable_fst := h.aemeasurable_snd
    aemeasurable_snd := h.aemeasurable_fst
    map_eq := h.map_eq.symm }

/--
theorem `trans` / 定理 `trans`

English:
theorem trans
  statement: {ρ : Measure δ} {h : δ -> γ} (h₁ : IdentDistrib f g μ ν)
  proof: { aemeasurable_fst := h₁.aemeasurable_fst
    aemeasurable_snd := h₂.aemeasurable_snd
    map_eq := h₁.map_eq.trans h₂.map_eq }

中文:
定理 trans
  结论: {ρ : 测度 δ} {h : δ -> γ} (h₁ : 同分布 f g μ ν)
  证明: { aemeasurable_fst := h₁.aemeasurable_fst
    aemeasurable_snd := h₂.aemeasurable_snd
    map_eq := h₁.map_eq.trans h₂.map_eq }
-/
protected theorem trans {ρ : Measure δ} {h : δ -> γ} (h₁ : IdentDistrib f g μ ν)
    (h₂ : IdentDistrib g h ν ρ) : IdentDistrib f h μ ρ :=
  { aemeasurable_fst := h₁.aemeasurable_fst
    aemeasurable_snd := h₂.aemeasurable_snd
    map_eq := h₁.map_eq.trans h₂.map_eq }

/--
theorem `comp_of_aemeasurable` / 定理 `comp_of_aemeasurable`

English:
theorem comp_of_aemeasurable
  statement: {u : γ -> δ} (h : IdentDistrib f g μ ν)
  proof: { aemeasurable_fst := hu.comp_aemeasurable h.aemeasurable_fst
    aemeasurable_snd := by rw [h.map_eq] at hu; exact hu.comp_aemeasurable h.aemeasurable_snd
    map_eq := by
      rw [← AEMeasurable.map_map_of_aemeasurable hu h.aemeasurable_fst]; rw [←
        AEMeasurable.map_map_of_aemeasurable _ h

中文:
定理 comp_of_aemeasurable
  结论: {u : γ -> δ} (h : 同分布 f g μ ν)
  证明: { aemeasurable_fst := hu.comp_aemeasurable h.aemeasurable_fst
    aemeasurable_snd := by rw [h.map_eq] at hu; exact hu.comp_aemeasurable h.aemeasurable_snd
    map_eq := by
      rw [← AEMeasurable.map_map_of_aemeasurable hu h.aemeasurable_fst]; rw [←
        AEMeasurable.map_map_of_aemeasurable _ h
-/
protected theorem comp_of_aemeasurable {u : γ -> δ} (h : IdentDistrib f g μ ν)
    (hu : AEMeasurable u (Measure.map f μ)) : IdentDistrib (u ∘ f) (u ∘ g) μ ν :=
  { aemeasurable_fst := hu.comp_aemeasurable h.aemeasurable_fst
    aemeasurable_snd := by rw [h.map_eq] at hu; exact hu.comp_aemeasurable h.aemeasurable_snd
    map_eq := by
      rw [← AEMeasurable.map_map_of_aemeasurable hu h.aemeasurable_fst]; rw [←
        AEMeasurable.map_map_of_aemeasurable _ h.aemeasurable_snd]; rw [h.map_eq]
      rwa [← h.map_eq] }

/--
theorem `comp` / 定理 `comp`

English:
theorem comp
  given: {u : γ -> δ} (h : IdentDistrib f g μ ν) (hu : Measurable u)
  proof: h.comp_of_aemeasurable hu.aemeasurable

中文:
定理 comp
  条件: {u : γ -> δ} (h : 同分布 f g μ ν) (hu : 可测 u)
  证明: h.comp_of_aemeasurable hu.aemeasurable
-/
protected theorem comp {u : γ -> δ} (h : IdentDistrib f g μ ν) (hu : Measurable u) :
    IdentDistrib (u ∘ f) (u ∘ g) μ ν :=
  h.comp_of_aemeasurable hu.aemeasurable

/--
theorem `of_ae_eq` / 定理 `of_ae_eq`

English:
theorem of_ae_eq
  given: {g : α -> γ} (hf : AEMeasurable f μ) (heq : f =ᵐ[μ] g)
  proof: { aemeasurable_fst := hf
    aemeasurable_snd := hf.congr heq
    map_eq := Measure.map_congr heq }

中文:
定理 of_ae_eq
  条件: {g : α -> γ} (hf : 几乎处处可测 f μ) (heq : f =ᵐ[μ] g)
  证明: { aemeasurable_fst := hf
    aemeasurable_snd := hf.congr heq
    map_eq := Measure.map_congr heq }
-/
protected theorem of_ae_eq {g : α -> γ} (hf : AEMeasurable f μ) (heq : f =ᵐ[μ] g) :
    IdentDistrib f g μ μ :=
  { aemeasurable_fst := hf
    aemeasurable_snd := hf.congr heq
    map_eq := Measure.map_congr heq }

/--
lemma `_root_.MeasureTheory.AEMeasurable.identDistrib_mk` / 引理 `_root_.MeasureTheory.AEMeasurable.identDistrib_mk`

English:
lemma _root_.MeasureTheory.AEMeasurable.identDistrib_mk
  proof: IdentDistrib.of_ae_eq hf hf.ae_eq_mk

中文:
引理 _root_.测度论.几乎处处可测.identDistrib_mk
  证明: IdentDistrib.of_ae_eq hf hf.ae_eq_mk

Depends on / 依赖: IdentDistrib, IdentDistrib.of_ae_eq, ae_eq_mk, hf.ae_eq_mk, of_ae_eq
-/
lemma _root_.MeasureTheory.AEMeasurable.identDistrib_mk
    (hf : AEMeasurable f μ) : IdentDistrib f (hf.mk f) μ μ :=
  IdentDistrib.of_ae_eq hf hf.ae_eq_mk

/--
lemma `_root_.MeasureTheory.AEStronglyMeasurable.identDistrib_mk` / 引理 `_root_.MeasureTheory.AEStronglyMeasurable.identDistrib_mk`

English:
lemma _root_.MeasureTheory.AEStronglyMeasurable.identDistrib_mk
  proof: IdentDistrib.of_ae_eq hf.aemeasurable hf.ae_eq_mk

中文:
引理 _root_.测度论.AEStronglyMeasurable.identDistrib_mk
  证明: IdentDistrib.of_ae_eq hf.aemeasurable hf.ae_eq_mk

Depends on / 依赖: IdentDistrib, IdentDistrib.of_ae_eq, ae_eq_mk, aemeasurable, hf.ae_eq_mk, hf.aemeasurable, of_ae_eq
-/
lemma _root_.MeasureTheory.AEStronglyMeasurable.identDistrib_mk
    [TopologicalSpace γ] [PseudoMetrizableSpace γ] [BorelSpace γ]
    (hf : AEStronglyMeasurable f μ) : IdentDistrib f (hf.mk f) μ μ :=
  IdentDistrib.of_ae_eq hf.aemeasurable hf.ae_eq_mk

/--
theorem `measure_mem_eq` / 定理 `measure_mem_eq`

English:
theorem measure_mem_eq
  given: (h : IdentDistrib f g μ ν) {s : Set γ} (hs : MeasurableSet s)
  proof: by
  rw [← Measure.map_apply_of_aemeasurable h.aemeasurable_fst hs]; rw [←
    Measure.map_apply_of_aemeasurable h.aemeasurable_snd hs]; rw [h.map_eq]

alias measure_preimage_eq := measure_mem_eq

中文:
定理 measure_mem_eq
  条件: (h : 同分布 f g μ ν) {s : 集合 γ} (hs : 可测集 s)
  证明: by
  rw [← Measure.map_apply_of_aemeasurable h.aemeasurable_fst hs]; rw [←
    Measure.map_apply_of_aemeasurable h.aemeasurable_snd hs]; rw [h.map_eq]

alias measure_preimage_eq := measure_mem_eq

Depends on / 依赖: Measure, Measure.map_apply_of_aemeasurable, aemeasurable_fst, aemeasurable_snd, h.aemeasurable_fst, h.aemeasurable_snd, h.map_eq, map_apply_of_aemeasurable, map_eq
-/
theorem measure_mem_eq (h : IdentDistrib f g μ ν) {s : Set γ} (hs : MeasurableSet s) :
    μ (f ⁻¹' s) = ν (g ⁻¹' s) := by
  rw [← Measure.map_apply_of_aemeasurable h.aemeasurable_fst hs]; rw [←
    Measure.map_apply_of_aemeasurable h.aemeasurable_snd hs]; rw [h.map_eq]

alias measure_preimage_eq := measure_mem_eq

/--
theorem `ae_snd` / 定理 `ae_snd`

English:
theorem ae_snd
  statement: (h : IdentDistrib f g μ ν) {p : γ -> Prop} (pmeas : MeasurableSet {x | p x})
  proof: by
  apply (ae_map_iff h.aemeasurable_snd pmeas).1
  rw [← h.map_eq]
  exact (ae_map_iff h.aemeasurable_fst pmeas).2 hp

中文:
定理 ae_snd
  结论: (h : 同分布 f g μ ν) {p : γ -> 命题} (pmeas : 可测集 {x | p x})
  证明: by
  apply (ae_map_iff h.aemeasurable_snd pmeas).1
  rw [← h.map_eq]
  exact (ae_map_iff h.aemeasurable_fst pmeas).2 hp

Depends on / 依赖: ae_map_iff, aemeasurable_fst, aemeasurable_snd, h.aemeasurable_fst, h.aemeasurable_snd, h.map_eq, map_eq
-/
theorem ae_snd (h : IdentDistrib f g μ ν) {p : γ -> Prop} (pmeas : MeasurableSet {x | p x})
    (hp : forallᵐ x ∂μ, p (f x)) : forallᵐ x ∂ν, p (g x) := by
  apply (ae_map_iff h.aemeasurable_snd pmeas).1
  rw [← h.map_eq]
  exact (ae_map_iff h.aemeasurable_fst pmeas).2 hp

/--
theorem `ae_mem_snd` / 定理 `ae_mem_snd`

English:
theorem ae_mem_snd
  statement: (h : IdentDistrib f g μ ν) {t : Set γ} (tmeas : MeasurableSet t)
  proof: h.ae_snd tmeas ht

中文:
定理 ae_mem_snd
  结论: (h : 同分布 f g μ ν) {t : 集合 γ} (tmeas : 可测集 t)
  证明: h.ae_snd tmeas ht

Depends on / 依赖: ae_snd, h.ae_snd
-/
theorem ae_mem_snd (h : IdentDistrib f g μ ν) {t : Set γ} (tmeas : MeasurableSet t)
    (ht : forallᵐ x ∂μ, f x in t) : forallᵐ x ∂ν, g x in t :=
  h.ae_snd tmeas ht

/--
theorem `_root_.ProbabilityTheory.HasLaw.identDistrib` / 定理 `_root_.ProbabilityTheory.HasLaw.identDistrib`

English:
theorem _root_.ProbabilityTheory.HasLaw.identDistrib
  statement: {κ : Measure γ} (h₀ : HasLaw f κ μ)
  proof: ⟨h₀.aemeasurable, h₁.aemeasurable, by simp [h₀.map_eq, h₁.map_eq]⟩

中文:
定理 _root_.ProbabilityTheory.有Law.identDistrib
  结论: {κ : 测度 γ} (h₀ : 有Law f κ μ)
  证明: ⟨h₀.aemeasurable, h₁.aemeasurable, by simp [h₀.map_eq, h₁.map_eq]⟩

Depends on / 依赖: aemeasurable, map_eq
-/
theorem _root_.ProbabilityTheory.HasLaw.identDistrib {κ : Measure γ} (h₀ : HasLaw f κ μ)
    (h₁ : HasLaw g κ ν) : IdentDistrib f g μ ν :=
  ⟨h₀.aemeasurable, h₁.aemeasurable, by simp [h₀.map_eq, h₁.map_eq]⟩

/--
theorem `hasLaw` / 定理 `hasLaw`

English:
theorem hasLaw
  given: {κ : Measure γ} (h₀ : IdentDistrib f g μ ν) (h₁ : HasLaw f κ μ)
  statement: HasLaw g κ ν
  proof: ⟨h₀.aemeasurable_snd, by simp [h₀.map_eq, ← h₁.map_eq]⟩

中文:
定理 hasLaw
  条件: {κ : 测度 γ} (h₀ : 同分布 f g μ ν) (h₁ : 有Law f κ μ)
  结论: 有Law g κ ν
  证明: ⟨h₀.aemeasurable_snd, by simp [h₀.map_eq, ← h₁.map_eq]⟩

Depends on / 依赖: aemeasurable_snd, map_eq
-/
theorem hasLaw {κ : Measure γ} (h₀ : IdentDistrib f g μ ν) (h₁ : HasLaw f κ μ) : HasLaw g κ ν :=
  ⟨h₀.aemeasurable_snd, by simp [h₀.map_eq, ← h₁.map_eq]⟩

/--
theorem `aestronglyMeasurable_fst` / 定理 `aestronglyMeasurable_fst`

English:
theorem aestronglyMeasurable_fst
  statement: [TopologicalSpace γ] [PseudoMetrizableSpace γ]
  proof: h.aemeasurable_fst.aestronglyMeasurable

中文:
定理 aestronglyMeasurable_fst
  结论: [拓扑空间 γ] [PseudoMetrizable空间 γ]
  证明: h.aemeasurable_fst.aestronglyMeasurable

Depends on / 依赖: aemeasurable_fst, aestronglyMeasurable, h.aemeasurable_fst.aestronglyMeasurable
-/
theorem aestronglyMeasurable_fst [TopologicalSpace γ] [PseudoMetrizableSpace γ]
    [OpensMeasurableSpace γ] [SecondCountableTopology γ] (h : IdentDistrib f g μ ν) :
    AEStronglyMeasurable f μ :=
  h.aemeasurable_fst.aestronglyMeasurable

/--
theorem `aestronglyMeasurable_snd` / 定理 `aestronglyMeasurable_snd`

English:
theorem aestronglyMeasurable_snd
  statement: [TopologicalSpace γ] [PseudoMetrizableSpace γ] [BorelSpace γ]
  proof: by
  refine aestronglyMeasurable_iff_aemeasurable_separable.2 ⟨h.aemeasurable_snd, ?_⟩
  rcases (aestronglyMeasurable_iff_aemeasurable_separable.1 hf).2 with ⟨t, t_sep, ht⟩
  refine ⟨closure t, t_sep.closure, ?_⟩
  apply h.ae_mem_snd isClosed_closure.measurableSet
  filter_upwards [ht] with x hx usi

中文:
定理 aestronglyMeasurable_snd
  结论: [拓扑空间 γ] [PseudoMetrizable空间 γ] [Borel空间 γ]
  证明: by
  refine aestronglyMeasurable_iff_aemeasurable_separable.2 ⟨h.aemeasurable_snd, ?_⟩
  rcases (aestronglyMeasurable_iff_aemeasurable_separable.1 hf).2 with ⟨t, t_sep, ht⟩
  refine ⟨closure t, t_sep.closure, ?_⟩
  apply h.ae_mem_snd isClosed_closure.measurableSet
  filter_upwards [ht] with x hx usi

Depends on / 依赖: ae_mem_snd, aemeasurable_snd, aestronglyMeasurable_iff_aemeasurable_separable, closure, filter_upwards, h.ae_mem_snd, h.aemeasurable_snd, isClosed_closure, isClosed_closure.measurableSet, measurableSet, subset_closure, t_sep, t_sep.closure
-/
theorem aestronglyMeasurable_snd [TopologicalSpace γ] [PseudoMetrizableSpace γ] [BorelSpace γ]
    (h : IdentDistrib f g μ ν) (hf : AEStronglyMeasurable f μ) : AEStronglyMeasurable g ν := by
  refine aestronglyMeasurable_iff_aemeasurable_separable.2 ⟨h.aemeasurable_snd, ?_⟩
  rcases (aestronglyMeasurable_iff_aemeasurable_separable.1 hf).2 with ⟨t, t_sep, ht⟩
  refine ⟨closure t, t_sep.closure, ?_⟩
  apply h.ae_mem_snd isClosed_closure.measurableSet
  filter_upwards [ht] with x hx using subset_closure hx

/--
theorem `aestronglyMeasurable_iff` / 定理 `aestronglyMeasurable_iff`

English:
theorem aestronglyMeasurable_iff
  statement: [TopologicalSpace γ] [PseudoMetrizableSpace γ] [BorelSpace γ]
  proof: ⟨fun hf => h.aestronglyMeasurable_snd hf, fun hg => h.symm.aestronglyMeasurable_snd hg⟩

中文:
定理 aestronglyMeasurable_iff
  结论: [拓扑空间 γ] [PseudoMetrizable空间 γ] [Borel空间 γ]
  证明: ⟨fun hf => h.aestronglyMeasurable_snd hf, fun hg => h.symm.aestronglyMeasurable_snd hg⟩

Depends on / 依赖: aestronglyMeasurable_snd, h.aestronglyMeasurable_snd, h.symm.aestronglyMeasurable_snd
-/
theorem aestronglyMeasurable_iff [TopologicalSpace γ] [PseudoMetrizableSpace γ] [BorelSpace γ]
    (h : IdentDistrib f g μ ν) : AEStronglyMeasurable f μ ↔ AEStronglyMeasurable g ν :=
  ⟨fun hf => h.aestronglyMeasurable_snd hf, fun hg => h.symm.aestronglyMeasurable_snd hg⟩

/--
theorem `essSup_eq` / 定理 `essSup_eq`

English:
theorem essSup_eq
  statement: [ConditionallyCompleteLinearOrder γ] [TopologicalSpace γ] [OpensMeasurableSpace γ]
  proof: by
  have I : forall a, μ {x : α | a < f x} = ν {x : β | a < g x} := fun a =>
    h.measure_mem_eq measurableSet_Ioi
  simp_rw [essSup_eq_sInf, I]

中文:
定理 essSup_eq
  结论: [条件完备线性序 γ] [拓扑空间 γ] [OpensMeasurable空间 γ]
  证明: by
  have I : forall a, μ {x : α | a < f x} = ν {x : β | a < g x} := fun a =>
    h.measure_mem_eq measurableSet_Ioi
  simp_rw [essSup_eq_sInf, I]

Depends on / 依赖: essSup_eq_sInf, h.measure_mem_eq, measurableSet_Ioi, measure_mem_eq, simp_rw
-/
theorem essSup_eq [ConditionallyCompleteLinearOrder γ] [TopologicalSpace γ] [OpensMeasurableSpace γ]
    [OrderClosedTopology γ] (h : IdentDistrib f g μ ν) : essSup f μ = essSup g ν := by
  have I : forall a, μ {x : α | a < f x} = ν {x : β | a < g x} := fun a =>
    h.measure_mem_eq measurableSet_Ioi
  simp_rw [essSup_eq_sInf, I]

/--
theorem `lintegral_eq` / 定理 `lintegral_eq`

English:
theorem lintegral_eq
  given: {f : α -> Real>=0∞} {g : β -> Real>=0∞} (h : IdentDistrib f g μ ν)
  proof: by
  change ∫⁻ x, id (f x) ∂μ = ∫⁻ x, id (g x) ∂ν
  rw [← lintegral_map' aemeasurable_id h.aemeasurable_fst]; rw [←
    lintegral_map' aemeasurable_id h.aemeasurable_snd]; rw [h.map_eq]

中文:
定理 lintegral_eq
  条件: {f : α -> 实数>=0∞} {g : β -> 实数>=0∞} (h : 同分布 f g μ ν)
  证明: by
  change ∫⁻ x, id (f x) ∂μ = ∫⁻ x, id (g x) ∂ν
  rw [← lintegral_map' aemeasurable_id h.aemeasurable_fst]; rw [←
    lintegral_map' aemeasurable_id h.aemeasurable_snd]; rw [h.map_eq]

Depends on / 依赖: aemeasurable_fst, aemeasurable_id, aemeasurable_snd, h.aemeasurable_fst, h.aemeasurable_snd, h.map_eq, lintegral_map, map_eq
-/
theorem lintegral_eq {f : α -> Real>=0∞} {g : β -> Real>=0∞} (h : IdentDistrib f g μ ν) :
    ∫⁻ x, f x ∂μ = ∫⁻ x, g x ∂ν := by
  change ∫⁻ x, id (f x) ∂μ = ∫⁻ x, id (g x) ∂ν
  rw [← lintegral_map' aemeasurable_id h.aemeasurable_fst]; rw [←
    lintegral_map' aemeasurable_id h.aemeasurable_snd]; rw [h.map_eq]

/--
theorem `integral_eq` / 定理 `integral_eq`

English:
theorem integral_eq
  statement: [NormedAddCommGroup γ] [NormedSpace Real γ] [BorelSpace γ]
  proof: by
  by_cases hf : AEStronglyMeasurable f μ
  · have A : AEStronglyMeasurable id (Measure.map f μ) := by
      rw [aestronglyMeasurable_iff_aemeasurable_separable]
      rcases (aestronglyMeasurable_iff_aemeasurable_separable.1 hf).2 with ⟨t, t_sep, ht⟩
      refine ⟨aemeasurable_id, ⟨closure t, t_s

中文:
定理 integral_eq
  结论: [赋范交换加群 γ] [赋范空间 实数 γ] [Borel空间 γ]
  证明: by
  by_cases hf : AEStronglyMeasurable f μ
  · have A : AEStronglyMeasurable id (Measure.map f μ) := by
      rw [aestronglyMeasurable_iff_aemeasurable_separable]
      rcases (aestronglyMeasurable_iff_aemeasurable_separable.1 hf).2 with ⟨t, t_sep, ht⟩
      refine ⟨aemeasurable_id, ⟨closure t, t_s

Depends on / 依赖: AEStronglyMeasurable, Measure, Measure.map, ae_map_iff, aemeasurabl, aemeasurable_fst, aemeasurable_id, aestronglyMeasurable_iff_aemeasurable_separable, closure, filter_upwards, h.aemeasurabl, h.aemeasurable_fst, integral_map, isClosed_closure, isClosed_closure.measurableSet, measurableSet, subset_closure, t_sep, t_sep.closure
-/
theorem integral_eq [NormedAddCommGroup γ] [NormedSpace Real γ] [BorelSpace γ]
    (h : IdentDistrib f g μ ν) : ∫ x, f x ∂μ = ∫ x, g x ∂ν := by
  by_cases hf : AEStronglyMeasurable f μ
  · have A : AEStronglyMeasurable id (Measure.map f μ) := by
      rw [aestronglyMeasurable_iff_aemeasurable_separable]
      rcases (aestronglyMeasurable_iff_aemeasurable_separable.1 hf).2 with ⟨t, t_sep, ht⟩
      refine ⟨aemeasurable_id, ⟨closure t, t_sep.closure, ?_⟩⟩
      rw [ae_map_iff h.aemeasurable_fst]
      · filter_upwards [ht] with x hx using subset_closure hx
      · exact isClosed_closure.measurableSet
    change ∫ x, id (f x) ∂μ = ∫ x, id (g x) ∂ν
    rw [← integral_map h.aemeasurable_fst A]
    rw [h.map_eq] at A
    rw [← integral_map h.aemeasurable_snd A]; rw [h.map_eq]
  · rw [integral_non_aestronglyMeasurable hf]
    rw [h.aestronglyMeasurable_iff] at hf
    rw [integral_non_aestronglyMeasurable hf]

/--
theorem `eLpNorm_eq` / 定理 `eLpNorm_eq`

English:
theorem eLpNorm_eq
  statement: [NormedAddCommGroup γ] [OpensMeasurableSpace γ] (h : IdentDistrib f g μ ν)
  proof: by
  by_cases h0 : p = 0
  · simp [h0]
  by_cases h_top : p = ∞
  · simp only [h_top, eLpNorm, eLpNormEssSup, ENNReal.top_ne_zero, if_true,
      if_false]
    apply essSup_eq
    exact h.comp (measurable_coe_nnreal_ennreal.comp measurable_nnnorm)
  simp only [eLpNorm_eq_eLpNorm' h0 h_top, eLpNorm',

中文:
定理 eLpNorm_eq
  结论: [赋范交换加群 γ] [OpensMeasurable空间 γ] (h : 同分布 f g μ ν)
  证明: by
  by_cases h0 : p = 0
  · simp [h0]
  by_cases h_top : p = ∞
  · simp only [h_top, eLpNorm, eLpNormEssSup, ENNReal.top_ne_zero, if_true,
      if_false]
    apply essSup_eq
    exact h.comp (measurable_coe_nnreal_ennreal.comp measurable_nnnorm)
  simp only [eLpNorm_eq_eLpNorm' h0 h_top, eLpNorm',

Depends on / 依赖: ENNReal, ENNReal.top_ne_zero, Measurable, Measurable.pow_const, eLpNorm, eLpNormEssSup, eLpNorm_eq_eLpNorm, essSup_eq, h.comp, h_top, if_false, if_true, lintegral_eq, measurable_coe_nnreal_ennreal, measurable_coe_nnreal_ennreal.comp, measurable_nnnorm, one_div, p.toReal, pow_const, toReal
-/
theorem eLpNorm_eq [NormedAddCommGroup γ] [OpensMeasurableSpace γ] (h : IdentDistrib f g μ ν)
    (p : Real>=0∞) : eLpNorm f p μ = eLpNorm g p ν := by
  by_cases h0 : p = 0
  · simp [h0]
  by_cases h_top : p = ∞
  · simp only [h_top, eLpNorm, eLpNormEssSup, ENNReal.top_ne_zero, if_true,
      if_false]
    apply essSup_eq
    exact h.comp (measurable_coe_nnreal_ennreal.comp measurable_nnnorm)
  simp only [eLpNorm_eq_eLpNorm' h0 h_top, eLpNorm', one_div]
  congr 1
  apply lintegral_eq
  exact h.comp (Measurable.pow_const (measurable_coe_nnreal_ennreal.comp measurable_nnnorm)
    p.toReal)

/--
theorem `memLp_snd` / 定理 `memLp_snd`

English:
theorem memLp_snd
  statement: [NormedAddCommGroup γ] [BorelSpace γ] {p : Real>=0∞} (h : IdentDistrib f g μ ν)
  proof: by
  refine ⟨h.aestronglyMeasurable_snd hf.aestronglyMeasurable, ?_⟩
  rw [← h.eLpNorm_eq]
  exact hf.2

中文:
定理 memLp_snd
  结论: [赋范交换加群 γ] [Borel空间 γ] {p : 实数>=0∞} (h : 同分布 f g μ ν)
  证明: by
  refine ⟨h.aestronglyMeasurable_snd hf.aestronglyMeasurable, ?_⟩
  rw [← h.eLpNorm_eq]
  exact hf.2

Depends on / 依赖: aestronglyMeasurable, aestronglyMeasurable_snd, eLpNorm_eq, h.aestronglyMeasurable_snd, h.eLpNorm_eq, hf.aestronglyMeasurable
-/
theorem memLp_snd [NormedAddCommGroup γ] [BorelSpace γ] {p : Real>=0∞} (h : IdentDistrib f g μ ν)
    (hf : MemLp f p μ) : MemLp g p ν := by
  refine ⟨h.aestronglyMeasurable_snd hf.aestronglyMeasurable, ?_⟩
  rw [← h.eLpNorm_eq]
  exact hf.2

/--
theorem `memLp_iff` / 定理 `memLp_iff`

English:
theorem memLp_iff
  given: [NormedAddCommGroup γ] [BorelSpace γ] {p : Real>=0∞} (h : IdentDistrib f g μ ν)
  proof: ⟨fun hf => h.memLp_snd hf, fun hg => h.symm.memLp_snd hg⟩

中文:
定理 memLp_iff
  条件: [赋范交换加群 γ] [Borel空间 γ] {p : 实数>=0∞} (h : 同分布 f g μ ν)
  证明: ⟨fun hf => h.memLp_snd hf, fun hg => h.symm.memLp_snd hg⟩

Depends on / 依赖: h.memLp_snd, h.symm.memLp_snd, memLp_snd
-/
theorem memLp_iff [NormedAddCommGroup γ] [BorelSpace γ] {p : Real>=0∞} (h : IdentDistrib f g μ ν) :
    MemLp f p μ ↔ MemLp g p ν :=
  ⟨fun hf => h.memLp_snd hf, fun hg => h.symm.memLp_snd hg⟩

/--
theorem `integrable_snd` / 定理 `integrable_snd`

English:
theorem integrable_snd
  statement: [NormedAddCommGroup γ] [BorelSpace γ] (h : IdentDistrib f g μ ν)
  proof: by
  rw [← memLp_one_iff_integrable] at hf ⊢
  exact h.memLp_snd hf

中文:
定理 integrable_snd
  结论: [赋范交换加群 γ] [Borel空间 γ] (h : 同分布 f g μ ν)
  证明: by
  rw [← memLp_one_iff_integrable] at hf ⊢
  exact h.memLp_snd hf

Depends on / 依赖: h.memLp_snd, memLp_one_iff_integrable, memLp_snd
-/
theorem integrable_snd [NormedAddCommGroup γ] [BorelSpace γ] (h : IdentDistrib f g μ ν)
    (hf : Integrable f μ) : Integrable g ν := by
  rw [← memLp_one_iff_integrable] at hf ⊢
  exact h.memLp_snd hf

/--
theorem `integrable_iff` / 定理 `integrable_iff`

English:
theorem integrable_iff
  given: [NormedAddCommGroup γ] [BorelSpace γ] (h : IdentDistrib f g μ ν)
  proof: ⟨fun hf => h.integrable_snd hf, fun hg => h.symm.integrable_snd hg⟩

中文:
定理 integrable_iff
  条件: [赋范交换加群 γ] [Borel空间 γ] (h : 同分布 f g μ ν)
  证明: ⟨fun hf => h.integrable_snd hf, fun hg => h.symm.integrable_snd hg⟩

Depends on / 依赖: h.integrable_snd, h.symm.integrable_snd, integrable_snd
-/
theorem integrable_iff [NormedAddCommGroup γ] [BorelSpace γ] (h : IdentDistrib f g μ ν) :
    Integrable f μ ↔ Integrable g ν :=
  ⟨fun hf => h.integrable_snd hf, fun hg => h.symm.integrable_snd hg⟩

/--
theorem `norm` / 定理 `norm`

English:
theorem norm
  given: [NormedAddCommGroup γ] [OpensMeasurableSpace γ] (h : IdentDistrib f g μ ν)
  proof: h.comp measurable_norm

中文:
定理 norm
  条件: [赋范交换加群 γ] [OpensMeasurable空间 γ] (h : 同分布 f g μ ν)
  证明: h.comp measurable_norm
-/
protected theorem norm [NormedAddCommGroup γ] [OpensMeasurableSpace γ] (h : IdentDistrib f g μ ν) :
    IdentDistrib (fun x => ‖f x‖) (fun x => ‖g x‖) μ ν :=
  h.comp measurable_norm

/--
theorem `nnnorm` / 定理 `nnnorm`

English:
theorem nnnorm
  statement: [NormedAddCommGroup γ] [OpensMeasurableSpace γ]
  proof: h.comp measurable_nnnorm

中文:
定理 nnnorm
  结论: [赋范交换加群 γ] [OpensMeasurable空间 γ]
  证明: h.comp measurable_nnnorm
-/
protected theorem nnnorm [NormedAddCommGroup γ] [OpensMeasurableSpace γ]
    (h : IdentDistrib f g μ ν) :
    IdentDistrib (fun x => ‖f x‖₊) (fun x => ‖g x‖₊) μ ν :=
  h.comp measurable_nnnorm

/--
theorem `pow` / 定理 `pow`

English:
theorem pow
  given: [Pow γ Nat] [MeasurablePow γ Nat] (h : IdentDistrib f g μ ν) {n : Nat}
  proof: h.comp (measurable_id.pow_const n)

中文:
定理 pow
  条件: [幂 γ 自然数] [MeasurablePow γ 自然数] (h : 同分布 f g μ ν) {n : 自然数}
  证明: h.comp (measurable_id.pow_const n)
-/
protected theorem pow [Pow γ Nat] [MeasurablePow γ Nat] (h : IdentDistrib f g μ ν) {n : Nat} :
    IdentDistrib (fun x => f x ^ n) (fun x => g x ^ n) μ ν :=
  h.comp (measurable_id.pow_const n)

/--
theorem `sq` / 定理 `sq`

English:
theorem sq
  given: [Pow γ Nat] [MeasurablePow γ Nat] (h : IdentDistrib f g μ ν)
  proof: h.comp (measurable_id.pow_const 2)

中文:
定理 sq
  条件: [幂 γ 自然数] [MeasurablePow γ 自然数] (h : 同分布 f g μ ν)
  证明: h.comp (measurable_id.pow_const 2)
-/
protected theorem sq [Pow γ Nat] [MeasurablePow γ Nat] (h : IdentDistrib f g μ ν) :
    IdentDistrib (fun x => f x ^ 2) (fun x => g x ^ 2) μ ν :=
  h.comp (measurable_id.pow_const 2)

/--
theorem `coe_nnreal_ennreal` / 定理 `coe_nnreal_ennreal`

English:
theorem coe_nnreal_ennreal
  given: {f : α -> Real>=0} {g : β -> Real>=0} (h : IdentDistrib f g μ ν)
  proof: h.comp measurable_coe_nnreal_ennreal

@[to_additive]

中文:
定理 coe_nnreal_ennreal
  条件: {f : α -> 实数>=0} {g : β -> 实数>=0} (h : 同分布 f g μ ν)
  证明: h.comp measurable_coe_nnreal_ennreal

@[to_additive]
-/
protected theorem coe_nnreal_ennreal {f : α -> Real>=0} {g : β -> Real>=0} (h : IdentDistrib f g μ ν) :
    IdentDistrib (fun x => (f x : Real>=0∞)) (fun x => (g x : Real>=0∞)) μ ν :=
  h.comp measurable_coe_nnreal_ennreal

@[to_additive]
/--
theorem `mul_const` / 定理 `mul_const`

English:
theorem mul_const
  given: [Mul γ] [MeasurableMul γ] (h : IdentDistrib f g μ ν) (c : γ)
  proof: h.comp (measurable_mul_const c)

@[to_additive]

中文:
定理 mul_const
  条件: [乘法 γ] [MeasurableMul γ] (h : 同分布 f g μ ν) (c : γ)
  证明: h.comp (measurable_mul_const c)

@[to_additive]

Depends on / 依赖: h.comp, measurable_mul_const
-/
theorem mul_const [Mul γ] [MeasurableMul γ] (h : IdentDistrib f g μ ν) (c : γ) :
    IdentDistrib (fun x => f x * c) (fun x => g x * c) μ ν :=
  h.comp (measurable_mul_const c)

@[to_additive]
/--
theorem `const_mul` / 定理 `const_mul`

English:
theorem const_mul
  given: [Mul γ] [MeasurableMul γ] (h : IdentDistrib f g μ ν) (c : γ)
  proof: h.comp (measurable_const_mul c)

@[to_additive]

中文:
定理 const_mul
  条件: [乘法 γ] [MeasurableMul γ] (h : 同分布 f g μ ν) (c : γ)
  证明: h.comp (measurable_const_mul c)

@[to_additive]

Depends on / 依赖: h.comp, measurable_const_mul
-/
theorem const_mul [Mul γ] [MeasurableMul γ] (h : IdentDistrib f g μ ν) (c : γ) :
    IdentDistrib (fun x => c * f x) (fun x => c * g x) μ ν :=
  h.comp (measurable_const_mul c)

@[to_additive]
/--
theorem `div_const` / 定理 `div_const`

English:
theorem div_const
  given: [Div γ] [MeasurableDiv γ] (h : IdentDistrib f g μ ν) (c : γ)
  proof: h.comp (MeasurableDiv.measurable_div_const c)

@[to_additive]

中文:
定理 div_const
  条件: [除法 γ] [MeasurableDiv γ] (h : 同分布 f g μ ν) (c : γ)
  证明: h.comp (MeasurableDiv.measurable_div_const c)

@[to_additive]

Depends on / 依赖: MeasurableDiv, MeasurableDiv.measurable_div_const, h.comp, measurable_div_const
-/
theorem div_const [Div γ] [MeasurableDiv γ] (h : IdentDistrib f g μ ν) (c : γ) :
    IdentDistrib (fun x => f x / c) (fun x => g x / c) μ ν :=
  h.comp (MeasurableDiv.measurable_div_const c)

@[to_additive]
/--
theorem `const_div` / 定理 `const_div`

English:
theorem const_div
  given: [Div γ] [MeasurableDiv γ] (h : IdentDistrib f g μ ν) (c : γ)
  proof: h.comp (MeasurableDiv.measurable_const_div c)

@[to_additive]

中文:
定理 const_div
  条件: [除法 γ] [MeasurableDiv γ] (h : 同分布 f g μ ν) (c : γ)
  证明: h.comp (MeasurableDiv.measurable_const_div c)

@[to_additive]

Depends on / 依赖: MeasurableDiv, MeasurableDiv.measurable_const_div, h.comp, measurable_const_div
-/
theorem const_div [Div γ] [MeasurableDiv γ] (h : IdentDistrib f g μ ν) (c : γ) :
    IdentDistrib (fun x => c / f x) (fun x => c / g x) μ ν :=
  h.comp (MeasurableDiv.measurable_const_div c)

@[to_additive]
/--
lemma `inv` / 引理 `inv`

English:
lemma inv
  given: [Inv γ] [MeasurableInv γ] (h : IdentDistrib f g μ ν)
  proof: h.comp measurable_inv

中文:
引理 inv
  条件: [取逆 γ] [MeasurableInv γ] (h : 同分布 f g μ ν)
  证明: h.comp measurable_inv

Depends on / 依赖: h.comp, measurable_inv
-/
lemma inv [Inv γ] [MeasurableInv γ] (h : IdentDistrib f g μ ν) :
    IdentDistrib f⁻¹ g⁻¹ μ ν := h.comp measurable_inv

/--
theorem `evariance_eq` / 定理 `evariance_eq`

English:
theorem evariance_eq
  given: {f : α -> Real} {g : β -> Real} (h : IdentDistrib f g μ ν)
  proof: by
  convert! (h.sub_const (∫ x, f x ∂μ)).nnnorm.coe_nnreal_ennreal.sq.lintegral_eq
  rw [h.integral_eq]
  rfl

中文:
定理 evariance_eq
  条件: {f : α -> 实数} {g : β -> 实数} (h : 同分布 f g μ ν)
  证明: by
  convert! (h.sub_const (∫ x, f x ∂μ)).nnnorm.coe_nnreal_ennreal.sq.lintegral_eq
  rw [h.integral_eq]
  rfl

Depends on / 依赖: coe_nnreal_ennreal, convert, h.integral_eq, h.sub_const, integral_eq, lintegral_eq, nnnorm, nnnorm.coe_nnreal_ennreal.sq.lintegral_eq, sub_const
-/
theorem evariance_eq {f : α -> Real} {g : β -> Real} (h : IdentDistrib f g μ ν) :
    evariance f μ = evariance g ν := by
  convert! (h.sub_const (∫ x, f x ∂μ)).nnnorm.coe_nnreal_ennreal.sq.lintegral_eq
  rw [h.integral_eq]
  rfl

/--
theorem `variance_eq` / 定理 `variance_eq`

English:
theorem variance_eq
  given: {f : α -> Real} {g : β -> Real} (h : IdentDistrib f g μ ν)
  proof: by rw [variance, h.evariance_eq]; rfl

中文:
定理 variance_eq
  条件: {f : α -> 实数} {g : β -> 实数} (h : 同分布 f g μ ν)
  证明: by rw [variance, h.evariance_eq]; rfl

Depends on / 依赖: evariance_eq, h.evariance_eq, variance
-/
theorem variance_eq {f : α -> Real} {g : β -> Real} (h : IdentDistrib f g μ ν) :
    variance f μ = variance g ν := by rw [variance, h.evariance_eq]; rfl

end IdentDistrib

section UniformIntegrable

open TopologicalSpace

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]
  {μ : Measure α} [IsFiniteMeasure μ]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `MemLp.uniformIntegrable_of_identDistrib_aux` / 定理 `MemLp.uniformIntegrable_of_identDistrib_aux`

English:
theorem MemLp.uniformIntegrable_of_identDistrib_aux
  statement: {ι : Type*} {f : ι -> α -> E} {j : ι} {p : Real>=0∞}
  proof: by
  refine uniformIntegrable_of' hp hp' hfmeas fun ε hε => ?_
  by_cases hι : Nonempty ι
  swap; · exact ⟨0, fun i => False.elim (hι <| Nonempty.intro i)⟩
  obtain ⟨C, hC₁, hC₂⟩ := hℒp.eLpNorm_indicator_norm_ge_pos_le (hfmeas _) hε
  refine ⟨⟨C, hC₁.le⟩, fun i => le_trans (le_of_eq ?_) hC₂⟩
  have 

中文:
定理 MemLp.uniform整数egrable_of_identDistrib_aux
  结论: {ι : 类型} {f : ι -> α -> E} {j : ι} {p : 实数>=0∞}
  证明: by
  refine uniformIntegrable_of' hp hp' hfmeas fun ε hε => ?_
  by_cases hι : Nonempty ι
  swap; · exact ⟨0, fun i => False.elim (hι <| Nonempty.intro i)⟩
  obtain ⟨C, hC₁, hC₂⟩ := hℒp.eLpNorm_indicator_norm_ge_pos_le (hfmeas _) hε
  refine ⟨⟨C, hC₁.le⟩, fun i => le_trans (le_of_eq ?_) hC₂⟩
  have 

Depends on / 依赖: False.elim, Nonempty, Nonempty.intro, Real.le_toNNReal_iff_coe_le, Set.ind, eLpNorm_indicator_norm_ge_pos_le, eLpNorm_norm, hfmeas, le_of_eq, le_toNNReal_iff_coe_le, le_trans, norm_nonneg, norm_toNNReal, p.eLpNorm_indicator_norm_ge_pos_le, simp_rw, uniformIntegrable_of
-/
theorem MemLp.uniformIntegrable_of_identDistrib_aux {ι : Type*} {f : ι -> α -> E} {j : ι} {p : Real>=0∞}
    (hp : 1 <= p) (hp' : p != ∞) (hℒp : MemLp (f j) p μ) (hfmeas : forall i, StronglyMeasurable (f i))
    (hf : forall i, IdentDistrib (f i) (f j) μ μ) : UniformIntegrable f p μ := by
  refine uniformIntegrable_of' hp hp' hfmeas fun ε hε => ?_
  by_cases hι : Nonempty ι
  swap; · exact ⟨0, fun i => False.elim (hι <| Nonempty.intro i)⟩
  obtain ⟨C, hC₁, hC₂⟩ := hℒp.eLpNorm_indicator_norm_ge_pos_le (hfmeas _) hε
  refine ⟨⟨C, hC₁.le⟩, fun i => le_trans (le_of_eq ?_) hC₂⟩
  have : {x | (⟨C, hC₁.le⟩ : Real>=0) <= ‖f i x‖₊} = {x | C <= ‖f i x‖} := by
    ext x
    simp_rw [← norm_toNNReal]
    exact Real.le_toNNReal_iff_coe_le (norm_nonneg _)
  rw [this]; rw [← eLpNorm_norm]; rw [← eLpNorm_norm (Set.indicator _ _)]
  simp_rw [norm_indicator_eq_indicator_norm, coe_nnnorm]
  let F : E -> Real := (fun x : E => if (⟨C, hC₁.le⟩ : Real>=0) <= ‖x‖₊ then ‖x‖ else 0)
  have F_meas : Measurable F := by
    apply measurable_norm.indicator (measurableSet_le measurable_const measurable_nnnorm)
  have : forall k, (fun x => Set.indicator {x | C <= ‖f k x‖} (fun a => ‖f k a‖) x) = F ∘ f k := by
    intro k
    ext x
    simp only [Set.indicator, Set.mem_ofPred_eq]; norm_cast
  rw [this]; rw [this]; rw [← eLpNorm_map_measure F_meas.aestronglyMeasurable (hf i).aemeasurable_fst]; rw [(hf i).map_eq]; rw [eLpNorm_map_measure F_meas.aestronglyMeasurable (hf j).aemeasurable_fst]

/--
theorem `MemLp.uniformIntegrable_of_identDistrib` / 定理 `MemLp.uniformIntegrable_of_identDistrib`

English:
theorem MemLp.uniformIntegrable_of_identDistrib
  statement: {ι : Type*} {f : ι -> α -> E} {j : ι} {p : Real>=0∞}
  proof: by
  have hfmeas : forall i, AEStronglyMeasurable (f i) μ := fun i =>
    (hf i).aestronglyMeasurable_iff.2 hℒp.1
  set g : ι -> α -> E := fun i => (hfmeas i).choose
  have hgmeas : forall i, StronglyMeasurable (g i) := fun i => (Exists.choose_spec <| hfmeas i).1
  have hgeq : forall i, g i =ᵐ[μ] f 

中文:
定理 MemLp.uniform整数egrable_of_identDistrib
  结论: {ι : 类型} {f : ι -> α -> E} {j : ι} {p : 实数>=0∞}
  证明: by
  have hfmeas : forall i, AEStronglyMeasurable (f i) μ := fun i =>
    (hf i).aestronglyMeasurable_iff.2 hℒp.1
  set g : ι -> α -> E := fun i => (hfmeas i).choose
  have hgmeas : forall i, StronglyMeasurable (g i) := fun i => (Exists.choose_spec <| hfmeas i).1
  have hgeq : forall i, g i =ᵐ[μ] f 

Depends on / 依赖: AEStronglyMeasurable, Exists, Exists.choose_spec, MemLp.uniformIntegrable_of_identDistrib_aux, StronglyMeasurable, UniformIntegrable, UniformIntegrable.ae_eq, ae_eq, aestronglyMeasurable_iff, choose_spec, hfmeas, hgmeas, p.ae_eq, uniformIntegrable_of_identDistrib_aux
-/
theorem MemLp.uniformIntegrable_of_identDistrib {ι : Type*} {f : ι -> α -> E} {j : ι} {p : Real>=0∞}
    (hp : 1 <= p) (hp' : p != ∞) (hℒp : MemLp (f j) p μ) (hf : forall i, IdentDistrib (f i) (f j) μ μ) :
    UniformIntegrable f p μ := by
  have hfmeas : forall i, AEStronglyMeasurable (f i) μ := fun i =>
    (hf i).aestronglyMeasurable_iff.2 hℒp.1
  set g : ι -> α -> E := fun i => (hfmeas i).choose
  have hgmeas : forall i, StronglyMeasurable (g i) := fun i => (Exists.choose_spec <| hfmeas i).1
  have hgeq : forall i, g i =ᵐ[μ] f i := fun i => (Exists.choose_spec <| hfmeas i).2.symm
  have hgℒp : MemLp (g j) p μ := hℒp.ae_eq (hgeq j).symm
  exact UniformIntegrable.ae_eq
    (MemLp.uniformIntegrable_of_identDistrib_aux hp hp' hgℒp hgmeas fun i =>
      (IdentDistrib.of_ae_eq (hgmeas i).aemeasurable (hgeq i)).trans
        ((hf i).trans <| IdentDistrib.of_ae_eq (hfmeas j).aemeasurable (hgeq j).symm)) hgeq

end UniformIntegrable

/--
lemma `indepFun_of_identDistrib_pair` / 引理 `indepFun_of_identDistrib_pair`

English:
lemma indepFun_of_identDistrib_pair
  proof: by
  rw [indepFun_iff_map_prod_eq_prod_map_map]; rw [← h_ident.map_eq]; rw [h_indep.map_prod_eq_prod_map_map]
  · exact congr (congrArg Measure.prod <| (h_ident.comp measurable_fst).map_eq)
      (h_ident.comp measurable_snd).map_eq
  · exact measurable_fst.aemeasurable.comp_aemeasurable h_ident.aem

中文:
引理 indepFun_of_identDistrib_pair
  证明: by
  rw [indepFun_iff_map_prod_eq_prod_map_map]; rw [← h_ident.map_eq]; rw [h_indep.map_prod_eq_prod_map_map]
  · exact congr (congrArg Measure.prod <| (h_ident.comp measurable_fst).map_eq)
      (h_ident.comp measurable_snd).map_eq
  · exact measurable_fst.aemeasurable.comp_aemeasurable h_ident.aem

Depends on / 依赖: Measure, Measure.prod, aemeasurable, aemeasurable_fst, aemeasurable_snd, comp_aemeasurable, h_ident, h_ident.aemeasurable_fst, h_ident.aemeasurable_snd, h_ident.comp, h_ident.map_eq, h_indep, h_indep.map_prod_eq_prod_map_map, indepFun_iff_map_prod_eq_prod_map_map, map_eq, map_prod_eq_prod_map_map, measurable_fst, measurable_fst.aemeasurable.comp_aemeasurable, measurable_snd, measurable_snd.aemeasurable.comp
-/
lemma indepFun_of_identDistrib_pair
    {μ : Measure γ} {μ' : Measure δ} [IsFiniteMeasure μ] [IsFiniteMeasure μ']
    {X : γ -> α} {X' : δ -> α} {Y : γ -> β} {Y' : δ -> β} (h_indep : X ⟂ᵢ[μ] Y)
    (h_ident : IdentDistrib (fun ω => (X ω, Y ω)) (fun ω => (X' ω, Y' ω)) μ μ') :
    X' ⟂ᵢ[μ'] Y' := by
  rw [indepFun_iff_map_prod_eq_prod_map_map]; rw [← h_ident.map_eq]; rw [h_indep.map_prod_eq_prod_map_map]
  · exact congr (congrArg Measure.prod <| (h_ident.comp measurable_fst).map_eq)
      (h_ident.comp measurable_snd).map_eq
  · exact measurable_fst.aemeasurable.comp_aemeasurable h_ident.aemeasurable_fst
  · exact measurable_snd.aemeasurable.comp_aemeasurable h_ident.aemeasurable_fst
  · exact measurable_fst.aemeasurable.comp_aemeasurable h_ident.aemeasurable_snd
  · exact measurable_snd.aemeasurable.comp_aemeasurable h_ident.aemeasurable_snd

end ProbabilityTheory
