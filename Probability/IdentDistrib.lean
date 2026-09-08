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

/-- Two functions defined on two (possibly different) measure spaces are identically distributed if
their image measures coincide. This only makes sense when the functions are ae measurable
(as otherwise the image measures are not defined), so we require this as well in the definition. -/
/-
**ProbabilityTheory.IdentDistrib** 是 Mathlib 中的一个结构，位于命名空间 `ProbabilityTheory`。
形式化陈述：IdentDistrib (f : α -> γ) (g : β -> γ) (μ : Measure α
参数：f : α -> γ；g : β -> γ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two functions defined on two (possibly different) measure spaces are identically
 distributed if
their image measures coincide. This only makes sense when the functions are ae m
easurable
(as otherwise the image measures are not defined), so we require this as well in
 the definition.
-/
structure IdentDistrib (f : α → γ) (g : β → γ)
    (μ : Measure α := by volume_tac)
    (ν : Measure β := by volume_tac) : Prop where
  aemeasurable_fst : AEMeasurable f μ
  aemeasurable_snd : AEMeasurable g ν
  map_eq : Measure.map f μ = Measure.map g ν

namespace IdentDistrib

open TopologicalSpace

variable {μ : Measure α} {ν : Measure β} {f : α → γ} {g : β → γ}

/-
**ProbabilityTheory.IdentDistrib.refl** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheo
ry.IdentDistrib`。
形式化陈述：∀ {α : Type u_1} {γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : Measu
rableSpace γ] {μ : MeasureTheory.Measure α}   {f : α → γ}, AEMeasurable f μ → Pr
obabilityTheory.IdentDistrib f f μ μ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem refl (hf : AEMeasurable f μ) : IdentDistrib f f μ μ :=
  { aemeasurable_fst := hf
    aemeasurable_snd := hf
    map_eq := rfl }
/-
**ProbabilityTheory.IdentDistrib.symm** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheo
ry.IdentDistrib`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : MeasurableSpace α] 
[inst_1 : MeasurableSpace β]   [inst_2 : MeasurableSpace γ] {μ : MeasureTheory.M
easure α} {ν : MeasureTheory.Measure β} {f : α → γ} {g : β → γ},   ProbabilityTh
eory.IdentDistrib f g μ ν → ProbabilityTheory.IdentDistrib g f ν μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IdentDistrib.aemeasurable_snd`：∀ {α : Type u_1} {β : T
ype u_2} {γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] 
  [inst_2 : MeasurableSpace γ] {f : α…
· 使用定理 `ProbabilityTheory.IdentDistrib.aemeasurable_fst`：∀ {α : Type u_1} {β : T
ype u_2} {γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] 
  [inst_2 : MeasurableSpace γ] {f : α…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.IdentDistrib.map_eq`：∀ {α : Type u_1} {β : Type u_2} {
γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 
: MeasurableSpace γ] {f : α…
-/
protected theorem symm (h : IdentDistrib f g μ ν) : IdentDistrib g f ν μ :=
  { aemeasurable_fst := h.aemeasurable_snd
    aemeasurable_snd := h.aemeasurable_fst
    map_eq := h.map_eq.symm }
/-
**ProbabilityTheory.IdentDistrib.trans** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityThe
ory.IdentDistrib`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} [inst : Meas
urableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 : MeasurableSpace γ] [inst
_3 : MeasurableSpace δ] {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure
 β}   {f : α → γ} {g : β → γ} {ρ : MeasureTheory.Measure δ} {h : δ → γ},   Proba
bilityTheory.IdentDistrib f g μ ν →     ProbabilityTheory.IdentDistrib g h ν ρ →
 ProbabilityTheory.IdentDistrib f h μ ρ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IdentDistrib.aemeasurable_fst`：∀ {α : Type u_1} {β : T
ype u_2} {γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] 
  [inst_2 : MeasurableSpace γ] {f : α…
· 使用定理 `ProbabilityTheory.IdentDistrib.aemeasurable_snd`：∀ {α : Type u_1} {β : T
ype u_2} {γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] 
  [inst_2 : MeasurableSpace γ] {f : α…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ProbabilityTheory.IdentDistrib.map_eq`：∀ {α : Type u_1} {β : Type u_2} {
γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 
: MeasurableSpace γ] {f : α…
-/
protected theorem trans {ρ : Measure δ} {h : δ → γ} (h₁ : IdentDistrib f g μ ν)
    (h₂ : IdentDistrib g h ν ρ) : IdentDistrib f h μ ρ :=
  { aemeasurable_fst := h₁.aemeasurable_fst
    aemeasurable_snd := h₂.aemeasurable_snd
    map_eq := h₁.map_eq.trans h₂.map_eq }
/-
**ProbabilityTheory.IdentDistrib.comp_of_aemeasurable** 是 Mathlib 中的一个定理，位于命名空间 
`ProbabilityTheory.IdentDistrib`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} [inst : Meas
urableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 : MeasurableSpace γ] [inst
_3 : MeasurableSpace δ] {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure
 β}   {f : α → γ} {g : β → γ} {u : γ → δ},   ProbabilityTheory.IdentDistrib f g 
μ ν →     AEMeasurable u (MeasureTheory.Measure.map f μ) → ProbabilityTheory.Ide
ntDistrib (u ∘ f) (u ∘ g) μ ν
参数：MeasureTheory.Measure.map f μ；u ∘ f；u ∘ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AEMeasurable.comp_aemeasurable`：comp_aemeasurable {f : α -> δ} {g : δ ->
 β} (hg : AEMeasurable g (μ.map f)) (hf : AEMeasurable f μ) : AEMeasurable (g ∘ 
f) μ
· 使用定理 `ProbabilityTheory.IdentDistrib.aemeasurable_fst`：∀ {α : Type u_1} {β : T
ype u_2} {γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] 
  [inst_2 : MeasurableSpace γ] {f : α…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.IdentDistrib.map_eq`：∀ {α : Type u_1} {β : Type u_2} {
γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 
: MeasurableSpace γ] {f : α…
· 使用定理 `ProbabilityTheory.IdentDistrib.aemeasurable_snd`：∀ {α : Type u_1} {β : T
ype u_2} {γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] 
  [inst_2 : MeasurableSpace γ] {f : α…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AEMeasurable.map_map_of_aemeasurable`：map_map_of_aemeasurable {g : β -> 
γ} {f : α -> β} (hg : AEMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) 
: (μ.map f).map g = μ.map …
-/
protected theorem comp_of_aemeasurable {u : γ → δ} (h : IdentDistrib f g μ ν)
    (hu : AEMeasurable u (Measure.map f μ)) : IdentDistrib (u ∘ f) (u ∘ g) μ ν :=
  { aemeasurable_fst := hu.comp_aemeasurable h.aemeasurable_fst
    aemeasurable_snd := by rw [h.map_eq] at hu; exact hu.comp_aemeasurable h.aemeasurable_snd
    map_eq := by
      rw [← AEMeasurable.map_map_of_aemeasurable hu h.aemeasurable_fst, ←
        AEMeasurable.map_map_of_aemeasurable _ h.aemeasurable_snd, h.map_eq]
      rwa [← h.map_eq] }
/-
**ProbabilityTheory.IdentDistrib.comp** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheo
ry.IdentDistrib`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} [inst : Meas
urableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 : MeasurableSpace γ] [inst
_3 : MeasurableSpace δ] {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure
 β}   {f : α → γ} {g : β → γ} {u : γ → δ},   ProbabilityTheory.IdentDistrib f g 
μ ν → Measurable u → ProbabilityTheory.IdentDistrib (u ∘ f) (u ∘ g) μ ν
参数：u ∘ f；u ∘ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IdentDistrib.comp_of_aemeasurable`：∀ {α : Type u_1} {β
 : Type u_2} {γ : Type u_3} {δ : Type u_4} [inst : MeasurableSpace α] [inst_1 : 
MeasurableSpace β]   [inst_2 : Measurable…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
-/
protected theorem comp {u : γ → δ} (h : IdentDistrib f g μ ν) (hu : Measurable u) :
    IdentDistrib (u ∘ f) (u ∘ g) μ ν :=
  h.comp_of_aemeasurable hu.aemeasurable
/-
**ProbabilityTheory.IdentDistrib.of_ae_eq** 是 Mathlib 中的一个定理，位于命名空间 `Probability
Theory.IdentDistrib`。
形式化陈述：∀ {α : Type u_1} {γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : Measu
rableSpace γ] {μ : MeasureTheory.Measure α}   {f g : α → γ}, AEMeasurable f μ → 
f =ᵐ[μ] g → ProbabilityTheory.IdentDistrib f g μ μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `AEMeasurable.congr`：congr (hf : AEMeasurable f μ) (h : f =ᵐ[μ] g) : AEMe
asurable g μ
· 使用定理 `MeasureTheory.Measure.map_congr`：map_congr {f g : α -> β} (h : f =ᵐ[μ] g
) : Measure.map f μ = Measure.map g μ
-/
protected theorem of_ae_eq {g : α → γ} (hf : AEMeasurable f μ) (heq : f =ᵐ[μ] g) :
    IdentDistrib f g μ μ :=
  { aemeasurable_fst := hf
    aemeasurable_snd := hf.congr heq
    map_eq := Measure.map_congr heq }
/-
**ProbabilityTheory.IdentDistrib._root_.MeasureTheory.AEMeasurable.identDistrib_
mk** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory.IdentDistrib`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MeasureTheory.AEMeasurable.identDistrib_mk
    (hf : AEMeasurable f μ) : IdentDistrib f (hf.mk f) μ μ :=
  IdentDistrib.of_ae_eq hf hf.ae_eq_mk
/-
**ProbabilityTheory.IdentDistrib._root_.MeasureTheory.AEStronglyMeasurable.ident
Distrib_mk** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory.IdentDistrib`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MeasureTheory.AEStronglyMeasurable.identDistrib_mk
    [TopologicalSpace γ] [PseudoMetrizableSpace γ] [BorelSpace γ]
    (hf : AEStronglyMeasurable f μ) : IdentDistrib f (hf.mk f) μ μ :=
  IdentDistrib.of_ae_eq hf.aemeasurable hf.ae_eq_mk
/-
**ProbabilityTheory.IdentDistrib.measure_mem_eq** 是 Mathlib 中的一个定理，位于命名空间 `Proba
bilityTheory.IdentDistrib`。
形式化陈述：measure_mem_eq (h : IdentDistrib f g μ ν) {s : Set γ} (hs : MeasurableSet 
s) : μ (f ⁻¹' s) = ν (g ⁻¹' s)
参数：h : IdentDistrib f g μ ν；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.map_apply_of_aemeasurable`：map_apply_of_aemeasurab
le (hf : AEMeasurable f μ) {s : Set β} (hs : MeasurableSet s) : μ.map f s = μ (f
 ⁻¹' s)
· 使用定理 `ProbabilityTheory.IdentDistrib.aemeasurable_fst`：∀ {α : Type u_1} {β : T
ype u_2} {γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] 
  [inst_2 : MeasurableSpace γ] {f : α…
· 使用定理 `ProbabilityTheory.IdentDistrib.aemeasurable_snd`：∀ {α : Type u_1} {β : T
ype u_2} {γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] 
  [inst_2 : MeasurableSpace γ] {f : α…
· 使用定理 `ProbabilityTheory.IdentDistrib.map_eq`：∀ {α : Type u_1} {β : Type u_2} {
γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 
: MeasurableSpace γ] {f : α…
-/
theorem measure_mem_eq (h : IdentDistrib f g μ ν) {s : Set γ} (hs : MeasurableSet s) :
    μ (f ⁻¹' s) = ν (g ⁻¹' s) := by
  rw [← Measure.map_apply_of_aemeasurable h.aemeasurable_fst hs, ←
    Measure.map_apply_of_aemeasurable h.aemeasurable_snd hs, h.map_eq]

alias measure_preimage_eq := measure_mem_eq
/-
**ProbabilityTheory.IdentDistrib.ae_snd** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTh
eory.IdentDistrib`。
形式化陈述：ae_snd (h : IdentDistrib f g μ ν) {p : γ -> Prop} (pmeas : MeasurableSet {
x | p x}) (hp : forallᵐ x ∂μ, p (f x)) : forallᵐ x ∂ν, p (g x)
参数：h : IdentDistrib f g μ ν；pmeas : MeasurableSet {x | p x}；hp : forallᵐ x ∂μ, p
 (f x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.ae_map_iff`：ae_map_iff {f : α -> β} (hf : AEMeasurable f μ
) {p : β -> Prop} (hp : MeasurableSet { x | p x }) : (forallᵐ y ∂μ.map f, p y) ↔
 forallᵐ x ∂μ,…
· 使用定理 `ProbabilityTheory.IdentDistrib.aemeasurable_snd`：∀ {α : Type u_1} {β : T
ype u_2} {γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] 
  [inst_2 : MeasurableSpace γ] {f : α…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.IdentDistrib.map_eq`：∀ {α : Type u_1} {β : Type u_2} {
γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 
: MeasurableSpace γ] {f : α…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ProbabilityTheory.IdentDistrib.aemeasurable_fst`：∀ {α : Type u_1} {β : T
ype u_2} {γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] 
  [inst_2 : MeasurableSpace γ] {f : α…
-/
theorem ae_snd (h : IdentDistrib f g μ ν) {p : γ → Prop} (pmeas : MeasurableSet {x | p x})
    (hp : ∀ᵐ x ∂μ, p (f x)) : ∀ᵐ x ∂ν, p (g x) := by
  apply (ae_map_iff h.aemeasurable_snd pmeas).1
  rw [← h.map_eq]
  exact (ae_map_iff h.aemeasurable_fst pmeas).2 hp
/-
**ProbabilityTheory.IdentDistrib.ae_mem_snd** 是 Mathlib 中的一个定理，位于命名空间 `Probabili
tyTheory.IdentDistrib`。
形式化陈述：ae_mem_snd (h : IdentDistrib f g μ ν) {t : Set γ} (tmeas : MeasurableSet t
) (ht : forallᵐ x ∂μ, f x in t) : forallᵐ x ∂ν, g x in t
参数：h : IdentDistrib f g μ ν；tmeas : MeasurableSet t；ht : forallᵐ x ∂μ, f x in t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.IdentDistrib.ae_snd`：ae_snd (h : IdentDistrib f g μ ν)
 {p : γ -> Prop} (pmeas : MeasurableSet {x | p x}) (hp : forallᵐ x ∂μ, p (f x)) 
: forallᵐ x ∂ν, p (g x)
-/
theorem ae_mem_snd (h : IdentDistrib f g μ ν) {t : Set γ} (tmeas : MeasurableSet t)
    (ht : ∀ᵐ x ∂μ, f x ∈ t) : ∀ᵐ x ∂ν, g x ∈ t :=
  h.ae_snd tmeas ht
/-
**ProbabilityTheory.IdentDistrib._root_.ProbabilityTheory.HasLaw.identDistrib** 
是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory.IdentDistrib`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.ProbabilityTheory.HasLaw.identDistrib {κ : Measure γ} (h₀ : HasLaw f κ μ)
    (h₁ : HasLaw g κ ν) : IdentDistrib f g μ ν :=
  ⟨h₀.aemeasurable, h₁.aemeasurable, by simp [h₀.map_eq, h₁.map_eq]⟩
/-
**ProbabilityTheory.IdentDistrib.hasLaw** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTh
eory.IdentDistrib`。
形式化陈述：hasLaw {κ : Measure γ} (h₀ : IdentDistrib f g μ ν) (h₁ : HasLaw f κ μ) : H
asLaw g κ ν
参数：h₀ : IdentDistrib f g μ ν；h₁ : HasLaw f κ μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IdentDistrib.aemeasurable_snd`：∀ {α : Type u_1} {β : T
ype u_2} {γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] 
  [inst_2 : MeasurableSpace γ] {f : α…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.HasLaw.map_eq`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : M
easurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheory.Meas
ure 𝓧} {P : autoParam…
· 使用定理 `ProbabilityTheory.IdentDistrib.map_eq`：∀ {α : Type u_1} {β : Type u_2} {
γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 
: MeasurableSpace γ] {f : α…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem hasLaw {κ : Measure γ} (h₀ : IdentDistrib f g μ ν) (h₁ : HasLaw f κ μ) : HasLaw g κ ν :=
  ⟨h₀.aemeasurable_snd, by simp [h₀.map_eq, ← h₁.map_eq]⟩

/-- In a second countable topology, the first function in an identically distributed pair is a.e.
strongly measurable. So is the second function, but use `h.symm.aestronglyMeasurable_fst` as
`h.aestronglyMeasurable_snd` has a different meaning. -/
/-
**ProbabilityTheory.IdentDistrib.aestronglyMeasurable_fst** 是 Mathlib 中的一个定理，位于命
名空间 `ProbabilityTheory.IdentDistrib`。
形式化陈述：aestronglyMeasurable_fst [TopologicalSpace γ] [PseudoMetrizableSpace γ] [O
pensMeasurableSpace γ] [SecondCountableTopology γ] (h : IdentDistrib f g μ ν) : 
AEStronglyMeasurable f μ
参数：h : IdentDistrib f g μ ν。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AEMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst
 : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 : M…
· 使用定理 `ProbabilityTheory.IdentDistrib.aemeasurable_fst`：∀ {α : Type u_1} {β : T
ype u_2} {γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] 
  [inst_2 : MeasurableSpace γ] {f : α…

--- 原说明 ---
In a second countable topology, the first function in an identically distributed
 pair is a.e.
strongly measurable. So is the second function, but use `h.symm.aestronglyMeasur
able_fst` as
`h.aestronglyMeasurable_snd` has a different meaning.
-/
theorem aestronglyMeasurable_fst [TopologicalSpace γ] [PseudoMetrizableSpace γ]
    [OpensMeasurableSpace γ] [SecondCountableTopology γ] (h : IdentDistrib f g μ ν) :
    AEStronglyMeasurable f μ :=
  h.aemeasurable_fst.aestronglyMeasurable

/-- If `f` and `g` are identically distributed and `f` is a.e. strongly measurable, so is `g`. -/
/-
**ProbabilityTheory.IdentDistrib.aestronglyMeasurable_snd** 是 Mathlib 中的一个定理，位于命
名空间 `ProbabilityTheory.IdentDistrib`。
形式化陈述：aestronglyMeasurable_snd [TopologicalSpace γ] [PseudoMetrizableSpace γ] [B
orelSpace γ] (h : IdentDistrib f g μ ν) (hf : AEStronglyMeasurable f μ) : AEStro
nglyMeasurable g ν
参数：h : IdentDistrib f g μ ν；hf : AEStronglyMeasurable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `aestronglyMeasurable_iff_aemeasurable_separable`：∀ {α : Type u_1} {β : T
ype u_2} [inst : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory
.Measure α}   {f : α → β} [Topologica…
· 使用定理 `ProbabilityTheory.IdentDistrib.aemeasurable_snd`：∀ {α : Type u_1} {β : T
ype u_2} {γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] 
  [inst_2 : MeasurableSpace γ] {f : α…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `TopologicalSpace.IsSeparable.closure`：∀ {α : Type u} [t : TopologicalSpa
ce α] {s : Set α},   TopologicalSpace.IsSeparable s → TopologicalSpace.IsSeparab
le (closure s)
· 使用定理 `ProbabilityTheory.IdentDistrib.ae_mem_snd`：ae_mem_snd (h : IdentDistrib 
f g μ ν) {t : Set γ} (tmeas : MeasurableSet t) (ht : forallᵐ x ∂μ, f x in t) : f
orallᵐ x ∂ν, g x in t
· 使用定理 `IsClosed.measurableSet`：IsClosed.measurableSet (h : IsClosed s) : Measur
ableSet s
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s

--- 原说明 ---
If `f` and `g` are identically distributed and `f` is a.e. strongly measurable, 
so is `g`.
-/
theorem aestronglyMeasurable_snd [TopologicalSpace γ] [PseudoMetrizableSpace γ] [BorelSpace γ]
    (h : IdentDistrib f g μ ν) (hf : AEStronglyMeasurable f μ) : AEStronglyMeasurable g ν := by
  refine aestronglyMeasurable_iff_aemeasurable_separable.2 ⟨h.aemeasurable_snd, ?_⟩
  rcases (aestronglyMeasurable_iff_aemeasurable_separable.1 hf).2 with ⟨t, t_sep, ht⟩
  refine ⟨closure t, t_sep.closure, ?_⟩
  apply h.ae_mem_snd isClosed_closure.measurableSet
  filter_upwards [ht] with x hx using subset_closure hx
/-
**ProbabilityTheory.IdentDistrib.aestronglyMeasurable_iff** 是 Mathlib 中的一个定理，位于命
名空间 `ProbabilityTheory.IdentDistrib`。
形式化陈述：aestronglyMeasurable_iff [TopologicalSpace γ] [PseudoMetrizableSpace γ] [B
orelSpace γ] (h : IdentDistrib f g μ ν) : AEStronglyMeasurable f μ ↔ AEStronglyM
easurable g ν
参数：h : IdentDistrib f g μ ν。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IdentDistrib.aestronglyMeasurable_snd`：aestronglyMeasu
rable_snd [TopologicalSpace γ] [PseudoMetrizableSpace γ] [BorelSpace γ] (h : Ide
ntDistrib f g μ ν) (hf : AEStronglyMeasurable…
· 使用定理 `ProbabilityTheory.IdentDistrib.symm`：∀ {α : Type u_1} {β : Type u_2} {γ 
: Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 : 
MeasurableSpace γ] {μ : M…
-/
theorem aestronglyMeasurable_iff [TopologicalSpace γ] [PseudoMetrizableSpace γ] [BorelSpace γ]
    (h : IdentDistrib f g μ ν) : AEStronglyMeasurable f μ ↔ AEStronglyMeasurable g ν :=
  ⟨fun hf => h.aestronglyMeasurable_snd hf, fun hg => h.symm.aestronglyMeasurable_snd hg⟩
/-
**ProbabilityTheory.IdentDistrib.essSup_eq** 是 Mathlib 中的一个定理，位于命名空间 `Probabilit
yTheory.IdentDistrib`。
形式化陈述：essSup_eq [ConditionallyCompleteLinearOrder γ] [TopologicalSpace γ] [Opens
MeasurableSpace γ] [OrderClosedTopology γ] (h : IdentDistrib f g μ ν) : essSup f
 μ = essSup g ν
参数：h : IdentDistrib f g μ ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IdentDistrib.measure_mem_eq`：measure_mem_eq (h : Ident
Distrib f g μ ν) {s : Set γ} (hs : MeasurableSet s) : μ (f ⁻¹' s) = ν (g ⁻¹' s)
· 使用定理 `measurableSet_Ioi`：measurableSet_Ioi [ClosedIicTopology α] : MeasurableS
et (Ioi a)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `essSup_eq_sInf`：essSup_eq_sInf {m : MeasurableSpace α} (μ : Measure α) (
f : α -> β) : essSup f μ = sInf { a | μ { x | a < f x } = 0 }
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem essSup_eq [ConditionallyCompleteLinearOrder γ] [TopologicalSpace γ] [OpensMeasurableSpace γ]
    [OrderClosedTopology γ] (h : IdentDistrib f g μ ν) : essSup f μ = essSup g ν := by
  have I : ∀ a, μ {x : α | a < f x} = ν {x : β | a < g x} := fun a =>
    h.measure_mem_eq measurableSet_Ioi
  simp_rw [essSup_eq_sInf, I]
/-
**ProbabilityTheory.IdentDistrib.lintegral_eq** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory.IdentDistrib`。
形式化陈述：lintegral_eq {f : α -> Real>=0∞} {g : β -> Real>=0∞} (h : IdentDistrib f g
 μ ν) : ∫⁻ x, f x ∂μ = ∫⁻ x, g x ∂ν
参数：h : IdentDistrib f g μ ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_map'`：lintegral_map' {f : β -> Real>=0∞} {g : α 
-> β} (hf : AEMeasurable f (Measure.map g μ)) (hg : AEMeasurable g μ) : ∫⁻ a, f 
a ∂Measure.map g μ…
· 使用定理 `aemeasurable_id`：aemeasurable_id : AEMeasurable id μ
· 使用定理 `ProbabilityTheory.IdentDistrib.aemeasurable_fst`：∀ {α : Type u_1} {β : T
ype u_2} {γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] 
  [inst_2 : MeasurableSpace γ] {f : α…
· 使用定理 `ProbabilityTheory.IdentDistrib.aemeasurable_snd`：∀ {α : Type u_1} {β : T
ype u_2} {γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] 
  [inst_2 : MeasurableSpace γ] {f : α…
· 使用定理 `ProbabilityTheory.IdentDistrib.map_eq`：∀ {α : Type u_1} {β : Type u_2} {
γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 
: MeasurableSpace γ] {f : α…
-/
theorem lintegral_eq {f : α → ℝ≥0∞} {g : β → ℝ≥0∞} (h : IdentDistrib f g μ ν) :
    ∫⁻ x, f x ∂μ = ∫⁻ x, g x ∂ν := by
  change ∫⁻ x, id (f x) ∂μ = ∫⁻ x, id (g x) ∂ν
  rw [← lintegral_map' aemeasurable_id h.aemeasurable_fst, ←
    lintegral_map' aemeasurable_id h.aemeasurable_snd, h.map_eq]
/-
**ProbabilityTheory.IdentDistrib.integral_eq** 是 Mathlib 中的一个定理，位于命名空间 `Probabil
ityTheory.IdentDistrib`。
形式化陈述：integral_eq [NormedAddCommGroup γ] [NormedSpace Real γ] [BorelSpace γ] (h 
: IdentDistrib f g μ ν) : ∫ x, f x ∂μ = ∫ x, g x ∂ν
参数：h : IdentDistrib f g μ ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `aestronglyMeasurable_iff_aemeasurable_separable`：∀ {α : Type u_1} {β : T
ype u_2} [inst : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory
.Measure α}   {f : α → β} [Topologica…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `aemeasurable_id`：aemeasurable_id : AEMeasurable id μ
· 使用定理 `TopologicalSpace.IsSeparable.closure`：∀ {α : Type u} [t : TopologicalSpa
ce α] {s : Set α},   TopologicalSpace.IsSeparable s → TopologicalSpace.IsSeparab
le (closure s)
· 使用定理 `MeasureTheory.ae_map_iff`：ae_map_iff {f : α -> β} (hf : AEMeasurable f μ
) {p : β -> Prop} (hp : MeasurableSet { x | p x }) : (forallᵐ y ∂μ.map f, p y) ↔
 forallᵐ x ∂μ,…
· 使用定理 `ProbabilityTheory.IdentDistrib.aemeasurable_fst`：∀ {α : Type u_1} {β : T
ype u_2} {γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] 
  [inst_2 : MeasurableSpace γ] {f : α…
· 使用定理 `IsClosed.measurableSet`：IsClosed.measurableSet (h : IsClosed s) : Measur
ableSet s
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_map`：integral_map {β} [MeasurableSpace β] {φ : α 
-> β} (hφ : AEMeasurable φ μ) {f : β -> G} (hfm : AEStronglyMeasurable f (Measur
e.map φ μ)) : ∫ …
· 使用定理 `ProbabilityTheory.IdentDistrib.aemeasurable_snd`：∀ {α : Type u_1} {β : T
ype u_2} {γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] 
  [inst_2 : MeasurableSpace γ] {f : α…
· 使用定理 `ProbabilityTheory.IdentDistrib.map_eq`：∀ {α : Type u_1} {β : Type u_2} {
γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 
: MeasurableSpace γ] {f : α…
· 使用定理 `MeasureTheory.integral_non_aestronglyMeasurable`：integral_non_aestrongly
Measurable {f : α -> G} (h : ¬AEStronglyMeasurable f μ) : ∫ a, f a ∂μ = 0
· 使用定理 `ProbabilityTheory.IdentDistrib.aestronglyMeasurable_iff`：aestronglyMeasu
rable_iff [TopologicalSpace γ] [PseudoMetrizableSpace γ] [BorelSpace γ] (h : Ide
ntDistrib f g μ ν) : AEStronglyMeasurable f μ…
-/
theorem integral_eq [NormedAddCommGroup γ] [NormedSpace ℝ γ] [BorelSpace γ]
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
    rw [← integral_map h.aemeasurable_snd A, h.map_eq]
  · rw [integral_non_aestronglyMeasurable hf]
    rw [h.aestronglyMeasurable_iff] at hf
    rw [integral_non_aestronglyMeasurable hf]
/-
**ProbabilityTheory.IdentDistrib.eLpNorm_eq** 是 Mathlib 中的一个定理，位于命名空间 `Probabili
tyTheory.IdentDistrib`。
形式化陈述：eLpNorm_eq [NormedAddCommGroup γ] [OpensMeasurableSpace γ] (h : IdentDistr
ib f g μ ν) (p : Real>=0∞) : eLpNorm f p μ = eLpNorm g p ν
参数：h : IdentDistrib f g μ ν；p : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.eLpNorm_exponent_zero`：eLpNorm_exponent_zero {f : α -> ε} 
: eLpNorm f 0 μ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
· 使用定理 `if_false`：∀ {α : Sort u_1} {x : Decidable False} (t e : α), (if False th
en t else e) = e
· 使用定理 `ProbabilityTheory.IdentDistrib.essSup_eq`：essSup_eq [ConditionallyComple
teLinearOrder γ] [TopologicalSpace γ] [OpensMeasurableSpace γ] [OrderClosedTopol
ogy γ] (h : IdentDistrib f g μ…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `ProbabilityTheory.IdentDistrib.comp`：∀ {α : Type u_1} {β : Type u_2} {γ 
: Type u_3} {δ : Type u_4} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace 
β]   [inst_2 : Measurable…
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_coe_nnreal_ennreal`：measurable_coe_nnreal_ennreal : Measurabl
e ((↑) : Real>=0 -> Real>=0∞)
· 使用定理 `measurable_nnnorm`：measurable_nnnorm : Measurable (nnnorm : α -> Real>=0
)
· 使用定理 `MeasureTheory.eLpNorm_eq_eLpNorm'`：eLpNorm_eq_eLpNorm' (hp_ne_zero : p !
= 0) (hp_ne_top : p != ∞) {f : α -> ε} : eLpNorm f p μ = eLpNorm' f (ENNReal.toR
eal p) μ
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `ProbabilityTheory.IdentDistrib.lintegral_eq`：lintegral_eq {f : α -> Real
>=0∞} {g : β -> Real>=0∞} (h : IdentDistrib f g μ ν) : ∫⁻ x, f x ∂μ = ∫⁻ x, g x 
∂ν
· 使用定理 `Measurable.pow_const`：Measurable.pow_const (hf : Measurable f) (c : γ) :
 Measurable fun x => f x ^ c
-/
theorem eLpNorm_eq [NormedAddCommGroup γ] [OpensMeasurableSpace γ] (h : IdentDistrib f g μ ν)
    (p : ℝ≥0∞) : eLpNorm f p μ = eLpNorm g p ν := by
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
/-
**ProbabilityTheory.IdentDistrib.memLp_snd** 是 Mathlib 中的一个定理，位于命名空间 `Probabilit
yTheory.IdentDistrib`。
形式化陈述：memLp_snd [NormedAddCommGroup γ] [BorelSpace γ] {p : Real>=0∞} (h : IdentD
istrib f g μ ν) (hf : MemLp f p μ) : MemLp g p ν
参数：h : IdentDistrib f g μ ν；hf : MemLp f p μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IdentDistrib.aestronglyMeasurable_snd`：aestronglyMeasu
rable_snd [TopologicalSpace γ] [PseudoMetrizableSpace γ] [BorelSpace γ] (h : Ide
ntDistrib f g μ ν) (hf : AEStronglyMeasurable…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.MemLp.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Type u_2
} {m0 : MeasurableSpace α} [inst : ENorm ε] {μ : MeasureTheory.Measure α}   [ins
t_1 : TopologicalSpace ε] {f :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.IdentDistrib.eLpNorm_eq`：eLpNorm_eq [NormedAddCommGrou
p γ] [OpensMeasurableSpace γ] (h : IdentDistrib f g μ ν) (p : Real>=0∞) : eLpNor
m f p μ = eLpNorm g p ν
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem memLp_snd [NormedAddCommGroup γ] [BorelSpace γ] {p : ℝ≥0∞} (h : IdentDistrib f g μ ν)
    (hf : MemLp f p μ) : MemLp g p ν := by
  refine ⟨h.aestronglyMeasurable_snd hf.aestronglyMeasurable, ?_⟩
  rw [← h.eLpNorm_eq]
  exact hf.2
/-
**ProbabilityTheory.IdentDistrib.memLp_iff** 是 Mathlib 中的一个定理，位于命名空间 `Probabilit
yTheory.IdentDistrib`。
形式化陈述：memLp_iff [NormedAddCommGroup γ] [BorelSpace γ] {p : Real>=0∞} (h : IdentD
istrib f g μ ν) : MemLp f p μ ↔ MemLp g p ν
参数：h : IdentDistrib f g μ ν。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IdentDistrib.memLp_snd`：memLp_snd [NormedAddCommGroup 
γ] [BorelSpace γ] {p : Real>=0∞} (h : IdentDistrib f g μ ν) (hf : MemLp f p μ) :
 MemLp g p ν
· 使用定理 `ProbabilityTheory.IdentDistrib.symm`：∀ {α : Type u_1} {β : Type u_2} {γ 
: Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 : 
MeasurableSpace γ] {μ : M…
-/
theorem memLp_iff [NormedAddCommGroup γ] [BorelSpace γ] {p : ℝ≥0∞} (h : IdentDistrib f g μ ν) :
    MemLp f p μ ↔ MemLp g p ν :=
  ⟨fun hf => h.memLp_snd hf, fun hg => h.symm.memLp_snd hg⟩
/-
**ProbabilityTheory.IdentDistrib.integrable_snd** 是 Mathlib 中的一个定理，位于命名空间 `Proba
bilityTheory.IdentDistrib`。
形式化陈述：integrable_snd [NormedAddCommGroup γ] [BorelSpace γ] (h : IdentDistrib f g
 μ ν) (hf : Integrable f μ) : Integrable g ν
参数：h : IdentDistrib f g μ ν；hf : Integrable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `ProbabilityTheory.IdentDistrib.memLp_snd`：memLp_snd [NormedAddCommGroup 
γ] [BorelSpace γ] {p : Real>=0∞} (h : IdentDistrib f g μ ν) (hf : MemLp f p μ) :
 MemLp g p ν
-/
theorem integrable_snd [NormedAddCommGroup γ] [BorelSpace γ] (h : IdentDistrib f g μ ν)
    (hf : Integrable f μ) : Integrable g ν := by
  rw [← memLp_one_iff_integrable] at hf ⊢
  exact h.memLp_snd hf
/-
**ProbabilityTheory.IdentDistrib.integrable_iff** 是 Mathlib 中的一个定理，位于命名空间 `Proba
bilityTheory.IdentDistrib`。
形式化陈述：integrable_iff [NormedAddCommGroup γ] [BorelSpace γ] (h : IdentDistrib f g
 μ ν) : Integrable f μ ↔ Integrable g ν
参数：h : IdentDistrib f g μ ν。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IdentDistrib.integrable_snd`：integrable_snd [NormedAdd
CommGroup γ] [BorelSpace γ] (h : IdentDistrib f g μ ν) (hf : Integrable f μ) : I
ntegrable g ν
· 使用定理 `ProbabilityTheory.IdentDistrib.symm`：∀ {α : Type u_1} {β : Type u_2} {γ 
: Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 : 
MeasurableSpace γ] {μ : M…
-/
theorem integrable_iff [NormedAddCommGroup γ] [BorelSpace γ] (h : IdentDistrib f g μ ν) :
    Integrable f μ ↔ Integrable g ν :=
  ⟨fun hf => h.integrable_snd hf, fun hg => h.symm.integrable_snd hg⟩
/-
**ProbabilityTheory.IdentDistrib.norm** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheo
ry.IdentDistrib`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : MeasurableSpace α] 
[inst_1 : MeasurableSpace β]   [inst_2 : MeasurableSpace γ] {μ : MeasureTheory.M
easure α} {ν : MeasureTheory.Measure β} {f : α → γ} {g : β → γ}   [inst_3 : Norm
edAddCommGroup γ] [OpensMeasurableSpace γ],   ProbabilityTheory.IdentDistrib f g
 μ ν → ProbabilityTheory.IdentDistrib (fun x => ‖f x‖) (fun x => ‖g x‖) μ ν
参数：fun x => ‖f x‖；fun x => ‖g x‖。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IdentDistrib.comp`：∀ {α : Type u_1} {β : Type u_2} {γ 
: Type u_3} {δ : Type u_4} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace 
β]   [inst_2 : Measurable…
· 使用定理 `measurable_norm`：measurable_norm : Measurable (norm : α -> Real)
-/
protected theorem norm [NormedAddCommGroup γ] [OpensMeasurableSpace γ] (h : IdentDistrib f g μ ν) :
    IdentDistrib (fun x => ‖f x‖) (fun x => ‖g x‖) μ ν :=
  h.comp measurable_norm
/-
**ProbabilityTheory.IdentDistrib.nnnorm** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTh
eory.IdentDistrib`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : MeasurableSpace α] 
[inst_1 : MeasurableSpace β]   [inst_2 : MeasurableSpace γ] {μ : MeasureTheory.M
easure α} {ν : MeasureTheory.Measure β} {f : α → γ} {g : β → γ}   [inst_3 : Norm
edAddCommGroup γ] [OpensMeasurableSpace γ],   ProbabilityTheory.IdentDistrib f g
 μ ν → ProbabilityTheory.IdentDistrib (fun x => ‖f x‖₊) (fun x => ‖g x‖₊) μ ν
参数：fun x => ‖f x‖₊；fun x => ‖g x‖₊。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IdentDistrib.comp`：∀ {α : Type u_1} {β : Type u_2} {γ 
: Type u_3} {δ : Type u_4} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace 
β]   [inst_2 : Measurable…
· 使用定理 `measurable_nnnorm`：measurable_nnnorm : Measurable (nnnorm : α -> Real>=0
)
-/
protected theorem nnnorm [NormedAddCommGroup γ] [OpensMeasurableSpace γ]
    (h : IdentDistrib f g μ ν) :
    IdentDistrib (fun x => ‖f x‖₊) (fun x => ‖g x‖₊) μ ν :=
  h.comp measurable_nnnorm
/-
**ProbabilityTheory.IdentDistrib.pow** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheor
y.IdentDistrib`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : MeasurableSpace α] 
[inst_1 : MeasurableSpace β]   [inst_2 : MeasurableSpace γ] {μ : MeasureTheory.M
easure α} {ν : MeasureTheory.Measure β} {f : α → γ} {g : β → γ}   [inst_3 : Pow 
γ ℕ] [MeasurablePow γ ℕ],   ProbabilityTheory.IdentDistrib f g μ ν →     ∀ {n : 
ℕ}, ProbabilityTheory.IdentDistrib (fun x => f x ^ n) (fun x => g x ^ n) μ ν
参数：fun x => f x ^ n；fun x => g x ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IdentDistrib.comp`：∀ {α : Type u_1} {β : Type u_2} {γ 
: Type u_3} {δ : Type u_4} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace 
β]   [inst_2 : Measurable…
· 使用定理 `Measurable.pow_const`：Measurable.pow_const (hf : Measurable f) (c : γ) :
 Measurable fun x => f x ^ c
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
-/
protected theorem pow [Pow γ ℕ] [MeasurablePow γ ℕ] (h : IdentDistrib f g μ ν) {n : ℕ} :
    IdentDistrib (fun x => f x ^ n) (fun x => g x ^ n) μ ν :=
  h.comp (measurable_id.pow_const n)
/-
**ProbabilityTheory.IdentDistrib.sq** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory
.IdentDistrib`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : MeasurableSpace α] 
[inst_1 : MeasurableSpace β]   [inst_2 : MeasurableSpace γ] {μ : MeasureTheory.M
easure α} {ν : MeasureTheory.Measure β} {f : α → γ} {g : β → γ}   [inst_3 : Pow 
γ ℕ] [MeasurablePow γ ℕ],   ProbabilityTheory.IdentDistrib f g μ ν → Probability
Theory.IdentDistrib (fun x => f x ^ 2) (fun x => g x ^ 2) μ ν
参数：fun x => f x ^ 2；fun x => g x ^ 2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IdentDistrib.comp`：∀ {α : Type u_1} {β : Type u_2} {γ 
: Type u_3} {δ : Type u_4} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace 
β]   [inst_2 : Measurable…
· 使用定理 `Measurable.pow_const`：Measurable.pow_const (hf : Measurable f) (c : γ) :
 Measurable fun x => f x ^ c
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
-/
protected theorem sq [Pow γ ℕ] [MeasurablePow γ ℕ] (h : IdentDistrib f g μ ν) :
    IdentDistrib (fun x => f x ^ 2) (fun x => g x ^ 2) μ ν :=
  h.comp (measurable_id.pow_const 2)
/-
**ProbabilityTheory.IdentDistrib.coe_nnreal_ennreal** 是 Mathlib 中的一个定理，位于命名空间 `P
robabilityTheory.IdentDistrib`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : Measu
rableSpace β] {μ : MeasureTheory.Measure α}   {ν : MeasureTheory.Measure β} {f :
 α → NNReal} {g : β → NNReal},   ProbabilityTheory.IdentDistrib f g μ ν → Probab
ilityTheory.IdentDistrib (fun x => ↑(f x)) (fun x => ↑(g x)) μ ν
参数：fun x => ↑(f x)；fun x => ↑(g x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IdentDistrib.comp`：∀ {α : Type u_1} {β : Type u_2} {γ 
: Type u_3} {δ : Type u_4} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace 
β]   [inst_2 : Measurable…
· 使用定理 `measurable_coe_nnreal_ennreal`：measurable_coe_nnreal_ennreal : Measurabl
e ((↑) : Real>=0 -> Real>=0∞)
-/
protected theorem coe_nnreal_ennreal {f : α → ℝ≥0} {g : β → ℝ≥0} (h : IdentDistrib f g μ ν) :
    IdentDistrib (fun x => (f x : ℝ≥0∞)) (fun x => (g x : ℝ≥0∞)) μ ν :=
  h.comp measurable_coe_nnreal_ennreal

@[to_additive]
/-
**ProbabilityTheory.IdentDistrib.mul_const** 是 Mathlib 中的一个定理，位于命名空间 `Probabilit
yTheory.IdentDistrib`。
形式化陈述：mul_const [Mul γ] [MeasurableMul γ] (h : IdentDistrib f g μ ν) (c : γ) : I
dentDistrib (fun x => f x * c) (fun x => g x * c) μ ν
参数：h : IdentDistrib f g μ ν；c : γ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IdentDistrib.comp`：∀ {α : Type u_1} {β : Type u_2} {γ 
: Type u_3} {δ : Type u_4} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace 
β]   [inst_2 : Measurable…
· 使用定理 `MeasurableMul.measurable_mul_const`：∀ {M : Type u_2} {inst : MeasurableS
pace M} {inst_1 : Mul M} [self : MeasurableMul M] (c : M), Measurable fun x => x
 * c
-/
theorem mul_const [Mul γ] [MeasurableMul γ] (h : IdentDistrib f g μ ν) (c : γ) :
    IdentDistrib (fun x => f x * c) (fun x => g x * c) μ ν :=
  h.comp (measurable_mul_const c)

@[to_additive]
/-
**ProbabilityTheory.IdentDistrib.const_mul** 是 Mathlib 中的一个定理，位于命名空间 `Probabilit
yTheory.IdentDistrib`。
形式化陈述：const_mul [Mul γ] [MeasurableMul γ] (h : IdentDistrib f g μ ν) (c : γ) : I
dentDistrib (fun x => c * f x) (fun x => c * g x) μ ν
参数：h : IdentDistrib f g μ ν；c : γ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IdentDistrib.comp`：∀ {α : Type u_1} {β : Type u_2} {γ 
: Type u_3} {δ : Type u_4} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace 
β]   [inst_2 : Measurable…
· 使用定理 `MeasurableMul.measurable_const_mul`：∀ {M : Type u_2} {inst : MeasurableS
pace M} {inst_1 : Mul M} [self : MeasurableMul M] (c : M), Measurable fun x => c
 * x
-/
theorem const_mul [Mul γ] [MeasurableMul γ] (h : IdentDistrib f g μ ν) (c : γ) :
    IdentDistrib (fun x => c * f x) (fun x => c * g x) μ ν :=
  h.comp (measurable_const_mul c)

@[to_additive]
/-
**ProbabilityTheory.IdentDistrib.div_const** 是 Mathlib 中的一个定理，位于命名空间 `Probabilit
yTheory.IdentDistrib`。
形式化陈述：div_const [Div γ] [MeasurableDiv γ] (h : IdentDistrib f g μ ν) (c : γ) : I
dentDistrib (fun x => f x / c) (fun x => g x / c) μ ν
参数：h : IdentDistrib f g μ ν；c : γ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IdentDistrib.comp`：∀ {α : Type u_1} {β : Type u_2} {γ 
: Type u_3} {δ : Type u_4} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace 
β]   [inst_2 : Measurable…
· 使用定理 `MeasurableDiv.measurable_div_const`：∀ {G₀ : Type u_2} {inst : Measurable
Space G₀} {inst_1 : Div G₀} [self : MeasurableDiv G₀] (c : G₀),   Measurable fun
 x => x / c
-/
theorem div_const [Div γ] [MeasurableDiv γ] (h : IdentDistrib f g μ ν) (c : γ) :
    IdentDistrib (fun x => f x / c) (fun x => g x / c) μ ν :=
  h.comp (MeasurableDiv.measurable_div_const c)

@[to_additive]
/-
**ProbabilityTheory.IdentDistrib.const_div** 是 Mathlib 中的一个定理，位于命名空间 `Probabilit
yTheory.IdentDistrib`。
形式化陈述：const_div [Div γ] [MeasurableDiv γ] (h : IdentDistrib f g μ ν) (c : γ) : I
dentDistrib (fun x => c / f x) (fun x => c / g x) μ ν
参数：h : IdentDistrib f g μ ν；c : γ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IdentDistrib.comp`：∀ {α : Type u_1} {β : Type u_2} {γ 
: Type u_3} {δ : Type u_4} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace 
β]   [inst_2 : Measurable…
· 使用定理 `MeasurableDiv.measurable_const_div`：∀ {G₀ : Type u_2} {inst : Measurable
Space G₀} {inst_1 : Div G₀} [self : MeasurableDiv G₀] (c : G₀),   Measurable fun
 x => c / x
-/
theorem const_div [Div γ] [MeasurableDiv γ] (h : IdentDistrib f g μ ν) (c : γ) :
    IdentDistrib (fun x => c / f x) (fun x => c / g x) μ ν :=
  h.comp (MeasurableDiv.measurable_const_div c)

@[to_additive]
/-
**ProbabilityTheory.IdentDistrib.inv** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheor
y.IdentDistrib`。
形式化陈述：inv [Inv γ] [MeasurableInv γ] (h : IdentDistrib f g μ ν) : IdentDistrib f⁻
¹ g⁻¹ μ ν
参数：h : IdentDistrib f g μ ν。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IdentDistrib.comp`：∀ {α : Type u_1} {β : Type u_2} {γ 
: Type u_3} {δ : Type u_4} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace 
β]   [inst_2 : Measurable…
· 使用定理 `MeasurableInv.measurable_inv`：∀ {G : Type u_2} {inst : Inv G} {inst_1 : 
MeasurableSpace G} [self : MeasurableInv G], Measurable Inv.inv
-/
lemma inv [Inv γ] [MeasurableInv γ] (h : IdentDistrib f g μ ν) :
    IdentDistrib f⁻¹ g⁻¹ μ ν := h.comp measurable_inv
/-
**ProbabilityTheory.IdentDistrib.evariance_eq** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory.IdentDistrib`。
形式化陈述：evariance_eq {f : α -> Real} {g : β -> Real} (h : IdentDistrib f g μ ν) : 
evariance f μ = evariance g ν
参数：h : IdentDistrib f g μ ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.IdentDistrib.integral_eq`：integral_eq [NormedAddCommGr
oup γ] [NormedSpace Real γ] [BorelSpace γ] (h : IdentDistrib f g μ ν) : ∫ x, f x
 ∂μ = ∫ x, g x ∂ν
· 使用定理 `ProbabilityTheory.IdentDistrib.lintegral_eq`：lintegral_eq {f : α -> Real
>=0∞} {g : β -> Real>=0∞} (h : IdentDistrib f g μ ν) : ∫⁻ x, f x ∂μ = ∫⁻ x, g x 
∂ν
· 使用定理 `ProbabilityTheory.IdentDistrib.sq`：∀ {α : Type u_1} {β : Type u_2} {γ : 
Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 : Me
asurableSpace γ] {μ : M…
· 使用定理 `ProbabilityTheory.IdentDistrib.coe_nnreal_ennreal`：∀ {α : Type u_1} {β :
 Type u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μ : MeasureT
heory.Measure α}   {ν : MeasureTheory.M…
· 使用定理 `ProbabilityTheory.IdentDistrib.nnnorm`：∀ {α : Type u_1} {β : Type u_2} {
γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 
: MeasurableSpace γ] {μ : M…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `ProbabilityTheory.IdentDistrib.sub_const`：∀ {α : Type u_1} {β : Type u_2
} {γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst
_2 : MeasurableSpace γ] {μ : M…
· 使用定理 `ContinuousSub.measurableSub`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Sub γ]   [ContinuousSub 
γ], MeasurableSub…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
-/
theorem evariance_eq {f : α → ℝ} {g : β → ℝ} (h : IdentDistrib f g μ ν) :
    evariance f μ = evariance g ν := by
  convert! (h.sub_const (∫ x, f x ∂μ)).nnnorm.coe_nnreal_ennreal.sq.lintegral_eq
  rw [h.integral_eq]
  rfl
/-
**ProbabilityTheory.IdentDistrib.variance_eq** 是 Mathlib 中的一个定理，位于命名空间 `Probabil
ityTheory.IdentDistrib`。
形式化陈述：variance_eq {f : α -> Real} {g : β -> Real} (h : IdentDistrib f g μ ν) : v
ariance f μ = variance g ν
参数：h : IdentDistrib f g μ ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.variance.eq_1`：∀ {Ω : Type u_1} {mΩ : MeasurableSpace 
Ω} (X : Ω → ℝ) (μ : MeasureTheory.Measure Ω),   ProbabilityTheory.variance X μ =
 (ProbabilityTheory.e…
· 使用定理 `ProbabilityTheory.IdentDistrib.evariance_eq`：evariance_eq {f : α -> Real
} {g : β -> Real} (h : IdentDistrib f g μ ν) : evariance f μ = evariance g ν
-/
theorem variance_eq {f : α → ℝ} {g : β → ℝ} (h : IdentDistrib f g μ ν) :
    variance f μ = variance g ν := by rw [variance, h.evariance_eq]; rfl

end IdentDistrib

section UniformIntegrable

open TopologicalSpace

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]
  {μ : Measure α} [IsFiniteMeasure μ]

set_option backward.isDefEq.respectTransparency false in
/-- This lemma is superseded by `MemLp.uniformIntegrable_of_identDistrib` which only requires
`AEStronglyMeasurable`. -/
/-
**ProbabilityTheory.MemLp.uniformIntegrable_of_identDistrib_aux** 是 Mathlib 中的一个
定理，位于命名空间 `ProbabilityTheory.MemLp`。
形式化陈述：∀ {α : Type u_1} [inst : MeasurableSpace α] {E : Type u_5} [inst_1 : Measu
rableSpace E] [inst_2 : NormedAddCommGroup E]   [BorelSpace E] {μ : MeasureTheor
y.Measure α} [MeasureTheory.IsFiniteMeasure μ] {ι : Type u_6} {f : ι → α → E} {j
 : ι}   {p : ENNReal},   1 ≤ p →     p ≠ ⊤ →       MeasureTheory.MemLp (f j) p μ
 →         (∀ (i : ι), MeasureTheory.StronglyMeasurable (f i)) →           (∀ (i
 : ι), ProbabilityTheory.IdentDistrib (f i) (f j) μ μ) → MeasureTheory.UniformIn
tegrable f p μ
参数：f j；∀ (i : ι), MeasureTheory.StronglyMeasurable (f i)；∀ (i : ι), ProbabilityT
heory.IdentDistrib (f i) (f j) μ μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.uniformIntegrable_of'`：uniformIntegrable_of' [IsFiniteMeas
ure μ] (hp : 1 <= p) (hp' : p != ∞) (hf : forall i, StronglyMeasurable (f i)) (h
 : forall ε : Real, 0 < ε…
· 使用定理 `MeasureTheory.MemLp.eLpNorm_indicator_norm_ge_pos_le`：∀ {α : Type u_1} {
β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Norm
edAddCommGroup β]   {p : ENNReal} {f : α →…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.le_toNNReal_iff_coe_le`：le_toNNReal_iff_coe_le {r : Real>=0} {p : R
eal} (hp : 0 <= p) : r <= Real.toNNReal p ↔ ↑r <= p
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.eLpNorm_norm`：eLpNorm_norm (f : α -> F) : eLpNorm (fun x =
> ‖f x‖) p μ = eLpNorm f p μ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `norm_indicator_eq_indicator_norm`：norm_indicator_eq_indicator_norm : ‖in
dicator s f a‖ = indicator s (fun a => ‖f a‖) a
· 使用定理 `Measurable.indicator`：Measurable.indicator [Zero β] (hf : Measurable f) 
(hs : MeasurableSet s) : Measurable (s.indicator f)
· 使用定理 `measurable_norm`：measurable_norm : Measurable (norm : α -> Real)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `measurableSet_le`：measurableSet_le {f g : δ -> α} (hf : Measurable f) (h
g : Measurable g) : MeasurableSet { a | f a <= g a }
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `NNReal.instOrderTopology`：OrderTopology NNReal
· 使用定理 `NNReal.instSecondCountableTopology`：SecondCountableTopology NNReal
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `measurable_nnnorm`：measurable_nnnorm : Measurable (nnnorm : α -> Real>=0
)
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `MeasureTheory.eLpNorm_map_measure`：eLpNorm_map_measure (hg : AEStronglyM
easurable g (Measure.map f μ)) (hf : AEMeasurable f μ) : eLpNorm g p (Measure.ma
p f μ) = eLpNorm (g ∘ f…
· 使用定理 `Measurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 :…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
This lemma is superseded by `MemLp.uniformIntegrable_of_identDistrib` which only
 requires
`AEStronglyMeasurable`.
-/
theorem MemLp.uniformIntegrable_of_identDistrib_aux {ι : Type*} {f : ι → α → E} {j : ι} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hp' : p ≠ ∞) (hℒp : MemLp (f j) p μ) (hfmeas : ∀ i, StronglyMeasurable (f i))
    (hf : ∀ i, IdentDistrib (f i) (f j) μ μ) : UniformIntegrable f p μ := by
  refine uniformIntegrable_of' hp hp' hfmeas fun ε hε => ?_
  by_cases hι : Nonempty ι
  swap; · exact ⟨0, fun i => False.elim (hι <| Nonempty.intro i)⟩
  obtain ⟨C, hC₁, hC₂⟩ := hℒp.eLpNorm_indicator_norm_ge_pos_le (hfmeas _) hε
  refine ⟨⟨C, hC₁.le⟩, fun i => le_trans (le_of_eq ?_) hC₂⟩
  have : {x | (⟨C, hC₁.le⟩ : ℝ≥0) ≤ ‖f i x‖₊} = {x | C ≤ ‖f i x‖} := by
    ext x
    simp_rw [← norm_toNNReal]
    exact Real.le_toNNReal_iff_coe_le (norm_nonneg _)
  rw [this, ← eLpNorm_norm, ← eLpNorm_norm (Set.indicator _ _)]
  simp_rw [norm_indicator_eq_indicator_norm, coe_nnnorm]
  let F : E → ℝ := (fun x : E => if (⟨C, hC₁.le⟩ : ℝ≥0) ≤ ‖x‖₊ then ‖x‖ else 0)
  have F_meas : Measurable F := by
    apply measurable_norm.indicator (measurableSet_le measurable_const measurable_nnnorm)
  have : ∀ k, (fun x ↦ Set.indicator {x | C ≤ ‖f k x‖} (fun a ↦ ‖f k a‖) x) = F ∘ f k := by
    intro k
    ext x
    simp only [Set.indicator, Set.mem_ofPred_eq]; norm_cast
  rw [this, this, ← eLpNorm_map_measure F_meas.aestronglyMeasurable (hf i).aemeasurable_fst,
    (hf i).map_eq, eLpNorm_map_measure F_meas.aestronglyMeasurable (hf j).aemeasurable_fst]

/-- A sequence of identically distributed Lᵖ functions is p-uniformly integrable. -/
/-
**ProbabilityTheory.MemLp.uniformIntegrable_of_identDistrib** 是 Mathlib 中的一个定理，位
于命名空间 `ProbabilityTheory.MemLp`。
形式化陈述：∀ {α : Type u_1} [inst : MeasurableSpace α] {E : Type u_5} [inst_1 : Measu
rableSpace E] [inst_2 : NormedAddCommGroup E]   [BorelSpace E] {μ : MeasureTheor
y.Measure α} [MeasureTheory.IsFiniteMeasure μ] {ι : Type u_6} {f : ι → α → E} {j
 : ι}   {p : ENNReal},   1 ≤ p →     p ≠ ⊤ →       MeasureTheory.MemLp (f j) p μ
 →         (∀ (i : ι), ProbabilityTheory.IdentDistrib (f i) (f j) μ μ) → Measure
Theory.UniformIntegrable f p μ
参数：f j；∀ (i : ι), ProbabilityTheory.IdentDistrib (f i) (f j) μ μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ProbabilityTheory.IdentDistrib.aestronglyMeasurable_iff`：aestronglyMeasu
rable_iff [TopologicalSpace γ] [PseudoMetrizableSpace γ] [BorelSpace γ] (h : Ide
ntDistrib f g μ ν) : AEStronglyMeasurable f μ…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.MemLp.ae_eq`：∀ {α : Type u_1} {ε : Type u_2} {m0 : Measura
bleSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α} [inst : ENorm ε]   [inst
_1 : Topologica…
· 使用定理 `MeasureTheory.UniformIntegrable.ae_eq`：∀ {α : Type u_1} {β : Type u_2} {
ι : Type u_3} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : No
rmedAddCommGroup β] {p : EN…
· 使用定理 `ProbabilityTheory.MemLp.uniformIntegrable_of_identDistrib_aux`：∀ {α : Ty
pe u_1} [inst : MeasurableSpace α] {E : Type u_5} [inst_1 : MeasurableSpace E] [
inst_2 : NormedAddCommGroup E]   [BorelSpace E] {μ …
· 使用定理 `ProbabilityTheory.IdentDistrib.trans`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} {δ : Type u_4} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace
 β]   [inst_2 : Measurable…
· 使用定理 `ProbabilityTheory.IdentDistrib.of_ae_eq`：∀ {α : Type u_1} {γ : Type u_3}
 [inst : MeasurableSpace α] [inst_1 : MeasurableSpace γ] {μ : MeasureTheory.Meas
ure α}   {f g : α → γ}, AEMea…
· 使用定理 `MeasureTheory.StronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {β : Typ
e u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topolo
gicalSpace.PseudoMetrizableSpace β]…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…

--- 原说明 ---
A sequence of identically distributed Lᵖ functions is p-uniformly integrable.
-/
theorem MemLp.uniformIntegrable_of_identDistrib {ι : Type*} {f : ι → α → E} {j : ι} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hp' : p ≠ ∞) (hℒp : MemLp (f j) p μ) (hf : ∀ i, IdentDistrib (f i) (f j) μ μ) :
    UniformIntegrable f p μ := by
  have hfmeas : ∀ i, AEStronglyMeasurable (f i) μ := fun i =>
    (hf i).aestronglyMeasurable_iff.2 hℒp.1
  set g : ι → α → E := fun i => (hfmeas i).choose
  have hgmeas : ∀ i, StronglyMeasurable (g i) := fun i => (Exists.choose_spec <| hfmeas i).1
  have hgeq : ∀ i, g i =ᵐ[μ] f i := fun i => (Exists.choose_spec <| hfmeas i).2.symm
  have hgℒp : MemLp (g j) p μ := hℒp.ae_eq (hgeq j).symm
  exact UniformIntegrable.ae_eq
    (MemLp.uniformIntegrable_of_identDistrib_aux hp hp' hgℒp hgmeas fun i =>
      (IdentDistrib.of_ae_eq (hgmeas i).aemeasurable (hgeq i)).trans
        ((hf i).trans <| IdentDistrib.of_ae_eq (hfmeas j).aemeasurable (hgeq j).symm)) hgeq

end UniformIntegrable

/-- If `X` and `Y` are independent and `(X, Y)` and `(X', Y')` are identically distributed,
then `X'` and `Y'` are independent. -/
/-
**ProbabilityTheory.indepFun_of_identDistrib_pair** 是 Mathlib 中的一个引理，位于命名空间 `Pro
babilityTheory`。
形式化陈述：indepFun_of_identDistrib_pair {μ : Measure γ} {μ' : Measure δ} [IsFiniteMe
asure μ] [IsFiniteMeasure μ'] {X : γ -> α} {X' : δ -> α} {Y : γ -> β} {Y' : δ ->
 β} (h_indep : X ⟂ᵢ[μ] Y) (h_ident : IdentDistrib (fun ω => (X ω, Y ω)) (fun ω =
> (X' ω, Y' ω)) μ μ') : X' ⟂ᵢ[μ'] Y'
参数：h_indep : X ⟂ᵢ[μ] Y；h_ident : IdentDistrib (fun ω => (X ω, Y ω)) (fun ω => (X
' ω, Y' ω)) μ μ'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map`：indepFun_iff_ma
p_prod_eq_prod_map_map {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'} [IsFi
niteMeasure μ] (hf : AEMeasurable f μ) (hg : …
· 使用定理 `AEMeasurable.comp_aemeasurable`：comp_aemeasurable {f : α -> δ} {g : δ ->
 β} (hg : AEMeasurable g (μ.map f)) (hf : AEMeasurable f μ) : AEMeasurable (g ∘ 
f) μ
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
· 使用定理 `ProbabilityTheory.IdentDistrib.aemeasurable_snd`：∀ {α : Type u_1} {β : T
ype u_2} {γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] 
  [inst_2 : MeasurableSpace γ] {f : α…
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.IdentDistrib.map_eq`：∀ {α : Type u_1} {β : Type u_2} {
γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 
: MeasurableSpace γ] {f : α…
· 使用定理 `ProbabilityTheory.IndepFun.map_prod_eq_prod_map_map`：∀ {Ω : Type u_1} {β
 : Type u_6} {β' : Type u_7} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measur
e Ω} {f : Ω → β}   {g : Ω → β'} {mβ : Mea…
· 使用定理 `ProbabilityTheory.IdentDistrib.aemeasurable_fst`：∀ {α : Type u_1} {β : T
ype u_2} {γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] 
  [inst_2 : MeasurableSpace γ] {f : α…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ProbabilityTheory.IdentDistrib.comp`：∀ {α : Type u_1} {β : Type u_2} {γ 
: Type u_3} {δ : Type u_4} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace 
β]   [inst_2 : Measurable…

--- 原说明 ---
If `X` and `Y` are independent and `(X, Y)` and `(X', Y')` are identically distr
ibuted,
then `X'` and `Y'` are independent.
-/
lemma indepFun_of_identDistrib_pair
    {μ : Measure γ} {μ' : Measure δ} [IsFiniteMeasure μ] [IsFiniteMeasure μ']
    {X : γ → α} {X' : δ → α} {Y : γ → β} {Y' : δ → β} (h_indep : X ⟂ᵢ[μ] Y)
    (h_ident : IdentDistrib (fun ω ↦ (X ω, Y ω)) (fun ω ↦ (X' ω, Y' ω)) μ μ') :
    X' ⟂ᵢ[μ'] Y' := by
  rw [indepFun_iff_map_prod_eq_prod_map_map, ← h_ident.map_eq, h_indep.map_prod_eq_prod_map_map]
  · exact congr (congrArg Measure.prod <| (h_ident.comp measurable_fst).map_eq)
      (h_ident.comp measurable_snd).map_eq
  · exact measurable_fst.aemeasurable.comp_aemeasurable h_ident.aemeasurable_fst
  · exact measurable_snd.aemeasurable.comp_aemeasurable h_ident.aemeasurable_fst
  · exact measurable_fst.aemeasurable.comp_aemeasurable h_ident.aemeasurable_snd
  · exact measurable_snd.aemeasurable.comp_aemeasurable h_ident.aemeasurable_snd

end ProbabilityTheory

