/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Composition.Lemmas
public import Mathlib.Probability.Kernel.Disintegration.Unique

/-!
# Regular conditional probability distribution

We define the regular conditional probability distribution of `Y : α → Ω` given `X : α → β`, where
`Ω` is a standard Borel space. This is a `Kernel β Ω` such that for almost all `a`, `condDistrib`
evaluated at `X a` and a measurable set `s` is equal to the conditional expectation
`μ⟦Y ⁻¹' s | mβ.comap X⟧` evaluated at `a`.

`μ⟦Y ⁻¹' s | mβ.comap X⟧` maps a measurable set `s` to a function `α → ℝ≥0∞`, and for all `s` that
map is unique up to a `μ`-null set. For all `a`, the map from sets to `ℝ≥0∞` that we obtain that way
verifies some of the properties of a measure, but in general the fact that the `μ`-null set depends
on `s` can prevent us from finding versions of the conditional expectation that combine into a true
measure. The standard Borel space assumption on `Ω` allows us to do so.

The case `Y = X = id` is developed in more detail in `Mathlib/Probability/Kernel/Condexp.lean`: here
`X` is understood as a map from `Ω` with a sub-σ-algebra `m` to `Ω` with its default σ-algebra and
the conditional distribution defines a kernel associated with the conditional expectation with
respect to `m`.

## Main definitions

* `condDistrib Y X μ`: regular conditional probability distribution of `Y : α → Ω` given
  `X : α → β`, where `Ω` is a standard Borel space.

## Main statements

* `condDistrib_ae_eq_condExp`: for almost all `a`, `condDistrib` evaluated at `X a` and a
  measurable set `s` is equal to the conditional expectation `μ⟦Y ⁻¹' s | mβ.comap X⟧ a`.
* `condExp_prod_ae_eq_integral_condDistrib`: the conditional expectation
  `μ[(fun a => f (X a, Y a)) | X; mβ]` is almost everywhere equal to the integral
  `∫ y, f (X a, y) ∂(condDistrib Y X μ (X a))`.

-/

@[expose] public section


open MeasureTheory Set Filter TopologicalSpace

open scoped ENNReal MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

variable {α β Ω F : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [Nonempty Ω] [NormedAddCommGroup F] {mα : MeasurableSpace α} {μ : Measure α} [IsFiniteMeasure μ]
  {X : α → β} {Y : α → Ω}

/-- **Regular conditional probability distribution**: kernel associated with the conditional
expectation of `Y` given `X`.
For almost all `a`, `condDistrib Y X μ` evaluated at `X a` and a measurable set `s` is equal to
the conditional expectation `μ⟦Y ⁻¹' s | mβ.comap X⟧ a`. It also satisfies the equality
`μ[(fun a => f (X a, Y a)) | mβ.comap X] =ᵐ[μ] fun a => ∫ y, f (X a, y) ∂(condDistrib Y X μ (X a))`
for all integrable functions `f`. -/
noncomputable irreducible_def condDistrib {_ : MeasurableSpace α} [MeasurableSpace β] (Y : α → Ω)
    (X : α → β) (μ : Measure α) [IsFiniteMeasure μ] : Kernel β Ω :=
  (μ.map fun a => (X a, Y a)).condKernel

/-
**ProbabilityTheory.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MeasurableSpace β] : IsMarkovKernel (condDistrib Y X μ) := by
  rw [condDistrib]; infer_instance

variable {mβ : MeasurableSpace β} {s : Set Ω} {t : Set β} {f : β × Ω → F}

/-- If the singleton `{x}` has non-zero mass for `μ.map X`, then for all `s : Set Ω`,
`condDistrib Y X μ x s = (μ.map X {x})⁻¹ * μ.map (fun a => (X a, Y a)) ({x} ×ˢ s)` . -/
/-
**ProbabilityTheory.condDistrib_apply_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Prob
abilityTheory`。
形式化陈述：condDistrib_apply_of_ne_zero [MeasurableSingletonClass β] (hY : Measurable
 Y) (x : β) (hX : μ.map X {x} != 0) (s : Set Ω) : condDistrib Y X μ x s = (μ.map
 X {x})⁻¹ * μ.map (fun a => (X a, Y a)) ({x} ×ˢ s)
参数：hY : Measurable Y；x : β；hX : μ.map X {x} != 0；s : Set Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.condDistrib_def`：∀ {α : Type u_5} {β : Type u_6} {Ω : 
Type u_7} [inst : MeasurableSpace Ω] [inst_1 : StandardBorelSpace Ω]   [inst_2 :
 Nonempty Ω] {x : Measu…
· 使用定理 `MeasureTheory.Measure.condKernel_apply_of_ne_zero`：∀ {α : Type u_1} {Ω :
 Type u_4} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω} [inst : StandardBor
elSpace Ω]   [inst_1 : Nonempty Ω] {ρ :…
· 使用定理 `MeasureTheory.Measure.fst_map_prodMk`：fst_map_prodMk {X : α -> β} {Y : α
 -> γ} {μ : Measure α} (hY : Measurable Y) : (μ.map fun a => (X a, Y a)).fst = μ
.map X

--- 原说明 ---
If the singleton `{x}` has non-zero mass for `μ.map X`, then for all `s : Set Ω`
,
`condDistrib Y X μ x s = (μ.map X {x})⁻¹ * μ.map (fun a => (X a, Y a)) ({x} ×ˢ s
)` .
-/
lemma condDistrib_apply_of_ne_zero [MeasurableSingletonClass β]
    (hY : Measurable Y) (x : β) (hX : μ.map X {x} ≠ 0) (s : Set Ω) :
    condDistrib Y X μ x s = (μ.map X {x})⁻¹ * μ.map (fun a => (X a, Y a)) ({x} ×ˢ s) := by
  rw [condDistrib, Measure.condKernel_apply_of_ne_zero _ s]
  · rw [Measure.fst_map_prodMk hY]
  · rwa [Measure.fst_map_prodMk hY]
/-
**ProbabilityTheory.compProd_map_condDistrib** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory`。
形式化陈述：compProd_map_condDistrib (hY : AEMeasurable Y μ) : (μ.map X) otimesₘ condD
istrib Y X μ = μ.map fun a => (X a, Y a)
参数：hY : AEMeasurable Y μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.condDistrib_def`：∀ {α : Type u_5} {β : Type u_6} {Ω : 
Type u_7} [inst : MeasurableSpace Ω] [inst_1 : StandardBorelSpace Ω]   [inst_2 :
 Nonempty Ω] {x : Measu…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.fst_map_prodMk₀`：fst_map_prodMk₀ {X : α -> β} {Y :
 α -> γ} {μ : Measure α} (hY : AEMeasurable Y μ) : (μ.map fun a => (X a, Y a)).f
st = μ.map X
· 使用引理 `MeasureTheory.Measure.disintegrate`：disintegrate : ρ.fst otimesₘ ρCond =
 ρ
· 使用定理 `MeasureTheory.Measure.condKernel.instIsCondKernel`：∀ {α : Type u_1} {Ω :
 Type u_4} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω} [inst : StandardBor
elSpace Ω]   [inst_1 : Nonempty Ω] (ρ :…
-/
lemma compProd_map_condDistrib (hY : AEMeasurable Y μ) :
    (μ.map X) ⊗ₘ condDistrib Y X μ = μ.map fun a ↦ (X a, Y a) := by
  rw [condDistrib, ← Measure.fst_map_prodMk₀ hY, Measure.disintegrate]
/-
**ProbabilityTheory.condDistrib_comp_map** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：condDistrib_comp_map (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) : con
dDistrib Y X μ ∘ₘ (μ.map X) = μ.map Y
参数：hX : AEMeasurable X μ；hY : AEMeasurable Y μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.snd_compProd`：snd_compProd (μ : Measure α) [SFinit
e μ] (κ : Kernel α β) [IsSFiniteKernel κ] : (μ otimesₘ κ).snd = κ ∘ₘ μ
· 使用定理 `MeasureTheory.Measure.instSFiniteMap`：∀ {α : Type u_2} {β : Type u_3} {m
0 : MeasurableSpace α} [inst : MeasurableSpace β] (μ : MeasureTheory.Measure α) 
  (f : α → β) [MeasureTheo…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.instIsMarkovKernelCondDistrib`：∀ {α : Type u_1} {β : T
ype u_2} {Ω : Type u_3} [inst : MeasurableSpace Ω] [inst_1 : StandardBorelSpace 
Ω]   [inst_2 : Nonempty Ω] {mα : Meas…
· 使用引理 `ProbabilityTheory.compProd_map_condDistrib`：compProd_map_condDistrib (hY
 : AEMeasurable Y μ) : (μ.map X) otimesₘ condDistrib Y X μ = μ.map fun a => (X a
, Y a)
· 使用定理 `MeasureTheory.Measure.snd_map_prodMk₀`：snd_map_prodMk₀ {X : α -> β} {Y :
 α -> γ} {μ : Measure α} (hX : AEMeasurable X μ) : (μ.map fun a => (X a, Y a)).s
nd = μ.map Y
-/
lemma condDistrib_comp_map (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) :
    condDistrib Y X μ ∘ₘ (μ.map X) = μ.map Y := by
  rw [← Measure.snd_compProd, compProd_map_condDistrib hY, Measure.snd_map_prodMk₀ hX]
/-
**ProbabilityTheory.condDistrib_congr** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheo
ry`。
形式化陈述：condDistrib_congr {X' : α -> β} {Y' : α -> Ω} (hY : Y =ᵐ[μ] Y') (hX : X =ᵐ
[μ] X') : condDistrib Y X μ = condDistrib Y' X' μ
参数：hY : Y =ᵐ[μ] Y'；hX : X =ᵐ[μ] X'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.condDistrib_def`：∀ {α : Type u_5} {β : Type u_6} {Ω : 
Type u_7} [inst : MeasurableSpace Ω] [inst_1 : StandardBorelSpace Ω]   [inst_2 :
 Nonempty Ω] {x : Measu…
· 使用定理 `MeasureTheory.Measure.map_congr`：map_congr {f g : α -> β} (h : f =ᵐ[μ] g
) : Measure.map f μ = Measure.map g μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
-/
lemma condDistrib_congr {X' : α → β} {Y' : α → Ω} (hY : Y =ᵐ[μ] Y') (hX : X =ᵐ[μ] X') :
    condDistrib Y X μ = condDistrib Y' X' μ := by
  rw [condDistrib, condDistrib]
  congr 1
  rw [Measure.map_congr]
  filter_upwards [hX, hY] with a ha hb using by rw [ha, hb]
/-
**ProbabilityTheory.condDistrib_congr_right** 是 Mathlib 中的一个引理，位于命名空间 `Probabili
tyTheory`。
形式化陈述：condDistrib_congr_right {X' : α -> β} (hX : X =ᵐ[μ] X') : condDistrib Y X 
μ = condDistrib Y X' μ
参数：hX : X =ᵐ[μ] X'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.condDistrib_congr`：condDistrib_congr {X' : α -> β} {Y'
 : α -> Ω} (hY : Y =ᵐ[μ] Y') (hX : X =ᵐ[μ] X') : condDistrib Y X μ = condDistrib
 Y' X' μ
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
-/
lemma condDistrib_congr_right {X' : α → β} (hX : X =ᵐ[μ] X') :
    condDistrib Y X μ = condDistrib Y X' μ :=
  condDistrib_congr (by rfl) hX
/-
**ProbabilityTheory.condDistrib_congr_left** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory`。
形式化陈述：condDistrib_congr_left {Y' : α -> Ω} (hY : Y =ᵐ[μ] Y') : condDistrib Y X μ
 = condDistrib Y' X μ
参数：hY : Y =ᵐ[μ] Y'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.condDistrib_congr`：condDistrib_congr {X' : α -> β} {Y'
 : α -> Ω} (hY : Y =ᵐ[μ] Y') (hX : X =ᵐ[μ] X') : condDistrib Y X μ = condDistrib
 Y' X' μ
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
-/
lemma condDistrib_congr_left {Y' : α → Ω} (hY : Y =ᵐ[μ] Y') :
    condDistrib Y X μ = condDistrib Y' X μ :=
  condDistrib_congr hY (by rfl)

section Measurability

/-
**ProbabilityTheory.measurable_condDistrib** 是 Mathlib 中的一个定理，位于命名空间 `Probabilit
yTheory`。
形式化陈述：measurable_condDistrib (hs : MeasurableSet s) : Measurable[mβ.comap X] fun
 a => condDistrib Y X μ (X a) s
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `ProbabilityTheory.Kernel.measurable_coe`：∀ {α : Type u_1} {β : Type u_2}
 {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ : ProbabilityTheory.Kernel
 α β)   {s : Set β}, Measurab…
· 使用定理 `Measurable.of_comap_le`：∀ {α : Type u_1} {β : Type u_2} {m₁ : Measurable
Space α} {m₂ : MeasurableSpace β} {f : α → β},   MeasurableSpace.comap f m₂ ≤ m₁
 → Measurabl…
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem measurable_condDistrib (hs : MeasurableSet s) :
    Measurable[mβ.comap X] fun a => condDistrib Y X μ (X a) s :=
  (Kernel.measurable_coe _ hs).comp (Measurable.of_comap_le le_rfl)
/-
**ProbabilityTheory._root_.MeasureTheory.AEStronglyMeasurable.ae_integrable_cond
Distrib_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.AEStronglyMeasurable.ae_integrable_condDistrib_map_iff
    (hY : AEMeasurable Y μ) (hf : AEStronglyMeasurable f (μ.map fun a => (X a, Y a))) :
    (∀ᵐ a ∂μ.map X, Integrable (fun ω => f (a, ω)) (condDistrib Y X μ a)) ∧
      Integrable (fun a => ∫ ω, ‖f (a, ω)‖ ∂condDistrib Y X μ a) (μ.map X) ↔
    Integrable f (μ.map fun a => (X a, Y a)) := by
  rw [condDistrib, ← hf.ae_integrable_condKernel_iff, Measure.fst_map_prodMk₀ hY]

variable [NormedSpace ℝ F]
/-
**ProbabilityTheory._root_.MeasureTheory.StronglyMeasurable.integral_condDistrib
** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.StronglyMeasurable.integral_condDistrib (hf : StronglyMeasurable f) :
    StronglyMeasurable (fun x ↦ ∫ y, f (x, y) ∂condDistrib Y X μ x) := by
  rw [condDistrib]; exact hf.integral_kernel_prod_right'
/-
**ProbabilityTheory._root_.MeasureTheory.AEStronglyMeasurable.integral_condDistr
ib_map** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.AEStronglyMeasurable.integral_condDistrib_map
    (hY : AEMeasurable Y μ) (hf : AEStronglyMeasurable f (μ.map fun a => (X a, Y a))) :
    AEStronglyMeasurable (fun x => ∫ y, f (x, y) ∂condDistrib Y X μ x) (μ.map X) := by
  rw [← Measure.fst_map_prodMk₀ hY, condDistrib]; exact hf.integral_condKernel
/-
**ProbabilityTheory._root_.MeasureTheory.AEStronglyMeasurable.integral_condDistr
ib** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.AEStronglyMeasurable.integral_condDistrib (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) (hf : AEStronglyMeasurable f (μ.map fun a => (X a, Y a))) :
    AEStronglyMeasurable (fun a => ∫ y, f (X a, y) ∂condDistrib Y X μ (X a)) μ :=
  (hf.integral_condDistrib_map hY).comp_aemeasurable hX
/-
**ProbabilityTheory.stronglyMeasurable_integral_condDistrib** 是 Mathlib 中的一个定理，位
于命名空间 `ProbabilityTheory`。
形式化陈述：stronglyMeasurable_integral_condDistrib (hf : StronglyMeasurable f) : Stro
nglyMeasurable[mβ.comap X] (fun a => ∫ y, f (X a, y) ∂condDistrib Y X μ (X a))
参数：hf : StronglyMeasurable f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.comp_measurable`：comp_measurable [Topol
ogicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ} {f : α -> β} {g :
 γ -> α} (hf : StronglyMeasurable f) (…
· 使用定理 `MeasureTheory.StronglyMeasurable.integral_condDistrib`：∀ {α : Type u_1} 
{β : Type u_2} {Ω : Type u_3} {F : Type u_4} [inst : MeasurableSpace Ω] [inst_1 
: StandardBorelSpace Ω]   [inst_2 : Nonempt…
· 使用定理 `Measurable.of_comap_le`：∀ {α : Type u_1} {β : Type u_2} {m₁ : Measurable
Space α} {m₂ : MeasurableSpace β} {f : α → β},   MeasurableSpace.comap f m₂ ≤ m₁
 → Measurabl…
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem stronglyMeasurable_integral_condDistrib (hf : StronglyMeasurable f) :
    StronglyMeasurable[mβ.comap X] (fun a ↦ ∫ y, f (X a, y) ∂condDistrib Y X μ (X a)) :=
  (hf.integral_condDistrib).comp_measurable <| Measurable.of_comap_le le_rfl
/-
**ProbabilityTheory.aestronglyMeasurable_integral_condDistrib** 是 Mathlib 中的一个定理
，位于命名空间 `ProbabilityTheory`。
形式化陈述：aestronglyMeasurable_integral_condDistrib (hX : AEMeasurable X μ) (hY : AE
Measurable Y μ) (hf : AEStronglyMeasurable f (μ.map fun a => (X a, Y a))) : AESt
ronglyMeasurable[mβ.comap X] (fun a => ∫ y, f (X a, y) ∂condDistrib Y X μ (X a))
 μ
参数：hX : AEMeasurable X μ；hY : AEMeasurable Y μ；hf : AEStronglyMeasurable f (μ.ma
p fun a => (X a, Y a))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.comp_ae_measurable'`：∀ {α : Type u_1}
 {β : Type u_2} {γ : Type u_3} [inst : TopologicalSpace β] {mα : MeasurableSpace
 α}   {x : MeasurableSpace γ} {f : α → β} {μ…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.integral_condDistrib_map`：∀ {α : Type
 u_1} {β : Type u_2} {Ω : Type u_3} {F : Type u_4} [inst : MeasurableSpace Ω] [i
nst_1 : StandardBorelSpace Ω]   [inst_2 : Nonempt…
-/
theorem aestronglyMeasurable_integral_condDistrib (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (hf : AEStronglyMeasurable f (μ.map fun a => (X a, Y a))) :
    AEStronglyMeasurable[mβ.comap X] (fun a => ∫ y, f (X a, y) ∂condDistrib Y X μ (X a)) μ :=
  (hf.integral_condDistrib_map hY).comp_ae_measurable' hX

end Measurability

/-- `condDistrib` is a.e. uniquely defined as the kernel satisfying the defining property of
`condKernel`. -/
/-
**ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd_of_measurable** 是 M
athlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：condDistrib_ae_eq_of_measure_eq_compProd_of_measurable (hX : Measurable X)
 (hY : Measurable Y) {κ : Kernel β Ω} [IsFiniteKernel κ] (hκ : μ.map (fun x => (
X x, Y x)) = μ.map X otimesₘ κ) : condDistrib Y X μ =ᵐ[μ.map X] κ
参数：hX : Measurable X；hY : Measurable Y；hκ : μ.map (fun x => (X x, Y x)) = μ.map 
X otimesₘ κ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `MeasureTheory.Measure.fst_apply`：fst_apply {s : Set α} (hs : MeasurableS
et s) : ρ.fst s = ρ (Prod.fst ⁻¹' s)
· 使用定理 `Measurable.prod`：Measurable.prod {f : α -> β × γ} (hf₁ : Measurable fun 
a => (f a).1) (hf₂ : Measurable fun a => (f a).2) : Measurable f
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.condDistrib_def`：∀ {α : Type u_5} {β : Type u_6} {Ω : 
Type u_7} [inst : MeasurableSpace Ω] [inst_1 : StandardBorelSpace Ω]   [inst_2 :
 Nonempty Ω] {x : Measu…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `ProbabilityTheory.eq_condKernel_of_measure_eq_compProd`：eq_condKernel_of
_measure_eq_compProd (κ : Kernel α Ω) [IsFiniteKernel κ] (hκ : ρ = ρ.fst otimesₘ
 κ) : forallᵐ x ∂ρ.fst, κ x = ρ.condKernel x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
`condDistrib` is a.e. uniquely defined as the kernel satisfying the defining pro
perty of
`condKernel`.
-/
theorem condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (hX : Measurable X) (hY : Measurable Y)
    {κ : Kernel β Ω} [IsFiniteKernel κ] (hκ : μ.map (fun x => (X x, Y x)) = μ.map X ⊗ₘ κ) :
    condDistrib Y X μ =ᵐ[μ.map X] κ := by
  have heq : μ.map X = (μ.map (fun x ↦ (X x, Y x))).fst := by
    ext s hs
    rw [Measure.map_apply hX hs, Measure.fst_apply hs, Measure.map_apply]
    exacts [rfl, Measurable.prod hX hY, measurable_fst hs]
  rw [heq, condDistrib]
  symm
  refine eq_condKernel_of_measure_eq_compProd _ ?_
  convert! hκ
  exact heq.symm

/-- `condDistrib` is a.e. uniquely defined as the kernel satisfying the defining property of
`condKernel`. -/
/-
**ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd** 是 Mathlib 中的一个引理，
位于命名空间 `ProbabilityTheory`。
形式化陈述：condDistrib_ae_eq_of_measure_eq_compProd (X : α -> β) (hY : AEMeasurable Y
 μ) {κ : Kernel β Ω} [IsFiniteKernel κ] (hκ : μ.map (fun x => (X x, Y x)) = μ.ma
p X otimesₘ κ) : condDistrib Y X μ =ᵐ[μ.map X] κ
参数：X : α -> β；hY : AEMeasurable Y μ；hκ : μ.map (fun x => (X x, Y x)) = μ.map X o
timesₘ κ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
`：condDistrib_ae_eq_of_measure_eq_compProd_of_measurable (hX : Measurable X) (hY
 : Measurable Y) {κ : Kernel β Ω} [IsFiniteKernel κ] (hκ : μ.m…
· 使用定理 `AEMeasurable.measurable_mk`：measurable_mk (h : AEMeasurable f μ) : Measu
rable (h.mk f)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.map_congr`：map_congr {f g : α -> β} (h : f =ᵐ[μ] g
) : Measure.map f μ = Measure.map g μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `AEMeasurable.ae_eq_mk`：ae_eq_mk (h : AEMeasurable f μ) : f =ᵐ[μ] h.mk f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.condDistrib_congr`：condDistrib_congr {X' : α -> β} {Y'
 : α -> Ω} (hY : Y =ᵐ[μ] Y') (hX : X =ᵐ[μ] X') : condDistrib Y X μ = condDistrib
 Y' X' μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.ae.congr_simp`：∀ {α : Type u_1} {F : Type u_3} [inst : Fun
Like F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F α]   (μ μ_1 
: F), μ = μ_1 → M…
· 使用定理 `MeasureTheory.Measure.map_of_not_aemeasurable`：map_of_not_aemeasurable {
f : α -> β} {μ : Measure α} (hf : ¬AEMeasurable f μ) : μ.map f = 0
· 使用定理 `MeasureTheory.ae_zero`：ae_zero {_m0 : MeasurableSpace α} : ae (0 : Measu
re α) = ⊥

--- 原说明 ---
`condDistrib` is a.e. uniquely defined as the kernel satisfying the defining pro
perty of
`condKernel`.
-/
lemma condDistrib_ae_eq_of_measure_eq_compProd
    (X : α → β) (hY : AEMeasurable Y μ) {κ : Kernel β Ω} [IsFiniteKernel κ]
    (hκ : μ.map (fun x => (X x, Y x)) = μ.map X ⊗ₘ κ) :
    condDistrib Y X μ =ᵐ[μ.map X] κ := by
  by_cases hX : AEMeasurable X μ
  swap; · simp [Measure.map_of_not_aemeasurable hX, Filter.EventuallyEq]
  suffices condDistrib (hY.mk Y) (hX.mk X) μ =ᵐ[μ.map (hX.mk X)] κ by
    rwa [Measure.map_congr hX.ae_eq_mk, condDistrib_congr hY.ae_eq_mk hX.ae_eq_mk]
  refine condDistrib_ae_eq_of_measure_eq_compProd_of_measurable (μ := μ)
    hX.measurable_mk hY.measurable_mk ((Eq.trans ?_ hκ).trans ?_)
  · refine Measure.map_congr ?_
    filter_upwards [hX.ae_eq_mk, hY.ae_eq_mk] with a haX haY using by rw [haX, haY]
  · rw [Measure.map_congr hX.ae_eq_mk]
/-
**ProbabilityTheory.condDistrib_ae_eq_iff_measure_eq_compProd** 是 Mathlib 中的一个引理
，位于命名空间 `ProbabilityTheory`。
形式化陈述：condDistrib_ae_eq_iff_measure_eq_compProd (X : α -> β) (hY : AEMeasurable 
Y μ) (κ : Kernel β Ω) [IsFiniteKernel κ] : (condDistrib Y X μ =ᵐ[μ.map X] κ) ↔ μ
.map (fun x => (X x, Y x)) = μ.map X otimesₘ κ
参数：X : α -> β；hY : AEMeasurable Y μ；κ : Kernel β Ω。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.compProd_congr`：compProd_congr [IsSFiniteKernel κ]
 [IsSFiniteKernel η] (h : κ =ᵐ[μ] η) : μ otimesₘ κ = μ otimesₘ η
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.instIsMarkovKernelCondDistrib`：∀ {α : Type u_1} {β : T
ype u_2} {Ω : Type u_3} [inst : MeasurableSpace Ω] [inst_1 : StandardBorelSpace 
Ω]   [inst_2 : Nonempty Ω] {mα : Meas…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用引理 `ProbabilityTheory.compProd_map_condDistrib`：compProd_map_condDistrib (hY
 : AEMeasurable Y μ) : (μ.map X) otimesₘ condDistrib Y X μ = μ.map fun a => (X a
, Y a)
· 使用引理 `ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd`：condDistrib_
ae_eq_of_measure_eq_compProd (X : α -> β) (hY : AEMeasurable Y μ) {κ : Kernel β 
Ω} [IsFiniteKernel κ] (hκ : μ.map (fun x => (X x…
-/
lemma condDistrib_ae_eq_iff_measure_eq_compProd
    (X : α → β) (hY : AEMeasurable Y μ) (κ : Kernel β Ω) [IsFiniteKernel κ] :
    (condDistrib Y X μ =ᵐ[μ.map X] κ) ↔ μ.map (fun x => (X x, Y x)) = μ.map X ⊗ₘ κ := by
  refine ⟨fun h ↦ ?_, condDistrib_ae_eq_of_measure_eq_compProd X hY⟩
  rw [Measure.compProd_congr h.symm, compProd_map_condDistrib hY]
/-
**ProbabilityTheory.condDistrib_comp** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheor
y`。
形式化陈述：condDistrib_comp {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} [StandardBorelSpa
ce Ω'] [Nonempty Ω'] (X : α -> β) (hY : AEMeasurable Y μ) {f : Ω -> Ω'} (hf : Me
asurable f) : condDistrib (f ∘ Y) X μ =ᵐ[μ.map X] (condDistrib Y X μ).map f
参数：X : α -> β；hY : AEMeasurable Y μ；hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd`：condDistrib_
ae_eq_of_measure_eq_compProd (X : α -> β) (hY : AEMeasurable Y μ) {κ : Kernel β 
Ω} [IsFiniteKernel κ] (hκ : μ.map (fun x => (X x…
· 使用定理 `Measurable.comp_aemeasurable'`：Measurable.comp_aemeasurable' [Measurable
Space δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) :
 AEMeasurable (fun …
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.map`：∀ {α : Type u_1} {β : Type 
u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : Me
asurableSpace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.instIsMarkovKernelCondDistrib`：∀ {α : Type u_1} {β : T
ype u_2} {Ω : Type u_3} [inst : MeasurableSpace Ω] [inst_1 : StandardBorelSpace 
Ω]   [inst_2 : Nonempty Ω] {mα : Meas…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AEMeasurable.map_map_of_aemeasurable`：map_map_of_aemeasurable {g : β -> 
γ} {f : α -> β} (hg : AEMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) 
: (μ.map f).map g = μ.map …
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Measurable.prodMap`：Measurable.prodMap [MeasurableSpace δ] {f : α -> β} 
{g : γ -> δ} (hf : Measurable f) (hg : Measurable g) : Measurable (Prod.map f g)
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `AEMeasurable.prodMk`：prodMk {f : α -> β} {g : α -> γ} (hf : AEMeasurable
 f μ) (hg : AEMeasurable g μ) : AEMeasurable (fun x => (f x, g x)) μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ProbabilityTheory.compProd_map_condDistrib`：compProd_map_condDistrib (hY
 : AEMeasurable Y μ) : (μ.map X) otimesₘ condDistrib Y X μ = μ.map fun a => (X a
, Y a)
· 使用引理 `MeasureTheory.Measure.compProd_map`：compProd_map [SFinite μ] [IsSFiniteK
ernel κ] {f : β -> γ} (hf : Measurable f) : μ otimesₘ (κ.map f) = (μ otimesₘ κ).
map (Prod.map id f)
· 使用定理 `MeasureTheory.Measure.instSFiniteMap`：∀ {α : Type u_2} {β : Type u_3} {m
0 : MeasurableSpace α} [inst : MeasurableSpace β] (μ : MeasureTheory.Measure α) 
  (f : α → β) [MeasureTheo…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.ae.congr_simp`：∀ {α : Type u_1} {F : Type u_3} [inst : Fun
Like F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F α]   (μ μ_1 
: F), μ = μ_1 → M…
· 使用定理 `MeasureTheory.Measure.map_of_not_aemeasurable`：map_of_not_aemeasurable {
f : α -> β} {μ : Measure α} (hf : ¬AEMeasurable f μ) : μ.map f = 0
· 使用定理 `MeasureTheory.ae_zero`：ae_zero {_m0 : MeasurableSpace α} : ae (0 : Measu
re α) = ⊥
-/
lemma condDistrib_comp {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} [StandardBorelSpace Ω']
    [Nonempty Ω'] (X : α → β) (hY : AEMeasurable Y μ) {f : Ω → Ω'} (hf : Measurable f) :
    condDistrib (f ∘ Y) X μ =ᵐ[μ.map X] (condDistrib Y X μ).map f := by
  by_cases hX : AEMeasurable X μ
  swap; · simp [Measure.map_of_not_aemeasurable hX, Filter.EventuallyEq]
  refine condDistrib_ae_eq_of_measure_eq_compProd X (by fun_prop) ?_
  calc μ.map (fun x ↦ (X x, (f ∘ Y) x))
  _ = (μ.map (fun x ↦ (X x, Y x))).map (Prod.map id f) := by
    rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
    simp [Function.comp_def]
  _ = (μ.map X ⊗ₘ condDistrib Y X μ).map (Prod.map id f) := by rw [compProd_map_condDistrib hY]
  _ = μ.map X ⊗ₘ (condDistrib Y X μ).map f := by rw [Measure.compProd_map hf]
/-
**ProbabilityTheory.condDistrib_comp_self** 是 Mathlib 中的一个引理，位于命名空间 `Probability
Theory`。
形式化陈述：condDistrib_comp_self (X : α -> β) {f : β -> Ω} (hf : Measurable f) : cond
Distrib (f ∘ X) X μ =ᵐ[μ.map X] Kernel.deterministic f hf
参数：X : α -> β；hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd`：condDistrib_
ae_eq_of_measure_eq_compProd (X : α -> β) (hY : AEMeasurable Y μ) {κ : Kernel β 
Ω} [IsFiniteKernel κ] (hκ : μ.map (fun x => (X x…
· 使用定理 `Measurable.comp_aemeasurable'`：Measurable.comp_aemeasurable' [Measurable
Space δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) :
 AEMeasurable (fun …
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.compProd_deterministic`：compProd_deterministic [SF
inite μ] {f : α -> β} (hf : Measurable f) : μ otimesₘ Kernel.deterministic f hf 
= μ.map (fun a => (a, f a))
· 使用定理 `MeasureTheory.Measure.instSFiniteMap`：∀ {α : Type u_2} {β : Type u_3} {m
0 : MeasurableSpace α} [inst : MeasurableSpace β] (μ : MeasureTheory.Measure α) 
  (f : α → β) [MeasureTheo…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `AEMeasurable.map_map_of_aemeasurable`：map_map_of_aemeasurable {g : β -> 
γ} {f : α -> β} (hg : AEMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) 
: (μ.map f).map g = μ.map …
· 使用定理 `AEMeasurable.prodMk`：prodMk {f : α -> β} {g : α -> γ} (hf : AEMeasurable
 f μ) (hg : AEMeasurable g μ) : AEMeasurable (fun x => (f x, g x)) μ
· 使用定理 `aemeasurable_id`：aemeasurable_id : AEMeasurable id μ
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.ae.congr_simp`：∀ {α : Type u_1} {F : Type u_3} [inst : Fun
Like F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F α]   (μ μ_1 
: F), μ = μ_1 → M…
· 使用定理 `MeasureTheory.Measure.map_of_not_aemeasurable`：map_of_not_aemeasurable {
f : α -> β} {μ : Measure α} (hf : ¬AEMeasurable f μ) : μ.map f = 0
· 使用定理 `MeasureTheory.ae_zero`：ae_zero {_m0 : MeasurableSpace α} : ae (0 : Measu
re α) = ⊥
-/
lemma condDistrib_comp_self (X : α → β) {f : β → Ω} (hf : Measurable f) :
    condDistrib (f ∘ X) X μ =ᵐ[μ.map X] Kernel.deterministic f hf := by
  by_cases hX : AEMeasurable X μ
  swap; · simp [Measure.map_of_not_aemeasurable hX, Filter.EventuallyEq]
  refine condDistrib_ae_eq_of_measure_eq_compProd X (by fun_prop) ?_
  rw [Measure.compProd_deterministic, AEMeasurable.map_map_of_aemeasurable (by fun_prop) hX]
  simp [Function.comp_def]
/-
**ProbabilityTheory.condDistrib_self** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheor
y`。
形式化陈述：condDistrib_self (Y : α -> Ω) : condDistrib Y Y μ =ᵐ[μ.map Y] Kernel.id
参数：Y : α -> Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.condDistrib.congr_simp`：∀ {α : Type u_5} {β : Type u_6
} {Ω : Type u_7} [inst : MeasurableSpace Ω] [inst_1 : StandardBorelSpace Ω]   [i
nst_2 : Nonempty Ω] {x : Measu…
· 使用定理 `CompTriple.comp_eq`：∀ {M : Type u_1} {N : Type u_2} {P : Type u_3} {φ : 
M → N} {ψ : N → P} {χ : outParam (M → P)} [self : CompTriple φ ψ χ],   ψ ∘ φ = χ
· 使用定理 `CompTriple.instIsIdId`：∀ {M : Type u_1}, CompTriple.IsId id
· 使用引理 `ProbabilityTheory.condDistrib_comp_self`：condDistrib_comp_self (X : α ->
 β) {f : β -> Ω} (hf : Measurable f) : condDistrib (f ∘ X) X μ =ᵐ[μ.map X] Kerne
l.deterministic f hf
-/
lemma condDistrib_self (Y : α → Ω) : condDistrib Y Y μ =ᵐ[μ.map Y] Kernel.id := by
  simpa using! condDistrib_comp_self Y measurable_id
/-
**ProbabilityTheory.condDistrib_const** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheo
ry`。
形式化陈述：condDistrib_const (X : α -> β) (c : Ω) : condDistrib (fun _ => c) X μ =ᵐ[μ
.map X] Kernel.deterministic (mα
参数：X : α -> β；c : Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用引理 `ProbabilityTheory.condDistrib_comp_self`：condDistrib_comp_self (X : α ->
 β) {f : β -> Ω} (hf : Measurable f) : condDistrib (f ∘ X) X μ =ᵐ[μ.map X] Kerne
l.deterministic f hf
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
-/
lemma condDistrib_const (X : α → β) (c : Ω) :
    condDistrib (fun _ ↦ c) X μ =ᵐ[μ.map X]
      Kernel.deterministic (mα := mβ) (fun _ ↦ c) (by fun_prop) := by
  have : (fun _ : α ↦ c) = (fun _ : β ↦ c) ∘ X := rfl
  rw [this]
  filter_upwards [condDistrib_comp_self X (measurable_const (a := c))] with b hb
  rw [hb]
/-
**ProbabilityTheory.condDistrib_map** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory
`。
形式化陈述：condDistrib_map {γ : Type*} {mγ : MeasurableSpace γ} {ν : Measure γ} [IsFi
niteMeasure ν] {f : γ -> α} (hX : AEMeasurable X (ν.map f)) (hY : AEMeasurable Y
 (ν.map f)) (hf : AEMeasurable f ν) : condDistrib Y X (ν.map f) =ᵐ[ν.map (X ∘ f)
] condDistrib (Y ∘ f) (X ∘ f) ν
参数：hX : AEMeasurable X (ν.map f)；hY : AEMeasurable Y (ν.map f)；hf : AEMeasurable
 f ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AEMeasurable.map_map_of_aemeasurable`：map_map_of_aemeasurable {g : β -> 
γ} {f : α -> β} (hg : AEMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) 
: (μ.map f).map g = μ.map …
· 使用引理 `ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd`：condDistrib_
ae_eq_of_measure_eq_compProd (X : α -> β) (hY : AEMeasurable Y μ) {κ : Kernel β 
Ω} [IsFiniteKernel κ] (hκ : μ.map (fun x => (X x…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.instIsMarkovKernelCondDistrib`：∀ {α : Type u_1} {β : T
ype u_2} {Ω : Type u_3} [inst : MeasurableSpace Ω] [inst_1 : StandardBorelSpace 
Ω]   [inst_2 : Nonempty Ω] {mα : Meas…
· 使用引理 `ProbabilityTheory.compProd_map_condDistrib`：compProd_map_condDistrib (hY
 : AEMeasurable Y μ) : (μ.map X) otimesₘ condDistrib Y X μ = μ.map fun a => (X a
, Y a)
· 使用定理 `AEMeasurable.comp_aemeasurable'`：comp_aemeasurable' {f : α -> δ} {g : δ 
-> β} (hg : AEMeasurable g (μ.map f)) (hf : AEMeasurable f μ) : AEMeasurable (fu
n x => g (f x)) μ
· 使用定理 `AEMeasurable.prodMk`：prodMk {f : α -> β} {g : α -> γ} (hf : AEMeasurable
 f μ) (hg : AEMeasurable g μ) : AEMeasurable (fun x => (f x, g x)) μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma condDistrib_map {γ : Type*} {mγ : MeasurableSpace γ}
    {ν : Measure γ} [IsFiniteMeasure ν] {f : γ → α}
    (hX : AEMeasurable X (ν.map f)) (hY : AEMeasurable Y (ν.map f)) (hf : AEMeasurable f ν) :
    condDistrib Y X (ν.map f) =ᵐ[ν.map (X ∘ f)] condDistrib (Y ∘ f) (X ∘ f) ν := by
  rw [← AEMeasurable.map_map_of_aemeasurable hX hf]
  refine condDistrib_ae_eq_of_measure_eq_compProd (μ := ν.map f) X hY ?_
  rw [AEMeasurable.map_map_of_aemeasurable hX hf, compProd_map_condDistrib (by fun_prop),
    AEMeasurable.map_map_of_aemeasurable (by fun_prop) hf]
  simp [Function.comp_def]
/-
**ProbabilityTheory.condDistrib_fst_prod** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：condDistrib_fst_prod {γ : Type*} {mγ : MeasurableSpace γ} (X : α -> β) (hY
 : AEMeasurable Y μ) (ν : Measure γ) [IsProbabilityMeasure ν] : condDistrib (fun
 ω => Y ω.1) (fun ω => X ω.1) (μ.prod ν) =ᵐ[μ.map X] condDistrib Y X μ
参数：X : α -> β；hY : AEMeasurable Y μ；ν : Measure γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.prod.instIsFiniteMeasure`：∀ {α : Type u_4} {β : Ty
pe u_5} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (μ : MeasureTheory.Mea
sure α)   (ν : MeasureTheory.Measure…
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用引理 `ProbabilityTheory.condDistrib_map`：condDistrib_map {γ : Type*} {mγ : Mea
surableSpace γ} {ν : Measure γ} [IsFiniteMeasure ν] {f : γ -> α} (hX : AEMeasura
ble X (ν.map f)) (hY : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.map_fst_prod`：∀ {α : Type u_1} {β : Type u_2} [ins
t : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μ : MeasureTheory.Measure α
}   {ν : MeasureTheory.M…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `AEMeasurable.fst`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} {m0 : M
easurableSpace α} [inst : MeasurableSpace β]   [inst_1 : MeasurableSpace γ] {μ :
 Measu…
· 使用定理 `aemeasurable_id`：aemeasurable_id : AEMeasurable id μ
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.ae.congr_simp`：∀ {α : Type u_1} {F : Type u_3} [inst : Fun
Like F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F α]   (μ μ_1 
: F), μ = μ_1 → M…
· 使用定理 `ProbabilityTheory.condDistrib.congr_simp`：∀ {α : Type u_5} {β : Type u_6
} {Ω : Type u_7} [inst : MeasurableSpace Ω] [inst_1 : StandardBorelSpace Ω]   [i
nst_2 : Nonempty Ω] {x : Measu…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AEMeasurable.map_map_of_aemeasurable`：map_map_of_aemeasurable {g : β -> 
γ} {f : α -> β} (hg : AEMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) 
: (μ.map f).map g = μ.map …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.Measure.map_of_not_aemeasurable`：map_of_not_aemeasurable {
f : α -> β} {μ : Measure α} (hf : ¬AEMeasurable f μ) : μ.map f = 0
· 使用定理 `MeasureTheory.ae_zero`：ae_zero {_m0 : MeasurableSpace α} : ae (0 : Measu
re α) = ⊥
-/
lemma condDistrib_fst_prod {γ : Type*} {mγ : MeasurableSpace γ}
    (X : α → β) (hY : AEMeasurable Y μ) (ν : Measure γ) [IsProbabilityMeasure ν] :
    condDistrib (fun ω ↦ Y ω.1) (fun ω ↦ X ω.1) (μ.prod ν) =ᵐ[μ.map X] condDistrib Y X μ := by
  by_cases hX : AEMeasurable X μ
  swap; · simp [Measure.map_of_not_aemeasurable hX, Filter.EventuallyEq]
  have h_map := condDistrib_map (X := X) (Y := Y) (f := Prod.fst (α := α) (β := γ))
      (ν := μ.prod ν) (mα := inferInstance) (mβ := inferInstance)
      (by simpa) (by simpa) (by fun_prop)
  rw [← AEMeasurable.map_map_of_aemeasurable (by simpa) (by fun_prop)] at h_map
  simp only [Measure.map_fst_prod, measure_univ, one_smul] at h_map
  exact h_map.symm
/-
**ProbabilityTheory.condDistrib_snd_prod** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：condDistrib_snd_prod {γ : Type*} {mγ : MeasurableSpace γ} (X : α -> β) (hY
 : AEMeasurable Y μ) (ν : Measure γ) [IsProbabilityMeasure ν] : condDistrib (fun
 ω => Y ω.2) (fun ω => X ω.2) (ν.prod μ) =ᵐ[μ.map X] condDistrib Y X μ
参数：X : α -> β；hY : AEMeasurable Y μ；ν : Measure γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.prod.instIsFiniteMeasure`：∀ {α : Type u_4} {β : Ty
pe u_5} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (μ : MeasureTheory.Mea
sure α)   (ν : MeasureTheory.Measure…
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用引理 `ProbabilityTheory.condDistrib_map`：condDistrib_map {γ : Type*} {mγ : Mea
surableSpace γ} {ν : Measure γ} [IsFiniteMeasure ν] {f : γ -> α} (hX : AEMeasura
ble X (ν.map f)) (hY : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.map_snd_prod`：∀ {α : Type u_1} {β : Type u_2} [ins
t : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μ : MeasureTheory.Measure α
}   {ν : MeasureTheory.M…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `AEMeasurable.snd`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} {m0 : M
easurableSpace α} [inst : MeasurableSpace β]   [inst_1 : MeasurableSpace γ] {μ :
 Measu…
· 使用定理 `aemeasurable_id`：aemeasurable_id : AEMeasurable id μ
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.ae.congr_simp`：∀ {α : Type u_1} {F : Type u_3} [inst : Fun
Like F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F α]   (μ μ_1 
: F), μ = μ_1 → M…
· 使用定理 `ProbabilityTheory.condDistrib.congr_simp`：∀ {α : Type u_5} {β : Type u_6
} {Ω : Type u_7} [inst : MeasurableSpace Ω] [inst_1 : StandardBorelSpace Ω]   [i
nst_2 : Nonempty Ω] {x : Measu…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AEMeasurable.map_map_of_aemeasurable`：map_map_of_aemeasurable {g : β -> 
γ} {f : α -> β} (hg : AEMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) 
: (μ.map f).map g = μ.map …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.Measure.map_of_not_aemeasurable`：map_of_not_aemeasurable {
f : α -> β} {μ : Measure α} (hf : ¬AEMeasurable f μ) : μ.map f = 0
· 使用定理 `MeasureTheory.ae_zero`：ae_zero {_m0 : MeasurableSpace α} : ae (0 : Measu
re α) = ⊥
-/
lemma condDistrib_snd_prod {γ : Type*} {mγ : MeasurableSpace γ}
    (X : α → β) (hY : AEMeasurable Y μ) (ν : Measure γ) [IsProbabilityMeasure ν] :
    condDistrib (fun ω ↦ Y ω.2) (fun ω ↦ X ω.2) (ν.prod μ) =ᵐ[μ.map X] condDistrib Y X μ := by
  by_cases hX : AEMeasurable X μ
  swap; · simp [Measure.map_of_not_aemeasurable hX, Filter.EventuallyEq]
  have h_map := condDistrib_map (X := X) (Y := Y) (f := Prod.snd (β := α) (α := γ))
      (ν := ν.prod μ) (mα := inferInstance) (mβ := inferInstance)
      (by simpa) (by simpa) (by fun_prop)
  rw [← AEMeasurable.map_map_of_aemeasurable (by simpa) (by fun_prop)] at h_map
  simp only [Measure.map_snd_prod, measure_univ, one_smul] at h_map
  exact h_map.symm

section Integrability

/-
**ProbabilityTheory.integrable_toReal_condDistrib** 是 Mathlib 中的一个定理，位于命名空间 `Pro
babilityTheory`。
形式化陈述：integrable_toReal_condDistrib (hX : AEMeasurable X μ) (hs : MeasurableSet 
s) : Integrable (fun a => (condDistrib Y X μ (X a)).real s) μ
参数：hX : AEMeasurable X μ；hs : MeasurableSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integrable_toReal_of_lintegral_ne_top`：integrable_toReal_o
f_lintegral_ne_top {f : α -> Real>=0∞} (hfm : AEMeasurable f μ) (hfi : ∫⁻ x, f x
 ∂μ != ∞) : Integrable (fun x => (f x).to…
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `ProbabilityTheory.Kernel.measurable_coe`：∀ {α : Type u_1} {β : Type u_2}
 {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ : ProbabilityTheory.Kernel
 α β)   {s : Set β}, Measurab…
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `MeasureTheory.lintegral_mono`：lintegral_mono ⦃f g : α -> Real>=0∞⦄ (hfg 
: f <= g) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用引理 `MeasureTheory.prob_le_one`：prob_le_one {μ : Measure α} [IsZeroOrProbabil
ityMeasure μ] {s : Set α} : μ s <= 1
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isZeroOrProbabilityMeasure`：∀ {α 
: Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ 
: ProbabilityTheory.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.instIsMarkovKernelCondDistrib`：∀ {α : Type u_1} {β : T
ype u_2} {Ω : Type u_3} [inst : MeasurableSpace Ω] [inst_1 : StandardBorelSpace 
Ω]   [inst_2 : Nonempty Ω] {mα : Meas…
· 使用定理 `MeasureTheory.lintegral_one`：lintegral_one : ∫⁻ _, (1 : Real>=0∞) ∂μ = μ
 univ
· 使用定理 `MeasureTheory.measure_lt_top`：measure_lt_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s < ∞
-/
theorem integrable_toReal_condDistrib (hX : AEMeasurable X μ) (hs : MeasurableSet s) :
    Integrable (fun a => (condDistrib Y X μ (X a)).real s) μ := by
  refine integrable_toReal_of_lintegral_ne_top ?_ ?_
  · exact Measurable.comp_aemeasurable (Kernel.measurable_coe _ hs) hX
  · refine ne_of_lt ?_
    calc
      ∫⁻ a, condDistrib Y X μ (X a) s ∂μ ≤ ∫⁻ _, 1 ∂μ := lintegral_mono fun a => prob_le_one
      _ = μ univ := lintegral_one
      _ < ∞ := measure_lt_top _ _
/-
**ProbabilityTheory._root_.MeasureTheory.Integrable.condDistrib_ae_map** 是 Mathl
ib 中的一个定理，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.Integrable.condDistrib_ae_map
    (hY : AEMeasurable Y μ) (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    ∀ᵐ b ∂μ.map X, Integrable (fun ω => f (b, ω)) (condDistrib Y X μ b) := by
  rw [condDistrib, ← Measure.fst_map_prodMk₀ (X := X) hY]; exact hf_int.condKernel_ae
/-
**ProbabilityTheory._root_.MeasureTheory.Integrable.condDistrib_ae** 是 Mathlib 中
的一个定理，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.Integrable.condDistrib_ae (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    ∀ᵐ a ∂μ, Integrable (fun ω => f (X a, ω)) (condDistrib Y X μ (X a)) :=
  ae_of_ae_map hX (hf_int.condDistrib_ae_map hY)
/-
**ProbabilityTheory._root_.MeasureTheory.Integrable.integral_norm_condDistrib_ma
p** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.Integrable.integral_norm_condDistrib_map
    (hY : AEMeasurable Y μ) (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    Integrable (fun x => ∫ y, ‖f (x, y)‖ ∂condDistrib Y X μ x) (μ.map X) := by
  rw [condDistrib, ← Measure.fst_map_prodMk₀ (X := X) hY]; exact hf_int.integral_norm_condKernel
/-
**ProbabilityTheory._root_.MeasureTheory.Integrable.integral_norm_condDistrib** 
是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.Integrable.integral_norm_condDistrib (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    Integrable (fun a => ∫ y, ‖f (X a, y)‖ ∂condDistrib Y X μ (X a)) μ :=
  (hf_int.integral_norm_condDistrib_map hY).comp_aemeasurable hX

variable [NormedSpace ℝ F]
/-
**ProbabilityTheory._root_.MeasureTheory.Integrable.norm_integral_condDistrib_ma
p** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.Integrable.norm_integral_condDistrib_map
    (hY : AEMeasurable Y μ) (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    Integrable (fun x => ‖∫ y, f (x, y) ∂condDistrib Y X μ x‖) (μ.map X) := by
  rw [condDistrib, ← Measure.fst_map_prodMk₀ (X := X) hY]; exact hf_int.norm_integral_condKernel
/-
**ProbabilityTheory._root_.MeasureTheory.Integrable.norm_integral_condDistrib** 
是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.Integrable.norm_integral_condDistrib (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    Integrable (fun a => ‖∫ y, f (X a, y) ∂condDistrib Y X μ (X a)‖) μ :=
  (hf_int.norm_integral_condDistrib_map hY).comp_aemeasurable hX
/-
**ProbabilityTheory._root_.MeasureTheory.Integrable.integral_condDistrib_map** 是
 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.Integrable.integral_condDistrib_map
    (hY : AEMeasurable Y μ) (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    Integrable (fun x => ∫ y, f (x, y) ∂condDistrib Y X μ x) (μ.map X) :=
  (integrable_norm_iff (hf_int.1.integral_condDistrib_map hY)).mp
    (hf_int.norm_integral_condDistrib_map hY)
/-
**ProbabilityTheory._root_.MeasureTheory.Integrable.integral_condDistrib** 是 Mat
hlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.Integrable.integral_condDistrib (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    Integrable (fun a => ∫ y, f (X a, y) ∂condDistrib Y X μ (X a)) μ :=
  (hf_int.integral_condDistrib_map hY).comp_aemeasurable hX

end Integrability

/-
**ProbabilityTheory.setLIntegral_preimage_condDistrib** 是 Mathlib 中的一个定理，位于命名空间 
`ProbabilityTheory`。
形式化陈述：setLIntegral_preimage_condDistrib (hX : Measurable X) (hY : AEMeasurable Y
 μ) (hs : MeasurableSet s) (ht : MeasurableSet t) : ∫⁻ a in X ⁻¹' t, condDistrib
 Y X μ (X a) s ∂μ = μ (X ⁻¹' t inter Y ⁻¹' s)
参数：hX : Measurable X；hY : AEMeasurable Y μ；hs : MeasurableSet s；ht : MeasurableS
et t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_map`：lintegral_map {f : β -> Real>=0∞} {g : α ->
 β} (hf : Measurable f) (hg : Measurable g) : ∫⁻ a, f a ∂map g μ = ∫⁻ a, f (g a)
 ∂μ
· 使用定理 `ProbabilityTheory.Kernel.measurable_coe`：∀ {α : Type u_1} {β : Type u_2}
 {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ : ProbabilityTheory.Kernel
 α β)   {s : Set β}, Measurab…
· 使用定理 `ProbabilityTheory.condDistrib_def`：∀ {α : Type u_5} {β : Type u_6} {Ω : 
Type u_7} [inst : MeasurableSpace Ω] [inst_1 : StandardBorelSpace Ω]   [inst_2 :
 Nonempty Ω] {x : Measu…
· 使用定理 `MeasureTheory.Measure.restrict_map`：restrict_map {f : α -> β} (hf : Meas
urable f) {s : Set β} (hs : MeasurableSet s) : (μ.map f).restrict s = (μ.restric
t <| f ⁻¹' s).map f
· 使用定理 `MeasureTheory.Measure.fst_map_prodMk₀`：fst_map_prodMk₀ {X : α -> β} {Y :
 α -> γ} {μ : Measure α} (hY : AEMeasurable Y μ) : (μ.map fun a => (X a, Y a)).f
st = μ.map X
· 使用引理 `MeasureTheory.Measure.setLIntegral_condKernel_eq_measure_prod`：setLInteg
ral_condKernel_eq_measure_prod {s : Set β} (hs : MeasurableSet s) {t : Set Ω} (h
t : MeasurableSet t) : ∫⁻ b in s, ρ.condKernel b t …
· 使用定理 `MeasureTheory.Measure.map_apply_of_aemeasurable`：map_apply_of_aemeasurab
le (hf : AEMeasurable f μ) {s : Set β} (hs : MeasurableSet s) : μ.map f s = μ (f
 ⁻¹' s)
· 使用定理 `AEMeasurable.prodMk`：prodMk {f : α -> β} {g : α -> γ} (hf : AEMeasurable
 f μ) (hg : AEMeasurable g μ) : AEMeasurable (fun x => (f x, g x)) μ
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasurableSet.prod`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace
 α} {mβ : MeasurableSpace β} {s : Set α} {t : Set β},   MeasurableSet s → Measur
ableSet …
· 使用定理 `Set.mk_preimage_prod`：mk_preimage_prod (f : γ -> α) (g : γ -> β) : (fun 
x => (f x, g x)) ⁻¹' s ×ˢ t = f ⁻¹' s inter g ⁻¹' t
-/
theorem setLIntegral_preimage_condDistrib (hX : Measurable X) (hY : AEMeasurable Y μ)
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    ∫⁻ a in X ⁻¹' t, condDistrib Y X μ (X a) s ∂μ = μ (X ⁻¹' t ∩ Y ⁻¹' s) := by
  rw [← lintegral_map (Kernel.measurable_coe _ hs) hX, condDistrib, ← Measure.restrict_map hX ht,
    ← Measure.fst_map_prodMk₀ hY, Measure.setLIntegral_condKernel_eq_measure_prod ht hs,
    Measure.map_apply_of_aemeasurable (hX.aemeasurable.prodMk hY) (ht.prod hs), mk_preimage_prod]
/-
**ProbabilityTheory.setLIntegral_condDistrib_of_measurableSet** 是 Mathlib 中的一个定理
，位于命名空间 `ProbabilityTheory`。
形式化陈述：setLIntegral_condDistrib_of_measurableSet (hX : Measurable X) (hY : AEMeas
urable Y μ) (hs : MeasurableSet s) {t : Set α} (ht : MeasurableSet[mβ.comap X] t
) : ∫⁻ a in t, condDistrib Y X μ (X a) s ∂μ = μ (t inter Y ⁻¹' s)
参数：hX : Measurable X；hY : AEMeasurable Y μ；hs : MeasurableSet s；ht : MeasurableS
et[mβ.comap X] t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.setLIntegral_preimage_condDistrib`：setLIntegral_preima
ge_condDistrib (hX : Measurable X) (hY : AEMeasurable Y μ) (hs : MeasurableSet s
) (ht : MeasurableSet t) : ∫⁻ a in X ⁻¹' …
-/
theorem setLIntegral_condDistrib_of_measurableSet (hX : Measurable X) (hY : AEMeasurable Y μ)
    (hs : MeasurableSet s) {t : Set α} (ht : MeasurableSet[mβ.comap X] t) :
    ∫⁻ a in t, condDistrib Y X μ (X a) s ∂μ = μ (t ∩ Y ⁻¹' s) := by
  obtain ⟨t', ht', rfl⟩ := ht
  rw [setLIntegral_preimage_condDistrib hX hY hs ht']

/-- For almost every `a : α`, the `condDistrib Y X μ` kernel applied to `X a` and a measurable set
`s` is equal to the conditional expectation of the indicator of `Y ⁻¹' s`. -/
/-
**ProbabilityTheory.condDistrib_ae_eq_condExp** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory`。
形式化陈述：condDistrib_ae_eq_condExp (hX : Measurable X) (hY : Measurable Y) (hs : Me
asurableSet s) : (fun a => (condDistrib Y X μ (X a)).real s) =ᵐ[μ] μ⟦Y ⁻¹' s | m
β.comap X⟧
参数：hX : Measurable X；hY : Measurable Y；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq`：ae_eq_condExp_of_f
orall_setIntegral_eq (hm : m <= m₀) [SigmaFinite (μ.trim hm)] {f g : α -> E} (hf
 : Integrable f μ) (hg_int_finite : forall…
· 使用定理 `Measurable.comap_le`：∀ {α : Type u_1} {β : Type u_2} {m₁ : MeasurableSpa
ce α} {m₂ : MeasurableSpace β} {f : α → β},   Measurable f → MeasurableSpace.com
ap f m₂ ≤…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.Integrable.indicator`：∀ {α : Type u_1} {ε' : Type u_4} {mα
 : MeasurableSpace α} {s : Set α} {μ : MeasureTheory.Measure α}   [inst : Topolo
gicalSpace ε'] [inst_1 :…
· 使用定理 `MeasureTheory.integrable_const`：integrable_const [IsFiniteMeasure μ] (c 
: β) : Integrable (fun _ : α => c) μ
· 使用定理 `MeasureTheory.Integrable.integrableOn`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
· 使用定理 `ProbabilityTheory.integrable_toReal_condDistrib`：integrable_toReal_condD
istrib (hX : AEMeasurable X μ) (hs : MeasurableSet s) : Integrable (fun a => (co
ndDistrib Y X μ (X a)).real s) μ
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_toReal`：integral_toReal {f : α -> Real>=0∞} (hfm 
: AEMeasurable f μ) (hf : forallᵐ x ∂μ, f x < ∞) : ∫ a, (f a).toReal ∂μ = (∫⁻ a,
 f a ∂μ).toReal
· 使用定理 `Measurable.mono`：Measurable.mono {ma ma' : MeasurableSpace α} {mb mb' : 
MeasurableSpace β} {f : α -> β} (hf : @Measurable α β ma mb f) (ha : ma <= ma') 
(hb :…
· 使用定理 `ProbabilityTheory.measurable_condDistrib`：measurable_condDistrib (hs : M
easurableSet s) : Measurable[mβ.comap X] fun a => condDistrib Y X μ (X a) s
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.measure_lt_top`：measure_lt_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s < ∞
· 使用定理 `ProbabilityTheory.IsFiniteKernel.isFiniteMeasure`：∀ {α : Type u_1} {β : 
Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheo
ry.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.instIsMarkovKernelCondDistrib`：∀ {α : Type u_1} {β : T
ype u_2} {Ω : Type u_3} [inst : MeasurableSpace Ω] [inst_1 : StandardBorelSpace 
Ω]   [inst_2 : Nonempty Ω] {mα : Meas…
· 使用定理 `MeasureTheory.integral_indicator_const`：integral_indicator_const [Comple
teSpace E] (e : E) ⦃s : Set X⦄ (s_meas : MeasurableSet s) : ∫ x : X, s.indicator
 (fun _ : X => e) x ∂μ = μ.r…
· 使用定理 `MeasureTheory.measureReal_restrict_apply`：measureReal_restrict_apply (ht
 : MeasurableSet t) : (μ.restrict s).real t = μ.real (t inter s)
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `ProbabilityTheory.setLIntegral_condDistrib_of_measurableSet`：setLIntegra
l_condDistrib_of_measurableSet (hX : Measurable X) (hY : AEMeasurable Y μ) (hs :
 MeasurableSet s) {t : Set α} (ht : MeasurableSet…
· 使用定理 `MeasureTheory.measureReal_def`：measureReal_def {α : Type*} {m : Measurab
leSpace α} (μ : Measure α) (s : Set α) : μ.real s = (μ s).toReal
· 使用定理 `Measurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 :…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
For almost every `a : α`, the `condDistrib Y X μ` kernel applied to `X a` and a 
measurable set
`s` is equal to the conditional expectation of the indicator of `Y ⁻¹' s`.
-/
theorem condDistrib_ae_eq_condExp (hX : Measurable X) (hY : Measurable Y) (hs : MeasurableSet s) :
    (fun a => (condDistrib Y X μ (X a)).real s) =ᵐ[μ] μ⟦Y ⁻¹' s | mβ.comap X⟧ := by
  refine ae_eq_condExp_of_forall_setIntegral_eq hX.comap_le ?_ ?_ ?_ ?_
  · exact (integrable_const _).indicator (hY hs)
  · exact fun t _ _ => (integrable_toReal_condDistrib hX.aemeasurable hs).integrableOn
  · intro t ht _
    simp_rw [measureReal_def]
    rw [integral_toReal ((measurable_condDistrib hs).mono hX.comap_le le_rfl).aemeasurable
      (Eventually.of_forall fun ω => measure_lt_top (condDistrib Y X μ (X ω)) _),
      integral_indicator_const _ (hY hs), measureReal_restrict_apply (hY hs), smul_eq_mul, mul_one,
      inter_comm, setLIntegral_condDistrib_of_measurableSet hX hY.aemeasurable hs ht,
      measureReal_def]
  · exact (measurable_condDistrib hs).ennreal_toReal.aestronglyMeasurable

/-- The conditional expectation of a function `f` of the product `(X, Y)` is almost everywhere equal
to the integral of `y ↦ f(X, y)` against the `condDistrib` kernel. -/
/-
**ProbabilityTheory.condExp_prod_ae_eq_integral_condDistrib'** 是 Mathlib 中的一个定理，
位于命名空间 `ProbabilityTheory`。
形式化陈述：condExp_prod_ae_eq_integral_condDistrib' [NormedSpace Real F] [CompleteSpa
ce F] (hX : Measurable X) (hY : AEMeasurable Y μ) (hf_int : Integrable f (μ.map 
fun a => (X a, Y a))) : μ[fun a => f (X a, Y a) | mβ.comap X] =ᵐ[μ] fun a => ∫ y
, f (X a, y) ∂condDistrib Y X μ (X a)
参数：hX : Measurable X；hY : AEMeasurable Y μ；hf_int : Integrable f (μ.map fun a =>
 (X a, Y a))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.integrable_map_measure`：integrable_map_measure {f : α -> α
'} {g : α' -> ε} (hg : AEStronglyMeasurable g (Measure.map f μ)) (hf : AEMeasura
ble f μ) : Integrable g (M…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `AEMeasurable.prodMk`：prodMk {f : α -> β} {g : α -> γ} (hf : AEMeasurable
 f μ) (hg : AEMeasurable g μ) : AEMeasurable (fun x => (f x, g x)) μ
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq`：ae_eq_condExp_of_f
orall_setIntegral_eq (hm : m <= m₀) [SigmaFinite (μ.trim hm)] {f g : α -> E} (hf
 : Integrable f μ) (hg_int_finite : forall…
· 使用定理 `Measurable.comap_le`：∀ {α : Type u_1} {β : Type u_2} {m₁ : MeasurableSpa
ce α} {m₂ : MeasurableSpace β} {f : α → β},   Measurable f → MeasurableSpace.com
ap f m₂ ≤…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.Integrable.integrableOn`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
· 使用定理 `MeasureTheory.Integrable.integral_condDistrib`：∀ {α : Type u_1} {β : Typ
e u_2} {Ω : Type u_3} {F : Type u_4} [inst : MeasurableSpace Ω] [inst_1 : Standa
rdBorelSpace Ω]   [inst_2 : Nonempt…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_map`：integral_map {β} [MeasurableSpace β] {φ : α 
-> β} (hφ : AEMeasurable φ μ) {f : β -> G} (hfm : AEStronglyMeasurable f (Measur
e.map φ μ)) : ∫ …
· 使用定理 `MeasureTheory.Measure.restrict_map`：restrict_map {f : α -> β} (hf : Meas
urable f) {s : Set β} (hs : MeasurableSet s) : (μ.map f).restrict s = (μ.restric
t <| f ⁻¹' s).map f
· 使用定理 `MeasureTheory.AEStronglyMeasurable.restrict`：∀ {α : Type u_1} {β : Type 
u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.M
easure α}   {f : α → β},   Measur…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.integral_condDistrib_map`：∀ {α : Type
 u_1} {β : Type u_2} {Ω : Type u_3} {F : Type u_4} [inst : MeasurableSpace Ω] [i
nst_1 : StandardBorelSpace Ω]   [inst_2 : Nonempt…
· 使用定理 `MeasureTheory.Measure.fst_map_prodMk₀`：fst_map_prodMk₀ {X : α -> β} {Y :
 α -> γ} {μ : Measure α} (hY : AEMeasurable Y μ) : (μ.map fun a => (X a, Y a)).f
st = μ.map X
· 使用定理 `ProbabilityTheory.condDistrib_def`：∀ {α : Type u_5} {β : Type u_6} {Ω : 
Type u_7} [inst : MeasurableSpace Ω] [inst_1 : StandardBorelSpace Ω]   [inst_2 :
 Nonempty Ω] {x : Measu…
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用引理 `MeasureTheory.Measure.setIntegral_condKernel_univ_right`：setIntegral_con
dKernel_univ_right {s : Set β} (hs : MeasurableSet s) (hf : IntegrableOn f (s ×ˢ
 Set.univ) ρ) : ∫ b in s, ∫ ω, f (b, ω) ∂(ρ.c…
· 使用定理 `MeasureTheory.setIntegral_map`：setIntegral_map {Y} [MeasurableSpace Y] {
g : X -> Y} {f : Y -> E} {s : Set Y} (hs : MeasurableSet s) (hf : AEStronglyMeas
urable f (Measure.m…
· 使用定理 `MeasurableSet.prod`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace
 α} {mβ : MeasurableSpace β} {s : Set α} {t : Set β},   MeasurableSet s → Measur
ableSet …
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `Set.mk_preimage_prod`：mk_preimage_prod (f : γ -> α) (g : γ -> β) : (fun 
x => (f x, g x)) ⁻¹' s ×ˢ t = f ⁻¹' s inter g ⁻¹' t
· 使用定理 `Set.preimage_univ`：preimage_univ : f ⁻¹' univ = univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `ProbabilityTheory.aestronglyMeasurable_integral_condDistrib`：aestronglyM
easurable_integral_condDistrib (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) (
hf : AEStronglyMeasurable f (μ.map fun a => (X a,…

--- 原说明 ---
The conditional expectation of a function `f` of the product `(X, Y)` is almost 
everywhere equal
to the integral of `y ↦ f(X, y)` against the `condDistrib` kernel.
-/
theorem condExp_prod_ae_eq_integral_condDistrib' [NormedSpace ℝ F] [CompleteSpace F]
    (hX : Measurable X) (hY : AEMeasurable Y μ)
    (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    μ[fun a => f (X a, Y a) | mβ.comap X] =ᵐ[μ]
      fun a => ∫ y, f (X a, y) ∂condDistrib Y X μ (X a) := by
  have hf_int' : Integrable (fun a => f (X a, Y a)) μ :=
    (integrable_map_measure hf_int.1 (hX.aemeasurable.prodMk hY)).mp hf_int
  refine (ae_eq_condExp_of_forall_setIntegral_eq hX.comap_le hf_int' (fun s _ _ => ?_) ?_ ?_).symm
  · exact (hf_int.integral_condDistrib hX.aemeasurable hY).integrableOn
  · rintro s ⟨t, ht, rfl⟩ _
    change ∫ a in X ⁻¹' t, ((fun x' => ∫ y, f (x', y) ∂(condDistrib Y X μ) x') ∘ X) a ∂μ =
      ∫ a in X ⁻¹' t, f (X a, Y a) ∂μ
    simp only [Function.comp_apply]
    rw [← integral_map hX.aemeasurable (f := fun x' => ∫ y, f (x', y) ∂(condDistrib Y X μ) x')]
    swap
    · rw [← Measure.restrict_map hX ht]
      exact (hf_int.1.integral_condDistrib_map hY).restrict
    rw [← Measure.restrict_map hX ht, ← Measure.fst_map_prodMk₀ hY, condDistrib,
      Measure.setIntegral_condKernel_univ_right ht hf_int.integrableOn,
      setIntegral_map (ht.prod MeasurableSet.univ) hf_int.1 (hX.aemeasurable.prodMk hY),
      mk_preimage_prod, preimage_univ, inter_univ]
  · exact aestronglyMeasurable_integral_condDistrib hX.aemeasurable hY hf_int.1

/-- The conditional expectation of a function `f` of the product `(X, Y)` is almost everywhere equal
to the integral of `y ↦ f(X, y)` against the `condDistrib` kernel. -/
/-
**ProbabilityTheory.condExp_prod_ae_eq_integral_condDistrib** 是 Mathlib 中的一个定理，位
于命名空间 `ProbabilityTheory`。
形式化陈述：condExp_prod_ae_eq_integral_condDistrib [NormedSpace Real F] [CompleteSpac
e F] (hX : Measurable X) (hY : AEMeasurable Y μ) (hf : StronglyMeasurable f) (hf
_int : Integrable (fun a => f (X a, Y a)) μ) : μ[fun a => f (X a, Y a) | mβ.coma
p X] =ᵐ[μ] fun a => ∫ y, f (X a, y) ∂condDistrib Y X μ (X a)
参数：hX : Measurable X；hY : AEMeasurable Y μ；hf : StronglyMeasurable f；hf_int : In
tegrable (fun a => f (X a, Y a)) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integrable_map_measure`：integrable_map_measure {f : α -> α
'} {g : α' -> ε} (hg : AEStronglyMeasurable g (Measure.map f μ)) (hf : AEMeasura
ble f μ) : Integrable g (M…
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `AEMeasurable.prodMk`：prodMk {f : α -> β} {g : α -> γ} (hf : AEMeasurable
 f μ) (hg : AEMeasurable g μ) : AEMeasurable (fun x => (f x, g x)) μ
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `ProbabilityTheory.condExp_prod_ae_eq_integral_condDistrib'`：condExp_prod
_ae_eq_integral_condDistrib' [NormedSpace Real F] [CompleteSpace F] (hX : Measur
able X) (hY : AEMeasurable Y μ) (hf_int : Integr…

--- 原说明 ---
The conditional expectation of a function `f` of the product `(X, Y)` is almost 
everywhere equal
to the integral of `y ↦ f(X, y)` against the `condDistrib` kernel.
-/
theorem condExp_prod_ae_eq_integral_condDistrib₀ [NormedSpace ℝ F] [CompleteSpace F]
    (hX : Measurable X) (hY : AEMeasurable Y μ)
    (hf : AEStronglyMeasurable f (μ.map fun a => (X a, Y a)))
    (hf_int : Integrable (fun a => f (X a, Y a)) μ) :
    μ[fun a => f (X a, Y a) | mβ.comap X] =ᵐ[μ] fun a => ∫ y, f (X a, y) ∂condDistrib Y X μ (X a) :=
  have hf_int' : Integrable f (μ.map fun a => (X a, Y a)) := by
    rwa [integrable_map_measure hf (hX.aemeasurable.prodMk hY)]
  condExp_prod_ae_eq_integral_condDistrib' hX hY hf_int'

/-- The conditional expectation of a function `f` of the product `(X, Y)` is almost everywhere equal
to the integral of `y ↦ f(X, y)` against the `condDistrib` kernel. -/
/-
**ProbabilityTheory.condExp_prod_ae_eq_integral_condDistrib** 是 Mathlib 中的一个定理，位
于命名空间 `ProbabilityTheory`。
形式化陈述：condExp_prod_ae_eq_integral_condDistrib [NormedSpace Real F] [CompleteSpac
e F] (hX : Measurable X) (hY : AEMeasurable Y μ) (hf : StronglyMeasurable f) (hf
_int : Integrable (fun a => f (X a, Y a)) μ) : μ[fun a => f (X a, Y a) | mβ.coma
p X] =ᵐ[μ] fun a => ∫ y, f (X a, y) ∂condDistrib Y X μ (X a)
参数：hX : Measurable X；hY : AEMeasurable Y μ；hf : StronglyMeasurable f；hf_int : In
tegrable (fun a => f (X a, Y a)) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integrable_map_measure`：integrable_map_measure {f : α -> α
'} {g : α' -> ε} (hg : AEStronglyMeasurable g (Measure.map f μ)) (hf : AEMeasura
ble f μ) : Integrable g (M…
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `AEMeasurable.prodMk`：prodMk {f : α -> β} {g : α -> γ} (hf : AEMeasurable
 f μ) (hg : AEMeasurable g μ) : AEMeasurable (fun x => (f x, g x)) μ
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `ProbabilityTheory.condExp_prod_ae_eq_integral_condDistrib'`：condExp_prod
_ae_eq_integral_condDistrib' [NormedSpace Real F] [CompleteSpace F] (hX : Measur
able X) (hY : AEMeasurable Y μ) (hf_int : Integr…

--- 原说明 ---
The conditional expectation of a function `f` of the product `(X, Y)` is almost 
everywhere equal
to the integral of `y ↦ f(X, y)` against the `condDistrib` kernel.
-/
theorem condExp_prod_ae_eq_integral_condDistrib [NormedSpace ℝ F] [CompleteSpace F]
    (hX : Measurable X) (hY : AEMeasurable Y μ) (hf : StronglyMeasurable f)
    (hf_int : Integrable (fun a => f (X a, Y a)) μ) :
    μ[fun a => f (X a, Y a) | mβ.comap X] =ᵐ[μ] fun a => ∫ y, f (X a, y) ∂condDistrib Y X μ (X a) :=
  have hf_int' : Integrable f (μ.map fun a => (X a, Y a)) := by
    rwa [integrable_map_measure hf.aestronglyMeasurable (hX.aemeasurable.prodMk hY)]
  condExp_prod_ae_eq_integral_condDistrib' hX hY hf_int'
/-
**ProbabilityTheory.condExp_ae_eq_integral_condDistrib** 是 Mathlib 中的一个定理，位于命名空间
 `ProbabilityTheory`。
形式化陈述：condExp_ae_eq_integral_condDistrib [NormedSpace Real F] [CompleteSpace F] 
(hX : Measurable X) (hY : AEMeasurable Y μ) {f : Ω -> F} (hf : StronglyMeasurabl
e f) (hf_int : Integrable (fun a => f (Y a)) μ) : μ[fun a => f (Y a) | mβ.comap 
X] =ᵐ[μ] fun a => ∫ y, f y ∂condDistrib Y X μ (X a)
参数：hX : Measurable X；hY : AEMeasurable Y μ；hf : StronglyMeasurable f；hf_int : In
tegrable (fun a => f (Y a)) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.condExp_prod_ae_eq_integral_condDistrib`：condExp_prod_
ae_eq_integral_condDistrib [NormedSpace Real F] [CompleteSpace F] (hX : Measurab
le X) (hY : AEMeasurable Y μ) (hf : StronglyMea…
· 使用定理 `MeasureTheory.StronglyMeasurable.comp_measurable`：comp_measurable [Topol
ogicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ} {f : α -> β} {g :
 γ -> α} (hf : StronglyMeasurable f) (…
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
-/
theorem condExp_ae_eq_integral_condDistrib [NormedSpace ℝ F] [CompleteSpace F] (hX : Measurable X)
    (hY : AEMeasurable Y μ) {f : Ω → F} (hf : StronglyMeasurable f)
    (hf_int : Integrable (fun a => f (Y a)) μ) :
    μ[fun a => f (Y a) | mβ.comap X] =ᵐ[μ] fun a => ∫ y, f y ∂condDistrib Y X μ (X a) :=
  condExp_prod_ae_eq_integral_condDistrib hX hY (hf.comp_measurable measurable_snd) hf_int

/-- The conditional expectation of `Y` given `X` is almost everywhere equal to the integral
`∫ y, y ∂(condDistrib Y X μ (X a))`. -/
/-
**ProbabilityTheory.condExp_ae_eq_integral_condDistrib'** 是 Mathlib 中的一个定理，位于命名空
间 `ProbabilityTheory`。
形式化陈述：condExp_ae_eq_integral_condDistrib' {Ω : Type*} [NormedAddCommGroup Ω] [No
rmedSpace Real Ω] [CompleteSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω] [SecondCo
untableTopology Ω] {Y : α -> Ω} (hX : Measurable X) (hY_int : Integrable Y μ) : 
μ[Y | mβ.comap X] =ᵐ[μ] fun a => ∫ y, y ∂condDistrib Y X μ (X a)
参数：hX : Measurable X；hY_int : Integrable Y μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.condExp_ae_eq_integral_condDistrib`：condExp_ae_eq_inte
gral_condDistrib [NormedSpace Real F] [CompleteSpace F] (hX : Measurable X) (hY 
: AEMeasurable Y μ) {f : Ω -> F} (hf : Str…
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `stronglyMeasurable_id`：∀ {α : Type u_1} {mα : MeasurableSpace α} [inst :
 TopologicalSpace α] [TopologicalSpace.PseudoMetrizableSpace α]   [OpensMeasurab
leSpace α] …
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α

--- 原说明 ---
The conditional expectation of `Y` given `X` is almost everywhere equal to the i
ntegral
`∫ y, y ∂(condDistrib Y X μ (X a))`.
-/
theorem condExp_ae_eq_integral_condDistrib' {Ω : Type*} [NormedAddCommGroup Ω] [NormedSpace ℝ Ω]
    [CompleteSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω] [SecondCountableTopology Ω] {Y : α → Ω}
    (hX : Measurable X) (hY_int : Integrable Y μ) :
    μ[Y | mβ.comap X] =ᵐ[μ] fun a => ∫ y, y ∂condDistrib Y X μ (X a) :=
  condExp_ae_eq_integral_condDistrib hX hY_int.1.aemeasurable stronglyMeasurable_id hY_int

open MeasureTheory
/-
**ProbabilityTheory._root_.MeasureTheory.AEStronglyMeasurable.comp_snd_map_prodM
k** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.AEStronglyMeasurable.comp_snd_map_prodMk {Ω F} {mΩ : MeasurableSpace Ω}
    (X : Ω → β) {μ : Measure Ω} [TopologicalSpace F] {f : Ω → F} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x : β × Ω => f x.2) (μ.map fun ω => (X ω, ω)) := by
  refine ⟨fun x => hf.mk f x.2, hf.stronglyMeasurable_mk.comp_measurable measurable_snd, ?_⟩
  suffices h : Measure.QuasiMeasurePreserving Prod.snd (μ.map fun ω ↦ (X ω, ω)) μ from
    Measure.QuasiMeasurePreserving.ae_eq h hf.ae_eq_mk
  refine ⟨measurable_snd, Measure.AbsolutelyContinuous.mk fun s hs hμs => ?_⟩
  rw [Measure.map_apply measurable_snd hs]
  by_cases hX : AEMeasurable X μ
  · rw [Measure.map_apply_of_aemeasurable]
    · rw [← univ_prod, mk_preimage_prod, preimage_univ, univ_inter, preimage_id']
      exact hμs
    · exact hX.prodMk aemeasurable_id
    · exact measurable_snd hs
  · rw [Measure.map_of_not_aemeasurable]
    · simp
    · contrapose hX; exact measurable_fst.comp_aemeasurable hX
/-
**ProbabilityTheory._root_.MeasureTheory.Integrable.comp_snd_map_prodMk** 是 Math
lib 中的一个定理，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.Integrable.comp_snd_map_prodMk
    {Ω} {mΩ : MeasurableSpace Ω} (X : Ω → β) {μ : Measure Ω} {f : Ω → F} (hf_int : Integrable f μ) :
    Integrable (fun x : β × Ω => f x.2) (μ.map fun ω => (X ω, ω)) := by
  by_cases hX : AEMeasurable X μ
  · have hf := hf_int.1.comp_snd_map_prodMk X (mΩ := mΩ) (mβ := mβ)
    refine ⟨hf, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lintegral_map' hf.enorm (hX.prodMk aemeasurable_id)]
    exact hf_int.2
  · rw [Measure.map_of_not_aemeasurable]
    · simp
    · contrapose hX; exact measurable_fst.comp_aemeasurable hX
/-
**ProbabilityTheory.aestronglyMeasurable_comp_snd_map_prodMk_iff** 是 Mathlib 中的一
个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：aestronglyMeasurable_comp_snd_map_prodMk_iff {Ω F} {_ : MeasurableSpace Ω}
 [TopologicalSpace F] {X : Ω -> β} {μ : Measure Ω} (hX : Measurable X) {f : Ω ->
 F} : AEStronglyMeasurable (fun x : β × Ω => f x.2) (μ.map fun ω => (X ω, ω)) ↔ 
AEStronglyMeasurable f μ
参数：hX : Measurable X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.comp_measurable`：comp_measurable {γ :
 Type*} {_ : MeasurableSpace γ} {_ : MeasurableSpace α} {f : γ -> α} {μ : Measur
e γ} (hg : AEStronglyMeasurable g (Measu…
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
· 使用定理 `MeasureTheory.AEStronglyMeasurable.comp_snd_map_prodMk`：∀ {β : Type u_2}
 {mβ : MeasurableSpace β} {Ω : Type u_5} {F : Type u_6} {mΩ : MeasurableSpace Ω}
 (X : Ω → β)   {μ : MeasureTheory.Measure Ω}…
-/
theorem aestronglyMeasurable_comp_snd_map_prodMk_iff {Ω F} {_ : MeasurableSpace Ω}
    [TopologicalSpace F] {X : Ω → β} {μ : Measure Ω} (hX : Measurable X) {f : Ω → F} :
    AEStronglyMeasurable (fun x : β × Ω => f x.2) (μ.map fun ω => (X ω, ω)) ↔
      AEStronglyMeasurable f μ :=
  ⟨fun h => h.comp_measurable (hX.prodMk measurable_id), fun h => h.comp_snd_map_prodMk X⟩
/-
**ProbabilityTheory.integrable_comp_snd_map_prodMk_iff** 是 Mathlib 中的一个定理，位于命名空间
 `ProbabilityTheory`。
形式化陈述：integrable_comp_snd_map_prodMk_iff {Ω} {_ : MeasurableSpace Ω} {X : Ω -> β
} {μ : Measure Ω} (hX : Measurable X) {f : Ω -> F} : Integrable (fun x : β × Ω =
> f x.2) (μ.map fun ω => (X ω, ω)) ↔ Integrable f μ
参数：hX : Measurable X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.comp_measurable`：∀ {α : Type u_1} {ε : Type u_5
} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace
 ε]   [inst_1 : ContinuousENor…
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
· 使用定理 `MeasureTheory.Integrable.comp_snd_map_prodMk`：∀ {β : Type u_2} {F : Type
 u_4} [inst : NormedAddCommGroup F] {mβ : MeasurableSpace β} {Ω : Type u_5}   {m
Ω : MeasurableSpace Ω} (X : Ω → β)…
-/
theorem integrable_comp_snd_map_prodMk_iff {Ω} {_ : MeasurableSpace Ω} {X : Ω → β} {μ : Measure Ω}
    (hX : Measurable X) {f : Ω → F} :
    Integrable (fun x : β × Ω => f x.2) (μ.map fun ω => (X ω, ω)) ↔ Integrable f μ :=
  ⟨fun h => h.comp_measurable (hX.prodMk measurable_id), fun h => h.comp_snd_map_prodMk X⟩
/-
**ProbabilityTheory.condExp_ae_eq_integral_condDistrib_id** 是 Mathlib 中的一个定理，位于命
名空间 `ProbabilityTheory`。
形式化陈述：condExp_ae_eq_integral_condDistrib_id [NormedSpace Real F] [CompleteSpace 
F] {X : Ω -> β} {μ : Measure Ω} [IsFiniteMeasure μ] (hX : Measurable X) {f : Ω -
> F} (hf_int : Integrable f μ) : μ[f | mβ.comap X] =ᵐ[μ] fun a => ∫ y, f y ∂cond
Distrib id X μ (X a)
参数：hX : Measurable X；hf_int : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.condExp_prod_ae_eq_integral_condDistrib'`：condExp_prod
_ae_eq_integral_condDistrib' [NormedSpace Real F] [CompleteSpace F] (hX : Measur
able X) (hY : AEMeasurable Y μ) (hf_int : Integr…
· 使用定理 `aemeasurable_id`：aemeasurable_id : AEMeasurable id μ
· 使用定理 `MeasureTheory.Integrable.comp_snd_map_prodMk`：∀ {β : Type u_2} {F : Type
 u_4} [inst : NormedAddCommGroup F] {mβ : MeasurableSpace β} {Ω : Type u_5}   {m
Ω : MeasurableSpace Ω} (X : Ω → β)…
-/
theorem condExp_ae_eq_integral_condDistrib_id [NormedSpace ℝ F] [CompleteSpace F] {X : Ω → β}
    {μ : Measure Ω} [IsFiniteMeasure μ] (hX : Measurable X) {f : Ω → F} (hf_int : Integrable f μ) :
    μ[f | mβ.comap X] =ᵐ[μ] fun a => ∫ y, f y ∂condDistrib id X μ (X a) :=
  condExp_prod_ae_eq_integral_condDistrib' hX aemeasurable_id (hf_int.comp_snd_map_prodMk X)

end ProbabilityTheory

