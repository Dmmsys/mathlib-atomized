/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.Hahn
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
public import Mathlib.MeasureTheory.Measure.Sub

/-!
# Lebesgue decomposition

This file proves the Lebesgue decomposition theorem. The Lebesgue decomposition theorem states that,
given two σ-finite measures `μ` and `ν`, there exists a σ-finite measure `ξ` and a measurable
function `f` such that `μ = ξ + fν` and `ξ` is mutually singular with respect to `ν`.

The Lebesgue decomposition provides the Radon-Nikodym theorem readily.

## Main definitions

* `MeasureTheory.Measure.HaveLebesgueDecomposition` : A pair of measures `μ` and `ν` is said
  to `HaveLebesgueDecomposition` if there exist a measure `ξ` and a measurable function `f`,
  such that `ξ` is mutually singular with respect to `ν` and `μ = ξ + ν.withDensity f`
* `MeasureTheory.Measure.singularPart` : If a pair of measures `HaveLebesgueDecomposition`,
  then `singularPart` chooses the measure from `HaveLebesgueDecomposition`, otherwise it
  returns the zero measure.
* `MeasureTheory.Measure.rnDeriv`: If a pair of measures
  `HaveLebesgueDecomposition`, then `rnDeriv` chooses the measurable function from
  `HaveLebesgueDecomposition`, otherwise it returns the zero function.

## Main results

* `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite` :
  the Lebesgue decomposition theorem.
* `MeasureTheory.Measure.eq_singularPart` : Given measures `μ` and `ν`, if `s` is a measure
  mutually singular to `ν` and `f` is a measurable function such that `μ = s + fν`, then
  `s = μ.singularPart ν`.
* `MeasureTheory.Measure.eq_rnDeriv` : Given measures `μ` and `ν`, if `s` is a
  measure mutually singular to `ν` and `f` is a measurable function such that `μ = s + fν`,
  then `f = μ.rnDeriv ν`.

## Tags

Lebesgue decomposition theorem
-/

@[expose] public section

assert_not_exists MeasureTheory.VectorMeasure

open scoped MeasureTheory NNReal ENNReal
open Set

namespace MeasureTheory

namespace Measure

variable {α : Type*} {m : MeasurableSpace α} {μ ν : Measure α}

/-- A pair of measures `μ` and `ν` is said to `HaveLebesgueDecomposition` if there exists a
measure `ξ` and a measurable function `f`, such that `ξ` is mutually singular with respect to
`ν` and `μ = ξ + ν.withDensity f`. -/
/-
**MeasureTheory.Measure.HaveLebesgueDecomposition** 是 Mathlib 中的一个类，位于命名空间 `Meas
ureTheory.Measure`。
形式化陈述：HaveLebesgueDecomposition (μ ν : Measure α) : Prop where lebesgue_decompos
ition : exists p : Measure α × (α -> Real>=0∞), Measurable p.2 ∧ p.1 ⟂ₘ ν ∧ μ = 
p.1 + ν.withDensity p.2  open scoped Classical in /-- If a pair of measures `Hav
eLebesgueDecomposition`, then `singularPart` chooses the measure from `HaveLebes
gueDecomposition`, otherwise it returns the zero measure. For sigma-finite measu
res, `μ = μ.singularPart ν + ν.withDensity (μ.rnDeriv ν)`. -/ noncomputable irre
ducible_def singularPart (
参数：μ ν : Measure α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pair of measures `μ` and `ν` is said to `HaveLebesgueDecomposition` if there e
xists a
measure `ξ` and a measurable function `f`, such that `ξ` is mutually singular wi
th respect to
`ν` and `μ = ξ + ν.withDensity f`.
-/
class HaveLebesgueDecomposition (μ ν : Measure α) : Prop where
  lebesgue_decomposition :
    ∃ p : Measure α × (α → ℝ≥0∞), Measurable p.2 ∧ p.1 ⟂ₘ ν ∧ μ = p.1 + ν.withDensity p.2

open scoped Classical in
/-- If a pair of measures `HaveLebesgueDecomposition`, then `singularPart` chooses the
measure from `HaveLebesgueDecomposition`, otherwise it returns the zero measure. For sigma-finite
measures, `μ = μ.singularPart ν + ν.withDensity (μ.rnDeriv ν)`. -/
noncomputable irreducible_def singularPart (μ ν : Measure α) : Measure α :=
  if h : HaveLebesgueDecomposition μ ν then (Classical.choose h.lebesgue_decomposition).1 else 0

open scoped Classical in
/-- If a pair of measures `HaveLebesgueDecomposition`, then `rnDeriv` chooses the
measurable function from `HaveLebesgueDecomposition`, otherwise it returns the zero function.
For sigma-finite measures, `μ = μ.singularPart ν + ν.withDensity (μ.rnDeriv ν)`. -/
noncomputable irreducible_def rnDeriv (μ ν : Measure α) : α → ℝ≥0∞ :=
  if h : HaveLebesgueDecomposition μ ν then (Classical.choose h.lebesgue_decomposition).2 else 0

section ByDefinition

/-
**MeasureTheory.Measure.haveLebesgueDecomposition_spec** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.Measure`。
形式化陈述：haveLebesgueDecomposition_spec (μ ν : Measure α) [h : HaveLebesgueDecompos
ition μ ν] : Measurable (μ.rnDeriv ν) ∧ μ.singularPart ν ⟂ₘ ν ∧ μ = μ.singularPa
rt ν + ν.withDensity (μ.rnDeriv ν)
参数：μ ν : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.HaveLebesgueDecomposition.lebesgue_decomposition`：
∀ {α : Type u_1} {m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [self :
 μ.HaveLebesgueDecomposition ν],   ∃ p, Measurable p.2 ∧ p.1…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.singularPart_def`：∀ {α : Type u_2} {m : Measurable
Space α} (μ ν : MeasureTheory.Measure α),   μ.singularPart ν = if h : μ.HaveLebe
sgueDecomposition ν then (Cl…
· 使用定理 `MeasureTheory.Measure.rnDeriv_def`：∀ {α : Type u_2} {m : MeasurableSpace
 α} (μ ν : MeasureTheory.Measure α),   μ.rnDeriv ν = if h : μ.HaveLebesgueDecomp
osition ν then (Classic…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem haveLebesgueDecomposition_spec (μ ν : Measure α) [h : HaveLebesgueDecomposition μ ν] :
    Measurable (μ.rnDeriv ν) ∧
      μ.singularPart ν ⟂ₘ ν ∧ μ = μ.singularPart ν + ν.withDensity (μ.rnDeriv ν) := by
  rw [singularPart, rnDeriv, dif_pos h, dif_pos h]
  exact Classical.choose_spec h.lebesgue_decomposition
/-
**MeasureTheory.Measure.rnDeriv_of_not_haveLebesgueDecomposition** 是 Mathlib 中的一
个引理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：rnDeriv_of_not_haveLebesgueDecomposition (h : ¬ HaveLebesgueDecomposition 
μ ν) : μ.rnDeriv ν = 0
参数：h : ¬ HaveLebesgueDecomposition μ ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.HaveLebesgueDecomposition.lebesgue_decomposition`：
∀ {α : Type u_1} {m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [self :
 μ.HaveLebesgueDecomposition ν],   ∃ p, Measurable p.2 ∧ p.1…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.rnDeriv_def`：∀ {α : Type u_2} {m : MeasurableSpace
 α} (μ ν : MeasureTheory.Measure α),   μ.rnDeriv ν = if h : μ.HaveLebesgueDecomp
osition ν then (Classic…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
lemma rnDeriv_of_not_haveLebesgueDecomposition (h : ¬ HaveLebesgueDecomposition μ ν) :
    μ.rnDeriv ν = 0 := by
  rw [rnDeriv, dif_neg h]
/-
**MeasureTheory.Measure.singularPart_of_not_haveLebesgueDecomposition** 是 Mathli
b 中的一个引理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：singularPart_of_not_haveLebesgueDecomposition (h : ¬ HaveLebesgueDecomposi
tion μ ν) : μ.singularPart ν = 0
参数：h : ¬ HaveLebesgueDecomposition μ ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.HaveLebesgueDecomposition.lebesgue_decomposition`：
∀ {α : Type u_1} {m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [self :
 μ.HaveLebesgueDecomposition ν],   ∃ p, Measurable p.2 ∧ p.1…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.singularPart_def`：∀ {α : Type u_2} {m : Measurable
Space α} (μ ν : MeasureTheory.Measure α),   μ.singularPart ν = if h : μ.HaveLebe
sgueDecomposition ν then (Cl…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
lemma singularPart_of_not_haveLebesgueDecomposition (h : ¬ HaveLebesgueDecomposition μ ν) :
    μ.singularPart ν = 0 := by
  rw [singularPart, dif_neg h]

@[fun_prop]
/-
**MeasureTheory.Measure.measurable_rnDeriv** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Measure`。
形式化陈述：measurable_rnDeriv (μ ν : Measure α) : Measurable μ.rnDeriv ν
参数：μ ν : Measure α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_spec`：haveLebesgueDecomp
osition_spec (μ ν : Measure α) [h : HaveLebesgueDecomposition μ ν] : Measurable 
(μ.rnDeriv ν) ∧ μ.singularPart ν ⟂ₘ ν ∧ μ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.rnDeriv_of_not_haveLebesgueDecomposition`：rnDeriv_
of_not_haveLebesgueDecomposition (h : ¬ HaveLebesgueDecomposition μ ν) : μ.rnDer
iv ν = 0
· 使用定理 `measurable_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace
 α] [inst_1 : MeasurableSpace β] [inst_2 : Zero α], Measurable 0
-/
theorem measurable_rnDeriv (μ ν : Measure α) : Measurable <| μ.rnDeriv ν := by
  by_cases h : HaveLebesgueDecomposition μ ν
  · exact (haveLebesgueDecomposition_spec μ ν).1
  · rw [rnDeriv_of_not_haveLebesgueDecomposition h]
    exact measurable_zero
/-
**MeasureTheory.Measure.mutuallySingular_singularPart** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.Measure`。
形式化陈述：mutuallySingular_singularPart (μ ν : Measure α) : μ.singularPart ν ⟂ₘ ν
参数：μ ν : Measure α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_spec`：haveLebesgueDecomp
osition_spec (μ ν : Measure α) [h : HaveLebesgueDecomposition μ ν] : Measurable 
(μ.rnDeriv ν) ∧ μ.singularPart ν ⟂ₘ ν ∧ μ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.singularPart_of_not_haveLebesgueDecomposition`：sin
gularPart_of_not_haveLebesgueDecomposition (h : ¬ HaveLebesgueDecomposition μ ν)
 : μ.singularPart ν = 0
· 使用定理 `MeasureTheory.Measure.MutuallySingular.zero_left`：zero_left : 0 ⟂ₘ μ
-/
theorem mutuallySingular_singularPart (μ ν : Measure α) : μ.singularPart ν ⟂ₘ ν := by
  by_cases h : HaveLebesgueDecomposition μ ν
  · exact (haveLebesgueDecomposition_spec μ ν).2.1
  · rw [singularPart_of_not_haveLebesgueDecomposition h]
    exact MutuallySingular.zero_left
/-
**MeasureTheory.Measure.MutuallySingular.haveLebesgueDecomposition** 是 Mathlib 中
的一个定理，位于命名空间 `MeasureTheory.Measure.MutuallySingular`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α}, 
  μ.MutuallySingular ν → μ.HaveLebesgueDecomposition ν
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace
 α] [inst_1 : MeasurableSpace β] [inst_2 : Zero α], Measurable 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.withDensity_zero`：withDensity_zero : μ.withDensity 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem MutuallySingular.haveLebesgueDecomposition (h : μ ⟂ₘ ν) : HaveLebesgueDecomposition μ ν :=
  ⟨⟨(μ, 0), measurable_zero, h, by simp⟩⟩
/-
**MeasureTheory.Measure.haveLebesgueDecomposition_add** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.Measure`。
形式化陈述：haveLebesgueDecomposition_add (μ ν : Measure α) [HaveLebesgueDecomposition
 μ ν] : μ = μ.singularPart ν + ν.withDensity (μ.rnDeriv ν)
参数：μ ν : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_spec`：haveLebesgueDecomp
osition_spec (μ ν : Measure α) [h : HaveLebesgueDecomposition μ ν] : Measurable 
(μ.rnDeriv ν) ∧ μ.singularPart ν ⟂ₘ ν ∧ μ …
-/
theorem haveLebesgueDecomposition_add (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] :
    μ = μ.singularPart ν + ν.withDensity (μ.rnDeriv ν) :=
  (haveLebesgueDecomposition_spec μ ν).2.2

/-- For the versions of this lemma where `ν.withDensity (μ.rnDeriv ν)` or `μ.singularPart ν` are
isolated, see `MeasureTheory.Measure.measure_sub_singularPart` and
`MeasureTheory.Measure.measure_sub_rnDeriv`. -/
/-
**MeasureTheory.Measure.singularPart_add_rnDeriv** 是 Mathlib 中的一个引理，位于命名空间 `Meas
ureTheory.Measure`。
形式化陈述：singularPart_add_rnDeriv (μ ν : Measure α) [HaveLebesgueDecomposition μ ν]
 : μ.singularPart ν + ν.withDensity (μ.rnDeriv ν) = μ
参数：μ ν : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_add`：haveLebesgueDecompo
sition_add (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] : μ = μ.singularPar
t ν + ν.withDensity (μ.rnDeriv ν)

--- 原说明 ---
For the versions of this lemma where `ν.withDensity (μ.rnDeriv ν)` or `μ.singula
rPart ν` are
isolated, see `MeasureTheory.Measure.measure_sub_singularPart` and
`MeasureTheory.Measure.measure_sub_rnDeriv`.
-/
lemma singularPart_add_rnDeriv (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] :
    μ.singularPart ν + ν.withDensity (μ.rnDeriv ν) = μ := (haveLebesgueDecomposition_add μ ν).symm

/-- For the versions of this lemma where `μ.singularPart ν` or `ν.withDensity (μ.rnDeriv ν)` are
isolated, see `MeasureTheory.Measure.measure_sub_singularPart` and
`MeasureTheory.Measure.measure_sub_rnDeriv`. -/
/-
**MeasureTheory.Measure.rnDeriv_add_singularPart** 是 Mathlib 中的一个引理，位于命名空间 `Meas
ureTheory.Measure`。
形式化陈述：rnDeriv_add_singularPart (μ ν : Measure α) [HaveLebesgueDecomposition μ ν]
 : ν.withDensity (μ.rnDeriv ν) + μ.singularPart ν = μ
参数：μ ν : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `MeasureTheory.Measure.singularPart_add_rnDeriv`：singularPart_add_rnDeriv
 (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] : μ.singularPart ν + ν.withDe
nsity (μ.rnDeriv ν) = μ

--- 原说明 ---
For the versions of this lemma where `μ.singularPart ν` or `ν.withDensity (μ.rnD
eriv ν)` are
isolated, see `MeasureTheory.Measure.measure_sub_singularPart` and
`MeasureTheory.Measure.measure_sub_rnDeriv`.
-/
lemma rnDeriv_add_singularPart (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] :
    ν.withDensity (μ.rnDeriv ν) + μ.singularPart ν = μ := by rw [add_comm, singularPart_add_rnDeriv]

end ByDefinition

section HaveLebesgueDecomposition

/-
**MeasureTheory.Measure.instHaveLebesgueDecompositionZeroLeft** 是 Mathlib 中的一个实例
，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：instHaveLebesgueDecompositionZeroLeft : HaveLebesgueDecomposition 0 ν
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.MutuallySingular.haveLebesgueDecomposition`：∀ {α :
 Type u_1} {m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α},   μ.Mutually
Singular ν → μ.HaveLebesgueDecomposition ν
· 使用定理 `MeasureTheory.Measure.MutuallySingular.zero_left`：zero_left : 0 ⟂ₘ μ
-/
instance instHaveLebesgueDecompositionZeroLeft : HaveLebesgueDecomposition 0 ν :=
  MutuallySingular.zero_left.haveLebesgueDecomposition
/-
**MeasureTheory.Measure.instHaveLebesgueDecompositionZeroRight** 是 Mathlib 中的一个实
例，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：instHaveLebesgueDecompositionZeroRight : HaveLebesgueDecomposition μ 0
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.MutuallySingular.haveLebesgueDecomposition`：∀ {α :
 Type u_1} {m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α},   μ.Mutually
Singular ν → μ.HaveLebesgueDecomposition ν
· 使用定理 `MeasureTheory.Measure.MutuallySingular.zero_right`：zero_right : μ ⟂ₘ 0
-/
instance instHaveLebesgueDecompositionZeroRight : HaveLebesgueDecomposition μ 0 :=
  MutuallySingular.zero_right.haveLebesgueDecomposition
/-
**MeasureTheory.Measure.instHaveLebesgueDecompositionSelf** 是 Mathlib 中的一个实例，位于命
名空间 `MeasureTheory.Measure`。
形式化陈述：instHaveLebesgueDecompositionSelf : HaveLebesgueDecomposition μ μ where le
besgue_decomposition
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `MeasureTheory.Measure.MutuallySingular.zero_left`：zero_left : 0 ⟂ₘ μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.withDensity_one`：withDensity_one : μ.withDensity 1 = μ
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance instHaveLebesgueDecompositionSelf : HaveLebesgueDecomposition μ μ where
  lebesgue_decomposition := ⟨⟨0, 1⟩, measurable_const, MutuallySingular.zero_left, by simp⟩
/-
**MeasureTheory.Measure.HaveLebesgueDecomposition.sum_left** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.Measure.HaveLebesgueDecomposition`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {ν : MeasureTheory.Measure α} {ι 
: Type u_2} [Countable ι]   (μ : ι → MeasureTheory.Measure α) [∀ (i : ι), (μ i).
HaveLebesgueDecomposition ν],   (MeasureTheory.Measure.sum μ).HaveLebesgueDecomp
osition ν
参数：μ : ι → MeasureTheory.Measure α；i : ι；μ i；MeasureTheory.Measure.sum μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.tsum'`：∀ {X : Type u_6} {E : Type u_7} {ι : Type u_8} [inst :
 MeasurableSpace X] [inst_1 : AddCommMonoid E]   [inst_2 : TopologicalSpace E] [
Topolo…
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `ENNReal.instMetrizableSpace`：TopologicalSpace.MetrizableSpace ENNReal
· 使用定理 `ContinuousAdd.measurableMul₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Add γ] [Con…
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `ENNReal.instContinuousAdd`：ContinuousAdd ENNReal
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `SummationFilter.instIsCountablyGeneratedFinsetFilterUnconditionalOfCount
able`：∀ (β : Type u_2) [Countable β], (SummationFilter.unconditional β).filter.I
sCountablyGenerated
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.withDensity_tsum`：withDensity_tsum {ι : Type*} [Countable 
ι] {f : ι -> α -> Real>=0∞} (h : forall i, Measurable (f i)) : μ.withDensity (∑'
 n, f n) = sum fun n…
· 使用定理 `MeasureTheory.Measure.sum_add_sum`：sum_add_sum {ι : Type*} (μ ν : ι -> M
easure α) : sum μ + sum ν = sum fun n => μ n + ν n
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `MeasureTheory.Measure.singularPart_add_rnDeriv`：singularPart_add_rnDeriv
 (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] : μ.singularPart ν + ν.withDe
nsity (μ.rnDeriv ν) = μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance HaveLebesgueDecomposition.sum_left {ι : Type*} [Countable ι] (μ : ι → Measure α)
    [∀ i, HaveLebesgueDecomposition (μ i) ν] : HaveLebesgueDecomposition (.sum μ) ν :=
  ⟨(.sum fun i ↦ (μ i).singularPart ν, ∑' i, rnDeriv (μ i) ν),
    by dsimp only; fun_prop, by simp [mutuallySingular_singularPart], by
      simp [withDensity_tsum, measurable_rnDeriv, Measure.sum_add_sum, singularPart_add_rnDeriv]⟩
/-
**MeasureTheory.Measure.HaveLebesgueDecomposition.add_left** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.Measure.HaveLebesgueDecomposition`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ ν μ' : MeasureTheory.Measure α
} [μ.HaveLebesgueDecomposition ν]   [μ'.HaveLebesgueDecomposition ν], (μ + μ').H
aveLebesgueDecomposition ν
参数：μ + μ'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.sum_fintype`：sum_fintype [Fintype ι] (μ : ι -> Mea
sure α) : sum μ = ∑ i, μ i
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Bool.true_eq_false`：(true = false) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `MeasureTheory.Measure.HaveLebesgueDecomposition.sum_left`：∀ {α : Type u_
1} {m : MeasurableSpace α} {ν : MeasureTheory.Measure α} {ι : Type u_2} [Countab
le ι]   (μ : ι → MeasureTheory.Measure α) [∀ (…
-/
instance HaveLebesgueDecomposition.add_left {μ' : Measure α} [HaveLebesgueDecomposition μ ν]
    [HaveLebesgueDecomposition μ' ν] : HaveLebesgueDecomposition (μ + μ') ν := by
  have : ∀ b, HaveLebesgueDecomposition (cond b μ μ') ν := by simp [*]
  simpa using sum_left (cond · μ μ')
/-
**MeasureTheory.Measure.haveLebesgueDecompositionSMul'** 是 Mathlib 中的一个实例，位于命名空间
 `MeasureTheory.Measure`。
形式化陈述：haveLebesgueDecompositionSMul' (μ ν : Measure α) [HaveLebesgueDecompositio
n μ ν] (r : Real>=0∞) : (r • μ).HaveLebesgueDecomposition ν where lebesgue_decom
position
参数：μ ν : Measure α；r : Real>=0∞。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_spec`：haveLebesgueDecomp
osition_spec (μ ν : Measure α) [h : HaveLebesgueDecomposition μ ν] : Measurable 
(μ.rnDeriv ν) ∧ μ.singularPart ν ⟂ₘ ν ∧ μ …
· 使用引理 `Measurable.const_smul`：Measurable.const_smul (hg : Measurable g) (c : M)
 : Measurable (c • g)
· 使用定理 `MeasurableSMul.toMeasurableConstSMul`：∀ {M : Type u_2} {α : Type u_3} {i
nst : SMul M α} {inst_1 : MeasurableSpace M} {inst_2 : MeasurableSpace α}   [sel
f : MeasurableSMul M α], M…
· 使用定理 `measurableSMul_of_mul`：∀ (M : Type u_2) [inst : Mul M] [inst_1 : Measura
bleSpace M] [MeasurableMul M], MeasurableSMul M M
· 使用定理 `MeasurableMul₂.toMeasurableMul`：∀ {M : Type u_2} [inst : MeasurableSpace
 M] [inst_1 : Mul M] [MeasurableMul₂ M], MeasurableMul M
· 使用定理 `MeasureTheory.Measure.MutuallySingular.smul`：smul (r : Real>=0∞) (h : ν 
⟂ₘ μ) : r • ν ⟂ₘ μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.withDensity_smul`：withDensity_smul (r : Real>=0∞) {f : α -
> Real>=0∞} (hf : Measurable f) : μ.withDensity (r • f) = r • μ.withDensity f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
-/
instance haveLebesgueDecompositionSMul' (μ ν : Measure α) [HaveLebesgueDecomposition μ ν]
    (r : ℝ≥0∞) : (r • μ).HaveLebesgueDecomposition ν where
  lebesgue_decomposition := by
    obtain ⟨hmeas, hsing, hadd⟩ := haveLebesgueDecomposition_spec μ ν
    refine ⟨⟨r • μ.singularPart ν, r • μ.rnDeriv ν⟩, hmeas.const_smul _, hsing.smul _, ?_⟩
    simp only
    rw [withDensity_smul _ hmeas, ← smul_add, ← hadd]
/-
**MeasureTheory.Measure.haveLebesgueDecompositionSMul** 是 Mathlib 中的一个实例，位于命名空间 
`MeasureTheory.Measure`。
形式化陈述：haveLebesgueDecompositionSMul (μ ν : Measure α) [HaveLebesgueDecomposition
 μ ν] (r : Real>=0) : (r • μ).HaveLebesgueDecomposition ν
参数：μ ν : Measure α；r : Real>=0。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.smul_def`：smul_def {M : Type*} [MulAction Real>=0∞ M] (c : Real>
=0) (x : M) : c • x = (c : Real>=0∞) • x
-/
instance haveLebesgueDecompositionSMul (μ ν : Measure α) [HaveLebesgueDecomposition μ ν]
    (r : ℝ≥0) : (r • μ).HaveLebesgueDecomposition ν := by
  rw [ENNReal.smul_def]; infer_instance
/-
**MeasureTheory.Measure.haveLebesgueDecompositionSMulRight** 是 Mathlib 中的一个实例，位于
命名空间 `MeasureTheory.Measure`。
形式化陈述：haveLebesgueDecompositionSMulRight (μ ν : Measure α) [HaveLebesgueDecompos
ition μ ν] (r : Real>=0) : μ.HaveLebesgueDecomposition (r • ν) where lebesgue_de
composition
参数：μ ν : Measure α；r : Real>=0。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_spec`：haveLebesgueDecomp
osition_spec (μ ν : Measure α) [h : HaveLebesgueDecomposition μ ν] : Measurable 
(μ.rnDeriv ν) ∧ μ.singularPart ν ⟂ₘ ν ∧ μ …
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `MeasureTheory.withDensity_zero`：withDensity_zero : μ.withDensity 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Measurable.const_smul`：Measurable.const_smul (hg : Measurable g) (c : M)
 : Measurable (c • g)
· 使用定理 `MeasurableSMul.toMeasurableConstSMul`：∀ {M : Type u_2} {α : Type u_3} {i
nst : SMul M α} {inst_1 : MeasurableSpace M} {inst_2 : MeasurableSpace α}   [sel
f : MeasurableSMul M α], M…
· 使用定理 `ENNReal.instMeasurableSMulNNReal`：MeasurableSMul NNReal ENNReal
· 使用定理 `MeasureTheory.Measure.MutuallySingular.mono_ac`：mono_ac (h : μ₁ ⟂ₘ ν₁) (
hμ : μ₂ ≪ μ₁) (hν : ν₂ ≪ ν₁) : μ₂ ⟂ₘ ν₂
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.rfl`：∀ {α : Type u_1} {mα : M
easurableSpace α} {μ : MeasureTheory.Measure α}, μ.AbsolutelyContinuous μ
· 使用引理 `MeasureTheory.Measure.smul_absolutelyContinuous`：smul_absolutelyContinuo
us {c : Real>=0∞} : c • μ ≪ μ
· 使用定理 `MeasureTheory.withDensity_smul`：withDensity_smul (r : Real>=0∞) {f : α -
> Real>=0∞} (hf : Measurable f) : μ.withDensity (r • f) = r • μ.withDensity f
· 使用定理 `ENNReal.smul_def`：smul_def {M : Type*} [MulAction Real>=0∞ M] (c : Real>
=0) (x : M) : c • x = (c : Real>=0∞) • x
· 使用定理 `MeasureTheory.withDensity_smul_measure`：withDensity_smul_measure (r : Re
al>=0∞) (f : α -> Real>=0∞) : (r • μ).withDensity f = r • μ.withDensity f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `ENNReal.coe_inv`：coe_inv (hr : r != 0) : (↑r⁻¹ : Real>=0∞) = (↑r)⁻¹
· 使用定理 `ENNReal.inv_mul_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a⁻¹ * a = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
instance haveLebesgueDecompositionSMulRight (μ ν : Measure α) [HaveLebesgueDecomposition μ ν]
    (r : ℝ≥0) :
    μ.HaveLebesgueDecomposition (r • ν) where
  lebesgue_decomposition := by
    obtain ⟨hmeas, hsing, hadd⟩ := haveLebesgueDecomposition_spec μ ν
    by_cases hr : r = 0
    · exact ⟨⟨μ, 0⟩, measurable_const, by simp [hr], by simp⟩
    refine ⟨⟨μ.singularPart ν, r⁻¹ • μ.rnDeriv ν⟩, hmeas.const_smul _,
      hsing.mono_ac AbsolutelyContinuous.rfl smul_absolutelyContinuous, ?_⟩
    have : r⁻¹ • rnDeriv μ ν = ((r⁻¹ : ℝ≥0) : ℝ≥0∞) • rnDeriv μ ν := by simp [ENNReal.smul_def]
    rw [this, withDensity_smul _ hmeas, ENNReal.smul_def r, withDensity_smul_measure,
      ← smul_assoc, smul_eq_mul, ENNReal.coe_inv hr, ENNReal.inv_mul_cancel, one_smul]
    · exact hadd
    · simp [hr]
    · exact ENNReal.coe_ne_top
/-
**MeasureTheory.Measure.haveLebesgueDecomposition_withDensity** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：haveLebesgueDecomposition_withDensity (μ : Measure α) {f : α -> Real>=0∞} 
(hf : Measurable f) : (μ.withDensity f).HaveLebesgueDecomposition μ
参数：μ : Measure α；hf : Measurable f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.MutuallySingular.zero_left`：zero_left : 0 ⟂ₘ μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem haveLebesgueDecomposition_withDensity (μ : Measure α) {f : α → ℝ≥0∞} (hf : Measurable f) :
    (μ.withDensity f).HaveLebesgueDecomposition μ := ⟨⟨⟨0, f⟩, hf, .zero_left, (zero_add _).symm⟩⟩
/-
**MeasureTheory.Measure.haveLebesgueDecompositionRnDeriv** 是 Mathlib 中的一个实例，位于命名
空间 `MeasureTheory.Measure`。
形式化陈述：haveLebesgueDecompositionRnDeriv (μ ν : Measure α) : HaveLebesgueDecomposi
tion (ν.withDensity (μ.rnDeriv ν)) ν
参数：μ ν : Measure α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_withDensity`：haveLebesgu
eDecomposition_withDensity (μ : Measure α) {f : α -> Real>=0∞} (hf : Measurable 
f) : (μ.withDensity f).HaveLebesgueDecomposition …
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
-/
instance haveLebesgueDecompositionRnDeriv (μ ν : Measure α) :
    HaveLebesgueDecomposition (ν.withDensity (μ.rnDeriv ν)) ν :=
  haveLebesgueDecomposition_withDensity ν (measurable_rnDeriv _ _)
/-
**MeasureTheory.Measure.instHaveLebesgueDecompositionSingularPart** 是 Mathlib 中的
一个实例，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：instHaveLebesgueDecompositionSingularPart : HaveLebesgueDecomposition (μ.s
ingularPart ν) ν
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace
 α] [inst_1 : MeasurableSpace β] [inst_2 : Zero α], Measurable 0
· 使用定理 `MeasureTheory.Measure.mutuallySingular_singularPart`：mutuallySingular_si
ngularPart (μ ν : Measure α) : μ.singularPart ν ⟂ₘ ν
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.withDensity_zero`：withDensity_zero : μ.withDensity 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance instHaveLebesgueDecompositionSingularPart :
    HaveLebesgueDecomposition (μ.singularPart ν) ν :=
  ⟨⟨μ.singularPart ν, 0⟩, measurable_zero, mutuallySingular_singularPart μ ν, by simp⟩

end HaveLebesgueDecomposition

/-
**MeasureTheory.Measure.singularPart_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Measure`。
形式化陈述：singularPart_le (μ ν : Measure α) : μ.singularPart ν <= μ
参数：μ ν : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_add`：haveLebesgueDecompo
sition_add (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] : μ = μ.singularPar
t ν + ν.withDensity (μ.rnDeriv ν)
· 使用定理 `MeasureTheory.Measure.le_add_right`：∀ {α : Type u_1} {m0 : MeasurableSpa
ce α} {μ ν ν' : MeasureTheory.Measure α}, μ ≤ ν → μ ≤ ν + ν'
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `MeasureTheory.Measure.HaveLebesgueDecomposition.lebesgue_decomposition`：
∀ {α : Type u_1} {m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [self :
 μ.HaveLebesgueDecomposition ν],   ∃ p, Measurable p.2 ∧ p.1…
· 使用定理 `MeasureTheory.Measure.singularPart_def`：∀ {α : Type u_2} {m : Measurable
Space α} (μ ν : MeasureTheory.Measure α),   μ.singularPart ν = if h : μ.HaveLebe
sgueDecomposition ν then (Cl…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `MeasureTheory.Measure.zero_le`：∀ {α : Type u_1} {_m0 : MeasurableSpace α
} (μ : MeasureTheory.Measure α), 0 ≤ μ
-/
theorem singularPart_le (μ ν : Measure α) : μ.singularPart ν ≤ μ := by
  by_cases hl : HaveLebesgueDecomposition μ ν
  · conv_rhs => rw [haveLebesgueDecomposition_add μ ν]
    exact Measure.le_add_right le_rfl
  · rw [singularPart, dif_neg hl]
    exact Measure.zero_le μ
/-
**MeasureTheory.Measure.withDensity_rnDeriv_le** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.Measure`。
形式化陈述：withDensity_rnDeriv_le (μ ν : Measure α) : ν.withDensity (μ.rnDeriv ν) <= 
μ
参数：μ ν : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_add`：haveLebesgueDecompo
sition_add (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] : μ = μ.singularPar
t ν + ν.withDensity (μ.rnDeriv ν)
· 使用定理 `MeasureTheory.Measure.le_add_left`：∀ {α : Type u_1} {m0 : MeasurableSpac
e α} {μ ν ν' : MeasureTheory.Measure α}, μ ≤ ν → μ ≤ ν' + ν
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `MeasureTheory.Measure.HaveLebesgueDecomposition.lebesgue_decomposition`：
∀ {α : Type u_1} {m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [self :
 μ.HaveLebesgueDecomposition ν],   ∃ p, Measurable p.2 ∧ p.1…
· 使用定理 `MeasureTheory.Measure.rnDeriv_def`：∀ {α : Type u_2} {m : MeasurableSpace
 α} (μ ν : MeasureTheory.Measure α),   μ.rnDeriv ν = if h : μ.HaveLebesgueDecomp
osition ν then (Classic…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `MeasureTheory.withDensity_zero`：withDensity_zero : μ.withDensity 0 = 0
· 使用定理 `MeasureTheory.Measure.zero_le`：∀ {α : Type u_1} {_m0 : MeasurableSpace α
} (μ : MeasureTheory.Measure α), 0 ≤ μ
-/
theorem withDensity_rnDeriv_le (μ ν : Measure α) : ν.withDensity (μ.rnDeriv ν) ≤ μ := by
  by_cases hl : HaveLebesgueDecomposition μ ν
  · conv_rhs => rw [haveLebesgueDecomposition_add μ ν]
    exact Measure.le_add_left le_rfl
  · rw [rnDeriv, dif_neg hl, withDensity_zero]
    exact Measure.zero_le μ
/-
**MeasureTheory.Measure._root_.AEMeasurable.singularPart** 是 Mathlib 中的一个引理，位于命名
空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.AEMeasurable.singularPart {β : Type*} {_ : MeasurableSpace β} {f : α → β}
    (hf : AEMeasurable f μ) (ν : Measure α) :
    AEMeasurable f (μ.singularPart ν) :=
  AEMeasurable.mono_measure hf (Measure.singularPart_le _ _)
/-
**MeasureTheory.Measure._root_.AEMeasurable.withDensity_rnDeriv** 是 Mathlib 中的一个
引理，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.AEMeasurable.withDensity_rnDeriv {β : Type*} {_ : MeasurableSpace β} {f : α → β}
    (hf : AEMeasurable f μ) (ν : Measure α) :
    AEMeasurable f (ν.withDensity (μ.rnDeriv ν)) :=
  AEMeasurable.mono_measure hf (Measure.withDensity_rnDeriv_le _ _)
/-
**MeasureTheory.Measure.MutuallySingular.singularPart** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.Measure.MutuallySingular`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α}, 
  μ.MutuallySingular ν → ∀ (ν' : MeasureTheory.Measure α), (μ.singularPart ν').M
utuallySingular ν
参数：ν' : MeasureTheory.Measure α；μ.singularPart ν'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.MutuallySingular.mono`：mono (h : μ₁ ⟂ₘ ν₁) (hμ : μ
₂ <= μ₁) (hν : ν₂ <= ν₁) : μ₂ ⟂ₘ ν₂
· 使用定理 `MeasureTheory.Measure.singularPart_le`：singularPart_le (μ ν : Measure α)
 : μ.singularPart ν <= μ
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
protected lemma MutuallySingular.singularPart (h : μ ⟂ₘ ν) (ν' : Measure α) :
    μ.singularPart ν' ⟂ₘ ν :=
  h.mono (singularPart_le μ ν') le_rfl
/-
**MeasureTheory.Measure.absolutelyContinuous_withDensity_rnDeriv** 是 Mathlib 中的一
个引理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：absolutelyContinuous_withDensity_rnDeriv [HaveLebesgueDecomposition ν μ] (
hμν : μ ≪ ν) : μ ≪ μ.withDensity (ν.rnDeriv μ)
参数：hμν : μ ≪ ν。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.mk`：mk (h : forall ⦃s : Set α
⦄, MeasurableSet s -> ν s = 0 -> μ s = 0) : μ ≪ ν
· 使用定理 `MeasureTheory.Measure.mutuallySingular_singularPart`：mutuallySingular_si
ngularPart (μ ν : Measure α) : μ.singularPart ν ⟂ₘ ν
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_union_compl`：inter_union_compl (s t : Set α) : s inter t union
 s inter tᶜ = s
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.measure_union_le`：measure_union_le (s t : Set α) : μ (s un
ion t) <= μ s + μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_add`：haveLebesgueDecompo
sition_add (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] : μ = μ.singularPar
t ν + ν.withDensity (μ.rnDeriv ν)
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
lemma absolutelyContinuous_withDensity_rnDeriv [HaveLebesgueDecomposition ν μ] (hμν : μ ≪ ν) :
    μ ≪ μ.withDensity (ν.rnDeriv μ) := by
  rw [haveLebesgueDecomposition_add ν μ] at hμν
  refine AbsolutelyContinuous.mk (fun s _ hνs ↦ ?_)
  obtain ⟨t, _, ht1, ht2⟩ := mutuallySingular_singularPart ν μ
  rw [← inter_union_compl s, ← nonpos_iff_eq_zero]
  refine (measure_union_le (s ∩ t) (s ∩ tᶜ)).trans ?_
  simp only [nonpos_iff_eq_zero, add_eq_zero]
  constructor
  · refine hμν ?_
    simp only [coe_add, Pi.add_apply, add_eq_zero]
    constructor
    · exact measure_mono_null Set.inter_subset_right ht1
    · exact measure_mono_null Set.inter_subset_left hνs
  · exact measure_mono_null Set.inter_subset_right ht2
/-
**MeasureTheory.Measure.AbsolutelyContinuous.withDensity_rnDeriv** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory.Measure.AbsolutelyContinuous`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ ν ξ : MeasureTheory.Measure α}
 [μ.HaveLebesgueDecomposition ν],   ξ.AbsolutelyContinuous μ → ξ.AbsolutelyConti
nuous ν → ξ.AbsolutelyContinuous (ν.withDensity (μ.rnDeriv ν))
参数：ν.withDensity (μ.rnDeriv ν)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.Measure.absolutelyContinuous_of_add_of_mutuallySingular`：a
bsolutelyContinuous_of_add_of_mutuallySingular {ν₁ ν₂ : Measure α} (h : μ ≪ ν₁ +
 ν₂) (h_ms : μ ⟂ₘ ν₂) : μ ≪ ν₁
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_add`：haveLebesgueDecompo
sition_add (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] : μ = μ.singularPar
t ν + ν.withDensity (μ.rnDeriv ν)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `MeasureTheory.Measure.MutuallySingular.mono_ac`：mono_ac (h : μ₁ ⟂ₘ ν₁) (
hμ : μ₂ ≪ μ₁) (hν : ν₂ ≪ ν₁) : μ₂ ⟂ₘ ν₂
· 使用定理 `MeasureTheory.Measure.MutuallySingular.symm`：symm (h : ν ⟂ₘ μ) : μ ⟂ₘ ν
· 使用定理 `MeasureTheory.Measure.mutuallySingular_singularPart`：mutuallySingular_si
ngularPart (μ ν : Measure α) : μ.singularPart ν ⟂ₘ ν
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.rfl`：∀ {α : Type u_1} {mα : M
easurableSpace α} {μ : MeasureTheory.Measure α}, μ.AbsolutelyContinuous μ
-/
lemma AbsolutelyContinuous.withDensity_rnDeriv {ξ : Measure α} [μ.HaveLebesgueDecomposition ν]
    (hξμ : ξ ≪ μ) (hξν : ξ ≪ ν) :
    ξ ≪ ν.withDensity (μ.rnDeriv ν) := by
  conv_rhs at hξμ => rw [μ.haveLebesgueDecomposition_add ν, add_comm]
  refine absolutelyContinuous_of_add_of_mutuallySingular hξμ ?_
  exact MutuallySingular.mono_ac (mutuallySingular_singularPart μ ν).symm hξν .rfl
/-
**MeasureTheory.Measure.absolutelyContinuous_withDensity_rnDeriv_swap** 是 Mathli
b 中的一个引理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：absolutelyContinuous_withDensity_rnDeriv_swap [ν.HaveLebesgueDecomposition
 μ] : ν.withDensity (μ.rnDeriv ν) ≪ μ.withDensity (ν.rnDeriv μ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.withDensity_rnDeriv`：∀ {α : T
ype u_1} {m : MeasurableSpace α} {μ ν ξ : MeasureTheory.Measure α} [μ.HaveLebesg
ueDecomposition ν],   ξ.AbsolutelyContinuous μ → ξ.A…
· 使用定理 `MeasureTheory.withDensity_absolutelyContinuous`：withDensity_absolutelyCo
ntinuous {m : MeasurableSpace α} (μ : Measure α) (f : α -> Real>=0∞) : μ.withDen
sity f ≪ μ
· 使用定理 `MeasureTheory.Measure.absolutelyContinuous_of_le`：absolutelyContinuous_o
f_le (h : μ <= ν) : μ ≪ ν
· 使用定理 `MeasureTheory.Measure.withDensity_rnDeriv_le`：withDensity_rnDeriv_le (μ 
ν : Measure α) : ν.withDensity (μ.rnDeriv ν) <= μ
-/
lemma absolutelyContinuous_withDensity_rnDeriv_swap [ν.HaveLebesgueDecomposition μ] :
    ν.withDensity (μ.rnDeriv ν) ≪ μ.withDensity (ν.rnDeriv μ) :=
  (withDensity_absolutelyContinuous ν (μ.rnDeriv ν)).withDensity_rnDeriv
    (absolutelyContinuous_of_le (withDensity_rnDeriv_le _ _))
/-
**MeasureTheory.Measure.singularPart_eq_zero_of_ac** 是 Mathlib 中的一个引理，位于命名空间 `Me
asureTheory.Measure`。
形式化陈述：singularPart_eq_zero_of_ac (h : μ ≪ ν) : μ.singularPart ν = 0
参数：h : μ ≪ ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.MutuallySingular.self_iff`：self_iff (μ : Measure α
) : μ ⟂ₘ μ ↔ μ = 0
· 使用定理 `MeasureTheory.Measure.MutuallySingular.mono_ac`：mono_ac (h : μ₁ ⟂ₘ ν₁) (
hμ : μ₂ ≪ μ₁) (hν : ν₂ ≪ ν₁) : μ₂ ⟂ₘ ν₂
· 使用定理 `MeasureTheory.Measure.mutuallySingular_singularPart`：mutuallySingular_si
ngularPart (μ ν : Measure α) : μ.singularPart ν ⟂ₘ ν
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.rfl`：∀ {α : Type u_1} {mα : M
easurableSpace α} {μ : MeasureTheory.Measure α}, μ.AbsolutelyContinuous μ
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.trans`：∀ {α : Type u_1} {mα :
 MeasurableSpace α} {μ₁ μ₂ μ₃ : MeasureTheory.Measure α},   μ₁.AbsolutelyContinu
ous μ₂ → μ₂.AbsolutelyContinuous μ₃ → …
· 使用定理 `MeasureTheory.Measure.absolutelyContinuous_of_le`：absolutelyContinuous_o
f_le (h : μ <= ν) : μ ≪ ν
· 使用定理 `MeasureTheory.Measure.singularPart_le`：singularPart_le (μ ν : Measure α)
 : μ.singularPart ν <= μ
-/
lemma singularPart_eq_zero_of_ac (h : μ ≪ ν) : μ.singularPart ν = 0 := by
  rw [← MutuallySingular.self_iff]
  exact MutuallySingular.mono_ac (mutuallySingular_singularPart _ _)
    AbsolutelyContinuous.rfl ((absolutelyContinuous_of_le (singularPart_le _ _)).trans h)

@[simp]
/-
**MeasureTheory.Measure.singularPart_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：singularPart_zero (ν : Measure α) : (0 : Measure α).singularPart ν = 0
参数：ν : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.Measure.singularPart_eq_zero_of_ac`：singularPart_eq_zero_o
f_ac (h : μ ≪ ν) : μ.singularPart ν = 0
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.zero`：∀ {α : Type u_1} {mα : 
MeasurableSpace α} (μ : MeasureTheory.Measure α), MeasureTheory.Measure.Absolute
lyContinuous 0 μ
-/
theorem singularPart_zero (ν : Measure α) : (0 : Measure α).singularPart ν = 0 :=
  singularPart_eq_zero_of_ac (AbsolutelyContinuous.zero _)

@[simp]
/-
**MeasureTheory.Measure.singularPart_zero_right** 是 Mathlib 中的一个引理，位于命名空间 `Measu
reTheory.Measure`。
形式化陈述：singularPart_zero_right (μ : Measure α) : μ.singularPart 0 = μ
参数：μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_add`：haveLebesgueDecompo
sition_add (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] : μ = μ.singularPar
t ν + ν.withDensity (μ.rnDeriv ν)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `MeasureTheory.withDensity_zero_left`：withDensity_zero_left (f : α -> Rea
l>=0∞) : (0 : Measure α).withDensity f = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma singularPart_zero_right (μ : Measure α) : μ.singularPart 0 = μ := by
  conv_rhs => rw [haveLebesgueDecomposition_add μ 0]
  simp
/-
**MeasureTheory.Measure.singularPart_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `MeasureT
heory.Measure`。
形式化陈述：singularPart_eq_zero (μ ν : Measure α) [μ.HaveLebesgueDecomposition ν] : μ
.singularPart ν = 0 ↔ μ ≪ ν
参数：μ ν : Measure α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_add`：haveLebesgueDecompo
sition_add (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] : μ = μ.singularPar
t ν + ν.withDensity (μ.rnDeriv ν)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `MeasureTheory.withDensity_absolutelyContinuous`：withDensity_absolutelyCo
ntinuous {m : MeasurableSpace α} (μ : Measure α) (f : α -> Real>=0∞) : μ.withDen
sity f ≪ μ
· 使用引理 `MeasureTheory.Measure.singularPart_eq_zero_of_ac`：singularPart_eq_zero_o
f_ac (h : μ ≪ ν) : μ.singularPart ν = 0
-/
lemma singularPart_eq_zero (μ ν : Measure α) [μ.HaveLebesgueDecomposition ν] :
    μ.singularPart ν = 0 ↔ μ ≪ ν := by
  have h_dec := haveLebesgueDecomposition_add μ ν
  refine ⟨fun h ↦ ?_, singularPart_eq_zero_of_ac⟩
  rw [h, zero_add] at h_dec
  rw [h_dec]
  exact withDensity_absolutelyContinuous ν _

@[simp]
/-
**MeasureTheory.Measure.withDensity_rnDeriv_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `M
easureTheory.Measure`。
形式化陈述：withDensity_rnDeriv_eq_zero (μ ν : Measure α) [μ.HaveLebesgueDecomposition
 ν] : ν.withDensity (μ.rnDeriv ν) = 0 ↔ μ ⟂ₘ ν
参数：μ ν : Measure α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_add`：haveLebesgueDecompo
sition_add (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] : μ = μ.singularPar
t ν + ν.withDensity (μ.rnDeriv ν)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `MeasureTheory.Measure.mutuallySingular_singularPart`：mutuallySingular_si
ngularPart (μ ν : Measure α) : μ.singularPart ν ⟂ₘ ν
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.MutuallySingular.self_iff`：self_iff (μ : Measure α
) : μ ⟂ₘ μ ↔ μ = 0
· 使用定理 `MeasureTheory.Measure.MutuallySingular.mono_ac`：mono_ac (h : μ₁ ⟂ₘ ν₁) (
hμ : μ₂ ≪ μ₁) (hν : ν₂ ≪ ν₁) : μ₂ ⟂ₘ ν₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.Measure.MutuallySingular.add_left_iff`：add_left_iff : μ₁ +
 μ₂ ⟂ₘ ν ↔ μ₁ ⟂ₘ ν ∧ μ₂ ⟂ₘ ν
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.rfl`：∀ {α : Type u_1} {mα : M
easurableSpace α} {μ : MeasureTheory.Measure α}, μ.AbsolutelyContinuous μ
· 使用定理 `MeasureTheory.withDensity_absolutelyContinuous`：withDensity_absolutelyCo
ntinuous {m : MeasurableSpace α} (μ : Measure α) (f : α -> Real>=0∞) : μ.withDen
sity f ≪ μ
-/
lemma withDensity_rnDeriv_eq_zero (μ ν : Measure α) [μ.HaveLebesgueDecomposition ν] :
    ν.withDensity (μ.rnDeriv ν) = 0 ↔ μ ⟂ₘ ν := by
  have h_dec := haveLebesgueDecomposition_add μ ν
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [h, add_zero] at h_dec
    rw [h_dec]
    exact mutuallySingular_singularPart μ ν
  · rw [← MutuallySingular.self_iff]
    rw [h_dec, MutuallySingular.add_left_iff] at h
    refine MutuallySingular.mono_ac h.2 AbsolutelyContinuous.rfl ?_
    exact withDensity_absolutelyContinuous _ _

@[simp]
/-
**MeasureTheory.Measure.rnDeriv_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory
.Measure`。
形式化陈述：rnDeriv_eq_zero (μ ν : Measure α) [μ.HaveLebesgueDecomposition ν] : μ.rnDe
riv ν =ᵐ[ν] 0 ↔ μ ⟂ₘ ν
参数：μ ν : Measure α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.withDensity_rnDeriv_eq_zero`：withDensity_rnDeriv_e
q_zero (μ ν : Measure α) [μ.HaveLebesgueDecomposition ν] : ν.withDensity (μ.rnDe
riv ν) = 0 ↔ μ ⟂ₘ ν
· 使用定理 `MeasureTheory.withDensity_eq_zero_iff`：withDensity_eq_zero_iff {f : α ->
 Real>=0∞} (hf : AEMeasurable f μ) : μ.withDensity f = 0 ↔ f =ᵐ[μ] 0
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma rnDeriv_eq_zero (μ ν : Measure α) [μ.HaveLebesgueDecomposition ν] :
    μ.rnDeriv ν =ᵐ[ν] 0 ↔ μ ⟂ₘ ν := by
  rw [← withDensity_rnDeriv_eq_zero, withDensity_eq_zero_iff (measurable_rnDeriv _ _).aemeasurable]
/-
**MeasureTheory.Measure.rnDeriv_zero** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Me
asure`。
形式化陈述：rnDeriv_zero (ν : Measure α) : (0 : Measure α).rnDeriv ν =ᵐ[ν] 0
参数：ν : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.rnDeriv_eq_zero`：rnDeriv_eq_zero (μ ν : Measure α)
 [μ.HaveLebesgueDecomposition ν] : μ.rnDeriv ν =ᵐ[ν] 0 ↔ μ ⟂ₘ ν
· 使用定理 `MeasureTheory.Measure.MutuallySingular.zero_left`：zero_left : 0 ⟂ₘ μ
-/
lemma rnDeriv_zero (ν : Measure α) : (0 : Measure α).rnDeriv ν =ᵐ[ν] 0 := by
  rw [rnDeriv_eq_zero]
  exact MutuallySingular.zero_left
/-
**MeasureTheory.Measure.MutuallySingular.rnDeriv_ae_eq_zero** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.Measure.MutuallySingular`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α}, 
μ.MutuallySingular ν → μ.rnDeriv ν =ᵐ[ν] 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.rnDeriv_eq_zero`：rnDeriv_eq_zero (μ ν : Measure α)
 [μ.HaveLebesgueDecomposition ν] : μ.rnDeriv ν =ᵐ[ν] 0 ↔ μ ⟂ₘ ν
· 使用引理 `MeasureTheory.Measure.rnDeriv_of_not_haveLebesgueDecomposition`：rnDeriv_
of_not_haveLebesgueDecomposition (h : ¬ HaveLebesgueDecomposition μ ν) : μ.rnDer
iv ν = 0
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
-/
lemma MutuallySingular.rnDeriv_ae_eq_zero (hμν : μ ⟂ₘ ν) :
    μ.rnDeriv ν =ᵐ[ν] 0 := by
  by_cases h : μ.HaveLebesgueDecomposition ν
  · rw [rnDeriv_eq_zero]
    exact hμν
  · rw [rnDeriv_of_not_haveLebesgueDecomposition h]

@[simp]
/-
**MeasureTheory.Measure.singularPart_withDensity** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.Measure`。
形式化陈述：singularPart_withDensity (ν : Measure α) (f : α -> Real>=0∞) : (ν.withDens
ity f).singularPart ν = 0
参数：ν : Measure α；f : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.Measure.singularPart_eq_zero_of_ac`：singularPart_eq_zero_o
f_ac (h : μ ≪ ν) : μ.singularPart ν = 0
· 使用定理 `MeasureTheory.withDensity_absolutelyContinuous`：withDensity_absolutelyCo
ntinuous {m : MeasurableSpace α} (μ : Measure α) (f : α -> Real>=0∞) : μ.withDen
sity f ≪ μ
-/
theorem singularPart_withDensity (ν : Measure α) (f : α → ℝ≥0∞) :
    (ν.withDensity f).singularPart ν = 0 :=
  singularPart_eq_zero_of_ac (withDensity_absolutelyContinuous _ _)
/-
**MeasureTheory.Measure.rnDeriv_singularPart** 是 Mathlib 中的一个引理，位于命名空间 `MeasureT
heory.Measure`。
形式化陈述：rnDeriv_singularPart (μ ν : Measure α) : (μ.singularPart ν).rnDeriv ν =ᵐ[ν
] 0
参数：μ ν : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.rnDeriv_eq_zero`：rnDeriv_eq_zero (μ ν : Measure α)
 [μ.HaveLebesgueDecomposition ν] : μ.rnDeriv ν =ᵐ[ν] 0 ↔ μ ⟂ₘ ν
· 使用定理 `MeasureTheory.Measure.mutuallySingular_singularPart`：mutuallySingular_si
ngularPart (μ ν : Measure α) : μ.singularPart ν ⟂ₘ ν
-/
lemma rnDeriv_singularPart (μ ν : Measure α) :
    (μ.singularPart ν).rnDeriv ν =ᵐ[ν] 0 := by
  rw [rnDeriv_eq_zero]
  exact mutuallySingular_singularPart μ ν

@[simp]
/-
**MeasureTheory.Measure.singularPart_self** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：singularPart_self (μ : Measure α) : μ.singularPart μ = 0
参数：μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.Measure.singularPart_eq_zero_of_ac`：singularPart_eq_zero_o
f_ac (h : μ ≪ ν) : μ.singularPart ν = 0
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.rfl`：∀ {α : Type u_1} {mα : M
easurableSpace α} {μ : MeasureTheory.Measure α}, μ.AbsolutelyContinuous μ
-/
lemma singularPart_self (μ : Measure α) : μ.singularPart μ = 0 :=
  singularPart_eq_zero_of_ac Measure.AbsolutelyContinuous.rfl
/-
**MeasureTheory.Measure.rnDeriv_self** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Me
asure`。
形式化陈述：rnDeriv_self (μ : Measure α) [SigmaFinite μ] : μ.rnDeriv μ =ᵐ[μ] fun _ => 
1
参数：μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.Measure.rnDeriv_add_singularPart`：rnDeriv_add_singularPart
 (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] : ν.withDensity (μ.rnDeriv ν)
 + μ.singularPart ν = μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.withDensity_one`：withDensity_one : μ.withDensity 1 = μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.withDensity_eq_iff_of_sigmaFinite`：withDensity_eq_iff_of_s
igmaFinite [SigmaFinite μ] {f g : α -> Real>=0∞} (hf : AEMeasurable f μ) (hg : A
EMeasurable g μ) : μ.withDensity f = …
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用定理 `aemeasurable_const`：aemeasurable_const {b : β} : AEMeasurable (fun _a : 
α => b) μ
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `MeasureTheory.Measure.singularPart_self`：singularPart_self (μ : Measure 
α) : μ.singularPart μ = 0
-/
lemma rnDeriv_self (μ : Measure α) [SigmaFinite μ] : μ.rnDeriv μ =ᵐ[μ] fun _ ↦ 1 := by
  have h := rnDeriv_add_singularPart μ μ
  rw [singularPart_self, add_zero] at h
  have h_one : μ = μ.withDensity 1 := by simp
  conv_rhs at h => rw [h_one]
  rwa [withDensity_eq_iff_of_sigmaFinite (measurable_rnDeriv _ _).aemeasurable] at h
  exact aemeasurable_const
/-
**MeasureTheory.Measure.singularPart_eq_self** 是 Mathlib 中的一个引理，位于命名空间 `MeasureT
heory.Measure`。
形式化陈述：singularPart_eq_self : μ.singularPart ν = μ ↔ μ ⟂ₘ ν
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.mutuallySingular_singularPart`：mutuallySingular_si
ngularPart (μ ν : Measure α) : μ.singularPart ν ⟂ₘ ν
· 使用定理 `MeasureTheory.Measure.MutuallySingular.haveLebesgueDecomposition`：∀ {α :
 Type u_1} {m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α},   μ.Mutually
Singular ν → μ.HaveLebesgueDecomposition ν
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `MeasureTheory.Measure.singularPart_add_rnDeriv`：singularPart_add_rnDeriv
 (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] : μ.singularPart ν + ν.withDe
nsity (μ.rnDeriv ν) = μ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `MeasureTheory.Measure.withDensity_rnDeriv_eq_zero`：withDensity_rnDeriv_e
q_zero (μ ν : Measure α) [μ.HaveLebesgueDecomposition ν] : ν.withDensity (μ.rnDe
riv ν) = 0 ↔ μ ⟂ₘ ν
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
lemma singularPart_eq_self : μ.singularPart ν = μ ↔ μ ⟂ₘ ν := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← h]
    exact mutuallySingular_singularPart _ _
  · have := h.haveLebesgueDecomposition
    conv_rhs => rw [← singularPart_add_rnDeriv μ ν]
    rw [(withDensity_rnDeriv_eq_zero _ _).mpr h, add_zero]

@[simp]
/-
**MeasureTheory.Measure.singularPart_singularPart** 是 Mathlib 中的一个引理，位于命名空间 `Mea
sureTheory.Measure`。
形式化陈述：singularPart_singularPart (μ ν : Measure α) : (μ.singularPart ν).singularP
art ν = μ.singularPart ν
参数：μ ν : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.singularPart_eq_self`：singularPart_eq_self : μ.sin
gularPart ν = μ ↔ μ ⟂ₘ ν
· 使用定理 `MeasureTheory.Measure.mutuallySingular_singularPart`：mutuallySingular_si
ngularPart (μ ν : Measure α) : μ.singularPart ν ⟂ₘ ν
-/
lemma singularPart_singularPart (μ ν : Measure α) :
    (μ.singularPart ν).singularPart ν = μ.singularPart ν := by
  rw [Measure.singularPart_eq_self]
  exact Measure.mutuallySingular_singularPart _ _
/-
**MeasureTheory.Measure.singularPart.instIsFiniteMeasure** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.Measure.singularPart`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [
MeasureTheory.IsFiniteMeasure μ],   MeasureTheory.IsFiniteMeasure (μ.singularPar
t ν)
参数：μ.singularPart ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.isFiniteMeasure_of_le`：isFiniteMeasure_of_le (μ : Measure 
α) [IsFiniteMeasure μ] (h : ν <= μ) : IsFiniteMeasure ν
· 使用定理 `MeasureTheory.Measure.singularPart_le`：singularPart_le (μ ν : Measure α)
 : μ.singularPart ν <= μ
-/
instance singularPart.instIsFiniteMeasure [IsFiniteMeasure μ] :
    IsFiniteMeasure (μ.singularPart ν) :=
  isFiniteMeasure_of_le μ <| singularPart_le μ ν
/-
**MeasureTheory.Measure.singularPart.instSigmaFinite** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.Measure.singularPart`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [
MeasureTheory.SigmaFinite μ],   MeasureTheory.SigmaFinite (μ.singularPart ν)
参数：μ.singularPart ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.sigmaFinite_of_le`：sigmaFinite_of_le (μ : Measure 
α) [hs : SigmaFinite μ] (h : ν <= μ) : SigmaFinite ν
· 使用定理 `MeasureTheory.Measure.singularPart_le`：singularPart_le (μ ν : Measure α)
 : μ.singularPart ν <= μ
-/
instance singularPart.instSigmaFinite [SigmaFinite μ] : SigmaFinite (μ.singularPart ν) :=
  sigmaFinite_of_le μ <| singularPart_le μ ν
/-
**MeasureTheory.Measure.singularPart.instIsLocallyFiniteMeasure** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory.Measure.singularPart`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [
inst : TopologicalSpace α]   [MeasureTheory.IsLocallyFiniteMeasure μ], MeasureTh
eory.IsLocallyFiniteMeasure (μ.singularPart ν)
参数：μ.singularPart ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.isLocallyFiniteMeasure_of_le`：isLocallyFiniteMeasu
re_of_le [TopologicalSpace α] {_m : MeasurableSpace α} {μ ν : Measure α} [H : Is
LocallyFiniteMeasure μ] (h : ν <= μ) : I…
· 使用定理 `MeasureTheory.Measure.singularPart_le`：singularPart_le (μ ν : Measure α)
 : μ.singularPart ν <= μ
-/
instance singularPart.instIsLocallyFiniteMeasure [TopologicalSpace α] [IsLocallyFiniteMeasure μ] :
    IsLocallyFiniteMeasure (μ.singularPart ν) :=
  isLocallyFiniteMeasure_of_le <| singularPart_le μ ν
/-
**MeasureTheory.Measure.withDensity.instIsFiniteMeasure** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.Measure.withDensity`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [
MeasureTheory.IsFiniteMeasure μ],   MeasureTheory.IsFiniteMeasure (ν.withDensity
 (μ.rnDeriv ν))
参数：ν.withDensity (μ.rnDeriv ν)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.isFiniteMeasure_of_le`：isFiniteMeasure_of_le (μ : Measure 
α) [IsFiniteMeasure μ] (h : ν <= μ) : IsFiniteMeasure ν
· 使用定理 `MeasureTheory.Measure.withDensity_rnDeriv_le`：withDensity_rnDeriv_le (μ 
ν : Measure α) : ν.withDensity (μ.rnDeriv ν) <= μ
-/
instance withDensity.instIsFiniteMeasure [IsFiniteMeasure μ] :
    IsFiniteMeasure (ν.withDensity <| μ.rnDeriv ν) :=
  isFiniteMeasure_of_le μ <| withDensity_rnDeriv_le μ ν
/-
**MeasureTheory.Measure.withDensity.instSigmaFinite** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.Measure.withDensity`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [
MeasureTheory.SigmaFinite μ],   MeasureTheory.SigmaFinite (ν.withDensity (μ.rnDe
riv ν))
参数：ν.withDensity (μ.rnDeriv ν)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.sigmaFinite_of_le`：sigmaFinite_of_le (μ : Measure 
α) [hs : SigmaFinite μ] (h : ν <= μ) : SigmaFinite ν
· 使用定理 `MeasureTheory.Measure.withDensity_rnDeriv_le`：withDensity_rnDeriv_le (μ 
ν : Measure α) : ν.withDensity (μ.rnDeriv ν) <= μ
-/
instance withDensity.instSigmaFinite [SigmaFinite μ] :
    SigmaFinite (ν.withDensity <| μ.rnDeriv ν) :=
  sigmaFinite_of_le μ <| withDensity_rnDeriv_le μ ν
/-
**MeasureTheory.Measure.withDensity.instIsLocallyFiniteMeasure** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory.Measure.withDensity`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [
inst : TopologicalSpace α]   [MeasureTheory.IsLocallyFiniteMeasure μ], MeasureTh
eory.IsLocallyFiniteMeasure (ν.withDensity (μ.rnDeriv ν))
参数：ν.withDensity (μ.rnDeriv ν)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.isLocallyFiniteMeasure_of_le`：isLocallyFiniteMeasu
re_of_le [TopologicalSpace α] {_m : MeasurableSpace α} {μ ν : Measure α} [H : Is
LocallyFiniteMeasure μ] (h : ν <= μ) : I…
· 使用定理 `MeasureTheory.Measure.withDensity_rnDeriv_le`：withDensity_rnDeriv_le (μ 
ν : Measure α) : ν.withDensity (μ.rnDeriv ν) <= μ
-/
instance withDensity.instIsLocallyFiniteMeasure [TopologicalSpace α] [IsLocallyFiniteMeasure μ] :
    IsLocallyFiniteMeasure (ν.withDensity <| μ.rnDeriv ν) :=
  isLocallyFiniteMeasure_of_le <| withDensity_rnDeriv_le μ ν

section RNDerivFinite

/-
**MeasureTheory.Measure.lintegral_rnDeriv_lt_top_of_measure_ne_top** 是 Mathlib 中
的一个定理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：lintegral_rnDeriv_lt_top_of_measure_ne_top (ν : Measure α) {s : Set α} (hs
 : μ s != ∞) : ∫⁻ x in s, μ.rnDeriv ν x ∂ν < ∞
参数：ν : Measure α；hs : μ s != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.withDensity_apply`：withDensity_apply (f : α -> Real>=0∞) {
s : Set α} (hs : MeasurableSet s) : μ.withDensity f s = ∫⁻ a in s, f a ∂μ
· 使用定理 `MeasureTheory.measurableSet_toMeasurable`：measurableSet_toMeasurable (μ 
: Measure α) (s : Set α) : MeasurableSet (toMeasurable μ s)
· 使用定理 `le_add_self`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ b + a
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `MeasureTheory.Measure.add_apply`：add_apply {_m : MeasurableSpace α} (μ₁ 
μ₂ : Measure α) (s : Set α) : (μ₁ + μ₂) s = μ₁ s + μ₂ s
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_add`：haveLebesgueDecompo
sition_add (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] : μ = μ.singularPar
t ν + ν.withDensity (μ.rnDeriv ν)
· 使用定理 `MeasureTheory.measure_toMeasurable`：measure_toMeasurable (s : Set α) : μ
 (toMeasurable μ s) = μ s
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `MeasureTheory.lintegral_mono_set`：lintegral_mono_set {_ : MeasurableSpac
e α} ⦃μ : Measure α⦄ {s t : Set α} {f : α -> Real>=0∞} (hst : s subseteq t) : ∫⁻
 x in s, f x ∂μ <= ∫⁻ …
· 使用定理 `MeasureTheory.subset_toMeasurable`：subset_toMeasurable (μ : Measure α) (
s : Set α) : s subseteq toMeasurable μ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.Measure.HaveLebesgueDecomposition.lebesgue_decomposition`：
∀ {α : Type u_1} {m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [self :
 μ.HaveLebesgueDecomposition ν],   ∃ p, Measurable p.2 ∧ p.1…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasureTheory.Measure.rnDeriv_def`：∀ {α : Type u_2} {m : MeasurableSpace
 α} (μ ν : MeasureTheory.Measure α),   μ.rnDeriv ν = if h : μ.HaveLebesgueDecomp
osition ν then (Classic…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `MeasureTheory.lintegral_zero`：lintegral_zero : ∫⁻ _ : α, 0 ∂μ = 0
-/
theorem lintegral_rnDeriv_lt_top_of_measure_ne_top (ν : Measure α) {s : Set α} (hs : μ s ≠ ∞) :
    ∫⁻ x in s, μ.rnDeriv ν x ∂ν < ∞ := by
  by_cases hl : HaveLebesgueDecomposition μ ν
  · suffices (∫⁻ x in toMeasurable μ s, μ.rnDeriv ν x ∂ν) < ∞ from
      lt_of_le_of_lt (lintegral_mono_set (subset_toMeasurable _ _)) this
    rw [← withDensity_apply _ (measurableSet_toMeasurable _ _)]
    calc
      _ ≤ (singularPart μ ν) (toMeasurable μ s) + _ := le_add_self
      _ = μ s := by rw [← Measure.add_apply, ← haveLebesgueDecomposition_add, measure_toMeasurable]
      _ < ⊤ := hs.lt_top
  · simp only [Measure.rnDeriv, dif_neg hl, Pi.zero_apply, lintegral_zero, ENNReal.zero_lt_top]
/-
**MeasureTheory.Measure.lintegral_rnDeriv_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.Measure`。
形式化陈述：lintegral_rnDeriv_lt_top (μ ν : Measure α) [IsFiniteMeasure μ] : ∫⁻ x, μ.r
nDeriv ν x ∂ν < ∞
参数：μ ν : Measure α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setLIntegral_univ`：setLIntegral_univ (f : α -> Real>=0∞) :
 ∫⁻ x in univ, f x ∂μ = ∫⁻ x, f x ∂μ
· 使用定理 `MeasureTheory.Measure.lintegral_rnDeriv_lt_top_of_measure_ne_top`：linteg
ral_rnDeriv_lt_top_of_measure_ne_top (ν : Measure α) {s : Set α} (hs : μ s != ∞)
 : ∫⁻ x in s, μ.rnDeriv ν x ∂ν < ∞
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.measure_lt_top`：measure_lt_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s < ∞
-/
theorem lintegral_rnDeriv_lt_top (μ ν : Measure α) [IsFiniteMeasure μ] :
    ∫⁻ x, μ.rnDeriv ν x ∂ν < ∞ := by
  rw [← setLIntegral_univ]
  exact lintegral_rnDeriv_lt_top_of_measure_ne_top _ (measure_lt_top _ _).ne

/-- The Radon-Nikodym derivative of a sigma-finite measure `μ` with respect to another
measure `ν` is `ν`-almost everywhere finite. -/
/-
**MeasureTheory.Measure.rnDeriv_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：rnDeriv_lt_top (μ ν : Measure α) [SigmaFinite μ] : forallᵐ x ∂ν, μ.rnDeriv
 ν x < ∞
参数：μ ν : Measure α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.ae_restrict_iff'`：ae_restrict_iff'₀ {p : α -> Prop} (hs : 
NullMeasurableSet s μ) : (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s -
> p x
· 使用定理 `MeasureTheory.measurableSet_spanningSets`：measurableSet_spanningSets (μ 
: Measure α) [SigmaFinite μ] (i : Nat) : MeasurableSet (spanningSets μ i)
· 使用定理 `MeasureTheory.ae_lt_top`：ae_lt_top {f : α -> Real>=0∞} (hf : Measurable 
f) (h2f : ∫⁻ x, f x ∂μ != ∞) : forallᵐ x ∂μ, f x < ∞
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.Measure.lintegral_rnDeriv_lt_top_of_measure_ne_top`：linteg
ral_rnDeriv_lt_top_of_measure_ne_top (ν : Measure α) {s : Set α} (hs : μ s != ∞)
 : ∫⁻ x in s, μ.rnDeriv ν x ∂ν < ∞
· 使用定理 `MeasureTheory.measure_spanningSets_lt_top`：measure_spanningSets_lt_top (
μ : Measure α) [SigmaFinite μ] (i : Nat) : μ (spanningSets μ i) < ∞
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.mem_spanningSetsIndex`：mem_spanningSetsIndex (μ : Measure 
α) [SigmaFinite μ] (x : α) : x in spanningSets μ (spanningSetsIndex μ x)

--- 原说明 ---
The Radon-Nikodym derivative of a sigma-finite measure `μ` with respect to anoth
er
measure `ν` is `ν`-almost everywhere finite.
-/
theorem rnDeriv_lt_top (μ ν : Measure α) [SigmaFinite μ] : ∀ᵐ x ∂ν, μ.rnDeriv ν x < ∞ := by
  suffices ∀ n, ∀ᵐ x ∂ν, x ∈ spanningSets μ n → μ.rnDeriv ν x < ∞ by
    filter_upwards [ae_all_iff.2 this] with _ hx using hx _ (mem_spanningSetsIndex _ _)
  intro n
  rw [← ae_restrict_iff' (measurableSet_spanningSets _ _)]
  apply ae_lt_top (measurable_rnDeriv _ _)
  refine (lintegral_rnDeriv_lt_top_of_measure_ne_top _ ?_).ne
  exact (measure_spanningSets_lt_top _ _).ne
/-
**MeasureTheory.Measure.rnDeriv_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：rnDeriv_ne_top (μ ν : Measure α) [SigmaFinite μ] : forallᵐ x ∂ν, μ.rnDeriv
 ν x != ∞
参数：μ ν : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.rnDeriv_lt_top`：rnDeriv_lt_top (μ ν : Measure α) [
SigmaFinite μ] : forallᵐ x ∂ν, μ.rnDeriv ν x < ∞
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
-/
lemma rnDeriv_ne_top (μ ν : Measure α) [SigmaFinite μ] : ∀ᵐ x ∂ν, μ.rnDeriv ν x ≠ ∞ := by
  filter_upwards [Measure.rnDeriv_lt_top μ ν] with x hx using hx.ne

end RNDerivFinite

/-- Given measures `μ` and `ν`, if `s` is a measure mutually singular to `ν` and `f` is a
measurable function such that `μ = s + fν`, then `s = μ.singularPart μ`.

This theorem provides the uniqueness of the `singularPart` in the Lebesgue decomposition theorem,
while `MeasureTheory.Measure.eq_rnDeriv` provides the uniqueness of the
`rnDeriv`. -/
/-
**MeasureTheory.Measure.eq_singularPart** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Measure`。
形式化陈述：eq_singularPart {s : Measure α} {f : α -> Real>=0∞} (hf : Measurable f) (h
s : s ⟂ₘ ν) (hadd : μ = s + ν.withDensity f) : s = μ.singularPart ν
参数：hf : Measurable f；hs : s ⟂ₘ ν；hadd : μ = s + ν.withDensity f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_spec`：haveLebesgueDecomp
osition_spec (μ ν : Measure α) [h : HaveLebesgueDecomposition μ ν] : Measurable 
(μ.rnDeriv ν) ∧ μ.singularPart ν ⟂ₘ ν ∧ μ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_inter`：compl_inter (s t : Set α) : (s inter t)ᶜ = sᶜ union tᶜ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `MeasureTheory.measure_union_le`：measure_union_le (s t : Set α) : μ (s un
ion t) <= μ s + μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `MeasureTheory.withDensity_absolutelyContinuous`：withDensity_absolutelyCo
ntinuous {m : MeasurableSpace α} (μ : Measure α) (f : α -> Real>=0∞) : μ.withDen
sity f ≪ μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasureTheory.Measure.add_apply`：add_apply {_m : MeasurableSpace α} (μ₁ 
μ₂ : Measure α) (s : Set α) : (μ₁ + μ₂) s = μ₁ s + μ₂ s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.sdiff_eq`：sdiff_eq (s t : Set α) : s \ t = s inter tᶜ
· 使用定理 `MeasureTheory.AEDisjoint.measure_sdiff_left`：measure_sdiff_left (h : AED
isjoint μ s t) : μ (s \ t) = μ s

--- 原说明 ---
Given measures `μ` and `ν`, if `s` is a measure mutually singular to `ν` and `f`
 is a
measurable function such that `μ = s + fν`, then `s = μ.singularPart μ`.

This theorem provides the uniqueness of the `singularPart` in the Lebesgue decom
position theorem,
while `MeasureTheory.Measure.eq_rnDeriv` provides the uniqueness of the
`rnDeriv`.
-/
theorem eq_singularPart {s : Measure α} {f : α → ℝ≥0∞} (hf : Measurable f) (hs : s ⟂ₘ ν)
    (hadd : μ = s + ν.withDensity f) : s = μ.singularPart ν := by
  have : HaveLebesgueDecomposition μ ν := ⟨⟨⟨s, f⟩, hf, hs, hadd⟩⟩
  obtain ⟨hmeas, hsing, hadd'⟩ := haveLebesgueDecomposition_spec μ ν
  obtain ⟨⟨S, hS₁, hS₂, hS₃⟩, ⟨T, hT₁, hT₂, hT₃⟩⟩ := hs, hsing
  rw [hadd'] at hadd
  have hνinter : ν (S ∩ T)ᶜ = 0 := by
    rw [compl_inter]
    refine nonpos_iff_eq_zero.1 (le_trans (measure_union_le _ _) ?_)
    rw [hT₃, hS₃, add_zero]
  have heq : s.restrict (S ∩ T)ᶜ = (μ.singularPart ν).restrict (S ∩ T)ᶜ := by
    ext1 A hA
    have hf : ν.withDensity f (A ∩ (S ∩ T)ᶜ) = 0 := by
      refine withDensity_absolutelyContinuous ν _ ?_
      rw [← nonpos_iff_eq_zero]
      exact hνinter ▸ measure_mono inter_subset_right
    have hrn : ν.withDensity (μ.rnDeriv ν) (A ∩ (S ∩ T)ᶜ) = 0 := by
      refine withDensity_absolutelyContinuous ν _ ?_
      rw [← nonpos_iff_eq_zero]
      exact hνinter ▸ measure_mono inter_subset_right
    rw [restrict_apply hA, restrict_apply hA, ← add_zero (s (A ∩ (S ∩ T)ᶜ)), ← hf, ← add_apply, ←
      hadd, add_apply, hrn, add_zero]
  have heq' : ∀ A : Set α, MeasurableSet A → s A = s.restrict (S ∩ T)ᶜ A := by
    intro A hA
    have hsinter : s (A ∩ (S ∩ T)) = 0 := by
      rw [← nonpos_iff_eq_zero]
      exact hS₂ ▸ measure_mono (inter_subset_right.trans inter_subset_left)
    rw [restrict_apply hA, ← sdiff_eq, AEDisjoint.measure_sdiff_left hsinter]
  ext1 A hA
  have hμinter : μ.singularPart ν (A ∩ (S ∩ T)) = 0 := by
    rw [← nonpos_iff_eq_zero]
    exact hT₂ ▸ measure_mono (inter_subset_right.trans inter_subset_right)
  rw [heq' A hA, heq, restrict_apply hA, ← sdiff_eq, AEDisjoint.measure_sdiff_left hμinter]
/-
**MeasureTheory.Measure.singularPart_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：singularPart_smul (μ ν : Measure α) (r : Real>=0) : (r • μ).singularPart ν
 = r • μ.singularPart ν
参数：μ ν : Measure α；r : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `MeasureTheory.Measure.singularPart_zero`：singularPart_zero (ν : Measure 
α) : (0 : Measure α).singularPart ν = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.eq_singularPart`：eq_singularPart {s : Measure α} {
f : α -> Real>=0∞} (hf : Measurable f) (hs : s ⟂ₘ ν) (hadd : μ = s + ν.withDensi
ty f) : s = μ.singularPart …
· 使用引理 `Measurable.const_smul`：Measurable.const_smul (hg : Measurable g) (c : M)
 : Measurable (c • g)
· 使用定理 `MeasurableSMul.toMeasurableConstSMul`：∀ {M : Type u_2} {α : Type u_3} {i
nst : SMul M α} {inst_1 : MeasurableSpace M} {inst_2 : MeasurableSpace α}   [sel
f : MeasurableSMul M α], M…
· 使用定理 `measurableSMul_of_mul`：∀ (M : Type u_2) [inst : Mul M] [inst_1 : Measura
bleSpace M] [MeasurableMul M], MeasurableSMul M M
· 使用定理 `MeasurableMul₂.toMeasurableMul`：∀ {M : Type u_2} [inst : MeasurableSpace
 M] [inst_1 : Mul M] [MeasurableMul₂ M], MeasurableMul M
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用定理 `MeasureTheory.Measure.MutuallySingular.smul`：smul (r : Real>=0∞) (h : ν 
⟂ₘ μ) : r • ν ⟂ₘ μ
· 使用定理 `MeasureTheory.Measure.mutuallySingular_singularPart`：mutuallySingular_si
ngularPart (μ ν : Measure α) : μ.singularPart ν ⟂ₘ ν
· 使用定理 `MeasureTheory.withDensity_smul`：withDensity_smul (r : Real>=0∞) {f : α -
> Real>=0∞} (hf : Measurable f) : μ.withDensity (r • f) = r • μ.withDensity f
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_add`：haveLebesgueDecompo
sition_add (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] : μ = μ.singularPar
t ν + ν.withDensity (μ.rnDeriv ν)
· 使用定理 `ENNReal.smul_def`：smul_def {M : Type*} [MulAction Real>=0∞ M] (c : Real>
=0) (x : M) : c • x = (c : Real>=0∞) • x
· 使用定理 `MeasureTheory.Measure.HaveLebesgueDecomposition.lebesgue_decomposition`：
∀ {α : Type u_1} {m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [self :
 μ.HaveLebesgueDecomposition ν],   ∃ p, Measurable p.2 ∧ p.1…
· 使用定理 `MeasureTheory.Measure.singularPart_def`：∀ {α : Type u_2} {m : Measurable
Space α} (μ ν : MeasureTheory.Measure α),   μ.singularPart ν = if h : μ.HaveLebe
sgueDecomposition ν then (Cl…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem singularPart_smul (μ ν : Measure α) (r : ℝ≥0) :
    (r • μ).singularPart ν = r • μ.singularPart ν := by
  by_cases hr : r = 0
  · rw [hr, zero_smul, zero_smul, singularPart_zero]
  by_cases hl : HaveLebesgueDecomposition μ ν
  · refine (eq_singularPart ((measurable_rnDeriv μ ν).const_smul (r : ℝ≥0∞))
          (MutuallySingular.smul r (mutuallySingular_singularPart _ _)) ?_).symm
    rw [withDensity_smul _ (measurable_rnDeriv _ _), ← smul_add,
      ← haveLebesgueDecomposition_add μ ν, ENNReal.smul_def]
  · rw [singularPart, singularPart, dif_neg hl, dif_neg, smul_zero]
    refine fun hl' ↦ hl ?_
    rw [← inv_smul_smul₀ hr μ]
    infer_instance
/-
**MeasureTheory.Measure.singularPart_smul_right** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.Measure`。
形式化陈述：singularPart_smul_right (μ ν : Measure α) (r : Real>=0) (hr : r != 0) : μ.
singularPart (r • ν) = μ.singularPart ν
参数：μ ν : Measure α；r : Real>=0；hr : r != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.eq_singularPart`：eq_singularPart {s : Measure α} {
f : α -> Real>=0∞} (hf : Measurable f) (hs : s ⟂ₘ ν) (hadd : μ = s + ν.withDensi
ty f) : s = μ.singularPart …
· 使用引理 `Measurable.const_smul`：Measurable.const_smul (hg : Measurable g) (c : M)
 : Measurable (c • g)
· 使用定理 `MeasurableSMul.toMeasurableConstSMul`：∀ {M : Type u_2} {α : Type u_3} {i
nst : SMul M α} {inst_1 : MeasurableSpace M} {inst_2 : MeasurableSpace α}   [sel
f : MeasurableSMul M α], M…
· 使用定理 `ENNReal.instMeasurableSMulNNReal`：MeasurableSMul NNReal ENNReal
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用定理 `MeasureTheory.Measure.MutuallySingular.mono_ac`：mono_ac (h : μ₁ ⟂ₘ ν₁) (
hμ : μ₂ ≪ μ₁) (hν : ν₂ ≪ ν₁) : μ₂ ⟂ₘ ν₂
· 使用定理 `MeasureTheory.Measure.mutuallySingular_singularPart`：mutuallySingular_si
ngularPart (μ ν : Measure α) : μ.singularPart ν ⟂ₘ ν
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.rfl`：∀ {α : Type u_1} {mα : M
easurableSpace α} {μ : MeasureTheory.Measure α}, μ.AbsolutelyContinuous μ
· 使用引理 `MeasureTheory.Measure.smul_absolutelyContinuous`：smul_absolutelyContinuo
us {c : Real>=0∞} : c • μ ≪ μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.smul_def`：smul_def {M : Type*} [MulAction Real>=0∞ M] (c : Real>
=0) (x : M) : c • x = (c : Real>=0∞) • x
· 使用定理 `MeasureTheory.withDensity_smul_measure`：withDensity_smul_measure (r : Re
al>=0∞) (f : α -> Real>=0∞) : (r • μ).withDensity f = r • μ.withDensity f
· 使用定理 `MeasureTheory.withDensity_smul`：withDensity_smul (r : Real>=0∞) {f : α -
> Real>=0∞} (hf : Measurable f) : μ.withDensity (r • f) = r • μ.withDensity f
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `smul_inv_smul₀`：smul_inv_smul₀ (ha : a != 0) (x : β) : a • a⁻¹ • x = x
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_add`：haveLebesgueDecompo
sition_add (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] : μ = μ.singularPar
t ν + ν.withDensity (μ.rnDeriv ν)
· 使用定理 `MeasureTheory.Measure.HaveLebesgueDecomposition.lebesgue_decomposition`：
∀ {α : Type u_1} {m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [self :
 μ.HaveLebesgueDecomposition ν],   ∃ p, Measurable p.2 ∧ p.1…
· 使用定理 `MeasureTheory.Measure.singularPart_def`：∀ {α : Type u_2} {m : Measurable
Space α} (μ ν : MeasureTheory.Measure α),   μ.singularPart ν = if h : μ.HaveLebe
sgueDecomposition ν then (Cl…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
-/
theorem singularPart_smul_right (μ ν : Measure α) (r : ℝ≥0) (hr : r ≠ 0) :
    μ.singularPart (r • ν) = μ.singularPart ν := by
  by_cases hl : HaveLebesgueDecomposition μ ν
  · refine (eq_singularPart ((measurable_rnDeriv μ ν).const_smul r⁻¹) ?_ ?_).symm
    · exact (mutuallySingular_singularPart μ ν).mono_ac AbsolutelyContinuous.rfl
        smul_absolutelyContinuous
    · rw [ENNReal.smul_def r, withDensity_smul_measure, ← withDensity_smul]
      swap; · exact (measurable_rnDeriv _ _).const_smul _
      convert! haveLebesgueDecomposition_add μ ν
      ext x
      simp only [Pi.smul_apply]
      rw [← ENNReal.smul_def, smul_inv_smul₀ hr]
  · rw [singularPart, singularPart, dif_neg hl, dif_neg]
    refine fun hl' ↦ hl ?_
    rw [← inv_smul_smul₀ hr ν]
    infer_instance
/-
**MeasureTheory.Measure.singularPart_add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Measure`。
形式化陈述：singularPart_add (μ₁ μ₂ ν : Measure α) [HaveLebesgueDecomposition μ₁ ν] [H
aveLebesgueDecomposition μ₂ ν] : (μ₁ + μ₂).singularPart ν = μ₁.singularPart ν + 
μ₂.singularPart ν
参数：μ₁ μ₂ ν : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.eq_singularPart`：eq_singularPart {s : Measure α} {
f : α -> Real>=0∞} (hf : Measurable f) (hs : s ⟂ₘ ν) (hadd : μ = s + ν.withDensi
ty f) : s = μ.singularPart …
· 使用定理 `Measurable.add`：∀ {M : Type u_2} {α : Type u_3} [inst : MeasurableSpace 
M] [inst_1 : Add M] {m : MeasurableSpace α} {f g : α → M}   [MeasurableAdd₂ M], 
Meas…
· 使用定理 `ContinuousAdd.measurableMul₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Add γ] [Con…
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `ENNReal.instContinuousAdd`：ContinuousAdd ENNReal
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用定理 `MeasureTheory.Measure.MutuallySingular.add_left`：add_left (h₁ : ν₁ ⟂ₘ μ)
 (h₂ : ν₂ ⟂ₘ μ) : ν₁ + ν₂ ⟂ₘ μ
· 使用定理 `MeasureTheory.Measure.mutuallySingular_singularPart`：mutuallySingular_si
ngularPart (μ ν : Measure α) : μ.singularPart ν ⟂ₘ ν
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.withDensity_add_left`：withDensity_add_left {f : α -> Real>
=0∞} (hf : Measurable f) (g : α -> Real>=0∞) : μ.withDensity (f + g) = μ.withDen
sity f + μ.withDensity g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_add`：haveLebesgueDecompo
sition_add (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] : μ = μ.singularPar
t ν + ν.withDensity (μ.rnDeriv ν)
-/
theorem singularPart_add (μ₁ μ₂ ν : Measure α) [HaveLebesgueDecomposition μ₁ ν]
    [HaveLebesgueDecomposition μ₂ ν] :
    (μ₁ + μ₂).singularPart ν = μ₁.singularPart ν + μ₂.singularPart ν := by
  refine (eq_singularPart ((measurable_rnDeriv μ₁ ν).add (measurable_rnDeriv μ₂ ν))
    ((mutuallySingular_singularPart _ _).add_left (mutuallySingular_singularPart _ _)) ?_).symm
  rw [withDensity_add_left (measurable_rnDeriv μ₁ ν)]
  conv_rhs => rw [add_assoc, add_comm (μ₂.singularPart ν), ← add_assoc, ← add_assoc]
  rw [← haveLebesgueDecomposition_add μ₁ ν, add_assoc, add_comm (ν.withDensity (μ₂.rnDeriv ν)),
    ← haveLebesgueDecomposition_add μ₂ ν]
/-
**MeasureTheory.Measure.singularPart_restrict** 是 Mathlib 中的一个引理，位于命名空间 `Measure
Theory.Measure`。
形式化陈述：singularPart_restrict (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] {s
 : Set α} (hs : MeasurableSet s) : (μ.restrict s).singularPart ν = (μ.singularPa
rt ν).restrict s
参数：μ ν : Measure α；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.eq_singularPart`：eq_singularPart {s : Measure α} {
f : α -> Real>=0∞} (hf : Measurable f) (hs : s ⟂ₘ ν) (hadd : μ = s + ν.withDensi
ty f) : s = μ.singularPart …
· 使用定理 `Measurable.indicator`：Measurable.indicator [Zero β] (hf : Measurable f) 
(hs : MeasurableSet s) : Measurable (s.indicator f)
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用引理 `MeasureTheory.Measure.MutuallySingular.restrict`：restrict (h : μ ⟂ₘ ν) (
s : Set α) : μ.restrict s ⟂ₘ ν
· 使用定理 `MeasureTheory.Measure.mutuallySingular_singularPart`：mutuallySingular_si
ngularPart (μ ν : Measure α) : μ.singularPart ν ⟂ₘ ν
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.withDensity_indicator`：withDensity_indicator {s : Set α} (
hs : MeasurableSet s) (f : α -> Real>=0∞) : μ.withDensity (s.indicator f) = (μ.r
estrict s).withDensity f
· 使用定理 `MeasureTheory.restrict_withDensity`：restrict_withDensity {s : Set α} (hs
 : MeasurableSet s) (f : α -> Real>=0∞) : (μ.withDensity f).restrict s = (μ.rest
rict s).withDensity f
· 使用定理 `MeasureTheory.Measure.restrict_add`：restrict_add {_m0 : MeasurableSpace 
α} (μ ν : Measure α) (s : Set α) : (μ + ν).restrict s = μ.restrict s + ν.restric
t s
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_add`：haveLebesgueDecompo
sition_add (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] : μ = μ.singularPar
t ν + ν.withDensity (μ.rnDeriv ν)
-/
lemma singularPart_restrict (μ ν : Measure α) [HaveLebesgueDecomposition μ ν]
    {s : Set α} (hs : MeasurableSet s) :
    (μ.restrict s).singularPart ν = (μ.singularPart ν).restrict s := by
  refine (Measure.eq_singularPart (f := s.indicator (μ.rnDeriv ν)) ?_ ?_ ?_).symm
  · exact (μ.measurable_rnDeriv ν).indicator hs
  · exact (Measure.mutuallySingular_singularPart μ ν).restrict s
  · ext t
    rw [withDensity_indicator hs, ← restrict_withDensity hs, ← Measure.restrict_add,
      ← μ.haveLebesgueDecomposition_add ν]

/-- If a set `s` separates the absolutely continuous part of `μ` with respect to `ν`
from the singular part, then the singular part equals the restriction of `μ` to `s`. -/
/-
**MeasureTheory.Measure.singularPart_eq_restrict'** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.Measure`。
形式化陈述：singularPart_eq_restrict' {s : Set α} [μ.HaveLebesgueDecomposition ν] (hμs
 : μ.singularPart ν sᶜ = 0) (hνs : ν.withDensity (μ.rnDeriv ν) s = 0) : μ.singul
arPart ν = μ.restrict s
参数：hμs : μ.singularPart ν sᶜ = 0；hνs : ν.withDensity (μ.rnDeriv ν) s = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.singularPart_add_rnDeriv`：singularPart_add_rnDeriv
 (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] : μ.singularPart ν + ν.withDe
nsity (μ.rnDeriv ν) = μ
· 使用定理 `MeasureTheory.Measure.restrict_add`：restrict_add {_m0 : MeasurableSpace 
α} (μ ν : Measure α) (s : Set α) : (μ + ν).restrict s = μ.restrict s + ν.restric
t s
· 使用定理 `MeasureTheory.Measure.restrict_eq_self_of_ae_mem`：restrict_eq_self_of_ae
_mem {_m0 : MeasurableSpace α} ⦃s : Set α⦄ ⦃μ : Measure α⦄ (hs : forallᵐ x ∂μ, x
 in s) : μ.restrict s = μ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.restrict_eq_zero`：restrict_eq_zero : μ.restrict s 
= 0 ↔ μ s = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a

--- 原说明 ---
If a set `s` separates the absolutely continuous part of `μ` with respect to `ν`
from the singular part, then the singular part equals the restriction of `μ` to 
`s`.
-/
theorem singularPart_eq_restrict' {s : Set α} [μ.HaveLebesgueDecomposition ν]
    (hμs : μ.singularPart ν sᶜ = 0) (hνs : ν.withDensity (μ.rnDeriv ν) s = 0) :
    μ.singularPart ν = μ.restrict s := by
  conv_rhs => rw [← singularPart_add_rnDeriv μ ν]
  rwa [restrict_add, restrict_eq_self_of_ae_mem, restrict_eq_zero.2 hνs, add_zero]

/-- If a set `s` separates `ν` from the singular part of `μ` with respect to `ν`,
then the singular part equals the restriction of `μ` to `s`. -/
/-
**MeasureTheory.Measure.singularPart_eq_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.Measure`。
形式化陈述：singularPart_eq_restrict {s : Set α} [μ.HaveLebesgueDecomposition ν] (hμs 
: μ.singularPart ν sᶜ = 0) (hνs : ν s = 0) : μ.singularPart ν = μ.restrict s
参数：hμs : μ.singularPart ν sᶜ = 0；hνs : ν s = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.singularPart_eq_restrict'`：singularPart_eq_restric
t' {s : Set α} [μ.HaveLebesgueDecomposition ν] (hμs : μ.singularPart ν sᶜ = 0) (
hνs : ν.withDensity (μ.rnDeriv ν) s =…
· 使用定理 `MeasureTheory.withDensity_absolutelyContinuous`：withDensity_absolutelyCo
ntinuous {m : MeasurableSpace α} (μ : Measure α) (f : α -> Real>=0∞) : μ.withDen
sity f ≪ μ

--- 原说明 ---
If a set `s` separates `ν` from the singular part of `μ` with respect to `ν`,
then the singular part equals the restriction of `μ` to `s`.
-/
theorem singularPart_eq_restrict {s : Set α} [μ.HaveLebesgueDecomposition ν]
    (hμs : μ.singularPart ν sᶜ = 0) (hνs : ν s = 0) :
    μ.singularPart ν = μ.restrict s :=
  singularPart_eq_restrict' hμs <| withDensity_absolutelyContinuous _ _ hνs
/-
**MeasureTheory.Measure.measure_sub_singularPart** 是 Mathlib 中的一个引理，位于命名空间 `Meas
ureTheory.Measure`。
形式化陈述：measure_sub_singularPart (μ ν : Measure α) [HaveLebesgueDecomposition μ ν]
 [IsFiniteMeasure μ] : μ - μ.singularPart ν = ν.withDensity (μ.rnDeriv ν)
参数：μ ν : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.rnDeriv_add_singularPart`：rnDeriv_add_singularPart
 (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] : ν.withDensity (μ.rnDeriv ν)
 + μ.singularPart ν = μ
· 使用定理 `MeasureTheory.Measure.add_sub_cancel`：∀ {α : Type u_1} {m : MeasurableSp
ace α} {μ ν : MeasureTheory.Measure α} [MeasureTheory.IsFiniteMeasure ν],   μ + 
ν - ν = μ
· 使用定理 `MeasureTheory.Measure.singularPart.instIsFiniteMeasure`：∀ {α : Type u_1}
 {m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [MeasureTheory.IsFinite
Measure μ],   MeasureTheory.IsFiniteMeasure …
-/
lemma measure_sub_singularPart (μ ν : Measure α) [HaveLebesgueDecomposition μ ν]
    [IsFiniteMeasure μ] :
    μ - μ.singularPart ν = ν.withDensity (μ.rnDeriv ν) := by
  nth_rw 1 [← rnDeriv_add_singularPart μ ν]
  exact Measure.add_sub_cancel
/-
**MeasureTheory.Measure.measure_sub_rnDeriv** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTh
eory.Measure`。
形式化陈述：measure_sub_rnDeriv (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] [IsF
initeMeasure μ] : μ - ν.withDensity (μ.rnDeriv ν) = μ.singularPart ν
参数：μ ν : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.singularPart_add_rnDeriv`：singularPart_add_rnDeriv
 (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] : μ.singularPart ν + ν.withDe
nsity (μ.rnDeriv ν) = μ
· 使用定理 `MeasureTheory.Measure.add_sub_cancel`：∀ {α : Type u_1} {m : MeasurableSp
ace α} {μ ν : MeasureTheory.Measure α} [MeasureTheory.IsFiniteMeasure ν],   μ + 
ν - ν = μ
· 使用定理 `MeasureTheory.Measure.withDensity.instIsFiniteMeasure`：∀ {α : Type u_1} 
{m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [MeasureTheory.IsFiniteM
easure μ],   MeasureTheory.IsFiniteMeasure …
-/
lemma measure_sub_rnDeriv (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] [IsFiniteMeasure μ] :
    μ - ν.withDensity (μ.rnDeriv ν) = μ.singularPart ν := by
  nth_rw 1 [← singularPart_add_rnDeriv μ ν]
  exact Measure.add_sub_cancel

/-- Given measures `μ` and `ν`, if `s` is a measure mutually singular to `ν` and `f` is a
measurable function such that `μ = s + fν`, then `f = μ.rnDeriv ν`.

This theorem provides the uniqueness of the `rnDeriv` in the Lebesgue decomposition
theorem, while `MeasureTheory.Measure.eq_singularPart` provides the uniqueness of the
`singularPart`. Here, the uniqueness is given in terms of the measures, while the uniqueness in
terms of the functions is given in `eq_rnDeriv`. -/
/-
**MeasureTheory.Measure.eq_withDensity_rnDeriv** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.Measure`。
形式化陈述：eq_withDensity_rnDeriv {s : Measure α} {f : α -> Real>=0∞} (hf : Measurabl
e f) (hs : s ⟂ₘ ν) (hadd : μ = s + ν.withDensity f) : ν.withDensity f = ν.withDe
nsity (μ.rnDeriv ν)
参数：hf : Measurable f；hs : s ⟂ₘ ν；hadd : μ = s + ν.withDensity f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_spec`：haveLebesgueDecomp
osition_spec (μ ν : Measure α) [h : HaveLebesgueDecomposition μ ν] : Measurable 
(μ.rnDeriv ν) ∧ μ.singularPart ν ⟂ₘ ν ∧ μ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_inter`：compl_inter (s t : Set α) : (s inter t)ᶜ = sᶜ union tᶜ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `MeasureTheory.measure_union_le`：measure_union_le (s t : Set α) : μ (s un
ion t) <= μ s + μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasureTheory.Measure.add_apply`：add_apply {_m : MeasurableSpace α} (μ₁ 
μ₂ : Measure α) (s : Set α) : (μ₁ + μ₂) s = μ₁ s + μ₂ s
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `MeasureTheory.withDensity_absolutelyContinuous`：withDensity_absolutelyCo
ntinuous {m : MeasurableSpace α} (μ : Measure α) (f : α -> Real>=0∞) : μ.withDen
sity f ≪ μ
· 使用定理 `Set.sdiff_eq`：sdiff_eq (s t : Set α) : s \ t = s inter tᶜ
· 使用定理 `MeasureTheory.measure_inter_add_sdiff`：measure_inter_add_sdiff (s : Set 
α) (ht : MeasurableSet t) : μ (s inter t) + μ (s \ t) = μ s
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)

--- 原说明 ---
Given measures `μ` and `ν`, if `s` is a measure mutually singular to `ν` and `f`
 is a
measurable function such that `μ = s + fν`, then `f = μ.rnDeriv ν`.

This theorem provides the uniqueness of the `rnDeriv` in the Lebesgue decomposit
ion
theorem, while `MeasureTheory.Measure.eq_singularPart` provides the uniqueness o
f the
`singularPart`. Here, the uniqueness is given in terms of the measures, while th
e uniqueness in
terms of the functions is given in `eq_rnDeriv`.
-/
theorem eq_withDensity_rnDeriv {s : Measure α} {f : α → ℝ≥0∞} (hf : Measurable f) (hs : s ⟂ₘ ν)
    (hadd : μ = s + ν.withDensity f) : ν.withDensity f = ν.withDensity (μ.rnDeriv ν) := by
  have : HaveLebesgueDecomposition μ ν := ⟨⟨⟨s, f⟩, hf, hs, hadd⟩⟩
  obtain ⟨hmeas, hsing, hadd'⟩ := haveLebesgueDecomposition_spec μ ν
  obtain ⟨⟨S, hS₁, hS₂, hS₃⟩, ⟨T, hT₁, hT₂, hT₃⟩⟩ := hs, hsing
  rw [hadd'] at hadd
  have hνinter : ν (S ∩ T)ᶜ = 0 := by
    rw [compl_inter]
    refine nonpos_iff_eq_zero.1 (le_trans (measure_union_le _ _) ?_)
    rw [hT₃, hS₃, add_zero]
  have heq :
    (ν.withDensity f).restrict (S ∩ T) = (ν.withDensity (μ.rnDeriv ν)).restrict (S ∩ T) := by
    ext1 A hA
    have hs : s (A ∩ (S ∩ T)) = 0 := by
      rw [← nonpos_iff_eq_zero]
      exact hS₂ ▸ measure_mono (inter_subset_right.trans inter_subset_left)
    have hsing : μ.singularPart ν (A ∩ (S ∩ T)) = 0 := by
      rw [← nonpos_iff_eq_zero]
      exact hT₂ ▸ measure_mono (inter_subset_right.trans inter_subset_right)
    rw [restrict_apply hA, restrict_apply hA, ← add_zero (ν.withDensity f (A ∩ (S ∩ T))), ← hs, ←
      add_apply, add_comm, ← hadd, add_apply, hsing, zero_add]
  have heq' :
    ∀ A : Set α, MeasurableSet A → ν.withDensity f A = (ν.withDensity f).restrict (S ∩ T) A := by
    intro A hA
    have hνfinter : ν.withDensity f (A ∩ (S ∩ T)ᶜ) = 0 := by
      rw [← nonpos_iff_eq_zero]
      exact withDensity_absolutelyContinuous ν f hνinter ▸ measure_mono inter_subset_right
    rw [restrict_apply hA, ← add_zero (ν.withDensity f (A ∩ (S ∩ T))), ← hνfinter, ← sdiff_eq,
      measure_inter_add_sdiff _ (hS₁.inter hT₁)]
  ext1 A hA
  have hνrn : ν.withDensity (μ.rnDeriv ν) (A ∩ (S ∩ T)ᶜ) = 0 := by
    rw [← nonpos_iff_eq_zero]
    exact
      withDensity_absolutelyContinuous ν (μ.rnDeriv ν) hνinter ▸
        measure_mono inter_subset_right
  rw [heq' A hA, heq, ← add_zero ((ν.withDensity (μ.rnDeriv ν)).restrict (S ∩ T) A), ← hνrn,
    restrict_apply hA, ← sdiff_eq, measure_inter_add_sdiff _ (hS₁.inter hT₁)]
/-
**MeasureTheory.Measure.eq_withDensity_rnDeriv** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.Measure`。
形式化陈述：eq_withDensity_rnDeriv {s : Measure α} {f : α -> Real>=0∞} (hf : Measurabl
e f) (hs : s ⟂ₘ ν) (hadd : μ = s + ν.withDensity f) : ν.withDensity f = ν.withDe
nsity (μ.rnDeriv ν)
参数：hf : Measurable f；hs : s ⟂ₘ ν；hadd : μ = s + ν.withDensity f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_spec`：haveLebesgueDecomp
osition_spec (μ ν : Measure α) [h : HaveLebesgueDecomposition μ ν] : Measurable 
(μ.rnDeriv ν) ∧ μ.singularPart ν ⟂ₘ ν ∧ μ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_inter`：compl_inter (s t : Set α) : (s inter t)ᶜ = sᶜ union tᶜ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `MeasureTheory.measure_union_le`：measure_union_le (s t : Set α) : μ (s un
ion t) <= μ s + μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasureTheory.Measure.add_apply`：add_apply {_m : MeasurableSpace α} (μ₁ 
μ₂ : Measure α) (s : Set α) : (μ₁ + μ₂) s = μ₁ s + μ₂ s
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `MeasureTheory.withDensity_absolutelyContinuous`：withDensity_absolutelyCo
ntinuous {m : MeasurableSpace α} (μ : Measure α) (f : α -> Real>=0∞) : μ.withDen
sity f ≪ μ
· 使用定理 `Set.sdiff_eq`：sdiff_eq (s t : Set α) : s \ t = s inter tᶜ
· 使用定理 `MeasureTheory.measure_inter_add_sdiff`：measure_inter_add_sdiff (s : Set 
α) (ht : MeasurableSet t) : μ (s inter t) + μ (s \ t) = μ s
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
-/
theorem eq_withDensity_rnDeriv₀ {s : Measure α} {f : α → ℝ≥0∞}
    (hf : AEMeasurable f ν) (hs : s ⟂ₘ ν) (hadd : μ = s + ν.withDensity f) :
    ν.withDensity f = ν.withDensity (μ.rnDeriv ν) := by
  rw [withDensity_congr_ae hf.ae_eq_mk] at hadd ⊢
  exact eq_withDensity_rnDeriv hf.measurable_mk hs hadd
/-
**MeasureTheory.Measure.eq_rnDeriv** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Meas
ure`。
形式化陈述：eq_rnDeriv [SigmaFinite ν] {s : Measure α} {f : α -> Real>=0∞} (hf : Measu
rable f) (hs : s ⟂ₘ ν) (hadd : μ = s + ν.withDensity f) : f =ᵐ[ν] μ.rnDeriv ν
参数：hf : Measurable f；hs : s ⟂ₘ ν；hadd : μ = s + ν.withDensity f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.eq_rnDeriv₀`：eq_rnDeriv₀ [SigmaFinite ν] {s : Meas
ure α} {f : α -> Real>=0∞} (hf : AEMeasurable f ν) (hs : s ⟂ₘ ν) (hadd : μ = s +
 ν.withDensity f) : f =…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
-/
theorem eq_rnDeriv₀ [SigmaFinite ν] {s : Measure α} {f : α → ℝ≥0∞}
    (hf : AEMeasurable f ν) (hs : s ⟂ₘ ν) (hadd : μ = s + ν.withDensity f) :
    f =ᵐ[ν] μ.rnDeriv ν :=
  (withDensity_eq_iff_of_sigmaFinite hf (measurable_rnDeriv _ _).aemeasurable).mp
    (eq_withDensity_rnDeriv₀ hf hs hadd)

/-- Given measures `μ` and `ν`, if `s` is a measure mutually singular to `ν` and `f` is a
measurable function such that `μ = s + fν`, then `f = μ.rnDeriv ν`.

This theorem provides the uniqueness of the `rnDeriv` in the Lebesgue decomposition
theorem, while `MeasureTheory.Measure.eq_singularPart` provides the uniqueness of the
`singularPart`. Here, the uniqueness is given in terms of the functions, while the uniqueness in
terms of the functions is given in `eq_withDensity_rnDeriv`. -/
/-
**MeasureTheory.Measure.eq_rnDeriv** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Meas
ure`。
形式化陈述：eq_rnDeriv [SigmaFinite ν] {s : Measure α} {f : α -> Real>=0∞} (hf : Measu
rable f) (hs : s ⟂ₘ ν) (hadd : μ = s + ν.withDensity f) : f =ᵐ[ν] μ.rnDeriv ν
参数：hf : Measurable f；hs : s ⟂ₘ ν；hadd : μ = s + ν.withDensity f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.eq_rnDeriv₀`：eq_rnDeriv₀ [SigmaFinite ν] {s : Meas
ure α} {f : α -> Real>=0∞} (hf : AEMeasurable f ν) (hs : s ⟂ₘ ν) (hadd : μ = s +
 ν.withDensity f) : f =…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ

--- 原说明 ---
Given measures `μ` and `ν`, if `s` is a measure mutually singular to `ν` and `f`
 is a
measurable function such that `μ = s + fν`, then `f = μ.rnDeriv ν`.

This theorem provides the uniqueness of the `rnDeriv` in the Lebesgue decomposit
ion
theorem, while `MeasureTheory.Measure.eq_singularPart` provides the uniqueness o
f the
`singularPart`. Here, the uniqueness is given in terms of the functions, while t
he uniqueness in
terms of the functions is given in `eq_withDensity_rnDeriv`.
-/
theorem eq_rnDeriv [SigmaFinite ν] {s : Measure α} {f : α → ℝ≥0∞} (hf : Measurable f) (hs : s ⟂ₘ ν)
    (hadd : μ = s + ν.withDensity f) : f =ᵐ[ν] μ.rnDeriv ν :=
  eq_rnDeriv₀ hf.aemeasurable hs hadd

/-- The Radon-Nikodym derivative of `f ν` with respect to `ν` is `f`. -/
/-
**MeasureTheory.Measure.rnDeriv_withDensity** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Measure`。
形式化陈述：rnDeriv_withDensity (ν : Measure α) [SigmaFinite ν] {f : α -> Real>=0∞} (h
f : Measurable f) : (ν.withDensity f).rnDeriv ν =ᵐ[ν] f
参数：ν : Measure α；hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.rnDeriv_withDensity₀`：rnDeriv_withDensity₀ (ν : Me
asure α) [SigmaFinite ν] {f : α -> Real>=0∞} (hf : AEMeasurable f ν) : (ν.withDe
nsity f).rnDeriv ν =ᵐ[ν] f
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ

--- 原说明 ---
The Radon-Nikodym derivative of `f ν` with respect to `ν` is `f`.
-/
theorem rnDeriv_withDensity₀ (ν : Measure α) [SigmaFinite ν] {f : α → ℝ≥0∞}
    (hf : AEMeasurable f ν) :
    (ν.withDensity f).rnDeriv ν =ᵐ[ν] f :=
  have : ν.withDensity f = 0 + ν.withDensity f := by rw [zero_add]
  (eq_rnDeriv₀ hf MutuallySingular.zero_left this).symm

/-- The Radon-Nikodym derivative of `f ν` with respect to `ν` is `f`. -/
/-
**MeasureTheory.Measure.rnDeriv_withDensity** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Measure`。
形式化陈述：rnDeriv_withDensity (ν : Measure α) [SigmaFinite ν] {f : α -> Real>=0∞} (h
f : Measurable f) : (ν.withDensity f).rnDeriv ν =ᵐ[ν] f
参数：ν : Measure α；hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.rnDeriv_withDensity₀`：rnDeriv_withDensity₀ (ν : Me
asure α) [SigmaFinite ν] {f : α -> Real>=0∞} (hf : AEMeasurable f ν) : (ν.withDe
nsity f).rnDeriv ν =ᵐ[ν] f
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ

--- 原说明 ---
The Radon-Nikodym derivative of `f ν` with respect to `ν` is `f`.
-/
theorem rnDeriv_withDensity (ν : Measure α) [SigmaFinite ν] {f : α → ℝ≥0∞} (hf : Measurable f) :
    (ν.withDensity f).rnDeriv ν =ᵐ[ν] f :=
  rnDeriv_withDensity₀ ν hf.aemeasurable
/-
**MeasureTheory.Measure.rnDeriv_restrict** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheor
y.Measure`。
形式化陈述：rnDeriv_restrict (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] [SigmaF
inite ν] {s : Set α} (hs : MeasurableSet s) : (μ.restrict s).rnDeriv ν =ᵐ[ν] s.i
ndicator (μ.rnDeriv ν)
参数：μ ν : Measure α；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.eq_rnDeriv`：eq_rnDeriv [SigmaFinite ν] {s : Measur
e α} {f : α -> Real>=0∞} (hf : Measurable f) (hs : s ⟂ₘ ν) (hadd : μ = s + ν.wit
hDensity f) : f =ᵐ[ν] …
· 使用定理 `Measurable.indicator`：Measurable.indicator [Zero β] (hf : Measurable f) 
(hs : MeasurableSet s) : Measurable (s.indicator f)
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用定理 `MeasureTheory.Measure.mutuallySingular_singularPart`：mutuallySingular_si
ngularPart (μ ν : Measure α) : μ.singularPart ν ⟂ₘ ν
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.singularPart_restrict`：singularPart_restrict (μ ν 
: Measure α) [HaveLebesgueDecomposition μ ν] {s : Set α} (hs : MeasurableSet s) 
: (μ.restrict s).singularPart ν =…
· 使用定理 `MeasureTheory.withDensity_indicator`：withDensity_indicator {s : Set α} (
hs : MeasurableSet s) (f : α -> Real>=0∞) : μ.withDensity (s.indicator f) = (μ.r
estrict s).withDensity f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.restrict_withDensity`：restrict_withDensity {s : Set α} (hs
 : MeasurableSet s) (f : α -> Real>=0∞) : (μ.withDensity f).restrict s = (μ.rest
rict s).withDensity f
· 使用定理 `MeasureTheory.Measure.restrict_add`：restrict_add {_m0 : MeasurableSpace 
α} (μ ν : Measure α) (s : Set α) : (μ + ν).restrict s = μ.restrict s + ν.restric
t s
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_add`：haveLebesgueDecompo
sition_add (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] : μ = μ.singularPar
t ν + ν.withDensity (μ.rnDeriv ν)
-/
lemma rnDeriv_restrict (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] [SigmaFinite ν]
    {s : Set α} (hs : MeasurableSet s) :
    (μ.restrict s).rnDeriv ν =ᵐ[ν] s.indicator (μ.rnDeriv ν) := by
  refine (eq_rnDeriv (s := (μ.restrict s).singularPart ν)
    ((measurable_rnDeriv _ _).indicator hs) (mutuallySingular_singularPart _ _) ?_).symm
  rw [singularPart_restrict _ _ hs, withDensity_indicator hs, ← restrict_withDensity hs,
    ← Measure.restrict_add, ← μ.haveLebesgueDecomposition_add ν]

/-- The Radon-Nikodym derivative of the restriction of a measure to a measurable set is the
indicator function of this set. -/
/-
**MeasureTheory.Measure.rnDeriv_restrict_self** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Measure`。
形式化陈述：rnDeriv_restrict_self (ν : Measure α) [SigmaFinite ν] {s : Set α} (hs : Me
asurableSet s) : (ν.restrict s).rnDeriv ν =ᵐ[ν] s.indicator 1
参数：ν : Measure α；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.withDensity_indicator_one`：withDensity_indicator_one {s : 
Set α} (hs : MeasurableSet s) : μ.withDensity (s.indicator 1) = μ.restrict s
· 使用定理 `MeasureTheory.Measure.rnDeriv_withDensity`：rnDeriv_withDensity (ν : Meas
ure α) [SigmaFinite ν] {f : α -> Real>=0∞} (hf : Measurable f) : (ν.withDensity 
f).rnDeriv ν =ᵐ[ν] f
· 使用定理 `Measurable.indicator`：Measurable.indicator [Zero β] (hf : Measurable f) 
(hs : MeasurableSet s) : Measurable (s.indicator f)
· 使用定理 `measurable_one`：measurable_one [One α] : Measurable (1 : β -> α)

--- 原说明 ---
The Radon-Nikodym derivative of the restriction of a measure to a measurable set
 is the
indicator function of this set.
-/
theorem rnDeriv_restrict_self (ν : Measure α) [SigmaFinite ν] {s : Set α} (hs : MeasurableSet s) :
    (ν.restrict s).rnDeriv ν =ᵐ[ν] s.indicator 1 := by
  rw [← withDensity_indicator_one hs]
  exact rnDeriv_withDensity _ (measurable_one.indicator hs)

/-- Radon-Nikodym derivative of the scalar multiple of a measure.
See also `rnDeriv_smul_left'`, which requires sigma-finite `ν` and `μ`. -/
/-
**MeasureTheory.Measure.rnDeriv_smul_left** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：rnDeriv_smul_left (ν μ : Measure α) [IsFiniteMeasure ν] [ν.HaveLebesgueDec
omposition μ] (r : Real>=0) : (r • ν).rnDeriv μ =ᵐ[μ] r • ν.rnDeriv μ
参数：ν μ : Measure α；r : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.withDensity_eq_iff`：withDensity_eq_iff {f g : α -> Real>=0
∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (hfi : ∫⁻ x, f x ∂μ != ∞) : μ
.withDensity f = μ.wit…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用引理 `AEMeasurable.const_smul`：AEMeasurable.const_smul (hg : AEMeasurable g μ)
 (c : M) : AEMeasurable (c • g) μ
· 使用定理 `MeasurableSMul.toMeasurableConstSMul`：∀ {M : Type u_2} {α : Type u_3} {i
nst : SMul M α} {inst_1 : MeasurableSpace M} {inst_2 : MeasurableSpace α}   [sel
f : MeasurableSMul M α], M…
· 使用定理 `ENNReal.instMeasurableSMulNNReal`：MeasurableSMul NNReal ENNReal
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.Measure.lintegral_rnDeriv_lt_top`：lintegral_rnDeriv_lt_top
 (μ ν : Measure α) [IsFiniteMeasure μ] : ∫⁻ x, μ.rnDeriv ν x ∂ν < ∞
· 使用定理 `MeasureTheory.withDensity_smul`：withDensity_smul (r : Real>=0∞) {f : α -
> Real>=0∞} (hf : Measurable f) : μ.withDensity (r • f) = r • μ.withDensity f
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_add`：haveLebesgueDecompo
sition_add (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] : μ = μ.singularPar
t ν + ν.withDensity (μ.rnDeriv ν)
· 使用定理 `MeasureTheory.Measure.singularPart_smul`：singularPart_smul (μ ν : Measur
e α) (r : Real>=0) : (r • μ).singularPart ν = r • μ.singularPart ν
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `MeasureTheory.Measure.add_right_inj`：∀ {α : Type u_1} {m0 : MeasurableSp
ace α} (μ ν₁ ν₂ : MeasureTheory.Measure α) [MeasureTheory.SigmaFinite μ],   μ + 
ν₁ = μ + ν₂ ↔ ν₁ = ν₂
· 使用定理 `MeasureTheory.Measure.singularPart.instSigmaFinite`：∀ {α : Type u_1} {m 
: MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite 
μ],   MeasureTheory.SigmaFinite (μ.singu…
· 使用定理 `MeasureTheory.SMul.sigmaFinite`：∀ {α : Type u_1} {m0 : MeasurableSpace α
} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ] (c : NNReal),   Me
asureTheory.SigmaFin…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ

--- 原说明 ---
Radon-Nikodym derivative of the scalar multiple of a measure.
See also `rnDeriv_smul_left'`, which requires sigma-finite `ν` and `μ`.
-/
theorem rnDeriv_smul_left (ν μ : Measure α) [IsFiniteMeasure ν]
    [ν.HaveLebesgueDecomposition μ] (r : ℝ≥0) :
    (r • ν).rnDeriv μ =ᵐ[μ] r • ν.rnDeriv μ := by
  rw [← withDensity_eq_iff]
  · simp_rw [ENNReal.smul_def]
    rw [withDensity_smul _ (measurable_rnDeriv _ _)]
    suffices (r • ν).singularPart μ + withDensity μ (rnDeriv (r • ν) μ)
        = (r • ν).singularPart μ + r • withDensity μ (rnDeriv ν μ) by
      rwa [Measure.add_right_inj] at this
    rw [← (r • ν).haveLebesgueDecomposition_add μ, singularPart_smul, ← smul_add,
      ← ν.haveLebesgueDecomposition_add μ]
  · exact (measurable_rnDeriv _ _).aemeasurable
  · exact (measurable_rnDeriv _ _).aemeasurable.const_smul _
  · exact (lintegral_rnDeriv_lt_top (r • ν) μ).ne

/-- Radon-Nikodym derivative of the scalar multiple of a measure.
See also `rnDeriv_smul_left_of_ne_top'`, which requires sigma-finite `ν` and `μ`. -/
/-
**MeasureTheory.Measure.rnDeriv_smul_left_of_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.Measure`。
形式化陈述：rnDeriv_smul_left_of_ne_top (ν μ : Measure α) [IsFiniteMeasure ν] [ν.HaveL
ebesgueDecomposition μ] {r : Real>=0∞} (hr : r != ∞) : (r • ν).rnDeriv μ =ᵐ[μ] r
 • ν.rnDeriv μ
参数：ν μ : Measure α；hr : r != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.rnDeriv_smul_left`：rnDeriv_smul_left (ν μ : Measur
e α) [IsFiniteMeasure ν] [ν.HaveLebesgueDecomposition μ] (r : Real>=0) : (r • ν)
.rnDeriv μ =ᵐ[μ] r • ν.rnDeri…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.coe_toNNReal`：∀ {a : ENNReal}, a ≠ ⊤ → ↑a.toNNReal = a

--- 原说明 ---
Radon-Nikodym derivative of the scalar multiple of a measure.
See also `rnDeriv_smul_left_of_ne_top'`, which requires sigma-finite `ν` and `μ`
.
-/
theorem rnDeriv_smul_left_of_ne_top (ν μ : Measure α) [IsFiniteMeasure ν]
    [ν.HaveLebesgueDecomposition μ] {r : ℝ≥0∞} (hr : r ≠ ∞) :
    (r • ν).rnDeriv μ =ᵐ[μ] r • ν.rnDeriv μ := by
  have h : (r.toNNReal • ν).rnDeriv μ =ᵐ[μ] r.toNNReal • ν.rnDeriv μ :=
    rnDeriv_smul_left ν μ r.toNNReal
  simpa [ENNReal.smul_def, ENNReal.coe_toNNReal hr] using h

/-- Radon-Nikodym derivative with respect to the scalar multiple of a measure.
See also `rnDeriv_smul_right'`, which requires sigma-finite `ν` and `μ`. -/
/-
**MeasureTheory.Measure.rnDeriv_smul_right** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Measure`。
形式化陈述：rnDeriv_smul_right (ν μ : Measure α) [IsFiniteMeasure ν] [ν.HaveLebesgueDe
composition μ] {r : Real>=0} (hr : r != 0) : ν.rnDeriv (r • μ) =ᵐ[μ] r⁻¹ • ν.rnD
eriv μ
参数：ν μ : Measure α；hr : r != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.ae_le`：∀ {α : Type u_1} {mα :
 MeasurableSpace α} {μ ν : MeasureTheory.Measure α},   μ.AbsolutelyContinuous ν 
→ MeasureTheory.ae μ ≤ MeasureTheory.a…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `MeasureTheory.Measure.absolutelyContinuous_smul`：absolutelyContinuous_sm
ul {c : Real>=0∞} (hc : c != 0) : μ ≪ c • μ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_ne_zero`：coe_ne_zero : (r : Real>=0∞) != 0 ↔ r != 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.withDensity_eq_iff`：withDensity_eq_iff {f g : α -> Real>=0
∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (hfi : ∫⁻ x, f x ∂μ != ∞) : μ
.withDensity f = μ.wit…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用引理 `AEMeasurable.const_smul`：AEMeasurable.const_smul (hg : AEMeasurable g μ)
 (c : M) : AEMeasurable (c • g) μ
· 使用定理 `MeasurableSMul.toMeasurableConstSMul`：∀ {M : Type u_2} {α : Type u_3} {i
nst : SMul M α} {inst_1 : MeasurableSpace M} {inst_2 : MeasurableSpace α}   [sel
f : MeasurableSMul M α], M…
· 使用定理 `ENNReal.instMeasurableSMulNNReal`：MeasurableSMul NNReal ENNReal
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.Measure.lintegral_rnDeriv_lt_top`：lintegral_rnDeriv_lt_top
 (μ ν : Measure α) [IsFiniteMeasure μ] : ∫⁻ x, μ.rnDeriv ν x ∂ν < ∞
· 使用定理 `MeasureTheory.withDensity_smul`：withDensity_smul (r : Real>=0∞) {f : α -
> Real>=0∞} (hf : Measurable f) : μ.withDensity (r • f) = r • μ.withDensity f
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_add`：haveLebesgueDecompo
sition_add (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] : μ = μ.singularPar
t ν + ν.withDensity (μ.rnDeriv ν)
· 使用定理 `MeasureTheory.Measure.singularPart_smul_right`：singularPart_smul_right (
μ ν : Measure α) (r : Real>=0) (hr : r != 0) : μ.singularPart (r • ν) = μ.singul
arPart ν
· 使用定理 `ENNReal.smul_def`：smul_def {M : Type*} [MulAction Real>=0∞ M] (c : Real>
=0) (x : M) : c • x = (c : Real>=0∞) • x
· 使用定理 `MeasureTheory.withDensity_smul_measure`：withDensity_smul_measure (r : Re
al>=0∞) (f : α -> Real>=0∞) : (r • μ).withDensity f = r • μ.withDensity f
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `MeasureTheory.Measure.add_right_inj`：∀ {α : Type u_1} {m0 : MeasurableSp
ace α} (μ ν₁ ν₂ : MeasureTheory.Measure α) [MeasureTheory.SigmaFinite μ],   μ + 
ν₁ = μ + ν₂ ↔ ν₁ = ν₂
· 使用定理 `MeasureTheory.Measure.singularPart.instSigmaFinite`：∀ {α : Type u_1} {m 
: MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite 
μ],   MeasureTheory.SigmaFinite (μ.singu…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ

--- 原说明 ---
Radon-Nikodym derivative with respect to the scalar multiple of a measure.
See also `rnDeriv_smul_right'`, which requires sigma-finite `ν` and `μ`.
-/
theorem rnDeriv_smul_right (ν μ : Measure α) [IsFiniteMeasure ν]
    [ν.HaveLebesgueDecomposition μ] {r : ℝ≥0} (hr : r ≠ 0) :
    ν.rnDeriv (r • μ) =ᵐ[μ] r⁻¹ • ν.rnDeriv μ := by
  refine (absolutelyContinuous_smul <| ENNReal.coe_ne_zero.2 hr).ae_le
    (?_ : ν.rnDeriv (r • μ) =ᵐ[r • μ] r⁻¹ • ν.rnDeriv μ)
  rw [← withDensity_eq_iff]
  rotate_left
  · exact (measurable_rnDeriv _ _).aemeasurable
  · exact (measurable_rnDeriv _ _).aemeasurable.const_smul _
  · exact (lintegral_rnDeriv_lt_top ν _).ne
  · simp_rw [ENNReal.smul_def]
    rw [withDensity_smul _ (measurable_rnDeriv _ _)]
    suffices ν.singularPart (r • μ) + withDensity (r • μ) (rnDeriv ν (r • μ))
        = ν.singularPart (r • μ) + r⁻¹ • withDensity (r • μ) (rnDeriv ν μ) by
      rwa [add_right_inj] at this
    rw [← ν.haveLebesgueDecomposition_add (r • μ), singularPart_smul_right _ _ _ hr,
      ENNReal.smul_def r, withDensity_smul_measure, ← ENNReal.smul_def, ← smul_assoc,
      smul_eq_mul, inv_mul_cancel₀ hr, one_smul]
    exact ν.haveLebesgueDecomposition_add μ

/-- Radon-Nikodym derivative with respect to the scalar multiple of a measure.
See also `rnDeriv_smul_right_of_ne_top'`, which requires sigma-finite `ν` and `μ`. -/
/-
**MeasureTheory.Measure.rnDeriv_smul_right_of_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.Measure`。
形式化陈述：rnDeriv_smul_right_of_ne_top (ν μ : Measure α) [IsFiniteMeasure ν] [ν.Have
LebesgueDecomposition μ] {r : Real>=0∞} (hr : r != 0) (hr_ne_top : r != ∞) : ν.r
nDeriv (r • μ) =ᵐ[μ] r⁻¹ • ν.rnDeriv μ
参数：ν μ : Measure α；hr : r != 0；hr_ne_top : r != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.rnDeriv_smul_right`：rnDeriv_smul_right (ν μ : Meas
ure α) [IsFiniteMeasure ν] [ν.HaveLebesgueDecomposition μ] {r : Real>=0} (hr : r
 != 0) : ν.rnDeriv (r • μ) =ᵐ[…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `ENNReal.toNNReal_eq_zero_iff`：toNNReal_eq_zero_iff (x : Real>=0∞) : x.to
NNReal = 0 ↔ x = 0 ∨ x = ∞
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.coe_inv`：coe_inv (hr : r != 0) : (↑r⁻¹ : Real>=0∞) = (↑r)⁻¹
· 使用定理 `ENNReal.coe_toNNReal`：∀ {a : ENNReal}, a ≠ ⊤ → ↑a.toNNReal = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a

--- 原说明 ---
Radon-Nikodym derivative with respect to the scalar multiple of a measure.
See also `rnDeriv_smul_right_of_ne_top'`, which requires sigma-finite `ν` and `μ
`.
-/
theorem rnDeriv_smul_right_of_ne_top (ν μ : Measure α) [IsFiniteMeasure ν]
    [ν.HaveLebesgueDecomposition μ] {r : ℝ≥0∞} (hr : r ≠ 0) (hr_ne_top : r ≠ ∞) :
    ν.rnDeriv (r • μ) =ᵐ[μ] r⁻¹ • ν.rnDeriv μ := by
  have h : ν.rnDeriv (r.toNNReal • μ) =ᵐ[μ] r.toNNReal⁻¹ • ν.rnDeriv μ := by
    refine rnDeriv_smul_right ν μ ?_
    rw [ne_eq, ENNReal.toNNReal_eq_zero_iff]
    simp [hr, hr_ne_top]
  have : (r.toNNReal)⁻¹ • rnDeriv ν μ = r⁻¹ • rnDeriv ν μ := by
    ext x
    simp only [Pi.smul_apply, ENNReal.smul_def, smul_eq_mul]
    rw [ENNReal.coe_inv, ENNReal.coe_toNNReal hr_ne_top]
    rw [ne_eq, ENNReal.toNNReal_eq_zero_iff]
    simp [hr, hr_ne_top]
  simp_rw [this, ENNReal.smul_def, ENNReal.coe_toNNReal hr_ne_top] at h
  exact h
/-
**MeasureTheory.Measure.rnDeriv_smul_same** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：rnDeriv_smul_same (ν μ : Measure α) [IsFiniteMeasure ν] [ν.HaveLebesgueDec
omposition μ] {r : Real>=0} (hr : r != 0) : (r • ν).rnDeriv (r • μ) =ᵐ[μ] ν.rnDe
riv μ
参数：ν μ : Measure α；hr : r != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.rnDeriv_smul_right`：rnDeriv_smul_right (ν μ : Meas
ure α) [IsFiniteMeasure ν] [ν.HaveLebesgueDecomposition μ] {r : Real>=0} (hr : r
 != 0) : ν.rnDeriv (r • μ) =ᵐ[…
· 使用定理 `MeasureTheory.Measure.rnDeriv_smul_left`：rnDeriv_smul_left (ν μ : Measur
e α) [IsFiniteMeasure ν] [ν.HaveLebesgueDecomposition μ] (r : Real>=0) : (r • ν)
.rnDeriv μ =ᵐ[μ] r • ν.rnDeri…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rnDeriv_smul_same (ν μ : Measure α) [IsFiniteMeasure ν]
    [ν.HaveLebesgueDecomposition μ] {r : ℝ≥0} (hr : r ≠ 0) :
    (r • ν).rnDeriv (r • μ) =ᵐ[μ] ν.rnDeriv μ := by
  filter_upwards [rnDeriv_smul_left ν μ r, rnDeriv_smul_right (r • ν) μ hr] with x hx1 hx2
  simp [hx1, hx2, hr]

/-- Radon-Nikodym derivative of a sum of two measures.
See also `rnDeriv_add'`, which requires sigma-finite `ν₁`, `ν₂` and `μ`. -/
/-
**MeasureTheory.Measure.rnDeriv_add** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Mea
sure`。
形式化陈述：rnDeriv_add (ν₁ ν₂ μ : Measure α) [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂
] [ν₁.HaveLebesgueDecomposition μ] [ν₂.HaveLebesgueDecomposition μ] [(ν₁ + ν₂).H
aveLebesgueDecomposition μ] : (ν₁ + ν₂).rnDeriv μ =ᵐ[μ] ν₁.rnDeriv μ + ν₂.rnDeri
v μ
参数：ν₁ ν₂ μ : Measure α；ν₁ + ν₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.withDensity_eq_iff`：withDensity_eq_iff {f g : α -> Real>=0
∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (hfi : ∫⁻ x, f x ∂μ != ∞) : μ
.withDensity f = μ.wit…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用定理 `Measurable.add`：∀ {M : Type u_2} {α : Type u_3} [inst : MeasurableSpace 
M] [inst_1 : Add M] {m : MeasurableSpace α} {f g : α → M}   [MeasurableAdd₂ M], 
Meas…
· 使用定理 `ContinuousAdd.measurableMul₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Add γ] [Con…
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `ENNReal.instContinuousAdd`：ContinuousAdd ENNReal
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.Measure.lintegral_rnDeriv_lt_top`：lintegral_rnDeriv_lt_top
 (μ ν : Measure α) [IsFiniteMeasure μ] : ∫⁻ x, μ.rnDeriv ν x ∂ν < ∞
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_add`：haveLebesgueDecompo
sition_add (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] : μ = μ.singularPar
t ν + ν.withDensity (μ.rnDeriv ν)
· 使用定理 `MeasureTheory.Measure.singularPart_add`：singularPart_add (μ₁ μ₂ ν : Meas
ure α) [HaveLebesgueDecomposition μ₁ ν] [HaveLebesgueDecomposition μ₂ ν] : (μ₁ +
 μ₂).singularPart ν = μ₁.sin…
· 使用定理 `MeasureTheory.withDensity_add_left`：withDensity_add_left {f : α -> Real>
=0∞} (hf : Measurable f) (g : α -> Real>=0∞) : μ.withDensity (f + g) = μ.withDen
sity f + μ.withDensity g
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `MeasureTheory.Measure.add_right_inj`：∀ {α : Type u_1} {m0 : MeasurableSp
ace α} (μ ν₁ ν₂ : MeasureTheory.Measure α) [MeasureTheory.SigmaFinite μ],   μ + 
ν₁ = μ + ν₂ ↔ ν₁ = ν₂
· 使用定理 `MeasureTheory.Measure.singularPart.instSigmaFinite`：∀ {α : Type u_1} {m 
: MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite 
μ],   MeasureTheory.SigmaFinite (μ.singu…
· 使用定理 `MeasureTheory.Add.sigmaFinite`：∀ {α : Type u_1} {m0 : MeasurableSpace α}
 (μ ν : MeasureTheory.Measure α) [MeasureTheory.SigmaFinite μ]   [MeasureTheory.
SigmaFinite ν], Mea…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ

--- 原说明 ---
Radon-Nikodym derivative of a sum of two measures.
See also `rnDeriv_add'`, which requires sigma-finite `ν₁`, `ν₂` and `μ`.
-/
lemma rnDeriv_add (ν₁ ν₂ μ : Measure α) [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
    [ν₁.HaveLebesgueDecomposition μ] [ν₂.HaveLebesgueDecomposition μ]
    [(ν₁ + ν₂).HaveLebesgueDecomposition μ] :
    (ν₁ + ν₂).rnDeriv μ =ᵐ[μ] ν₁.rnDeriv μ + ν₂.rnDeriv μ := by
  rw [← withDensity_eq_iff]
  · suffices (ν₁ + ν₂).singularPart μ + μ.withDensity ((ν₁ + ν₂).rnDeriv μ)
        = (ν₁ + ν₂).singularPart μ + μ.withDensity (ν₁.rnDeriv μ + ν₂.rnDeriv μ) by
      rwa [add_right_inj] at this
    rw [← (ν₁ + ν₂).haveLebesgueDecomposition_add μ, singularPart_add,
      withDensity_add_left (measurable_rnDeriv _ _), add_assoc,
      add_comm (ν₂.singularPart μ), add_assoc, add_comm _ (ν₂.singularPart μ),
      ← ν₂.haveLebesgueDecomposition_add μ, ← add_assoc, ← ν₁.haveLebesgueDecomposition_add μ]
  · exact (measurable_rnDeriv _ _).aemeasurable
  · exact ((measurable_rnDeriv _ _).add (measurable_rnDeriv _ _)).aemeasurable
  · exact (lintegral_rnDeriv_lt_top (ν₁ + ν₂) μ).ne

/-- If two finite measures `μ` and `ν` are not mutually singular, there exists some `ε > 0` and
a measurable set `E`, such that `ν(E) > 0` and `E` is positive with respect to `μ - εν`.

This lemma is useful for the Lebesgue decomposition theorem. -/
/-
**MeasureTheory.Measure.exists_positive_of_not_mutuallySingular** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：exists_positive_of_not_mutuallySingular (μ ν : Measure α) [IsFiniteMeasure
 μ] [IsFiniteMeasure ν] (h : ¬ μ ⟂ₘ ν) : exists ε : Real>=0, 0 < ε ∧ exists E : 
Set α, MeasurableSet E ∧ 0 < ν E ∧ forall A, MeasurableSet A -> ε * ν (A inter E
) <= μ (A inter E)
参数：μ ν : Measure α；h : ¬ μ ⟂ₘ ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.hahn_decomposition`：hahn_decomposition (μ ν : Measure α) [
IsFiniteMeasure μ] [IsFiniteMeasure ν] : exists s, MeasurableSet s ∧ (forall t, 
MeasurableSet t -> t s…
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `MeasurableSet.iInter`：MeasurableSet.iInter [Countable ι] {f : ι -> Set α
} (h : forall b, MeasurableSet (f b)) : MeasurableSet (⋂ b, f b)
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_eq_left`：∀ {α : Type u} {s t : Set α}, s ∩ t = s ↔ s ⊆ t
· 使用定理 `Set.iInter_subset`：iInter_subset : forall (s : ι -> Set β) (i : ι), ⋂ i,
 s i subseteq s i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `ENNReal.coe_inv`：coe_inv (hr : r != 0) : (↑r⁻¹ : Real>=0∞) = (↑r)⁻¹
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 85 条，此处仅展示前 30 条）

--- 原说明 ---
If two finite measures `μ` and `ν` are not mutually singular, there exists some 
`ε > 0` and
a measurable set `E`, such that `ν(E) > 0` and `E` is positive with respect to `
μ - εν`.

This lemma is useful for the Lebesgue decomposition theorem.
-/
theorem exists_positive_of_not_mutuallySingular (μ ν : Measure α) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (h : ¬ μ ⟂ₘ ν) :
    ∃ ε : ℝ≥0, 0 < ε ∧
      ∃ E : Set α, MeasurableSet E ∧ 0 < ν E
        ∧ ∀ A, MeasurableSet A → ε * ν (A ∩ E) ≤ μ (A ∩ E) := by
  -- for all `n : ℕ`, obtain the Hahn decomposition for `μ - (1 / n) ν`
  have h_decomp (n : ℕ) : ∃ s : Set α, MeasurableSet s
        ∧ (∀ t, MeasurableSet t → ((1 / (n + 1) : ℝ≥0) • ν) (t ∩ s) ≤ μ (t ∩ s))
        ∧ (∀ t, MeasurableSet t → μ (t ∩ sᶜ) ≤ ((1 / (n + 1) : ℝ≥0) • ν) (t ∩ sᶜ)) := by
    obtain ⟨s, hs, hs_le, hs_ge⟩ := hahn_decomposition μ ((1 / (n + 1) : ℝ≥0) • ν)
    refine ⟨s, hs, fun t ht ↦ ?_, fun t ht ↦ ?_⟩
    · exact hs_le (t ∩ s) (ht.inter hs) inter_subset_right
    · exact hs_ge (t ∩ sᶜ) (ht.inter hs.compl) inter_subset_right
  choose f hf₁ hf₂ hf₃ using h_decomp
  -- set `A` to be the intersection of all the negative parts of obtained Hahn decompositions
  -- and we show that `μ A = 0`
  let A := ⋂ n, (f n)ᶜ
  have hAmeas : MeasurableSet A := MeasurableSet.iInter fun n ↦ (hf₁ n).compl
  have hA₂ (n : ℕ) (t : Set α) (ht : MeasurableSet t) :
      μ (t ∩ A) ≤ ((1 / (n + 1) : ℝ≥0) • ν) (t ∩ A) := by
    specialize hf₃ n (t ∩ A) (ht.inter hAmeas)
    have : A ∩ (f n)ᶜ = A := inter_eq_left.mpr (iInter_subset _ n)
    rwa [inter_assoc, this] at hf₃
  have hA₃ (n : ℕ) : μ A ≤ (1 / (n + 1) : ℝ≥0) * ν A := by simpa using hA₂ n univ .univ
  have hμ : μ A = 0 := by
    lift μ A to ℝ≥0 using measure_ne_top _ _ with μA
    lift ν A to ℝ≥0 using measure_ne_top _ _ with νA
    rw [ENNReal.coe_eq_zero]
    by_cases! hb : 0 < νA
    · suffices ∀ b, 0 < b → μA ≤ b by
        by_contra h
        have h' := this (μA / 2) (half_pos (zero_lt_iff.2 h))
        rw [← @Classical.not_not (μA ≤ μA / 2)] at h'
        exact h' (not_le.2 (NNReal.half_lt_self h))
      intro c hc
      have : ∃ n : ℕ, 1 / (n + 1 : ℝ) < c * (νA : ℝ)⁻¹ := by
        refine exists_nat_one_div_lt ?_
        positivity
      rcases this with ⟨n, hn⟩
      have hb₁ : (0 : ℝ) < (νA : ℝ)⁻¹ := by rw [_root_.inv_pos]; exact hb
      have h' : 1 / (↑n + 1) * νA < c := by
        rw [← NNReal.coe_lt_coe, ← mul_lt_mul_iff_left₀ hb₁, NNReal.coe_mul, mul_assoc, ←
          NNReal.coe_inv, ← NNReal.coe_mul, mul_inv_cancel₀, ← NNReal.coe_mul, mul_one,
          NNReal.coe_inv]
        · exact hn
        · exact hb.ne'
      refine le_trans ?_ h'.le
      rw [← ENNReal.coe_le_coe, ENNReal.coe_mul]
      exact hA₃ n
    · rw [le_zero_iff] at hb
      simpa [hb] using hA₃ 0
  -- since `μ` and `ν` are not mutually singular, `μ A = 0` implies `ν Aᶜ > 0`
  rw [MutuallySingular] at h; push Not at h
  have := h _ hAmeas hμ
  simp_rw [A, compl_iInter, compl_compl] at this
  -- as `Aᶜ = ⋃ n, f n`, `ν Aᶜ > 0` implies there exists some `n` such that `ν (f n) > 0`
  obtain ⟨n, hn⟩ := exists_measure_pos_of_not_measure_iUnion_null this
  -- thus, choosing `f n` as the set `E` suffices
  exact ⟨1 / (n + 1), by simp, f n, hf₁ n, hn, hf₂ n⟩

namespace LebesgueDecomposition

/-- Given two measures `μ` and `ν`, `measurableLE μ ν` is the set of measurable
functions `f`, such that, for all measurable sets `A`, `∫⁻ x in A, f x ∂μ ≤ ν A`.

This is useful for the Lebesgue decomposition theorem. -/
/-
**MeasureTheory.Measure.LebesgueDecomposition.measurableLE** 是 Mathlib 中的一个定义，位于
命名空间 `MeasureTheory.Measure.LebesgueDecomposition`。
形式化陈述：measurableLE (μ ν : Measure α) : Set (α -> Real>=0∞)
参数：μ ν : Measure α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two measures `μ` and `ν`, `measurableLE μ ν` is the set of measurable
functions `f`, such that, for all measurable sets `A`, `∫⁻ x in A, f x ∂μ ≤ ν A`
.

This is useful for the Lebesgue decomposition theorem.
-/
def measurableLE (μ ν : Measure α) : Set (α → ℝ≥0∞) :=
  {f | Measurable f ∧ ∀ (A : Set α), MeasurableSet A → (∫⁻ x in A, f x ∂μ) ≤ ν A}
/-
**MeasureTheory.Measure.LebesgueDecomposition.zero_mem_measurableLE** 是 Mathlib 
中的一个定理，位于命名空间 `MeasureTheory.Measure.LebesgueDecomposition`。
形式化陈述：zero_mem_measurableLE : (0 : α -> Real>=0∞) in measurableLE μ ν
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace
 α] [inst_1 : MeasurableSpace β] [inst_2 : Zero α], Measurable 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
-/
theorem zero_mem_measurableLE : (0 : α → ℝ≥0∞) ∈ measurableLE μ ν :=
  ⟨measurable_zero, fun A _ ↦ by simp⟩
/-
**MeasureTheory.Measure.LebesgueDecomposition.sup_mem_measurableLE** 是 Mathlib 中
的一个定理，位于命名空间 `MeasureTheory.Measure.LebesgueDecomposition`。
形式化陈述：sup_mem_measurableLE {f g : α -> Real>=0∞} (hf : f in measurableLE μ ν) (h
g : g in measurableLE μ ν) : (fun a => f a ⊔ g a) in measurableLE μ ν
参数：hf : f in measurableLE μ ν；hg : g in measurableLE μ ν。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.max`：Measurable.max {f g : δ -> α} (hf : Measurable f) (hg : 
Measurable g) : Measurable fun a => max (f a) (g a)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `measurableSet_le`：measurableSet_le {f g : δ -> α} (hf : Measurable f) (h
g : Measurable g) : MeasurableSet { a | f a <= g a }
· 使用定理 `measurableSet_lt`：measurableSet_lt [SecondCountableTopology α] [OrderClo
sedTopology α] {f g : δ -> α} (hf : Measurable f) (hg : Measurable g) : Measurab
leSet …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setLIntegral_max`：setLIntegral_max {f g : α -> Real>=0∞} (
hf : Measurable f) (hg : Measurable g) (s : Set α) : ∫⁻ x in s, max (f x) (g x) 
∂μ = ∫⁻ x in s inter…
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sdiff_eq`：sdiff_eq (s t : Set α) : s \ t = s inter tᶜ
· 使用定理 `MeasureTheory.measure_inter_add_sdiff`：measure_inter_add_sdiff (s : Set 
α) (ht : MeasurableSet t) : μ (s inter t) + μ (s \ t) = μ s
-/
theorem sup_mem_measurableLE {f g : α → ℝ≥0∞} (hf : f ∈ measurableLE μ ν)
    (hg : g ∈ measurableLE μ ν) : (fun a ↦ f a ⊔ g a) ∈ measurableLE μ ν := by
  refine ⟨Measurable.max hf.1 hg.1, fun A hA ↦ ?_⟩
  have h₁ := hA.inter (measurableSet_le hf.1 hg.1)
  have h₂ := hA.inter (measurableSet_lt hg.1 hf.1)
  rw [setLIntegral_max hf.1 hg.1]
  refine (add_le_add (hg.2 _ h₁) (hf.2 _ h₂)).trans_eq ?_
  simp only [← not_le, ← compl_ofPred, ← sdiff_eq]
  exact measure_inter_add_sdiff _ (measurableSet_le hf.1 hg.1)
/-
**MeasureTheory.Measure.LebesgueDecomposition.iSup_succ_eq_sup** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory.Measure.LebesgueDecomposition`。
形式化陈述：iSup_succ_eq_sup {α} (f : Nat -> α -> Real>=0∞) (m : Nat) (a : α) : ⨆ (k :
 Nat) (_ : k <= m + 1), f k a = f m.succ a ⊔ ⨆ (k : Nat) (_ : k <= m), f k a
参数：f : Nat -> α -> Real>=0∞；m : Nat；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `le_antisymm_iff`：le_antisymm_iff : a = b ↔ a <= b ∧ b <= a
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `Nat.of_le_succ`：∀ {m n : ℕ}, m ≤ n.succ → m ≤ n ∨ m = n.succ
· 使用定理 `le_sup_of_le_right`：le_sup_of_le_right (h : c <= b) : c <= a ⊔ b
· 使用定理 `le_iSup₂`：le_iSup₂ {f : forall i, κ i -> α} (i : ι) (j : κ i) : f i j <=
 ⨆ (i) (j), f i j
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `biSup_mono`：biSup_mono {p q : ι -> Prop} (hpq : forall i, p i -> q i) : 
⨆ (i) (_ : p i), f i <= ⨆ (i) (_ : q i), f i
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
-/
theorem iSup_succ_eq_sup {α} (f : ℕ → α → ℝ≥0∞) (m : ℕ) (a : α) :
    ⨆ (k : ℕ) (_ : k ≤ m + 1), f k a = f m.succ a ⊔ ⨆ (k : ℕ) (_ : k ≤ m), f k a := by
  set c := ⨆ (k : ℕ) (_ : k ≤ m + 1), f k a with hc
  set d := f m.succ a ⊔ ⨆ (k : ℕ) (_ : k ≤ m), f k a with hd
  rw [le_antisymm_iff, hc, hd]
  constructor
  · refine iSup₂_le fun n hn ↦ ?_
    rcases Nat.of_le_succ hn with (h | h)
    · exact le_sup_of_le_right (le_iSup₂ (f := fun k (_ : k ≤ m) ↦ f k a) n h)
    · exact h ▸ le_sup_left
  · refine sup_le ?_ (biSup_mono fun n hn ↦ hn.trans m.le_succ)
    exact @le_iSup₂ ℝ≥0∞ ℕ (fun i ↦ i ≤ m + 1) _ _ (m + 1) le_rfl
/-
**MeasureTheory.Measure.LebesgueDecomposition.iSup_mem_measurableLE** 是 Mathlib 
中的一个定理，位于命名空间 `MeasureTheory.Measure.LebesgueDecomposition`。
形式化陈述：iSup_mem_measurableLE (f : Nat -> α -> Real>=0∞) (hf : forall n, f n in me
asurableLE μ ν) (n : Nat) : (fun x => ⨆ (k) (_ : k <= n), f k x) in measurableLE
 μ ν
参数：f : Nat -> α -> Real>=0∞；hf : forall n, f n in measurableLE μ ν；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `iSup_iSup_eq_left`：iSup_iSup_eq_left {b : β} {f : forall x : β, x = b ->
 α} : ⨆ x, ⨆ h : x = b, f x h = f b rfl
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.Measure.LebesgueDecomposition.iSup_succ_eq_sup`：iSup_succ_
eq_sup {α} (f : Nat -> α -> Real>=0∞) (m : Nat) (a : α) : ⨆ (k : Nat) (_ : k <= 
m + 1), f k a = f m.succ a ⊔ ⨆ (k : Nat) (_ : k <=…
· 使用定理 `Measurable.iSup`：∀ {α : Type u_1} {δ : Type u_4} [inst : TopologicalSpac
e α] {mα : MeasurableSpace α} [BorelSpace α]   {mδ : MeasurableSpace δ} [inst_2 
: Con…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Measurable.iSup_Prop`：Measurable.iSup_Prop {α} {mα : MeasurableSpace α} 
[ConditionallyCompleteLattice α] (p : Prop) {f : δ -> α} (hf : Measurable f) : M
easurable …
· 使用定理 `MeasureTheory.Measure.LebesgueDecomposition.sup_mem_measurableLE`：sup_me
m_measurableLE {f g : α -> Real>=0∞} (hf : f in measurableLE μ ν) (hg : g in mea
surableLE μ ν) : (fun a => f a ⊔ g a) in measurableLE …
-/
theorem iSup_mem_measurableLE (f : ℕ → α → ℝ≥0∞) (hf : ∀ n, f n ∈ measurableLE μ ν) (n : ℕ) :
    (fun x ↦ ⨆ (k) (_ : k ≤ n), f k x) ∈ measurableLE μ ν := by
  induction n with
  | zero =>
    constructor
    · simp [(hf 0).1]
    · intro A hA; simp [(hf 0).2 A hA]
  | succ m hm =>
    have :
      (fun a : α ↦ ⨆ (k : ℕ) (_ : k ≤ m + 1), f k a) = fun a ↦
        f m.succ a ⊔ ⨆ (k : ℕ) (_ : k ≤ m), f k a :=
      funext fun _ ↦ iSup_succ_eq_sup _ _ _
    refine ⟨.iSup fun n ↦ Measurable.iSup_Prop _ (hf n).1, fun A hA ↦ ?_⟩
    rw [this]; exact (sup_mem_measurableLE (hf m.succ) hm).2 A hA
/-
**MeasureTheory.Measure.LebesgueDecomposition.iSup_mem_measurableLE'** 是 Mathlib
 中的一个定理，位于命名空间 `MeasureTheory.Measure.LebesgueDecomposition`。
形式化陈述：iSup_mem_measurableLE' (f : Nat -> α -> Real>=0∞) (hf : forall n, f n in m
easurableLE μ ν) (n : Nat) : (⨆ (k) (_ : k <= n), f k) in measurableLE μ ν
参数：f : Nat -> α -> Real>=0∞；hf : forall n, f n in measurableLE μ ν；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_apply`：iSup_apply {α : Type*} {β : α -> Type*} {ι : Sort*} [forall 
i, SupSet (β i)] {f : ι -> forall a, β a} {a : α} : (⨆ i, f i) a = ⨆ i, f i a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.Measure.LebesgueDecomposition.iSup_mem_measurableLE`：iSup_
mem_measurableLE (f : Nat -> α -> Real>=0∞) (hf : forall n, f n in measurableLE 
μ ν) (n : Nat) : (fun x => ⨆ (k) (_ : k <= n), f k x) i…
-/
theorem iSup_mem_measurableLE' (f : ℕ → α → ℝ≥0∞) (hf : ∀ n, f n ∈ measurableLE μ ν) (n : ℕ) :
    (⨆ (k) (_ : k ≤ n), f k) ∈ measurableLE μ ν := by
  convert! iSup_mem_measurableLE f hf n
  simp

section SuprLemmas

--TODO: these statements should be moved elsewhere

/-
**MeasureTheory.Measure.LebesgueDecomposition.iSup_monotone** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.Measure.LebesgueDecomposition`。
形式化陈述：iSup_monotone {α : Type*} (f : Nat -> α -> Real>=0∞) : Monotone fun n x =>
 ⨆ (k) (_ : k <= n), f k x
参数：f : Nat -> α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `biSup_mono`：biSup_mono {p q : ι -> Prop} (hpq : forall i, p i -> q i) : 
⨆ (i) (_ : p i), f i <= ⨆ (i) (_ : q i), f i
· 使用引理 `ge_trans`：ge_trans : b <= a -> c <= b -> c <= a
-/
theorem iSup_monotone {α : Type*} (f : ℕ → α → ℝ≥0∞) :
    Monotone fun n x ↦ ⨆ (k) (_ : k ≤ n), f k x :=
  fun _ _ hnm _ ↦ biSup_mono fun _ ↦ ge_trans hnm
/-
**MeasureTheory.Measure.LebesgueDecomposition.iSup_monotone'** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory.Measure.LebesgueDecomposition`。
形式化陈述：iSup_monotone' {α : Type*} (f : Nat -> α -> Real>=0∞) (x : α) : Monotone f
un n => ⨆ (k) (_ : k <= n), f k x
参数：f : Nat -> α -> Real>=0∞；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.LebesgueDecomposition.iSup_monotone`：iSup_monotone
 {α : Type*} (f : Nat -> α -> Real>=0∞) : Monotone fun n x => ⨆ (k) (_ : k <= n)
, f k x
-/
theorem iSup_monotone' {α : Type*} (f : ℕ → α → ℝ≥0∞) (x : α) :
    Monotone fun n ↦ ⨆ (k) (_ : k ≤ n), f k x := fun _ _ hnm ↦ iSup_monotone f hnm x
/-
**MeasureTheory.Measure.LebesgueDecomposition.iSup_le_le** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.Measure.LebesgueDecomposition`。
形式化陈述：iSup_le_le {α : Type*} (f : Nat -> α -> Real>=0∞) (n k : Nat) (hk : k <= n
) : f k <= fun x => ⨆ (k) (_ : k <= n), f k x
参数：f : Nat -> α -> Real>=0∞；n k : Nat；hk : k <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iSup₂`：le_iSup₂ {f : forall i, κ i -> α} (i : ι) (j : κ i) : f i j <=
 ⨆ (i) (j), f i j
-/
theorem iSup_le_le {α : Type*} (f : ℕ → α → ℝ≥0∞) (n k : ℕ) (hk : k ≤ n) :
    f k ≤ fun x ↦ ⨆ (k) (_ : k ≤ n), f k x :=
  fun x ↦ le_iSup₂ (f := fun k (_ : k ≤ n) ↦ f k x) k hk

end SuprLemmas

/-- `measurableLEEval μ ν` is the set of `∫⁻ x, f x ∂μ` for all `f ∈ measurableLE μ ν`. -/
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/-
**MeasureTheory.Measure.LebesgueDecomposition.measurableLEEval** 是 Mathlib 中的一个定
义，位于命名空间 `MeasureTheory.Measure.LebesgueDecomposition`。
形式化陈述：measurableLEEval (μ ν : Measure α) : Set Real>=0∞
参数：μ ν : Measure α。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def measurableLEEval (μ ν : Measure α) : Set ℝ≥0∞ :=
  (fun f : α → ℝ≥0∞ ↦ ∫⁻ x, f x ∂μ) '' measurableLE μ ν

end LebesgueDecomposition

open LebesgueDecomposition

/-- Any pair of finite measures `μ` and `ν`, `HaveLebesgueDecomposition`. That is to say,
there exist a measure `ξ` and a measurable function `f`, such that `ξ` is mutually singular
with respect to `ν` and `μ = ξ + ν.withDensity f`.

This is not an instance since this is also shown for the more general σ-finite measures with
`MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`. -/
/-
**MeasureTheory.Measure.haveLebesgueDecomposition_of_finiteMeasure** 是 Mathlib 中
的一个定理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：haveLebesgueDecomposition_of_finiteMeasure [IsFiniteMeasure μ] [IsFiniteMe
asure ν] : HaveLebesgueDecomposition μ ν where lebesgue_decomposition
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_seq_tendsto_sSup`：exists_seq_tendsto_sSup {α : Type*} [Conditiona
llyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α] [FirstCountable
Topology α] {…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `ENNReal.instMetrizableSpace`：TopologicalSpace.MetrizableSpace ENNReal
· 使用定理 `MeasureTheory.Measure.LebesgueDecomposition.zero_mem_measurableLE`：zero_
mem_measurableLE : (0 : α -> Real>=0∞) in measurableLE μ ν
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `OrderTop.bddAbove`：∀ {α : Type u_1} [inst : Preorder α] [OrderTop α] (s 
: Set α), BddAbove s
· 使用定理 `MeasureTheory.lintegral_tendsto_of_tendsto_of_monotone`：lintegral_tendst
o_of_tendsto_of_monotone {f : Nat -> α -> Real>=0∞} {F : α -> Real>=0∞} (hf : fo
rall n, AEMeasurable (f n) μ) (h_mono : fora…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_apply`：iSup_apply {α : Type*} {β : α -> Type*} {ι : Sort*} [forall 
i, SupSet (β i)] {f : ι -> forall a, β a} {a : α} : (⨆ i, f i) a = ⨆ i, f i a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.Measure.LebesgueDecomposition.iSup_mem_measurableLE`：iSup_
mem_measurableLE (f : Nat -> α -> Real>=0∞) (hf : forall n, f n in measurableLE 
μ ν) (n : Nat) : (fun x => ⨆ (k) (_ : k <= n), f k x) i…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.Measure.LebesgueDecomposition.iSup_monotone'`：iSup_monoton
e' {α : Type*} (f : Nat -> α -> Real>=0∞) (x : α) : Monotone fun n => ⨆ (k) (_ :
 k <= n), f k x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `tendsto_atTop_iSup`：tendsto_atTop_iSup (h_mono : Monotone f) : Tendsto f
 atTop (𝓝 (⨆ i, f i))
· 使用定理 `LinearOrder.supConvergenceClass`：∀ {α : Type u_1} [inst : TopologicalSpa
ce α] [inst_1 : LinearOrder α] [OrderTopology α], SupConvergenceClass α
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
（共 96 条，此处仅展示前 30 条）

--- 原说明 ---
Any pair of finite measures `μ` and `ν`, `HaveLebesgueDecomposition`. That is to
 say,
there exist a measure `ξ` and a measurable function `f`, such that `ξ` is mutual
ly singular
with respect to `ν` and `μ = ξ + ν.withDensity f`.

This is not an instance since this is also shown for the more general σ-finite m
easures with
`MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`.
-/
theorem haveLebesgueDecomposition_of_finiteMeasure [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    HaveLebesgueDecomposition μ ν where
  lebesgue_decomposition := by
    have h := @exists_seq_tendsto_sSup _ _ _ _ _ (measurableLEEval ν μ)
      ⟨0, 0, zero_mem_measurableLE, by simp⟩ (OrderTop.bddAbove _)
    choose g _ hg₂ f hf₁ hf₂ using h
    -- we set `ξ` to be the supremum of an increasing sequence of functions obtained from above
    set ξ := ⨆ (n) (k) (_ : k ≤ n), f k with hξ
    -- we see that `ξ` has the largest integral among all functions in `measurableLE`
    have hξ₁ : sSup (measurableLEEval ν μ) = ∫⁻ a, ξ a ∂ν := by
      have := @lintegral_tendsto_of_tendsto_of_monotone _ _ ν (fun n ↦ ⨆ (k) (_ : k ≤ n), f k)
          (⨆ (n) (k) (_ : k ≤ n), f k) ?_ ?_ ?_
      · refine tendsto_nhds_unique ?_ this
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le hg₂ tendsto_const_nhds (fun n ↦ ?_)
          fun n ↦ ?_
        · rw [← hf₂ n]
          apply lintegral_mono
          convert! iSup_le_le f n n le_rfl
          simp only [iSup_apply]
        · exact le_sSup ⟨⨆ (k : ℕ) (_ : k ≤ n), f k, iSup_mem_measurableLE' _ hf₁ _, rfl⟩
      · intro n
        refine Measurable.aemeasurable ?_
        convert! (iSup_mem_measurableLE _ hf₁ n).1
        simp
      · refine Filter.Eventually.of_forall fun a ↦ ?_
        simp [iSup_monotone' f _]
      · refine Filter.Eventually.of_forall fun a ↦ ?_
        simp [tendsto_atTop_iSup (iSup_monotone' f a)]
    have hξm : Measurable ξ := by
      convert! Measurable.iSup fun n ↦ (iSup_mem_measurableLE _ hf₁ n).1
      simp [hξ]
    -- we see that `ξ` has the largest integral among all functions in `measurableLE`
    have hξle A (hA : MeasurableSet A) : ∫⁻ a in A, ξ a ∂ν ≤ μ A := by
        rw [hξ]
        simp_rw [iSup_apply]
        rw [lintegral_iSup (fun n ↦ (iSup_mem_measurableLE _ hf₁ n).1) (iSup_monotone _)]
        exact iSup_le fun n ↦ (iSup_mem_measurableLE _ hf₁ n).2 A hA
    have hle : ν.withDensity ξ ≤ μ := by
      refine le_intro fun B hB _ ↦ ?_
      rw [withDensity_apply _ hB]
      exact hξle B hB
    have : IsFiniteMeasure (ν.withDensity ξ) := isFiniteMeasure_of_le _ hle
    -- `ξ` is the `f` in the theorem statement and we set `μ₁` to be `μ - ν.withDensity ξ`
    -- since we need `μ₁ + ν.withDensity ξ = μ`
    set μ₁ := μ - ν.withDensity ξ with hμ₁
    refine ⟨⟨μ₁, ξ⟩, hξm, ?_, ?_⟩
    · by_contra h
      -- if they are not mutually singular, then from `exists_positive_of_not_mutuallySingular`,
      -- there exists some `ε > 0` and a measurable set `E`, such that `μ(E) > 0` and `E` is
      -- positive with respect to `ν - εμ`
      obtain ⟨ε, hε₁, E, hE₁, hE₂, hE₃⟩ := exists_positive_of_not_mutuallySingular μ₁ ν h
      simp_rw [hμ₁] at hE₃
      -- since `E` is positive, we have `∫⁻ a in A ∩ E, ε + ξ a ∂ν ≤ μ (A ∩ E)` for all `A`
      have hε₂ (A : Set α) (hA : MeasurableSet A) : ∫⁻ a in A ∩ E, ε + ξ a ∂ν ≤ μ (A ∩ E) := by
        specialize hE₃ A hA
        rw [lintegral_add_left measurable_const, lintegral_const, restrict_apply_univ]
        rw [Measure.sub_apply (hA.inter hE₁) hle, withDensity_apply _ (hA.inter hE₁)] at hE₃
        refine add_le_of_le_tsub_right_of_le (hξle _ (hA.inter hE₁)) hE₃
      -- from this, we can show `ξ + ε * E.indicator` is a function in `measurableLE` with
      -- integral greater than `ξ`
      have hξε : (ξ + E.indicator fun _ ↦ (ε : ℝ≥0∞)) ∈ measurableLE ν μ := by
        refine ⟨hξm.add (measurable_const.indicator hE₁), fun A hA ↦ ?_⟩
        have : ∫⁻ a in A, (ξ + E.indicator fun _ ↦ (ε : ℝ≥0∞)) a ∂ν =
            ∫⁻ a in A ∩ E, ε + ξ a ∂ν + ∫⁻ a in A \ E, ξ a ∂ν := by
          simp only [lintegral_add_left measurable_const, lintegral_add_left hξm,
            setLIntegral_const, add_assoc, lintegral_inter_add_sdiff _ _ hE₁, Pi.add_apply,
            lintegral_indicator hE₁, restrict_apply hE₁]
          rw [inter_comm, add_comm]
        rw [this, ← measure_inter_add_sdiff A hE₁]
        exact add_le_add (hε₂ A hA) (hξle (A \ E) (hA.diff hE₁))
      have : (∫⁻ a, ξ a + E.indicator (fun _ ↦ (ε : ℝ≥0∞)) a ∂ν) ≤ sSup (measurableLEEval ν μ) :=
        le_sSup ⟨ξ + E.indicator fun _ ↦ (ε : ℝ≥0∞), hξε, rfl⟩
      -- but this contradicts the maximality of `∫⁻ x, ξ x ∂ν`
      refine not_lt.2 this ?_
      rw [hξ₁, lintegral_add_left hξm, lintegral_indicator hE₁, setLIntegral_const]
      refine ENNReal.lt_add_right ?_ (ENNReal.mul_pos_iff.2 ⟨ENNReal.coe_pos.2 hε₁, hE₂⟩).ne'
      have := measure_ne_top (ν.withDensity ξ) univ
      rwa [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at this
    -- since `ν.withDensity ξ ≤ μ`, it is clear that `μ = μ₁ + ν.withDensity ξ`
    · rw [hμ₁]
      ext1 A hA
      rw [Measure.coe_add, Pi.add_apply, Measure.sub_apply hA hle, add_comm,
        add_tsub_cancel_of_le (hle A)]

/-- If any finite measure has a Lebesgue decomposition with respect to `ν`,
then the same is true for any s-finite measure. -/
/-
**MeasureTheory.Measure.HaveLebesgueDecomposition.sfinite_of_isFiniteMeasure** 是
 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure.HaveLebesgueDecomposition`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [
MeasureTheory.SFinite μ],   (∀ (μ : MeasureTheory.Measure α) [MeasureTheory.IsFi
niteMeasure μ], μ.HaveLebesgueDecomposition ν) →     μ.HaveLebesgueDecomposition
 ν
参数：∀ (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ], μ.HaveLebe
sgueDecomposition ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.HaveLebesgueDecomposition.sum_left`：∀ {α : Type u_
1} {m : MeasurableSpace α} {ν : MeasureTheory.Measure α} {ι : Type u_2} [Countab
le ι]   (μ : ι → MeasureTheory.Measure α) [∀ (…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用引理 `MeasureTheory.sum_sfiniteSeq`：sum_sfiniteSeq (μ : Measure α) [h : SFinit
e μ] : sum (sfiniteSeq μ) = μ

--- 原说明 ---
If any finite measure has a Lebesgue decomposition with respect to `ν`,
then the same is true for any s-finite measure.
-/
theorem HaveLebesgueDecomposition.sfinite_of_isFiniteMeasure [SFinite μ]
    (_h : ∀ (μ : Measure α) [IsFiniteMeasure μ], HaveLebesgueDecomposition μ ν) :
    HaveLebesgueDecomposition μ ν :=
  sum_sfiniteSeq μ ▸ sum_left _

attribute [local instance] haveLebesgueDecomposition_of_finiteMeasure

-- see Note [lower instance priority]
variable (μ ν) in
/-- **The Lebesgue decomposition theorem**:
Any s-finite measure `μ` has Lebesgue decomposition with respect to any σ-finite measure `ν`.
That is to say, there exist a measure `ξ` and a measurable function `f`,
such that `ξ` is mutually singular with respect to `ν` and `μ = ξ + ν.withDensity f` -/
nonrec instance (priority := 100) haveLebesgueDecomposition_of_sigmaFinite
    [SFinite μ] [SigmaFinite ν] : HaveLebesgueDecomposition μ ν := by
  wlog hμ : IsFiniteMeasure μ generalizing μ
  · exact .sfinite_of_isFiniteMeasure fun μ _ ↦ this μ ‹_›
  -- Take a disjoint cover that consists of sets of finite measure `ν`.
  set s : ℕ → Set α := disjointed (spanningSets ν)
  have hsm : ∀ n, MeasurableSet (s n) := .disjointed <| measurableSet_spanningSets _
  have hs : ∀ n, Fact (ν (s n) < ⊤) := fun n ↦
    ⟨lt_of_le_of_lt (measure_mono <| disjointed_le ..) (measure_spanningSets_lt_top ν n)⟩
  -- Note that the restrictions of `μ` and `ν` to `s n` are finite measures.
  -- Therefore, as we proved above, these restrictions have a Lebesgue decomposition.
  -- Let `ξ n` and `f n` be the singular part and the Radon-Nikodym derivative
  -- of these restrictions.
  set ξ : ℕ → Measure α := fun n : ℕ ↦ singularPart (.restrict μ (s n)) (.restrict ν (s n))
  set f : ℕ → α → ℝ≥0∞ := fun n ↦ (s n).indicator (rnDeriv (.restrict μ (s n)) (.restrict ν (s n)))
  have hfm (n : ℕ) : Measurable (f n) := by measurability
  -- Each `ξ n` is supported on `s n` and is mutually singular with the restriction of `ν` to `s n`.
  -- Therefore, `ξ n` is mutually singular with `ν`, hence their sum is mutually singular with `ν`.
  have hξ : .sum ξ ⟂ₘ ν := by
    refine MutuallySingular.sum_left.2 fun n ↦ ?_
    rw [← ν.restrict_add_restrict_compl (hsm n)]
    refine (mutuallySingular_singularPart ..).add_right (.singularPart ?_ _)
    refine ⟨(s n)ᶜ, (hsm n).compl, ?_⟩
    simp [hsm]
  -- Finally, the sum of all `ξ n` and measure `ν` with the density `∑' n, f n`
  -- is equal to `μ`, thus `(Measure.sum ξ, ∑' n, f n)` is a Lebesgue decomposition for `μ` and `ν`.
  have hadd : .sum ξ + ν.withDensity (∑' n, f n) = μ := calc
    .sum ξ + ν.withDensity (∑' n, f n) = .sum fun n ↦ ξ n + ν.withDensity (f n) := by
      rw [withDensity_tsum hfm, Measure.sum_add_sum]
    _ = .sum fun n ↦ .restrict μ (s n) := by
      simp_rw [ξ, f, withDensity_indicator (hsm _), singularPart_add_rnDeriv]
    _ = μ := sum_restrict_disjointed_spanningSets ..
  exact ⟨⟨(.sum ξ, ∑' n, f n), by fun_prop, hξ, hadd.symm⟩⟩

section rnDeriv

/-- Radon-Nikodym derivative of the scalar multiple of a measure.
See also `rnDeriv_smul_left`, which has no hypothesis on `μ` but requires finite `ν`. -/
/-
**MeasureTheory.Measure.rnDeriv_smul_left'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Measure`。
形式化陈述：rnDeriv_smul_left' (ν μ : Measure α) [SigmaFinite ν] [SigmaFinite μ] (r : 
Real>=0) : (r • ν).rnDeriv μ =ᵐ[μ] r • ν.rnDeriv μ
参数：ν μ : Measure α；r : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.withDensity_eq_iff_of_sigmaFinite`：withDensity_eq_iff_of_s
igmaFinite [SigmaFinite μ] {f g : α -> Real>=0∞} (hf : AEMeasurable f μ) (hg : A
EMeasurable g μ) : μ.withDensity f = …
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用引理 `AEMeasurable.const_smul`：AEMeasurable.const_smul (hg : AEMeasurable g μ)
 (c : M) : AEMeasurable (c • g) μ
· 使用定理 `MeasurableSMul.toMeasurableConstSMul`：∀ {M : Type u_2} {α : Type u_3} {i
nst : SMul M α} {inst_1 : MeasurableSpace M} {inst_2 : MeasurableSpace α}   [sel
f : MeasurableSMul M α], M…
· 使用定理 `ENNReal.instMeasurableSMulNNReal`：MeasurableSMul NNReal ENNReal
· 使用定理 `MeasureTheory.withDensity_smul`：withDensity_smul (r : Real>=0∞) {f : α -
> Real>=0∞} (hf : Measurable f) : μ.withDensity (r • f) = r • μ.withDensity f
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_add`：haveLebesgueDecompo
sition_add (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] : μ = μ.singularPar
t ν + ν.withDensity (μ.rnDeriv ν)
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.Measure.singularPart_smul`：singularPart_smul (μ ν : Measur
e α) (r : Real>=0) : (r • μ).singularPart ν = r • μ.singularPart ν
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `MeasureTheory.Measure.add_right_inj`：∀ {α : Type u_1} {m0 : MeasurableSp
ace α} (μ ν₁ ν₂ : MeasureTheory.Measure α) [MeasureTheory.SigmaFinite μ],   μ + 
ν₁ = μ + ν₂ ↔ ν₁ = ν₂
· 使用定理 `MeasureTheory.Measure.singularPart.instSigmaFinite`：∀ {α : Type u_1} {m 
: MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite 
μ],   MeasureTheory.SigmaFinite (μ.singu…
· 使用定理 `MeasureTheory.SMul.sigmaFinite`：∀ {α : Type u_1} {m0 : MeasurableSpace α
} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ] (c : NNReal),   Me
asureTheory.SigmaFin…

--- 原说明 ---
Radon-Nikodym derivative of the scalar multiple of a measure.
See also `rnDeriv_smul_left`, which has no hypothesis on `μ` but requires finite
 `ν`.
-/
theorem rnDeriv_smul_left' (ν μ : Measure α) [SigmaFinite ν] [SigmaFinite μ] (r : ℝ≥0) :
    (r • ν).rnDeriv μ =ᵐ[μ] r • ν.rnDeriv μ := by
  rw [← withDensity_eq_iff_of_sigmaFinite]
  · simp_rw [ENNReal.smul_def]
    rw [withDensity_smul _ (measurable_rnDeriv _ _)]
    suffices (r • ν).singularPart μ + withDensity μ (rnDeriv (r • ν) μ)
        = (r • ν).singularPart μ + r • withDensity μ (rnDeriv ν μ) by
      rwa [Measure.add_right_inj] at this
    rw [← (r • ν).haveLebesgueDecomposition_add μ, singularPart_smul, ← smul_add,
      ← ν.haveLebesgueDecomposition_add μ]
  · exact (measurable_rnDeriv _ _).aemeasurable
  · exact (measurable_rnDeriv _ _).aemeasurable.const_smul _

/-- Radon-Nikodym derivative of the scalar multiple of a measure.
See also `rnDeriv_smul_left_of_ne_top`, which has no hypothesis on `μ` but requires finite `ν`. -/
/-
**MeasureTheory.Measure.rnDeriv_smul_left_of_ne_top'** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.Measure`。
形式化陈述：rnDeriv_smul_left_of_ne_top' (ν μ : Measure α) [SigmaFinite ν] [SigmaFinit
e μ] {r : Real>=0∞} (hr : r != ∞) : (r • ν).rnDeriv μ =ᵐ[μ] r • ν.rnDeriv μ
参数：ν μ : Measure α；hr : r != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.rnDeriv_smul_left'`：rnDeriv_smul_left' (ν μ : Meas
ure α) [SigmaFinite ν] [SigmaFinite μ] (r : Real>=0) : (r • ν).rnDeriv μ =ᵐ[μ] r
 • ν.rnDeriv μ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.coe_toNNReal`：∀ {a : ENNReal}, a ≠ ⊤ → ↑a.toNNReal = a

--- 原说明 ---
Radon-Nikodym derivative of the scalar multiple of a measure.
See also `rnDeriv_smul_left_of_ne_top`, which has no hypothesis on `μ` but requi
res finite `ν`.
-/
theorem rnDeriv_smul_left_of_ne_top' (ν μ : Measure α) [SigmaFinite ν] [SigmaFinite μ]
    {r : ℝ≥0∞} (hr : r ≠ ∞) :
    (r • ν).rnDeriv μ =ᵐ[μ] r • ν.rnDeriv μ := by
  have h : (r.toNNReal • ν).rnDeriv μ =ᵐ[μ] r.toNNReal • ν.rnDeriv μ :=
    rnDeriv_smul_left' ν μ r.toNNReal
  simpa [ENNReal.smul_def, ENNReal.coe_toNNReal hr] using h

/-- Radon-Nikodym derivative with respect to the scalar multiple of a measure.
See also `rnDeriv_smul_right`, which has no hypothesis on `μ` but requires finite `ν`. -/
/-
**MeasureTheory.Measure.rnDeriv_smul_right'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Measure`。
形式化陈述：rnDeriv_smul_right' (ν μ : Measure α) [SigmaFinite ν] [SigmaFinite μ] {r :
 Real>=0} (hr : r != 0) : ν.rnDeriv (r • μ) =ᵐ[μ] r⁻¹ • ν.rnDeriv μ
参数：ν μ : Measure α；hr : r != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.ae_le`：∀ {α : Type u_1} {mα :
 MeasurableSpace α} {μ ν : MeasureTheory.Measure α},   μ.AbsolutelyContinuous ν 
→ MeasureTheory.ae μ ≤ MeasureTheory.a…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `MeasureTheory.Measure.absolutelyContinuous_smul`：absolutelyContinuous_sm
ul {c : Real>=0∞} (hc : c != 0) : μ ≪ c • μ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_ne_zero`：coe_ne_zero : (r : Real>=0∞) != 0 ↔ r != 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.withDensity_eq_iff_of_sigmaFinite`：withDensity_eq_iff_of_s
igmaFinite [SigmaFinite μ] {f g : α -> Real>=0∞} (hf : AEMeasurable f μ) (hg : A
EMeasurable g μ) : μ.withDensity f = …
· 使用定理 `MeasureTheory.SMul.sigmaFinite`：∀ {α : Type u_1} {m0 : MeasurableSpace α
} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ] (c : NNReal),   Me
asureTheory.SigmaFin…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用引理 `AEMeasurable.const_smul`：AEMeasurable.const_smul (hg : AEMeasurable g μ)
 (c : M) : AEMeasurable (c • g) μ
· 使用定理 `MeasurableSMul.toMeasurableConstSMul`：∀ {M : Type u_2} {α : Type u_3} {i
nst : SMul M α} {inst_1 : MeasurableSpace M} {inst_2 : MeasurableSpace α}   [sel
f : MeasurableSMul M α], M…
· 使用定理 `ENNReal.instMeasurableSMulNNReal`：MeasurableSMul NNReal ENNReal
· 使用定理 `MeasureTheory.withDensity_smul`：withDensity_smul (r : Real>=0∞) {f : α -
> Real>=0∞} (hf : Measurable f) : μ.withDensity (r • f) = r • μ.withDensity f
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_add`：haveLebesgueDecompo
sition_add (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] : μ = μ.singularPar
t ν + ν.withDensity (μ.rnDeriv ν)
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.Measure.singularPart_smul_right`：singularPart_smul_right (
μ ν : Measure α) (r : Real>=0) (hr : r != 0) : μ.singularPart (r • ν) = μ.singul
arPart ν
· 使用定理 `ENNReal.smul_def`：smul_def {M : Type*} [MulAction Real>=0∞ M] (c : Real>
=0) (x : M) : c • x = (c : Real>=0∞) • x
· 使用定理 `MeasureTheory.withDensity_smul_measure`：withDensity_smul_measure (r : Re
al>=0∞) (f : α -> Real>=0∞) : (r • μ).withDensity f = r • μ.withDensity f
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `MeasureTheory.Measure.add_right_inj`：∀ {α : Type u_1} {m0 : MeasurableSp
ace α} (μ ν₁ ν₂ : MeasureTheory.Measure α) [MeasureTheory.SigmaFinite μ],   μ + 
ν₁ = μ + ν₂ ↔ ν₁ = ν₂
· 使用定理 `MeasureTheory.Measure.singularPart.instSigmaFinite`：∀ {α : Type u_1} {m 
: MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite 
μ],   MeasureTheory.SigmaFinite (μ.singu…

--- 原说明 ---
Radon-Nikodym derivative with respect to the scalar multiple of a measure.
See also `rnDeriv_smul_right`, which has no hypothesis on `μ` but requires finit
e `ν`.
-/
theorem rnDeriv_smul_right' (ν μ : Measure α) [SigmaFinite ν] [SigmaFinite μ]
    {r : ℝ≥0} (hr : r ≠ 0) :
    ν.rnDeriv (r • μ) =ᵐ[μ] r⁻¹ • ν.rnDeriv μ := by
  refine (absolutelyContinuous_smul <| ENNReal.coe_ne_zero.2 hr).ae_le
    (?_ : ν.rnDeriv (r • μ) =ᵐ[r • μ] r⁻¹ • ν.rnDeriv μ)
  rw [← withDensity_eq_iff_of_sigmaFinite]
  · simp_rw [ENNReal.smul_def]
    rw [withDensity_smul _ (measurable_rnDeriv _ _)]
    suffices ν.singularPart (r • μ) + withDensity (r • μ) (rnDeriv ν (r • μ))
        = ν.singularPart (r • μ) + r⁻¹ • withDensity (r • μ) (rnDeriv ν μ) by
      rwa [add_right_inj] at this
    rw [← ν.haveLebesgueDecomposition_add (r • μ), singularPart_smul_right _ _ _ hr,
      ENNReal.smul_def r, withDensity_smul_measure, ← ENNReal.smul_def, ← smul_assoc,
      smul_eq_mul, inv_mul_cancel₀ hr, one_smul]
    exact ν.haveLebesgueDecomposition_add μ
  · exact (measurable_rnDeriv _ _).aemeasurable
  · exact (measurable_rnDeriv _ _).aemeasurable.const_smul _

/-- Radon-Nikodym derivative with respect to the scalar multiple of a measure.
See also `rnDeriv_smul_right_of_ne_top`, which has no hypothesis on `μ` but requires finite `ν`. -/
/-
**MeasureTheory.Measure.rnDeriv_smul_right_of_ne_top'** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.Measure`。
形式化陈述：rnDeriv_smul_right_of_ne_top' (ν μ : Measure α) [SigmaFinite ν] [SigmaFini
te μ] {r : Real>=0∞} (hr : r != 0) (hr_ne_top : r != ∞) : ν.rnDeriv (r • μ) =ᵐ[μ
] r⁻¹ • ν.rnDeriv μ
参数：ν μ : Measure α；hr : r != 0；hr_ne_top : r != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.rnDeriv_smul_right'`：rnDeriv_smul_right' (ν μ : Me
asure α) [SigmaFinite ν] [SigmaFinite μ] {r : Real>=0} (hr : r != 0) : ν.rnDeriv
 (r • μ) =ᵐ[μ] r⁻¹ • ν.rnDeriv …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `ENNReal.toNNReal_eq_zero_iff`：toNNReal_eq_zero_iff (x : Real>=0∞) : x.to
NNReal = 0 ↔ x = 0 ∨ x = ∞
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ENNReal.coe_toNNReal`：∀ {a : ENNReal}, a ≠ ⊤ → ↑a.toNNReal = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.inv_ne_top`：inv_ne_top : a⁻¹ != ∞ ↔ a != 0
· 使用定理 `ENNReal.smul_def`：smul_def {M : Type*} [MulAction Real>=0∞ M] (c : Real>
=0) (x : M) : c • x = (c : Real>=0∞) • x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.toNNReal_inv`：∀ (a : ENNReal), a⁻¹.toNNReal = a.toNNReal⁻¹

--- 原说明 ---
Radon-Nikodym derivative with respect to the scalar multiple of a measure.
See also `rnDeriv_smul_right_of_ne_top`, which has no hypothesis on `μ` but requ
ires finite `ν`.
-/
theorem rnDeriv_smul_right_of_ne_top' (ν μ : Measure α) [SigmaFinite ν] [SigmaFinite μ]
    {r : ℝ≥0∞} (hr : r ≠ 0) (hr_ne_top : r ≠ ∞) :
    ν.rnDeriv (r • μ) =ᵐ[μ] r⁻¹ • ν.rnDeriv μ := by
  have h : ν.rnDeriv (r.toNNReal • μ) =ᵐ[μ] r.toNNReal⁻¹ • ν.rnDeriv μ := by
    refine rnDeriv_smul_right' ν μ ?_
    rw [ne_eq, ENNReal.toNNReal_eq_zero_iff]
    simp [hr, hr_ne_top]
  rwa [ENNReal.smul_def, ENNReal.coe_toNNReal hr_ne_top,
    ← ENNReal.toNNReal_inv, ENNReal.smul_def, ENNReal.coe_toNNReal (ENNReal.inv_ne_top.mpr hr)] at h

/-- Radon-Nikodym derivative of a sum of two measures.
See also `rnDeriv_add`, which has no hypothesis on `μ` but requires finite `ν₁` and `ν₂`. -/
/-
**MeasureTheory.Measure.rnDeriv_add'** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Me
asure`。
形式化陈述：rnDeriv_add' (ν₁ ν₂ μ : Measure α) [SigmaFinite ν₁] [SigmaFinite ν₂] [Sigm
aFinite μ] : (ν₁ + ν₂).rnDeriv μ =ᵐ[μ] ν₁.rnDeriv μ + ν₂.rnDeriv μ
参数：ν₁ ν₂ μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.withDensity_eq_iff_of_sigmaFinite`：withDensity_eq_iff_of_s
igmaFinite [SigmaFinite μ] {f g : α -> Real>=0∞} (hf : AEMeasurable f μ) (hg : A
EMeasurable g μ) : μ.withDensity f = …
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用定理 `Measurable.add`：∀ {M : Type u_2} {α : Type u_3} [inst : MeasurableSpace 
M] [inst_1 : Add M] {m : MeasurableSpace α} {f g : α → M}   [MeasurableAdd₂ M], 
Meas…
· 使用定理 `ContinuousAdd.measurableMul₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Add γ] [Con…
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `ENNReal.instContinuousAdd`：ContinuousAdd ENNReal
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_add`：haveLebesgueDecompo
sition_add (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] : μ = μ.singularPar
t ν + ν.withDensity (μ.rnDeriv ν)
· 使用定理 `MeasureTheory.Measure.HaveLebesgueDecomposition.add_left`：∀ {α : Type u_
1} {m : MeasurableSpace α} {μ ν μ' : MeasureTheory.Measure α} [μ.HaveLebesgueDec
omposition ν]   [μ'.HaveLebesgueDecomposition …
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.Measure.singularPart_add`：singularPart_add (μ₁ μ₂ ν : Meas
ure α) [HaveLebesgueDecomposition μ₁ ν] [HaveLebesgueDecomposition μ₂ ν] : (μ₁ +
 μ₂).singularPart ν = μ₁.sin…
· 使用定理 `MeasureTheory.withDensity_add_left`：withDensity_add_left {f : α -> Real>
=0∞} (hf : Measurable f) (g : α -> Real>=0∞) : μ.withDensity (f + g) = μ.withDen
sity f + μ.withDensity g
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `MeasureTheory.Measure.add_right_inj`：∀ {α : Type u_1} {m0 : MeasurableSp
ace α} (μ ν₁ ν₂ : MeasureTheory.Measure α) [MeasureTheory.SigmaFinite μ],   μ + 
ν₁ = μ + ν₂ ↔ ν₁ = ν₂
· 使用定理 `MeasureTheory.Measure.singularPart.instSigmaFinite`：∀ {α : Type u_1} {m 
: MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite 
μ],   MeasureTheory.SigmaFinite (μ.singu…
· 使用定理 `MeasureTheory.Add.sigmaFinite`：∀ {α : Type u_1} {m0 : MeasurableSpace α}
 (μ ν : MeasureTheory.Measure α) [MeasureTheory.SigmaFinite μ]   [MeasureTheory.
SigmaFinite ν], Mea…

--- 原说明 ---
Radon-Nikodym derivative of a sum of two measures.
See also `rnDeriv_add`, which has no hypothesis on `μ` but requires finite `ν₁` 
and `ν₂`.
-/
lemma rnDeriv_add' (ν₁ ν₂ μ : Measure α) [SigmaFinite ν₁] [SigmaFinite ν₂] [SigmaFinite μ] :
    (ν₁ + ν₂).rnDeriv μ =ᵐ[μ] ν₁.rnDeriv μ + ν₂.rnDeriv μ := by
  rw [← withDensity_eq_iff_of_sigmaFinite]
  · suffices (ν₁ + ν₂).singularPart μ + μ.withDensity ((ν₁ + ν₂).rnDeriv μ)
        = (ν₁ + ν₂).singularPart μ + μ.withDensity (ν₁.rnDeriv μ + ν₂.rnDeriv μ) by
      rwa [add_right_inj] at this
    rw [← (ν₁ + ν₂).haveLebesgueDecomposition_add μ, singularPart_add,
      withDensity_add_left (measurable_rnDeriv _ _), add_assoc,
      add_comm (ν₂.singularPart μ), add_assoc, add_comm _ (ν₂.singularPart μ),
      ← ν₂.haveLebesgueDecomposition_add μ, ← add_assoc, ← ν₁.haveLebesgueDecomposition_add μ]
  · exact (measurable_rnDeriv _ _).aemeasurable
  · exact ((measurable_rnDeriv _ _).add (measurable_rnDeriv _ _)).aemeasurable
/-
**MeasureTheory.Measure.rnDeriv_add_of_mutuallySingular** 是 Mathlib 中的一个引理，位于命名空
间 `MeasureTheory.Measure`。
形式化陈述：rnDeriv_add_of_mutuallySingular (ν₁ ν₂ μ : Measure α) [SigmaFinite ν₁] [Si
gmaFinite ν₂] [SigmaFinite μ] (h : ν₂ ⟂ₘ μ) : (ν₁ + ν₂).rnDeriv μ =ᵐ[μ] ν₁.rnDer
iv μ
参数：ν₁ ν₂ μ : Measure α；h : ν₂ ⟂ₘ μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `MeasureTheory.Measure.rnDeriv_eq_zero`：rnDeriv_eq_zero (μ ν : Measure α)
 [μ.HaveLebesgueDecomposition ν] : μ.rnDeriv ν =ᵐ[ν] 0 ↔ μ ⟂ₘ ν
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用引理 `MeasureTheory.Measure.rnDeriv_add'`：rnDeriv_add' (ν₁ ν₂ μ : Measure α) [
SigmaFinite ν₁] [SigmaFinite ν₂] [SigmaFinite μ] : (ν₁ + ν₂).rnDeriv μ =ᵐ[μ] ν₁.
rnDeriv μ + ν₂.rnDeriv μ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rnDeriv_add_of_mutuallySingular (ν₁ ν₂ μ : Measure α)
    [SigmaFinite ν₁] [SigmaFinite ν₂] [SigmaFinite μ] (h : ν₂ ⟂ₘ μ) :
    (ν₁ + ν₂).rnDeriv μ =ᵐ[μ] ν₁.rnDeriv μ := by
  filter_upwards [rnDeriv_add' ν₁ ν₂ μ, (rnDeriv_eq_zero ν₂ μ).mpr h] with x hx_add hx_zero
  simp [hx_add, hx_zero]

end rnDeriv

/-
**MeasureTheory.Measure.add_sub_of_mutuallySingular** 是 Mathlib 中的一个引理，位于命名空间 `M
easureTheory.Measure`。
形式化陈述：add_sub_of_mutuallySingular {ξ : Measure α} (h : μ ⟂ₘ ξ) : μ + (ν - ξ) = μ
 + ν - ξ
参数：h : μ ⟂ₘ ξ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.Measure.MutuallySingular.measurableSet_nullSet`：measurable
Set_nullSet (h : μ ⟂ₘ ν) : MeasurableSet h.nullSet
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.MutuallySingular.restrict_nullSet`：restrict_nullSe
t (h : μ ⟂ₘ ν) : μ.restrict h.nullSet = 0
· 使用定理 `MeasureTheory.Measure.restrict_sub_eq_restrict_sub_restrict`：restrict_su
b_eq_restrict_sub_restrict (h_meas_s : MeasurableSet s) : (μ - ν).restrict s = μ
.restrict s - ν.restrict s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用引理 `MeasureTheory.Measure.MutuallySingular.restrict_compl_nullSet`：restrict_
compl_nullSet (h : μ ⟂ₘ ν) : ν.restrict h.nullSetᶜ = 0
· 使用定理 `MeasureTheory.Measure.sub_zero`：∀ {α : Type u_1} {m : MeasurableSpace α}
 {μ : MeasureTheory.Measure α}, μ - 0 = μ
· 使用定理 `MeasureTheory.Measure.restrict_add_restrict_compl`：restrict_add_restrict
_compl (hs : MeasurableSet s) : μ.restrict s + μ.restrict sᶜ = μ
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `_private.Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue.0.MeasureT
heory.Measure.add_sub_of_mutuallySingular._abel_1_1`：∀ {α : Type u_1} {m : Measu
rableSpace α} {μ ν ξ : MeasureTheory.Measure α} (h : μ.MutuallySingular ξ),   μ.
restrict h.nullSet + μ.restrict h…
· 使用定理 `MeasureTheory.Measure.restrict_add`：restrict_add {_m0 : MeasurableSpace 
α} (μ ν : Measure α) (s : Set α) : (μ + ν).restrict s = μ.restrict s + ν.restric
t s
-/
lemma add_sub_of_mutuallySingular {ξ : Measure α} (h : μ ⟂ₘ ξ) : μ + (ν - ξ) = μ + ν - ξ := by
  let s := h.nullSet
  have hs : MeasurableSet s := h.measurableSet_nullSet
  have h_le_s : μ.restrict s + (ν - ξ).restrict s = μ.restrict s + ν.restrict s - ξ.restrict s := by
    rw [h.restrict_nullSet, restrict_sub_eq_restrict_sub_restrict hs]
    simp
  have h_le_s_compl : μ.restrict sᶜ + (ν - ξ).restrict sᶜ =
      μ.restrict sᶜ + ν.restrict sᶜ - ξ.restrict sᶜ := by
    rw [restrict_sub_eq_restrict_sub_restrict hs.compl, h.restrict_compl_nullSet]
    simp
  calc μ + (ν - ξ)
  _ = μ.restrict s + μ.restrict sᶜ + (ν - ξ).restrict s + (ν - ξ).restrict sᶜ := by
    rw [restrict_add_restrict_compl hs, add_assoc, restrict_add_restrict_compl hs]
  _ = μ.restrict s + (ν - ξ).restrict s + (μ.restrict sᶜ + (ν - ξ).restrict sᶜ) := by abel
  _ = (μ.restrict s + ν.restrict s - ξ.restrict s) +
      (μ.restrict sᶜ + ν.restrict sᶜ - ξ.restrict sᶜ) := by rw [h_le_s, h_le_s_compl]
  _ = (μ + ν - ξ).restrict s + (μ + ν - ξ).restrict sᶜ := by
      simp [restrict_sub_eq_restrict_sub_restrict hs,
        restrict_sub_eq_restrict_sub_restrict hs.compl]
  _ = μ + ν - ξ := by rw [restrict_add_restrict_compl hs]

end Measure

end MeasureTheory

