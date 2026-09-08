/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker, Devon Tuma, Kexing Ying
-/
module

public import Mathlib.Probability.Density
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Uniform distributions and probability mass functions

This file defines two related notions of uniform distributions, which will be unified in the future.

## Uniform distributions

Defines the uniform distribution for any set with finite measure.

### Main definitions
* `IsUniform X s ℙ μ` : A random variable `X` has uniform distribution on `s` under `ℙ` if the
  push-forward measure agrees with the rescaled restricted measure `μ`.

## Uniform probability mass functions

This file defines a number of uniform `PMF` distributions from various inputs,
  uniformly drawing from the corresponding object.

### Main definitions
`PMF.uniformOfFinset` gives each element in the set equal probability,
  with `0` probability for elements not in the set.

`PMF.uniformOfFintype` gives all elements equal probability,
  equal to the inverse of the size of the `Fintype`.

`PMF.ofMultiset` draws randomly from the given `Multiset`, treating duplicate values as distinct.
  Each probability is given by the count of the element divided by the size of the `Multiset`

## TODO
* Refactor the `PMF` definitions to come from a `uniformMeasure` on a `Finset`/`Fintype`/`Multiset`.
-/

@[expose] public section

open scoped Finset MeasureTheory NNReal ENNReal

-- TODO: We can't `open ProbabilityTheory` without opening the `ProbabilityTheory` scope :(
open TopologicalSpace MeasureTheory.Measure PMF

noncomputable section

namespace MeasureTheory

variable {E : Type*} [MeasurableSpace E] {μ : Measure E}

namespace pdf

variable {Ω : Type*}
variable {_ : MeasurableSpace Ω} {ℙ : Measure Ω}

/-- A random variable `X` has uniform distribution on `s` if its push-forward measure is
`(μ s)⁻¹ • μ.restrict s`. -/
/-
**MeasureTheory.pdf.IsUniform** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.pdf`。
形式化陈述：IsUniform (X : Ω -> E) (s : Set E) (ℙ : Measure Ω) (μ : Measure E
参数：X : Ω -> E；s : Set E；ℙ : Measure Ω。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A random variable `X` has uniform distribution on `s` if its push-forward measur
e is
`(μ s)⁻¹ • μ.restrict s`.
-/
def IsUniform (X : Ω → E) (s : Set E) (ℙ : Measure Ω) (μ : Measure E := by volume_tac) :=
  map X ℙ = ProbabilityTheory.cond μ s

namespace IsUniform

/-
**MeasureTheory.pdf.IsUniform.aemeasurable** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.pdf.IsUniform`。
形式化陈述：aemeasurable {X : Ω -> E} {s : Set E} (hns : μ s != 0) (hnt : μ s != ∞) (h
u : IsUniform X s ℙ μ) : AEMeasurable X ℙ
参数：hns : μ s != 0；hnt : μ s != ∞；hu : IsUniform X s ℙ μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用引理 `zero_ne_one'`：zero_ne_one' [One α] [NeZero (1 : α)] : (0 : α) != 1
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_of_not_aemeasurable`：map_of_not_aemeasurable {
f : α -> β} {μ : Measure α} (hf : ¬AEMeasurable f μ) : μ.map f = 0
· 使用定理 `MeasureTheory.Measure.smul_apply`：smul_apply {_m : MeasurableSpace α} (c
 : R) (μ : Measure α) (s : Set α) : (c • μ) s = c • μ s
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `ENNReal.inv_mul_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a⁻¹ * a = 1
-/
theorem aemeasurable {X : Ω → E} {s : Set E} (hns : μ s ≠ 0) (hnt : μ s ≠ ∞)
    (hu : IsUniform X s ℙ μ) : AEMeasurable X ℙ := by
  dsimp [IsUniform, ProbabilityTheory.cond] at hu
  by_contra h
  rw [map_of_not_aemeasurable h] at hu
  apply zero_ne_one' ℝ≥0∞
  calc
    0 = (0 : Measure E) Set.univ := rfl
    _ = _ := by rw [hu, Measure.smul_apply, restrict_apply MeasurableSet.univ,
      Set.univ_inter, smul_eq_mul, ENNReal.inv_mul_cancel hns hnt]
/-
**MeasureTheory.pdf.IsUniform.absolutelyContinuous** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.pdf.IsUniform`。
形式化陈述：absolutelyContinuous {X : Ω -> E} {s : Set E} (hu : IsUniform X s ℙ μ) : m
ap X ℙ ≪ μ
参数：hu : IsUniform X s ℙ μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.cond_absolutelyContinuous`：cond_absolutelyContinuous :
 μ[|s] ≪ μ
-/
theorem absolutelyContinuous {X : Ω → E} {s : Set E} (hu : IsUniform X s ℙ μ) : map X ℙ ≪ μ := by
  rw [hu]; exact ProbabilityTheory.cond_absolutelyContinuous
/-
**MeasureTheory.pdf.IsUniform.measure_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.pdf.IsUniform`。
形式化陈述：measure_preimage {X : Ω -> E} {s : Set E} (hns : μ s != 0) (hnt : μ s != ∞
) (hu : IsUniform X s ℙ μ) {A : Set E} (hA : MeasurableSet A) : ℙ (X ⁻¹' A) = μ 
(s inter A) / μ s
参数：hns : μ s != 0；hnt : μ s != ∞；hu : IsUniform X s ℙ μ；hA : MeasurableSet A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.map_apply_of_aemeasurable`：map_apply_of_aemeasurab
le (hf : AEMeasurable f μ) {s : Set β} (hs : MeasurableSet s) : μ.map f s = μ (f
 ⁻¹' s)
· 使用定理 `MeasureTheory.pdf.IsUniform.aemeasurable`：aemeasurable {X : Ω -> E} {s :
 Set E} (hns : μ s != 0) (hnt : μ s != ∞) (hu : IsUniform X s ℙ μ) : AEMeasurabl
e X ℙ
· 使用定理 `ProbabilityTheory.cond_apply'`：cond_apply' (ht : MeasurableSet t) (μ : M
easure Ω) : μ[t | s] = (μ s)⁻¹ * μ (s inter t)
· 使用定理 `ENNReal.div_eq_inv_mul`：∀ {a b : ENNReal}, a / b = b⁻¹ * a
-/
theorem measure_preimage {X : Ω → E} {s : Set E} (hns : μ s ≠ 0) (hnt : μ s ≠ ∞)
    (hu : IsUniform X s ℙ μ) {A : Set E} (hA : MeasurableSet A) :
    ℙ (X ⁻¹' A) = μ (s ∩ A) / μ s := by
  rwa [← map_apply_of_aemeasurable (hu.aemeasurable hns hnt) hA, hu, ProbabilityTheory.cond_apply',
    ENNReal.div_eq_inv_mul]
/-
**MeasureTheory.pdf.IsUniform.isProbabilityMeasure** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.pdf.IsUniform`。
形式化陈述：isProbabilityMeasure {X : Ω -> E} {s : Set E} (hns : μ s != 0) (hnt : μ s 
!= ∞) (hu : IsUniform X s ℙ μ) : IsProbabilityMeasure ℙ
参数：hns : μ s != 0；hnt : μ s != ∞；hu : IsUniform X s ℙ μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.preimage_univ`：preimage_univ : f ⁻¹' univ = univ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.pdf.IsUniform.measure_preimage`：measure_preimage {X : Ω ->
 E} {s : Set E} (hns : μ s != 0) (hnt : μ s != ∞) (hu : IsUniform X s ℙ μ) {A : 
Set E} (hA : MeasurableSet A) : ℙ …
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `ENNReal.div_self`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a / a = 1
-/
theorem isProbabilityMeasure {X : Ω → E} {s : Set E} (hns : μ s ≠ 0) (hnt : μ s ≠ ∞)
    (hu : IsUniform X s ℙ μ) : IsProbabilityMeasure ℙ :=
  ⟨by
    have : X ⁻¹' Set.univ = Set.univ := Set.preimage_univ
    rw [← this, hu.measure_preimage hns hnt MeasurableSet.univ, Set.inter_univ,
      ENNReal.div_self hns hnt]⟩
/-
**MeasureTheory.pdf.IsUniform.toMeasurable_iff** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.pdf.IsUniform`。
形式化陈述：toMeasurable_iff {X : Ω -> E} {s : Set E} : IsUniform X (toMeasurable μ s)
 ℙ μ ↔ IsUniform X s ℙ μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.cond_toMeasurable_eq`：cond_toMeasurable_eq : μ[|(toMea
surable μ s)] = μ[|s]
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toMeasurable_iff {X : Ω → E} {s : Set E} :
    IsUniform X (toMeasurable μ s) ℙ μ ↔ IsUniform X s ℙ μ := by
  unfold IsUniform
  rw [ProbabilityTheory.cond_toMeasurable_eq]
/-
**MeasureTheory.pdf.IsUniform.toMeasurable** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.pdf.IsUniform`。
形式化陈述：∀ {E : Type u_1} [inst : MeasurableSpace E] {μ : MeasureTheory.Measure E} 
{Ω : Type u_2} {x : MeasurableSpace Ω}   {ℙ : MeasureTheory.Measure Ω} {X : Ω → 
E} {s : Set E},   MeasureTheory.pdf.IsUniform X s ℙ μ → MeasureTheory.pdf.IsUnif
orm X (MeasureTheory.toMeasurable μ s) ℙ μ
参数：MeasureTheory.toMeasurable μ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.pdf.IsUniform.toMeasurable_iff`：toMeasurable_iff {X : Ω ->
 E} {s : Set E} : IsUniform X (toMeasurable μ s) ℙ μ ↔ IsUniform X s ℙ μ
-/
protected theorem toMeasurable {X : Ω → E} {s : Set E} (hu : IsUniform X s ℙ μ) :
    IsUniform X (toMeasurable μ s) ℙ μ :=
  toMeasurable_iff.mpr hu
/-
**MeasureTheory.pdf.IsUniform.hasPDF** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.pd
f.IsUniform`。
形式化陈述：hasPDF {X : Ω -> E} {s : Set E} (hns : μ s != 0) (hnt : μ s != ∞) (hu : Is
Uniform X s ℙ μ) : HasPDF X ℙ μ
参数：hns : μ s != 0；hnt : μ s != ∞；hu : IsUniform X s ℙ μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.hasPDF_of_map_eq_withDensity`：hasPDF_of_map_eq_withDensity
 (hX : AEMeasurable X ℙ) (f : E -> Real>=0∞) (hf : AEMeasurable f μ) (h : map X 
ℙ = μ.withDensity f) : HasPDF X …
· 使用定理 `MeasureTheory.pdf.IsUniform.aemeasurable`：aemeasurable {X : Ω -> E} {s :
 Set E} (hns : μ s != 0) (hnt : μ s != ∞) (hu : IsUniform X s ℙ μ) : AEMeasurabl
e X ℙ
· 使用定理 `AEMeasurable.indicator`：AEMeasurable.indicator (hfm : AEMeasurable f μ) 
{s} (hs : MeasurableSet s) : AEMeasurable (s.indicator f) μ
· 使用引理 `AEMeasurable.const_smul`：AEMeasurable.const_smul (hg : AEMeasurable g μ)
 (c : M) : AEMeasurable (c • g) μ
· 使用定理 `MeasurableSMul.toMeasurableConstSMul`：∀ {M : Type u_2} {α : Type u_3} {i
nst : SMul M α} {inst_1 : MeasurableSpace M} {inst_2 : MeasurableSpace α}   [sel
f : MeasurableSMul M α], M…
· 使用定理 `measurableSMul_of_mul`：∀ (M : Type u_2) [inst : Mul M] [inst_1 : Measura
bleSpace M] [MeasurableMul M], MeasurableSMul M M
· 使用定理 `MeasurableMul₂.toMeasurableMul`：∀ {M : Type u_2} [inst : MeasurableSpace
 M] [inst_1 : Mul M] [MeasurableMul₂ M], MeasurableMul M
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `measurable_one`：measurable_one [One α] : Measurable (1 : β -> α)
· 使用定理 `MeasureTheory.measurableSet_toMeasurable`：measurableSet_toMeasurable (μ 
: Measure α) (s : Set α) : MeasurableSet (toMeasurable μ s)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.withDensity_indicator`：withDensity_indicator {s : Set α} (
hs : MeasurableSet s) (f : α -> Real>=0∞) : μ.withDensity (s.indicator f) = (μ.r
estrict s).withDensity f
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.withDensity_smul`：withDensity_smul (r : Real>=0∞) {f : α -
> Real>=0∞} (hf : Measurable f) : μ.withDensity (r • f) = r • μ.withDensity f
· 使用定理 `MeasureTheory.withDensity_one`：withDensity_one : μ.withDensity 1 = μ
· 使用定理 `MeasureTheory.Measure.restrict_toMeasurable`：restrict_toMeasurable (h : 
μ s != ∞) : μ.restrict (toMeasurable μ s) = μ.restrict s
· 使用定理 `MeasureTheory.measure_toMeasurable`：measure_toMeasurable (s : Set α) : μ
 (toMeasurable μ s) = μ s
· 使用定理 `ProbabilityTheory.cond.eq_1`：∀ {Ω : Type u_1} {m : MeasurableSpace Ω} (μ
 : MeasureTheory.Measure Ω) (s : Set Ω), μ[|s] = (μ s)⁻¹ • μ.restrict s
-/
theorem hasPDF {X : Ω → E} {s : Set E} (hns : μ s ≠ 0) (hnt : μ s ≠ ∞)
    (hu : IsUniform X s ℙ μ) : HasPDF X ℙ μ := by
  let t := toMeasurable μ s
  apply hasPDF_of_map_eq_withDensity (hu.aemeasurable hns hnt) (t.indicator ((μ t)⁻¹ • 1)) <|
    (measurable_one.aemeasurable.const_smul (μ t)⁻¹).indicator (measurableSet_toMeasurable μ s)
  rw [hu, withDensity_indicator (measurableSet_toMeasurable μ s), withDensity_smul _ measurable_one,
    withDensity_one, restrict_toMeasurable hnt, measure_toMeasurable, ProbabilityTheory.cond]
/-
**MeasureTheory.pdf.IsUniform.pdf_eq_zero_of_measure_eq_zero_or_top** 是 Mathlib 
中的一个定理，位于命名空间 `MeasureTheory.pdf.IsUniform`。
形式化陈述：pdf_eq_zero_of_measure_eq_zero_or_top {X : Ω -> E} {s : Set E} (hu : IsUni
form X s ℙ μ) (hμs : μ s = 0 ∨ μ s = ∞) : pdf X ℙ μ =ᵐ[μ] 0
参数：hu : IsUniform X s ℙ μ；hμs : μ s = 0 ∨ μ s = ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ENNReal.inv_zero`：0⁻¹ = ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.restrict_eq_zero`：restrict_eq_zero : μ.restrict s 
= 0 ↔ μ s = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `ENNReal.inv_top`：⊤⁻¹ = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
-/
theorem pdf_eq_zero_of_measure_eq_zero_or_top {X : Ω → E} {s : Set E}
    (hu : IsUniform X s ℙ μ) (hμs : μ s = 0 ∨ μ s = ∞) : pdf X ℙ μ =ᵐ[μ] 0 := by
  rcases hμs with H | H
  · simp only [IsUniform, ProbabilityTheory.cond, H, ENNReal.inv_zero, restrict_eq_zero.mpr H,
    smul_zero] at hu
    simp [pdf, hu]
  · simp only [IsUniform, ProbabilityTheory.cond, H, ENNReal.inv_top, zero_smul] at hu
    simp [pdf, hu]
/-
**MeasureTheory.pdf.IsUniform.pdf_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.pd
f.IsUniform`。
形式化陈述：pdf_eq {X : Ω -> E} {s : Set E} (hms : MeasurableSet s) (hu : IsUniform X 
s ℙ μ) : pdf X ℙ μ =ᵐ[μ] s.indicator ((μ s)⁻¹ • (1 : E -> Real>=0∞))
参数：hms : MeasurableSet s；hu : IsUniform X s ℙ μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.inv_top`：⊤⁻¹ = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Set.indicator_zero'`：∀ {α : Type u_1} (M : Type u_3) [inst : Zero M] {s 
: Set α}, s.indicator 0 = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.pdf.IsUniform.pdf_eq_zero_of_measure_eq_zero_or_top`：pdf_e
q_zero_of_measure_eq_zero_or_top {X : Ω -> E} {s : Set E} (hu : IsUniform X s ℙ 
μ) (hμs : μ s = 0 ∨ μ s = ∞) : pdf X ℙ μ =ᵐ[μ] 0
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.measure_eq_zero_iff_ae_notMem`：measure_eq_zero_iff_ae_notM
em {s : Set α} : μ s = 0 ↔ forallᵐ a ∂μ, a ∉ s
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ENNReal.inv_zero`：0⁻¹ = ⊤
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.pdf.IsUniform.hasPDF`：hasPDF {X : Ω -> E} {s : Set E} (hns
 : μ s != 0) (hnt : μ s != ∞) (hu : IsUniform X s ℙ μ) : HasPDF X ℙ μ
· 使用定理 `MeasureTheory.pdf.IsUniform.isProbabilityMeasure`：isProbabilityMeasure {
X : Ω -> E} {s : Set E} (hns : μ s != 0) (hnt : μ s != ∞) (hu : IsUniform X s ℙ 
μ) : IsProbabilityMeasure ℙ
· 使用定理 `MeasureTheory.pdf.eq_of_map_eq_withDensity`：eq_of_map_eq_withDensity [Is
FiniteMeasure ℙ] {X : Ω -> E} [HasPDF X ℙ μ] (f : E -> Real>=0∞) (hmf : AEMeasur
able f μ) : map X ℙ = μ.withDens…
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `AEMeasurable.indicator`：AEMeasurable.indicator (hfm : AEMeasurable f μ) 
{s} (hs : MeasurableSet s) : AEMeasurable (s.indicator f) μ
· 使用引理 `AEMeasurable.const_smul`：AEMeasurable.const_smul (hg : AEMeasurable g μ)
 (c : M) : AEMeasurable (c • g) μ
· 使用定理 `MeasurableSMul.toMeasurableConstSMul`：∀ {M : Type u_2} {α : Type u_3} {i
nst : SMul M α} {inst_1 : MeasurableSpace M} {inst_2 : MeasurableSpace α}   [sel
f : MeasurableSMul M α], M…
· 使用定理 `measurableSMul_of_mul`：∀ (M : Type u_2) [inst : Mul M] [inst_1 : Measura
bleSpace M] [MeasurableMul M], MeasurableSMul M M
· 使用定理 `MeasurableMul₂.toMeasurableMul`：∀ {M : Type u_2} [inst : MeasurableSpace
 M] [inst_1 : Mul M] [MeasurableMul₂ M], MeasurableMul M
（共 37 条，此处仅展示前 30 条）
-/
theorem pdf_eq {X : Ω → E} {s : Set E} (hms : MeasurableSet s)
    (hu : IsUniform X s ℙ μ) : pdf X ℙ μ =ᵐ[μ] s.indicator ((μ s)⁻¹ • (1 : E → ℝ≥0∞)) := by
  by_cases hnt : μ s = ∞
  · simp [pdf_eq_zero_of_measure_eq_zero_or_top hu (Or.inr hnt), hnt]
  by_cases hns : μ s = 0
  · filter_upwards [measure_eq_zero_iff_ae_notMem.mp hns,
      pdf_eq_zero_of_measure_eq_zero_or_top hu (Or.inl hns)] with x hx h'x
    simp [hx, h'x, hns]
  have : HasPDF X ℙ μ := hasPDF hns hnt hu
  have : IsProbabilityMeasure ℙ := isProbabilityMeasure hns hnt hu
  apply (eq_of_map_eq_withDensity _ _).mp
  · rw [hu, withDensity_indicator hms, withDensity_smul _ measurable_one, withDensity_one,
      ProbabilityTheory.cond]
  · exact (measurable_one.aemeasurable.const_smul (μ s)⁻¹).indicator hms
/-
**MeasureTheory.pdf.IsUniform.pdf_toReal_ae_eq** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.pdf.IsUniform`。
形式化陈述：pdf_toReal_ae_eq {X : Ω -> E} {s : Set E} (hms : MeasurableSet s) (hX : Is
Uniform X s ℙ μ) : (fun x => (pdf X ℙ μ x).toReal) =ᵐ[μ] fun x => (s.indicator (
(μ s)⁻¹ • (1 : E -> Real>=0∞)) x).toReal
参数：hms : MeasurableSet s；hX : IsUniform X s ℙ μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.fun_comp`：∀ {α : Type u} {β : Type v} {γ : Type w} {
f g : α → β} {l : Filter α}, f =ᶠ[l] g → ∀ (h : β → γ), h ∘ f =ᶠ[l] h ∘ g
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.pdf.IsUniform.pdf_eq`：pdf_eq {X : Ω -> E} {s : Set E} (hms
 : MeasurableSet s) (hu : IsUniform X s ℙ μ) : pdf X ℙ μ =ᵐ[μ] s.indicator ((μ s
)⁻¹ • (1 : E -> Real>=0∞…
-/
theorem pdf_toReal_ae_eq {X : Ω → E} {s : Set E} (hms : MeasurableSet s)
    (hX : IsUniform X s ℙ μ) :
    (fun x => (pdf X ℙ μ x).toReal) =ᵐ[μ] fun x =>
      (s.indicator ((μ s)⁻¹ • (1 : E → ℝ≥0∞)) x).toReal :=
  Filter.EventuallyEq.fun_comp (pdf_eq hms hX) ENNReal.toReal

variable {X : Ω → ℝ} {s : Set ℝ}
/-
**MeasureTheory.pdf.IsUniform.mul_pdf_integrable** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.pdf.IsUniform`。
形式化陈述：mul_pdf_integrable (hcs : IsCompact s) (huX : IsUniform X s ℙ) : Integrabl
e fun x : Real => x * (pdf X ℙ volume x).toReal
参数：hcs : IsCompact s；huX : IsUniform X s ℙ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MeasureTheory.Integrable.congr`：∀ {α : Type u_1} {ε : Type u_5} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace ε]   [ins
t_1 : ContinuousENor…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.pdf.IsUniform.pdf_eq_zero_of_measure_eq_zero_or_top`：pdf_e
q_zero_of_measure_eq_zero_or_top {X : Ω -> E} {s : Set E} (hu : IsUniform X s ℙ 
μ) (hμs : μ s = 0 ∨ μ s = ∞) : pdf X ℙ μ =ᵐ[μ] 0
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.pdf.IsUniform.isProbabilityMeasure`：isProbabilityMeasure {
X : Ω -> E} {s : Set E} (hns : μ s != 0) (hnt : μ s != ∞) (hu : IsUniform X s ℙ 
μ) : IsProbabilityMeasure ℙ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.AEStronglyMeasurable.mul`：∀ {α : Type u_1} {β : Type u_2} 
[inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measur
e α}   {f g : α → β} [inst_1…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `aestronglyMeasurable_id`：∀ {α : Type u_5} [inst : TopologicalSpace α] [T
opologicalSpace.PseudoMetrizableSpace α] {x : MeasurableSpace α}   [OpensMeasura
bleSpace α] […
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `AEMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst
 : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 : M…
· 使用定理 `AEMeasurable.ennreal_toReal`：AEMeasurable.ennreal_toReal {f : α -> Real>
=0∞} {μ : Measure α} (hf : AEMeasurable f μ) : AEMeasurable (fun x => ENNReal.to
Real (f x)) μ
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasureTheory.measurable_pdf`：measurable_pdf {m : MeasurableSpace Ω} (X 
: Ω -> E) (ℙ : Measure Ω) (μ : Measure E
· 使用定理 `MeasureTheory.pdf.hasFiniteIntegral_mul`：hasFiniteIntegral_mul {f : Real
 -> Real} {g : Real -> Real>=0∞} (hg : pdf X ℙ =ᵐ[volume] g) (hgi : ∫⁻ x, ‖f x‖ₑ
 * g x != ∞) : HasFiniteInteg…
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
（共 50 条，此处仅展示前 30 条）
-/
theorem mul_pdf_integrable (hcs : IsCompact s) (huX : IsUniform X s ℙ) :
    Integrable fun x : ℝ => x * (pdf X ℙ volume x).toReal := by
  by_cases hnt : volume s = 0 ∨ volume s = ∞
  · have I : Integrable (fun x ↦ x * ENNReal.toReal (0)) := by simp
    apply I.congr
    filter_upwards [pdf_eq_zero_of_measure_eq_zero_or_top huX hnt] with x hx
    simp [hx]
  simp only [not_or] at hnt
  have : IsProbabilityMeasure ℙ := isProbabilityMeasure hnt.1 hnt.2 huX
  constructor
  · exact aestronglyMeasurable_id.mul
      (measurable_pdf X ℙ).aemeasurable.ennreal_toReal.aestronglyMeasurable
  refine hasFiniteIntegral_mul (pdf_eq hcs.measurableSet huX) ?_
  set ind := (volume s)⁻¹ • (1 : ℝ → ℝ≥0∞)
  have : ∀ x, ‖x‖ₑ * s.indicator ind x = s.indicator (fun x => ‖x‖ₑ * ind x) x := fun x =>
    (s.indicator_mul_right (fun x => ↑‖x‖₊) ind).symm
  simp only [ind, this, lintegral_indicator hcs.measurableSet, mul_one, smul_eq_mul,
    Pi.one_apply, Pi.smul_apply]
  rw [lintegral_mul_const _ measurable_enorm]
  exact ENNReal.mul_ne_top (setLIntegral_lt_top_of_isCompact hnt.2 hcs continuous_nnnorm).ne
    (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.mpr hnt.1)).ne

/-- A real uniform random variable `X` with support `s` has expectation
`(λ s)⁻¹ * ∫ x in s, x ∂λ` where `λ` is the Lebesgue measure. -/
/-
**MeasureTheory.pdf.IsUniform.integral_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.pdf.IsUniform`。
形式化陈述：integral_eq (huX : IsUniform X s ℙ) : ∫ x, X x ∂ℙ = (volume s)⁻¹.toReal * 
∫ x in s, x
参数：huX : IsUniform X s ℙ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.integral_smul_measure`：integral_smul_measure (f : α -> G) 
(c : Real>=0∞) : ∫ x, f x ∂c • μ = c.toReal • ∫ x, f x ∂μ
· 使用定理 `MeasureTheory.integral_map`：integral_map {β} [MeasurableSpace β] {φ : α 
-> β} (hφ : AEMeasurable φ μ) {f : β -> G} (hfm : AEStronglyMeasurable f (Measur
e.map φ μ)) : ∫ …
· 使用定理 `aestronglyMeasurable_id`：∀ {α : Type u_5} [inst : TopologicalSpace α] [T
opologicalSpace.PseudoMetrizableSpace α] {x : MeasurableSpace α}   [OpensMeasura
bleSpace α] […
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `MeasureTheory.Measure.map_of_not_aemeasurable`：map_of_not_aemeasurable {
f : α -> β} {μ : Measure α} (hf : ¬AEMeasurable f μ) : μ.map f = 0
· 使用定理 `MeasureTheory.integral_zero_measure`：integral_zero_measure {m : Measurab
leSpace α} (f : α -> G) : (∫ x, f x ∂(0 : Measure α)) = 0
· 使用定理 `MeasureTheory.integral_non_aestronglyMeasurable`：integral_non_aestrongly
Measurable {f : α -> G} (h : ¬AEStronglyMeasurable f μ) : ∫ a, f a ∂μ = 0
· 使用定理 `aestronglyMeasurable_iff_aemeasurable`：∀ {α : Type u_1} {β : Type u_2} [
inst : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α
}   {f : α → β} [inst_1 : M…

--- 原说明 ---
A real uniform random variable `X` with support `s` has expectation
`(λ s)⁻¹ * ∫ x in s, x ∂λ` where `λ` is the Lebesgue measure.
-/
theorem integral_eq (huX : IsUniform X s ℙ) :
    ∫ x, X x ∂ℙ = (volume s)⁻¹.toReal * ∫ x in s, x := by
  rw [← smul_eq_mul, ← integral_smul_measure]
  dsimp only [IsUniform, ProbabilityTheory.cond] at huX
  rw [← huX]
  by_cases hX : AEMeasurable X ℙ
  · exact (integral_map hX aestronglyMeasurable_id).symm
  · rw [map_of_not_aemeasurable hX, integral_zero_measure, integral_non_aestronglyMeasurable]
    rwa [aestronglyMeasurable_iff_aemeasurable]

end IsUniform

variable {X : Ω → E}

/-
**MeasureTheory.pdf.IsUniform.cond** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.pdf.
IsUniform`。
形式化陈述：∀ {E : Type u_1} [inst : MeasurableSpace E] {μ : MeasureTheory.Measure E} 
{s : Set E},   MeasureTheory.pdf.IsUniform id s μ[|s] μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.map_id`：map_id : map id μ = μ
-/
lemma IsUniform.cond {s : Set E} :
    IsUniform (id : E → E) s (ProbabilityTheory.cond μ s) μ :=
  map_id

/-- The density of the uniform measure on a set with respect to itself. This allows us to abstract
away the choice of random variable and probability space. -/
/-
**MeasureTheory.pdf.uniformPDF** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.pdf`。
形式化陈述：uniformPDF (s : Set E) (x : E) (μ : Measure E
参数：s : Set E；x : E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The density of the uniform measure on a set with respect to itself. This allows 
us to abstract
away the choice of random variable and probability space.
-/
def uniformPDF (s : Set E) (x : E) (μ : Measure E := by volume_tac) : ℝ≥0∞ :=
  s.indicator ((μ s)⁻¹ • (1 : E → ℝ≥0∞)) x

/-- Check that indeed any uniform random variable has the uniformPDF. -/
/-
**MeasureTheory.pdf.uniformPDF_eq_pdf** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.p
df`。
形式化陈述：uniformPDF_eq_pdf {s : Set E} (hs : MeasurableSet s) (hu : pdf.IsUniform X
 s ℙ μ) : (fun x => uniformPDF s x μ) =ᵐ[μ] pdf X ℙ μ
参数：hs : MeasurableSet s；hu : pdf.IsUniform X s ℙ μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.pdf.IsUniform.pdf_eq`：pdf_eq {X : Ω -> E} {s : Set E} (hms
 : MeasurableSet s) (hu : IsUniform X s ℙ μ) : pdf X ℙ μ =ᵐ[μ] s.indicator ((μ s
)⁻¹ • (1 : E -> Real>=0∞…
· 使用引理 `MeasureTheory.ae_eq_refl`：ae_eq_refl (f : α -> β) : f =ᵐ[μ] f

--- 原说明 ---
Check that indeed any uniform random variable has the uniformPDF.
-/
lemma uniformPDF_eq_pdf {s : Set E} (hs : MeasurableSet s) (hu : pdf.IsUniform X s ℙ μ) :
    (fun x ↦ uniformPDF s x μ) =ᵐ[μ] pdf X ℙ μ :=
  (hu.pdf_eq hs).symm.trans (ae_eq_refl _)

open scoped Classical in
/-- Alternative way of writing the uniformPDF. -/
/-
**MeasureTheory.pdf.uniformPDF_ite** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.pdf`
。
形式化陈述：uniformPDF_ite {s : Set E} {x : E} : uniformPDF s x μ = if x in s then (μ 
s)⁻¹ else 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True

--- 原说明 ---
Alternative way of writing the uniformPDF.
-/
lemma uniformPDF_ite {s : Set E} {x : E} :
    uniformPDF s x μ = if x ∈ s then (μ s)⁻¹ else 0 := by
  norm_num [uniformPDF, Set.indicator]

end pdf

end MeasureTheory

namespace PMF

variable {α : Type*}

open scoped NNReal ENNReal

section UniformOfFinset

/-- Uniform distribution taking the same non-zero probability on the nonempty finset `s` -/
/-
**PMF.uniformOfFinset** 是 Mathlib 中的一个定义，位于命名空间 `PMF`。
形式化陈述：uniformOfFinset (s : Finset α) (hs : s.Nonempty) : PMF α
参数：s : Finset α；hs : s.Nonempty。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Uniform distribution taking the same non-zero probability on the nonempty finset
 `s`
-/
def uniformOfFinset (s : Finset α) (hs : s.Nonempty) : PMF α := by
  classical
  refine ofFinset (fun a => if a ∈ s then s.card⁻¹ else 0) s ?_ ?_
  · simp only [Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const, nsmul_eq_mul]
    have : (s.card : ℝ≥0∞) ≠ 0 := by
      simpa only [Ne, Nat.cast_eq_zero, Finset.card_eq_zero] using
        Finset.nonempty_iff_ne_empty.1 hs
    exact ENNReal.mul_inv_cancel this <| ENNReal.natCast_ne_top s.card
  · exact fun x hx => by simp only [hx, if_false]

variable {s : Finset α} (hs : s.Nonempty) {a : α}

open scoped Classical in
@[simp]
/-
**PMF.uniformOfFinset_apply** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：uniformOfFinset_apply (a : α) : uniformOfFinset s hs a = if a in s then (s
.card : Real>=0∞)⁻¹ else 0
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uniformOfFinset_apply (a : α) :
    uniformOfFinset s hs a = if a ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0 :=
  rfl
/-
**PMF.uniformOfFinset_apply_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：uniformOfFinset_apply_of_mem (ha : a in s) : uniformOfFinset s hs a = (s.c
ard : Real>=0∞)⁻¹
参数：ha : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem uniformOfFinset_apply_of_mem (ha : a ∈ s) : uniformOfFinset s hs a = (s.card : ℝ≥0∞)⁻¹ := by
  simp [ha]
/-
**PMF.uniformOfFinset_apply_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：uniformOfFinset_apply_of_notMem (ha : a ∉ s) : uniformOfFinset s hs a = 0
参数：ha : a ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem uniformOfFinset_apply_of_notMem (ha : a ∉ s) : uniformOfFinset s hs a = 0 := by simp [ha]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**PMF.support_uniformOfFinset** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：support_uniformOfFinset : (uniformOfFinset s hs).support = s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem support_uniformOfFinset : (uniformOfFinset s hs).support = s :=
  Set.ext
    (by
      let ⟨a, ha⟩ := hs
      simp [mem_support_iff])
/-
**PMF.mem_support_uniformOfFinset_iff** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：mem_support_uniformOfFinset_iff (a : α) : a in (uniformOfFinset s hs).supp
ort ↔ a in s
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PMF.support_uniformOfFinset`：support_uniformOfFinset : (uniformOfFinset 
s hs).support = s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_support_uniformOfFinset_iff (a : α) : a ∈ (uniformOfFinset s hs).support ↔ a ∈ s := by
  simp

section Measure

variable (t : Set α)

open scoped Classical in
@[simp]
/-
**PMF.toOuterMeasure_uniformOfFinset_apply** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：toOuterMeasure_uniformOfFinset_apply : (uniformOfFinset s hs).toOuterMeasu
re t = #{x in s | x in t} / #s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PMF.toOuterMeasure_apply`：toOuterMeasure_apply : p.toOuterMeasure s = ∑'
 x, s.indicator p x
· 使用定理 `tsum_congr`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [in
st_1 : TopologicalSpace α] {L : SummationFilter β}   {f g : β → α}, (∀ (b : β), 
…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `tsum_eq_sum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [i
nst_1 : TopologicalSpace α] {f : β → α}   {L : SummationFilter β} [L.LeAtTop] {s
 …
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
-/
theorem toOuterMeasure_uniformOfFinset_apply :
    (uniformOfFinset s hs).toOuterMeasure t = #{x ∈ s | x ∈ t} / #s :=
  calc
    (uniformOfFinset s hs).toOuterMeasure t = ∑' x, if x ∈ t then uniformOfFinset s hs x else 0 :=
      toOuterMeasure_apply (uniformOfFinset s hs) t
    _ = ∑' x, if x ∈ s ∧ x ∈ t then (#s : ℝ≥0∞)⁻¹ else 0 :=
      tsum_congr fun x => by simp_rw [uniformOfFinset_apply, ← ite_and, and_comm]
    _ = ∑ x ∈ s with x ∈ t, if x ∈ s ∧ x ∈ t then (#s : ℝ≥0∞)⁻¹ else 0 :=
      tsum_eq_sum fun _ hx => if_neg fun h => hx (Finset.mem_filter.2 h)
    _ = ∑ x ∈ s with x ∈ t, (#s : ℝ≥0∞)⁻¹ :=
      Finset.sum_congr rfl fun x hx => by
        have : x ∈ s ∧ x ∈ t := by simpa using hx
        simp only [this, and_self_iff, if_true]
    _ = #{x ∈ s | x ∈ t} / #s := by
        simp only [div_eq_mul_inv, Finset.sum_const, nsmul_eq_mul]

open scoped Classical in
@[simp]
/-
**PMF.toMeasure_uniformOfFinset_apply** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：toMeasure_uniformOfFinset_apply [MeasurableSpace α] (ht : MeasurableSet t)
 : (uniformOfFinset s hs).toMeasure t = #{x in s | x in t} / #s
参数：ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PMF.toMeasure_apply_eq_toOuterMeasure_apply`：toMeasure_apply_eq_toOuterM
easure_apply (hs : MeasurableSet s) : p.toMeasure s = p.toOuterMeasure s
· 使用定理 `PMF.toOuterMeasure_uniformOfFinset_apply`：toOuterMeasure_uniformOfFinset
_apply : (uniformOfFinset s hs).toOuterMeasure t = #{x in s | x in t} / #s
-/
theorem toMeasure_uniformOfFinset_apply [MeasurableSpace α] (ht : MeasurableSet t) :
    (uniformOfFinset s hs).toMeasure t = #{x ∈ s | x ∈ t} / #s :=
  (toMeasure_apply_eq_toOuterMeasure_apply _ ht).trans (toOuterMeasure_uniformOfFinset_apply hs t)

end Measure

end UniformOfFinset

section UniformOfFintype

/-- The uniform pmf taking the same uniform value on all of the fintype `α` -/
/-
**PMF.uniformOfFintype** 是 Mathlib 中的一个定义，位于命名空间 `PMF`。
形式化陈述：uniformOfFintype (α : Type*) [Fintype α] [Nonempty α] : PMF α
参数：α : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.univ_nonempty`：univ_nonempty [Nonempty α] : (univ : Finset α).Non
empty

--- 原说明 ---
The uniform pmf taking the same uniform value on all of the fintype `α`
-/
def uniformOfFintype (α : Type*) [Fintype α] [Nonempty α] : PMF α :=
  uniformOfFinset Finset.univ Finset.univ_nonempty

variable [Fintype α] [Nonempty α]

@[simp]
/-
**PMF.uniformOfFintype_apply** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：uniformOfFintype_apply (a : α) : uniformOfFintype α a = (Fintype.card α : 
Real>=0∞)⁻¹
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem uniformOfFintype_apply (a : α) : uniformOfFintype α a = (Fintype.card α : ℝ≥0∞)⁻¹ := by
  simp [uniformOfFintype, Finset.mem_univ, uniformOfFinset_apply]

@[simp]
/-
**PMF.support_uniformOfFintype** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：support_uniformOfFintype (α : Type*) [Fintype α] [Nonempty α] : (uniformOf
Fintype α).support = ⊤
参数：α : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PMF.uniformOfFintype_apply`：uniformOfFintype_apply (a : α) : uniformOfFi
ntype α a = (Fintype.card α : Real>=0∞)⁻¹
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem support_uniformOfFintype (α : Type*) [Fintype α] [Nonempty α] :
    (uniformOfFintype α).support = ⊤ :=
  Set.ext fun x => by simp [mem_support_iff]
/-
**PMF.mem_support_uniformOfFintype** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：mem_support_uniformOfFintype (a : α) : a in (uniformOfFintype α).support
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PMF.support_uniformOfFintype`：support_uniformOfFintype (α : Type*) [Fint
ype α] [Nonempty α] : (uniformOfFintype α).support = ⊤
-/
theorem mem_support_uniformOfFintype (a : α) : a ∈ (uniformOfFintype α).support := by simp

section Measure

variable (s : Set α)

/-
**PMF.toOuterMeasure_uniformOfFintype_apply** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：toOuterMeasure_uniformOfFintype_apply [Fintype s] : (uniformOfFintype α).t
oOuterMeasure s = Fintype.card s / Fintype.card α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.univ_nonempty`：univ_nonempty [Nonempty α] : (univ : Finset α).Non
empty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PMF.uniformOfFintype.eq_1`：∀ (α : Type u_2) [inst : Fintype α] [inst_1 :
 Nonempty α], PMF.uniformOfFintype α = PMF.uniformOfFinset Finset.univ ⋯
· 使用定理 `PMF.toOuterMeasure_uniformOfFinset_apply`：toOuterMeasure_uniformOfFinset
_apply : (uniformOfFinset s hs).toOuterMeasure t = #{x in s | x in t} / #s
· 使用定理 `Fintype.card_subtype`：Fintype.card_subtype [Fintype α] (p : α -> Prop) [
Fintype {a // p a}] [DecidablePred p] : Fintype.card { x // p x } = #{x | p x}
· 使用定理 `Finset.card_univ`：Finset.card_univ [Fintype α] : #(univ : Finset α) = Fi
ntype.card α
-/
theorem toOuterMeasure_uniformOfFintype_apply [Fintype s] :
    (uniformOfFintype α).toOuterMeasure s = Fintype.card s / Fintype.card α := by
  classical
  rw [uniformOfFintype, toOuterMeasure_uniformOfFinset_apply, Fintype.card_subtype,
    Finset.card_univ]
/-
**PMF.toMeasure_uniformOfFintype_apply** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：toMeasure_uniformOfFintype_apply [MeasurableSpace α] (hs : MeasurableSet s
) [Fintype s] : (uniformOfFintype α).toMeasure s = Fintype.card s / Fintype.card
 α
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PMF.toMeasure_uniformOfFinset_apply`：toMeasure_uniformOfFinset_apply [Me
asurableSpace α] (ht : MeasurableSet t) : (uniformOfFinset s hs).toMeasure t = #
{x in s | x in t} / #s
· 使用定理 `Finset.univ_nonempty`：univ_nonempty [Nonempty α] : (univ : Finset α).Non
empty
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fintype.card_subtype`：Fintype.card_subtype [Fintype α] (p : α -> Prop) [
Fintype {a // p a}] [DecidablePred p] : Fintype.card { x // p x } = #{x | p x}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toMeasure_uniformOfFintype_apply [MeasurableSpace α] (hs : MeasurableSet s) [Fintype s] :
    (uniformOfFintype α).toMeasure s = Fintype.card s / Fintype.card α := by
  classical
  simp [uniformOfFintype, Fintype.card_subtype, hs]

end Measure

end UniformOfFintype

section OfMultiset

open scoped Classical in
/-- Given a non-empty multiset `s` we construct the `PMF` which sends `a` to the fraction of
  elements in `s` that are `a`. -/
/-
**PMF.ofMultiset** 是 Mathlib 中的一个定义，位于命名空间 `PMF`。
形式化陈述：ofMultiset (s : Multiset α) (hs : s != 0) : PMF α
参数：s : Multiset α；hs : s != 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a non-empty multiset `s` we construct the `PMF` which sends `a` to the fra
ction of
  elements in `s` that are `a`.
-/
def ofMultiset (s : Multiset α) (hs : s ≠ 0) : PMF α :=
  ⟨fun a => s.count a / (Multiset.card s),
    ENNReal.summable.hasSum_iff.2
      (calc
        (∑' b : α, (s.count b : ℝ≥0∞) / (Multiset.card s))
          = (Multiset.card s : ℝ≥0∞)⁻¹ * ∑' b, (s.count b : ℝ≥0∞) := by
            simp_rw [ENNReal.div_eq_inv_mul, ENNReal.tsum_mul_left]
        _ = (Multiset.card s : ℝ≥0∞)⁻¹ * ∑ b ∈ s.toFinset, (s.count b : ℝ≥0∞) :=
          (congr_arg (fun x => (Multiset.card s : ℝ≥0∞)⁻¹ * x)
            (tsum_eq_sum fun a ha =>
              Nat.cast_eq_zero.2 <| by rwa [Multiset.count_eq_zero, ← Multiset.mem_toFinset]))
        _ = 1 := by
          rw [← Nat.cast_sum, Multiset.toFinset_sum_count_eq s,
            ENNReal.inv_mul_cancel (Nat.cast_ne_zero.2 (hs ∘ Multiset.card_eq_zero.1))
              (ENNReal.natCast_ne_top _)]
        )⟩

variable {s : Multiset α} (hs : s ≠ 0)

open scoped Classical in
@[simp]
/-
**PMF.ofMultiset_apply** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：ofMultiset_apply (a : α) : ofMultiset s hs a = s.count a / (Multiset.card 
s)
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofMultiset_apply (a : α) : ofMultiset s hs a = s.count a / (Multiset.card s) :=
  rfl

open scoped Classical in
@[simp]
/-
**PMF.support_ofMultiset** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：support_ofMultiset : (ofMultiset s hs).support = s.toFinset
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem support_ofMultiset : (ofMultiset s hs).support = s.toFinset :=
  Set.ext (by simp [mem_support_iff])

open scoped Classical in
/-
**PMF.mem_support_ofMultiset_iff** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：mem_support_ofMultiset_iff (a : α) : a in (ofMultiset s hs).support ↔ a in
 s.toFinset
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PMF.support_ofMultiset`：support_ofMultiset : (ofMultiset s hs).support =
 s.toFinset
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_support_ofMultiset_iff (a : α) : a ∈ (ofMultiset s hs).support ↔ a ∈ s.toFinset := by
  simp
/-
**PMF.ofMultiset_apply_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：ofMultiset_apply_of_notMem {a : α} (ha : a ∉ s) : ofMultiset s hs a = 0
参数：ha : a ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
theorem ofMultiset_apply_of_notMem {a : α} (ha : a ∉ s) : ofMultiset s hs a = 0 := by
  simpa only [ofMultiset_apply, ENNReal.div_eq_zero_iff, Nat.cast_eq_zero, Multiset.count_eq_zero,
    ENNReal.natCast_ne_top, or_false] using ha

section Measure

variable (t : Set α)

open scoped Classical in
@[simp]
/-
**PMF.toOuterMeasure_ofMultiset_apply** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：toOuterMeasure_ofMultiset_apply : (ofMultiset s hs).toOuterMeasure t = (∑'
 x, (s.filter (· in t)).count x : Real>=0∞) / (Multiset.card s)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PMF.toOuterMeasure_apply`：toOuterMeasure_apply : p.toOuterMeasure s = ∑'
 x, s.indicator p x
· 使用定理 `tsum_congr`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [in
st_1 : TopologicalSpace α] {L : SummationFilter β}   {f g : β → α}, (∀ (b : β), 
…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Multiset.count_filter_of_pos`：count_filter_of_pos {p} [DecidablePred p] 
{a} {s : Multiset α} (h : p a) : count a (filter p s) = count a s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Multiset.count_eq_zero_of_notMem`：count_eq_zero_of_notMem {a : α} {s : M
ultiset α} (h : a ∉ s) : count a s = 0
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem toOuterMeasure_ofMultiset_apply :
    (ofMultiset s hs).toOuterMeasure t =
      (∑' x, (s.filter (· ∈ t)).count x : ℝ≥0∞) / (Multiset.card s) := by
  simp_rw [div_eq_mul_inv, ← ENNReal.tsum_mul_right, toOuterMeasure_apply]
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ t <;> simp [Set.indicator, hx, div_eq_mul_inv]

open scoped Classical in
@[simp]
/-
**PMF.toMeasure_ofMultiset_apply** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：toMeasure_ofMultiset_apply [MeasurableSpace α] (ht : MeasurableSet t) : (o
fMultiset s hs).toMeasure t = (∑' x, (s.filter (· in t)).count x : Real>=0∞) / (
Multiset.card s)
参数：ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PMF.toMeasure_apply_eq_toOuterMeasure_apply`：toMeasure_apply_eq_toOuterM
easure_apply (hs : MeasurableSet s) : p.toMeasure s = p.toOuterMeasure s
· 使用定理 `PMF.toOuterMeasure_ofMultiset_apply`：toOuterMeasure_ofMultiset_apply : (
ofMultiset s hs).toOuterMeasure t = (∑' x, (s.filter (· in t)).count x : Real>=0
∞) / (Multiset.card s)
-/
theorem toMeasure_ofMultiset_apply [MeasurableSpace α] (ht : MeasurableSet t) :
    (ofMultiset s hs).toMeasure t = (∑' x, (s.filter (· ∈ t)).count x : ℝ≥0∞) / (Multiset.card s) :=
  (toMeasure_apply_eq_toOuterMeasure_apply _ ht).trans (toOuterMeasure_ofMultiset_apply hs t)

end Measure

end OfMultiset

end PMF

