/-
Copyright (c) 2023 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker
-/
module

public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# The multiplicative and additive convolution of measures

In this file we define and prove properties about the convolutions of two measures.

## Main definitions

* `MeasureTheory.Measure.mconv`: The multiplicative convolution of two measures: the map of `*`
  under the product measure.
* `MeasureTheory.Measure.conv`: The additive convolution of two measures: the map of `+`
  under the product measure.
-/

@[expose] public section

namespace MeasureTheory

namespace Measure
open scoped ENNReal

variable {M : Type*} [Monoid M] [MeasurableSpace M]

/-- Multiplicative convolution of measures. -/
@[to_additive /-- Additive convolution of measures. -/]
/-
**MeasureTheory.Measure.mconv** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：mconv (μ : Measure M) (ν : Measure M) : Measure M
参数：μ : Measure M；ν : Measure M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplicative convolution of measures.
-/
noncomputable def mconv (μ : Measure M) (ν : Measure M) :
    Measure M := Measure.map (fun x : M × M ↦ x.1 * x.2) (μ.prod ν)

/-- Scoped notation for the multiplicative convolution of measures. -/
scoped[MeasureTheory] infixr:80 " ∗ₘ " => MeasureTheory.Measure.mconv

/-- Scoped notation for the additive convolution of measures. -/
scoped[MeasureTheory] infixr:80 " ∗ " => MeasureTheory.Measure.conv

@[to_additive]
/-
**MeasureTheory.Measure.lintegral_mconv_eq_lintegral_prod** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.Measure`。
形式化陈述：lintegral_mconv_eq_lintegral_prod [MeasurableMul₂ M] {μ ν : Measure M} {f 
: M -> Real>=0∞} (hf : Measurable f) : ∫⁻ z, f z ∂(μ ∗ₘ ν) = ∫⁻ z, f (z.1 * z.2)
 ∂(μ.prod ν)
参数：hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.mconv.eq_1`：∀ {M : Type u_1} [inst : Monoid M] [in
st_1 : MeasurableSpace M] (μ ν : MeasureTheory.Measure M),   μ.mconv ν = Measure
Theory.Measure.map (fu…
· 使用定理 `MeasureTheory.lintegral_map`：lintegral_map {f : β -> Real>=0∞} {g : α ->
 β} (hf : Measurable f) (hg : Measurable g) : ∫⁻ a, f a ∂map g μ = ∫⁻ a, f (g a)
 ∂μ
· 使用定理 `MeasurableMul₂.measurable_mul`：∀ {M : Type u_2} {inst : MeasurableSpace 
M} {inst_1 : Mul M} [self : MeasurableMul₂ M], Measurable fun p => p.1 * p.2
-/
theorem lintegral_mconv_eq_lintegral_prod [MeasurableMul₂ M] {μ ν : Measure M}
    {f : M → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z, f z ∂(μ ∗ₘ ν) = ∫⁻ z, f (z.1 * z.2) ∂(μ.prod ν) := by
  rw [mconv, lintegral_map hf measurable_mul]

@[to_additive]
/-
**MeasureTheory.Measure.lintegral_mconv** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Measure`。
形式化陈述：lintegral_mconv [MeasurableMul₂ M] {μ ν : Measure M} [SFinite ν] {f : M ->
 Real>=0∞} (hf : Measurable f) : ∫⁻ z, f z ∂(μ ∗ₘ ν) = ∫⁻ x, ∫⁻ y, f (x * y) ∂ν 
∂μ
参数：hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.lintegral_mconv_eq_lintegral_prod`：lintegral_mconv
_eq_lintegral_prod [MeasurableMul₂ M] {μ ν : Measure M} {f : M -> Real>=0∞} (hf 
: Measurable f) : ∫⁻ z, f z ∂(μ ∗ₘ ν) = ∫⁻ z,…
· 使用定理 `MeasureTheory.lintegral_prod`：lintegral_prod (f : α × β -> Real>=0∞) (hf
 : AEMeasurable f (μ.prod ν)) : ∫⁻ z, f z ∂μ.prod ν = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ
· 使用定理 `Measurable.comp_aemeasurable'`：Measurable.comp_aemeasurable' [Measurable
Space δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) :
 AEMeasurable (fun …
· 使用定理 `AEMeasurable.fun_mul`：∀ {M : Type u_2} {α : Type u_3} [inst : Measurable
Space M] [inst_1 : Mul M] {m : MeasurableSpace α} {f g : α → M}   {μ : MeasureTh
eory.Measu…
· 使用定理 `AEMeasurable.fst`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} {m0 : M
easurableSpace α} [inst : MeasurableSpace β]   [inst_1 : MeasurableSpace γ] {μ :
 Measu…
· 使用定理 `aemeasurable_id`：aemeasurable_id : AEMeasurable id μ
· 使用定理 `AEMeasurable.snd`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} {m0 : M
easurableSpace α} [inst : MeasurableSpace β]   [inst_1 : MeasurableSpace γ] {μ :
 Measu…
-/
theorem lintegral_mconv [MeasurableMul₂ M] {μ ν : Measure M} [SFinite ν]
    {f : M → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z, f z ∂(μ ∗ₘ ν) = ∫⁻ x, ∫⁻ y, f (x * y) ∂ν ∂μ := by
  rw [lintegral_mconv_eq_lintegral_prod hf, lintegral_prod _ (by fun_prop)]

@[to_additive]
/-
**MeasureTheory.Measure.dirac_mconv** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Mea
sure`。
形式化陈述：dirac_mconv [MeasurableMul₂ M] (x : M) (μ : Measure M) [SFinite μ] : (dira
c x) ∗ₘ μ = μ.map (fun y => x * y)
参数：x : M；μ : Measure M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.dirac_prod`：dirac_prod (x : α) : (dirac x).prod ν 
= map (Prod.mk x) ν
· 使用定理 `MeasureTheory.Measure.map_map`：map_map {g : β -> γ} {f : α -> β} (hg : M
easurable g) (hf : Measurable f) : (μ.map f).map g = μ.map (g ∘ f)
· 使用定理 `Measurable.fun_mul`：∀ {M : Type u_2} {α : Type u_3} [inst : MeasurableSp
ace M] [inst_1 : Mul M] {m : MeasurableSpace α} {f g : α → M}   [MeasurableMul₂ 
M], Meas…
· 使用定理 `Measurable.fst`：Measurable.fst {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).1
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `Measurable.snd`：Measurable.snd {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).2
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma dirac_mconv [MeasurableMul₂ M] (x : M) (μ : Measure M) [SFinite μ] :
    (dirac x) ∗ₘ μ = μ.map (fun y ↦ x * y) := by
  unfold mconv
  rw [dirac_prod, map_map (by fun_prop) (by fun_prop)]
  simp [Function.comp_def]

@[to_additive]
/-
**MeasureTheory.Measure.mconv_dirac** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Mea
sure`。
形式化陈述：mconv_dirac [MeasurableMul₂ M] (μ : Measure M) [SFinite μ] (x : M) : μ ∗ₘ 
(dirac x) = μ.map (fun y => y * x)
参数：μ : Measure M；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.prod_dirac`：prod_dirac (y : β) : μ.prod (dirac y) 
= map (fun x => (x, y)) μ
· 使用定理 `MeasureTheory.Measure.map_map`：map_map {g : β -> γ} {f : α -> β} (hg : M
easurable g) (hf : Measurable f) : (μ.map f).map g = μ.map (g ∘ f)
· 使用定理 `Measurable.fun_mul`：∀ {M : Type u_2} {α : Type u_3} [inst : MeasurableSp
ace M] [inst_1 : Mul M] {m : MeasurableSpace α} {f g : α → M}   [MeasurableMul₂ 
M], Meas…
· 使用定理 `Measurable.fst`：Measurable.fst {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).1
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `Measurable.snd`：Measurable.snd {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).2
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mconv_dirac [MeasurableMul₂ M] (μ : Measure M) [SFinite μ] (x : M) :
    μ ∗ₘ (dirac x) = μ.map (fun y ↦ y * x) := by
  unfold mconv
  rw [prod_dirac, map_map (by fun_prop) (by fun_prop)]
  simp [Function.comp_def]

@[to_additive (attr := simp)]
/-
**MeasureTheory.Measure.dirac_mconv_dirac** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：dirac_mconv_dirac [MeasurableMul₂ M] (x y : M) : (dirac x) ∗ₘ (dirac y) = 
dirac (x * y)
参数：x y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.mconv_dirac`：mconv_dirac [MeasurableMul₂ M] (μ : M
easure M) [SFinite μ] (x : M) : μ ∗ₘ (dirac x) = μ.map (fun y => y * x)
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.Measure.dirac.instSigmaFinite`：∀ {α : Type u_1} [inst : Me
asurableSpace α] {a : α}, MeasureTheory.SigmaFinite (MeasureTheory.Measure.dirac
 a)
· 使用定理 `MeasureTheory.Measure.map_dirac'`：map_dirac' {f : α -> β} (hf : Measurab
le f) (a : α) : (dirac a).map f = dirac (f a)
· 使用定理 `Measurable.mul_const`：Measurable.mul_const [MeasurableMul M] (hf : Measu
rable f) (c : M) : Measurable fun x => f x * c
· 使用定理 `MeasurableMul₂.toMeasurableMul`：∀ {M : Type u_2} [inst : MeasurableSpace
 M] [inst_1 : Mul M] [MeasurableMul₂ M], MeasurableMul M
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
-/
lemma dirac_mconv_dirac [MeasurableMul₂ M] (x y : M) :
    (dirac x) ∗ₘ (dirac y) = dirac (x * y) := by
  rw [mconv_dirac, map_dirac' (by fun_prop)]

/-- Convolution of the dirac measure at 1 with a measure μ returns μ. -/
@[to_additive (attr := simp)
/-- Convolution of the dirac measure at 0 with a measure μ returns μ. -/]
/-
**MeasureTheory.Measure.dirac_one_mconv** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Measure`。
形式化陈述：dirac_one_mconv [MeasurableMul₂ M] (μ : Measure M) [SFinite μ] : (dirac 1)
 ∗ₘ μ = μ
参数：μ : Measure M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.dirac_mconv`：dirac_mconv [MeasurableMul₂ M] (x : M
) (μ : Measure M) [SFinite μ] : (dirac x) ∗ₘ μ = μ.map (fun y => x * y)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MeasureTheory.Measure.map_id'`：map_id' : map (fun x => x) μ = μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dirac_one_mconv [MeasurableMul₂ M] (μ : Measure M) [SFinite μ] :
    (dirac 1) ∗ₘ μ = μ := by
  simp [dirac_mconv]

/-- Convolution of a measure μ with the dirac measure at 1 returns μ. -/
@[to_additive (attr := simp)
/-- Convolution of a measure μ with the dirac measure at 0 returns μ. -/]
/-
**MeasureTheory.Measure.mconv_dirac_one** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Measure`。
形式化陈述：mconv_dirac_one [MeasurableMul₂ M] (μ : Measure M) [SFinite μ] : μ ∗ₘ (dir
ac 1) = μ
参数：μ : Measure M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.mconv_dirac`：mconv_dirac [MeasurableMul₂ M] (μ : M
easure M) [SFinite μ] (x : M) : μ ∗ₘ (dirac x) = μ.map (fun y => y * x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MeasureTheory.Measure.map_id'`：map_id' : map (fun x => x) μ = μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mconv_dirac_one [MeasurableMul₂ M]
    (μ : Measure M) [SFinite μ] : μ ∗ₘ (dirac 1) = μ := by
  simp [mconv_dirac]

/-- Convolution of the zero measure with a measure μ returns the zero measure. -/
@[to_additive (attr := simp) /-- Convolution of the zero measure with a measure μ returns
the zero measure. -/]
/-
**MeasureTheory.Measure.zero_mconv** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Meas
ure`。
形式化陈述：zero_mconv (μ : Measure M) : (0 : Measure M) ∗ₘ μ = (0 : Measure M)
参数：μ : Measure M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.zero_prod`：zero_prod (ν : Measure β) : (0 : Measur
e α).prod ν = 0
· 使用定理 `MeasureTheory.Measure.map_zero`：∀ {α : Type u_1} {β : Type u_2} {mα : Me
asurableSpace α} {mβ : MeasurableSpace β} (f : α → β),   MeasureTheory.Measure.m
ap f 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zero_mconv (μ : Measure M) : (0 : Measure M) ∗ₘ μ = (0 : Measure M) := by
  unfold mconv
  simp

/-- Convolution of a measure μ with the zero measure returns the zero measure. -/
@[to_additive (attr := simp) /-- Convolution of a measure μ with the zero measure returns the zero
measure. -/]
/-
**MeasureTheory.Measure.mconv_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Meas
ure`。
形式化陈述：mconv_zero (μ : Measure M) : μ ∗ₘ (0 : Measure M) = (0 : Measure M)
参数：μ : Measure M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.prod_zero`：prod_zero (μ : Measure α) : μ.prod (0 :
 Measure β) = 0
· 使用定理 `MeasureTheory.Measure.map_zero`：∀ {α : Type u_1} {β : Type u_2} {mα : Me
asurableSpace α} {mβ : MeasurableSpace β} (f : α → β),   MeasureTheory.Measure.m
ap f 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mconv_zero (μ : Measure M) : μ ∗ₘ (0 : Measure M) = (0 : Measure M) := by
  unfold mconv
  simp

-- `mconv_smul_right` needs an instance to get `SFinite (c • ν)` from `SFinite ν`,
-- hence it is placed in the `WithDensity` file, where the instance is defined.
@[to_additive conv_smul_left]
/-
**MeasureTheory.Measure.mconv_smul_left** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Measure`。
形式化陈述：mconv_smul_left (μ : Measure M) (ν : Measure M) [SFinite ν] (s : Real>=0∞)
 : (s • μ) ∗ₘ ν = s • (μ ∗ₘ ν)
参数：μ : Measure M；ν : Measure M；s : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.map_smul`：∀ {α : Type u_1} {β : Type u_2} {mα : Me
asurableSpace α} {mβ : MeasurableSpace β} {R : Type u_4} [inst : SMul R ENNReal]
   [inst_1 : IsScala…
· 使用引理 `MeasureTheory.Measure.prod_smul_left`：prod_smul_left {μ : Measure α} {R 
: Type*} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (c : R) : (c • μ)
.prod ν = c • (μ.prod ν)
-/
theorem mconv_smul_left (μ : Measure M) (ν : Measure M) [SFinite ν] (s : ℝ≥0∞) :
    (s • μ) ∗ₘ ν = s • (μ ∗ₘ ν) := by
  unfold mconv
  rw [← Measure.map_smul, Measure.prod_smul_left]

@[to_additive]
/-
**MeasureTheory.Measure.mconv_add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measu
re`。
形式化陈述：mconv_add [MeasurableMul₂ M] (μ : Measure M) (ν : Measure M) (ρ : Measure 
M) [SFinite μ] [SFinite ν] [SFinite ρ] : μ ∗ₘ (ν + ρ) = μ ∗ₘ ν + μ ∗ₘ ρ
参数：μ : Measure M；ν : Measure M；ρ : Measure M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.prod_add`：prod_add (ν' : Measure β) [SFinite ν'] :
 μ.prod (ν + ν') = μ.prod ν + μ.prod ν'
· 使用定理 `MeasureTheory.Measure.map_add`：∀ {α : Type u_1} {β : Type u_2} {mα : Mea
surableSpace α} {mβ : MeasurableSpace β} (μ ν : MeasureTheory.Measure α)   {f : 
α → β},   Measurabl…
· 使用定理 `Measurable.fun_mul`：∀ {M : Type u_2} {α : Type u_3} [inst : MeasurableSp
ace M] [inst_1 : Mul M] {m : MeasurableSpace α} {f g : α → M}   [MeasurableMul₂ 
M], Meas…
· 使用定理 `Measurable.fst`：Measurable.fst {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).1
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `Measurable.snd`：Measurable.snd {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).2
-/
theorem mconv_add [MeasurableMul₂ M] (μ : Measure M) (ν : Measure M) (ρ : Measure M) [SFinite μ]
    [SFinite ν] [SFinite ρ] : μ ∗ₘ (ν + ρ) = μ ∗ₘ ν + μ ∗ₘ ρ := by
  unfold mconv
  rw [prod_add, Measure.map_add]
  fun_prop

@[to_additive]
/-
**MeasureTheory.Measure.add_mconv** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measu
re`。
形式化陈述：add_mconv [MeasurableMul₂ M] (μ : Measure M) (ν : Measure M) (ρ : Measure 
M) [SFinite μ] [SFinite ν] [SFinite ρ] : (μ + ν) ∗ₘ ρ = μ ∗ₘ ρ + ν ∗ₘ ρ
参数：μ : Measure M；ν : Measure M；ρ : Measure M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.add_prod`：add_prod (μ' : Measure α) [SFinite μ'] :
 (μ + μ').prod ν = μ.prod ν + μ'.prod ν
· 使用定理 `MeasureTheory.Measure.map_add`：∀ {α : Type u_1} {β : Type u_2} {mα : Mea
surableSpace α} {mβ : MeasurableSpace β} (μ ν : MeasureTheory.Measure α)   {f : 
α → β},   Measurabl…
· 使用定理 `Measurable.fun_mul`：∀ {M : Type u_2} {α : Type u_3} [inst : MeasurableSp
ace M] [inst_1 : Mul M] {m : MeasurableSpace α} {f g : α → M}   [MeasurableMul₂ 
M], Meas…
· 使用定理 `Measurable.fst`：Measurable.fst {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).1
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `Measurable.snd`：Measurable.snd {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).2
-/
theorem add_mconv [MeasurableMul₂ M] (μ : Measure M) (ν : Measure M) (ρ : Measure M) [SFinite μ]
    [SFinite ν] [SFinite ρ] : (μ + ν) ∗ₘ ρ = μ ∗ₘ ρ + ν ∗ₘ ρ := by
  unfold mconv
  rw [add_prod, Measure.map_add]
  fun_prop

/-- To get commutativity, we need the underlying multiplication to be commutative. -/
@[to_additive /-- To get commutativity, we need the underlying addition to be commutative. -/]
/-
**MeasureTheory.Measure.mconv_comm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Meas
ure`。
形式化陈述：mconv_comm {M : Type*} [CommMonoid M] [MeasurableSpace M] [MeasurableMul₂ 
M] (μ : Measure M) (ν : Measure M) [SFinite μ] [SFinite ν] : μ ∗ₘ ν = ν ∗ₘ μ
参数：μ : Measure M；ν : Measure M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.prod_swap`：prod_swap : map Prod.swap (μ.prod ν) = 
ν.prod μ
· 使用定理 `MeasureTheory.Measure.map_map`：map_map {g : β -> γ} {f : α -> β} (hg : M
easurable g) (hf : Measurable f) : (μ.map f).map g = μ.map (g ∘ f)
· 使用定理 `Measurable.fun_mul`：∀ {M : Type u_2} {α : Type u_3} [inst : MeasurableSp
ace M] [inst_1 : Mul M] {m : MeasurableSpace α} {f g : α → M}   [MeasurableMul₂ 
M], Meas…
· 使用定理 `Measurable.fst`：Measurable.fst {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).1
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `Measurable.snd`：Measurable.snd {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).2
· 使用定理 `measurable_swap`：measurable_swap : Measurable (Prod.swap : α × β -> β × 
α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
To get commutativity, we need the underlying multiplication to be commutative.
-/
theorem mconv_comm {M : Type*} [CommMonoid M] [MeasurableSpace M] [MeasurableMul₂ M] (μ : Measure M)
    (ν : Measure M) [SFinite μ] [SFinite ν] : μ ∗ₘ ν = ν ∗ₘ μ := by
  unfold mconv
  rw [← prod_swap, map_map (by fun_prop)]
  · simp [Function.comp_def, mul_comm]
  fun_prop

/-- The convolution of s-finite measures is s-finite. -/
@[to_additive /-- The convolution of s-finite measures is s-finite. -/]
/-
**MeasureTheory.Measure.sfinite_mconv_of_sfinite** 是 Mathlib 中的一个实例，位于命名空间 `Meas
ureTheory.Measure`。
形式化陈述：sfinite_mconv_of_sfinite (μ : Measure M) (ν : Measure M) [SFinite μ] [SFin
ite ν] : SFinite (μ ∗ₘ ν)
参数：μ : Measure M；ν : Measure M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The convolution of s-finite measures is s-finite.
-/
instance sfinite_mconv_of_sfinite (μ : Measure M) (ν : Measure M) [SFinite μ] [SFinite ν] :
    SFinite (μ ∗ₘ ν) := inferInstanceAs <| SFinite ((μ.prod ν).map fun (x : M × M) ↦ x.1 * x.2)

@[to_additive]
/-
**MeasureTheory.Measure.finite_of_finite_mconv** 是 Mathlib 中的一个实例，位于命名空间 `Measur
eTheory.Measure`。
形式化陈述：finite_of_finite_mconv (μ : Measure M) (ν : Measure M) [IsFiniteMeasure μ]
 [IsFiniteMeasure ν] : IsFiniteMeasure (μ ∗ₘ ν)
参数：μ : Measure M；ν : Measure M。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsFiniteMeasure.measure_univ_lt_top`：∀ {α : Type u_1} {m0 
: MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsFinit
eMeasure μ],   μ Set.univ < ⊤
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用定理 `MeasureTheory.Measure.prod.instIsFiniteMeasure`：∀ {α : Type u_4} {β : Ty
pe u_5} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (μ : MeasureTheory.Mea
sure α)   (ν : MeasureTheory.Measure…
-/
instance finite_of_finite_mconv (μ : Measure M) (ν : Measure M) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] : IsFiniteMeasure (μ ∗ₘ ν) := by
  have h : (μ ∗ₘ ν) Set.univ < ⊤ := by
    unfold mconv
    exact IsFiniteMeasure.measure_univ_lt_top
  exact { measure_univ_lt_top := h }

/-- Convolution is associative. -/
@[to_additive /-- Convolution is associative. -/]
/-
**MeasureTheory.Measure.mconv_assoc** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Mea
sure`。
形式化陈述：mconv_assoc [MeasurableMul₂ M] (μ ν ρ : Measure M) [SFinite ν] [SFinite ρ]
 : (μ ∗ₘ ν) ∗ₘ ρ = μ ∗ₘ (ν ∗ₘ ρ)
参数：μ ν ρ : Measure M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext_of_lintegral`：∀ {α : Type u_1} {m : Measurable
Space α} {μ : MeasureTheory.Measure α} (ν : MeasureTheory.Measure α),   (∀ (f : 
α → ENNReal), Measurable f →…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.lintegral_mconv`：lintegral_mconv [MeasurableMul₂ M
] {μ ν : Measure M} [SFinite ν] {f : M -> Real>=0∞} (hf : Measurable f) : ∫⁻ z, 
f z ∂(μ ∗ₘ ν) = ∫⁻ x, ∫⁻ y,…
· 使用定理 `Measurable.lintegral_prod_right`：Measurable.lintegral_prod_right [SFinit
e ν] {f : α -> β -> Real>=0∞} (hf : Measurable (uncurry f)) : Measurable fun x =
> ∫⁻ y, f x y ∂ν
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
· 使用定理 `Measurable.fun_mul`：∀ {M : Type u_2} {α : Type u_3} [inst : MeasurableSp
ace M] [inst_1 : Mul M] {m : MeasurableSpace α} {f g : α → M}   [MeasurableMul₂ 
M], Meas…
· 使用定理 `Measurable.fst`：Measurable.fst {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).1
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `Measurable.snd`：Measurable.snd {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).2
· 使用定理 `MeasureTheory.lintegral_congr`：lintegral_congr {f g : α -> Real>=0∞} (h 
: forall a, f a = g a) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `Measurable.const_mul`：Measurable.const_mul [MeasurableMul M] (hf : Measu
rable f) (c : M) : Measurable fun x => c * f x
· 使用定理 `MeasurableMul₂.toMeasurableMul`：∀ {M : Type u_2} [inst : MeasurableSpace
 M] [inst_1 : Mul M] [MeasurableMul₂ M], MeasurableMul M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Convolution is associative.
-/
theorem mconv_assoc [MeasurableMul₂ M] (μ ν ρ : Measure M)
    [SFinite ν] [SFinite ρ] :
    (μ ∗ₘ ν) ∗ₘ ρ = μ ∗ₘ (ν ∗ₘ ρ) := by
  refine ext_of_lintegral _ fun f hf ↦ ?_
  repeat rw [lintegral_mconv (by fun_prop)]
  refine lintegral_congr fun x ↦ ?_
  rw [lintegral_mconv (by fun_prop)]
  repeat refine lintegral_congr fun x ↦ ?_
  simp [mul_assoc]

@[to_additive]
/-
**MeasureTheory.Measure.probabilitymeasure_of_probabilitymeasures_mconv** 是 Math
lib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：probabilitymeasure_of_probabilitymeasures_mconv (μ : Measure M) (ν : Measu
re M) [MeasurableMul₂ M] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : IsP
robabilityMeasure (μ ∗ₘ ν)
参数：μ : Measure M；ν : Measure M。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.isProbabilityMeasure_map`：∀ {α : Type u_1} {β : Ty
pe u_2} {m0 : MeasurableSpace α} [inst : MeasurableSpace β] {μ : MeasureTheory.M
easure α}   [MeasureTheory.IsProbabi…
· 使用定理 `MeasureTheory.Measure.prod.instIsProbabilityMeasure`：∀ {α : Type u_4} {β
 : Type u_5} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (μ : MeasureTheor
y.Measure α)   (ν : MeasureTheory.Measure…
· 使用定理 `AEMeasurable.fun_mul`：∀ {M : Type u_2} {α : Type u_3} [inst : Measurable
Space M] [inst_1 : Mul M] {m : MeasurableSpace α} {f g : α → M}   {μ : MeasureTh
eory.Measu…
· 使用定理 `AEMeasurable.fst`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} {m0 : M
easurableSpace α} [inst : MeasurableSpace β]   [inst_1 : MeasurableSpace γ] {μ :
 Measu…
· 使用定理 `aemeasurable_id`：aemeasurable_id : AEMeasurable id μ
· 使用定理 `AEMeasurable.snd`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} {m0 : M
easurableSpace α} [inst : MeasurableSpace β]   [inst_1 : MeasurableSpace γ] {μ :
 Measu…
-/
instance probabilitymeasure_of_probabilitymeasures_mconv (μ : Measure M) (ν : Measure M)
    [MeasurableMul₂ M] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (μ ∗ₘ ν) :=
  isProbabilityMeasure_map (by fun_prop)

@[to_additive]
/-
**MeasureTheory.Measure.mconv_absolutelyContinuous** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.Measure`。
形式化陈述：mconv_absolutelyContinuous [MeasurableMul₂ M] {μ ν ρ : Measure M} [IsMulLe
ftInvariant ρ] [SFinite ν] (hν : ν ≪ ρ) : μ ∗ₘ ν ≪ ρ
参数：hν : ν ≪ ρ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.mk`：mk (h : forall ⦃s : Set α
⦄, MeasurableSet s -> ν s = 0 -> μ s = 0) : μ ≪ ν
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_indicator_one`：lintegral_indicator_one {s : Set 
α} (hs : MeasurableSet s) : ∫⁻ a, s.indicator 1 a ∂μ = μ s
· 使用定理 `MeasureTheory.Measure.lintegral_mconv`：lintegral_mconv [MeasurableMul₂ M
] {μ ν : Measure M} [SFinite ν] {f : M -> Real>=0∞} (hf : Measurable f) : ∫⁻ z, 
f z ∂(μ ∗ₘ ν) = ∫⁻ x, ∫⁻ y,…
· 使用定理 `Measurable.indicator`：Measurable.indicator [Zero β] (hf : Measurable f) 
(hs : MeasurableSet s) : Measurable (s.indicator f)
· 使用定理 `measurable_one`：measurable_one [One α] : Measurable (1 : β -> α)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasurableSet.preimage`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {m :
 MeasurableSpace α} {mβ : MeasurableSpace β} {t : Set β},   MeasurableSet t → Me
asurable f →…
· 使用定理 `Measurable.const_mul`：Measurable.const_mul [MeasurableMul M] (hf : Measu
rable f) (c : M) : Measurable fun x => c * f x
· 使用定理 `MeasurableMul₂.toMeasurableMul`：∀ {M : Type u_2} [inst : MeasurableSpace
 M] [inst_1 : Mul M] [MeasurableMul₂ M], MeasurableMul M
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `MeasureTheory.Measure.IsMulLeftInvariant.map_mul_left_eq_self`：∀ {G : Ty
pe u_1} {inst : MeasurableSpace G} {inst_1 : Mul G} {μ : MeasureTheory.Measure G
} [self : μ.IsMulLeftInvariant]   (g : G), MeasureT…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mconv_absolutelyContinuous [MeasurableMul₂ M] {μ ν ρ : Measure M}
    [IsMulLeftInvariant ρ] [SFinite ν] (hν : ν ≪ ρ) : μ ∗ₘ ν ≪ ρ := by
  refine AbsolutelyContinuous.mk (fun s hs h ↦ ?_)
  rw [← lintegral_indicator_one hs, lintegral_mconv (by measurability)]
  conv in s.indicator 1 (_ * _) => change s.indicator 1 ((fun y ↦ x * y) y)
  simp only [← Set.indicator_comp_right, Pi.one_comp]
  conv in ∫⁻ _, _ ∂ν =>
    rw [lintegral_indicator_one (by apply MeasurableSet.preimage hs (by fun_prop))]
  have h0 (x : M) : ν (HMul.hMul x ⁻¹' s) = 0 := by
    apply hν
    rw [← map_apply (by fun_prop) hs, IsMulLeftInvariant.map_mul_left_eq_self, h]
  simp [h0]

@[to_additive]
/-
**MeasureTheory.Measure.map_mconv_monoidHom** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTh
eory.Measure`。
形式化陈述：map_mconv_monoidHom {M M' : Type*} {mM : MeasurableSpace M} [Monoid M] [Me
asurableMul₂ M] {mM' : MeasurableSpace M'} [Monoid M'] [MeasurableMul₂ M'] {μ ν 
: Measure M} [SFinite μ] [SFinite ν] (L : M ->* M') (hL : Measurable L) : (μ ∗ₘ 
ν).map L = (μ.map L) ∗ₘ (ν.map L)
参数：L : M ->* M'；hL : Measurable L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_map`：map_map {g : β -> γ} {f : α -> β} (hg : M
easurable g) (hf : Measurable f) : (μ.map f).map g = μ.map (g ∘ f)
· 使用定理 `Measurable.fun_mul`：∀ {M : Type u_2} {α : Type u_3} [inst : MeasurableSp
ace M] [inst_1 : Mul M] {m : MeasurableSpace α} {f g : α → M}   [MeasurableMul₂ 
M], Meas…
· 使用定理 `Measurable.fst`：Measurable.fst {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).1
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `Measurable.snd`：Measurable.snd {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).2
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Measurable.prodMap`：Measurable.prodMap [MeasurableSpace δ] {f : α -> β} 
{g : γ -> δ} (hf : Measurable f) (hg : Measurable g) : Measurable (Prod.map f g)
· 使用定理 `MeasureTheory.Measure.map_prod_map`：map_prod_map {δ} [MeasurableSpace δ]
 {f : α -> β} {g : γ -> δ} (μa : Measure α) (μc : Measure γ) [SFinite μa] [SFini
te μc] (hf : Measurable …
-/
lemma map_mconv_monoidHom {M M' : Type*} {mM : MeasurableSpace M} [Monoid M] [MeasurableMul₂ M]
    {mM' : MeasurableSpace M'} [Monoid M'] [MeasurableMul₂ M']
    {μ ν : Measure M} [SFinite μ] [SFinite ν]
    (L : M →* M') (hL : Measurable L) :
    (μ ∗ₘ ν).map L = (μ.map L) ∗ₘ (ν.map L) := by
  unfold mconv
  rw [map_map (by fun_prop) (by fun_prop)]
  have : (L ∘ fun p : M × M ↦ p.1 * p.2) = (fun p : M' × M' ↦ p.1 * p.2) ∘ (Prod.map L L) := by
    ext; simp
  rw [this, ← map_map (by fun_prop) (by fun_prop), ← map_prod_map _ _ (by fun_prop) (by fun_prop)]
/-
**MeasureTheory.Measure.map_conv_continuousLinearMap** 是 Mathlib 中的一个引理，位于命名空间 `
MeasureTheory.Measure`。
形式化陈述：map_conv_continuousLinearMap {E F : Type*} [AddCommMonoid E] [AddCommMonoi
d F] [Module Real E] [Module Real F] [TopologicalSpace E] [TopologicalSpace F] {
mE : MeasurableSpace E} [MeasurableAdd₂ E] {mF : MeasurableSpace F} [MeasurableA
dd₂ F] [OpensMeasurableSpace E] [BorelSpace F] {μ ν : Measure E} [SFinite μ] [SF
inite ν] (L : E ->L[Real] F) : (μ ∗ ν).map L = (μ.map L) ∗ (ν.map L)
参数：L : E ->L[Real] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_conv_addMonoidHom`：∀ {M : Type u_2} {M' : Type
 u_3} {mM : MeasurableSpace M} [inst : AddMonoid M] [MeasurableAdd₂ M]   {mM' : 
MeasurableSpace M'} [inst_2 : Add…
· 使用定理 `AddMonoidHom.coe_coe`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [in
st : AddZero M] [inst_1 : AddZero N] [inst_2 : FunLike F M N]   [inst_3 : AddMon
oidHomClas…
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
-/
lemma map_conv_continuousLinearMap {E F : Type*} [AddCommMonoid E] [AddCommMonoid F]
    [Module ℝ E] [Module ℝ F] [TopologicalSpace E] [TopologicalSpace F]
    {mE : MeasurableSpace E} [MeasurableAdd₂ E] {mF : MeasurableSpace F} [MeasurableAdd₂ F]
    [OpensMeasurableSpace E] [BorelSpace F]
    {μ ν : Measure E} [SFinite μ] [SFinite ν]
    (L : E →L[ℝ] F) :
    (μ ∗ ν).map L = (μ.map L) ∗ (ν.map L) := by
  suffices (μ ∗ ν).map (L : E →+ F) = (μ.map (L : E →+ F)) ∗ (ν.map (L : E →+ F)) by simpa
  rw [map_conv_addMonoidHom]
  rw [AddMonoidHom.coe_coe]
  fun_prop

end Measure

end MeasureTheory

