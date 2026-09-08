/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.Probability.Kernel.Composition.CompProd
public import Mathlib.Probability.Kernel.Disintegration.MeasurableStieltjes

/-!
# Building a Markov kernel from a conditional cumulative distribution function

Let `κ : Kernel α (β × ℝ)` and `ν : Kernel α β` be two finite kernels.
A function `f : α × β → StieltjesFunction ℝ` is called a conditional kernel CDF of `κ` with respect
to `ν` if it is measurable, tends to 0 at -∞ and to 1 at +∞ for all `p : α × β`,
`fun b ↦ f (a, b) x` is `(ν a)`-integrable for all `a : α` and `x : ℝ` and for all measurable
sets `s : Set β`, `∫ b in s, f (a, b) x ∂(ν a) = (κ a).real (s ×ˢ Iic x)`.

From such a function with property `hf : IsCondKernelCDF f κ ν`, we can build a `Kernel (α × β) ℝ`
denoted by `hf.toKernel f` such that `κ = ν ⊗ₖ hf.toKernel f`.

## Main definitions

Let `κ : Kernel α (β × ℝ)` and `ν : Kernel α β`.

* `ProbabilityTheory.IsCondKernelCDF`: a function `f : α × β → StieltjesFunction ℝ` is called
  a conditional kernel CDF of `κ` with respect to `ν` if it is measurable, tends to 0 at -∞ and
  to 1 at +∞ for all `p : α × β`, if `fun b ↦ f (a, b) x` is `(ν a)`-integrable for all `a : α` and
  `x : ℝ` and for all measurable sets `s : Set β`,
  `∫ b in s, f (a, b) x ∂(ν a) = (κ a).real (s ×ˢ Iic x)`.
* `ProbabilityTheory.IsCondKernelCDF.toKernel`: from a function `f : α × β → StieltjesFunction ℝ`
  with the property `hf : IsCondKernelCDF f κ ν`, build a `Kernel (α × β) ℝ` such that
  `κ = ν ⊗ₖ hf.toKernel f`.
* `ProbabilityTheory.IsRatCondKernelCDF`: a function `f : α × β → ℚ → ℝ` is called a rational
  conditional kernel CDF of `κ` with respect to `ν` if is measurable and satisfies the same
  integral conditions as in the definition of `IsCondKernelCDF`, and the `ℚ → ℝ` function `f (a, b)`
  satisfies the properties of a Stieltjes function for `(ν a)`-almost all `b : β`.

## Main statements

* `ProbabilityTheory.isCondKernelCDF_stieltjesOfMeasurableRat`: if `f : α × β → ℚ → ℝ` has the
  property `IsRatCondKernelCDF`, then `stieltjesOfMeasurableRat f` is a function
  `α × β → StieltjesFunction ℝ` with the property `IsCondKernelCDF`.
* `ProbabilityTheory.compProd_toKernel`: for `hf : IsCondKernelCDF f κ ν`, `ν ⊗ₖ hf.toKernel f = κ`.

-/

@[expose] public section

open MeasureTheory Set Filter TopologicalSpace

open scoped NNReal ENNReal MeasureTheory Topology ProbabilityTheory

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {κ : Kernel α (β × ℝ)} {ν : Kernel α β}

section stieltjesOfMeasurableRat

variable {f : α × β → ℚ → ℝ}

/-- a function `f : α × β → ℚ → ℝ` is called a rational conditional kernel CDF of `κ` with respect
to `ν` if is measurable, if `fun b ↦ f (a, b) x` is `(ν a)`-integrable for all `a : α` and `x : ℝ`
and for all measurable sets `s : Set β`, `∫ b in s, f (a, b) x ∂(ν a) = (κ a).real (s ×ˢ Iic x)`.
Also the `ℚ → ℝ` function `f (a, b)` should satisfy the properties of a Stieltjes function for
`(ν a)`-almost all `b : β`. -/
/-
**ProbabilityTheory.IsRatCondKernelCDF** 是 Mathlib 中的一个归纳类型，位于命名空间 `ProbabilityT
heory`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     {mα : MeasurableSpace α} →       {
mβ : MeasurableSpace β} →         (α × β → ℚ → ℝ) → ProbabilityTheory.Kernel α (
β × ℝ) → ProbabilityTheory.Kernel α β → Prop
参数：α × β → ℚ → ℝ；β × ℝ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
a function `f : α × β → ℚ → ℝ` is called a rational conditional kernel CDF of `κ
` with respect
to `ν` if is measurable, if `fun b ↦ f (a, b) x` is `(ν a)`-integrable for all `
a : α` and `x : ℝ`
and for all measurable sets `s : Set β`, `∫ b in s, f (a, b) x ∂(ν a) = (κ a).re
al (s ×ˢ Iic x)`.
Also the `ℚ → ℝ` function `f (a, b)` should satisfy the properties of a Stieltje
s function for
`(ν a)`-almost all `b : β`.
-/
structure IsRatCondKernelCDF (f : α × β → ℚ → ℝ) (κ : Kernel α (β × ℝ)) (ν : Kernel α β) :
    Prop where
  measurable : Measurable f
  isRatStieltjesPoint_ae (a : α) : ∀ᵐ b ∂(ν a), IsRatStieltjesPoint f (a, b)
  integrable (a : α) (q : ℚ) : Integrable (fun b ↦ f (a, b) q) (ν a)
  setIntegral (a : α) {s : Set β} (_hs : MeasurableSet s) (q : ℚ) :
    ∫ b in s, f (a, b) q ∂(ν a) = (κ a).real (s ×ˢ Iic (q : ℝ))
/-
**ProbabilityTheory.IsRatCondKernelCDF.mono** 是 Mathlib 中的一个定理，位于命名空间 `Probabili
tyTheory.IsRatCondKernelCDF`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β}   {κ : ProbabilityTheory.Kernel α (β × ℝ)} {ν : ProbabilityTheory.Kernel
 α β} {f : α × β → ℚ → ℝ},   ProbabilityTheory.IsRatCondKernelCDF f κ ν → ∀ (a :
 α), ∀ᵐ (b : β) ∂ν a, Monotone (f (a, b))
参数：β × ℝ；a : α；b : β；f (a, b)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDF.isRatStieltjesPoint_ae`：∀ {α : Type
 u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α × 
β → ℚ → ℝ}   {κ : ProbabilityTheory.Kernel α (β ×…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ProbabilityTheory.IsRatStieltjesPoint.mono`：∀ {α : Type u_1} {f : α → ℚ 
→ ℝ} {a : α}, ProbabilityTheory.IsRatStieltjesPoint f a → Monotone (f a)
-/
lemma IsRatCondKernelCDF.mono (hf : IsRatCondKernelCDF f κ ν) (a : α) :
    ∀ᵐ b ∂(ν a), Monotone (f (a, b)) := by
  filter_upwards [hf.isRatStieltjesPoint_ae a] with b hb using hb.mono
/-
**ProbabilityTheory.IsRatCondKernelCDF.tendsto_atTop_one** 是 Mathlib 中的一个定理，位于命名
空间 `ProbabilityTheory.IsRatCondKernelCDF`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β}   {κ : ProbabilityTheory.Kernel α (β × ℝ)} {ν : ProbabilityTheory.Kernel
 α β} {f : α × β → ℚ → ℝ},   ProbabilityTheory.IsRatCondKernelCDF f κ ν →     ∀ 
(a : α), ∀ᵐ (b : β) ∂ν a, Filter.Tendsto (f (a, b)) Filter.atTop (nhds 1)
参数：β × ℝ；a : α；b : β；f (a, b)；nhds 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDF.isRatStieltjesPoint_ae`：∀ {α : Type
 u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α × 
β → ℚ → ℝ}   {κ : ProbabilityTheory.Kernel α (β ×…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ProbabilityTheory.IsRatStieltjesPoint.tendsto_atTop_one`：∀ {α : Type u_1
} {f : α → ℚ → ℝ} {a : α},   ProbabilityTheory.IsRatStieltjesPoint f a → Filter.
Tendsto (f a) Filter.atTop (nhds 1)
-/
lemma IsRatCondKernelCDF.tendsto_atTop_one (hf : IsRatCondKernelCDF f κ ν) (a : α) :
    ∀ᵐ b ∂(ν a), Tendsto (f (a, b)) atTop (𝓝 1) := by
  filter_upwards [hf.isRatStieltjesPoint_ae a] with b hb using hb.tendsto_atTop_one
/-
**ProbabilityTheory.IsRatCondKernelCDF.tendsto_atBot_zero** 是 Mathlib 中的一个定理，位于命
名空间 `ProbabilityTheory.IsRatCondKernelCDF`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β}   {κ : ProbabilityTheory.Kernel α (β × ℝ)} {ν : ProbabilityTheory.Kernel
 α β} {f : α × β → ℚ → ℝ},   ProbabilityTheory.IsRatCondKernelCDF f κ ν →     ∀ 
(a : α), ∀ᵐ (b : β) ∂ν a, Filter.Tendsto (f (a, b)) Filter.atBot (nhds 0)
参数：β × ℝ；a : α；b : β；f (a, b)；nhds 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDF.isRatStieltjesPoint_ae`：∀ {α : Type
 u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α × 
β → ℚ → ℝ}   {κ : ProbabilityTheory.Kernel α (β ×…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ProbabilityTheory.IsRatStieltjesPoint.tendsto_atBot_zero`：∀ {α : Type u_
1} {f : α → ℚ → ℝ} {a : α},   ProbabilityTheory.IsRatStieltjesPoint f a → Filter
.Tendsto (f a) Filter.atBot (nhds 0)
-/
lemma IsRatCondKernelCDF.tendsto_atBot_zero (hf : IsRatCondKernelCDF f κ ν) (a : α) :
    ∀ᵐ b ∂(ν a), Tendsto (f (a, b)) atBot (𝓝 0) := by
  filter_upwards [hf.isRatStieltjesPoint_ae a] with b hb using hb.tendsto_atBot_zero
/-
**ProbabilityTheory.IsRatCondKernelCDF.iInf_rat_gt_eq** 是 Mathlib 中的一个定理，位于命名空间 
`ProbabilityTheory.IsRatCondKernelCDF`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β}   {κ : ProbabilityTheory.Kernel α (β × ℝ)} {ν : ProbabilityTheory.Kernel
 α β} {f : α × β → ℚ → ℝ},   ProbabilityTheory.IsRatCondKernelCDF f κ ν → ∀ (a :
 α), ∀ᵐ (b : β) ∂ν a, ∀ (q : ℚ), ⨅ r, f (a, b) ↑r = f (a, b) q
参数：β × ℝ；a : α；b : β；q : ℚ；a, b；a, b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDF.isRatStieltjesPoint_ae`：∀ {α : Type
 u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α × 
β → ℚ → ℝ}   {κ : ProbabilityTheory.Kernel α (β ×…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ProbabilityTheory.IsRatStieltjesPoint.iInf_rat_gt_eq`：∀ {α : Type u_1} {
f : α → ℚ → ℝ} {a : α}, ProbabilityTheory.IsRatStieltjesPoint f a → ∀ (t : ℚ), ⨅
 r, f a ↑r = f a t
-/
lemma IsRatCondKernelCDF.iInf_rat_gt_eq (hf : IsRatCondKernelCDF f κ ν) (a : α) :
    ∀ᵐ b ∂(ν a), ∀ q, ⨅ r : Ioi q, f (a, b) r = f (a, b) q := by
  filter_upwards [hf.isRatStieltjesPoint_ae a] with b hb using hb.iInf_rat_gt_eq
/-
**ProbabilityTheory.stieltjesOfMeasurableRat_ae_eq** 是 Mathlib 中的一个引理，位于命名空间 `Pr
obabilityTheory`。
形式化陈述：stieltjesOfMeasurableRat_ae_eq (hf : IsRatCondKernelCDF f κ ν) (a : α) (q 
: Rat) : (fun b => stieltjesOfMeasurableRat f hf.measurable (a, b) q) =ᵐ[ν a] fu
n b => f (a, b) q
参数：hf : IsRatCondKernelCDF f κ ν；a : α；q : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDF.measurable`：∀ {α : Type u_1} {β : T
ype u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α × β → ℚ → ℝ}  
 {κ : ProbabilityTheory.Kernel α (β ×…
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDF.isRatStieltjesPoint_ae`：∀ {α : Type
 u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α × 
β → ℚ → ℝ}   {κ : ProbabilityTheory.Kernel α (β ×…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.stieltjesOfMeasurableRat_eq`：stieltjesOfMeasurableRat_
eq (hf : Measurable f) (a : α) (r : Rat) : stieltjesOfMeasurableRat f hf a r = t
oRatCDF f a r
· 使用引理 `ProbabilityTheory.toRatCDF_of_isRatStieltjesPoint`：toRatCDF_of_isRatStie
ltjesPoint {a : α} (h : IsRatStieltjesPoint f a) (q : Rat) : toRatCDF f a q = f 
a q
-/
lemma stieltjesOfMeasurableRat_ae_eq (hf : IsRatCondKernelCDF f κ ν) (a : α) (q : ℚ) :
    (fun b ↦ stieltjesOfMeasurableRat f hf.measurable (a, b) q) =ᵐ[ν a] fun b ↦ f (a, b) q := by
  filter_upwards [hf.isRatStieltjesPoint_ae a] with a ha
  rw [stieltjesOfMeasurableRat_eq, toRatCDF_of_isRatStieltjesPoint ha]
/-
**ProbabilityTheory.setIntegral_stieltjesOfMeasurableRat_rat** 是 Mathlib 中的一个引理，
位于命名空间 `ProbabilityTheory`。
形式化陈述：setIntegral_stieltjesOfMeasurableRat_rat (hf : IsRatCondKernelCDF f κ ν) (
a : α) (q : Rat) {s : Set β} (hs : MeasurableSet s) : ∫ b in s, stieltjesOfMeasu
rableRat f hf.measurable (a, b) q ∂(ν a) = (κ a).real (s ×ˢ Iic (q : Real))
参数：hf : IsRatCondKernelCDF f κ ν；a : α；q : Rat；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDF.measurable`：∀ {α : Type u_1} {β : T
ype u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α × β → ℚ → ℝ}  
 {κ : ProbabilityTheory.Kernel α (β ×…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setIntegral_congr_ae`：setIntegral_congr_ae (hs : Measurabl
eSet s) (h : forallᵐ x ∂μ, x in s -> f x = g x) : ∫ x in s, f x ∂μ = ∫ x in s, g
 x ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.stieltjesOfMeasurableRat_ae_eq`：stieltjesOfMeasurableR
at_ae_eq (hf : IsRatCondKernelCDF f κ ν) (a : α) (q : Rat) : (fun b => stieltjes
OfMeasurableRat f hf.measurable (a, b)…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDF.setIntegral`：∀ {α : Type u_1} {β : 
Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α × β → ℚ → ℝ} 
  {κ : ProbabilityTheory.Kernel α (β ×…
-/
lemma setIntegral_stieltjesOfMeasurableRat_rat (hf : IsRatCondKernelCDF f κ ν) (a : α) (q : ℚ)
    {s : Set β} (hs : MeasurableSet s) :
    ∫ b in s, stieltjesOfMeasurableRat f hf.measurable (a, b) q ∂(ν a)
      = (κ a).real (s ×ˢ Iic (q : ℝ)) := by
  rw [setIntegral_congr_ae hs (g := fun b ↦ f (a, b) q) ?_, hf.setIntegral a hs]
  filter_upwards [stieltjesOfMeasurableRat_ae_eq hf a q] with b hb using fun _ ↦ hb
/-
**ProbabilityTheory.setLIntegral_stieltjesOfMeasurableRat_rat** 是 Mathlib 中的一个引理
，位于命名空间 `ProbabilityTheory`。
形式化陈述：setLIntegral_stieltjesOfMeasurableRat_rat [IsFiniteKernel κ] (hf : IsRatCo
ndKernelCDF f κ ν) (a : α) (q : Rat) {s : Set β} (hs : MeasurableSet s) : ∫⁻ b i
n s, ENNReal.ofReal (stieltjesOfMeasurableRat f hf.measurable (a, b) q) ∂(ν a) =
 κ a (s ×ˢ Iic (q : Real))
参数：hf : IsRatCondKernelCDF f κ ν；a : α；q : Rat；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDF.measurable`：∀ {α : Type u_1} {β : T
ype u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α × β → ℚ → ℝ}  
 {κ : ProbabilityTheory.Kernel α (β ×…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.ofReal_integral_eq_lintegral_ofReal`：ofReal_integral_eq_li
ntegral_ofReal {f : α -> Real} (hfi : Integrable f μ) (f_nn : 0 <=ᵐ[μ] f) : ENNR
eal.ofReal (∫ x, f x ∂μ) = ∫⁻ x, ENNRea…
· 使用定理 `MeasureTheory.Integrable.restrict`：∀ {α : Type u_1} {m : MeasurableSpace
 α} {μ : MeasureTheory.Measure α} {ε : Type u_8} [inst : TopologicalSpace ε]   [
inst_1 : ContinuousENor…
· 使用定理 `MeasureTheory.integrable_congr`：integrable_congr {f g : α -> ε} (h : f =
ᵐ[μ] g) : Integrable f μ ↔ Integrable g μ
· 使用引理 `ProbabilityTheory.stieltjesOfMeasurableRat_ae_eq`：stieltjesOfMeasurableR
at_ae_eq (hf : IsRatCondKernelCDF f κ ν) (a : α) (q : Rat) : (fun b => stieltjes
OfMeasurableRat f hf.measurable (a, b)…
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDF.integrable`：∀ {α : Type u_1} {β : T
ype u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α × β → ℚ → ℝ}  
 {κ : ProbabilityTheory.Kernel α (β ×…
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.stieltjesOfMeasurableRat_nonneg`：stieltjesOfMeasurable
Rat_nonneg (hf : Measurable f) (a : α) (r : Real) : 0 <= stieltjesOfMeasurableRa
t f hf a r
· 使用引理 `ProbabilityTheory.setIntegral_stieltjesOfMeasurableRat_rat`：setIntegral_
stieltjesOfMeasurableRat_rat (hf : IsRatCondKernelCDF f κ ν) (a : α) (q : Rat) {
s : Set β} (hs : MeasurableSet s) : ∫ b in s, st…
· 使用定理 `MeasureTheory.ofReal_measureReal`：ofReal_measureReal (h : μ s != ∞
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `ProbabilityTheory.IsFiniteKernel.isFiniteMeasure`：∀ {α : Type u_1} {β : 
Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheo
ry.Kernel α β}   [ProbabilityTheory.Is…
-/
lemma setLIntegral_stieltjesOfMeasurableRat_rat [IsFiniteKernel κ] (hf : IsRatCondKernelCDF f κ ν)
    (a : α) (q : ℚ) {s : Set β} (hs : MeasurableSet s) :
    ∫⁻ b in s, ENNReal.ofReal (stieltjesOfMeasurableRat f hf.measurable (a, b) q) ∂(ν a)
      = κ a (s ×ˢ Iic (q : ℝ)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [setIntegral_stieltjesOfMeasurableRat_rat hf a q hs, ofReal_measureReal]
  · refine Integrable.restrict ?_
    rw [integrable_congr (stieltjesOfMeasurableRat_ae_eq hf a q)]
    exact hf.integrable a q
  · exact ae_of_all _ (fun x ↦ stieltjesOfMeasurableRat_nonneg _ _ _)
/-
**ProbabilityTheory.setLIntegral_stieltjesOfMeasurableRat** 是 Mathlib 中的一个引理，位于命
名空间 `ProbabilityTheory`。
形式化陈述：setLIntegral_stieltjesOfMeasurableRat [IsFiniteKernel κ] (hf : IsRatCondKe
rnelCDF f κ ν) (a : α) (x : Real) {s : Set β} (hs : MeasurableSet s) : ∫⁻ b in s
, ENNReal.ofReal (stieltjesOfMeasurableRat f hf.measurable (a, b) x) ∂(ν a) = κ 
a (s ×ˢ Iic x)
参数：hf : IsRatCondKernelCDF f κ ν；a : α；x : Real；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDF.measurable`：∀ {α : Type u_1} {β : T
ype u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α × β → ℚ → ℝ}  
 {κ : ProbabilityTheory.Kernel α (β ×…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_zero_measure`：lintegral_zero_measure {m : Measur
ableSpace α} (f : α -> Real>=0∞) : ∫⁻ a, f a ∂(0 : Measure α) = 0
· 使用定理 `exists_rat_gt`：exists_rat_gt (x : K) : exists q : Rat, x < q
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDF.setIntegral`：∀ {α : Type u_1} {β : 
Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α × β → ℚ → ℝ} 
  {κ : ProbabilityTheory.Kernel α (β ×…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.integral_zero_measure`：integral_zero_measure {m : Measurab
leSpace α} (f : α -> G) : (∫ x, f x ∂(0 : Measure α)) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.measureReal_eq_zero_iff`：measureReal_eq_zero_iff (h : μ s 
!= ∞
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `ProbabilityTheory.IsFiniteKernel.isFiniteMeasure`：∀ {α : Type u_1} {β : 
Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheo
ry.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Monotone.measure_iInter`：∀ {α : Type u_1} {ι : Type u_5} {m : Measurable
Space α} {μ : MeasureTheory.Measure α} [inst : Preorder ι]   [IsCodirectedOrder 
ι] [Filter.at…
· 使用定理 `SemilatticeInf.instIsCodirectedOrder`：∀ {α : Type u_1} [inst : Semilatti
ceInf α], IsCodirectedOrder α
（共 64 条，此处仅展示前 30 条）
-/
lemma setLIntegral_stieltjesOfMeasurableRat [IsFiniteKernel κ] (hf : IsRatCondKernelCDF f κ ν)
    (a : α) (x : ℝ) {s : Set β} (hs : MeasurableSet s) :
    ∫⁻ b in s, ENNReal.ofReal (stieltjesOfMeasurableRat f hf.measurable (a, b) x) ∂(ν a)
      = κ a (s ×ˢ Iic x) := by
  -- We have the result for `x : ℚ` thanks to `setLIntegral_stieltjesOfMeasurableRat_rat`.
  -- We use a monotone convergence argument to extend it to the reals.
  by_cases hρ_zero : (ν a).restrict s = 0
  · rw [hρ_zero, lintegral_zero_measure]
    have ⟨q, hq⟩ := exists_rat_gt x
    suffices κ a (s ×ˢ Iic (q : ℝ)) = 0 by
      symm
      refine measure_mono_null (fun p ↦ ?_) this
      simp only [mem_prod, mem_Iic, and_imp]
      exact fun h1 h2 ↦ ⟨h1, h2.trans hq.le⟩
    suffices (κ a).real (s ×ˢ Iic (q : ℝ)) = 0 by
      rw [measureReal_eq_zero_iff] at this
      simpa [measure_ne_top] using this
    rw [← hf.setIntegral a hs q]
    simp [hρ_zero]
  have h : ∫⁻ b in s, ENNReal.ofReal (stieltjesOfMeasurableRat f hf.measurable (a, b) x) ∂(ν a)
      = ∫⁻ b in s, ⨅ r : { r' : ℚ // x < r' },
        ENNReal.ofReal (stieltjesOfMeasurableRat f hf.measurable (a, b) r) ∂(ν a) := by
    congr with b : 1
    simp_rw [← measure_stieltjesOfMeasurableRat_Iic]
    rw [← Monotone.measure_iInter]
    · congr with y : 1
      simp only [mem_Iic, mem_iInter, Subtype.forall]
      exact le_iff_forall_lt_rat_imp_le
    · exact fun r r' hrr' ↦ Iic_subset_Iic.mpr <| mod_cast hrr'
    · exact fun _ ↦ nullMeasurableSet_Iic
    · obtain ⟨q, hq⟩ := exists_rat_gt x
      exact ⟨⟨q, hq⟩, measure_ne_top _ _⟩
  have h_nonempty : Nonempty { r' : ℚ // x < ↑r' } := by
    obtain ⟨r, hrx⟩ := exists_rat_gt x
    exact ⟨⟨r, hrx⟩⟩
  rw [h, lintegral_iInf_directed_of_measurable hρ_zero fun q : { r' : ℚ // x < ↑r' } ↦ ?_]
  rotate_left
  · intro b
    rw [setLIntegral_stieltjesOfMeasurableRat_rat hf a _ hs]
    exact measure_ne_top _ _
  · refine Monotone.directed_ge fun i j hij b ↦ ?_
    simp_rw [← measure_stieltjesOfMeasurableRat_Iic]
    refine measure_mono (Iic_subset_Iic.mpr ?_)
    exact mod_cast hij
  · refine Measurable.ennreal_ofReal ?_
    exact (measurable_stieltjesOfMeasurableRat hf.measurable _).comp measurable_prodMk_left
  simp_rw [setLIntegral_stieltjesOfMeasurableRat_rat hf _ _ hs]
  rw [← Monotone.measure_iInter]
  · rw [← prod_iInter]
    congr with y
    simp only [mem_iInter, mem_Iic, Subtype.forall]
    exact ⟨le_of_forall_lt_rat_imp_le, fun hyx q hq ↦ hyx.trans hq.le⟩
  · exact fun i j hij ↦ prod_mono_right (by gcongr)
  · exact fun i ↦ (hs.prod measurableSet_Iic).nullMeasurableSet
  · exact ⟨h_nonempty.some, measure_ne_top _ _⟩
/-
**ProbabilityTheory.lintegral_stieltjesOfMeasurableRat** 是 Mathlib 中的一个引理，位于命名空间
 `ProbabilityTheory`。
形式化陈述：lintegral_stieltjesOfMeasurableRat [IsFiniteKernel κ] (hf : IsRatCondKerne
lCDF f κ ν) (a : α) (x : Real) : ∫⁻ b, ENNReal.ofReal (stieltjesOfMeasurableRat 
f hf.measurable (a, b) x) ∂(ν a) = κ a (univ ×ˢ Iic x)
参数：hf : IsRatCondKernelCDF f κ ν；a : α；x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDF.measurable`：∀ {α : Type u_1} {β : T
ype u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α × β → ℚ → ℝ}  
 {κ : ProbabilityTheory.Kernel α (β ×…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setLIntegral_univ`：setLIntegral_univ (f : α -> Real>=0∞) :
 ∫⁻ x in univ, f x ∂μ = ∫⁻ x, f x ∂μ
· 使用引理 `ProbabilityTheory.setLIntegral_stieltjesOfMeasurableRat`：setLIntegral_st
ieltjesOfMeasurableRat [IsFiniteKernel κ] (hf : IsRatCondKernelCDF f κ ν) (a : α
) (x : Real) {s : Set β} (hs : MeasurableSet …
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
-/
lemma lintegral_stieltjesOfMeasurableRat [IsFiniteKernel κ] (hf : IsRatCondKernelCDF f κ ν)
    (a : α) (x : ℝ) :
    ∫⁻ b, ENNReal.ofReal (stieltjesOfMeasurableRat f hf.measurable (a, b) x) ∂(ν a)
      = κ a (univ ×ˢ Iic x) := by
  rw [← setLIntegral_univ, setLIntegral_stieltjesOfMeasurableRat hf _ _ MeasurableSet.univ]
/-
**ProbabilityTheory.integrable_stieltjesOfMeasurableRat** 是 Mathlib 中的一个引理，位于命名空
间 `ProbabilityTheory`。
形式化陈述：integrable_stieltjesOfMeasurableRat [IsFiniteKernel κ] (hf : IsRatCondKern
elCDF f κ ν) (a : α) (x : Real) : Integrable (fun b => stieltjesOfMeasurableRat 
f hf.measurable (a, b) x) (ν a)
参数：hf : IsRatCondKernelCDF f κ ν；a : α；x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDF.measurable`：∀ {α : Type u_1} {β : T
ype u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α × β → ℚ → ℝ}  
 {κ : ProbabilityTheory.Kernel α (β ×…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用引理 `ProbabilityTheory.stieltjesOfMeasurableRat_nonneg`：stieltjesOfMeasurable
Rat_nonneg (hf : Measurable f) (a : α) (r : Real) : 0 <= stieltjesOfMeasurableRa
t f hf a r
· 使用定理 `MeasureTheory.integrable_toReal_of_lintegral_ne_top`：integrable_toReal_o
f_lintegral_ne_top {f : α -> Real>=0∞} (hfm : AEMeasurable f μ) (hfi : ∫⁻ x, f x
 ∂μ != ∞) : Integrable (fun x => (f x).to…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Measurable.ennreal_ofReal`：Measurable.ennreal_ofReal {f : α -> Real} (hf
 : Measurable f) : Measurable fun x => ENNReal.ofReal (f x)
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用引理 `ProbabilityTheory.measurable_stieltjesOfMeasurableRat`：measurable_stielt
jesOfMeasurableRat (hf : Measurable f) (x : Real) : Measurable fun a => stieltje
sOfMeasurableRat f hf a x
· 使用定理 `measurable_prodMk_left`：measurable_prodMk_left {x : α} : Measurable (@Pr
od.mk _ β x)
· 使用引理 `ProbabilityTheory.lintegral_stieltjesOfMeasurableRat`：lintegral_stieltje
sOfMeasurableRat [IsFiniteKernel κ] (hf : IsRatCondKernelCDF f κ ν) (a : α) (x :
 Real) : ∫⁻ b, ENNReal.ofReal (stieltjesOf…
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `ProbabilityTheory.IsFiniteKernel.isFiniteMeasure`：∀ {α : Type u_1} {β : 
Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheo
ry.Kernel α β}   [ProbabilityTheory.Is…
-/
lemma integrable_stieltjesOfMeasurableRat [IsFiniteKernel κ] (hf : IsRatCondKernelCDF f κ ν)
    (a : α) (x : ℝ) :
    Integrable (fun b ↦ stieltjesOfMeasurableRat f hf.measurable (a, b) x) (ν a) := by
  have : (fun b ↦ stieltjesOfMeasurableRat f hf.measurable (a, b) x)
      = fun b ↦ (ENNReal.ofReal (stieltjesOfMeasurableRat f hf.measurable (a, b) x)).toReal := by
    ext t
    rw [ENNReal.toReal_ofReal]
    exact stieltjesOfMeasurableRat_nonneg _ _ _
  rw [this]
  refine integrable_toReal_of_lintegral_ne_top ?_ ?_
  · refine (Measurable.ennreal_ofReal ?_).aemeasurable
    exact (measurable_stieltjesOfMeasurableRat hf.measurable x).comp measurable_prodMk_left
  · rw [lintegral_stieltjesOfMeasurableRat hf]
    exact measure_ne_top _ _
/-
**ProbabilityTheory.setIntegral_stieltjesOfMeasurableRat** 是 Mathlib 中的一个引理，位于命名
空间 `ProbabilityTheory`。
形式化陈述：setIntegral_stieltjesOfMeasurableRat [IsFiniteKernel κ] (hf : IsRatCondKer
nelCDF f κ ν) (a : α) (x : Real) {s : Set β} (hs : MeasurableSet s) : ∫ b in s, 
stieltjesOfMeasurableRat f hf.measurable (a, b) x ∂(ν a) = (κ a).real (s ×ˢ Iic 
x)
参数：hf : IsRatCondKernelCDF f κ ν；a : α；x : Real；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDF.measurable`：∀ {α : Type u_1} {β : T
ype u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α × β → ℚ → ℝ}  
 {κ : ProbabilityTheory.Kernel α (β ×…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.ofReal_eq_ofReal_iff`：ofReal_eq_ofReal_iff {p q : Real} (hp : 0 
<= p) (hq : 0 <= q) : ENNReal.ofReal p = ENNReal.ofReal q ↔ p = q
· 使用定理 `MeasureTheory.setIntegral_nonneg`：setIntegral_nonneg (hs : MeasurableSet
 s) (hf : forall x, x in s -> 0 <= f x) : 0 <= ∫ x in s, f x ∂μ
· 使用引理 `ProbabilityTheory.stieltjesOfMeasurableRat_nonneg`：stieltjesOfMeasurable
Rat_nonneg (hf : Measurable f) (a : α) (r : Real) : 0 <= stieltjesOfMeasurableRa
t f hf a r
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
· 使用定理 `MeasureTheory.ofReal_measureReal`：ofReal_measureReal (h : μ s != ∞
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `ProbabilityTheory.IsFiniteKernel.isFiniteMeasure`：∀ {α : Type u_1} {β : 
Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheo
ry.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `MeasureTheory.ofReal_integral_eq_lintegral_ofReal`：ofReal_integral_eq_li
ntegral_ofReal {f : α -> Real} (hfi : Integrable f μ) (f_nn : 0 <=ᵐ[μ] f) : ENNR
eal.ofReal (∫ x, f x ∂μ) = ∫⁻ x, ENNRea…
· 使用定理 `MeasureTheory.Integrable.restrict`：∀ {α : Type u_1} {m : MeasurableSpace
 α} {μ : MeasureTheory.Measure α} {ε : Type u_8} [inst : TopologicalSpace ε]   [
inst_1 : ContinuousENor…
· 使用引理 `ProbabilityTheory.integrable_stieltjesOfMeasurableRat`：integrable_stielt
jesOfMeasurableRat [IsFiniteKernel κ] (hf : IsRatCondKernelCDF f κ ν) (a : α) (x
 : Real) : Integrable (fun b => stieltjesOf…
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.setLIntegral_stieltjesOfMeasurableRat`：setLIntegral_st
ieltjesOfMeasurableRat [IsFiniteKernel κ] (hf : IsRatCondKernelCDF f κ ν) (a : α
) (x : Real) {s : Set β} (hs : MeasurableSet …
-/
lemma setIntegral_stieltjesOfMeasurableRat [IsFiniteKernel κ] (hf : IsRatCondKernelCDF f κ ν)
    (a : α) (x : ℝ) {s : Set β} (hs : MeasurableSet s) :
    ∫ b in s, stieltjesOfMeasurableRat f hf.measurable (a, b) x ∂(ν a)
      = (κ a).real (s ×ˢ Iic x) := by
  rw [← ENNReal.ofReal_eq_ofReal_iff, ofReal_measureReal]
  rotate_left
  · exact setIntegral_nonneg hs (fun _ _ ↦ stieltjesOfMeasurableRat_nonneg _ _ _)
  · exact ENNReal.toReal_nonneg
  rw [ofReal_integral_eq_lintegral_ofReal, setLIntegral_stieltjesOfMeasurableRat hf _ _ hs]
  · exact (integrable_stieltjesOfMeasurableRat hf _ _).restrict
  · exact ae_of_all _ (fun _ ↦ stieltjesOfMeasurableRat_nonneg _ _ _)
/-
**ProbabilityTheory.integral_stieltjesOfMeasurableRat** 是 Mathlib 中的一个引理，位于命名空间 
`ProbabilityTheory`。
形式化陈述：integral_stieltjesOfMeasurableRat [IsFiniteKernel κ] (hf : IsRatCondKernel
CDF f κ ν) (a : α) (x : Real) : ∫ b, stieltjesOfMeasurableRat f hf.measurable (a
, b) x ∂(ν a) = (κ a).real (univ ×ˢ Iic x)
参数：hf : IsRatCondKernelCDF f κ ν；a : α；x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDF.measurable`：∀ {α : Type u_1} {β : T
ype u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α × β → ℚ → ℝ}  
 {κ : ProbabilityTheory.Kernel α (β ×…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setIntegral_univ`：setIntegral_univ : ∫ x in univ, f x ∂μ =
 ∫ x, f x ∂μ
· 使用引理 `ProbabilityTheory.setIntegral_stieltjesOfMeasurableRat`：setIntegral_stie
ltjesOfMeasurableRat [IsFiniteKernel κ] (hf : IsRatCondKernelCDF f κ ν) (a : α) 
(x : Real) {s : Set β} (hs : MeasurableSet s…
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
-/
lemma integral_stieltjesOfMeasurableRat [IsFiniteKernel κ] (hf : IsRatCondKernelCDF f κ ν)
    (a : α) (x : ℝ) :
    ∫ b, stieltjesOfMeasurableRat f hf.measurable (a, b) x ∂(ν a)
      = (κ a).real (univ ×ˢ Iic x) := by
  rw [← setIntegral_univ, setIntegral_stieltjesOfMeasurableRat hf _ _ MeasurableSet.univ]

end stieltjesOfMeasurableRat

section isRatCondKernelCDFAux

variable {f : α × β → ℚ → ℝ}

/-- This property implies `IsRatCondKernelCDF`. The measurability, integrability and integral
conditions are the same, but the limit properties of `IsRatCondKernelCDF` are replaced by
limits of integrals. -/
/-
**ProbabilityTheory.IsRatCondKernelCDFAux** 是 Mathlib 中的一个归纳类型，位于命名空间 `Probabili
tyTheory`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     {mα : MeasurableSpace α} →       {
mβ : MeasurableSpace β} →         (α × β → ℚ → ℝ) → ProbabilityTheory.Kernel α (
β × ℝ) → ProbabilityTheory.Kernel α β → Prop
参数：α × β → ℚ → ℝ；β × ℝ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This property implies `IsRatCondKernelCDF`. The measurability, integrability and
 integral
conditions are the same, but the limit properties of `IsRatCondKernelCDF` are re
placed by
limits of integrals.
-/
structure IsRatCondKernelCDFAux (f : α × β → ℚ → ℝ) (κ : Kernel α (β × ℝ)) (ν : Kernel α β) :
    Prop where
  measurable : Measurable f
  mono' (a : α) {q r : ℚ} (_hqr : q ≤ r) : ∀ᵐ c ∂(ν a), f (a, c) q ≤ f (a, c) r
  nonneg' (a : α) (q : ℚ) : ∀ᵐ c ∂(ν a), 0 ≤ f (a, c) q
  le_one' (a : α) (q : ℚ) : ∀ᵐ c ∂(ν a), f (a, c) q ≤ 1
  /- Same as `Tendsto (fun q : ℚ ↦ ∫ c, f (a, c) q ∂(ν a)) atBot (𝓝 0)` but slightly easier
  to prove in the current applications of this definition (some integral convergence lemmas
  currently apply only to `ℕ`, not `ℚ`) -/
  tendsto_integral_of_antitone (a : α) (seq : ℕ → ℚ) (_hs : Antitone seq)
    (_hs_tendsto : Tendsto seq atTop atBot) :
    Tendsto (fun m ↦ ∫ c, f (a, c) (seq m) ∂(ν a)) atTop (𝓝 0)
  /- Same as `Tendsto (fun q : ℚ ↦ ∫ c, f (a, c) q ∂(ν a)) atTop (𝓝 ((ν a).real univ))` but
  slightly easier to prove in the current applications of this definition (some integral convergence
  lemmas currently apply only to `ℕ`, not `ℚ`) -/
  tendsto_integral_of_monotone (a : α) (seq : ℕ → ℚ) (_hs : Monotone seq)
    (_hs_tendsto : Tendsto seq atTop atTop) :
    Tendsto (fun m ↦ ∫ c, f (a, c) (seq m) ∂(ν a)) atTop (𝓝 ((ν a).real univ))
  integrable (a : α) (q : ℚ) : Integrable (fun c ↦ f (a, c) q) (ν a)
  setIntegral (a : α) {A : Set β} (_hA : MeasurableSet A) (q : ℚ) :
    ∫ c in A, f (a, c) q ∂(ν a) = (κ a).real (A ×ˢ Iic ↑q)
/-
**ProbabilityTheory.IsRatCondKernelCDFAux.measurable_right** 是 Mathlib 中的一个定理，位于
命名空间 `ProbabilityTheory.IsRatCondKernelCDFAux`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β}   {κ : ProbabilityTheory.Kernel α (β × ℝ)} {ν : ProbabilityTheory.Kernel
 α β} {f : α × β → ℚ → ℝ},   ProbabilityTheory.IsRatCondKernelCDFAux f κ ν → ∀ (
a : α) (q : ℚ), Measurable fun t => f (a, t) q
参数：β × ℝ；a : α；q : ℚ；a, t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDFAux.measurable`：∀ {α : Type u_1} {β 
: Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α × β → ℚ → ℝ
}   {κ : ProbabilityTheory.Kernel α (β ×…
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `measurable_pi_iff`：measurable_pi_iff {g : α -> forall a, X a} : Measurab
le g ↔ forall a, Measurable fun x => g x a
· 使用定理 `measurable_prodMk_left`：measurable_prodMk_left {x : α} : Measurable (@Pr
od.mk _ β x)
-/
lemma IsRatCondKernelCDFAux.measurable_right (hf : IsRatCondKernelCDFAux f κ ν) (a : α) (q : ℚ) :
    Measurable (fun t ↦ f (a, t) q) := by
  let h := hf.measurable
  rw [measurable_pi_iff] at h
  exact (h q).comp measurable_prodMk_left
/-
**ProbabilityTheory.IsRatCondKernelCDFAux.mono** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory.IsRatCondKernelCDFAux`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β}   {κ : ProbabilityTheory.Kernel α (β × ℝ)} {ν : ProbabilityTheory.Kernel
 α β} {f : α × β → ℚ → ℝ},   ProbabilityTheory.IsRatCondKernelCDFAux f κ ν → ∀ (
a : α), ∀ᵐ (c : β) ∂ν a, Monotone (f (a, c))
参数：β × ℝ；a : α；c : β；f (a, c)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Encodable.countable`：∀ {α : Type u_1} [Encodable α], Countable α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Prop.countable`：∀ (p : Prop), Countable p
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDFAux.mono'`：∀ {α : Type u_1} {β : Typ
e u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α × β → ℚ → ℝ}   {
κ : ProbabilityTheory.Kernel α (β ×…
-/
lemma IsRatCondKernelCDFAux.mono (hf : IsRatCondKernelCDFAux f κ ν) (a : α) :
    ∀ᵐ c ∂(ν a), Monotone (f (a, c)) := by
  unfold Monotone
  simp_rw [ae_all_iff]
  exact fun _ _ hqr ↦ hf.mono' a hqr
/-
**ProbabilityTheory.IsRatCondKernelCDFAux.nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Prob
abilityTheory.IsRatCondKernelCDFAux`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β}   {κ : ProbabilityTheory.Kernel α (β × ℝ)} {ν : ProbabilityTheory.Kernel
 α β} {f : α × β → ℚ → ℝ},   ProbabilityTheory.IsRatCondKernelCDFAux f κ ν → ∀ (
a : α), ∀ᵐ (c : β) ∂ν a, ∀ (q : ℚ), 0 ≤ f (a, c) q
参数：β × ℝ；a : α；c : β；q : ℚ；a, c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
· 使用定理 `Encodable.countable`：∀ {α : Type u_1} [Encodable α], Countable α
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDFAux.nonneg'`：∀ {α : Type u_1} {β : T
ype u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α × β → ℚ → ℝ}  
 {κ : ProbabilityTheory.Kernel α (β ×…
-/
lemma IsRatCondKernelCDFAux.nonneg (hf : IsRatCondKernelCDFAux f κ ν) (a : α) :
    ∀ᵐ c ∂(ν a), ∀ q, 0 ≤ f (a, c) q := ae_all_iff.mpr <| hf.nonneg' a
/-
**ProbabilityTheory.IsRatCondKernelCDFAux.le_one** 是 Mathlib 中的一个定理，位于命名空间 `Prob
abilityTheory.IsRatCondKernelCDFAux`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β}   {κ : ProbabilityTheory.Kernel α (β × ℝ)} {ν : ProbabilityTheory.Kernel
 α β} {f : α × β → ℚ → ℝ},   ProbabilityTheory.IsRatCondKernelCDFAux f κ ν → ∀ (
a : α), ∀ᵐ (c : β) ∂ν a, ∀ (q : ℚ), f (a, c) q ≤ 1
参数：β × ℝ；a : α；c : β；q : ℚ；a, c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
· 使用定理 `Encodable.countable`：∀ {α : Type u_1} [Encodable α], Countable α
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDFAux.le_one'`：∀ {α : Type u_1} {β : T
ype u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α × β → ℚ → ℝ}  
 {κ : ProbabilityTheory.Kernel α (β ×…
-/
lemma IsRatCondKernelCDFAux.le_one (hf : IsRatCondKernelCDFAux f κ ν) (a : α) :
    ∀ᵐ c ∂(ν a), ∀ q, f (a, c) q ≤ 1 := ae_all_iff.mpr <| hf.le_one' a
/-
**ProbabilityTheory.IsRatCondKernelCDFAux.tendsto_zero_of_antitone** 是 Mathlib 中
的一个定理，位于命名空间 `ProbabilityTheory.IsRatCondKernelCDFAux`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β}   {κ : ProbabilityTheory.Kernel α (β × ℝ)} {ν : ProbabilityTheory.Kernel
 α β} {f : α × β → ℚ → ℝ},   ProbabilityTheory.IsRatCondKernelCDFAux f κ ν →    
 ∀ [ProbabilityTheory.IsFiniteKernel ν] (a : α) (seq : ℕ → ℚ),       Antitone se
q →         Filter.Tendsto seq Filter.atTop Filter.atBot →           ∀ᵐ (c : β) 
∂ν a, Filter.Tendsto (fun m => f (a, c) (seq m)) Filter.atTop (nhds 0)
参数：β × ℝ；a : α；seq : ℕ → ℚ；c : β；fun m => f (a, c) (seq m)；nhds 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.tendsto_of_integral_tendsto_of_antitone`：tendsto_of_integr
al_tendsto_of_antitone {μ : Measure α} {f : Nat -> α -> Real} {F : α -> Real} (h
f_int : forall n, Integrable (f n) μ) (hF_i…
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDFAux.integrable`：∀ {α : Type u_1} {β 
: Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α × β → ℚ → ℝ
}   {κ : ProbabilityTheory.Kernel α (β ×…
· 使用定理 `MeasureTheory.integrable_const`：integrable_const [IsFiniteMeasure μ] (c 
: β) : Integrable (fun _ : α => c) μ
· 使用定理 `ProbabilityTheory.IsFiniteKernel.isFiniteMeasure`：∀ {α : Type u_1} {β : 
Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheo
ry.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_zero`：integral_zero : ∫ _ : α, (0 : G) ∂μ = 0
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDFAux.tendsto_integral_of_antitone`：∀ 
{α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} 
{f : α × β → ℚ → ℝ}   {κ : ProbabilityTheory.Kernel α (β ×…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDFAux.mono`：∀ {α : Type u_1} {β : Type
 u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {κ : ProbabilityTheory
.Kernel α (β × ℝ)} {ν : Probabilit…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDFAux.nonneg`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {κ : ProbabilityTheo
ry.Kernel α (β × ℝ)} {ν : Probabilit…
-/
lemma IsRatCondKernelCDFAux.tendsto_zero_of_antitone (hf : IsRatCondKernelCDFAux f κ ν)
    [IsFiniteKernel ν] (a : α) (seq : ℕ → ℚ) (hseq : Antitone seq)
    (hseq_tendsto : Tendsto seq atTop atBot) :
    ∀ᵐ c ∂(ν a), Tendsto (fun m ↦ f (a, c) (seq m)) atTop (𝓝 0) := by
  refine tendsto_of_integral_tendsto_of_antitone ?_ (integrable_const _) ?_ ?_ ?_
  · exact fun n ↦ hf.integrable a (seq n)
  · rw [integral_zero]
    exact hf.tendsto_integral_of_antitone a seq hseq hseq_tendsto
  · filter_upwards [hf.mono a] with t ht using fun n m hnm ↦ ht (hseq hnm)
  · filter_upwards [hf.nonneg a] with c hc using fun i ↦ hc (seq i)
/-
**ProbabilityTheory.IsRatCondKernelCDFAux.tendsto_one_of_monotone** 是 Mathlib 中的
一个定理，位于命名空间 `ProbabilityTheory.IsRatCondKernelCDFAux`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β}   {κ : ProbabilityTheory.Kernel α (β × ℝ)} {ν : ProbabilityTheory.Kernel
 α β} {f : α × β → ℚ → ℝ},   ProbabilityTheory.IsRatCondKernelCDFAux f κ ν →    
 ∀ [ProbabilityTheory.IsFiniteKernel ν] (a : α) (seq : ℕ → ℚ),       Monotone se
q →         Filter.Tendsto seq Filter.atTop Filter.atTop →           ∀ᵐ (c : β) 
∂ν a, Filter.Tendsto (fun m => f (a, c) (seq m)) Filter.atTop (nhds 1)
参数：β × ℝ；a : α；seq : ℕ → ℚ；c : β；fun m => f (a, c) (seq m)；nhds 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.tendsto_of_integral_tendsto_of_monotone`：tendsto_of_integr
al_tendsto_of_monotone {μ : Measure α} {f : Nat -> α -> Real} {F : α -> Real} (h
f_int : forall n, Integrable (f n) μ) (hF_i…
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDFAux.integrable`：∀ {α : Type u_1} {β 
: Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α × β → ℚ → ℝ
}   {κ : ProbabilityTheory.Kernel α (β ×…
· 使用定理 `MeasureTheory.integrable_const`：integrable_const [IsFiniteMeasure μ] (c 
: β) : Integrable (fun _ : α => c) μ
· 使用定理 `ProbabilityTheory.IsFiniteKernel.isFiniteMeasure`：∀ {α : Type u_1} {β : 
Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheo
ry.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_const`：integral_const (c : E) : ∫ _ : α, c ∂μ = μ
.real univ • c
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDFAux.tendsto_integral_of_monotone`：∀ 
{α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} 
{f : α × β → ℚ → ℝ}   {κ : ProbabilityTheory.Kernel α (β ×…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDFAux.mono`：∀ {α : Type u_1} {β : Type
 u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {κ : ProbabilityTheory
.Kernel α (β × ℝ)} {ν : Probabilit…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDFAux.le_one`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {κ : ProbabilityTheo
ry.Kernel α (β × ℝ)} {ν : Probabilit…
-/
lemma IsRatCondKernelCDFAux.tendsto_one_of_monotone (hf : IsRatCondKernelCDFAux f κ ν)
    [IsFiniteKernel ν] (a : α) (seq : ℕ → ℚ) (hseq : Monotone seq)
    (hseq_tendsto : Tendsto seq atTop atTop) :
    ∀ᵐ c ∂(ν a), Tendsto (fun m ↦ f (a, c) (seq m)) atTop (𝓝 1) := by
  refine tendsto_of_integral_tendsto_of_monotone ?_ (integrable_const _) ?_ ?_ ?_
  · exact fun n ↦ hf.integrable a (seq n)
  · rw [MeasureTheory.integral_const, smul_eq_mul, mul_one]
    exact hf.tendsto_integral_of_monotone a seq hseq hseq_tendsto
  · filter_upwards [hf.mono a] with t ht using fun n m hnm ↦ ht (hseq hnm)
  · filter_upwards [hf.le_one a] with c hc using fun i ↦ hc (seq i)
/-
**ProbabilityTheory.IsRatCondKernelCDFAux.tendsto_atTop_one** 是 Mathlib 中的一个定理，位
于命名空间 `ProbabilityTheory.IsRatCondKernelCDFAux`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β}   {κ : ProbabilityTheory.Kernel α (β × ℝ)} {ν : ProbabilityTheory.Kernel
 α β} {f : α × β → ℚ → ℝ},   ProbabilityTheory.IsRatCondKernelCDFAux f κ ν →    
 ∀ [ProbabilityTheory.IsFiniteKernel ν] (a : α), ∀ᵐ (t : β) ∂ν a, Filter.Tendsto
 (f (a, t)) Filter.atTop (nhds 1)
参数：β × ℝ；a : α；t : β；f (a, t)；nhds 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDFAux.tendsto_one_of_monotone`：∀ {α : 
Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {κ 
: ProbabilityTheory.Kernel α (β × ℝ)} {ν : Probabilit…
· 使用定理 `Nat.mono_cast`：mono_cast : Monotone (Nat.cast : Nat -> α)
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `tendsto_natCast_atTop_atTop`：tendsto_natCast_atTop_atTop [Semiring R] [P
artialOrder R] [IsOrderedRing R] [Archimedean R] : Tendsto ((↑) : Nat -> R) atTo
p atTop
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanRat`：Archimedean ℚ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDFAux.mono`：∀ {α : Type u_1} {β : Type
 u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {κ : ProbabilityTheory
.Kernel α (β × ℝ)} {ν : Probabilit…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendsto_iff_tendsto_subseq_of_monotone`：tendsto_iff_tendsto_subseq_of_mo
notone {ι₁ ι₂ α : Type*} [SemilatticeSup ι₁] [Preorder ι₂] [Nonempty ι₁] [Topolo
gicalSpace α] [Conditionally…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
-/
lemma IsRatCondKernelCDFAux.tendsto_atTop_one (hf : IsRatCondKernelCDFAux f κ ν) [IsFiniteKernel ν]
    (a : α) :
    ∀ᵐ t ∂(ν a), Tendsto (f (a, t)) atTop (𝓝 1) := by
  suffices ∀ᵐ t ∂(ν a), Tendsto (fun (n : ℕ) ↦ f (a, t) n) atTop (𝓝 1) by
    filter_upwards [this, hf.mono a] with t ht h_mono
    rw [tendsto_iff_tendsto_subseq_of_monotone h_mono tendsto_natCast_atTop_atTop]
    exact ht
  filter_upwards [hf.tendsto_one_of_monotone a Nat.cast Nat.mono_cast tendsto_natCast_atTop_atTop]
    with x hx using hx
/-
**ProbabilityTheory.IsRatCondKernelCDFAux.tendsto_atBot_zero** 是 Mathlib 中的一个定理，
位于命名空间 `ProbabilityTheory.IsRatCondKernelCDFAux`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β}   {κ : ProbabilityTheory.Kernel α (β × ℝ)} {ν : ProbabilityTheory.Kernel
 α β} {f : α × β → ℚ → ℝ},   ProbabilityTheory.IsRatCondKernelCDFAux f κ ν →    
 ∀ [ProbabilityTheory.IsFiniteKernel ν] (a : α), ∀ᵐ (t : β) ∂ν a, Filter.Tendsto
 (f (a, t)) Filter.atBot (nhds 0)
参数：β × ℝ；a : α；t : β；f (a, t)；nhds 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDFAux.tendsto_zero_of_antitone`：∀ {α :
 Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {κ
 : ProbabilityTheory.Kernel α (β × ℝ)} {ν : Probabilit…
· 使用定理 `Monotone.neg`：∀ {α : Type u} {β : Type u_1} [inst : AddGroup α] [inst_1 
: Preorder α] [AddLeftMono α] [AddRightMono α]   [inst_4 : Preorder β] {f : β → 
α}…
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Nat.mono_cast`：mono_cast : Monotone (Nat.cast : Nat -> α)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_neg_atBot_iff`：∀ {α : Type u_1} {G : Type u_2} [inst : Ad
dCommGroup G] [inst_1 : PartialOrder G] [IsOrderedAddMonoid G] {l : Filter α}   
{f : α → G}, Filte…
· 使用定理 `tendsto_natCast_atTop_atTop`：tendsto_natCast_atTop_atTop [Semiring R] [P
artialOrder R] [IsOrderedRing R] [Archimedean R] : Tendsto ((↑) : Nat -> R) atTo
p atTop
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanRat`：Archimedean ℚ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDFAux.mono`：∀ {α : Type u_1} {β : Type
 u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {κ : ProbabilityTheory
.Kernel α (β × ℝ)} {ν : Probabilit…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Monotone.comp_antitone`：Monotone.comp_antitone (hg : Monotone g) (hf : A
ntitone f) : Antitone (g ∘ f)
· 使用定理 `monotone_id`：monotone_id [Preorder α] : Monotone (id : α -> α)
· 使用定理 `tendsto_iff_tendsto_subseq_of_antitone`：tendsto_iff_tendsto_subseq_of_an
titone {ι₁ ι₂ α : Type*} [SemilatticeSup ι₁] [Preorder ι₂] [Nonempty ι₁] [Topolo
gicalSpace α] [Conditionally…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.tendsto_comp_neg_atTop_iff`：∀ {α : Type u_1} {G : Type u_2} [inst
 : AddCommGroup G] [inst_1 : PartialOrder G] [IsOrderedAddMonoid G] {l : Filter 
α}   {f : G → α}, Filte…
-/
lemma IsRatCondKernelCDFAux.tendsto_atBot_zero (hf : IsRatCondKernelCDFAux f κ ν) [IsFiniteKernel ν]
    (a : α) :
    ∀ᵐ t ∂(ν a), Tendsto (f (a, t)) atBot (𝓝 0) := by
  suffices ∀ᵐ t ∂(ν a), Tendsto (fun q : ℚ ↦ f (a, t) (-q)) atTop (𝓝 0) by
    filter_upwards [this] with t ht
    exact tendsto_comp_neg_atTop_iff.mp ht
  suffices ∀ᵐ t ∂(ν a), Tendsto (fun (n : ℕ) ↦ f (a, t) (-n)) atTop (𝓝 0) by
    filter_upwards [this, hf.mono a] with t ht h_mono
    have h_anti : Antitone (fun q ↦ f (a, t) (-q)) := h_mono.comp_antitone monotone_id.neg
    exact (tendsto_iff_tendsto_subseq_of_antitone h_anti tendsto_natCast_atTop_atTop).mpr ht
  exact hf.tendsto_zero_of_antitone _ _ Nat.mono_cast.neg
    (tendsto_neg_atBot_iff.mpr tendsto_natCast_atTop_atTop)
/-
**ProbabilityTheory.IsRatCondKernelCDFAux.bddBelow_range** 是 Mathlib 中的一个定理，位于命名
空间 `ProbabilityTheory.IsRatCondKernelCDFAux`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β}   {κ : ProbabilityTheory.Kernel α (β × ℝ)} {ν : ProbabilityTheory.Kernel
 α β} {f : α × β → ℚ → ℝ},   ProbabilityTheory.IsRatCondKernelCDFAux f κ ν →    
 ∀ (a : α), ∀ᵐ (t : β) ∂ν a, ∀ (q : ℚ), BddBelow (Set.range fun r => f (a, t) ↑r
)
参数：β × ℝ；a : α；t : β；q : ℚ；Set.range fun r => f (a, t) ↑r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDFAux.nonneg`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {κ : ProbabilityTheo
ry.Kernel α (β × ℝ)} {ν : Probabilit…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma IsRatCondKernelCDFAux.bddBelow_range (hf : IsRatCondKernelCDFAux f κ ν) (a : α) :
    ∀ᵐ t ∂(ν a), ∀ q : ℚ, BddBelow (range fun (r : Ioi q) ↦ f (a, t) r) := by
  filter_upwards [hf.nonneg a] with c hc
  refine fun q ↦ ⟨0, ?_⟩
  simp [mem_lowerBounds, hc]
/-
**ProbabilityTheory.IsRatCondKernelCDFAux.integrable_iInf_rat_gt** 是 Mathlib 中的一
个定理，位于命名空间 `ProbabilityTheory.IsRatCondKernelCDFAux`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β}   {κ : ProbabilityTheory.Kernel α (β × ℝ)} {ν : ProbabilityTheory.Kernel
 α β} {f : α × β → ℚ → ℝ},   ProbabilityTheory.IsRatCondKernelCDFAux f κ ν →    
 ∀ [ProbabilityTheory.IsFiniteKernel ν] (a : α) (q : ℚ), MeasureTheory.Integrabl
e (fun t => ⨅ r, f (a, t) ↑r) (ν a)
参数：β × ℝ；a : α；q : ℚ；fun t => ⨅ r, f (a, t) ↑r；ν a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `Measurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 :…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Measurable.iInf`：∀ {α : Type u_1} {δ : Type u_4} [inst : TopologicalSpac
e α] {mα : MeasurableSpace α} [BorelSpace α]   {mδ : MeasurableSpace δ} [inst_2 
: Con…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `SetCoe.countable`：∀ {α : Type u} [Countable α] (s : Set α), Countable ↑s
· 使用定理 `Encodable.countable`：∀ {α : Type u_1} [Encodable α], Countable α
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDFAux.measurable_right`：∀ {α : Type u_
1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {κ : Proba
bilityTheory.Kernel α (β × ℝ)} {ν : Probabilit…
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.eLpNorm_le_of_ae_bound`：eLpNorm_le_of_ae_bound {f : α -> F
} {C : Real} (hfC : forallᵐ x ∂μ, ‖f x‖ <= C) : eLpNorm f p μ <= μ Set.univ ^ p.
toReal⁻¹ * ENNReal.ofReal …
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDFAux.le_one`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {κ : ProbabilityTheo
ry.Kernel α (β × ℝ)} {ν : Probabilit…
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDFAux.nonneg`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {κ : ProbabilityTheo
ry.Kernel α (β × ℝ)} {ν : Probabilit…
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDFAux.bddBelow_range`：∀ {α : Type u_1}
 {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {κ : Probabi
lityTheory.Kernel α (β × ℝ)} {ν : Probabilit…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Real.norm_eq_abs`：norm_eq_abs (r : Real) : ‖r‖ = |r|
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `le_ciInf`：le_ciInf [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, c <=
 f x) : c <= iInf f
· 使用定理 `Set.nonempty_Ioi_subtype`：∀ {α : Type u_1} [inst : Preorder α] {a : α} [
NoMaxOrder α], Nonempty ↑(Set.Ioi a)
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `ciInf_le_of_le`：ciInf_le_of_le {f : ι -> α} (H : BddBelow (range f)) (c 
: ι) (h : f c <= a) : iInf f <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
（共 43 条，此处仅展示前 30 条）
-/
lemma IsRatCondKernelCDFAux.integrable_iInf_rat_gt (hf : IsRatCondKernelCDFAux f κ ν)
    [IsFiniteKernel ν] (a : α) (q : ℚ) :
    Integrable (fun t ↦ ⨅ r : Ioi q, f (a, t) r) (ν a) := by
  rw [← memLp_one_iff_integrable]
  refine ⟨(Measurable.iInf fun i ↦ hf.measurable_right a _).aestronglyMeasurable, ?_⟩
  refine (?_ : _ ≤ (ν a univ : ℝ≥0∞)).trans_lt (measure_lt_top _ _)
  refine (eLpNorm_le_of_ae_bound (C := 1) ?_).trans (by simp)
  filter_upwards [hf.bddBelow_range a, hf.nonneg a, hf.le_one a]
    with t hbdd_below h_nonneg h_le_one
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · refine ciInf_le_of_le ?_ ?_ ?_
    · exact hbdd_below _
    · exact ⟨q + 1, by simp⟩
    · exact h_le_one _
  · exact le_ciInf fun r ↦ h_nonneg _
/-
**ProbabilityTheory._root_.MeasureTheory.Measure.iInf_rat_gt_prod_Iic** 是 Mathli
b 中的一个引理，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MeasureTheory.Measure.iInf_rat_gt_prod_Iic {ρ : Measure (α × ℝ)} [IsFiniteMeasure ρ]
    {s : Set α} (hs : MeasurableSet s) (t : ℚ) :
    ⨅ r : { r' : ℚ // t < r' }, ρ (s ×ˢ Iic (r : ℝ)) = ρ (s ×ˢ Iic (t : ℝ)) := by
  rw [← Monotone.measure_iInter]
  · rw [← prod_iInter]
    congr with x : 1
    simp only [mem_iInter, mem_Iic, Subtype.forall]
    refine ⟨fun h ↦ ?_, fun h a hta ↦ h.trans ?_⟩
    · refine le_of_forall_lt_rat_imp_le fun q htq ↦ h q ?_
      exact mod_cast htq
    · exact mod_cast hta.le
  · exact fun r r' hrr' ↦ prod_mono_right <| by gcongr
  · exact fun _ => (hs.prod measurableSet_Iic).nullMeasurableSet
  · exact ⟨⟨t + 1, lt_add_one _⟩, measure_ne_top ρ _⟩
/-
**ProbabilityTheory.IsRatCondKernelCDFAux.setIntegral_iInf_rat_gt** 是 Mathlib 中的
一个定理，位于命名空间 `ProbabilityTheory.IsRatCondKernelCDFAux`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β}   {κ : ProbabilityTheory.Kernel α (β × ℝ)} {ν : ProbabilityTheory.Kernel
 α β} {f : α × β → ℚ → ℝ},   ProbabilityTheory.IsRatCondKernelCDFAux f κ ν →    
 ∀ [ProbabilityTheory.IsFiniteKernel κ] [ProbabilityTheory.IsFiniteKernel ν] (a 
: α) (q : ℚ) {A : Set β},       MeasurableSet A → ∫ (t : β) in A, ⨅ r, f (a, t) 
↑r ∂ν a = (κ a).real (A ×ˢ Set.Iic ↑q)
参数：β × ℝ；a : α；q : ℚ；t : β；a, t；κ a；A ×ˢ Set.Iic ↑q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDFAux.setIntegral`：∀ {α : Type u_1} {β
 : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α × β → ℚ → 
ℝ}   {κ : ProbabilityTheory.Kernel α (β ×…
· 使用定理 `MeasureTheory.setIntegral_mono_ae`：setIntegral_mono_ae (h : f <=ᵐ[μ] g) 
: ∫ x in s, f x ∂μ <= ∫ x in s, g x ∂μ
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `MeasureTheory.Integrable.integrableOn`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDFAux.integrable_iInf_rat_gt`：∀ {α : T
ype u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {κ :
 ProbabilityTheory.Kernel α (β × ℝ)} {ν : Probabilit…
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDFAux.integrable`：∀ {α : Type u_1} {β 
: Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α × β → ℚ → ℝ
}   {κ : ProbabilityTheory.Kernel α (β ×…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDFAux.bddBelow_range`：∀ {α : Type u_1}
 {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {κ : Probabi
lityTheory.Kernel α (β × ℝ)} {ν : Probabilit…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ciInf_le`：ciInf_le {f : ι -> α} (H : BddBelow (range f)) (c : ι) : iInf 
f <= f c
· 使用定理 `le_ciInf`：le_ciInf [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, c <=
 f x) : c <= iInf f
· 使用定理 `Set.nonempty_Ioi_subtype`：∀ {α : Type u_1} [inst : Preorder α] {a : α} [
NoMaxOrder α], Nonempty ↑(Set.Ioi a)
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `MeasureTheory.measureReal_def`：measureReal_def {α : Type*} {m : Measurab
leSpace α} (μ : Measure α) (s : Set α) : μ.real s = (μ s).toReal
· 使用定理 `MeasureTheory.Measure.iInf_rat_gt_prod_Iic`：∀ {α : Type u_1} {mα : Measu
rableSpace α} {ρ : MeasureTheory.Measure (α × ℝ)} [MeasureTheory.IsFiniteMeasure
 ρ]   {s : Set α}, MeasurableSet…
· 使用定理 `ProbabilityTheory.IsFiniteKernel.isFiniteMeasure`：∀ {α : Type u_1} {β : 
Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheo
ry.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `ENNReal.toReal_iInf`：toReal_iInf (hf : forall i, f i != ∞) : (iInf f).to
Real = ⨅ i, (f i).toReal
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDFAux.mono`：∀ {α : Type u_1} {β : Type
 u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {κ : ProbabilityTheory
.Kernel α (β × ℝ)} {ν : Probabilit…
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
lemma IsRatCondKernelCDFAux.setIntegral_iInf_rat_gt (hf : IsRatCondKernelCDFAux f κ ν)
    [IsFiniteKernel κ] [IsFiniteKernel ν] (a : α) (q : ℚ) {A : Set β} (hA : MeasurableSet A) :
    ∫ t in A, ⨅ r : Ioi q, f (a, t) r ∂(ν a) = (κ a).real (A ×ˢ Iic (q : ℝ)) := by
  refine le_antisymm ?_ ?_
  · have h : ∀ r : Ioi q, ∫ t in A, ⨅ r' : Ioi q, f (a, t) r' ∂(ν a)
        ≤ (κ a).real (A ×ˢ Iic (r : ℝ)) := by
      intro r
      rw [← hf.setIntegral a hA]
      refine setIntegral_mono_ae ?_ ?_ ?_
      · exact (hf.integrable_iInf_rat_gt _ _).integrableOn
      · exact (hf.integrable _ _).integrableOn
      · filter_upwards [hf.bddBelow_range a] with t ht using ciInf_le (ht _) r
    calc ∫ t in A, ⨅ r : Ioi q, f (a, t) r ∂(ν a)
      ≤ ⨅ r : Ioi q, (κ a).real (A ×ˢ Iic (r : ℝ)) := le_ciInf h
    _ = (κ a).real (A ×ˢ Iic (q : ℝ)) := by
        rw [measureReal_def, ← Measure.iInf_rat_gt_prod_Iic hA q]
        exact (ENNReal.toReal_iInf (fun r ↦ measure_ne_top _ _)).symm
  · rw [← hf.setIntegral a hA]
    refine setIntegral_mono_ae ?_ ?_ ?_
    · exact (hf.integrable _ _).integrableOn
    · exact (hf.integrable_iInf_rat_gt _ _).integrableOn
    · filter_upwards [hf.mono a] with c h_mono using le_ciInf (fun r ↦ h_mono (le_of_lt r.prop))
/-
**ProbabilityTheory.IsRatCondKernelCDFAux.iInf_rat_gt_eq** 是 Mathlib 中的一个定理，位于命名
空间 `ProbabilityTheory.IsRatCondKernelCDFAux`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β}   {κ : ProbabilityTheory.Kernel α (β × ℝ)} {ν : ProbabilityTheory.Kernel
 α β} {f : α × β → ℚ → ℝ},   ProbabilityTheory.IsRatCondKernelCDFAux f κ ν →    
 ∀ [ProbabilityTheory.IsFiniteKernel κ] [ProbabilityTheory.IsFiniteKernel ν] (a 
: α),       ∀ᵐ (t : β) ∂ν a, ∀ (q : ℚ), ⨅ r, f (a, t) ↑r = f (a, t) q
参数：β × ℝ；a : α；t : β；q : ℚ；a, t；a, t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
· 使用定理 `Encodable.countable`：∀ {α : Type u_1} [Encodable α], Countable α
· 使用定理 `MeasureTheory.ae_eq_of_forall_setIntegral_eq_of_sigmaFinite`：ae_eq_of_fo
rall_setIntegral_eq_of_sigmaFinite [SigmaFinite μ] {f g : α -> E} (hf_int_finite
 : forall s, MeasurableSet s -> μ s < ∞ -> Integr…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `ProbabilityTheory.IsFiniteKernel.isFiniteMeasure`：∀ {α : Type u_1} {β : 
Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheo
ry.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `MeasureTheory.Integrable.integrableOn`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDFAux.integrable_iInf_rat_gt`：∀ {α : T
ype u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {κ :
 ProbabilityTheory.Kernel α (β × ℝ)} {ν : Probabilit…
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDFAux.integrable`：∀ {α : Type u_1} {β 
: Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α × β → ℚ → ℝ
}   {κ : ProbabilityTheory.Kernel α (β ×…
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDFAux.setIntegral`：∀ {α : Type u_1} {β
 : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α × β → ℚ → 
ℝ}   {κ : ProbabilityTheory.Kernel α (β ×…
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDFAux.setIntegral_iInf_rat_gt`：∀ {α : 
Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {κ 
: ProbabilityTheory.Kernel α (β × ℝ)} {ν : Probabilit…
-/
lemma IsRatCondKernelCDFAux.iInf_rat_gt_eq (hf : IsRatCondKernelCDFAux f κ ν) [IsFiniteKernel κ]
    [IsFiniteKernel ν] (a : α) :
    ∀ᵐ t ∂(ν a), ∀ q : ℚ, ⨅ r : Ioi q, f (a, t) r = f (a, t) q := by
  rw [ae_all_iff]
  refine fun q ↦ ae_eq_of_forall_setIntegral_eq_of_sigmaFinite (μ := ν a) ?_ ?_ ?_
  · exact fun _ _ _ ↦ (hf.integrable_iInf_rat_gt _ _).integrableOn
  · exact fun _ _ _ ↦ (hf.integrable a _).integrableOn
  · intro s hs _
    rw [hf.setIntegral _ hs, hf.setIntegral_iInf_rat_gt _ _ hs]
/-
**ProbabilityTheory.IsRatCondKernelCDFAux.isRatStieltjesPoint_ae** 是 Mathlib 中的一
个定理，位于命名空间 `ProbabilityTheory.IsRatCondKernelCDFAux`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β}   {κ : ProbabilityTheory.Kernel α (β × ℝ)} {ν : ProbabilityTheory.Kernel
 α β} {f : α × β → ℚ → ℝ},   ProbabilityTheory.IsRatCondKernelCDFAux f κ ν →    
 ∀ [ProbabilityTheory.IsFiniteKernel κ] [ProbabilityTheory.IsFiniteKernel ν] (a 
: α),       ∀ᵐ (t : β) ∂ν a, ProbabilityTheory.IsRatStieltjesPoint f (a, t)
参数：β × ℝ；a : α；t : β；a, t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDFAux.mono`：∀ {α : Type u_1} {β : Type
 u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {κ : ProbabilityTheory
.Kernel α (β × ℝ)} {ν : Probabilit…
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDFAux.iInf_rat_gt_eq`：∀ {α : Type u_1}
 {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {κ : Probabi
lityTheory.Kernel α (β × ℝ)} {ν : Probabilit…
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDFAux.tendsto_atBot_zero`：∀ {α : Type 
u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {κ : Pro
babilityTheory.Kernel α (β × ℝ)} {ν : Probabilit…
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDFAux.tendsto_atTop_one`：∀ {α : Type u
_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {κ : Prob
abilityTheory.Kernel α (β × ℝ)} {ν : Probabilit…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
-/
lemma IsRatCondKernelCDFAux.isRatStieltjesPoint_ae (hf : IsRatCondKernelCDFAux f κ ν)
    [IsFiniteKernel κ] [IsFiniteKernel ν] (a : α) :
    ∀ᵐ t ∂(ν a), IsRatStieltjesPoint f (a, t) := by
  filter_upwards [hf.tendsto_atTop_one a, hf.tendsto_atBot_zero a,
    hf.iInf_rat_gt_eq a, hf.mono a] with t ht_top ht_bot ht_iInf h_mono
  exact ⟨h_mono, ht_top, ht_bot, ht_iInf⟩
/-
**ProbabilityTheory.IsRatCondKernelCDFAux.isRatCondKernelCDF** 是 Mathlib 中的一个定理，
位于命名空间 `ProbabilityTheory.IsRatCondKernelCDFAux`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β}   {κ : ProbabilityTheory.Kernel α (β × ℝ)} {ν : ProbabilityTheory.Kernel
 α β} {f : α × β → ℚ → ℝ},   ProbabilityTheory.IsRatCondKernelCDFAux f κ ν →    
 ∀ [ProbabilityTheory.IsFiniteKernel κ] [ProbabilityTheory.IsFiniteKernel ν],   
    ProbabilityTheory.IsRatCondKernelCDF f κ ν
参数：β × ℝ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDFAux.measurable`：∀ {α : Type u_1} {β 
: Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α × β → ℚ → ℝ
}   {κ : ProbabilityTheory.Kernel α (β ×…
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDFAux.isRatStieltjesPoint_ae`：∀ {α : T
ype u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {κ :
 ProbabilityTheory.Kernel α (β × ℝ)} {ν : Probabilit…
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDFAux.integrable`：∀ {α : Type u_1} {β 
: Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α × β → ℚ → ℝ
}   {κ : ProbabilityTheory.Kernel α (β ×…
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDFAux.setIntegral`：∀ {α : Type u_1} {β
 : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α × β → ℚ → 
ℝ}   {κ : ProbabilityTheory.Kernel α (β ×…
-/
lemma IsRatCondKernelCDFAux.isRatCondKernelCDF (hf : IsRatCondKernelCDFAux f κ ν) [IsFiniteKernel κ]
    [IsFiniteKernel ν] :
    IsRatCondKernelCDF f κ ν where
  measurable := hf.measurable
  isRatStieltjesPoint_ae := hf.isRatStieltjesPoint_ae
  integrable := hf.integrable
  setIntegral := hf.setIntegral

end isRatCondKernelCDFAux

section IsCondKernelCDF

variable {f : α × β → StieltjesFunction ℝ}

/-- A function `f : α × β → StieltjesFunction ℝ` is called a conditional kernel CDF of `κ` with
respect to `ν` if it is measurable, tends to 0 at -∞ and to 1 at +∞ for all `p : α × β`,
`fun b ↦ f (a, b) x` is `(ν a)`-integrable for all `a : α` and `x : ℝ` and for all
measurable sets `s : Set β`, `∫ b in s, f (a, b) x ∂(ν a) = (κ a).real (s ×ˢ Iic x)`. -/
/-
**ProbabilityTheory.IsCondKernelCDF** 是 Mathlib 中的一个归纳类型，位于命名空间 `ProbabilityTheo
ry`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     {mα : MeasurableSpace α} →       {
mβ : MeasurableSpace β} →         (α × β → StieltjesFunction ℝ) → ProbabilityThe
ory.Kernel α (β × ℝ) → ProbabilityTheory.Kernel α β → Prop
参数：α × β → StieltjesFunction ℝ；β × ℝ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f : α × β → StieltjesFunction ℝ` is called a conditional kernel CDF 
of `κ` with
respect to `ν` if it is measurable, tends to 0 at -∞ and to 1 at +∞ for all `p :
 α × β`,
`fun b ↦ f (a, b) x` is `(ν a)`-integrable for all `a : α` and `x : ℝ` and for a
ll
measurable sets `s : Set β`, `∫ b in s, f (a, b) x ∂(ν a) = (κ a).real (s ×ˢ Iic
 x)`.
-/
structure IsCondKernelCDF (f : α × β → StieltjesFunction ℝ) (κ : Kernel α (β × ℝ))
    (ν : Kernel α β) : Prop where
  measurable (x : ℝ) : Measurable fun p ↦ f p x
  integrable (a : α) (x : ℝ) : Integrable (fun b ↦ f (a, b) x) (ν a)
  tendsto_atTop_one (p : α × β) : Tendsto (f p) atTop (𝓝 1)
  tendsto_atBot_zero (p : α × β) : Tendsto (f p) atBot (𝓝 0)
  setIntegral (a : α) {s : Set β} (_hs : MeasurableSet s) (x : ℝ) :
    ∫ b in s, f (a, b) x ∂(ν a) = (κ a).real (s ×ˢ Iic x)
/-
**ProbabilityTheory.IsCondKernelCDF.nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Probabilit
yTheory.IsCondKernelCDF`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β}   {κ : ProbabilityTheory.Kernel α (β × ℝ)} {ν : ProbabilityTheory.Kernel
 α β} {f : α × β → StieltjesFunction ℝ},   ProbabilityTheory.IsCondKernelCDF f κ
 ν → ∀ (p : α × β) (x : ℝ), 0 ≤ ↑(f p) x
参数：β × ℝ；p : α × β；x : ℝ；f p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.le_of_tendsto`：Monotone.le_of_tendsto [TopologicalSpace α] [Pre
order α] [OrderClosedTopology α] [Preorder β] [IsCodirectedOrder β] {f : β -> α}
 {a : α} (hf…
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `instIsCodirectedOrder`：∀ {R : Type u_3} [inst : Ring R] [inst_1 : Partia
lOrder R] [IsOrderedRing R] [Archimedean R], IsCodirectedOrder R
· 使用定理 `StieltjesFunction.mono`：mono : Monotone f
· 使用定理 `ProbabilityTheory.IsCondKernelCDF.tendsto_atBot_zero`：∀ {α : Type u_1} {
β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α × β → Sti
eltjesFunction ℝ}   {κ : ProbabilityTheory…
-/
lemma IsCondKernelCDF.nonneg (hf : IsCondKernelCDF f κ ν) (p : α × β) (x : ℝ) : 0 ≤ f p x :=
  Monotone.le_of_tendsto (f p).mono (hf.tendsto_atBot_zero p) x
/-
**ProbabilityTheory.IsCondKernelCDF.le_one** 是 Mathlib 中的一个定理，位于命名空间 `Probabilit
yTheory.IsCondKernelCDF`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β}   {κ : ProbabilityTheory.Kernel α (β × ℝ)} {ν : ProbabilityTheory.Kernel
 α β} {f : α × β → StieltjesFunction ℝ},   ProbabilityTheory.IsCondKernelCDF f κ
 ν → ∀ (p : α × β) (x : ℝ), ↑(f p) x ≤ 1
参数：β × ℝ；p : α × β；x : ℝ；f p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.ge_of_tendsto`：Monotone.ge_of_tendsto [TopologicalSpace α] [Pre
order α] [OrderClosedTopology α] [Preorder β] [IsDirectedOrder β] {f : β -> α} {
a : α} (hf :…
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `StieltjesFunction.mono`：mono : Monotone f
· 使用定理 `ProbabilityTheory.IsCondKernelCDF.tendsto_atTop_one`：∀ {α : Type u_1} {β
 : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α × β → Stie
ltjesFunction ℝ}   {κ : ProbabilityTheory…
-/
lemma IsCondKernelCDF.le_one (hf : IsCondKernelCDF f κ ν) (p : α × β) (x : ℝ) : f p x ≤ 1 :=
  Monotone.ge_of_tendsto (f p).mono (hf.tendsto_atTop_one p) x
/-
**ProbabilityTheory.IsCondKernelCDF.integral** 是 Mathlib 中的一个定理，位于命名空间 `Probabil
ityTheory.IsCondKernelCDF`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β}   {κ : ProbabilityTheory.Kernel α (β × ℝ)} {ν : ProbabilityTheory.Kernel
 α β} {f : α × β → StieltjesFunction ℝ},   ProbabilityTheory.IsCondKernelCDF f κ
 ν →     ∀ (a : α) (x : ℝ), ∫ (b : β), ↑(f (a, b)) x ∂ν a = (κ a).real (Set.univ
 ×ˢ Set.Iic x)
参数：β × ℝ；a : α；x : ℝ；b : β；f (a, b)；κ a；Set.univ ×ˢ Set.Iic x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.IsCondKernelCDF.setIntegral`：∀ {α : Type u_1} {β : Typ
e u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α × β → StieltjesF
unction ℝ}   {κ : ProbabilityTheory…
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
-/
lemma IsCondKernelCDF.integral
    {f : α × β → StieltjesFunction ℝ} (hf : IsCondKernelCDF f κ ν) (a : α) (x : ℝ) :
    ∫ b, f (a, b) x ∂(ν a) = (κ a).real (univ ×ˢ Iic x) := by
  rw [← hf.setIntegral _ MeasurableSet.univ, Measure.restrict_univ]
/-
**ProbabilityTheory.IsCondKernelCDF.setLIntegral** 是 Mathlib 中的一个定理，位于命名空间 `Prob
abilityTheory.IsCondKernelCDF`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β}   {κ : ProbabilityTheory.Kernel α (β × ℝ)} {ν : ProbabilityTheory.Kernel
 α β} [ProbabilityTheory.IsFiniteKernel κ]   {f : α × β → StieltjesFunction ℝ}, 
  ProbabilityTheory.IsCondKernelCDF f κ ν →     ∀ (a : α) {s : Set β},       Mea
surableSet s → ∀ (x : ℝ), ∫⁻ (b : β) in s, ENNReal.ofReal (↑(f (a, b)) x) ∂ν a =
 (κ a) (s ×ˢ Set.Iic x)
参数：β × ℝ；a : α；x : ℝ；b : β；↑(f (a, b)) x；κ a；s ×ˢ Set.Iic x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.ofReal_integral_eq_lintegral_ofReal`：ofReal_integral_eq_li
ntegral_ofReal {f : α -> Real} (hfi : Integrable f μ) (f_nn : 0 <=ᵐ[μ] f) : ENNR
eal.ofReal (∫ x, f x ∂μ) = ∫⁻ x, ENNRea…
· 使用定理 `MeasureTheory.Integrable.restrict`：∀ {α : Type u_1} {m : MeasurableSpace
 α} {μ : MeasureTheory.Measure α} {ε : Type u_8} [inst : TopologicalSpace ε]   [
inst_1 : ContinuousENor…
· 使用定理 `ProbabilityTheory.IsCondKernelCDF.integrable`：∀ {α : Type u_1} {β : Type
 u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α × β → StieltjesFu
nction ℝ}   {κ : ProbabilityTheory…
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.IsCondKernelCDF.nonneg`：∀ {α : Type u_1} {β : Type u_2
} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {κ : ProbabilityTheory.Ker
nel α (β × ℝ)} {ν : Probabilit…
· 使用定理 `ProbabilityTheory.IsCondKernelCDF.setIntegral`：∀ {α : Type u_1} {β : Typ
e u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α × β → StieltjesF
unction ℝ}   {κ : ProbabilityTheory…
· 使用定理 `MeasureTheory.ofReal_measureReal`：ofReal_measureReal (h : μ s != ∞
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `ProbabilityTheory.IsFiniteKernel.isFiniteMeasure`：∀ {α : Type u_1} {β : 
Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheo
ry.Kernel α β}   [ProbabilityTheory.Is…
-/
lemma IsCondKernelCDF.setLIntegral [IsFiniteKernel κ]
    {f : α × β → StieltjesFunction ℝ} (hf : IsCondKernelCDF f κ ν)
    (a : α) {s : Set β} (hs : MeasurableSet s) (x : ℝ) :
    ∫⁻ b in s, ENNReal.ofReal (f (a, b) x) ∂(ν a) = κ a (s ×ˢ Iic x) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (hf.integrable a x).restrict
    (ae_of_all _ (fun _ ↦ hf.nonneg _ _)), hf.setIntegral a hs x, ofReal_measureReal]
/-
**ProbabilityTheory.IsCondKernelCDF.lintegral** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory.IsCondKernelCDF`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β}   {κ : ProbabilityTheory.Kernel α (β × ℝ)} {ν : ProbabilityTheory.Kernel
 α β} [ProbabilityTheory.IsFiniteKernel κ]   {f : α × β → StieltjesFunction ℝ}, 
  ProbabilityTheory.IsCondKernelCDF f κ ν →     ∀ (a : α) (x : ℝ), ∫⁻ (b : β), E
NNReal.ofReal (↑(f (a, b)) x) ∂ν a = (κ a) (Set.univ ×ˢ Set.Iic x)
参数：β × ℝ；a : α；x : ℝ；b : β；↑(f (a, b)) x；κ a；Set.univ ×ˢ Set.Iic x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.IsCondKernelCDF.setLIntegral`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {κ : ProbabilityTheo
ry.Kernel α (β × ℝ)} {ν : Probabilit…
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
-/
lemma IsCondKernelCDF.lintegral [IsFiniteKernel κ]
    {f : α × β → StieltjesFunction ℝ} (hf : IsCondKernelCDF f κ ν) (a : α) (x : ℝ) :
    ∫⁻ b, ENNReal.ofReal (f (a, b) x) ∂(ν a) = κ a (univ ×ˢ Iic x) := by
  rw [← hf.setLIntegral _ MeasurableSet.univ, Measure.restrict_univ]
/-
**ProbabilityTheory.isCondKernelCDF_stieltjesOfMeasurableRat** 是 Mathlib 中的一个引理，
位于命名空间 `ProbabilityTheory`。
形式化陈述：isCondKernelCDF_stieltjesOfMeasurableRat {f : α × β -> Rat -> Real} (hf : 
IsRatCondKernelCDF f κ ν) [IsFiniteKernel κ] : IsCondKernelCDF (stieltjesOfMeasu
rableRat f hf.measurable) κ ν where measurable
参数：hf : IsRatCondKernelCDF f κ ν。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDF.measurable`：∀ {α : Type u_1} {β : T
ype u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α × β → ℚ → ℝ}  
 {κ : ProbabilityTheory.Kernel α (β ×…
· 使用引理 `ProbabilityTheory.measurable_stieltjesOfMeasurableRat`：measurable_stielt
jesOfMeasurableRat (hf : Measurable f) (x : Real) : Measurable fun a => stieltje
sOfMeasurableRat f hf a x
· 使用引理 `ProbabilityTheory.integrable_stieltjesOfMeasurableRat`：integrable_stielt
jesOfMeasurableRat [IsFiniteKernel κ] (hf : IsRatCondKernelCDF f κ ν) (a : α) (x
 : Real) : Integrable (fun b => stieltjesOf…
· 使用引理 `ProbabilityTheory.tendsto_stieltjesOfMeasurableRat_atTop`：tendsto_stielt
jesOfMeasurableRat_atTop (hf : Measurable f) (a : α) : Tendsto (stieltjesOfMeasu
rableRat f hf a) atTop (𝓝 1)
· 使用引理 `ProbabilityTheory.tendsto_stieltjesOfMeasurableRat_atBot`：tendsto_stielt
jesOfMeasurableRat_atBot (hf : Measurable f) (a : α) : Tendsto (stieltjesOfMeasu
rableRat f hf a) atBot (𝓝 0)
· 使用引理 `ProbabilityTheory.setIntegral_stieltjesOfMeasurableRat`：setIntegral_stie
ltjesOfMeasurableRat [IsFiniteKernel κ] (hf : IsRatCondKernelCDF f κ ν) (a : α) 
(x : Real) {s : Set β} (hs : MeasurableSet s…
-/
lemma isCondKernelCDF_stieltjesOfMeasurableRat {f : α × β → ℚ → ℝ} (hf : IsRatCondKernelCDF f κ ν)
    [IsFiniteKernel κ] :
    IsCondKernelCDF (stieltjesOfMeasurableRat f hf.measurable) κ ν where
  measurable := measurable_stieltjesOfMeasurableRat hf.measurable
  integrable := integrable_stieltjesOfMeasurableRat hf
  tendsto_atTop_one := tendsto_stieltjesOfMeasurableRat_atTop hf.measurable
  tendsto_atBot_zero := tendsto_stieltjesOfMeasurableRat_atBot hf.measurable
  setIntegral a _ hs x := setIntegral_stieltjesOfMeasurableRat hf a x hs

end IsCondKernelCDF

section ToKernel

variable {_ : MeasurableSpace β} {f : α × β → StieltjesFunction ℝ}
  {κ : Kernel α (β × ℝ)} {ν : Kernel α β}

/-- A function `f : α × β → StieltjesFunction ℝ` with the property `IsCondKernelCDF f κ ν` gives a
Markov kernel from `α × β` to `ℝ`, by taking for each `p : α × β` the measure defined by `f p`. -/
noncomputable
/-
**ProbabilityTheory.IsCondKernelCDF.toKernel** 是 Mathlib 中的一个定义，位于命名空间 `Probabil
ityTheory.IsCondKernelCDF`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     {mα : MeasurableSpace α} →       {
x : MeasurableSpace β} →         {κ : ProbabilityTheory.Kernel α (β × ℝ)} →     
      {ν : ProbabilityTheory.Kernel α β} →             (f : α × β → StieltjesFun
ction ℝ) →               ProbabilityTheory.IsCondKernelCDF f κ ν → ProbabilityTh
eory.Kernel (α × β) ℝ
参数：β × ℝ；f : α × β → StieltjesFunction ℝ；α × β。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
-/
def IsCondKernelCDF.toKernel (f : α × β → StieltjesFunction ℝ) (hf : IsCondKernelCDF f κ ν) :
    Kernel (α × β) ℝ where
  toFun p := (f p).measure
  measurable' := StieltjesFunction.measurable_measure hf.measurable
    hf.tendsto_atBot_zero hf.tendsto_atTop_one
/-
**ProbabilityTheory.IsCondKernelCDF.toKernel_apply** 是 Mathlib 中的一个定理，位于命名空间 `Pr
obabilityTheory.IsCondKernelCDF`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {x : MeasurableSp
ace β} {f : α × β → StieltjesFunction ℝ}   {κ : ProbabilityTheory.Kernel α (β × 
ℝ)} {ν : ProbabilityTheory.Kernel α β}   {hf : ProbabilityTheory.IsCondKernelCDF
 f κ ν} (p : α × β),   (ProbabilityTheory.IsCondKernelCDF.toKernel f hf) p = (f 
p).measure
参数：β × ℝ；p : α × β；ProbabilityTheory.IsCondKernelCDF.toKernel f hf；f p。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsCondKernelCDF.toKernel_apply {hf : IsCondKernelCDF f κ ν} (p : α × β) :
    hf.toKernel f p = (f p).measure := rfl
/-
**ProbabilityTheory.instIsMarkovKernel_toKernel** 是 Mathlib 中的一个实例，位于命名空间 `Proba
bilityTheory`。
形式化陈述：instIsMarkovKernel_toKernel {hf : IsCondKernelCDF f κ ν} : IsMarkovKernel 
(hf.toKernel f)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `StieltjesFunction.isProbabilityMeasure`：isProbabilityMeasure [Nonempty R
] (hf_bot : Tendsto f atBot (𝓝 0)) (hf_top : Tendsto f atTop (𝓝 1)) : IsProbabil
ityMeasure f.measure
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `ProbabilityTheory.IsCondKernelCDF.tendsto_atBot_zero`：∀ {α : Type u_1} {
β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α × β → Sti
eltjesFunction ℝ}   {κ : ProbabilityTheory…
· 使用定理 `ProbabilityTheory.IsCondKernelCDF.tendsto_atTop_one`：∀ {α : Type u_1} {β
 : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α × β → Stie
ltjesFunction ℝ}   {κ : ProbabilityTheory…
-/
instance instIsMarkovKernel_toKernel {hf : IsCondKernelCDF f κ ν} :
    IsMarkovKernel (hf.toKernel f) :=
  ⟨fun _ ↦ (f _).isProbabilityMeasure (hf.tendsto_atBot_zero _) (hf.tendsto_atTop_one _)⟩
/-
**ProbabilityTheory.IsCondKernelCDF.toKernel_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Prob
abilityTheory.IsCondKernelCDF`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {x : MeasurableSp
ace β} {f : α × β → StieltjesFunction ℝ}   {κ : ProbabilityTheory.Kernel α (β × 
ℝ)} {ν : ProbabilityTheory.Kernel α β}   {hf : ProbabilityTheory.IsCondKernelCDF
 f κ ν} (p : α × β) (x_1 : ℝ),   ((ProbabilityTheory.IsCondKernelCDF.toKernel f 
hf) p) (Set.Iic x_1) = ENNReal.ofReal (↑(f p) x_1)
参数：β × ℝ；p : α × β；x_1 : ℝ；(ProbabilityTheory.IsCondKernelCDF.toKernel f hf) p；S
et.Iic x_1；↑(f p) x_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.IsCondKernelCDF.toKernel_apply`：∀ {α : Type u_1} {β : 
Type u_2} {mα : MeasurableSpace α} {x : MeasurableSpace β} {f : α × β → Stieltje
sFunction ℝ}   {κ : ProbabilityTheory.…
· 使用定理 `StieltjesFunction.measure_Iic`：measure_Iic {l : Real} (hf : Tendsto f at
Bot (𝓝 l)) (x : R) : f.measure (Iic x) = ofReal (f x - l)
· 使用定理 `ProbabilityTheory.IsCondKernelCDF.tendsto_atBot_zero`：∀ {α : Type u_1} {
β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α × β → Sti
eltjesFunction ℝ}   {κ : ProbabilityTheory…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsCondKernelCDF.toKernel_Iic {hf : IsCondKernelCDF f κ ν} (p : α × β) (x : ℝ) :
    hf.toKernel f p (Iic x) = ENNReal.ofReal (f p x) := by
  rw [IsCondKernelCDF.toKernel_apply p, (f p).measure_Iic (hf.tendsto_atBot_zero p)]
  simp

end ToKernel

section

variable {f : α × β → StieltjesFunction ℝ}

/-
**ProbabilityTheory.setLIntegral_toKernel_Iic** 是 Mathlib 中的一个引理，位于命名空间 `Probabi
lityTheory`。
形式化陈述：setLIntegral_toKernel_Iic [IsFiniteKernel κ] (hf : IsCondKernelCDF f κ ν) 
(a : α) (x : Real) {s : Set β} (hs : MeasurableSet s) : ∫⁻ b in s, hf.toKernel f
 (a, b) (Iic x) ∂(ν a) = κ a (s ×ˢ Iic x)
参数：hf : IsCondKernelCDF f κ ν；a : α；x : Real；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ProbabilityTheory.IsCondKernelCDF.toKernel_Iic`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {x : MeasurableSpace β} {f : α × β → StieltjesF
unction ℝ}   {κ : ProbabilityTheory.…
· 使用定理 `ProbabilityTheory.IsCondKernelCDF.setLIntegral`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {κ : ProbabilityTheo
ry.Kernel α (β × ℝ)} {ν : Probabilit…
-/
lemma setLIntegral_toKernel_Iic [IsFiniteKernel κ] (hf : IsCondKernelCDF f κ ν)
    (a : α) (x : ℝ) {s : Set β} (hs : MeasurableSet s) :
    ∫⁻ b in s, hf.toKernel f (a, b) (Iic x) ∂(ν a) = κ a (s ×ˢ Iic x) := by
  simp_rw [IsCondKernelCDF.toKernel_Iic]
  exact hf.setLIntegral _ hs _
/-
**ProbabilityTheory.setLIntegral_toKernel_univ** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：setLIntegral_toKernel_univ [IsFiniteKernel κ] (hf : IsCondKernelCDF f κ ν)
 (a : α) {s : Set β} (hs : MeasurableSet s) : ∫⁻ b in s, hf.toKernel f (a, b) un
iv ∂(ν a) = κ a (s ×ˢ univ)
参数：hf : IsCondKernelCDF f κ ν；a : α；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.iUnion_Iic_rat`：iUnion_Iic_rat : ⋃ r : Rat, Iic (r : Real) = univ
· 使用定理 `Set.prod_iUnion`：prod_iUnion {s : Set α} {t : ι -> Set β} : (s ×ˢ ⋃ i, t
 i) = ⋃ i, s ×ˢ t i
· 使用定理 `Monotone.directed_le`：Monotone.directed_le [Preorder α] [IsDirectedOrder
 α] [Preorder β] {f : α -> β} : Monotone f -> Directed (· <= ·) f
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanRat`：Archimedean ℚ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Iic_subset_Iic`：Iic_subset_Iic : Iic a subseteq Iic b ↔ a <= b
· 使用定理 `Set.prod_subset_prod_iff`：prod_subset_prod_iff : s ×ˢ t subseteq s₁ ×ˢ t
₁ ↔ s subseteq s₁ ∧ t subseteq t₁ ∨ s = ∅ ∨ t = ∅
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Directed.measure_iUnion`：∀ {α : Type u_1} {ι : Type u_5} {m : Measurable
Space α} {μ : MeasureTheory.Measure α} [Countable ι] {s : ι → Set α},   Directed
 (fun x1 x2 =…
· 使用定理 `Encodable.countable`：∀ {α : Type u_1} [Encodable α], Countable α
· 使用定理 `MeasureTheory.lintegral_iSup_directed`：lintegral_iSup_directed [Countabl
e β] {f : β -> α -> Real>=0∞} (hf : forall b, AEMeasurable (f b) μ) (h_directed 
: Directed (· <= ·) f) : ∫⁻…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `ProbabilityTheory.Kernel.measurable_coe`：∀ {α : Type u_1} {β : Type u_2}
 {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ : ProbabilityTheory.Kernel
 α β)   {s : Set β}, Measurab…
· 使用定理 `measurableSet_Iic`：measurableSet_Iic [ClosedIicTopology α] : MeasurableS
et (Iic a)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `measurable_prodMk_left`：measurable_prodMk_left {x : α} : Measurable (@Pr
od.mk _ β x)
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
（共 32 条，此处仅展示前 30 条）
-/
lemma setLIntegral_toKernel_univ [IsFiniteKernel κ] (hf : IsCondKernelCDF f κ ν)
    (a : α) {s : Set β} (hs : MeasurableSet s) :
    ∫⁻ b in s, hf.toKernel f (a, b) univ ∂(ν a) = κ a (s ×ˢ univ) := by
  rw [← Real.iUnion_Iic_rat, prod_iUnion]
  have h_dir : Directed (fun x y ↦ x ⊆ y) fun q : ℚ ↦ Iic (q : ℝ) := by
    refine Monotone.directed_le fun r r' hrr' ↦ Iic_subset_Iic.mpr ?_
    exact mod_cast hrr'
  have h_dir_prod : Directed (fun x y ↦ x ⊆ y) fun q : ℚ ↦ s ×ˢ Iic (q : ℝ) := by
    refine Monotone.directed_le fun i j hij ↦ ?_
    refine prod_subset_prod_iff.mpr (Or.inl ⟨subset_rfl, Iic_subset_Iic.mpr ?_⟩)
    exact mod_cast hij
  simp_rw [h_dir.measure_iUnion, h_dir_prod.measure_iUnion]
  rw [lintegral_iSup_directed]
  · simp_rw [setLIntegral_toKernel_Iic hf _ _ hs]
  · refine fun q ↦ Measurable.aemeasurable ?_
    exact (Kernel.measurable_coe _ measurableSet_Iic).comp measurable_prodMk_left
  · refine Monotone.directed_le fun i j hij t ↦ measure_mono (Iic_subset_Iic.mpr ?_)
    exact mod_cast hij
/-
**ProbabilityTheory.lintegral_toKernel_univ** 是 Mathlib 中的一个引理，位于命名空间 `Probabili
tyTheory`。
形式化陈述：lintegral_toKernel_univ [IsFiniteKernel κ] (hf : IsCondKernelCDF f κ ν) (a
 : α) : ∫⁻ b, hf.toKernel f (a, b) univ ∂(ν a) = κ a univ
参数：hf : IsCondKernelCDF f κ ν；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setLIntegral_univ`：setLIntegral_univ (f : α -> Real>=0∞) :
 ∫⁻ x in univ, f x ∂μ = ∫⁻ x, f x ∂μ
· 使用引理 `ProbabilityTheory.setLIntegral_toKernel_univ`：setLIntegral_toKernel_univ
 [IsFiniteKernel κ] (hf : IsCondKernelCDF f κ ν) (a : α) {s : Set β} (hs : Measu
rableSet s) : ∫⁻ b in s, hf.toKern…
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `Set.univ_prod_univ`：univ_prod_univ : @univ α ×ˢ @univ β = univ
-/
lemma lintegral_toKernel_univ [IsFiniteKernel κ] (hf : IsCondKernelCDF f κ ν) (a : α) :
    ∫⁻ b, hf.toKernel f (a, b) univ ∂(ν a) = κ a univ := by
  rw [← setLIntegral_univ, setLIntegral_toKernel_univ hf a MeasurableSet.univ, univ_prod_univ]
/-
**ProbabilityTheory.setLIntegral_toKernel_prod** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：setLIntegral_toKernel_prod [IsFiniteKernel κ] (hf : IsCondKernelCDF f κ ν)
 (a : α) {s : Set β} (hs : MeasurableSet s) {t : Set Real} (ht : MeasurableSet t
) : ∫⁻ b in s, hf.toKernel f (a, b) t ∂(ν a) = κ a (s ×ˢ t)
参数：hf : IsCondKernelCDF f κ ν；a : α；hs : MeasurableSet s；ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSpace.induction_on_inter`：induction_on_inter {m : MeasurableSp
ace α} {C : forall s : Set α, MeasurableSet s -> Prop} {s : Set (Set α)} (h_eq :
 m = generateFrom s) (h_…
· 使用定理 `borel_eq_generateFrom_Iic`：borel_eq_generateFrom_Iic : borel α = Measura
bleSpace.generateFrom (range Iic)
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `isPiSystem_Iic`：isPiSystem_Iic : IsPiSystem (range Iic : Set (Set α))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Set.prod_empty`：prod_empty : s ×ˢ (∅ : Set β) = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ProbabilityTheory.setLIntegral_toKernel_Iic`：setLIntegral_toKernel_Iic [
IsFiniteKernel κ] (hf : IsCondKernelCDF f κ ν) (a : α) (x : Real) {s : Set β} (h
s : MeasurableSet s) : ∫⁻ b in s,…
· 使用定理 `MeasureTheory.measure_compl`：measure_compl (h₁ : MeasurableSet s) (h_fin
 : μ s != ∞) : μ sᶜ = μ univ - μ s
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `ProbabilityTheory.IsFiniteKernel.isFiniteMeasure`：∀ {α : Type u_1} {β : 
Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheo
ry.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `MeasureTheory.lintegral_sub`：lintegral_sub {f g : α -> Real>=0∞} (hg : M
easurable g) (hg_fin : ∫⁻ a, g a ∂μ != ∞) (h_le : g <=ᵐ[μ] f) : ∫⁻ a, f a - g a 
∂μ = ∫⁻ a, f a ∂μ…
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `ProbabilityTheory.Kernel.measurable_coe`：∀ {α : Type u_1} {β : Type u_2}
 {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ : ProbabilityTheory.Kernel
 α β)   {s : Set β}, Measurab…
· 使用定理 `measurable_prodMk_left`：measurable_prodMk_left {x : α} : Measurable (@Pr
od.mk _ β x)
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用引理 `ProbabilityTheory.setLIntegral_toKernel_univ`：setLIntegral_toKernel_univ
 [IsFiniteKernel κ] (hf : IsCondKernelCDF f κ ν) (a : α) {s : Set β} (hs : Measu
rableSet s) : ∫⁻ b in s, hf.toKern…
（共 50 条，此处仅展示前 30 条）
-/
lemma setLIntegral_toKernel_prod [IsFiniteKernel κ] (hf : IsCondKernelCDF f κ ν)
    (a : α) {s : Set β} (hs : MeasurableSet s) {t : Set ℝ} (ht : MeasurableSet t) :
    ∫⁻ b in s, hf.toKernel f (a, b) t ∂(ν a) = κ a (s ×ˢ t) := by
  -- `setLIntegral_toKernel_Iic` gives the result for `t = Iic x`. These sets form a
  -- π-system that generates the Borel σ-algebra, hence we can get the same equality for any
  -- measurable set `t`.
  induction t, ht
    using MeasurableSpace.induction_on_inter (borel_eq_generateFrom_Iic ℝ) isPiSystem_Iic with
  | empty => simp only [measure_empty, lintegral_const, zero_mul, prod_empty]
  | basic t ht =>
    obtain ⟨q, rfl⟩ := ht
    exact setLIntegral_toKernel_Iic hf a _ hs
  | compl t ht iht =>
    calc ∫⁻ b in s, hf.toKernel f (a, b) tᶜ ∂(ν a)
      = ∫⁻ b in s, hf.toKernel f (a, b) univ - hf.toKernel f (a, b) t ∂(ν a) := by
          congr with x; rw [measure_compl ht (measure_ne_top (hf.toKernel f (a, x)) _)]
    _ = ∫⁻ b in s, hf.toKernel f (a, b) univ ∂(ν a)
          - ∫⁻ b in s, hf.toKernel f (a, b) t ∂(ν a) := by
        rw [lintegral_sub]
        · exact (Kernel.measurable_coe (hf.toKernel f) ht).comp measurable_prodMk_left
        · rw [iht]
          exact measure_ne_top _ _
        · exact Eventually.of_forall fun a ↦ measure_mono (subset_univ _)
    _ = κ a (s ×ˢ univ) - κ a (s ×ˢ t) := by
        rw [setLIntegral_toKernel_univ hf a hs, iht]
    _ = κ a (s ×ˢ tᶜ) := by
        rw [← measure_sdiff _ (hs.prod ht).nullMeasurableSet (measure_ne_top _ _)]
        · rw [prod_sdiff_prod, compl_eq_univ_sdiff]
          simp only [sdiff_self, empty_prod, union_empty]
        · rw [prod_subset_prod_iff]
          exact Or.inl ⟨subset_rfl, subset_univ t⟩
  | iUnion f hf_disj hf_meas ihf =>
    simp_rw [measure_iUnion hf_disj hf_meas]
    rw [lintegral_tsum, prod_iUnion, measure_iUnion]
    · simp_rw [ihf]
    · exact hf_disj.mono fun i j h ↦ h.set_prod_right _ _
    · exact fun i ↦ MeasurableSet.prod hs (hf_meas i)
    · exact fun i ↦
        ((Kernel.measurable_coe _ (hf_meas i)).comp measurable_prodMk_left).aemeasurable.restrict

open scoped Function in -- required for scoped `on` notation
/-
**ProbabilityTheory.lintegral_toKernel_mem** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory`。
形式化陈述：lintegral_toKernel_mem [IsFiniteKernel κ] (hf : IsCondKernelCDF f κ ν) (a 
: α) {s : Set (β × Real)} (hs : MeasurableSet s) : ∫⁻ b, hf.toKernel f (a, b) (P
rod.mk b ⁻¹' s) ∂(ν a) = κ a s
参数：hf : IsCondKernelCDF f κ ν；a : α；β × Real；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSpace.induction_on_inter`：induction_on_inter {m : MeasurableSp
ace α} {C : forall s : Set α, MeasurableSet s -> Prop} {s : Set (Set α)} (h_eq :
 m = generateFrom s) (h_…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `generateFrom_prod`：generateFrom_prod : generateFrom (image2 (· ×ˢ ·) { s
 : Set α | MeasurableSet s } { t : Set β | MeasurableSet t }) = Prod.instMeasura
bleSpac…
· 使用引理 `isPiSystem_prod`：isPiSystem_prod : IsPiSystem (image2 (· ×ˢ ·) { s : Set
 α | MeasurableSet s } { t : Set β | MeasurableSet t })
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.lintegral_add_compl`：lintegral_add_compl (f : α -> Real>=0
∞) {A : Set α} (hA : MeasurableSet A) : ∫⁻ x in A, f x ∂μ + ∫⁻ x in Aᶜ, f x ∂μ =
 ∫⁻ x, f x ∂μ
· 使用定理 `MeasureTheory.setLIntegral_congr_fun`：setLIntegral_congr_fun {f g : α ->
 Real>=0∞} {s : Set α} (hs : MeasurableSet s) (hfg : EqOn f g s) : ∫⁻ x in s, f 
x ∂μ = ∫⁻ x in s, g x ∂μ
· 使用定理 `Set.mk_preimage_prod_right`：mk_preimage_prod_right (ha : a in s) : Prod.
mk a ⁻¹' s ×ˢ t = t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.mk_preimage_prod_right_eq_empty`：mk_preimage_prod_right_eq_empty (ha
 : a ∉ s) : Prod.mk a ⁻¹' s ×ˢ t = ∅
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Set.mem_compl_iff`：mem_compl_iff (s : Set α) (x : α) : x in sᶜ ↔ x ∉ s
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `ProbabilityTheory.setLIntegral_toKernel_prod`：setLIntegral_toKernel_prod
 [IsFiniteKernel κ] (hf : IsCondKernelCDF f κ ν) (a : α) {s : Set β} (hs : Measu
rableSet s) {t : Set Real} (ht : M…
· 使用定理 `MeasureTheory.measure_compl`：measure_compl (h₁ : MeasurableSet s) (h_fin
 : μ s != ∞) : μ sᶜ = μ univ - μ s
· 使用定理 `measurable_prodMk_left`：measurable_prodMk_left {x : α} : Measurable (@Pr
od.mk _ β x)
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `ProbabilityTheory.IsFiniteKernel.isFiniteMeasure`：∀ {α : Type u_1} {β : 
Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheo
ry.Kernel α β}   [ProbabilityTheory.Is…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
（共 50 条，此处仅展示前 30 条）
-/
lemma lintegral_toKernel_mem [IsFiniteKernel κ] (hf : IsCondKernelCDF f κ ν)
    (a : α) {s : Set (β × ℝ)} (hs : MeasurableSet s) :
    ∫⁻ b, hf.toKernel f (a, b) (Prod.mk b ⁻¹' s) ∂(ν a) = κ a s := by
  -- `setLIntegral_toKernel_prod` gives the result for sets of the form `t₁ × t₂`. These
  -- sets form a π-system that generates the product σ-algebra, hence we can get the same equality
  -- for any measurable set `s`.
  induction s, hs
    using MeasurableSpace.induction_on_inter generateFrom_prod.symm isPiSystem_prod with
  | empty =>
    simp only [preimage_empty, measure_empty, lintegral_const, zero_mul]
  | basic s hs =>
    rcases hs with ⟨t₁, ht₁, t₂, ht₂, rfl⟩
    simp only [mem_ofPred_eq] at ht₁ ht₂
    rw [← lintegral_add_compl _ ht₁]
    have h_eq1 : ∫⁻ x in t₁, hf.toKernel f (a, x) (Prod.mk x ⁻¹' t₁ ×ˢ t₂) ∂(ν a)
        = ∫⁻ x in t₁, hf.toKernel f (a, x) t₂ ∂(ν a) := by
      refine setLIntegral_congr_fun ht₁ (fun a ha ↦ ?_)
      rw [mk_preimage_prod_right ha]
    have h_eq2 :
        ∫⁻ x in t₁ᶜ, hf.toKernel f (a, x) (Prod.mk x ⁻¹' t₁ ×ˢ t₂) ∂(ν a) = 0 := by
      suffices h_eq_zero :
          ∀ x ∈ t₁ᶜ, hf.toKernel f (a, x) (Prod.mk x ⁻¹' t₁ ×ˢ t₂) = 0 by
        rw [setLIntegral_congr_fun ht₁.compl h_eq_zero]
        simp only [lintegral_const, zero_mul]
      intro a hat₁
      rw [mem_compl_iff] at hat₁
      simp only [hat₁, not_false_eq_true, mk_preimage_prod_right_eq_empty, measure_empty]
    rw [h_eq1, h_eq2, add_zero]
    exact setLIntegral_toKernel_prod hf a ht₁ ht₂
  | compl t ht ht_eq =>
    calc ∫⁻ b, hf.toKernel f (a, b) (Prod.mk b ⁻¹' tᶜ) ∂(ν a)
      = ∫⁻ b, hf.toKernel f (a, b) (Prod.mk b ⁻¹' t)ᶜ ∂(ν a) := rfl
    _ = ∫⁻ b, hf.toKernel f (a, b) univ
          - hf.toKernel f (a, b) (Prod.mk b ⁻¹' t) ∂(ν a) := by
        congr with x : 1
        exact measure_compl (measurable_prodMk_left ht)
          (measure_ne_top (hf.toKernel f (a, x)) _)
    _ = ∫⁻ x, hf.toKernel f (a, x) univ ∂(ν a) -
          ∫⁻ x, hf.toKernel f (a, x) (Prod.mk x ⁻¹' t) ∂(ν a) := by
        have h_le : (fun x ↦ hf.toKernel f (a, x) (Prod.mk x ⁻¹' t))
              ≤ᵐ[ν a] fun x ↦ hf.toKernel f (a, x) univ :=
          Eventually.of_forall fun _ ↦ measure_mono (subset_univ _)
        rw [lintegral_sub _ _ h_le]
        · exact Kernel.measurable_kernel_prodMk_left' ht a
        refine ((lintegral_mono_ae h_le).trans_lt ?_).ne
        rw [lintegral_toKernel_univ hf]
        exact measure_lt_top _ univ
    _ = κ a univ - κ a t := by rw [ht_eq, lintegral_toKernel_univ hf]
    _ = κ a tᶜ := (measure_compl ht (measure_ne_top _ _)).symm
  | iUnion f' hf_disj hf_meas hf_eq =>
    have h_eq : ∀ a, Prod.mk a ⁻¹' ⋃ i, f' i = ⋃ i, Prod.mk a ⁻¹' f' i := by
      simp only [preimage_iUnion, implies_true]
    simp_rw [h_eq]
    have h_disj : ∀ a, Pairwise (Disjoint on fun i ↦ Prod.mk a ⁻¹' f' i) := by
      intro _ _ _ hij
      exact Disjoint.preimage _ (hf_disj hij)
    calc ∫⁻ b, hf.toKernel f (a, b) (⋃ i, Prod.mk b ⁻¹' f' i) ∂(ν a)
      = ∫⁻ b, ∑' i, hf.toKernel f (a, b) (Prod.mk b ⁻¹' f' i) ∂(ν a) := by
          congr with x : 1
          rw [measure_iUnion (h_disj x) fun i ↦ measurable_prodMk_left (hf_meas i)]
    _ = ∑' i, ∫⁻ b, hf.toKernel f (a, b) (Prod.mk b ⁻¹' f' i) ∂(ν a) :=
          lintegral_tsum fun i ↦ (Kernel.measurable_kernel_prodMk_left' (hf_meas i) a).aemeasurable
    _ = ∑' i, κ a (f' i) := by simp_rw [hf_eq]
    _ = κ a (iUnion f') := (measure_iUnion hf_disj hf_meas).symm
/-
**ProbabilityTheory.compProd_toKernel** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheo
ry`。
形式化陈述：compProd_toKernel [IsFiniteKernel κ] [IsSFiniteKernel ν] (hf : IsCondKerne
lCDF f κ ν) : ν otimesₖ hf.toKernel f = κ
参数：hf : IsCondKernelCDF f κ ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.Kernel.compProd_apply`：compProd_apply (hs : Measurable
Set s) (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKer
nel η] (a : α) : (κ otimesₖ η…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用引理 `ProbabilityTheory.lintegral_toKernel_mem`：lintegral_toKernel_mem [IsFini
teKernel κ] (hf : IsCondKernelCDF f κ ν) (a : α) {s : Set (β × Real)} (hs : Meas
urableSet s) : ∫⁻ b, hf.toKern…
-/
lemma compProd_toKernel [IsFiniteKernel κ] [IsSFiniteKernel ν] (hf : IsCondKernelCDF f κ ν) :
    ν ⊗ₖ hf.toKernel f = κ := by
  ext a s hs
  rw [Kernel.compProd_apply hs, lintegral_toKernel_mem hf a hs]

end

end ProbabilityTheory

