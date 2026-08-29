/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Probability.Kernel.MeasurableLIntegral

/-!
# With Density

For an s-finite kernel `κ : Kernel α β` and a function `f : α → β → ℝ≥0∞` which is finite
everywhere, we define `withDensity κ f` as the kernel `a ↦ (κ a).withDensity (f a)`. This is
an s-finite kernel.

## Main definitions

* `ProbabilityTheory.Kernel.withDensity κ (f : α → β → ℝ≥0∞)`:
  kernel `a ↦ (κ a).withDensity (f a)`. It is defined if `κ` is s-finite. If `f` is finite
  everywhere, then this is also an s-finite kernel. The class of s-finite kernels is the smallest
  class of kernels that contains finite kernels and which is stable by `withDensity`.
  Integral: `∫⁻ b, g b ∂(withDensity κ f a) = ∫⁻ b, f a b * g b ∂(κ a)`

## Main statements

* `ProbabilityTheory.Kernel.lintegral_withDensity`:
  `∫⁻ b, g b ∂(withDensity κ f a) = ∫⁻ b, f a b * g b ∂(κ a)`

-/

@[expose] public section


open MeasureTheory ProbabilityTheory

open scoped MeasureTheory ENNReal NNReal

namespace ProbabilityTheory.Kernel

variable {α β ι : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
variable {κ : Kernel α β} {f : α -> β -> Real>=0∞}

/--
Definition of `withDensity` / `withDensity` 的定义

English:
definition withDensity
  signature: (κ : Kernel α β) [IsSFiniteKernel κ] (f : α -> β -> Real>=0∞)
  body: @dite _ (Measurable (Function.uncurry f)) (Classical.dec _) (fun hf =>
    (⟨fun a => (κ a).withDensity (f a),
      by
        refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
        simp_rw [withDensity_apply _ hs]
        exact hf.setLIntegral_kernel_prod_right hs⟩ : Kernel α β)) fun _ => 0

中文:
定义 withDensity
  签名: (κ : 核 α β) [是SFiniteKernel κ] (f : α -> β -> 实数>=0∞)
  定义体: @dite _ (Measurable (Function.uncurry f)) (Classical.dec _) (fun hf =>
    (⟨fun a => (κ a).withDensity (f a),
      by
        refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
        simp_rw [withDensity_apply _ hs]
        exact hf.setLIntegral_kernel_prod_right hs⟩ : Kernel α β)) fun _ => 0

Depends on / 依赖: Classical, Classical.dec, Function, Function.uncurry, Kernel, Measurable, Measure, Measure.measurable_of_measurable_coe, hf.setLIntegral_kernel_prod_right, measurable_of_measurable_coe, setLIntegral_kernel_prod_right, simp_rw, uncurry, withDensity, withDensity_apply
-/
noncomputable def withDensity (κ : Kernel α β) [IsSFiniteKernel κ] (f : α -> β -> Real>=0∞) :
    Kernel α β :=
  @dite _ (Measurable (Function.uncurry f)) (Classical.dec _) (fun hf =>
    (⟨fun a => (κ a).withDensity (f a),
      by
        refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
        simp_rw [withDensity_apply _ hs]
        exact hf.setLIntegral_kernel_prod_right hs⟩ : Kernel α β)) fun _ => 0

/--
theorem `withDensity_of_not_measurable` / 定理 `withDensity_of_not_measurable`

English:
theorem withDensity_of_not_measurable
  statement: (κ : Kernel α β) [IsSFiniteKernel κ]
  proof: by exact dif_neg hf

中文:
定理 withDensity_of_not_measurable
  结论: (κ : 核 α β) [是SFiniteKernel κ]
  证明: by exact dif_neg hf

Depends on / 依赖: dif_neg
-/
theorem withDensity_of_not_measurable (κ : Kernel α β) [IsSFiniteKernel κ]
    (hf : ¬Measurable (Function.uncurry f)) : withDensity κ f = 0 := by exact dif_neg hf

/--
theorem `withDensity_apply` / 定理 `withDensity_apply`

English:
theorem withDensity_apply
  statement: (κ : Kernel α β) [IsSFiniteKernel κ]
  proof: by
  rw [withDensity]; rw [dif_pos hf]
  rfl

中文:
定理 withDensity_apply
  结论: (κ : 核 α β) [是SFiniteKernel κ]
  证明: by
  rw [withDensity]; rw [dif_pos hf]
  rfl
-/
protected theorem withDensity_apply (κ : Kernel α β) [IsSFiniteKernel κ]
    (hf : Measurable (Function.uncurry f)) (a : α) :
    withDensity κ f a = (κ a).withDensity (f a) := by
  rw [withDensity]; rw [dif_pos hf]
  rfl

/--
theorem `withDensity_apply'` / 定理 `withDensity_apply'`

English:
theorem withDensity_apply'
  statement: (κ : Kernel α β) [IsSFiniteKernel κ]
  proof: by
  rw [Kernel.withDensity_apply κ hf]; rw [withDensity_apply' _ s]

nonrec lemma withDensity_congr_ae (κ : Kernel α β) [IsSFiniteKernel κ] {f g : α -> β -> Real>=0∞}
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g))
    (hfg : forall a, f a =ᵐ[κ a] g a) :
    withDensity κ f = withDensity κ g := by
  ext a
  rw [Kernel.withDensity_apply _ hf]; rw [Kernel.withDensity_apply _ hg]; rw [withDensity_congr_ae (hfg a)]

nonrec lemma withDensity_absolutelyContinuous [IsSFiniteKernel κ]
    (f : α -> β -> Real>=0∞) (a : α) :
    Kernel.withDensity κ f a ≪ κ a := by
  by_cases hf : Measurable (Function.uncurry f)
  · rw [Kernel.withDensity_apply _ hf]
    exact withDensity_absolutelyContinuous _ _
  · rw [withDensity_of_not_measurable _ hf]
    simp [Measure.AbsolutelyContinuous.zero]

@[simp]

中文:
定理 withDensity_apply'
  结论: (κ : 核 α β) [是SFiniteKernel κ]
  证明: by
  rw [Kernel.withDensity_apply κ hf]; rw [withDensity_apply' _ s]

nonrec lemma withDensity_congr_ae (κ : Kernel α β) [IsSFiniteKernel κ] {f g : α -> β -> Real>=0∞}
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g))
    (hfg : forall a, f a =ᵐ[κ a] g a) :
    withDensity κ f = withDensity κ g := by
  ext a
  rw [Kernel.withDensity_apply _ hf]; rw [Kernel.withDensity_apply _ hg]; rw [withDensity_congr_ae (hfg a)]

nonrec lemma withDensity_absolutelyContinuous [IsSFiniteKernel κ]
    (f : α -> β -> Real>=0∞) (a : α) :
    Kernel.withDensity κ f a ≪ κ a := by
  by_cases hf : Measurable (Function.uncurry f)
  · rw [Kernel.withDensity_apply _ hf]
    exact withDensity_absolutelyContinuous _ _
  · rw [withDensity_of_not_measurable _ hf]
    simp [Measure.AbsolutelyContinuous.zero]

@[simp]
-/
protected theorem withDensity_apply' (κ : Kernel α β) [IsSFiniteKernel κ]
    (hf : Measurable (Function.uncurry f)) (a : α) (s : Set β) :
    withDensity κ f a s = ∫⁻ b in s, f a b ∂κ a := by
  rw [Kernel.withDensity_apply κ hf]; rw [withDensity_apply' _ s]

nonrec lemma withDensity_congr_ae (κ : Kernel α β) [IsSFiniteKernel κ] {f g : α -> β -> Real>=0∞}
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g))
    (hfg : forall a, f a =ᵐ[κ a] g a) :
    withDensity κ f = withDensity κ g := by
  ext a
  rw [Kernel.withDensity_apply _ hf]; rw [Kernel.withDensity_apply _ hg]; rw [withDensity_congr_ae (hfg a)]

nonrec lemma withDensity_absolutelyContinuous [IsSFiniteKernel κ]
    (f : α -> β -> Real>=0∞) (a : α) :
    Kernel.withDensity κ f a ≪ κ a := by
  by_cases hf : Measurable (Function.uncurry f)
  · rw [Kernel.withDensity_apply _ hf]
    exact withDensity_absolutelyContinuous _ _
  · rw [withDensity_of_not_measurable _ hf]
    simp [Measure.AbsolutelyContinuous.zero]

@[simp]
/--
lemma `withDensity_one` / 引理 `withDensity_one`

English:
lemma withDensity_one
  given: (κ : Kernel α β) [IsSFiniteKernel κ]
  proof: by
  ext; rw [Kernel.withDensity_apply _ measurable_const]; simp

@[simp]

中文:
引理 withDensity_one
  条件: (κ : 核 α β) [是SFiniteKernel κ]
  证明: by
  ext; rw [Kernel.withDensity_apply _ measurable_const]; simp

@[simp]

Depends on / 依赖: Kernel, Kernel.withDensity_apply, measurable_const, withDensity_apply
-/
lemma withDensity_one (κ : Kernel α β) [IsSFiniteKernel κ] :
    Kernel.withDensity κ 1 = κ := by
  ext; rw [Kernel.withDensity_apply _ measurable_const]; simp

@[simp]
/--
lemma `withDensity_one'` / 引理 `withDensity_one'`

English:
lemma withDensity_one'
  given: (κ : Kernel α β) [IsSFiniteKernel κ]
  proof: Kernel.withDensity_one _

@[simp]

中文:
引理 withDensity_one'
  条件: (κ : 核 α β) [是SFiniteKernel κ]
  证明: Kernel.withDensity_one _

@[simp]

Depends on / 依赖: Kernel, Kernel.withDensity_one, withDensity_one
-/
lemma withDensity_one' (κ : Kernel α β) [IsSFiniteKernel κ] :
    Kernel.withDensity κ (fun _ _ => 1) = κ := Kernel.withDensity_one _

@[simp]
/--
lemma `withDensity_zero` / 引理 `withDensity_zero`

English:
lemma withDensity_zero
  given: (κ : Kernel α β) [IsSFiniteKernel κ]
  proof: by
  ext; rw [Kernel.withDensity_apply _ measurable_const]; simp

@[simp]

中文:
引理 withDensity_zero
  条件: (κ : 核 α β) [是SFiniteKernel κ]
  证明: by
  ext; rw [Kernel.withDensity_apply _ measurable_const]; simp

@[simp]

Depends on / 依赖: Kernel, Kernel.withDensity_apply, measurable_const, withDensity_apply
-/
lemma withDensity_zero (κ : Kernel α β) [IsSFiniteKernel κ] :
    Kernel.withDensity κ 0 = 0 := by
  ext; rw [Kernel.withDensity_apply _ measurable_const]; simp

@[simp]
/--
lemma `withDensity_zero'` / 引理 `withDensity_zero'`

English:
lemma withDensity_zero'
  given: (κ : Kernel α β) [IsSFiniteKernel κ]
  proof: Kernel.withDensity_zero _

中文:
引理 withDensity_zero'
  条件: (κ : 核 α β) [是SFiniteKernel κ]
  证明: Kernel.withDensity_zero _

Depends on / 依赖: Kernel, Kernel.withDensity_zero, withDensity_zero
-/
lemma withDensity_zero' (κ : Kernel α β) [IsSFiniteKernel κ] :
    Kernel.withDensity κ (fun _ _ => 0) = 0 := Kernel.withDensity_zero _

/--
theorem `lintegral_withDensity` / 定理 `lintegral_withDensity`

English:
theorem lintegral_withDensity
  statement: (κ : Kernel α β) [IsSFiniteKernel κ]
  proof: by
  rw [Kernel.withDensity_apply _ hf]; rw [lintegral_withDensity_eq_lintegral_mul _ (Measurable.of_uncurry_left hf) hg]
  simp_rw [Pi.mul_apply]

中文:
定理 lintegral_withDensity
  结论: (κ : 核 α β) [是SFiniteKernel κ]
  证明: by
  rw [Kernel.withDensity_apply _ hf]; rw [lintegral_withDensity_eq_lintegral_mul _ (Measurable.of_uncurry_left hf) hg]
  simp_rw [Pi.mul_apply]

Depends on / 依赖: Kernel, Kernel.withDensity_apply, Measurable, Measurable.of_uncurry_left, Pi.mul_apply, lintegral_withDensity_eq_lintegral_mul, mul_apply, of_uncurry_left, simp_rw, withDensity_apply
-/
theorem lintegral_withDensity (κ : Kernel α β) [IsSFiniteKernel κ]
    (hf : Measurable (Function.uncurry f)) (a : α) {g : β -> Real>=0∞} (hg : Measurable g) :
    ∫⁻ b, g b ∂withDensity κ f a = ∫⁻ b, f a b * g b ∂κ a := by
  rw [Kernel.withDensity_apply _ hf]; rw [lintegral_withDensity_eq_lintegral_mul _ (Measurable.of_uncurry_left hf) hg]
  simp_rw [Pi.mul_apply]

/--
theorem `integral_withDensity` / 定理 `integral_withDensity`

English:
theorem integral_withDensity
  statement: {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  proof: by
  rw [Kernel.withDensity_apply]; rw [integral_withDensity_eq_integral_smul]
  · fun_prop
  · fun_prop

中文:
定理 integral_withDensity
  结论: {E : 类型} [赋范交换加群 E] [赋范空间 实数 E]
  证明: by
  rw [Kernel.withDensity_apply]; rw [integral_withDensity_eq_integral_smul]
  · fun_prop
  · fun_prop

Depends on / 依赖: Kernel, Kernel.withDensity_apply, fun_prop, integral_withDensity_eq_integral_smul, withDensity_apply
-/
theorem integral_withDensity {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {f : β -> E} [IsSFiniteKernel κ] {a : α} {g : α -> β -> Real>=0}
    (hg : Measurable (Function.uncurry g)) :
    ∫ b, f b ∂withDensity κ (fun a b => g a b) a = ∫ b, g a b • f b ∂κ a := by
  rw [Kernel.withDensity_apply]; rw [integral_withDensity_eq_integral_smul]
  · fun_prop
  · fun_prop

/--
theorem `withDensity_add_left` / 定理 `withDensity_add_left`

English:
theorem withDensity_add_left
  statement: (κ η : Kernel α β) [IsSFiniteKernel κ] [IsSFiniteKernel η]
  proof: by
  by_cases hf : Measurable (Function.uncurry f)
  · ext a s
    simp only [Kernel.withDensity_apply _ hf, add_apply, withDensity_add_measure]
  · simp_rw [withDensity_of_not_measurable _ hf]
    rw [zero_add]

中文:
定理 withDensity_add_left
  结论: (κ η : 核 α β) [是SFiniteKernel κ] [是SFiniteKernel η]
  证明: by
  by_cases hf : Measurable (Function.uncurry f)
  · ext a s
    simp only [Kernel.withDensity_apply _ hf, add_apply, withDensity_add_measure]
  · simp_rw [withDensity_of_not_measurable _ hf]
    rw [zero_add]

Depends on / 依赖: Function, Function.uncurry, Kernel, Kernel.withDensity_apply, Measurable, add_apply, simp_rw, uncurry, withDensity_add_measure, withDensity_apply, withDensity_of_not_measurable, zero_add
-/
theorem withDensity_add_left (κ η : Kernel α β) [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (f : α -> β -> Real>=0∞) : withDensity (κ + η) f = withDensity κ f + withDensity η f := by
  by_cases hf : Measurable (Function.uncurry f)
  · ext a s
    simp only [Kernel.withDensity_apply _ hf, add_apply, withDensity_add_measure]
  · simp_rw [withDensity_of_not_measurable _ hf]
    rw [zero_add]

/--
theorem `withDensity_kernel_sum` / 定理 `withDensity_kernel_sum`

English:
theorem withDensity_kernel_sum
  statement: [Countable ι] (κ : ι -> Kernel α β) (hκ : forall i, IsSFiniteKernel (κ i))
  proof: by
  by_cases hf : Measurable (Function.uncurry f)
  · ext1 a
    simp_rw [sum_apply, Kernel.withDensity_apply _ hf, sum_apply,
      withDensity_sum (fun n => κ n a) (f a)]
  · simp_rw [withDensity_of_not_measurable _ hf]
    exact sum_zero.symm

中文:
定理 withDensity_kernel_sum
  结论: [可数 ι] (κ : ι -> 核 α β) (hκ : 对任意 i, 是SFiniteKernel (κ i))
  证明: by
  by_cases hf : Measurable (Function.uncurry f)
  · ext1 a
    simp_rw [sum_apply, Kernel.withDensity_apply _ hf, sum_apply,
      withDensity_sum (fun n => κ n a) (f a)]
  · simp_rw [withDensity_of_not_measurable _ hf]
    exact sum_zero.symm

Depends on / 依赖: Function, Function.uncurry, Kernel, Kernel.withDensity_apply, Measurable, simp_rw, sum_apply, sum_zero, sum_zero.symm, uncurry, withDensity_apply, withDensity_of_not_measurable, withDensity_sum
-/
theorem withDensity_kernel_sum [Countable ι] (κ : ι -> Kernel α β) (hκ : forall i, IsSFiniteKernel (κ i))
    (f : α -> β -> Real>=0∞) :
    withDensity (Kernel.sum κ) f = Kernel.sum fun i => withDensity (κ i) f := by
  by_cases hf : Measurable (Function.uncurry f)
  · ext1 a
    simp_rw [sum_apply, Kernel.withDensity_apply _ hf, sum_apply,
      withDensity_sum (fun n => κ n a) (f a)]
  · simp_rw [withDensity_of_not_measurable _ hf]
    exact sum_zero.symm

/--
lemma `withDensity_add_right` / 引理 `withDensity_add_right`

English:
lemma withDensity_add_right
  statement: [IsSFiniteKernel κ] {f g : α -> β -> Real>=0∞}
  proof: by
  ext a
  rw [add_apply]; rw [Kernel.withDensity_apply _ hf]; rw [Kernel.withDensity_apply _ hg]; rw [Kernel.withDensity_apply]; rw [Pi.add_apply]; rw [MeasureTheory.withDensity_add_right]
  · fun_prop
  · exact hf.add hg

中文:
引理 withDensity_add_right
  结论: [是SFiniteKernel κ] {f g : α -> β -> 实数>=0∞}
  证明: by
  ext a
  rw [add_apply]; rw [Kernel.withDensity_apply _ hf]; rw [Kernel.withDensity_apply _ hg]; rw [Kernel.withDensity_apply]; rw [Pi.add_apply]; rw [MeasureTheory.withDensity_add_right]
  · fun_prop
  · exact hf.add hg

Depends on / 依赖: Kernel, Kernel.withDensity_apply, MeasureTheory, MeasureTheory.withDensity_add_right, Pi.add_apply, add_apply, fun_prop, hf.add, withDensity_add_right, withDensity_apply
-/
lemma withDensity_add_right [IsSFiniteKernel κ] {f g : α -> β -> Real>=0∞}
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g)) :
    withDensity κ (f + g) = withDensity κ f + withDensity κ g := by
  ext a
  rw [add_apply]; rw [Kernel.withDensity_apply _ hf]; rw [Kernel.withDensity_apply _ hg]; rw [Kernel.withDensity_apply]; rw [Pi.add_apply]; rw [MeasureTheory.withDensity_add_right]
  · fun_prop
  · exact hf.add hg

/--
lemma `withDensity_sub_add_cancel` / 引理 `withDensity_sub_add_cancel`

English:
lemma withDensity_sub_add_cancel
  statement: [IsSFiniteKernel κ] {f g : α -> β -> Real>=0∞}
  proof: by
  rw [← withDensity_add_right _ hg]
  swap; · exact hf.sub hg
  refine withDensity_congr_ae κ ((hf.sub hg).add hg) hf (fun a => ?_)
  filter_upwards [hfg a] with x hx
  rwa [Pi.add_apply, Pi.add_apply, tsub_add_cancel_iff_le]

中文:
引理 withDensity_sub_add_cancel
  结论: [是SFiniteKernel κ] {f g : α -> β -> 实数>=0∞}
  证明: by
  rw [← withDensity_add_right _ hg]
  swap; · exact hf.sub hg
  refine withDensity_congr_ae κ ((hf.sub hg).add hg) hf (fun a => ?_)
  filter_upwards [hfg a] with x hx
  rwa [Pi.add_apply, Pi.add_apply, tsub_add_cancel_iff_le]

Depends on / 依赖: Pi.add_apply, add_apply, filter_upwards, hf.sub, tsub_add_cancel_iff_le, withDensity_add_right, withDensity_congr_ae
-/
lemma withDensity_sub_add_cancel [IsSFiniteKernel κ] {f g : α -> β -> Real>=0∞}
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g))
    (hfg : forall a, g a <=ᵐ[κ a] f a) :
    withDensity κ (fun a x => f a x - g a x) + withDensity κ g = withDensity κ f := by
  rw [← withDensity_add_right _ hg]
  swap; · exact hf.sub hg
  refine withDensity_congr_ae κ ((hf.sub hg).add hg) hf (fun a => ?_)
  filter_upwards [hfg a] with x hx
  rwa [Pi.add_apply, Pi.add_apply, tsub_add_cancel_iff_le]

/--
theorem `withDensity_tsum` / 定理 `withDensity_tsum`

English:
theorem withDensity_tsum
  statement: [Countable ι] (κ : Kernel α β) [IsSFiniteKernel κ] {f : ι -> α -> β -> Real>=0∞}
  proof: by
  have h_sum_a : forall a, Summable fun n => f n a := fun a => Pi.summable.mpr fun b => ENNReal.summable
  have h_sum : Summable fun n => f n := Pi.summable.mpr h_sum_a
  ext a s hs
  rw [sum_apply' _ a hs]; rw [Kernel.withDensity_apply' κ _ a s]
  swap
  · have : Function.uncurry (∑' n, f n) = ∑' n, Function.uncurry (f n) := by
      ext1 p
      simp only [Function.uncurry_def]
      rw [tsum_apply h_sum]; rw [tsum_apply (h_sum_a _)]; rw [tsum_apply]
      exact Pi.summable.mpr fun p => ENNReal.summable
    rw [this]
    fun_prop
  have : ∫⁻ b in s, (∑' n, f n) a b ∂κ a = ∫⁻ b in s, ∑' n, (fun b => f n a b) b ∂κ a := by
    congr with b
    rw [tsum_apply h_sum]; rw [tsum_apply (h_sum_a a)]
  rw [this]; rw [lintegral_tsum fun n => by fun_prop]
  congr with n
  rw [Kernel.withDensity_apply' _ (hf n) a s]

中文:
定理 withDensity_tsum
  结论: [可数 ι] (κ : 核 α β) [是SFiniteKernel κ] {f : ι -> α -> β -> 实数>=0∞}
  证明: by
  have h_sum_a : forall a, Summable fun n => f n a := fun a => Pi.summable.mpr fun b => ENNReal.summable
  have h_sum : Summable fun n => f n := Pi.summable.mpr h_sum_a
  ext a s hs
  rw [sum_apply' _ a hs]; rw [Kernel.withDensity_apply' κ _ a s]
  swap
  · have : Function.uncurry (∑' n, f n) = ∑' n, Function.uncurry (f n) := by
      ext1 p
      simp only [Function.uncurry_def]
      rw [tsum_apply h_sum]; rw [tsum_apply (h_sum_a _)]; rw [tsum_apply]
      exact Pi.summable.mpr fun p => ENNReal.summable
    rw [this]
    fun_prop
  have : ∫⁻ b in s, (∑' n, f n) a b ∂κ a = ∫⁻ b in s, ∑' n, (fun b => f n a b) b ∂κ a := by
    congr with b
    rw [tsum_apply h_sum]; rw [tsum_apply (h_sum_a a)]
  rw [this]; rw [lintegral_tsum fun n => by fun_prop]
  congr with n
  rw [Kernel.withDensity_apply' _ (hf n) a s]

Depends on / 依赖: ENNReal, ENNReal.summable, Function, Function.uncurry, Function.uncurry_def, Kernel, Kernel.withDensity_apply, Pi.summable.mpr, Summable, fun_prop, h_sum, h_sum_a, sum_apply, summable, tsum_apply, uncurry, uncurry_def, withDensity_apply
-/
theorem withDensity_tsum [Countable ι] (κ : Kernel α β) [IsSFiniteKernel κ] {f : ι -> α -> β -> Real>=0∞}
    (hf : forall i, Measurable (Function.uncurry (f i))) :
    withDensity κ (∑' n, f n) = Kernel.sum fun n => withDensity κ (f n) := by
  have h_sum_a : forall a, Summable fun n => f n a := fun a => Pi.summable.mpr fun b => ENNReal.summable
  have h_sum : Summable fun n => f n := Pi.summable.mpr h_sum_a
  ext a s hs
  rw [sum_apply' _ a hs]; rw [Kernel.withDensity_apply' κ _ a s]
  swap
  · have : Function.uncurry (∑' n, f n) = ∑' n, Function.uncurry (f n) := by
      ext1 p
      simp only [Function.uncurry_def]
      rw [tsum_apply h_sum]; rw [tsum_apply (h_sum_a _)]; rw [tsum_apply]
      exact Pi.summable.mpr fun p => ENNReal.summable
    rw [this]
    fun_prop
  have : ∫⁻ b in s, (∑' n, f n) a b ∂κ a = ∫⁻ b in s, ∑' n, (fun b => f n a b) b ∂κ a := by
    congr with b
    rw [tsum_apply h_sum]; rw [tsum_apply (h_sum_a a)]
  rw [this]; rw [lintegral_tsum fun n => by fun_prop]
  congr with n
  rw [Kernel.withDensity_apply' _ (hf n) a s]

/--
theorem `isFiniteKernel_withDensity_of_bounded` / 定理 `isFiniteKernel_withDensity_of_bounded`

English:
theorem isFiniteKernel_withDensity_of_bounded
  statement: (κ : Kernel α β) [IsFiniteKernel κ] {B : Real>=0∞}
  proof: by
  by_cases hf : Measurable (Function.uncurry f)
  · exact ⟨⟨B * κ.bound, ENNReal.mul_lt_top hB_top.lt_top κ.bound_lt_top, fun a => by
        rw [Kernel.withDensity_apply' κ hf a Set.univ]
        calc
          ∫⁻ b in Set.univ, f a b ∂κ a <= ∫⁻ _ in Set.univ, B ∂κ a := lintegral_mono (hf_B a)
          _ = B * κ a Set.univ := by
            simp only [Measure.restrict_univ, MeasureTheory.lintegral_const]
          _ <= B * κ.bound := by grw [measure_le_bound]⟩⟩
  · rw [withDensity_of_not_measurable _ hf]
    infer_instance

中文:
定理 isFiniteKernel_withDensity_of_bounded
  结论: (κ : 核 α β) [是FiniteKernel κ] {B : 实数>=0∞}
  证明: by
  by_cases hf : Measurable (Function.uncurry f)
  · exact ⟨⟨B * κ.bound, ENNReal.mul_lt_top hB_top.lt_top κ.bound_lt_top, fun a => by
        rw [Kernel.withDensity_apply' κ hf a Set.univ]
        calc
          ∫⁻ b in Set.univ, f a b ∂κ a <= ∫⁻ _ in Set.univ, B ∂κ a := lintegral_mono (hf_B a)
          _ = B * κ a Set.univ := by
            simp only [Measure.restrict_univ, MeasureTheory.lintegral_const]
          _ <= B * κ.bound := by grw [measure_le_bound]⟩⟩
  · rw [withDensity_of_not_measurable _ hf]
    infer_instance

Depends on / 依赖: ENNReal, ENNReal.mul_lt_top, Function, Function.uncurry, Kernel, Kernel.withDensity_apply, Measurable, Measure, Measure.restrict_univ, MeasureTheory, MeasureTheory.lintegral_const, Set.univ, bound_lt_top, hB_top, hB_top.lt_top, hf_B, infer_instance, lintegral_const, lintegral_mono, lt_top
-/
theorem isFiniteKernel_withDensity_of_bounded (κ : Kernel α β) [IsFiniteKernel κ] {B : Real>=0∞}
    (hB_top : B != ∞) (hf_B : forall a b, f a b <= B) : IsFiniteKernel (withDensity κ f) := by
  by_cases hf : Measurable (Function.uncurry f)
  · exact ⟨⟨B * κ.bound, ENNReal.mul_lt_top hB_top.lt_top κ.bound_lt_top, fun a => by
        rw [Kernel.withDensity_apply' κ hf a Set.univ]
        calc
          ∫⁻ b in Set.univ, f a b ∂κ a <= ∫⁻ _ in Set.univ, B ∂κ a := lintegral_mono (hf_B a)
          _ = B * κ a Set.univ := by
            simp only [Measure.restrict_univ, MeasureTheory.lintegral_const]
          _ <= B * κ.bound := by grw [measure_le_bound]⟩⟩
  · rw [withDensity_of_not_measurable _ hf]
    infer_instance

/--
theorem `isSFiniteKernel_withDensity_of_isFiniteKernel` / 定理 `isSFiniteKernel_withDensity_of_isFiniteKernel`

English:
theorem isSFiniteKernel_withDensity_of_isFiniteKernel
  statement: (κ : Kernel α β) [IsFiniteKernel κ]
  proof: by
  -- We already have that for `f` bounded from above and a `κ` a finite kernel,
  -- `withDensity κ f` is finite. We write any function as a countable sum of bounded
  -- functions, and decompose an s-finite kernel as a sum of finite kernels. We then use that
  -- `withDensity` commutes with sums for both arguments and get a sum of finite kernels.
  by_cases hf : Measurable (Function.uncurry f)
  swap; · rw [withDensity_of_not_measurable _ hf]; infer_instance
  let fs : Nat -> α -> β -> Real>=0∞ := fun n a b => min (f a b) (n + 1) - min (f a b) n
  have h_le : forall a b n, ⌈(f a b).toReal⌉₊ <= n -> f a b <= n := by
    intro a b n hn
    have : (f a b).toReal <= n := Nat.le_of_ceil_le hn
    rw [← ENNReal.le_ofReal_iff_toReal_le (hf_ne_top a b) _] at this
    · simpa
    · exact n.cast_nonneg
  have h_zero : forall a b n, ⌈(f a b).toReal⌉₊ <= n -> fs n a b = 0 := by
    intro a b n hn
    suffices min (f a b) (n + 1) = f a b ∧ min (f a b) n = f a b by
      simp_rw [fs, this.1, this.2, tsub_self (f a b)]
    exact ⟨min_eq_left ((h_le a b n hn).trans (le_add_of_nonneg_right zero_le_one)),
      min_eq_left (h_le a b n hn)⟩
  have hf_eq_tsum : f = ∑' n, fs n := by
    have h_sum_a : forall a, Summable fun n => fs n a :=
      fun _ => Pi.summable.mpr fun _ => ENNReal.summable
    ext a b : 2
    rw [tsum_apply (Pi.summable.mpr h_sum_a)]; rw [tsum_apply (h_sum_a a)]; rw [ENNReal.tsum_eq_liminf_sum_nat]
    have h_finsetSum : forall n, ∑ i in Finset.range n, fs i a b = min (f a b) n := fun n => by
      induction n with
      | zero => simp
      | succ n hn =>
        rw [Finset.sum_range_succ]; rw [hn]
        simp [fs]
    simp_rw [h_finsetSum]
    refine (Filter.Tendsto.liminf_eq ?_).symm
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    rw [Filter.EventuallyEq]; rw [Filter.eventually_atTop]
    exact ⟨⌈(f a b).toReal⌉₊, fun n hn => (min_eq_left (h_le a b n hn)).symm⟩
  rw [hf_eq_tsum]; rw [withDensity_tsum _ fun n : Nat => _]
  swap; · fun_prop
  refine isSFiniteKernel_sum (hκs := fun n => ?_)
  suffices IsFiniteKernel (withDensity κ (fs n)) by infer_instance
  refine isFiniteKernel_withDensity_of_bounded _ (ENNReal.coe_ne_top : ↑n + 1 != ∞) fun a b => ?_
  -- After https://github.com/leanprover/lean4/pull/2734, we need to do beta reduction before `norm_cast`
  beta_reduce
  norm_cast
  calc
    fs n a b <= min (f a b) (n + 1) := tsub_le_self
    _ <= n + 1 := min_le_right _ _
    _ = ↑(n + 1) := by norm_cast

中文:
定理 isSFiniteKernel_withDensity_of_isFiniteKernel
  结论: (κ : 核 α β) [是FiniteKernel κ]
  证明: by
  -- We already have that for `f` bounded from above and a `κ` a finite kernel,
  -- `withDensity κ f` is finite. We write any function as a countable sum of bounded
  -- functions, and decompose an s-finite kernel as a sum of finite kernels. We then use that
  -- `withDensity` commutes with sums for both arguments and get a sum of finite kernels.
  by_cases hf : Measurable (Function.uncurry f)
  swap; · rw [withDensity_of_not_measurable _ hf]; infer_instance
  let fs : Nat -> α -> β -> Real>=0∞ := fun n a b => min (f a b) (n + 1) - min (f a b) n
  have h_le : forall a b n, ⌈(f a b).toReal⌉₊ <= n -> f a b <= n := by
    intro a b n hn
    have : (f a b).toReal <= n := Nat.le_of_ceil_le hn
    rw [← ENNReal.le_ofReal_iff_toReal_le (hf_ne_top a b) _] at this
    · simpa
    · exact n.cast_nonneg
  have h_zero : forall a b n, ⌈(f a b).toReal⌉₊ <= n -> fs n a b = 0 := by
    intro a b n hn
    suffices min (f a b) (n + 1) = f a b ∧ min (f a b) n = f a b by
      simp_rw [fs, this.1, this.2, tsub_self (f a b)]
    exact ⟨min_eq_left ((h_le a b n hn).trans (le_add_of_nonneg_right zero_le_one)),
      min_eq_left (h_le a b n hn)⟩
  have hf_eq_tsum : f = ∑' n, fs n := by
    have h_sum_a : forall a, Summable fun n => fs n a :=
      fun _ => Pi.summable.mpr fun _ => ENNReal.summable
    ext a b : 2
    rw [tsum_apply (Pi.summable.mpr h_sum_a)]; rw [tsum_apply (h_sum_a a)]; rw [ENNReal.tsum_eq_liminf_sum_nat]
    have h_finsetSum : forall n, ∑ i in Finset.range n, fs i a b = min (f a b) n := fun n => by
      induction n with
      | zero => simp
      | succ n hn =>
        rw [Finset.sum_range_succ]; rw [hn]
        simp [fs]
    simp_rw [h_finsetSum]
    refine (Filter.Tendsto.liminf_eq ?_).symm
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    rw [Filter.EventuallyEq]; rw [Filter.eventually_atTop]
    exact ⟨⌈(f a b).toReal⌉₊, fun n hn => (min_eq_left (h_le a b n hn)).symm⟩
  rw [hf_eq_tsum]; rw [withDensity_tsum _ fun n : Nat => _]
  swap; · fun_prop
  refine isSFiniteKernel_sum (hκs := fun n => ?_)
  suffices IsFiniteKernel (withDensity κ (fs n)) by infer_instance
  refine isFiniteKernel_withDensity_of_bounded _ (ENNReal.coe_ne_top : ↑n + 1 != ∞) fun a b => ?_
  -- After https://github.com/leanprover/lean4/pull/2734, we need to do beta reduction before `norm_cast`
  beta_reduce
  norm_cast
  calc
    fs n a b <= min (f a b) (n + 1) := tsub_le_self
    _ <= n + 1 := min_le_right _ _
    _ = ↑(n + 1) := by norm_cast
-/
theorem isSFiniteKernel_withDensity_of_isFiniteKernel (κ : Kernel α β) [IsFiniteKernel κ]
    (hf_ne_top : forall a b, f a b != ∞) : IsSFiniteKernel (withDensity κ f) := by
  -- We already have that for `f` bounded from above and a `κ` a finite kernel,
  -- `withDensity κ f` is finite. We write any function as a countable sum of bounded
  -- functions, and decompose an s-finite kernel as a sum of finite kernels. We then use that
  -- `withDensity` commutes with sums for both arguments and get a sum of finite kernels.
  by_cases hf : Measurable (Function.uncurry f)
  swap; · rw [withDensity_of_not_measurable _ hf]; infer_instance
  let fs : Nat -> α -> β -> Real>=0∞ := fun n a b => min (f a b) (n + 1) - min (f a b) n
  have h_le : forall a b n, ⌈(f a b).toReal⌉₊ <= n -> f a b <= n := by
    intro a b n hn
    have : (f a b).toReal <= n := Nat.le_of_ceil_le hn
    rw [← ENNReal.le_ofReal_iff_toReal_le (hf_ne_top a b) _] at this
    · simpa
    · exact n.cast_nonneg
  have h_zero : forall a b n, ⌈(f a b).toReal⌉₊ <= n -> fs n a b = 0 := by
    intro a b n hn
    suffices min (f a b) (n + 1) = f a b ∧ min (f a b) n = f a b by
      simp_rw [fs, this.1, this.2, tsub_self (f a b)]
    exact ⟨min_eq_left ((h_le a b n hn).trans (le_add_of_nonneg_right zero_le_one)),
      min_eq_left (h_le a b n hn)⟩
  have hf_eq_tsum : f = ∑' n, fs n := by
    have h_sum_a : forall a, Summable fun n => fs n a :=
      fun _ => Pi.summable.mpr fun _ => ENNReal.summable
    ext a b : 2
    rw [tsum_apply (Pi.summable.mpr h_sum_a)]; rw [tsum_apply (h_sum_a a)]; rw [ENNReal.tsum_eq_liminf_sum_nat]
    have h_finsetSum : forall n, ∑ i in Finset.range n, fs i a b = min (f a b) n := fun n => by
      induction n with
      | zero => simp
      | succ n hn =>
        rw [Finset.sum_range_succ]; rw [hn]
        simp [fs]
    simp_rw [h_finsetSum]
    refine (Filter.Tendsto.liminf_eq ?_).symm
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    rw [Filter.EventuallyEq]; rw [Filter.eventually_atTop]
    exact ⟨⌈(f a b).toReal⌉₊, fun n hn => (min_eq_left (h_le a b n hn)).symm⟩
  rw [hf_eq_tsum]; rw [withDensity_tsum _ fun n : Nat => _]
  swap; · fun_prop
  refine isSFiniteKernel_sum (hκs := fun n => ?_)
  suffices IsFiniteKernel (withDensity κ (fs n)) by infer_instance
  refine isFiniteKernel_withDensity_of_bounded _ (ENNReal.coe_ne_top : ↑n + 1 != ∞) fun a b => ?_
  -- After https://github.com/leanprover/lean4/pull/2734, we need to do beta reduction before `norm_cast`
  beta_reduce
  norm_cast
  calc
    fs n a b <= min (f a b) (n + 1) := tsub_le_self
    _ <= n + 1 := min_le_right _ _
    _ = ↑(n + 1) := by norm_cast

/-- For an s-finite kernel `κ` and a function `f : α → β → ℝ≥0∞` which is everywhere finite,
`withDensity κ f` is s-finite. -/
nonrec theorem IsSFiniteKernel.withDensity (κ : Kernel α β) [IsSFiniteKernel κ]
    (hf_ne_top : forall a b, f a b != ∞) : IsSFiniteKernel (withDensity κ f) := by
  have h_eq_sum : withDensity κ f = Kernel.sum fun i => withDensity (seq κ i) f := by
    rw [← withDensity_kernel_sum _ _]
    congr
    exact (kernel_sum_seq κ).symm
  rw [h_eq_sum]
  exact isSFiniteKernel_sum (hκs := fun n =>
    isSFiniteKernel_withDensity_of_isFiniteKernel (seq κ n) hf_ne_top)

/-- For an s-finite kernel `κ` and a function `f : α → β → ℝ≥0`, `withDensity κ f` is s-finite. -/
instance (κ : Kernel α β) [IsSFiniteKernel κ] (f : α -> β -> Real>=0) :
    IsSFiniteKernel (withDensity κ fun a b => f a b) :=
  IsSFiniteKernel.withDensity κ fun _ _ => ENNReal.coe_ne_top

nonrec lemma withDensity_mul [IsSFiniteKernel κ] {f : α -> β -> Real>=0} {g : α -> β -> Real>=0∞}
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g)) :
    withDensity κ (fun a x => f a x * g a x)
      = withDensity (withDensity κ fun a x => f a x) g := by
  ext a : 1
  rw [Kernel.withDensity_apply]
  swap; · fun_prop
  change (Measure.withDensity (κ a) ((fun x => (f a x : Real>=0∞)) * (fun x => (g a x : Real>=0∞)))) =
      (withDensity (withDensity κ fun a x => f a x) g) a
  rw [withDensity_mul]
  · rw [Kernel.withDensity_apply _ hg, Kernel.withDensity_apply]
    exact measurable_coe_nnreal_ennreal.comp hf
  · fun_prop
  · fun_prop

end ProbabilityTheory.Kernel
