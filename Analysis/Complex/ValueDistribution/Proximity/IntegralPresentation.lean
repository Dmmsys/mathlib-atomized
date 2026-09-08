/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Stefan Kebekus
-/

module

public import Mathlib.Analysis.Complex.ValueDistribution.Proximity.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage

/-!
# Integral Presentation of the Proximity Function

If `f : ℂ → ℂ` is meromorphic, this file establishes a presentation of the proximity function
`proximity f ⊤` as iterated circle averages. This statement can be used to compare the proximity-
and logarithmic counting functions, and is one of the key ingredients in the proof of Cartan's
classic formula for the characteristic function.

See Section VI.2 of [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677] for a detailed
discussion.
-/

public section

open Filter MeasureTheory Real Set

namespace ValueDistribution

variable {f : ℂ → ℂ} {R : ℝ}

namespace Cartan

/-!
### Integrability of the Cartan Kernel

The proof of the integral presentation of the proximity function relies on an extended computation,
applying Fubini's theorem to the Cartan kernel of integration. This section defines the kernel and
establishes its integrability, as a function of two variables.
-/

/--
Given `f : ℂ → ℂ` and `R : ℝ`, define the Cartan kernel of integration as the function
`α β ↦ log ‖f (circleMap 0 R β) - circleMap 0 1 α‖`.
-/
/-
**ValueDistribution.Cartan.cartanKernel** 是 Mathlib 中的一个定义，位于命名空间 `ValueDistribu
tion.Cartan`。
形式化陈述：cartanKernel (f : Complex -> Complex) (R : Real) (α β : Real) : Real
参数：f : Complex -> Complex；R : Real；α β : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `f : ℂ → ℂ` and `R : ℝ`, define the Cartan kernel of integration as the fu
nction
`α β ↦ log ‖f (circleMap 0 R β) - circleMap 0 1 α‖`.
-/
noncomputable def cartanKernel (f : ℂ → ℂ) (R : ℝ) (α β : ℝ) : ℝ :=
  log ‖f (circleMap 0 R β) - circleMap 0 1 α‖

/--
For every function `f : ℂ → ℂ`, the Cartan kernel of integration `cartanKernel f R α β` is
integrable as a function in `α`.
-/
/-
**ValueDistribution.Cartan.integrableOn_cartanKernel_left** 是 Mathlib 中的一个引理，位于命
名空间 `ValueDistribution.Cartan`。
形式化陈述：integrableOn_cartanKernel_left (f : Complex -> Complex) (R : Real) (β : Re
al) : IntegrableOn (cartanKernel f R · β) (Ioc 0 (2 * π))
参数：f : Complex -> Complex；R : Real；β : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `intervalIntegrable_iff_integrableOn_Ioc_of_le`：intervalIntegrable_iff_in
tegrableOn_Ioc_of_le (hab : a <= b) : IntervalIntegrable f μ a b ↔ IntegrableOn 
f (Ioc a b) μ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.two_pi_pos`：two_pi_pos : 0 < 2 * π
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `norm_sub_rev`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), 
‖a - b‖ = ‖b - a‖
· 使用引理 `circleIntegrable_log_norm_sub_const`：circleIntegrable_log_norm_sub_const
 (r : Real) : CircleIntegrable (log ‖· - a‖) c r

--- 原说明 ---
For every function `f : ℂ → ℂ`, the Cartan kernel of integration `cartanKernel f
 R α β` is
integrable as a function in `α`.
-/
lemma integrableOn_cartanKernel_left (f : ℂ → ℂ) (R : ℝ) (β : ℝ) :
    IntegrableOn (cartanKernel f R · β) (Ioc 0 (2 * π)) := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le).1
  simpa [cartanKernel, norm_sub_rev, CircleIntegrable] using circleIntegrable_log_norm_sub_const 1

/--
If `f : ℂ → ℂ` is measurable, then the Cartan kernel of integration is measurable as a function in
the two variables `α` and `β`.
-/
@[fun_prop]
/-
**ValueDistribution.Cartan.measurable_cartanKernel** 是 Mathlib 中的一个定理，位于命名空间 `Va
lueDistribution.Cartan`。
形式化陈述：measurable_cartanKernel (hf : Measurable f) : Measurable (fun p : Real × R
eal => cartanKernel f R p.1 p.2)
参数：hf : Measurable f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.log`：∀ {α : Type u_1} {m : MeasurableSpace α} {f : α → ℝ}, Me
asurable f → Measurable fun x => Real.log (f x)
· 使用定理 `Measurable.norm`：Measurable.norm {f : β -> α} (hf : Measurable f) : Meas
urable fun a => norm (f a)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Measurable.fun_sub`：∀ {G : Type u_2} {α : Type u_3} [inst : MeasurableSp
ace G] [inst_1 : Sub G] {m : MeasurableSpace α} {f g : α → G}   [MeasurableSub₂ 
G], Meas…
· 使用定理 `ContinuousSub.measurableSub₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Sub γ] [Con…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
· 使用定理 `measurable_circleMap`：measurable_circleMap (c : Complex) (R : Real) : Me
asurable (circleMap c R)
· 使用定理 `Measurable.snd`：Measurable.snd {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).2
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `Measurable.fst`：Measurable.fst {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).1

--- 原说明 ---
If `f : ℂ → ℂ` is measurable, then the Cartan kernel of integration is measurabl
e as a function in
the two variables `α` and `β`.
-/
theorem measurable_cartanKernel (hf : Measurable f) :
    Measurable (fun p : ℝ × ℝ ↦ cartanKernel f R p.1 p.2) := by
  unfold cartanKernel; fun_prop

/- Formula for the `L¹` norm of an angular slice of the Cartan kernel. -/
/-
**ValueDistribution.Cartan.integral_norm_cartanKernel_eq** 是 Mathlib 中的一个引理，位于命名
空间 `ValueDistribution.Cartan`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Formula for the `L¹` norm of an angular slice of the Cartan kernel.
-/
private lemma integral_norm_cartanKernel_eq (f : ℂ → ℂ) (R β : ℝ) :
    ∫ α in Ioc 0 (2 * π), ‖cartanKernel f R α β‖ =
      2 * (∫ α, (cartanKernel f R α β)⁺ ∂(volume.restrict (Ioc 0 (2 * π)))) -
        (2 * π) * log⁺ ‖f (circleMap 0 R β)‖ := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 (2 * π))
  calc ∫ α, ‖cartanKernel f R α β‖ ∂μ
    _ = 2 * (∫ α, (cartanKernel f R α β)⁺ ∂μ) - ∫ α, cartanKernel f R α β ∂μ :=
      integral_abs_eq_two_mul_integral_posPart_sub_integral (integrableOn_cartanKernel_left f R β)
    _ = 2 * (∫ α, (cartanKernel f R α β)⁺ ∂μ) - 2 * π * log⁺ ‖f (circleMap 0 R β)‖ := by
      congr
      set z := f (circleMap 0 R β)
      suffices h_avg : circleAverage (log ‖z - ·‖) 0 1 = log⁺ ‖z‖ by
        convert congr(2 * π * $h_avg)
        simp [circleAverage_def, field, cartanKernel, intervalIntegral.integral_of_le two_pi_pos.le]
      simp [norm_sub_rev]

/-
If `f : ℂ → ℂ` is meromorphic,, then the `L¹` norms of the angular slices of the Cartan kernel form
an integrable family.
-/
/-
**ValueDistribution.Cartan.integrable_integral_norm_cartanKernel** 是 Mathlib 中的一
个引理，位于命名空间 `ValueDistribution.Cartan`。
形式化陈述：integrable_integral_norm_cartanKernel (h : Meromorphic f) : Integrable (∫ 
α, ‖cartanKernel f R α ·‖ ∂(volume.restrict (Ioc 0 (2 * π)))) (volume.restrict (
Ioc 0 (2 * π)))
参数：h : Meromorphic f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用引理 `continuous_posPart`：continuous_posPart : Continuous (posPart : α -> α)
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `ValueDistribution.Cartan.measurable_cartanKernel`：measurable_cartanKerne
l (hf : Measurable f) : Measurable (fun p : Real × Real => cartanKernel f R p.1 
p.2)
· 使用定理 `Meromorphic.measurable`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{f : 𝕜 → E} …
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `MeromorphicOn.circleIntegrable_posLog_norm`：MeromorphicOn.circleIntegrab
le_posLog_norm (hf : MeromorphicOn f (sphere c |R|)) : CircleIntegrable (log⁺ ‖f
 ·‖) c R
· 使用引理 `Meromorphic.meromorphicOn`：meromorphicOn {s : Set 𝕜} (hf : Meromorphic f
) : MeromorphicOn f s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegrable_iff_integrableOn_Ioc_of_le`：intervalIntegrable_iff_in
tegrableOn_Ioc_of_le (hab : a <= b) : IntervalIntegrable f μ a b ↔ IntegrableOn 
f (Ioc a b) μ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.two_pi_pos`：two_pi_pos : 0 < 2 * π
· 使用定理 `CircleIntegrable.eq_1`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] (f
 : ℂ → E) (c : ℂ) (R : ℝ),   CircleIntegrable f c R = IntervalIntegrable (fun θ 
=> f (circl…
· 使用定理 `MeasureTheory.Integrable.add`：∀ {α : Type u_1} {m : MeasurableSpace α} {
μ : MeasureTheory.Measure α} {ε' : Type u_8} [inst : TopologicalSpace ε']   [ins
t_1 : ESeminormedA…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `MeasureTheory.integrable_const`：integrable_const [IsFiniteMeasure μ] (c 
: β) : Integrable (fun _ : α => c) μ
· 使用定理 `MeasureTheory.Integrable.mono`：∀ {α : Type u_1} {β : Type u_2} {γ : Type
 u_3} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : NormedAddC
ommGroup β] [inst_1…
· 使用定理 `MeasureTheory.Integrable.const_mul`：∀ {α : Type u_1} {m : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} {𝕜 : Type u_8} [inst : NormedRing 𝕜] {f : α →
 𝕜},   MeasureTheory.Int…
（共 92 条，此处仅展示前 30 条）

--- 原说明 ---
If `f : ℂ → ℂ` is meromorphic,, then the `L¹` norms of the angular slices of the
 Cartan kernel form
an integrable family.
-/
lemma integrable_integral_norm_cartanKernel (h : Meromorphic f) :
    Integrable (∫ α, ‖cartanKernel f R α ·‖ ∂(volume.restrict (Ioc 0 (2 * π))))
      (volume.restrict (Ioc 0 (2 * π))) := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 (2 * π))
  have h_meas_K : Measurable (fun a : ℝ × ℝ ↦ (cartanKernel f R a.1 a.2)⁺) := by fun_prop
  have h_int_posLog : Integrable (fun β ↦ log⁺ ‖f (circleMap 0 R β)‖) μ := by
    have : CircleIntegrable (log⁺ ‖f ·‖) 0 R := h.meromorphicOn.circleIntegrable_posLog_norm
    rwa [CircleIntegrable, intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le] at this
  have h_int_Bound : Integrable (fun β ↦ log⁺ ‖f (circleMap 0 R β)‖ + log 2) μ :=
    h_int_posLog.add (integrable_const _)
  have h_int_Term1 : Integrable (fun β ↦ ∫ α, (cartanKernel f R α β)⁺ ∂μ) μ := by
    apply Integrable.mono (h_int_Bound.const_mul (2 * π))
      h_meas_K.stronglyMeasurable.integral_prod_left'.aestronglyMeasurable
    filter_upwards with β
    have h_int_nonneg : 0 ≤ ∫ α, (cartanKernel f R α β)⁺ ∂μ := by positivity
    have h_bound_nonneg : 0 ≤ (2 * π) * (log⁺ ‖f (circleMap 0 R β)‖ + log 2) := by
      positivity [posLog_nonneg (x := ‖f (circleMap 0 R β)‖)]
    rw [norm_of_nonneg h_int_nonneg, norm_of_nonneg h_bound_nonneg]
    have : ∫ α, (cartanKernel f R α β)⁺ ∂(volume.restrict (Ioc 0 (2 * π))) ≤
        ∫ _, log⁺ ‖f (circleMap 0 R β)‖ + log 2 ∂(volume.restrict (Ioc 0 (2 * π))) := by
      refine integral_mono_of_nonneg (.of_forall (by simp [posPart])) (integrable_const _)
        (.of_forall ?_)
      intro α
      calc (cartanKernel f R α β)⁺
        _ = log⁺ ‖f (circleMap 0 R β) + (-circleMap 0 1 α)‖ := by
          simp [cartanKernel, posLog_def, posPart, max_comm, sub_eq_add_neg]
        _ ≤ log⁺ ‖f (circleMap 0 R β)‖ + log⁺ ‖-circleMap 0 1 α‖ + log 2 :=
          posLog_norm_add_le (f (circleMap 0 R β)) (-circleMap 0 1 α)
        _ = log⁺ ‖f (circleMap 0 R β)‖ + log 2 := by
          simp [norm_circleMap_zero, add_comm]
    rwa [integral_const, smul_eq_mul, mul_comm, measureReal_restrict_apply_univ,
      mul_comm, volume_real_Ioc_of_le two_pi_pos.le, sub_zero] at this
  exact Integrable.congr ((h_int_Term1.const_mul 2).sub (h_int_posLog.const_mul (2 * π)))
    (Eventually.of_forall fun β ↦ (integral_norm_cartanKernel_eq f R β).symm)

/--
If `f : ℂ → ℂ` is meromorphic, then the Cartan kernel of integration is integrable as a function in
the two variables `α` and `β`.
-/
/-
**ValueDistribution.Cartan.integrableOn_cartanKernel** 是 Mathlib 中的一个定理，位于命名空间 `
ValueDistribution.Cartan`。
形式化陈述：integrableOn_cartanKernel (h : Meromorphic f) : IntegrableOn (fun p => car
tanKernel f R p.1 p.2) (uIoc 0 (2 * π) ×ˢ uIoc 0 (2 * π))
参数：h : Meromorphic f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.IntegrableOn.eq_1`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]   (f 
: α → ε) (s : Set α) …
· 使用定理 `MeasureTheory.Measure.volume_eq_prod`：volume_eq_prod (α β) [MeasureSpace
 α] [MeasureSpace β] : (volume : Measure (α × β)) = (volume : Measure α).prod (v
olume : Measure β)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.prod_restrict`：prod_restrict (s : Set α) (t : Set 
β) : (μ.restrict s).prod (ν.restrict t) = (μ.prod ν).restrict (s ×ˢ t)
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `Meromorphic.measurable`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{f : 𝕜 → E} …
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.uIoc_of_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b
 → Set.uIoc a b = Set.Ioc a b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.two_pi_pos`：two_pi_pos : 0 < 2 * π
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.integrable_prod_iff'`：integrable_prod_iff' [SFinite μ] ⦃f 
: α × β -> E⦄ (h1f : AEStronglyMeasurable f (μ.prod ν)) : Integrable f (μ.prod ν
) ↔ (forallᵐ y ∂ν, Integ…
· 使用定理 `MeasureTheory.instSFiniteRestrict`：∀ {α : Type u_1} {m0 : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} [MeasureTheory.SFinite μ] (s : Set α),   Meas
ureTheory.SFinite (μ.re…
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
If `f : ℂ → ℂ` is meromorphic, then the Cartan kernel of integration is integrab
le as a function in
the two variables `α` and `β`.
-/
theorem integrableOn_cartanKernel (h : Meromorphic f) :
    IntegrableOn (fun p ↦ cartanKernel f R p.1 p.2) (uIoc 0 (2 * π) ×ˢ uIoc 0 (2 * π)) := by
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
  have := h.measurable
  simpa [uIoc_of_le two_pi_pos.le] using (integrable_prod_iff' (by fun_prop)).2
    ⟨Eventually.of_forall (integrableOn_cartanKernel_left f R),
      integrable_integral_norm_cartanKernel h⟩

/--
Corollary of `integrableOn_cartanKernel`: If `f : ℂ → ℂ` is meromorphic, then the function
`β ↦ ∫ α in 0..2 * π, Cartan.cartanKernel f R α β` is integrable.
-/
/-
**ValueDistribution.Cartan.integrableOn_intervalIntegral_cartanKernel_left** 是 M
athlib 中的一个引理，位于命名空间 `ValueDistribution.Cartan`。
形式化陈述：integrableOn_intervalIntegral_cartanKernel_left (h : Meromorphic f) : Inte
grableOn (∫ α in 0..2 * π, Cartan.cartanKernel f R α ·) (Ioc 0 (2 * π))
参数：h : Meromorphic f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ValueDistribution.Cartan.integrableOn_cartanKernel`：integrableOn_cartanK
ernel (h : Meromorphic f) : IntegrableOn (fun p => cartanKernel f R p.1 p.2) (uI
oc 0 (2 * π) ×ˢ uIoc 0 (2 * π))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.two_pi_pos`：two_pi_pos : 0 < 2 * π
· 使用定理 `MeasureTheory.Integrable.integral_prod_right`：∀ {α : Type u_1} {β : Type
 u_2} {E : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {
μ : MeasureTheory.Measure α} {ν : …
· 使用定理 `MeasureTheory.instSFiniteRestrict`：∀ {α : Type u_1} {m0 : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} [MeasureTheory.SFinite μ] (s : Set α),   Meas
ureTheory.SFinite (μ.re…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.prod_restrict`：prod_restrict (s : Set α) (t : Set 
β) : (μ.restrict s).prod (ν.restrict t) = (μ.prod ν).restrict (s ×ˢ t)
· 使用定理 `MeasureTheory.Measure.volume_eq_prod`：volume_eq_prod (α β) [MeasureSpace
 α] [MeasureSpace β] : (volume : Measure (α × β)) = (volume : Measure α).prod (v
olume : Measure β)
· 使用定理 `MeasureTheory.IntegrableOn.eq_1`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]   (f 
: α → ε) (s : Set α) …
· 使用定理 `Set.uIoc_of_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b
 → Set.uIoc a b = Set.Ioc a b

--- 原说明 ---
Corollary of `integrableOn_cartanKernel`: If `f : ℂ → ℂ` is meromorphic, then th
e function
`β ↦ ∫ α in 0..2 * π, Cartan.cartanKernel f R α β` is integrable.
-/
lemma integrableOn_intervalIntegral_cartanKernel_left (h : Meromorphic f) :
    IntegrableOn (∫ α in 0..2 * π, Cartan.cartanKernel f R α ·) (Ioc 0 (2 * π)) := by
  have h_int := Cartan.integrableOn_cartanKernel (R := R) h
  rw [uIoc_of_le two_pi_pos.le, IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
    at h_int
  simpa [IntegrableOn, intervalIntegral.integral_of_le two_pi_pos.le, Cartan.cartanKernel]
    using h_int.integral_prod_right

/--
Corollary of `integrableOn_cartanKernel`: If `f : ℂ → ℂ` is meromorphic, then the function
`α ↦ ∫ β in 0..2 * π, Cartan.cartanKernel f R α β` is integrable.
-/
/-
**ValueDistribution.Cartan.integrableOn_intervalIntegral_cartanKernel_right** 是 
Mathlib 中的一个引理，位于命名空间 `ValueDistribution.Cartan`。
形式化陈述：integrableOn_intervalIntegral_cartanKernel_right (h : Meromorphic f) : Int
egrableOn (∫ β in 0..2 * π, Cartan.cartanKernel f R · β) (Ioc 0 (2 * π))
参数：h : Meromorphic f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ValueDistribution.Cartan.integrableOn_cartanKernel`：integrableOn_cartanK
ernel (h : Meromorphic f) : IntegrableOn (fun p => cartanKernel f R p.1 p.2) (uI
oc 0 (2 * π) ×ˢ uIoc 0 (2 * π))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.two_pi_pos`：two_pi_pos : 0 < 2 * π
· 使用定理 `MeasureTheory.Integrable.integral_prod_left`：∀ {α : Type u_1} {β : Type 
u_2} {E : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {μ
 : MeasureTheory.Measure α} {ν : …
· 使用定理 `MeasureTheory.instSFiniteRestrict`：∀ {α : Type u_1} {m0 : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} [MeasureTheory.SFinite μ] (s : Set α),   Meas
ureTheory.SFinite (μ.re…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.prod_restrict`：prod_restrict (s : Set α) (t : Set 
β) : (μ.restrict s).prod (ν.restrict t) = (μ.prod ν).restrict (s ×ˢ t)
· 使用定理 `MeasureTheory.Measure.volume_eq_prod`：volume_eq_prod (α β) [MeasureSpace
 α] [MeasureSpace β] : (volume : Measure (α × β)) = (volume : Measure α).prod (v
olume : Measure β)
· 使用定理 `MeasureTheory.IntegrableOn.eq_1`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]   (f 
: α → ε) (s : Set α) …
· 使用定理 `Set.uIoc_of_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b
 → Set.uIoc a b = Set.Ioc a b

--- 原说明 ---
Corollary of `integrableOn_cartanKernel`: If `f : ℂ → ℂ` is meromorphic, then th
e function
`α ↦ ∫ β in 0..2 * π, Cartan.cartanKernel f R α β` is integrable.
-/
lemma integrableOn_intervalIntegral_cartanKernel_right (h : Meromorphic f) :
    IntegrableOn (∫ β in 0..2 * π, Cartan.cartanKernel f R · β) (Ioc 0 (2 * π)) := by
  have h_int := Cartan.integrableOn_cartanKernel (R := R) h
  rw [uIoc_of_le two_pi_pos.le, IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
    at h_int
  simpa [IntegrableOn, intervalIntegral.integral_of_le two_pi_pos.le, Cartan.cartanKernel]
    using h_int.integral_prod_left

end Cartan

/--
Presentation of the proximity function as iterated circle averages.
-/
/-
**ValueDistribution.circleAverage_circleAverage_eq_proximity_top** 是 Mathlib 中的一
个定理，位于命名空间 `ValueDistribution`。
形式化陈述：circleAverage_circleAverage_eq_proximity_top (h : Meromorphic f) : (fun R 
=> circleAverage (fun a => circleAverage (log ‖f · - a‖) 0 R) 0 1) = proximity f
 ⊤
参数：h : Meromorphic f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `intervalIntegral.integral_const_mul`：integral_const_mul [NormedDivisionR
ing 𝕜] [NormedAlgebra Real 𝕜] (r : 𝕜) (f : Real -> 𝕜) : ∫ x in a..b, r * f x ∂μ 
= r * ∫ x in a..b, f x ∂μ
· 使用定理 `_private.Mathlib.Analysis.Complex.ValueDistribution.Proximity.IntegralPr
esentation.0.ValueDistribution.Cartan.cartanKernel.eq_1`：∀ (f : ℂ → ℂ) (R α β : 
ℝ),   ValueDistribution.Cartan.cartanKernel f R α β = Real.log ‖f (circleMap 0 R
 β) - circleMap 0 1 α‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `MeasureTheory.intervalIntegral_intervalIntegral_swap`：intervalIntegral_i
ntervalIntegral_swap {F : Real -> Real -> E} {a b c d : Real} (h : IntegrableOn 
F.uncurry (uIoc a b ×ˢ uIoc c d)) : ∫ x in…
· 使用定理 `ValueDistribution.Cartan.integrableOn_cartanKernel`：integrableOn_cartanK
ernel (h : Meromorphic f) : IntegrableOn (fun p => cartanKernel f R p.1 p.2) (uI
oc 0 (2 * π) ×ˢ uIoc 0 (2 * π))
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `intervalIntegral.integral_congr`：integral_congr {a b : Real} (h : EqOn f
 g [[a, b]]) : ∫ x in a..b, f x ∂μ = ∫ x in a..b, g x ∂μ
· 使用定理 `norm_sub_rev`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), 
‖a - b‖ = ‖b - a‖
· 使用定理 `circleAverage_log_norm_sub_const_eq_posLog`：circleAverage_log_norm_sub_c
onst_eq_posLog : circleAverage (log ‖· - a‖) 0 1 = log⁺ ‖a‖
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.two_pi_pos`：two_pi_pos : 0 < 2 * π

--- 原说明 ---
Presentation of the proximity function as iterated circle averages.
-/
theorem circleAverage_circleAverage_eq_proximity_top (h : Meromorphic f) :
    (fun R ↦ circleAverage (fun a ↦ circleAverage (log ‖f · - a‖) 0 R) 0 1) = proximity f ⊤ := by
  ext R
  let F : ℝ → ℝ → ℝ := Cartan.cartanKernel f R
  calc circleAverage (fun a ↦ circleAverage (log ‖f · - a‖) 0 R) 0 1
    _ = (2 * π)⁻¹ * (2 * π)⁻¹ * ∫ α in 0..2 * π, ∫ β in 0..2 * π, F α β := by
      simp [circleAverage, F, Cartan.cartanKernel, mul_assoc]
    _ = (2 * π)⁻¹ * (2 * π)⁻¹ * ∫ β in 0..2 * π, ∫ α in 0..2 * π, F α β := by
      rw [MeasureTheory.intervalIntegral_intervalIntegral_swap]
      exact Cartan.integrableOn_cartanKernel h
    _ = (2 * π)⁻¹ * ∫ β in 0..2 * π, ((2 * π)⁻¹ * ∫ α in 0..2 * π, F α β) := by
      simp [mul_comm, mul_left_comm, mul_assoc]
    _ = (2 * π)⁻¹ * ∫ β in 0..2 * π, log⁺ ‖f (circleMap 0 R β)‖ := by
      congr 1
      apply intervalIntegral.integral_congr
      intro β hβ
      calc (2 * π)⁻¹ * ∫ α in 0..2 * π, F α β
        _ = circleAverage (log ‖f (circleMap 0 R β) - ·‖) 0 1 := by
          simp [F, circleAverage, Cartan.cartanKernel]
        _ = log⁺ ‖f (circleMap 0 R β)‖ := by
          simp [norm_sub_rev]
    _ = circleAverage (log⁺ ‖f ·‖) 0 R := by
      simp [circleAverage, intervalIntegral.integral_of_le two_pi_pos.le]

/--
Complementary statement to `proximity_top_eq_circleAverage_circleAverage`, providing circle
integrability of the integrand.
-/
/-
**ValueDistribution.circleIntegrable_circleAverage_log_norm_sub** 是 Mathlib 中的一个
定理，位于命名空间 `ValueDistribution`。
形式化陈述：circleIntegrable_circleAverage_log_norm_sub (h : Meromorphic f) : CircleIn
tegrable (fun a => circleAverage (log ‖f · - a‖) 0 R) 0 1
参数：h : Meromorphic f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `norm_sub_rev`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), 
‖a - b‖ = ‖b - a‖
· 使用定理 `Real.circleAverage_zero`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] 
[inst_1 : NormedSpace ℝ E] {f : ℂ → E} {c : ℂ} [CompleteSpace E],   Real.circleA
verage f c 0 …
· 使用定理 `CircleIntegrable.eq_1`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] (f
 : ℂ → E) (c : ℂ) (R : ℝ),   CircleIntegrable f c R = IntervalIntegrable (fun θ 
=> f (circl…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `intervalIntegrable_iff_integrableOn_Ioc_of_le`：intervalIntegrable_iff_in
tegrableOn_Ioc_of_le (hab : a <= b) : IntervalIntegrable f μ a b ↔ IntegrableOn 
f (Ioc a b) μ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.two_pi_pos`：two_pi_pos : 0 < 2 * π
· 使用定理 `MeasureTheory.IntegrableOn.congr_fun`：∀ {α : Type u_1} {ε : Type u_3} {m
α : MeasurableSpace α} {f g : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}  
 [inst : TopologicalSpace …
· 使用定理 `MeasureTheory.Integrable.const_mul`：∀ {α : Type u_1} {m : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} {𝕜 : Type u_8} [inst : NormedRing 𝕜] {f : α →
 𝕜},   MeasureTheory.Int…
· 使用引理 `ValueDistribution.Cartan.integrableOn_intervalIntegral_cartanKernel_righ
t`：integrableOn_intervalIntegral_cartanKernel_right (h : Meromorphic f) : Integr
ableOn (∫ β in 0..2 * π, Cartan.cartanKernel f R · β) (Ioc 0 (2…
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `measurableSet_Ioc`：measurableSet_Ioc [ClosedIicTopology α] : MeasurableS
et (Ioc a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ

--- 原说明 ---
Complementary statement to `proximity_top_eq_circleAverage_circleAverage`, provi
ding circle
integrability of the integrand.
-/
theorem circleIntegrable_circleAverage_log_norm_sub (h : Meromorphic f) :
    CircleIntegrable (fun a ↦ circleAverage (log ‖f · - a‖) 0 R) 0 1 := by
  by_cases hR : R = 0
  · simp [hR, circleAverage_zero, norm_sub_rev, circleIntegrable_log_norm_sub_const]
  rw [CircleIntegrable, intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le]
  apply IntegrableOn.congr_fun
    ((Cartan.integrableOn_intervalIntegral_cartanKernel_right (R := R) h).const_mul (2 * π)⁻¹)
    (fun _ _ ↦ by simp [circleAverage, Cartan.cartanKernel]) measurableSet_Ioc

end ValueDistribution

