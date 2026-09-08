/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Measurability of real and complex functions

We show that most standard real and complex functions are measurable, notably `exp`, `cos`, `sin`,
`cosh`, `sinh`, `log`, `pow`, `arcsin`, `arccos`.

See also `MeasureTheory.Function.SpecialFunctions.Arctan` and
`MeasureTheory.Function.SpecialFunctions.Inner`, which have been split off to minimize imports.
-/

public section

-- Guard against import creep:
assert_not_exists InnerProductSpace Real.arctan FiniteDimensional.proper

noncomputable section

open NNReal ENNReal MeasureTheory

namespace Real

variable {α : Type*} {_ : MeasurableSpace α} {f : α → ℝ} {μ : MeasureTheory.Measure α}

/-
**Real.measurable_exp** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：measurable_exp : Measurable exp
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Real.continuous_exp`：continuous_exp : Continuous exp
-/
theorem measurable_exp : Measurable exp :=
  continuous_exp.measurable
/-
**Real.measurable_log** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：measurable_log : Measurable log
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_of_measurable_on_compl_singleton`：measurable_of_measurable_on
_compl_singleton [MeasurableSingletonClass α] {f : α -> β} (a : α) (hf : Measura
ble ({ x | x != a }.domRestrict f…
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `instMeasurableEqOfSecondCountableTopologyOfT2Space`：∀ {α : Type u_1} [in
st : TopologicalSpace α] [inst_1 : MeasurableSpace α] [OpensMeasurableSpace α]  
 [SecondCountableTopology α] [T2Space α]…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuousOn_iff_continuous_domRestrict`：continuousOn_iff_continuous_dom
Restrict : ContinuousOn f s ↔ Continuous (s.domRestrict f)
· 使用定理 `Real.continuousOn_log`：continuousOn_log : ContinuousOn log {0}ᶜ
-/
theorem measurable_log : Measurable log :=
  measurable_of_measurable_on_compl_singleton 0 <|
    Continuous.measurable <| continuousOn_iff_continuous_domRestrict.1 continuousOn_log
/-
**Real.measurable_of_measurable_exp** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：measurable_of_measurable_exp (hf : Measurable (fun x => exp (f x))) : Meas
urable f
参数：hf : Measurable (fun x => exp (f x))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.log_exp`：log_exp (x : Real) : log (exp x) = x
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `Real.measurable_log`：measurable_log : Measurable log
-/
lemma measurable_of_measurable_exp (hf : Measurable (fun x ↦ exp (f x))) :
    Measurable f := by
  have : f = fun x ↦ log (exp (f x)) := by ext; rw [log_exp]
  rw [this]
  exact measurable_log.comp hf
/-
**Real.aemeasurable_of_aemeasurable_exp** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：aemeasurable_of_aemeasurable_exp (hf : AEMeasurable (fun x => exp (f x)) μ
) : AEMeasurable f μ
参数：hf : AEMeasurable (fun x => exp (f x)) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.log_exp`：log_exp (x : Real) : log (exp x) = x
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `Real.measurable_log`：measurable_log : Measurable log
-/
lemma aemeasurable_of_aemeasurable_exp (hf : AEMeasurable (fun x ↦ exp (f x)) μ) :
    AEMeasurable f μ := by
  have : f = fun x ↦ log (exp (f x)) := by ext; rw [log_exp]
  rw [this]
  exact measurable_log.comp_aemeasurable hf
/-
**Real.aemeasurable_of_aemeasurable_exp_mul** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：aemeasurable_of_aemeasurable_exp_mul {t : Real} (ht : t != 0) (hf : AEMeas
urable (fun x => exp (t * f x)) μ) : AEMeasurable f μ
参数：ht : t != 0；hf : AEMeasurable (fun x => exp (t * f x)) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `GroupWithZero.toMulDivCancelClass`：∀ {G₀ : Type u} [inst : GroupWithZero
 G₀], MulDivCancelClass G₀
· 使用定理 `AEMeasurable.fun_div`：∀ {G : Type u_2} {α : Type u_3} [inst : Measurable
Space G] [inst_1 : Div G] {m : MeasurableSpace α} {f g : α → G}   {μ : MeasureTh
eory.Measu…
· 使用定理 `measurableDiv₂_of_mul_inv`：∀ (G : Type u_2) [inst : MeasurableSpace G] [
inst_1 : DivInvMonoid G] [MeasurableMul₂ G] [MeasurableInv G],   MeasurableDiv₂ 
G
· 使用定理 `ContinuousMul.measurableMul₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Mul γ] [Con…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `ContinuousInv₀.measurableInv`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : GroupWithZero γ]   [T1S
pace γ] [Continuou…
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `instIsTopologicalDivisionRingReal`：IsTopologicalDivisionRing ℝ
· 使用引理 `Real.aemeasurable_of_aemeasurable_exp`：aemeasurable_of_aemeasurable_exp 
(hf : AEMeasurable (fun x => exp (f x)) μ) : AEMeasurable f μ
· 使用定理 `aemeasurable_const`：aemeasurable_const {b : β} : AEMeasurable (fun _a : 
α => b) μ
-/
lemma aemeasurable_of_aemeasurable_exp_mul {t : ℝ}
    (ht : t ≠ 0) (hf : AEMeasurable (fun x ↦ exp (t * f x)) μ) :
    AEMeasurable f μ := by
  simpa only [mul_div_cancel_left₀ _ ht]
    using (aemeasurable_of_aemeasurable_exp hf).fun_div (aemeasurable_const (b := t))
/-
**Real.measurable_sin** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：measurable_sin : Measurable sin
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Real.continuous_sin`：continuous_sin : Continuous sin
-/
theorem measurable_sin : Measurable sin :=
  continuous_sin.measurable
/-
**Real.measurable_cos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：measurable_cos : Measurable cos
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Real.continuous_cos`：continuous_cos : Continuous cos
-/
theorem measurable_cos : Measurable cos :=
  continuous_cos.measurable
/-
**Real.measurable_sinh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：measurable_sinh : Measurable sinh
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Real.continuous_sinh`：continuous_sinh : Continuous sinh
-/
theorem measurable_sinh : Measurable sinh :=
  continuous_sinh.measurable
/-
**Real.measurable_cosh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：measurable_cosh : Measurable cosh
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Real.continuous_cosh`：continuous_cosh : Continuous cosh
-/
theorem measurable_cosh : Measurable cosh :=
  continuous_cosh.measurable

@[fun_prop]
/-
**Real.measurable_arcsin** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：measurable_arcsin : Measurable arcsin
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Real.continuous_arcsin`：continuous_arcsin : Continuous arcsin
-/
theorem measurable_arcsin : Measurable arcsin :=
  continuous_arcsin.measurable

@[fun_prop]
/-
**Real.measurable_arccos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：measurable_arccos : Measurable arccos
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Real.continuous_arccos`：continuous_arccos : Continuous arccos
-/
theorem measurable_arccos : Measurable arccos :=
  continuous_arccos.measurable

end Real

namespace Complex

@[fun_prop]
/-
**Complex.measurable_re** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：measurable_re : Measurable re
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Complex.continuous_re`：Continuous Complex.re
-/
theorem measurable_re : Measurable re :=
  continuous_re.measurable

@[fun_prop]
/-
**Complex.measurable_im** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：measurable_im : Measurable im
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Complex.continuous_im`：Continuous Complex.im
-/
theorem measurable_im : Measurable im :=
  continuous_im.measurable
/-
**Complex.measurable_ofReal** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：measurable_ofReal : Measurable ((↑) : Real -> Complex)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
-/
theorem measurable_ofReal : Measurable ((↑) : ℝ → ℂ) :=
  continuous_ofReal.measurable
/-
**Complex.measurable_exp** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：measurable_exp : Measurable exp
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Complex.continuous_exp`：continuous_exp : Continuous exp
-/
theorem measurable_exp : Measurable exp :=
  continuous_exp.measurable
/-
**Complex.measurable_sin** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：measurable_sin : Measurable sin
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Complex.continuous_sin`：continuous_sin : Continuous sin
-/
theorem measurable_sin : Measurable sin :=
  continuous_sin.measurable
/-
**Complex.measurable_cos** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：measurable_cos : Measurable cos
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Complex.continuous_cos`：continuous_cos : Continuous cos
-/
theorem measurable_cos : Measurable cos :=
  continuous_cos.measurable
/-
**Complex.measurable_sinh** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：measurable_sinh : Measurable sinh
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Complex.continuous_sinh`：continuous_sinh : Continuous sinh
-/
theorem measurable_sinh : Measurable sinh :=
  continuous_sinh.measurable
/-
**Complex.measurable_cosh** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：measurable_cosh : Measurable cosh
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Complex.continuous_cosh`：continuous_cosh : Continuous cosh
-/
theorem measurable_cosh : Measurable cosh :=
  continuous_cosh.measurable
/-
**Complex.measurable_arg** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：measurable_arg : Measurable arg
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.ite`：Measurable.ite {p : α -> Prop} {_ : DecidablePred p} (hp
 : MeasurableSet { a : α | p a }) (hf : Measurable f) (hg : Measurable g) : Meas
urab…
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
· 使用定理 `measurable_le`：measurable_le : Measurable fun p : α × α => p.1 <= p.2
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `Complex.measurable_re`：measurable_re : Measurable re
· 使用定理 `Real.measurable_arcsin`：measurable_arcsin : Measurable arcsin
· 使用定理 `Measurable.fun_div`：∀ {G : Type u_2} {α : Type u_3} [inst : MeasurableSp
ace G] [inst_1 : Div G] {m : MeasurableSpace α} {f g : α → G}   [MeasurableDiv₂ 
G], Meas…
· 使用定理 `measurableDiv₂_of_mul_inv`：∀ (G : Type u_2) [inst : MeasurableSpace G] [
inst_1 : DivInvMonoid G] [MeasurableMul₂ G] [MeasurableInv G],   MeasurableDiv₂ 
G
· 使用定理 `ContinuousMul.measurableMul₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Mul γ] [Con…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `ContinuousInv₀.measurableInv`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : GroupWithZero γ]   [T1S
pace γ] [Continuou…
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `instIsTopologicalDivisionRingReal`：IsTopologicalDivisionRing ℝ
· 使用定理 `Complex.measurable_im`：measurable_im : Measurable im
· 使用定理 `Measurable.norm`：Measurable.norm {f : β -> α} (hf : Measurable f) : Meas
urable fun a => norm (f a)
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `Measurable.add_const`：∀ {M : Type u_2} {α : Type u_3} [inst : Measurable
Space M] [inst_1 : Add M] {m : MeasurableSpace α} {f : α → M}   [MeasurableAdd M
], Measura…
· 使用定理 `ContinuousAdd.measurableAdd`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Add γ]   [SeparatelyCont
inuousAdd γ], Mea…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
（共 40 条，此处仅展示前 30 条）
-/
theorem measurable_arg : Measurable arg :=
  Measurable.ite (by measurability) (by fun_prop) <|
    Measurable.ite (by measurability) (by fun_prop) (by fun_prop)
/-
**Complex.measurable_log** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：measurable_log : Measurable log
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.add`：∀ {M : Type u_2} {α : Type u_3} [inst : MeasurableSpace 
M] [inst_1 : Add M] {m : MeasurableSpace α} {f g : α → M}   [MeasurableAdd₂ M], 
Meas…
· 使用定理 `ContinuousAdd.measurableMul₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Add γ] [Con…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `Complex.measurable_ofReal`：measurable_ofReal : Measurable ((↑) : Real ->
 Complex)
· 使用定理 `Real.measurable_log`：measurable_log : Measurable log
· 使用定理 `measurable_norm`：measurable_norm : Measurable (norm : α -> Real)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Measurable.mul_const`：Measurable.mul_const [MeasurableMul M] (hf : Measu
rable f) (c : M) : Measurable fun x => f x * c
· 使用定理 `ContinuousMul.measurableMul`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Mul γ]   [SeparatelyCont
inuousMul γ], Mea…
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Complex.measurable_arg`：measurable_arg : Measurable arg
-/
theorem measurable_log : Measurable log :=
  (measurable_ofReal.comp <| Real.measurable_log.comp measurable_norm).add <|
    (measurable_ofReal.comp measurable_arg).mul_const I

end Complex

section RealComposition

open Real

variable {α : Type*} {m : MeasurableSpace α} {f : α → ℝ} (hf : Measurable f)
include hf

@[fun_prop]
/-
**Measurable.exp** 是 Mathlib 中的一个定理，位于命名空间 `Measurable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {f : α → ℝ}, Measurable f → Measu
rable fun x => Real.exp (f x)
参数：f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `Real.measurable_exp`：measurable_exp : Measurable exp
-/
protected theorem Measurable.exp : Measurable fun x => Real.exp (f x) :=
  Real.measurable_exp.comp hf

@[fun_prop]
/-
**Measurable.log** 是 Mathlib 中的一个定理，位于命名空间 `Measurable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {f : α → ℝ}, Measurable f → Measu
rable fun x => Real.log (f x)
参数：f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `Real.measurable_log`：measurable_log : Measurable log
-/
protected theorem Measurable.log : Measurable fun x => log (f x) :=
  measurable_log.comp hf

@[fun_prop]
/-
**Measurable.cos** 是 Mathlib 中的一个定理，位于命名空间 `Measurable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {f : α → ℝ}, Measurable f → Measu
rable fun x => Real.cos (f x)
参数：f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `Real.measurable_cos`：measurable_cos : Measurable cos
-/
protected theorem Measurable.cos : Measurable fun x ↦ cos (f x) := measurable_cos.comp hf

@[fun_prop]
/-
**Measurable.sin** 是 Mathlib 中的一个定理，位于命名空间 `Measurable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {f : α → ℝ}, Measurable f → Measu
rable fun x => Real.sin (f x)
参数：f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `Real.measurable_sin`：measurable_sin : Measurable sin
-/
protected theorem Measurable.sin : Measurable fun x ↦ sin (f x) := measurable_sin.comp hf

@[fun_prop]
/-
**Measurable.cosh** 是 Mathlib 中的一个定理，位于命名空间 `Measurable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {f : α → ℝ}, Measurable f → Measu
rable fun x => Real.cosh (f x)
参数：f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `Real.measurable_cosh`：measurable_cosh : Measurable cosh
-/
protected theorem Measurable.cosh : Measurable fun x ↦ cosh (f x) := measurable_cosh.comp hf

@[fun_prop]
/-
**Measurable.sinh** 是 Mathlib 中的一个定理，位于命名空间 `Measurable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {f : α → ℝ}, Measurable f → Measu
rable fun x => Real.sinh (f x)
参数：f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `Real.measurable_sinh`：measurable_sinh : Measurable sinh
-/
protected theorem Measurable.sinh : Measurable fun x ↦ sinh (f x) := measurable_sinh.comp hf

@[fun_prop]
/-
**Measurable.sqrt** 是 Mathlib 中的一个定理，位于命名空间 `Measurable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {f : α → ℝ}, Measurable f → Measu
rable fun x => √(f x)
参数：f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Real.continuous_sqrt`：continuous_sqrt : Continuous (√· : Real -> Real)
-/
protected theorem Measurable.sqrt : Measurable fun x => √(f x) := continuous_sqrt.measurable.comp hf

end RealComposition

section RealComposition

open Real

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {f : α → ℝ} (hf : AEMeasurable f μ)
include hf

@[fun_prop]
/-
**AEMeasurable.exp** 是 Mathlib 中的一个定理，位于命名空间 `AEMeasurable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f 
: α → ℝ},   AEMeasurable f μ → AEMeasurable (fun x => Real.exp (f x)) μ
参数：fun x => Real.exp (f x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `Real.measurable_exp`：measurable_exp : Measurable exp
-/
protected lemma AEMeasurable.exp : AEMeasurable (fun x ↦ exp (f x)) μ :=
  measurable_exp.comp_aemeasurable hf

@[fun_prop]
/-
**AEMeasurable.log** 是 Mathlib 中的一个定理，位于命名空间 `AEMeasurable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f 
: α → ℝ},   AEMeasurable f μ → AEMeasurable (fun x => Real.log (f x)) μ
参数：fun x => Real.log (f x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `Real.measurable_log`：measurable_log : Measurable log
-/
protected lemma AEMeasurable.log : AEMeasurable (fun x ↦ log (f x)) μ :=
  measurable_log.comp_aemeasurable hf

@[fun_prop]
/-
**AEMeasurable.cos** 是 Mathlib 中的一个定理，位于命名空间 `AEMeasurable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f 
: α → ℝ},   AEMeasurable f μ → AEMeasurable (fun x => Real.cos (f x)) μ
参数：fun x => Real.cos (f x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `Real.measurable_cos`：measurable_cos : Measurable cos
-/
protected lemma AEMeasurable.cos : AEMeasurable (fun x ↦ cos (f x)) μ :=
  measurable_cos.comp_aemeasurable hf

@[fun_prop]
/-
**AEMeasurable.sin** 是 Mathlib 中的一个定理，位于命名空间 `AEMeasurable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f 
: α → ℝ},   AEMeasurable f μ → AEMeasurable (fun x => Real.sin (f x)) μ
参数：fun x => Real.sin (f x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `Real.measurable_sin`：measurable_sin : Measurable sin
-/
protected lemma AEMeasurable.sin : AEMeasurable (fun x ↦ sin (f x)) μ :=
  measurable_sin.comp_aemeasurable hf

@[fun_prop]
/-
**AEMeasurable.cosh** 是 Mathlib 中的一个定理，位于命名空间 `AEMeasurable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f 
: α → ℝ},   AEMeasurable f μ → AEMeasurable (fun x => Real.cosh (f x)) μ
参数：fun x => Real.cosh (f x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `Real.measurable_cosh`：measurable_cosh : Measurable cosh
-/
protected lemma AEMeasurable.cosh : AEMeasurable (fun x ↦ cosh (f x)) μ :=
  measurable_cosh.comp_aemeasurable hf

@[fun_prop]
/-
**AEMeasurable.sinh** 是 Mathlib 中的一个定理，位于命名空间 `AEMeasurable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f 
: α → ℝ},   AEMeasurable f μ → AEMeasurable (fun x => Real.sinh (f x)) μ
参数：fun x => Real.sinh (f x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `Real.measurable_sinh`：measurable_sinh : Measurable sinh
-/
protected lemma AEMeasurable.sinh : AEMeasurable (fun x ↦ sinh (f x)) μ :=
  measurable_sinh.comp_aemeasurable hf

@[fun_prop]
/-
**AEMeasurable.sqrt** 是 Mathlib 中的一个定理，位于命名空间 `AEMeasurable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f 
: α → ℝ},   AEMeasurable f μ → AEMeasurable (fun x => √(f x)) μ
参数：fun x => √(f x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Real.continuous_sqrt`：continuous_sqrt : Continuous (√· : Real -> Real)
-/
protected lemma AEMeasurable.sqrt : AEMeasurable (fun x ↦ √(f x)) μ :=
  continuous_sqrt.measurable.comp_aemeasurable hf

end RealComposition

section ComplexComposition

open Complex

variable {α : Type*} {m : MeasurableSpace α} {f : α → ℂ} (hf : Measurable f)
include hf

@[fun_prop]
/-
**Measurable.cexp** 是 Mathlib 中的一个定理，位于命名空间 `Measurable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {f : α → ℂ}, Measurable f → Measu
rable fun x => Complex.exp (f x)
参数：f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `Complex.measurable_exp`：measurable_exp : Measurable exp
-/
protected theorem Measurable.cexp : Measurable fun x => Complex.exp (f x) :=
  Complex.measurable_exp.comp hf

@[fun_prop]
/-
**Measurable.ccos** 是 Mathlib 中的一个定理，位于命名空间 `Measurable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {f : α → ℂ}, Measurable f → Measu
rable fun x => Complex.cos (f x)
参数：f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `Complex.measurable_cos`：measurable_cos : Measurable cos
-/
protected theorem Measurable.ccos : Measurable fun x => Complex.cos (f x) :=
  Complex.measurable_cos.comp hf

@[fun_prop]
/-
**Measurable.csin** 是 Mathlib 中的一个定理，位于命名空间 `Measurable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {f : α → ℂ}, Measurable f → Measu
rable fun x => Complex.sin (f x)
参数：f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `Complex.measurable_sin`：measurable_sin : Measurable sin
-/
protected theorem Measurable.csin : Measurable fun x => Complex.sin (f x) :=
  Complex.measurable_sin.comp hf

@[fun_prop]
/-
**Measurable.ccosh** 是 Mathlib 中的一个定理，位于命名空间 `Measurable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {f : α → ℂ}, Measurable f → Measu
rable fun x => Complex.cosh (f x)
参数：f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `Complex.measurable_cosh`：measurable_cosh : Measurable cosh
-/
protected theorem Measurable.ccosh : Measurable fun x => Complex.cosh (f x) :=
  Complex.measurable_cosh.comp hf

@[fun_prop]
/-
**Measurable.csinh** 是 Mathlib 中的一个定理，位于命名空间 `Measurable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {f : α → ℂ}, Measurable f → Measu
rable fun x => Complex.sinh (f x)
参数：f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `Complex.measurable_sinh`：measurable_sinh : Measurable sinh
-/
protected theorem Measurable.csinh : Measurable fun x => Complex.sinh (f x) :=
  Complex.measurable_sinh.comp hf

@[fun_prop]
/-
**Measurable.carg** 是 Mathlib 中的一个定理，位于命名空间 `Measurable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {f : α → ℂ}, Measurable f → Measu
rable fun x => (f x).arg
参数：f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `Complex.measurable_arg`：measurable_arg : Measurable arg
-/
protected theorem Measurable.carg : Measurable fun x => arg (f x) :=
  measurable_arg.comp hf

@[fun_prop]
/-
**Measurable.clog** 是 Mathlib 中的一个定理，位于命名空间 `Measurable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {f : α → ℂ}, Measurable f → Measu
rable fun x => Complex.log (f x)
参数：f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `Complex.measurable_log`：measurable_log : Measurable log
-/
protected theorem Measurable.clog : Measurable fun x => Complex.log (f x) :=
  measurable_log.comp hf

end ComplexComposition

section ComplexComposition

open Complex

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {f : α → ℂ} (hf : AEMeasurable f μ)
include hf

@[fun_prop]
/-
**AEMeasurable.cexp** 是 Mathlib 中的一个定理，位于命名空间 `AEMeasurable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f 
: α → ℂ},   AEMeasurable f μ → AEMeasurable (fun x => Complex.exp (f x)) μ
参数：fun x => Complex.exp (f x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `Complex.measurable_exp`：measurable_exp : Measurable exp
-/
protected lemma AEMeasurable.cexp : AEMeasurable (fun x ↦ exp (f x)) μ :=
  measurable_exp.comp_aemeasurable hf

@[fun_prop]
/-
**AEMeasurable.ccos** 是 Mathlib 中的一个定理，位于命名空间 `AEMeasurable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f 
: α → ℂ},   AEMeasurable f μ → AEMeasurable (fun x => Complex.cos (f x)) μ
参数：fun x => Complex.cos (f x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `Complex.measurable_cos`：measurable_cos : Measurable cos
-/
protected lemma AEMeasurable.ccos : AEMeasurable (fun x ↦ cos (f x)) μ :=
  measurable_cos.comp_aemeasurable hf

@[fun_prop]
/-
**AEMeasurable.csin** 是 Mathlib 中的一个定理，位于命名空间 `AEMeasurable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f 
: α → ℂ},   AEMeasurable f μ → AEMeasurable (fun x => Complex.sin (f x)) μ
参数：fun x => Complex.sin (f x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `Complex.measurable_sin`：measurable_sin : Measurable sin
-/
protected lemma AEMeasurable.csin : AEMeasurable (fun x ↦ sin (f x)) μ :=
  measurable_sin.comp_aemeasurable hf

@[fun_prop]
/-
**AEMeasurable.ccosh** 是 Mathlib 中的一个定理，位于命名空间 `AEMeasurable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f 
: α → ℂ},   AEMeasurable f μ → AEMeasurable (fun x => Complex.cosh (f x)) μ
参数：fun x => Complex.cosh (f x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `Complex.measurable_cosh`：measurable_cosh : Measurable cosh
-/
protected lemma AEMeasurable.ccosh : AEMeasurable (fun x ↦ cosh (f x)) μ :=
  measurable_cosh.comp_aemeasurable hf

@[fun_prop]
/-
**AEMeasurable.csinh** 是 Mathlib 中的一个定理，位于命名空间 `AEMeasurable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f 
: α → ℂ},   AEMeasurable f μ → AEMeasurable (fun x => Complex.sinh (f x)) μ
参数：fun x => Complex.sinh (f x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `Complex.measurable_sinh`：measurable_sinh : Measurable sinh
-/
protected lemma AEMeasurable.csinh : AEMeasurable (fun x ↦ sinh (f x)) μ :=
  measurable_sinh.comp_aemeasurable hf

@[fun_prop]
/-
**AEMeasurable.carg** 是 Mathlib 中的一个定理，位于命名空间 `AEMeasurable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f 
: α → ℂ},   AEMeasurable f μ → AEMeasurable (fun x => (f x).arg) μ
参数：fun x => (f x).arg。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `Complex.measurable_arg`：measurable_arg : Measurable arg
-/
protected lemma AEMeasurable.carg : AEMeasurable (fun x ↦ arg (f x)) μ :=
  measurable_arg.comp_aemeasurable hf

@[fun_prop]
/-
**AEMeasurable.clog** 是 Mathlib 中的一个定理，位于命名空间 `AEMeasurable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f 
: α → ℂ},   AEMeasurable f μ → AEMeasurable (fun x => Complex.log (f x)) μ
参数：fun x => Complex.log (f x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `Complex.measurable_log`：measurable_log : Measurable log
-/
protected lemma AEMeasurable.clog : AEMeasurable (fun x ↦ log (f x)) μ :=
  measurable_log.comp_aemeasurable hf

end ComplexComposition

@[fun_prop]
/-
**Measurable.complex_ofReal** 是 Mathlib 中的一个定理，位于命名空间 `Measurable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {f : α → ℝ}, Measurable f → Measu
rable fun x => ↑(f x)
参数：f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
-/
protected theorem Measurable.complex_ofReal {α : Type*} {m : MeasurableSpace α} {f : α → ℝ}
    (hf : Measurable f) :
    Measurable fun x ↦ (f x : ℂ) := by fun_prop

@[fun_prop]
/-
**AEMeasurable.complex_ofReal** 是 Mathlib 中的一个定理，位于命名空间 `AEMeasurable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f 
: α → ℝ},   AEMeasurable f μ → AEMeasurable (fun x => ↑(f x)) μ
参数：fun x => ↑(f x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp_aemeasurable'`：Measurable.comp_aemeasurable' [Measurable
Space δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) :
 AEMeasurable (fun …
· 使用定理 `Measurable.complex_ofReal`：∀ {α : Type u_1} {m : MeasurableSpace α} {f :
 α → ℝ}, Measurable f → Measurable fun x => ↑(f x)
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
-/
protected theorem AEMeasurable.complex_ofReal {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {f : α → ℝ} (hf : AEMeasurable f μ) :
    AEMeasurable (fun x ↦ (f x : ℂ)) μ := by
  fun_prop

section PowInstances

/-
**Complex.hasMeasurablePow** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Complex.hasMeasurablePow : MeasurablePow Complex Complex
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.ite`：Measurable.ite {p : α -> Prop} {_ : DecidablePred p} (hp
 : MeasurableSet { a : α | p a }) (hf : Measurable f) (hg : Measurable g) : Meas
urab…
· 使用引理 `Measurable.eq_const`：Measurable.eq_const {_ : MeasurableSpace α} [Measur
ableSpace β] [MeasurableSingletonClass β] {f : α -> β} (hf : Measurable f) (a : 
β) : Meas…
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `instMeasurableEqOfSecondCountableTopologyOfT2Space`：∀ {α : Type u_1} [in
st : TopologicalSpace α] [inst_1 : MeasurableSpace α] [OpensMeasurableSpace α]  
 [SecondCountableTopology α] [T2Space α]…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `Measurable.fst`：Measurable.fst {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).1
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `Measurable.snd`：Measurable.snd {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).2
· 使用定理 `measurable_one`：measurable_one [One α] : Measurable (1 : β -> α)
· 使用定理 `measurable_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace
 α] [inst_1 : MeasurableSpace β] [inst_2 : Zero α], Measurable 0
· 使用定理 `Measurable.cexp`：∀ {α : Type u_1} {m : MeasurableSpace α} {f : α → ℂ}, M
easurable f → Measurable fun x => Complex.exp (f x)
· 使用定理 `Measurable.fun_mul`：∀ {M : Type u_2} {α : Type u_3} [inst : MeasurableSp
ace M] [inst_1 : Mul M] {m : MeasurableSpace α} {f g : α → M}   [MeasurableMul₂ 
M], Meas…
· 使用定理 `ContinuousMul.measurableMul₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Mul γ] [Con…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Measurable.clog`：∀ {α : Type u_1} {m : MeasurableSpace α} {f : α → ℂ}, M
easurable f → Measurable fun x => Complex.log (f x)
-/
instance Complex.hasMeasurablePow : MeasurablePow ℂ ℂ :=
  ⟨Measurable.ite (by measurability)
    (Measurable.ite (by measurability) measurable_one measurable_zero) (by fun_prop)⟩
/-
**Real.hasMeasurablePow** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Real.hasMeasurablePow : MeasurablePow Real Real
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `Complex.measurable_re`：measurable_re : Measurable re
· 使用定理 `Measurable.pow`：Measurable.pow (hf : Measurable f) (hg : Measurable g) :
 Measurable fun x => f x ^ g x
· 使用定理 `Measurable.complex_ofReal`：∀ {α : Type u_1} {m : MeasurableSpace α} {f :
 α → ℝ}, Measurable f → Measurable fun x => ↑(f x)
· 使用定理 `Measurable.fst`：Measurable.fst {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).1
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `Measurable.snd`：Measurable.snd {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).2
-/
instance Real.hasMeasurablePow : MeasurablePow ℝ ℝ := ⟨Complex.measurable_re.comp <| by fun_prop⟩
/-
**NNReal.hasMeasurablePow** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：NNReal.hasMeasurablePow : MeasurablePow Real>=0 Real
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.subtype_mk`：Measurable.subtype_mk {p : β -> Prop} {f : α -> β
} (hf : Measurable f) {h : forall x, p (f x)} : Measurable fun x => (⟨f x, h x⟩ 
: Subtype p…
· 使用定理 `Measurable.pow`：Measurable.pow (hf : Measurable f) (hg : Measurable g) :
 Measurable fun x => f x ^ g x
· 使用定理 `Measurable.coe_nnreal_real`：Measurable.coe_nnreal_real {f : α -> Real>=0
} (hf : Measurable f) : Measurable fun x => (f x : Real)
· 使用定理 `Measurable.fst`：Measurable.fst {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).1
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `Measurable.snd`：Measurable.snd {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).2
-/
instance NNReal.hasMeasurablePow : MeasurablePow ℝ≥0 ℝ := ⟨Measurable.subtype_mk (by fun_prop)⟩
/-
**ENNReal.hasMeasurablePow** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ENNReal.hasMeasurablePow : MeasurablePow Real>=0∞ Real
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.measurable_of_measurable_nnreal_prod`：measurable_of_measurable_n
nreal_prod {_ : MeasurableSpace β} {_ : MeasurableSpace γ} {f : Real>=0∞ × β -> 
γ} (H₁ : Measurable fun p : Real>=…
· 使用定理 `Measurable.ite`：Measurable.ite {p : α -> Prop} {_ : DecidablePred p} (hp
 : MeasurableSet { a : α | p a }) (hf : Measurable f) (hg : Measurable g) : Meas
urab…
· 使用引理 `Measurable.and`：Measurable.and (hp : Measurable p) (hq : Measurable q) :
 Measurable fun a => p a ∧ q a
· 使用引理 `Measurable.eq_const`：Measurable.eq_const {_ : MeasurableSpace α} [Measur
ableSpace β] [MeasurableSingletonClass β] {f : α -> β} (hf : Measurable f) (a : 
β) : Meas…
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `instMeasurableEqOfSecondCountableTopologyOfT2Space`：∀ {α : Type u_1} [in
st : TopologicalSpace α] [inst_1 : MeasurableSpace α] [OpensMeasurableSpace α]  
 [SecondCountableTopology α] [T2Space α]…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `NNReal.instSecondCountableTopology`：SecondCountableTopology NNReal
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Measurable.fst`：Measurable.fst {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).1
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
· 使用定理 `measurable_lt`：measurable_lt [SecondCountableTopology α] [OrderClosedTop
ology α] : Measurable fun p : α × α => p.1 < p.2
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `Measurable.snd`：Measurable.snd {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).2
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `Measurable.coe_nnreal_ennreal`：Measurable.coe_nnreal_ennreal {f : α -> R
eal>=0} (hf : Measurable f) : Measurable fun x => (f x : Real>=0∞)
· 使用定理 `Measurable.pow`：Measurable.pow (hf : Measurable f) (hg : Measurable g) :
 Measurable fun x => f x ^ g x
· 使用定理 `measurableSet_Ioi`：measurableSet_Ioi [ClosedIicTopology α] : MeasurableS
et (Ioi a)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `MeasurableSingletonClass.measurableSet_singleton`：∀ {α : Type u_7} {inst
 : MeasurableSpace α} [self : MeasurableSingletonClass α] (x : α), MeasurableSet
 {x}
-/
instance ENNReal.hasMeasurablePow : MeasurablePow ℝ≥0∞ ℝ := by
  refine ⟨ENNReal.measurable_of_measurable_nnreal_prod ?_ ?_⟩
  · simp_rw [ENNReal.coe_rpow_def]
    exact Measurable.ite (by measurability) measurable_const (by fun_prop)
  · simp_rw [ENNReal.top_rpow_def]
    refine Measurable.ite measurableSet_Ioi measurable_const ?_
    exact Measurable.ite (measurableSet_singleton 0) measurable_const measurable_const

end PowInstances

