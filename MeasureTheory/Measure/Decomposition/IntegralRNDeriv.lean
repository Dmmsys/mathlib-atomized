/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

import Mathlib.Analysis.Convex.Approximation
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.RadonNikodym

/-!
# Integrals of functions of Radon-Nikodym derivatives

## Main statements

* `mul_le_integral_rnDeriv_of_ac`: for a convex continuous function `f` on `[0, ∞)`, if `μ`
  is absolutely continuous with respect to `ν`, then
  `ν.real univ * f (μ.real univ / ν.real univ) ≤ ∫ x, f (μ.rnDeriv ν x).toReal ∂ν`.
* `ConvexOn.integrable_apply_rnDeriv_of_integrable_compProd`: for `f` a convex function on `[0, ∞)`,
  if `f ((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) (a, b))` is integrable, then `f (μ.rnDeriv ν a)` is integrable.

-/

public section


open Set ProbabilityTheory
open scoped ENNReal

namespace MeasureTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {μ ν : Measure 𝓧} {f : ℝ → ℝ}

@[fun_prop]
/-
**MeasureTheory.Measure.integrable_toReal_rnDeriv** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.Measure`。
形式化陈述：∀ {𝓧 : Type u_1} {m𝓧 : MeasurableSpace 𝓧} {μ ν : MeasureTheory.Measure 𝓧} 
[MeasureTheory.IsFiniteMeasure μ],   MeasureTheory.Integrable (fun x => (μ.rnDer
iv ν x).toReal) ν
参数：fun x => (μ.rnDeriv ν x).toReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integrable_toReal_of_lintegral_ne_top`：integrable_toReal_o
f_lintegral_ne_top {f : α -> Real>=0∞} (hfm : AEMeasurable f μ) (hfi : ∫⁻ x, f x
 ∂μ != ∞) : Integrable (fun x => (f x).to…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.Measure.lintegral_rnDeriv_lt_top`：lintegral_rnDeriv_lt_top
 (μ ν : Measure α) [IsFiniteMeasure μ] : ∫⁻ x, μ.rnDeriv ν x ∂ν < ∞
-/
lemma Measure.integrable_toReal_rnDeriv [IsFiniteMeasure μ] :
    Integrable (fun x ↦ (μ.rnDeriv ν x).toReal) ν :=
  integrable_toReal_of_lintegral_ne_top (Measure.measurable_rnDeriv _ _).aemeasurable
    (Measure.lintegral_rnDeriv_lt_top _ _).ne

/-- For a convex continuous function `f` on `[0, ∞)`, if `μ` is absolutely continuous
with respect to a probability measure `ν`, then
`f μ.real univ ≤ ∫ x, f (μ.rnDeriv ν x).toReal ∂ν`. -/
/-
**MeasureTheory.le_integral_rnDeriv_of_ac** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：le_integral_rnDeriv_of_ac [IsFiniteMeasure μ] [IsProbabilityMeasure ν] (hf
_cvx : ConvexOn Real (Ici 0) f) (hf_cont : ContinuousWithinAt f (Ici 0) 0) (hf_i
nt : Integrable (fun x => f (μ.rnDeriv ν x).toReal) ν) (hμν : μ ≪ ν) : f (μ.real
 univ) <= ∫ x, f (μ.rnDeriv ν x).toReal ∂ν
参数：hf_cvx : ConvexOn Real (Ici 0) f；hf_cont : ContinuousWithinAt f (Ici 0) 0；hf_
int : Integrable (fun x => f (μ.rnDeriv ν x).toReal) ν；hμν : μ ≪ ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ConvexOn.continuousOn_Ici`：ConvexOn.continuousOn_Ici {f : Real -> Real} 
{y : Real} (hf_cvx : ConvexOn Real (Ici y) f) (hf_cont : ContinuousWithinAt f (I
ci y) y) : Cont…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.integral_toReal_rnDeriv`：integral_toReal_rnDeriv [
SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) : ∫ x, (μ.rnDeriv ν x).toReal ∂ν = 
μ.real Set.univ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.average_eq_integral`：average_eq_integral [IsProbabilityMea
sure μ] (f : α -> E) : ⨍ x, f x ∂μ = ∫ x, f x ∂μ
· 使用定理 `ConvexOn.map_average_le`：ConvexOn.map_average_le [IsFiniteMeasure μ] [Ne
Zero μ] (hg : ConvexOn Real s g) (hgc : ContinuousOn g s) (hsc : IsClosed s) (hf
s : forallᵐ x…
· 使用定理 `MeasureTheory.IsProbabilityMeasure.neZero`：∀ {α : Type u_1} {m0 : Measur
ableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ
], NeZero μ
· 使用定理 `isClosed_Ici`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Preor
der α] [ClosedIciTopology α] {a : α}, IsClosed (Set.Ici a)
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.Measure.integrable_toReal_rnDeriv`：∀ {𝓧 : Type u_1} {m𝓧 : 
MeasurableSpace 𝓧} {μ ν : MeasureTheory.Measure 𝓧} [MeasureTheory.IsFiniteMeasur
e μ],   MeasureTheory.Integrable (fun…

--- 原说明 ---
For a convex continuous function `f` on `[0, ∞)`, if `μ` is absolutely continuou
s
with respect to a probability measure `ν`, then
`f μ.real univ ≤ ∫ x, f (μ.rnDeriv ν x).toReal ∂ν`.
-/
lemma le_integral_rnDeriv_of_ac [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousWithinAt f (Ici 0) 0)
    (hf_int : Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν) (hμν : μ ≪ ν) :
    f (μ.real univ) ≤ ∫ x, f (μ.rnDeriv ν x).toReal ∂ν := by
  have hf_cont' : ContinuousOn f (Ici 0) := hf_cvx.continuousOn_Ici hf_cont
  calc f (μ.real univ)
    = f (∫ x, (μ.rnDeriv ν x).toReal ∂ν) := by rw [Measure.integral_toReal_rnDeriv hμν]
  _ ≤ ∫ x, f (μ.rnDeriv ν x).toReal ∂ν := by
    rw [← average_eq_integral, ← average_eq_integral]
    exact ConvexOn.map_average_le hf_cvx hf_cont' isClosed_Ici (by simp)
      Measure.integrable_toReal_rnDeriv hf_int

/-- For a convex continuous function `f` on `[0, ∞)`, if `μ` is absolutely continuous
with respect to `ν`, then
`ν.real univ * f (μ.real univ / ν.real univ) ≤ ∫ x, f (μ.rnDeriv ν x).toReal ∂ν`. -/
/-
**MeasureTheory.mul_le_integral_rnDeriv_of_ac** 是 Mathlib 中的一个引理，位于命名空间 `Measure
Theory`。
形式化陈述：mul_le_integral_rnDeriv_of_ac [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hf_
cvx : ConvexOn Real (Ici 0) f) (hf_cont : ContinuousWithinAt f (Ici 0) 0) (hf_in
t : Integrable (fun x => f (μ.rnDeriv ν x).toReal) ν) (hμν : μ ≪ ν) : ν.real uni
v * f (μ.real univ / ν.real univ) <= ∫ x, f (μ.rnDeriv ν x).toReal ∂ν
参数：hf_cvx : ConvexOn Real (Ici 0) f；hf_cont : ContinuousWithinAt f (Ici 0) 0；hf_
int : Integrable (fun x => f (μ.rnDeriv ν x).toReal) ν；hμν : μ ≪ ν。
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
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_zero_measure`：integral_zero_measure {m : Measurab
leSpace α} (f : α -> G) : (∫ x, f x ∂(0 : Measure α)) = 0
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.smul_finite`：∀ {α : Type u_1} {m0 : MeasurableSpac
e α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ] {c : ENNRea
l},   c ≠ ⊤ → MeasureTh…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.smul`：∀ {α : Type u_1} {R : T
ype u_5} {mα : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [inst : SMul R
 ENNReal]   [inst_1 : IsScalarTower R…
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.rnDeriv_smul_left_of_ne_top'`：rnDeriv_smul_left_of
_ne_top' (ν μ : Measure α) [SigmaFinite ν] [SigmaFinite μ] {r : Real>=0∞} (hr : 
r != ∞) : (r • ν).rnDeriv μ =ᵐ[μ] r • ν.…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.average`：∀ {α : Type u_1} {m0 : Measurable
Space α} {μ : MeasureTheory.Measure α},   MeasureTheory.IsFiniteMeasure ((μ Set.
univ)⁻¹ • μ)
· 使用定理 `MeasureTheory.Measure.ae_ennreal_smul_measure_eq`：∀ {α : Type u_1} {m0 :
 MeasurableSpace α} {c : ENNReal},   c ≠ 0 → ∀ (μ : MeasureTheory.Measure α), Me
asureTheory.ae (c • μ) = MeasureTheory…
· 使用定理 `MeasureTheory.Measure.rnDeriv_smul_right_of_ne_top'`：rnDeriv_smul_right_
of_ne_top' (ν μ : Measure α) [SigmaFinite ν] [SigmaFinite μ] {r : Real>=0∞} (hr 
: r != 0) (hr_ne_top : r != ∞) : ν.rnDeri…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Pi.smul_apply`：∀ {ι : Type u_1} {α : Type u_2} {M : ι → Type u_5} [inst 
: (i : ι) → SMul α (M i)] (a : α) (f : (i : ι) → M i) (i : ι),   (a • f) i = a •
 f …
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `ENNReal.inv_mul_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a⁻¹ * a = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MeasureTheory.integral_smul_measure`：integral_smul_measure (f : α -> G) 
(c : Real>=0∞) : ∫ x, f x ∂c • μ = c.toReal • ∫ x, f x ∂μ
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
For a convex continuous function `f` on `[0, ∞)`, if `μ` is absolutely continuou
s
with respect to `ν`, then
`ν.real univ * f (μ.real univ / ν.real univ) ≤ ∫ x, f (μ.rnDeriv ν x).toReal ∂ν`
.
-/
lemma mul_le_integral_rnDeriv_of_ac [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousWithinAt f (Ici 0) 0)
    (hf_int : Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν) (hμν : μ ≪ ν) :
    ν.real univ * f (μ.real univ / ν.real univ)
      ≤ ∫ x, f (μ.rnDeriv ν x).toReal ∂ν := by
  by_cases hν : ν = 0
  · simp [hν]
  have : NeZero ν := ⟨hν⟩
  let μ' := (ν univ)⁻¹ • μ
  let ν' := (ν univ)⁻¹ • ν
  have : IsFiniteMeasure μ' := μ.smul_finite (by simp [hν])
  have hμν' : μ' ≪ ν' := hμν.smul _
  have h_rnDeriv_eq : μ'.rnDeriv ν' =ᵐ[ν] μ.rnDeriv ν := by
    have h1' : μ'.rnDeriv ν' =ᵐ[ν'] (ν univ)⁻¹ • μ.rnDeriv ν' :=
      Measure.rnDeriv_smul_left_of_ne_top' (μ := ν') (ν := μ) (by simp [hν])
    have h1 : μ'.rnDeriv ν' =ᵐ[ν] (ν univ)⁻¹ • μ.rnDeriv ν' := by
      rwa [Measure.ae_ennreal_smul_measure_eq] at h1'
      simp
    have h2 : μ.rnDeriv ν' =ᵐ[ν] (ν univ)⁻¹⁻¹ • μ.rnDeriv ν :=
      Measure.rnDeriv_smul_right_of_ne_top' (μ := ν) (ν := μ) (by simp) (by simp [hν])
    filter_upwards [h1, h2] with x h1 h2
    rw [h1, Pi.smul_apply, smul_eq_mul, h2]
    simp only [inv_inv, Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, ENNReal.inv_mul_cancel, one_mul]
    · simp [hν]
    · simp
  have h_eq : ∫ x, f (μ'.rnDeriv ν' x).toReal ∂ν'
      = (ν.real univ)⁻¹ * ∫ x, f ((μ.rnDeriv ν x).toReal) ∂ν := by
    rw [integral_smul_measure, smul_eq_mul, ENNReal.toReal_inv]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [h_rnDeriv_eq] with x hx
    rw [hx]
  have h : f (μ'.real univ) ≤ ∫ x, f (μ'.rnDeriv ν' x).toReal ∂ν' :=
    le_integral_rnDeriv_of_ac hf_cvx hf_cont ?_ hμν'
  swap
  · refine Integrable.smul_measure ?_ (by simp [hν])
    refine (integrable_congr ?_).mpr hf_int
    filter_upwards [h_rnDeriv_eq] with x hx
    rw [hx]
  rw [h_eq, mul_comm, ← div_le_iff₀, div_eq_inv_mul, inv_inv] at h
  · convert! h
    · simp only [div_eq_inv_mul, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
      ENNReal.toReal_inv, μ', measureReal_def]
  · simp [ENNReal.toReal_pos_iff, hν, measureReal_def]

section Integrable

variable {𝓨 : Type*} {m𝓨 : MeasurableSpace 𝓨} {κ η : Kernel 𝓧 𝓨} {f : ℝ → ℝ}
  [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-
**MeasureTheory.lintegral_rnDeriv_compProd** 是 Mathlib 中的一个引理，位于命名空间 `MeasureThe
ory`。
形式化陈述：lintegral_rnDeriv_compProd [IsSFiniteKernel κ] [IsFiniteKernel η] (hκη : μ
 otimesₘ κ ≪ μ otimesₘ η) : forallᵐ a ∂μ, ∫⁻ b, (μ otimesₘ κ).rnDeriv (μ otimesₘ
 η) (a, b) ∂η a = κ a univ
参数：hκη : μ otimesₘ κ ≪ μ otimesₘ η。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite`：ae_eq_of_f
orall_setLIntegral_eq_of_sigmaFinite [SigmaFinite μ] {f g : α -> Real>=0∞} (hf :
 Measurable f) (hg : Measurable g) (h : forall s, …
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `Measurable.lintegral_kernel_prod_left`：∀ {α : Type u_1} {β : Type u_2} {
mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kernel α
 β}   [ProbabilityTheory.Is…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `Measurable.snd`：Measurable.snd {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).2
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `Measurable.fst`：Measurable.fst {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).1
· 使用定理 `ProbabilityTheory.Kernel.measurable_coe`：∀ {α : Type u_1} {β : Type u_2}
 {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (κ : ProbabilityTheory.Kernel
 α β)   {s : Set β}, Measurab…
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.setLIntegral_compProd`：setLIntegral_compProd [SFin
ite μ] [IsSFiniteKernel κ] {f : α × β -> Real>=0∞} (hf : Measurable f) {s : Set 
α} (hs : MeasurableSet s) {t : Se…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用引理 `MeasureTheory.Measure.setLIntegral_rnDeriv`：setLIntegral_rnDeriv [HaveLe
besgueDecomposition μ ν] [SFinite ν] (hμν : μ ≪ ν) (s : Set α) : ∫⁻ x in s, μ.rn
Deriv ν x ∂ν = μ s
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `MeasureTheory.Measure.instSFiniteProdCompProd`：∀ {α : Type u_1} {β : Typ
e u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : MeasureTheory.Meas
ure α}   {κ : ProbabilityTheory.Ker…
· 使用定理 `MeasureTheory.Measure.instIsFiniteMeasureProdCompProdOfIsFiniteKernel`：∀
 {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
 {μ : MeasureTheory.Measure α}   {κ : ProbabilityTheory.Ker…
· 使用引理 `MeasureTheory.Measure.compProd_apply_prod`：compProd_apply_prod [SFinite 
μ] [IsSFiniteKernel κ] {s : Set α} {t : Set β} (hs : MeasurableSet s) (ht : Meas
urableSet t) : (μ otimesₘ κ) (s…
-/
lemma lintegral_rnDeriv_compProd [IsSFiniteKernel κ] [IsFiniteKernel η]
    (hκη : μ ⊗ₘ κ ≪ μ ⊗ₘ η) :
    ∀ᵐ a ∂μ, ∫⁻ b, (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) (a, b) ∂η a = κ a univ := by
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite (by fun_prop) (κ.measurable_coe .univ) ?_
  intro s hs hsμ
  calc ∫⁻ a in s, ∫⁻ b, (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) (a, b) ∂(η a) ∂μ
  _ = ∫⁻ a in s, ∫⁻ b in univ, (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) (a, b) ∂(η a) ∂μ := by simp
  _ = ∫⁻ a in s, (κ a) univ ∂μ := by
    rw [← Measure.setLIntegral_compProd (by fun_prop) hs .univ, Measure.setLIntegral_rnDeriv hκη,
      Measure.compProd_apply_prod hs .univ]

variable [IsMarkovKernel κ] [IsMarkovKernel η]

/-- The value of a convex function applied at a Radon-Nikodym derivative can be bounded by the
integral of the function applied to the Radon-Nikodym derivative of composition-products. -/
/-
**MeasureTheory._root_.ConvexOn.apply_rnDeriv_ae_le_integral** 是 Mathlib 中的一个引理，
位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The value of a convex function applied at a Radon-Nikodym derivative can be boun
ded by the
integral of the function applied to the Radon-Nikodym derivative of composition-
products.
-/
lemma _root_.ConvexOn.apply_rnDeriv_ae_le_integral (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont_at : ContinuousWithinAt f (Ici 0) 0)
    (h_int : Integrable (fun p ↦ f ((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) p).toReal) (ν ⊗ₘ η))
    (hκη : μ ⊗ₘ κ ≪ μ ⊗ₘ η) :
    (fun a ↦ f (μ.rnDeriv ν a).toReal)
      ≤ᵐ[ν] fun a ↦ ∫ b, f ((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) (a, b)).toReal ∂(η a) := by
  have hf_cont : ContinuousOn f (Ici 0) := hf_cvx.continuousOn_Ici hf_cont_at
  have h_lt_top : ∀ᵐ a ∂ν, ∀ᵐ b ∂η a, (μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) (a, b) < ∞ :=
    Measure.ae_ae_of_ae_compProd <| (μ ⊗ₘ κ).rnDeriv_lt_top (ν ⊗ₘ η)
  have h_integrable : Integrable (fun x ↦ ((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) x).toReal) (ν ⊗ₘ η) :=
    Measure.integrable_toReal_rnDeriv
  rw [Measure.integrable_compProd_iff] at h_integrable h_int
  rotate_left
  · exact StronglyMeasurable.aestronglyMeasurable (by fun_prop)
  · exact StronglyMeasurable.aestronglyMeasurable (by fun_prop)
  have h_ae1 : ∀ᵐ a ∂ν,
      μ.rnDeriv ν a * ∫⁻ b, (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) (a, b) ∂(η a) = μ.rnDeriv ν a := by
    filter_upwards [Measure.ae_rnDeriv_ne_zero_imp_of_ae _ (lintegral_rnDeriv_compProd hκη)]
      with a ha
    by_cases h0 : μ.rnDeriv ν a = 0
    · simp [h0]
    · simp [ha h0]
  have h_ae2 : ∀ᵐ a ∂ν, ∀ᵐ b ∂(η a), μ.rnDeriv ν a * (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) (a, b) =
      (μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) (a, b) := by
    have h_compProd : (fun p ↦ μ.rnDeriv ν p.1 * (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) p) =ᵐ[ν ⊗ₘ η]
        (μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) := (rnDeriv_compProd hκη ν).symm
    rwa [Filter.EventuallyEq, Measure.ae_compProd_iff] at h_compProd
    simp only [measurableSet_setOfPred]
    fun_prop
  filter_upwards [h_ae1, h_ae2, h_lt_top, h_integrable.1, h_int.1]
    with a h_eq_one h_mul_eq h_lt_top h_int' h_int
  calc f (μ.rnDeriv ν a).toReal
    = f (μ.rnDeriv ν a * ∫⁻ b, (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) (a, b) ∂(η a)).toReal := by simp [h_eq_one]
  _ = f (∫⁻ b, (μ.rnDeriv ν a) * (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) (a, b) ∂(η a)).toReal := by
    rw [lintegral_const_mul _ (by fun_prop)]
  _ = f (∫⁻ b, (μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) (a, b) ∂(η a)).toReal := by
    congr 2
    refine lintegral_congr_ae ?_
    filter_upwards [h_mul_eq] with b hb using hb
  _ = f (∫ b, ((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) (a, b)).toReal ∂(η a)) := by
    rw [integral_toReal (by fun_prop) h_lt_top]
  _ ≤ ∫ b, f ((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) (a, b)).toReal ∂(η a) := by
    rw [← average_eq_integral, ← average_eq_integral]
    exact ConvexOn.map_average_le hf_cvx hf_cont isClosed_Ici (by simp) h_int' h_int

/-- For `f` a convex function on `Ici 0`, if `f ((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) (a, b))` is integrable,
then `f (μ.rnDeriv ν a)` is integrable. -/
/-
**MeasureTheory._root_.ConvexOn.integrable_apply_rnDeriv_of_integrable_compProd*
* 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `f` a convex function on `Ici 0`, if `f ((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) (a, b))` 
is integrable,
then `f (μ.rnDeriv ν a)` is integrable.
-/
lemma _root_.ConvexOn.integrable_apply_rnDeriv_of_integrable_compProd (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont_at : ContinuousWithinAt f (Ici 0) 0)
    (hf_int : Integrable (fun p ↦ f ((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) p).toReal) (ν ⊗ₘ η))
    (hκη : μ ⊗ₘ κ ≪ μ ⊗ₘ η) :
    Integrable (fun a ↦ f (μ.rnDeriv ν a).toReal) ν := by
  have hf_cont : ContinuousOn f (Ici 0) := hf_cvx.continuousOn_Ici hf_cont_at
  obtain ⟨c, c', h⟩ : ∃ c c', ∀ x, 0 ≤ x → c * x + c' ≤ f x :=
    hf_cvx.exists_affine_le_real isClosed_Ici hf_cont.lowerSemicontinuousOn
  refine integrable_of_le_of_le (f := fun a ↦ f (μ.rnDeriv ν a).toReal)
    (g₁ := fun x ↦ c * (μ.rnDeriv ν x).toReal + c')
    (g₂ := fun x ↦ ∫ b, f ((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) (x, b)).toReal ∂(η x))
    ?_ ?_ ?_ (by fun_prop) ?_
  · exact StronglyMeasurable.aestronglyMeasurable (by fun_prop)
  · exact ae_of_all _ fun x ↦ h _ ENNReal.toReal_nonneg
  · exact hf_cvx.apply_rnDeriv_ae_le_integral hf hf_cont_at hf_int hκη
  · exact hf_int.integral_compProd

end Integrable

end MeasureTheory

