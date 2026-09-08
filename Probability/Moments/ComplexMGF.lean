/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul

/-!
# The complex-valued moment-generating function

The moment-generating function (mgf) is `t : ℝ ↦ μ[fun ω ↦ rexp (t * X ω)]`. It can be extended to
a complex function `z : ℂ ↦ μ[fun ω ↦ cexp (z * X ω)]`, which we call `complexMGF X μ`.
That function is holomorphic on the vertical strip with base the interior of the interval
of definition of the mgf.
On the vertical line that goes through 0, `complexMGF X μ` is equal to the characteristic function.
This allows us to link properties of the characteristic function and the mgf (mostly deducing
properties of the mgf from those of the characteristic function).

## Main definitions

* `complexMGF X μ`: the function `z : ℂ ↦ μ[fun ω ↦ cexp (z * X ω)]`.

## Main results

* `complexMGF_ofReal`: for `x : ℝ`, `complexMGF X μ x = mgf X μ x`.

* `hasDerivAt_complexMGF`: for all `z : ℂ` such that the real part `z.re` belongs to the interior
  of the interval of definition of the mgf, `complexMGF X μ` is differentiable at `z`
  with derivative `μ[X * exp (z * X)]`.
* `differentiableOn_complexMGF`: `complexMGF X μ` is holomorphic on the vertical strip
  `{z | z.re ∈ interior (integrableExpSet X μ)}`.
* `analyticOn_complexMGF`: `complexMGF X μ` is analytic on the vertical strip
  `{z | z.re ∈ interior (integrableExpSet X μ)}`.

* `eqOn_complexMGF_of_mgf`: if two random variables have the same moment-generating function,
  then they have the same `complexMGF` on the vertical strip
  `{z | z.re ∈ interior (integrableExpSet X μ)}`.
  Once we know that equal `mgf` implies equal distributions, we will be able to show that
  the `complexMGF` are equal everywhere, not only on the strip.
  This lemma will be used in the proof of the equality of distributions.

* `ext_of_complexMGF_eq`: If the complex moment-generating functions of two random variables `X`
  and `Y` with respect to the finite measures `μ`, `μ'`, respectively, coincide, then
  `μ.map X = μ'.map Y`. In other words, complex moment-generating functions separate the
  distributions of random variables.

## TODO

* Prove that if two random variables have the same `mgf`, then the have the same `complexMGF`.

-/

@[expose] public section


open MeasureTheory Filter Finset Real Complex

open scoped MeasureTheory ProbabilityTheory ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω ι : Type*} {m : MeasurableSpace Ω} {X : Ω → ℝ} {μ : Measure Ω} {t u v : ℝ} {z ε : ℂ}

/-- Complex extension of the moment-generating function. -/
noncomputable
/-
**ProbabilityTheory.complexMGF** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory`。
形式化陈述：complexMGF (X : Ω -> Real) (μ : Measure Ω) (z : Complex) : Complex
参数：X : Ω -> Real；μ : Measure Ω；z : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def complexMGF (X : Ω → ℝ) (μ : Measure Ω) (z : ℂ) : ℂ := ∫ ω, cexp (z * X ω) ∂μ
/-
**ProbabilityTheory.complexMGF_undef** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheor
y`。
形式化陈述：complexMGF_undef (hX : AEMeasurable X μ) (h : ¬ Integrable (fun ω => rexp 
(z.re * X ω)) μ) : complexMGF X μ z = 0
参数：hX : AEMeasurable X μ；h : ¬ Integrable (fun ω => rexp (z.re * X ω)) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.complexMGF.eq_1`：∀ {Ω : Type u_1} {m : MeasurableSpace
 Ω} (X : Ω → ℝ) (μ : MeasureTheory.Measure Ω) (z : ℂ),   ProbabilityTheory.compl
exMGF X μ z = ∫ (ω : Ω)…
· 使用定理 `MeasureTheory.integral_undef`：integral_undef {f : α -> G} (h : ¬Integrab
le f μ) : ∫ a, f a ∂μ = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integrable_norm_iff`：integrable_norm_iff {f : α -> β} (hf 
: AEStronglyMeasurable f μ) : Integrable (fun a => ‖f a‖) μ ↔ Integrable f μ
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用定理 `Continuous.cexp`：Continuous.cexp (h : Continuous f) : Continuous fun y =
> exp (f y)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `MeasureTheory.AEStronglyMeasurable.const_mul`：∀ {α : Type u_1} {β : Type
 u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.
Measure α}   {f : α → β} [inst_1 :…
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
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
· 使用定理 `AEMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst
 : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 : M…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.norm_exp`：norm_exp (z : Complex) : ‖exp z‖ = Real.exp z.re
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
-/
lemma complexMGF_undef (hX : AEMeasurable X μ) (h : ¬ Integrable (fun ω ↦ rexp (z.re * X ω)) μ) :
    complexMGF X μ z = 0 := by
  rw [complexMGF, integral_undef]
  rw [← integrable_norm_iff (by fun_prop)]
  simpa [Complex.norm_exp] using h
/-
**ProbabilityTheory.complexMGF_id_map** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheo
ry`。
形式化陈述：complexMGF_id_map (hX : AEMeasurable X μ) : complexMGF id (μ.map X) = comp
lexMGF X μ
参数：hX : AEMeasurable X μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.complexMGF.eq_1`：∀ {Ω : Type u_1} {m : MeasurableSpace
 Ω} (X : Ω → ℝ) (μ : MeasureTheory.Measure Ω) (z : ℂ),   ProbabilityTheory.compl
exMGF X μ z = ∫ (ω : Ω)…
· 使用定理 `MeasureTheory.integral_map`：integral_map {β} [MeasurableSpace β] {φ : α 
-> β} (hφ : AEMeasurable φ μ) {f : β -> G} (hfm : AEStronglyMeasurable f (Measur
e.map φ μ)) : ∫ …
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用定理 `Continuous.cexp`：Continuous.cexp (h : Continuous f) : Continuous fun y =
> exp (f y)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `MeasureTheory.AEStronglyMeasurable.const_mul`：∀ {α : Type u_1} {β : Type
 u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.
Measure α}   {f : α → β} [inst_1 :…
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
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
· 使用定理 `aestronglyMeasurable_id`：∀ {α : Type u_5} [inst : TopologicalSpace α] [T
opologicalSpace.PseudoMetrizableSpace α] {x : MeasurableSpace α}   [OpensMeasura
bleSpace α] […
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
-/
lemma complexMGF_id_map (hX : AEMeasurable X μ) : complexMGF id (μ.map X) = complexMGF X μ := by
  ext t
  rw [complexMGF, integral_map hX]
  · rfl
  · fun_prop
/-
**ProbabilityTheory.complexMGF_congr_identDistrib** 是 Mathlib 中的一个引理，位于命名空间 `Pro
babilityTheory`。
形式化陈述：complexMGF_congr_identDistrib {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ' 
: Measure Ω'} {Y : Ω' -> Real} (h : IdentDistrib X Y μ μ') : complexMGF X μ = co
mplexMGF Y μ'
参数：h : IdentDistrib X Y μ μ'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.complexMGF_id_map`：complexMGF_id_map (hX : AEMeasurabl
e X μ) : complexMGF id (μ.map X) = complexMGF X μ
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
lemma complexMGF_congr_identDistrib {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ' : Measure Ω'}
    {Y : Ω' → ℝ} (h : IdentDistrib X Y μ μ') :
    complexMGF X μ = complexMGF Y μ' := by
  rw [← complexMGF_id_map h.aemeasurable_fst, ← complexMGF_id_map h.aemeasurable_snd, h.map_eq]
/-
**ProbabilityTheory.norm_complexMGF_le_mgf** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory`。
形式化陈述：norm_complexMGF_le_mgf : ‖complexMGF X μ z‖ <= mgf X μ z.re
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.complexMGF.eq_1`：∀ {Ω : Type u_1} {m : MeasurableSpace
 Ω} (X : Ω → ℝ) (μ : MeasureTheory.Measure Ω) (z : ℂ),   ProbabilityTheory.compl
exMGF X μ z = ∫ (ω : Ω)…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.re_add_im`：re_add_im (z : Complex) : (z.re : Complex) + z.im * I
 = z
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `Complex.exp_add`：exp_add : exp (x + y) = exp x * exp y
· 使用定理 `MeasureTheory.norm_integral_le_integral_norm`：norm_integral_le_integral_
norm (f : α -> G) : ‖∫ a, f a ∂μ‖ <= ∫ a, ‖f a‖ ∂μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.norm_mul`：∀ (z w : ℂ), ‖z * w‖ = ‖z‖ * ‖w‖
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Complex.norm_exp`：norm_exp (z : Complex) : ‖exp z‖ = Real.exp z.re
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Real.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma norm_complexMGF_le_mgf : ‖complexMGF X μ z‖ ≤ mgf X μ z.re := by
  rw [complexMGF, ← re_add_im z]
  simp_rw [add_mul, Complex.exp_add, re_add_im]
  calc ‖∫ ω, cexp (z.re * X ω) * cexp (z.im * I * X ω) ∂μ‖
  _ ≤ ∫ ω, ‖cexp (z.re * X ω) * cexp (z.im * I * X ω)‖ ∂μ := norm_integral_le_integral_norm _
  _ = ∫ ω, rexp (z.re * X ω) ∂μ := by simp [Complex.norm_exp]
/-
**ProbabilityTheory.complexMGF_ofReal** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheo
ry`。
形式化陈述：complexMGF_ofReal (x : Real) : complexMGF X μ x = mgf X μ x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.complexMGF.eq_1`：∀ {Ω : Type u_1} {m : MeasurableSpace
 Ω} (X : Ω → ℝ) (μ : MeasureTheory.Measure Ω) (z : ℂ),   ProbabilityTheory.compl
exMGF X μ z = ∫ (ω : Ω)…
· 使用定理 `ProbabilityTheory.mgf.eq_1`：∀ {Ω : Type u_1} {m : MeasurableSpace Ω} (X 
: Ω → ℝ) (μ : MeasureTheory.Measure Ω) (t : ℝ),   ProbabilityTheory.mgf X μ t = 
∫ (x : Ω), (fun …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `integral_complex_ofReal`：integral_complex_ofReal {f : X -> Real} : ∫ x, 
(f x : Complex) ∂μ = ∫ x, f x ∂μ
-/
lemma complexMGF_ofReal (x : ℝ) : complexMGF X μ x = mgf X μ x := by
  rw [complexMGF, mgf]
  norm_cast
/-
**ProbabilityTheory.re_complexMGF_ofReal** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：re_complexMGF_ofReal (x : Real) : (complexMGF X μ x).re = mgf X μ x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.complexMGF_ofReal`：complexMGF_ofReal (x : Real) : comp
lexMGF X μ x = mgf X μ x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma re_complexMGF_ofReal (x : ℝ) : (complexMGF X μ x).re = mgf X μ x := by
  simp [complexMGF_ofReal]
/-
**ProbabilityTheory.re_complexMGF_ofReal'** 是 Mathlib 中的一个引理，位于命名空间 `Probability
Theory`。
形式化陈述：re_complexMGF_ofReal' : (fun x : Real => (complexMGF X μ x).re) = mgf X μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ProbabilityTheory.re_complexMGF_ofReal`：re_complexMGF_ofReal (x : Real) 
: (complexMGF X μ x).re = mgf X μ x
-/
lemma re_complexMGF_ofReal' : (fun x : ℝ ↦ (complexMGF X μ x).re) = mgf X μ := by
  ext x
  exact re_complexMGF_ofReal x
/-
**ProbabilityTheory.complexMGF_id_mul_I** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTh
eory`。
形式化陈述：complexMGF_id_mul_I {μ : Measure Real} (t : Real) : complexMGF id μ (t * I
) = charFun μ t
参数：t : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `conj_trivial`：∀ {R : Type u} [inst : CommSemiring R] [inst_1 : StarRing 
R] [TrivialStar R] (a : R), (starRingEnd R) a = a
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.RingNF.mul_assoc_rev`：mul_assoc_rev (a b c : R) : a * (b 
* c) = a * b * c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Mathlib.Tactic.RingNF.nat_rawCast_1`：nat_rawCast_1 : (Nat.rawCast 1 : R)
 = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma complexMGF_id_mul_I {μ : Measure ℝ} (t : ℝ) :
    complexMGF id μ (t * I) = charFun μ t := by
  simp only [complexMGF, id_eq, charFun, RCLike.inner_apply, conj_trivial, ofReal_mul]
  congr with x
  ring_nf
/-
**ProbabilityTheory.complexMGF_mul_I** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheor
y`。
形式化陈述：complexMGF_mul_I (hX : AEMeasurable X μ) (t : Real) : complexMGF X μ (t * 
I) = charFun (μ.map X) t
参数：hX : AEMeasurable X μ；t : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.complexMGF_id_map`：complexMGF_id_map (hX : AEMeasurabl
e X μ) : complexMGF id (μ.map X) = complexMGF X μ
· 使用引理 `ProbabilityTheory.complexMGF_id_mul_I`：complexMGF_id_mul_I {μ : Measure 
Real} (t : Real) : complexMGF id μ (t * I) = charFun μ t
-/
lemma complexMGF_mul_I (hX : AEMeasurable X μ) (t : ℝ) :
    complexMGF X μ (t * I) = charFun (μ.map X) t := by
  rw [← complexMGF_id_map hX, complexMGF_id_mul_I]

section Analytic

/-- For `z : ℂ` with `z.re ∈ interior (integrableExpSet X μ)`, the derivative of the function
`z' ↦ μ[X ^ n * cexp (z' * X)]` at `z` is `μ[X ^ (n + 1) * cexp (z * X)]`. -/
/-
**ProbabilityTheory.hasDerivAt_integral_pow_mul_exp** 是 Mathlib 中的一个引理，位于命名空间 `P
robabilityTheory`。
形式化陈述：hasDerivAt_integral_pow_mul_exp (hz : z.re in interior (integrableExpSet X
 μ)) (n : Nat) : HasDerivAt (fun z => μ[fun ω => X ω ^ n * cexp (z * X ω)]) μ[fu
n ω => X ω ^ (n + 1) * cexp (z * X ω)] z
参数：hz : z.re in interior (integrableExpSet X μ)；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.aemeasurable_of_mem_interior_integrableExpSet`：aemeasu
rable_of_mem_interior_integrableExpSet (hv : v in interior (integrableExpSet X μ
)) : AEMeasurable X μ
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_nhds_iff_exists_Ioo_subset`：mem_nhds_iff_exists_Ioo_subset [NoMaxOrd
er α] [NoMinOrder α] {a : α} {s : Set α} : s in 𝓝 a ↔ exists l u, a in Ioo l u ∧
 Ioo l u subseteq s
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
（共 103 条，此处仅展示前 30 条）

--- 原说明 ---
For `z : ℂ` with `z.re ∈ interior (integrableExpSet X μ)`, the derivative of the
 function
`z' ↦ μ[X ^ n * cexp (z' * X)]` at `z` is `μ[X ^ (n + 1) * cexp (z * X)]`.
-/
lemma hasDerivAt_integral_pow_mul_exp (hz : z.re ∈ interior (integrableExpSet X μ)) (n : ℕ) :
    HasDerivAt (fun z ↦ μ[fun ω ↦ X ω ^ n * cexp (z * X ω)])
        μ[fun ω ↦ X ω ^ (n + 1) * cexp (z * X ω)] z := by
  have hX : AEMeasurable X μ := aemeasurable_of_mem_interior_integrableExpSet hz
  have hz' := hz
  rw [mem_interior_iff_mem_nhds, mem_nhds_iff_exists_Ioo_subset] at hz'
  obtain ⟨l, u, hlu, h_subset⟩ := hz'
  let t := ((z.re - l) ⊓ (u - z.re)) / 2
  have h_pos : 0 < (z.re - l) ⊓ (u - z.re) := by simp [hlu.1, hlu.2]
  have ht : 0 < t := half_pos h_pos
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := fun ω ↦ |X ω| ^ (n + 1) * rexp (z.re * X ω + t / 2 * |X ω|))
    (F := fun z ω ↦ X ω ^ n * cexp (z * X ω))
    (F' := fun z ω ↦ X ω ^ (n + 1) * cexp (z * X ω)) (Metric.ball_mem_nhds _ (half_pos ht))
    ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact .of_forall fun z ↦ by fun_prop
  · exact integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet hz n
  · fun_prop
  · refine ae_of_all _ fun ω ε hε ↦ ?_
    simp only [norm_mul, norm_pow, norm_real, Real.norm_eq_abs]
    rw [Complex.norm_exp]
    simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    gcongr
    have : ε = z + (ε - z) := by simp
    rw [this, add_re, add_mul]
    gcongr _ + ?_
    refine (le_abs_self _).trans ?_
    rw [abs_mul]
    gcongr
    refine (abs_re_le_norm _).trans ?_
    simp only [Metric.mem_ball, dist_eq_norm] at hε
    exact hε.le
  · refine integrable_pow_abs_mul_exp_add_of_integrable_exp_mul ?_ ?_ ?_ ?_ (t := t) (n + 1)
    · exact h_subset (add_half_inf_sub_mem_Ioo hlu)
    · exact h_subset (sub_half_inf_sub_mem_Ioo hlu)
    · positivity
    · exact lt_of_lt_of_le (by simp [ht]) (le_abs_self _)
  · refine ae_of_all _ fun ω ε hε ↦ ?_
    simp_rw [pow_succ, mul_assoc]
    refine HasDerivAt.const_mul _ ?_
    simp_rw [← smul_eq_mul, Complex.exp_eq_exp_ℂ]
    convert! hasDerivAt_exp_smul_const (X ω : ℂ) ε using 1
    rw [smul_eq_mul, mul_comm]

/-- For all `z : ℂ` with `z.re ∈ interior (integrableExpSet X μ)`,
`complexMGF X μ` is differentiable at `z` with derivative `μ[X * exp (z * X)]`. -/
/-
**ProbabilityTheory.hasDerivAt_complexMGF** 是 Mathlib 中的一个定理，位于命名空间 `Probability
Theory`。
形式化陈述：hasDerivAt_complexMGF (hz : z.re in interior (integrableExpSet X μ)) : Has
DerivAt (complexMGF X μ) μ[fun ω => X ω * cexp (z * X ω)] z
参数：hz : z.re in interior (integrableExpSet X μ)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用引理 `ProbabilityTheory.hasDerivAt_integral_pow_mul_exp`：hasDerivAt_integral_p
ow_mul_exp (hz : z.re in interior (integrableExpSet X μ)) (n : Nat) : HasDerivAt
 (fun z => μ[fun ω => X ω ^ n * cexp (z…

--- 原说明 ---
For all `z : ℂ` with `z.re ∈ interior (integrableExpSet X μ)`,
`complexMGF X μ` is differentiable at `z` with derivative `μ[X * exp (z * X)]`.
-/
theorem hasDerivAt_complexMGF (hz : z.re ∈ interior (integrableExpSet X μ)) :
    HasDerivAt (complexMGF X μ) μ[fun ω ↦ X ω * cexp (z * X ω)] z := by
  convert! hasDerivAt_integral_pow_mul_exp hz 0
  · simp [complexMGF]
  · simp

/-- `complexMGF X μ` is holomorphic on the vertical strip
`{z | z.re ∈ interior (integrableExpSet X μ)}`. -/
/-
**ProbabilityTheory.differentiableOn_complexMGF** 是 Mathlib 中的一个定理，位于命名空间 `Proba
bilityTheory`。
形式化陈述：differentiableOn_complexMGF : DifferentiableOn Complex (complexMGF X μ) {z
 | z.re in interior (integrableExpSet X μ)}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `ProbabilityTheory.hasDerivAt_complexMGF`：hasDerivAt_complexMGF (hz : z.r
e in interior (integrableExpSet X μ)) : HasDerivAt (complexMGF X μ) μ[fun ω => X
 ω * cexp (z * X ω)] z
· 使用定理 `HasFDerivWithinAt.differentiableWithinAt`：HasFDerivWithinAt.differentiab
leWithinAt (h : HasFDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `HasFDerivAt.hasFDerivWithinAt`：HasFDerivAt.hasFDerivWithinAt (h : HasFDe
rivAt f f' x) : HasFDerivWithinAt f f' s x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hasDerivAt_iff_hasFDerivAt`：hasDerivAt_iff_hasFDerivAt {f' : F} : HasDer
ivAt f f' x ↔ HasFDerivAt f (toSpanSingleton 𝕜 f') x

--- 原说明 ---
`complexMGF X μ` is holomorphic on the vertical strip
`{z | z.re ∈ interior (integrableExpSet X μ)}`.
-/
theorem differentiableOn_complexMGF :
    DifferentiableOn ℂ (complexMGF X μ) {z | z.re ∈ interior (integrableExpSet X μ)} := by
  intro z hz
  have h := hasDerivAt_complexMGF hz
  rw [hasDerivAt_iff_hasFDerivAt] at h
  exact h.hasFDerivWithinAt.differentiableWithinAt
/-
**ProbabilityTheory.analyticOnNhd_complexMGF** 是 Mathlib 中的一个定理，位于命名空间 `Probabil
ityTheory`。
形式化陈述：analyticOnNhd_complexMGF : AnalyticOnNhd Complex (complexMGF X μ) {z | z.r
e in interior (integrableExpSet X μ)}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableOn.analyticOnNhd`：∀ {E : Type u} [inst : NormedAddCommGrou
p E] [inst_1 : NormedSpace ℂ E] [CompleteSpace E] {s : Set ℂ} {f : ℂ → E},   Dif
ferentiableOn ℂ f s …
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `ProbabilityTheory.differentiableOn_complexMGF`：differentiableOn_complexM
GF : DifferentiableOn Complex (complexMGF X μ) {z | z.re in interior (integrable
ExpSet X μ)}
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `Complex.continuous_re`：Continuous Complex.re
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
-/
theorem analyticOnNhd_complexMGF :
    AnalyticOnNhd ℂ (complexMGF X μ) {z | z.re ∈ interior (integrableExpSet X μ)} :=
  differentiableOn_complexMGF.analyticOnNhd (isOpen_interior.preimage Complex.continuous_re)

/-- `complexMGF X μ` is analytic on the vertical strip
  `{z | z.re ∈ interior (integrableExpSet X μ)}`. -/
/-
**ProbabilityTheory.analyticOn_complexMGF** 是 Mathlib 中的一个定理，位于命名空间 `Probability
Theory`。
形式化陈述：analyticOn_complexMGF : AnalyticOn Complex (complexMGF X μ) {z | z.re in i
nterior (integrableExpSet X μ)}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticOnNhd.analyticOn`：AnalyticOnNhd.analyticOn (hf : AnalyticOnNhd 𝕜
 f s) : AnalyticOn 𝕜 f s
· 使用定理 `ProbabilityTheory.analyticOnNhd_complexMGF`：analyticOnNhd_complexMGF : A
nalyticOnNhd Complex (complexMGF X μ) {z | z.re in interior (integrableExpSet X 
μ)}

--- 原说明 ---
`complexMGF X μ` is analytic on the vertical strip
  `{z | z.re ∈ interior (integrableExpSet X μ)}`.
-/
theorem analyticOn_complexMGF :
    AnalyticOn ℂ (complexMGF X μ) {z | z.re ∈ interior (integrableExpSet X μ)} :=
  analyticOnNhd_complexMGF.analyticOn

/-- `complexMGF X μ` is analytic at any point `z` with `z.re ∈ interior (integrableExpSet X μ)`. -/
/-
**ProbabilityTheory.analyticAt_complexMGF** 是 Mathlib 中的一个引理，位于命名空间 `Probability
Theory`。
形式化陈述：analyticAt_complexMGF (hz : z.re in interior (integrableExpSet X μ)) : Ana
lyticAt Complex (complexMGF X μ) z
参数：hz : z.re in interior (integrableExpSet X μ)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.analyticOnNhd_complexMGF`：analyticOnNhd_complexMGF : A
nalyticOnNhd Complex (complexMGF X μ) {z | z.re in interior (integrableExpSet X 
μ)}

--- 原说明 ---
`complexMGF X μ` is analytic at any point `z` with `z.re ∈ interior (integrableE
xpSet X μ)`.
-/
lemma analyticAt_complexMGF (hz : z.re ∈ interior (integrableExpSet X μ)) :
    AnalyticAt ℂ (complexMGF X μ) z :=
  analyticOnNhd_complexMGF z hz

end Analytic

section Deriv

/-! ### Iterated derivatives of `complexMGF` -/

/-
**ProbabilityTheory.hasDerivAt_iteratedDeriv_complexMGF** 是 Mathlib 中的一个引理，位于命名空
间 `ProbabilityTheory`。
形式化陈述：hasDerivAt_iteratedDeriv_complexMGF (hz : z.re in interior (integrableExpS
et X μ)) (n : Nat) : HasDerivAt (iteratedDeriv n (complexMGF X μ)) μ[fun ω => X 
ω ^ (n + 1) * cexp (z * X ω)] z
参数：hz : z.re in interior (integrableExpSet X μ)；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `iteratedDeriv_zero`：iteratedDeriv_zero : iteratedDeriv 0 f = f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ProbabilityTheory.hasDerivAt_complexMGF`：hasDerivAt_complexMGF (hz : z.r
e in interior (integrableExpSet X μ)) : HasDerivAt (complexMGF X μ) μ[fun ω => X
 ω * cexp (z * X ω)] z
· 使用定理 `iteratedDeriv_succ`：iteratedDeriv_succ : iteratedDeriv (n + 1) f = deriv
 (iteratedDeriv n f)
· 使用定理 `IsOpen.eventually_mem`：IsOpen.eventually_mem (hs : IsOpen s) (hx : x in 
s) : forallᶠ x in 𝓝 x, x in s
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `Complex.continuous_re`：Continuous Complex.re
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Filter.EventuallyEq.hasDerivAt_iff`：Filter.EventuallyEq.hasDerivAt_iff (
h : f₀ =ᶠ[𝓝 x] f₁) : HasDerivAt f₀ f' x ↔ HasDerivAt f₁ f' x
· 使用引理 `ProbabilityTheory.hasDerivAt_integral_pow_mul_exp`：hasDerivAt_integral_p
ow_mul_exp (hz : z.re in interior (integrableExpSet X μ)) (n : Nat) : HasDerivAt
 (fun z => μ[fun ω => X ω ^ n * cexp (z…

--- 原说明 ---
### Iterated derivatives of `complexMGF`
-/
lemma hasDerivAt_iteratedDeriv_complexMGF (hz : z.re ∈ interior (integrableExpSet X μ)) (n : ℕ) :
    HasDerivAt (iteratedDeriv n (complexMGF X μ)) μ[fun ω ↦ X ω ^ (n + 1) * cexp (z * X ω)] z := by
  induction n generalizing z with
  | zero => simp [hasDerivAt_complexMGF hz]
  | succ n hn =>
    rw [iteratedDeriv_succ]
    have : deriv (iteratedDeriv n (complexMGF X μ))
        =ᶠ[𝓝 z] fun z ↦ μ[fun ω ↦ X ω ^ (n + 1) * cexp (z * X ω)] := by
      have h_mem : ∀ᶠ y in 𝓝 z, y.re ∈ interior (integrableExpSet X μ) := by
        refine IsOpen.eventually_mem ?_ hz
        exact isOpen_interior.preimage Complex.continuous_re
      filter_upwards [h_mem] with y hy using HasDerivAt.deriv (hn hy)
    rw [EventuallyEq.hasDerivAt_iff this]
    exact hasDerivAt_integral_pow_mul_exp hz (n + 1)

/-- For `z : ℂ` with `z.re ∈ interior (integrableExpSet X μ)`, the n-th derivative of the function
`complexMGF X μ` at `z` is `μ[X ^ n * cexp (z * X)]`. -/
/-
**ProbabilityTheory.iteratedDeriv_complexMGF** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory`。
形式化陈述：iteratedDeriv_complexMGF (hz : z.re in interior (integrableExpSet X μ)) (n
 : Nat) : iteratedDeriv n (complexMGF X μ) z = μ[fun ω => X ω ^ n * cexp (z * X 
ω)]
参数：hz : z.re in interior (integrableExpSet X μ)；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedDeriv_zero`：iteratedDeriv_zero : iteratedDeriv 0 f = f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iteratedDeriv_succ`：iteratedDeriv_succ : iteratedDeriv (n + 1) f = deriv
 (iteratedDeriv n f)
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用引理 `ProbabilityTheory.hasDerivAt_iteratedDeriv_complexMGF`：hasDerivAt_iterat
edDeriv_complexMGF (hz : z.re in interior (integrableExpSet X μ)) (n : Nat) : Ha
sDerivAt (iteratedDeriv n (complexMGF X μ))…

--- 原说明 ---
For `z : ℂ` with `z.re ∈ interior (integrableExpSet X μ)`, the n-th derivative o
f the function
`complexMGF X μ` at `z` is `μ[X ^ n * cexp (z * X)]`.
-/
lemma iteratedDeriv_complexMGF (hz : z.re ∈ interior (integrableExpSet X μ)) (n : ℕ) :
    iteratedDeriv n (complexMGF X μ) z = μ[fun ω ↦ X ω ^ n * cexp (z * X ω)] := by
  induction n generalizing z with
  | zero => simp [complexMGF]
  | succ n hn =>
    rw [iteratedDeriv_succ]
    exact (hasDerivAt_iteratedDeriv_complexMGF hz n).deriv

end Deriv

section EqOfMGF

/-! We prove that if two random variables have the same `mgf`, then
they also have the same `complexMGF`. -/

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {Y : Ω' → ℝ} {μ' : Measure Ω'}

/-- If two random variables have the same moment-generating function then they have
the same `integrableExpSet`. -/
/-
**ProbabilityTheory.integrableExpSet_eq_of_mgf'** 是 Mathlib 中的一个引理，位于命名空间 `Proba
bilityTheory`。
形式化陈述：integrableExpSet_eq_of_mgf' (hXY : mgf X μ = mgf Y μ') (hμμ' : μ = 0 ↔ μ' 
= 0) : integrableExpSet X μ = integrableExpSet Y μ'
参数：hXY : mgf X μ = mgf Y μ'；hμμ' : μ = 0 ↔ μ' = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.mgf_pos_iff`：mgf_pos_iff [hμ : NeZero μ] : 0 < mgf X μ
 t ↔ Integrable (fun ω => exp (t * X ω)) μ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
If two random variables have the same moment-generating function then they have
the same `integrableExpSet`.
-/
lemma integrableExpSet_eq_of_mgf' (hXY : mgf X μ = mgf Y μ') (hμμ' : μ = 0 ↔ μ' = 0) :
    integrableExpSet X μ = integrableExpSet Y μ' := by
  ext t
  simp only [integrableExpSet, Set.mem_ofPred_eq]
  by_cases hμ : μ = 0
  · simp [hμ, hμμ'.mp hμ]
  have : NeZero μ := ⟨hμ⟩
  have : NeZero μ' := ⟨(not_iff_not.mpr hμμ').mp hμ⟩
  rw [← mgf_pos_iff, ← mgf_pos_iff, hXY]

/-- If two random variables have the same moment-generating function then they have
the same `integrableExpSet`. -/
/-
**ProbabilityTheory.integrableExpSet_eq_of_mgf** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：integrableExpSet_eq_of_mgf [IsProbabilityMeasure μ] (hXY : mgf X μ = mgf Y
 μ') : integrableExpSet X μ = integrableExpSet Y μ'
参数：hXY : mgf X μ = mgf Y μ'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.integrableExpSet_eq_of_mgf'`：integrableExpSet_eq_of_mg
f' (hXY : mgf X μ = mgf Y μ') (hμμ' : μ = 0 ↔ μ' = 0) : integrableExpSet X μ = i
ntegrableExpSet Y μ'
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `false_iff`：∀ (p : Prop), (False ↔ p) = ¬p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `ProbabilityTheory.mgf_pos`：mgf_pos [IsProbabilityMeasure μ] (h_int_X : I
ntegrable (fun ω => exp (t * X ω)) μ) : 0 < mgf X μ t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Real.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `enorm_one`：∀ {G : Type u_1} [inst : SeminormedAddCommGroup G] [inst_1 : 
One G] [NormOneClass G], ‖1‖ₑ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ProbabilityTheory.mgf_zero'`：mgf_zero' : mgf X μ 0 = μ.real Set.univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False

--- 原说明 ---
If two random variables have the same moment-generating function then they have
the same `integrableExpSet`.
-/
lemma integrableExpSet_eq_of_mgf [IsProbabilityMeasure μ]
    (hXY : mgf X μ = mgf Y μ') :
    integrableExpSet X μ = integrableExpSet Y μ' := by
  refine integrableExpSet_eq_of_mgf' hXY ?_
  simp only [IsProbabilityMeasure.ne_zero, false_iff]
  suffices mgf Y μ' 0 ≠ 0 by
    intro h_contra
    simp [h_contra] at this
  rw [← hXY]
  exact (mgf_pos (by simp)).ne'

/-- If two random variables have the same moment-generating function then they have
the same `complexMGF` on the vertical strip `{z | z.re ∈ interior (integrableExpSet X μ)}`.

TODO: once we know that equal `mgf` implies equal distributions, we will be able to show that
the `complexMGF` are equal everywhere, not only on the strip.
This lemma will be used in the proof of the equality of distributions. -/
/-
**ProbabilityTheory.eqOn_complexMGF_of_mgf'** 是 Mathlib 中的一个引理，位于命名空间 `Probabili
tyTheory`。
形式化陈述：eqOn_complexMGF_of_mgf' (hXY : mgf X μ = mgf Y μ') (hμμ' : μ = 0 ↔ μ' = 0)
 : Set.EqOn (complexMGF X μ) (complexMGF Y μ') {z | z.re in interior (integrable
ExpSet X μ)}
参数：hXY : mgf X μ = mgf Y μ'；hμμ' : μ = 0 ↔ μ' = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `ProbabilityTheory.analyticOnNhd_complexMGF`：analyticOnNhd_complexMGF : A
nalyticOnNhd Complex (complexMGF X μ) {z | z.re in interior (integrableExpSet X 
μ)}
· 使用引理 `ProbabilityTheory.integrableExpSet_eq_of_mgf'`：integrableExpSet_eq_of_mg
f' (hXY : mgf X μ = mgf Y μ') (hμμ' : μ = 0 ↔ μ' = 0) : integrableExpSet X μ = i
ntegrableExpSet Y μ'
· 使用定理 `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`：eqOn_of_preconnecte
d_of_frequently_eq (hf : AnalyticOnNhd 𝕜 f U) (hg : AnalyticOnNhd 𝕜 g U) (hU : I
sPreconnected U) (h₀ : z₀ in U) (hfg : ex…
· 使用定理 `Convex.isPreconnected`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 
: _root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousAdd E]   [Continuo
usSMul ℝ E]…
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
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Convex.linear_preimage`：Convex.linear_preimage {s : Set F} (hs : Convex 
𝕜 s) (f : E ->ₗ[𝕜] F) : Convex 𝕜 (f ⁻¹' s)
· 使用定理 `Convex.interior`：∀ {𝕜 : Type u_2} {E : Type u_3} [inst : Field 𝕜] [inst_
1 : PartialOrder 𝕜] [inst_2 : AddCommGroup E]   [inst_3 : _root_.Module 𝕜 E] [in
st_4 …
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用引理 `ProbabilityTheory.convex_integrableExpSet`：convex_integrableExpSet : Con
vex Real (integrableExpSet X μ)
· 使用定理 `Filter.Frequently.of_forall`：∀ {α : Type u} {f : Filter α} [f.NeBot] {p 
: α → Prop}, (∀ (x : α), p x) → ∃ᶠ (x : α) in f, p x
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
· 使用引理 `ProbabilityTheory.complexMGF_ofReal`：complexMGF_ofReal (x : Real) : comp
lexMGF X μ x = mgf X μ x
· 使用引理 `Filter.frequently_iff_seq_forall`：frequently_iff_seq_forall {ι : Type*} 
{l : Filter ι} {p : ι -> Prop} [l.IsCountablyGenerated] : (existsᶠ n in l, p n) 
↔ exists ns : Nat -> ι…
· 使用定理 `FirstCountableTopology.nhds_generated_countable`：∀ {α : Type u} {t : Top
ologicalSpace α} [self : FirstCountableTopology α] (a : α), (nhds a).IsCountably
Generated
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
If two random variables have the same moment-generating function then they have
the same `complexMGF` on the vertical strip `{z | z.re ∈ interior (integrableExp
Set X μ)}`.

TODO: once we know that equal `mgf` implies equal distributions, we will be able
 to show that
the `complexMGF` are equal everywhere, not only on the strip.
This lemma will be used in the proof of the equality of distributions.
-/
lemma eqOn_complexMGF_of_mgf' (hXY : mgf X μ = mgf Y μ') (hμμ' : μ = 0 ↔ μ' = 0) :
    Set.EqOn (complexMGF X μ) (complexMGF Y μ') {z | z.re ∈ interior (integrableExpSet X μ)} := by
  by_cases h_empty : interior (integrableExpSet X μ) = ∅
  · simp [h_empty]
  rw [← ne_eq, ← Set.nonempty_iff_ne_empty] at h_empty
  obtain ⟨t, ht⟩ := h_empty
  have hX : AnalyticOnNhd ℂ (complexMGF X μ) {z | z.re ∈ interior (integrableExpSet X μ)} :=
    analyticOnNhd_complexMGF
  have hY : AnalyticOnNhd ℂ (complexMGF Y μ') {z | z.re ∈ interior (integrableExpSet Y μ')} :=
    analyticOnNhd_complexMGF
  rw [integrableExpSet_eq_of_mgf' hXY hμμ'] at hX ht ⊢
  refine AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq hX hY
    (convex_integrableExpSet.interior.linear_preimage reLm).isPreconnected
    (z₀ := (t : ℂ)) (by simp [ht]) ?_
  have h_real : ∃ᶠ (x : ℝ) in 𝓝[≠] t, complexMGF X μ x = complexMGF Y μ' x := by
    refine .of_forall fun y ↦ ?_
    rw [complexMGF_ofReal, complexMGF_ofReal, hXY]
  rw [frequently_iff_seq_forall] at h_real ⊢
  obtain ⟨xs, hx_tendsto, hx_eq⟩ := h_real
  refine ⟨fun n ↦ xs n, ?_, fun n ↦ ?_⟩
  · rw [tendsto_nhdsWithin_iff] at hx_tendsto ⊢
    constructor
    · rw [tendsto_ofReal_iff]
      exact hx_tendsto.1
    · simpa using hx_tendsto.2
  · simp [hx_eq]

/-- If two random variables have the same moment-generating function then they have
the same `complexMGF` on the vertical strip `{z | z.re ∈ interior (integrableExpSet X μ)}`. -/
/-
**ProbabilityTheory.eqOn_complexMGF_of_mgf** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory`。
形式化陈述：eqOn_complexMGF_of_mgf [IsProbabilityMeasure μ] (hXY : mgf X μ = mgf Y μ')
 : Set.EqOn (complexMGF X μ) (complexMGF Y μ') {z | z.re in interior (integrable
ExpSet X μ)}
参数：hXY : mgf X μ = mgf Y μ'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.eqOn_complexMGF_of_mgf'`：eqOn_complexMGF_of_mgf' (hXY 
: mgf X μ = mgf Y μ') (hμμ' : μ = 0 ↔ μ' = 0) : Set.EqOn (complexMGF X μ) (compl
exMGF Y μ') {z | z.re in interi…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `false_iff`：∀ (p : Prop), (False ↔ p) = ¬p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `ProbabilityTheory.mgf_pos`：mgf_pos [IsProbabilityMeasure μ] (h_int_X : I
ntegrable (fun ω => exp (t * X ω)) μ) : 0 < mgf X μ t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Real.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `enorm_one`：∀ {G : Type u_1} [inst : SeminormedAddCommGroup G] [inst_1 : 
One G] [NormOneClass G], ‖1‖ₑ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ProbabilityTheory.mgf_zero'`：mgf_zero' : mgf X μ 0 = μ.real Set.univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False

--- 原说明 ---
If two random variables have the same moment-generating function then they have
the same `complexMGF` on the vertical strip `{z | z.re ∈ interior (integrableExp
Set X μ)}`.
-/
lemma eqOn_complexMGF_of_mgf [IsProbabilityMeasure μ]
    (hXY : mgf X μ = mgf Y μ') :
    Set.EqOn (complexMGF X μ) (complexMGF Y μ') {z | z.re ∈ interior (integrableExpSet X μ)} := by
  refine eqOn_complexMGF_of_mgf' hXY ?_
  simp only [IsProbabilityMeasure.ne_zero, false_iff]
  suffices mgf Y μ' 0 ≠ 0 by
    intro h_contra
    simp [h_contra] at this
  rw [← hXY]
  exact (mgf_pos (by simp)).ne'

end EqOfMGF

section ext

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {Y : Ω' → ℝ} {μ' : Measure Ω'}

set_option backward.isDefEq.respectTransparency.types false in
/-- If the complex moment-generating functions of two random variables `X` and `Y` with respect to
the finite measures `μ`, `μ'`, respectively, coincide, then `μ.map X = μ'.map Y`. In other words,
complex moment-generating functions separate the distributions of random variables. -/
/-
**ProbabilityTheory._root_.MeasureTheory.Measure.ext_of_complexMGF_eq** 是 Mathli
b 中的一个定理，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the complex moment-generating functions of two random variables `X` and `Y` w
ith respect to
the finite measures `μ`, `μ'`, respectively, coincide, then `μ.map X = μ'.map Y`
. In other words,
complex moment-generating functions separate the distributions of random variabl
es.
-/
theorem _root_.MeasureTheory.Measure.ext_of_complexMGF_eq [IsFiniteMeasure μ]
    [IsFiniteMeasure μ'] (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ')
    (h : complexMGF X μ = complexMGF Y μ') :
    μ.map X = μ'.map Y := by
  have inner_ne_zero (x : ℝ) (h : x ≠ 0) : innerₗ ℝ x ≠ 0 :=
    DFunLike.ne_iff.mpr ⟨x, inner_self_ne_zero.mpr h⟩
  apply MeasureTheory.ext_of_integral_char_eq continuous_probChar probChar_ne_one inner_ne_zero
    continuous_inner (fun w ↦ ?_)
  rw [funext_iff] at h
  specialize h (Multiplicative.toAdd w * I)
  simp_rw [complexMGF, mul_assoc, mul_comm I, ← mul_assoc] at h
  simp only [BoundedContinuousFunction.char_apply, innerₗ_apply_apply,
    RCLike.inner_apply, conj_trivial, probChar_apply, ofReal_mul]
  rwa [integral_map hX (by fun_prop), integral_map hY (by fun_prop)]
/-
**ProbabilityTheory._root_.MeasureTheory.Measure.ext_of_complexMGF_id_eq** 是 Mat
hlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MeasureTheory.Measure.ext_of_complexMGF_id_eq
    {μ μ' : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure μ']
    (h : complexMGF id μ = complexMGF id μ') :
    μ = μ' := by
  simpa using Measure.ext_of_complexMGF_eq aemeasurable_id aemeasurable_id h

end ext

end ProbabilityTheory

