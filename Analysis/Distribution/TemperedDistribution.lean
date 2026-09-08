/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM

/-!
# TemperedDistribution

## Main definitions

* `TemperedDistribution E F`: The space `𝓢(E, ℂ) →L[ℂ] F` equipped with the pointwise
  convergence topology.
* `MeasureTheory.Measure.toTemperedDistribution`: Every measure of temperate growth is a tempered
  distribution.
* `Function.HasTemperateGrowth.toTemperedDistribution`: Every function of temperate growth is a
  tempered distribution.
* `SchwartzMap.toTemperedDistributionCLM`: The canonical map from `𝓢` to `𝓢'` as a continuous linear
  map.
* `MeasureTheory.Lp.toTemperedDistribution`: Every `Lp` function is a tempered distribution.
* `TemperedDistribution.mulLeftCLM`: Multiplication with temperate growth function as a continuous
  linear map.
* `TemperedDistribution.instLineDeriv`: The directional derivative on tempered distributions.
* `TemperedDistribution.fourierTransformCLM`: The Fourier transform on tempered distributions.

## Notation
* `𝓢'(E, F)`: The space of tempered distributions `TemperedDistribution E F` scoped in
  `SchwartzMap`
-/

@[expose] public noncomputable section

open SchwartzMap ContinuousLinearMap MeasureTheory MeasureTheory.Measure

open scoped Nat NNReal ContDiff

variable {ι 𝕜 E F F₁ F₂ : Type*}

section definition

variable [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℂ F]

variable (E F) in
/-- The space of tempered distribution is the space of continuous linear maps from the Schwartz to
a normed space, equipped with the topology of pointwise convergence. -/
/-
**TemperedDistribution** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：TemperedDistribution
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The space of tempered distribution is the space of continuous linear maps from t
he Schwartz to
a normed space, equipped with the topology of pointwise convergence.
-/
abbrev TemperedDistribution := 𝓢(E, ℂ) →Lₚₜ[ℂ] F
/- Since mathlib is missing quite a few results that show that continuity of linear maps and
convergence of sequences can be checked for strong duals of Fréchet-Montel spaces pointwise, we
use the pointwise topology for now and not the strong topology. The pointwise topology is
conventionally used in PDE texts, but has the downside that it is not barrelled, hence the uniform
boundedness principle does not hold. -/

@[inherit_doc]
scoped[SchwartzMap] notation "𝓢'(" E ", " F ")" => TemperedDistribution E F

end definition

/-! ### Embeddings into tempered distributions -/

section Embeddings

variable [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

namespace MeasureTheory.Measure

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (μ : Measure E := by volume_tac) [hμ : μ.HasTemperateGrowth]

set_option backward.privateInPublic true in
/-- Every temperate growth measure defines a tempered distribution. -/
/-
**MeasureTheory.Measure.toTemperedDistribution** 是 Mathlib 中的一个定义，位于命名空间 `Measur
eTheory.Measure`。
形式化陈述：toTemperedDistribution : 𝓢'(E, Complex)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every temperate growth measure defines a tempered distribution.
-/
def toTemperedDistribution : 𝓢'(E, ℂ) :=
  toPointwiseConvergenceCLM _ _ _ _ (integralCLM ℂ μ)

set_option backward.privateInPublic true in
@[simp]
/-
**MeasureTheory.Measure.toTemperedDistribution_apply** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.Measure`。
形式化陈述：toTemperedDistribution_apply (g : 𝓢(E, Complex)) : μ.toTemperedDistributio
n g = ∫ (x : E), g x ∂μ
参数：g : 𝓢(E, Complex)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toTemperedDistribution_apply (g : 𝓢(E, ℂ)) :
    μ.toTemperedDistribution g = ∫ (x : E), g x ∂μ := by
  rfl

end MeasureTheory.Measure

namespace Function.HasTemperateGrowth

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (μ : Measure E := by volume_tac) [hμ : μ.HasTemperateGrowth]

set_option backward.privateInPublic true in
/-- A function of temperate growth `f` defines a tempered distribution via integration, namely
`g ↦ ∫ (x : E), g x • f x ∂μ`. -/
/-
**Function.HasTemperateGrowth.toTemperedDistribution** 是 Mathlib 中的一个定义，位于命名空间 `
Function.HasTemperateGrowth`。
形式化陈述：toTemperedDistribution {f : E -> F} (hf : f.HasTemperateGrowth) : 𝓢'(E, F)
参数：hf : f.HasTemperateGrowth。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function of temperate growth `f` defines a tempered distribution via integrati
on, namely
`g ↦ ∫ (x : E), g x • f x ∂μ`.
-/
def toTemperedDistribution {f : E → F} (hf : f.HasTemperateGrowth) : 𝓢'(E, F) :=
  toPointwiseConvergenceCLM _ _ _ _ ((integralCLM ℂ μ) ∘L (bilinLeftCLM (lsmul ℂ ℂ) hf))

set_option backward.privateInPublic true in
@[simp]
/-
**Function.HasTemperateGrowth.toTemperedDistribution_apply** 是 Mathlib 中的一个定理，位于
命名空间 `Function.HasTemperateGrowth`。
形式化陈述：toTemperedDistribution_apply {f : E -> F} (hf : f.HasTemperateGrowth) (g :
 𝓢(E, Complex)) : toTemperedDistribution μ hf g = ∫ (x : E), g x • f x ∂μ
参数：hf : f.HasTemperateGrowth；g : 𝓢(E, Complex)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toTemperedDistribution_apply {f : E → F} (hf : f.HasTemperateGrowth) (g : 𝓢(E, ℂ)) :
    toTemperedDistribution μ hf g = ∫ (x : E), g x • f x ∂μ := rfl

end Function.HasTemperateGrowth

namespace SchwartzMap

section MeasurableSpace

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

set_option backward.isDefEq.respectTransparency false in
variable (E F) in
/-- The canonical embedding of `𝓢(E, F)` into `𝓢'(E, F)` as a continuous linear map. -/
/-
**SchwartzMap.toTemperedDistributionCLM** 是 Mathlib 中的一个定义，位于命名空间 `SchwartzMap`。
形式化陈述：toTemperedDistributionCLM (μ : Measure E
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical embedding of `𝓢(E, F)` into `𝓢'(E, F)` as a continuous linear map.
-/
def toTemperedDistributionCLM (μ : Measure E := by volume_tac) [hμ : μ.HasTemperateGrowth] :
    𝓢(E, F) →L[ℂ] 𝓢'(E, F) where
  toFun f := toPointwiseConvergenceCLM _ _ _ _ <| integralCLM ℂ μ ∘L pairing (lsmul ℂ ℂ).flip f
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  cont := PointwiseConvergenceCLM.continuous_of_continuous_eval
    fun g ↦ (integralCLM ℂ μ).cont.comp <| pairing_continuous_left (lsmul ℂ ℂ).flip g

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**SchwartzMap.toTemperedDistributionCLM_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `S
chwartzMap`。
形式化陈述：toTemperedDistributionCLM_apply_apply (μ : Measure E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousLinearMap.toPointwiseConvergenceCLM_apply`：∀ {𝕜₁ : Type u_4} (
𝕜₂ : Type u_5) [inst : NormedField 𝕜₁] [inst_1 : NormedField 𝕜₂] (σ : 𝕜₁ →+* 𝕜₂)
 (E : Type u_7)   (F : Type u_8) [inst_2 …
· 使用定理 `AddHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : Add M] [
inst_1 : Add N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_add' 
: ∀ (x y :…
· 使用定理 `LinearMap.mk.congr_simp`：∀ {R : Type u_14} {S : Type u_15} [inst : Semir
ing R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_16}   {M₂ : Type u_17} [i
nst_2 : AddCo…
· 使用定理 `ContinuousLinearMap.mk.congr_simp`：∀ {R : Type u_1} {S : Type u_2} [inst
 : Semiring R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_3}   [inst_2 : To
pologicalSpace M] [inst…
· 使用定理 `ContinuousLinearMap.comp_apply`：comp_apply (g : M₂ ->SL[σ₂₃] M₃) (f : M₁
 ->SL[σ₁₂] M₂) (x : M₁) : (g ∘SL f) x = g (f x)
· 使用引理 `SchwartzMap.integralCLM_apply`：integralCLM_apply (f : 𝓢(D, V)) : integra
lCLM 𝕜 μ f = ∫ x, f x ∂μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toTemperedDistributionCLM_apply_apply (μ : Measure E := by volume_tac)
    [hμ : μ.HasTemperateGrowth] (f : 𝓢(E, F)) (g : 𝓢(E, ℂ)) :
    toTemperedDistributionCLM E F μ f g = ∫ (x : E), g x • f x ∂μ := by
  simp [toTemperedDistributionCLM, comp_apply _]

end MeasurableSpace

section MeasureSpace

variable [MeasureSpace E] [BorelSpace E] [SecondCountableTopology E]
  [(volume (α := E)).HasTemperateGrowth]

/-
**SchwartzMap.instCoeToTemperedDistribution** 是 Mathlib 中的一个实例，位于命名空间 `SchwartzM
ap`。
形式化陈述：instCoeToTemperedDistribution : Coe 𝓢(E, F) 𝓢'(E, F) where coe
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCoeToTemperedDistribution :
    Coe 𝓢(E, F) 𝓢'(E, F) where
  coe := toTemperedDistributionCLM E F volume
/-
**SchwartzMap.coe_apply** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：coe_apply (f : 𝓢(E, F)) (g : 𝓢(E, Complex)) : (f : 𝓢'(E, F)) g = ∫ (x : E)
, g x • f x
参数：f : 𝓢(E, F)；g : 𝓢(E, Complex)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SchwartzMap.toTemperedDistributionCLM_apply_apply`：toTemperedDistributio
nCLM_apply_apply (μ : Measure E
-/
theorem coe_apply (f : 𝓢(E, F)) (g : 𝓢(E, ℂ)) :
    (f : 𝓢'(E, F)) g = ∫ (x : E), g x • f x :=
  toTemperedDistributionCLM_apply_apply volume f g

end MeasureSpace

end SchwartzMap

namespace MeasureTheory.Lp

open scoped ENNReal

variable [CompleteSpace F]

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [hμ : μ.HasTemperateGrowth]

/-- Define a tempered distribution from a L^p function. -/
/-
**MeasureTheory.Lp.toTemperedDistribution** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheo
ry.Lp`。
形式化陈述：toTemperedDistribution {p : Real>=0∞} [hp : Fact (1 <= p)] (f : Lp F p μ) 
: 𝓢'(E, F)
参数：1 <= p；f : Lp F p μ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define a tempered distribution from a L^p function.
-/
def toTemperedDistribution {p : ℝ≥0∞}
    [hp : Fact (1 ≤ p)] (f : Lp F p μ) : 𝓢'(E, F) :=
  haveI := ENNReal.HolderConjugate.inv_one_sub_inv' hp.out
  haveI : Fact (1 ≤ (1 - p⁻¹)⁻¹) := by simp [fact_iff]
  toPointwiseConvergenceCLM _ _ _ _ <|
    (lsmul ℂ ℂ).flip.lpPairing μ p (1 - p⁻¹)⁻¹ f ∘L toLpCLM ℂ ℂ (1 - p⁻¹)⁻¹ μ

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**MeasureTheory.Lp.toTemperedDistribution_apply** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.Lp`。
形式化陈述：toTemperedDistribution_apply {p : Real>=0∞} [hp : Fact (1 <= p)] (f : Lp F
 p μ) (g : 𝓢(E, Complex)) : toTemperedDistribution f g = ∫ (x : E), g x • f x ∂μ
参数：1 <= p；f : Lp F p μ；g : 𝓢(E, Complex)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.toPointwiseConvergenceCLM_apply`：∀ {𝕜₁ : Type u_4} (
𝕜₂ : Type u_5) [inst : NormedField 𝕜₁] [inst_1 : NormedField 𝕜₂] (σ : 𝕜₁ →+* 𝕜₂)
 (E : Type u_7)   (F : Type u_8) [inst_2 …
· 使用定理 `ContinuousLinearMap.comp_apply`：comp_apply (g : M₂ ->SL[σ₂₃] M₃) (f : M₁
 ->SL[σ₁₂] M₂) (x : M₁) : (g ∘SL f) x = g (f x)
· 使用引理 `ContinuousLinearMap.lpPairing_eq_integral`：lpPairing_eq_integral (f : Lp
 E p μ) (g : Lp F q μ) : B.lpPairing μ p q f g = ∫ x, B (f x) (g x) ∂μ
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `SchwartzMap.coeFn_toLp`：coeFn_toLp (f : 𝓢(E, F)) (p : Real>=0∞) (μ : Mea
sure E
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
-/
theorem toTemperedDistribution_apply {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] (f : Lp F p μ)
    (g : 𝓢(E, ℂ)) :
    toTemperedDistribution f g = ∫ (x : E), g x • f x ∂μ := by
  simp only [toTemperedDistribution, toPointwiseConvergenceCLM_apply, comp_apply _, toLpCLM_apply,
    lpPairing_eq_integral, lsmul_flip_apply, toSpanSingleton_apply]
  apply integral_congr_ae
  filter_upwards [g.coeFn_toLp (1 - p⁻¹)⁻¹ μ] with x hg
  rw [hg]

/-- This coercion has to be a `CoeHead`, because `𝓢'(E, F)` can't infer the value of `p` or `μ`. -/
/-
**MeasureTheory.Lp.instCoeToTemperedDistribution** 是 Mathlib 中的一个实例，位于命名空间 `Meas
ureTheory.Lp`。
形式化陈述：instCoeToTemperedDistribution {p : Real>=0∞} [hp : Fact (1 <= p)] : CoeHea
d (Lp F p μ) 𝓢'(E, F) where coe
参数：1 <= p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This coercion has to be a `CoeHead`, because `𝓢'(E, F)` can't infer the value of
 `p` or `μ`.
-/
instance instCoeToTemperedDistribution {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] :
    CoeHead (Lp F p μ) 𝓢'(E, F) where
  coe := toTemperedDistribution

@[simp]
/-
**MeasureTheory.Lp.toTemperedDistribution_toLp_eq** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.Lp`。
形式化陈述：toTemperedDistribution_toLp_eq [SecondCountableTopology E] {p : Real>=0∞} 
[hp : Fact (1 <= p)] (f : 𝓢(E, F)) : ((f : Lp F p μ) : 𝓢'(E, F)) = f.toTemperedD
istributionCLM E F μ
参数：1 <= p；f : 𝓢(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformConvergenceCLM.ext`：ext [TopologicalSpace F] {𝔖 : Set (Set E)} {f
 g : E ->SLᵤ[σ, 𝔖] F} (h : forall x, f x = g x) : f = g
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `secondCountableTopologyEither_of_left`：∀ (α : Type u_6) (β : Type u_7) [
inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolog
y α],   SecondCountableTopo…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Lp.toTemperedDistribution_apply`：toTemperedDistribution_ap
ply {p : Real>=0∞} [hp : Fact (1 <= p)] (f : Lp F p μ) (g : 𝓢(E, Complex)) : toT
emperedDistribution f g = ∫ (x : E)…
· 使用定理 `SchwartzMap.toTemperedDistributionCLM_apply_apply`：toTemperedDistributio
nCLM_apply_apply (μ : Measure E
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `SchwartzMap.coeFn_toLp`：coeFn_toLp (f : 𝓢(E, F)) (p : Real>=0∞) (μ : Mea
sure E
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
-/
theorem toTemperedDistribution_toLp_eq [SecondCountableTopology E] {p : ℝ≥0∞} [hp : Fact (1 ≤ p)]
    (f : 𝓢(E, F)) : ((f : Lp F p μ) : 𝓢'(E, F)) = f.toTemperedDistributionCLM E F μ := by
  ext g
  simp only [Lp.toTemperedDistribution_apply, toTemperedDistributionCLM_apply_apply]
  apply integral_congr_ae
  filter_upwards [f.coeFn_toLp p μ] with x hf
  rw [hf]

set_option backward.isDefEq.respectTransparency false in
variable (F) in
/-- The natural embedding of L^p into tempered distributions. -/
/-
**MeasureTheory.Lp.toTemperedDistributionCLM** 是 Mathlib 中的一个定义，位于命名空间 `MeasureT
heory.Lp`。
形式化陈述：toTemperedDistributionCLM (μ : Measure E
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural embedding of L^p into tempered distributions.
-/
def toTemperedDistributionCLM (μ : Measure E := by volume_tac) [μ.HasTemperateGrowth]
    (p : ℝ≥0∞) [hp : Fact (1 ≤ p)] :
    Lp F p μ →L[ℂ] 𝓢'(E, F) where
  toFun := toTemperedDistribution
  map_add' f g := by simp [Lp.toTemperedDistribution]
  map_smul' a f := by simp [Lp.toTemperedDistribution]
  cont := by
    apply PointwiseConvergenceCLM.continuous_of_continuous_eval
    intro g
    have : Fact (1 ≤ (1 - p⁻¹)⁻¹) := by simp [fact_iff]
    have hpq : ENNReal.HolderConjugate p (1 - p⁻¹)⁻¹ :=
      ENNReal.HolderConjugate.inv_one_sub_inv' hp.out
    exact (((lsmul ℂ ℂ (E := F)).flip.lpPairing μ p (1 - p⁻¹)⁻¹).flip (g.toLp (1 - p⁻¹)⁻¹ μ)).cont

@[simp]
/-
**MeasureTheory.Lp.toTemperedDistributionCLM_apply** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.Lp`。
形式化陈述：toTemperedDistributionCLM_apply {p : Real>=0∞} [hp : Fact (1 <= p)] (f : L
p F p μ) : toTemperedDistributionCLM F μ p f = f
参数：1 <= p；f : Lp F p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
theorem toTemperedDistributionCLM_apply {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] (f : Lp F p μ) :
    toTemperedDistributionCLM F μ p f = f := rfl

variable [FiniteDimensional ℝ E] [IsLocallyFiniteMeasure μ]
/-
**MeasureTheory.Lp.ker_toTemperedDistributionCLM_eq_bot** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.Lp`。
形式化陈述：ker_toTemperedDistributionCLM_eq_bot {p : Real>=0∞} [hp : Fact (1 <= p)] :
 (MeasureTheory.Lp.toTemperedDistributionCLM F μ p).ker = ⊥
参数：1 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.ker_eq_bot'`：ker_eq_bot' {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ fo
rall m, f m = 0 -> m = 0
· 使用定理 `ContinuousLinearMap.coe_coe`：coe_coe (f : M₁ ->SL[σ₁₂] M₂) : ⇑(f : M₁ ->
ₛₗ[σ₁₂] M₂) = f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Lp.eq_zero_iff_ae_eq_zero`：eq_zero_iff_ae_eq_zero {f : Lp 
E p μ} : f = 0 ↔ f =ᵐ[μ] 0
· 使用定理 `ae_eq_zero_of_integral_contDiff_smul_eq_zero`：ae_eq_zero_of_integral_con
tDiff_smul_eq_zero (hf : LocallyIntegrable f μ) (h : forall (g : E -> Real), Con
tDiff Real ∞ g -> HasCompactSuppor…
· 使用定理 `MeasureTheory.MemLp.locallyIntegrable`：∀ {X : Type u_1} {ε : Type u_3} [
inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst_2 : TopologicalSpa
ce ε]   [inst_3 : Continuou…
· 使用定理 `MeasureTheory.Lp.memLp`：∀ {α : Type u_1} {E : Type u_4} {m : MeasurableS
pace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGroup
 E] (f : ↥(M…
· 使用定理 `Fact.elim`：Fact.elim {p : Prop} (h : Fact p) : p
· 使用定理 `HasCompactSupport.comp_left`：∀ {α : Type u_2} {β : Type u_4} {γ : Type u
_5} [inst : TopologicalSpace α] [inst_1 : Zero β] [inst_2 : Zero γ]   {g : β → γ
} {f : α → β}, Ha…
· 使用定理 `ContDiff.clm_apply`：ContDiff.clm_apply {f : E -> F ->L[𝕜] G} {g : E -> F
} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) : ContDiff 𝕜 n fun x => (f x) (g x
)
· 使用定理 `contDiff_const`：contDiff_const {c : F} : ContDiff 𝕜 n fun _ : E => c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Lp.toTemperedDistribution_apply`：toTemperedDistribution_ap
ply {p : Real>=0∞} [hp : Fact (1 <= p)] (f : Lp F p μ) (g : 𝓢(E, Complex)) : toT
emperedDistribution f g = ∫ (x : E)…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HasCompactSupport.toSchwartzMap_toFun`：∀ {E : Type u_5} {F : Type u_6} [
inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommG
roup F]   [inst_3 : NormedS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `UniformConvergenceCLM.instIsZeroApply`：∀ {𝕜₁ : Type u_1} {𝕜₂ : Type u_2}
 [inst : NormedField 𝕜₁] [inst_1 : NormedField 𝕜₂] (σ : 𝕜₁ →+* 𝕜₂) {E : Type u_3
}   (F : Type u_4) [inst_2 …
-/
theorem ker_toTemperedDistributionCLM_eq_bot {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] :
    (MeasureTheory.Lp.toTemperedDistributionCLM F μ p).ker = ⊥ := by
  rw [LinearMap.ker_eq_bot', ContinuousLinearMap.coe_coe]
  intro f hf
  rw [eq_zero_iff_ae_eq_zero]
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero
  · exact (Lp.memLp f).locallyIntegrable hp.elim
  · intro g g_smooth g_cpt
    have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := g_cpt.comp_left rfl
    have hg₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
    calc
      _ = toTemperedDistributionCLM F μ p f (hg₁.toSchwartzMap hg₂) := by simp
      _ = _ := by simp [hf]

end MeasureTheory.Lp

end Embeddings

namespace TemperedDistribution

/-! ### Scalar multiplication with temperate growth functions -/

section Multiplication

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

section TVS

variable [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousConstSMul ℂ F]

variable (F) in
/-- Multiplication with a temperate growth function as a continuous linear map on `𝓢'(E, F)`. -/
/-
**TemperedDistribution.smulLeftCLM** 是 Mathlib 中的一个定义，位于命名空间 `TemperedDistributi
on`。
形式化陈述：smulLeftCLM (g : E -> Complex) : 𝓢'(E, F) ->L[Complex] 𝓢'(E, F)
参数：g : E -> Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplication with a temperate growth function as a continuous linear map on `𝓢
'(E, F)`.
-/
def smulLeftCLM (g : E → ℂ) : 𝓢'(E, F) →L[ℂ] 𝓢'(E, F) :=
  PointwiseConvergenceCLM.precomp _ (SchwartzMap.smulLeftCLM ℂ g)

@[simp]
/-
**TemperedDistribution.smulLeftCLM_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `Temper
edDistribution`。
形式化陈述：smulLeftCLM_apply_apply (g : E -> Complex) (f : 𝓢'(E, F)) (f' : 𝓢(E, Compl
ex)) : smulLeftCLM F g f f' = f (SchwartzMap.smulLeftCLM Complex g f')
参数：g : E -> Complex；f : 𝓢'(E, F)；f' : 𝓢(E, Complex)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smulLeftCLM_apply_apply (g : E → ℂ) (f : 𝓢'(E, F)) (f' : 𝓢(E, ℂ)) :
    smulLeftCLM F g f f' = f (SchwartzMap.smulLeftCLM ℂ g f') := by
  rfl

@[simp]
/-
**TemperedDistribution.smulLeftCLM_const** 是 Mathlib 中的一个定理，位于命名空间 `TemperedDist
ribution`。
形式化陈述：smulLeftCLM_const (c : Complex) (f : 𝓢'(E, F)) : smulLeftCLM F (fun _ : E 
=> c) f = c • f
参数：c : Complex；f : 𝓢'(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformConvergenceCLM.ext`：ext [TopologicalSpace F] {𝔖 : Set (Set E)} {f
 g : E ->SLᵤ[σ, 𝔖] F} (h : forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Real.isScalarTower`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousSMul ℝ E]   [T2Space 
E] {A : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `TemperedDistribution.smulLeftCLM_apply_apply`：smulLeftCLM_apply_apply (g
 : E -> Complex) (f : 𝓢'(E, F)) (f' : 𝓢(E, Complex)) : smulLeftCLM F g f f' = f 
(SchwartzMap.smulLeftCLM Complex g…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SchwartzMap.smulLeftCLM_const`：smulLeftCLM_const (c : 𝕜) : smulLeftCLM F
 (fun (_ : E) => c) = c • ContinuousLinearMap.id 𝕜 _
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `UniformConvergenceCLM.instIsSMulApply`：∀ {𝕜₁ : Type u_1} {𝕜₂ : Type u_2}
 [inst : NormedField 𝕜₁] [inst_1 : NormedField 𝕜₂] (σ : 𝕜₁ →+* 𝕜₂) {E : Type u_3
}   (F : Type u_4) [inst_2 …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smulLeftCLM_const (c : ℂ) (f : 𝓢'(E, F)) : smulLeftCLM F (fun _ : E ↦ c) f = c • f := by
  ext1; simp

@[simp]
/-
**TemperedDistribution.smulLeftCLM_smulLeftCLM_apply** 是 Mathlib 中的一个定理，位于命名空间 `
TemperedDistribution`。
形式化陈述：smulLeftCLM_smulLeftCLM_apply {g₁ g₂ : E -> Complex} (hg₁ : g₁.HasTemperat
eGrowth) (hg₂ : g₂.HasTemperateGrowth) (f : 𝓢'(E, F)) : smulLeftCLM F g₂ (smulLe
ftCLM F g₁ f) = smulLeftCLM F (g₁ * g₂) f
参数：hg₁ : g₁.HasTemperateGrowth；hg₂ : g₂.HasTemperateGrowth；f : 𝓢'(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformConvergenceCLM.ext`：ext [TopologicalSpace F] {𝔖 : Set (Set E)} {f
 g : E ->SLᵤ[σ, 𝔖] F} (h : forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Real.isScalarTower`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousSMul ℝ E]   [T2Space 
E] {A : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TemperedDistribution.smulLeftCLM_apply_apply`：smulLeftCLM_apply_apply (g
 : E -> Complex) (f : 𝓢'(E, F)) (f' : 𝓢(E, Complex)) : smulLeftCLM F g f f' = f 
(SchwartzMap.smulLeftCLM Complex g…
· 使用定理 `SchwartzMap.smulLeftCLM_smulLeftCLM_apply`：smulLeftCLM_smulLeftCLM_apply
 {g₁ g₂ : E -> 𝕜} (hg₁ : g₁.HasTemperateGrowth) (hg₂ : g₂.HasTemperateGrowth) (f
 : 𝓢(E, F)) : smulLeftCLM F g₁ …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smulLeftCLM_smulLeftCLM_apply {g₁ g₂ : E → ℂ} (hg₁ : g₁.HasTemperateGrowth)
    (hg₂ : g₂.HasTemperateGrowth) (f : 𝓢'(E, F)) :
    smulLeftCLM F g₂ (smulLeftCLM F g₁ f) = smulLeftCLM F (g₁ * g₂) f := by
  ext; simp [hg₁, hg₂]
/-
**TemperedDistribution.smulLeftCLM_compL_smulLeftCLM** 是 Mathlib 中的一个定理，位于命名空间 `
TemperedDistribution`。
形式化陈述：smulLeftCLM_compL_smulLeftCLM {g₁ g₂ : E -> Complex} (hg₁ : g₁.HasTemperat
eGrowth) (hg₂ : g₂.HasTemperateGrowth) : smulLeftCLM F g₂ ∘L smulLeftCLM F g₁ = 
smulLeftCLM F (g₁ * g₂)
参数：hg₁ : g₁.HasTemperateGrowth；hg₂ : g₂.HasTemperateGrowth。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TemperedDistribution.smulLeftCLM_smulLeftCLM_apply`：smulLeftCLM_smulLeft
CLM_apply {g₁ g₂ : E -> Complex} (hg₁ : g₁.HasTemperateGrowth) (hg₂ : g₂.HasTemp
erateGrowth) (f : 𝓢'(E, F)) : smulLeftCL…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smulLeftCLM_compL_smulLeftCLM {g₁ g₂ : E → ℂ} (hg₁ : g₁.HasTemperateGrowth)
    (hg₂ : g₂.HasTemperateGrowth) :
    smulLeftCLM F g₂ ∘L smulLeftCLM F g₁ = smulLeftCLM F (g₁ * g₂) := by
  ext1 f
  simp [hg₁, hg₂]
/-
**TemperedDistribution.smulLeftCLM_smul** 是 Mathlib 中的一个定理，位于命名空间 `TemperedDistr
ibution`。
形式化陈述：smulLeftCLM_smul {g : E -> Complex} (hg : g.HasTemperateGrowth) (c : Compl
ex) : smulLeftCLM F (c • g) = c • smulLeftCLM F g
参数：hg : g.HasTemperateGrowth；c : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `UniformConvergenceCLM.ext`：ext [TopologicalSpace F] {𝔖 : Set (Set E)} {f
 g : E ->SLᵤ[σ, 𝔖] F} (h : forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Real.isScalarTower`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousSMul ℝ E]   [T2Space 
E] {A : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TemperedDistribution.smulLeftCLM_apply_apply`：smulLeftCLM_apply_apply (g
 : E -> Complex) (f : 𝓢'(E, F)) (f' : 𝓢(E, Complex)) : smulLeftCLM F g f f' = f 
(SchwartzMap.smulLeftCLM Complex g…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SchwartzMap.smulLeftCLM_smul`：smulLeftCLM_smul {g : E -> 𝕜} (hg : g.HasT
emperateGrowth) (c : 𝕜) : smulLeftCLM F (c • g) = c • smulLeftCLM F g
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `UniformConvergenceCLM.instIsSMulApply`：∀ {𝕜₁ : Type u_1} {𝕜₂ : Type u_2}
 [inst : NormedField 𝕜₁] [inst_1 : NormedField 𝕜₂] (σ : 𝕜₁ →+* 𝕜₂) {E : Type u_3
}   (F : Type u_4) [inst_2 …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smulLeftCLM_smul {g : E → ℂ} (hg : g.HasTemperateGrowth) (c : ℂ) :
    smulLeftCLM F (c • g) = c • smulLeftCLM F g := by
  ext f u
  simp [SchwartzMap.smulLeftCLM_smul hg]
/-
**TemperedDistribution.smulLeftCLM_add** 是 Mathlib 中的一个定理，位于命名空间 `TemperedDistri
bution`。
形式化陈述：smulLeftCLM_add {g₁ g₂ : E -> Complex} (hg₁ : g₁.HasTemperateGrowth) (hg₂ 
: g₂.HasTemperateGrowth) : smulLeftCLM F (g₁ + g₂) = smulLeftCLM F g₁ + smulLeft
CLM F g₂
参数：hg₁ : g₁.HasTemperateGrowth；hg₂ : g₂.HasTemperateGrowth。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformConvergenceCLM.ext`：ext [TopologicalSpace F] {𝔖 : Set (Set E)} {f
 g : E ->SLᵤ[σ, 𝔖] F} (h : forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Real.isScalarTower`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousSMul ℝ E]   [T2Space 
E] {A : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TemperedDistribution.smulLeftCLM_apply_apply`：smulLeftCLM_apply_apply (g
 : E -> Complex) (f : 𝓢'(E, F)) (f' : 𝓢(E, Complex)) : smulLeftCLM F g f f' = f 
(SchwartzMap.smulLeftCLM Complex g…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SchwartzMap.smulLeftCLM_add`：smulLeftCLM_add {g₁ g₂ : E -> 𝕜} (hg₁ : g₁.
HasTemperateGrowth) (hg₂ : g₂.HasTemperateGrowth) : smulLeftCLM F (g₁ + g₂) = sm
ulLeftCLM F g₁ + …
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `UniformConvergenceCLM.instIsAddApply`：∀ {𝕜₁ : Type u_1} {𝕜₂ : Type u_2} 
[inst : NormedField 𝕜₁] [inst_1 : NormedField 𝕜₂] (σ : 𝕜₁ →+* 𝕜₂) {E : Type u_3}
   (F : Type u_4) [inst_2 …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smulLeftCLM_add {g₁ g₂ : E → ℂ} (hg₁ : g₁.HasTemperateGrowth)
    (hg₂ : g₂.HasTemperateGrowth) :
    smulLeftCLM F (g₁ + g₂) = smulLeftCLM F g₁ + smulLeftCLM F g₂ := by
  ext f u
  simp [SchwartzMap.smulLeftCLM_add hg₁ hg₂]
/-
**TemperedDistribution.smulLeftCLM_sub** 是 Mathlib 中的一个定理，位于命名空间 `TemperedDistri
bution`。
形式化陈述：smulLeftCLM_sub {g₁ g₂ : E -> Complex} (hg₁ : g₁.HasTemperateGrowth) (hg₂ 
: g₂.HasTemperateGrowth) : smulLeftCLM F (g₁ - g₂) = smulLeftCLM F g₁ - smulLeft
CLM F g₂
参数：hg₁ : g₁.HasTemperateGrowth；hg₂ : g₂.HasTemperateGrowth。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `UniformConvergenceCLM.ext`：ext [TopologicalSpace F] {𝔖 : Set (Set E)} {f
 g : E ->SLᵤ[σ, 𝔖] F} (h : forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Real.isScalarTower`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousSMul ℝ E]   [T2Space 
E] {A : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TemperedDistribution.smulLeftCLM_apply_apply`：smulLeftCLM_apply_apply (g
 : E -> Complex) (f : 𝓢'(E, F)) (f' : 𝓢(E, Complex)) : smulLeftCLM F g f f' = f 
(SchwartzMap.smulLeftCLM Complex g…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SchwartzMap.smulLeftCLM_sub`：smulLeftCLM_sub {g₁ g₂ : E -> 𝕜} (hg₁ : g₁.
HasTemperateGrowth) (hg₂ : g₂.HasTemperateGrowth) : smulLeftCLM F (g₁ - g₂) = sm
ulLeftCLM F g₁ - …
· 使用定理 `sub_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Sub β}   {inst_2 : Sub F} [self : IsSu…
· 使用定理 `ContinuousLinearMap.instIsSubApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `UniformConvergenceCLM.instIsSubApply`：∀ {𝕜₁ : Type u_1} {𝕜₂ : Type u_2} 
[inst : NormedField 𝕜₁] [inst_1 : NormedField 𝕜₂] (σ : 𝕜₁ →+* 𝕜₂) {E : Type u_3}
   (F : Type u_4) [inst_2 …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smulLeftCLM_sub {g₁ g₂ : E → ℂ} (hg₁ : g₁.HasTemperateGrowth)
    (hg₂ : g₂.HasTemperateGrowth) :
    smulLeftCLM F (g₁ - g₂) = smulLeftCLM F g₁ - smulLeftCLM F g₂ := by
  ext f u
  simp [SchwartzMap.smulLeftCLM_sub hg₁ hg₂]
/-
**TemperedDistribution.smulLeftCLM_neg** 是 Mathlib 中的一个定理，位于命名空间 `TemperedDistri
bution`。
形式化陈述：smulLeftCLM_neg {g : E -> Complex} (hg : g.HasTemperateGrowth) : smulLeftC
LM F (-g) = -smulLeftCLM F g
参数：hg : g.HasTemperateGrowth。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `UniformConvergenceCLM.ext`：ext [TopologicalSpace F] {𝔖 : Set (Set E)} {f
 g : E ->SLᵤ[σ, 𝔖] F} (h : forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Real.isScalarTower`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousSMul ℝ E]   [T2Space 
E] {A : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TemperedDistribution.smulLeftCLM_apply_apply`：smulLeftCLM_apply_apply (g
 : E -> Complex) (f : 𝓢'(E, F)) (f' : 𝓢(E, Complex)) : smulLeftCLM F g f f' = f 
(SchwartzMap.smulLeftCLM Complex g…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SchwartzMap.smulLeftCLM_neg`：smulLeftCLM_neg {g : E -> 𝕜} (hg : g.HasTem
perateGrowth) : smulLeftCLM F (-g) = -smulLeftCLM F g
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `ContinuousLinearMap.instIsNegApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `UniformConvergenceCLM.instIsNegApply`：∀ {𝕜₁ : Type u_1} {𝕜₂ : Type u_2} 
[inst : NormedField 𝕜₁] [inst_1 : NormedField 𝕜₂] (σ : 𝕜₁ →+* 𝕜₂) {E : Type u_3}
   (F : Type u_4) [inst_2 …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smulLeftCLM_neg {g : E → ℂ} (hg : g.HasTemperateGrowth) :
    smulLeftCLM F (-g) = -smulLeftCLM F g := by
  ext f u
  simp [SchwartzMap.smulLeftCLM_neg hg]
/-
**TemperedDistribution.smulLeftCLM_sum** 是 Mathlib 中的一个定理，位于命名空间 `TemperedDistri
bution`。
形式化陈述：smulLeftCLM_sum {g : ι -> E -> Complex} {s : Finset ι} (hg : forall i in s
, (g i).HasTemperateGrowth) : smulLeftCLM F (fun x => ∑ i in s, g i x) = ∑ i in 
s, smulLeftCLM F (g i)
参数：hg : forall i in s, (g i).HasTemperateGrowth。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformConvergenceCLM.ext`：ext [TopologicalSpace F] {𝔖 : Set (Set E)} {f
 g : E ->SLᵤ[σ, 𝔖] F} (h : forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Real.isScalarTower`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousSMul ℝ E]   [T2Space 
E] {A : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TemperedDistribution.smulLeftCLM_apply_apply`：smulLeftCLM_apply_apply (g
 : E -> Complex) (f : 𝓢'(E, F)) (f' : 𝓢(E, Complex)) : smulLeftCLM F g f f' = f 
(SchwartzMap.smulLeftCLM Complex g…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SchwartzMap.smulLeftCLM_sum`：smulLeftCLM_sum {g : ι -> E -> 𝕜} {s : Fins
et ι} (hg : forall i in s, (g i).HasTemperateGrowth) : smulLeftCLM F (fun x => ∑
 i in s, g i x) =…
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `UniformConvergenceCLM.instIsZeroApply`：∀ {𝕜₁ : Type u_1} {𝕜₂ : Type u_2}
 [inst : NormedField 𝕜₁] [inst_1 : NormedField 𝕜₂] (σ : 𝕜₁ →+* 𝕜₂) {E : Type u_3
}   (F : Type u_4) [inst_2 …
· 使用定理 `UniformConvergenceCLM.instIsAddApply`：∀ {𝕜₁ : Type u_1} {𝕜₂ : Type u_2} 
[inst : NormedField 𝕜₁] [inst_1 : NormedField 𝕜₂] (σ : 𝕜₁ →+* 𝕜₂) {E : Type u_3}
   (F : Type u_4) [inst_2 …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smulLeftCLM_sum {g : ι → E → ℂ} {s : Finset ι} (hg : ∀ i ∈ s, (g i).HasTemperateGrowth) :
    smulLeftCLM F (fun x ↦ ∑ i ∈ s, g i x) = ∑ i ∈ s, smulLeftCLM F (g i) := by
  ext f u
  simp [SchwartzMap.smulLeftCLM_sum hg]

end TVS

open ENNReal MeasureTheory

variable [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [hμ : μ.HasTemperateGrowth]

/-- Coercion of the product of two `Lp` functions to a tempered distribution is equal to the left
multiplication if the left factor is a function of temperate growth. -/
/-
**TemperedDistribution._root_.MeasureTheory.Lp.toTemperedDistribution_smul_eq** 
是 Mathlib 中的一个定理，位于命名空间 `TemperedDistribution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion of the product of two `Lp` functions to a tempered distribution is equa
l to the left
multiplication if the left factor is a function of temperate growth.
-/
theorem _root_.MeasureTheory.Lp.toTemperedDistribution_smul_eq {p q r : ℝ≥0∞} [p.HolderTriple q r]
    [Fact (1 ≤ q)] [Fact (1 ≤ r)] {g : E → ℂ} (hg₁ : g.HasTemperateGrowth) (hg₂ : MemLp g p μ)
    (f : Lp F q μ) :
    ((hg₂.toLp _) • f : Lp F r μ) = smulLeftCLM F g f := by
  ext u
  simp only [Lp.toTemperedDistribution_apply, smulLeftCLM_apply_apply]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_lpSMul (r := r) (hg₂.toLp _) f, hg₂.coeFn_toLp] with x hg hg'
  simp [hg, hg', hg₁, smul_smul, mul_comm]

end Multiplication

/-! ### Derivatives -/

section deriv

section TVS

variable [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousConstSMul ℂ F]

variable (F) in
/-- The 1-dimensional derivative on tempered distribution as a continuous `ℂ`-linear map. -/
/-
**TemperedDistribution.derivCLM** 是 Mathlib 中的一个定义，位于命名空间 `TemperedDistribution`
。
形式化陈述：derivCLM : 𝓢'(Real, F) ->L[Complex] 𝓢'(Real, F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The 1-dimensional derivative on tempered distribution as a continuous `ℂ`-linear
 map.
-/
def derivCLM : 𝓢'(ℝ, F) →L[ℂ] 𝓢'(ℝ, F) :=
  PointwiseConvergenceCLM.precomp F (-SchwartzMap.derivCLM ℂ ℂ)

@[simp]
/-
**TemperedDistribution.derivCLM_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `TemperedD
istribution`。
形式化陈述：derivCLM_apply_apply (f : 𝓢'(Real, F)) (g : 𝓢(Real, Complex)) : derivCLM F
 f g = f (-SchwartzMap.derivCLM Complex Complex g)
参数：f : 𝓢'(Real, F)；g : 𝓢(Real, Complex)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem derivCLM_apply_apply (f : 𝓢'(ℝ, F)) (g : 𝓢(ℝ, ℂ)) :
    derivCLM F f g = f (-SchwartzMap.derivCLM ℂ ℂ g) := rfl

end TVS

variable [RCLike 𝕜] [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace 𝕜 F]

variable (𝕜) in
/-
**TemperedDistribution.derivCLM_toTemperedDistributionCLM_eq** 是 Mathlib 中的一个定理，
位于命名空间 `TemperedDistribution`。
形式化陈述：derivCLM_toTemperedDistributionCLM_eq (f : 𝓢(Real, F)) : derivCLM F (f : 𝓢
'(Real, F)) = SchwartzMap.derivCLM 𝕜 F f
参数：f : 𝓢(Real, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformConvergenceCLM.ext`：ext [TopologicalSpace F] {𝔖 : Set (Set E)} {f
 g : E ->SLᵤ[σ, 𝔖] F} (h : forall x, f x = g x) : f = g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.instHasTemperateGrowth`：∀ {E : Ty
pe u_5} [inst : NormedAddCommGroup E] [inst_1 : MeasurableSpace E] [inst_2 : Nor
medSpace ℝ E]   [FiniteDimensional ℝ E] [BorelSpace…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Real.isScalarTower`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousSMul ℝ E]   [T2Space 
E] {A : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `SchwartzMap.toTemperedDistributionCLM_apply_apply`：toTemperedDistributio
nCLM_apply_apply (μ : Measure E
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `SchwartzMap.instIsNegApply`：∀ {E : Type u_5} {F : Type u_6} [inst : Norm
edAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [
inst_3 : NormedS…
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `MeasureTheory.integral_neg`：integral_neg (f : α -> G) : ∫ a, -f a ∂μ = -
∫ a, f a ∂μ
· 使用定理 `SchwartzMap.integral_smul_deriv_right_eq_neg_left`：integral_smul_deriv_r
ight_eq_neg_left (f : 𝓢(Real, 𝕜)) (g : 𝓢(Real, F)) : ∫ (x : Real), f x • deriv g
 x = -∫ (x : Real), deriv f x • g x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem derivCLM_toTemperedDistributionCLM_eq (f : 𝓢(ℝ, F)) :
    derivCLM F (f : 𝓢'(ℝ, F)) = SchwartzMap.derivCLM 𝕜 F f := by
  ext1 g
  simp [integral_smul_deriv_right_eq_neg_left, integral_neg]

end deriv

section lineDeriv

open LineDeriv

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

section TVS

variable [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousConstSMul ℂ F]

/-- The partial derivative (or directional derivative) in the direction `m : E` as a
continuous linear map on tempered distributions. -/
/-
**TemperedDistribution.instLineDeriv** 是 Mathlib 中的一个实例，位于命名空间 `TemperedDistribu
tion`。
形式化陈述：instLineDeriv : LineDeriv E 𝓢'(E, F) 𝓢'(E, F) where lineDerivOp m
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The partial derivative (or directional derivative) in the direction `m : E` as a
continuous linear map on tempered distributions.
-/
instance instLineDeriv : LineDeriv E 𝓢'(E, F) 𝓢'(E, F) where
  lineDerivOp m := PointwiseConvergenceCLM.precomp F (-lineDerivOpCLM ℂ 𝓢(E, ℂ) m)

@[simp]
/-
**TemperedDistribution.lineDerivOp_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `Temper
edDistribution`。
形式化陈述：lineDerivOp_apply_apply (f : 𝓢'(E, F)) (g : 𝓢(E, Complex)) (m : E) : ∂_{m}
 f g = f (- ∂_{m} g)
参数：f : 𝓢'(E, F)；g : 𝓢(E, Complex)；m : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lineDerivOp_apply_apply (f : 𝓢'(E, F)) (g : 𝓢(E, ℂ)) (m : E) :
    ∂_{m} f g = f (- ∂_{m} g) := rfl
/-
**TemperedDistribution.** 是 Mathlib 中的一个实例，位于命名空间 `TemperedDistribution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LineDerivAdd E 𝓢'(E, F) 𝓢'(E, F) where
  lineDerivOp_add m := (PointwiseConvergenceCLM.precomp F (-lineDerivOpCLM ℂ 𝓢(E, ℂ) m)).map_add
  lineDerivOp_left_add x y f := by
    ext u
    simp [lineDerivOp_left_add, add_comm]
/-
**TemperedDistribution.** 是 Mathlib 中的一个实例，位于命名空间 `TemperedDistribution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LineDerivSMul ℂ E 𝓢'(E, F) 𝓢'(E, F) where
  lineDerivOp_smul m := (PointwiseConvergenceCLM.precomp F (-lineDerivOpCLM ℂ 𝓢(E, ℂ) m)).map_smul
/-
**TemperedDistribution.** 是 Mathlib 中的一个实例，位于命名空间 `TemperedDistribution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LineDerivSMul ℝ E 𝓢'(E, F) 𝓢'(E, F) where
  lineDerivOp_smul m :=
    (PointwiseConvergenceCLM.precomp F (-lineDerivOpCLM ℂ 𝓢(E, ℂ) m)).map_smul_of_tower
/-
**TemperedDistribution.** 是 Mathlib 中的一个实例，位于命名空间 `TemperedDistribution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ContinuousLineDeriv E 𝓢'(E, F) 𝓢'(E, F) where
  continuous_lineDerivOp m :=
    (PointwiseConvergenceCLM.precomp F (-lineDerivOpCLM ℂ 𝓢(E, ℂ) m)).continuous
/-
**TemperedDistribution.lineDerivOpCLM_eq** 是 Mathlib 中的一个定理，位于命名空间 `TemperedDist
ribution`。
形式化陈述：lineDerivOpCLM_eq (m : E) : lineDerivOpCLM Complex 𝓢'(E, F) m = PointwiseC
onvergenceCLM.precomp F (-lineDerivOpCLM Complex 𝓢(E, Complex) m)
参数：m : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TemperedDistribution.instLineDerivAdd`：∀ {E : Type u_3} {F : Type u_4} [
inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : AddCommGroup F
]   [inst_3 : _root_.Module…
· 使用定理 `TemperedDistribution.instLineDerivSMulComplex`：∀ {E : Type u_3} {F : Typ
e u_4} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : AddCom
mGroup F]   [inst_3 : _root_.Module…
· 使用定理 `TemperedDistribution.instContinuousLineDeriv`：∀ {E : Type u_3} {F : Type
 u_4} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : AddComm
Group F]   [inst_3 : _root_.Module…
-/
theorem lineDerivOpCLM_eq (m : E) : lineDerivOpCLM ℂ 𝓢'(E, F) m =
  PointwiseConvergenceCLM.precomp F (-lineDerivOpCLM ℂ 𝓢(E, ℂ) m) := rfl

end TVS

variable [NormedAddCommGroup F] [NormedSpace ℂ F]

set_option backward.isDefEq.respectTransparency false in
/-
**TemperedDistribution.** 是 Mathlib 中的一个实例，位于命名空间 `TemperedDistribution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LineDerivLeftSMul ℝ E 𝓢'(E, F) 𝓢'(E, F) where
  lineDerivOp_left_smul r x f := by
    ext u
    simp [lineDerivOp_left_smul, map_smul_of_tower f]

variable
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
  {μ : Measure E} [μ.IsAddHaarMeasure]
/-
**TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq** 是 Mathlib 中的一个
定理，位于命名空间 `TemperedDistribution`。
形式化陈述：lineDerivOp_toTemperedDistributionCLM_eq (f : 𝓢(E, F)) (m : E) : ∂_{m} (to
TemperedDistributionCLM E F μ f) = toTemperedDistributionCLM E F μ (∂_{m} f)
参数：f : 𝓢(E, F)；m : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformConvergenceCLM.ext`：ext [TopologicalSpace F] {𝔖 : Set (Set E)} {f
 g : E ->SLᵤ[σ, 𝔖] F} (h : forall x, f x = g x) : f = g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.instHasTemperateGrowth`：∀ {E : Ty
pe u_5} [inst : NormedAddCommGroup E] [inst_1 : MeasurableSpace E] [inst_2 : Nor
medSpace ℝ E]   [FiniteDimensional ℝ E] [BorelSpace…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SchwartzMap.toTemperedDistributionCLM_apply_apply`：toTemperedDistributio
nCLM_apply_apply (μ : Measure E
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `SchwartzMap.instIsNegApply`：∀ {E : Type u_5} {F : Type u_6} [inst : Norm
edAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [
inst_3 : NormedS…
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `MeasureTheory.integral_neg`：integral_neg (f : α -> G) : ∫ a, -f a ∂μ = -
∫ a, f a ∂μ
· 使用定理 `SchwartzMap.integral_smul_lineDerivOp_right_eq_neg_left`：integral_smul_l
ineDerivOp_right_eq_neg_left (f : 𝓢(D, 𝕜)) (g : 𝓢(D, F)) (v : D) : ∫ (x : D), f 
x • ∂_{v} g x ∂μ = -∫ (x : D), ∂_{v} f x • g …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lineDerivOp_toTemperedDistributionCLM_eq (f : 𝓢(E, F)) (m : E) :
    ∂_{m} (toTemperedDistributionCLM E F μ f) = toTemperedDistributionCLM E F μ (∂_{m} f) := by
  ext1 g
  simp [integral_smul_lineDerivOp_right_eq_neg_left g f, integral_neg]

end lineDeriv

/-! ### Laplacian-/

section Laplacian

open Laplacian LineDeriv
open scoped SchwartzMap

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section TVS

variable [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousConstSMul ℂ F]

/-
**TemperedDistribution.** 是 Mathlib 中的一个实例，位于命名空间 `TemperedDistribution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Laplacian 𝓢'(E, F) 𝓢'(E, F) where
  laplacian := LineDeriv.laplacianCLM ℝ E 𝓢'(E, F)

@[simp]
/-
**TemperedDistribution.laplacianCLM_apply** 是 Mathlib 中的一个定理，位于命名空间 `TemperedDis
tribution`。
形式化陈述：laplacianCLM_apply (f : 𝓢'(E, F)) : laplacianCLM Complex E 𝓢'(E, F) f = Δ 
f
参数：f : 𝓢'(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `TemperedDistribution.instLineDerivAdd`：∀ {E : Type u_3} {F : Type u_4} [
inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : AddCommGroup F
]   [inst_3 : _root_.Module…
· 使用定理 `TemperedDistribution.instLineDerivSMulComplex`：∀ {E : Type u_3} {F : Typ
e u_4} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : AddCom
mGroup F]   [inst_3 : _root_.Module…
· 使用定理 `TemperedDistribution.instContinuousLineDeriv`：∀ {E : Type u_3} {F : Type
 u_4} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : AddComm
Group F]   [inst_3 : _root_.Module…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem laplacianCLM_apply (f : 𝓢'(E, F)) : laplacianCLM ℂ E 𝓢'(E, F) f = Δ f := by
  simp [laplacianCLM, laplacian]

end TVS

variable [NormedAddCommGroup F] [NormedSpace ℂ F]

/-
**TemperedDistribution.laplacian_eq_sum** 是 Mathlib 中的一个定理，位于命名空间 `TemperedDistr
ibution`。
形式化陈述：laplacian_eq_sum [Fintype ι] (b : OrthonormalBasis ι Real E) (f : 𝓢'(E, F)
) : Δ f = ∑ i, ∂_{b i} (∂_{b i} f)
参数：b : OrthonormalBasis ι Real E；f : 𝓢'(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LineDeriv.laplacianCLM_eq_sum`：laplacianCLM_eq_sum [Fintype ι] (v : Orth
onormalBasis ι Real E) (f : V₁) : laplacianCLM Real E V₁ f = ∑ i, ∂_{v i} (∂_{v 
i} f)
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `TemperedDistribution.instLineDerivAdd`：∀ {E : Type u_3} {F : Type u_4} [
inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : AddCommGroup F
]   [inst_3 : _root_.Module…
· 使用定理 `TemperedDistribution.instLineDerivSMulReal`：∀ {E : Type u_3} {F : Type u
_4} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : AddCommGr
oup F]   [inst_3 : _root_.Module…
· 使用定理 `TemperedDistribution.instContinuousLineDeriv`：∀ {E : Type u_3} {F : Type
 u_4} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : AddComm
Group F]   [inst_3 : _root_.Module…
· 使用定理 `TemperedDistribution.instLineDerivLeftSMulReal`：∀ {E : Type u_3} {F : Ty
pe u_4} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : Norme
dAddCommGroup F]   [inst_3 : NormedS…
-/
theorem laplacian_eq_sum [Fintype ι] (b : OrthonormalBasis ι ℝ E) (f : 𝓢'(E, F)) :
    Δ f = ∑ i, ∂_{b i} (∂_{b i} f) := LineDeriv.laplacianCLM_eq_sum b f

@[simp]
/-
**TemperedDistribution.laplacian_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `Tempered
Distribution`。
形式化陈述：laplacian_apply_apply (f : 𝓢'(E, F)) (u : 𝓢(E, Complex)) : (Δ f) u = f (Δ 
u)
参数：f : 𝓢'(E, F)；u : 𝓢(E, Complex)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TemperedDistribution.laplacian_eq_sum`：laplacian_eq_sum [Fintype ι] (b :
 OrthonormalBasis ι Real E) (f : 𝓢'(E, F)) : Δ f = ∑ i, ∂_{b i} (∂_{b i} f)
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `UniformConvergenceCLM.instIsZeroApply`：∀ {𝕜₁ : Type u_1} {𝕜₂ : Type u_2}
 [inst : NormedField 𝕜₁] [inst_1 : NormedField 𝕜₂] (σ : 𝕜₁ →+* 𝕜₂) {E : Type u_3
}   (F : Type u_4) [inst_2 …
· 使用定理 `UniformConvergenceCLM.instIsAddApply`：∀ {𝕜₁ : Type u_1} {𝕜₂ : Type u_2} 
[inst : NormedField 𝕜₁] [inst_1 : NormedField 𝕜₂] (σ : 𝕜₁ →+* 𝕜₂) {E : Type u_3}
   (F : Type u_4) [inst_2 …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `SchwartzMap.laplacian_eq_sum`：laplacian_eq_sum [Fintype ι] (b : Orthonor
malBasis ι Real E) (f : 𝓢(E, F)) : Δ f = ∑ i, ∂_{b i} (∂_{b i} f)
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem laplacian_apply_apply (f : 𝓢'(E, F)) (u : 𝓢(E, ℂ)) : (Δ f) u = f (Δ u) := by
  simp [laplacian_eq_sum (stdOrthonormalBasis ℝ E),
    SchwartzMap.laplacian_eq_sum (stdOrthonormalBasis ℝ E), map_neg, neg_neg]

variable [MeasurableSpace E] [BorelSpace E]

/-- The distributional Laplacian and the classical Laplacian coincide on `𝓢(E, F)`. -/
@[simp]
/-
**TemperedDistribution.laplacian_toTemperedDistributionCLM_eq** 是 Mathlib 中的一个定理
，位于命名空间 `TemperedDistribution`。
形式化陈述：laplacian_toTemperedDistributionCLM_eq (f : 𝓢(E, F)) : Δ (f : 𝓢'(E, F)) = 
Δ f
参数：f : 𝓢(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformConvergenceCLM.ext`：ext [TopologicalSpace F] {𝔖 : Set (Set E)} {f
 g : E ->SLᵤ[σ, 𝔖] F} (h : forall x, f x = g x) : f = g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.instHasTemperateGrowth`：∀ {E : Ty
pe u_5} [inst : NormedAddCommGroup E] [inst_1 : MeasurableSpace E] [inst_2 : Nor
medSpace ℝ E]   [FiniteDimensional ℝ E] [BorelSpace…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TemperedDistribution.laplacian_apply_apply`：laplacian_apply_apply (f : 𝓢
'(E, F)) (u : 𝓢(E, Complex)) : (Δ f) u = f (Δ u)
· 使用定理 `SchwartzMap.toTemperedDistributionCLM_apply_apply`：toTemperedDistributio
nCLM_apply_apply (μ : Measure E
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `SchwartzMap.integral_smul_laplacian_right_eq_left`：integral_smul_laplaci
an_right_eq_left (f : 𝓢(E, 𝕜)) (g : 𝓢(E, F)) : ∫ x, f x • Δ g x ∂μ = ∫ x, Δ f x 
• g x ∂μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The distributional Laplacian and the classical Laplacian coincide on `𝓢(E, F)`.
-/
theorem laplacian_toTemperedDistributionCLM_eq (f : 𝓢(E, F)) :
    Δ (f : 𝓢'(E, F)) = Δ f := by
  ext u
  simp [SchwartzMap.integral_smul_laplacian_right_eq_left]

end Laplacian

/-! ### Fourier transform -/

section Fourier

open FourierTransform

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

section TVS

variable [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousConstSMul ℂ F]

/-
**TemperedDistribution.instFourierTransform** 是 Mathlib 中的一个实例，位于命名空间 `TemperedD
istribution`。
形式化陈述：instFourierTransform : FourierTransform 𝓢'(E, F) 𝓢'(E, F) where fourier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFourierTransform : FourierTransform 𝓢'(E, F) 𝓢'(E, F) where
  fourier := PointwiseConvergenceCLM.precomp F (fourierCLM ℂ 𝓢(E, ℂ))
/-
**TemperedDistribution.instFourierAdd** 是 Mathlib 中的一个实例，位于命名空间 `TemperedDistrib
ution`。
形式化陈述：instFourierAdd : FourierAdd 𝓢'(E, F) 𝓢'(E, F) where fourier_add
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.map_add`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : S
emiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_2 :
 TopologicalSpace…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
instance instFourierAdd : FourierAdd 𝓢'(E, F) 𝓢'(E, F) where
  fourier_add := (PointwiseConvergenceCLM.precomp F (fourierCLM ℂ 𝓢(E, ℂ))).map_add
/-
**TemperedDistribution.instFourierSMul** 是 Mathlib 中的一个实例，位于命名空间 `TemperedDistri
bution`。
形式化陈述：instFourierSMul : FourierSMul Complex 𝓢'(E, F) 𝓢'(E, F) where fourier_smul
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.map_smul`：∀ {R₁ : Type u_1} [inst : Semiring R₁] {M₁
 : Type u_4} [inst_1 : TopologicalSpace M₁] [inst_2 : AddCommMonoid M₁]   {M₂ : 
Type u_6} [inst_3 …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
instance instFourierSMul : FourierSMul ℂ 𝓢'(E, F) 𝓢'(E, F) where
  fourier_smul := (PointwiseConvergenceCLM.precomp F (fourierCLM ℂ 𝓢(E, ℂ))).map_smul
/-
**TemperedDistribution.instContinuousFourier** 是 Mathlib 中的一个实例，位于命名空间 `Tempered
Distribution`。
形式化陈述：instContinuousFourier : ContinuousFourier 𝓢'(E, F) 𝓢'(E, F) where continuo
us_fourier
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.cont`：∀ {R : Type u_1} {S : Type u_2} [inst : Semiri
ng R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_3}   [inst_2 : Topological
Space M] [inst…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
instance instContinuousFourier : ContinuousFourier 𝓢'(E, F) 𝓢'(E, F) where
  continuous_fourier := (PointwiseConvergenceCLM.precomp F (fourierCLM ℂ 𝓢(E, ℂ))).cont

@[simp]
/-
**TemperedDistribution.fourier_apply** 是 Mathlib 中的一个定理，位于命名空间 `TemperedDistribu
tion`。
形式化陈述：fourier_apply (f : 𝓢'(E, F)) (g : 𝓢(E, Complex)) : 𝓕 f g = f (𝓕 g)
参数：f : 𝓢'(E, F)；g : 𝓢(E, Complex)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fourier_apply (f : 𝓢'(E, F)) (g : 𝓢(E, ℂ)) : 𝓕 f g = f (𝓕 g) := rfl

@[deprecated (since := "2026-01-06")]
alias fourierTransformCLM := FourierTransform.fourierCLM

@[deprecated (since := "2026-01-06")]
alias fourierTransformCLM_apply := FourierTransform.fourierCLM_apply

@[deprecated (since := "2026-01-06")]
alias fourierTransform_apply := fourier_apply
/-
**TemperedDistribution.instFourierTransformInv** 是 Mathlib 中的一个实例，位于命名空间 `Temper
edDistribution`。
形式化陈述：instFourierTransformInv : FourierTransformInv 𝓢'(E, F) 𝓢'(E, F) where four
ierInv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFourierTransformInv : FourierTransformInv 𝓢'(E, F) 𝓢'(E, F) where
  fourierInv := PointwiseConvergenceCLM.precomp F (fourierInvCLM ℂ 𝓢(E, ℂ))
/-
**TemperedDistribution.instFourierInvAdd** 是 Mathlib 中的一个实例，位于命名空间 `TemperedDist
ribution`。
形式化陈述：instFourierInvAdd : FourierInvAdd 𝓢'(E, F) 𝓢'(E, F) where fourierInv_add
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.map_add`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : S
emiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_2 :
 TopologicalSpace…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
instance instFourierInvAdd : FourierInvAdd 𝓢'(E, F) 𝓢'(E, F) where
  fourierInv_add := (PointwiseConvergenceCLM.precomp F (fourierInvCLM ℂ 𝓢(E, ℂ))).map_add
/-
**TemperedDistribution.instFourierInvSMul** 是 Mathlib 中的一个实例，位于命名空间 `TemperedDis
tribution`。
形式化陈述：instFourierInvSMul : FourierInvSMul Complex 𝓢'(E, F) 𝓢'(E, F) where fourie
rInv_smul
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.map_smul`：∀ {R₁ : Type u_1} [inst : Semiring R₁] {M₁
 : Type u_4} [inst_1 : TopologicalSpace M₁] [inst_2 : AddCommMonoid M₁]   {M₂ : 
Type u_6} [inst_3 …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
instance instFourierInvSMul : FourierInvSMul ℂ 𝓢'(E, F) 𝓢'(E, F) where
  fourierInv_smul := (PointwiseConvergenceCLM.precomp F (fourierInvCLM ℂ 𝓢(E, ℂ))).map_smul
/-
**TemperedDistribution.instContinuousFourierInv** 是 Mathlib 中的一个实例，位于命名空间 `Tempe
redDistribution`。
形式化陈述：instContinuousFourierInv : ContinuousFourierInv 𝓢'(E, F) 𝓢'(E, F) where co
ntinuous_fourierInv
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.cont`：∀ {R : Type u_1} {S : Type u_2} [inst : Semiri
ng R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_3}   [inst_2 : Topological
Space M] [inst…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
instance instContinuousFourierInv : ContinuousFourierInv 𝓢'(E, F) 𝓢'(E, F) where
  continuous_fourierInv := (PointwiseConvergenceCLM.precomp F (fourierInvCLM ℂ 𝓢(E, ℂ))).cont

@[simp]
/-
**TemperedDistribution.fourierInv_apply** 是 Mathlib 中的一个定理，位于命名空间 `TemperedDistr
ibution`。
形式化陈述：fourierInv_apply (f : 𝓢'(E, F)) (g : 𝓢(E, Complex)) : 𝓕⁻ f g = f (𝓕⁻ g)
参数：f : 𝓢'(E, F)；g : 𝓢(E, Complex)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fourierInv_apply (f : 𝓢'(E, F)) (g : 𝓢(E, ℂ)) : 𝓕⁻ f g = f (𝓕⁻ g) := rfl

@[deprecated (since := "2026-01-06")]
alias fourierTransformInvCLM := FourierTransform.fourierInvCLM

@[deprecated (since := "2026-01-06")]
alias fourierTransformInvCLM_apply := FourierTransform.fourierInvCLM_apply

@[deprecated (since := "2026-01-06")]
alias fourierTransformInv_apply := fourierInv_apply
/-
**TemperedDistribution.instFourierPair** 是 Mathlib 中的一个实例，位于命名空间 `TemperedDistri
bution`。
形式化陈述：instFourierPair : FourierPair 𝓢'(E, F) 𝓢'(E, F) where fourierInv_fourier_e
q f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformConvergenceCLM.ext`：ext [TopologicalSpace F] {𝔖 : Set (Set E)} {f
 g : E ->SLᵤ[σ, 𝔖] F} (h : forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FourierInvPair.fourier_fourierInv_eq`：∀ {E : Type u_5} {F : Type u_6} {i
nst : FourierTransform F E} {inst_1 : FourierTransformInv E F}   [self : Fourier
InvPair E F] (f : E), Four…
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance instFourierPair : FourierPair 𝓢'(E, F) 𝓢'(E, F) where
  fourierInv_fourier_eq f := by ext; simp
/-
**TemperedDistribution.instFourierPairInv** 是 Mathlib 中的一个实例，位于命名空间 `TemperedDis
tribution`。
形式化陈述：instFourierPairInv : FourierInvPair 𝓢'(E, F) 𝓢'(E, F) where fourier_fourie
rInv_eq f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformConvergenceCLM.ext`：ext [TopologicalSpace F] {𝔖 : Set (Set E)} {f
 g : E ->SLᵤ[σ, 𝔖] F} (h : forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FourierPair.fourierInv_fourier_eq`：∀ {E : Type u_5} {F : Type u_6} {inst
 : FourierTransform E F} {inst_1 : FourierTransformInv F E}   [self : FourierPai
r E F] (f : E), Fourier…
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance instFourierPairInv : FourierInvPair 𝓢'(E, F) 𝓢'(E, F) where
  fourier_fourierInv_eq f := by ext; simp

end TVS

section embedding

variable [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- The distributional Fourier transform and the classical Fourier transform coincide on
`𝓢(E, F)`. -/
/-
**TemperedDistribution.fourier_toTemperedDistributionCLM_eq** 是 Mathlib 中的一个定理，位
于命名空间 `TemperedDistribution`。
形式化陈述：fourier_toTemperedDistributionCLM_eq (f : 𝓢(E, F)) : 𝓕 (f : 𝓢'(E, F)) = 𝓕 
f
参数：f : 𝓢(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformConvergenceCLM.ext`：ext [TopologicalSpace F] {𝔖 : Set (Set E)} {f
 g : E ->SLᵤ[σ, 𝔖] F} (h : forall x, f x = g x) : f = g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.instHasTemperateGrowth`：∀ {E : Ty
pe u_5} [inst : NormedAddCommGroup E] [inst_1 : MeasurableSpace E] [inst_2 : Nor
medSpace ℝ E]   [FiniteDimensional ℝ E] [BorelSpace…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SchwartzMap.toTemperedDistributionCLM_apply_apply`：toTemperedDistributio
nCLM_apply_apply (μ : Measure E
· 使用定理 `SchwartzMap.integral_fourier_smul_eq`：integral_fourier_smul_eq (f : 𝓢(V,
 Complex)) (g : 𝓢(V, F)) : ∫ ξ, 𝓕 f ξ • g ξ = ∫ x, f x • 𝓕 g x

--- 原说明 ---
The distributional Fourier transform and the classical Fourier transform coincid
e on
`𝓢(E, F)`.
-/
theorem fourier_toTemperedDistributionCLM_eq (f : 𝓢(E, F)) :
    𝓕 (f : 𝓢'(E, F)) = 𝓕 f := by
  ext g
  simpa using integral_fourier_smul_eq g f

@[deprecated (since := "2026-01-14")]
alias fourierTransform_toTemperedDistributionCLM_eq := fourier_toTemperedDistributionCLM_eq

/-- The distributional inverse Fourier transform and the classical inverse Fourier transform
coincide on `𝓢(E, F)`. -/
/-
**TemperedDistribution.fourierInv_toTemperedDistributionCLM_eq** 是 Mathlib 中的一个定
理，位于命名空间 `TemperedDistribution`。
形式化陈述：fourierInv_toTemperedDistributionCLM_eq (f : 𝓢(E, F)) : 𝓕⁻ (f : 𝓢'(E, F)) 
= 𝓕⁻ f
参数：f : 𝓢(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.instHasTemperateGrowth`：∀ {E : Ty
pe u_5} [inst : NormedAddCommGroup E] [inst_1 : MeasurableSpace E] [inst_2 : Nor
medSpace ℝ E]   [FiniteDimensional ℝ E] [BorelSpace…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FourierInvPair.fourier_fourierInv_eq`：∀ {E : Type u_5} {F : Type u_6} {i
nst : FourierTransform F E} {inst_1 : FourierTransformInv E F}   [self : Fourier
InvPair E F] (f : E), Four…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TemperedDistribution.fourier_toTemperedDistributionCLM_eq`：fourier_toTem
peredDistributionCLM_eq (f : 𝓢(E, F)) : 𝓕 (f : 𝓢'(E, F)) = 𝓕 f
· 使用定理 `FourierPair.fourierInv_fourier_eq`：∀ {E : Type u_5} {F : Type u_6} {inst
 : FourierTransform E F} {inst_1 : FourierTransformInv F E}   [self : FourierPai
r E F] (f : E), Fourier…

--- 原说明 ---
The distributional inverse Fourier transform and the classical inverse Fourier t
ransform
coincide on `𝓢(E, F)`.
-/
theorem fourierInv_toTemperedDistributionCLM_eq (f : 𝓢(E, F)) :
    𝓕⁻ (f : 𝓢'(E, F)) = 𝓕⁻ f := calc
  _ = 𝓕⁻ (toTemperedDistributionCLM E F volume (𝓕 (𝓕⁻ f))) := by
    congr; exact (fourier_fourierInv_eq f).symm
  _ = 𝓕⁻ (𝓕 (toTemperedDistributionCLM E F volume (𝓕⁻ f))) := by
    rw [fourier_toTemperedDistributionCLM_eq]
  _ = _ := fourierInv_fourier_eq _

@[deprecated (since := "2026-01-14")]
alias fourierTransformInv_toTemperedDistributionCLM_eq := fourierInv_toTemperedDistributionCLM_eq

end embedding

open LineDeriv Real

variable [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The line derivative in direction `m` of the Fourier transform is given by the Fourier transform
of the multiplication with `-(2 * π * Complex.I) • (inner ℝ · m)`. -/
/-
**TemperedDistribution.lineDerivOp_fourier_eq** 是 Mathlib 中的一个定理，位于命名空间 `Tempere
dDistribution`。
形式化陈述：lineDerivOp_fourier_eq (f : 𝓢'(E, F)) (m : E) : ∂_{m} (𝓕 f) = 𝓕 (- (2 * π 
* Complex.I) • smulLeftCLM F (inner Real · m) f)
参数：f : 𝓢'(E, F)；m : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformConvergenceCLM.ext`：ext [TopologicalSpace F] {𝔖 : Set (Set E)} {f
 g : E ->SLᵤ[σ, 𝔖] F} (h : forall x, f x = g x) : f = g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Function.hasTemperateGrowth_inner_left`：hasTemperateGrowth_inner_left (c
 : H) : (inner Real · c).HasTemperateGrowth
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Real.isScalarTower`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousSMul ℝ E]   [T2Space 
E] {A : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `FourierTransform.fourier_neg`：fourier_neg (f : E) : 𝓕 (-f) = - 𝓕 f
· 使用定理 `SchwartzMap.fourier_lineDerivOp_eq`：fourier_lineDerivOp_eq (f : 𝓢(V, E))
 (m : V) : 𝓕 (∂_{m} f) = (2 * π * Complex.I) • smulLeftCLM E (inner Real · m) (𝓕
 f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SchwartzMap.smulLeftCLM_ofReal`：smulLeftCLM_ofReal {g : E -> Real} (hg :
 g.HasTemperateGrowth) (f : 𝓢(E, F)) : smulLeftCLM F (fun x => RCLike.ofReal (K
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `FourierSMul.fourier_smul`：∀ {R : Type u_5} {E : Type u_6} {F : outParam 
(Type u_7)} {inst : SMul R E} {inst_1 : SMul R F}   {inst_2 : FourierTransform E
 F} [self : Fo…
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
The line derivative in direction `m` of the Fourier transform is given by the Fo
urier transform
of the multiplication with `-(2 * π * Complex.I) • (inner ℝ · m)`.
-/
theorem lineDerivOp_fourier_eq (f : 𝓢'(E, F)) (m : E) :
    ∂_{m} (𝓕 f) = 𝓕 (- (2 * π * Complex.I) • smulLeftCLM F (inner ℝ · m) f) := by
  ext u
  have : (inner ℝ · m).HasTemperateGrowth := by fun_prop
  simp [SchwartzMap.fourier_lineDerivOp_eq, ← smulLeftCLM_ofReal ℂ this]

/-- The Fourier transform of line derivative in direction `m` is given by multiplication of
`(2 * π * Complex.I) • (inner ℝ · m)` with the Fourier transform. -/
/-
**TemperedDistribution.fourier_lineDerivOp_eq** 是 Mathlib 中的一个定理，位于命名空间 `Tempere
dDistribution`。
形式化陈述：fourier_lineDerivOp_eq (f : 𝓢'(E, F)) (m : E) : 𝓕 (∂_{m} f) = (2 * π * Com
plex.I) • smulLeftCLM F (inner Real · m) (𝓕 f)
参数：f : 𝓢'(E, F)；m : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformConvergenceCLM.ext`：ext [TopologicalSpace F] {𝔖 : Set (Set E)} {f
 g : E ->SLᵤ[σ, 𝔖] F} (h : forall x, f x = g x) : f = g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Function.hasTemperateGrowth_inner_left`：hasTemperateGrowth_inner_left (c
 : H) : (inner Real · c).HasTemperateGrowth
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Real.isScalarTower`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousSMul ℝ E]   [T2Space 
E] {A : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `SchwartzMap.lineDerivOp_fourier_eq`：lineDerivOp_fourier_eq (f : 𝓢(V, E))
 (m : V) : ∂_{m} (𝓕 f) = 𝓕 (-(2 * π * Complex.I) • smulLeftCLM E (inner Real · m
) f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SchwartzMap.smulLeftCLM_ofReal`：smulLeftCLM_ofReal {g : E -> Real} (hg :
 g.HasTemperateGrowth) (f : 𝓢(E, F)) : smulLeftCLM F (fun x => RCLike.ofReal (K
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `FourierTransform.fourier_neg`：fourier_neg (f : E) : 𝓕 (-f) = - 𝓕 f
· 使用定理 `FourierSMul.fourier_smul`：∀ {R : Type u_5} {E : Type u_6} {F : outParam 
(Type u_7)} {inst : SMul R E} {inst_1 : SMul R F}   {inst_2 : FourierTransform E
 F} [self : Fo…
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `UniformConvergenceCLM.instIsSMulApply`：∀ {𝕜₁ : Type u_1} {𝕜₂ : Type u_2}
 [inst : NormedField 𝕜₁] [inst_1 : NormedField 𝕜₂] (σ : 𝕜₁ →+* 𝕜₂) {E : Type u_3
}   (F : Type u_4) [inst_2 …
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
The Fourier transform of line derivative in direction `m` is given by multiplica
tion of
`(2 * π * Complex.I) • (inner ℝ · m)` with the Fourier transform.
-/
theorem fourier_lineDerivOp_eq (f : 𝓢'(E, F)) (m : E) :
    𝓕 (∂_{m} f) = (2 * π * Complex.I) • smulLeftCLM F (inner ℝ · m) (𝓕 f) := by
  ext u
  have : (inner ℝ · m).HasTemperateGrowth := by fun_prop
  simp [SchwartzMap.lineDerivOp_fourier_eq, ← smulLeftCLM_ofReal ℂ this]

/-- The line derivative in direction `m` of the inverse Fourier transform is given by the inverse
Fourier transform of the multiplication with `(2 * π * Complex.I) • (inner ℝ · m)`. -/
/-
**TemperedDistribution.lineDerivOp_fourierInv_eq** 是 Mathlib 中的一个定理，位于命名空间 `Temp
eredDistribution`。
形式化陈述：lineDerivOp_fourierInv_eq (f : 𝓢'(E, F)) (m : E) : ∂_{m} (𝓕⁻ f) = 𝓕⁻ ((2 *
 π * Complex.I) • smulLeftCLM F (inner Real · m) f)
参数：f : 𝓢'(E, F)；m : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformConvergenceCLM.ext`：ext [TopologicalSpace F] {𝔖 : Set (Set E)} {f
 g : E ->SLᵤ[σ, 𝔖] F} (h : forall x, f x = g x) : f = g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Function.hasTemperateGrowth_inner_left`：hasTemperateGrowth_inner_left (c
 : H) : (inner Real · c).HasTemperateGrowth
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Real.isScalarTower`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousSMul ℝ E]   [T2Space 
E] {A : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `FourierTransform.fourierInv_neg`：fourierInv_neg (f : E) : 𝓕⁻ (-f) = - 𝓕⁻
 f
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `SchwartzMap.fourierInv_lineDerivOp_eq`：fourierInv_lineDerivOp_eq (f : 𝓢(
V, E)) (m : V) : 𝓕⁻ (∂_{m} f) = -(2 * π * Complex.I) • smulLeftCLM E (inner Real
 · m) (𝓕⁻ f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SchwartzMap.smulLeftCLM_ofReal`：smulLeftCLM_ofReal {g : E -> Real} (hg :
 g.HasTemperateGrowth) (f : 𝓢(E, F)) : smulLeftCLM F (fun x => RCLike.ofReal (K
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FourierInvSMul.fourierInv_smul`：∀ {R : Type u_5} {E : Type u_6} {F : out
Param (Type u_7)} {inst : SMul R E} {inst_1 : SMul R F}   {inst_2 : FourierTrans
formInv E F} [self :…
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
The line derivative in direction `m` of the inverse Fourier transform is given b
y the inverse
Fourier transform of the multiplication with `(2 * π * Complex.I) • (inner ℝ · m
)`.
-/
theorem lineDerivOp_fourierInv_eq (f : 𝓢'(E, F)) (m : E) :
    ∂_{m} (𝓕⁻ f) = 𝓕⁻ ((2 * π * Complex.I) • smulLeftCLM F (inner ℝ · m) f) := by
  ext u
  have : (inner ℝ · m).HasTemperateGrowth := by fun_prop
  simp [SchwartzMap.fourierInv_lineDerivOp_eq, ← smulLeftCLM_ofReal ℂ this]

/-- The inverse Fourier transform of line derivative in direction `m` is given by multiplication of
`-(2 * π * Complex.I) • (inner ℝ · m)` with the inverse Fourier transform. -/
/-
**TemperedDistribution.fourierInv_lineDerivOp_eq** 是 Mathlib 中的一个定理，位于命名空间 `Temp
eredDistribution`。
形式化陈述：fourierInv_lineDerivOp_eq (f : 𝓢'(E, F)) (m : E) : 𝓕⁻ (∂_{m} f) = -(2 * π 
* Complex.I) • smulLeftCLM F (inner Real · m) (𝓕⁻ f)
参数：f : 𝓢'(E, F)；m : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformConvergenceCLM.ext`：ext [TopologicalSpace F] {𝔖 : Set (Set E)} {f
 g : E ->SLᵤ[σ, 𝔖] F} (h : forall x, f x = g x) : f = g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Function.hasTemperateGrowth_inner_left`：hasTemperateGrowth_inner_left (c
 : H) : (inner Real · c).HasTemperateGrowth
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Real.isScalarTower`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousSMul ℝ E]   [T2Space 
E] {A : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `SchwartzMap.lineDerivOp_fourierInv_eq`：lineDerivOp_fourierInv_eq (f : 𝓢(
V, E)) (m : V) : ∂_{m} (𝓕⁻ f) = 𝓕⁻ ((2 * π * Complex.I) • smulLeftCLM E (inner R
eal · m) f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SchwartzMap.smulLeftCLM_ofReal`：smulLeftCLM_ofReal {g : E -> Real} (hg :
 g.HasTemperateGrowth) (f : 𝓢(E, F)) : smulLeftCLM F (fun x => RCLike.ofReal (K
· 使用定理 `FourierInvSMul.fourierInv_smul`：∀ {R : Type u_5} {E : Type u_6} {F : out
Param (Type u_7)} {inst : SMul R E} {inst_1 : SMul R F}   {inst_2 : FourierTrans
formInv E F} [self :…
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
The inverse Fourier transform of line derivative in direction `m` is given by mu
ltiplication of
`-(2 * π * Complex.I) • (inner ℝ · m)` with the inverse Fourier transform.
-/
theorem fourierInv_lineDerivOp_eq (f : 𝓢'(E, F)) (m : E) :
    𝓕⁻ (∂_{m} f) = -(2 * π * Complex.I) • smulLeftCLM F (inner ℝ · m) (𝓕⁻ f) := by
  ext u
  have : (inner ℝ · m).HasTemperateGrowth := by fun_prop
  simp [SchwartzMap.lineDerivOp_fourierInv_eq, ← smulLeftCLM_ofReal ℂ this]

end Fourier

section DiracDelta

variable [NormedAddCommGroup E]

section definition

variable [NormedSpace ℝ E]

/-- The Dirac delta distribution -/
/-
**TemperedDistribution.delta** 是 Mathlib 中的一个定义，位于命名空间 `TemperedDistribution`。
形式化陈述：delta (x : E) : 𝓢'(E, Complex)
参数：x : E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Dirac delta distribution
-/
def delta (x : E) : 𝓢'(E, ℂ) :=
  toPointwiseConvergenceCLM _ _ _ _ <|
    (BoundedContinuousFunction.evalCLM ℂ x).comp (toBoundedContinuousFunctionCLM ℂ E ℂ)

@[simp]
/-
**TemperedDistribution.delta_apply** 是 Mathlib 中的一个定理，位于命名空间 `TemperedDistributi
on`。
形式化陈述：delta_apply (x : E) (f : 𝓢(E, Complex)) : delta x f = f x
参数：x : E；f : 𝓢(E, Complex)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem delta_apply (x : E) (f : 𝓢(E, ℂ)) : delta x f = f x :=
  rfl

open MeasureTheory MeasureTheory.Measure

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- Dirac measure considered as a tempered distribution is the delta distribution. -/
@[simp]
/-
**TemperedDistribution.toTemperedDistribution_dirac_eq_delta** 是 Mathlib 中的一个定理，
位于命名空间 `TemperedDistribution`。
形式化陈述：toTemperedDistribution_dirac_eq_delta (x : E) : (dirac x).toTemperedDistri
bution = delta x
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformConvergenceCLM.ext`：ext [TopologicalSpace F] {𝔖 : Set (Set E)} {f
 g : E ->SLᵤ[σ, 𝔖] F} (h : forall x, f x = g x) : f = g
· 使用定理 `MeasureTheory.IsFiniteMeasure.instHasTemperateGrowth`：∀ {E : Type u_5} [
inst : NormedAddCommGroup E] [inst_1 : MeasurableSpace E] {μ : MeasureTheory.Mea
sure E}   [h : MeasureTheory.IsFiniteMeasu…
· 使用定理 `MeasureTheory.Measure.dirac.instIsFiniteMeasure`：∀ {α : Type u_1} [inst 
: MeasurableSpace α] {a : α}, MeasureTheory.IsFiniteMeasure (MeasureTheory.Measu
re.dirac a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.toTemperedDistribution_apply`：toTemperedDistributi
on_apply (g : 𝓢(E, Complex)) : μ.toTemperedDistribution g = ∫ (x : E), g x ∂μ
· 使用定理 `MeasureTheory.integral_dirac`：integral_dirac [MeasurableSpace α] [Measur
ableSingletonClass α] (f : α -> E) (a : α) : ∫ x, f x ∂Measure.dirac a = f a
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `instMeasurableEqOfSecondCountableTopologyOfT2Space`：∀ {α : Type u_1} [in
st : TopologicalSpace α] [inst_1 : MeasurableSpace α] [OpensMeasurableSpace α]  
 [SecondCountableTopology α] [T2Space α]…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Dirac measure considered as a tempered distribution is the delta distribution.
-/
theorem toTemperedDistribution_dirac_eq_delta (x : E) :
  (dirac x).toTemperedDistribution = delta x := by aesop

end definition

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

open FourierTransform

/-- The Fourier transform of the delta distribution is equal to the volume.

Informally, this is usually represented as `𝓕 δ = 1`. -/
/-
**TemperedDistribution.fourier_delta_zero** 是 Mathlib 中的一个定理，位于命名空间 `TemperedDis
tribution`。
形式化陈述：fourier_delta_zero : 𝓕 (delta (0 : E)) = volume.toTemperedDistribution
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformConvergenceCLM.ext`：ext [TopologicalSpace F] {𝔖 : Set (Set E)} {f
 g : E ->SLᵤ[σ, 𝔖] F} (h : forall x, f x = g x) : f = g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
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
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.instHasTemperateGrowth`：∀ {E : Ty
pe u_5} [inst : NormedAddCommGroup E] [inst_1 : MeasurableSpace E] [inst_2 : Nor
medSpace ℝ E]   [FiniteDimensional ℝ E] [BorelSpace…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inner_zero_right`：inner_zero_right (x : E) : ⟪x, 0⟫ = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `AddChar.map_zero_eq_one`：∀ {A : Type u_1} {M : Type u_3} [inst : AddMono
id A] [inst_1 : Monoid M] (ψ : AddChar A M), ψ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `MeasureTheory.Measure.toTemperedDistribution_apply`：toTemperedDistributi
on_apply (g : 𝓢(E, Complex)) : μ.toTemperedDistribution g = ∫ (x : E), g x ∂μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The Fourier transform of the delta distribution is equal to the volume.

Informally, this is usually represented as `𝓕 δ = 1`.
-/
theorem fourier_delta_zero : 𝓕 (delta (0 : E)) = volume.toTemperedDistribution := by
  ext f
  simp [SchwartzMap.fourier_coe, Real.fourier_eq]

end DiracDelta

end TemperedDistribution

