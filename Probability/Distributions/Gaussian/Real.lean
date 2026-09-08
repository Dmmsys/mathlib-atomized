/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Luccioli, Rémy Degenne, Alexander Bentkamp
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Gaussian distributions over ℝ

We define a Gaussian measure over the reals.

## Main definitions

* `gaussianPDFReal`: the function `μ v x ↦ (1 / (sqrt (2 * pi * v))) * exp (- (x - μ)^2 / (2 * v))`,
  which is the probability density function of a Gaussian distribution with mean `μ` and
  variance `v` (when `v ≠ 0`).
* `gaussianPDF`: `ℝ≥0∞`-valued pdf, `gaussianPDF μ v x = ENNReal.ofReal (gaussianPDFReal μ v x)`.
* `gaussianReal`: a Gaussian measure on `ℝ`, parametrized by its mean `μ` and variance `v`.
  If `v = 0`, this is `dirac μ`, otherwise it is defined as the measure with density
  `gaussianPDF μ v` with respect to the Lebesgue measure.

## Main results

* `gaussianReal_add_const`: if `X` is a random variable with Gaussian distribution with mean `μ` and
  variance `v`, then `X + y` is Gaussian with mean `μ + y` and variance `v`.
* `gaussianReal_const_mul`: if `X` is a random variable with Gaussian distribution with mean `μ` and
  variance `v`, then `c * X` is Gaussian with mean `c * μ` and variance `c ^ 2 * v`.

-/

@[expose] public section

open scoped ENNReal NNReal Real Complex

open MeasureTheory

namespace ProbabilityTheory

section GaussianPDF

/-- Probability density function of the Gaussian distribution with mean `μ` and variance `v`. -/
noncomputable
/-
**ProbabilityTheory.gaussianPDFReal** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory
`。
形式化陈述：gaussianPDFReal (μ : Real) (v : Real>=0) (x : Real) : Real
参数：μ : Real；v : Real>=0；x : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def gaussianPDFReal (μ : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ :=
  (√(2 * π * v))⁻¹ * rexp (-(x - μ) ^ 2 / (2 * v))
/-
**ProbabilityTheory.gaussianPDFReal_def** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTh
eory`。
形式化陈述：gaussianPDFReal_def (μ : Real) (v : Real>=0) : gaussianPDFReal μ v = fun x
 => (√(2 * π * v))⁻¹ * rexp (-(x - μ) ^ 2 / (2 * v))
参数：μ : Real；v : Real>=0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma gaussianPDFReal_def (μ : ℝ) (v : ℝ≥0) :
    gaussianPDFReal μ v =
      fun x ↦ (√(2 * π * v))⁻¹ * rexp (-(x - μ) ^ 2 / (2 * v)) := rfl

@[simp]
/-
**ProbabilityTheory.gaussianPDFReal_zero_var** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory`。
形式化陈述：gaussianPDFReal_zero_var (m : Real) : gaussianPDFReal m 0 = 0
参数：m : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Real.sqrt_zero`：sqrt_zero : √0 = 0
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `Real.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma gaussianPDFReal_zero_var (m : ℝ) : gaussianPDFReal m 0 = 0 := by
  ext1 x
  simp [gaussianPDFReal]

/-- The Gaussian pdf is positive when the variance is not zero. -/
/-
**ProbabilityTheory.gaussianPDFReal_pos** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTh
eory`。
形式化陈述：gaussianPDFReal_pos (μ : Real) (v : Real>=0) (x : Real) (hv : v != 0) : 0 
< gaussianPDFReal μ v x
参数：μ : Real；v : Real>=0；x : Real；hv : v != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.gaussianPDFReal.eq_1`：∀ (μ : ℝ) (v : NNReal) (x : ℝ), 
  ProbabilityTheory.gaussianPDFReal μ v x = (√(2 * Real.pi * ↑v))⁻¹ * Real.exp (
-(x - μ) ^ 2 / (2 * ↑v))
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `Real.sqrt_pos_of_pos`：∀ {x : ℝ}, 0 < x → 0 < √x
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
· 使用定理 `Mathlib.Meta.Positivity.nnreal_coe_pos`：∀ {r : NNReal}, 0 < r → 0 < ↑r
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x

--- 原说明 ---
The Gaussian pdf is positive when the variance is not zero.
-/
lemma gaussianPDFReal_pos (μ : ℝ) (v : ℝ≥0) (x : ℝ) (hv : v ≠ 0) : 0 < gaussianPDFReal μ v x := by
  rw [gaussianPDFReal]
  positivity

/-- The Gaussian pdf is nonnegative. -/
/-
**ProbabilityTheory.gaussianPDFReal_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory`。
形式化陈述：gaussianPDFReal_nonneg (μ : Real) (v : Real>=0) (x : Real) : 0 <= gaussian
PDFReal μ v x
参数：μ : Real；v : Real>=0；x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.gaussianPDFReal.eq_1`：∀ (μ : ℝ) (v : NNReal) (x : ℝ), 
  ProbabilityTheory.gaussianPDFReal μ v x = (√(2 * Real.pi * ↑v))⁻¹ * Real.exp (
-(x - μ) ^ 2 / (2 * ↑v))
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `inv_nonneg_of_nonneg`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_
1 : PartialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 ≤ a → 0 ≤ a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Real.sqrt_nonneg`：∀ (x : ℝ), 0 ≤ √x
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x

--- 原说明 ---
The Gaussian pdf is nonnegative.
-/
lemma gaussianPDFReal_nonneg (μ : ℝ) (v : ℝ≥0) (x : ℝ) : 0 ≤ gaussianPDFReal μ v x := by
  rw [gaussianPDFReal]
  positivity

/-- The Gaussian pdf is measurable. -/
@[fun_prop]
/-
**ProbabilityTheory.measurable_uncurry_gaussianPDFReal** 是 Mathlib 中的一个引理，位于命名空间
 `ProbabilityTheory`。
形式化陈述：measurable_uncurry_gaussianPDFReal : Measurable (fun (μ, v, x) => gaussian
PDFReal μ v x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.fun_mul`：∀ {M : Type u_2} {α : Type u_3} [inst : MeasurableSp
ace M] [inst_1 : Mul M] {m : MeasurableSpace α} {f g : α → M}   [MeasurableMul₂ 
M], Meas…
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
· 使用定理 `Measurable.fun_inv`：∀ {G : Type u_2} {α : Type u_3} [inst : Inv G] [inst
_1 : MeasurableSpace G] [MeasurableInv G] {m : MeasurableSpace α}   {f : α → G},
 Measura…
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
· 使用定理 `Measurable.sqrt`：∀ {α : Type u_1} {m : MeasurableSpace α} {f : α → ℝ}, M
easurable f → Measurable fun x => √(f x)
· 使用定理 `Measurable.const_mul`：Measurable.const_mul [MeasurableMul M] (hf : Measu
rable f) (c : M) : Measurable fun x => c * f x
· 使用定理 `ContinuousMul.measurableMul`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Mul γ]   [SeparatelyCont
inuousMul γ], Mea…
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `Measurable.coe_nnreal_real`：Measurable.coe_nnreal_real {f : α -> Real>=0
} (hf : Measurable f) : Measurable fun x => (f x : Real)
· 使用定理 `Measurable.fst`：Measurable.fst {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).1
· 使用定理 `Measurable.snd`：Measurable.snd {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).2
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `Measurable.exp`：∀ {α : Type u_1} {m : MeasurableSpace α} {f : α → ℝ}, Me
asurable f → Measurable fun x => Real.exp (f x)
· 使用定理 `Measurable.fun_div`：∀ {G : Type u_2} {α : Type u_3} [inst : MeasurableSp
ace G] [inst_1 : Div G] {m : MeasurableSpace α} {f g : α → G}   [MeasurableDiv₂ 
G], Meas…
· 使用定理 `measurableDiv₂_of_mul_inv`：∀ (G : Type u_2) [inst : MeasurableSpace G] [
inst_1 : DivInvMonoid G] [MeasurableMul₂ G] [MeasurableInv G],   MeasurableDiv₂ 
G
· 使用定理 `Measurable.fun_neg`：∀ {G : Type u_2} {α : Type u_3} [inst : Neg G] [inst
_1 : MeasurableSpace G] [MeasurableNeg G] {m : MeasurableSpace α}   {f : α → G},
 Measura…
· 使用定理 `ContinuousNeg.measurableNeg`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Neg γ]   [ContinuousNeg 
γ], MeasurableNeg…
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
The Gaussian pdf is measurable.
-/
lemma measurable_uncurry_gaussianPDFReal : Measurable (fun (μ, v, x) ↦ gaussianPDFReal μ v x) := by
  unfold gaussianPDFReal
  fun_prop
/-
**ProbabilityTheory.measurable_gaussianPDFReal** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：measurable_gaussianPDFReal (μ : Real) (v : Real>=0) : Measurable (gaussian
PDFReal μ v)
参数：μ : Real；v : Real>=0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
· 使用引理 `ProbabilityTheory.measurable_uncurry_gaussianPDFReal`：measurable_uncurry
_gaussianPDFReal : Measurable (fun (μ, v, x) => gaussianPDFReal μ v x)
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
-/
lemma measurable_gaussianPDFReal (μ : ℝ) (v : ℝ≥0) : Measurable (gaussianPDFReal μ v) := by
  fun_prop

/-- The Gaussian pdf is strongly measurable. -/
@[fun_prop]
/-
**ProbabilityTheory.stronglyMeasurable_uncurry_gaussianPDFReal** 是 Mathlib 中的一个引
理，位于命名空间 `ProbabilityTheory`。
形式化陈述：stronglyMeasurable_uncurry_gaussianPDFReal : StronglyMeasurable (fun (μ, v
, x) => gaussianPDFReal μ v x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.stronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {f : α → 
β} {mα : MeasurableSpace α} [inst : MeasurableSpace β]   [inst_1 : TopologicalSp
ace β] [Topological…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用引理 `ProbabilityTheory.measurable_uncurry_gaussianPDFReal`：measurable_uncurry
_gaussianPDFReal : Measurable (fun (μ, v, x) => gaussianPDFReal μ v x)

--- 原说明 ---
The Gaussian pdf is strongly measurable.
-/
lemma stronglyMeasurable_uncurry_gaussianPDFReal :
    StronglyMeasurable (fun (μ, v, x) ↦ gaussianPDFReal μ v x) :=
  measurable_uncurry_gaussianPDFReal.stronglyMeasurable
/-
**ProbabilityTheory.stronglyMeasurable_gaussianPDFReal** 是 Mathlib 中的一个引理，位于命名空间
 `ProbabilityTheory`。
形式化陈述：stronglyMeasurable_gaussianPDFReal (μ : Real) (v : Real>=0) : StronglyMeas
urable (gaussianPDFReal μ v)
参数：μ : Real；v : Real>=0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.comp_measurable`：comp_measurable [Topol
ogicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ} {f : α -> β} {g :
 γ -> α} (hf : StronglyMeasurable f) (…
· 使用引理 `ProbabilityTheory.stronglyMeasurable_uncurry_gaussianPDFReal`：stronglyMe
asurable_uncurry_gaussianPDFReal : StronglyMeasurable (fun (μ, v, x) => gaussian
PDFReal μ v x)
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
-/
lemma stronglyMeasurable_gaussianPDFReal (μ : ℝ) (v : ℝ≥0) :
    StronglyMeasurable (gaussianPDFReal μ v) := by
  fun_prop

@[fun_prop]
/-
**ProbabilityTheory.integrable_gaussianPDFReal** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：integrable_gaussianPDFReal (μ : Real) (v : Real>=0) : Integrable (gaussian
PDFReal μ v)
参数：μ : Real；v : Real>=0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.gaussianPDFReal_def`：gaussianPDFReal_def (μ : Real) (v
 : Real>=0) : gaussianPDFReal μ v = fun x => (√(2 * π * v))⁻¹ * rexp (-(x - μ) ^
 2 / (2 * v))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Real.sqrt_zero`：sqrt_zero : √0 = 0
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `Real.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Real.sqrt_mul'`：sqrt_mul' (x) {y : Real} (hy : 0 <= y) : √(x * y) = √x *
 √y
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
（共 108 条，此处仅展示前 30 条）
-/
lemma integrable_gaussianPDFReal (μ : ℝ) (v : ℝ≥0) :
    Integrable (gaussianPDFReal μ v) := by
  rw [gaussianPDFReal_def]
  by_cases hv : v = 0
  · simp [hv]
  let g : ℝ → ℝ := fun x ↦ (√(2 * π * v))⁻¹ * rexp (-x ^ 2 / (2 * v))
  have hg : Integrable g := by
    suffices g = fun x ↦ (√(2 * π * v))⁻¹ * rexp (-(2 * v)⁻¹ * x ^ 2) by
      rw [this]
      refine (integrable_exp_neg_mul_sq ?_).const_mul (√(2 * π * v))⁻¹
      simpa [pos_iff_ne_zero]
    ext x
    simp only [g, NNReal.zero_le_coe, Real.sqrt_mul',
      mul_inv_rev, NNReal.coe_mul, NNReal.coe_inv, NNReal.coe_ofNat, neg_mul, mul_eq_mul_left_iff,
      Real.exp_eq_exp, mul_eq_zero, inv_eq_zero, Real.sqrt_eq_zero, NNReal.coe_eq_zero, hv,
      false_or]
    rw [mul_comm]
    left
    field
  exact Integrable.comp_sub_right hg μ

/-- The Gaussian distribution pdf integrates to 1 when the variance is not zero. -/
/-
**ProbabilityTheory.lintegral_gaussianPDFReal_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `
ProbabilityTheory`。
形式化陈述：lintegral_gaussianPDFReal_eq_one (μ : Real) {v : Real>=0} (h : v != 0) : ∫
⁻ x, ENNReal.ofReal (gaussianPDFReal μ v x) = 1
参数：μ : Real；h : v != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.toReal_eq_one_iff`：toReal_eq_one_iff (x : Real>=0∞) : x.toReal =
 1 ↔ x = 1
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `MeasureTheory.StronglyMeasurable.comp_measurable`：comp_measurable [Topol
ogicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ} {f : α -> β} {g :
 γ -> α} (hf : StronglyMeasurable f) (…
· 使用引理 `ProbabilityTheory.stronglyMeasurable_uncurry_gaussianPDFReal`：stronglyMe
asurable_uncurry_gaussianPDFReal : StronglyMeasurable (fun (μ, v, x) => gaussian
PDFReal μ v x)
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用引理 `ProbabilityTheory.gaussianPDFReal_nonneg`：gaussianPDFReal_nonneg (μ : Re
al) (v : Real>=0) (x : Real) : 0 <= gaussianPDFReal μ v x
· 使用定理 `MeasureTheory.integral_eq_lintegral_of_nonneg_ae`：integral_eq_lintegral_
of_nonneg_ae {f : α -> Real} (hf : 0 <=ᵐ[μ] f) (hfm : AEStronglyMeasurable f μ) 
: ∫ a, f a ∂μ = ENNReal.toReal (∫⁻ a, …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.integral_const_mul`：integral_const_mul {L : Type*} [RCLike
 L] (r : L) (f : α -> L) : ∫ a, r * f a ∂μ = r * ∫ a, f a ∂μ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.integral_sub_right_eq_self`：∀ {G : Type u_4} {E : Type u_5
} [inst : MeasurableSpace G] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpa
ce ℝ E]   {μ : MeasureTheory.M…
· 使用定理 `ContinuousAdd.measurableAdd`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Add γ]   [SeparatelyCont
inuousAdd γ], Mea…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
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
· 使用定理 `MeasureTheory.IsAddLeftInvariant.isAddRightInvariant`：∀ {G : Type u_1} [
inst : MeasurableSpace G] [inst_1 : AddCommSemigroup G] {μ : MeasureTheory.Measu
re G}   [μ.IsAddLeftInvariant], μ.IsAddRig…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsAddLeftInvariant`：∀ {G : Type
 u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpac
e G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
（共 96 条，此处仅展示前 30 条）

--- 原说明 ---
The Gaussian distribution pdf integrates to 1 when the variance is not zero.
-/
lemma lintegral_gaussianPDFReal_eq_one (μ : ℝ) {v : ℝ≥0} (h : v ≠ 0) :
    ∫⁻ x, ENNReal.ofReal (gaussianPDFReal μ v x) = 1 := by
  rw [← ENNReal.toReal_eq_one_iff]
  have hfm : AEStronglyMeasurable (gaussianPDFReal μ v) volume := by fun_prop
  have hf : 0 ≤ₐₛ gaussianPDFReal μ v := ae_of_all _ (gaussianPDFReal_nonneg μ v)
  rw [← integral_eq_lintegral_of_nonneg_ae hf hfm]
  simp only [gaussianPDFReal,
    integral_const_mul]
  rw [integral_sub_right_eq_self (μ := volume) (fun a ↦ rexp (-a ^ 2 / ((2 : ℝ) * v))) μ]
  simp only [div_eq_inv_mul, mul_inv_rev,
    mul_neg]
  simp_rw [← neg_mul]
  rw [neg_mul, integral_gaussian, ← Real.sqrt_inv, ← Real.sqrt_mul]
  · simp [field]
  · positivity

/-- The Gaussian distribution pdf integrates to 1 when the variance is not zero. -/
/-
**ProbabilityTheory.integral_gaussianPDFReal_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `P
robabilityTheory`。
形式化陈述：integral_gaussianPDFReal_eq_one (μ : Real) {v : Real>=0} (hv : v != 0) : ∫
 x, gaussianPDFReal μ v x = 1
参数：μ : Real；hv : v != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.lintegral_gaussianPDFReal_eq_one`：lintegral_gaussianPD
FReal_eq_one (μ : Real) {v : Real>=0} (h : v != 0) : ∫⁻ x, ENNReal.ofReal (gauss
ianPDFReal μ v x) = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.ofReal_eq_ofReal_iff`：ofReal_eq_ofReal_iff {p q : Real} (hp : 0 
<= p) (hq : 0 <= q) : ENNReal.ofReal p = ENNReal.ofReal q ↔ p = q
· 使用引理 `MeasureTheory.integral_nonneg`：integral_nonneg {f : α -> E} (hf : 0 <= f
) : 0 <= ∫ x, f x ∂μ
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
· 使用引理 `ProbabilityTheory.gaussianPDFReal_nonneg`：gaussianPDFReal_nonneg (μ : Re
al) (v : Real>=0) (x : Real) : 0 <= gaussianPDFReal μ v x
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `ENNReal.ofReal_one`：ENNReal.ofReal 1 = 1
· 使用定理 `MeasureTheory.ofReal_integral_eq_lintegral_ofReal`：ofReal_integral_eq_li
ntegral_ofReal {f : α -> Real} (hfi : Integrable f μ) (f_nn : 0 <=ᵐ[μ] f) : ENNR
eal.ofReal (∫ x, f x ∂μ) = ∫⁻ x, ENNRea…
· 使用引理 `ProbabilityTheory.integrable_gaussianPDFReal`：integrable_gaussianPDFReal
 (μ : Real) (v : Real>=0) : Integrable (gaussianPDFReal μ v)
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α

--- 原说明 ---
The Gaussian distribution pdf integrates to 1 when the variance is not zero.
-/
lemma integral_gaussianPDFReal_eq_one (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    ∫ x, gaussianPDFReal μ v x = 1 := by
  have h := lintegral_gaussianPDFReal_eq_one μ hv
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_gaussianPDFReal _ _)
    (ae_of_all _ (gaussianPDFReal_nonneg _ _)), ← ENNReal.ofReal_one] at h
  rwa [← ENNReal.ofReal_eq_ofReal_iff (integral_nonneg (gaussianPDFReal_nonneg _ _)) zero_le_one]
/-
**ProbabilityTheory.gaussianPDFReal_sub** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTh
eory`。
形式化陈述：gaussianPDFReal_sub {μ : Real} {v : Real>=0} (x y : Real) : gaussianPDFRea
l μ v (x - y) = gaussianPDFReal (μ + y) v x
参数：x y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_add_eq_sub_sub_swap`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (
a b c : α), a - (b + c) = a - c - b
-/
lemma gaussianPDFReal_sub {μ : ℝ} {v : ℝ≥0} (x y : ℝ) :
    gaussianPDFReal μ v (x - y) = gaussianPDFReal (μ + y) v x := by
  simp only [gaussianPDFReal]
  rw [sub_add_eq_sub_sub_swap]
/-
**ProbabilityTheory.gaussianPDFReal_add** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTh
eory`。
形式化陈述：gaussianPDFReal_add {μ : Real} {v : Real>=0} (x y : Real) : gaussianPDFRea
l μ v (x + y) = gaussianPDFReal (μ - y) v x
参数：x y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.gaussianPDFReal_sub`：gaussianPDFReal_sub {μ : Real} {v
 : Real>=0} (x y : Real) : gaussianPDFReal μ v (x - y) = gaussianPDFReal (μ + y)
 v x
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
lemma gaussianPDFReal_add {μ : ℝ} {v : ℝ≥0} (x y : ℝ) :
    gaussianPDFReal μ v (x + y) = gaussianPDFReal (μ - y) v x := by
  rw [sub_eq_add_neg, ← gaussianPDFReal_sub, sub_eq_add_neg, neg_neg]
/-
**ProbabilityTheory.gaussianPDFReal_inv_mul** 是 Mathlib 中的一个引理，位于命名空间 `Probabili
tyTheory`。
形式化陈述：gaussianPDFReal_inv_mul {μ : Real} {v : Real>=0} {c : Real} (hc : c != 0) 
(x : Real) : gaussianPDFReal μ v (c⁻¹ * x) = |c| * gaussianPDFReal (c * μ) (.mk 
(c ^ 2) (sq_nonneg _) * v) x
参数：hc : c != 0；x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ProbabilityTheory.gaussianPDFReal.eq_1`：∀ (μ : ℝ) (v : NNReal) (x : ℝ), 
  ProbabilityTheory.gaussianPDFReal μ v x = (√(2 * Real.pi * ↑v))⁻¹ * Real.exp (
-(x - μ) ^ 2 / (2 * ↑v))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.sqrt_mul'`：sqrt_mul' (x) {y : Real} (hy : 0 <= y) : √(x * y) = √x *
 √y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Real.sqrt_mul`：sqrt_mul {x : Real} (hx : 0 <= x) (y : Real) : √(x * y) =
 √x * √y
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `Even.pow_nonneg`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : LinearOr
der R] [IsOrderedRing R] [ExistsAddOfLE R] {n : ℕ},   Even n → ∀ (a : R), 0 ≤ a 
^ n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `even_two_mul`：even_two_mul (a : α) : Even (2 * a)
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
（共 122 条，此处仅展示前 30 条）
-/
lemma gaussianPDFReal_inv_mul {μ : ℝ} {v : ℝ≥0} {c : ℝ} (hc : c ≠ 0) (x : ℝ) :
    gaussianPDFReal μ v (c⁻¹ * x)
      = |c| * gaussianPDFReal (c * μ) (.mk (c ^ 2) (sq_nonneg _) * v) x := by
  simp only [gaussianPDFReal.eq_1, NNReal.zero_le_coe,
    Real.sqrt_mul', mul_inv_rev, NNReal.coe_mul, NNReal.coe_mk]
  rw [← mul_assoc]
  refine congr_arg₂ _ ?_ ?_
  · simp (disch := positivity) only [Real.sqrt_mul, mul_inv_rev, field]
    rw [Real.sqrt_sq_eq_abs]
  · congr 1
    field
/-
**ProbabilityTheory.gaussianPDFReal_mul** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTh
eory`。
形式化陈述：gaussianPDFReal_mul {μ : Real} {v : Real>=0} {c : Real} (hc : c != 0) (x :
 Real) : gaussianPDFReal μ v (c * x) = |c⁻¹| * gaussianPDFReal (c⁻¹ * μ) (.mk (c
 ^ 2)⁻¹ (inv_nonneg.mpr (sq_nonneg _)) * v) x
参数：hc : c != 0；x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_nonneg`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Partia
lOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 ≤ a⁻¹ ↔ 0 ≤ a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用引理 `ProbabilityTheory.gaussianPDFReal_inv_mul`：gaussianPDFReal_inv_mul {μ : 
Real} {v : Real>=0} {c : Real} (hc : c != 0) (x : Real) : gaussianPDFReal μ v (c
⁻¹ * x) = |c| * gaussianPDFReal…
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `abs_inv`：abs_inv (a : α) : |a⁻¹| = |a|⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NNReal.mk.congr_simp`：∀ (x x_1 : ℝ) (e_x : x = x_1) (hx : 0 ≤ x), NNReal
.mk x hx = NNReal.mk x_1 ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma gaussianPDFReal_mul {μ : ℝ} {v : ℝ≥0} {c : ℝ} (hc : c ≠ 0) (x : ℝ) :
    gaussianPDFReal μ v (c * x)
      = |c⁻¹| * gaussianPDFReal (c⁻¹ * μ) (.mk (c ^ 2)⁻¹ (inv_nonneg.mpr (sq_nonneg _)) * v) x := by
  conv_lhs => rw [← inv_inv c, gaussianPDFReal_inv_mul (inv_ne_zero hc)]
  simp

/-- The pdf of a Gaussian distribution on ℝ with mean `μ` and variance `v`. -/
noncomputable
/-
**ProbabilityTheory.gaussianPDF** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory`。
形式化陈述：gaussianPDF (μ : Real) (v : Real>=0) (x : Real) : Real>=0∞
参数：μ : Real；v : Real>=0；x : Real。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def gaussianPDF (μ : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (gaussianPDFReal μ v x)
/-
**ProbabilityTheory.gaussianPDF_def** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory
`。
形式化陈述：gaussianPDF_def (μ : Real) (v : Real>=0) : gaussianPDF μ v = fun x => ENNR
eal.ofReal (gaussianPDFReal μ v x)
参数：μ : Real；v : Real>=0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma gaussianPDF_def (μ : ℝ) (v : ℝ≥0) :
    gaussianPDF μ v = fun x ↦ ENNReal.ofReal (gaussianPDFReal μ v x) := rfl

@[simp]
/-
**ProbabilityTheory.gaussianPDF_zero_var** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：gaussianPDF_zero_var (μ : Real) : gaussianPDF μ 0 = 0
参数：μ : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `ProbabilityTheory.gaussianPDFReal_zero_var`：gaussianPDFReal_zero_var (m 
: Real) : gaussianPDFReal m 0 = 0
· 使用定理 `ENNReal.ofReal_zero`：ENNReal.ofReal 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma gaussianPDF_zero_var (μ : ℝ) : gaussianPDF μ 0 = 0 := by ext; simp [gaussianPDF]

@[simp]
/-
**ProbabilityTheory.toReal_gaussianPDF** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityThe
ory`。
形式化陈述：toReal_gaussianPDF {μ : Real} {v : Real>=0} (x : Real) : (gaussianPDF μ v 
x).toReal = gaussianPDFReal μ v x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.gaussianPDF.eq_1`：∀ (μ : ℝ) (v : NNReal) (x : ℝ),   Pr
obabilityTheory.gaussianPDF μ v x = ENNReal.ofReal (ProbabilityTheory.gaussianPD
FReal μ v x)
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用引理 `ProbabilityTheory.gaussianPDFReal_nonneg`：gaussianPDFReal_nonneg (μ : Re
al) (v : Real>=0) (x : Real) : 0 <= gaussianPDFReal μ v x
-/
lemma toReal_gaussianPDF {μ : ℝ} {v : ℝ≥0} (x : ℝ) :
    (gaussianPDF μ v x).toReal = gaussianPDFReal μ v x := by
  rw [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg μ v x)]
/-
**ProbabilityTheory.gaussianPDF_pos** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory
`。
形式化陈述：gaussianPDF_pos (μ : Real) {v : Real>=0} (hv : v != 0) (x : Real) : 0 < ga
ussianPDF μ v x
参数：μ : Real；hv : v != 0；x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.gaussianPDF.eq_1`：∀ (μ : ℝ) (v : NNReal) (x : ℝ),   Pr
obabilityTheory.gaussianPDF μ v x = ENNReal.ofReal (ProbabilityTheory.gaussianPD
FReal μ v x)
· 使用定理 `ENNReal.ofReal_pos`：ofReal_pos {p : Real} : 0 < ENNReal.ofReal p ↔ 0 < p
· 使用引理 `ProbabilityTheory.gaussianPDFReal_pos`：gaussianPDFReal_pos (μ : Real) (v
 : Real>=0) (x : Real) (hv : v != 0) : 0 < gaussianPDFReal μ v x
-/
lemma gaussianPDF_pos (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) : 0 < gaussianPDF μ v x := by
  rw [gaussianPDF, ENNReal.ofReal_pos]
  exact gaussianPDFReal_pos _ _ _ hv
/-
**ProbabilityTheory.gaussianPDF_lt_top** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityThe
ory`。
形式化陈述：gaussianPDF_lt_top {μ : Real} {v : Real>=0} {x : Real} : gaussianPDF μ v x
 < ∞
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma gaussianPDF_lt_top {μ : ℝ} {v : ℝ≥0} {x : ℝ} : gaussianPDF μ v x < ∞ := by simp [gaussianPDF]
/-
**ProbabilityTheory.gaussianPDF_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityThe
ory`。
形式化陈述：gaussianPDF_ne_top {μ : Real} {v : Real>=0} {x : Real} : gaussianPDF μ v x
 != ∞
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma gaussianPDF_ne_top {μ : ℝ} {v : ℝ≥0} {x : ℝ} : gaussianPDF μ v x ≠ ∞ := by simp [gaussianPDF]

@[simp]
/-
**ProbabilityTheory.support_gaussianPDF** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTh
eory`。
形式化陈述：support_gaussianPDF {μ : Real} {v : Real>=0} (hv : v != 0) : Function.supp
ort (gaussianPDF μ v) = Set.univ
参数：hv : v != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `ProbabilityTheory.gaussianPDF_pos`：gaussianPDF_pos (μ : Real) {v : Real>
=0} (hv : v != 0) (x : Real) : 0 < gaussianPDF μ v x
-/
lemma support_gaussianPDF {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0) :
    Function.support (gaussianPDF μ v) = Set.univ := by
  ext x
  simp only [Set.mem_univ, iff_true]
  exact (gaussianPDF_pos _ hv x).ne'

@[fun_prop]
/-
**ProbabilityTheory.measurable_uncurry_gaussianPDF** 是 Mathlib 中的一个引理，位于命名空间 `Pr
obabilityTheory`。
形式化陈述：measurable_uncurry_gaussianPDF : Measurable (fun (μ, v, x) => gaussianPDF 
μ v x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.ennreal_ofReal`：Measurable.ennreal_ofReal {f : α -> Real} (hf
 : Measurable f) : Measurable fun x => ENNReal.ofReal (f x)
· 使用引理 `ProbabilityTheory.measurable_uncurry_gaussianPDFReal`：measurable_uncurry
_gaussianPDFReal : Measurable (fun (μ, v, x) => gaussianPDFReal μ v x)
-/
lemma measurable_uncurry_gaussianPDF : Measurable (fun (μ, v, x) ↦ gaussianPDF μ v x) :=
  Measurable.ennreal_ofReal (by fun_prop)
/-
**ProbabilityTheory.measurable_gaussianPDF** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory`。
形式化陈述：measurable_gaussianPDF (μ : Real) (v : Real>=0) : Measurable (gaussianPDF 
μ v)
参数：μ : Real；v : Real>=0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
· 使用引理 `ProbabilityTheory.measurable_uncurry_gaussianPDF`：measurable_uncurry_gau
ssianPDF : Measurable (fun (μ, v, x) => gaussianPDF μ v x)
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
-/
lemma measurable_gaussianPDF (μ : ℝ) (v : ℝ≥0) : Measurable (gaussianPDF μ v) := by
  fun_prop

@[fun_prop]
/-
**ProbabilityTheory.stronglyMeasurable_uncurry_gaussianPDF** 是 Mathlib 中的一个引理，位于
命名空间 `ProbabilityTheory`。
形式化陈述：stronglyMeasurable_uncurry_gaussianPDF : StronglyMeasurable (fun (μ, v, x)
 => gaussianPDF μ v x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.stronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {f : α → 
β} {mα : MeasurableSpace α} [inst : MeasurableSpace β]   [inst_1 : TopologicalSp
ace β] [Topological…
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `ENNReal.instMetrizableSpace`：TopologicalSpace.MetrizableSpace ENNReal
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用引理 `ProbabilityTheory.measurable_uncurry_gaussianPDF`：measurable_uncurry_gau
ssianPDF : Measurable (fun (μ, v, x) => gaussianPDF μ v x)
-/
lemma stronglyMeasurable_uncurry_gaussianPDF :
    StronglyMeasurable (fun (μ, v, x) ↦ gaussianPDF μ v x) :=
  measurable_uncurry_gaussianPDF.stronglyMeasurable
/-
**ProbabilityTheory.stronglyMeasurable_gaussianPDF** 是 Mathlib 中的一个引理，位于命名空间 `Pr
obabilityTheory`。
形式化陈述：stronglyMeasurable_gaussianPDF (μ : Real) (v : Real>=0) : StronglyMeasurab
le (gaussianPDF μ v)
参数：μ : Real；v : Real>=0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.comp_measurable`：comp_measurable [Topol
ogicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ} {f : α -> β} {g :
 γ -> α} (hf : StronglyMeasurable f) (…
· 使用引理 `ProbabilityTheory.stronglyMeasurable_uncurry_gaussianPDF`：stronglyMeasur
able_uncurry_gaussianPDF : StronglyMeasurable (fun (μ, v, x) => gaussianPDF μ v 
x)
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
-/
lemma stronglyMeasurable_gaussianPDF (μ : ℝ) (v : ℝ≥0) :
    StronglyMeasurable (gaussianPDF μ v) := by
  fun_prop

@[simp]
/-
**ProbabilityTheory.lintegral_gaussianPDF_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `Prob
abilityTheory`。
形式化陈述：lintegral_gaussianPDF_eq_one (μ : Real) {v : Real>=0} (h : v != 0) : ∫⁻ x,
 gaussianPDF μ v x = 1
参数：μ : Real；h : v != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.lintegral_gaussianPDFReal_eq_one`：lintegral_gaussianPD
FReal_eq_one (μ : Real) {v : Real>=0} (h : v != 0) : ∫⁻ x, ENNReal.ofReal (gauss
ianPDFReal μ v x) = 1
-/
lemma lintegral_gaussianPDF_eq_one (μ : ℝ) {v : ℝ≥0} (h : v ≠ 0) :
    ∫⁻ x, gaussianPDF μ v x = 1 :=
  lintegral_gaussianPDFReal_eq_one μ h

end GaussianPDF

section GaussianReal

/-- A Gaussian distribution on `ℝ` with mean `μ` and variance `v`. -/
@[wikidata Q133871]
noncomputable
/-
**ProbabilityTheory.gaussianReal** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory`。
形式化陈述：gaussianReal (μ : Real) (v : Real>=0) : Measure Real
参数：μ : Real；v : Real>=0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def gaussianReal (μ : ℝ) (v : ℝ≥0) : Measure ℝ :=
  if v = 0 then Measure.dirac μ else volume.withDensity (gaussianPDF μ v)
/-
**ProbabilityTheory.gaussianReal_of_var_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Proba
bilityTheory`。
形式化陈述：gaussianReal_of_var_ne_zero (μ : Real) {v : Real>=0} (hv : v != 0) : gauss
ianReal μ v = volume.withDensity (gaussianPDF μ v)
参数：μ : Real；hv : v != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
lemma gaussianReal_of_var_ne_zero (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    gaussianReal μ v = volume.withDensity (gaussianPDF μ v) := if_neg hv

@[simp]
/-
**ProbabilityTheory.gaussianReal_zero_var** 是 Mathlib 中的一个引理，位于命名空间 `Probability
Theory`。
形式化陈述：gaussianReal_zero_var (μ : Real) : gaussianReal μ 0 = Measure.dirac μ
参数：μ : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
lemma gaussianReal_zero_var (μ : ℝ) : gaussianReal μ 0 = Measure.dirac μ := if_pos rfl
/-
**ProbabilityTheory.instIsProbabilityMeasureGaussianReal** 是 Mathlib 中的一个实例，位于命名
空间 `ProbabilityTheory`。
形式化陈述：instIsProbabilityMeasureGaussianReal (μ : Real) (v : Real>=0) : IsProbabil
ityMeasure (gaussianReal μ v) where measure_univ
参数：μ : Real；v : Real>=0。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.gaussianReal_zero_var`：gaussianReal_zero_var (μ : Real
) : gaussianReal μ 0 = Measure.dirac μ
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `MeasureTheory.Measure.dirac.isProbabilityMeasure`：∀ {α : Type u_1} [inst
 : MeasurableSpace α] {x : α}, MeasureTheory.IsProbabilityMeasure (MeasureTheory
.Measure.dirac x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ProbabilityTheory.gaussianReal_of_var_ne_zero`：gaussianReal_of_var_ne_ze
ro (μ : Real) {v : Real>=0} (hv : v != 0) : gaussianReal μ v = volume.withDensit
y (gaussianPDF μ v)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MeasureTheory.withDensity_apply`：withDensity_apply (f : α -> Real>=0∞) {
s : Set α} (hs : MeasurableSet s) : μ.withDensity f s = ∫⁻ a in s, f a ∂μ
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
· 使用引理 `ProbabilityTheory.lintegral_gaussianPDF_eq_one`：lintegral_gaussianPDF_eq
_one (μ : Real) {v : Real>=0} (h : v != 0) : ∫⁻ x, gaussianPDF μ v x = 1
-/
instance instIsProbabilityMeasureGaussianReal (μ : ℝ) (v : ℝ≥0) :
    IsProbabilityMeasure (gaussianReal μ v) where
  measure_univ := by by_cases h : v = 0 <;> simp [gaussianReal_of_var_ne_zero, h]
/-
**ProbabilityTheory.nullSingletonClass_gaussianReal** 是 Mathlib 中的一个引理，位于命名空间 `P
robabilityTheory`。
形式化陈述：nullSingletonClass_gaussianReal {μ : Real} {v : Real>=0} (h : v != 0) : Nu
llSingletonClass (gaussianReal μ v)
参数：h : v != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.gaussianReal_of_var_ne_zero`：gaussianReal_of_var_ne_ze
ro (μ : Real) {v : Real>=0} (hv : v != 0) : gaussianReal μ v = volume.withDensit
y (gaussianPDF μ v)
-/
lemma nullSingletonClass_gaussianReal {μ : ℝ} {v : ℝ≥0} (h : v ≠ 0) :
    NullSingletonClass (gaussianReal μ v) := by
  rw [gaussianReal_of_var_ne_zero _ h]
  infer_instance

@[deprecated (since := "2026-06-09")]
alias noAtoms_gaussianReal := nullSingletonClass_gaussianReal
/-
**ProbabilityTheory.gaussianReal_apply** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityThe
ory`。
形式化陈述：gaussianReal_apply (μ : Real) {v : Real>=0} (hv : v != 0) (s : Set Real) :
 gaussianReal μ v s = ∫⁻ x in s, gaussianPDF μ v x
参数：μ : Real；hv : v != 0；s : Set Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.gaussianReal_of_var_ne_zero`：gaussianReal_of_var_ne_ze
ro (μ : Real) {v : Real>=0} (hv : v != 0) : gaussianReal μ v = volume.withDensit
y (gaussianPDF μ v)
· 使用定理 `MeasureTheory.withDensity_apply'`：withDensity_apply' [SFinite μ] (f : α 
-> Real>=0∞) (s : Set α) : μ.withDensity f s = ∫⁻ a in s, f a ∂μ
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
-/
lemma gaussianReal_apply (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (s : Set ℝ) :
    gaussianReal μ v s = ∫⁻ x in s, gaussianPDF μ v x := by
  rw [gaussianReal_of_var_ne_zero _ hv, withDensity_apply' _ s]
/-
**ProbabilityTheory.gaussianReal_apply_eq_integral** 是 Mathlib 中的一个引理，位于命名空间 `Pr
obabilityTheory`。
形式化陈述：gaussianReal_apply_eq_integral (μ : Real) {v : Real>=0} (hv : v != 0) (s :
 Set Real) : gaussianReal μ v s = ENNReal.ofReal (∫ x in s, gaussianPDFReal μ v 
x)
参数：μ : Real；hv : v != 0；s : Set Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.gaussianReal_apply`：gaussianReal_apply (μ : Real) {v :
 Real>=0} (hv : v != 0) (s : Set Real) : gaussianReal μ v s = ∫⁻ x in s, gaussia
nPDF μ v x
· 使用定理 `MeasureTheory.ofReal_integral_eq_lintegral_ofReal`：ofReal_integral_eq_li
ntegral_ofReal {f : α -> Real} (hfi : Integrable f μ) (f_nn : 0 <=ᵐ[μ] f) : ENNR
eal.ofReal (∫ x, f x ∂μ) = ∫⁻ x, ENNRea…
· 使用定理 `MeasureTheory.Integrable.restrict`：∀ {α : Type u_1} {m : MeasurableSpace
 α} {μ : MeasureTheory.Measure α} {ε : Type u_8} [inst : TopologicalSpace ε]   [
inst_1 : ContinuousENor…
· 使用引理 `ProbabilityTheory.integrable_gaussianPDFReal`：integrable_gaussianPDFReal
 (μ : Real) (v : Real>=0) : Integrable (gaussianPDFReal μ v)
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.gaussianPDFReal_nonneg`：gaussianPDFReal_nonneg (μ : Re
al) (v : Real>=0) (x : Real) : 0 <= gaussianPDFReal μ v x
-/
lemma gaussianReal_apply_eq_integral (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (s : Set ℝ) :
    gaussianReal μ v s = ENNReal.ofReal (∫ x in s, gaussianPDFReal μ v x) := by
  rw [gaussianReal_apply _ hv s, ofReal_integral_eq_lintegral_ofReal]
  · rfl
  · exact (integrable_gaussianPDFReal _ _).restrict
  · exact ae_of_all _ (gaussianPDFReal_nonneg _ _)
/-
**ProbabilityTheory.gaussianReal_absolutelyContinuous** 是 Mathlib 中的一个引理，位于命名空间 
`ProbabilityTheory`。
形式化陈述：gaussianReal_absolutelyContinuous (μ : Real) {v : Real>=0} (hv : v != 0) :
 gaussianReal μ v ≪ volume
参数：μ : Real；hv : v != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.gaussianReal_of_var_ne_zero`：gaussianReal_of_var_ne_ze
ro (μ : Real) {v : Real>=0} (hv : v != 0) : gaussianReal μ v = volume.withDensit
y (gaussianPDF μ v)
· 使用定理 `MeasureTheory.withDensity_absolutelyContinuous`：withDensity_absolutelyCo
ntinuous {m : MeasurableSpace α} (μ : Measure α) (f : α -> Real>=0∞) : μ.withDen
sity f ≪ μ
-/
lemma gaussianReal_absolutelyContinuous (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    gaussianReal μ v ≪ volume := by
  rw [gaussianReal_of_var_ne_zero _ hv]
  exact withDensity_absolutelyContinuous _ _
/-
**ProbabilityTheory.gaussianReal_absolutelyContinuous'** 是 Mathlib 中的一个引理，位于命名空间
 `ProbabilityTheory`。
形式化陈述：gaussianReal_absolutelyContinuous' (μ : Real) {v : Real>=0} (hv : v != 0) 
: volume ≪ gaussianReal μ v
参数：μ : Real；hv : v != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.gaussianReal_of_var_ne_zero`：gaussianReal_of_var_ne_ze
ro (μ : Real) {v : Real>=0} (hv : v != 0) : gaussianReal μ v = volume.withDensit
y (gaussianPDF μ v)
· 使用引理 `MeasureTheory.withDensity_absolutelyContinuous'`：withDensity_absolutelyC
ontinuous' {μ : Measure α} {f : α -> Real>=0∞} (hf : AEMeasurable f μ) (hf_ne_ze
ro : forallᵐ x ∂μ, f x != 0) : μ ≪ μ.…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用引理 `ProbabilityTheory.measurable_gaussianPDF`：measurable_gaussianPDF (μ : Re
al) (v : Real>=0) : Measurable (gaussianPDF μ v)
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `ProbabilityTheory.gaussianPDF_pos`：gaussianPDF_pos (μ : Real) {v : Real>
=0} (hv : v != 0) (x : Real) : 0 < gaussianPDF μ v x
-/
lemma gaussianReal_absolutelyContinuous' (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    volume ≪ gaussianReal μ v := by
  rw [gaussianReal_of_var_ne_zero _ hv]
  refine withDensity_absolutelyContinuous' ?_ ?_
  · exact (measurable_gaussianPDF _ _).aemeasurable
  · exact ae_of_all _ (fun _ ↦ (gaussianPDF_pos _ hv _).ne')
/-
**ProbabilityTheory.rnDeriv_gaussianReal** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：rnDeriv_gaussianReal (μ : Real) (v : Real>=0) : ∂(gaussianReal μ v)/∂volum
e =ₐₛ gaussianPDF μ v
参数：μ : Real；v : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `ProbabilityTheory.gaussianReal_zero_var`：gaussianReal_zero_var (μ : Real
) : gaussianReal μ 0 = Measure.dirac μ
· 使用引理 `ProbabilityTheory.gaussianPDF_zero_var`：gaussianPDF_zero_var (μ : Real) 
: gaussianPDF μ 0 = 0
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Measure.eq_rnDeriv`：eq_rnDeriv [SigmaFinite ν] {s : Measur
e α} {f : α -> Real>=0∞} (hf : Measurable f) (hs : s ⟂ₘ ν) (hadd : μ = s + ν.wit
hDensity f) : f =ᵐ[ν] …
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
· 使用定理 `measurable_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace
 α] [inst_1 : MeasurableSpace β] [inst_2 : Zero α], Measurable 0
· 使用引理 `MeasureTheory.mutuallySingular_dirac`：mutuallySingular_dirac [Measurable
SingletonClass α] (x : α) (μ : Measure α) [NullSingletonClass μ] : Measure.dirac
 x ⟂ₘ μ
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `MeasureTheory.withDensity_zero`：withDensity_zero : μ.withDensity 0 = 0
（共 34 条，此处仅展示前 30 条）
-/
lemma rnDeriv_gaussianReal (μ : ℝ) (v : ℝ≥0) :
    ∂(gaussianReal μ v)/∂volume =ₐₛ gaussianPDF μ v := by
  by_cases hv : v = 0
  · simp only [hv, gaussianReal_zero_var, gaussianPDF_zero_var]
    refine (Measure.eq_rnDeriv measurable_zero (mutuallySingular_dirac μ volume) ?_).symm
    rw [withDensity_zero, add_zero]
  · rw [gaussianReal_of_var_ne_zero _ hv]
    exact Measure.rnDeriv_withDensity _ (measurable_gaussianPDF μ v)
/-
**ProbabilityTheory.integral_gaussianReal_eq_integral_smul** 是 Mathlib 中的一个引理，位于
命名空间 `ProbabilityTheory`。
形式化陈述：integral_gaussianReal_eq_integral_smul {E : Type*} [NormedAddCommGroup E] 
[NormedSpace Real E] {μ : Real} {v : Real>=0} {f : Real -> E} (hv : v != 0) : ∫ 
x, f x ∂(gaussianReal μ v) = ∫ x, gaussianPDFReal μ v x • f x
参数：hv : v != 0。
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
· 使用定理 `integral_withDensity_eq_integral_toReal_smul`：integral_withDensity_eq_in
tegral_toReal_smul {f : X -> Real>=0∞} (f_meas : Measurable f) (hf_lt_top : fora
llᵐ x ∂μ, f x < ∞) (g : X -> E) : …
· 使用引理 `ProbabilityTheory.measurable_gaussianPDF`：measurable_gaussianPDF (μ : Re
al) (v : Real>=0) : Measurable (gaussianPDF μ v)
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.gaussianPDF_lt_top`：gaussianPDF_lt_top {μ : Real} {v :
 Real>=0} {x : Real} : gaussianPDF μ v x < ∞
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ProbabilityTheory.toReal_gaussianPDF`：toReal_gaussianPDF {μ : Real} {v :
 Real>=0} (x : Real) : (gaussianPDF μ v x).toReal = gaussianPDFReal μ v x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma integral_gaussianReal_eq_integral_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : ℝ} {v : ℝ≥0} {f : ℝ → E} (hv : v ≠ 0) :
    ∫ x, f x ∂(gaussianReal μ v) = ∫ x, gaussianPDFReal μ v x • f x := by
  simp [gaussianReal, hv,
    integral_withDensity_eq_integral_toReal_smul (measurable_gaussianPDF _ _)
      (ae_of_all _ fun _ ↦ gaussianPDF_lt_top)]

@[fun_prop]
/-
**ProbabilityTheory.measurable_gaussianReal** 是 Mathlib 中的一个引理，位于命名空间 `Probabili
tyTheory`。
形式化陈述：measurable_gaussianReal : Measurable gaussianReal.uncurry
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.ite`：Measurable.ite {p : α -> Prop} {_ : DecidablePred p} (hp
 : MeasurableSet { a : α | p a }) (hf : Measurable f) (hg : Measurable g) : Meas
urab…
· 使用引理 `Measurable.eq_const`：Measurable.eq_const {_ : MeasurableSpace α} [Measur
ableSpace β] [MeasurableSingletonClass β] {f : α -> β} (hf : Measurable f) (a : 
β) : Meas…
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `NNReal.instSecondCountableTopology`：SecondCountableTopology NNReal
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `NNReal.instCompleteSpace`：CompleteSpace NNReal
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Measurable.snd`：Measurable.snd {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).2
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
· 使用定理 `MeasureTheory.Measure.measurable_dirac`：measurable_dirac : Measurable (M
easure.dirac : α -> Measure α)
· 使用定理 `Measurable.fst`：Measurable.fst {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).1
· 使用定理 `MeasureTheory.measurable_withDensity`：measurable_withDensity {β : Type*}
 [MeasurableSpace β] {f : β -> α -> Real>=0∞} [SFinite μ] (hf : Measurable f.unc
urry) : Measurable fun b =…
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
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用引理 `ProbabilityTheory.measurable_uncurry_gaussianPDF`：measurable_uncurry_gau
ssianPDF : Measurable (fun (μ, v, x) => gaussianPDF μ v x)
（共 31 条，此处仅展示前 30 条）
-/
lemma measurable_gaussianReal :
    Measurable gaussianReal.uncurry :=
  Measurable.ite (by measurability) (by fun_prop) (by fun_prop)

section Transformations

variable {μ : ℝ} {v : ℝ≥0}

/-
**ProbabilityTheory._root_.MeasurableEmbedding.gaussianReal_comap_apply** 是 Math
lib 中的一个引理，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MeasurableEmbedding.gaussianReal_comap_apply (hv : v ≠ 0)
    {f : ℝ → ℝ} (hf : MeasurableEmbedding f)
    {f' : ℝ → ℝ} (h_deriv : ∀ x, HasDerivAt f (f' x) x) {s : Set ℝ} (hs : MeasurableSet s) :
    (gaussianReal μ v).comap f s
      = ENNReal.ofReal (∫ x in s, |f' x| * gaussianPDFReal μ v (f x)) := by
  rw [gaussianReal_of_var_ne_zero _ hv, gaussianPDF_def]
  exact hf.withDensity_ofReal_comap_apply_eq_integral_abs_deriv_mul' hs h_deriv
    (ae_of_all _ (gaussianPDFReal_nonneg _ _)) (integrable_gaussianPDFReal _ _)
/-
**ProbabilityTheory._root_.MeasurableEquiv.gaussianReal_map_symm_apply** 是 Mathl
ib 中的一个引理，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MeasurableEquiv.gaussianReal_map_symm_apply (hv : v ≠ 0) (f : ℝ ≃ᵐ ℝ) {f' : ℝ → ℝ}
    (h_deriv : ∀ x, HasDerivAt f (f' x) x) {s : Set ℝ} (hs : MeasurableSet s) :
    (gaussianReal μ v).map f.symm s
      = ENNReal.ofReal (∫ x in s, |f' x| * gaussianPDFReal μ v (f x)) := by
  rw [gaussianReal_of_var_ne_zero _ hv, gaussianPDF_def]
  exact f.withDensity_ofReal_map_symm_apply_eq_integral_abs_deriv_mul' hs h_deriv
    (ae_of_all _ (gaussianPDFReal_nonneg _ _)) (integrable_gaussianPDFReal _ _)

/-- The map of a Gaussian distribution by addition of a constant is a Gaussian. -/
/-
**ProbabilityTheory.gaussianReal_map_add_const** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：gaussianReal_map_add_const (y : Real) : (gaussianReal μ v).map (· + y) = g
aussianReal (μ + y) v
参数：y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.gaussianReal_zero_var`：gaussianReal_zero_var (μ : Real
) : gaussianReal μ 0 = Measure.dirac μ
· 使用定理 `MeasureTheory.Measure.map_dirac`：∀ {α : Type u_1} {β : Type u_2} [inst :
 MeasurableSpace α] [inst_1 : MeasurableSpace β] [MeasurableSingletonClass α]   
[MeasurableSingletonC…
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
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
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `HasDerivAt.sub_const`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] 
{F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f : 𝕜
 → F} {f' …
· 使用定理 `hasDerivAt_id`：hasDerivAt_id : HasDerivAt id 1 x
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `MeasurableEquiv.gaussianReal_map_symm_apply`：∀ {μ : ℝ} {v : NNReal},   v
 ≠ 0 →     ∀ (f : ℝ ≃ᵐ ℝ) {f' : ℝ → ℝ},       (∀ (x : ℝ), HasDerivAt (⇑f) (f' x)
 x) →         ∀ {s : Set ℝ},     …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
The map of a Gaussian distribution by addition of a constant is a Gaussian.
-/
lemma gaussianReal_map_add_const (y : ℝ) :
    (gaussianReal μ v).map (· + y) = gaussianReal (μ + y) v := by
  by_cases hv : v = 0
  · simp [hv, gaussianReal_zero_var]
  let e : ℝ ≃ᵐ ℝ := (Homeomorph.addRight y).symm.toMeasurableEquiv
  have he' : ∀ x, HasDerivAt e ((fun _ ↦ 1) x) x := fun _ ↦ (hasDerivAt_id _).sub_const y
  change (gaussianReal μ v).map e.symm = gaussianReal (μ + y) v
  ext s' hs'
  rw [MeasurableEquiv.gaussianReal_map_symm_apply hv e he' hs']
  simp only [abs_one, one_mul]
  rw [gaussianReal_apply_eq_integral _ hv s']
  simp [e, gaussianPDFReal_sub _ y, Homeomorph.addRight, ← sub_eq_add_neg]

/-- The map of a Gaussian distribution by addition of a constant is a Gaussian. -/
/-
**ProbabilityTheory.gaussianReal_map_const_add** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：gaussianReal_map_const_add (y : Real) : (gaussianReal μ v).map (y + ·) = g
aussianReal (μ + y) v
参数：y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `ProbabilityTheory.gaussianReal_map_add_const`：gaussianReal_map_add_const
 (y : Real) : (gaussianReal μ v).map (· + y) = gaussianReal (μ + y) v

--- 原说明 ---
The map of a Gaussian distribution by addition of a constant is a Gaussian.
-/
lemma gaussianReal_map_const_add (y : ℝ) :
    (gaussianReal μ v).map (y + ·) = gaussianReal (μ + y) v := by
  simp_rw [add_comm y]
  exact gaussianReal_map_add_const y

set_option backward.isDefEq.respectTransparency.types false in
/-- The map of a Gaussian distribution by multiplication by a constant is a Gaussian. -/
/-
**ProbabilityTheory.gaussianReal_map_const_mul** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：gaussianReal_map_const_mul (c : Real) : (gaussianReal μ v).map (c * ·) = g
aussianReal (c * μ) (.mk (c ^ 2) (sq_nonneg _) * v)
参数：c : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.gaussianReal_zero_var`：gaussianReal_zero_var (μ : Real
) : gaussianReal μ 0 = Measure.dirac μ
· 使用定理 `MeasureTheory.Measure.map_dirac`：∀ {α : Type u_1} {β : Type u_2} [inst :
 MeasurableSpace α] [inst_1 : MeasurableSpace β] [MeasurableSingletonClass α]   
[MeasurableSingletonC…
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用引理 `MeasureTheory.Measure.map_const`：map_const (μ : Measure α) (c : β) : μ.m
ap (fun _ => c) = (μ Set.univ) • dirac c
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
（共 65 条，此处仅展示前 30 条）

--- 原说明 ---
The map of a Gaussian distribution by multiplication by a constant is a Gaussian
.
-/
lemma gaussianReal_map_const_mul (c : ℝ) :
    (gaussianReal μ v).map (c * ·) = gaussianReal (c * μ) (.mk (c ^ 2) (sq_nonneg _) * v) := by
  by_cases hv : v = 0
  · simp [hv, mul_zero, gaussianReal_zero_var]
  by_cases hc : c = 0
  · simp [hc, zero_mul]
  let e : ℝ ≃ᵐ ℝ := (Homeomorph.mulLeft₀ c hc).symm.toMeasurableEquiv
  have he' : ∀ x, HasDerivAt e ((fun _ ↦ c⁻¹) x) x := by
    suffices ∀ x, HasDerivAt (fun x => c⁻¹ * x) (c⁻¹ * 1) x by rwa [mul_one] at this
    exact fun _ ↦ HasDerivAt.const_mul _ (hasDerivAt_id _)
  change (gaussianReal μ v).map e.symm = gaussianReal (c * μ) (.mk (c ^ 2) (sq_nonneg _) * v)
  ext s' hs'
  rw [MeasurableEquiv.gaussianReal_map_symm_apply hv e he' hs',
    gaussianReal_apply_eq_integral _ _ s']
  swap
  · simp only [ne_eq, mul_eq_zero, hv, or_false]
    rw [← NNReal.coe_inj]
    simp [hc]
  simp only [e, Homeomorph.mulLeft₀,
    Equiv.mulLeft₀_symm_apply, Homeomorph.toMeasurableEquiv_coe, Homeomorph.homeomorph_mk_coe_symm,
    gaussianPDFReal_inv_mul hc]
  congr with x
  suffices |c⁻¹| * |c| = 1 by rw [← mul_assoc, this, one_mul]
  rw [abs_inv, inv_mul_cancel₀]
  rwa [ne_eq, abs_eq_zero]

/-- The map of a Gaussian distribution by multiplication by a constant is a Gaussian. -/
/-
**ProbabilityTheory.gaussianReal_map_mul_const** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：gaussianReal_map_mul_const (c : Real) : (gaussianReal μ v).map (· * c) = g
aussianReal (c * μ) (.mk (c ^ 2) (sq_nonneg _) * v)
参数：c : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `ProbabilityTheory.gaussianReal_map_const_mul`：gaussianReal_map_const_mul
 (c : Real) : (gaussianReal μ v).map (c * ·) = gaussianReal (c * μ) (.mk (c ^ 2)
 (sq_nonneg _) * v)

--- 原说明 ---
The map of a Gaussian distribution by multiplication by a constant is a Gaussian
.
-/
lemma gaussianReal_map_mul_const (c : ℝ) :
    (gaussianReal μ v).map (· * c) = gaussianReal (c * μ) (.mk (c ^ 2) (sq_nonneg _) * v) := by
  simp_rw [mul_comm _ c]
  exact gaussianReal_map_const_mul c
/-
**ProbabilityTheory.gaussianReal_map_neg** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：gaussianReal_map_neg : (gaussianReal μ v).map (fun x => -x) = gaussianReal
 (-μ) v
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `NNReal.mk.congr_simp`：∀ (x x_1 : ℝ) (e_x : x = x_1) (hx : 0 ≤ x), NNReal
.mk x hx = NNReal.mk x_1 ⋯
· 使用定理 `Even.neg_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistribNeg
 α] {n : ℕ}, Even n → ∀ (a : α), (-a) ^ n = a ^ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用引理 `ProbabilityTheory.gaussianReal_map_const_mul`：gaussianReal_map_const_mul
 (c : Real) : (gaussianReal μ v).map (c * ·) = gaussianReal (c * μ) (.mk (c ^ 2)
 (sq_nonneg _) * v)
-/
lemma gaussianReal_map_neg : (gaussianReal μ v).map (fun x ↦ -x) = gaussianReal (-μ) v := by
  simpa using gaussianReal_map_const_mul (μ := μ) (v := v) (-1)

/-- The map of a Gaussian distribution by multiplication by a constant is a Gaussian. -/
/-
**ProbabilityTheory.gaussianReal_map_div_const** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：gaussianReal_map_div_const (c : Real) : (gaussianReal μ v).map (· / c) = g
aussianReal (μ / c) (v / .mk (c ^ 2) (sq_nonneg _))
参数：c : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `NNReal.mk.congr_simp`：∀ (x x_1 : ℝ) (e_x : x = x_1) (hx : 0 ≤ x), NNReal
.mk x hx = NNReal.mk x_1 ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ProbabilityTheory.gaussianReal_map_mul_const`：gaussianReal_map_mul_const
 (c : Real) : (gaussianReal μ v).map (· * c) = gaussianReal (c * μ) (.mk (c ^ 2)
 (sq_nonneg _) * v)

--- 原说明 ---
The map of a Gaussian distribution by multiplication by a constant is a Gaussian
.
-/
lemma gaussianReal_map_div_const (c : ℝ) :
    (gaussianReal μ v).map (· / c) = gaussianReal (μ / c) (v / .mk (c ^ 2) (sq_nonneg _)) := by
  simp_rw [div_eq_mul_inv]
  convert! gaussianReal_map_mul_const c⁻¹ using 2 <;> rw [mul_comm]
  ext; simp
/-
**ProbabilityTheory.gaussianReal_map_sub_const** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：gaussianReal_map_sub_const (y : Real) : (gaussianReal μ v).map (· - y) = g
aussianReal (μ - y) v
参数：y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `ProbabilityTheory.gaussianReal_map_add_const`：gaussianReal_map_add_const
 (y : Real) : (gaussianReal μ v).map (· + y) = gaussianReal (μ + y) v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma gaussianReal_map_sub_const (y : ℝ) :
    (gaussianReal μ v).map (· - y) = gaussianReal (μ - y) v := by
  simp_rw [sub_eq_add_neg, gaussianReal_map_add_const]
/-
**ProbabilityTheory.gaussianReal_map_const_sub** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：gaussianReal_map_const_sub (y : Real) : (gaussianReal μ v).map (y - ·) = g
aussianReal (y - μ) v
参数：y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.map_map`：map_map {g : β -> γ} {f : α -> β} (hg : M
easurable g) (hf : Measurable f) : (μ.map f).map g = μ.map (g ∘ f)
· 使用定理 `Measurable.const_add`：∀ {M : Type u_2} {α : Type u_3} [inst : Measurable
Space M] [inst_1 : Add M] {m : MeasurableSpace α} {f : α → M}   [MeasurableAdd M
], Measura…
· 使用定理 `ContinuousAdd.measurableAdd`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Add γ]   [SeparatelyCont
inuousAdd γ], Mea…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
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
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `Measurable.fun_neg`：∀ {G : Type u_2} {α : Type u_3} [inst : Neg G] [inst
_1 : MeasurableSpace G] [MeasurableNeg G] {m : MeasurableSpace α}   {f : α → G},
 Measura…
· 使用定理 `ContinuousNeg.measurableNeg`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Neg γ]   [ContinuousNeg 
γ], MeasurableNeg…
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用引理 `ProbabilityTheory.gaussianReal_map_neg`：gaussianReal_map_neg : (gaussian
Real μ v).map (fun x => -x) = gaussianReal (-μ) v
· 使用引理 `ProbabilityTheory.gaussianReal_map_const_add`：gaussianReal_map_const_add
 (y : Real) : (gaussianReal μ v).map (y + ·) = gaussianReal (μ + y) v
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
lemma gaussianReal_map_const_sub (y : ℝ) :
    (gaussianReal μ v).map (y - ·) = gaussianReal (y - μ) v := by
  simp_rw [sub_eq_add_neg]
  have : (fun x ↦ y + -x) = (fun x ↦ y + x) ∘ fun x ↦ -x := by ext; simp
  rw [this, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_neg,
    gaussianReal_map_const_add, add_comm]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ}

/-- If `X` is a real random variable with Gaussian law with mean `μ` and variance `v`, then `X + y`
has Gaussian law with mean `μ + y` and variance `v`. -/
/-
**ProbabilityTheory.gaussianReal_add_const** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory`。
形式化陈述：gaussianReal_add_const (hX : HasLaw X (gaussianReal μ v) P) (y : Real) : H
asLaw (fun ω => X ω + y) (gaussianReal (μ + y) v) P
参数：hX : HasLaw X (gaussianReal μ v) P；y : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.HasLaw.comp`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : Mea
surableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheory.Measur
e 𝓧} {P : MeasureTh…
· 使用定理 `AEMeasurable.add_const`：∀ {M : Type u_2} {α : Type u_3} [inst : Measurab
leSpace M] [inst_1 : Add M] {m : MeasurableSpace α} {f : α → M}   {μ : MeasureTh
eory.Measure…
· 使用定理 `ContinuousAdd.measurableAdd`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Add γ]   [SeparatelyCont
inuousAdd γ], Mea…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
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
· 使用定理 `aemeasurable_id`：aemeasurable_id : AEMeasurable id μ
· 使用引理 `ProbabilityTheory.gaussianReal_map_add_const`：gaussianReal_map_add_const
 (y : Real) : (gaussianReal μ v).map (· + y) = gaussianReal (μ + y) v

--- 原说明 ---
If `X` is a real random variable with Gaussian law with mean `μ` and variance `v
`, then `X + y`
has Gaussian law with mean `μ + y` and variance `v`.
-/
lemma gaussianReal_add_const (hX : HasLaw X (gaussianReal μ v) P) (y : ℝ) :
    HasLaw (fun ω ↦ X ω + y) (gaussianReal (μ + y) v) P :=
  HasLaw.comp ⟨by fun_prop, gaussianReal_map_add_const y⟩ hX

/-- If `X` is a real random variable with Gaussian law with mean `μ` and variance `v`, then `y + X`
has Gaussian law with mean `μ + y` and variance `v`. -/
/-
**ProbabilityTheory.gaussianReal_const_add** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory`。
形式化陈述：gaussianReal_const_add (hX : HasLaw X (gaussianReal μ v) P) (y : Real) : H
asLaw (fun ω => y + X ω) (gaussianReal (μ + y) v) P
参数：hX : HasLaw X (gaussianReal μ v) P；y : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.HasLaw.comp`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : Mea
surableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheory.Measur
e 𝓧} {P : MeasureTh…
· 使用定理 `AEMeasurable.const_add`：∀ {M : Type u_2} {α : Type u_3} [inst : Measurab
leSpace M] [inst_1 : Add M] {m : MeasurableSpace α} {f : α → M}   {μ : MeasureTh
eory.Measure…
· 使用定理 `ContinuousAdd.measurableAdd`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Add γ]   [SeparatelyCont
inuousAdd γ], Mea…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
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
· 使用定理 `aemeasurable_id`：aemeasurable_id : AEMeasurable id μ
· 使用引理 `ProbabilityTheory.gaussianReal_map_const_add`：gaussianReal_map_const_add
 (y : Real) : (gaussianReal μ v).map (y + ·) = gaussianReal (μ + y) v

--- 原说明 ---
If `X` is a real random variable with Gaussian law with mean `μ` and variance `v
`, then `y + X`
has Gaussian law with mean `μ + y` and variance `v`.
-/
lemma gaussianReal_const_add (hX : HasLaw X (gaussianReal μ v) P) (y : ℝ) :
    HasLaw (fun ω ↦ y + X ω) (gaussianReal (μ + y) v) P :=
  HasLaw.comp ⟨by fun_prop, gaussianReal_map_const_add y⟩ hX

/-- If `X` is a real random variable with Gaussian law with mean `μ` and variance `v`, then `X - y`
has Gaussian law with mean `μ - y` and variance `v`. -/
/-
**ProbabilityTheory.gaussianReal_sub_const** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory`。
形式化陈述：gaussianReal_sub_const (hX : HasLaw X (gaussianReal μ v) P) (y : Real) : H
asLaw (fun ω => X ω - y) (gaussianReal (μ - y) v) P
参数：hX : HasLaw X (gaussianReal μ v) P；y : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.HasLaw.comp`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : Mea
surableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheory.Measur
e 𝓧} {P : MeasureTh…
· 使用定理 `AEMeasurable.sub_const`：∀ {G : Type u_2} {α : Type u_3} [inst : Measurab
leSpace G] [inst_1 : Sub G] {m : MeasurableSpace α} {f : α → G}   {μ : MeasureTh
eory.Measure…
· 使用定理 `ContinuousSub.measurableSub`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Sub γ]   [ContinuousSub 
γ], MeasurableSub…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `aemeasurable_id`：aemeasurable_id : AEMeasurable id μ
· 使用引理 `ProbabilityTheory.gaussianReal_map_sub_const`：gaussianReal_map_sub_const
 (y : Real) : (gaussianReal μ v).map (· - y) = gaussianReal (μ - y) v

--- 原说明 ---
If `X` is a real random variable with Gaussian law with mean `μ` and variance `v
`, then `X - y`
has Gaussian law with mean `μ - y` and variance `v`.
-/
lemma gaussianReal_sub_const (hX : HasLaw X (gaussianReal μ v) P) (y : ℝ) :
    HasLaw (fun ω ↦ X ω - y) (gaussianReal (μ - y) v) P :=
  HasLaw.comp ⟨by fun_prop, gaussianReal_map_sub_const y⟩ hX

/-- If `X` is a real random variable with Gaussian law with mean `μ` and variance `v`, then `c * X`
has Gaussian law with mean `c * μ` and variance `c ^ 2 * v`. -/
/-
**ProbabilityTheory.gaussianReal_const_mul** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory`。
形式化陈述：gaussianReal_const_mul (hX : HasLaw X (gaussianReal μ v) P) (c : Real) : H
asLaw (fun ω => c * X ω) (gaussianReal (c * μ) (.mk (c ^ 2) (sq_nonneg _) * v)) 
P
参数：hX : HasLaw X (gaussianReal μ v) P；c : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.HasLaw.comp`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : Mea
surableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheory.Measur
e 𝓧} {P : MeasureTh…
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `AEMeasurable.const_mul`：AEMeasurable.const_mul [MeasurableMul M] (hf : A
EMeasurable f μ) (c : M) : AEMeasurable (fun x => c * f x) μ
· 使用定理 `ContinuousMul.measurableMul`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Mul γ]   [SeparatelyCont
inuousMul γ], Mea…
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `aemeasurable_id`：aemeasurable_id : AEMeasurable id μ
· 使用引理 `ProbabilityTheory.gaussianReal_map_const_mul`：gaussianReal_map_const_mul
 (c : Real) : (gaussianReal μ v).map (c * ·) = gaussianReal (c * μ) (.mk (c ^ 2)
 (sq_nonneg _) * v)

--- 原说明 ---
If `X` is a real random variable with Gaussian law with mean `μ` and variance `v
`, then `c * X`
has Gaussian law with mean `c * μ` and variance `c ^ 2 * v`.
-/
lemma gaussianReal_const_mul (hX : HasLaw X (gaussianReal μ v) P) (c : ℝ) :
    HasLaw (fun ω ↦ c * X ω) (gaussianReal (c * μ) (.mk (c ^ 2) (sq_nonneg _) * v)) P :=
  HasLaw.comp ⟨by fun_prop, gaussianReal_map_const_mul c⟩ hX

/-- If `X` is a real random variable with Gaussian law with mean `μ` and variance `v`, then `X * c`
has Gaussian law with mean `c * μ` and variance `c ^ 2 * v`. -/
/-
**ProbabilityTheory.gaussianReal_mul_const** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory`。
形式化陈述：gaussianReal_mul_const (hX : HasLaw X (gaussianReal μ v) P) (c : Real) : H
asLaw (fun ω => X ω * c) (gaussianReal (c * μ) (.mk (c ^ 2) (sq_nonneg _) * v)) 
P
参数：hX : HasLaw X (gaussianReal μ v) P；c : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.HasLaw.comp`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : Mea
surableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheory.Measur
e 𝓧} {P : MeasureTh…
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `AEMeasurable.mul_const`：AEMeasurable.mul_const [MeasurableMul M] (hf : A
EMeasurable f μ) (c : M) : AEMeasurable (fun x => f x * c) μ
· 使用定理 `ContinuousMul.measurableMul`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Mul γ]   [SeparatelyCont
inuousMul γ], Mea…
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `aemeasurable_id`：aemeasurable_id : AEMeasurable id μ
· 使用引理 `ProbabilityTheory.gaussianReal_map_mul_const`：gaussianReal_map_mul_const
 (c : Real) : (gaussianReal μ v).map (· * c) = gaussianReal (c * μ) (.mk (c ^ 2)
 (sq_nonneg _) * v)

--- 原说明 ---
If `X` is a real random variable with Gaussian law with mean `μ` and variance `v
`, then `X * c`
has Gaussian law with mean `c * μ` and variance `c ^ 2 * v`.
-/
lemma gaussianReal_mul_const (hX : HasLaw X (gaussianReal μ v) P) (c : ℝ) :
    HasLaw (fun ω ↦ X ω * c) (gaussianReal (c * μ) (.mk (c ^ 2) (sq_nonneg _) * v)) P :=
  HasLaw.comp ⟨by fun_prop, gaussianReal_map_mul_const c⟩ hX
/-
**ProbabilityTheory.gaussianReal_neg** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheor
y`。
形式化陈述：gaussianReal_neg (hX : HasLaw X (gaussianReal μ v) P) : HasLaw (-X) (gauss
ianReal (-μ) v) P
参数：hX : HasLaw X (gaussianReal μ v) P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.neg_def`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : (i : ι) → Neg (G
 i)] (f : (i : ι) → G i), -f = fun i => -f i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `ProbabilityTheory.HasLaw.comp`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : Mea
surableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheory.Measur
e 𝓧} {P : MeasureTh…
· 使用定理 `AEMeasurable.fun_neg`：∀ {G : Type u_2} {α : Type u_3} [inst : Neg G] [in
st_1 : MeasurableSpace G] [MeasurableNeg G] {m : MeasurableSpace α}   {f : α → G
} {μ : Mea…
· 使用定理 `ContinuousNeg.measurableNeg`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Neg γ]   [ContinuousNeg 
γ], MeasurableNeg…
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `aemeasurable_id`：aemeasurable_id : AEMeasurable id μ
· 使用引理 `ProbabilityTheory.gaussianReal_map_neg`：gaussianReal_map_neg : (gaussian
Real μ v).map (fun x => -x) = gaussianReal (-μ) v
-/
lemma gaussianReal_neg (hX : HasLaw X (gaussianReal μ v) P) :
    HasLaw (-X) (gaussianReal (-μ) v) P := by
  rw [Pi.neg_def, ← Function.comp_def]
  exact HasLaw.comp ⟨by fun_prop, gaussianReal_map_neg⟩ hX

/-- If `X` is a real random variable with Gaussian law with mean `μ` and variance `v`, then `X * c`
has Gaussian law with mean `c * μ` and variance `c ^ 2 * v`. -/
/-
**ProbabilityTheory.gaussianReal_div_const** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory`。
形式化陈述：gaussianReal_div_const (hX : HasLaw X (gaussianReal μ v) P) (c : Real) : H
asLaw (fun ω => X ω / c) (gaussianReal (μ / c) (v / .mk (c ^ 2) (sq_nonneg _))) 
P
参数：hX : HasLaw X (gaussianReal μ v) P；c : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.HasLaw.comp`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : Mea
surableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheory.Measur
e 𝓧} {P : MeasureTh…
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `AEMeasurable.div_const`：AEMeasurable.div_const [MeasurableDiv G] (hf : A
EMeasurable f μ) (c : G) : AEMeasurable (fun x => f x / c) μ
· 使用定理 `measurableDiv_of_mul_inv`：∀ (G : Type u_2) [inst : MeasurableSpace G] [i
nst_1 : DivInvMonoid G] [MeasurableMul G] [MeasurableInv G],   MeasurableDiv G
· 使用定理 `ContinuousMul.measurableMul`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Mul γ]   [SeparatelyCont
inuousMul γ], Mea…
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
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
· 使用定理 `aemeasurable_id`：aemeasurable_id : AEMeasurable id μ
· 使用引理 `ProbabilityTheory.gaussianReal_map_div_const`：gaussianReal_map_div_const
 (c : Real) : (gaussianReal μ v).map (· / c) = gaussianReal (μ / c) (v / .mk (c 
^ 2) (sq_nonneg _))

--- 原说明 ---
If `X` is a real random variable with Gaussian law with mean `μ` and variance `v
`, then `X * c`
has Gaussian law with mean `c * μ` and variance `c ^ 2 * v`.
-/
lemma gaussianReal_div_const (hX : HasLaw X (gaussianReal μ v) P) (c : ℝ) :
    HasLaw (fun ω ↦ X ω / c) (gaussianReal (μ / c) (v / .mk (c ^ 2) (sq_nonneg _))) P :=
  HasLaw.comp ⟨by fun_prop, gaussianReal_map_div_const c⟩ hX

/-- If `X` is a real random variable with Gaussian law with mean `μ` and variance `v`, then `y - X`
has Gaussian law with mean `y - μ` and variance `v`. -/
/-
**ProbabilityTheory.gaussianReal_const_sub** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory`。
形式化陈述：gaussianReal_const_sub (hX : HasLaw X (gaussianReal μ v) P) (y : Real) : H
asLaw (fun ω => y - X ω) (gaussianReal (y - μ) v) P
参数：hX : HasLaw X (gaussianReal μ v) P；y : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.HasLaw.comp`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : Mea
surableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheory.Measur
e 𝓧} {P : MeasureTh…
· 使用定理 `AEMeasurable.const_sub`：∀ {G : Type u_2} {α : Type u_3} [inst : Measurab
leSpace G] [inst_1 : Sub G] {m : MeasurableSpace α} {f : α → G}   {μ : MeasureTh
eory.Measure…
· 使用定理 `ContinuousSub.measurableSub`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Sub γ]   [ContinuousSub 
γ], MeasurableSub…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `aemeasurable_id`：aemeasurable_id : AEMeasurable id μ
· 使用引理 `ProbabilityTheory.gaussianReal_map_const_sub`：gaussianReal_map_const_sub
 (y : Real) : (gaussianReal μ v).map (y - ·) = gaussianReal (y - μ) v

--- 原说明 ---
If `X` is a real random variable with Gaussian law with mean `μ` and variance `v
`, then `y - X`
has Gaussian law with mean `y - μ` and variance `v`.
-/
lemma gaussianReal_const_sub (hX : HasLaw X (gaussianReal μ v) P) (y : ℝ) :
    HasLaw (fun ω ↦ y - X ω) (gaussianReal (y - μ) v) P :=
  HasLaw.comp ⟨by fun_prop, gaussianReal_map_const_sub y⟩ hX

end Transformations

section CharacteristicFunction

open Real Complex

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {p : Measure Ω} {μ : ℝ} {v : ℝ≥0} {X : Ω → ℝ}

-- see https://github.com/leanprover-community/mathlib4/issues/29041
set_option linter.unusedSimpArgs false in
/-- The complex moment-generating function of a Gaussian distribution with mean `μ` and variance `v`
is given by `z ↦ exp (z * μ + v * z ^ 2 / 2)`. -/
/-
**ProbabilityTheory.complexMGF_id_gaussianReal** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：complexMGF_id_gaussianReal (z : Complex) : complexMGF id (gaussianReal μ v
) z = cexp (z * μ + v * z ^ 2 / 2)
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `ProbabilityTheory.gaussianReal_zero_var`：gaussianReal_zero_var (μ : Real
) : gaussianReal μ 0 = Measure.dirac μ
· 使用定理 `MeasureTheory.integral_dirac`：integral_dirac [MeasurableSpace α] [Measur
ableSingletonClass α] (f : α -> E) (a : α) : ∫ x, f x ∂Measure.dirac a = f a
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ProbabilityTheory.integral_gaussianReal_eq_integral_smul`：integral_gauss
ianReal_eq_integral_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
 {μ : Real} {v : Real>=0} {f : Real -> E} (hv …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `Complex.ofReal_inv`：ofReal_inv (r : Real) : ((r⁻¹ : Real) : Complex) = (
r : Complex)⁻¹
· 使用定理 `Complex.ofReal_exp`：ofReal_exp (x : Real) : (Real.exp x : Complex) = exp
 x
（共 200 条，此处仅展示前 30 条）

--- 原说明 ---
The complex moment-generating function of a Gaussian distribution with mean `μ` 
and variance `v`
is given by `z ↦ exp (z * μ + v * z ^ 2 / 2)`.
-/
theorem complexMGF_id_gaussianReal (z : ℂ) :
    complexMGF id (gaussianReal μ v) z = cexp (z * μ + v * z ^ 2 / 2) := by
  by_cases hv : v = 0
  · simp [complexMGF, hv]
  calc ∫ x, cexp (z * x) ∂gaussianReal μ v
    _ = ∫ x, gaussianPDFReal μ v x * cexp (z * x) ∂ℙ := by
      simp_rw [integral_gaussianReal_eq_integral_smul hv, Complex.real_smul]
    _ = (√(2 * π * v))⁻¹
        * ∫ x : ℝ, cexp (-(2 * v)⁻¹ * x ^ 2 + (z + μ / v) * x + -μ ^ 2 / (2 * v)) ∂ℙ := by
      unfold gaussianPDFReal
      push_cast
      simp_rw [mul_assoc, integral_const_mul, ← Complex.exp_add]
      congr with x
      congr 1
      ring
    _ = (√(2 * π * v))⁻¹ * (π / - -(2 * v)⁻¹) ^ (1 / 2 : ℂ)
        * cexp (-μ ^ 2 / (2 * v) - (z + μ / v) ^ 2 / (4 * -(2 * v)⁻¹)) := by
      rw [integral_cexp_quadratic (by simpa using pos_iff_ne_zero.mpr hv), ← mul_assoc]
    _ = 1 * cexp (-μ ^ 2 / (2 * v) - (z + μ / v) ^ 2 / (4 * -(2 * v)⁻¹)) := by
      congr 1
      simp only [field, sqrt_eq_rpow, one_div, ofReal_inv, NNReal.coe_inv, NNReal.coe_mul,
        NNReal.coe_ofNat, ofReal_mul, ofReal_ofNat, neg_neg, div_inv_eq_mul,
        ne_eq, ofReal_eq_zero, rpow_eq_zero, not_false_eq_true]
      rw [Complex.ofReal_cpow (by positivity)]
      push_cast
      ring_nf
    _ = cexp (z * μ + v * z ^ 2 / 2) := by
      rw [one_mul]
      congr 1
      have : (v : ℂ) ≠ 0 := by simpa
      simp [field]
      ring

/-- The complex moment-generating function of a random variable with Gaussian distribution
with mean `μ` and variance `v` is given by `z ↦ exp (z * μ + v * z ^ 2 / 2)`. -/
/-
**ProbabilityTheory.complexMGF_gaussianReal** 是 Mathlib 中的一个定理，位于命名空间 `Probabili
tyTheory`。
形式化陈述：complexMGF_gaussianReal (hX : p.map X = gaussianReal μ v) (z : Complex) : 
complexMGF X p z = cexp (z * μ + v * z ^ 2 / 2)
参数：hX : p.map X = gaussianReal μ v；z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `aemeasurable_of_map_neZero`：aemeasurable_of_map_neZero {μ : Measure α} {
f : α -> β} (h : NeZero (μ.map f)) : AEMeasurable f μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.IsProbabilityMeasure.neZero`：∀ {α : Type u_1} {m0 : Measur
ableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ
], NeZero μ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.complexMGF_id_map`：complexMGF_id_map (hX : AEMeasurabl
e X μ) : complexMGF id (μ.map X) = complexMGF X μ
· 使用定理 `ProbabilityTheory.complexMGF_id_gaussianReal`：complexMGF_id_gaussianReal
 (z : Complex) : complexMGF id (gaussianReal μ v) z = cexp (z * μ + v * z ^ 2 / 
2)

--- 原说明 ---
The complex moment-generating function of a random variable with Gaussian distri
bution
with mean `μ` and variance `v` is given by `z ↦ exp (z * μ + v * z ^ 2 / 2)`.
-/
theorem complexMGF_gaussianReal (hX : p.map X = gaussianReal μ v) (z : ℂ) :
    complexMGF X p z = cexp (z * μ + v * z ^ 2 / 2) := by
  have hX_meas : AEMeasurable X p := aemeasurable_of_map_neZero (by rw [hX]; infer_instance)
  rw [← complexMGF_id_map hX_meas, hX, complexMGF_id_gaussianReal]

/-- The characteristic function of a Gaussian distribution with mean `μ` and variance `v`
is given by `t ↦ exp (t * μ - v * t ^ 2 / 2)`. -/
/-
**ProbabilityTheory.charFun_gaussianReal** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：charFun_gaussianReal (t : Real) : charFun (gaussianReal μ v) t = cexp (t *
 μ * I - v * t ^ 2 / 2)
参数：t : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.complexMGF_id_mul_I`：complexMGF_id_mul_I {μ : Measure 
Real} (t : Real) : complexMGF id μ (t * I) = charFun μ t
· 使用定理 `ProbabilityTheory.complexMGF_id_gaussianReal`：complexMGF_id_gaussianReal
 (z : Complex) : complexMGF id (gaussianReal μ v) z = cexp (z * μ + v * z ^ 2 / 
2)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `Complex.I_sq`：I_sq : I ^ 2 = -1
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
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
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
（共 69 条，此处仅展示前 30 条）

--- 原说明 ---
The characteristic function of a Gaussian distribution with mean `μ` and varianc
e `v`
is given by `t ↦ exp (t * μ - v * t ^ 2 / 2)`.
-/
theorem charFun_gaussianReal (t : ℝ) :
    charFun (gaussianReal μ v) t = cexp (t * μ * I - v * t ^ 2 / 2) := by
  rw [← complexMGF_id_mul_I, complexMGF_id_gaussianReal]
  congr
  simp only [mul_pow, I_sq, mul_neg, mul_one, sub_eq_add_neg]
  ring_nf

/-- The moment-generating function of a random variable with Gaussian distribution
with mean `μ` and variance `v` is given by `t ↦ exp (μ * t + v * t ^ 2 / 2)`. -/
/-
**ProbabilityTheory.mgf_gaussianReal** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheor
y`。
形式化陈述：mgf_gaussianReal (hX : p.map X = gaussianReal μ v) (t : Real) : mgf X p t 
= rexp (μ * t + v * t ^ 2 / 2)
参数：hX : p.map X = gaussianReal μ v；t : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `aemeasurable_of_map_neZero`：aemeasurable_of_map_neZero {μ : Measure α} {
f : α -> β} (h : NeZero (μ.map f)) : AEMeasurable f μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.IsProbabilityMeasure.neZero`：∀ {α : Type u_1} {m0 : Measur
ableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ
], NeZero μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.mgf_id_map`：mgf_id_map (hX : AEMeasurable X μ) : mgf i
d (μ.map X) = mgf X μ
· 使用引理 `ProbabilityTheory.complexMGF_ofReal`：complexMGF_ofReal (x : Real) : comp
lexMGF X μ x = mgf X μ x
· 使用定理 `ProbabilityTheory.complexMGF_id_gaussianReal`：complexMGF_id_gaussianReal
 (z : Complex) : complexMGF id (gaussianReal μ v) z = cexp (z * μ + v * z ^ 2 / 
2)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂

--- 原说明 ---
The moment-generating function of a random variable with Gaussian distribution
with mean `μ` and variance `v` is given by `t ↦ exp (μ * t + v * t ^ 2 / 2)`.
-/
theorem mgf_gaussianReal (hX : p.map X = gaussianReal μ v) (t : ℝ) :
    mgf X p t = rexp (μ * t + v * t ^ 2 / 2) := by
  suffices (mgf X p t : ℂ) = rexp (μ * t + ↑v * t ^ 2 / 2) from mod_cast this
  have hX_meas : AEMeasurable X p := aemeasurable_of_map_neZero (by rw [hX]; infer_instance)
  rw [← mgf_id_map hX_meas, ← complexMGF_ofReal, hX, complexMGF_id_gaussianReal, mul_comm μ]
  norm_cast
/-
**ProbabilityTheory.mgf_fun_id_gaussianReal** 是 Mathlib 中的一个定理，位于命名空间 `Probabili
tyTheory`。
形式化陈述：mgf_fun_id_gaussianReal : mgf (fun x => x) (gaussianReal μ v) = fun t => r
exp (μ * t + v * t ^ 2 / 2)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.mgf_gaussianReal`：mgf_gaussianReal (hX : p.map X = gau
ssianReal μ v) (t : Real) : mgf X p t = rexp (μ * t + v * t ^ 2 / 2)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.map_id'`：map_id' : map (fun x => x) μ = μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mgf_fun_id_gaussianReal :
    mgf (fun x ↦ x) (gaussianReal μ v) = fun t ↦ rexp (μ * t + v * t ^ 2 / 2) := by
  ext t
  rw [mgf_gaussianReal]
  simp
/-
**ProbabilityTheory.mgf_id_gaussianReal** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTh
eory`。
形式化陈述：mgf_id_gaussianReal : mgf id (gaussianReal μ v) = fun t => rexp (μ * t + v
 * t ^ 2 / 2)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.mgf_fun_id_gaussianReal`：mgf_fun_id_gaussianReal : mgf
 (fun x => x) (gaussianReal μ v) = fun t => rexp (μ * t + v * t ^ 2 / 2)
-/
theorem mgf_id_gaussianReal : mgf id (gaussianReal μ v) = fun t ↦ rexp (μ * t + v * t ^ 2 / 2) :=
  mgf_fun_id_gaussianReal

/-- The cumulant-generating function of a random variable with Gaussian distribution
with mean `μ` and variance `v` is given by `t ↦ μ * t + v * t ^ 2 / 2`. -/
/-
**ProbabilityTheory.cgf_gaussianReal** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheor
y`。
形式化陈述：cgf_gaussianReal (hX : p.map X = gaussianReal μ v) (t : Real) : cgf X p t 
= μ * t + v * t ^ 2 / 2
参数：hX : p.map X = gaussianReal μ v；t : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.cgf.eq_1`：∀ {Ω : Type u_1} {m : MeasurableSpace Ω} (X 
: Ω → ℝ) (μ : MeasureTheory.Measure Ω) (t : ℝ),   ProbabilityTheory.cgf X μ t = 
Real.log (Probab…
· 使用定理 `ProbabilityTheory.mgf_gaussianReal`：mgf_gaussianReal (hX : p.map X = gau
ssianReal μ v) (t : Real) : mgf X p t = rexp (μ * t + v * t ^ 2 / 2)
· 使用定理 `Real.log_exp`：log_exp (x : Real) : log (exp x) = x

--- 原说明 ---
The cumulant-generating function of a random variable with Gaussian distribution
with mean `μ` and variance `v` is given by `t ↦ μ * t + v * t ^ 2 / 2`.
-/
theorem cgf_gaussianReal (hX : p.map X = gaussianReal μ v) (t : ℝ) :
    cgf X p t = μ * t + v * t ^ 2 / 2 := by
  rw [cgf, mgf_gaussianReal hX t, Real.log_exp]
/-
**ProbabilityTheory.integrable_exp_mul_gaussianReal** 是 Mathlib 中的一个引理，位于命名空间 `P
robabilityTheory`。
形式化陈述：integrable_exp_mul_gaussianReal (t : Real) : Integrable (fun x => rexp (t 
* x)) (gaussianReal μ v)
参数：t : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.mgf_pos_iff`：mgf_pos_iff [hμ : NeZero μ] : 0 < mgf X μ
 t ↔ Integrable (fun ω => exp (t * X ω)) μ
· 使用定理 `MeasureTheory.IsProbabilityMeasure.neZero`：∀ {α : Type u_1} {m0 : Measur
ableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ
], NeZero μ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ProbabilityTheory.mgf_gaussianReal`：mgf_gaussianReal (hX : p.map X = gau
ssianReal μ v) (t : Real) : mgf X p t = rexp (μ * t + v * t ^ 2 / 2)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.map_id'`：map_id' : map (fun x => x) μ = μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
-/
lemma integrable_exp_mul_gaussianReal (t : ℝ) :
    Integrable (fun x ↦ rexp (t * x)) (gaussianReal μ v) := by
  rw [← mgf_pos_iff, mgf_gaussianReal (μ := μ) (v := v) (by simp)]
  exact Real.exp_pos _

@[simp]
/-
**ProbabilityTheory.integrableExpSet_id_gaussianReal** 是 Mathlib 中的一个引理，位于命名空间 `
ProbabilityTheory`。
形式化陈述：integrableExpSet_id_gaussianReal : integrableExpSet id (gaussianReal μ v) 
= Set.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用引理 `ProbabilityTheory.integrable_exp_mul_gaussianReal`：integrable_exp_mul_ga
ussianReal (t : Real) : Integrable (fun x => rexp (t * x)) (gaussianReal μ v)
-/
lemma integrableExpSet_id_gaussianReal : integrableExpSet id (gaussianReal μ v) = Set.univ := by
  ext
  simpa [integrableExpSet] using integrable_exp_mul_gaussianReal _

@[simp]
/-
**ProbabilityTheory.integrableExpSet_fun_id_gaussianReal** 是 Mathlib 中的一个引理，位于命名
空间 `ProbabilityTheory`。
形式化陈述：integrableExpSet_fun_id_gaussianReal : integrableExpSet (fun x => x) (gaus
sianReal μ v) = Set.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.integrableExpSet_id_gaussianReal`：integrableExpSet_id_
gaussianReal : integrableExpSet id (gaussianReal μ v) = Set.univ
-/
lemma integrableExpSet_fun_id_gaussianReal :
    integrableExpSet (fun x ↦ x) (gaussianReal μ v) = Set.univ :=
  integrableExpSet_id_gaussianReal

end CharacteristicFunction

section Moments

variable {μ : ℝ} {v : ℝ≥0}

/-- The mean of a real Gaussian distribution `gaussianReal μ v` is its mean parameter `μ`. -/
@[simp]
/-
**ProbabilityTheory.integral_id_gaussianReal** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory`。
形式化陈述：integral_id_gaussianReal : ∫ x, x ∂gaussianReal μ v = μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.deriv_mgf_zero`：deriv_mgf_zero (h : 0 in interior (int
egrableExpSet X μ)) : deriv (mgf X μ) 0 = μ[X]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `ProbabilityTheory.integrableExpSet_fun_id_gaussianReal`：integrableExpSet
_fun_id_gaussianReal : integrableExpSet (fun x => x) (gaussianReal μ v) = Set.un
iv
· 使用定理 `interior_univ`：interior_univ : interior (univ : Set X) = univ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ProbabilityTheory.mgf_fun_id_gaussianReal`：mgf_fun_id_gaussianReal : mgf
 (fun x => x) (gaussianReal μ v) = fun t => rexp (μ * t + v * t ^ 2 / 2)
· 使用定理 `deriv_exp`：deriv_exp (hc : DifferentiableAt Real f x) : deriv (fun x => 
Real.exp (f x)) x = Real.exp (f x) * deriv f x
· 使用定理 `DifferentiableAt.fun_add`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type u_…
· 使用定理 `DifferentiableAt.const_mul`：DifferentiableAt.const_mul (ha : Differentia
bleAt 𝕜 a x) (b : 𝔸) : DifferentiableAt 𝕜 (fun y => b * a y) x
· 使用定理 `differentiableAt_id`：differentiableAt_id : DifferentiableAt 𝕜 id x
· 使用定理 `DifferentiableAt.div_const`：DifferentiableAt.div_const (hc : Differentia
bleAt 𝕜 c x) (d : 𝕜') : DifferentiableAt 𝕜 (fun x => c x / d) x
· 使用定理 `DifferentiableAt.fun_pow`：∀ {𝕜 : Type u_1} {𝔸 : Type u_2} {E : Type u_3}
 [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedRing 𝔸]   [inst_2 : NormedAd
dCommGroup E] …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Real.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `deriv_fun_add`：deriv_fun_add (hf : DifferentiableAt 𝕜 f x) (hg : Differe
ntiableAt 𝕜 g x) : deriv (fun y => f y + g y) x = deriv f x + deriv g x
· 使用定理 `deriv_fun_mul`：deriv_fun_mul (hc : DifferentiableAt 𝕜 c x) (hd : Differe
ntiableAt 𝕜 d x) : deriv (fun y => c y * d y) x = deriv c x * d x + c x * deriv 
d x
· 使用定理 `differentiableAt_const`：differentiableAt_const (c : F) : DifferentiableA
t 𝕜 (fun _ => c) x
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `deriv_const'`：deriv_const' : (deriv fun _ : 𝕜 => c) = fun _ => 0
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
The mean of a real Gaussian distribution `gaussianReal μ v` is its mean paramete
r `μ`.
-/
lemma integral_id_gaussianReal : ∫ x, x ∂gaussianReal μ v = μ := by
  rw [← deriv_mgf_zero (by simp), mgf_fun_id_gaussianReal, _root_.deriv_exp (by fun_prop)]
  simp only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
    add_zero, Real.exp_zero, one_mul]
  rw [deriv_fun_add (by fun_prop) (by fun_prop), deriv_fun_mul (by fun_prop) (by fun_prop)]
  simp

/-- The variance of a real Gaussian distribution `gaussianReal μ v` is
its variance parameter `v`. -/
@[simp]
/-
**ProbabilityTheory.variance_fun_id_gaussianReal** 是 Mathlib 中的一个引理，位于命名空间 `Prob
abilityTheory`。
形式化陈述：variance_fun_id_gaussianReal : Var[fun x => x; gaussianReal μ v] = v
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.variance_eq_integral`：variance_eq_integral (hX : AEMea
surable X μ) : Var[X; μ] = ∫ ω, (X ω - μ[X]) ^ 2 ∂μ
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ProbabilityTheory.integral_id_gaussianReal`：integral_id_gaussianReal : ∫
 x, x ∂gaussianReal μ v = μ
· 使用定理 `MeasureTheory.integral_map`：integral_map {β} [MeasurableSpace β] {φ : α 
-> β} (hφ : AEMeasurable φ μ) {f : β -> G} (hfm : AEStronglyMeasurable f (Measur
e.map φ μ)) : ∫ …
· 使用定理 `AEMeasurable.sub_const`：∀ {G : Type u_2} {α : Type u_3} [inst : Measurab
leSpace G] [inst_1 : Sub G] {m : MeasurableSpace α} {f : α → G}   {μ : MeasureTh
eory.Measure…
· 使用定理 `ContinuousSub.measurableSub`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Sub γ]   [ContinuousSub 
γ], MeasurableSub…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `aemeasurable_id`：aemeasurable_id : AEMeasurable id μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.fun_pow`：∀ {α : Type u_1} {β : Type u
_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Me
asure α}   {f : α → β} [inst_1 :…
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
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `ProbabilityTheory.gaussianReal_map_sub_const`：gaussianReal_map_sub_const
 (y : Real) : (gaussianReal μ v).map (· - y) = gaussianReal (μ - y) v
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ProbabilityTheory.iteratedDeriv_mgf_zero`：iteratedDeriv_mgf_zero (h : 0 
in interior (integrableExpSet X μ)) (n : Nat) : iteratedDeriv n (mgf X μ) 0 = μ[
X ^ n]
· 使用引理 `ProbabilityTheory.integrableExpSet_fun_id_gaussianReal`：integrableExpSet
_fun_id_gaussianReal : integrableExpSet (fun x => x) (gaussianReal μ v) = Set.un
iv
· 使用定理 `interior_univ`：interior_univ : interior (univ : Set X) = univ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
（共 86 条，此处仅展示前 30 条）

--- 原说明 ---
The variance of a real Gaussian distribution `gaussianReal μ v` is
its variance parameter `v`.
-/
lemma variance_fun_id_gaussianReal : Var[fun x ↦ x; gaussianReal μ v] = v := by
  rw [variance_eq_integral measurable_id'.aemeasurable]
  simp only [integral_id_gaussianReal]
  calc ∫ ω, (ω - μ) ^ 2 ∂gaussianReal μ v
  _ = ∫ ω, ω ^ 2 ∂(gaussianReal μ v).map (fun x ↦ x - μ) := by
    rw [integral_map (by fun_prop) (by fun_prop)]
  _ = ∫ ω, ω ^ 2 ∂(gaussianReal 0 v) := by simp [gaussianReal_map_sub_const]
  _ = iteratedDeriv 2 (mgf (fun x ↦ x) (gaussianReal 0 v)) 0 := by
    rw [iteratedDeriv_mgf_zero] <;> simp
  _ = v := by
    rw [mgf_fun_id_gaussianReal, iteratedDeriv_succ, iteratedDeriv_one]
    simp only [zero_mul, zero_add]
    have : deriv (fun t ↦ rexp (v * t ^ 2 / 2)) = fun t ↦ v * t * rexp (v * t ^ 2 / 2) := by
      ext t
      rw [_root_.deriv_exp (by fun_prop)]
      simp only [deriv_div_const, differentiableAt_const, differentiableAt_fun_id, Nat.cast_ofNat,
        DifferentiableAt.fun_pow, deriv_fun_mul, deriv_const', zero_mul, deriv_fun_pow,
        Nat.add_one_sub_one, pow_one, deriv_id'', mul_one, zero_add]
      ring
    rw [this, deriv_fun_mul (by fun_prop) (by fun_prop), deriv_fun_mul (by fun_prop) (by fun_prop)]
    simp

/-- The variance of a real Gaussian distribution `gaussianReal μ v` is
its variance parameter `v`. -/
@[simp]
/-
**ProbabilityTheory.variance_id_gaussianReal** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory`。
形式化陈述：variance_id_gaussianReal : Var[id; gaussianReal μ v] = v
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.variance_fun_id_gaussianReal`：variance_fun_id_gaussian
Real : Var[fun x => x; gaussianReal μ v] = v

--- 原说明 ---
The variance of a real Gaussian distribution `gaussianReal μ v` is
its variance parameter `v`.
-/
lemma variance_id_gaussianReal : Var[id; gaussianReal μ v] = v :=
  variance_fun_id_gaussianReal

/-- All the moments of a real Gaussian distribution are finite. That is, the identity is in Lp for
all finite `p`. -/
/-
**ProbabilityTheory.memLp_id_gaussianReal** 是 Mathlib 中的一个引理，位于命名空间 `Probability
Theory`。
形式化陈述：memLp_id_gaussianReal (p : Real>=0) : MemLp id p (gaussianReal μ v)
参数：p : Real>=0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.memLp_of_mem_interior_integrableExpSet`：memLp_of_mem_i
nterior_integrableExpSet (h : 0 in interior (integrableExpSet X μ)) (p : Real>=0
) : MemLp X p μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.integrableExpSet_id_gaussianReal`：integrableExpSet_id_
gaussianReal : integrableExpSet id (gaussianReal μ v) = Set.univ
· 使用定理 `interior_univ`：interior_univ : interior (univ : Set X) = univ

--- 原说明 ---
All the moments of a real Gaussian distribution are finite. That is, the identit
y is in Lp for
all finite `p`.
-/
lemma memLp_id_gaussianReal (p : ℝ≥0) : MemLp id p (gaussianReal μ v) :=
  memLp_of_mem_interior_integrableExpSet (by simp) p

/-- All the moments of a real Gaussian distribution are finite. That is, the identity is in Lp for
all finite `p`. -/
/-
**ProbabilityTheory.memLp_id_gaussianReal'** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory`。
形式化陈述：memLp_id_gaussianReal' (p : Real>=0∞) (hp : p != ∞) : MemLp id p (gaussian
Real μ v)
参数：p : Real>=0∞；hp : p != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用引理 `ProbabilityTheory.memLp_id_gaussianReal`：memLp_id_gaussianReal (p : Real
>=0) : MemLp id p (gaussianReal μ v)

--- 原说明 ---
All the moments of a real Gaussian distribution are finite. That is, the identit
y is in Lp for
all finite `p`.
-/
lemma memLp_id_gaussianReal' (p : ℝ≥0∞) (hp : p ≠ ∞) : MemLp id p (gaussianReal μ v) := by
  lift p to ℝ≥0 using hp
  exact memLp_id_gaussianReal p

end Moments

/-- Two real Gaussian distributions are equal iff they have the same mean and variance. -/
/-
**ProbabilityTheory.gaussianReal_ext_iff** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：gaussianReal_ext_iff {μ₁ μ₂ : Real} {v₁ v₂ : Real>=0} : gaussianReal μ₁ v₁
 = gaussianReal μ₂ v₂ ↔ μ₁ = μ₂ ∧ v₁ = v₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.integral_id_gaussianReal`：integral_id_gaussianReal : ∫
 x, x ∂gaussianReal μ v = μ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用引理 `ProbabilityTheory.variance_id_gaussianReal`：variance_id_gaussianReal : V
ar[id; gaussianReal μ v] = v

--- 原说明 ---
Two real Gaussian distributions are equal iff they have the same mean and varian
ce.
-/
lemma gaussianReal_ext_iff {μ₁ μ₂ : ℝ} {v₁ v₂ : ℝ≥0} :
    gaussianReal μ₁ v₁ = gaussianReal μ₂ v₂ ↔ μ₁ = μ₂ ∧ v₁ = v₂ := by
  refine ⟨fun h ↦ ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  rw [← integral_id_gaussianReal (μ := μ₁) (v := v₁),
    ← integral_id_gaussianReal (μ := μ₂) (v := v₂), h]
  simp only [integral_id_gaussianReal, true_and]
  suffices (v₁ : ℝ) = v₂ by simpa
  rw [← variance_id_gaussianReal (μ := μ₁) (v := v₁),
    ← variance_id_gaussianReal (μ := μ₂) (v := v₂), h]

section LinearMap

variable {μ : ℝ} {v : ℝ≥0}

/-
**ProbabilityTheory.gaussianReal_map_linearMap** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：gaussianReal_map_linearMap (L : Real ->ₗ[Real] Real) : (gaussianReal μ v).
map L = gaussianReal (L μ) ((L 1 ^ 2).toNNReal * v)
参数：L : Real ->ₗ[Real] Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Dual.apply_one_mul_eq`：Dual.apply_one_mul_eq (f : Dual R R) (r : R) : f 
1 * r = f r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `ProbabilityTheory.gaussianReal_map_const_mul`：gaussianReal_map_const_mul
 (c : Real) : (gaussianReal μ v).map (c * ·) = gaussianReal (c * μ) (.mk (c ^ 2)
 (sq_nonneg _) * v)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Even.pow_nonneg`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : LinearOr
der R] [IsOrderedRing R] [ExistsAddOfLE R] {n : ℕ},   Even n → ∀ (a : R), 0 ≤ a 
^ n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `even_two_mul`：even_two_mul (a : α) : Even (2 * a)
-/
lemma gaussianReal_map_linearMap (L : ℝ →ₗ[ℝ] ℝ) :
    (gaussianReal μ v).map L = gaussianReal (L μ) ((L 1 ^ 2).toNNReal * v) := by
  have : (L : ℝ → ℝ) = fun x ↦ L 1 * x := by simp
  rw [this, gaussianReal_map_const_mul]
  congr
  simp only [mul_one, left_eq_sup]
  positivity
/-
**ProbabilityTheory.gaussianReal_map_continuousLinearMap** 是 Mathlib 中的一个引理，位于命名
空间 `ProbabilityTheory`。
形式化陈述：gaussianReal_map_continuousLinearMap (L : Real ->L[Real] Real) : (gaussian
Real μ v).map L = gaussianReal (L μ) ((L 1 ^ 2).toNNReal * v)
参数：L : Real ->L[Real] Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.gaussianReal_map_linearMap`：gaussianReal_map_linearMap
 (L : Real ->ₗ[Real] Real) : (gaussianReal μ v).map L = gaussianReal (L μ) ((L 1
 ^ 2).toNNReal * v)
-/
lemma gaussianReal_map_continuousLinearMap (L : ℝ →L[ℝ] ℝ) :
    (gaussianReal μ v).map L = gaussianReal (L μ) ((L 1 ^ 2).toNNReal * v) :=
  gaussianReal_map_linearMap L

@[simp]
/-
**ProbabilityTheory.integral_linearMap_gaussianReal** 是 Mathlib 中的一个引理，位于命名空间 `P
robabilityTheory`。
形式化陈述：integral_linearMap_gaussianReal (L : Real ->ₗ[Real] Real) : ∫ x, L x ∂(gau
ssianReal μ v) = L μ
参数：L : Real ->ₗ[Real] Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_map`：integral_map {β} [MeasurableSpace β] {φ : α 
-> β} (hφ : AEMeasurable φ μ) {f : β -> G} (hfm : AEStronglyMeasurable f (Measur
e.map φ μ)) : ∫ …
· 使用定理 `Continuous.aemeasurable`：Continuous.aemeasurable {f : α -> γ} (h : Conti
nuous f) {μ : Measure α} : AEMeasurable f μ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `IsModuleTopology.continuous_of_linearMap`：continuous_of_linearMap (φ : A
 ->ₗ[R] B) : Continuous φ
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `aestronglyMeasurable_id`：∀ {α : Type u_5} [inst : TopologicalSpace α] [T
opologicalSpace.PseudoMetrizableSpace α] {x : MeasurableSpace α}   [OpensMeasura
bleSpace α] […
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `ProbabilityTheory.gaussianReal_map_linearMap`：gaussianReal_map_linearMap
 (L : Real ->ₗ[Real] Real) : (gaussianReal μ v).map L = gaussianReal (L μ) ((L 1
 ^ 2).toNNReal * v)
· 使用引理 `ProbabilityTheory.integral_id_gaussianReal`：integral_id_gaussianReal : ∫
 x, x ∂gaussianReal μ v = μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma integral_linearMap_gaussianReal (L : ℝ →ₗ[ℝ] ℝ) :
    ∫ x, L x ∂(gaussianReal μ v) = L μ := by
  have : ∫ x, L x ∂(gaussianReal μ v) = ∫ x, x ∂((gaussianReal μ v).map L) := by
    rw [integral_map (φ := L) (by fun_prop) (by fun_prop)]
  simp [this, gaussianReal_map_linearMap]

@[simp]
/-
**ProbabilityTheory.integral_continuousLinearMap_gaussianReal** 是 Mathlib 中的一个引理
，位于命名空间 `ProbabilityTheory`。
形式化陈述：integral_continuousLinearMap_gaussianReal (L : Real ->L[Real] Real) : ∫ x,
 L x ∂(gaussianReal μ v) = L μ
参数：L : Real ->L[Real] Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.integral_linearMap_gaussianReal`：integral_linearMap_ga
ussianReal (L : Real ->ₗ[Real] Real) : ∫ x, L x ∂(gaussianReal μ v) = L μ
-/
lemma integral_continuousLinearMap_gaussianReal (L : ℝ →L[ℝ] ℝ) :
    ∫ x, L x ∂(gaussianReal μ v) = L μ := integral_linearMap_gaussianReal L

@[simp]
/-
**ProbabilityTheory.variance_linearMap_gaussianReal** 是 Mathlib 中的一个引理，位于命名空间 `P
robabilityTheory`。
形式化陈述：variance_linearMap_gaussianReal (L : Real ->ₗ[Real] Real) : Var[L; gaussia
nReal μ v] = (L 1 ^ 2).toNNReal * v
参数：L : Real ->ₗ[Real] Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.variance_id_map`：variance_id_map (hX : AEMeasurable X 
μ) : Var[id; μ.map X] = Var[X; μ]
· 使用定理 `Continuous.aemeasurable`：Continuous.aemeasurable {f : α -> γ} (h : Conti
nuous f) {μ : Measure α} : AEMeasurable f μ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `IsModuleTopology.continuous_of_linearMap`：continuous_of_linearMap (φ : A
 ->ₗ[R] B) : Continuous φ
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用引理 `ProbabilityTheory.gaussianReal_map_linearMap`：gaussianReal_map_linearMap
 (L : Real ->ₗ[Real] Real) : (gaussianReal μ v).map L = gaussianReal (L μ) ((L 1
 ^ 2).toNNReal * v)
· 使用引理 `ProbabilityTheory.variance_id_gaussianReal`：variance_id_gaussianReal : V
ar[id; gaussianReal μ v] = v
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma variance_linearMap_gaussianReal (L : ℝ →ₗ[ℝ] ℝ) :
    Var[L; gaussianReal μ v] = (L 1 ^ 2).toNNReal * v := by
  rw [← variance_id_map, gaussianReal_map_linearMap, variance_id_gaussianReal]
  · simp only [NNReal.coe_mul, Real.coe_toNNReal']
  · fun_prop

@[simp]
/-
**ProbabilityTheory.variance_continuousLinearMap_gaussianReal** 是 Mathlib 中的一个引理
，位于命名空间 `ProbabilityTheory`。
形式化陈述：variance_continuousLinearMap_gaussianReal (L : Real ->L[Real] Real) : Var[
L; gaussianReal μ v] = (L 1 ^ 2).toNNReal * v
参数：L : Real ->L[Real] Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.variance_linearMap_gaussianReal`：variance_linearMap_ga
ussianReal (L : Real ->ₗ[Real] Real) : Var[L; gaussianReal μ v] = (L 1 ^ 2).toNN
Real * v
-/
lemma variance_continuousLinearMap_gaussianReal (L : ℝ →L[ℝ] ℝ) :
    Var[L; gaussianReal μ v] = (L 1 ^ 2).toNNReal * v :=
  variance_linearMap_gaussianReal L

end LinearMap

/-- The convolution of two real Gaussian distributions with means `m₁, m₂` and variances `v₁, v₂`
is a real Gaussian distribution with mean `m₁ + m₂` and variance `v₁ + v₂`. -/
/-
**ProbabilityTheory.gaussianReal_conv_gaussianReal** 是 Mathlib 中的一个引理，位于命名空间 `Pr
obabilityTheory`。
形式化陈述：gaussianReal_conv_gaussianReal {m₁ m₂ : Real} {v₁ v₂ : Real>=0} : (gaussia
nReal m₁ v₁) ∗ (gaussianReal m₂ v₂) = gaussianReal (m₁ + m₂) (v₁ + v₂)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext_of_charFun`：∀ {E : Type u_3} [inst : Measurabl
eSpace E] {μ ν : MeasureTheory.Measure E} [inst_1 : NormedAddCommGroup E]   [ins
t_2 : InnerProductSpace ℝ …
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `MeasureTheory.Measure.finite_of_finite_conv`：∀ {M : Type u_1} [inst : Ad
dMonoid M] [inst_1 : MeasurableSpace M] (μ ν : MeasureTheory.Measure M)   [Measu
reTheory.IsFiniteMeasure μ] [Meas…
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.charFun_conv`：charFun_conv [IsFiniteMeasure μ] [IsFiniteMe
asure ν] (t : E) : charFun (μ ∗ ν) t = charFun μ t * charFun ν t
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ProbabilityTheory.charFun_gaussianReal`：charFun_gaussianReal (t : Real) 
: charFun (gaussianReal μ v) t = cexp (t * μ * I - v * t ^ 2 / 2)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.exp_add`：exp_add : exp (x + y) = exp x * exp y
· 使用定理 `Complex.ofReal_add`：ofReal_add (r s : Real) : ((r + s : Real) : Complex)
 = r + s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
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
（共 69 条，此处仅展示前 30 条）

--- 原说明 ---
The convolution of two real Gaussian distributions with means `m₁, m₂` and varia
nces `v₁, v₂`
is a real Gaussian distribution with mean `m₁ + m₂` and variance `v₁ + v₂`.
-/
lemma gaussianReal_conv_gaussianReal {m₁ m₂ : ℝ} {v₁ v₂ : ℝ≥0} :
    (gaussianReal m₁ v₁) ∗ (gaussianReal m₂ v₂) = gaussianReal (m₁ + m₂) (v₁ + v₂) := by
  refine Measure.ext_of_charFun ?_
  ext t
  simp_rw [charFun_conv, charFun_gaussianReal]
  rw [← Complex.exp_add]
  simp only [Complex.ofReal_add, NNReal.coe_add]
  ring_nf

/- The sum of two real Gaussian variables with means `m₁, m₂` and variances `v₁, v₂` is a real
Gaussian distribution with mean `m₁ + m₂` and variance `v_1 + v_2`. -/
/-
**ProbabilityTheory.gaussianReal_add_gaussianReal_of_indepFun** 是 Mathlib 中的一个引理
，位于命名空间 `ProbabilityTheory`。
形式化陈述：gaussianReal_add_gaussianReal_of_indepFun {Ω} {mΩ : MeasurableSpace Ω} {P 
: Measure Ω} {m₁ m₂ : Real} {v₁ v₂ : Real>=0} {X Y : Ω -> Real} (hXY : IndepFun 
X Y P) (hX : P.map X = gaussianReal m₁ v₁) (hY : P.map Y = gaussianReal m₂ v₂) :
 P.map (X + Y) = gaussianReal (m₁ + m₂) (v₁ + v₂)
参数：hXY : IndepFun X Y P；hX : P.map X = gaussianReal m₁ v₁；hY : P.map Y = gaussia
nReal m₂ v₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.IndepFun.map_add_eq_map_conv_map₀'`：∀ {Ω : Type u_7} {
mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {M : Type u_10} [inst : Ad
dMonoid M]   [inst_1 : MeasurableSpace M] …
· 使用定理 `ContinuousAdd.measurableMul₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Add γ] [Con…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
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
· 使用定理 `AEMeasurable.of_map_ne_zero`：∀ {α : Type u_1} {β : Type u_2} {mα : Measu
rableSpace α} {mβ : MeasurableSpace β} {f : α → β}   {μ : MeasureTheory.Measure 
α}, MeasureTheory…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.IsProbabilityMeasure.neZero`：∀ {α : Type u_1} {m0 : Measur
ableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ
], NeZero μ
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用引理 `ProbabilityTheory.gaussianReal_conv_gaussianReal`：gaussianReal_conv_gaus
sianReal {m₁ m₂ : Real} {v₁ v₂ : Real>=0} : (gaussianReal m₁ v₁) ∗ (gaussianReal
 m₂ v₂) = gaussianReal (m₁ + m₂) (v₁ +…

--- 原说明 ---
The sum of two real Gaussian variables with means `m₁, m₂` and variances `v₁, v₂
` is a real
Gaussian distribution with mean `m₁ + m₂` and variance `v_1 + v_2`.
-/
lemma gaussianReal_add_gaussianReal_of_indepFun {Ω} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {m₁ m₂ : ℝ} {v₁ v₂ : ℝ≥0} {X Y : Ω → ℝ} (hXY : IndepFun X Y P)
    (hX : P.map X = gaussianReal m₁ v₁) (hY : P.map Y = gaussianReal m₂ v₂) :
    P.map (X + Y) = gaussianReal (m₁ + m₂) (v₁ + v₂) := by
  rw [hXY.map_add_eq_map_conv_map₀', hX, hY, gaussianReal_conv_gaussianReal]
  · apply AEMeasurable.of_map_ne_zero; simp [NeZero.ne, hX]
  · apply AEMeasurable.of_map_ne_zero; simp [NeZero.ne, hY]
  · rw [hX]; apply IsFiniteMeasure.toSigmaFinite
  · rw [hY]; apply IsFiniteMeasure.toSigmaFinite

end GaussianReal

end ProbabilityTheory

