/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Disintegration.CondCDF
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Cumulative distribution function of a real probability measure

The cumulative distribution function (cdf) of a probability measure over `ℝ` is a monotone, right
continuous function with limit 0 at -∞ and 1 at +∞, such that `cdf μ x = μ (Iic x)` for all `x : ℝ`.
Two probability measures are equal if and only if they have the same cdf.

## Main definitions

* `ProbabilityTheory.cdf μ`: cumulative distribution function of `μ : Measure ℝ`, defined as the
  conditional cdf (`ProbabilityTheory.condCDF`) of the product measure
  `(Measure.dirac Unit.unit).prod μ` evaluated at `Unit.unit`.

The definition could be replaced by the more elementary `cdf μ x = μ.real (Iic x)`, but using
`condCDF` gives us access to its API, from which most properties of the cdf follow directly.

## Main statements

* `ProbabilityTheory.ofReal_cdf`: for a probability measure `μ` and `x : ℝ`,
  `ENNReal.ofReal (cdf μ x) = μ (Iic x)`.
* `MeasureTheory.Measure.ext_of_cdf`: two probability measures are equal if and only if they have
  the same cdf.

## TODO

The definition could be extended to a finite measure by rescaling `condCDF`, but it would be nice
to have more structure on Stieltjes functions first. Right now, if `f` is a Stieltjes function,
`2 • f` makes no sense. We could define Stieltjes functions as a submodule.

The definition could be extended to `ℝⁿ`, either by extending the definition of `condCDF`, or by
using another construction here.
-/

@[expose] public section

open MeasureTheory Measure Set Filter

open scoped Topology

namespace ProbabilityTheory

/-- Cumulative distribution function of a real measure. The definition currently makes sense only
for probability measures. In that case, it satisfies `cdf μ x = μ.real (Iic x)` (see
`ProbabilityTheory.cdf_eq_real`). -/
@[wikidata Q386228]
noncomputable
/-
**ProbabilityTheory.cdf** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory`。
形式化陈述：cdf (μ : Measure Real) : StieltjesFunction Real
参数：μ : Measure Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def cdf (μ : Measure ℝ) : StieltjesFunction ℝ :=
  condCDF ((dirac Unit.unit).prod μ) Unit.unit

section ExplicitMeasureArg
variable (μ : Measure ℝ)

/-- The cdf is non-negative. -/
/-
**ProbabilityTheory.cdf_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：cdf_nonneg (x : Real) : 0 <= cdf μ x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.condCDF_nonneg`：condCDF_nonneg (ρ : Measure (α × Real)
) (a : α) (r : Real) : 0 <= condCDF ρ a r

--- 原说明 ---
The cdf is non-negative.
-/
lemma cdf_nonneg (x : ℝ) : 0 ≤ cdf μ x := condCDF_nonneg _ _ _

/-- The cdf is lower or equal to 1. -/
/-
**ProbabilityTheory.cdf_le_one** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：cdf_le_one (x : Real) : cdf μ x <= 1
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.condCDF_le_one`：condCDF_le_one (ρ : Measure (α × Real)
) (a : α) (x : Real) : condCDF ρ a x <= 1

--- 原说明 ---
The cdf is lower or equal to 1.
-/
lemma cdf_le_one (x : ℝ) : cdf μ x ≤ 1 := condCDF_le_one _ _ _

/-- The cdf is monotone. -/
/-
**ProbabilityTheory.monotone_cdf** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：monotone_cdf : Monotone (cdf μ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StieltjesFunction.mono`：mono : Monotone f

--- 原说明 ---
The cdf is monotone.
-/
lemma monotone_cdf : Monotone (cdf μ) := (condCDF _ _).mono

/-- The cdf tends to 0 at -∞. -/
/-
**ProbabilityTheory.tendsto_cdf_atBot** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheo
ry`。
形式化陈述：tendsto_cdf_atBot : Tendsto (cdf μ) atBot (𝓝 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.tendsto_condCDF_atBot`：tendsto_condCDF_atBot (ρ : Meas
ure (α × Real)) (a : α) : Tendsto (condCDF ρ a) atBot (𝓝 0)

--- 原说明 ---
The cdf tends to 0 at -∞.
-/
lemma tendsto_cdf_atBot : Tendsto (cdf μ) atBot (𝓝 0) := tendsto_condCDF_atBot _ _

/-- The cdf tends to 1 at +∞. -/
/-
**ProbabilityTheory.tendsto_cdf_atTop** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheo
ry`。
形式化陈述：tendsto_cdf_atTop : Tendsto (cdf μ) atTop (𝓝 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.tendsto_condCDF_atTop`：tendsto_condCDF_atTop (ρ : Meas
ure (α × Real)) (a : α) : Tendsto (condCDF ρ a) atTop (𝓝 1)

--- 原说明 ---
The cdf tends to 1 at +∞.
-/
lemma tendsto_cdf_atTop : Tendsto (cdf μ) atTop (𝓝 1) := tendsto_condCDF_atTop _ _
/-
**ProbabilityTheory.ofReal_cdf** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：ofReal_cdf [IsProbabilityMeasure μ] (x : Real) : ENNReal.ofReal (cdf μ x) 
= μ (Iic x)
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.lintegral_condCDF`：lintegral_condCDF (ρ : Measure (α ×
 Real)) [IsFiniteMeasure ρ] (x : Real) : ∫⁻ a, ENNReal.ofReal (condCDF ρ a x) ∂ρ
.fst = ρ (univ ×ˢ Iic x)
· 使用定理 `MeasureTheory.Measure.prod.instIsFiniteMeasure`：∀ {α : Type u_4} {β : Ty
pe u_5} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (μ : MeasureTheory.Mea
sure α)   (ν : MeasureTheory.Measure…
· 使用定理 `MeasureTheory.Measure.dirac.instIsFiniteMeasure`：∀ {α : Type u_1} [inst 
: MeasurableSpace α] {a : α}, MeasureTheory.IsFiniteMeasure (MeasureTheory.Measu
re.dirac a)
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MeasureTheory.Measure.fst_prod`：fst_prod [IsProbabilityMeasure ν] : (μ.p
rod ν).fst = μ
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.sigmaFinite_of_locallyFinite`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace α]   [Secon
dCountableTopology α] [MeasureTh…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toIsLocallyFiniteMeasure`：∀ {α : Type u_1}
 {m0 : MeasurableSpace α} [inst : TopologicalSpace α] (μ : MeasureTheory.Measure
 α)   [MeasureTheory.IsFiniteMeasure μ], Mea…
· 使用定理 `MeasureTheory.lintegral_dirac`：lintegral_dirac [MeasurableSingletonClass
 α] (a : α) (f : α -> Real>=0∞) : ∫⁻ a, f a ∂dirac a = f a
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorelSpace_of_discreteMeasurableSpace`：∀ {α : Type u_1} [inst : 
MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α], StandardBorelSpace
 α
· 使用定理 `instDiscreteMeasurableSpace`：∀ {α : Type u_1}, DiscreteMeasurableSpace α
· 使用定理 `instCountablePUnit`：Countable PUnit.{u}
· 使用定理 `MeasureTheory.Measure.prod_prod`：prod_prod (s : Set α) (t : Set β) : μ.p
rod ν (s ×ˢ t) = μ s * ν t
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `MeasureTheory.Measure.dirac.isProbabilityMeasure`：∀ {α : Type u_1} [inst
 : MeasurableSpace α] {x : α}, MeasureTheory.IsProbabilityMeasure (MeasureTheory
.Measure.dirac x)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
lemma ofReal_cdf [IsProbabilityMeasure μ] (x : ℝ) : ENNReal.ofReal (cdf μ x) = μ (Iic x) := by
  have h := lintegral_condCDF ((dirac Unit.unit).prod μ) x
  simpa only [fst_prod, prod_prod, measure_univ, one_mul, lintegral_dirac] using! h
/-
**ProbabilityTheory.cdf_eq_real** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：cdf_eq_real [IsProbabilityMeasure μ] (x : Real) : cdf μ x = μ.real (Iic x)
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measureReal_def`：measureReal_def {α : Type*} {m : Measurab
leSpace α} (μ : Measure α) (s : Set α) : μ.real s = (μ s).toReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.ofReal_cdf`：ofReal_cdf [IsProbabilityMeasure μ] (x : R
eal) : ENNReal.ofReal (cdf μ x) = μ (Iic x)
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用引理 `ProbabilityTheory.cdf_nonneg`：cdf_nonneg (x : Real) : 0 <= cdf μ x
-/
lemma cdf_eq_real [IsProbabilityMeasure μ] (x : ℝ) : cdf μ x = μ.real (Iic x) := by
  rw [measureReal_def, ← ofReal_cdf μ x, ENNReal.toReal_ofReal (cdf_nonneg μ x)]
/-
**ProbabilityTheory.instIsProbabilityMeasurecdf** 是 Mathlib 中的一个实例，位于命名空间 `Proba
bilityTheory`。
形式化陈述：instIsProbabilityMeasurecdf : IsProbabilityMeasure (cdf μ).measure
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
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
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StieltjesFunction.measure_univ`：measure_univ [Nonempty R] {l u : Real} (
hfl : Tendsto f atBot (𝓝 l)) (hfu : Tendsto f atTop (𝓝 u)) : f.measure univ = of
Real (u - l)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `ProbabilityTheory.tendsto_cdf_atBot`：tendsto_cdf_atBot : Tendsto (cdf μ)
 atBot (𝓝 0)
· 使用引理 `ProbabilityTheory.tendsto_cdf_atTop`：tendsto_cdf_atTop : Tendsto (cdf μ)
 atTop (𝓝 1)
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `ENNReal.ofReal_one`：ENNReal.ofReal 1 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance instIsProbabilityMeasurecdf : IsProbabilityMeasure (cdf μ).measure := by
  constructor
  simp only [StieltjesFunction.measure_univ _ (tendsto_cdf_atBot μ) (tendsto_cdf_atTop μ), sub_zero,
    ENNReal.ofReal_one]

/-- The measure associated to the cdf of a probability measure is the same probability measure. -/
/-
**ProbabilityTheory.measure_cdf** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：measure_cdf [IsProbabilityMeasure μ] : (cdf μ).measure = μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext_of_Iic`：ext_of_Iic {α : Type*} [TopologicalSpa
ce α] {m : MeasurableSpace α} [SecondCountableTopology α] [LinearOrder α] [Order
Topology α] [BorelSpac…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
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
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StieltjesFunction.measure_Iic`：measure_Iic {l : Real} (hf : Tendsto f at
Bot (𝓝 l)) (x : R) : f.measure (Iic x) = ofReal (f x - l)
· 使用引理 `ProbabilityTheory.tendsto_cdf_atBot`：tendsto_cdf_atBot : Tendsto (cdf μ)
 atBot (𝓝 0)
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用引理 `ProbabilityTheory.ofReal_cdf`：ofReal_cdf [IsProbabilityMeasure μ] (x : R
eal) : ENNReal.ofReal (cdf μ x) = μ (Iic x)

--- 原说明 ---
The measure associated to the cdf of a probability measure is the same probabili
ty measure.
-/
lemma measure_cdf [IsProbabilityMeasure μ] : (cdf μ).measure = μ := by
  refine ext_of_Iic (cdf μ).measure μ (fun a ↦ ?_)
  rw [StieltjesFunction.measure_Iic _ (tendsto_cdf_atBot μ), sub_zero, ofReal_cdf]

end ExplicitMeasureArg

/-
**ProbabilityTheory.cdf_measure_stieltjesFunction** 是 Mathlib 中的一个引理，位于命名空间 `Pro
babilityTheory`。
形式化陈述：cdf_measure_stieltjesFunction (f : StieltjesFunction Real) (hf0 : Tendsto 
f atBot (𝓝 0)) (hf1 : Tendsto f atTop (𝓝 1)) : cdf f.measure = f
参数：f : StieltjesFunction Real；hf0 : Tendsto f atBot (𝓝 0)；hf1 : Tendsto f atTop 
(𝓝 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StieltjesFunction.eq_of_measure_of_tendsto_atBot`：eq_of_measure_of_tends
to_atBot (g : StieltjesFunction R) {l : Real} (hfg : f.measure = g.measure) (hfl
 : Tendsto f atBot (𝓝 l)) (hgl : Tends…
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
· 使用定理 `StieltjesFunction.measure_univ`：measure_univ [Nonempty R] {l u : Real} (
hfl : Tendsto f atBot (𝓝 l)) (hfu : Tendsto f atTop (𝓝 u)) : f.measure univ = of
Real (u - l)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `ENNReal.ofReal_one`：ENNReal.ofReal 1 = 1
· 使用引理 `ProbabilityTheory.measure_cdf`：measure_cdf [IsProbabilityMeasure μ] : (c
df μ).measure = μ
· 使用引理 `ProbabilityTheory.tendsto_cdf_atBot`：tendsto_cdf_atBot : Tendsto (cdf μ)
 atBot (𝓝 0)
-/
lemma cdf_measure_stieltjesFunction (f : StieltjesFunction ℝ) (hf0 : Tendsto f atBot (𝓝 0))
    (hf1 : Tendsto f atTop (𝓝 1)) :
    cdf f.measure = f := by
  refine (cdf f.measure).eq_of_measure_of_tendsto_atBot f ?_ (tendsto_cdf_atBot _) hf0
  have h_prob : IsProbabilityMeasure f.measure :=
    ⟨by rw [f.measure_univ hf0 hf1, sub_zero, ENNReal.ofReal_one]⟩
  exact measure_cdf f.measure

open unitInterval in
/-
**ProbabilityTheory.unitInterval.cdf_eq_real** 是 Mathlib 中的一个定理，位于命名空间 `Probabil
ityTheory.unitInterval`。
形式化陈述：∀ (μ : MeasureTheory.Measure ↑unitInterval) [MeasureTheory.IsProbabilityMe
asure μ] (x : ↑unitInterval),   ↑(ProbabilityTheory.cdf (MeasureTheory.Measure.m
ap Subtype.val μ)) ↑x = μ.real (Set.Icc 0 x)
参数：μ : MeasureTheory.Measure ↑unitInterval；x : ↑unitInterval；ProbabilityTheory.c
df (MeasureTheory.Measure.map Subtype.val μ)；Set.Icc 0 x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.isProbabilityMeasure_map`：∀ {α : Type u_1} {β : Ty
pe u_2} {m0 : MeasurableSpace α} [inst : MeasurableSpace β] {μ : MeasureTheory.M
easure α}   [MeasureTheory.IsProbabi…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Measurable.subtype_coe`：Measurable.subtype_coe {p : β -> Prop} {f : α ->
 Subtype p} (hf : Measurable f) : Measurable fun a : α => (f a : β)
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.cdf_eq_real`：cdf_eq_real [IsProbabilityMeasure μ] (x :
 Real) : cdf μ x = μ.real (Iic x)
· 使用定理 `MeasureTheory.map_measureReal_apply`：map_measureReal_apply [MeasurableSp
ace β] {f : α -> β} (hf : Measurable f) {s : Set β} (hs : MeasurableSet s) : (μ.
map f).real s = μ.real (f…
· 使用定理 `measurable_subtype_coe`：measurable_subtype_coe {p : α -> Prop} : Measura
ble ((↑) : Subtype p -> α)
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
· 使用引理 `unitInterval.subtype_Iic_eq_Icc`：subtype_Iic_eq_Icc (x : I) : Subtype.va
l ⁻¹' (Iic ↑x) = Icc 0 x
-/
lemma unitInterval.cdf_eq_real (μ : Measure I) [IsProbabilityMeasure μ] (x : I) :
    cdf (μ.map Subtype.val) x.1 = μ.real (Icc 0 x) := by
  have : IsProbabilityMeasure (μ.map Subtype.val) := isProbabilityMeasure_map (by fun_prop)
  rw [ProbabilityTheory.cdf_eq_real,
    map_measureReal_apply measurable_subtype_coe measurableSet_Iic, subtype_Iic_eq_Icc]

end ProbabilityTheory

open ProbabilityTheory

/-- If two real probability distributions have the same cdf, they are equal. -/
/-
**MeasureTheory.Measure.eq_of_cdf** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MeasureTheory.Measure.eq_of_cdf (μ ν : Measure Real) [IsProbabilityMeasure
 μ] [IsProbabilityMeasure ν] (h : cdf μ = cdf ν) : μ = ν
参数：μ ν : Measure Real；h : cdf μ = cdf ν。
该定理/引理给出了一组等式。
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.measure_cdf`：measure_cdf [IsProbabilityMeasure μ] : (c
df μ).measure = μ

--- 原说明 ---
If two real probability distributions have the same cdf, they are equal.
-/
lemma MeasureTheory.Measure.eq_of_cdf (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (h : cdf μ = cdf ν) : μ = ν := by
  rw [← measure_cdf μ, ← measure_cdf ν, h]
/-
**MeasureTheory.Measure.cdf_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Meas
ure`。
形式化陈述：∀ (μ ν : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure μ] [
MeasureTheory.IsProbabilityMeasure ν],   ProbabilityTheory.cdf μ = ProbabilityTh
eory.cdf ν ↔ μ = ν
参数：μ ν : MeasureTheory.Measure ℝ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.Measure.eq_of_cdf`：MeasureTheory.Measure.eq_of_cdf (μ ν : 
Measure Real) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (h : cdf μ = cdf
 ν) : μ = ν
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
@[simp] lemma MeasureTheory.Measure.cdf_eq_iff (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    cdf μ = cdf ν ↔ μ = ν :=
⟨eq_of_cdf μ ν, fun h ↦ by rw [h]⟩
