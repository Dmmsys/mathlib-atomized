/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Gaussian distributions in Banach spaces

We introduce a predicate `IsGaussian` for measures on a Banach space `E` such that the map by
any continuous linear form is a Gaussian measure on `ℝ`.

For Gaussian distributions in `ℝ`, see the file
`Mathlib/Probability/Distributions/Gaussian/Real.lean`.

## Main definitions

* `IsGaussian`: a measure `μ` is Gaussian if its map by every continuous linear form
  `L : Dual ℝ E` is a real Gaussian measure.
  That is, `μ.map L = gaussianReal (μ[L]) (Var[L; μ]).toNNReal`.

## Main statements

* `isGaussian_iff_charFunDual_eq`: a finite measure `μ` is Gaussian if and only if
  its characteristic function has value `exp (μ[L] * I - Var[L; μ] / 2)` for every
  continuous linear form `L : Dual ℝ E`.

## References

* [Martin Hairer, *An introduction to stochastic PDEs*][hairer2009introduction]

-/

public section

open MeasureTheory Complex
open scoped ENNReal NNReal

namespace ProbabilityTheory

/-- A measure is Gaussian if its map by every continuous linear form is a real Gaussian measure. -/
/-
**ProbabilityTheory.IsGaussian** 是 Mathlib 中的一个归纳类型，位于命名空间 `ProbabilityTheory`。
形式化陈述：{E : Type u_1} →   [TopologicalSpace E] →     [inst : AddCommMonoid E] → [
_root_.Module ℝ E] → {mE : MeasurableSpace E} → MeasureTheory.Measure E → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A measure is Gaussian if its map by every continuous linear form is a real Gauss
ian measure.
-/
class IsGaussian {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
    {mE : MeasurableSpace E} (μ : Measure E) : Prop where
  map_eq_gaussianReal (L : StrongDual ℝ E) : μ.map L = gaussianReal (μ[L]) (Var[L; μ]).toNNReal

/-- A Gaussian measure is a probability measure. -/
/-
**ProbabilityTheory.IsGaussian.toIsProbabilityMeasure** 是 Mathlib 中的一个定理，位于命名空间 
`ProbabilityTheory.IsGaussian`。
形式化陈述：∀ {E : Type u_1} [inst : TopologicalSpace E] [inst_1 : AddCommMonoid E] [i
nst_2 : _root_.Module ℝ E]   {mE : MeasurableSpace E} (μ : MeasureTheory.Measure
 E) [ProbabilityTheory.IsGaussian μ],   MeasureTheory.IsProbabilityMeasure μ
参数：μ : MeasureTheory.Measure E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.IsGaussian.map_eq_gaussianReal`：∀ {E : Type u_1} {inst
 : TopologicalSpace E} {inst_1 : AddCommMonoid E} {inst_2 : _root_.Module ℝ E}  
 {mE : MeasurableSpace E} {μ : Measure…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `MeasureTheory.integral_zero`：integral_zero : ∫ _ : α, (0 : G) ∂μ = 0
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `measurable_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace
 α] [inst_1 : MeasurableSpace β] [inst_2 : Zero α], Measurable 0
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ

--- 原说明 ---
A Gaussian measure is a probability measure.
-/
instance IsGaussian.toIsProbabilityMeasure {E : Type*} [TopologicalSpace E] [AddCommMonoid E]
    [Module ℝ E] {mE : MeasurableSpace E} (μ : Measure E) [IsGaussian μ] :
    IsProbabilityMeasure μ where
  measure_univ := by
    have : μ.map (0 : StrongDual ℝ E) Set.univ = 1 := by
      simp [-FunLike.coe_zero, IsGaussian.map_eq_gaussianReal]
    simpa [-FunLike.coe_zero,
      Measure.map_apply (by fun_prop : Measurable (0 : StrongDual ℝ E)) .univ] using this

/-- A real Gaussian measure is Gaussian. -/
/-
**ProbabilityTheory.isGaussian_gaussianReal** 是 Mathlib 中的一个实例，位于命名空间 `Probabili
tyTheory`。
形式化陈述：isGaussian_gaussianReal (m : Real) (v : Real>=0) : IsGaussian (gaussianRea
l m v) where map_eq_gaussianReal L
参数：m : Real；v : Real>=0。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.gaussianReal_map_continuousLinearMap`：gaussianReal_map
_continuousLinearMap (L : Real ->L[Real] Real) : (gaussianReal μ v).map L = gaus
sianReal (L μ) ((L 1 ^ 2).toNNReal * v)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `ProbabilityTheory.integral_continuousLinearMap_gaussianReal`：integral_co
ntinuousLinearMap_gaussianReal (L : Real ->L[Real] Real) : ∫ x, L x ∂(gaussianRe
al μ v) = L μ
· 使用引理 `ProbabilityTheory.variance_continuousLinearMap_gaussianReal`：variance_co
ntinuousLinearMap_gaussianReal (L : Real ->L[Real] Real) : Var[L; gaussianReal μ
 v] = (L 1 ^ 2).toNNReal * v
· 使用定理 `Real.toNNReal_mul`：toNNReal_mul {p q : Real} (hp : 0 <= p) : Real.toNNRe
al (p * q) = Real.toNNReal p * Real.toNNReal q
· 使用定理 `le_max_of_le_left`：le_max_of_le_left : a <= b -> a <= max b c
· 使用定理 `Even.pow_nonneg`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : LinearOr
der R] [IsOrderedRing R] [ExistsAddOfLE R] {n : ℕ},   Even n → ∀ (a : R), 0 ≤ a 
^ n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `even_two_mul`：even_two_mul (a : α) : Even (2 * a)
· 使用定理 `Real.toNNReal_coe`：∀ {r : NNReal}, (↑r).toNNReal = r

--- 原说明 ---
A real Gaussian measure is Gaussian.
-/
instance isGaussian_gaussianReal (m : ℝ) (v : ℝ≥0) : IsGaussian (gaussianReal m v) where
  map_eq_gaussianReal L := by
    rw [gaussianReal_map_continuousLinearMap]
    simp only [integral_continuousLinearMap_gaussianReal, variance_continuousLinearMap_gaussianReal,
      Real.coe_toNNReal']
    congr
    rw [Real.toNNReal_mul (by positivity), Real.toNNReal_coe]
    congr
    simp only [left_eq_sup]
    positivity

/-- A Gaussian measure over `ℝ` is some `gaussianReal`. -/
/-
**ProbabilityTheory.IsGaussian.eq_gaussianReal** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory.IsGaussian`。
形式化陈述：∀ (μ : MeasureTheory.Measure ℝ),   ProbabilityTheory.IsGaussian μ →     μ 
= ProbabilityTheory.gaussianReal (∫ (x : ℝ), id x ∂μ) (ProbabilityTheory.varianc
e id μ).toNNReal
参数：μ : MeasureTheory.Measure ℝ；∫ (x : ℝ), id x ∂μ；ProbabilityTheory.variance id 
μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_id`：map_id : map id μ = μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ProbabilityTheory.IsGaussian.map_eq_gaussianReal`：∀ {E : Type u_1} {inst
 : TopologicalSpace E} {inst_1 : AddCommMonoid E} {inst_2 : _root_.Module ℝ E}  
 {mE : MeasurableSpace E} {μ : Measure…

--- 原说明 ---
A Gaussian measure over `ℝ` is some `gaussianReal`.
-/
lemma IsGaussian.eq_gaussianReal (μ : Measure ℝ) (h : IsGaussian μ) :
    μ = gaussianReal μ[id] Var[id; μ].toNNReal := calc
  μ = μ.map (ContinuousLinearMap.id ℝ ℝ) := by simp
  _ = gaussianReal μ[id] Var[id; μ].toNNReal := by rw [h.map_eq_gaussianReal]; simp
/-
**ProbabilityTheory.isGaussian_of_isGaussian_map** 是 Mathlib 中的一个引理，位于命名空间 `Prob
abilityTheory`。
形式化陈述：isGaussian_of_isGaussian_map {E : Type*} [TopologicalSpace E] [AddCommMono
id E] [Module Real E] {mE : MeasurableSpace E} [OpensMeasurableSpace E] {μ : Mea
sure E} (h : forall L : E ->L[Real] Real, IsGaussian (μ.map L)) : IsGaussian μ
参数：h : forall L : E ->L[Real] Real, IsGaussian (μ.map L)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.IsGaussian.eq_gaussianReal`：∀ (μ : MeasureTheory.Measu
re ℝ),   ProbabilityTheory.IsGaussian μ →     μ = ProbabilityTheory.gaussianReal
 (∫ (x : ℝ), id x ∂μ) (Probability…
· 使用定理 `MeasureTheory.integral_map`：integral_map {β} [MeasurableSpace β] {φ : α 
-> β} (hφ : AEMeasurable φ μ) {f : β -> G} (hfm : AEStronglyMeasurable f (Measur
e.map φ μ)) : ∫ …
· 使用定理 `Continuous.aemeasurable`：Continuous.aemeasurable {f : α -> γ} (h : Conti
nuous f) {μ : Measure α} : AEMeasurable f μ
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `aestronglyMeasurable_id`：∀ {α : Type u_5} [inst : TopologicalSpace α] [T
opologicalSpace.PseudoMetrizableSpace α] {x : MeasurableSpace α}   [OpensMeasura
bleSpace α] […
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用引理 `ProbabilityTheory.variance_map`：variance_map {Ω' : Type*} {mΩ' : Measura
bleSpace Ω'} {μ : Measure Ω'} {Y : Ω' -> Ω} (hX : AEMeasurable X (μ.map Y)) (hY 
: AEMeasurable Y μ) …
· 使用定理 `aemeasurable_id`：aemeasurable_id : AEMeasurable id μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CompTriple.comp_eq`：∀ {M : Type u_1} {N : Type u_2} {P : Type u_3} {φ : 
M → N} {ψ : N → P} {χ : outParam (M → P)} [self : CompTriple φ ψ χ],   ψ ∘ φ = χ
· 使用定理 `CompTriple.instIsIdId`：∀ {M : Type u_1}, CompTriple.IsId id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isGaussian_of_isGaussian_map {E : Type*} [TopologicalSpace E] [AddCommMonoid E]
    [Module ℝ E] {mE : MeasurableSpace E} [OpensMeasurableSpace E] {μ : Measure E}
    (h : ∀ L : E →L[ℝ] ℝ, IsGaussian (μ.map L)) : IsGaussian μ := by
  refine ⟨fun L ↦ ?_⟩
  rw [(h L).eq_gaussianReal, integral_map, variance_map]
  · simp
  all_goals fun_prop
/-
**ProbabilityTheory.isGaussian_of_map_eq_gaussianReal** 是 Mathlib 中的一个引理，位于命名空间 
`ProbabilityTheory`。
形式化陈述：isGaussian_of_map_eq_gaussianReal {E : Type*} [TopologicalSpace E] [AddCom
mMonoid E] [Module Real E] {mE : MeasurableSpace E} [OpensMeasurableSpace E] {μ 
: Measure E} (h : forall L : E ->L[Real] Real, exists (m : Real) (v : Real>=0), 
μ.map L = gaussianReal m v) : IsGaussian μ
参数：h : forall L : E ->L[Real] Real, exists (m : Real) (v : Real>=0), μ.map L = g
aussianReal m v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.isGaussian_of_isGaussian_map`：isGaussian_of_isGaussian
_map {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module Real E] {mE : Me
asurableSpace E} [OpensMeasurableSpa…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma isGaussian_of_map_eq_gaussianReal {E : Type*} [TopologicalSpace E] [AddCommMonoid E]
    [Module ℝ E] {mE : MeasurableSpace E} [OpensMeasurableSpace E] {μ : Measure E}
    (h : ∀ L : E →L[ℝ] ℝ, ∃ (m : ℝ) (v : ℝ≥0), μ.map L = gaussianReal m v) :
    IsGaussian μ := by
  refine isGaussian_of_isGaussian_map fun L ↦ ?_
  obtain ⟨m, v, h⟩ := h L
  rw [h]
  infer_instance

/-- Mapping a Gaussian measure by a measurable and continuous linear map yields a Gaussian
measure. See also `isGaussian_map`, which does not assume measurability but has stronger hypotheses
on `E`. In particular, it requires `E` to be a Borel space, which requires some second countability
hypotheses if `E` is a product space. This version does not, which can be useful for instance
if `L := Prod.fst`, which is always measurable. -/
/-
**ProbabilityTheory.isGaussian_map_of_measurable** 是 Mathlib 中的一个引理，位于命名空间 `Prob
abilityTheory`。
形式化陈述：isGaussian_map_of_measurable {E F : Type*} [TopologicalSpace E] [AddCommMo
noid E] [Module Real E] {mE : MeasurableSpace E} [TopologicalSpace F] [AddCommMo
noid F] [Module Real F] {mF : MeasurableSpace F} [OpensMeasurableSpace F] {μ : M
easure E} {L : E ->L[Real] F} [IsGaussian μ] (hL : Measurable L) : IsGaussian (μ
.map L)
参数：hL : Measurable L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.isGaussian_of_map_eq_gaussianReal`：isGaussian_of_map_e
q_gaussianReal {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module Real E
] {mE : MeasurableSpace E} [OpensMeasurab…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_map`：map_map {g : β -> γ} {f : α -> β} (hg : M
easurable g) (hf : Measurable f) : (μ.map f).map g = μ.map (g ∘ f)
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.coe_comp`：coe_comp (h : M₂ ->SL[σ₂₃] M₃) (f : M₁ ->S
L[σ₁₂] M₂) : ⇑(h ∘SL f) = h ∘ f
· 使用定理 `ProbabilityTheory.IsGaussian.map_eq_gaussianReal`：∀ {E : Type u_1} {inst
 : TopologicalSpace E} {inst_1 : AddCommMonoid E} {inst_2 : _root_.Module ℝ E}  
 {mE : MeasurableSpace E} {μ : Measure…

--- 原说明 ---
Mapping a Gaussian measure by a measurable and continuous linear map yields a Ga
ussian
measure. See also `isGaussian_map`, which does not assume measurability but has 
stronger hypotheses
on `E`. In particular, it requires `E` to be a Borel space, which requires some 
second countability
hypotheses if `E` is a product space. This version does not, which can be useful
 for instance
if `L := Prod.fst`, which is always measurable.
-/
lemma isGaussian_map_of_measurable {E F : Type*} [TopologicalSpace E] [AddCommMonoid E]
    [Module ℝ E] {mE : MeasurableSpace E} [TopologicalSpace F] [AddCommMonoid F]
    [Module ℝ F] {mF : MeasurableSpace F} [OpensMeasurableSpace F] {μ : Measure E}
    {L : E →L[ℝ] F} [IsGaussian μ] (hL : Measurable L) : IsGaussian (μ.map L) := by
  refine isGaussian_of_map_eq_gaussianReal fun L' ↦ ⟨μ[L' ∘L L], Var[L' ∘L L; μ].toNNReal, ?_⟩
  rw [Measure.map_map (by fun_prop) hL, ← ContinuousLinearMap.coe_comp,
    IsGaussian.map_eq_gaussianReal]

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
  {μ : Measure E} [IsGaussian μ]

/-- Dirac measures are Gaussian. -/
/-
**ProbabilityTheory.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Dirac measures are Gaussian.
-/
instance {x : E} : IsGaussian (Measure.dirac x) where
  map_eq_gaussianReal L := by simp

omit [IsGaussian μ] in
/-
**ProbabilityTheory.IsGaussian.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory.IsGaussian`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] 
[inst_2 : MeasurableSpace E] [BorelSpace E]   {μ : MeasureTheory.Measure E} [Sub
singleton E] [MeasureTheory.IsProbabilityMeasure μ], ProbabilityTheory.IsGaussia
n μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `Subsingleton.set_cases`：set_cases {p : Set α -> Prop} (h0 : p ∅) (h1 : p
 univ) (s) : p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `MeasureTheory.Measure.dirac.isProbabilityMeasure`：∀ {α : Type u_1} [inst
 : MeasurableSpace α] {x : α}, MeasureTheory.IsProbabilityMeasure (MeasureTheory
.Measure.dirac x)
· 使用定理 `ProbabilityTheory.instIsGaussianDirac`：∀ {E : Type u_1} [inst : NormedAd
dCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : MeasurableSpace E] [BorelSpac
e E]   {x : E}, Probability…
-/
lemma IsGaussian.of_subsingleton [Subsingleton E] [IsProbabilityMeasure μ] :
    IsGaussian μ := by
  convert! instIsGaussianDirac (x := (0 : E))
  ext s -
  apply Subsingleton.set_cases (p := fun s ↦ μ s = _)
  all_goals simp
/-
**ProbabilityTheory.IsGaussian.memLp_dual** 是 Mathlib 中的一个定理，位于命名空间 `Probability
Theory.IsGaussian`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] 
[inst_2 : MeasurableSpace E] [BorelSpace E]   (μ : MeasureTheory.Measure E) [Pro
babilityTheory.IsGaussian μ] (L : StrongDual ℝ E) (p : ENNReal),   p ≠ ⊤ → Measu
reTheory.MemLp (⇑L) p μ
参数：μ : MeasureTheory.Measure E；L : StrongDual ℝ E；p : ENNReal；⇑L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.memLp_map_measure_iff`：memLp_map_measure_iff (hg : AEStron
glyMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) : MemLp g p (Measure.
map f μ) ↔ MemLp (g ∘ f) …
· 使用定理 `aestronglyMeasurable_id`：∀ {α : Type u_5} [inst : TopologicalSpace α] [T
opologicalSpace.PseudoMetrizableSpace α] {x : MeasurableSpace α}   [OpensMeasura
bleSpace α] […
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `ContinuousLinearMap.measurable`：∀ {R : Type u_2} {E : Type u_3} {F : Typ
e u_4} [inst : Semiring R] [inst_1 : SeminormedAddCommGroup E]   [inst_2 : _root
_.Module R E] [inst_…
· 使用定理 `ProbabilityTheory.IsGaussian.map_eq_gaussianReal`：∀ {E : Type u_1} {inst
 : TopologicalSpace E} {inst_1 : AddCommMonoid E} {inst_2 : _root_.Module ℝ E}  
 {mE : MeasurableSpace E} {μ : Measure…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ENNReal.coe_toNNReal`：∀ {a : ENNReal}, a ≠ ⊤ → ↑a.toNNReal = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ProbabilityTheory.memLp_id_gaussianReal`：memLp_id_gaussianReal (p : Real
>=0) : MemLp id p (gaussianReal μ v)
-/
lemma IsGaussian.memLp_dual (μ : Measure E) [IsGaussian μ] (L : StrongDual ℝ E)
    (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp L p μ := by
  suffices MemLp (id ∘ L) p μ from this
  rw [← memLp_map_measure_iff (by fun_prop) (by fun_prop), IsGaussian.map_eq_gaussianReal L]
  convert! memLp_id_gaussianReal p.toNNReal
  simp [hp]

@[fun_prop]
/-
**ProbabilityTheory.IsGaussian.integrable_dual** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory.IsGaussian`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] 
[inst_2 : MeasurableSpace E] [BorelSpace E]   (μ : MeasureTheory.Measure E) [Pro
babilityTheory.IsGaussian μ] (L : StrongDual ℝ E), MeasureTheory.Integrable (⇑L)
 μ
参数：μ : MeasureTheory.Measure E；L : StrongDual ℝ E；⇑L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `ProbabilityTheory.IsGaussian.memLp_dual`：∀ {E : Type u_1} [inst : Normed
AddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : MeasurableSpace E] [BorelSp
ace E]   (μ : MeasureTheory.M…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma IsGaussian.integrable_dual (μ : Measure E) [IsGaussian μ] (L : StrongDual ℝ E) :
    Integrable L μ := by
  rw [← memLp_one_iff_integrable]
  exact IsGaussian.memLp_dual μ L 1 (by simp)

/-- The map of a Gaussian measure by a continuous linear map is Gaussian. -/
/-
**ProbabilityTheory.isGaussian_map** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory`
。
形式化陈述：isGaussian_map (L : E ->L[Real] F) : IsGaussian (μ.map L)
参数：L : E ->L[Real] F。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.isGaussian_map_of_measurable`：isGaussian_map_of_measur
able {E F : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module Real E] {mE : 
MeasurableSpace E} [TopologicalSpace…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `ContinuousLinearMap.measurable`：∀ {R : Type u_2} {E : Type u_3} {F : Typ
e u_4} [inst : Semiring R] [inst_1 : SeminormedAddCommGroup E]   [inst_2 : _root
_.Module R E] [inst_…

--- 原说明 ---
The map of a Gaussian measure by a continuous linear map is Gaussian.
-/
instance isGaussian_map (L : E →L[ℝ] F) : IsGaussian (μ.map L) :=
  isGaussian_map_of_measurable (by fun_prop)
/-
**ProbabilityTheory.isGaussian_map_equiv** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityT
heory`。
形式化陈述：isGaussian_map_equiv (L : E ≃L[Real] F) : IsGaussian (μ.map L)
参数：L : E ≃L[Real] F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isGaussian_map_equiv (L : E ≃L[ℝ] F) : IsGaussian (μ.map L) :=
  isGaussian_map (L : E →L[ℝ] F)
/-
**ProbabilityTheory.isGaussian_map_equiv_iff** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory`。
形式化陈述：isGaussian_map_equiv_iff {μ : Measure E} (L : E ≃L[Real] F) : IsGaussian (
μ.map L) ↔ IsGaussian μ
参数：L : E ≃L[Real] F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_map`：map_map {g : β -> γ} {f : α -> β} (hg : M
easurable g) (hf : Measurable f) : (μ.map f).map g = μ.map (g ∘ f)
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `ContinuousSemilinearMapClass.toContinuousMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `ContinuousSemilinearEquivClass.continuousSemilinearMapClass`：∀ (F : Type
 u_1) {R : Type u_2} {S : Type u_3} [inst : Semiring R] [inst_1 : Semiring S] (σ
 : R →+* S) {σ' : S →+* R}   [inst_2 : RingHomInv…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousLinearEquiv.symm_comp_self`：symm_comp_self (e : M₁ ≃SL[σ₁₂] M₂
) : (e.symm : M₂ -> M₁) ∘ (e : M₁ -> M₂) = id
· 使用定理 `MeasureTheory.Measure.map_id`：map_id : map id μ = μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isGaussian_map_equiv_iff {μ : Measure E} (L : E ≃L[ℝ] F) :
    IsGaussian (μ.map L) ↔ IsGaussian μ := by
  refine ⟨fun h ↦ ?_, fun _ ↦ inferInstance⟩
  suffices μ = (μ.map L).map L.symm by rw [this]; infer_instance
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  simp

section charFunDual

/-- The characteristic function of a Gaussian measure `μ` has value
`exp (μ[L] * I - Var[L; μ] / 2)` at `L : Dual ℝ E`. -/
/-
**ProbabilityTheory.IsGaussian.charFunDual_eq** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory.IsGaussian`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] 
[inst_2 : MeasurableSpace E] [BorelSpace E]   {μ : MeasureTheory.Measure E} [Pro
babilityTheory.IsGaussian μ] (L : StrongDual ℝ E),   MeasureTheory.charFunDual μ
 L =     Complex.exp ((∫ (x : E), ↑(L x) ∂μ) * Complex.I - ↑(ProbabilityTheory.v
ariance (⇑L) μ) / 2)
参数：L : StrongDual ℝ E；(∫ (x : E), ↑(L x) ∂μ) * Complex.I - ↑(ProbabilityTheory.v
ariance (⇑L) μ) / 2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.charFunDual_eq_charFun_map_one`：charFunDual_eq_charFun_map
_one [OpensMeasurableSpace E] (L : StrongDual Real E) : charFunDual μ L = charFu
n (μ.map L) 1
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `ProbabilityTheory.IsGaussian.map_eq_gaussianReal`：∀ {E : Type u_1} {inst
 : TopologicalSpace E} {inst_1 : AddCommMonoid E} {inst_2 : _root_.Module ℝ E}  
 {mE : MeasurableSpace E} {μ : Measure…
· 使用定理 `ProbabilityTheory.charFun_gaussianReal`：charFun_gaussianReal (t : Real) 
: charFun (gaussianReal μ v) t = cexp (t * μ * I - v * t ^ 2 / 2)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `integral_complex_ofReal`：integral_complex_ofReal {f : X -> Real} : ∫ x, 
(f x : Complex) ∂μ = ∫ x, f x ∂μ
· 使用定理 `ProbabilityTheory.variance_nonneg`：variance_nonneg (X : Ω -> Real) (μ : 
Measure Ω) : 0 <= variance X μ

--- 原说明 ---
The characteristic function of a Gaussian measure `μ` has value
`exp (μ[L] * I - Var[L; μ] / 2)` at `L : Dual ℝ E`.
-/
lemma IsGaussian.charFunDual_eq (L : StrongDual ℝ E) :
    charFunDual μ L = exp (μ[L] * I - Var[L; μ] / 2) := by
  calc charFunDual μ L
  _ = charFun (μ.map L) 1 := by rw [charFunDual_eq_charFun_map_one]
  _ = charFun (gaussianReal (μ[L]) (Var[L; μ]).toNNReal) 1 := by
    rw [IsGaussian.map_eq_gaussianReal L]
  _ = exp (μ[L] * I - Var[L; μ] / 2) := by
    rw [charFun_gaussianReal]
    simp only [ofReal_one, one_mul, Real.coe_toNNReal', one_pow, mul_one]
    congr
    · rw [integral_complex_ofReal]
    · simp only [sup_eq_left]
      exact variance_nonneg _ _

/-- A finite measure is Gaussian iff its characteristic function has value
`exp (μ[L] * I - Var[L; μ] / 2)` for every `L : Dual ℝ E`. -/
/-
**ProbabilityTheory.isGaussian_iff_charFunDual_eq** 是 Mathlib 中的一个定理，位于命名空间 `Pro
babilityTheory`。
形式化陈述：isGaussian_iff_charFunDual_eq {μ : Measure E} [IsFiniteMeasure μ] : IsGaus
sian μ ↔ forall L : StrongDual Real E, charFunDual μ L = exp (μ[L] * I - Var[L; 
μ] / 2)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ProbabilityTheory.IsGaussian.charFunDual_eq`：∀ {E : Type u_1} [inst : No
rmedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : MeasurableSpace E] [Bor
elSpace E]   {μ : MeasureTheory.M…
· 使用定理 `MeasureTheory.Measure.ext_of_charFun`：∀ {E : Type u_3} [inst : Measurabl
eSpace E] {μ ν : MeasureTheory.Measure E} [inst_1 : NormedAddCommGroup E]   [ins
t_2 : InnerProductSpace ℝ …
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.charFun_map_eq_charFunDual_smul`：charFun_map_eq_charFunDua
l_smul [OpensMeasurableSpace E] (L : StrongDual Real E) (u : Real) : charFun (μ.
map L) u = charFunDual μ (u • L)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `ProbabilityTheory.charFun_gaussianReal`：charFun_gaussianReal (t : Real) 
: charFun (gaussianReal μ v) t = cexp (t * μ * I - v * t ^ 2 / 2)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `MeasureTheory.integral_const_mul`：integral_const_mul {L : Type*} [RCLike
 L] (r : L) (f : α -> L) : ∫ a, r * f a ∂μ = r * ∫ a, f a ∂μ
· 使用定理 `integral_complex_ofReal`：integral_complex_ofReal {f : X -> Real} : ∫ x, 
(f x : Complex) ∂μ = ∫ x, f x ∂μ
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
· 使用定理 `ProbabilityTheory.variance_nonneg`：variance_nonneg (X : Ω -> Real) (μ : 
Measure Ω) : 0 <= variance X μ
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.ofReal_pow`：ofReal_pow (r : Real) (n : Nat) : ((r ^ n : Real) : 
Complex) = (r : Complex) ^ n
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
A finite measure is Gaussian iff its characteristic function has value
`exp (μ[L] * I - Var[L; μ] / 2)` for every `L : Dual ℝ E`.
-/
theorem isGaussian_iff_charFunDual_eq {μ : Measure E} [IsFiniteMeasure μ] :
    IsGaussian μ ↔ ∀ L : StrongDual ℝ E, charFunDual μ L = exp (μ[L] * I - Var[L; μ] / 2) := by
  refine ⟨fun h ↦ h.charFunDual_eq, fun h ↦ ⟨fun L ↦ Measure.ext_of_charFun ?_⟩⟩
  ext u
  rw [charFun_map_eq_charFunDual_smul L u, h (u • L), charFun_gaussianReal]
  simp only [smul_apply, smul_eq_mul, ofReal_mul, Real.coe_toNNReal']
  congr
  · rw [integral_const_mul, integral_complex_ofReal]
  · rw [max_eq_left (variance_nonneg _ _), mul_comm, ← ofReal_pow, ← ofReal_mul,
      ← variance_const_mul]
    congr

alias ⟨_, isGaussian_of_charFunDual_eq⟩ := isGaussian_iff_charFunDual_eq

end charFunDual

section charFun

open InnerProductSpace
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] {μ : Measure E}

/-
**ProbabilityTheory.IsGaussian.charFun_eq** 是 Mathlib 中的一个定理，位于命名空间 `Probability
Theory.IsGaussian`。
形式化陈述：∀ {E : Type u_3} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace
 ℝ E] [inst_2 : MeasurableSpace E]   [BorelSpace E] {μ : MeasureTheory.Measure E
} [ProbabilityTheory.IsGaussian μ] (t : E),   MeasureTheory.charFun μ t =     Co
mplex.exp       ((∫ (x : E), ↑((fun x => inner ℝ t x) x) ∂μ) * Complex.I -      
   ↑(ProbabilityTheory.variance (fun x => inner ℝ t x) μ) / 2)
参数：t : E；(∫ (x : E), ↑((fun x => inner ℝ t x) x) ∂μ) * Complex.I -         ↑(Pro
babilityTheory.variance (fun x => inner ℝ t x) μ) / 2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
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
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.charFun_eq_charFunDual_toDualMap`：charFun_eq_charFunDual_t
oDualMap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E] {mE : Mea
surableSpace E} {μ : Measure E} (t :…
· 使用定理 `ProbabilityTheory.IsGaussian.charFunDual_eq`：∀ {E : Type u_1} [inst : No
rmedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : MeasurableSpace E] [Bor
elSpace E]   {μ : MeasureTheory.M…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsGaussian.charFun_eq [IsGaussian μ] (t : E) :
    charFun μ t = exp (μ[fun x ↦ ⟪t, x⟫] * I - Var[fun x ↦ ⟪t, x⟫; μ] / 2) := by
  rw [charFun_eq_charFunDual_toDualMap, IsGaussian.charFunDual_eq]
  simp [toDualMap]

-- TODO: This should not require completeness as `toDualMap` has dense range, but this is not
-- in mathlib.
/-
**ProbabilityTheory.isGaussian_iff_charFun_eq** 是 Mathlib 中的一个引理，位于命名空间 `Probabi
lityTheory`。
形式化陈述：isGaussian_iff_charFun_eq [CompleteSpace E] [IsFiniteMeasure μ] : IsGaussi
an μ ↔ forall t, charFun μ t = exp (μ[fun x => ⟪t, x⟫] * I - Var[fun x => ⟪t, x⟫
; μ] / 2)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
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
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `LinearIsometryEquiv.surjective`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Ty
pe u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+
* R₂} {σ₂₁ : R₂ →+* …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `MeasureTheory.charFun_eq_charFunDual_toDualMap`：charFun_eq_charFunDual_t
oDualMap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E] {mE : Mea
surableSpace E} {μ : Measure E} (t :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `innerSL_apply_norm`：innerSL_apply_norm (x : E) : ‖innerSL 𝕜 x‖ = ‖x‖
· 使用定理 `LinearIsometryEquiv.coe_ofSurjective`：coe_ofSurjective (f : F ->ₛₗᵢ[σ₁₂]
 E₂) (hfr : Function.Surjective f) : ⇑(LinearIsometryEquiv.ofSurjective f hfr) =
 f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isGaussian_iff_charFun_eq [CompleteSpace E] [IsFiniteMeasure μ] :
    IsGaussian μ ↔
    ∀ t, charFun μ t = exp (μ[fun x ↦ ⟪t, x⟫] * I - Var[fun x ↦ ⟪t, x⟫; μ] / 2) := by
  simp_rw [isGaussian_iff_charFunDual_eq, (toDual ℝ E).surjective.forall,
    charFun_eq_charFunDual_toDualMap]
  simp [toDualMap, toDual]

end charFun

/-
**ProbabilityTheory.isGaussian_conv** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory
`。
形式化陈述：isGaussian_conv [SecondCountableTopology E] {μ ν : Measure E} [IsGaussian 
μ] [IsGaussian ν] : IsGaussian (μ ∗ ν) where map_eq_gaussianReal L
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.map_conv_continuousLinearMap`：map_conv_continuousL
inearMap {E F : Type*} [AddCommMonoid E] [AddCommMonoid F] [Module Real E] [Modu
le Real F] [TopologicalSpace E] [Topolog…
· 使用定理 `ContinuousAdd.measurableMul₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Add γ] [Con…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
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
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.sigmaFinite_of_locallyFinite`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace α]   [Secon
dCountableTopology α] [MeasureTh…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toIsLocallyFiniteMeasure`：∀ {α : Type u_1}
 {m0 : MeasurableSpace α} [inst : TopologicalSpace α] (μ : MeasureTheory.Measure
 α)   [MeasureTheory.IsFiniteMeasure μ], Mea…
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `ProbabilityTheory.IsGaussian.toIsProbabilityMeasure`：∀ {E : Type u_1} [i
nst : TopologicalSpace E] [inst_1 : AddCommMonoid E] [inst_2 : _root_.Module ℝ E
]   {mE : MeasurableSpace E} (μ : Measure…
· 使用定理 `MeasureTheory.integral_map`：integral_map {β} [MeasurableSpace β] {φ : α 
-> β} (hφ : AEMeasurable φ μ) {f : β -> G} (hfm : AEStronglyMeasurable f (Measur
e.map φ μ)) : ∫ …
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `ContinuousLinearMap.measurable`：∀ {R : Type u_2} {E : Type u_3} {F : Typ
e u_4} [inst : Semiring R] [inst_1 : SeminormedAddCommGroup E]   [inst_2 : _root
_.Module R E] [inst_…
· 使用定理 `aestronglyMeasurable_id`：∀ {α : Type u_5} [inst : TopologicalSpace α] [T
opologicalSpace.PseudoMetrizableSpace α] {x : MeasurableSpace α}   [OpensMeasura
bleSpace α] […
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用引理 `ProbabilityTheory.variance_id_map`：variance_id_map (hX : AEMeasurable X 
μ) : Var[id; μ.map X] = Var[X; μ]
· 使用定理 `ProbabilityTheory.IsGaussian.map_eq_gaussianReal`：∀ {E : Type u_1} {inst
 : TopologicalSpace E} {inst_1 : AddCommMonoid E} {inst_2 : _root_.Module ℝ E}  
 {mE : MeasurableSpace E} {μ : Measure…
· 使用引理 `ProbabilityTheory.gaussianReal_conv_gaussianReal`：gaussianReal_conv_gaus
sianReal {m₁ m₂ : Real} {v₁ v₂ : Real>=0} : (gaussianReal m₁ v₁) ∗ (gaussianReal
 m₂ v₂) = gaussianReal (m₁ + m₂) (v₁ +…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `ProbabilityTheory.integral_id_gaussianReal`：integral_id_gaussianReal : ∫
 x, x ∂gaussianReal μ v = μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 34 条，此处仅展示前 30 条）
-/
instance isGaussian_conv [SecondCountableTopology E]
    {μ ν : Measure E} [IsGaussian μ] [IsGaussian ν] :
    IsGaussian (μ ∗ ν) where
  map_eq_gaussianReal L := by
    have : (μ ∗ ν)[L] = ∫ x, x ∂((μ.map L).conv (ν.map L)) := by
      rw [← Measure.map_conv_continuousLinearMap L,
        integral_map (φ := L) (by fun_prop) (by fun_prop)]
    rw [Measure.map_conv_continuousLinearMap L, this, ← variance_id_map (by fun_prop),
      Measure.map_conv_continuousLinearMap L, IsGaussian.map_eq_gaussianReal L,
      IsGaussian.map_eq_gaussianReal L, gaussianReal_conv_gaussianReal]
    congr <;> simp [variance_nonneg]
/-
**ProbabilityTheory.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (c : E) : IsGaussian (μ.map (fun x ↦ x + c)) := by
  refine isGaussian_of_charFunDual_eq fun L ↦ ?_
  rw [charFunDual_map_add_const, IsGaussian.charFunDual_eq, ← exp_add]
  have hL_comp : L ∘ (fun x ↦ x + c) = fun x ↦ L x + L c := by ext; simp
  rw [variance_map (by fun_prop) (by fun_prop), integral_map (by fun_prop) (by fun_prop),
    hL_comp, variance_add_const (by fun_prop), integral_complex_ofReal, integral_complex_ofReal]
  simp only [map_add]
  rw [integral_add (by fun_prop) (by fun_prop)]
  congr
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, ofReal_add]
  ring
/-
**ProbabilityTheory.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (c : E) : IsGaussian (μ.map (fun x ↦ c + x)) := by simp_rw [add_comm c]; infer_instance
/-
**ProbabilityTheory.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (c : E) : IsGaussian (μ.map (fun x ↦ x - c)) := by simp_rw [sub_eq_add_neg]; infer_instance
/-
**ProbabilityTheory.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsGaussian (μ.map (fun x ↦ -x)) := by
  change IsGaussian (μ.map (ContinuousLinearEquiv.neg ℝ))
  infer_instance
/-
**ProbabilityTheory.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (c : E) : IsGaussian (μ.map (fun x ↦ c - x)) := by
  simp_rw [sub_eq_add_neg]
  suffices IsGaussian ((μ.map (fun x ↦ -x)).map (fun x ↦ c + x)) by
    rwa [Measure.map_map (by fun_prop) (by fun_prop), Function.comp_def] at this
  infer_instance

/-- A product of Gaussian distributions is Gaussian. -/
/-
**ProbabilityTheory.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A product of Gaussian distributions is Gaussian.
-/
instance [SecondCountableTopologyEither E F] {ν : Measure F} [IsGaussian ν] :
    IsGaussian (μ.prod ν) := by
  refine isGaussian_of_charFunDual_eq fun L ↦ ?_
  rw [charFunDual_prod, IsGaussian.charFunDual_eq, IsGaussian.charFunDual_eq, ← Complex.exp_add]
  congr
  let (eq := hL₁) L₁ := L.comp (.inl ℝ E F)
  let (eq := hL₂) L₂ := L.comp (.inr ℝ E F)
  rw [← hL₁, ← hL₂, sub_add_sub_comm, ← add_mul]
  congr
  · simp_rw [integral_complex_ofReal]
    rw [integral_continuousLinearMap_prod' (IsGaussian.integrable_dual μ (L.comp (.inl ℝ E F)))
      (IsGaussian.integrable_dual ν (L.comp (.inr ℝ E F)))]
    norm_cast
  · field_simp
    rw [variance_dual_prod' (IsGaussian.memLp_dual μ (L.comp (.inl ℝ E F)) 2 (by simp))
      (IsGaussian.memLp_dual ν (L.comp (.inr ℝ E F)) 2 (by simp))]
    norm_cast

end ProbabilityTheory

