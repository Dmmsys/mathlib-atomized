/-
Copyright (c) 2024 Jakob Stiefel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Stiefel, Rémy Degenne, Thomas Zhu
-/
module

public import Mathlib.Analysis.Fourier.BoundedContinuousFunctionChar
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.MeasureTheory.Group.IntegralConvolution
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.FiniteMeasureExt

/-!
# Characteristic Function of a Finite Measure

This file defines the characteristic function of a finite measure on a topological vector space `V`.

The characteristic function of a finite measure `P` on `V` is the mapping
`W → ℂ, w => ∫ v, e (L v w) ∂P`,
where `e` is a continuous additive character and `L : V →ₗ[ℝ] W →ₗ[ℝ] ℝ` is a bilinear map.

A typical example is `V = W = ℝ` and `L v w = v * w`.

The integral is expressed as `∫ v, char he hL w v ∂P`, where `char he hL w` is the
bounded continuous function `fun v ↦ e (L v w)` and `he`, `hL` are continuity hypotheses on `e`
and `L`.

## Main definitions

* `innerProbChar`: the bounded continuous map `x ↦ exp(⟪x, t⟫ * I)` in an inner product space.
  This is `char` for the inner product bilinear map and the additive character `e = probChar`.
* `charFun μ t`: the characteristic function of a measure `μ` at `t` in an inner product space `E`.
  This is defined as `∫ x, exp (⟪x, t⟫ * I) ∂μ`, where `⟪x, t⟫` is the inner product on `E`.
  It is equal to `∫ v, innerProbChar w v ∂P` (see `charFun_eq_integral_innerProbChar`).
* `probCharDual`: the bounded continuous map `x ↦ exp (L x * I)`, for a continuous linear form `L`.
* `charFunDual μ L`: the characteristic function of a measure `μ` at `L : Dual ℝ E` in
  a normed space `E`. This is the integral `∫ v, exp (L v * I) ∂μ`.

## Main statements

* `ext_of_integral_char_eq`: Assume `e` and `L` are non-trivial. If the integrals of `char`
  with respect to two finite measures `P` and `P'` coincide, then `P = P'`.
* `Measure.ext_of_charFun`: If the characteristic functions `charFun` of two finite measures
  `μ` and `ν` on a complete second-countable inner product space coincide, then `μ = ν`.
* `Measure.ext_of_charFunDual`: If the characteristic functions `charFunDual` of two finite measures
  `μ` and `ν` on a Banach space coincide, then `μ = ν`.

-/

@[expose] public section

open BoundedContinuousFunction RealInnerProductSpace Real Complex ComplexConjugate WithLp

open scoped ENNReal

namespace BoundedContinuousFunction

variable {E F : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
  [SeminormedAddCommGroup F] [NormedSpace ℝ F]

/-- The bounded continuous map `x ↦ exp(⟪x, t⟫ * I)`. -/
noncomputable
/-
**BoundedContinuousFunction.innerProbChar** 是 Mathlib 中的一个定义，位于命名空间 `BoundedCont
inuousFunction`。
形式化陈述：innerProbChar (t : E) : E ->ᵇ Complex
参数：t : E。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Real.continuous_probChar`：continuous_probChar : Continuous probChar
· 使用定理 `continuous_inner`：continuous_inner : Continuous fun p : E × E => ⟪p.1, p
.2⟫
-/
def innerProbChar (t : E) : E →ᵇ ℂ :=
  char continuous_probChar (L := innerₗ E) continuous_inner t
/-
**BoundedContinuousFunction.innerProbChar_apply** 是 Mathlib 中的一个引理，位于命名空间 `Bound
edContinuousFunction`。
形式化陈述：innerProbChar_apply (t x : E) : innerProbChar t x = exp (⟪x, t⟫ * I)
参数：t x : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma innerProbChar_apply (t x : E) : innerProbChar t x = exp (⟪x, t⟫ * I) := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**BoundedContinuousFunction.innerProbChar_zero** 是 Mathlib 中的一个引理，位于命名空间 `Bounde
dContinuousFunction`。
形式化陈述：innerProbChar_zero : innerProbChar (0 : E) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `BoundedContinuousFunction.char_zero_eq_one`：char_zero_eq_one : char he h
L 0 = 1
· 使用定理 `Real.continuous_probChar`：continuous_probChar : Continuous probChar
· 使用定理 `continuous_inner`：continuous_inner : Continuous fun p : E × E => ⟪p.1, p
.2⟫
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma innerProbChar_zero : innerProbChar (0 : E) = 1 := by simp [innerProbChar]

/-- The bounded continuous map `x ↦ exp (L x * I)`, for a continuous linear form `L`. -/
noncomputable
/-
**BoundedContinuousFunction.probCharDual** 是 Mathlib 中的一个定义，位于命名空间 `BoundedConti
nuousFunction`。
形式化陈述：probCharDual (L : StrongDual Real F) : F ->ᵇ Complex
参数：L : StrongDual Real F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Real.continuous_probChar`：continuous_probChar : Continuous probChar
-/
def probCharDual (L : StrongDual ℝ F) : F →ᵇ ℂ :=
  char continuous_probChar
    (L := isBoundedBilinearMap_apply.symm.toContinuousLinearMap.toLinearMap₁₂)
    isBoundedBilinearMap_apply.symm.continuous L
/-
**BoundedContinuousFunction.probCharDual_apply** 是 Mathlib 中的一个引理，位于命名空间 `Bounde
dContinuousFunction`。
形式化陈述：probCharDual_apply (L : StrongDual Real F) (x : F) : probCharDual L x = ex
p (L x * I)
参数：L : StrongDual Real F；x : F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma probCharDual_apply (L : StrongDual ℝ F) (x : F) : probCharDual L x = exp (L x * I) := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**BoundedContinuousFunction.probCharDual_zero** 是 Mathlib 中的一个引理，位于命名空间 `Bounded
ContinuousFunction`。
形式化陈述：probCharDual_zero : probCharDual (0 : StrongDual Real F) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `BoundedContinuousFunction.char_zero_eq_one`：char_zero_eq_one : char he h
L 0 = 1
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Real.continuous_probChar`：continuous_probChar : Continuous probChar
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma probCharDual_zero : probCharDual (0 : StrongDual ℝ F) = 1 := by simp [probCharDual]

end BoundedContinuousFunction

namespace MeasureTheory

variable {W : Type*} [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
    {e : AddChar ℝ Circle}

section ext

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [PseudoEMetricSpace V] [MeasurableSpace V]
    [BorelSpace V] [CompleteSpace V] [SecondCountableTopology V] {L : V →ₗ[ℝ] W →ₗ[ℝ] ℝ}

/-- If the integrals of `char` with respect to two finite measures `P` and `P'` coincide, then
`P = P'`. -/
/-
**MeasureTheory.ext_of_integral_char_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：ext_of_integral_char_eq (he : Continuous e) (he' : e != 1) (hL' : forall v
 != 0, L v != 0) (hL : Continuous fun p : V × W => L p.1 p.2) {P P' : Measure V}
 [IsFiniteMeasure P] [IsFiniteMeasure P'] (h : forall w, ∫ v, char he hL w v ∂P 
= ∫ v, char he hL w v ∂P') : P = P'
参数：he : Continuous e；he' : e != 1；hL' : forall v != 0, L v != 0；hL : Continuous 
fun p : V × W => L p.1 p.2；h : forall w, ∫ v, char he hL w v ∂P = ∫ v, char he h
L w v ∂P'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `MeasureTheory.ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_
complete_countable`：ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_co
mplete_countable [PseudoEMetricSpace E] [BorelSpace E] [CompleteSpace E] [Second
…
· 使用引理 `BoundedContinuousFunction.separatesPoints_charPoly`：separatesPoints_char
Poly (he : Continuous e) (he' : e != 1) (hL : Continuous fun p : V × W => L p.1 
p.2) (hL' : forall v != 0, L v != 0) : (…
· 使用定理 `instBoundedMul`：∀ {R : Type u_1} [inst : NonUnitalSeminormedRing R], Bou
ndedMul R
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
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `CStarRing.to_normedStarGroup`：∀ {E : Type u_2} [inst : NonUnitalNormedRi
ng E] [inst_1 : StarRing E] [CStarRing E], NormedStarGroup E
· 使用定理 `RCLike.instCStarRing`：∀ {K : Type u_1} [inst : RCLike K], CStarRing K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_finsetSum`：integral_finsetSum {ι} (s : Finset ι) 
{f : ι -> α -> G} (hf : forall i in s, Integrable (f i) μ) : ∫ a, ∑ i in s, f i 
a ∂μ = ∑ i in s, ∫ a, …
· 使用定理 `MeasureTheory.Integrable.const_mul`：∀ {α : Type u_1} {m : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} {𝕜 : Type u_8} [inst : NormedRing 𝕜] {f : α →
 𝕜},   MeasureTheory.Int…
· 使用引理 `BoundedContinuousFunction.integrable`：integrable [IsFiniteMeasure μ] (f 
: X ->ᵇ E) : Integrable f μ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.integral_const_mul`：integral_const_mul {L : Type*} [RCLike
 L] (r : L) (f : α -> L) : ∫ a, r * f a ∂μ = r * ∫ a, f a ∂μ
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
If the integrals of `char` with respect to two finite measures `P` and `P'` coin
cide, then
`P = P'`.
-/
theorem ext_of_integral_char_eq (he : Continuous e) (he' : e ≠ 1)
    (hL' : ∀ v ≠ 0, L v ≠ 0) (hL : Continuous fun p : V × W ↦ L p.1 p.2)
    {P P' : Measure V} [IsFiniteMeasure P] [IsFiniteMeasure P']
    (h : ∀ w, ∫ v, char he hL w v ∂P = ∫ v, char he hL w v ∂P') :
    P = P' := by
  apply ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable
      (separatesPoints_charPoly he he' hL hL')
  intro _ hg
  simp only [mem_charPoly] at hg
  obtain ⟨w, hw⟩ := hg
  rw [hw]
  have hsum (P : Measure V) [IsFiniteMeasure P] :
      ∫ v, w.coeff.sum (fun a z ↦ z * e (L v a)) ∂P =
        w.coeff.sum (fun a z ↦ ∫ v, z * e (L v a) ∂P) :=
    integral_finsetSum _ fun a ha ↦ ((char he hL a).integrable P).const_mul  _
  rw [hsum P, hsum P']
  apply Finset.sum_congr rfl fun i _ => ?_
  simp only [MeasureTheory.integral_const_mul, mul_eq_mul_left_iff]
  exact Or.inl (h i)

end ext

section InnerProductSpace

variable {E : Type*} {mE : MeasurableSpace E} {μ : Measure E} {t : E}

/-- The characteristic function of a measure in an inner product space. -/
/-
**MeasureTheory.charFun** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：charFun [Inner Real E] (μ : Measure E) (t : E) : Complex
参数：μ : Measure E；t : E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The characteristic function of a measure in an inner product space.
-/
noncomputable def charFun [Inner ℝ E] (μ : Measure E) (t : E) : ℂ := ∫ x, exp (⟪x, t⟫ * I) ∂μ
/-
**MeasureTheory.charFun_apply** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：charFun_apply [Inner Real E] (t : E) : charFun μ t = ∫ x, exp (⟪x, t⟫ * I)
 ∂μ
参数：t : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma charFun_apply [Inner ℝ E] (t : E) : charFun μ t = ∫ x, exp (⟪x, t⟫ * I) ∂μ := rfl
/-
**MeasureTheory.charFun_apply_real** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：charFun_apply_real {μ : Measure Real} (t : Real) : charFun μ t = ∫ x, exp 
(t * x * I) ∂μ
参数：t : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `conj_trivial`：∀ {R : Type u} [inst : CommSemiring R] [inst_1 : StarRing 
R] [TrivialStar R] (a : R), (starRingEnd R) a = a
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma charFun_apply_real {μ : Measure ℝ} (t : ℝ) :
    charFun μ t = ∫ x, exp (t * x * I) ∂μ := by simp [charFun_apply]

variable [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

@[simp]
/-
**MeasureTheory.charFun_zero** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：charFun_zero (μ : Measure E) : charFun μ 0 = μ.real Set.univ
参数：μ : Measure E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `inner_zero_right`：inner_zero_right (x : E) : ⟪x, 0⟫ = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Complex.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `MeasureTheory.integral_const`：integral_const (c : E) : ∫ _ : α, c ∂μ = μ
.real univ • c
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma charFun_zero (μ : Measure E) : charFun μ 0 = μ.real Set.univ := by
  simp [charFun_apply]

@[simp]
/-
**MeasureTheory.charFun_zero_measure** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：charFun_zero_measure : charFun (0 : Measure E) t = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_zero_measure`：integral_zero_measure {m : Measurab
leSpace α} (f : α -> G) : (∫ x, f x ∂(0 : Measure α)) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma charFun_zero_measure : charFun (0 : Measure E) t = 0 := by simp [charFun_apply]

@[simp]
/-
**MeasureTheory.charFun_neg** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：charFun_neg (t : E) : charFun μ (-t) = conj (charFun μ t)
参数：t : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `inner_neg_right`：inner_neg_right (x y : E) : ⟪x, -y⟫ = -⟪x, y⟫
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Complex.conj_ofReal`：conj_ofReal (r : Real) : conj (r : Complex) = r
· 使用定理 `Complex.conj_I`：conj_I : conj I = -I
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma charFun_neg (t : E) : charFun μ (-t) = conj (charFun μ t) := by
  simp [charFun_apply, ← integral_conj, ← exp_conj]

/-- `charFun` as the integral of a bounded continuous function. -/
/-
**MeasureTheory.charFun_eq_integral_innerProbChar** 是 Mathlib 中的一个引理，位于命名空间 `Mea
sureTheory`。
形式化陈述：charFun_eq_integral_innerProbChar : charFun μ t = ∫ v, innerProbChar t v ∂
μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`charFun` as the integral of a bounded continuous function.
-/
lemma charFun_eq_integral_innerProbChar : charFun μ t = ∫ v, innerProbChar t v ∂μ := by
  simp [charFun_apply, innerProbChar_apply]
/-
**MeasureTheory.charFun_eq_integral_probChar** 是 Mathlib 中的一个引理，位于命名空间 `MeasureT
heory`。
形式化陈述：charFun_eq_integral_probChar (t : E) : charFun μ t = ∫ x, (probChar ⟪x, t⟫
 : Complex) ∂μ
参数：t : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma charFun_eq_integral_probChar (t : E) : charFun μ t = ∫ x, (probChar ⟪x, t⟫ : ℂ) ∂μ := by
  simp [charFun_apply, probChar_apply]

/-- `charFun` is a Fourier integral for the inner product and the character `probChar`. -/
/-
**MeasureTheory.charFun_eq_fourierIntegral** 是 Mathlib 中的一个引理，位于命名空间 `MeasureThe
ory`。
形式化陈述：charFun_eq_fourierIntegral (t : E) : charFun μ t = VectorFourier.fourierIn
tegral probChar μ (innerₗ E) 1 (-t)
参数：t : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `VectorFourier.fourierIntegral_probChar`：fourierIntegral_probChar {V W : 
Type*} {_ : MeasurableSpace V} [AddCommGroup V] [Module Real V] [AddCommGroup W]
 [Module Real W] (L : V ->ₗ[…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inner_neg_right`：inner_neg_right (x y : E) : ⟪x, -y⟫ = -⟪x, y⟫
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`charFun` is a Fourier integral for the inner product and the character `probCha
r`.
-/
lemma charFun_eq_fourierIntegral (t : E) :
    charFun μ t = VectorFourier.fourierIntegral probChar μ (innerₗ E) 1 (-t) := by
  simp [charFun_apply, VectorFourier.fourierIntegral_probChar]

/-- `charFun` is a Fourier integral for the inner product and the character `fourierChar`. -/
/-
**MeasureTheory.charFun_eq_fourierIntegral'** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTh
eory`。
形式化陈述：charFun_eq_fourierIntegral' (t : E) : charFun μ t = VectorFourier.fourierI
ntegral fourierChar μ (innerₗ E) 1 (-(2 * π)⁻¹ • t)
参数：t : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `inner_neg_right`：inner_neg_right (x y : E) : ⟪x, -y⟫ = -⟪x, y⟫
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Complex.ofReal_inv`：ofReal_inv (r : Real) : ((r⁻¹ : Real) : Complex) = (
r : Complex)⁻¹
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a

--- 原说明 ---
`charFun` is a Fourier integral for the inner product and the character `fourier
Char`.
-/
lemma charFun_eq_fourierIntegral' (t : E) :
    charFun μ t
      = VectorFourier.fourierIntegral fourierChar μ (innerₗ E) 1 (-(2 * π)⁻¹ • t) := by
  simp only [charFun_apply, VectorFourier.fourierIntegral, neg_smul,
    innerₗ_apply_apply, inner_neg_right, inner_smul_right, neg_neg,
    fourierChar_apply', Pi.ofNat_apply, Circle.smul_def, Circle.coe_exp, ofReal_mul, ofReal_ofNat,
    ofReal_inv, smul_eq_mul, mul_one]
  congr with x
  rw [← mul_assoc, mul_inv_cancel₀ (by simp [pi_ne_zero]), one_mul]
/-
**MeasureTheory.norm_charFun_le** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：norm_charFun_le (t : E) : ‖charFun μ t‖ <= μ.real Set.univ
参数：t : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.charFun_eq_fourierIntegral`：charFun_eq_fourierIntegral (t 
: E) : charFun μ t = VectorFourier.fourierIntegral probChar μ (innerₗ E) 1 (-t)
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `VectorFourier.norm_fourierIntegral_le_integral_norm`：norm_fourierIntegra
l_le_integral_norm (e : AddChar 𝕜 𝕊) (μ : Measure V) (L : V ->ₗ[𝕜] W ->ₗ[𝕜] 𝕜) (
f : V -> E) (w : W) : ‖fourierIntegral e …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `MeasureTheory.integral_const`：integral_const (c : E) : ∫ _ : α, c ∂μ = μ
.real univ • c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma norm_charFun_le (t : E) : ‖charFun μ t‖ ≤ μ.real Set.univ := by
  rw [charFun_eq_fourierIntegral]
  exact (VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _).trans_eq (by simp)
/-
**MeasureTheory.norm_charFun_le_one** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：norm_charFun_le_one [IsProbabilityMeasure μ] (t : E) : ‖charFun μ t‖ <= 1
参数：t : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用引理 `MeasureTheory.norm_charFun_le`：norm_charFun_le (t : E) : ‖charFun μ t‖ <
= μ.real Set.univ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.probReal_univ`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {
μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ],   μ.real Se
t.univ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma norm_charFun_le_one [IsProbabilityMeasure μ] (t : E) : ‖charFun μ t‖ ≤ 1 :=
  (norm_charFun_le _).trans_eq (by simp)
/-
**MeasureTheory.norm_one_sub_charFun_le_two** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTh
eory`。
形式化陈述：norm_one_sub_charFun_le_two [IsProbabilityMeasure μ] : ‖1 - charFun μ t‖ <
= 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `norm_sub_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), ‖
a - b‖ ≤ ‖a‖ + ‖b‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `Mathlib.Meta.NormNum.isNat_eq_true`：∀ {α : Type u} [inst : AddMonoidWith
One α] {a b : α} {c : ℕ},   Mathlib.Meta.NormNum.IsNat a c → Mathlib.Meta.NormNu
m.IsNat b c → a = b
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
-/
lemma norm_one_sub_charFun_le_two [IsProbabilityMeasure μ] : ‖1 - charFun μ t‖ ≤ 2 :=
  calc ‖1 - charFun μ t‖
  _ ≤ ‖(1 : ℂ)‖ + ‖charFun μ t‖ := norm_sub_le _ _
  _ ≤ 1 + 1 := by simp [norm_charFun_le_one]
  _ = 2 := by norm_num

@[fun_prop]
/-
**MeasureTheory.stronglyMeasurable_charFun** 是 Mathlib 中的一个引理，位于命名空间 `MeasureThe
ory`。
形式化陈述：stronglyMeasurable_charFun [OpensMeasurableSpace E] [SecondCountableTopolo
gy E] [SFinite μ] : StronglyMeasurable (charFun μ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.integral_prod_left`：MeasureTheory.Stron
glyMeasurable.integral_prod_left [SFinite μ] ⦃f : α -> β -> E⦄ (hf : StronglyMea
surable (uncurry f)) : StronglyMeasurable…
· 使用定理 `Measurable.stronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {f : α → 
β} {mα : MeasurableSpace α} [inst : MeasurableSpace β]   [inst_1 : TopologicalSp
ace β] [Topological…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Measurable.cexp`：∀ {α : Type u_1} {m : MeasurableSpace α} {f : α → ℂ}, M
easurable f → Measurable fun x => Complex.exp (f x)
· 使用定理 `Measurable.mul_const`：Measurable.mul_const [MeasurableMul M] (hf : Measu
rable f) (c : M) : Measurable fun x => f x * c
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
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Measurable.complex_ofReal`：∀ {α : Type u_1} {m : MeasurableSpace α} {f :
 α → ℝ}, Measurable f → Measurable fun x => ↑(f x)
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `Continuous.inner`：Continuous.inner (hf : Continuous f) (hg : Continuous 
g) : Continuous fun t => ⟪f t, g t⟫
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
-/
lemma stronglyMeasurable_charFun [OpensMeasurableSpace E] [SecondCountableTopology E] [SFinite μ] :
    StronglyMeasurable (charFun μ) :=
  (Measurable.stronglyMeasurable (by fun_prop)).integral_prod_left

@[fun_prop]
/-
**MeasureTheory.measurable_charFun** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：measurable_charFun [OpensMeasurableSpace E] [SecondCountableTopology E] [S
Finite μ] : Measurable (charFun μ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用引理 `MeasureTheory.stronglyMeasurable_charFun`：stronglyMeasurable_charFun [Op
ensMeasurableSpace E] [SecondCountableTopology E] [SFinite μ] : StronglyMeasurab
le (charFun μ)
-/
lemma measurable_charFun [OpensMeasurableSpace E] [SecondCountableTopology E] [SFinite μ] :
    Measurable (charFun μ) :=
  stronglyMeasurable_charFun.measurable
/-
**MeasureTheory.intervalIntegrable_charFun** 是 Mathlib 中的一个引理，位于命名空间 `MeasureThe
ory`。
形式化陈述：intervalIntegrable_charFun {μ : Measure Real} [IsFiniteMeasure μ] {a b : R
eal} : IntervalIntegrable (charFun μ) volume a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntervalIntegrable.mono_fun'`：mono_fun' {f : Real -> E} {g : Real -> Rea
l} (hg : IntervalIntegrable g μ a b) (hfm : AEStronglyMeasurable f (μ.restrict (
Ι a b))) (hle : (f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用引理 `MeasureTheory.stronglyMeasurable_charFun`：stronglyMeasurable_charFun [Op
ensMeasurableSpace E] [SecondCountableTopology E] [SFinite μ] : StronglyMeasurab
le (charFun μ)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.sigmaFinite_of_locallyFinite`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace α]   [Secon
dCountableTopology α] [MeasureTh…
· 使用定理 `MeasureTheory.isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts`：∀ {α 
: Type u_1} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topol
ogicalSpace α]   [WeaklyLocallyCompactSpace α] [Measure…
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `MeasureTheory.Measure.Regular.toIsFiniteMeasureOnCompacts`：∀ {α : Type u
_1} {inst : MeasurableSpace α} {inst_1 : TopologicalSpace α} {μ : MeasureTheory.
Measure α}   [self : μ.Regular], MeasureTheory.…
· 使用定理 `MeasureTheory.Measure.InnerRegularCompactLTTop.instRegularOfBorelSpaceOf
R1SpaceOfIsFiniteMeasure`：∀ {α : Type u_1} [inst : MeasurableSpace α] {μ : Measu
reTheory.Measure α} [inst_1 : TopologicalSpace α] [BorelSpace α]   [R1Space α] [
h : μ.…
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.regularSpace`：∀ {X : Type u_2} [i
nst : TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X], RegularSpa
ce X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.toIsCompletelyPseudoMetriza
bleSpace`：∀ {X : Type u_1} [inst : TopologicalSpace X] [TopologicalSpace.IsCompl
etelyMetrizableSpace X],   TopologicalSpace.IsCompletelyPseudoMetrizab…
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
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.norm_charFun_le`：norm_charFun_le (t : E) : ‖charFun μ t‖ <
= μ.real Set.univ
-/
lemma intervalIntegrable_charFun {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ} :
    IntervalIntegrable (charFun μ) volume a b :=
  IntervalIntegrable.mono_fun' (g := fun _ ↦ μ.real Set.univ) (by simp)
    stronglyMeasurable_charFun.aestronglyMeasurable (ae_of_all _ norm_charFun_le)
/-
**MeasureTheory.charFun_map_smul** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：charFun_map_smul [BorelSpace E] (r : Real) (t : E) : charFun (μ.map (r • ·
)) t = charFun μ (r • t)
参数：r : Real；t : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.charFun_apply`：charFun_apply [Inner Real E] (t : E) : char
Fun μ t = ∫ x, exp (⟪x, t⟫ * I) ∂μ
· 使用定理 `MeasureTheory.integral_map`：integral_map {β} [MeasurableSpace β] {φ : α 
-> β} (hφ : AEMeasurable φ μ) {f : β -> G} (hfm : AEStronglyMeasurable f (Measur
e.map φ μ)) : ∫ …
· 使用定理 `AEMeasurable.fun_const_smul`：∀ {M : Type u_2} {X : Type u_3} {α : Type u
_4} [inst : MeasurableSpace X] [inst_1 : SMul M X] {m : MeasurableSpace α}   {μ 
: MeasureTheory.M…
· 使用定理 `MeasurableSMul.toMeasurableConstSMul`：∀ {M : Type u_2} {α : Type u_3} {i
nst : SMul M α} {inst_1 : MeasurableSpace M} {inst_2 : MeasurableSpace α}   [sel
f : MeasurableSMul M α], M…
· 使用定理 `ContinuousSMul.toMeasurableSMul`：∀ {M : Type u_7} {α : Type u_8} [inst :
 TopologicalSpace M] [inst_1 : TopologicalSpace α] [inst_2 : MeasurableSpace M] 
  [inst_3 : Measurabl…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `aemeasurable_id`：aemeasurable_id : AEMeasurable id μ
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用定理 `Continuous.cexp`：Continuous.cexp (h : Continuous f) : Continuous fun y =
> exp (f y)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `MeasureTheory.AEStronglyMeasurable.mul_const`：∀ {α : Type u_1} {β : Type
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
· 使用定理 `Continuous.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   {f
 : α → β} [inst_1 : T…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Continuous.inner`：Continuous.inner (hf : Continuous f) (hg : Continuous 
g) : Continuous fun t => ⟪f t, g t⟫
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma charFun_map_smul [BorelSpace E] (r : ℝ) (t : E) :
    charFun (μ.map (r • ·)) t = charFun μ (r • t) := by
  rw [charFun_apply, charFun_apply,
    integral_map (by fun_prop) (by fun_prop)]
  simp_rw [inner_smul_right, ← real_inner_smul_left]
/-
**MeasureTheory.charFun_map_smul_comp** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：charFun_map_smul_comp {X : Type*} {mX : MeasurableSpace X} {μ : Measure X}
 [BorelSpace E] {f : X -> E} (hf : AEMeasurable f μ) (r : Real) (t : E) : charFu
n (μ.map (fun x => r • (f x))) t = charFun (μ.map f) (r • t)
参数：hf : AEMeasurable f μ；r : Real；t : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AEMeasurable.map_map_of_aemeasurable`：map_map_of_aemeasurable {g : β -> 
γ} {f : α -> β} (hg : AEMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) 
: (μ.map f).map g = μ.map …
· 使用定理 `AEMeasurable.fun_const_smul`：∀ {M : Type u_2} {X : Type u_3} {α : Type u
_4} [inst : MeasurableSpace X] [inst_1 : SMul M X] {m : MeasurableSpace α}   {μ 
: MeasureTheory.M…
· 使用定理 `MeasurableSMul.toMeasurableConstSMul`：∀ {M : Type u_2} {α : Type u_3} {i
nst : SMul M α} {inst_1 : MeasurableSpace M} {inst_2 : MeasurableSpace α}   [sel
f : MeasurableSMul M α], M…
· 使用定理 `ContinuousSMul.toMeasurableSMul`：∀ {M : Type u_7} {α : Type u_8} [inst :
 TopologicalSpace M] [inst_1 : TopologicalSpace α] [inst_2 : MeasurableSpace M] 
  [inst_3 : Measurabl…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `aemeasurable_id`：aemeasurable_id : AEMeasurable id μ
· 使用引理 `MeasureTheory.charFun_map_smul`：charFun_map_smul [BorelSpace E] (r : Rea
l) (t : E) : charFun (μ.map (r • ·)) t = charFun μ (r • t)
-/
lemma charFun_map_smul_comp {X : Type*} {mX : MeasurableSpace X} {μ : Measure X} [BorelSpace E]
    {f : X → E} (hf : AEMeasurable f μ) (r : ℝ) (t : E) :
    charFun (μ.map (fun x ↦ r • (f x))) t = charFun (μ.map f) (r • t) := by
  rw [show (fun x ↦ r • (f x)) = (r • ·) ∘ f from rfl, ← AEMeasurable.map_map_of_aemeasurable,
    charFun_map_smul]
  all_goals fun_prop
/-
**MeasureTheory.charFun_map_mul** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：charFun_map_mul {μ : Measure Real} (r t : Real) : charFun (μ.map (r * ·)) 
t = charFun μ (r * t)
参数：r t : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.charFun_map_smul`：charFun_map_smul [BorelSpace E] (r : Rea
l) (t : E) : charFun (μ.map (r • ·)) t = charFun μ (r • t)
-/
lemma charFun_map_mul {μ : Measure ℝ} (r t : ℝ) :
    charFun (μ.map (r * ·)) t = charFun μ (r * t) := charFun_map_smul r t
/-
**MeasureTheory.charFun_map_mul_comp** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：charFun_map_mul_comp {X : Type*} {mX : MeasurableSpace X} {μ : Measure X} 
{f : X -> Real} (hf : AEMeasurable f μ) (r t : Real) : charFun (μ.map (fun x => 
r * (f x))) t = charFun (μ.map f) (r * t)
参数：hf : AEMeasurable f μ；r t : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.charFun_map_smul_comp`：charFun_map_smul_comp {X : Type*} {
mX : MeasurableSpace X} {μ : Measure X} [BorelSpace E] {f : X -> E} (hf : AEMeas
urable f μ) (r : Real) (t…
-/
lemma charFun_map_mul_comp {X : Type*} {mX : MeasurableSpace X} {μ : Measure X}
    {f : X → ℝ} (hf : AEMeasurable f μ) (r t : ℝ) :
    charFun (μ.map (fun x ↦ r * (f x))) t = charFun (μ.map f) (r * t) :=
  charFun_map_smul_comp hf r t

variable {E : Type*} [MeasurableSpace E] {μ ν : Measure E} {t : E}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

@[simp]
/-
**MeasureTheory.charFun_dirac** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：charFun_dirac [OpensMeasurableSpace E] {x : E} (t : E) : charFun (Measure.
dirac x) t = cexp (⟪x, t⟫ * I)
参数：t : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.charFun_apply`：charFun_apply [Inner Real E] (t : E) : char
Fun μ t = ∫ x, exp (⟪x, t⟫ * I) ∂μ
· 使用定理 `MeasureTheory.integral_dirac`：integral_dirac [MeasurableSpace α] [Measur
ableSingletonClass α] (f : α -> E) (a : α) : ∫ x, f x ∂Measure.dirac a = f a
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `OpensMeasurableSpace.toMeasurableSingletonClass`：∀ {α : Type u_1} [inst 
: TopologicalSpace α] [inst_1 : MeasurableSpace α] [OpensMeasurableSpace α] [T1S
pace α],   MeasurableSingletonClass α
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
-/
lemma charFun_dirac [OpensMeasurableSpace E] {x : E} (t : E) :
    charFun (Measure.dirac x) t = cexp (⟪x, t⟫ * I) := by
  rw [charFun_apply, integral_dirac]
/-
**MeasureTheory.charFun_map_add_const** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：charFun_map_add_const [BorelSpace E] (r t : E) : charFun (μ.map (· + r)) t
 = charFun μ t * cexp (⟪r, t⟫ * I)
参数：r t : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.charFun_apply`：charFun_apply [Inner Real E] (t : E) : char
Fun μ t = ∫ x, exp (⟪x, t⟫ * I) ∂μ
· 使用定理 `MeasureTheory.integral_map`：integral_map {β} [MeasurableSpace β] {φ : α 
-> β} (hφ : AEMeasurable φ μ) {f : β -> G} (hfm : AEStronglyMeasurable f (Measur
e.map φ μ)) : ∫ …
· 使用定理 `AEMeasurable.add_const`：∀ {M : Type u_2} {α : Type u_3} [inst : Measurab
leSpace M] [inst_1 : Add M] {m : MeasurableSpace α} {f : α → M}   {μ : MeasureTh
eory.Measure…
· 使用定理 `ContinuousAdd.measurableAdd`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Add γ]   [SeparatelyCont
inuousAdd γ], Mea…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `aemeasurable_id`：aemeasurable_id : AEMeasurable id μ
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用定理 `Continuous.cexp`：Continuous.cexp (h : Continuous f) : Continuous fun y =
> exp (f y)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `MeasureTheory.AEStronglyMeasurable.mul_const`：∀ {α : Type u_1} {β : Type
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
· 使用定理 `Continuous.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   {f
 : α → β} [inst_1 : T…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Continuous.inner`：Continuous.inner (hf : Continuous f) (hg : Continuous 
g) : Continuous fun t => ⟪f t, g t⟫
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_mul_const`：integral_mul_const {L : Type*} [RCLike
 L] (r : L) (f : α -> L) : ∫ a, f a * r ∂μ = (∫ a, f a ∂μ) * r
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Complex.exp_add`：exp_add : exp (x + y) = exp x * exp y
· 使用定理 `inner_add_left`：inner_add_left (x y z : E) : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z
⟫
（共 48 条，此处仅展示前 30 条）
-/
lemma charFun_map_add_const [BorelSpace E] (r t : E) :
    charFun (μ.map (· + r)) t = charFun μ t * cexp (⟪r, t⟫ * I) := by
  rw [charFun_apply, charFun_apply, integral_map (by fun_prop) (by fun_prop),
    ← integral_mul_const]
  congr with a
  rw [← Complex.exp_add]
  congr
  rw [inner_add_left]
  simp only [ofReal_add]
  ring
/-
**MeasureTheory.charFun_map_const_add** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：charFun_map_const_add [BorelSpace E] (r t : E) : charFun (μ.map (r + ·)) t
 = charFun μ t * cexp (⟪r, t⟫ * I)
参数：r t : E。
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
· 使用引理 `MeasureTheory.charFun_map_add_const`：charFun_map_add_const [BorelSpace E
] (r t : E) : charFun (μ.map (· + r)) t = charFun μ t * cexp (⟪r, t⟫ * I)
-/
lemma charFun_map_const_add [BorelSpace E] (r t : E) :
    charFun (μ.map (r + ·)) t = charFun μ t * cexp (⟪r, t⟫ * I) := by
  simp_rw [add_comm r]
  exact charFun_map_add_const _ _

variable [BorelSpace E] [SecondCountableTopology E]

/-- If the characteristic functions `charFun` of two finite measures `μ` and `ν` on
a complete second-countable inner product space coincide, then `μ = ν`. -/
/-
**MeasureTheory.Measure.ext_of_charFun** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：∀ {E : Type u_3} [inst : MeasurableSpace E] {μ ν : MeasureTheory.Measure E
} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace ℝ E] [BorelSpace
 E] [SecondCountableTopology E] [CompleteSpace E]   [MeasureTheory.IsFiniteMeasu
re μ] [MeasureTheory.IsFiniteMeasure ν],   MeasureTheory.charFun μ = MeasureTheo
ry.charFun ν → μ = ν
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.ext_of_integral_char_eq`：ext_of_integral_char_eq (he : Con
tinuous e) (he' : e != 1) (hL' : forall v != 0, L v != 0) (hL : Continuous fun p
 : V × W => L p.1 p.2) {P P…
· 使用定理 `Real.continuous_probChar`：continuous_probChar : Continuous probChar
· 使用定理 `Real.probChar_ne_one`：probChar_ne_one : probChar != 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `DFunLike.ne_iff`：ne_iff {f g : F} : f != g ↔ exists a, f a != g a
· 使用定理 `inner_self_ne_zero`：inner_self_ne_zero {x : E} : ⟪x, x⟫ != 0 ↔ x != 0
· 使用定理 `continuous_inner`：continuous_inner : Continuous fun p : E × E => ⟪p.1, p
.2⟫
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.charFun_eq_integral_innerProbChar`：charFun_eq_integral_inn
erProbChar : charFun μ t = ∫ v, innerProbChar t v ∂μ

--- 原说明 ---
If the characteristic functions `charFun` of two finite measures `μ` and `ν` on
a complete second-countable inner product space coincide, then `μ = ν`.
-/
theorem Measure.ext_of_charFun [CompleteSpace E]
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : charFun μ = charFun ν) :
    μ = ν := by
  simp_rw [funext_iff, charFun_eq_integral_innerProbChar] at h
  refine ext_of_integral_char_eq continuous_probChar probChar_ne_one (L := innerₗ E)
    ?_ ?_ h
  · exact fun v hv ↦ DFunLike.ne_iff.mpr ⟨v, inner_self_ne_zero.mpr hv⟩
  · exact continuous_inner

/-- The characteristic function of a convolution of measures
is the product of the respective characteristic functions. -/
/-
**MeasureTheory.charFun_conv** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：charFun_conv [IsFiniteMeasure μ] [IsFiniteMeasure ν] (t : E) : charFun (μ 
∗ ν) t = charFun μ t * charFun ν t
参数：t : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_conv`：∀ {M : Type u_1} {F : Type u_2} [inst : Add
Monoid M] {mM : MeasurableSpace M} [MeasurableAdd₂ M]   [inst_2 : NormedAddCommG
roup F] {μ ν : Me…
· 使用定理 `ContinuousAdd.measurableMul₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Add γ] [Con…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.sigmaFinite_of_locallyFinite`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace α]   [Secon
dCountableTopology α] [MeasureTh…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toIsLocallyFiniteMeasure`：∀ {α : Type u_1}
 {m0 : MeasurableSpace α} [inst : TopologicalSpace α] (μ : MeasureTheory.Measure
 α)   [MeasureTheory.IsFiniteMeasure μ], Mea…
· 使用定理 `MeasureTheory.Integrable.mono`：∀ {α : Type u_1} {β : Type u_2} {γ : Type
 u_3} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : NormedAddC
ommGroup β] [inst_1…
· 使用定理 `MeasureTheory.integrable_const`：integrable_const [IsFiniteMeasure μ] (c 
: β) : Integrable (fun _ : α => c) μ
· 使用定理 `MeasureTheory.Measure.finite_of_finite_conv`：∀ {M : Type u_1} [inst : Ad
dMonoid M] [inst_1 : MeasurableSpace M] (μ ν : MeasureTheory.Measure M)   [Measu
reTheory.IsFiniteMeasure μ] [Meas…
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用定理 `Continuous.cexp`：Continuous.cexp (h : Continuous f) : Continuous fun y =
> exp (f y)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `MeasureTheory.AEStronglyMeasurable.mul_const`：∀ {α : Type u_1} {β : Type
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
· 使用定理 `Continuous.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   {f
 : α → β} [inst_1 : T…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Continuous.inner`：Continuous.inner (hf : Continuous f) (hg : Continuous 
g) : Continuous fun t => ⟪f t, g t⟫
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
The characteristic function of a convolution of measures
is the product of the respective characteristic functions.
-/
lemma charFun_conv [IsFiniteMeasure μ] [IsFiniteMeasure ν] (t : E) :
    charFun (μ ∗ ν) t = charFun μ t * charFun ν t := by
  simp_rw [charFun_apply]
  rw [integral_conv]
  · simp [inner_add_left, add_mul, Complex.exp_add, integral_const_mul, integral_mul_const]
  · exact (integrable_const (1 : ℝ)).mono (by fun_prop) (by simp)

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ E] [InnerProductSpace ℝ F] {mE : MeasurableSpace E}
    {mF : MeasurableSpace F}

/-- The characteristic function of a product of measures is a product of
characteristic functions. This is the version for Hilbert spaces, see `charFunDual_prod`
for the Banach space version. -/
/-
**MeasureTheory.charFun_prod** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：charFun_prod {μ : Measure E} {ν : Measure F} [SFinite μ] [SFinite ν] (t : 
WithLp 2 (E × F)) : charFun ((μ.prod ν).map (toLp 2)) t = charFun μ (ofLp t).1 *
 charFun ν (ofLp t).2
参数：t : WithLp 2 (E × F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.integral_map_equiv`：integral_map_equiv {β} [MeasurableSpac
e β] (e : α ≃ᵐ β) (f : β -> G) : ∫ y, f y ∂Measure.map e μ = ∫ x, f (e x) ∂μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Complex.ofReal_add`：ofReal_add (r s : Real) : ((r + s : Real) : Complex)
 = r + s
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `Complex.exp_add`：exp_add : exp (x + y) = exp x * exp y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The characteristic function of a product of measures is a product of
characteristic functions. This is the version for Hilbert spaces, see `charFunDu
al_prod`
for the Banach space version.
-/
lemma charFun_prod {μ : Measure E} {ν : Measure F} [SFinite μ] [SFinite ν]
    (t : WithLp 2 (E × F)) :
    charFun ((μ.prod ν).map (toLp 2)) t =
      charFun μ (ofLp t).1 * charFun ν (ofLp t).2 := by
  simp_rw [charFun, prod_inner_apply, ← MeasurableEquiv.coe_toLp, ← integral_prod_mul,
    integral_map_equiv]
  simp [ofReal_add, add_mul, Complex.exp_add]

variable [CompleteSpace E] [CompleteSpace F] [SecondCountableTopology E] [SecondCountableTopology F]
    [BorelSpace E] [BorelSpace F]

/-- The characteristic function of a measure is a product of
characteristic functions if and only if it is a product measure.
This is the version for Hilbert spaces, see `charFunDual_eq_prod_iff`
for the Banach space version. -/
/-
**MeasureTheory.charFun_eq_prod_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：charFun_eq_prod_iff {μ : Measure E} {ν : Measure F} {ξ : Measure (E × F)} 
[IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ξ] : (forall t, charFun
 (ξ.map (toLp 2)) t = charFun μ (ofLp t).1 * charFun ν (ofLp t).2) ↔ ξ = μ.prod 
ν where mp h
参数：E × F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `MeasurableEquiv.map_measurableEquiv_injective`：map_measurableEquiv_injec
tive (e : α ≃ᵐ β) : Injective (Measure.map e)
· 使用定理 `MeasureTheory.Measure.ext_of_charFun`：∀ {E : Type u_3} [inst : Measurabl
eSpace E] {μ ν : MeasureTheory.Measure E} [inst_1 : NormedAddCommGroup E]   [ins
t_2 : InnerProductSpace ℝ …
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用定理 `MeasureTheory.Measure.prod.instIsFiniteMeasure`：∀ {α : Type u_4} {β : Ty
pe u_5} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (μ : MeasureTheory.Mea
sure α)   (ν : MeasureTheory.Measure…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasurableEquiv.coe_toLp`：coe_toLp : ⇑(MeasurableEquiv.toLp p X) = WithL
p.toLp p
· 使用引理 `MeasureTheory.charFun_prod`：charFun_prod {μ : Measure E} {ν : Measure F}
 [SFinite μ] [SFinite ν] (t : WithLp 2 (E × F)) : charFun ((μ.prod ν).map (toLp 
2)) t = charFun …
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.sigmaFinite_of_locallyFinite`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace α]   [Secon
dCountableTopology α] [MeasureTh…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toIsLocallyFiniteMeasure`：∀ {α : Type u_1}
 {m0 : MeasurableSpace α} [inst : TopologicalSpace α] (μ : MeasureTheory.Measure
 α)   [MeasureTheory.IsFiniteMeasure μ], Mea…

--- 原说明 ---
The characteristic function of a measure is a product of
characteristic functions if and only if it is a product measure.
This is the version for Hilbert spaces, see `charFunDual_eq_prod_iff`
for the Banach space version.
-/
lemma charFun_eq_prod_iff {μ : Measure E} {ν : Measure F} {ξ : Measure (E × F)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ξ] :
    (∀ t, charFun (ξ.map (toLp 2)) t = charFun μ (ofLp t).1 * charFun ν (ofLp t).2) ↔
    ξ = μ.prod ν where
  mp h := by
    refine (MeasurableEquiv.toLp 2 (E × F)).map_measurableEquiv_injective
      <| Measure.ext_of_charFun <| funext fun t ↦ ?_
    rw [MeasurableEquiv.coe_toLp, h, charFun_prod]
  mpr h := by rw [h]; exact charFun_prod

variable {ι : Type*} [Fintype ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)] {mE : ∀ i, MeasurableSpace (E i)}

/-- The characteristic function of a product of measures is a product of
characteristic functions. This is the version for Hilbert spaces, see `charFunDual_pi`
for the Banach space version. -/
/-
**MeasureTheory.charFun_pi** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：charFun_pi {μ : (i : ι) -> Measure (E i)} [forall i, SigmaFinite (μ i)] (t
 : PiLp 2 E) : charFun ((Measure.pi μ).map (toLp 2)) t = ∏ i, charFun (μ i) (t i
)
参数：i : ι；E i；μ i；t : PiLp 2 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.integral_map_equiv`：integral_map_equiv {β} [MeasurableSpac
e β] (e : α ≃ᵐ β) (f : β -> G) : ∫ y, f y ∂Measure.map e μ = ∫ x, f (e x) ∂μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Complex.ofReal_sum`：ofReal_sum (f : α -> Real) : ((∑ i in s, f i : Real)
 : Complex) = ∑ i in s, (f i : Complex)
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `Complex.exp_sum`：exp_sum {α : Type*} (s : Finset α) (f : α -> Complex) :
 exp (∑ x in s, f x) = ∏ x in s, exp (f x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The characteristic function of a product of measures is a product of
characteristic functions. This is the version for Hilbert spaces, see `charFunDu
al_pi`
for the Banach space version.
-/
lemma charFun_pi {μ : (i : ι) → Measure (E i)} [∀ i, SigmaFinite (μ i)] (t : PiLp 2 E) :
    charFun ((Measure.pi μ).map (toLp 2)) t = ∏ i, charFun (μ i) (t i) := by
  simp_rw [charFun, PiLp.inner_apply, ← MeasurableEquiv.coe_toLp, ← integral_fintype_prod_eq_prod,
    integral_map_equiv]
  simp [ofReal_sum, Finset.sum_mul, Complex.exp_sum]

variable [∀ i, CompleteSpace (E i)] [∀ i, SecondCountableTopology (E i)] [∀ i, BorelSpace (E i)]

/-- The characteristic function of a measure is a product of
characteristic functions if and only if it is a product measure.
This is the version for Hilbert spaces, see `charFunDual_eq_pi_iff`
for the Banach space version. -/
/-
**MeasureTheory.charFun_eq_pi_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：charFun_eq_pi_iff {μ : (i : ι) -> Measure (E i)} {ν : Measure (Π i, E i)} 
[forall i, IsFiniteMeasure (μ i)] [IsFiniteMeasure ν] : (forall t, charFun (ν.ma
p (toLp 2)) t = ∏ i, charFun (μ i) (t i)) ↔ ν = Measure.pi μ where mp h
参数：i : ι；E i；Π i, E i；μ i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `MeasurableEquiv.map_measurableEquiv_injective`：map_measurableEquiv_injec
tive (e : α ≃ᵐ β) : Injective (Measure.map e)
· 使用定理 `MeasureTheory.Measure.ext_of_charFun`：∀ {E : Type u_3} [inst : Measurabl
eSpace E] {μ ν : MeasureTheory.Measure E} [inst_1 : NormedAddCommGroup E]   [ins
t_2 : InnerProductSpace ℝ …
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用定理 `MeasureTheory.Measure.pi.instIsFiniteMeasure`：∀ {ι : Type u_1} {α : ι → 
Type u_3} [inst : Fintype ι] [inst_1 : (i : ι) → MeasurableSpace (α i)]   (μ : (
i : ι) → MeasureTheory.Measure (α …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasurableEquiv.coe_toLp`：coe_toLp : ⇑(MeasurableEquiv.toLp p X) = WithL
p.toLp p
· 使用引理 `MeasureTheory.charFun_pi`：charFun_pi {μ : (i : ι) -> Measure (E i)} [for
all i, SigmaFinite (μ i)] (t : PiLp 2 E) : charFun ((Measure.pi μ).map (toLp 2))
 t = ∏ i, char…
· 使用定理 `MeasureTheory.sigmaFinite_of_locallyFinite`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace α]   [Secon
dCountableTopology α] [MeasureTh…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toIsLocallyFiniteMeasure`：∀ {α : Type u_1}
 {m0 : MeasurableSpace α} [inst : TopologicalSpace α] (μ : MeasureTheory.Measure
 α)   [MeasureTheory.IsFiniteMeasure μ], Mea…

--- 原说明 ---
The characteristic function of a measure is a product of
characteristic functions if and only if it is a product measure.
This is the version for Hilbert spaces, see `charFunDual_eq_pi_iff`
for the Banach space version.
-/
lemma charFun_eq_pi_iff {μ : (i : ι) → Measure (E i)} {ν : Measure (Π i, E i)}
    [∀ i, IsFiniteMeasure (μ i)] [IsFiniteMeasure ν] :
    (∀ t, charFun (ν.map (toLp 2)) t = ∏ i, charFun (μ i) (t i)) ↔ ν = Measure.pi μ where
  mp h := by
    refine (MeasurableEquiv.toLp 2 (Π i, E i)).map_measurableEquiv_injective
      <| Measure.ext_of_charFun <| funext fun t ↦ ?_
    rw [MeasurableEquiv.coe_toLp, h, charFun_pi]
  mpr h := by rw [h]; exact charFun_pi

end InnerProductSpace

section NormedSpace

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {mE : MeasurableSpace E}
  [NormedAddCommGroup F] [NormedSpace ℝ F] {mF : MeasurableSpace F}
  {μ : Measure E} {ν : Measure F}

/-- The characteristic function of a measure in a normed space, function from `StrongDual ℝ E` to
`ℂ` with `charFunDual μ L = ∫ v, exp (L v * I) ∂μ`. -/
noncomputable
/-
**MeasureTheory.charFunDual** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：charFunDual (μ : Measure E) (L : StrongDual Real E) : Complex
参数：μ : Measure E；L : StrongDual Real E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def charFunDual (μ : Measure E) (L : StrongDual ℝ E) : ℂ := ∫ v, probCharDual L v ∂μ
/-
**MeasureTheory.charFunDual_apply** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：charFunDual_apply (L : StrongDual Real E) : charFunDual μ L = ∫ v, exp (L 
v * I) ∂μ
参数：L : StrongDual Real E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma charFunDual_apply (L : StrongDual ℝ E) : charFunDual μ L = ∫ v, exp (L v * I) ∂μ := rfl
/-
**MeasureTheory.charFunDual_eq_charFun_map_one** 是 Mathlib 中的一个引理，位于命名空间 `Measur
eTheory`。
形式化陈述：charFunDual_eq_charFun_map_one [OpensMeasurableSpace E] (L : StrongDual Re
al E) : charFunDual μ L = charFun (μ.map L) 1
参数：L : StrongDual Real E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.charFunDual_apply`：charFunDual_apply (L : StrongDual Real 
E) : charFunDual μ L = ∫ v, exp (L v * I) ∂μ
· 使用定理 `MeasureTheory.integral_map`：integral_map {β} [MeasurableSpace β] {φ : α 
-> β} (hφ : AEMeasurable φ μ) {f : β -> G} (hfm : AEStronglyMeasurable f (Measur
e.map φ μ)) : ∫ …
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `ContinuousLinearMap.measurable`：∀ {R : Type u_2} {E : Type u_3} {F : Typ
e u_4} [inst : Semiring R] [inst_1 : SeminormedAddCommGroup E]   [inst_2 : _root
_.Module R E] [inst_…
· 使用定理 `Measurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 :…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Measurable.cexp`：∀ {α : Type u_1} {m : MeasurableSpace α} {f : α → ℂ}, M
easurable f → Measurable fun x => Complex.exp (f x)
· 使用定理 `Measurable.mul_const`：Measurable.mul_const [MeasurableMul M] (hf : Measu
rable f) (c : M) : Measurable fun x => f x * c
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
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Measurable.complex_ofReal`：∀ {α : Type u_1} {m : MeasurableSpace α} {f :
 α → ℝ}, Measurable f → Measurable fun x => ↑(f x)
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用引理 `MeasureTheory.charFun_apply`：charFun_apply [Inner Real E] (t : E) : char
Fun μ t = ∫ x, exp (⟪x, t⟫ * I) ∂μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `conj_trivial`：∀ {R : Type u} [inst : CommSemiring R] [inst_1 : StarRing 
R] [TrivialStar R] (a : R), (starRingEnd R) a = a
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
（共 31 条，此处仅展示前 30 条）
-/
lemma charFunDual_eq_charFun_map_one [OpensMeasurableSpace E] (L : StrongDual ℝ E) :
    charFunDual μ L = charFun (μ.map L) 1 := by
  rw [charFunDual_apply]
  have : ∫ x, cexp (L x * I) ∂μ = ∫ x, cexp (x * I) ∂(μ.map L) := by
    rw [integral_map]
    · fun_prop
    · exact Measurable.aestronglyMeasurable <| by fun_prop
  rw [this, charFun_apply]
  simp
/-
**MeasureTheory.charFun_map_eq_charFunDual_smul** 是 Mathlib 中的一个引理，位于命名空间 `Measu
reTheory`。
形式化陈述：charFun_map_eq_charFunDual_smul [OpensMeasurableSpace E] (L : StrongDual R
eal E) (u : Real) : charFun (μ.map L) u = charFunDual μ (u • L)
参数：L : StrongDual Real E；u : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用引理 `MeasureTheory.charFunDual_apply`：charFunDual_apply (L : StrongDual Real 
E) : charFunDual μ L = ∫ v, exp (L v * I) ∂μ
· 使用定理 `MeasureTheory.integral_map`：integral_map {β} [MeasurableSpace β] {φ : α 
-> β} (hφ : AEMeasurable φ μ) {f : β -> G} (hfm : AEStronglyMeasurable f (Measur
e.map φ μ)) : ∫ …
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `ContinuousLinearMap.measurable`：∀ {R : Type u_2} {E : Type u_3} {F : Typ
e u_4} [inst : Semiring R] [inst_1 : SeminormedAddCommGroup E]   [inst_2 : _root
_.Module R E] [inst_…
· 使用定理 `Measurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 :…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Measurable.cexp`：∀ {α : Type u_1} {m : MeasurableSpace α} {f : α → ℂ}, M
easurable f → Measurable fun x => Complex.exp (f x)
· 使用定理 `Measurable.mul_const`：Measurable.mul_const [MeasurableMul M] (hf : Measu
rable f) (c : M) : Measurable fun x => f x * c
· 使用定理 `ContinuousMul.measurableMul`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Mul γ]   [SeparatelyCont
inuousMul γ], Mea…
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Measurable.const_mul`：Measurable.const_mul [MeasurableMul M] (hf : Measu
rable f) (c : M) : Measurable fun x => c * f x
· 使用定理 `Measurable.complex_ofReal`：∀ {α : Type u_1} {m : MeasurableSpace α} {f :
 α → ℝ}, Measurable f → Measurable fun x => ↑(f x)
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
（共 36 条，此处仅展示前 30 条）
-/
lemma charFun_map_eq_charFunDual_smul [OpensMeasurableSpace E] (L : StrongDual ℝ E) (u : ℝ) :
    charFun (μ.map L) u = charFunDual μ (u • L) := by
  rw [charFunDual_apply]
  have : ∫ x, cexp ((u • L) x * I) ∂μ = ∫ x, cexp (u * x * I) ∂(μ.map L) := by
    rw [integral_map]
    · simp
    · fun_prop
    · exact Measurable.aestronglyMeasurable <| by fun_prop
  rw [this, charFun_apply]
  simp
/-
**MeasureTheory.charFun_eq_charFunDual_toDualMap** 是 Mathlib 中的一个引理，位于命名空间 `Meas
ureTheory`。
形式化陈述：charFun_eq_charFunDual_toDualMap {E : Type*} [NormedAddCommGroup E] [Inner
ProductSpace Real E] {mE : MeasurableSpace E} {μ : Measure E} (t : E) : charFun 
μ t = charFunDual μ (InnerProductSpace.toDualMap Real E t)
参数：t : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `real_inner_comm`：real_inner_comm (x y : F) : ⟪y, x⟫_Real = ⟪x, y⟫_Real
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma charFun_eq_charFunDual_toDualMap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {mE : MeasurableSpace E} {μ : Measure E} (t : E) :
    charFun μ t = charFunDual μ (InnerProductSpace.toDualMap ℝ E t) := by
  simp [charFunDual_apply, charFun_apply, real_inner_comm]

@[simp]
/-
**MeasureTheory.charFun_toDual_symm_eq_charFunDual** 是 Mathlib 中的一个引理，位于命名空间 `Me
asureTheory`。
形式化陈述：charFun_toDual_symm_eq_charFunDual {E : Type*} [NormedAddCommGroup E] [Com
pleteSpace E] [InnerProductSpace Real E] {mE : MeasurableSpace E} {μ : Measure E
} (L : StrongDual Real E) : charFun μ ((InnerProductSpace.toDual Real E).symm L)
 = charFunDual μ L
参数：L : StrongDual Real E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.charFun_eq_charFunDual_toDualMap`：charFun_eq_charFunDual_t
oDualMap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E] {mE : Mea
surableSpace E} {μ : Measure E} (t :…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `InnerProductSpace.toDual_apply_eq_toDualMap_apply`：toDual_apply_eq_toDua
lMap_apply (x : E) : toDual 𝕜 E x = toDualMap 𝕜 E x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearIsometryEquiv.apply_symm_apply`：apply_symm_apply (x : E₂) : e (e.s
ymm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma charFun_toDual_symm_eq_charFunDual {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    [InnerProductSpace ℝ E] {mE : MeasurableSpace E} {μ : Measure E} (L : StrongDual ℝ E) :
    charFun μ ((InnerProductSpace.toDual ℝ E).symm L) = charFunDual μ L := by
  rw [charFun_eq_charFunDual_toDualMap, ← InnerProductSpace.toDual_apply_eq_toDualMap_apply]
  simp
/-
**MeasureTheory.charFunDual_map** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：charFunDual_map [OpensMeasurableSpace E] [BorelSpace F] (L : E ->L[Real] F
) (L' : StrongDual Real F) : charFunDual (μ.map L) L' = charFunDual μ (L'.comp L
)
参数：L : E ->L[Real] F；L' : StrongDual Real F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.charFunDual_eq_charFun_map_one`：charFunDual_eq_charFun_map
_one [OpensMeasurableSpace E] (L : StrongDual Real E) : charFunDual μ L = charFu
n (μ.map L) 1
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.Measure.map_map`：map_map {g : β -> γ} {f : α -> β} (hg : M
easurable g) (hf : Measurable f) : (μ.map f).map g = μ.map (g ∘ f)
· 使用定理 `ContinuousLinearMap.measurable`：∀ {R : Type u_2} {E : Type u_3} {F : Typ
e u_4} [inst : Semiring R] [inst_1 : SeminormedAddCommGroup E]   [inst_2 : _root
_.Module R E] [inst_…
· 使用定理 `ContinuousLinearMap.coe_comp`：coe_comp (h : M₂ ->SL[σ₂₃] M₃) (f : M₁ ->S
L[σ₁₂] M₂) : ⇑(h ∘SL f) = h ∘ f
-/
lemma charFunDual_map [OpensMeasurableSpace E] [BorelSpace F] (L : E →L[ℝ] F)
    (L' : StrongDual ℝ F) : charFunDual (μ.map L) L' = charFunDual μ (L'.comp L) := by
  rw [charFunDual_eq_charFun_map_one, charFunDual_eq_charFun_map_one,
    Measure.map_map (by fun_prop) (by fun_prop), ContinuousLinearMap.coe_comp]

@[simp]
/-
**MeasureTheory.charFunDual_dirac** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：charFunDual_dirac [OpensMeasurableSpace E] {x : E} (L : StrongDual Real E)
 : charFunDual (Measure.dirac x) L = cexp (L x * I)
参数：L : StrongDual Real E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.charFunDual_apply`：charFunDual_apply (L : StrongDual Real 
E) : charFunDual μ L = ∫ v, exp (L v * I) ∂μ
· 使用定理 `MeasureTheory.integral_dirac`：integral_dirac [MeasurableSpace α] [Measur
ableSingletonClass α] (f : α -> E) (a : α) : ∫ x, f x ∂Measure.dirac a = f a
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `OpensMeasurableSpace.toMeasurableSingletonClass`：∀ {α : Type u_1} [inst 
: TopologicalSpace α] [inst_1 : MeasurableSpace α] [OpensMeasurableSpace α] [T1S
pace α],   MeasurableSingletonClass α
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
-/
lemma charFunDual_dirac [OpensMeasurableSpace E] {x : E} (L : StrongDual ℝ E) :
    charFunDual (Measure.dirac x) L = cexp (L x * I) := by
  rw [charFunDual_apply, integral_dirac]
/-
**MeasureTheory.charFunDual_map_add_const** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：charFunDual_map_add_const [BorelSpace E] (r : E) (L : StrongDual Real E) :
 charFunDual (μ.map (· + r)) L = charFunDual μ L * cexp (L r * I)
参数：r : E；L : StrongDual Real E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.charFunDual_apply`：charFunDual_apply (L : StrongDual Real 
E) : charFunDual μ L = ∫ v, exp (L v * I) ∂μ
· 使用定理 `MeasureTheory.integral_map`：integral_map {β} [MeasurableSpace β] {φ : α 
-> β} (hφ : AEMeasurable φ μ) {f : β -> G} (hfm : AEStronglyMeasurable f (Measur
e.map φ μ)) : ∫ …
· 使用定理 `AEMeasurable.add_const`：∀ {M : Type u_2} {α : Type u_3} [inst : Measurab
leSpace M] [inst_1 : Add M] {m : MeasurableSpace α} {f : α → M}   {μ : MeasureTh
eory.Measure…
· 使用定理 `ContinuousAdd.measurableAdd`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Add γ]   [SeparatelyCont
inuousAdd γ], Mea…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `aemeasurable_id`：aemeasurable_id : AEMeasurable id μ
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用定理 `Continuous.cexp`：Continuous.cexp (h : Continuous f) : Continuous fun y =
> exp (f y)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `MeasureTheory.AEStronglyMeasurable.mul_const`：∀ {α : Type u_1} {β : Type
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
· 使用定理 `Continuous.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   {f
 : α → β} [inst_1 : T…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Continuous.clm_apply`：Continuous.clm_apply {f : X -> E ->L[𝕜] F} {g : X 
-> E} (hf : Continuous f) (hg : Continuous g) : Continuous (fun x => f x (g x))
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_mul_const`：integral_mul_const {L : Type*} [RCLike
 L] (r : L) (f : α -> L) : ∫ a, f a * r ∂μ = (∫ a, f a ∂μ) * r
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Complex.exp_add`：exp_add : exp (x + y) = exp x * exp y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 51 条，此处仅展示前 30 条）
-/
lemma charFunDual_map_add_const [BorelSpace E] (r : E) (L : StrongDual ℝ E) :
    charFunDual (μ.map (· + r)) L = charFunDual μ L * cexp (L r * I) := by
  rw [charFunDual_apply, charFunDual_apply, integral_map (by fun_prop) (by fun_prop),
    ← integral_mul_const]
  congr with a
  rw [← Complex.exp_add]
  congr
  simp only [map_add, ofReal_add]
  ring
/-
**MeasureTheory.charFunDual_map_const_add** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：charFunDual_map_const_add [BorelSpace E] (r : E) (L : StrongDual Real E) :
 charFunDual (μ.map (r + ·)) L = charFunDual μ L * cexp (L r * I)
参数：r : E；L : StrongDual Real E。
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
· 使用引理 `MeasureTheory.charFunDual_map_add_const`：charFunDual_map_add_const [Bore
lSpace E] (r : E) (L : StrongDual Real E) : charFunDual (μ.map (· + r)) L = char
FunDual μ L * cexp (L r * I)
-/
lemma charFunDual_map_const_add [BorelSpace E] (r : E) (L : StrongDual ℝ E) :
    charFunDual (μ.map (r + ·)) L = charFunDual μ L * cexp (L r * I) := by
  simp_rw [add_comm r]
  exact charFunDual_map_add_const _ _

/-- The characteristic function of a product of measures is a product of
characteristic functions. This is the version for Banach spaces, see `charFun_prod`
for the Hilbert space version. -/
/-
**MeasureTheory.charFunDual_prod** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：charFunDual_prod [SFinite μ] [SFinite ν] (L : StrongDual Real (E × F)) : c
harFunDual (μ.prod ν) L = charFunDual μ (L.comp (.inl Real E F)) * charFunDual ν
 (L.comp (.inr Real E F))
参数：L : StrongDual Real (E × F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ContinuousLinearMap.comp_inl_add_comp_inr`：comp_inl_add_comp_inr (L : M₁
 × M₂ ->L[R] M₃) (v : M₁ × M₂) : L.comp (.inl R M₁ M₂) v.1 + L.comp (.inr R M₁ M
₂) v.2 = L v
· 使用定理 `Complex.ofReal_add`：ofReal_add (r s : Real) : ((r + s : Real) : Complex)
 = r + s
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `Complex.exp_add`：exp_add : exp (x + y) = exp x * exp y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The characteristic function of a product of measures is a product of
characteristic functions. This is the version for Banach spaces, see `charFun_pr
od`
for the Hilbert space version.
-/
lemma charFunDual_prod [SFinite μ] [SFinite ν] (L : StrongDual ℝ (E × F)) :
    charFunDual (μ.prod ν) L
      = charFunDual μ (L.comp (.inl ℝ E F)) * charFunDual ν (L.comp (.inr ℝ E F)) := by
  simp_rw [charFunDual_apply, ← L.comp_inl_add_comp_inr, ofReal_add, add_mul,
    Complex.exp_add, ← integral_prod_mul]

/-- The characteristic function of a product of measures is a product of
characteristic functions. This is `charFunDual_prod` for `WithLp`.
See `charFun_prod` for the Hilbert space version. -/
/-
**MeasureTheory.charFunDual_prod'** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：charFunDual_prod' (p : Real>=0∞) [Fact (1 <= p)] [SFinite μ] [SFinite ν] (
L : StrongDual Real (WithLp p (E × F))) : charFunDual ((μ.prod ν).map (toLp p)) 
L = charFunDual μ (L.comp ((prodContinuousLinearEquiv p Real E F).symm.toContinu
ousLinearMap.comp (.inl Real E F))) * charFunDual ν (L.comp ((prodContinuousLine
arEquiv p Real E F).symm.toContinuousLinearMap.comp (.inr Real E F)))
参数：p : Real>=0∞；1 <= p；L : StrongDual Real (WithLp p (E × F))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ContinuousLinearMap.comp_apply`：comp_apply (g : M₂ ->SL[σ₂₃] M₃) (f : M₁
 ->SL[σ₁₂] M₂) (x : M₁) : (g ∘SL f) x = g (f x)
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用引理 `ContinuousLinearMap.comp_inl_add_comp_inr`：comp_inl_add_comp_inr (L : M₁
 × M₂ ->L[R] M₃) (v : M₁ × M₂) : L.comp (.inl R M₁ M₂) v.1 + L.comp (.inr R M₁ M
₂) v.2 = L v
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasurableEquiv.coe_toLp`：coe_toLp : ⇑(MeasurableEquiv.toLp p X) = WithL
p.toLp p
· 使用定理 `MeasureTheory.integral_map_equiv`：integral_map_equiv {β} [MeasurableSpac
e β] (e : α ≃ᵐ β) (f : β -> G) : ∫ y, f y ∂Measure.map e μ = ∫ x, f (e x) ∂μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The characteristic function of a product of measures is a product of
characteristic functions. This is `charFunDual_prod` for `WithLp`.
See `charFun_prod` for the Hilbert space version.
-/
lemma charFunDual_prod' (p : ℝ≥0∞) [Fact (1 ≤ p)] [SFinite μ] [SFinite ν]
    (L : StrongDual ℝ (WithLp p (E × F))) :
    charFunDual ((μ.prod ν).map (toLp p)) L =
      charFunDual μ (L.comp
        ((prodContinuousLinearEquiv p ℝ E F).symm.toContinuousLinearMap.comp
          (.inl ℝ E F))) *
      charFunDual ν (L.comp
        ((prodContinuousLinearEquiv p ℝ E F).symm.toContinuousLinearMap.comp
          (.inr ℝ E F))) := by
  simp_rw [charFunDual_apply, ← integral_prod_mul, ← Complex.exp_add, ← add_mul, ← ofReal_add,
    L.comp_apply, ← map_add, ContinuousLinearMap.comp_inl_add_comp_inr]
  rw [← MeasurableEquiv.coe_toLp, integral_map_equiv]
  simp

/-- The characteristic function of a product of measures is a product of
characteristic functions. This is the version for Banach spaces, see `charFunDual_pi`
for the Hilbert space version. -/
/-
**MeasureTheory.charFunDual_pi** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：charFunDual_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {E : ι -> Type*} [f
orall i, NormedAddCommGroup (E i)] [forall i, NormedSpace Real (E i)] {mE : fora
ll i, MeasurableSpace (E i)} {μ : (i : ι) -> Measure (E i)} [forall i, SigmaFini
te (μ i)] (L : StrongDual Real (Π i, E i)) : charFunDual (Measure.pi μ) L = ∏ i,
 charFunDual (μ i) (L.comp (.single Real E i))
参数：E i；E i；E i；i : ι；E i；μ i；L : StrongDual Real (Π i, E i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ContinuousLinearMap.sum_comp_single`：sum_comp_single [Fintype ι] [Decida
bleEq ι] (L : (Π i, φ i) ->L[R] M) (v : Π i, φ i) : ∑ i, L.comp (.single R φ i) 
(v i) = L v
· 使用定理 `Complex.ofReal_sum`：ofReal_sum (f : α -> Real) : ((∑ i in s, f i : Real)
 : Complex) = ∑ i in s, (f i : Complex)
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `Complex.exp_sum`：exp_sum {α : Type*} (s : Finset α) (f : α -> Complex) :
 exp (∑ x in s, f x) = ∏ x in s, exp (f x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The characteristic function of a product of measures is a product of
characteristic functions. This is the version for Banach spaces, see `charFunDua
l_pi`
for the Hilbert space version.
-/
lemma charFunDual_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] {mE : ∀ i, MeasurableSpace (E i)}
    {μ : (i : ι) → Measure (E i)} [∀ i, SigmaFinite (μ i)] (L : StrongDual ℝ (Π i, E i)) :
    charFunDual (Measure.pi μ) L =
      ∏ i, charFunDual (μ i) (L.comp (.single ℝ E i)) := by
  simp_rw [charFunDual_apply, ← L.sum_comp_single, ofReal_sum, Finset.sum_mul, Complex.exp_sum,
    ← integral_fintype_prod_eq_prod]

/-- The characteristic function of a product of measures is a product of
characteristic functions. This is `charFunDual_pi` for `PiLp`.
See `charFunDual_pi` for the Banach space version. -/
/-
**MeasureTheory.charFunDual_pi'** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：charFunDual_pi' (p : Real>=0∞) [Fact (1 <= p)] {ι : Type*} [Fintype ι] [De
cidableEq ι] {E : ι -> Type*} [forall i, NormedAddCommGroup (E i)] [forall i, No
rmedSpace Real (E i)] {mE : forall i, MeasurableSpace (E i)} {μ : (i : ι) -> Mea
sure (E i)} [forall i, SigmaFinite (μ i)] (L : StrongDual Real (PiLp p E)) : cha
rFunDual ((Measure.pi μ).map (toLp p)) L = ∏ i, charFunDual (μ i) (L.comp ((PiLp
.continuousLinearEquiv p Real E).symm.toContinuousLinearMap.comp (.single Real E
 i)))
参数：p : Real>=0∞；1 <= p；E i；E i；E i；i : ι；E i；μ i；L : StrongDual Real (PiLp p E)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `ContinuousLinearMap.comp_apply`：comp_apply (g : M₂ ->SL[σ₂₃] M₃) (f : M₁
 ->SL[σ₁₂] M₂) (x : M₁) : (g ∘SL f) x = g (f x)
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用引理 `ContinuousLinearMap.sum_comp_single`：sum_comp_single [Fintype ι] [Decida
bleEq ι] (L : (Π i, φ i) ->L[R] M) (v : Π i, φ i) : ∑ i, L.comp (.single R φ i) 
(v i) = L v
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasurableEquiv.coe_toLp`：coe_toLp : ⇑(MeasurableEquiv.toLp p X) = WithL
p.toLp p
· 使用定理 `MeasureTheory.integral_map_equiv`：integral_map_equiv {β} [MeasurableSpac
e β] (e : α ≃ᵐ β) (f : β -> G) : ∫ y, f y ∂Measure.map e μ = ∫ x, f (e x) ∂μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PiLp.continuousLinearEquiv_symm_apply`：∀ (p : ENNReal) (𝕜 : Type u_1) {ι
 : Type u_2} (β : ι → Type u_4) [inst : Semiring 𝕜]   [inst_1 : (i : ι) → AddCom
mGroup (β i)] [inst_2 : (i …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The characteristic function of a product of measures is a product of
characteristic functions. This is `charFunDual_pi` for `PiLp`.
See `charFunDual_pi` for the Banach space version.
-/
lemma charFunDual_pi' (p : ℝ≥0∞) [Fact (1 ≤ p)] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : ι) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    (L : StrongDual ℝ (PiLp p E)) :
    charFunDual ((Measure.pi μ).map (toLp p)) L =
      ∏ i, charFunDual (μ i) (L.comp
        ((PiLp.continuousLinearEquiv p ℝ E).symm.toContinuousLinearMap.comp (.single ℝ E i))) := by
  simp_rw [charFunDual_apply, ← integral_fintype_prod_eq_prod, ← Complex.exp_sum, ← Finset.sum_mul,
    ← ofReal_sum, L.comp_apply, ← map_sum, ContinuousLinearMap.sum_comp_single]
  rw [← MeasurableEquiv.coe_toLp, integral_map_equiv]
  simp

variable [BorelSpace E] [SecondCountableTopology E]

/-- If two finite measures have the same characteristic function, then they are equal. -/
/-
**MeasureTheory.Measure.ext_of_charFunDual** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Measure`。
形式化陈述：∀ {E : Type u_2} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] 
{mE : MeasurableSpace E} [BorelSpace E]   [SecondCountableTopology E] [CompleteS
pace E] {μ ν : MeasureTheory.Measure E} [MeasureTheory.IsFiniteMeasure μ]   [Mea
sureTheory.IsFiniteMeasure ν], MeasureTheory.charFunDual μ = MeasureTheory.charF
unDual ν → μ = ν
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.ext_of_integral_char_eq`：ext_of_integral_char_eq (he : Con
tinuous e) (he' : e != 1) (hL' : forall v != 0, L v != 0) (hL : Continuous fun p
 : V × W => L p.1 p.2) {P P…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Real.continuous_probChar`：continuous_probChar : Continuous probChar
· 使用定理 `Real.probChar_ne_one`：probChar_ne_one : probChar != 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `DFunLike.ne_iff`：ne_iff {f g : F} : f != g ↔ exists a, f a != g a
· 使用引理 `SeparatingDual.exists_ne_zero`：exists_ne_zero {x : V} (hx : x != 0) : ex
ists f : StrongDual R V, f x != 0
· 使用定理 `instSeparatingDualRealOfIsTopologicalAddGroupOfContinuousSMulOfLocallyCo
nvexSpaceOfT1Space`：∀ {E : Type u_1} [inst : TopologicalSpace E] [inst_1 : AddCo
mmGroup E] [IsTopologicalAddGroup E]   [inst_3 : _root_.Module ℝ E] [ContinuousS
…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsBoundedBilinearMap.continuous`：continuous (h : IsBoundedBilinearMap 𝕜 
f) : Continuous f
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用引理 `IsBoundedBilinearMap.symm`：symm (h : IsBoundedBilinearMap 𝕜 f) : IsBound
edBilinearMap 𝕜 (fun p => f (p.2, p.1)) where add_left x₁ x₂ y
· 使用定理 `isBoundedBilinearMap_apply`：isBoundedBilinearMap_apply : IsBoundedBiline
arMap 𝕜 fun p : (E ->L[𝕜] F) × E => p.1 p.2
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x

--- 原说明 ---
If two finite measures have the same characteristic function, then they are equa
l.
-/
theorem Measure.ext_of_charFunDual [CompleteSpace E]
    {μ ν : Measure E} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : charFunDual μ = charFunDual ν) :
    μ = ν := by
  refine ext_of_integral_char_eq continuous_probChar probChar_ne_one
    ?_ ?_ (fun L ↦ funext_iff.mp h L)
  · exact fun v hv ↦ DFunLike.ne_iff.mpr <| SeparatingDual.exists_ne_zero hv
  · exact isBoundedBilinearMap_apply.symm.continuous

/-- The characteristic function of a measure is a product of
characteristic functions if and only if it is a product measure.
This is the version for Banach spaces, see `charFun_eq_prod_iff`
for the Hilbert space version. -/
/-
**MeasureTheory.charFunDual_eq_prod_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory
`。
形式化陈述：charFunDual_eq_prod_iff [BorelSpace F] [SecondCountableTopology F] [Comple
teSpace E] [CompleteSpace F] {ξ : Measure (E × F)} [IsFiniteMeasure μ] [IsFinite
Measure ν] [IsFiniteMeasure ξ] : (forall L, charFunDual ξ L = charFunDual μ (L.c
omp (.inl Real E F)) * charFunDual ν (L.comp (.inr Real E F))) ↔ ξ = μ.prod ν wh
ere mp h
参数：E × F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext_of_charFunDual`：∀ {E : Type u_2} [inst : Norme
dAddCommGroup E] [inst_1 : NormedSpace ℝ E] {mE : MeasurableSpace E} [BorelSpace
 E]   [SecondCountableTopology…
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `TopologicalSpace.instSecondCountableTopologyProd`：∀ {α : Type u} [t : To
pologicalSpace α] {β : Type u_1} [inst : TopologicalSpace β] [SecondCountableTop
ology α]   [SecondCountableTopology β]…
· 使用定理 `MeasureTheory.Measure.prod.instIsFiniteMeasure`：∀ {α : Type u_4} {β : Ty
pe u_5} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (μ : MeasureTheory.Mea
sure α)   (ν : MeasureTheory.Measure…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.charFunDual_prod`：charFunDual_prod [SFinite μ] [SFinite ν]
 (L : StrongDual Real (E × F)) : charFunDual (μ.prod ν) L = charFunDual μ (L.com
p (.inl Real E F)) *…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.sigmaFinite_of_locallyFinite`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace α]   [Secon
dCountableTopology α] [MeasureTh…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toIsLocallyFiniteMeasure`：∀ {α : Type u_1}
 {m0 : MeasurableSpace α} [inst : TopologicalSpace α] (μ : MeasureTheory.Measure
 α)   [MeasureTheory.IsFiniteMeasure μ], Mea…

--- 原说明 ---
The characteristic function of a measure is a product of
characteristic functions if and only if it is a product measure.
This is the version for Banach spaces, see `charFun_eq_prod_iff`
for the Hilbert space version.
-/
lemma charFunDual_eq_prod_iff [BorelSpace F] [SecondCountableTopology F] [CompleteSpace E]
    [CompleteSpace F] {ξ : Measure (E × F)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteMeasure ξ] :
    (∀ L, charFunDual ξ L =
      charFunDual μ (L.comp (.inl ℝ E F)) * charFunDual ν (L.comp (.inr ℝ E F))) ↔
    ξ = μ.prod ν where
  mp h := by
    refine Measure.ext_of_charFunDual <| funext fun t ↦ ?_
    rw [h, charFunDual_prod]
  mpr h := by rw [h]; exact charFunDual_prod

/-- The characteristic function of a measure is a product of
characteristic functions if and only if it is a product measure.
This is `charFunDual_eq_prod_iff` for `WithLp`.
See `charFun_eq_prod_iff` for the Hilbert space version. -/
/-
**MeasureTheory.charFunDual_eq_prod_iff'** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheor
y`。
形式化陈述：charFunDual_eq_prod_iff' (p : Real>=0∞) [Fact (1 <= p)] [BorelSpace F] [Se
condCountableTopology F] [CompleteSpace E] [CompleteSpace F] {ξ : Measure (E × F
)} [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ξ] : (forall L, char
FunDual (ξ.map (toLp p)) L = charFunDual μ (L.comp ((WithLp.prodContinuousLinear
Equiv p Real E F).symm.toContinuousLinearMap.comp (.inl Real E F))) * charFunDua
l ν (L.comp ((WithLp.prodContinuousLinearEquiv p Real E F).symm.toContinuousLine
arMap.comp (.inr Real E F)
参数：p : Real>=0∞；1 <= p；E × F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableEquiv.map_measurableEquiv_injective`：map_measurableEquiv_injec
tive (e : α ≃ᵐ β) : Injective (Measure.map e)
· 使用定理 `MeasureTheory.Measure.ext_of_charFunDual`：∀ {E : Type u_2} [inst : Norme
dAddCommGroup E] [inst_1 : NormedSpace ℝ E] {mE : MeasurableSpace E} [BorelSpace
 E]   [SecondCountableTopology…
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用定理 `MeasureTheory.Measure.prod.instIsFiniteMeasure`：∀ {α : Type u_4} {β : Ty
pe u_5} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (μ : MeasureTheory.Mea
sure α)   (ν : MeasureTheory.Measure…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasurableEquiv.coe_toLp`：coe_toLp : ⇑(MeasurableEquiv.toLp p X) = WithL
p.toLp p
· 使用引理 `MeasureTheory.charFunDual_prod'`：charFunDual_prod' (p : Real>=0∞) [Fact 
(1 <= p)] [SFinite μ] [SFinite ν] (L : StrongDual Real (WithLp p (E × F))) : cha
rFunDual ((μ.prod ν).…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.sigmaFinite_of_locallyFinite`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace α]   [Secon
dCountableTopology α] [MeasureTh…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toIsLocallyFiniteMeasure`：∀ {α : Type u_1}
 {m0 : MeasurableSpace α} [inst : TopologicalSpace α] (μ : MeasureTheory.Measure
 α)   [MeasureTheory.IsFiniteMeasure μ], Mea…

--- 原说明 ---
The characteristic function of a measure is a product of
characteristic functions if and only if it is a product measure.
This is `charFunDual_eq_prod_iff` for `WithLp`.
See `charFun_eq_prod_iff` for the Hilbert space version.
-/
lemma charFunDual_eq_prod_iff' (p : ℝ≥0∞) [Fact (1 ≤ p)] [BorelSpace F]
    [SecondCountableTopology F] [CompleteSpace E] [CompleteSpace F] {ξ : Measure (E × F)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ξ] :
    (∀ L, charFunDual (ξ.map (toLp p)) L =
      charFunDual μ (L.comp
        ((WithLp.prodContinuousLinearEquiv p ℝ E F).symm.toContinuousLinearMap.comp
          (.inl ℝ E F))) *
      charFunDual ν (L.comp
        ((WithLp.prodContinuousLinearEquiv p ℝ E F).symm.toContinuousLinearMap.comp
          (.inr ℝ E F)))) ↔
    ξ = μ.prod ν where
  mp h := by
    refine (MeasurableEquiv.toLp p (E × F)).map_measurableEquiv_injective
      <| Measure.ext_of_charFunDual <| funext fun L ↦ ?_
    rw [MeasurableEquiv.coe_toLp, h, charFunDual_prod']
  mpr h := by rw [h]; exact charFunDual_prod' p

/-- The characteristic function of a measure is a product of
characteristic functions if and only if it is a product measure.
This is the version for Banach spaces, see `charFun_eq_pi_iff`
for the Hilbert space version. -/
/-
**MeasureTheory.charFunDual_eq_pi_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：charFunDual_eq_pi_iff {ι : Type*} [Fintype ι] [DecidableEq ι] {E : ι -> Ty
pe*} [forall i, NormedAddCommGroup (E i)] [forall i, NormedSpace Real (E i)] {mE
 : forall i, MeasurableSpace (E i)} [forall i, BorelSpace (E i)] [forall i, Seco
ndCountableTopology (E i)] [forall i, CompleteSpace (E i)] {μ : (i : ι) -> Measu
re (E i)} {ν : Measure (Π i, E i)} [forall i, IsFiniteMeasure (μ i)] [IsFiniteMe
asure ν] : (forall L, charFunDual ν L = ∏ i, charFunDual (μ i) (L.comp (.single 
Real E i))) ↔ ν = Measure.
参数：E i；E i；E i；E i；E i；E i；i : ι；E i；Π i, E i；μ i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext_of_charFunDual`：∀ {E : Type u_2} [inst : Norme
dAddCommGroup E] [inst_1 : NormedSpace ℝ E] {mE : MeasurableSpace E} [BorelSpace
 E]   [SecondCountableTopology…
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `TopologicalSpace.instSecondCountableTopologyForallOfCountable`：∀ {ι : Ty
pe u_1} {X : ι → Type u_2} [Countable ι] [inst : (a : ι) → TopologicalSpace (X a
)]   [∀ (a : ι), SecondCountableTopology (X a)], Se…
· 使用定理 `MeasureTheory.Measure.pi.instIsFiniteMeasure`：∀ {ι : Type u_1} {α : ι → 
Type u_3} [inst : Fintype ι] [inst_1 : (i : ι) → MeasurableSpace (α i)]   (μ : (
i : ι) → MeasureTheory.Measure (α …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.charFunDual_pi`：charFunDual_pi {ι : Type*} [Fintype ι] [De
cidableEq ι] {E : ι -> Type*} [forall i, NormedAddCommGroup (E i)] [forall i, No
rmedSpace Real (E …
· 使用定理 `MeasureTheory.sigmaFinite_of_locallyFinite`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace α]   [Secon
dCountableTopology α] [MeasureTh…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toIsLocallyFiniteMeasure`：∀ {α : Type u_1}
 {m0 : MeasurableSpace α} [inst : TopologicalSpace α] (μ : MeasureTheory.Measure
 α)   [MeasureTheory.IsFiniteMeasure μ], Mea…

--- 原说明 ---
The characteristic function of a measure is a product of
characteristic functions if and only if it is a product measure.
This is the version for Banach spaces, see `charFun_eq_pi_iff`
for the Hilbert space version.
-/
lemma charFunDual_eq_pi_iff {ι : Type*} [Fintype ι] [DecidableEq ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] {mE : ∀ i, MeasurableSpace (E i)}
    [∀ i, BorelSpace (E i)] [∀ i, SecondCountableTopology (E i)] [∀ i, CompleteSpace (E i)]
    {μ : (i : ι) → Measure (E i)} {ν : Measure (Π i, E i)} [∀ i, IsFiniteMeasure (μ i)]
    [IsFiniteMeasure ν] :
    (∀ L, charFunDual ν L = ∏ i, charFunDual (μ i) (L.comp (.single ℝ E i))) ↔
    ν = Measure.pi μ where
  mp h := by
    refine Measure.ext_of_charFunDual <| funext fun t ↦ ?_
    rw [h, charFunDual_pi]
  mpr h := by rw [h]; exact charFunDual_pi

/-- The characteristic function of a measure is a product of
characteristic functions if and only if it is a product measure.
This is `charFunDual_eq_pi_iff` for `PiLp`.
See `charFun_eq_pi_iff` for the Hilbert space version. -/
/-
**MeasureTheory.charFunDual_eq_pi_iff'** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`
。
形式化陈述：charFunDual_eq_pi_iff' (p : Real>=0∞) [Fact (1 <= p)] {ι : Type*} [Fintype
 ι] [DecidableEq ι] {E : ι -> Type*} [forall i, NormedAddCommGroup (E i)] [foral
l i, NormedSpace Real (E i)] {mE : forall i, MeasurableSpace (E i)} [forall i, B
orelSpace (E i)] [forall i, SecondCountableTopology (E i)] [forall i, CompleteSp
ace (E i)] {μ : (i : ι) -> Measure (E i)} {ν : Measure (Π i, E i)} [forall i, Is
FiniteMeasure (μ i)] [IsFiniteMeasure ν] : (forall L, charFunDual (ν.map (toLp p
)) L = ∏ i, charFunDual (μ
参数：p : Real>=0∞；1 <= p；E i；E i；E i；E i；E i；E i；i : ι；E i；Π i, E i；μ i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableEquiv.map_measurableEquiv_injective`：map_measurableEquiv_injec
tive (e : α ≃ᵐ β) : Injective (Measure.map e)
· 使用定理 `MeasureTheory.Measure.ext_of_charFunDual`：∀ {E : Type u_2} [inst : Norme
dAddCommGroup E] [inst_1 : NormedSpace ℝ E] {mE : MeasurableSpace E} [BorelSpace
 E]   [SecondCountableTopology…
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用定理 `MeasureTheory.Measure.pi.instIsFiniteMeasure`：∀ {ι : Type u_1} {α : ι → 
Type u_3} [inst : Fintype ι] [inst_1 : (i : ι) → MeasurableSpace (α i)]   (μ : (
i : ι) → MeasureTheory.Measure (α …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasurableEquiv.coe_toLp`：coe_toLp : ⇑(MeasurableEquiv.toLp p X) = WithL
p.toLp p
· 使用引理 `MeasureTheory.charFunDual_pi'`：charFunDual_pi' (p : Real>=0∞) [Fact (1 <
= p)] {ι : Type*} [Fintype ι] [DecidableEq ι] {E : ι -> Type*} [forall i, Normed
AddCommGroup (E i)]…
· 使用定理 `MeasureTheory.sigmaFinite_of_locallyFinite`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace α]   [Secon
dCountableTopology α] [MeasureTh…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toIsLocallyFiniteMeasure`：∀ {α : Type u_1}
 {m0 : MeasurableSpace α} [inst : TopologicalSpace α] (μ : MeasureTheory.Measure
 α)   [MeasureTheory.IsFiniteMeasure μ], Mea…

--- 原说明 ---
The characteristic function of a measure is a product of
characteristic functions if and only if it is a product measure.
This is `charFunDual_eq_pi_iff` for `PiLp`.
See `charFun_eq_pi_iff` for the Hilbert space version.
-/
lemma charFunDual_eq_pi_iff' (p : ℝ≥0∞) [Fact (1 ≤ p)] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    {mE : ∀ i, MeasurableSpace (E i)} [∀ i, BorelSpace (E i)] [∀ i, SecondCountableTopology (E i)]
    [∀ i, CompleteSpace (E i)] {μ : (i : ι) → Measure (E i)} {ν : Measure (Π i, E i)}
    [∀ i, IsFiniteMeasure (μ i)] [IsFiniteMeasure ν] :
    (∀ L, charFunDual (ν.map (toLp p)) L =
      ∏ i, charFunDual (μ i) (L.comp
        ((PiLp.continuousLinearEquiv p ℝ E).symm.toContinuousLinearMap.comp (.single ℝ E i)))) ↔
    ν = Measure.pi μ where
  mp h := by
    refine (MeasurableEquiv.toLp p (Π i, E i)).map_measurableEquiv_injective
      <| Measure.ext_of_charFunDual <| funext fun L ↦ ?_
    rw [MeasurableEquiv.coe_toLp, h, charFunDual_pi']
  mpr h := by rw [h]; exact charFunDual_pi' p

/-- The characteristic function of a convolution of measures
is the product of the respective characteristic functions. -/
/-
**MeasureTheory.charFunDual_conv** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：charFunDual_conv {μ ν : Measure E} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
 (L : StrongDual Real E) : charFunDual (μ ∗ ν) L = charFunDual μ L * charFunDual
 ν L
参数：L : StrongDual Real E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_conv`：∀ {M : Type u_1} {F : Type u_2} [inst : Add
Monoid M] {mM : MeasurableSpace M} [MeasurableAdd₂ M]   [inst_2 : NormedAddCommG
roup F] {μ ν : Me…
· 使用定理 `ContinuousAdd.measurableMul₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Add γ] [Con…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.sigmaFinite_of_locallyFinite`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace α]   [Secon
dCountableTopology α] [MeasureTh…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toIsLocallyFiniteMeasure`：∀ {α : Type u_1}
 {m0 : MeasurableSpace α} [inst : TopologicalSpace α] (μ : MeasureTheory.Measure
 α)   [MeasureTheory.IsFiniteMeasure μ], Mea…
· 使用定理 `MeasureTheory.Integrable.mono`：∀ {α : Type u_1} {β : Type u_2} {γ : Type
 u_3} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : NormedAddC
ommGroup β] [inst_1…
· 使用定理 `MeasureTheory.integrable_const`：integrable_const [IsFiniteMeasure μ] (c 
: β) : Integrable (fun _ : α => c) μ
· 使用定理 `MeasureTheory.Measure.finite_of_finite_conv`：∀ {M : Type u_1} [inst : Ad
dMonoid M] [inst_1 : MeasurableSpace M] (μ ν : MeasureTheory.Measure M)   [Measu
reTheory.IsFiniteMeasure μ] [Meas…
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用定理 `Continuous.cexp`：Continuous.cexp (h : Continuous f) : Continuous fun y =
> exp (f y)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `MeasureTheory.AEStronglyMeasurable.mul_const`：∀ {α : Type u_1} {β : Type
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
· 使用定理 `Continuous.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   {f
 : α → β} [inst_1 : T…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Continuous.clm_apply`：Continuous.clm_apply {f : X -> E ->L[𝕜] F} {g : X 
-> E} (hf : Continuous f) (hg : Continuous g) : Continuous (fun x => f x (g x))
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
（共 46 条，此处仅展示前 30 条）

--- 原说明 ---
The characteristic function of a convolution of measures
is the product of the respective characteristic functions.
-/
lemma charFunDual_conv {μ ν : Measure E} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (L : StrongDual ℝ E) : charFunDual (μ ∗ ν) L = charFunDual μ L * charFunDual ν L := by
  simp_rw [charFunDual_apply]
  rw [integral_conv]
  · simp [add_mul, Complex.exp_add, integral_const_mul, integral_mul_const]
  · exact (integrable_const (1 : ℝ)).mono (by fun_prop) (by simp)

end NormedSpace

end MeasureTheory

