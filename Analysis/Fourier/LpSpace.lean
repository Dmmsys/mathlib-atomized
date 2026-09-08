/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution
public import Mathlib.Analysis.Normed.Operator.Extend

/-!

# The Fourier transform on $L^p$

In this file we define the Fourier transform on $L^2$ as a linear isometry equivalence.

## Main definitions

* `MeasureTheory.Lp.fourierTransformₗᵢ`: The Fourier transform on $L^2$ as a linear isometry
  equivalence.

## Main statements

* `SchwartzMap.toLp_fourier_eq`: The Fourier transform on `𝓢(E, F)` agrees with the Fourier
  transform on $L^2$.
* `MeasureTheory.Lp.fourier_toTemperedDistribution_eq`: The Fourier transform on $L^2$ agrees with
  the Fourier transform on `𝓢'(E, F)`.

-/

@[expose] public section

noncomputable section

section FourierTransform

variable {E F : Type*}
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

open SchwartzMap MeasureTheory FourierTransform ComplexInnerProductSpace

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace MeasureTheory.Lp

variable (E F) in
/-- The Fourier transform on `L2` as a linear isometry equivalence. -/
@[wikidata Q6520159]
/-
**MeasureTheory.Lp.fourierTransform** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Lp`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Fourier transform on `L2` as a linear isometry equivalence.
-/
def fourierTransformₗᵢ : (Lp (α := E) F 2) ≃ₗᵢ[ℂ] (Lp (α := E) F 2) :=
  (fourierEquiv ℂ 𝓢(E, F)).extendOfIsometry
    (toLpCLM ℂ (E := E) F 2 volume) (toLpCLM ℂ (E := E) F 2 volume)
    -- Not explicitly stating the measure as being the volume causes time-outs in the proofs below
    (denseRange_toLpCLM ENNReal.ofNat_ne_top) (denseRange_toLpCLM ENNReal.ofNat_ne_top)
    norm_fourier_toL2_eq
/-
**MeasureTheory.Lp.instFourierTransform** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory
.Lp`。
形式化陈述：instFourierTransform : FourierTransform (Lp (α
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
-/
instance instFourierTransform : FourierTransform (Lp (α := E) F 2) (Lp (α := E) F 2) where
  fourier := fourierTransformₗᵢ E F
/-
**MeasureTheory.Lp.instFourierAdd** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：instFourierAdd : FourierAdd (Lp (α
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LinearIsometryEquiv.map_add`：map_add (x y : E) : e (x + y) = e x + e y
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
-/
instance instFourierAdd : FourierAdd (Lp (α := E) F 2) (Lp (α := E) F 2) where
  fourier_add := (fourierTransformₗᵢ E F).map_add
/-
**MeasureTheory.Lp.instFourierSMul** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：instFourierSMul : FourierSMul Complex (Lp (α
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LinearIsometryEquiv.map_smul`：map_smul [Module R E₂] {e : E ≃ₗᵢ[R] E₂} (
c : R) (x : E) : e (c • x) = c • e x
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
-/
instance instFourierSMul : FourierSMul ℂ (Lp (α := E) F 2) (Lp (α := E) F 2) where
  fourier_smul := (fourierTransformₗᵢ E F).map_smul
/-
**MeasureTheory.Lp.instContinuousFourier** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheor
y.Lp`。
形式化陈述：instContinuousFourier : ContinuousFourier (Lp (α
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `LinearIsometryEquiv.continuous`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Ty
pe u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+
* R₂} {σ₂₁ : R₂ →+* …
-/
instance instContinuousFourier : ContinuousFourier (Lp (α := E) F 2) (Lp (α := E) F 2) where
  continuous_fourier := (fourierTransformₗᵢ E F).continuous
/-
**MeasureTheory.Lp.instFourierTransformInv** 是 Mathlib 中的一个实例，位于命名空间 `MeasureThe
ory.Lp`。
形式化陈述：instFourierTransformInv : FourierTransformInv (Lp (α
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
-/
instance instFourierTransformInv : FourierTransformInv (Lp (α := E) F 2) (Lp (α := E) F 2) where
  fourierInv := (fourierTransformₗᵢ E F).symm
/-
**MeasureTheory.Lp.instFourierInvAdd** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Lp
`。
形式化陈述：instFourierInvAdd : FourierInvAdd (Lp (α
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LinearIsometryEquiv.map_add`：map_add (x y : E) : e (x + y) = e x + e y
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
-/
instance instFourierInvAdd : FourierInvAdd (Lp (α := E) F 2) (Lp (α := E) F 2) where
  fourierInv_add := (fourierTransformₗᵢ E F).symm.map_add
/-
**MeasureTheory.Lp.instFourierInvSMul** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.L
p`。
形式化陈述：instFourierInvSMul : FourierInvSMul Complex (Lp (α
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LinearIsometryEquiv.map_smul`：map_smul [Module R E₂] {e : E ≃ₗᵢ[R] E₂} (
c : R) (x : E) : e (c • x) = c • e x
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
-/
instance instFourierInvSMul : FourierInvSMul ℂ (Lp (α := E) F 2) (Lp (α := E) F 2) where
  fourierInv_smul := (fourierTransformₗᵢ E F).symm.map_smul
/-
**MeasureTheory.Lp.instContinuousFourierInv** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTh
eory.Lp`。
形式化陈述：instContinuousFourierInv : ContinuousFourierInv (Lp (α
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `LinearIsometryEquiv.continuous`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Ty
pe u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+
* R₂} {σ₂₁ : R₂ →+* …
-/
instance instContinuousFourierInv : ContinuousFourierInv (Lp (α := E) F 2) (Lp (α := E) F 2) where
  continuous_fourierInv := (fourierTransformₗᵢ E F).symm.continuous
/-
**MeasureTheory.Lp.instFourierPair** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：instFourierPair : FourierPair (Lp (α
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LinearIsometryEquiv.symm_apply_apply`：symm_apply_apply (x : E) : e.symm 
(e x) = x
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
-/
instance instFourierPair : FourierPair (Lp (α := E) F 2) (Lp (α := E) F 2) where
  fourierInv_fourier_eq := (Lp.fourierTransformₗᵢ E F).symm_apply_apply
/-
**MeasureTheory.Lp.instFourierPairInv** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.L
p`。
形式化陈述：instFourierPairInv : FourierInvPair (Lp (α
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LinearIsometryEquiv.apply_symm_apply`：apply_symm_apply (x : E₂) : e (e.s
ymm x) = x
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
-/
instance instFourierPairInv : FourierInvPair (Lp (α := E) F 2) (Lp (α := E) F 2) where
  fourier_fourierInv_eq := (Lp.fourierTransformₗᵢ E F).apply_symm_apply

/-- Plancherel's theorem for `L2` functions. -/
@[simp]
/-
**MeasureTheory.Lp.norm_fourier_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：norm_fourier_eq (f : Lp (α
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LinearIsometryEquiv.norm_map`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type
 u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* 
R₂} {σ₂₁ : R₂ →+* …
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)

--- 原说明 ---
Plancherel's theorem for `L2` functions.
-/
theorem norm_fourier_eq (f : Lp (α := E) F 2) : ‖𝓕 f‖ = ‖f‖ :=
  (Lp.fourierTransformₗᵢ E F).norm_map f

@[simp]
/-
**MeasureTheory.Lp.inner_fourier_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`
。
形式化陈述：inner_fourier_eq (f g : Lp (α
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LinearIsometryEquiv.inner_map_map`：LinearIsometryEquiv.inner_map_map (f 
: E ≃ₗᵢ[𝕜] E') (x y : E) : ⟪f x, f y⟫ = ⟪x, y⟫
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
-/
theorem inner_fourier_eq (f g : Lp (α := E) F 2) : ⟪𝓕 f, 𝓕 g⟫ = ⟪f, g⟫ :=
  (Lp.fourierTransformₗᵢ E F).inner_map_map f g

end MeasureTheory.Lp

@[simp]
/-
**SchwartzMap.toLp_fourier_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SchwartzMap.toLp_fourier_eq (f : 𝓢(E, F)) : 𝓕 (f.toLp 2) = (𝓕 f).toLp 2
参数：f : 𝓢(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.extendOfNorm_eq`：extendOfNorm_eq (h_dense : DenseRange e) (h_n
orm : exists C, forall x, ‖f x‖ <= C * ‖e x‖) (x : E) : f.extendOfNorm e (e x) =
 f x
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `SchwartzMap.denseRange_toLpCLM`：denseRange_toLpCLM [FiniteDimensional Re
al E] [BorelSpace E] {p : Real>=0∞} (hp : p != ⊤) [hp' : Fact (1 <= p)] {μ : Mea
sure E} [hμ : μ.HasT…
· 使用引理 `ENNReal.ofNat_ne_top`：ofNat_ne_top {n : Nat} [Nat.AtLeastTwo n] : ofNat(
n) != ∞
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G
 : Type u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : Measura
bleSpace G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `secondCountableTopologyEither_of_left`：∀ (α : Type u_6) (β : Type u_7) [
inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolog
y α],   SecondCountableTopo…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.instHasTemperateGrowth`：∀ {E : Ty
pe u_5} [inst : NormedAddCommGroup E] [inst_1 : MeasurableSpace E] [inst_2 : Nor
medSpace ℝ E]   [FiniteDimensional ℝ E] [BorelSpace…
· 使用定理 `SchwartzMap.norm_fourier_toL2_eq`：∀ {V : Type u_3} [inst : NormedAddComm
Group V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : FiniteDimensional ℝ V]   [in
st_3 : MeasurableSpace…
-/
theorem SchwartzMap.toLp_fourier_eq (f : 𝓢(E, F)) : 𝓕 (f.toLp 2) = (𝓕 f).toLp 2 := by
  apply LinearMap.extendOfNorm_eq
  · exact SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top
  use 1
  intro f
  rw [one_mul]
  exact (norm_fourier_toL2_eq f).le

@[simp]
/-
**SchwartzMap.toLp_fourierInv_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SchwartzMap.toLp_fourierInv_eq (f : 𝓢(E, F)) : 𝓕⁻ (f.toLp 2) = (𝓕⁻ f).toLp
 2
参数：f : 𝓢(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.extendOfNorm_eq`：extendOfNorm_eq (h_dense : DenseRange e) (h_n
orm : exists C, forall x, ‖f x‖ <= C * ‖e x‖) (x : E) : f.extendOfNorm e (e x) =
 f x
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `SchwartzMap.denseRange_toLpCLM`：denseRange_toLpCLM [FiniteDimensional Re
al E] [BorelSpace E] {p : Real>=0∞} (hp : p != ⊤) [hp' : Fact (1 <= p)] {μ : Mea
sure E} [hμ : μ.HasT…
· 使用引理 `ENNReal.ofNat_ne_top`：ofNat_ne_top {n : Nat} [Nat.AtLeastTwo n] : ofNat(
n) != ∞
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G
 : Type u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : Measura
bleSpace G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `secondCountableTopologyEither_of_left`：∀ (α : Type u_6) (β : Type u_7) [
inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolog
y α],   SecondCountableTopo…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.instHasTemperateGrowth`：∀ {E : Ty
pe u_5} [inst : NormedAddCommGroup E] [inst_1 : MeasurableSpace E] [inst_2 : Nor
medSpace ℝ E]   [FiniteDimensional ℝ E] [BorelSpace…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SchwartzMap.toLp.congr_simp`：∀ {E : Type u_5} {F : Type u_6} [inst : Nor
medAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   
[inst_3 : NormedS…
· 使用定理 `FourierInvPair.fourier_fourierInv_eq`：∀ {E : Type u_5} {F : Type u_6} {i
nst : FourierTransform F E} {inst_1 : FourierTransformInv E F}   [self : Fourier
InvPair E F] (f : E), Four…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `SchwartzMap.norm_fourier_toL2_eq`：∀ {V : Type u_3} [inst : NormedAddComm
Group V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : FiniteDimensional ℝ V]   [in
st_3 : MeasurableSpace…
-/
theorem SchwartzMap.toLp_fourierInv_eq (f : 𝓢(E, F)) : 𝓕⁻ (f.toLp 2) = (𝓕⁻ f).toLp 2 := by
  apply LinearMap.extendOfNorm_eq
  · exact SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top
  use 1
  intro f
  rw [one_mul]
  convert! (norm_fourier_toL2_eq (𝓕⁻ f)).symm.le
  simp

namespace MeasureTheory.Lp

/-- The `𝓢'`-Fourier transform and the `L2`-Fourier transform coincide on `L2`. -/
/-
**MeasureTheory.Lp.fourier_toTemperedDistribution_eq** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.Lp`。
形式化陈述：fourier_toTemperedDistribution_eq (f : Lp (α
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.instHasTemperateGrowth`：∀ {E : Ty
pe u_5} [inst : NormedAddCommGroup E] [inst_1 : MeasurableSpace E] [inst_2 : Nor
medSpace ℝ E]   [FiniteDimensional ℝ E] [BorelSpace…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `DenseRange.induction_on`：DenseRange.induction_on [TopologicalSpace β] {e
 : α -> β} (he : DenseRange e) {p : β -> Prop} (b₀ : β) (hp : IsClosed { b | p b
 }) (ih : for…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `secondCountableTopologyEither_of_left`：∀ (α : Type u_6) (β : Type u_7) [
inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolog
y α],   SecondCountableTopo…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `SchwartzMap.denseRange_toLpCLM`：denseRange_toLpCLM [FiniteDimensional Re
al E] [BorelSpace E] {p : Real>=0∞} (hp : p != ⊤) [hp' : Fact (1 <= p)] {μ : Mea
sure E} [hμ : μ.HasT…
· 使用引理 `ENNReal.ofNat_ne_top`：ofNat_ne_top {n : Nat} [Nat.AtLeastTwo n] : ofNat(
n) != ∞
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G
 : Type u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : Measura
bleSpace G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
· 使用定理 `PointwiseConvergenceCLM.instT2Space`：∀ {𝕜₁ : Type u_4} {𝕜₂ : Type u_5} [
inst : NormedField 𝕜₁] [inst_1 : NormedField 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂} {E : Type u_7} 
  {F : Type u_8} [inst_2 …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Lp.toTemperedDistribution_toLp_eq`：toTemperedDistribution_
toLp_eq [SecondCountableTopology E] {p : Real>=0∞} [hp : Fact (1 <= p)] (f : 𝓢(E
, F)) : ((f : Lp F p μ) : 𝓢'(E, F)) =…
· 使用定理 `TemperedDistribution.fourier_toTemperedDistributionCLM_eq`：fourier_toTem
peredDistributionCLM_eq (f : 𝓢(E, F)) : 𝓕 (f : 𝓢'(E, F)) = 𝓕 f
· 使用定理 `MeasureTheory.Lp.toTemperedDistribution.congr_simp`：∀ {E : Type u_3} {F 
: Type u_4} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : N
ormedAddCommGroup F]   [inst_3 : NormedS…
· 使用定理 `SchwartzMap.toLp_fourier_eq`：SchwartzMap.toLp_fourier_eq (f : 𝓢(E, F)) :
 𝓕 (f.toLp 2) = (𝓕 f).toLp 2
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
The `𝓢'`-Fourier transform and the `L2`-Fourier transform coincide on `L2`.
-/
theorem fourier_toTemperedDistribution_eq (f : Lp (α := E) F 2) :
    𝓕 (f : 𝓢'(E, F)) = (𝓕 f : Lp (α := E) F 2) := by
  set p := fun f : Lp (α := E) F 2 ↦ 𝓕 (f : 𝓢'(E, F)) = (𝓕 f : Lp (α := E) F 2)
  apply DenseRange.induction_on (p := p)
    (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top) f
  · apply isClosed_eq
    · exact (fourierCLM ℂ 𝓢'(E, F) ∘L toTemperedDistributionCLM F volume 2).continuous
    · exact (toTemperedDistributionCLM F volume 2 ∘L fourierCLM ℂ (Lp (α := E) F 2)).continuous
  intro f
  simp [p, TemperedDistribution.fourier_toTemperedDistributionCLM_eq]

/-- The `𝓢'`-inverse Fourier transform and the `L2`-inverse Fourier transform coincide on `L2`. -/
/-
**MeasureTheory.Lp.fourierInv_toTemperedDistribution_eq** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.Lp`。
形式化陈述：fourierInv_toTemperedDistribution_eq (f : Lp (α
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.instHasTemperateGrowth`：∀ {E : Ty
pe u_5} [inst : NormedAddCommGroup E] [inst_1 : MeasurableSpace E] [inst_2 : Nor
medSpace ℝ E]   [FiniteDimensional ℝ E] [BorelSpace…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FourierInvPair.fourier_fourierInv_eq`：∀ {E : Type u_5} {F : Type u_6} {i
nst : FourierTransform F E} {inst_1 : FourierTransformInv E F}   [self : Fourier
InvPair E F] (f : E), Four…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Lp.fourier_toTemperedDistribution_eq`：fourier_toTemperedDi
stribution_eq (f : Lp (α
· 使用定理 `FourierPair.fourierInv_fourier_eq`：∀ {E : Type u_5} {F : Type u_6} {inst
 : FourierTransform E F} {inst_1 : FourierTransformInv F E}   [self : FourierPai
r E F] (f : E), Fourier…

--- 原说明 ---
The `𝓢'`-inverse Fourier transform and the `L2`-inverse Fourier transform coinci
de on `L2`.
-/
theorem fourierInv_toTemperedDistribution_eq (f : Lp (α := E) F 2) :
    𝓕⁻ (f : 𝓢'(E, F)) = (𝓕⁻ f : Lp (α := E) F 2) := calc
  _ = 𝓕⁻ (Lp.toTemperedDistribution (𝓕 (𝓕⁻ f))) := by
    congr; exact (fourier_fourierInv_eq f).symm
  _ = 𝓕⁻ (𝓕 (Lp.toTemperedDistribution (𝓕⁻ f))) := by
    rw [fourier_toTemperedDistribution_eq]
  _ = _ := fourierInv_fourier_eq _

end MeasureTheory.Lp

end FourierTransform

