/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.LocallyConvex.ContinuousOfBounded
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
public import Mathlib.Probability.Moments.Variance

/-!
# Covariance in Banach spaces

We define the covariance of a finite measure in a Banach space `E`,
as a continuous bilinear form on `Dual ℝ E`.

## Main definitions

Let `μ` be a finite measure on a normed space `E` with the Borel σ-algebra. We then define

* `Dual.toLp`: the function `MemLp.toLp` as a continuous linear map from `Dual 𝕜 E` (for `RCLike 𝕜`)
  into the space `Lp 𝕜 p μ` for `p ≥ 1`. This needs a hypothesis `MemLp id p μ` (we set it to the
  junk value 0 if that's not the case).
* `covarianceBilinDual` : covariance of a measure `μ` with `∫ x, ‖x‖^2 ∂μ < ∞` on a Banach space,
  as a continuous bilinear form `Dual ℝ E →L[ℝ] Dual ℝ E →L[ℝ] ℝ`.
  If the second moment of `μ` is not finite, we set `covarianceBilinDual μ = 0`.

## Main statements

* `covarianceBilinDual_apply` : the covariance of `μ` on `L₁, L₂ : Dual ℝ E` is equal to
  `∫ x, (L₁ x - μ[L₁]) * (L₂ x - μ[L₂]) ∂μ`.
* `covarianceBilinDual_same_eq_variance`: `covarianceBilinDual μ L L = Var[L; μ]`.

## Implementation notes

The hypothesis that `μ` has a second moment is written as `MemLp id 2 μ` in the code.

-/

@[expose] public section


open MeasureTheory ProbabilityTheory Complex NormedSpace
open scoped ENNReal NNReal Real Topology

variable {E : Type*} [NormedAddCommGroup E] {mE : MeasurableSpace E} {μ : Measure E} {p : ℝ≥0∞}

namespace StrongDual

section LinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]

open scoped Classical in
/-- Linear map from the dual to `Lp` equal to `MemLp.toLp` if `MemLp id p μ` and to 0 otherwise. -/
noncomputable
/-
**StrongDual.toLp** 是 Mathlib 中的一个定义，位于命名空间 `StrongDual`。
形式化陈述：toLp (μ : Measure E) (p : Real>=0∞) [Fact (1 <= p)] : StrongDual 𝕜 E ->L[𝕜
] Lp 𝕜 p μ where toLinearMap
参数：μ : Measure E；p : Real>=0∞；1 <= p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def toLpₗ (μ : Measure E) (p : ℝ≥0∞) :
    StrongDual 𝕜 E →ₗ[𝕜] Lp 𝕜 p μ :=
  if h_Lp : MemLp id p μ then
  { toFun := fun L ↦ MemLp.toLp L (h_Lp.continuousLinearMap_comp L)
    map_add' u v := by push_cast; rw [MemLp.toLp_add]
    map_smul' c L := by push_cast; rw [MemLp.toLp_const_smul]; rfl }
  else 0

@[simp]
/-
**StrongDual.toLp** 是 Mathlib 中的一个定义，位于命名空间 `StrongDual`。
形式化陈述：toLp (μ : Measure E) (p : Real>=0∞) [Fact (1 <= p)] : StrongDual 𝕜 E ->L[𝕜
] Lp 𝕜 p μ where toLinearMap
参数：μ : Measure E；p : Real>=0∞；1 <= p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toLpₗ_apply (h_Lp : MemLp id p μ) (L : StrongDual 𝕜 E) :
    L.toLpₗ μ p = MemLp.toLp L (h_Lp.continuousLinearMap_comp L) := by
  simp [toLpₗ, dif_pos h_Lp]

@[simp]
/-
**StrongDual.toLp** 是 Mathlib 中的一个定义，位于命名空间 `StrongDual`。
形式化陈述：toLp (μ : Measure E) (p : Real>=0∞) [Fact (1 <= p)] : StrongDual 𝕜 E ->L[𝕜
] Lp 𝕜 p μ where toLinearMap
参数：μ : Measure E；p : Real>=0∞；1 <= p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toLpₗ_of_not_memLp (h_Lp : ¬ MemLp id p μ) (L : StrongDual 𝕜 E) :
    L.toLpₗ μ p = 0 := by
  simp [toLpₗ, dif_neg h_Lp]
/-
**StrongDual.norm_toLp** 是 Mathlib 中的一个引理，位于命名空间 `StrongDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma norm_toLpₗ_le [OpensMeasurableSpace E] (L : StrongDual 𝕜 E) :
    ‖L.toLpₗ μ p‖ ≤ ‖L‖ * (eLpNorm id p μ).toReal := by
  by_cases h_Lp : MemLp id p μ
  swap
  · simp only [h_Lp, not_false_eq_true, toLpₗ_of_not_memLp, Lp.norm_zero]
    positivity
  by_cases hp : p = 0
  · simp only [h_Lp, toLpₗ_apply, Lp.norm_toLp]
    simp [hp]
  by_cases hp_top : p = ∞
  · simp only [hp_top, StrongDual.toLpₗ_apply h_Lp, Lp.norm_toLp, eLpNorm_exponent_top] at h_Lp ⊢
    simp only [eLpNormEssSup, id_eq]
    suffices (essSup (fun x ↦ ‖L x‖ₑ) μ).toReal ≤ (essSup (fun x ↦ ‖L‖ₑ * ‖x‖ₑ) μ).toReal by
      rwa [ENNReal.essSup_const_mul, ENNReal.toReal_mul, toReal_enorm] at this
    gcongr
    · rw [ENNReal.essSup_const_mul]
      exact ENNReal.mul_ne_top (by simp) h_Lp.eLpNorm_ne_top
    · exact essSup_mono_ae <| ae_of_all _ L.le_opENorm
  have h0 : 0 < p.toReal := by simp [ENNReal.toReal_pos_iff, pos_iff_ne_zero, hp, Ne.lt_top hp_top]
  suffices ‖L.toLpₗ μ p‖
      ≤ (‖L‖ₑ ^ p.toReal * ∫⁻ x, ‖x‖ₑ ^ p.toReal ∂μ).toReal ^ p.toReal⁻¹ by
    refine this.trans_eq ?_
    simp only [ENNReal.toReal_mul]
    rw [← ENNReal.toReal_rpow, Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul (by positivity), mul_inv_cancel₀ h0.ne', Real.rpow_one, toReal_enorm]
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp [hp]) hp_top, ENNReal.toReal_rpow]
    simp
  rw [StrongDual.toLpₗ_apply h_Lp, Lp.norm_toLp,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp [hp]) hp_top]
  simp only [one_div]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  suffices ∫⁻ x, ‖L x‖ₑ ^ p.toReal ∂μ ≤ ‖L‖ₑ ^ p.toReal * ∫⁻ x, ‖x‖ₑ ^ p.toReal ∂μ by
    rw [← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
    gcongr
    rwa [ENNReal.ofReal_toReal]
    refine ENNReal.mul_ne_top (by simp) ?_
    have h := h_Lp.eLpNorm_ne_top
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp [hp]) hp_top] at h
    simpa [h0] using h
  calc ∫⁻ x, ‖L x‖ₑ ^ p.toReal ∂μ
  _ ≤ ∫⁻ x, ‖L‖ₑ ^ p.toReal * ‖x‖ₑ ^ p.toReal ∂μ := by
    refine lintegral_mono fun x ↦ ?_
    rw [← ENNReal.mul_rpow_of_nonneg]
    swap; · positivity
    gcongr
    exact L.le_opENorm x
  _ = ‖L‖ₑ ^ p.toReal * ∫⁻ x, ‖x‖ₑ ^ p.toReal ∂μ := by rw [lintegral_const_mul]; fun_prop

end LinearMap

section ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E] [OpensMeasurableSpace E]

/-- Continuous linear map from the dual to `Lp` equal to `MemLp.toLp` if `MemLp id p μ`
and to 0 otherwise. -/
noncomputable
/-
**StrongDual.toLp** 是 Mathlib 中的一个定义，位于命名空间 `StrongDual`。
形式化陈述：toLp (μ : Measure E) (p : Real>=0∞) [Fact (1 <= p)] : StrongDual 𝕜 E ->L[𝕜
] Lp 𝕜 p μ where toLinearMap
参数：μ : Measure E；p : Real>=0∞；1 <= p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def toLp (μ : Measure E) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    StrongDual 𝕜 E →L[𝕜] Lp 𝕜 p μ where
  toLinearMap := StrongDual.toLpₗ μ p
  cont := by
    refine LinearMap.continuous_of_locally_bounded _ fun s hs ↦ ?_
    rw [image_isVonNBounded_iff]
    simp_rw [isVonNBounded_iff'] at hs
    obtain ⟨r, hxr⟩ := hs
    refine ⟨r * (eLpNorm id p μ).toReal, fun L hLs ↦ ?_⟩
    specialize hxr L hLs
    refine (StrongDual.norm_toLpₗ_le L).trans ?_
    gcongr

@[simp]
/-
**StrongDual.toLp_apply** 是 Mathlib 中的一个引理，位于命名空间 `StrongDual`。
形式化陈述：toLp_apply [Fact (1 <= p)] (h_Lp : MemLp id p μ) (L : StrongDual 𝕜 E) : L.
toLp μ p = MemLp.toLp L (h_Lp.continuousLinearMap_comp L)
参数：1 <= p；h_Lp : MemLp id p μ；L : StrongDual 𝕜 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
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
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用引理 `MeasureTheory.MemLp.continuousLinearMap_comp`：MeasureTheory.MemLp.contin
uousLinearMap_comp [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 
F] {f : α -> E} (h_Lp : MemLp f p …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `StrongDual.toLpₗ_apply`：toLpₗ_apply (h_Lp : MemLp id p μ) (L : StrongDua
l 𝕜 E) : L.toLpₗ μ p = MemLp.toLp L (h_Lp.continuousLinearMap_comp L)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toLp_apply [Fact (1 ≤ p)] (h_Lp : MemLp id p μ) (L : StrongDual 𝕜 E) :
    L.toLp μ p = MemLp.toLp L (h_Lp.continuousLinearMap_comp L) := by
  simp [toLp, h_Lp]

@[simp]
/-
**StrongDual.toLp_of_not_memLp** 是 Mathlib 中的一个引理，位于命名空间 `StrongDual`。
形式化陈述：toLp_of_not_memLp [Fact (1 <= p)] (h_Lp : ¬ MemLp id p μ) (L : StrongDual 
𝕜 E) : L.toLp μ p = 0
参数：1 <= p；h_Lp : ¬ MemLp id p μ；L : StrongDual 𝕜 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
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
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `StrongDual.toLpₗ_of_not_memLp`：toLpₗ_of_not_memLp (h_Lp : ¬ MemLp id p μ
) (L : StrongDual 𝕜 E) : L.toLpₗ μ p = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toLp_of_not_memLp [Fact (1 ≤ p)] (h_Lp : ¬ MemLp id p μ) (L : StrongDual 𝕜 E) :
    L.toLp μ p = 0 := by
  simp [toLp, h_Lp]

end ContinuousLinearMap

end StrongDual

namespace ProbabilityTheory

section Centered

variable [NormedSpace ℝ E] [OpensMeasurableSpace E]

/-- Continuous bilinear form with value `∫ x, L₁ x * L₂ x ∂μ` on `(L₁, L₂)`.
This is equal to the covariance only if `μ` is centered. -/
noncomputable
/-
**ProbabilityTheory.uncenteredCovarianceBilinDual** 是 Mathlib 中的一个定义，位于命名空间 `Pro
babilityTheory`。
形式化陈述：uncenteredCovarianceBilinDual (μ : Measure E) : StrongDual Real E ->L[Real
] StrongDual Real E ->L[Real] Real
参数：μ : Measure E。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
-/
def uncenteredCovarianceBilinDual (μ : Measure E) : StrongDual ℝ E →L[ℝ] StrongDual ℝ E →L[ℝ] ℝ :=
  ContinuousLinearMap.bilinearComp (isBoundedBilinearMap_inner (𝕜 := ℝ)).toContinuousLinearMap
    (StrongDual.toLp μ 2) (StrongDual.toLp μ 2)
/-
**ProbabilityTheory.uncenteredCovarianceBilinDual_apply** 是 Mathlib 中的一个引理，位于命名空
间 `ProbabilityTheory`。
形式化陈述：uncenteredCovarianceBilinDual_apply (h : MemLp id 2 μ) (L₁ L₂ : StrongDual
 Real E) : uncenteredCovarianceBilinDual μ L₁ L₂ = ∫ x, L₁ x * L₂ x ∂μ
参数：h : MemLp id 2 μ；L₁ L₂ : StrongDual Real E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
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
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `conj_trivial`：∀ {R : Type u} [inst : CommSemiring R] [inst_1 : StarRing 
R] [TrivialStar R] (a : R), (starRingEnd R) a = a
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用引理 `MeasureTheory.MemLp.continuousLinearMap_comp`：MeasureTheory.MemLp.contin
uousLinearMap_comp [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 
F] {f : α -> E} (h_Lp : MemLp f p …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ContinuousLinearMap.bilinearComp.congr_simp`：∀ {𝕜 : Type u_1} {𝕜₂ : Type
 u_2} {𝕜₃ : Type u_3} {E : Type u_4} {F : Type u_6} {G : Type u_8}   [inst : Sem
inormedAddCommGroup E] [inst_1 : …
· 使用定理 `IsBoundedBilinearMap.toContinuousLinearMap.congr_simp`：∀ {𝕜 : Type u_1} 
[inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : SeminormedAddCommGro
up E]   [inst_2 : NormedSpace 𝕜 E] {F : Typ…
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `StrongDual.toLp_apply`：toLp_apply [Fact (1 <= p)] (h_Lp : MemLp id p μ) 
(L : StrongDual 𝕜 E) : L.toLp μ p = MemLp.toLp L (h_Lp.continuousLinearMap_comp 
L)
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
（共 33 条，此处仅展示前 30 条）
-/
lemma uncenteredCovarianceBilinDual_apply (h : MemLp id 2 μ) (L₁ L₂ : StrongDual ℝ E) :
    uncenteredCovarianceBilinDual μ L₁ L₂ = ∫ x, L₁ x * L₂ x ∂μ := by
  simp only [uncenteredCovarianceBilinDual, ContinuousLinearMap.bilinearComp_apply,
    StrongDual.toLp_apply h, L2.inner_def, RCLike.inner_apply, conj_trivial]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (h.continuousLinearMap_comp L₁),
    MemLp.coeFn_toLp (h.continuousLinearMap_comp L₂)] with x hxL₁ hxL₂
  simp only [id_eq] at hxL₁ hxL₂
  rw [hxL₁, hxL₂, mul_comm]
/-
**ProbabilityTheory.uncenteredCovarianceBilinDual_of_not_memLp** 是 Mathlib 中的一个引
理，位于命名空间 `ProbabilityTheory`。
形式化陈述：uncenteredCovarianceBilinDual_of_not_memLp (h : ¬ MemLp id 2 μ) (L₁ L₂ : S
trongDual Real E) : uncenteredCovarianceBilinDual μ L₁ L₂ = 0
参数：h : ¬ MemLp id 2 μ；L₁ L₂ : StrongDual Real E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
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
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `StrongDual.toLp_of_not_memLp`：toLp_of_not_memLp [Fact (1 <= p)] (h_Lp : 
¬ MemLp id p μ) (L : StrongDual 𝕜 E) : L.toLp μ p = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma uncenteredCovarianceBilinDual_of_not_memLp (h : ¬ MemLp id 2 μ) (L₁ L₂ : StrongDual ℝ E) :
    uncenteredCovarianceBilinDual μ L₁ L₂ = 0 := by
  simp [uncenteredCovarianceBilinDual, StrongDual.toLp_of_not_memLp h]

@[simp]
/-
**ProbabilityTheory.uncenteredCovarianceBilinDual_zero** 是 Mathlib 中的一个引理，位于命名空间
 `ProbabilityTheory`。
形式化陈述：uncenteredCovarianceBilinDual_zero : uncenteredCovarianceBilinDual (0 : Me
asure E) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
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
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Lp.ext_iff`：∀ {α : Type u_1} {E : Type u_4} {m : Measurabl
eSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGro
up E] {f g : ↥…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `ContinuousLinearMap.bilinearComp.congr_simp`：∀ {𝕜 : Type u_1} {𝕜₂ : Type
 u_2} {𝕜₃ : Type u_3} {E : Type u_4} {F : Type u_6} {G : Type u_8}   [inst : Sem
inormedAddCommGroup E] [inst_1 : …
· 使用定理 `Subsingleton.eq_zero`：∀ {α : Type u} [inst : Zero α] [Subsingleton α] (a
 : α), a = 0
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用引理 `ContinuousLinearMap.bilinearComp_zero_right`：bilinearComp_zero_right {f 
: E ->SL[σ₁₃] F ->SL[σ₂₃] G} {gE : E' ->SL[σ₁'] E} : bilinearComp f gE (0 : F' -
>SL[σ₂'] F) = 0
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
（共 32 条，此处仅展示前 30 条）
-/
lemma uncenteredCovarianceBilinDual_zero : uncenteredCovarianceBilinDual (0 : Measure E) = 0 := by
  ext
  have : Subsingleton (Lp ℝ 2 (0 : Measure E)) := ⟨fun x y ↦ Lp.ext_iff.2 rfl⟩
  simp [uncenteredCovarianceBilinDual, Subsingleton.eq_zero (StrongDual.toLp 0 2)]
/-
**ProbabilityTheory.norm_uncenteredCovarianceBilinDual_le** 是 Mathlib 中的一个引理，位于命
名空间 `ProbabilityTheory`。
形式化陈述：norm_uncenteredCovarianceBilinDual_le (L₁ L₂ : StrongDual Real E) : ‖uncen
teredCovarianceBilinDual μ L₁ L₂‖ <= ‖L₁‖ * ‖L₂‖ * ∫ x, ‖x‖ ^ 2 ∂μ
参数：L₁ L₂ : StrongDual Real E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
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
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.uncenteredCovarianceBilinDual_apply`：uncenteredCovaria
nceBilinDual_apply (h : MemLp id 2 μ) (L₁ L₂ : StrongDual Real E) : uncenteredCo
varianceBilinDual μ L₁ L₂ = ∫ x, L₁ x * L₂ …
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.norm_integral_le_integral_norm`：norm_integral_le_integral_
norm (f : α -> G) : ‖∫ a, f a ∂μ‖ <= ∫ a, ‖f a‖ ∂μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用引理 `MeasureTheory.integral_mono_ae`：integral_mono_ae {f g : α -> E} (hf : In
tegrable f μ) (hg : Integrable g μ) (h : f <=ᵐ[μ] g) : ∫ x, f x ∂μ <= ∫ x, g x ∂
μ
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
· 使用定理 `MeasureTheory.Integrable.norm`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f 
: α → β}, MeasureTh…
· 使用定理 `MeasureTheory.MemLp.integrable_mul`：∀ {α : Type u_1} {m : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} {𝕜 : Type u_8} [inst : NormedRing 𝕜]   {p q :
 ENNReal} {f g : α → 𝕜},…
· 使用引理 `MeasureTheory.MemLp.continuousLinearMap_comp`：MeasureTheory.MemLp.contin
uousLinearMap_comp [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 
F] {f : α -> E} (h_Lp : MemLp f p …
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `MeasureTheory.Integrable.const_mul`：∀ {α : Type u_1} {m : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} {𝕜 : Type u_8} [inst : NormedRing 𝕜] {f : α →
 𝕜},   MeasureTheory.Int…
（共 73 条，此处仅展示前 30 条）
-/
lemma norm_uncenteredCovarianceBilinDual_le (L₁ L₂ : StrongDual ℝ E) :
    ‖uncenteredCovarianceBilinDual μ L₁ L₂‖ ≤ ‖L₁‖ * ‖L₂‖ * ∫ x, ‖x‖ ^ 2 ∂μ := by
  by_cases h : MemLp id 2 μ
  swap; · simp only [uncenteredCovarianceBilinDual_of_not_memLp h, norm_zero]; positivity
  calc ‖uncenteredCovarianceBilinDual μ L₁ L₂‖
  _ = ‖∫ x, L₁ x * L₂ x ∂μ‖ := by rw [uncenteredCovarianceBilinDual_apply h]
  _ ≤ ∫ x, ‖L₁ x‖ * ‖L₂ x‖ ∂μ := (norm_integral_le_integral_norm _).trans (by simp)
  _ ≤ ∫ x, ‖L₁‖ * ‖x‖ * ‖L₂‖ * ‖x‖ ∂μ := by
    refine integral_mono_ae ?_ ?_ (ae_of_all _ fun x ↦ ?_)
    · simp_rw [← norm_mul]
      exact (MemLp.integrable_mul (h.continuousLinearMap_comp L₁)
        (h.continuousLinearMap_comp L₂)).norm
    · simp_rw [mul_assoc]
      refine Integrable.const_mul ?_ _
      simp_rw [← mul_assoc, mul_comm _ (‖L₂‖), mul_assoc, ← pow_two]
      refine Integrable.const_mul ?_ _
      exact h.integrable_norm_pow (by simp)
    · simp only
      rw [mul_assoc]
      gcongr
      · exact ContinuousLinearMap.le_opNorm L₁ x
      · exact ContinuousLinearMap.le_opNorm L₂ x
  _ = ‖L₁‖ * ‖L₂‖ * ∫ x, ‖x‖ ^ 2 ∂μ := by
    rw [← integral_const_mul]
    congr with x
    ring

end Centered

section Covariance

variable [NormedSpace ℝ E] [BorelSpace E]

/-- Continuous bilinear form with value `∫ x, (L₁ x - μ[L₁]) * (L₂ x - μ[L₂]) ∂μ` on `(L₁, L₂)`
if `MemLp id 2 μ`. If not, we set it to zero. -/
noncomputable
/-
**ProbabilityTheory.covarianceBilinDual** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTh
eory`。
形式化陈述：covarianceBilinDual (μ : Measure E) : StrongDual Real E ->L[Real] StrongDu
al Real E ->L[Real] Real
参数：μ : Measure E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def covarianceBilinDual (μ : Measure E) : StrongDual ℝ E →L[ℝ] StrongDual ℝ E →L[ℝ] ℝ :=
  uncenteredCovarianceBilinDual (μ.map (fun x ↦ x - ∫ x, x ∂μ))

omit [BorelSpace E] in
/-
**ProbabilityTheory._root_.MeasureTheory.memLp_id_of_self_sub_integral** 是 Mathl
ib 中的一个引理，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MeasureTheory.memLp_id_of_self_sub_integral {p : ℝ≥0∞}
    (h_Lp : MemLp (fun x ↦ x - ∫ y, y ∂μ) p μ) : MemLp id p μ := by
  have : (id : E → E) = fun x ↦ x - ∫ x, x ∂μ + ∫ x, x ∂μ := by ext; simp
  rw [this]
  apply h_Lp.add
  set c := ∫ x, x ∂μ
  /- We need to check that the constant `c = ∫ x, x ∂μ` is in `L^p`. Note that we don't assume
  that `μ` is finite, so this requires an argument. If the constant is zero, it's obvious.
  If it's nonzero, this means that `x` is integrable for `μ` (as otherwise the integral would be
  `0` by our choice of junk value), so `‖x‖ ^ (1/p)` is in `L^p`.
  The constant `c` is controlled by `2 ‖x - c‖` close to `0` (say when `‖x‖ ≤ ‖c‖ / 2`)
  and by a multiple of `‖x‖ ^ (1/p)` away from `0`. Those two functions
  are in `L^p` by assumptions, so the constant `c` also is. -/
  by_cases hx : c = 0
  · simp [hx]
  rcases eq_or_ne p 0 with rfl | hp0
  · simp [aestronglyMeasurable_const]
  rcases eq_or_ne p ∞ with rfl | hptop
  · exact memLp_top_const c
  apply (integrable_norm_rpow_iff (by fun_prop) hp0 hptop).1
  have I : Integrable (fun (x : E) ↦ ‖x‖) μ := by
    apply Integrable.norm
    contrapose hx
    exact integral_undef hx
  have := (h_Lp.integrable_norm_rpow hp0 hptop).const_mul (2 ^ p.toReal)
  apply (((I.const_mul (2 * ‖c‖ ^ (p.toReal - 1))).add this)).mono' (by fun_prop)
  filter_upwards [] with y
  lift p to ℝ≥0 using hptop
  simp only [ENNReal.coe_toReal, Real.norm_eq_abs, Pi.add_apply]
  rw [abs_of_nonneg (by positivity)]
  rcases le_total ‖y‖ (‖c‖ / 2)
  · have : ‖c‖ ≤ ‖y‖ + ‖y - c‖ := Eq.trans_le (by abel_nf) (norm_sub_le y (y - c))
    calc ‖c‖ ^ (p : ℝ)
    _ ≤ (2 * ‖y - c‖) ^ (p : ℝ) := by
      gcongr
      linarith
    _ = 0 + 2 ^ (p : ℝ) * ‖y - c‖ ^ (p : ℝ) := by
      rw [Real.mul_rpow (by simp) (by positivity)]
      ring
    _ ≤ 2 * ‖c‖ ^ (p - 1 : ℝ) * ‖y‖ + 2 ^ (p : ℝ) * ‖y - c‖ ^ (p : ℝ) := by
      gcongr
      positivity
  · calc ‖c‖ ^ (p : ℝ)
    _ = ‖c‖ ^ ((p - 1) + 1 : ℝ) := by abel_nf
    _ = ‖c‖ ^ (p - 1 : ℝ) * ‖c‖ := by rw [Real.rpow_add (by positivity), Real.rpow_one]
    _ ≤ ‖c‖ ^ (p - 1 : ℝ) * (2 * ‖y‖) := by gcongr; linarith
    _ = 2 * ‖c‖ ^ (p - 1 : ℝ) * ‖y‖ + 0 := by ring
    _ ≤ 2 * ‖c‖ ^ (p - 1 : ℝ) * ‖y‖ + 2 ^ (p : ℝ) * ‖y - c‖ ^ (p : ℝ) := by gcongr; positivity
/-
**ProbabilityTheory.covarianceBilinDual_of_not_memLp'** 是 Mathlib 中的一个引理，位于命名空间 
`ProbabilityTheory`。
形式化陈述：covarianceBilinDual_of_not_memLp' (h : ¬ MemLp (fun x => x - ∫ y, y ∂μ) 2 
μ) (L₁ L₂ : StrongDual Real E) : covarianceBilinDual μ L₁ L₂ = 0
参数：h : ¬ MemLp (fun x => x - ∫ y, y ∂μ) 2 μ；L₁ L₂ : StrongDual Real E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
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
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.covarianceBilinDual.eq_1`：∀ {E : Type u_1} [inst : Nor
medAddCommGroup E] {mE : MeasurableSpace E} [inst_1 : NormedSpace ℝ E]   [inst_2
 : BorelSpace E] (μ : MeasureThe…
· 使用引理 `ProbabilityTheory.uncenteredCovarianceBilinDual_of_not_memLp`：uncentered
CovarianceBilinDual_of_not_memLp (h : ¬ MemLp id 2 μ) (L₁ L₂ : StrongDual Real E
) : uncenteredCovarianceBilinDual μ L₁ L₂ = 0
· 使用定理 `MeasurableEmbedding.memLp_map_measure_iff`：∀ {α : Type u_1} {m0 : Measur
ableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α} {ε : Type u_7}   [inst 
: TopologicalSpace ε] [inst_1 :…
· 使用定理 `measurableEmbedding_subRight`：∀ {G : Type u_1} [inst : AddGroup G] [inst
_1 : MeasurableSpace G] [MeasurableAdd G] (g : G),   MeasurableEmbedding fun x =
> x - g
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
-/
lemma covarianceBilinDual_of_not_memLp' (h : ¬ MemLp (fun x ↦ x - ∫ y, y ∂μ) 2 μ)
    (L₁ L₂ : StrongDual ℝ E) :
    covarianceBilinDual μ L₁ L₂ = 0 := by
  rw [covarianceBilinDual, uncenteredCovarianceBilinDual_of_not_memLp]
  rw [(measurableEmbedding_subRight _).memLp_map_measure_iff]
  exact h

@[simp]
/-
**ProbabilityTheory.covarianceBilinDual_of_not_memLp** 是 Mathlib 中的一个引理，位于命名空间 `
ProbabilityTheory`。
形式化陈述：covarianceBilinDual_of_not_memLp (h : ¬ MemLp id 2 μ) (L₁ L₂ : StrongDual 
Real E) : covarianceBilinDual μ L₁ L₂ = 0
参数：h : ¬ MemLp id 2 μ；L₁ L₂ : StrongDual Real E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `ProbabilityTheory.covarianceBilinDual_of_not_memLp'`：covarianceBilinDual
_of_not_memLp' (h : ¬ MemLp (fun x => x - ∫ y, y ∂μ) 2 μ) (L₁ L₂ : StrongDual Re
al E) : covarianceBilinDual μ L₁ L₂ = 0
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `MeasureTheory.memLp_id_of_self_sub_integral`：∀ {E : Type u_1} [inst : No
rmedAddCommGroup E] {mE : MeasurableSpace E} {μ : MeasureTheory.Measure E}   [in
st_1 : NormedSpace ℝ E] {p : ENNR…
-/
lemma covarianceBilinDual_of_not_memLp (h : ¬ MemLp id 2 μ) (L₁ L₂ : StrongDual ℝ E) :
    covarianceBilinDual μ L₁ L₂ = 0 := by
  apply covarianceBilinDual_of_not_memLp'
  contrapose h
  exact memLp_id_of_self_sub_integral h

@[simp]
/-
**ProbabilityTheory.covarianceBilinDual_zero** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory`。
形式化陈述：covarianceBilinDual_zero : covarianceBilinDual (0 : Measure E) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
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
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.covarianceBilinDual.eq_1`：∀ {E : Type u_1} [inst : Nor
medAddCommGroup E] {mE : MeasurableSpace E} [inst_1 : NormedSpace ℝ E]   [inst_2
 : BorelSpace E] (μ : MeasureThe…
· 使用定理 `MeasureTheory.Measure.map_zero`：∀ {α : Type u_1} {β : Type u_2} {mα : Me
asurableSpace α} {mβ : MeasurableSpace β} (f : α → β),   MeasureTheory.Measure.m
ap f 0 = 0
· 使用引理 `ProbabilityTheory.uncenteredCovarianceBilinDual_zero`：uncenteredCovarian
ceBilinDual_zero : uncenteredCovarianceBilinDual (0 : Measure E) = 0
-/
lemma covarianceBilinDual_zero : covarianceBilinDual (0 : Measure E) = 0 := by
  rw [covarianceBilinDual, Measure.map_zero, uncenteredCovarianceBilinDual_zero]
/-
**ProbabilityTheory.covarianceBilinDual_comm** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory`。
形式化陈述：covarianceBilinDual_comm (L₁ L₂ : StrongDual Real E) : covarianceBilinDual
 μ L₁ L₂ = covarianceBilinDual μ L₂ L₁
参数：L₁ L₂ : StrongDual Real E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
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
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasurableEmbedding.memLp_map_measure_iff`：∀ {α : Type u_1} {m0 : Measur
ableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α} {ε : Type u_7}   [inst 
: TopologicalSpace ε] [inst_1 :…
· 使用定理 `measurableEmbedding_subRight`：∀ {G : Type u_1} [inst : AddGroup G] [inst
_1 : MeasurableSpace G] [MeasurableAdd G] (g : G),   MeasurableEmbedding fun x =
> x - g
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.uncenteredCovarianceBilinDual_apply`：uncenteredCovaria
nceBilinDual_apply (h : MemLp id 2 μ) (L₁ L₂ : StrongDual Real E) : uncenteredCo
varianceBilinDual μ L₁ L₂ = ∫ x, L₁ x * L₂ …
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ProbabilityTheory.covarianceBilinDual_of_not_memLp'`：covarianceBilinDual
_of_not_memLp' (h : ¬ MemLp (fun x => x - ∫ y, y ∂μ) 2 μ) (L₁ L₂ : StrongDual Re
al E) : covarianceBilinDual μ L₁ L₂ = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma covarianceBilinDual_comm (L₁ L₂ : StrongDual ℝ E) :
    covarianceBilinDual μ L₁ L₂ = covarianceBilinDual μ L₂ L₁ := by
  by_cases h : MemLp (fun x ↦ x - ∫ y, y ∂μ) 2 μ
  · have h' : MemLp id 2 (Measure.map (fun x ↦ x - ∫ (x : E), x ∂μ) μ) :=
      (measurableEmbedding_subRight _).memLp_map_measure_iff.mpr <| h
    simp_rw [covarianceBilinDual, uncenteredCovarianceBilinDual_apply h', mul_comm (L₁ _)]
  · simp [h, covarianceBilinDual_of_not_memLp']

@[simp]
/-
**ProbabilityTheory.covarianceBilinDual_self_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `P
robabilityTheory`。
形式化陈述：covarianceBilinDual_self_nonneg (L : StrongDual Real E) : 0 <= covarianceB
ilinDual μ L L
参数：L : StrongDual Real E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
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
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `real_inner_self_nonneg`：real_inner_self_nonneg {x : F} : 0 <= ⟪x, x⟫_Rea
l
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.covarianceBilinDual_of_not_memLp`：covarianceBilinDual_
of_not_memLp (h : ¬ MemLp id 2 μ) (L₁ L₂ : StrongDual Real E) : covarianceBilinD
ual μ L₁ L₂ = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma covarianceBilinDual_self_nonneg (L : StrongDual ℝ E) : 0 ≤ covarianceBilinDual μ L L := by
  by_cases h : MemLp id 2 μ
  · simp only [covarianceBilinDual, uncenteredCovarianceBilinDual,
      ContinuousLinearMap.bilinearComp_apply, IsBoundedBilinearMap.toContinuousLinearMap_apply]
    exact real_inner_self_nonneg
  · simp [h]
/-
**ProbabilityTheory.isPosSemidef_covarianceBilinDual** 是 Mathlib 中的一个引理，位于命名空间 `
ProbabilityTheory`。
形式化陈述：isPosSemidef_covarianceBilinDual : (covarianceBilinDual μ).toBilinForm.IsP
osSemidef where eq
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
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
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用引理 `ProbabilityTheory.covarianceBilinDual_comm`：covarianceBilinDual_comm (L₁
 L₂ : StrongDual Real E) : covarianceBilinDual μ L₁ L₂ = covarianceBilinDual μ L
₂ L₁
· 使用引理 `ProbabilityTheory.covarianceBilinDual_self_nonneg`：covarianceBilinDual_s
elf_nonneg (L : StrongDual Real E) : 0 <= covarianceBilinDual μ L L
-/
lemma isPosSemidef_covarianceBilinDual : (covarianceBilinDual μ).toBilinForm.IsPosSemidef where
  eq := covarianceBilinDual_comm
  nonneg := covarianceBilinDual_self_nonneg

variable [CompleteSpace E] [IsFiniteMeasure μ]
/-
**ProbabilityTheory.covarianceBilinDual_apply** 是 Mathlib 中的一个引理，位于命名空间 `Probabi
lityTheory`。
形式化陈述：covarianceBilinDual_apply (h : MemLp id 2 μ) (L₁ L₂ : StrongDual Real E) :
 covarianceBilinDual μ L₁ L₂ = ∫ x, (L₁ x - μ[L₁]) * (L₂ x - μ[L₂]) ∂μ
参数：h : MemLp id 2 μ；L₁ L₂ : StrongDual Real E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
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
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.covarianceBilinDual.eq_1`：∀ {E : Type u_1} [inst : Nor
medAddCommGroup E] {mE : MeasurableSpace E} [inst_1 : NormedSpace ℝ E]   [inst_2
 : BorelSpace E] (μ : MeasureThe…
· 使用引理 `ProbabilityTheory.uncenteredCovarianceBilinDual_apply`：uncenteredCovaria
nceBilinDual_apply (h : MemLp id 2 μ) (L₁ L₂ : StrongDual Real E) : uncenteredCo
varianceBilinDual μ L₁ L₂ = ∫ x, L₁ x * L₂ …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasurableEmbedding.memLp_map_measure_iff`：∀ {α : Type u_1} {m0 : Measur
ableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α} {ε : Type u_7}   [inst 
: TopologicalSpace ε] [inst_1 :…
· 使用定理 `measurableEmbedding_subRight`：∀ {G : Type u_1} [inst : AddGroup G] [inst
_1 : MeasurableSpace G] [MeasurableAdd G] (g : G),   MeasurableEmbedding fun x =
> x - g
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
· 使用定理 `MeasureTheory.MemLp.sub`：∀ {α : Type u_1} {E : Type u_2} {m : Measurable
Space α} [inst : NormedAddCommGroup E] {p : ENNReal}   {μ : MeasureTheory.Measur
e α} {f g : α…
· 使用定理 `MeasureTheory.memLp_const`：memLp_const (c : E) [IsFiniteMeasure μ] : Mem
Lp (fun _ : α => c) p μ
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
· 使用定理 `aemeasurable_id`：aemeasurable_id : AEMeasurable id μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.fun_mul`：∀ {α : Type u_1} {β : Type u
_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Me
asure α}   {f g : α → β} [inst_1…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Continuous.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   {f
 : α → β} [inst_1 : T…
（共 55 条，此处仅展示前 30 条）
-/
lemma covarianceBilinDual_apply (h : MemLp id 2 μ) (L₁ L₂ : StrongDual ℝ E) :
    covarianceBilinDual μ L₁ L₂ = ∫ x, (L₁ x - μ[L₁]) * (L₂ x - μ[L₂]) ∂μ := by
  rw [covarianceBilinDual, uncenteredCovarianceBilinDual_apply,
    integral_map (by fun_prop) (by fun_prop)]
  · have hL (L : StrongDual ℝ E) : μ[L] = L (∫ x, x ∂μ) :=
      L.integral_comp_comm (h.integrable (by simp))
    simp [← hL]
  · exact (measurableEmbedding_subRight _).memLp_map_measure_iff.mpr <| h.sub (memLp_const _)
/-
**ProbabilityTheory.covarianceBilinDual_apply'** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：covarianceBilinDual_apply' (h : MemLp id 2 μ) (L₁ L₂ : StrongDual Real E) 
: covarianceBilinDual μ L₁ L₂ = ∫ x, L₁ (x - μ[id]) * L₂ (x - μ[id]) ∂μ
参数：h : MemLp id 2 μ；L₁ L₂ : StrongDual Real E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
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
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.covarianceBilinDual_apply`：covarianceBilinDual_apply (
h : MemLp id 2 μ) (L₁ L₂ : StrongDual Real E) : covarianceBilinDual μ L₁ L₂ = ∫ 
x, (L₁ x - μ[L₁]) * (L₂ x - μ[L₂]…
· 使用定理 `ContinuousLinearMap.integral_comp_comm`：integral_comp_comm [CompleteSpac
e E] (L : E ->L[𝕜] Fₗ) {φ : X -> E} (φ_int : Integrable φ μ) : ∫ x, L (φ x) ∂μ =
 L (∫ x, φ x ∂μ)
· 使用定理 `MeasureTheory.MemLp.integrable`：∀ {α : Type u_1} {ε : Type u_5} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace ε]   [ins
t_1 : ContinuousENor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma covarianceBilinDual_apply' (h : MemLp id 2 μ) (L₁ L₂ : StrongDual ℝ E) :
    covarianceBilinDual μ L₁ L₂ = ∫ x, L₁ (x - μ[id]) * L₂ (x - μ[id]) ∂μ := by
  rw [covarianceBilinDual_apply h]
  have hL (L : StrongDual ℝ E) : μ[L] = L (∫ x, x ∂μ) :=
    L.integral_comp_comm (h.integrable (by simp))
  simp [← hL]
/-
**ProbabilityTheory.covarianceBilinDual_eq_covariance** 是 Mathlib 中的一个引理，位于命名空间 
`ProbabilityTheory`。
形式化陈述：covarianceBilinDual_eq_covariance (h : MemLp id 2 μ) (L₁ L₂ : StrongDual R
eal E) : covarianceBilinDual μ L₁ L₂ = cov[L₁, L₂; μ]
参数：h : MemLp id 2 μ；L₁ L₂ : StrongDual Real E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
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
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.covarianceBilinDual_apply`：covarianceBilinDual_apply (
h : MemLp id 2 μ) (L₁ L₂ : StrongDual Real E) : covarianceBilinDual μ L₁ L₂ = ∫ 
x, (L₁ x - μ[L₁]) * (L₂ x - μ[L₂]…
· 使用定理 `ProbabilityTheory.covariance.eq_1`：∀ {Ω : Type u_1} {mΩ : MeasurableSpac
e Ω} (X Y : Ω → ℝ) (μ : MeasureTheory.Measure Ω),   ProbabilityTheory.covariance
 X Y μ = ∫ (ω : Ω), (X …
-/
lemma covarianceBilinDual_eq_covariance (h : MemLp id 2 μ) (L₁ L₂ : StrongDual ℝ E) :
    covarianceBilinDual μ L₁ L₂ = cov[L₁, L₂; μ] := by
  rw [covarianceBilinDual_apply h, covariance]
/-
**ProbabilityTheory.covarianceBilinDual_self_eq_variance** 是 Mathlib 中的一个引理，位于命名
空间 `ProbabilityTheory`。
形式化陈述：covarianceBilinDual_self_eq_variance (h : MemLp id 2 μ) (L : StrongDual Re
al E) : covarianceBilinDual μ L L = Var[L; μ]
参数：h : MemLp id 2 μ；L : StrongDual Real E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
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
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.covarianceBilinDual_eq_covariance`：covarianceBilinDual
_eq_covariance (h : MemLp id 2 μ) (L₁ L₂ : StrongDual Real E) : covarianceBilinD
ual μ L₁ L₂ = cov[L₁, L₂; μ]
· 使用引理 `ProbabilityTheory.covariance_self`：covariance_self {X : Ω -> Real} (hX :
 AEMeasurable X μ) : cov[X, X; μ] = Var[X; μ]
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `ContinuousLinearMap.measurable`：∀ {R : Type u_2} {E : Type u_3} {F : Typ
e u_4} [inst : Semiring R] [inst_1 : SeminormedAddCommGroup E]   [inst_2 : _root
_.Module R E] [inst_…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
-/
lemma covarianceBilinDual_self_eq_variance (h : MemLp id 2 μ) (L : StrongDual ℝ E) :
    covarianceBilinDual μ L L = Var[L; μ] := by
  rw [covarianceBilinDual_eq_covariance h, covariance_self (by fun_prop)]

end Covariance

end ProbabilityTheory

