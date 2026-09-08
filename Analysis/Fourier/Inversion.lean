/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Integral.PeakFunction
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Fourier inversion formula

In a finite-dimensional real inner product space, we show the Fourier inversion formula, i.e.,
`𝓕⁻ (𝓕 f) v = f v` if `f` and `𝓕 f` are integrable, and `f` is continuous at `v`. This is proved
in `MeasureTheory.Integrable.fourier_inversion`. See also `Continuous.fourier_inversion`
giving `𝓕⁻ (𝓕 f) = f` under an additional continuity assumption for `f`.

We use the following proof. A naïve computation gives
`𝓕⁻ (𝓕 f) v
= ∫_w exp (2 I π ⟪w, v⟫) 𝓕 f (w) dw
= ∫_w exp (2 I π ⟪w, v⟫) ∫_x, exp (-2 I π ⟪w, x⟫) f x dx) dw
= ∫_x (∫_ w, exp (2 I π ⟪w, v - x⟫ dw) f x dx `

However, the Fubini step does not make sense for lack of integrability, and the middle integral
`∫_ w, exp (2 I π ⟪w, v - x⟫ dw` (which one would like to be a Dirac at `v - x`) is not defined.
To gain integrability, one multiplies with a Gaussian function `exp (-c⁻¹ ‖w‖^2)`, with a large
(but finite) `c`. As this function converges pointwise to `1` when `c → ∞`, we get
`∫_w exp (2 I π ⟪w, v⟫) 𝓕 f (w) dw = lim_c ∫_w exp (-c⁻¹ ‖w‖^2 + 2 I π ⟪w, v⟫) 𝓕 f (w) dw`.
One can perform Fubini on the right-hand side for fixed `c`, writing the integral as
`∫_x (∫_w exp (-c⁻¹‖w‖^2 + 2 I π ⟪w, v - x⟫ dw)) f x dx`.
The middle factor is the Fourier transform of a more and more flat function
(converging to the constant `1`), hence it becomes more and more concentrated, around the
point `v`. (Morally, it converges to the Dirac at `v`). Moreover, it has integral one.
Therefore, multiplying by `f` and integrating, one gets a term converging to `f v` as `c → ∞`.
Since it also converges to `𝓕⁻ (𝓕 f) v`, this proves the result.

To check the concentration property of the middle factor and the fact that it has integral one, we
rely on the explicit computation of the Fourier transform of Gaussians.
-/

public section

open Filter MeasureTheory Complex Module Metric Real Bornology

open scoped Topology FourierTransform RealInnerProductSpace Complex

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℂ E] {f : V → E}

namespace Real

/-
**Real.tendsto_integral_cexp_sq_smul** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：tendsto_integral_cexp_sq_smul (hf : Integrable f) : Tendsto (fun (c : Real
) => (∫ v : V, cexp (- c⁻¹ * ‖v‖ ^ 2) • f v)) atTop (𝓝 (∫ v : V, f v))
参数：hf : Integrable f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.tendsto_integral_filter_of_dominated_convergence`：tendsto_
integral_filter_of_dominated_convergence {ι} {l : Filter ι} [l.IsCountablyGenera
ted] {F : ι -> α -> G} {f : α -> G} (bound : α -> Re…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.AEStronglyMeasurable.smul`：∀ {α : Type u_1} {β : Type u_2}
 [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measu
re α}   {𝕜 : Type u_5} [inst_…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
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
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `Continuous.cexp`：Continuous.cexp (h : Continuous f) : Continuous fun y =
> exp (f y)
· 使用定理 `Continuous.const_mul`：Continuous.const_mul (hf : Continuous f) (b : M) :
 Continuous (b * f ·)
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
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `Continuous.fun_pow`：∀ {M : Type u_3} {X : Type u_5} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace M] [inst_2 : Monoid M]   [ContinuousMul M] {f
 : X → M…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
· 使用定理 `Continuous.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAddGr
oup E] [inst_1 : TopologicalSpace α] {f : α → E},   Continuous f → Continuous fu
n x =…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
（共 73 条，此处仅展示前 30 条）
-/
lemma tendsto_integral_cexp_sq_smul (hf : Integrable f) :
    Tendsto (fun (c : ℝ) ↦ (∫ v : V, cexp (- c⁻¹ * ‖v‖ ^ 2) • f v))
      atTop (𝓝 (∫ v : V, f v)) := by
  apply tendsto_integral_filter_of_dominated_convergence _ _ _ hf.norm
  · filter_upwards with v
    nth_rewrite 2 [show f v = cexp (- (0 : ℝ) * ‖v‖ ^ 2) • f v by simp]
    apply (Tendsto.cexp _).smul_const
    exact tendsto_inv_atTop_zero.ofReal.neg.mul_const _
  · filter_upwards with c using
      AEStronglyMeasurable.smul (Continuous.aestronglyMeasurable (by fun_prop)) hf.1
  · filter_upwards [Ici_mem_atTop (0 : ℝ)] with c (hc : 0 ≤ c)
    filter_upwards with v
    simp only [ofReal_inv, neg_mul, norm_smul]
    norm_cast
    conv_rhs => rw [← one_mul (‖f v‖)]
    gcongr
    simp only [norm_eq_abs, abs_exp, exp_le_one_iff, Left.neg_nonpos_iff]
    positivity

variable [CompleteSpace E]

set_option backward.isDefEq.respectTransparency false in
/-
**Real.tendsto_integral_gaussian_smul** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：tendsto_integral_gaussian_smul (hf : Integrable f) (h'f : Integrable (𝓕 f)
) (v : V) : Tendsto (fun (c : Real) => ∫ w : V, ((π * c) ^ (finrank Real V / 2 :
 Complex) * cexp (-π ^ 2 * c * ‖v - w‖ ^ 2)) • f w) atTop (𝓝 (𝓕⁻ (𝓕 f) v))
参数：hf : Integrable f；h'f : Integrable (𝓕 f)；v : V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Continuous.neg`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpace
 X] [inst_1 : TopologicalSpace G] [inst_2 : Neg G]   [ContinuousNeg G] {f : X → 
G}, …
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `continuous_inner`：continuous_inner : Continuous fun p : E × E => ⟪p.1, p
.2⟫
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `VectorFourier.fourierIntegral_convergent_iff`：fourierIntegral_convergent
_iff (he : Continuous e) (hL : Continuous fun p : V × W => L p.1 p.2) {f : V -> 
E} (w : W) : Integrable (fun v : V…
· 使用定理 `Real.continuous_fourierChar`：continuous_fourierChar : Continuous 𝐞
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submonoid.smul_def`：∀ {M' : Type u_1} {α : Type u_2} [inst : MulOneClass
 M'] [inst_1 : SMul M' α] {S : Submonoid M'} (g : ↥S) (a : α),   g • a = ↑g • a
· 使用定理 `Real.fourierChar_apply`：fourierChar_apply (x : Real) : 𝐞 x = Complex.exp
 (↑(2 * π * x) * Complex.I)
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `Complex.exp_add`：exp_add : exp (x + y) = exp x * exp y
· 使用定理 `real_inner_comm`：real_inner_comm (x y : F) : ⟪y, x⟫_Real = ⟪x, y⟫_Real
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
（共 81 条，此处仅展示前 30 条）
-/
lemma tendsto_integral_gaussian_smul (hf : Integrable f) (h'f : Integrable (𝓕 f)) (v : V) :
    Tendsto (fun (c : ℝ) ↦
      ∫ w : V, ((π * c) ^ (finrank ℝ V / 2 : ℂ) * cexp (-π ^ 2 * c * ‖v - w‖ ^ 2)) • f w)
    atTop (𝓝 (𝓕⁻ (𝓕 f) v)) := by
  have A : Tendsto (fun (c : ℝ) ↦ (∫ w : V, cexp (- c⁻¹ * ‖w‖ ^ 2 + 2 * π * I * ⟪v, w⟫)
       • (𝓕 f) w)) atTop (𝓝 (𝓕⁻ (𝓕 f) v)) := by
    have : Integrable (fun w ↦ 𝐞 ⟪w, v⟫ • (𝓕 f) w) := by
      have B : Continuous fun p : V × V => (- innerₗ V) p.1 p.2 := continuous_inner.neg
      simpa using!
        (VectorFourier.fourierIntegral_convergent_iff Real.continuous_fourierChar B v).2 h'f
    convert! tendsto_integral_cexp_sq_smul this using 4 with c w
    · rw [Submonoid.smul_def, Real.fourierChar_apply, smul_smul, ← Complex.exp_add, real_inner_comm]
      congr 3
      simp only [ofReal_mul, ofReal_ofNat]
      ring
    · simp [fourierInv_eq]
  have B : Tendsto (fun (c : ℝ) ↦ (∫ w : V,
        𝓕 (fun w ↦ cexp (- c⁻¹ * ‖w‖ ^ 2 + 2 * π * I * ⟪v, w⟫)) w • f w)) atTop
      (𝓝 (𝓕⁻ (𝓕 f) v)) := by
    apply A.congr'
    filter_upwards [Ioi_mem_atTop 0] with c (hc : 0 < c)
    have J : Integrable (fun w ↦ cexp (- c⁻¹ * ‖w‖ ^ 2 + 2 * π * I * ⟪v, w⟫)) :=
      GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (by simpa) _ _
    simpa using! (VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ V)
      Real.continuous_fourierChar continuous_inner J hf).symm
  apply B.congr'
  filter_upwards [Ioi_mem_atTop 0] with c (hc : 0 < c)
  congr with w
  rw [fourier_gaussian_innerProductSpace' (by simpa)]
  congr
  · simp
  · simp; ring
/-
**Real.tendsto_integral_gaussian_smul'** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：tendsto_integral_gaussian_smul' (hf : Integrable f) {v : V} (h'f : Continu
ousAt f v) : Tendsto (fun (c : Real) => ∫ w : V, ((π * c : Complex) ^ (finrank R
eal V / 2 : Complex) * cexp (-π ^ 2 * c * ‖v - w‖ ^ 2)) • f w) atTop (𝓝 (f v))
参数：hf : Integrable f；h'f : ContinuousAt f v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `tendsto_integral_comp_smul_smul_of_integrable'`：tendsto_integral_comp_sm
ul_smul_of_integrable' {φ : F -> Real} (hφ : forall x, 0 <= φ x) (h'φ : ∫ x, φ x
 ∂μ = 1) (h : Tendsto (fun x => ‖x‖ …
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_const_mul`：integral_const_mul {L : Type*} [RCLike
 L] (r : L) (f : α -> L) : ∫ a, r * f a ∂μ = r * ∫ a, f a ∂μ
· 使用定理 `GaussianFourier.integral_rexp_neg_mul_sq_norm`：integral_rexp_neg_mul_sq_
norm {b : Real} (hb : 0 < b) : ∫ v : V, rexp (-b * ‖v‖ ^ 2) = (π / b) ^ (Module.
finrank Real V / 2 : Real)
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
· 使用定理 `Real.rpow_sub`：rpow_sub {x : Real} (hx : 0 < x) (y z : Real) : x ^ (y - 
z) = x ^ y / x ^ z
· 使用定理 `Real.rpow_mul`：rpow_mul {x : Real} (hx : 0 <= x) (y z : Real) : x ^ (y *
 z) = (x ^ y) ^ z
· 使用定理 `Real.pi_nonneg`：pi_nonneg : 0 <= π
· 使用定理 `Real.rpow_add`：rpow_add (hx : 0 < x) (y z : Real) : x ^ (y + z) = x ^ y 
* x ^ z
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf'`：∀ {R : Type u_1} [inst : CommSemiri
ng R] {a a' b : R},   a = a' → ∀ {e : ℕ}, Nat.rawCast 1 = e → a' ^ e * Nat.rawCa
st 1 = b → a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
（共 135 条，此处仅展示前 30 条）
-/
lemma tendsto_integral_gaussian_smul' (hf : Integrable f) {v : V} (h'f : ContinuousAt f v) :
    Tendsto (fun (c : ℝ) ↦
      ∫ w : V, ((π * c : ℂ) ^ (finrank ℝ V / 2 : ℂ) * cexp (-π ^ 2 * c * ‖v - w‖ ^ 2)) • f w)
    atTop (𝓝 (f v)) := by
  let φ : V → ℝ := fun w ↦ π ^ (finrank ℝ V / 2 : ℝ) * Real.exp (-π ^ 2 * ‖w‖ ^ 2)
  have A : Tendsto (fun (c : ℝ) ↦ ∫ w : V, (c ^ finrank ℝ V * φ (c • (v - w))) • f w)
      atTop (𝓝 (f v)) := by
    apply tendsto_integral_comp_smul_smul_of_integrable'
    · exact fun x ↦ by positivity
    · rw [integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm (by positivity)]
      nth_rewrite 2 [← pow_one π]
      rw [← rpow_natCast, ← rpow_natCast, ← rpow_sub pi_pos, ← rpow_mul pi_nonneg,
        ← rpow_add pi_pos]
      ring_nf
      exact rpow_zero _
    · have A : Tendsto (fun (w : V) ↦ π ^ 2 * ‖w‖ ^ 2) (cobounded V) atTop := by
        rw [tendsto_const_mul_atTop_of_pos (by positivity)]
        apply (tendsto_pow_atTop two_ne_zero).comp tendsto_norm_cobounded_atTop
      have B := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (finrank ℝ V / 2) 1
        zero_lt_one |>.comp A |>.const_mul (π ^ (-finrank ℝ V / 2 : ℝ))
      rw [mul_zero] at B
      convert! B using 2 with x
      simp only [neg_mul, one_mul, Function.comp_apply, ← mul_assoc, ← rpow_natCast, φ]
      congr 1
      rw [mul_rpow (by positivity) (by positivity), ← rpow_mul pi_nonneg,
        ← rpow_mul (norm_nonneg _), ← mul_assoc, ← rpow_add pi_pos, mul_comm]
      congr <;> ring
    · exact hf
    · exact h'f
  have B : Tendsto
      (fun (c : ℝ) ↦
        ∫ w : V, ((c ^ (1 / 2 : ℝ)) ^ finrank ℝ V * φ ((c ^ (1 / 2 : ℝ)) • (v - w))) • f w)
      atTop (𝓝 (f v)) :=
    A.comp (tendsto_rpow_atTop (by simp))
  apply B.congr'
  filter_upwards [Ioi_mem_atTop 0] with c (hc : 0 < c)
  congr with w
  rw [← coe_smul]
  congr
  rw [ofReal_mul, ofReal_mul, ofReal_exp, ← mul_assoc]
  congr
  · rw [mul_cpow_ofReal_nonneg pi_nonneg hc.le, ← rpow_natCast, ← rpow_mul hc.le, mul_comm,
      ofReal_cpow pi_nonneg, ofReal_cpow hc.le]
    simp [div_eq_inv_mul]
  · norm_cast
    simp only [one_div, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, neg_mul, neg_inj,
      ← rpow_natCast, ← rpow_mul hc.le, mul_assoc]
    simp

end Real

variable [CompleteSpace E]

/-- **Fourier inversion formula**: If a function `f` on a finite-dimensional real inner product
space is integrable, and its Fourier transform `𝓕 f` is also integrable, then `𝓕⁻ (𝓕 f) = f` at
continuity points of `f`. -/
/-
**MeasureTheory.Integrable.fourierInv_fourier_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasureTheory.Integrable.fourierInv_fourier_eq (hf : Integrable f) (h'f : 
Integrable (𝓕 f)) {v : V} (hv : ContinuousAt f v) : 𝓕⁻ (𝓕 f) v = f v
参数：hf : Integrable f；h'f : Integrable (𝓕 f)；hv : ContinuousAt f v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `Real.tendsto_integral_gaussian_smul`：tendsto_integral_gaussian_smul (hf 
: Integrable f) (h'f : Integrable (𝓕 f)) (v : V) : Tendsto (fun (c : Real) => ∫ 
w : V, ((π * c) ^ (finran…
· 使用引理 `Real.tendsto_integral_gaussian_smul'`：tendsto_integral_gaussian_smul' (h
f : Integrable f) {v : V} (h'f : ContinuousAt f v) : Tendsto (fun (c : Real) => 
∫ w : V, ((π * c : Complex…

--- 原说明 ---
**Fourier inversion formula**: If a function `f` on a finite-dimensional real in
ner product
space is integrable, and its Fourier transform `𝓕 f` is also integrable, then `𝓕
⁻ (𝓕 f) = f` at
continuity points of `f`.
-/
theorem MeasureTheory.Integrable.fourierInv_fourier_eq
    (hf : Integrable f) (h'f : Integrable (𝓕 f)) {v : V}
    (hv : ContinuousAt f v) : 𝓕⁻ (𝓕 f) v = f v :=
  tendsto_nhds_unique (Real.tendsto_integral_gaussian_smul hf h'f v)
    (Real.tendsto_integral_gaussian_smul' hf hv)

/-- **Fourier inversion formula**: If a function `f` on a finite-dimensional real inner product
space is continuous, integrable, and its Fourier transform `𝓕 f` is also integrable,
then `𝓕⁻ (𝓕 f) = f`. -/
/-
**Continuous.fourierInv_fourier_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.fourierInv_fourier_eq (h : Continuous f) (hf : Integrable f) (h
'f : Integrable (𝓕 f)) : 𝓕⁻ (𝓕 f) = f
参数：h : Continuous f；hf : Integrable f；h'f : Integrable (𝓕 f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.Integrable.fourierInv_fourier_eq`：MeasureTheory.Integrable
.fourierInv_fourier_eq (hf : Integrable f) (h'f : Integrable (𝓕 f)) {v : V} (hv 
: ContinuousAt f v) : 𝓕⁻ (𝓕 f) v = f…
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x

--- 原说明 ---
**Fourier inversion formula**: If a function `f` on a finite-dimensional real in
ner product
space is continuous, integrable, and its Fourier transform `𝓕 f` is also integra
ble,
then `𝓕⁻ (𝓕 f) = f`.
-/
theorem Continuous.fourierInv_fourier_eq (h : Continuous f)
    (hf : Integrable f) (h'f : Integrable (𝓕 f)) :
    𝓕⁻ (𝓕 f) = f := by
  ext v
  exact hf.fourierInv_fourier_eq h'f h.continuousAt

/-- **Fourier inversion formula**: If a function `f` on a finite-dimensional real inner product
space is integrable, and its Fourier transform `𝓕 f` is also integrable, then `𝓕 (𝓕⁻ f) = f` at
continuity points of `f`. -/
/-
**MeasureTheory.Integrable.fourier_fourierInv_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasureTheory.Integrable.fourier_fourierInv_eq (hf : Integrable f) (h'f : 
Integrable (𝓕 f)) {v : V} (hv : ContinuousAt f v) : 𝓕 (𝓕⁻ f) v = f v
参数：hf : Integrable f；h'f : Integrable (𝓕 f)；hv : ContinuousAt f v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Real.fourierInv_comm`：fourierInv_comm (f : V -> E) : 𝓕 (𝓕⁻ f) = 𝓕⁻ (𝓕 f)
· 使用定理 `MeasureTheory.Integrable.fourierInv_fourier_eq`：MeasureTheory.Integrable
.fourierInv_fourier_eq (hf : Integrable f) (h'f : Integrable (𝓕 f)) {v : V} (hv 
: ContinuousAt f v) : 𝓕⁻ (𝓕 f) v = f…

--- 原说明 ---
**Fourier inversion formula**: If a function `f` on a finite-dimensional real in
ner product
space is integrable, and its Fourier transform `𝓕 f` is also integrable, then `𝓕
 (𝓕⁻ f) = f` at
continuity points of `f`.
-/
theorem MeasureTheory.Integrable.fourier_fourierInv_eq
    (hf : Integrable f) (h'f : Integrable (𝓕 f)) {v : V}
    (hv : ContinuousAt f v) : 𝓕 (𝓕⁻ f) v = f v := by
  rw [fourierInv_comm]
  exact hf.fourierInv_fourier_eq h'f hv

/-- **Fourier inversion formula**: If a function `f` on a finite-dimensional real inner product
space is continuous, integrable, and its Fourier transform `𝓕 f` is also integrable,
then `𝓕 (𝓕⁻ f) = f`. -/
/-
**Continuous.fourier_fourierInv_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.fourier_fourierInv_eq (h : Continuous f) (hf : Integrable f) (h
'f : Integrable (𝓕 f)) : 𝓕 (𝓕⁻ f) = f
参数：h : Continuous f；hf : Integrable f；h'f : Integrable (𝓕 f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.Integrable.fourier_fourierInv_eq`：MeasureTheory.Integrable
.fourier_fourierInv_eq (hf : Integrable f) (h'f : Integrable (𝓕 f)) {v : V} (hv 
: ContinuousAt f v) : 𝓕 (𝓕⁻ f) v = f…
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x

--- 原说明 ---
**Fourier inversion formula**: If a function `f` on a finite-dimensional real in
ner product
space is continuous, integrable, and its Fourier transform `𝓕 f` is also integra
ble,
then `𝓕 (𝓕⁻ f) = f`.
-/
theorem Continuous.fourier_fourierInv_eq (h : Continuous f)
    (hf : Integrable f) (h'f : Integrable (𝓕 f)) :
    𝓕 (𝓕⁻ f) = f := by
  ext v
  exact hf.fourier_fourierInv_eq h'f h.continuousAt
