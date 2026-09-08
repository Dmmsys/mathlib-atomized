/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# The Riemann-Lebesgue Lemma

In this file we prove the Riemann-Lebesgue lemma, for functions on finite-dimensional real vector
spaces `V`: if `f` is a function on `V` (valued in a complete normed space `E`), then the
Fourier transform of `f`, viewed as a function on the dual space of `V`, tends to 0 along the
cocompact filter. Here the Fourier transform is defined by

`fun w : StrongDual ℝ V ↦ ∫ (v : V), exp (↑(2 * π * w v) * I) • f v`.

This is true for arbitrary functions, but is only interesting for `L¹` functions (if `f` is not
integrable then the integral is zero for all `w`). This is proved first for continuous
compactly-supported functions on inner-product spaces; then we pass to arbitrary functions using the
density of continuous compactly-supported functions in `L¹` space. Finally we generalise from
inner-product spaces to arbitrary finite-dimensional spaces, by choosing a continuous linear
equivalence to an inner-product space.

## Main results

- `tendsto_integral_exp_inner_smul_cocompact` : for `V` a finite-dimensional real inner product
  space and `f : V → E`, the function `fun w : V ↦ ∫ v : V, exp (2 * π * ⟪w, v⟫ * I) • f v`
  tends to 0 along `cocompact V`.
- `tendsto_integral_exp_smul_cocompact` : for `V` a finite-dimensional real vector space (endowed
  with its unique Hausdorff topological vector space structure), and `W` the dual of `V`, the
  function `fun w : W ↦ ∫ v : V, exp (2 * π * w v * I) • f v` tends to along `cocompact W`.
- `Real.tendsto_integral_exp_smul_cocompact`: special case of functions on `ℝ`.
- `Real.zero_at_infty_fourierIntegral` and `Real.zero_at_infty_vector_fourierIntegral`:
  reformulations explicitly using the Fourier integral.
-/

public section

noncomputable section

open MeasureTheory Filter Complex Set Module

open scoped Filter Topology Real ENNReal FourierTransform RealInnerProductSpace NNReal

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : V → E}

section InnerProductSpace

variable [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

local notation3 "i" => fun (w : V) => (1 / (2 * ‖w‖ ^ 2) : ℝ) • w

/-- Shifting `f` by `(1 / (2 * ‖w‖ ^ 2)) • w` negates the integral in the Riemann-Lebesgue lemma. -/
/-
**fourierIntegral_half_period_translate** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fourierIntegral_half_period_translate {w : V} (hw : w != 0) : (∫ v : V, 𝐞 
(-⟪v, w⟫) • f (v + i w)) = -∫ v : V, 𝐞 (-⟪v, w⟫) • f v
参数：hw : w != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inner_smul_left`：inner_smul_left (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪
x, y⟫
· 使用定理 `inner_self_eq_norm_sq_to_K`：inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ 
= (‖x‖ : 𝕜) ^ 2
· 使用定理 `RCLike.ofReal_real_eq_id`：ofReal_real_eq_id : @ofReal Real _ = id
· 使用定理 `id.eq_1`：∀ {α : Sort u} (a : α), id a = a
· 使用定理 `RCLike.conj_to_real`：conj_to_real {x : Real} : conj x = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_div`：div_div : a / b / c = a / (b * c)
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用引理 `sq_eq_zero_iff`：sq_eq_zero_iff : a ^ 2 = 0 ↔ a = 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `norm_eq_zero`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a‖ = 
0 ↔ a = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inner_add_left`：inner_add_left (x y z : E) : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z
⟫
· 使用定理 `neg_add`：neg_add {R} [CommRing R] {a₁ a₂ b₁ b₂ : R} (_ : -a₁ = b₁) (_ : 
-a₂ = b₂) : -(a₁ + a₂) = b₁ + b₂
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Complex.ofReal_add`：ofReal_add (r s : Real) : ((r + s : Real) : Complex)
 = r + s
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `Complex.exp_add`：exp_add : exp (x + y) = exp x * exp y
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
（共 115 条，此处仅展示前 30 条）

--- 原说明 ---
Shifting `f` by `(1 / (2 * ‖w‖ ^ 2)) • w` negates the integral in the Riemann-Le
besgue lemma.
-/
theorem fourierIntegral_half_period_translate {w : V} (hw : w ≠ 0) :
    (∫ v : V, 𝐞 (-⟪v, w⟫) • f (v + i w)) = -∫ v : V, 𝐞 (-⟪v, w⟫) • f v := by
  have hiw : ⟪i w, w⟫ = 1 / 2 := by
    rw [inner_smul_left, inner_self_eq_norm_sq_to_K, RCLike.ofReal_real_eq_id, id,
      RCLike.conj_to_real, ← div_div, div_mul_cancel₀]
    rwa [Ne, sq_eq_zero_iff, norm_eq_zero]
  have :
    (fun v : V => 𝐞 (-⟪v, w⟫) • f (v + i w)) =
      fun v : V => (fun x : V => -(𝐞 (-⟪x, w⟫) • f x)) (v + i w) := by
    ext1 v
    simp_rw [inner_add_left, hiw, Circle.smul_def, Real.fourierChar_apply, neg_add, mul_add,
      ofReal_add, add_mul, exp_add]
    match_scalars
    have H : exp (- (π * I)) = (-1)⁻¹ := by rw [exp_neg, exp_pi_mul_I]
    linear_combination (norm := ring_nf) cexp (-2 * π * ⟪v, w⟫ * I) * H
  rw [this, integral_add_right_eq_self (fun (x : V) ↦ -(𝐞 (-⟪x, w⟫) • f x))
        ((fun w ↦ (1 / (2 * ‖w‖ ^ (2 : ℕ))) • w) w)]
  simp only [integral_neg]

/-- Rewrite the Fourier integral in a form that allows us to use uniform continuity. -/
/-
**fourierIntegral_eq_half_sub_half_period_translate** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：fourierIntegral_eq_half_sub_half_period_translate {w : V} (hw : w != 0) (h
f : Integrable f) : ∫ v : V, 𝐞 (-⟪v, w⟫) • f v = (1 / (2 : Complex)) • ∫ v : V, 
𝐞 (-⟪v, w⟫) • (f v - f (v + i w))
参数：hw : w != 0；hf : Integrable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `MeasureTheory.integral_sub`：integral_sub {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a - g a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.fourierIntegral_convergent_iff`：∀ {V : Type u_1} {E : Type u_3} [in
st : NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E] [inst_2 : NormedAddCommGro
up V]   [inst_3 : InnerPr…
· 使用定理 `MeasureTheory.Integrable.comp_add_right`：∀ {G : Type u_4} {F : Type u_6}
 [inst : MeasurableSpace G] [inst_1 : NormedAddCommGroup F] {μ : MeasureTheory.M
easure G}   [inst_2 : AddGrou…
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
· 使用定理 `MeasureTheory.IsAddLeftInvariant.isAddRightInvariant`：∀ {G : Type u_1} [
inst : MeasurableSpace G] [inst_1 : AddCommSemigroup G] {μ : MeasureTheory.Measu
re G}   [μ.IsAddLeftInvariant], μ.IsAddRig…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsAddLeftInvariant`：∀ {G : Type
 u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpac
e G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `fourierIntegral_half_period_translate`：fourierIntegral_half_period_trans
late {w : V} (hw : w != 0) : (∫ v : V, 𝐞 (-⟪v, w⟫) • f (v + i w)) = -∫ v : V, 𝐞 
(-⟪v, w⟫) • f v
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_smul`：two_smul : (2 : R) • x = x + x
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
Rewrite the Fourier integral in a form that allows us to use uniform continuity.
-/
theorem fourierIntegral_eq_half_sub_half_period_translate {w : V} (hw : w ≠ 0)
    (hf : Integrable f) :
    ∫ v : V, 𝐞 (-⟪v, w⟫) • f v = (1 / (2 : ℂ)) • ∫ v : V, 𝐞 (-⟪v, w⟫) • (f v - f (v + i w)) := by
  simp_rw [smul_sub]
  rw [integral_sub, fourierIntegral_half_period_translate hw, sub_eq_add_neg, neg_neg, ←
    two_smul ℂ _, ← @smul_assoc _ _ _ _ _ _ (IsScalarTower.left ℂ), smul_eq_mul]
  · simp
  exacts [(Real.fourierIntegral_convergent_iff w).2 hf,
    (Real.fourierIntegral_convergent_iff w).2 (hf.comp_add_right _)]

/-- Riemann-Lebesgue Lemma for continuous and compactly-supported functions: the integral
`∫ v, exp (-2 * π * ⟪w, v⟫ * I) • f v` tends to 0 w.r.t. `cocompact V`. Note that this is primarily
of interest as a preparatory step for the more general result
`tendsto_integral_exp_inner_smul_cocompact` in which `f` can be arbitrary. -/
/-
**tendsto_integral_exp_inner_smul_cocompact_of_continuous_compact_support** 是 Ma
thlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_integral_exp_inner_smul_cocompact_of_continuous_compact_support (h
f1 : Continuous f) (hf2 : HasCompactSupport f) : Tendsto (fun w : V => ∫ v : V, 
𝐞 (-⟪v, w⟫) • f v) (cocompact V) (𝓝 0)
参数：hf1 : Continuous f；hf2 : HasCompactSupport f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NormedAddGroup.tendsto_nhds_zero`：∀ {α : Type u_2} {E : Type u_5} [inst 
: SeminormedAddGroup E] {f : α → E} {l : Filter α},   Filter.Tendsto f l (nhds 0
) ↔ ∀ ε > 0, ∀ᶠ (x : α…
· 使用定理 `HasCompactSupport.exists_pos_le_norm`：∀ {α : Type u_1} {E : Type u_2} [i
nst : NormedAddGroup α] {f : α → E} [inst_1 : Zero E],   HasCompactSupport f → ∃
 R, 0 < R ∧ ∀ (x : α), R ≤…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsClosed.measurableSet`：IsClosed.measurableSet (h : IsClosed s) : Measur
ableSet s
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用引理 `Metric.isClosed_closedBall`：isClosed_closedBall : IsClosed (closedBall x
 ε)
· 使用定理 `ProperSpace.isCompact_closedBall`：∀ {α : Type u} {inst : PseudoMetricSpa
ce α} [self : ProperSpace α] (x : α) (r : ℝ), IsCompact (Metric.closedBall x r)
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `IsCompact.measure_lt_top`：∀ {α : Type u_1} {m0 : MeasurableSpace α} [ins
t : TopologicalSpace α] {μ : MeasureTheory.Measure α}   [MeasureTheory.IsFiniteM
easureOnCompac…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G
 : Type u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : Measura
bleSpace G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `add_pos_of_nonneg_of_pos`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst
_1 : Preorder α] [AddLeftStrictMono α] {a b : α},   0 ≤ a → 0 < b → 0 < a + b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `ENNReal.coe_add`：∀ (x y : NNReal), ↑(x + y) = ↑x + ↑y
（共 128 条，此处仅展示前 30 条）

--- 原说明 ---
Riemann-Lebesgue Lemma for continuous and compactly-supported functions: the int
egral
`∫ v, exp (-2 * π * ⟪w, v⟫ * I) • f v` tends to 0 w.r.t. `cocompact V`. Note tha
t this is primarily
of interest as a preparatory step for the more general result
`tendsto_integral_exp_inner_smul_cocompact` in which `f` can be arbitrary.
-/
theorem tendsto_integral_exp_inner_smul_cocompact_of_continuous_compact_support (hf1 : Continuous f)
    (hf2 : HasCompactSupport f) :
    Tendsto (fun w : V => ∫ v : V, 𝐞 (-⟪v, w⟫) • f v) (cocompact V) (𝓝 0) := by
  refine NormedAddGroup.tendsto_nhds_zero.mpr fun ε hε => ?_
  suffices ∃ T : ℝ, ∀ w : V, T ≤ ‖w‖ → ‖∫ v : V, 𝐞 (-⟪v, w⟫) • f v‖ < ε by
    simp_rw [← comap_dist_left_atTop_eq_cocompact (0 : V), eventually_comap, eventually_atTop,
      dist_eq_norm', sub_zero]
    exact
      let ⟨T, hT⟩ := this
      ⟨T, fun b hb v hv => hT v (hv.symm ▸ hb)⟩
  obtain ⟨R, -, hR_bd⟩ : ∃ R : ℝ, 0 < R ∧ ∀ x : V, R ≤ ‖x‖ → f x = 0 := hf2.exists_pos_le_norm
  let A := {v : V | ‖v‖ ≤ R + 1}
  have mA : MeasurableSet A := by
    suffices A = Metric.closedBall (0 : V) (R + 1) by
      rw [this]
      exact Metric.isClosed_closedBall.measurableSet
    simp_rw [A, Metric.closedBall, dist_eq_norm, sub_zero]
  obtain ⟨B, hB_pos, hB_vol⟩ : ∃ B : ℝ≥0, 0 < B ∧ volume A ≤ B := by
    have hc : IsCompact A := by
      simpa only [Metric.closedBall, dist_eq_norm, sub_zero] using isCompact_closedBall (0 : V) _
    let B₀ := volume A
    replace hc : B₀ < ⊤ := hc.measure_lt_top
    refine ⟨B₀.toNNReal + 1, add_pos_of_nonneg_of_pos B₀.toNNReal.coe_nonneg one_pos, ?_⟩
    rw [ENNReal.coe_add, ENNReal.coe_one, ENNReal.coe_toNNReal hc.ne]
    exact le_self_add
  --* Use uniform continuity to choose δ such that `‖x - y‖ < δ` implies `‖f x - f y‖ < ε / B`.
  obtain ⟨δ, hδ1, hδ2⟩ :=
    Metric.uniformContinuous_iff.mp (hf2.uniformContinuous_of_continuous hf1) (ε / B)
      (div_pos hε hB_pos)
  refine ⟨1 / 2 + 1 / (2 * δ), fun w hw_bd => ?_⟩
  have hw_ne : w ≠ 0 := by
    contrapose! hw_bd; rw [hw_bd, norm_zero]
    exact add_pos one_half_pos (one_div_pos.mpr <| mul_pos two_pos hδ1)
  have hw'_nm : ‖i w‖ = 1 / (2 * ‖w‖) := by
    rw [norm_smul, norm_div, Real.norm_of_nonneg (mul_nonneg two_pos.le <| sq_nonneg _), norm_one,
      sq, ← div_div, ← div_div, ← div_div, div_mul_cancel₀ _ (norm_eq_zero.not.mpr hw_ne)]
  --* Rewrite integral in terms of `f v - f (v + w')`.
  have : ‖(1 / 2 : ℂ)‖ = 2⁻¹ := by simp
  rw [fourierIntegral_eq_half_sub_half_period_translate hw_ne
      (hf1.integrable_of_hasCompactSupport hf2),
    norm_smul, this, inv_mul_eq_div, div_lt_iff₀' two_pos]
  refine lt_of_le_of_lt (norm_integral_le_integral_norm _) ?_
  simp_rw [Circle.norm_smul]
  --* Show integral can be taken over A only.
  have int_A : ∫ v : V, ‖f v - f (v + i w)‖ = ∫ v in A, ‖f v - f (v + i w)‖ := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun v hv => ?_).symm
    dsimp only [A] at hv
    simp only [mem_ofPred, not_le] at hv
    rw [hR_bd v _, hR_bd (v + i w) _, sub_zero, norm_zero]
    · rw [← sub_neg_eq_add]
      refine le_trans ?_ (norm_sub_norm_le _ _)
      rw [le_sub_iff_add_le, norm_neg]
      refine le_trans ?_ hv.le
      rw [add_le_add_iff_left, hw'_nm, ← div_div]
      refine (div_le_one <| norm_pos_iff.mpr hw_ne).mpr ?_
      refine le_trans (le_add_of_nonneg_right <| one_div_nonneg.mpr <| ?_) hw_bd
      exact (mul_pos (zero_lt_two' ℝ) hδ1).le
    · exact (le_add_of_nonneg_right zero_le_one).trans hv.le
  rw [int_A]; clear int_A
  --* Bound integral using fact that `‖f v - f (v + w')‖` is small.
  have bdA : ∀ v : V, v ∈ A → ‖‖f v - f (v + i w)‖‖ ≤ ε / B := by
    simp_rw [norm_norm]
    simp_rw [dist_eq_norm] at hδ2
    refine fun x _ => (hδ2 ?_).le
    rw [sub_add_cancel_left, norm_neg, hw'_nm, ← div_div, div_lt_iff₀ (norm_pos_iff.mpr hw_ne), ←
      div_lt_iff₀' hδ1, div_div]
    exact (lt_add_of_pos_left _ one_half_pos).trans_le hw_bd
  have bdA2 := norm_setIntegral_le_of_norm_le_const (hB_vol.trans_lt ENNReal.coe_lt_top) bdA
  have : ‖_‖ = ∫ v : V in A, ‖f v - f (v + i w)‖ :=
    Real.norm_of_nonneg (setIntegral_nonneg mA fun x _ => norm_nonneg _)
  rw [this] at bdA2
  refine bdA2.trans_lt ?_
  rw [div_mul_eq_mul_div, div_lt_iff₀ (NNReal.coe_pos.mpr hB_pos), mul_comm (2 : ℝ), mul_assoc,
    mul_lt_mul_iff_right₀ hε]
  refine (ENNReal.toReal_mono ENNReal.coe_ne_top hB_vol).trans_lt ?_
  rw [ENNReal.coe_toReal, two_mul]
  exact lt_add_of_pos_left _ hB_pos

variable (f)

/-- Riemann-Lebesgue lemma for functions on a real inner-product space: the integral
`∫ v, exp (-2 * π * ⟪w, v⟫ * I) • f v` tends to 0 as `w → ∞`. -/
/-
**tendsto_integral_exp_inner_smul_cocompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_integral_exp_inner_smul_cocompact : Tendsto (fun w : V => ∫ v, 𝐞 (
-⟪v, w⟫) • f v) (cocompact V) (𝓝 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.tendsto_nhds`：tendsto_nhds {f : Filter β} {u : β -> α} {a : α} : 
Tendsto u f (𝓝 a) ↔ forall ε > 0, forallᶠ x in f, dist (u x) a < ε
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.Integrable.exists_hasCompactSupport_integral_sub_le`：∀ {α 
: Type u_1} [inst : TopologicalSpace α] [NormalSpace α] [inst_2 : MeasurableSpac
e α] [BorelSpace α] {E : Type u_2}   [inst_4 : NormedAd…
· 使用定理 `PerfectlyNormalSpace.toNormalSpace`：∀ {X : Type u} {inst : TopologicalSp
ace X} [self : PerfectlyNormalSpace X], NormalSpace X
· 使用定理 `T6Space.toPerfectlyNormalSpace`：∀ {X : Type u} {inst : TopologicalSpace 
X} [self : T6Space X], PerfectlyNormalSpace X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.regularSpace`：∀ {X : Type u_2} [i
nst : TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X], RegularSpa
ce X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `MeasureTheory.Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMea
sure`：∀ {X : Type u_3} [inst : TopologicalSpace X] [TopologicalSpace.PseudoMetri
zableSpace X] [SigmaCompactSpace X]   [inst_3 : MeasurableSpace X]…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `MeasureTheory.isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts`：∀ {α 
: Type u_1} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topol
ogicalSpace α]   [WeaklyLocallyCompactSpace α] [Measure…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G
 : Type u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : Measura
bleSpace G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `two_pos`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : PartialO
rder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
（共 64 条，此处仅展示前 30 条）

--- 原说明 ---
Riemann-Lebesgue lemma for functions on a real inner-product space: the integral
`∫ v, exp (-2 * π * ⟪w, v⟫ * I) • f v` tends to 0 as `w → ∞`.
-/
theorem tendsto_integral_exp_inner_smul_cocompact :
    Tendsto (fun w : V => ∫ v, 𝐞 (-⟪v, w⟫) • f v) (cocompact V) (𝓝 0) := by
  by_cases hfi : Integrable f; swap
  · convert! tendsto_const_nhds (x := (0 : E)) with w
    apply integral_undef
    rwa [Real.fourierIntegral_convergent_iff]
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  obtain ⟨g, hg_supp, hfg, hg_cont, -⟩ :=
    hfi.exists_hasCompactSupport_integral_sub_le (div_pos hε two_pos)
  refine
    ((Metric.tendsto_nhds.mp
            (tendsto_integral_exp_inner_smul_cocompact_of_continuous_compact_support hg_cont
              hg_supp))
          _ (div_pos hε two_pos)).mp
      (Eventually.of_forall fun w hI => ?_)
  rw [dist_eq_norm] at hI ⊢
  have : ‖(∫ v, 𝐞 (-⟪v, w⟫) • f v) - ∫ v, 𝐞 (-⟪v, w⟫) • g v‖ ≤ ε / 2 := by
    refine le_trans ?_ hfg
    simp_rw [← integral_sub ((Real.fourierIntegral_convergent_iff w).2 hfi)
      ((Real.fourierIntegral_convergent_iff w).2 (hg_cont.integrable_of_hasCompactSupport hg_supp)),
      ← smul_sub, ← Pi.sub_apply]
    exact VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 _ (innerₗ V) (f - g) w
  replace := add_lt_add_of_le_of_lt this hI
  rw [add_halves] at this
  refine ((le_of_eq ?_).trans (norm_add_le _ _)).trans_lt this
  simp only [sub_zero, sub_add_cancel]

/-- The Riemann-Lebesgue lemma for functions on `ℝ`. -/
/-
**Real.tendsto_integral_exp_smul_cocompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.tendsto_integral_exp_smul_cocompact (f : Real -> E) : Tendsto (fun w 
: Real => ∫ v : Real, 𝐞 (-(v * w)) • f v) (cocompact Real) (𝓝 0)
参数：f : Real -> E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `tendsto_integral_exp_inner_smul_cocompact`：tendsto_integral_exp_inner_sm
ul_cocompact : Tendsto (fun w : V => ∫ v, 𝐞 (-⟪v, w⟫) • f v) (cocompact V) (𝓝 0)

--- 原说明 ---
The Riemann-Lebesgue lemma for functions on `ℝ`.
-/
theorem Real.tendsto_integral_exp_smul_cocompact (f : ℝ → E) :
    Tendsto (fun w : ℝ => ∫ v : ℝ, 𝐞 (-(v * w)) • f v) (cocompact ℝ) (𝓝 0) := by
  simp_rw [mul_comm]
  exact tendsto_integral_exp_inner_smul_cocompact f

/-- The Riemann-Lebesgue lemma for functions on `ℝ`, formulated via
`Real.instFourierTransform.fourier`. -/
/-
**Real.zero_at_infty_fourier** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.zero_at_infty_fourier (f : Real -> E) : Tendsto (𝓕 f) (cocompact Real
) (𝓝 0)
参数：f : Real -> E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_integral_exp_inner_smul_cocompact`：tendsto_integral_exp_inner_sm
ul_cocompact : Tendsto (fun w : V => ∫ v, 𝐞 (-⟪v, w⟫) • f v) (cocompact V) (𝓝 0)

--- 原说明 ---
The Riemann-Lebesgue lemma for functions on `ℝ`, formulated via
`Real.instFourierTransform.fourier`.
-/
theorem Real.zero_at_infty_fourier (f : ℝ → E) : Tendsto (𝓕 f) (cocompact ℝ) (𝓝 0) :=
  tendsto_integral_exp_inner_smul_cocompact f

/-- Riemann-Lebesgue lemma for functions on a finite-dimensional inner-product space, formulated
via dual space. **Do not use** -- it is only a stepping stone to
`tendsto_integral_exp_smul_cocompact` where the inner-product-space structure isn't required. -/
/-
**tendsto_integral_exp_smul_cocompact_of_inner_product** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：tendsto_integral_exp_smul_cocompact_of_inner_product (μ : Measure V) [μ.Is
AddHaarMeasure] : Tendsto (fun w : StrongDual Real V => ∫ v, 𝐞 (-w v) • f v ∂μ) 
(cocompact (StrongDual Real V)) (𝓝 0)
参数：μ : Measure V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G
 : Type u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : Measura
bleSpace G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsAddLeftInvariant`：∀ {G : Type
 u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpac
e G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.isAddLeftInvariant_eq_smul`：∀ {G : Type u_1} [inst
 : TopologicalSpace G] [inst_1 : AddGroup G] [inst_2 : IsTopologicalAddGroup G] 
  [inst_3 : MeasurableSpace G] [inst_4…
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_smul_nnreal_measure`：integral_smul_nnreal_measure
 (f : α -> G) (c : Real>=0) : ∫ x, f x ∂(c • μ) = c • ∫ x, f x ∂μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Filter.Tendsto.const_smul`：Filter.Tendsto.const_smul {f : β -> α} {l : F
ilter β} {a : α} (hf : Tendsto f l (𝓝 a)) (c : M) : Tendsto (fun x => c • f x) l
 (𝓝 (c • a))
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `NNReal.instContinuousSMulOfReal`：∀ {α : Type u_1} [inst : TopologicalSpa
ce α] [inst_1 : MulAction ℝ α] [ContinuousSMul ℝ α], ContinuousSMul NNReal α
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
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
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `inner_conj_symm`：inner_conj_symm (x y : E) : ⟪y, x⟫† = ⟪x, y⟫
· 使用定理 `RCLike.conj_to_real`：conj_to_real {x : Real} : conj x = x
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
Riemann-Lebesgue lemma for functions on a finite-dimensional inner-product space
, formulated
via dual space. **Do not use** -- it is only a stepping stone to
`tendsto_integral_exp_smul_cocompact` where the inner-product-space structure is
n't required.
-/
theorem tendsto_integral_exp_smul_cocompact_of_inner_product (μ : Measure V) [μ.IsAddHaarMeasure] :
    Tendsto (fun w : StrongDual ℝ V => ∫ v, 𝐞 (-w v) • f v ∂μ) (cocompact (StrongDual ℝ V))
    (𝓝 0) := by
  rw [μ.isAddLeftInvariant_eq_smul volume]
  simp_rw [integral_smul_nnreal_measure]
  rw [← (smul_zero _ : Measure.addHaarScalarFactor μ volume • (0 : E) = 0)]
  apply Tendsto.const_smul
  let A := (InnerProductSpace.toDual ℝ V).symm
  have : (fun w : StrongDual ℝ V ↦ ∫ v, 𝐞 (-w v) • f v) =
      (fun w : V ↦ ∫ v, 𝐞 (-⟪v, w⟫) • f v) ∘ A := by
    ext1 w
    congr 1 with v : 1
    rw [← inner_conj_symm, RCLike.conj_to_real, InnerProductSpace.toDual_symm_apply]
  rw [this]
  exact (tendsto_integral_exp_inner_smul_cocompact f).comp
      A.toHomeomorph.toCocompactMap.cocompact_tendsto'

end InnerProductSpace

section NoInnerProduct

variable (f) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
  [MeasurableSpace V] [BorelSpace V] [Module ℝ V] [ContinuousSMul ℝ V] [FiniteDimensional ℝ V]

/-- Riemann-Lebesgue lemma for functions on a finite-dimensional real vector space, formulated via
dual space. -/
/-
**tendsto_integral_exp_smul_cocompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_integral_exp_smul_cocompact (μ : Measure V) [μ.IsAddHaarMeasure] :
 Tendsto (fun w : StrongDual Real V => ∫ v, 𝐞 (-w v) • f v ∂μ) (cocompact (Stron
gDual Real V)) (𝓝 0)
参数：μ : Measure V。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `ContinuousLinearEquiv.isAddHaarMeasure_map`：∀ {E : Type u_3} {F : Type u
_4} {R : Type u_5} {S : Type u_6} [inst : Semiring R] [inst_1 : Semiring S]   [i
nst_2 : AddCommGroup E] [inst_3 …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ContinuousLinearEquiv.symm_apply_apply`：symm_apply_apply (e : M₁ ≃SL[σ₁₂
] M₂) (b : M₁) : e.symm (e b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.integral_map_equiv`：integral_map_equiv {β} [MeasurableSpac
e β] (e : α ≃ᵐ β) (f : β -> G) : ∫ y, f y ∂Measure.map e μ = ∫ x, f (e x) ∂μ
· 使用定理 `Homeomorph.toCocompactMap_toFun`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace α] [inst_1 : TopologicalSpace β] (f : α ≃ₜ β) (a : α),   f.toC
ocompactMap a = f a
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousLinearEquiv.arrowCongrSL_apply`：∀ {𝕜 : Type u_1} {𝕜₂ : Type u_
2} {𝕜₃ : Type u_3} {𝕜₄ : Type u_4} {E : Type u_5} {F : Type u_6} {G : Type u_7} 
  {H : Type u_8} [inst : AddCo…
· 使用定理 `ContinuousLinearMap.id_comp`：id_comp (f : M₁ ->SL[σ₁₂] M₂) : .id R₂ M₂ ∘
SL f = f
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_integral_exp_smul_cocompact_of_inner_product`：tendsto_integral_e
xp_smul_cocompact_of_inner_product (μ : Measure V) [μ.IsAddHaarMeasure] : Tendst
o (fun w : StrongDual Real V => ∫ v, 𝐞 (-w…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CocompactMap.cocompact_tendsto'`：∀ {α : Type u} {β : Type v} [inst : Top
ologicalSpace α] [inst_1 : TopologicalSpace β] (self : CocompactMap α β),   Filt
er.Tendsto self.toFun…

--- 原说明 ---
Riemann-Lebesgue lemma for functions on a finite-dimensional real vector space, 
formulated via
dual space.
-/
theorem tendsto_integral_exp_smul_cocompact (μ : Measure V) [μ.IsAddHaarMeasure] :
    Tendsto (fun w : StrongDual ℝ V => ∫ v, 𝐞 (-w v) • f v ∂μ) (cocompact (StrongDual ℝ V))
      (𝓝 0) := by
  -- We have already proved the result for inner-product spaces, formulated in a way which doesn't
  -- refer to the inner product. So we choose an arbitrary inner-product space isomorphic to V
  -- and port the result over from there.
  let V' := EuclideanSpace ℝ (Fin (finrank ℝ V))
  have A : V ≃L[ℝ] V' := toEuclidean
  borelize V'
  -- various equivs derived from A
  let Aₘ : MeasurableEquiv V V' := A.toHomeomorph.toMeasurableEquiv
  -- isomorphism between duals derived from A
  let Adual : StrongDual ℝ V ≃L[ℝ] StrongDual ℝ V' := A.arrowCongrSL (.refl _ _)
  have : (μ.map Aₘ).IsAddHaarMeasure := A.isAddHaarMeasure_map _
  convert!
    (tendsto_integral_exp_smul_cocompact_of_inner_product (f ∘ A.symm) (μ.map Aₘ)).comp
      Adual.toHomeomorph.toCocompactMap.cocompact_tendsto' with
    w
  suffices ∫ v, 𝐞 (-w v) • f v ∂μ = ∫ (x : V), 𝐞 (-w (A.symm (Aₘ x))) • f (A.symm (Aₘ x)) ∂μ by
    simpa [Function.comp_apply, integral_map_equiv, Adual]
  simp [Aₘ]

/-- The Riemann-Lebesgue lemma, formulated in terms of `VectorFourier.fourierIntegral` (with the
pairing in the definition of `fourierIntegral` taken to be the canonical pairing between `V` and
its dual space). -/
/-
**Real.zero_at_infty_vector_fourierIntegral** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.zero_at_infty_vector_fourierIntegral (μ : Measure V) [μ.IsAddHaarMeas
ure] : Tendsto (VectorFourier.fourierIntegral 𝐞 μ (topDualPairing Real V).flip f
) (cocompact (StrongDual Real V)) (𝓝 0)
参数：μ : Measure V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_integral_exp_smul_cocompact`：tendsto_integral_exp_smul_cocompact
 (μ : Measure V) [μ.IsAddHaarMeasure] : Tendsto (fun w : StrongDual Real V => ∫ 
v, 𝐞 (-w v) • f v ∂μ) (co…

--- 原说明 ---
The Riemann-Lebesgue lemma, formulated in terms of `VectorFourier.fourierIntegra
l` (with the
pairing in the definition of `fourierIntegral` taken to be the canonical pairing
 between `V` and
its dual space).
-/
theorem Real.zero_at_infty_vector_fourierIntegral (μ : Measure V) [μ.IsAddHaarMeasure] :
    Tendsto (VectorFourier.fourierIntegral 𝐞 μ (topDualPairing ℝ V).flip f)
      (cocompact (StrongDual ℝ V)) (𝓝 0) :=
  _root_.tendsto_integral_exp_smul_cocompact f μ

end NoInnerProduct

