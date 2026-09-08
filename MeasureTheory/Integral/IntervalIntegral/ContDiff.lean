/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Fundamental theorem of calculus for `C^1` functions

We give versions of the second fundamental theorem of calculus under the strong assumption
that the function is `C^1` on the interval. This is restrictive, but satisfied in many situations.
-/

public section

noncomputable section

open MeasureTheory Set Filter Function Asymptotics

open scoped Topology ENNReal Interval NNReal

variable {ι 𝕜 E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : ℝ → E} {a b : ℝ}

namespace intervalIntegral

variable [CompleteSpace E]

/-- Fundamental theorem of calculus-2: If `f : ℝ → E` is `C^1` on `[a, b]`,
then `∫ y in a..b, deriv f y` equals `f b - f a`. -/
/-
**intervalIntegral.integral_deriv_of_contDiffOn_Icc** 是 Mathlib 中的一个定理，位于命名空间 `i
ntervalIntegral`。
形式化陈述：integral_deriv_of_contDiffOn_Icc (h : ContDiffOn Real 1 f (Icc a b)) (hab 
: a <= b) : ∫ x in a..b, deriv f x = f b - f a
参数：h : ContDiffOn Real 1 f (Icc a b)；hab : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegral.integral_same`：integral_same : ∫ x in a..a, f x ∂μ = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`：integral_eq_sub_of
_hasDerivAt_of_le (hab : a <= b) (hcont : ContinuousOn f (Icc a b)) (hderiv : fo
rall x in Ioo a b, HasDerivAt f (f' x) x) …
· 使用定理 `ContDiffOn.continuousOn`：ContDiffOn.continuousOn (h : ContDiffOn 𝕜 n f s
) : ContinuousOn f s
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
· 使用定理 `DifferentiableWithinAt.differentiableAt`：DifferentiableWithinAt.differen
tiableAt (h : DifferentiableWithinAt 𝕜 f s x) (hs : s in 𝓝 x) : DifferentiableAt
 𝕜 f x
· 使用定理 `ContDiffWithinAt.differentiableWithinAt`：ContDiffWithinAt.differentiable
WithinAt (h : ContDiffWithinAt 𝕜 n f s x) (hn : n != 0) : DifferentiableWithinAt
 𝕜 f s x
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Icc_mem_nhds`：Icc_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Icc a
 b in 𝓝 x
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `ContDiffOn.derivWithin`：∀ {𝕜 : Type u_1} {F : Type u_2} [inst : Nontrivi
allyNormedField 𝕜] [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] 
{m n : WithT…
· 使用定理 `uniqueDiffOn_Icc`：uniqueDiffOn_Icc {a b : Real} (hab : a < b) : UniqueDi
ffOn Real (Icc a b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `IntervalIntegrable.congr_ae`：IntervalIntegrable.congr_ae {g : Real -> ε}
 (hf : IntervalIntegrable f μ a b) (h : f =ᵐ[μ.restrict (Ι a b)] g) : IntervalIn
tegrable g μ a b
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `ContinuousOn.intervalIntegrable_of_Icc`：ContinuousOn.intervalIntegrable_
of_Icc {u : Real -> E} {a b : Real} (h : a <= b) (hu : ContinuousOn u (Icc a b))
 : IntervalIntegrable u μ a …
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae.congr_simp`：∀ {α : Type u_1} {F : Type u_3} [inst : Fun
Like F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F α]   (μ μ_1 
: F), μ = μ_1 → M…
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
Fundamental theorem of calculus-2: If `f : ℝ → E` is `C^1` on `[a, b]`,
then `∫ y in a..b, deriv f y` equals `f b - f a`.
-/
theorem integral_deriv_of_contDiffOn_Icc (h : ContDiffOn ℝ 1 f (Icc a b)) (hab : a ≤ b) :
    ∫ x in a..b, deriv f x = f b - f a := by
  rcases hab.eq_or_lt with rfl | h'ab
  · simp
  apply integral_eq_sub_of_hasDerivAt_of_le hab h.continuousOn
  · intro x hx
    apply DifferentiableAt.hasDerivAt
    apply ((h x ⟨hx.1.le, hx.2.le⟩).differentiableWithinAt one_ne_zero).differentiableAt
    exact Icc_mem_nhds hx.1 hx.2
  · have := (h.derivWithin (m := 0) (uniqueDiffOn_Icc h'ab) (by simp)).continuousOn
    apply (this.intervalIntegrable_of_Icc (μ := volume) hab).congr_ae
    simp only [hab, uIoc_of_le]
    rw [← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
    exact derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)

/-- Fundamental theorem of calculus-2: If `f : ℝ → E` is `C^1` on `[a, b]`,
then `∫ y in a..b, derivWithin f (Icc a b) y` equals `f b - f a`. -/
/-
**intervalIntegral.integral_derivWithin_Icc_of_contDiffOn_Icc** 是 Mathlib 中的一个定理
，位于命名空间 `intervalIntegral`。
形式化陈述：integral_derivWithin_Icc_of_contDiffOn_Icc (h : ContDiffOn Real 1 f (Icc a
 b)) (hab : a <= b) : ∫ x in a..b, derivWithin f (Icc a b) x = f b - f a
参数：h : ContDiffOn Real 1 f (Icc a b)；hab : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `intervalIntegral.integral_deriv_of_contDiffOn_Icc`：integral_deriv_of_con
tDiffOn_Icc (h : ContDiffOn Real 1 f (Icc a b)) (hab : a <= b) : ∫ x in a..b, de
riv f x = f b - f a
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.restrict_Ioo_eq_restrict_Ioc`：restrict_Ioo_eq_restrict_Ioc
 : μ.restrict (Ioo a b) = μ.restrict (Ioc a b)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.self_mem_ae_restrict`：self_mem_ae_restrict {s} (hs : Measu
rableSet s) : s in ae (μ.restrict s)
· 使用定理 `measurableSet_Ioo`：measurableSet_Ioo [OrderClosedTopology α] : Measurabl
eSet (Ioo a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `derivWithin_of_mem_nhds`：derivWithin_of_mem_nhds (h : s in 𝓝 x) : derivW
ithin f s x = deriv f x
· 使用定理 `Icc_mem_nhds`：Icc_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Icc a
 b in 𝓝 x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
Fundamental theorem of calculus-2: If `f : ℝ → E` is `C^1` on `[a, b]`,
then `∫ y in a..b, derivWithin f (Icc a b) y` equals `f b - f a`.
-/
theorem integral_derivWithin_Icc_of_contDiffOn_Icc (h : ContDiffOn ℝ 1 f (Icc a b)) (hab : a ≤ b) :
    ∫ x in a..b, derivWithin f (Icc a b) x = f b - f a := by
  rw [← integral_deriv_of_contDiffOn_Icc h hab]
  rw [integral_of_le hab, integral_of_le hab]
  apply MeasureTheory.integral_congr_ae
  rw [← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
  exact derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)

/-- Fundamental theorem of calculus-2: If `f : ℝ → E` is `C^1` on `[a, b]`,
then `∫ y in a..b, deriv f y` equals `f b - f a`. -/
/-
**intervalIntegral.integral_deriv_of_contDiffOn_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `
intervalIntegral`。
形式化陈述：integral_deriv_of_contDiffOn_uIcc (h : ContDiffOn Real 1 f (uIcc a b)) : ∫
 x in a..b, deriv f x = f b - f a
参数：h : ContDiffOn Real 1 f (uIcc a b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `intervalIntegral.integral_deriv_of_contDiffOn_Icc`：integral_deriv_of_con
tDiffOn_Icc (h : ContDiffOn Real 1 f (Icc a b)) (hab : a <= b) : ∫ x in a..b, de
riv f x = f b - f a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.uIcc_of_le`：uIcc_of_le (h : a <= b) : [[a, b]] = Icc a b
· 使用定理 `intervalIntegral.integral_symm`：integral_symm (a b) : ∫ x in b..a, f x ∂
μ = -∫ x in a..b, f x ∂μ
· 使用引理 `Set.uIcc_of_ge`：uIcc_of_ge (h : b <= a) : [[a, b]] = Icc b a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `_private.Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff.0.inte
rvalIntegral.integral_deriv_of_contDiffOn_uIcc._abel_1_1`：∀ {E : Type u_1} [inst
 : NormedAddCommGroup E] {f : ℝ → E} {a b : ℝ}, -(f a - f b) = f b - f a

--- 原说明 ---
Fundamental theorem of calculus-2: If `f : ℝ → E` is `C^1` on `[a, b]`,
then `∫ y in a..b, deriv f y` equals `f b - f a`.
-/
theorem integral_deriv_of_contDiffOn_uIcc (h : ContDiffOn ℝ 1 f (uIcc a b)) :
    ∫ x in a..b, deriv f x = f b - f a := by
  rcases le_or_gt a b with hab | hab
  · simp only [uIcc_of_le hab] at h
    exact integral_deriv_of_contDiffOn_Icc h hab
  · simp only [uIcc_of_ge hab.le] at h
    rw [integral_symm, integral_deriv_of_contDiffOn_Icc h hab.le]
    abel

/-- Fundamental theorem of calculus-2: If `f : ℝ → E` is `C^1` on `[a, b]`,
then `∫ y in a..b, derivWithin f (uIcc a b) y` equals `f b - f a`. -/
/-
**intervalIntegral.integral_derivWithin_uIcc_of_contDiffOn_uIcc** 是 Mathlib 中的一个
定理，位于命名空间 `intervalIntegral`。
形式化陈述：integral_derivWithin_uIcc_of_contDiffOn_uIcc (h : ContDiffOn Real 1 f (uIc
c a b)) : ∫ x in a..b, derivWithin f (uIcc a b) x = f b - f a
参数：h : ContDiffOn Real 1 f (uIcc a b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Set.uIcc_of_le`：uIcc_of_le (h : a <= b) : [[a, b]] = Icc a b
· 使用定理 `intervalIntegral.integral_derivWithin_Icc_of_contDiffOn_Icc`：integral_de
rivWithin_Icc_of_contDiffOn_Icc (h : ContDiffOn Real 1 f (Icc a b)) (hab : a <= 
b) : ∫ x in a..b, derivWithin f (Icc a b) x = f b…
· 使用引理 `Set.uIcc_of_ge`：uIcc_of_ge (h : b <= a) : [[a, b]] = Icc b a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `intervalIntegral.integral_symm`：integral_symm (a b) : ∫ x in b..a, f x ∂
μ = -∫ x in a..b, f x ∂μ
· 使用定理 `_private.Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff.0.inte
rvalIntegral.integral_derivWithin_uIcc_of_contDiffOn_uIcc._abel_1_1`：∀ {E : Type
 u_1} [inst : NormedAddCommGroup E] {f : ℝ → E} {a b : ℝ}, -(f a - f b) = f b - 
f a

--- 原说明 ---
Fundamental theorem of calculus-2: If `f : ℝ → E` is `C^1` on `[a, b]`,
then `∫ y in a..b, derivWithin f (uIcc a b) y` equals `f b - f a`.
-/
theorem integral_derivWithin_uIcc_of_contDiffOn_uIcc (h : ContDiffOn ℝ 1 f (uIcc a b)) :
    ∫ x in a..b, derivWithin f (uIcc a b) x = f b - f a := by
  rcases le_or_gt a b with hab | hab
  · simp only [uIcc_of_le hab] at h ⊢
    exact integral_derivWithin_Icc_of_contDiffOn_Icc h hab
  · simp only [uIcc_of_ge hab.le] at h ⊢
    rw [integral_symm, integral_derivWithin_Icc_of_contDiffOn_Icc h hab.le]
    abel

end intervalIntegral

open intervalIntegral

/-
**enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc (h : ContDiffOn Real 1 f (I
cc a b)) (hab : a <= b) : ‖f b - f a‖ₑ <= ∫⁻ x in Icc a b, ‖deriv f x‖ₑ
参数：h : ContDiffOn Real 1 f (Icc a b)；hab : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `edist_eq_enorm_sub`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (
a b : E), edist a b = ‖a - b‖ₑ
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `Isometry.edist_eq`：edist_eq (hf : Isometry f) (x y : α) : edist (f x) (f
 y) = edist x y
· 使用定理 `LinearIsometry.isometry`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5}
 {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} [
inst_2 : Semi…
· 使用定理 `intervalIntegral.integral_deriv_of_contDiffOn_Icc`：integral_deriv_of_con
tDiffOn_Icc (h : ContDiffOn Real 1 f (Icc a b)) (hab : a <= b) : ∫ x in a..b, de
riv f x = f b - f a
· 使用定理 `ContDiff.comp_contDiffOn`：ContDiff.comp_contDiffOn {s : Set E} {g : F ->
 G} {f : E -> F} (hg : ContDiff 𝕜 n g) (hf : ContDiffOn 𝕜 n f s) : ContDiffOn 𝕜 
n (g ∘ f) s
· 使用定理 `LinearIsometry.contDiff`：LinearIsometry.contDiff (f : E ->ₗᵢ[𝕜] F) : Con
tDiff 𝕜 n f
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用定理 `MeasureTheory.restrict_Ioc_eq_restrict_Icc`：restrict_Ioc_eq_restrict_Icc
 : μ.restrict (Ioc a b) = μ.restrict (Icc a b)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.enorm_integral_le_lintegral_enorm`：enorm_integral_le_linte
gral_enorm (f : α -> G) : ‖∫ a, f a ∂μ‖ₑ <= ∫⁻ a, ‖f a‖ₑ ∂μ
· 使用定理 `MeasureTheory.lintegral_mono_ae`：lintegral_mono_ae {f g : α -> Real>=0∞}
 (h : forallᵐ a ∂μ, f a <= g a) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.restrict_Ioo_eq_restrict_Icc`：restrict_Ioo_eq_restrict_Icc
 : μ.restrict (Ioo a b) = μ.restrict (Icc a b)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.self_mem_ae_restrict`：self_mem_ae_restrict {s} (hs : Measu
rableSet s) : s in ae (μ.restrict s)
· 使用定理 `measurableSet_Ioo`：measurableSet_Ioo [OrderClosedTopology α] : Measurabl
eSet (Ioo a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `fderiv_comp_deriv`：fderiv_comp_deriv (hl : DifferentiableAt 𝕜 l (f x)) (
hf : DifferentiableAt 𝕜 f x) : deriv (l ∘ f) x = (fderiv 𝕜 l (f x) : F -> E) (de
riv f x…
· 使用定理 `Differentiable.differentiableAt`：Differentiable.differentiableAt (h : Di
fferentiable 𝕜 f) : DifferentiableAt 𝕜 f x
· 使用定理 `ContDiff.differentiable`：ContDiff.differentiable (h : ContDiff 𝕜 n f) (h
n : n != 0) : Differentiable 𝕜 f
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
（共 52 条，此处仅展示前 30 条）
-/
theorem enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc (h : ContDiffOn ℝ 1 f (Icc a b))
    (hab : a ≤ b) :
    ‖f b - f a‖ₑ ≤ ∫⁻ x in Icc a b, ‖deriv f x‖ₑ := by
  /- We want to write `f b - f a = ∫ x in Icc a b, deriv f x` and use the inequality between
  norm of integral and integral of norm. There is a small difficulty that this formula is not
  true when `E` is not complete, so we need to go first to the completion, and argue there. -/
  let g := UniformSpace.Completion.toComplₗᵢ (𝕜 := ℝ) (E := E)
  have : ‖(g ∘ f) b - (g ∘ f) a‖ₑ = ‖f b - f a‖ₑ := by
    rw [← edist_eq_enorm_sub, Function.comp_def, g.isometry.edist_eq, edist_eq_enorm_sub]
  rw [← this, ← integral_deriv_of_contDiffOn_Icc (g.contDiff.comp_contDiffOn h) hab,
    integral_of_le hab, restrict_Ioc_eq_restrict_Icc]
  apply (enorm_integral_le_lintegral_enorm _).trans
  apply lintegral_mono_ae
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
  rw [fderiv_comp_deriv]; rotate_left
  · exact (g.contDiff.differentiable one_ne_zero).differentiableAt
  · exact (h x ⟨hx.1.le, hx.2.le⟩).contDiffAt (Icc_mem_nhds hx.1 hx.2)
      |>.differentiableAt one_ne_zero
  have : fderiv ℝ g (f x) = g.toContinuousLinearMap := g.toContinuousLinearMap.fderiv
  simp [this]
/-
**enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc** 是 Mathlib 中的一个定理，位于
命名空间 ``。
形式化陈述：enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc (h : ContDiffOn R
eal 1 f (Icc a b)) (hab : a <= b) : ‖f b - f a‖ₑ <= ∫⁻ x in Icc a b, ‖derivWithi
n f (Icc a b) x‖ₑ
参数：h : ContDiffOn Real 1 f (Icc a b)；hab : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc`：enorm_sub_le_lintegral_d
eriv_of_contDiffOn_Icc (h : ContDiffOn Real 1 f (Icc a b)) (hab : a <= b) : ‖f b
 - f a‖ₑ <= ∫⁻ x in Icc a b, ‖deriv …
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.restrict_Ioo_eq_restrict_Icc`：restrict_Ioo_eq_restrict_Icc
 : μ.restrict (Ioo a b) = μ.restrict (Icc a b)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.self_mem_ae_restrict`：self_mem_ae_restrict {s} (hs : Measu
rableSet s) : s in ae (μ.restrict s)
· 使用定理 `measurableSet_Ioo`：measurableSet_Ioo [OrderClosedTopology α] : Measurabl
eSet (Ioo a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `derivWithin_of_mem_nhds`：derivWithin_of_mem_nhds (h : s in 𝓝 x) : derivW
ithin f s x = deriv f x
· 使用定理 `Icc_mem_nhds`：Icc_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Icc a
 b in 𝓝 x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc (h : ContDiffOn ℝ 1 f (Icc a b))
    (hab : a ≤ b) :
    ‖f b - f a‖ₑ ≤ ∫⁻ x in Icc a b, ‖derivWithin f (Icc a b) x‖ₑ := by
  apply (enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc h hab).trans_eq
  apply lintegral_congr_ae
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
  rw [derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)]
