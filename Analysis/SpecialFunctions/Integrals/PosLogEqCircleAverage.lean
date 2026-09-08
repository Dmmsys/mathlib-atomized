/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Complex.Harmonic.MeanValue
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.LogTrigonometric
public import Mathlib.MeasureTheory.Integral.CircleAverage

/-!
# Representation of `log⁺` as a Circle Average

If `a` is any complex number, `circleAverage_log_norm_sub_const_eq_posLog` represents `log⁺ a` as
the circle average of `log ‖· - a‖` over the unit circle.
-/

public section

open Filter Interval intervalIntegral MeasureTheory Metric Real

variable {a c : ℂ} {R : ℝ}

/-!
## Circle Integrability
-/

/--
If `a` is any complex number, the function `(log ‖· - a‖)` is circle integrable over every circle.
-/
@[fun_prop]
/-
**circleIntegrable_log_norm_sub_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：circleIntegrable_log_norm_sub_const (r : Real) : CircleIntegrable (log ‖· 
- a‖) c r
参数：r : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicOn.circleIntegrable_log_norm`：MeromorphicOn.circleIntegrable_
log_norm (hf : MeromorphicOn f (sphere c |R|)) : CircleIntegrable (log ‖f ·‖) c 
R
· 使用定理 `MeromorphicAt.fun_sub`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
x : 𝕜} {f g…
· 使用引理 `MeromorphicAt.id`：id (x : 𝕜) : MeromorphicAt id x
· 使用引理 `MeromorphicAt.const`：const (e : E) (x : 𝕜) : MeromorphicAt (fun _ => e) 
x

--- 原说明 ---
If `a` is any complex number, the function `(log ‖· - a‖)` is circle integrable 
over every circle.
-/
lemma circleIntegrable_log_norm_sub_const (r : ℝ) : CircleIntegrable (log ‖· - a‖) c r :=
  MeromorphicOn.circleIntegrable_log_norm (fun z hz ↦ by fun_prop)

/-!
## Computing `circleAverage (log ‖· - a‖) 0 1` in case where `‖a‖ < 1`.
-/

/--
If `a : ℂ` has norm smaller than one, then `circleAverage (log ‖· - a‖) 0 1` vanishes.
-/
@[simp]
/-
**circleAverage_log_norm_sub_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `a : ℂ` has norm smaller than one, then `circleAverage (log ‖· - a‖) 0 1` van
ishes.
-/
theorem circleAverage_log_norm_sub_const₀ (h : ‖a‖ < 1) : circleAverage (log ‖· - a‖) 0 1 = 0 := by
  calc circleAverage (log ‖· - a‖) 0 1
  _ = circleAverage (log ‖1 - ·⁻¹ * a‖) 0 1 := by
    apply circleAverage_congr_sphere
    intro z hz
    simp_all only [abs_one, mem_sphere_iff_norm, sub_zero]
    congr 1
    have : z ≠ 0 := fun h ↦ by simp [h] at hz
    calc ‖z - a‖
    _ = ‖z⁻¹ * (z - a)‖ := by simp [hz]
    _ = ‖1 - z⁻¹ * a‖ := by field_simp
  _ = 0 := by
    rw [circleAverage_zero_one_congr_inv (f := fun x ↦ log ‖1 - x * a‖),
      InnerProductSpace.HarmonicOnNhd.circleAverage_eq, zero_mul, sub_zero,
      CStarRing.norm_of_mem_unitary (unitary ℂ).one_mem, log_one]
    intro x hx
    have : ‖x * a‖ < 1 := by
      calc ‖x * a‖
      _ = ‖x‖ * ‖a‖ := by simp
      _ ≤ ‖a‖ := mul_le_of_le_one_left (norm_nonneg _) (by aesop)
      _ < 1 := h
    apply AnalyticAt.harmonicAt_log_norm (by fun_prop)
    rw [sub_ne_zero]
    by_contra! hCon
    rwa [← hCon, CStarRing.norm_of_mem_unitary (unitary ℂ).one_mem, lt_self_iff_false] at this

/-!
## Computing `circleAverage (log ‖· - a‖) 0 1` in case where `‖a‖ = 1`.
-/

-- Integral computation used in `circleAverage_log_norm_id_sub_const₁`
/-
**circleAverage_log_norm_sub_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma circleAverage_log_norm_sub_const₁_integral :
    ∫ x in 0..(2 * π), log (4 * sin (x / 2) ^ 2) / 2 = 0 := by
  calc ∫ x in 0..(2 * π), log (4 * sin (x / 2) ^ 2) / 2
  _ = ∫ (x : ℝ) in 0..π, log (4 * sin x ^ 2) := by
    have {x : ℝ} : x / 2 = 2⁻¹ * x := by ring
    rw [intervalIntegral.integral_div, this, inv_mul_integral_comp_div
      (f := fun x ↦ log (4 * sin x ^ 2))]
    simp
  _ = ∫ (x : ℝ) in 0..π, log 4 + 2 * log (sin x) := by
    apply integral_congr_codiscreteWithin
    apply codiscreteWithin_mono (by tauto : Ι 0 π ⊆ Set.univ)
    have : AnalyticOnNhd ℝ (4 * sin · ^ 2) Set.univ := fun _ _ ↦ by fun_prop
    have := this.preimage_zero_mem_codiscrete (x := π / 2)
    simp only [sin_pi_div_two, one_pow, mul_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      Set.preimage_compl, forall_const] at this
    filter_upwards [this] with a ha
    simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff, mul_eq_zero,
      OfNat.ofNat_ne_zero, ne_eq, not_false_eq_true, pow_eq_zero_iff, false_or] at ha
    rw [log_mul (by simp) (by simp_all), log_pow, Nat.cast_ofNat]
  _ = (∫ (x : ℝ) in 0..π, log 4) + 2 * ∫ (x : ℝ) in 0..π, log (sin x) := by
    rw [integral_add _root_.intervalIntegrable_const
      (by apply intervalIntegrable_log_sin.const_mul 2), intervalIntegral.integral_const_mul]
  _ = 0 := by
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, integral_log_sin_zero_pi,
      (by norm_num : (4 : ℝ) = 2 * 2), log_mul two_ne_zero two_ne_zero]
    ring

/--
If `a : ℂ` has norm one, then the circle average `circleAverage (log ‖· - a‖) 0 1` vanishes.
-/
/-
**circleAverage_log_norm_sub_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `a : ℂ` has norm one, then the circle average `circleAverage (log ‖· - a‖) 0 
1` vanishes.
-/
theorem circleAverage_log_norm_sub_const₁ (h : ‖a‖ = 1) :
    circleAverage (log ‖· - a‖) 0 1 = 0 := by
  -- Observing that the problem is rotation invariant, we rotate by an angle of `ζ = - arg a` and
  -- reduce the problem to the case where `a = 1`. The integral can then be evaluated by a direct
  -- computation.
  simp only [circleAverage, mul_inv_rev, smul_eq_mul, mul_eq_zero, inv_eq_zero, OfNat.ofNat_ne_zero,
    or_false]
  right
  obtain ⟨ζ, hζ⟩ : ∃ ζ, a⁻¹ = circleMap 0 1 ζ := by simp [Set.exists_range_iff.1, h]
  calc ∫ x in 0..(2 * π), log ‖circleMap 0 1 x - a‖
  _ = ∫ x in 0..(2 * π), log ‖(circleMap 0 1 ζ) * (circleMap 0 1 x - a)‖ := by
    simp
  _ = ∫ x in 0..(2 * π), log ‖circleMap 0 1 (ζ + x) - (circleMap 0 1 ζ) * a‖ := by
    simp [mul_sub, circleMap, add_mul, Complex.exp_add]
  _ = ∫ x in 0..(2 * π), log ‖circleMap 0 1 (ζ + x) - 1‖ := by
    simp [← hζ, inv_mul_cancel₀ (by aesop : a ≠ 0)]
  _ = ∫ x in 0..(2 * π), log ‖circleMap 0 1 x - 1‖ := by
    have : Function.Periodic (log ‖circleMap 0 1 · - 1‖) (2 * π) :=
      fun x ↦ by simp [periodic_circleMap 0 1 x]
    have := this.intervalIntegral_add_eq (t := 0) (s := ζ)
    simp_all [integral_comp_add_left (log ‖circleMap 0 1 · - 1‖)]
  _ = ∫ x in 0..(2 * π), log (4 * sin (x / 2) ^ 2) / 2 := by
    apply integral_congr
    intro x hx
    simp only
    rw [Complex.norm_def, log_sqrt (circleMap 0 1 x - 1).normSq_nonneg]
    congr
    calc Complex.normSq (circleMap 0 1 x - 1)
    _ = (cos x - 1) * (cos x - 1) + sin x * sin x := by
      simp [circleMap, Complex.normSq_apply]
    _ = sin x ^ 2 + cos x ^ 2 + 1 - 2 * cos x := by
      ring
    _ = 2 - 2 * cos x := by
      rw [sin_sq_add_cos_sq]
      norm_num
    _ = 2 - 2 * cos (2 * (x / 2)) := by
      rw [← mul_div_assoc]
      simp
    _ = 4 - 4 * cos (x / 2) ^ 2 := by
      rw [cos_two_mul]
      ring
    _ = 4 * sin (x / 2) ^ 2 := by
      nth_rw 1 [← mul_one 4, ← sin_sq_add_cos_sq (x / 2)]
      ring
  _ = 0 := circleAverage_log_norm_sub_const₁_integral

/-!
## Computing `circleAverage (log ‖· - a‖) 0 1` in case where `1 < ‖a‖`.
-/

/--
If `a : ℂ` has norm greater than one, then `circleAverage (log ‖· - a‖) 0 1` equals `log ‖a‖`.
-/
@[simp]
/-
**circleAverage_log_norm_sub_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `a : ℂ` has norm greater than one, then `circleAverage (log ‖· - a‖) 0 1` equ
als `log ‖a‖`.
-/
theorem circleAverage_log_norm_sub_const₂ (h : 1 < ‖a‖) :
    circleAverage (log ‖· - a‖) 0 1 = log ‖a‖ := by
  rw [InnerProductSpace.HarmonicOnNhd.circleAverage_eq, zero_sub, norm_neg]
  intro x hx
  apply AnalyticAt.harmonicAt_log_norm (by fun_prop)
  rw [sub_ne_zero]
  by_contra!
  simp_all only [abs_one, Metric.mem_closedBall, dist_zero_right]
  linarith

/-!
## Presentation of `log⁺` in Terms of Circle Averages
-/

/--
The `circleAverage (log ‖· - a‖) 0 1` equals `log⁺ ‖a‖`.
-/
@[simp]
/-
**circleAverage_log_norm_sub_const_eq_posLog** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：circleAverage_log_norm_sub_const_eq_posLog : circleAverage (log ‖· - a‖) 0
 1 = log⁺ ‖a‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `circleAverage_log_norm_sub_const₂`：circleAverage_log_norm_sub_const₂ (h 
: 1 < ‖a‖) : circleAverage (log ‖· - a‖) 0 1 = log ‖a‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.posLog_eq_log`：posLog_eq_log (hx : 1 <= |x|) : log⁺ x = log x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `abs_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (z : E), |‖z‖| 
= ‖z‖
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `circleAverage_log_norm_sub_const₁`：circleAverage_log_norm_sub_const₁ (h 
: ‖a‖ = 1) : circleAverage (log ‖· - a‖) 0 1 = 0
· 使用定理 `Real.posLog_eq_zero_iff`：posLog_eq_zero_iff (x : Real) : log⁺ x = 0 ↔ |x
| <= 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `circleAverage_log_norm_sub_const₀`：circleAverage_log_norm_sub_const₀ (h 
: ‖a‖ < 1) : circleAverage (log ‖· - a‖) 0 1 = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a

--- 原说明 ---
The `circleAverage (log ‖· - a‖) 0 1` equals `log⁺ ‖a‖`.
-/
theorem circleAverage_log_norm_sub_const_eq_posLog :
    circleAverage (log ‖· - a‖) 0 1 = log⁺ ‖a‖ := by
  rcases lt_trichotomy 1 ‖a‖ with h | h | h
  · rw [circleAverage_log_norm_sub_const₂ h]
    apply (posLog_eq_log _).symm
    simp_all [le_of_lt h]
  · rw [eq_comm, circleAverage_log_norm_sub_const₁ h.symm, posLog_eq_zero_iff]
    simp_all
  · rw [eq_comm, circleAverage_log_norm_sub_const₀ h, posLog_eq_zero_iff]
    simp_all [le_of_lt h]

/--
The `circleAverage (log ‖· + a‖) 0 1` equals `log⁺ ‖a‖`.
-/
@[simp]
/-
**circleAverage_log_norm_add_const_eq_posLog** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：circleAverage_log_norm_add_const_eq_posLog : circleAverage (log ‖· + a‖) 0
 1 = log⁺ ‖a‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `circleAverage_log_norm_sub_const_eq_posLog`：circleAverage_log_norm_sub_c
onst_eq_posLog : circleAverage (log ‖· - a‖) 0 1 = log⁺ ‖a‖
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖

--- 原说明 ---
The `circleAverage (log ‖· + a‖) 0 1` equals `log⁺ ‖a‖`.
-/
theorem circleAverage_log_norm_add_const_eq_posLog :
    circleAverage (log ‖· + a‖) 0 1 = log⁺ ‖a‖ := by
  have : (log ‖· + a‖) = (log ‖· - -a‖) := by simp
  simp [this]

/--
Generalization of `circleAverage_log_norm_sub_const_eq_posLog`: The
`circleAverage (log ‖· - a‖) c R` equals `log R + log⁺ (|R|⁻¹ * ‖c - a‖)`.
-/
/-
**circleAverage_log_norm_sub_const_eq_log_radius_add_posLog** 是 Mathlib 中的一个定理，位
于命名空间 ``。
形式化陈述：circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (hR : R != 0) : 
circleAverage (log ‖· - a‖) c R = log R + log⁺ (R⁻¹ * ‖c - a‖)
参数：hR : R != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.circleAverage_eq_circleAverage_zero_one`：circleAverage_eq_circleAve
rage_zero_one : circleAverage f c R = (circleAverage (fun z => f (R * z + c)) 0 
1)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Complex.ofReal_inv`：ofReal_inv (r : Real) : ((r⁻¹ : Real) : Complex) = (
r : Complex)⁻¹
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_sub`：subst_sub {M : Type*} [Ring M] {x₁ x
₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ - X₂ = Y) 
(hy : a * Y = y) : x₁ - …
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_add`：subst_add {M : Type*} [Semiring M] {
x₁ x₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ + X₂ =
 Y) (hy : a * Y = y) : x…
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval_cons_neg`：eval_cons_mul_e
val_cons_neg [CommGroupWithZero M] (n : Int) {e : M} (he : e != 0) {L l l' : NF 
M} (h : L.eval * l.eval = l'.eval) : ((n, e) …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Complex.ofReal_ne_zero`：ofReal_ne_zero {z : Real} : (z : Complex) != 0 ↔
 z != 0
· 使用定理 `not_false_eq_true`：(¬False) = True
（共 109 条，此处仅展示前 30 条）

--- 原说明 ---
Generalization of `circleAverage_log_norm_sub_const_eq_posLog`: The
`circleAverage (log ‖· - a‖) c R` equals `log R + log⁺ (|R|⁻¹ * ‖c - a‖)`.
-/
theorem circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (hR : R ≠ 0) :
    circleAverage (log ‖· - a‖) c R = log R + log⁺ (R⁻¹ * ‖c - a‖) := by
  calc circleAverage (log ‖· - a‖) c R
  _ = circleAverage (fun z ↦ log ‖R * (z + R⁻¹ * (c - a))‖) 0 1 := by
    rw [circleAverage_eq_circleAverage_zero_one]
    congr
    ext z
    congr
    rw [Complex.ofReal_inv R]
    field [Complex.ofReal_ne_zero.mpr hR]
  _ = circleAverage (fun z ↦ log ‖R‖ + log ‖z + R⁻¹ * (c - a)‖) 0 1 := by
    apply circleAverage_congr_codiscreteWithin _ (zero_ne_one' ℝ).symm
    have : {z | ‖z + ↑R⁻¹ * (c - a)‖ ≠ 0} ∈ codiscreteWithin (Metric.sphere (0 : ℂ) |1|) := by
      apply codiscreteWithin_iff_locallyFiniteComplementWithin.2
      intro z hz
      use Set.univ
      simp only [univ_mem, abs_one, Complex.ofReal_inv, ne_eq, norm_eq_zero, Set.univ_inter,
        true_and]
      apply Set.Subsingleton.finite
      intro z₁ hz₁ z₂ hz₂
      simp_all only [ne_eq, abs_one, mem_sphere_iff_norm, sub_zero, Set.mem_sdiff,
        Set.mem_ofPred_eq, Decidable.not_not]
      rw [add_eq_zero_iff_eq_neg.1 hz₁.2, add_eq_zero_iff_eq_neg.1 hz₂.2]
    filter_upwards [this] with z hz
    rw [norm_mul, log_mul (norm_ne_zero_iff.2 (Complex.ofReal_ne_zero.mpr hR)) hz]
    simp
  _ = log R + log⁺ (|R|⁻¹ * ‖c - a‖) := by
    rw [← Pi.add_def, circleAverage_add (circleIntegrable_const (log ‖R‖) 0 1)
      (MeromorphicOn.circleIntegrable_log_norm (fun _ _ ↦ by fun_prop)), circleAverage_const]
    simp
  _ = log R + log⁺ (R⁻¹ * ‖c - a‖) := by
    congr 1
    rcases hR.lt_or_gt with h | h
    · simp [abs_of_neg h]
    · rw [abs_of_pos h]

/--
Trivial corollary of
`circleAverage_log_norm_sub_const_eq_log_radius_add_posLog`: If `u : ℂ` lies within the closed ball
with center `c` and radius `R`, then the circle average
`circleAverage (log ‖· - u‖) c R` equals `log R`.
-/
/-
**circleAverage_log_norm_sub_const_of_mem_closedBall** 是 Mathlib 中的一个引理，位于命名空间 `
`。
形式化陈述：circleAverage_log_norm_sub_const_of_mem_closedBall (hu : a in closedBall c
 |R|) : circleAverage (log ‖· - a‖) c R = log R
参数：hu : a in closedBall c |R|。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Metric.closedBall_zero`：∀ {γ : Type w} [inst : MetricSpace γ] {x : γ}, M
etric.closedBall x 0 = {x}
· 使用定理 `Real.circleAverage_zero`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] 
[inst_1 : NormedSpace ℝ E] {f : ℂ → E} {c : ℂ} [CompleteSpace E],   Real.circleA
verage f c 0 …
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `Real.log_zero`：log_zero : log 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `circleAverage_log_norm_sub_const_eq_log_radius_add_posLog`：circleAverage
_log_norm_sub_const_eq_log_radius_add_posLog (hR : R != 0) : circleAverage (log 
‖· - a‖) c R = log R + log⁺ (R⁻¹ * ‖c - a‖)
· 使用定理 `add_eq_left`：∀ {M : Type u_4} [inst : AddMonoid M] [IsLeftCancelAdd M] {
a b : M}, a + b = a ↔ b = 0
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `Real.posLog_eq_zero_iff`：posLog_eq_zero_iff (x : Real) : log⁺ x = 0 ↔ |x
| <= 1
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用定理 `abs_inv`：abs_inv (a : α) : |a⁻¹| = |a|⁻¹
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `inv_mul_le_one_of_le₀`：inv_mul_le_one_of_le₀ (h : a <= b) (hb : 0 <= b) 
: b⁻¹ * a <= 1
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `dist_eq_norm'`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b :
 E), dist a b = ‖b - a‖
· 使用定理 `Metric.mem_closedBall`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x y 
: α} {ε : ℝ}, y ∈ Metric.closedBall x ε ↔ dist y x ≤ ε
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
Trivial corollary of
`circleAverage_log_norm_sub_const_eq_log_radius_add_posLog`: If `u : ℂ` lies wit
hin the closed ball
with center `c` and radius `R`, then the circle average
`circleAverage (log ‖· - u‖) c R` equals `log R`.
-/
lemma circleAverage_log_norm_sub_const_of_mem_closedBall (hu : a ∈ closedBall c |R|) :
    circleAverage (log ‖· - a‖) c R = log R := by
  by_cases hR : R = 0
  · simp_all
  rw [circleAverage_log_norm_sub_const_eq_log_radius_add_posLog hR, add_eq_left,
    posLog_eq_zero_iff, abs_mul, abs_inv, abs_of_nonneg (norm_nonneg (c - a))]
  rw [mem_closedBall, dist_eq_norm'] at hu
  apply inv_mul_le_one_of_le₀ hu (abs_nonneg R)
