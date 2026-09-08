/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mihai Iancu, Stefan Kebekus, Sebastian Schleissinger, Aristotle AI
-/
module

public import Mathlib.Analysis.Complex.MeanValue
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Poisson Integral Formula

We present two versions of the **Poisson Integral Formula** for ℂ-differentiable functions on
arbitrary disks in the complex plane, formulated with the real part of the Herglotz–Riesz kernel of
integration and with the Poisson kernel, respectively.
-/

public section

open Complex MeasureTheory Metric Real Set

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : ℂ → E} {R : ℝ} {w c : ℂ} {s : Set ℂ}

/-!
## Kernels of Integration

For convenience, this preliminary section discussed the kernels on integration that appear in the
various versions of the Poisson Formula.
-/

/--
The Herglotz-Riesz kernel of integration.
-/
/-
**herglotzRieszKernel** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：herglotzRieszKernel (c w z : Complex) : Complex
参数：c w z : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Herglotz-Riesz kernel of integration.
-/
noncomputable def herglotzRieszKernel (c w z : ℂ) : ℂ :=
  ((z - c) + (w - c)) / ((z - c) - (w - c))
/-
**herglotzRieszKernel_def** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：herglotzRieszKernel_def (c w z : Complex) : herglotzRieszKernel c w z = ((
z - c) + (w - c)) / ((z - c) - (w - c))
参数：c w z : Complex。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma herglotzRieszKernel_def (c w z : ℂ) :
    herglotzRieszKernel c w z = ((z - c) + (w - c)) / ((z - c) - (w - c)) := by rfl
/-
**herglotzRieszKernel_fun_def** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：herglotzRieszKernel_fun_def (c w : Complex) : herglotzRieszKernel c w = fu
n z => ((z - c) + (w - c)) / ((z - c) - (w - c))
参数：c w : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `herglotzRieszKernel_def`：herglotzRieszKernel_def (c w z : Complex) : her
glotzRieszKernel c w z = ((z - c) + (w - c)) / ((z - c) - (w - c))
-/
lemma herglotzRieszKernel_fun_def (c w : ℂ) :
    herglotzRieszKernel c w = fun z ↦ ((z - c) + (w - c)) / ((z - c) - (w - c)) := by
  ext z
  exact herglotzRieszKernel_def c w z
/-
**herglotzRieszKernel_add_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：herglotzRieszKernel_add_const (c w z : Complex) : herglotzRieszKernel c w 
(z + c) = herglotzRieszKernel 0 (w - c) z
参数：c w z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `herglotzRieszKernel_fun_def`：herglotzRieszKernel_fun_def (c w : Complex)
 : herglotzRieszKernel c w = fun z => ((z - c) + (w - c)) / ((z - c) - (w - c))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma herglotzRieszKernel_add_const (c w z : ℂ) :
    herglotzRieszKernel c w (z + c) = herglotzRieszKernel 0 (w - c) z := by
  simp [herglotzRieszKernel_fun_def]

/--
The Poisson kernel of integration.
-/
/-
**poissonKernel** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：poissonKernel (c w z : Complex) : Real
参数：c w z : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Poisson kernel of integration.
-/
noncomputable def poissonKernel (c w z : ℂ) : ℝ :=
  (‖z - c‖ ^ 2 - ‖w - c‖ ^ 2) / ‖(z - c) - (w - c)‖ ^ 2
/-
**poissonKernel_def** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：poissonKernel_def (c w z : Complex) : poissonKernel c w z = (‖z - c‖ ^ 2 -
 ‖w - c‖ ^ 2) / ‖(z - c) - (w - c)‖ ^ 2
参数：c w z : Complex。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma poissonKernel_def (c w z : ℂ) :
    poissonKernel c w z = (‖z - c‖ ^ 2 - ‖w - c‖ ^ 2) / ‖(z - c) - (w - c)‖ ^ 2 := by rfl
/-
**poissonKernel_eq_re_herglotzRieszKernel_aux** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma poissonKernel_eq_re_herglotzRieszKernel_aux {a b : ℂ} :
    ((a + b) / (a - b)).re = (‖a‖ ^ 2 - ‖b‖ ^ 2) / ‖a - b‖ ^ 2 := by
  rw [div_re, normSq_eq_norm_sq (a - b), ← add_div, add_re, sub_re, add_im, sub_im]
  calc ((a.re + b.re) * (a.re - b.re) + (a.im + b.im) * (a.im - b.im)) / ‖a - b‖ ^ 2
    _ = ((a.re * a.re + a.im * a.im) - (b.re * b.re + b.im * b.im)) / ‖a - b‖ ^ 2 := by
      congr! 1; ring
    _ = (‖a‖ ^ 2 - ‖b‖ ^ 2) / ‖a - b‖ ^ 2 := by
      simp [← normSq_apply, normSq_eq_norm_sq]

/--
Companion theorem to the Poisson Integral Formula: The real part of the Herglotz–Riesz kernel and
the Poisson kernel agree on the path of integration.
-/
/-
**poissonKernel_eq_re_herglotzRieszKernel** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：poissonKernel_eq_re_herglotzRieszKernel {c w : Complex} : poissonKernel c 
w = Complex.re ∘ herglotzRieszKernel c w
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `_private.Mathlib.Analysis.Complex.Poisson.0.poissonKernel.eq_1`：∀ (c w z
 : ℂ), poissonKernel c w z = (‖z - c‖ ^ 2 - ‖w - c‖ ^ 2) / ‖z - c - (w - c)‖ ^ 2
· 使用定理 `_private.Mathlib.Analysis.Complex.Poisson.0.herglotzRieszKernel.eq_1`：∀ 
(c w z : ℂ), herglotzRieszKernel c w z = (z - c + (w - c)) / (z - c - (w - c))
· 使用定理 `_private.Mathlib.Analysis.Complex.Poisson.0.poissonKernel_eq_re_herglotz
RieszKernel_aux`：∀ {a b : ℂ}, ((a + b) / (a - b)).re = (‖a‖ ^ 2 - ‖b‖ ^ 2) / ‖a 
- b‖ ^ 2

--- 原说明 ---
Companion theorem to the Poisson Integral Formula: The real part of the Herglotz
–Riesz kernel and
the Poisson kernel agree on the path of integration.
-/
lemma poissonKernel_eq_re_herglotzRieszKernel {c w : ℂ} :
    poissonKernel c w = Complex.re ∘ herglotzRieszKernel c w := by
  ext z
  rw [Function.comp_apply, poissonKernel, herglotzRieszKernel,
    poissonKernel_eq_re_herglotzRieszKernel_aux]
/-
**re_herglotzRieszKernel_le_aux** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma re_herglotzRieszKernel_le_aux (φ θ r R : ℝ) (h₁ : 0 < r) (h₂ : r < R) :
    ((R * exp (θ * I) + r * exp (φ * I)) / (R * exp (θ * I) - r * exp (φ * I))).re
      ≤ (R + r) / (R - r) := by
  rw [div_eq_mul_inv]
  have h_cos : (R ^ 2 + r ^ 2 - 2 * R * r * Real.cos (θ - φ)) ≥ (R - r) ^ 2 := by
    nlinarith [mul_pos h₁ (sub_pos.mpr h₂), Real.cos_le_one (θ - φ)]
  have h_subst :
      (R ^ 2 - r ^ 2) / (R ^ 2 + r ^ 2 - 2 * R * r * Real.cos (θ - φ)) ≤ (R + r) / (R - r) := by
    rw [div_le_div_iff₀] <;> nlinarith [mul_pos h₁ (sub_pos.mpr h₂)]
  convert h_subst
  rw [← div_eq_mul_inv, poissonKernel_eq_re_herglotzRieszKernel_aux]
  suffices (R * R * normSq (cexp (θ * I)) + r * r * normSq (cexp (φ * I)) -
      2 * (R * Real.cos θ * (r * Real.cos φ) + R * Real.sin θ * (r * Real.sin φ))) =
      (R ^ 2 + r ^ 2 - 2 * R * r * Real.cos (θ - φ)) by
    rw [← this]; simp [← normSq_eq_norm_sq, Complex.normSq_sub]
  simp [normSq_eq_norm_sq, Real.cos_sub]
  ring

/--
Companion theorem to the Poisson Integral Formula: Upper estimate for the real part of the
Herglotz-Riesz kernel.
-/
/-
**re_herglotzRieszKernel_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：re_herglotzRieszKernel_le {c z : Complex} (hz : z in sphere c R) (hw : w i
n ball c R) : ((z - c + (w - c)) / ((z - c) - (w - c))).re <= (R + ‖w - c‖) / (R
 - ‖w - c‖)
参数：hz : z in sphere c R；hw : w in ball c R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_sub_sub_cancel_right`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : 
G), a - c - (b - c) = a - b
· 使用定理 `Complex.norm_mul_exp_arg_mul_I`：norm_mul_exp_arg_mul_I (x : Complex) : ‖
x‖ * exp (arg x * I) = x
· 使用定理 `_private.Mathlib.Analysis.Complex.Poisson.0.re_herglotzRieszKernel_le_au
x`：∀ (φ θ r R : ℝ),   0 < r →     r < R →       ((↑R * Complex.exp (↑θ * Complex
.I) + ↑r * Complex.exp (↑φ * Complex.I)) /             (↑R * Co…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_ball_iff_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] {a
 b : E} {r : ℝ}, b ∈ Metric.ball a r ↔ ‖b - a‖ < r
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Companion theorem to the Poisson Integral Formula: Upper estimate for the real p
art of the
Herglotz-Riesz kernel.
-/
theorem re_herglotzRieszKernel_le {c z : ℂ} (hz : z ∈ sphere c R) (hw : w ∈ ball c R) :
    ((z - c + (w - c)) / ((z - c) - (w - c))).re ≤ (R + ‖w - c‖) / (R - ‖w - c‖) := by
  obtain ⟨η₀, rfl, η₂⟩ : 0 < R ∧ R = ‖z - c‖ ∧ z - c ≠ 0 := by
    grind [ball_eq_empty, mem_sphere, dist_eq_norm, norm_pos_iff]
  by_cases h₁w : ‖w - c‖ = 0
  · aesop
  simpa using re_herglotzRieszKernel_le_aux (w - c).arg (z - c).arg ‖w - c‖ ‖z - c‖
    (by simpa using h₁w) (mem_ball_iff_norm.1 hw)
/-
**le_re_herglotzRieszKernel_aux** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma le_re_herglotzRieszKernel_aux (θ φ r R : ℝ) (h₁ : 0 < r) (h₂ : r < R) :
    (R - r) / (R + r)
      ≤ ((R * exp (θ * I) + r * exp (φ * I)) / (R * exp (θ * I) - r * exp (φ * I))).re := by
  rw [poissonKernel_eq_re_herglotzRieszKernel_aux]
  simp only [Complex.norm_mul, norm_real, norm_eq_abs, norm_exp_ofReal_mul_I, mul_one, sq_abs,
    sq_sub_sq]
  field_simp [sub_pos.mpr h₂]
  simp only [mul_comm I] -- make sure exponents are in the form `?angle * I` for the simplification
  rw [div_le_div_iff₀ (by positivity [h₁.trans h₂]) ?hpos, ← normSq_eq_norm_sq, normSq_sub,
    normSq_eq_norm_sq, normSq_eq_norm_sq]
  case hpos => simpa [sq_pos_iff, sub_eq_zero] using
    (mt <| congr_arg (‖·‖)) <| by simpa [abs_of_pos, h₁, h₁.trans h₂] using h₂.ne'
  have key := calc
    (-(R * cexp (θ * I) * (starRingEnd ℂ) (r * cexp (φ * I)))).re ≤ _ := re_le_norm _
    _ ≤ R * r := by simp [abs_of_pos, h₁, h₁.trans h₂]
  simpa using calc
    R ^ 2 + r ^ 2 - 2 * (R * cexp (θ * I) * (starRingEnd ℂ) (r * cexp (φ * I))).re
    _ ≤ R ^ 2 + r ^ 2 + 2 * (R * r) := by rw [sub_eq_add_neg, ← mul_neg, ← neg_re]; gcongr
    _ = (R + r) * (R + r) := by ring

/--
Companion theorem to the Poisson Integral Formula: Lower estimate for the real part of the
Herglotz-Riesz kernel.
-/
/-
**le_re_herglotzRieszKernel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_re_herglotzRieszKernel {c z : Complex} (hz : z in sphere c R) (hw : w i
n ball c R) : (R - ‖w - c‖) / (R + ‖w - c‖) <= ((z - c + (w - c)) / ((z - c) - (
w - c))).re
参数：hz : z in sphere c R；hw : w in ball c R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `sub_sub_sub_cancel_right`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : 
G), a - c - (b - c) = a - b
· 使用定理 `Complex.norm_mul_exp_arg_mul_I`：norm_mul_exp_arg_mul_I (x : Complex) : ‖
x‖ * exp (arg x * I) = x
· 使用定理 `_private.Mathlib.Analysis.Complex.Poisson.0.le_re_herglotzRieszKernel_au
x`：∀ (θ φ r R : ℝ),   0 < r →     r < R →       (R - r) / (R + r) ≤         ((↑R
 * Complex.exp (↑θ * Complex.I) + ↑r * Complex.exp (↑φ * Comple…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_ball_iff_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] {a
 b : E} {r : ℝ}, b ∈ Metric.ball a r ↔ ‖b - a‖ < r
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Companion theorem to the Poisson Integral Formula: Lower estimate for the real p
art of the
Herglotz-Riesz kernel.
-/
theorem le_re_herglotzRieszKernel {c z : ℂ} (hz : z ∈ sphere c R) (hw : w ∈ ball c R) :
    (R - ‖w - c‖) / (R + ‖w - c‖) ≤ ((z - c + (w - c)) / ((z - c) - (w - c))).re := by
  obtain ⟨η₀, rfl, η₂⟩ : 0 < R ∧ R = ‖z - c‖ ∧ z - c ≠ 0 := by
    grind [ball_eq_empty, mem_sphere, dist_eq_norm, norm_pos_iff]
  by_cases h₁w : ‖w - c‖ = 0
  · aesop
  simpa using le_re_herglotzRieszKernel_aux (z - c).arg (w - c).arg ‖w - c‖ ‖z - c‖
    (by simpa using h₁w) (mem_ball_iff_norm.1 hw)

/--
The Herglotz–Riesz kernel `herglotzRieszKernel c w` is continuous on the circle `sphere c |R|`
whenever `w ∈ ball c R`.
-/
/-
**continuousOn_herglotzRieszKernel_sphere** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : ℝ} {w c : ℂ}, w ∈ Metric.ball c R → ContinuousOn (herglotzRieszKern
el c w) (Metric.sphere c |R|)
参数：herglotzRieszKernel c w；Metric.sphere c |R|。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.div`：ContinuousOn.div (hf : ContinuousOn f s) (hg : Continu
ousOn g s) (h₀ : forall x in s, g x != 0) : ContinuousOn (f / g) s
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `ContinuousOn.add_const`：∀ {M : Type u_1} [inst : TopologicalSpace M] [in
st_1 : Add M] [SeparatelyContinuousAdd M] {X : Type u_2}   [inst_3 : Topological
Space X] {f …
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
· 使用定理 `ContinuousOn.fun_sub`：∀ {G : Type u_1} {X : Type u_3} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f 
g : X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s

--- 原说明 ---
The Herglotz–Riesz kernel `herglotzRieszKernel c w` is continuous on the circle 
`sphere c |R|`
whenever `w ∈ ball c R`.
-/
@[fun_prop] lemma continuousOn_herglotzRieszKernel_sphere (hw : w ∈ ball c R) :
    ContinuousOn (herglotzRieszKernel c w) (sphere c |R|) := by
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  grind [mem_sphere, mem_ball, le_abs_self R]

/--
Taking real parts commutes with the Herglotz–Riesz kernel integral of a real-valued
circle-integrable function.
-/
/-
**re_circleAverage_herglotzRieszKernel_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：re_circleAverage_herglotzRieszKernel_smul {g : Complex -> Real} (hg : Circ
leIntegrable g 0 R) (hw : w in ball 0 R) : (circleAverage (fun ζ => herglotzRies
zKernel 0 w ζ • (g ζ : Complex)) 0 R).re = circleAverage ((Complex.re ∘ herglotz
RieszKernel 0 w) • g) 0 R
参数：hg : CircleIntegrable g 0 R；hw : w in ball 0 R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `ContinuousLinearMap.integrable_comp`：ContinuousLinearMap.integrable_comp
 {φ : α -> H} (L : H ->SL[σ] E) (φ_int : Integrable φ μ) : Integrable (fun a : α
 => L (φ a)) μ
· 使用定理 `CircleIntegrable.continuousOn_smul`：continuousOn_smul {f : Complex -> F}
 {g : Complex -> 𝕜} (hf : CircleIntegrable f c R) (hg : ContinuousOn g (sphere c
 |R|)) : CircleIntegrabl…
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `continuousOn_herglotzRieszKernel_sphere`：∀ {R : ℝ} {w c : ℂ}, w ∈ Metric
.ball c R → ContinuousOn (herglotzRieszKernel c w) (Metric.sphere c |R|)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.circleAverage_comp_comm`：∀ {E : Type u_1} [inst : No
rmedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {F : Type u_2} [inst_2 : NormedAd
dCommGroup F]   [inst_3 : NormedS…
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Taking real parts commutes with the Herglotz–Riesz kernel integral of a real-val
ued
circle-integrable function.
-/
theorem re_circleAverage_herglotzRieszKernel_smul {g : ℂ → ℝ}
    (hg : CircleIntegrable g 0 R) (hw : w ∈ ball 0 R) :
    (circleAverage (fun ζ ↦ herglotzRieszKernel 0 w ζ • (g ζ : ℂ)) 0 R).re
      = circleAverage ((Complex.re ∘ herglotzRieszKernel 0 w) • g) 0 R := by
  have h₁ : CircleIntegrable (fun ζ ↦ (g ζ : ℂ)) 0 R := by
    simp only [CircleIntegrable, intervalIntegrable_iff] at hg ⊢
    exact Complex.ofRealCLM.integrable_comp hg
  have h₂ : CircleIntegrable (fun ζ ↦ herglotzRieszKernel 0 w ζ • (g ζ : ℂ)) 0 R :=
    h₁.continuousOn_smul (continuousOn_herglotzRieszKernel_sphere hw)
  calc (circleAverage (fun ζ ↦ herglotzRieszKernel 0 w ζ • (g ζ : ℂ)) 0 R).re
      = circleAverage (Complex.reCLM ∘ fun ζ ↦ herglotzRieszKernel 0 w ζ • (g ζ : ℂ)) 0 R :=
        (Complex.reCLM.circleAverage_comp_comm h₂).symm
    _ = circleAverage ((Complex.re ∘ herglotzRieszKernel 0 w) • g) 0 R := by
        simp [Function.comp_def, Complex.mul_re, Pi.mul_def]

/-!
## Integral Formulas
-/

-- Trigonometric identity used in the computation of
-- `DiffContOnCl.circleAverage_re_smul_on_ball_zero`.
/-
**circleAverage_re_smul_on_ball_zero_aux** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma circleAverage_re_smul_on_ball_zero_aux {φ θ : ℝ} {r : ℝ} :
    (R * exp (θ * I)) / (R * exp (θ * I) - r * exp (φ * I)) - (r * exp (θ * I))
      / (r * exp (θ * I) - R * exp (φ * I))
      = ((R * exp (θ * I) + r * exp (φ * I)) / (R * exp (θ * I) - r * exp (φ * I))).re := by
  simp only [Complex.ext_iff, exp_ofReal_mul_I, add_re, sub_re, mul_re, div_re, ofReal_re,
    I_re, I_im, add_im, sub_im, mul_im, div_im, ofReal_im, normSq_apply]
  grind [Real.sin_sq]

-- Version of `DiffContOnCl.circleAverage_re_smul` in case where the center of the ball is zero.
/-
**DiffContOnCl.circleAverage_re_smul_on_ball_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma DiffContOnCl.circleAverage_re_smul_on_ball_zero [CompleteSpace E]
    (hf : DiffContOnCl ℂ f (ball 0 R)) (hw : w ∈ ball 0 R) :
    Real.circleAverage (fun z ↦ ((z + w) / (z - w)).re • f z) 0 R = f w := by
  -- Trivial case: nonpositive radius
  rcases le_or_gt R 0 with hR | hR
  · simp_all [ball_eq_empty.2 hR]
  -- Trivial case: w is at the center
  obtain rfl | h₁w := eq_or_ne w 0
  · refine (circleAverage_congr_sphere fun z hz ↦ ?_).trans (abs_of_pos hR ▸ hf |>.circleAverage)
    rw [abs_of_pos hR] at hz
    simp [div_self (a := z) (by aesop)]
  -- General case: positive radius, w is not at the center
  let W := R * exp (w.arg * I)
  let q := ‖w‖ / R
  have h₁q : 0 < q := by positivity
  have h₂q : q < 1 := by simpa [← div_lt_one hR] using hw
  -- Lemma used by automatisation tactics to ensure that quotients are non-zero.
  have η₀ {x : ℂ} (h : ‖x‖ ≤ R) : q * x - W ≠ 0 := by
    suffices ‖q * x‖ < ‖W‖ by grind
    calc
      ‖q * x‖ = q * ‖x‖ := by simp [abs_of_pos h₁q]
      _ ≤ q * R := by gcongr
      _ < 1 * R := by gcongr
      _ = ‖W‖ := by simp [W, abs_of_pos hR]
  have h0 : ∮ (z : ℂ) in C(0, R), z⁻¹ • ((q * z) / (q * z - W)) • f z = 0 := calc
    ∮ (z : ℂ) in C(0, R), z⁻¹ • ((q * z) / (q * z - W)) • f z
    _ = ∮ (z : ℂ) in C(0, R), (q / (q * z - W)) • f z := by
      apply circleIntegral.integral_congr hR.le fun z hz ↦ ?_
      have hz : z ≠ 0 := by aesop
      match_scalars
      field
    _ = 0 := by
      apply DifferentiableOn.diffContOnCl ?_ |>.smul hf |>.circleIntegral_eq_zero hR.le
      rw [closure_ball 0 hR.ne']
      fun_prop (disch := aesop)
  -- Main computation starts here
  calc Real.circleAverage (fun z ↦ ((z + w) / (z - w)).re • f z) 0 R
    _ = Real.circleAverage (fun z ↦ (z / (z - w) - (q • z) / (q • z - W)) • f z) 0 R := by
      apply circleAverage_congr_sphere fun z hz ↦ ?_
      have hzR : ‖z‖ = R := by simpa [abs_of_pos hR] using hz
      match_scalars
      simp only [q, W, real_smul, ofReal_div, coe_algebraMap, mul_one]
      rw [← norm_mul_exp_arg_mul_I w, ← norm_mul_exp_arg_mul_I z, hzR,
        ← circleAverage_re_smul_on_ball_zero_aux, norm_mul_exp_arg_mul_I w]
      field [hR.ne.symm]
    _ = Real.circleAverage (fun z ↦ (z / (z - w)) • f z) 0 R
        - Real.circleAverage (fun z ↦ ((q • z) / (q • z - W)) • f z) 0 R := by
      simp_rw [sub_smul]
      have h₁ : ∀ z ∈ sphere 0 R, z - w ≠ 0 := by aesop (add simp sub_eq_zero)
      have h₃ : ContinuousOn f (sphere 0 R) :=
        hf.2.mono <| sphere_subset_closedBall.trans_eq (closure_ball 0 hR.ne').symm
      rw [circleAverage_fun_sub]
      all_goals
        apply ContinuousOn.circleIntegrable hR.le
        fun_prop (disch := aesop)
    _ = f w := by
      rw [← abs_of_pos hR] at hw hf
      simp [← hf.circleAverage_smul_div hw, circleAverage_eq_circleIntegral (ne_of_lt hR).symm, h0]

/--
**Poisson integral formula** for ℂ-differentiable functions on arbitrary disks in the complex plane,
formulated with the real part of the Herglotz–Riesz kernel of integration.
-/
/-
**DiffContOnCl.circleAverage_re_herglotzRieszKernel_smul** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：DiffContOnCl.circleAverage_re_herglotzRieszKernel_smul [CompleteSpace E] {
c : Complex} (hf : DiffContOnCl Complex f (ball c R)) (hw : w in ball c R) : Rea
l.circleAverage ((re ∘ herglotzRieszKernel c w) • f) c R = f w
参数：hf : DiffContOnCl Complex f (ball c R)；hw : w in ball c R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.ball_eq_empty`：ball_eq_empty : ball x ε = ∅ ↔ ε <= 0
· 使用定理 `DiffContOnCl.comp`：comp {g : G -> E} {t : Set G} (hf : DiffContOnCl 𝕜 f 
s) (hg : DiffContOnCl 𝕜 g t) (h : MapsTo g t s) : DiffContOnCl 𝕜 (f ∘ g) t
· 使用定理 `DifferentiableOn.diffContOnCl`：DifferentiableOn.diffContOnCl (h : Differ
entiableOn 𝕜 f (closure s)) : DiffContOnCl 𝕜 f s
· 使用定理 `DifferentiableOn.add_const`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {F : Type u_…
· 使用定理 `differentiableOn_id`：differentiableOn_id : DifferentiableOn 𝕜 id s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `dist_add_self_left`：∀ {E : Type u_2} [inst : SeminormedAddCommGroup E] (
a b : E), dist (b + a) a = ‖b‖
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_ball_iff_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] {a
 b : E} {r : ℝ}, b ∈ Metric.ball a r ↔ ‖b - a‖ < r
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `herglotzRieszKernel_def`：herglotzRieszKernel_def (c w z : Complex) : her
glotzRieszKernel c w z = ((z - c) + (w - c)) / ((z - c) - (w - c))
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `_private.Mathlib.Analysis.Complex.Poisson.0.DiffContOnCl.circleAverage_r
e_smul_on_ball_zero`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℂ E] {f : ℂ → E} {R : ℝ} {w : ℂ} [CompleteSpace E],   DiffContOnCl ℂ f
 …

--- 原说明 ---
**Poisson integral formula** for ℂ-differentiable functions on arbitrary disks i
n the complex plane,
formulated with the real part of the Herglotz–Riesz kernel of integration.
-/
theorem DiffContOnCl.circleAverage_re_herglotzRieszKernel_smul [CompleteSpace E] {c : ℂ}
    (hf : DiffContOnCl ℂ f (ball c R)) (hw : w ∈ ball c R) :
    Real.circleAverage ((re ∘ herglotzRieszKernel c w) • f) c R = f w := by
  rcases le_or_gt R 0 with hR | hR
  · simp_all [ball_eq_empty.2 hR]
  have h₁g : DiffContOnCl ℂ (fun z ↦ f (z + c)) (ball 0 R) :=
    hf.comp (DifferentiableOn.diffContOnCl <| by fun_prop) (by intro; aesop)
  have h₂g : w - c ∈ ball 0 R := by simpa using mem_ball_iff_norm.1 hw
  simpa [← circleAverage_map_add_const, herglotzRieszKernel_def]
    using circleAverage_re_smul_on_ball_zero h₁g h₂g

/--
**Poisson integral formula** for ℂ-differentiable functions on arbitrary disks in the complex plane,
formulated with the real part of the Herglotz–Riesz kernel of integration expanded.
-/
/-
**DiffContOnCl.circleAverage_re_herglotzRieszKernel_smul'** 是 Mathlib 中的一个定理，位于命
名空间 ``。
形式化陈述：DiffContOnCl.circleAverage_re_herglotzRieszKernel_smul' [CompleteSpace E] 
{c : Complex} (hf : DiffContOnCl Complex f (ball c R)) (hw : w in ball c R) : Re
al.circleAverage (fun z => ((z - c + (w - c)) / ((z - c) - (w - c))).re • f z) c
 R = f w
参数：hf : DiffContOnCl Complex f (ball c R)；hw : w in ball c R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DiffContOnCl.circleAverage_re_herglotzRieszKernel_smul`：DiffContOnCl.cir
cleAverage_re_herglotzRieszKernel_smul [CompleteSpace E] {c : Complex} (hf : Dif
fContOnCl Complex f (ball c R)) (hw : w in b…

--- 原说明 ---
**Poisson integral formula** for ℂ-differentiable functions on arbitrary disks i
n the complex plane,
formulated with the real part of the Herglotz–Riesz kernel of integration expand
ed.
-/
theorem DiffContOnCl.circleAverage_re_herglotzRieszKernel_smul' [CompleteSpace E] {c : ℂ}
    (hf : DiffContOnCl ℂ f (ball c R)) (hw : w ∈ ball c R) :
    Real.circleAverage (fun z ↦ ((z - c + (w - c)) / ((z - c) - (w - c))).re • f z) c R = f w :=
  hf.circleAverage_re_herglotzRieszKernel_smul hw

/--
**Poisson integral formula** for ℂ-differentiable functions on arbitrary disks in the complex plane,
formulated with the Poisson kernel of integration.
-/
/-
**DiffContOnCl.circleAverage_poissonKernel_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DiffContOnCl.circleAverage_poissonKernel_smul [CompleteSpace E] {c : Compl
ex} (hf : DiffContOnCl Complex f (ball c R)) (hw : w in ball c R) : Real.circleA
verage (poissonKernel c w • f) c R = f w
参数：hf : DiffContOnCl Complex f (ball c R)；hw : w in ball c R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `poissonKernel_eq_re_herglotzRieszKernel`：poissonKernel_eq_re_herglotzRie
szKernel {c w : Complex} : poissonKernel c w = Complex.re ∘ herglotzRieszKernel 
c w
· 使用定理 `DiffContOnCl.circleAverage_re_herglotzRieszKernel_smul`：DiffContOnCl.cir
cleAverage_re_herglotzRieszKernel_smul [CompleteSpace E] {c : Complex} (hf : Dif
fContOnCl Complex f (ball c R)) (hw : w in b…

--- 原说明 ---
**Poisson integral formula** for ℂ-differentiable functions on arbitrary disks i
n the complex plane,
formulated with the Poisson kernel of integration.
-/
theorem DiffContOnCl.circleAverage_poissonKernel_smul [CompleteSpace E] {c : ℂ}
    (hf : DiffContOnCl ℂ f (ball c R)) (hw : w ∈ ball c R) :
    Real.circleAverage (poissonKernel c w • f) c R = f w := by
  simp_rw [poissonKernel_eq_re_herglotzRieszKernel]
  apply hf.circleAverage_re_herglotzRieszKernel_smul hw

/--
**Poisson integral formula** for ℂ-differentiable functions on arbitrary disks in the complex plane,
formulated with the Poisson kernel of integration expanded.
-/
/-
**DiffContOnCl.circleAverage_poissonKernel_smul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DiffContOnCl.circleAverage_poissonKernel_smul' [CompleteSpace E] {c : Comp
lex} (hf : DiffContOnCl Complex f (ball c R)) (hw : w in ball c R) : Real.circle
Average (fun z => ((‖z - c‖ ^ 2 - ‖w - c‖ ^ 2) / ‖(z - c) - (w - c)‖ ^ 2) • f z)
 c R = f w
参数：hf : DiffContOnCl Complex f (ball c R)；hw : w in ball c R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DiffContOnCl.circleAverage_poissonKernel_smul`：DiffContOnCl.circleAverag
e_poissonKernel_smul [CompleteSpace E] {c : Complex} (hf : DiffContOnCl Complex 
f (ball c R)) (hw : w in ball c R) …

--- 原说明 ---
**Poisson integral formula** for ℂ-differentiable functions on arbitrary disks i
n the complex plane,
formulated with the Poisson kernel of integration expanded.
-/
theorem DiffContOnCl.circleAverage_poissonKernel_smul' [CompleteSpace E] {c : ℂ}
    (hf : DiffContOnCl ℂ f (ball c R)) (hw : w ∈ ball c R) :
    Real.circleAverage (fun z ↦ ((‖z - c‖ ^ 2 - ‖w - c‖ ^ 2) / ‖(z - c) - (w - c)‖ ^ 2) • f z) c R
      = f w := by
  apply hf.circleAverage_poissonKernel_smul hw

/-!
## Derivative of the Herglotz–Riesz Kernel Integral
-/

/-
For `w ∈ ball c R`, there is a radius `d > 0` such that `ball w d ⊆ ball c R` and all points of
`ball w d` keep distance at least `d` from the circle `sphere c R`.
-/
/-
**exists_ball_subset_forall_le_norm_circleMap_sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `w ∈ ball c R`, there is a radius `d > 0` such that `ball w d ⊆ ball c R` an
d all points of
`ball w d` keep distance at least `d` from the circle `sphere c R`.
-/
private lemma exists_ball_subset_forall_le_norm_circleMap_sub (hw : w ∈ ball c R) :
    ∃ d > 0, ball w d ⊆ ball c R ∧ ∀ x ∈ ball w d, ∀ θ : ℝ, d ≤ ‖circleMap c R θ - x‖ := by
  have : Disjoint {w} (ball c R)ᶜ := by simpa
  obtain ⟨d, hd, h_disj⟩ := this.exists_thickenings isCompact_singleton isOpen_ball.isClosed_compl
  refine ⟨d, hd, ?_, ?_⟩ <;> grw [thickening_singleton] at h_disj
  · simpa using (h_disj.mono_right (self_subset_thickening hd _)).subset_compl_left
  · intro x hx θ
    have := h_disj.subset_compl_right hx
    simp only [mem_compl_iff, mem_thickening_iff, mem_ball, not_lt, not_exists, not_and] at this
    simpa [← dist_eq_norm'] using this (circleMap c R θ) (by simp [dist_eq_norm, le_abs_self])

/--
**Derivative of the Herglotz–Riesz kernel integral**: if `f` is circle integrable and `w` lies
inside the circle, then `w ↦ circleAverage (fun ζ ↦ herglotzRieszKernel 0 w ζ • f ζ) 0 R` has
derivative `circleAverage (fun ζ ↦ (2 * ζ / (ζ - w) ^ 2) • f ζ) 0 R` at `w`.
-/
/-
**hasDerivAt_circleAverage_herglotzRieszKernel_smul** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：hasDerivAt_circleAverage_herglotzRieszKernel_smul (hg : CircleIntegrable f
 0 R) (hw : w in ball 0 R) : HasDerivAt (fun w => circleAverage (fun ζ => herglo
tzRieszKernel 0 w ζ • f ζ) 0 R) (circleAverage (fun ζ => (2 * ζ / (ζ - w) ^ 2) •
 f ζ) 0 R) w
参数：hg : CircleIntegrable f 0 R；hw : w in ball 0 R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.pos_of_mem_ball`：pos_of_mem_ball (hy : y in ball x ε) : 0 < ε
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `_private.Mathlib.Analysis.Complex.Poisson.0.exists_ball_subset_forall_le
_norm_circleMap_sub`：∀ {R : ℝ} {w c : ℂ},   w ∈ Metric.ball c R →     ∃ d > 0, M
etric.ball w d ⊆ Metric.ball c R ∧ ∀ x ∈ Metric.ball w d, ∀ (θ : ℝ), d ≤ ‖circle
M…
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `intervalIntegrable_iff`：intervalIntegrable_iff : IntervalIntegrable f μ 
a b ↔ IntegrableOn f (Ι a b) μ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `HasDerivAt.const_smul`：HasDerivAt.const_smul (c : R) (hf : HasDerivAt f 
f' x) : HasDerivAt (c • f) (c • f') x
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`：∀ {𝕜 
: Type u_1} [inst : RCLike 𝕜] {μ : MeasureTheory.Measure ℝ} {E : Type u_2} [inst
_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace ℝ E]…
· 使用定理 `Metric.ball_mem_nhds`：ball_mem_nhds (x : α) {ε : Real} (ε0 : 0 < ε) : ba
ll x ε in 𝓝 x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.AEStronglyMeasurable.smul`：∀ {α : Type u_1} {β : Type u_2}
 [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measu
re α}   {𝕜 : Type u_5} [inst_…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `herglotzRieszKernel_def`：herglotzRieszKernel_def (c w z : Complex) : her
glotzRieszKernel c w z = ((z - c) + (w - c)) / ((z - c) - (w - c))
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Measurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 :…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Measurable.fun_div`：∀ {G : Type u_2} {α : Type u_3} [inst : MeasurableSp
ace G] [inst_1 : Div G] {m : MeasurableSpace α} {f g : α → G}   [MeasurableDiv₂ 
G], Meas…
· 使用定理 `measurableDiv₂_of_mul_inv`：∀ (G : Type u_2) [inst : MeasurableSpace G] [
inst_1 : DivInvMonoid G] [MeasurableMul₂ G] [MeasurableInv G],   MeasurableDiv₂ 
G
（共 113 条，此处仅展示前 30 条）

--- 原说明 ---
**Derivative of the Herglotz–Riesz kernel integral**: if `f` is circle integrabl
e and `w` lies
inside the circle, then `w ↦ circleAverage (fun ζ ↦ herglotzRieszKernel 0 w ζ • 
f ζ) 0 R` has
derivative `circleAverage (fun ζ ↦ (2 * ζ / (ζ - w) ^ 2) • f ζ) 0 R` at `w`.
-/
theorem hasDerivAt_circleAverage_herglotzRieszKernel_smul (hg : CircleIntegrable f 0 R)
    (hw : w ∈ ball 0 R) :
    HasDerivAt (fun w ↦ circleAverage (fun ζ ↦ herglotzRieszKernel 0 w ζ • f ζ) 0 R)
      (circleAverage (fun ζ ↦ (2 * ζ / (ζ - w) ^ 2) • f ζ) 0 R) w := by
  have hR : 0 < R := pos_of_mem_ball hw
  obtain ⟨d, hd, hsub, hdist⟩ := exists_ball_subset_forall_le_norm_circleMap_sub hw
  have hgm : AEStronglyMeasurable (fun θ ↦ f (circleMap 0 R θ))
      (volume.restrict (uIoc 0 (2 * π))) := (intervalIntegrable_iff.1 hg).aestronglyMeasurable
  simp only [circleAverage_def]
  apply HasDerivAt.const_smul
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := fun x θ ↦ (2 * circleMap 0 R θ / (circleMap 0 R θ - x) ^ 2) • f (circleMap 0 R θ))
    (bound := fun θ ↦ 2 * R * (d ^ 2)⁻¹ * ‖f (circleMap 0 R θ)‖)
    (ball_mem_nhds w hd) ?meas1 ?int ?meas2 ?bound ?int_bound ?diff).2
  -- Measurability of the integrand, for `x` near `w`
  case meas1 =>
    filter_upwards with x
    apply AEStronglyMeasurable.smul _ hgm
    simp only [herglotzRieszKernel_def, sub_zero]
    exact Measurable.aestronglyMeasurable (by fun_prop)
  -- Integrability of the integrand at `w`
  case int =>
    have h₁ : CircleIntegrable (herglotzRieszKernel 0 w • f) 0 R :=
      hg.continuousOn_smul (continuousOn_herglotzRieszKernel_sphere hw)
    simpa only [CircleIntegrable, Pi.smul_apply'] using h₁
  -- Measurability of the differentiated integrand
  case meas2 =>
    exact (Measurable.aestronglyMeasurable (by fun_prop)).smul hgm
  -- Uniform bound for the differentiated integrand near `w`
  case bound =>
    filter_upwards with θ _ x hx
    have h₁ : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [norm_smul, norm_div, norm_mul, norm_circleMap_zero, abs_of_pos hR, norm_pow,
      div_eq_mul_inv, h₁]
    gcongr
    exact hdist x hx θ
  -- Integrability of the bound
  case int_bound =>
    exact (IntervalIntegrable.norm hg).const_mul _
  -- Differentiability of the integrand in `x`, for `x` near `w`
  case diff =>
    filter_upwards with θ _ x hx
    have h₁ : circleMap 0 R θ - x ≠ 0 := sub_ne_zero.2 (circleMap_ne_mem_ball (hsub hx) θ)
    have h₂ : HasDerivAt (fun x ↦ herglotzRieszKernel 0 x (circleMap 0 R θ))
        (2 * circleMap 0 R θ / (circleMap 0 R θ - x) ^ 2) x := by
      have h₃ := ((hasDerivAt_id' x).const_add (circleMap 0 R θ)).div
        ((hasDerivAt_id' x).const_sub (circleMap 0 R θ)) h₁
      simpa [herglotzRieszKernel_def, sub_zero, sub_sub, ← two_mul, Pi.div_def] using h₃
    exact h₂.smul_const (f (circleMap 0 R θ))

/--
The Herglotz–Riesz kernel integral of a circle-integrable function is differentiable in the pole
parameter, throughout the open ball.
-/
/-
**differentiableOn_circleAverage_herglotzRieszKernel_smul** 是 Mathlib 中的一个定理，位于命
名空间 ``。
形式化陈述：differentiableOn_circleAverage_herglotzRieszKernel_smul (hg : CircleIntegr
able f 0 R) : DifferentiableOn Complex (fun w => circleAverage (fun ζ => herglot
zRieszKernel 0 w ζ • f ζ) 0 R) (ball 0 R)
参数：hg : CircleIntegrable f 0 R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `hasDerivAt_circleAverage_herglotzRieszKernel_smul`：hasDerivAt_circleAver
age_herglotzRieszKernel_smul (hg : CircleIntegrable f 0 R) (hw : w in ball 0 R) 
: HasDerivAt (fun w => circleAverage (f…

--- 原说明 ---
The Herglotz–Riesz kernel integral of a circle-integrable function is differenti
able in the pole
parameter, throughout the open ball.
-/
theorem differentiableOn_circleAverage_herglotzRieszKernel_smul (hg : CircleIntegrable f 0 R) :
    DifferentiableOn ℂ
      (fun w ↦ circleAverage (fun ζ ↦ herglotzRieszKernel 0 w ζ • f ζ) 0 R) (ball 0 R) :=
  fun _ hw ↦ hasDerivAt_circleAverage_herglotzRieszKernel_smul hg hw
    |>.differentiableAt.differentiableWithinAt

/--
The Herglotz–Riesz kernel integral of a circle-integrable function is analytic in the pole
parameter, throughout the open ball.
-/
/-
**analyticOnNhd_circleAverage_herglotzRieszKernel_smul** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：analyticOnNhd_circleAverage_herglotzRieszKernel_smul [CompleteSpace E] (hg
 : CircleIntegrable f 0 R) : AnalyticOnNhd Complex (fun w => circleAverage (fun 
ζ => herglotzRieszKernel 0 w ζ • f ζ) 0 R) (ball 0 R)
参数：hg : CircleIntegrable f 0 R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableOn.analyticOnNhd`：∀ {E : Type u} [inst : NormedAddCommGrou
p E] [inst_1 : NormedSpace ℂ E] [CompleteSpace E] {s : Set ℂ} {f : ℂ → E},   Dif
ferentiableOn ℂ f s …
· 使用定理 `differentiableOn_circleAverage_herglotzRieszKernel_smul`：differentiableO
n_circleAverage_herglotzRieszKernel_smul (hg : CircleIntegrable f 0 R) : Differe
ntiableOn Complex (fun w => circleAverage (fu…
· 使用定理 `Metric.isOpen_ball`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x : α} 
{ε : ℝ}, IsOpen (Metric.ball x ε)

--- 原说明 ---
The Herglotz–Riesz kernel integral of a circle-integrable function is analytic i
n the pole
parameter, throughout the open ball.
-/
theorem analyticOnNhd_circleAverage_herglotzRieszKernel_smul [CompleteSpace E]
    (hg : CircleIntegrable f 0 R) :
    AnalyticOnNhd ℂ
      (fun w ↦ circleAverage (fun ζ ↦ herglotzRieszKernel 0 w ζ • f ζ) 0 R) (ball 0 R) :=
  (differentiableOn_circleAverage_herglotzRieszKernel_smul hg).analyticOnNhd isOpen_ball
