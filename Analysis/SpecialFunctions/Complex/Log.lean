/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The complex `log` function

Basic properties, relationship with `exp`.
-/

@[expose] public section

noncomputable section

namespace Complex

open Set Filter Bornology

open scoped Real Topology ComplexConjugate

/-- Inverse of the `exp` function. Returns values such that `(log x).im > - π` and `(log x).im ≤ π`.
  `log 0 = 0` -/
@[pp_nodot]
/-
**Complex.log** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：log (x : Complex) : Complex
参数：x : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Inverse of the `exp` function. Returns values such that `(log x).im > - π` and `
(log x).im ≤ π`.
  `log 0 = 0`
-/
noncomputable def log (x : ℂ) : ℂ :=
  Real.log ‖x‖ + arg x * I
/-
**Complex.log_re** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：log_re (x : Complex) : x.log.re = Real.log ‖x‖
参数：x : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem log_re (x : ℂ) : x.log.re = Real.log ‖x‖ := by simp [log]
/-
**Complex.log_im** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：log_im (x : Complex) : x.log.im = x.arg
参数：x : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem log_im (x : ℂ) : x.log.im = x.arg := by simp [log]
/-
**Complex.neg_pi_lt_log_im** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：neg_pi_lt_log_im (x : Complex) : -π < (log x).im
参数：x : Complex。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.log_im`：log_im (x : Complex) : x.log.im = x.arg
-/
theorem neg_pi_lt_log_im (x : ℂ) : -π < (log x).im := by simp only [log_im, neg_pi_lt_arg]
/-
**Complex.log_im_le_pi** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：log_im_le_pi (x : Complex) : (log x).im <= π
参数：x : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.log_im`：log_im (x : Complex) : x.log.im = x.arg
-/
theorem log_im_le_pi (x : ℂ) : (log x).im ≤ π := by simp only [log_im, arg_le_pi]
/-
**Complex.exp_log** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：exp_log {x : Complex} (hx : x != 0) : exp (log x) = x
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.log.eq_1`：∀ (x : ℂ), Complex.log x = ↑(Real.log ‖x‖) + ↑x.arg * 
Complex.I
· 使用定理 `Complex.exp_add_mul_I`：exp_add_mul_I : exp (x + y * I) = exp x * (cos y 
+ sin y * I)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.ofReal_sin`：ofReal_sin (x : Real) : (Real.sin x : Complex) = sin
 x
· 使用定理 `Complex.sin_arg`：sin_arg (x : Complex) : Real.sin (arg x) = x.im / ‖x‖
· 使用定理 `Complex.ofReal_cos`：ofReal_cos (x : Real) : (Real.cos x : Complex) = cos
 x
· 使用定理 `Complex.cos_arg`：cos_arg {x : Complex} (hx : x != 0) : Real.cos (arg x) 
= x.re / ‖x‖
· 使用定理 `Complex.ofReal_exp`：ofReal_exp (x : Real) : (Real.exp x : Complex) = exp
 x
· 使用定理 `Real.exp_log`：exp_log (hx : 0 < x) : exp (log x) = x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Complex.ofReal_div`：ofReal_div (r s : Real) : ((r / s : Real) : Complex)
 = r / s
· 使用引理 `mul_div_cancel₀`：mul_div_cancel₀ (a : G₀) (hb : b != 0) : b * (a / b) = 
a
· 使用定理 `Complex.ofReal_ne_zero`：ofReal_ne_zero {z : Real} : (z : Complex) != 0 ↔
 z != 0
· 使用定理 `norm_ne_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≠ 0 ↔ a ≠ 0
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Complex.re_add_im`：re_add_im (z : Complex) : (z.re : Complex) + z.im * I
 = z
-/
theorem exp_log {x : ℂ} (hx : x ≠ 0) : exp (log x) = x := by
  rw [log, exp_add_mul_I, ← ofReal_sin, sin_arg, ← ofReal_cos, cos_arg hx, ← ofReal_exp,
    Real.exp_log (norm_pos_iff.mpr hx), mul_add, ofReal_div, ofReal_div,
    mul_div_cancel₀ _ (ofReal_ne_zero.2 <| norm_ne_zero_iff.mpr hx), ← mul_assoc,
    mul_div_cancel₀ _ (ofReal_ne_zero.2 <| norm_ne_zero_iff.mpr hx), re_add_im]

@[simp]
/-
**Complex.range_exp** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：range_exp : Set.range exp = {0}ᶜ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Complex.exp_ne_zero`：exp_ne_zero : exp x != 0
· 使用定理 `Complex.exp_log`：exp_log {x : Complex} (hx : x != 0) : exp (log x) = x
-/
theorem range_exp : Set.range exp = {0}ᶜ :=
  Set.ext fun x =>
    ⟨by
      rintro ⟨x, rfl⟩
      exact exp_ne_zero x, fun hx => ⟨log x, exp_log hx⟩⟩
/-
**Complex.log_exp** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：log_exp {x : Complex} (hx₁ : -π < x.im) (hx₂ : x.im <= π) : log (exp x) = 
x
参数：hx₁ : -π < x.im；hx₂ : x.im <= π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.log.eq_1`：∀ (x : ℂ), Complex.log x = ↑(Real.log ‖x‖) + ↑x.arg * 
Complex.I
· 使用定理 `Complex.norm_exp`：norm_exp (z : Complex) : ‖exp z‖ = Real.exp z.re
· 使用定理 `Real.log_exp`：log_exp (x : Real) : log (exp x) = x
· 使用定理 `Complex.exp_eq_exp_re_mul_sin_add_cos`：exp_eq_exp_re_mul_sin_add_cos : e
xp x = exp x.re * (cos x.im + sin x.im * I)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.ofReal_exp`：ofReal_exp (x : Real) : (Real.exp x : Complex) = exp
 x
· 使用定理 `Complex.arg_mul_cos_add_sin_mul_I`：arg_mul_cos_add_sin_mul_I {r : Real} 
(hr : 0 < r) {θ : Real} (hθ : θ in Set.Ioc (-π) π) : arg (r * (cos θ + sin θ * I
)) = θ
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `Complex.re_add_im`：re_add_im (z : Complex) : (z.re : Complex) + z.im * I
 = z
-/
theorem log_exp {x : ℂ} (hx₁ : -π < x.im) (hx₂ : x.im ≤ π) : log (exp x) = x := by
  rw [log, norm_exp, Real.log_exp, exp_eq_exp_re_mul_sin_add_cos, ← ofReal_exp,
    arg_mul_cos_add_sin_mul_I (Real.exp_pos _) ⟨hx₁, hx₂⟩, re_add_im]
/-
**Complex.log_exp_eq_re_add_toIocMod** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：log_exp_eq_re_add_toIocMod (x : Complex) : log (exp x) = x.re + (toIocMod 
Real.two_pi_pos (-π) x.im) * I
参数：x : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.two_pi_pos`：two_pi_pos : 0 < 2 * π
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.log.eq_1`：∀ (x : ℂ), Complex.log x = ↑(Real.log ‖x‖) + ↑x.arg * 
Complex.I
· 使用定理 `Complex.norm_exp`：norm_exp (z : Complex) : ‖exp z‖ = Real.exp z.re
· 使用定理 `Real.log_exp`：log_exp (x : Real) : log (exp x) = x
· 使用定理 `Complex.arg_exp`：arg_exp (z : Complex) : arg (exp z) = toIocMod Real.two
_pi_pos (-π) z.im
-/
theorem log_exp_eq_re_add_toIocMod (x : ℂ) :
    log (exp x) = x.re + (toIocMod Real.two_pi_pos (-π) x.im) * I := by
  rw [log, norm_exp, Real.log_exp, arg_exp]
/-
**Complex.log_exp_eq_sub_toIocDiv** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：log_exp_eq_sub_toIocDiv (x : Complex) : log (exp x) = x - (toIocDiv Real.t
wo_pi_pos (-π) x.im) * (2 * π * I)
参数：x : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.two_pi_pos`：two_pi_pos : 0 < 2 * π
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.log_exp_eq_re_add_toIocMod`：log_exp_eq_re_add_toIocMod (x : Comp
lex) : log (exp x) = x.re + (toIocMod Real.two_pi_pos (-π) x.im) * I
· 使用定理 `toIocMod.eq_1`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : Linear
Order α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p : α} (hp : 0 
< p…
· 使用定理 `Complex.ofReal_sub`：ofReal_sub (r s : Real) : ((r - s : Real) : Complex)
 = r - s
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_sub_assoc`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b c : G), a +
 b - c = a + (b - c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Complex.re_add_im`：re_add_im (z : Complex) : (z.re : Complex) + z.im * I
 = z
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem log_exp_eq_sub_toIocDiv (x : ℂ) :
    log (exp x) = x - (toIocDiv Real.two_pi_pos (-π) x.im) * (2 * π * I) := by
  rw [log_exp_eq_re_add_toIocMod, toIocMod, ofReal_sub, sub_mul, ← add_sub_assoc]
  simp [mul_assoc]
/-
**Complex.exp_inj_of_neg_pi_lt_of_le_pi** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：exp_inj_of_neg_pi_lt_of_le_pi {x y : Complex} (hx₁ : -π < x.im) (hx₂ : x.i
m <= π) (hy₁ : -π < y.im) (hy₂ : y.im <= π) (hxy : exp x = exp y) : x = y
参数：hx₁ : -π < x.im；hx₂ : x.im <= π；hy₁ : -π < y.im；hy₂ : y.im <= π；hxy : exp x =
 exp y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.log_exp`：log_exp {x : Complex} (hx₁ : -π < x.im) (hx₂ : x.im <= 
π) : log (exp x) = x
-/
theorem exp_inj_of_neg_pi_lt_of_le_pi {x y : ℂ} (hx₁ : -π < x.im) (hx₂ : x.im ≤ π) (hy₁ : -π < y.im)
    (hy₂ : y.im ≤ π) (hxy : exp x = exp y) : x = y := by
  rw [← log_exp hx₁ hx₂, ← log_exp hy₁ hy₂, hxy]
/-
**Complex.ofReal_log** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：ofReal_log {x : Real} (hx : 0 <= x) : (x.log : Complex) = log x
参数：hx : 0 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.ext`：∀ {z w : ℂ}, z.re = w.re → z.im = w.im → z = w
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.log_re`：log_re (x : Complex) : x.log.re = Real.log ‖x‖
· 使用定理 `Complex.ofReal_re`：ofReal_re (r : Real) : Complex.re (r : Complex) = r
· 使用定理 `Complex.norm_of_nonneg`：∀ {r : ℝ}, 0 ≤ r → ‖↑r‖ = r
· 使用定理 `Complex.ofReal_im`：ofReal_im (r : Real) : (r : Complex).im = 0
· 使用定理 `Complex.log_im`：log_im (x : Complex) : x.log.im = x.arg
· 使用定理 `Complex.arg_ofReal_of_nonneg`：arg_ofReal_of_nonneg {x : Real} (hx : 0 <=
 x) : arg x = 0
-/
theorem ofReal_log {x : ℝ} (hx : 0 ≤ x) : (x.log : ℂ) = log x :=
  Complex.ext (by rw [log_re, ofReal_re, Complex.norm_of_nonneg hx])
    (by rw [ofReal_im, log_im, arg_ofReal_of_nonneg hx])

@[simp, norm_cast]
/-
**Complex.natCast_log** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：natCast_log {n : Nat} : Real.log n = log n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.ofReal_log`：ofReal_log {x : Real} (hx : 0 <= x) : (x.log : Compl
ex) = log x
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用定理 `Complex.ofReal_natCast`：∀ (n : ℕ), ↑↑n = ↑n
-/
lemma natCast_log {n : ℕ} : Real.log n = log n := ofReal_natCast n ▸ ofReal_log n.cast_nonneg

@[simp]
/-
**Complex.ofNat_log** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：ofNat_log {n : Nat} [n.AtLeastTwo] : Real.log ofNat(n) = log (OfNat.ofNat 
n)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Complex.natCast_log`：natCast_log {n : Nat} : Real.log n = log n
-/
lemma ofNat_log {n : ℕ} [n.AtLeastTwo] :
    Real.log ofNat(n) = log (OfNat.ofNat n) :=
  natCast_log
/-
**Complex.log_ofReal_re** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：log_ofReal_re (x : Real) : (log (x : Complex)).re = Real.log x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.log_re`：log_re (x : Complex) : x.log.re = Real.log ‖x‖
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
· 使用定理 `Real.log_abs`：log_abs (x : Real) : log |x| = log x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem log_ofReal_re (x : ℝ) : (log (x : ℂ)).re = Real.log x := by simp [log_re]
/-
**Complex.log_ofReal_mul** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：log_ofReal_mul {r : Real} (hr : 0 < r) {x : Complex} (hx : x != 0) : log (
r * x) = Real.log r + log x
参数：hr : 0 < r；hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_ne_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≠ 0 ↔ a ≠ 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
· 使用定理 `Complex.arg_real_mul`：arg_real_mul (x : Complex) {r : Real} (hr : 0 < r)
 : arg (r * x) = arg x
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.log_mul`：log_mul (hx : x != 0) (hy : y != 0) : log (x * y) = log x 
+ log y
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Complex.ofReal_add`：ofReal_add (r s : Real) : ((r + s : Real) : Complex)
 = r + s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem log_ofReal_mul {r : ℝ} (hr : 0 < r) {x : ℂ} (hx : x ≠ 0) :
    log (r * x) = Real.log r + log x := by
  replace hx := norm_ne_zero_iff.mpr hx
  simp_rw [log, norm_mul, norm_real, arg_real_mul _ hr, Real.norm_of_nonneg hr.le,
    Real.log_mul hr.ne' hx, ofReal_add, add_assoc]
/-
**Complex.log_mul_ofReal** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：log_mul_ofReal (r : Real) (hr : 0 < r) (x : Complex) (hx : x != 0) : log (
x * r) = Real.log r + log x
参数：r : Real；hr : 0 < r；x : Complex；hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Complex.log_ofReal_mul`：log_ofReal_mul {r : Real} (hr : 0 < r) {x : Comp
lex} (hx : x != 0) : log (r * x) = Real.log r + log x
-/
theorem log_mul_ofReal (r : ℝ) (hr : 0 < r) (x : ℂ) (hx : x ≠ 0) :
    log (x * r) = Real.log r + log x := by rw [mul_comm, log_ofReal_mul hr hx]
/-
**Complex.log_mul_eq_add_log_iff** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：log_mul_eq_add_log_iff {x y : Complex} (hx₀ : x != 0) (hy₀ : y != 0) : log
 (x * y) = log x + log y ↔ arg x + arg y in Set.Ioc (-π) π
参数：hx₀ : x != 0；hy₀ : y != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Complex.ext_iff`：∀ {z w : ℂ}, z = w ↔ z.re = w.re ∧ z.im = w.im
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Complex.log_re`：log_re (x : Complex) : x.log.re = Real.log ‖x‖
· 使用定理 `Complex.log_im`：log_im (x : Complex) : x.log.im = x.arg
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Real.log_mul`：log_mul (hx : x != 0) (hy : y != 0) : log (x * y) = log x 
+ log y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_ne_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≠ 0 ↔ a ≠ 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `Complex.arg_mul_eq_add_arg_iff`：arg_mul_eq_add_arg_iff {x y : Complex} (
hx₀ : x != 0) (hy₀ : y != 0) : (x * y).arg = x.arg + y.arg ↔ arg x + arg y in Se
t.Ioc (-π) π
-/
lemma log_mul_eq_add_log_iff {x y : ℂ} (hx₀ : x ≠ 0) (hy₀ : y ≠ 0) :
    log (x * y) = log x + log y ↔ arg x + arg y ∈ Set.Ioc (-π) π := by
  refine Complex.ext_iff.trans <| Iff.trans ?_ <| arg_mul_eq_add_arg_iff hx₀ hy₀
  simp_rw [add_re, add_im, log_re, log_im, norm_mul,
    Real.log_mul (norm_ne_zero_iff.mpr hx₀) (norm_ne_zero_iff.mpr hy₀), true_and]

alias ⟨_, log_mul⟩ := log_mul_eq_add_log_iff

@[simp]
/-
**Complex.log_zero** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：log_zero : log 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `Real.log_zero`：log_zero : log 0 = 0
· 使用定理 `Complex.arg_zero`：arg_zero : arg 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem log_zero : log 0 = 0 := by simp [log]

@[simp]
/-
**Complex.log_one** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：log_one : log 1 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用定理 `Complex.arg_one`：Complex.arg 1 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem log_one : log 1 = 0 := by simp [log]

/-- This holds true for all `x : ℂ` because of the junk values `0 / 0 = 0` and `log 0 = 0`. -/
/-
**Complex.log_div_self** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (x : ℂ), Complex.log (x / x) = 0
参数：x : ℂ；x / x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Complex.norm_div`：∀ (z w : ℂ), ‖z / w‖ = ‖z‖ / ‖w‖
· 使用定理 `Real.log_div_self`：∀ (x : ℝ), Real.log (x / x) = 0
· 使用定理 `Complex.arg_div_self`：∀ (x : ℂ), (x / x).arg = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
This holds true for all `x : ℂ` because of the junk values `0 / 0 = 0` and `log 
0 = 0`.
-/
@[simp] lemma log_div_self (x : ℂ) : log (x / x) = 0 := by simp [log]
/-
**Complex.log_neg_one** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：log_neg_one : log (-1) = π * I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用定理 `Complex.arg_neg_one`：arg_neg_one : arg (-1) = π
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
This holds true for all `x : ℂ` because of the junk values `0 / 0 = 0` and `log 
0 = 0`.
-/
theorem log_neg_one : log (-1) = π * I := by simp [log]
/-
**Complex.log_I** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：log_I : log I = π / 2 * I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Complex.norm_I`：‖Complex.I‖ = 1
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用定理 `Complex.arg_I`：arg_I : arg I = π / 2
· 使用定理 `Complex.ofReal_div`：ofReal_div (r s : Real) : ((r / s : Real) : Complex)
 = r / s
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem log_I : log I = π / 2 * I := by simp [log]
/-
**Complex.log_neg_I** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：log_neg_I : log (-I) = -(π / 2) * I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `Complex.norm_I`：‖Complex.I‖ = 1
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.arg_neg_I`：arg_neg_I : arg (-I) = -(π / 2)
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
· 使用定理 `Complex.ofReal_div`：ofReal_div (r s : Real) : ((r / s : Real) : Complex)
 = r / s
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem log_neg_I : log (-I) = -(π / 2) * I := by simp [log]
/-
**Complex.log_conj_eq_ite** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：log_conj_eq_ite (x : Complex) : log (conj x) = if x.arg = π then log x els
e conj (log x)
参数：x : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.norm_conj`：norm_conj (z : Complex) : ‖conj z‖ = ‖z‖
· 使用定理 `Complex.arg_conj`：arg_conj (x : Complex) : arg (conj x) = if arg x = π t
hen π else -arg x
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `RingHomClass.toLinearMapClassNNRat`：∀ {F : Type u_1} {R : Type u_2} {S :
 Type u_3} [inst : DivisionSemiring R] [inst_1 : CharZero R]   [inst_2 : Divisio
nSemiring S] [inst_3 : C…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Complex.conj_ofReal`：conj_ofReal (r : Real) : conj (r : Complex) = r
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
· 使用定理 `Complex.conj_I`：conj_I : conj I = -I
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem log_conj_eq_ite (x : ℂ) : log (conj x) = if x.arg = π then log x else conj (log x) := by
  simp_rw [log, norm_conj, arg_conj, map_add, map_mul, conj_ofReal]
  split_ifs with hx
  · rw [hx]
  simp_rw [ofReal_neg, conj_I, mul_neg, neg_mul]
/-
**Complex.log_conj** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：log_conj (x : Complex) (h : x.arg != π) : log (conj x) = conj (log x)
参数：x : Complex；h : x.arg != π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.log_conj_eq_ite`：log_conj_eq_ite (x : Complex) : log (conj x) = 
if x.arg = π then log x else conj (log x)
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem log_conj (x : ℂ) (h : x.arg ≠ π) : log (conj x) = conj (log x) := by
  rw [log_conj_eq_ite, if_neg h]
/-
**Complex.log_inv_eq_ite** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：log_inv_eq_ite (x : Complex) : log x⁻¹ = if x.arg = π then -conj (log x) e
lse -log x
参数：x : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `Complex.log_zero`：log_zero : log 0 = 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.arg_zero`：arg_zero : arg 0 = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Complex.inv_def`：inv_def (z : Complex) : z⁻¹ = conj z * ((normSq z)⁻¹ : 
Real)
· 使用定理 `Complex.log_mul_ofReal`：log_mul_ofReal (r : Real) (hr : 0 < r) (x : Comp
lex) (hx : x != 0) : log (x * r) = Real.log r + log x
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Complex.normSq_pos`：normSq_pos {z : Complex} : 0 < normSq z ↔ z != 0
· 使用定理 `map_ne_zero`：map_ne_zero : f a != 0 ↔ a != 0
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `Real.log_inv`：log_inv (x : Real) : log x⁻¹ = -log x
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_neg_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), a - b = -b + a
· 使用定理 `Complex.log_conj_eq_ite`：log_conj_eq_ite (x : Complex) : log (conj x) = 
if x.arg = π then log x else conj (log x)
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
（共 45 条，此处仅展示前 30 条）
-/
theorem log_inv_eq_ite (x : ℂ) : log x⁻¹ = if x.arg = π then -conj (log x) else -log x := by
  by_cases hx : x = 0
  · simp [hx]
  rw [inv_def, log_mul_ofReal, Real.log_inv, ofReal_neg, ← sub_eq_neg_add, log_conj_eq_ite]
  · simp_rw [log, map_add, map_mul, conj_ofReal, conj_I, normSq_eq_norm_sq, Real.log_pow,
      Nat.cast_two, ofReal_mul, neg_add, mul_neg, neg_neg]
    norm_num
    grind
  · rwa [inv_pos, Complex.normSq_pos]
  · rwa [map_ne_zero]
/-
**Complex.log_inv** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：log_inv (x : Complex) (hx : x.arg != π) : log x⁻¹ = -log x
参数：x : Complex；hx : x.arg != π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.log_inv_eq_ite`：log_inv_eq_ite (x : Complex) : log x⁻¹ = if x.ar
g = π then -conj (log x) else -log x
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem log_inv (x : ℂ) (hx : x.arg ≠ π) : log x⁻¹ = -log x := by rw [log_inv_eq_ite, if_neg hx]
/-
**Complex.two_pi_I_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：two_pi_I_ne_zero : (2 * π * I : Complex) != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem two_pi_I_ne_zero : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
/-
**Complex.exp_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：exp_eq_one_iff {x : Complex} : exp x = 1 ↔ exists n : Int, x = n * (2 * π 
* I)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `existsUnique_add_zsmul_mem_Ioc`：∀ {G : Type u_1} [inst : AddCommGroup G]
 [inst_1 : LinearOrder G] [IsOrderedAddMonoid G] [Archimedean G] {a : G},   0 < 
a → ∀ (b c : G), ∃! …
· 使用定理 `Real.two_pi_pos`：two_pi_pos : 0 < 2 * π
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `eq_neg_iff_add_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
a = -b ↔ a + b = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `neg_add_cancel_left`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), -a 
+ (a + b) = b
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.log_exp`：log_exp {x : Complex} (hx₁ : -π < x.im) (hx₂ : x.im <= 
π) : log (exp x) = x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Function.Periodic.int_mul`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
c : α} [inst : NonAssocRing α],   Function.Periodic f c → ∀ (n : ℤ), Function.Pe
riodic f (↑n * …
· 使用定理 `Complex.exp_periodic`：exp_periodic : Function.Periodic exp (2 * π * I)
· 使用定理 `Complex.log_one`：log_one : log 1 = 0
（共 32 条，此处仅展示前 30 条）
-/
theorem exp_eq_one_iff {x : ℂ} : exp x = 1 ↔ ∃ n : ℤ, x = n * (2 * π * I) := by
  constructor
  · intro h
    rcases existsUnique_add_zsmul_mem_Ioc Real.two_pi_pos x.im (-π) with ⟨n, hn, -⟩
    use -n
    rw [Int.cast_neg, neg_mul, eq_neg_iff_add_eq_zero]
    have : (x + n * (2 * π * I)).im ∈ Set.Ioc (-π) π := by simpa [two_mul, mul_add] using hn
    rw [← log_exp this.1 this.2, exp_periodic.int_mul n, h, log_one]
  · rintro ⟨n, rfl⟩
    exact (exp_periodic.int_mul n).eq.trans exp_zero
/-
**Complex.exp_eq_one_iff_of_im_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：exp_eq_one_iff_of_im_nonneg {x : Complex} (hx : 0 <= x.im) : exp x = 1 ↔ e
xists n : Nat, x = n * (2 * π * I)
参数：hx : 0 <= x.im。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.exp_eq_one_iff`：exp_eq_one_iff {x : Complex} : exp x = 1 ↔ exist
s n : Int, x = n * (2 * π * I)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftIntNatCastLeOfNat`：CanLift ℤ ℕ (fun n => ↑n) fun x => 0 ≤ x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `nonneg_of_mul_nonneg_left`：nonneg_of_mul_nonneg_left [MulPosStrictMono R
] (h : 0 <= a * b) (hb : 0 < b) : 0 <= a
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
（共 31 条，此处仅展示前 30 条）
-/
theorem exp_eq_one_iff_of_im_nonneg {x : ℂ} (hx : 0 ≤ x.im) :
    exp x = 1 ↔ ∃ n : ℕ, x = n * (2 * π * I) := by
  rw [exp_eq_one_iff]
  refine ⟨fun ⟨n, hn⟩ ↦ ?_, fun ⟨n, hn⟩ ↦ ⟨n, by rw [hn]; norm_cast⟩⟩
  have : 0 ≤ n * (2 * π) := by simpa [hn] using hx
  lift n to ℕ using by exact_mod_cast nonneg_of_mul_nonneg_left this (by positivity)
  exact ⟨n, hn⟩
/-
**Complex.exp_two_pi_mul_I_mul_div_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Complex
`。
形式化陈述：exp_two_pi_mul_I_mul_div_eq_one_iff {k N : Nat} (hN : N != 0) : exp (2 * π
 * I * k / N) = 1 ↔ N ∣ k
参数：hN : N != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.exp_eq_one_iff`：exp_eq_one_iff {x : Complex} : exp x = 1 ↔ exist
s n : Int, x = n * (2 * π * I)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用引理 `mul_right_inj'`：mul_right_inj' (ha : a != 0) : a * b = a * c ↔ b = c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval₃`：div_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval / l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval`：eval_cons_mul_eval [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : ((n, e) ::ᵣ L).eval * l.eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
（共 42 条，此处仅展示前 30 条）
-/
theorem exp_two_pi_mul_I_mul_div_eq_one_iff {k N : ℕ} (hN : N ≠ 0) :
    exp (2 * π * I * k / N) = 1 ↔ N ∣ k := by
  rw [exp_eq_one_iff]
  conv in _ = _ => rw [← mul_comm (2 * π * I), mul_div_assoc, mul_right_inj' (by simp)]
  field_simp [Nat.cast_ne_zero.mpr hN]
  norm_cast
  simp [← dvd_def, Int.ofNat_dvd]
/-
**Complex.exp_eq_exp_iff_exp_sub_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：exp_eq_exp_iff_exp_sub_eq_one {x y : Complex} : exp x = exp y ↔ exp (x - y
) = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.exp_sub`：exp_sub : exp (x - y) = exp x / exp y
· 使用引理 `div_eq_one_iff_eq`：div_eq_one_iff_eq (hb : b != 0) : a / b = 1 ↔ a = b
· 使用定理 `Complex.exp_ne_zero`：exp_ne_zero : exp x != 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem exp_eq_exp_iff_exp_sub_eq_one {x y : ℂ} : exp x = exp y ↔ exp (x - y) = 1 := by
  rw [exp_sub, div_eq_one_iff_eq (exp_ne_zero _)]
/-
**Complex.exp_eq_exp_iff_exists_int** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：exp_eq_exp_iff_exists_int {x y : Complex} : exp x = exp y ↔ exists n : Int
, x = y + n * (2 * π * I)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem exp_eq_exp_iff_exists_int {x y : ℂ} : exp x = exp y ↔ ∃ n : ℤ, x = y + n * (2 * π * I) := by
  simp only [exp_eq_exp_iff_exp_sub_eq_one, exp_eq_one_iff, sub_eq_iff_eq_add']
/-
**Complex.re_eq_re_of_cexp_eq_cexp** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ {x y : ℂ}, Complex.exp x = Complex.exp y → x.re = y.re
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Complex.exp_eq_exp_iff_exists_int`：exp_eq_exp_iff_exists_int {x y : Comp
lex} : exp x = exp y ↔ exists n : Int, x = y + n * (2 * π * I)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[grind .] lemma re_eq_re_of_cexp_eq_cexp {x y : ℂ} (h : cexp x = cexp y) :
    x.re = y.re := by
  obtain ⟨n, hn⟩ := exp_eq_exp_iff_exists_int.1 h
  simp [hn]
/-
**Complex.log_exp_exists** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：log_exp_exists (z : Complex) : exists n : Int, log (exp z) = z + n * (2 * 
π * I)
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.exp_eq_exp_iff_exists_int`：exp_eq_exp_iff_exists_int {x y : Comp
lex} : exp x = exp y ↔ exists n : Int, x = y + n * (2 * π * I)
· 使用定理 `Complex.exp_log`：exp_log {x : Complex} (hx : x != 0) : exp (log x) = x
· 使用定理 `Complex.exp_ne_zero`：exp_ne_zero : exp x != 0
-/
theorem log_exp_exists (z : ℂ) :
    ∃ n : ℤ, log (exp z) = z + n * (2 * π * I) := by
  rw [← exp_eq_exp_iff_exists_int, exp_log]
  exact exp_ne_zero z

@[simp]
/-
**Complex.countable_preimage_exp** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：countable_preimage_exp {s : Set Complex} : (exp ⁻¹' s).Countable ↔ s.Count
able
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Countable.mono`：∀ {α : Type u} {s₁ s₂ : Set α}, s₁ ⊆ s₂ → s₂.Countab
le → s₁.Countable
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `Complex.range_exp`：range_exp : Set.range exp = {0}ᶜ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sdiff_eq`：sdiff_eq (s t : Set α) : s \ t = s inter tᶜ
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `Set.sdiff_union_self`：sdiff_union_self {s t : Set α} : s \ t union t = s
 union t
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.Countable.insert`：∀ {α : Type u} {s : Set α} (a : α), s.Countable → 
(insert a s).Countable
· 使用定理 `Set.Countable.image`：∀ {α : Type u} {β : Type v} {s : Set α}, s.Countabl
e → ∀ (f : α → β), (f '' s).Countable
· 使用定理 `Set.biUnion_preimage_singleton`：biUnion_preimage_singleton (f : α -> β) 
(s : Set β) : ⋃ y in s, f ⁻¹' {y} = f ⁻¹' s
· 使用定理 `Set.Countable.biUnion`：∀ {α : Type u} {β : Type v} {s : Set α} {t : (a :
 α) → a ∈ s → Set β},   s.Countable → (∀ (a : α) (ha : a ∈ s), (t a ha).Countabl
e) → (⋃ a, …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ofPred_exists`：ofPred_exists (p : ι -> β -> Prop) : { x | exists i, 
p i x } = ⋃ i, { x | p i x }
· 使用定理 `Set.countable_iUnion`：countable_iUnion {t : ι -> Set α} [Countable ι] (h
t : forall i, (t i).Countable) : (⋃ i, t i).Countable
· 使用定理 `instCountableInt`：Countable ℤ
· 使用定理 `Set.countable_singleton`：∀ {α : Type u} (a : α), {a}.Countable
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
theorem countable_preimage_exp {s : Set ℂ} : (exp ⁻¹' s).Countable ↔ s.Countable := by
  refine ⟨fun hs => ?_, fun hs => ?_⟩
  · refine ((hs.image exp).insert 0).mono ?_
    rw [Set.image_preimage_eq_inter_range, range_exp, ← Set.sdiff_eq, ← Set.union_singleton,
        Set.sdiff_union_self]
    exact Set.subset_union_left
  · rw [← Set.biUnion_preimage_singleton]
    refine hs.biUnion fun z hz => ?_
    by_cases! h : ∃ w, exp w = z
    · rcases h with ⟨w, rfl⟩
      simp only [Set.preimage, Set.mem_singleton_iff, exp_eq_exp_iff_exists_int, Set.ofPred_exists]
      exact Set.countable_iUnion fun m => Set.countable_singleton _
    · simp [Set.preimage, h]

alias ⟨_, _root_.Set.Countable.preimage_cexp⟩ := countable_preimage_exp
/-
**Complex.tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero** 是 Mathlib 中的一个定理，
位于命名空间 `Complex`。
形式化陈述：tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero {z : Complex} (hre : z.
re < 0) (him : z.im = 0) : Tendsto log (𝓝[{ z : Complex | z.im < 0 }] z) (𝓝 <| R
eal.log ‖z‖ - π * I)
参数：hre : z.re < 0；him : z.im = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.Tendsto.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Add M] [ContinuousAdd M] {α : Type u_2} {f g : α → M}   {x : Filter α} {a b :
 M},   F…
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
· 使用定理 `ContinuousWithinAt.tendsto`：ContinuousWithinAt.tendsto (h : ContinuousWi
thinAt f s x) : Tendsto f (𝓝[s] x) (𝓝 (f x))
· 使用定理 `ContinuousAt.comp_continuousWithinAt`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst_2
 : TopologicalSpace γ] {f …
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
· 使用定理 `ContinuousWithinAt.log`：∀ {α : Type u_1} [inst : TopologicalSpace α] {f 
: α → ℝ} {s : Set α} {a : α},   ContinuousWithinAt f s a → f a ≠ 0 → ContinuousW
ithinAt (fun…
· 使用定理 `Continuous.continuousWithinAt`：Continuous.continuousWithinAt (h : Contin
uous f) : ContinuousWithinAt f s x
· 使用定理 `continuous_norm`：∀ {E : Type u_4} [inst : SeminormedAddGroup E], Continu
ous fun a => ‖a‖
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Filter.Tendsto.mul`：Filter.Tendsto.mul {α : Type*} {f g : α -> M} {x : F
ilter α} {a b : M} (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) : Tendsto (
fun x =>…
（共 36 条，此处仅展示前 30 条）
-/
theorem tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero {z : ℂ} (hre : z.re < 0)
    (him : z.im = 0) : Tendsto log (𝓝[{ z : ℂ | z.im < 0 }] z) (𝓝 <| Real.log ‖z‖ - π * I) := by
  convert!
    (continuous_ofReal.continuousAt.comp_continuousWithinAt
          (continuous_norm.continuousWithinAt.log _)).tendsto.add
      (((continuous_ofReal.tendsto _).comp <|
            tendsto_arg_nhdsWithin_im_neg_of_re_neg_of_im_zero hre him).mul
        tendsto_const_nhds) using 1
  · simp [sub_eq_add_neg]
  · lift z to ℝ using him
    simpa using hre.ne
/-
**Complex.continuousWithinAt_log_of_re_neg_of_im_zero** 是 Mathlib 中的一个定理，位于命名空间 
`Complex`。
形式化陈述：continuousWithinAt_log_of_re_neg_of_im_zero {z : Complex} (hre : z.re < 0)
 (him : z.im = 0) : ContinuousWithinAt log { z : Complex | 0 <= z.im } z
参数：hre : z.re < 0；him : z.im = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Add M] [ContinuousAdd M] {α : Type u_2} {f g : α → M}   {x : Filter α} {a b :
 M},   F…
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
· 使用定理 `ContinuousWithinAt.tendsto`：ContinuousWithinAt.tendsto (h : ContinuousWi
thinAt f s x) : Tendsto f (𝓝[s] x) (𝓝 (f x))
· 使用定理 `ContinuousAt.comp_continuousWithinAt`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst_2
 : TopologicalSpace γ] {f …
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
· 使用定理 `ContinuousWithinAt.log`：∀ {α : Type u_1} [inst : TopologicalSpace α] {f 
: α → ℝ} {s : Set α} {a : α},   ContinuousWithinAt f s a → f a ≠ 0 → ContinuousW
ithinAt (fun…
· 使用定理 `Continuous.continuousWithinAt`：Continuous.continuousWithinAt (h : Contin
uous f) : ContinuousWithinAt f s x
· 使用定理 `continuous_norm`：∀ {E : Type u_4} [inst : SeminormedAddGroup E], Continu
ous fun a => ‖a‖
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `ContinuousWithinAt.mul`：ContinuousWithinAt.mul (hf : ContinuousWithinAt 
f s x) (hg : ContinuousWithinAt g s x) : ContinuousWithinAt (f * g) s x
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Complex.continuousWithinAt_arg_of_re_neg_of_im_zero`：continuousWithinAt_
arg_of_re_neg_of_im_zero {z : Complex} (hre : z.re < 0) (him : z.im = 0) : Conti
nuousWithinAt arg { z : Complex | 0 <= z.…
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
-/
theorem continuousWithinAt_log_of_re_neg_of_im_zero {z : ℂ} (hre : z.re < 0) (him : z.im = 0) :
    ContinuousWithinAt log { z : ℂ | 0 ≤ z.im } z := by
  convert!
    (continuous_ofReal.continuousAt.comp_continuousWithinAt
          (continuous_norm.continuousWithinAt.log _)).tendsto.add
      ((continuous_ofReal.continuousAt.comp_continuousWithinAt <|
            continuousWithinAt_arg_of_re_neg_of_im_zero hre him).mul
        tendsto_const_nhds) using 1
  lift z to ℝ using him
  simpa using hre.ne
/-
**Complex.tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero** 是 Mathlib 中的一个
定理，位于命名空间 `Complex`。
形式化陈述：tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero {z : Complex} (hre :
 z.re < 0) (him : z.im = 0) : Tendsto log (𝓝[{ z : Complex | 0 <= z.im }] z) (𝓝 
<| Real.log ‖z‖ + π * I)
参数：hre : z.re < 0；him : z.im = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Complex.arg_eq_pi_iff`：arg_eq_pi_iff {z : Complex} : arg z = π ↔ z.re < 
0 ∧ z.im = 0
· 使用定理 `ContinuousWithinAt.tendsto`：ContinuousWithinAt.tendsto (h : ContinuousWi
thinAt f s x) : Tendsto f (𝓝[s] x) (𝓝 (f x))
· 使用定理 `Complex.continuousWithinAt_log_of_re_neg_of_im_zero`：continuousWithinAt_
log_of_re_neg_of_im_zero {z : Complex} (hre : z.re < 0) (him : z.im = 0) : Conti
nuousWithinAt log { z : Complex | 0 <= z.…
-/
theorem tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero {z : ℂ} (hre : z.re < 0)
    (him : z.im = 0) : Tendsto log (𝓝[{ z : ℂ | 0 ≤ z.im }] z) (𝓝 <| Real.log ‖z‖ + π * I) := by
  simpa only [log, arg_eq_pi_iff.2 ⟨hre, him⟩] using
    (continuousWithinAt_log_of_re_neg_of_im_zero hre him).tendsto

@[simp]
/-
**Complex.map_exp_comap_re_atBot** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：map_exp_comap_re_atBot : map exp (comap re atBot) = 𝓝[!=] 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.comap_exp_nhds_zero`：comap_exp_nhds_zero : comap exp (𝓝 0) = com
ap re atBot
· 使用定理 `Filter.map_comap`：map_comap (f : Filter β) (m : α -> β) : (f.comap m).ma
p m = f ⊓ 𝓟 (range m)
· 使用定理 `Complex.range_exp`：range_exp : Set.range exp = {0}ᶜ
· 使用定理 `nhdsWithin.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] (x : X) (s
 : Set X), nhdsWithin x s = nhds x ⊓ Filter.principal s
-/
theorem map_exp_comap_re_atBot : map exp (comap re atBot) = 𝓝[≠] 0 := by
  rw [← comap_exp_nhds_zero, map_comap, range_exp, nhdsWithin]

@[simp]
/-
**Complex.map_exp_comap_re_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：map_exp_comap_re_atTop : map exp (comap re atTop) = cobounded Complex
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.comap_exp_cobounded`：comap_exp_cobounded : comap exp (cobounded 
Complex) = comap re atTop
· 使用定理 `Filter.map_comap`：map_comap (f : Filter β) (m : α -> β) : (f.comap m).ma
p m = f ⊓ 𝓟 (range m)
· 使用定理 `Complex.range_exp`：range_exp : Set.range exp = {0}ᶜ
· 使用定理 `inf_eq_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b =
 a ↔ a ≤ b
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
· 使用引理 `Bornology.eventually_ne_cobounded`：eventually_ne_cobounded (a : α) : for
allᶠ x in cobounded α, x != a
-/
theorem map_exp_comap_re_atTop : map exp (comap re atTop) = cobounded ℂ := by
  rw [← comap_exp_cobounded, map_comap, range_exp, inf_eq_left, le_principal_iff]
  exact eventually_ne_cobounded _

end Complex

section LogDeriv

open Complex Filter

open Topology

variable {α : Type*}

/-
**continuousAt_clog** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_clog {x : Complex} (h : x in slitPlane) : ContinuousAt log x
参数：h : x in slitPlane。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1 :
 Add M] [ContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f g : 
X → M}…
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
· 使用定理 `ContinuousAt.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace
 Z] {f …
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
· 使用定理 `Real.continuousAt_log`：continuousAt_log (hx : x != 0) : ContinuousAt log
 x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_ne_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≠ 0 ↔ a ≠ 0
· 使用定理 `Complex.slitPlane_ne_zero`：∀ {z : ℂ}, z ∈ Complex.slitPlane → z ≠ 0
· 使用定理 `continuous_norm`：∀ {E : Type u_4} [inst : SeminormedAddGroup E], Continu
ous fun a => ‖a‖
· 使用定理 `continuous_mul_const`：continuous_mul_const (m : M) : Continuous (· * m)
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Complex.continuousAt_arg`：continuousAt_arg (h : x in slitPlane) : Contin
uousAt arg x
-/
theorem continuousAt_clog {x : ℂ} (h : x ∈ slitPlane) : ContinuousAt log x := by
  refine ContinuousAt.add ?_ ?_
  · refine continuous_ofReal.continuousAt.comp ?_
    refine (Real.continuousAt_log ?_).comp continuous_norm.continuousAt
    exact norm_ne_zero_iff.mpr <| slitPlane_ne_zero h
  · have h_cont_mul : Continuous fun x : ℂ => x * I := by fun_prop
    refine h_cont_mul.continuousAt.comp (continuous_ofReal.continuousAt.comp ?_)
    exact continuousAt_arg h
/-
**_root_.Filter.Tendsto.clog** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：_root_.Filter.Tendsto.clog {l : Filter α} {f : α -> Complex} {x : Complex}
 (h : Tendsto f l (𝓝 x)) (hx : x in slitPlane) : Tendsto (fun t => log (f t)) l 
(𝓝 <| log x)
参数：h : Tendsto f l (𝓝 x)；hx : x in slitPlane。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Filter.Tendsto.clog {l : Filter α} {f : α → ℂ} {x : ℂ} (h : Tendsto f l (𝓝 x))
    (hx : x ∈ slitPlane) : Tendsto (fun t => log (f t)) l (𝓝 <| log x) :=
  (continuousAt_clog hx).tendsto.comp h

variable [TopologicalSpace α]

nonrec
/-
**_root_.ContinuousAt.clog** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：_root_.ContinuousAt.clog {f : α -> Complex} {x : α} (h₁ : ContinuousAt f x
) (h₂ : f x in slitPlane) : ContinuousAt (fun t => log (f t)) x
参数：h₁ : ContinuousAt f x；h₂ : f x in slitPlane。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.ContinuousAt.clog {f : α → ℂ} {x : α} (h₁ : ContinuousAt f x)
    (h₂ : f x ∈ slitPlane) : ContinuousAt (fun t => log (f t)) x :=
  h₁.clog h₂

nonrec
/-
**_root_.ContinuousWithinAt.clog** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：_root_.ContinuousWithinAt.clog {f : α -> Complex} {s : Set α} {x : α} (h₁ 
: ContinuousWithinAt f s x) (h₂ : f x in slitPlane) : ContinuousWithinAt (fun t 
=> log (f t)) s x
参数：h₁ : ContinuousWithinAt f s x；h₂ : f x in slitPlane。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.ContinuousWithinAt.clog {f : α → ℂ} {s : Set α} {x : α}
    (h₁ : ContinuousWithinAt f s x) (h₂ : f x ∈ slitPlane) :
    ContinuousWithinAt (fun t => log (f t)) s x :=
  h₁.clog h₂

nonrec
/-
**_root_.ContinuousOn.clog** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：_root_.ContinuousOn.clog {f : α -> Complex} {s : Set α} (h₁ : ContinuousOn
 f s) (h₂ : forall x in s, f x in slitPlane) : ContinuousOn (fun t => log (f t))
 s
参数：h₁ : ContinuousOn f s；h₂ : forall x in s, f x in slitPlane。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.ContinuousOn.clog {f : α → ℂ} {s : Set α} (h₁ : ContinuousOn f s)
    (h₂ : ∀ x ∈ s, f x ∈ slitPlane) : ContinuousOn (fun t => log (f t)) s := fun x hx =>
  (h₁ x hx).clog (h₂ x hx)

nonrec
/-
**_root_.Continuous.clog** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：_root_.Continuous.clog {f : α -> Complex} (h₁ : Continuous f) (h₂ : forall
 x, f x in slitPlane) : Continuous fun t => log (f t)
参数：h₁ : Continuous f；h₂ : forall x, f x in slitPlane。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Continuous.clog {f : α → ℂ} (h₁ : Continuous f)
    (h₂ : ∀ x, f x ∈ slitPlane) : Continuous fun t => log (f t) :=
  continuous_iff_continuousAt.2 fun x => h₁.continuousAt.clog (h₂ x)

end LogDeriv

namespace Complex

open Set
open scoped Real

/-- `Complex.exp` as an `OpenPartialHomeomorph` with `source = {z | -π < im z < π}` and
`target = {z | 0 < re z} ∪ {z | im z ≠ 0}` (a.k.a. `slitPlane`).
This definition is used to prove that `Complex.log`
is complex differentiable at all points but the negative real semi-axis.
-/
/-
**Complex.expOpenPartialHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：expOpenPartialHomeomorph : OpenPartialHomeomorph Complex Complex where toF
un
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.isOpen_slitPlane`：IsOpen Complex.slitPlane

--- 原说明 ---
`Complex.exp` as an `OpenPartialHomeomorph` with `source = {z | -π < im z < π}` 
and
`target = {z | 0 < re z} ∪ {z | im z ≠ 0}` (a.k.a. `slitPlane`).
This definition is used to prove that `Complex.log`
is complex differentiable at all points but the negative real semi-axis.
-/
noncomputable def expOpenPartialHomeomorph : OpenPartialHomeomorph ℂ ℂ where
  toFun := exp
  invFun := log
  source := {z : ℂ | z.im ∈ Ioo (-π) π}
  target := slitPlane
  map_source' := by
    rintro ⟨x, y⟩ ⟨h₁ : -π < y, h₂ : y < π⟩
    simp [exp_mem_slitPlane, h₂.ne,
      (toIocMod_eq_self Real.two_pi_pos).mpr ⟨h₁, by simpa [two_mul] using h₂.le⟩]
  map_target' z h := by
    simp only [mem_ofPred, log_im, mem_Ioo, neg_pi_lt_arg, arg_lt_pi_iff, true_and]
    exact h.imp_left le_of_lt
  left_inv' _x hx := log_exp hx.1 (le_of_lt hx.2)
  right_inv' _x hx := exp_log <| slitPlane_ne_zero hx
  open_source := isOpen_Ioo.preimage continuous_im
  open_target := isOpen_slitPlane
  continuousOn_toFun := by fun_prop
  continuousOn_invFun := continuousOn_id.clog fun _ ↦ id

@[deprecated (since := "2026-01-13")]
alias expPartialHomeomorph := expOpenPartialHomeomorph

end Complex

