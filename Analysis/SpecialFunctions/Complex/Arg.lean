/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# The argument of a complex number.

We define `arg : ℂ → ℝ`, returning a real number in the range $(-π, π]$,
such that for `x ≠ 0`, `sin (arg x) = x.im / x.abs` and `cos (arg x) = x.re / x.abs`,
while `arg 0` defaults to `0`
-/

@[expose] public section

open Filter Metric Set
open scoped ComplexConjugate Real Topology

namespace Complex
variable {a x z : ℂ}

/-- `arg` returns values in the range $(-π, π]$, such that for `x ≠ 0`,
  `sin (arg x) = x.im / x.abs` and `cos (arg x) = x.re / x.abs`,
  `arg 0` defaults to `0` -/
/-
**Complex.arg** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：arg (x : Complex) : Real
参数：x : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`arg` returns values in the range $(-π, π]$, such that for `x ≠ 0`,
  `sin (arg x) = x.im / x.abs` and `cos (arg x) = x.re / x.abs`,
  `arg 0` defaults to `0`
-/
noncomputable def arg (x : ℂ) : ℝ :=
  if 0 ≤ x.re then Real.arcsin (x.im / ‖x‖)
  else if 0 ≤ x.im then Real.arcsin ((-x).im / ‖x‖) + π else Real.arcsin ((-x).im / ‖x‖) - π
/-
**Complex.sin_arg** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：sin_arg (x : Complex) : Real.sin (arg x) = x.im / ‖x‖
参数：x : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Real.sin_arcsin`：sin_arcsin {x : Real} (hx₁ : -1 <= x) (hx₂ : x <= 1) : 
sin (arcsin x) = x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `abs_le`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrder G
] [IsOrderedAddMonoid G] {a b : G},   |a| ≤ b ↔ -b ≤ a ∧ a ≤ b
· 使用定理 `Complex.abs_im_div_norm_le_one`：abs_im_div_norm_le_one (z : Complex) : |
z.im / ‖z‖| <= 1
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用定理 `Real.arcsin_neg`：arcsin_neg (x : Real) : arcsin (-x) = -arcsin x
· 使用定理 `Real.sin_add`：∀ (x y : ℝ), Real.sin (x + y) = Real.sin x * Real.cos y + 
Real.cos x * Real.sin y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Real.sin_neg`：sin_neg : sin (-x) = -sin x
· 使用定理 `Real.cos_pi`：cos_pi : cos π = -1
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Real.cos_neg`：cos_neg : cos (-x) = cos x
· 使用定理 `Real.sin_pi`：sin_pi : sin π = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
-/
theorem sin_arg (x : ℂ) : Real.sin (arg x) = x.im / ‖x‖ := by
  unfold arg; split_ifs <;>
    simp [sub_eq_add_neg, Real.sin_arcsin (abs_le.1 (abs_im_div_norm_le_one x)).1
      (abs_le.1 (abs_im_div_norm_le_one x)).2, Real.sin_add, neg_div, Real.arcsin_neg, Real.sin_neg]
/-
**Complex.cos_arg** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：cos_arg {x : Complex} (hx : x != 0) : Real.cos (arg x) = x.re / ‖x‖
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.arg.eq_1`：∀ (x : ℂ),   x.arg =     if 0 ≤ x.re then Real.arcsin 
(x.im / ‖x‖)     else if 0 ≤ x.im then Real.arcsin ((-x).im / ‖x‖) + Real.pi els
e Real…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Real.cos_arcsin`：cos_arcsin (x : Real) : cos (arcsin x) = √(1 - x ^ 2)
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
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.one_eq_eval`：one_eq_eval [GroupWithZero M] :
 (1:M) = NF.eval (M
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval_cons_neg`：eval_cons_mul_e
val_cons_neg [CommGroupWithZero M] (n : Int) {e : M} (he : e != 0) {L l l' : NF 
M} (h : L.eval * l.eval = l'.eval) : ((n, e) …
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
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
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_ofNat`：∀ {α : Type u_1} [inst : GroupWith
Zero α] (a : α) {n : ℕ}, n ≠ 0 → Mathlib.Tactic.FieldSimp.zpow' a ↑n = a ^ n
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.pow_eq_eval`：pow_eq_eval [CommGroupWithZero 
M] {l : NF M} {r : Nat} (hr : r != 0) {x : M} (hx : x = l.eval) : x ^ r = (l ^ r
).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval₃`：div_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval / l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
（共 72 条，此处仅展示前 30 条）
-/
theorem cos_arg {x : ℂ} (hx : x ≠ 0) : Real.cos (arg x) = x.re / ‖x‖ := by
  rw [arg]
  split_ifs with h₁ h₂
  · rw [Real.cos_arcsin]
    field_simp
    simp [Real.sqrt_sq, (norm_pos_iff.mpr hx).le, *]
    field
  · rw [Real.cos_add_pi, Real.cos_arcsin]
    field_simp
    simp [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq_eq_abs, _root_.abs_of_neg (not_le.1 h₁), *]
    field
  · rw [Real.cos_sub_pi, Real.cos_arcsin]
    field_simp
    simp [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq_eq_abs, _root_.abs_of_neg (not_le.1 h₁), *]
    field

@[simp]
/-
**Complex.norm_mul_exp_arg_mul_I** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：norm_mul_exp_arg_mul_I (x : Complex) : ‖x‖ * exp (arg x * I) = x
参数：x : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_ne_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≠ 0 ↔ a ≠ 0
· 使用定理 `Complex.ext`：∀ {z w : ℂ}, z.re = w.re → z.im = w.im → z = w
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Complex.exp_ofReal_mul_I_re`：exp_ofReal_mul_I_re (x : Real) : (exp (x * 
I)).re = Real.cos x
· 使用定理 `Complex.cos_arg`：cos_arg {x : Complex} (hx : x != 0) : Real.cos (arg x) 
= x.re / ‖x‖
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `IsUnit.div_mul_cancel`：∀ {α : Type u} [inst : DivisionMonoid α] {b : α},
 IsUnit b → ∀ (a : α), a / b * b = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Complex.exp_ofReal_mul_I_im`：exp_ofReal_mul_I_im (x : Real) : (exp (x * 
I)).im = Real.sin x
· 使用定理 `Complex.sin_arg`：sin_arg (x : Complex) : Real.sin (arg x) = x.im / ‖x‖
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem norm_mul_exp_arg_mul_I (x : ℂ) : ‖x‖ * exp (arg x * I) = x := by
  rcases eq_or_ne x 0 with (rfl | hx)
  · simp
  · have : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    apply Complex.ext <;> simp [sin_arg, cos_arg hx, this, mul_comm ‖x‖]

@[simp]
/-
**Complex.norm_mul_cos_add_sin_mul_I** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：norm_mul_cos_add_sin_mul_I (x : Complex) : (‖x‖ * (cos (arg x) + sin (arg 
x) * I) : Complex) = x
参数：x : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.exp_mul_I`：exp_mul_I : exp (x * I) = cos x + sin x * I
· 使用定理 `Complex.norm_mul_exp_arg_mul_I`：norm_mul_exp_arg_mul_I (x : Complex) : ‖
x‖ * exp (arg x * I) = x
-/
theorem norm_mul_cos_add_sin_mul_I (x : ℂ) : (‖x‖ * (cos (arg x) + sin (arg x) * I) : ℂ) = x := by
  rw [← exp_mul_I, norm_mul_exp_arg_mul_I]

@[simp]
/-
**Complex.norm_mul_cos_arg** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：norm_mul_cos_arg (x : Complex) : ‖x‖ * Real.cos (arg x) = x.re
参数：x : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Complex.sin_ofReal_im`：sin_ofReal_im (x : Real) : (sin x).im = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Complex.cos_ofReal_im`：cos_ofReal_im (x : Real) : (cos x).im = 0
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Complex.norm_mul_cos_add_sin_mul_I`：norm_mul_cos_add_sin_mul_I (x : Comp
lex) : (‖x‖ * (cos (arg x) + sin (arg x) * I) : Complex) = x
-/
lemma norm_mul_cos_arg (x : ℂ) : ‖x‖ * Real.cos (arg x) = x.re := by
  simpa [-norm_mul_cos_add_sin_mul_I] using! congr_arg re (norm_mul_cos_add_sin_mul_I x)

@[simp]
/-
**Complex.norm_mul_sin_arg** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：norm_mul_sin_arg (x : Complex) : ‖x‖ * Real.sin (arg x) = x.im
参数：x : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Complex.cos_ofReal_im`：cos_ofReal_im (x : Real) : (cos x).im = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Complex.sin_ofReal_im`：sin_ofReal_im (x : Real) : (sin x).im = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Complex.norm_mul_cos_add_sin_mul_I`：norm_mul_cos_add_sin_mul_I (x : Comp
lex) : (‖x‖ * (cos (arg x) + sin (arg x) * I) : Complex) = x
-/
lemma norm_mul_sin_arg (x : ℂ) : ‖x‖ * Real.sin (arg x) = x.im := by
  simpa [-norm_mul_cos_add_sin_mul_I] using! congr_arg im (norm_mul_cos_add_sin_mul_I x)
/-
**Complex.norm_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：norm_eq_one_iff (z : Complex) : ‖z‖ = 1 ↔ exists θ : Real, exp (θ * I) = z
参数：z : Complex。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.ofReal_one`：ofReal_one : ((1 : Real) : Complex) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Complex.norm_mul_exp_arg_mul_I`：norm_mul_exp_arg_mul_I (x : Complex) : ‖
x‖ * exp (arg x * I) = x
· 使用定理 `Complex.norm_exp_ofReal_mul_I`：norm_exp_ofReal_mul_I (x : Real) : ‖exp (
x * I)‖ = 1
-/
theorem norm_eq_one_iff (z : ℂ) : ‖z‖ = 1 ↔ ∃ θ : ℝ, exp (θ * I) = z := by
  refine ⟨fun hz => ⟨arg z, ?_⟩, ?_⟩
  · calc
      exp (arg z * I) = ‖z‖ * exp (arg z * I) := by rw [hz, ofReal_one, one_mul]
      _ = z := norm_mul_exp_arg_mul_I z
  · rintro ⟨θ, rfl⟩
    exact Complex.norm_exp_ofReal_mul_I θ

@[simp]
/-
**Complex.range_exp_mul_I** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：range_exp_mul_I : (Set.range fun x : Real => exp (x * I)) = Metric.sphere 
0 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem range_exp_mul_I : (Set.range fun x : ℝ => exp (x * I)) = Metric.sphere 0 1 := by
  ext x
  simp only [mem_sphere_zero_iff_norm, norm_eq_one_iff, Set.mem_range]
/-
**Complex.arg_mul_cos_add_sin_mul_I** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_mul_cos_add_sin_mul_I {r : Real} (hr : 0 < r) {θ : Real} (hθ : θ in Se
t.Ioc (-π) π) : arg (r * (cos θ + sin θ * I)) = θ
参数：hr : 0 < r；hθ : θ in Set.Ioc (-π) π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Complex.norm_of_nonneg`：∀ {r : ℝ}, 0 ≤ r → ‖↑r‖ = r
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Complex.norm_cos_add_sin_mul_I`：norm_cos_add_sin_mul_I (x : Real) : ‖cos
 x + sin x * I‖ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Complex.re_ofReal_mul`：re_ofReal_mul (r : Real) (z : Complex) : (r * z).
re = r * z.re
· 使用定理 `mul_nonneg_iff_right_nonneg_of_pos`：mul_nonneg_iff_right_nonneg_of_pos [
PosMulStrictMono R] (ha : 0 < a) : 0 <= a * b ↔ 0 <= b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Complex.im_ofReal_mul`：im_ofReal_mul (r : Real) (z : Complex) : (r * z).
im = r * z.im
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `GroupWithZero.toMulDivCancelClass`：∀ {G₀ : Type u} [inst : GroupWithZero
 G₀], MulDivCancelClass G₀
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Real.cos_nonneg_of_mem_Icc`：cos_nonneg_of_mem_Icc {x : Real} (hx : x in 
Icc (-(π / 2)) (π / 2)) : 0 <= cos x
· 使用定理 `Real.arcsin_sin'`：arcsin_sin' {x : Real} (hx : x in Icc (-(π / 2)) (π / 
2)) : arcsin (sin x) = x
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `Set.mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
cc a b ↔ a ≤ x ∧ x ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStri
ctMono α] {a : α}, 0 < -a ↔ a < 0
（共 109 条，此处仅展示前 30 条）
-/
theorem arg_mul_cos_add_sin_mul_I {r : ℝ} (hr : 0 < r) {θ : ℝ} (hθ : θ ∈ Set.Ioc (-π) π) :
    arg (r * (cos θ + sin θ * I)) = θ := by
  simp only [arg, norm_mul, norm_cos_add_sin_mul_I, Complex.norm_of_nonneg hr.le, mul_one]
  simp only [re_ofReal_mul, im_ofReal_mul, neg_im, ← ofReal_cos, ← ofReal_sin, ←
    mk_eq_add_mul_I, neg_div, mul_div_cancel_left₀ _ hr.ne', mul_nonneg_iff_right_nonneg_of_pos hr]
  by_cases h₁ : θ ∈ Set.Icc (-(π / 2)) (π / 2)
  · rw [if_pos]
    exacts [Real.arcsin_sin' h₁, Real.cos_nonneg_of_mem_Icc h₁]
  · rw [Set.mem_Icc, not_and_or, not_le, not_le] at h₁
    rcases h₁ with h₁ | h₁
    · replace hθ := hθ.1
      have hcos : Real.cos θ < 0 := by
        rw [← neg_pos, ← Real.cos_add_pi]
        refine Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩ <;> linarith
      have hsin : Real.sin θ < 0 := Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) hθ
      rw [if_neg, if_neg, ← Real.sin_add_pi, Real.arcsin_sin, add_sub_cancel_right] <;> [linarith;
        linarith; exact hsin.not_ge; exact hcos.not_ge]
    · replace hθ := hθ.2
      have hcos : Real.cos θ < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt h₁ (by linarith)
      have hsin : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc ⟨by linarith, hθ⟩
      rw [if_neg, if_pos, ← Real.sin_sub_pi, Real.arcsin_sin, sub_add_cancel] <;> [linarith;
        linarith; exact hsin; exact hcos.not_ge]
/-
**Complex.arg_cos_add_sin_mul_I** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_cos_add_sin_mul_I {θ : Real} (hθ : θ in Set.Ioc (-π) π) : arg (cos θ +
 sin θ * I) = θ
参数：hθ : θ in Set.Ioc (-π) π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Complex.ofReal_one`：ofReal_one : ((1 : Real) : Complex) = 1
· 使用定理 `Complex.arg_mul_cos_add_sin_mul_I`：arg_mul_cos_add_sin_mul_I {r : Real} 
(hr : 0 < r) {θ : Real} (hθ : θ in Set.Ioc (-π) π) : arg (r * (cos θ + sin θ * I
)) = θ
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem arg_cos_add_sin_mul_I {θ : ℝ} (hθ : θ ∈ Set.Ioc (-π) π) : arg (cos θ + sin θ * I) = θ := by
  rw [← one_mul (_ + _), ← ofReal_one, arg_mul_cos_add_sin_mul_I zero_lt_one hθ]
/-
**Complex.arg_exp** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_exp (z : Complex) : arg (exp z) = toIocMod Real.two_pi_pos (-π) z.im
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.two_pi_pos`：two_pi_pos : 0 < 2 * π
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.exp_mul_I`：exp_mul_I : exp (x * I) = cos x + sin x * I
· 使用定理 `Complex.ofReal_exp`：ofReal_exp (x : Real) : (Real.exp x : Complex) = exp
 x
· 使用定理 `toIocMod.eq_1`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : Linear
Order α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p : α} (hp : 0 
< p…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.ofReal_sub`：ofReal_sub (r s : Real) : ((r - s : Real) : Complex)
 = r - s
· 使用定理 `Complex.ofReal_zsmul`：∀ (n : ℤ) (r : ℝ), ↑(n • r) = n • ↑r
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `Function.Periodic.sub_zsmul_eq`：∀ {α : Type u_1} {β : Type u_2} {f : α →
 β} {c x : α} [inst : AddGroup α],   Function.Periodic f c → ∀ (n : ℤ), f (x - n
 • c) = f x
· 使用定理 `Complex.exp_mul_I_periodic`：exp_mul_I_periodic : Function.Periodic (fun 
x => exp (x * I)) (2 * π)
· 使用定理 `Complex.exp_add`：exp_add : exp (x + y) = exp x * exp y
· 使用定理 `Complex.re_add_im`：re_add_im (z : Complex) : (z.re : Complex) + z.im * I
 = z
· 使用定理 `Complex.arg_mul_cos_add_sin_mul_I`：arg_mul_cos_add_sin_mul_I {r : Real} 
(hr : 0 < r) {θ : Real} (hθ : θ in Set.Ioc (-π) π) : arg (r * (cos θ + sin θ * I
)) = θ
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
（共 50 条，此处仅展示前 30 条）
-/
theorem arg_exp (z : ℂ) : arg (exp z) = toIocMod Real.two_pi_pos (-π) z.im := by
  convert!
    arg_mul_cos_add_sin_mul_I (Real.exp_pos z.re) (θ := toIocMod Real.two_pi_pos (-π) z.im) _
    using 1
  · rw [← exp_mul_I, ofReal_exp, toIocMod]
    push_cast
    rw [exp_mul_I_periodic.sub_zsmul_eq, ← exp_add, re_add_im]
  · convert! toIocMod_mem_Ioc ..
    ring
/-
**Complex.arg_exp_mul_I** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：arg_exp_mul_I (θ : Real) : arg (exp (θ * I)) = toIocMod Real.two_pi_pos (-
π) θ
参数：θ : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.two_pi_pos`：two_pi_pos : 0 < 2 * π
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.arg_exp`：arg_exp (z : Complex) : arg (exp z) = toIocMod Real.two
_pi_pos (-π) z.im
· 使用定理 `toIocMod.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma arg_exp_mul_I (θ : ℝ) :
    arg (exp (θ * I)) = toIocMod Real.two_pi_pos (-π) θ := by
  simp [arg_exp]

@[simp]
/-
**Complex.arg_zero** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_zero : arg 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `Real.arcsin_zero`：arcsin_zero : arcsin 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem arg_zero : arg 0 = 0 := by simp [arg]
/-
**Complex.ext_norm_arg** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：ext_norm_arg {x y : Complex} (h₁ : ‖x‖ = ‖y‖) (h₂ : x.arg = y.arg) : x = y
参数：h₁ : ‖x‖ = ‖y‖；h₂ : x.arg = y.arg。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.norm_mul_exp_arg_mul_I`：norm_mul_exp_arg_mul_I (x : Complex) : ‖
x‖ * exp (arg x * I) = x
-/
theorem ext_norm_arg {x y : ℂ} (h₁ : ‖x‖ = ‖y‖) (h₂ : x.arg = y.arg) : x = y := by
  rw [← norm_mul_exp_arg_mul_I x, ← norm_mul_exp_arg_mul_I y, h₁, h₂]
/-
**Complex.ext_norm_arg_iff** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：ext_norm_arg_iff {x y : Complex} : x = y ↔ ‖x‖ = ‖y‖ ∧ arg x = arg y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `and_imp`：∀ {a b c : Prop}, a ∧ b → c ↔ a → b → c
· 使用定理 `Complex.ext_norm_arg`：ext_norm_arg {x y : Complex} (h₁ : ‖x‖ = ‖y‖) (h₂ 
: x.arg = y.arg) : x = y
-/
theorem ext_norm_arg_iff {x y : ℂ} : x = y ↔ ‖x‖ = ‖y‖ ∧ arg x = arg y :=
  ⟨fun h => h ▸ ⟨rfl, rfl⟩, and_imp.2 ext_norm_arg⟩
/-
**Complex.arg_mem_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_mem_Ioc (z : Complex) : arg z in Set.Ioc (-π) π
参数：z : Complex。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.arg_zero`：arg_zero : arg 0 = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `existsUnique_add_zsmul_mem_Ioc`：∀ {G : Type u_1} [inst : AddCommGroup G]
 [inst_1 : LinearOrder G] [IsOrderedAddMonoid G] [Archimedean G] {a : G},   0 < 
a → ∀ (b c : G), ∃! …
· 使用定理 `Real.two_pi_pos`：two_pi_pos : 0 < 2 * π
· 使用定理 `Complex.norm_mul_cos_add_sin_mul_I`：norm_mul_cos_add_sin_mul_I (x : Comp
lex) : (‖x‖ * (cos (arg x) + sin (arg x) * I) : Complex) = x
· 使用定理 `Complex.cos_add_int_mul_two_pi`：cos_add_int_mul_two_pi (x : Complex) (n 
: Int) : cos (x + n * (2 * π)) = cos x
· 使用定理 `Complex.sin_add_int_mul_two_pi`：sin_add_int_mul_two_pi (x : Complex) (n 
: Int) : sin (x + n * (2 * π)) = sin x
· 使用定理 `Complex.arg_mul_cos_add_sin_mul_I`：arg_mul_cos_add_sin_mul_I {r : Real} 
(hr : 0 < r) {θ : Real} (hθ : θ in Set.Ioc (-π) π) : arg (r * (cos θ + sin θ * I
)) = θ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `neg_add_cancel_left`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), -a 
+ (a + b) = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.ofReal_add`：ofReal_add (r s : Real) : ((r + s : Real) : Complex)
 = r + s
（共 31 条，此处仅展示前 30 条）
-/
theorem arg_mem_Ioc (z : ℂ) : arg z ∈ Set.Ioc (-π) π := by
  have hπ : 0 < π := Real.pi_pos
  rcases eq_or_ne z 0 with (rfl | hz)
  · simp [hπ, hπ.le]
  rcases existsUnique_add_zsmul_mem_Ioc Real.two_pi_pos (arg z) (-π) with ⟨N, hN, -⟩
  rw [two_mul, neg_add_cancel_left, ← two_mul, zsmul_eq_mul] at hN
  rw [← norm_mul_cos_add_sin_mul_I z, ← cos_add_int_mul_two_pi _ N, ← sin_add_int_mul_two_pi _ N]
  have := arg_mul_cos_add_sin_mul_I (norm_pos_iff.mpr hz) hN
  push_cast at this
  rwa [this]

@[simp]
/-
**Complex.toIocMod_arg** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：toIocMod_arg (z : Complex) : toIocMod Real.two_pi_pos (-π) z.arg = z.arg
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.two_pi_pos`：two_pi_pos : 0 < 2 * π
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toIocMod.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `neg_add_cancel_left`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), -a 
+ (a + b) = b
· 使用定理 `Complex.arg_mem_Ioc`：arg_mem_Ioc (z : Complex) : arg z in Set.Ioc (-π) π
-/
theorem toIocMod_arg (z : ℂ) : toIocMod Real.two_pi_pos (-π) z.arg = z.arg := by
  simpa [toIocMod_eq_self, two_mul] using z.arg_mem_Ioc

@[simp]
/-
**Complex.range_arg** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：range_arg : Set.range arg = Set.Ioc (-π) π
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `Complex.arg_mem_Ioc`：arg_mem_Ioc (z : Complex) : arg z in Set.Ioc (-π) π
· 使用定理 `Complex.arg_cos_add_sin_mul_I`：arg_cos_add_sin_mul_I {θ : Real} (hθ : θ 
in Set.Ioc (-π) π) : arg (cos θ + sin θ * I) = θ
-/
theorem range_arg : Set.range arg = Set.Ioc (-π) π :=
  (Set.range_subset_iff.2 arg_mem_Ioc).antisymm fun _ hx => ⟨_, arg_cos_add_sin_mul_I hx⟩
/-
**Complex.arg_le_pi** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_le_pi (x : Complex) : arg x <= π
参数：x : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Complex.arg_mem_Ioc`：arg_mem_Ioc (z : Complex) : arg z in Set.Ioc (-π) π
-/
theorem arg_le_pi (x : ℂ) : arg x ≤ π :=
  (arg_mem_Ioc x).2
/-
**Complex.neg_pi_lt_arg** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：neg_pi_lt_arg (x : Complex) : -π < arg x
参数：x : Complex。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Complex.arg_mem_Ioc`：arg_mem_Ioc (z : Complex) : arg z in Set.Ioc (-π) π
-/
theorem neg_pi_lt_arg (x : ℂ) : -π < arg x :=
  (arg_mem_Ioc x).1
/-
**Complex.arg_lt_arg_add_two_pi** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_lt_arg_add_two_pi (x y : Complex) : x.arg < y.arg + 2 * π
参数：x y : Complex。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem arg_lt_arg_add_two_pi (x y : ℂ) : x.arg < y.arg + 2 * π := by
  grind [arg_le_pi x, neg_pi_lt_arg y]
/-
**Complex.abs_arg_sub_arg_lt** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：abs_arg_sub_arg_lt (x y : Complex) : |x.arg - y.arg| < 2 * π
参数：x y : Complex。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem abs_arg_sub_arg_lt (x y : ℂ) : |x.arg - y.arg| < 2 * π := by
  grind [arg_lt_arg_add_two_pi x y, arg_lt_arg_add_two_pi y x]
/-
**Complex.abs_arg_le_pi** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：abs_arg_le_pi (z : Complex) : |arg z| <= π
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_le`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrder G
] [IsOrderedAddMonoid G] {a b : G},   |a| ≤ b ↔ -b ≤ a ∧ a ≤ b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Complex.neg_pi_lt_arg`：neg_pi_lt_arg (x : Complex) : -π < arg x
· 使用定理 `Complex.arg_le_pi`：arg_le_pi (x : Complex) : arg x <= π
-/
theorem abs_arg_le_pi (z : ℂ) : |arg z| ≤ π :=
  abs_le.2 ⟨(neg_pi_lt_arg z).le, arg_le_pi z⟩

@[simp]
/-
**Complex.arg_nonneg_iff** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_nonneg_iff {z : Complex} : 0 <= arg z ↔ 0 <= z.im
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.arg_zero`：arg_zero : arg 0 = 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.sin_nonneg_of_mem_Icc`：sin_nonneg_of_mem_Icc {x : Real} (hx : x in 
Icc 0 π) : 0 <= sin x
· 使用定理 `Complex.arg_le_pi`：arg_le_pi (x : Complex) : arg x <= π
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Real.sin_neg_of_neg_of_neg_pi_lt`：sin_neg_of_neg_of_neg_pi_lt {x : Real}
 (hx0 : x < 0) (hpx : -π < x) : sin x < 0
· 使用定理 `Complex.neg_pi_lt_arg`：neg_pi_lt_arg (x : Complex) : -π < arg x
· 使用定理 `Complex.sin_arg`：sin_arg (x : Complex) : Real.sin (arg x) = x.im / ‖x‖
· 使用引理 `le_div_iff₀`：le_div_iff₀ (hc : 0 < c) : a <= b / c ↔ a * c <= b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem arg_nonneg_iff {z : ℂ} : 0 ≤ arg z ↔ 0 ≤ z.im := by
  rcases eq_or_ne z 0 with (rfl | h₀); · simp
  calc
    0 ≤ arg z ↔ 0 ≤ Real.sin (arg z) :=
      ⟨fun h => Real.sin_nonneg_of_mem_Icc ⟨h, arg_le_pi z⟩, by
        contrapose!
        intro h
        exact Real.sin_neg_of_neg_of_neg_pi_lt h (neg_pi_lt_arg _)⟩
    _ ↔ _ := by rw [sin_arg, le_div_iff₀ (norm_pos_iff.mpr h₀), zero_mul]

@[simp]
/-
**Complex.arg_neg_iff** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_neg_iff {z : Complex} : arg z < 0 ↔ z.im < 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le`：lt_iff_lt_of_le_iff_le {β} [LinearOrder α] [Line
arOrder β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) : b < a ↔ d < c
· 使用定理 `Complex.arg_nonneg_iff`：arg_nonneg_iff {z : Complex} : 0 <= arg z ↔ 0 <=
 z.im
-/
theorem arg_neg_iff {z : ℂ} : arg z < 0 ↔ z.im < 0 :=
  lt_iff_lt_of_le_iff_le arg_nonneg_iff
/-
**Complex.arg_real_mul** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_real_mul (x : Complex) {r : Real} (hr : 0 < r) : arg (r * x) = arg x
参数：x : Complex；hr : 0 < r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.norm_mul_cos_add_sin_mul_I`：norm_mul_cos_add_sin_mul_I (x : Comp
lex) : (‖x‖ * (cos (arg x) + sin (arg x) * I) : Complex) = x
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `Complex.arg_mul_cos_add_sin_mul_I`：arg_mul_cos_add_sin_mul_I {r : Real} 
(hr : 0 < r) {θ : Real} (hθ : θ in Set.Ioc (-π) π) : arg (r * (cos θ + sin θ * I
)) = θ
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `Complex.arg_mem_Ioc`：arg_mem_Ioc (z : Complex) : arg z in Set.Ioc (-π) π
-/
theorem arg_real_mul (x : ℂ) {r : ℝ} (hr : 0 < r) : arg (r * x) = arg x := by
  rcases eq_or_ne x 0 with (rfl | hx); · rw [mul_zero]
  conv_lhs =>
    rw [← norm_mul_cos_add_sin_mul_I x, ← mul_assoc, ← ofReal_mul,
      arg_mul_cos_add_sin_mul_I (mul_pos hr (norm_pos_iff.mpr hx)) x.arg_mem_Ioc]
/-
**Complex.arg_mul_real** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_mul_real {r : Real} (hr : 0 < r) (x : Complex) : arg (x * r) = arg x
参数：hr : 0 < r；x : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.arg_real_mul`：arg_real_mul (x : Complex) {r : Real} (hr : 0 < r)
 : arg (r * x) = arg x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem arg_mul_real {r : ℝ} (hr : 0 < r) (x : ℂ) : arg (x * r) = arg x :=
  mul_comm x r ▸ arg_real_mul x hr
/-
**Complex.arg_eq_arg_iff** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_eq_arg_iff {x y : Complex} (hx : x != 0) (hy : y != 0) : arg x = arg y
 ↔ (‖y‖ / ‖x‖ : Complex) * x = y
参数：hx : x != 0；hy : y != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `norm_div`：norm_div (a b : α) : ‖a / b‖ = ‖a‖ / ‖b‖
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_ne_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≠ 0 ↔ a ≠ 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.ofReal_div`：ofReal_div (r s : Real) : ((r / s : Real) : Complex)
 = r / s
· 使用定理 `Complex.arg_real_mul`：arg_real_mul (x : Complex) {r : Real} (hr : 0 < r)
 : arg (r * x) = arg x
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem arg_eq_arg_iff {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    arg x = arg y ↔ (‖y‖ / ‖x‖ : ℂ) * x = y := by
  simp only [ext_norm_arg_iff, norm_mul, norm_div, norm_real, norm_norm,
    div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hx), true_and]
  rw [← ofReal_div, arg_real_mul]
  exact div_pos (norm_pos_iff.mpr hy) (norm_pos_iff.mpr hx)
/-
**Complex.arg_one** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：Complex.arg 1 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Real.arcsin_zero`：arcsin_zero : arcsin 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma arg_one : arg 1 = 0 := by simp [arg, zero_le_one]

/-- This holds true for all `x : ℂ` because of the junk values `0 / 0 = 0` and `arg 0 = 0`. -/
/-
**Complex.arg_div_self** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (x : ℂ), (x / x).arg = 0
参数：x : ℂ；x / x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `Complex.arg_zero`：arg_zero : arg 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Complex.arg_one`：Complex.arg 1 = 0

--- 原说明 ---
This holds true for all `x : ℂ` because of the junk values `0 / 0 = 0` and `arg 
0 = 0`.
-/
@[simp] lemma arg_div_self (x : ℂ) : arg (x / x) = 0 := by
  obtain rfl | hx := eq_or_ne x 0 <;> simp [*]

@[simp]
/-
**Complex.arg_neg_one** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_neg_one : arg (-1) = π
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Real.arcsin_zero`：arcsin_zero : arcsin 0 = 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem arg_neg_one : arg (-1) = π := by simp [arg]

@[simp]
/-
**Complex.arg_I** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_I : arg I = π / 2
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
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Complex.norm_I`：‖Complex.I‖ = 1
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Real.arcsin_one`：arcsin_one : arcsin 1 = π / 2
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem arg_I : arg I = π / 2 := by simp [arg]

@[simp]
/-
**Complex.arg_neg_I** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_neg_I : arg (-I) = -(π / 2)
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
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `Complex.norm_I`：‖Complex.I‖ = 1
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Real.arcsin_neg`：arcsin_neg (x : Real) : arcsin (-x) = -arcsin x
· 使用定理 `Real.arcsin_one`：arcsin_one : arcsin 1 = π / 2
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem arg_neg_I : arg (-I) = -(π / 2) := by simp [arg]

@[simp]
/-
**Complex.tan_arg** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：tan_arg (x : Complex) : Real.tan (arg x) = x.im / x.re
参数：x : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.arg_zero`：arg_zero : arg 0 = 0
· 使用定理 `Real.tan_zero`：tan_zero : tan 0 = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Real.tan_eq_sin_div_cos`：∀ (x : ℝ), Real.tan x = Real.sin x / Real.cos x
· 使用定理 `Complex.sin_arg`：sin_arg (x : Complex) : Real.sin (arg x) = x.im / ‖x‖
· 使用定理 `Complex.cos_arg`：cos_arg {x : Complex} (hx : x != 0) : Real.cos (arg x) 
= x.re / ‖x‖
· 使用引理 `div_div_div_cancel_right₀`：div_div_div_cancel_right₀ (hc : c != 0) (a b 
: G₀) : a / c / (b / c) = a / b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_ne_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≠ 0 ↔ a ≠ 0
-/
theorem tan_arg (x : ℂ) : Real.tan (arg x) = x.im / x.re := by
  by_cases h : x = 0
  · simp only [h, zero_div, Complex.zero_im, Complex.arg_zero, Real.tan_zero, Complex.zero_re]
  rw [Real.tan_eq_sin_div_cos, sin_arg, cos_arg h,
    div_div_div_cancel_right₀ (norm_ne_zero_iff.mpr h)]
/-
**Complex.arg_ofReal_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_ofReal_of_nonneg {x : Real} (hx : 0 <= x) : arg x = 0
参数：hx : 0 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `Real.arcsin_zero`：arcsin_zero : arcsin 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem arg_ofReal_of_nonneg {x : ℝ} (hx : 0 ≤ x) : arg x = 0 := by simp [arg, hx]

@[simp, norm_cast]
/-
**Complex.natCast_arg** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：natCast_arg {n : Nat} : arg n = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.arg_ofReal_of_nonneg`：arg_ofReal_of_nonneg {x : Real} (hx : 0 <=
 x) : arg x = 0
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用定理 `Complex.ofReal_natCast`：∀ (n : ℕ), ↑↑n = ↑n
-/
lemma natCast_arg {n : ℕ} : arg n = 0 :=
  ofReal_natCast n ▸ arg_ofReal_of_nonneg n.cast_nonneg

@[simp]
/-
**Complex.ofNat_arg** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：ofNat_arg {n : Nat} [n.AtLeastTwo] : arg ofNat(n) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Complex.natCast_arg`：natCast_arg {n : Nat} : arg n = 0
-/
lemma ofNat_arg {n : ℕ} [n.AtLeastTwo] : arg ofNat(n) = 0 :=
  natCast_arg
/-
**Complex.arg_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_eq_zero_iff {z : Complex} : arg z = 0 ↔ 0 <= z.re ∧ z.im = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.norm_mul_cos_add_sin_mul_I`：norm_mul_cos_add_sin_mul_I (x : Comp
lex) : (‖x‖ * (cos (arg x) + sin (arg x) * I) : Complex) = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Complex.cos_zero`：cos_zero : cos 0 = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.sin_zero`：sin_zero : sin 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Complex.arg_ofReal_of_nonneg`：arg_ofReal_of_nonneg {x : Real} (hx : 0 <=
 x) : arg x = 0
-/
theorem arg_eq_zero_iff {z : ℂ} : arg z = 0 ↔ 0 ≤ z.re ∧ z.im = 0 := by
  refine ⟨fun h => ?_, ?_⟩
  · rw [← norm_mul_cos_add_sin_mul_I z, h]
    simp [norm_nonneg]
  · obtain ⟨x, y⟩ := z
    rintro ⟨h, rfl : y = 0⟩
    exact arg_ofReal_of_nonneg h

open ComplexOrder in
/-
**Complex.arg_eq_zero_iff_zero_le** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：arg_eq_zero_iff_zero_le {z : Complex} : arg z = 0 ↔ 0 <= z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.arg_eq_zero_iff`：arg_eq_zero_iff {z : Complex} : arg z = 0 ↔ 0 <
= z.re ∧ z.im = 0
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Complex.nonneg_iff`：nonneg_iff {z : Complex} : 0 <= z ↔ 0 <= z.re ∧ 0 = 
z.im
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma arg_eq_zero_iff_zero_le {z : ℂ} : arg z = 0 ↔ 0 ≤ z := by
  rw [arg_eq_zero_iff, eq_comm, nonneg_iff]
/-
**Complex.arg_eq_pi_iff** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_eq_pi_iff {z : Complex} : arg z = π ↔ z.re < 0 ∧ z.im = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.arg_zero`：arg_zero : arg 0 = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Real.pi_ne_zero`：pi_ne_zero : π != 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.norm_mul_cos_add_sin_mul_I`：norm_mul_cos_add_sin_mul_I (x : Comp
lex) : (‖x‖ * (cos (arg x) + sin (arg x) * I) : Complex) = x
· 使用定理 `Complex.cos_pi`：cos_pi : cos π = -1
· 使用定理 `Complex.sin_pi`：sin_pi : sin π = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Complex.arg_neg_one`：arg_neg_one : arg (-1) = π
· 使用定理 `Complex.arg_real_mul`：arg_real_mul (x : Complex) {r : Real} (hr : 0 < r)
 : arg (r * x) = arg x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
（共 33 条，此处仅展示前 30 条）
-/
theorem arg_eq_pi_iff {z : ℂ} : arg z = π ↔ z.re < 0 ∧ z.im = 0 := by
  by_cases h₀ : z = 0
  · simp [h₀, Real.pi_ne_zero.symm]
  constructor
  · intro h
    rw [← norm_mul_cos_add_sin_mul_I z, h]
    simp [h₀]
  · obtain ⟨x, y⟩ := z
    rintro ⟨h : x < 0, rfl : y = 0⟩
    rw [← arg_neg_one, ← arg_real_mul (-1) (neg_pos.2 h)]
    simp [← ofReal_def]

open ComplexOrder in
/-
**Complex.arg_eq_pi_iff_lt_zero** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：arg_eq_pi_iff_lt_zero {z : Complex} : arg z = π ↔ z < 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.arg_eq_pi_iff`：arg_eq_pi_iff {z : Complex} : arg z = π ↔ z.re < 
0 ∧ z.im = 0
-/
lemma arg_eq_pi_iff_lt_zero {z : ℂ} : arg z = π ↔ z < 0 := arg_eq_pi_iff
/-
**Complex.arg_lt_pi_iff** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_lt_pi_iff {z : Complex} : arg z < π ↔ 0 <= z.re ∨ z.im != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LE.le.lt_iff_ne`：lt_iff_ne (h : a <= b) : a < b ↔ a != b
· 使用定理 `Complex.arg_le_pi`：arg_le_pi (x : Complex) : arg x <= π
· 使用定理 `not_iff_comm`：not_iff_comm : (¬a ↔ b) ↔ (¬b ↔ a)
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Complex.arg_eq_pi_iff`：arg_eq_pi_iff {z : Complex} : arg z = π ↔ z.re < 
0 ∧ z.im = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem arg_lt_pi_iff {z : ℂ} : arg z < π ↔ 0 ≤ z.re ∨ z.im ≠ 0 := by
  rw [(arg_le_pi z).lt_iff_ne, not_iff_comm, not_or, not_le, Classical.not_not, arg_eq_pi_iff]
/-
**Complex.arg_ofReal_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_ofReal_of_neg {x : Real} (hx : x < 0) : arg x = π
参数：hx : x < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Complex.arg_eq_pi_iff`：arg_eq_pi_iff {z : Complex} : arg z = π ↔ z.re < 
0 ∧ z.im = 0
-/
theorem arg_ofReal_of_neg {x : ℝ} (hx : x < 0) : arg x = π :=
  arg_eq_pi_iff.2 ⟨hx, rfl⟩
/-
**Complex.arg_eq_pi_div_two_iff** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_eq_pi_div_two_iff {z : Complex} : arg z = π / 2 ↔ z.re = 0 ∧ 0 < z.im
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.arg_zero`：arg_zero : arg 0 = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Real.pi_div_two_pos`：pi_div_two_pos : 0 < π / 2
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.norm_mul_cos_add_sin_mul_I`：norm_mul_cos_add_sin_mul_I (x : Comp
lex) : (‖x‖ * (cos (arg x) + sin (arg x) * I) : Complex) = x
· 使用定理 `Complex.ofReal_div`：ofReal_div (r s : Real) : ((r / s : Real) : Complex)
 = r / s
· 使用定理 `Complex.cos_pi_div_two`：cos_pi_div_two : cos (π / 2) = 0
· 使用定理 `Complex.sin_pi_div_two`：sin_pi_div_two : sin (π / 2) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Complex.arg_I`：arg_I : arg I = π / 2
（共 34 条，此处仅展示前 30 条）
-/
theorem arg_eq_pi_div_two_iff {z : ℂ} : arg z = π / 2 ↔ z.re = 0 ∧ 0 < z.im := by
  by_cases h₀ : z = 0; · simp [h₀, Real.pi_div_two_pos.ne]
  constructor
  · intro h
    rw [← norm_mul_cos_add_sin_mul_I z, h]
    simp [h₀]
  · obtain ⟨x, y⟩ := z
    rintro ⟨rfl : x = 0, hy : 0 < y⟩
    rw [← arg_I, ← arg_real_mul I hy, ofReal_mul', I_re, I_im, mul_zero, mul_one]
/-
**Complex.arg_eq_neg_pi_div_two_iff** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_eq_neg_pi_div_two_iff {z : Complex} : arg z = -(π / 2) ↔ z.re = 0 ∧ z.
im < 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.arg_zero`：arg_zero : arg 0 = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.norm_mul_cos_add_sin_mul_I`：norm_mul_cos_add_sin_mul_I (x : Comp
lex) : (‖x‖ * (cos (arg x) + sin (arg x) * I) : Complex) = x
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
· 使用定理 `Complex.ofReal_div`：ofReal_div (r s : Real) : ((r / s : Real) : Complex)
 = r / s
· 使用定理 `Complex.cos_neg`：cos_neg : cos (-x) = cos x
· 使用定理 `Complex.cos_pi_div_two`：cos_pi_div_two : cos (π / 2) = 0
· 使用定理 `Complex.sin_neg`：sin_neg : sin (-x) = -sin x
· 使用定理 `Complex.sin_pi_div_two`：sin_pi_div_two : sin (π / 2) = 1
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
（共 45 条，此处仅展示前 30 条）
-/
theorem arg_eq_neg_pi_div_two_iff {z : ℂ} : arg z = -(π / 2) ↔ z.re = 0 ∧ z.im < 0 := by
  by_cases h₀ : z = 0; · simp [h₀, Real.pi_ne_zero]
  constructor
  · intro h
    rw [← norm_mul_cos_add_sin_mul_I z, h]
    simp [h₀]
  · obtain ⟨x, y⟩ := z
    rintro ⟨rfl : x = 0, hy : y < 0⟩
    rw [← arg_neg_I, ← arg_real_mul (-I) (neg_pos.2 hy), mk_eq_add_mul_I]
    simp
/-
**Complex.arg_of_re_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_of_re_nonneg {x : Complex} (hx : 0 <= x.re) : arg x = Real.arcsin (x.i
m / ‖x‖)
参数：hx : 0 <= x.re。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem arg_of_re_nonneg {x : ℂ} (hx : 0 ≤ x.re) : arg x = Real.arcsin (x.im / ‖x‖) :=
  if_pos hx
/-
**Complex.arg_of_re_neg_of_im_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_of_re_neg_of_im_nonneg {x : Complex} (hx_re : x.re < 0) (hx_im : 0 <= 
x.im) : arg x = Real.arcsin ((-x).im / ‖x‖) + π
参数：hx_re : x.re < 0；hx_im : 0 <= x.im。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
· 使用定理 `if_false`：∀ {α : Sort u_1} {x : Decidable False} (t e : α), (if False th
en t else e) = e
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem arg_of_re_neg_of_im_nonneg {x : ℂ} (hx_re : x.re < 0) (hx_im : 0 ≤ x.im) :
    arg x = Real.arcsin ((-x).im / ‖x‖) + π := by
  simp only [arg, hx_re.not_ge, hx_im, if_true, if_false]
/-
**Complex.arg_of_re_neg_of_im_neg** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_of_re_neg_of_im_neg {x : Complex} (hx_re : x.re < 0) (hx_im : x.im < 0
) : arg x = Real.arcsin ((-x).im / ‖x‖) - π
参数：hx_re : x.re < 0；hx_im : x.im < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `if_false`：∀ {α : Sort u_1} {x : Decidable False} (t e : α), (if False th
en t else e) = e
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem arg_of_re_neg_of_im_neg {x : ℂ} (hx_re : x.re < 0) (hx_im : x.im < 0) :
    arg x = Real.arcsin ((-x).im / ‖x‖) - π := by
  simp only [arg, hx_re.not_ge, hx_im.not_ge, if_false]
/-
**Complex.arg_of_im_nonneg_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_of_im_nonneg_of_ne_zero {z : Complex} (h₁ : 0 <= z.im) (h₂ : z != 0) :
 arg z = Real.arccos (z.re / ‖z‖)
参数：h₁ : 0 <= z.im；h₂ : z != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.cos_arg`：cos_arg {x : Complex} (hx : x != 0) : Real.cos (arg x) 
= x.re / ‖x‖
· 使用定理 `Real.arccos_cos`：arccos_cos {x : Real} (hx₁ : 0 <= x) (hx₂ : x <= π) : a
rccos (cos x) = x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Complex.arg_nonneg_iff`：arg_nonneg_iff {z : Complex} : 0 <= arg z ↔ 0 <=
 z.im
· 使用定理 `Complex.arg_le_pi`：arg_le_pi (x : Complex) : arg x <= π
-/
theorem arg_of_im_nonneg_of_ne_zero {z : ℂ} (h₁ : 0 ≤ z.im) (h₂ : z ≠ 0) :
    arg z = Real.arccos (z.re / ‖z‖) := by
  rw [← cos_arg h₂, Real.arccos_cos (arg_nonneg_iff.2 h₁) (arg_le_pi _)]
/-
**Complex.arg_of_im_pos** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_of_im_pos {z : Complex} (hz : 0 < z.im) : arg z = Real.arccos (z.re / 
‖z‖)
参数：hz : 0 < z.im。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.arg_of_im_nonneg_of_ne_zero`：arg_of_im_nonneg_of_ne_zero {z : Co
mplex} (h₁ : 0 <= z.im) (h₂ : z != 0) : arg z = Real.arccos (z.re / ‖z‖)
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem arg_of_im_pos {z : ℂ} (hz : 0 < z.im) : arg z = Real.arccos (z.re / ‖z‖) :=
  arg_of_im_nonneg_of_ne_zero hz.le fun h => hz.ne' <| h.symm ▸ rfl
/-
**Complex.arg_of_im_neg** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_of_im_neg {z : Complex} (hz : z.im < 0) : arg z = -Real.arccos (z.re /
 ‖z‖)
参数：hz : z.im < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.cos_arg`：cos_arg {x : Complex} (hx : x != 0) : Real.cos (arg x) 
= x.re / ‖x‖
· 使用定理 `Real.cos_neg`：cos_neg : cos (-x) = cos x
· 使用定理 `Real.arccos_cos`：arccos_cos {x : Real} (hx₁ : 0 <= x) (hx₂ : x <= π) : a
rccos (cos x) = x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, 0 ≤ -a ↔ a ≤ 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Complex.arg_neg_iff`：arg_neg_iff {z : Complex} : arg z < 0 ↔ z.im < 0
· 使用定理 `neg_le`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftMono 
α] [AddRightMono α] {a b : α}, -a ≤ b ↔ -b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Complex.neg_pi_lt_arg`：neg_pi_lt_arg (x : Complex) : -π < arg x
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
theorem arg_of_im_neg {z : ℂ} (hz : z.im < 0) : arg z = -Real.arccos (z.re / ‖z‖) := by
  have h₀ : z ≠ 0 := mt (congr_arg im) hz.ne
  rw [← cos_arg h₀, ← Real.cos_neg, Real.arccos_cos, neg_neg]
  exacts [neg_nonneg.2 (arg_neg_iff.2 hz).le, neg_le.2 (neg_pi_lt_arg z).le]
/-
**Complex.arg_conj** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_conj (x : Complex) : arg (conj x) = if arg x = π then π else -arg x
参数：x : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.norm_conj`：norm_conj (z : Complex) : ‖conj z‖ = ‖z‖
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Real.arcsin_neg`：arcsin_neg (x : Real) : arcsin (-x) = -arcsin x
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `Real.arcsin_zero`：arcsin_zero : arcsin 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
（共 36 条，此处仅展示前 30 条）
-/
theorem arg_conj (x : ℂ) : arg (conj x) = if arg x = π then π else -arg x := by
  simp_rw [arg_eq_pi_iff, arg, neg_im, conj_im, conj_re, norm_conj, neg_div, neg_neg,
    Real.arcsin_neg]
  rcases lt_trichotomy x.re 0 with (hr | hr | hr) <;>
    rcases lt_trichotomy x.im 0 with (hi | hi | hi)
  · simp [hr, hr.not_ge, hi.le, hi.ne, not_le.2 hi, add_comm]
  · simp [hr, hr.not_ge, hi]
  · simp [hr, hr.not_ge, hi.ne.symm, hi.le, not_le.2 hi, sub_eq_neg_add]
  · simp [hr]
  · simp [hr]
  · simp [hr]
  · simp [hr.le, hi.ne]
  · simp [hr.le, hr.le.not_gt]
  · simp [hr.le, hr.le.not_gt]
/-
**Complex.arg_inv** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_inv (x : Complex) : arg x⁻¹ = if arg x = π then π else -arg x
参数：x : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.arg_conj`：arg_conj (x : Complex) : arg (conj x) = if arg x = π t
hen π else -arg x
· 使用定理 `Complex.inv_def`：inv_def (z : Complex) : z⁻¹ = conj z * ((normSq z)⁻¹ : 
Real)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Complex.arg_zero`：arg_zero : arg 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Complex.arg_real_mul`：arg_real_mul (x : Complex) {r : Real} (hr : 0 < r)
 : arg (r * x) = arg x
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem arg_inv (x : ℂ) : arg x⁻¹ = if arg x = π then π else -arg x := by
  rw [← arg_conj, inv_def, mul_comm]
  by_cases hx : x = 0
  · simp [hx]
  · exact arg_real_mul (conj x) (by simp [hx])
/-
**Complex.abs_arg_inv** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (x : ℂ), |x⁻¹.arg| = |x.arg|
参数：x : ℂ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.arg_inv`：arg_inv (x : Complex) : arg x⁻¹ = if arg x = π then π e
lse -arg x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `abs_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a : 
α), |(-a)| = |a|
-/
@[simp] lemma abs_arg_inv (x : ℂ) : |x⁻¹.arg| = |x.arg| := by rw [arg_inv]; split_ifs <;> simp [*]

-- TODO: Replace the next two lemmas by general facts about periodic functions
/-
**Complex.norm_eq_one_iff'** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：norm_eq_one_iff' : ‖x‖ = 1 ↔ exists θ in Set.Ioc (-π) π, exp (θ * I) = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.norm_eq_one_iff`：norm_eq_one_iff (z : Complex) : ‖z‖ = 1 ↔ exist
s θ : Real, exp (θ * I) = z
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `two_pos`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : PartialO
rder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
（共 50 条，此处仅展示前 30 条）
-/
lemma norm_eq_one_iff' : ‖x‖ = 1 ↔ ∃ θ ∈ Set.Ioc (-π) π, exp (θ * I) = x := by
  rw [norm_eq_one_iff]
  constructor
  · rintro ⟨θ, rfl⟩
    refine ⟨toIocMod (mul_pos two_pos Real.pi_pos) (-π) θ, ?_, ?_⟩
    · convert! toIocMod_mem_Ioc _ _ _
      ring
    · rw [eq_sub_of_add_eq <| toIocMod_add_toIocDiv_zsmul _ _ θ, ofReal_sub,
      ofReal_zsmul, ofReal_mul, ofReal_ofNat, exp_mul_I_periodic.sub_zsmul_eq]
  · rintro ⟨θ, _, rfl⟩
    exact ⟨θ, rfl⟩
/-
**Complex.image_exp_Ioc_eq_sphere** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：image_exp_Ioc_eq_sphere : (fun θ : Real => exp (θ * I)) '' Set.Ioc (-π) π 
= sphere 0 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `Complex.norm_eq_one_iff'`：norm_eq_one_iff' : ‖x‖ = 1 ↔ exists θ in Set.I
oc (-π) π, exp (θ * I) = x
-/
lemma image_exp_Ioc_eq_sphere : (fun θ : ℝ ↦ exp (θ * I)) '' Set.Ioc (-π) π = sphere 0 1 := by
  ext; simpa using norm_eq_one_iff'.symm
/-
**Complex.arg_le_pi_div_two_iff** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_le_pi_div_two_iff {z : Complex} : arg z <= π / 2 ↔ 0 <= re z ∨ im z < 
0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.arg_of_re_nonneg`：arg_of_re_nonneg {x : Complex} (hx : 0 <= x.re
) : arg x = Real.arcsin (x.im / ‖x‖)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Complex.arg_of_re_neg_of_im_nonneg`：arg_of_re_neg_of_im_nonneg {x : Comp
lex} (hx_re : x.re < 0) (hx_im : 0 <= x.im) : arg x = Real.arcsin ((-x).im / ‖x‖
) + π
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_lt_iff_lt_add`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [A
ddRightStrictMono α] {a b c : α}, a - c < b ↔ a < b + c
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `half_sub`：half_sub (a : K) : a / 2 - a = -(a / 2)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
（共 54 条，此处仅展示前 30 条）
-/
theorem arg_le_pi_div_two_iff {z : ℂ} : arg z ≤ π / 2 ↔ 0 ≤ re z ∨ im z < 0 := by
  rcases le_or_gt 0 (re z) with hre | hre
  · simp only [hre, arg_of_re_nonneg hre, Real.arcsin_le_pi_div_two, true_or]
  simp only [hre.not_ge, false_or]
  rcases le_or_gt 0 (im z) with him | him
  · simp only [him.not_gt]
    rw [iff_false, not_le, arg_of_re_neg_of_im_nonneg hre him, ← sub_lt_iff_lt_add, half_sub,
      Real.neg_pi_div_two_lt_arcsin, neg_im, neg_div, neg_lt_neg_iff, div_lt_one, ←
      abs_of_nonneg him, abs_im_lt_norm]
    exacts [hre.ne, norm_pos_iff.mpr <| ne_of_apply_ne re hre.ne]
  · simp only [him]
    rw [iff_true, arg_of_re_neg_of_im_neg hre him]
    exact (sub_le_self _ Real.pi_pos.le).trans (Real.arcsin_le_pi_div_two _)
/-
**Complex.neg_pi_div_two_le_arg_iff** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：neg_pi_div_two_le_arg_iff {z : Complex} : -(π / 2) <= arg z ↔ 0 <= re z ∨ 
0 <= im z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.arg_of_re_nonneg`：arg_of_re_nonneg {x : Complex} (hx : 0 <= x.re
) : arg x = Real.arcsin (x.im / ‖x‖)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `Complex.arg_of_re_neg_of_im_nonneg`：arg_of_re_neg_of_im_nonneg {x : Comp
lex} (hx_re : x.re < 0) (hx_im : 0 <= x.im) : arg x = Real.arcsin ((-x).im / ‖x‖
) + π
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Real.neg_pi_div_two_le_arcsin`：neg_pi_div_two_le_arcsin (x : Real) : -(π
 / 2) <= arcsin x
· 使用定理 `le_add_of_nonneg_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1
 : LE α] [AddLeftMono α] {a b : α}, 0 ≤ b → a ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Complex.arg_of_re_neg_of_im_neg`：arg_of_re_neg_of_im_neg {x : Complex} (
hx_re : x.re < 0) (hx_im : x.im < 0) : arg x = Real.arcsin ((-x).im / ‖x‖) - π
· 使用定理 `sub_lt_iff_lt_add'`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : LT 
α] [AddLeftStrictMono α] {a b c : α}, a - b < c ↔ a < b + c
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
（共 46 条，此处仅展示前 30 条）
-/
theorem neg_pi_div_two_le_arg_iff {z : ℂ} : -(π / 2) ≤ arg z ↔ 0 ≤ re z ∨ 0 ≤ im z := by
  rcases le_or_gt 0 (re z) with hre | hre
  · simp only [hre, arg_of_re_nonneg hre, Real.neg_pi_div_two_le_arcsin, true_or]
  simp only [hre.not_ge, false_or]
  rcases le_or_gt 0 (im z) with him | him
  · simp only [him]
    rw [iff_true, arg_of_re_neg_of_im_nonneg hre him]
    exact (Real.neg_pi_div_two_le_arcsin _).trans (le_add_of_nonneg_right Real.pi_pos.le)
  · simp only [him.not_ge]
    rw [iff_false, not_le, arg_of_re_neg_of_im_neg hre him, sub_lt_iff_lt_add', ←
      sub_eq_add_neg, sub_half, Real.arcsin_lt_pi_div_two, div_lt_one, neg_im, ← abs_of_neg him,
      abs_im_lt_norm]
    exacts [hre.ne, norm_pos_iff.mpr <| ne_of_apply_ne re hre.ne]
/-
**Complex.neg_pi_div_two_lt_arg_iff** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：neg_pi_div_two_lt_arg_iff {z : Complex} : -(π / 2) < arg z ↔ 0 < re z ∨ 0 
<= im z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lt_iff_le_and_ne`：lt_iff_le_and_ne : a < b ↔ a <= b ∧ a != b
· 使用定理 `Complex.neg_pi_div_two_le_arg_iff`：neg_pi_div_two_le_arg_iff {z : Comple
x} : -(π / 2) <= arg z ↔ 0 <= re z ∨ 0 <= im z
· 使用定理 `ne_comm`：∀ {α : Sort u_1} {a b : α}, a ≠ b ↔ b ≠ a
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Complex.arg_eq_neg_pi_div_two_iff`：arg_eq_neg_pi_div_two_iff {z : Comple
x} : arg z = -(π / 2) ↔ z.re = 0 ∧ z.im < 0
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `LT.lt.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma neg_pi_div_two_lt_arg_iff {z : ℂ} : -(π / 2) < arg z ↔ 0 < re z ∨ 0 ≤ im z := by
  rw [lt_iff_le_and_ne, neg_pi_div_two_le_arg_iff, ne_comm, Ne, arg_eq_neg_pi_div_two_iff]
  rcases lt_trichotomy z.re 0 with hre | hre | hre
  · simp [hre.ne, hre.not_ge, hre.not_gt]
  · simp [hre]
  · simp [hre, hre.le, hre.ne']
/-
**Complex.arg_lt_pi_div_two_iff** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：arg_lt_pi_div_two_iff {z : Complex} : arg z < π / 2 ↔ 0 < re z ∨ im z < 0 
∨ z = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lt_iff_le_and_ne`：lt_iff_le_and_ne : a < b ↔ a <= b ∧ a != b
· 使用定理 `Complex.arg_le_pi_div_two_iff`：arg_le_pi_div_two_iff {z : Complex} : arg
 z <= π / 2 ↔ 0 <= re z ∨ im z < 0
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Complex.arg_eq_pi_div_two_iff`：arg_eq_pi_div_two_iff {z : Complex} : arg
 z = π / 2 ↔ z.re = 0 ∧ 0 < z.im
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `LT.lt.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma arg_lt_pi_div_two_iff {z : ℂ} : arg z < π / 2 ↔ 0 < re z ∨ im z < 0 ∨ z = 0 := by
  rw [lt_iff_le_and_ne, arg_le_pi_div_two_iff, Ne, arg_eq_pi_div_two_iff]
  rcases lt_trichotomy z.re 0 with hre | hre | hre
  · have : z ≠ 0 := by simp [Complex.ext_iff, hre.ne]
    simp [hre.ne, hre.not_ge, hre.not_gt, this]
  · have : z = 0 ↔ z.im = 0 := by simp [Complex.ext_iff, hre]
    simp [hre, this, or_comm, le_iff_eq_or_lt]
  · simp [hre, hre.le, hre.ne']

@[simp]
/-
**Complex.abs_arg_le_pi_div_two_iff** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：abs_arg_le_pi_div_two_iff {z : Complex} : |arg z| <= π / 2 ↔ 0 <= re z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_le`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrder G
] [IsOrderedAddMonoid G] {a b : G},   |a| ≤ b ↔ -b ≤ a ∧ a ≤ b
· 使用定理 `Complex.arg_le_pi_div_two_iff`：arg_le_pi_div_two_iff {z : Complex} : arg
 z <= π / 2 ↔ 0 <= re z ∨ im z < 0
· 使用定理 `Complex.neg_pi_div_two_le_arg_iff`：neg_pi_div_two_le_arg_iff {z : Comple
x} : -(π / 2) <= arg z ↔ 0 <= re z ∨ 0 <= im z
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `or_and_left`：∀ {a b c : Prop}, a ∨ b ∧ c ↔ (a ∨ b) ∧ (a ∨ c)
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `and_not_self_iff`：∀ (a : Prop), a ∧ ¬a ↔ False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem abs_arg_le_pi_div_two_iff {z : ℂ} : |arg z| ≤ π / 2 ↔ 0 ≤ re z := by
  rw [abs_le, arg_le_pi_div_two_iff, neg_pi_div_two_le_arg_iff, ← or_and_left, ← not_le,
    and_not_self_iff, or_false]

@[simp]
/-
**Complex.abs_arg_lt_pi_div_two_iff** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：abs_arg_lt_pi_div_two_iff {z : Complex} : |arg z| < π / 2 ↔ 0 < re z ∨ z =
 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_lt`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [A
ddLeftMono α] {a b : α} [AddRightMono α],   |a| < b ↔ -b < a ∧ a < b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `Complex.arg_lt_pi_div_two_iff`：arg_lt_pi_div_two_iff {z : Complex} : arg
 z < π / 2 ↔ 0 < re z ∨ im z < 0 ∨ z = 0
· 使用引理 `Complex.neg_pi_div_two_lt_arg_iff`：neg_pi_div_two_lt_arg_iff {z : Comple
x} : -(π / 2) < arg z ↔ 0 < re z ∨ 0 <= im z
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `or_and_left`：∀ {a b c : Prop}, a ∨ b ∧ c ↔ (a ∨ b) ∧ (a ∨ c)
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
theorem abs_arg_lt_pi_div_two_iff {z : ℂ} : |arg z| < π / 2 ↔ 0 < re z ∨ z = 0 := by
  rw [abs_lt, arg_lt_pi_div_two_iff, neg_pi_div_two_lt_arg_iff, ← or_and_left]
  rcases eq_or_ne z 0 with hz | hz
  · simp [hz]
  · simp_rw [hz, or_false, ← not_lt, not_and_self_iff, or_false]

@[simp]
/-
**Complex.arg_conj_coe_angle** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_conj_coe_angle (x : Complex) : (arg (conj x) : Real.Angle) = -arg x
参数：x : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.arg_conj`：arg_conj (x : Complex) : arg (conj x) = if arg x = π t
hen π else -arg x
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Real.Angle.neg_coe_pi`：neg_coe_pi : -(π : Angle) = π
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
theorem arg_conj_coe_angle (x : ℂ) : (arg (conj x) : Real.Angle) = -arg x := by
  by_cases h : arg x = π <;> simp [arg_conj, h]

@[simp]
/-
**Complex.arg_inv_coe_angle** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_inv_coe_angle (x : Complex) : (arg x⁻¹ : Real.Angle) = -arg x
参数：x : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.arg_inv`：arg_inv (x : Complex) : arg x⁻¹ = if arg x = π then π e
lse -arg x
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Real.Angle.neg_coe_pi`：neg_coe_pi : -(π : Angle) = π
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
theorem arg_inv_coe_angle (x : ℂ) : (arg x⁻¹ : Real.Angle) = -arg x := by
  by_cases h : arg x = π <;> simp [arg_inv, h]
/-
**Complex.arg_neg_eq_arg_sub_pi_of_im_pos** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_neg_eq_arg_sub_pi_of_im_pos {x : Complex} (hi : 0 < x.im) : arg (-x) =
 arg x - π
参数：hi : 0 < x.im。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.arg_of_im_pos`：arg_of_im_pos {z : Complex} (hz : 0 < z.im) : arg
 z = Real.arccos (z.re / ‖z‖)
· 使用定理 `Complex.arg_of_im_neg`：arg_of_im_neg {z : Complex} (hz : z.im < 0) : arg
 z = -Real.arccos (z.re / ‖z‖)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Left.neg_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [Ad
dLeftStrictMono α] {a : α}, -a < 0 ↔ 0 < a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用定理 `Real.arccos_neg`：arccos_neg (x : Real) : arccos (-x) = π - arccos x
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem arg_neg_eq_arg_sub_pi_of_im_pos {x : ℂ} (hi : 0 < x.im) : arg (-x) = arg x - π := by
  rw [arg_of_im_pos hi, arg_of_im_neg (show (-x).im < 0 from Left.neg_neg_iff.2 hi)]
  simp [neg_div, Real.arccos_neg]
/-
**Complex.arg_neg_eq_arg_add_pi_of_im_neg** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_neg_eq_arg_add_pi_of_im_neg {x : Complex} (hi : x.im < 0) : arg (-x) =
 arg x + π
参数：hi : x.im < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.arg_of_im_neg`：arg_of_im_neg {z : Complex} (hz : z.im < 0) : arg
 z = -Real.arccos (z.re / ‖z‖)
· 使用定理 `Complex.arg_of_im_pos`：arg_of_im_pos {z : Complex} (hz : 0 < z.im) : arg
 z = Real.arccos (z.re / ‖z‖)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Left.neg_pos_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [Ad
dLeftStrictMono α] {a : α}, 0 < -a ↔ a < 0
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用定理 `Real.arccos_neg`：arccos_neg (x : Real) : arccos (-x) = π - arccos x
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem arg_neg_eq_arg_add_pi_of_im_neg {x : ℂ} (hi : x.im < 0) : arg (-x) = arg x + π := by
  rw [arg_of_im_neg hi, arg_of_im_pos (show 0 < (-x).im from Left.neg_pos_iff.2 hi)]
  simp [neg_div, Real.arccos_neg, add_comm, ← sub_eq_add_neg]
/-
**Complex.arg_neg_eq_arg_sub_pi_iff** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_neg_eq_arg_sub_pi_iff {x : Complex} : arg (-x) = arg x - π ↔ 0 < x.im 
∨ x.im = 0 ∧ x.re < 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.arg_neg_eq_arg_add_pi_of_im_neg`：arg_neg_eq_arg_add_pi_of_im_neg
 {x : Complex} (hi : x.im < 0) : arg (-x) = arg x + π
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Complex.ext`：∀ {z w : ℂ}, z.re = w.re → z.im = w.im → z = w
· 使用定理 `Complex.arg_ofReal_of_neg`：arg_ofReal_of_neg {x : Real} (hx : x < 0) : a
rg x = π
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
· 使用定理 `Complex.arg_ofReal_of_nonneg`：arg_ofReal_of_nonneg {x : Real} (hx : 0 <=
 x) : arg x = 0
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Left.neg_pos_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [Ad
dLeftStrictMono α] {a : α}, 0 < -a ↔ a < 0
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 40 条，此处仅展示前 30 条）
-/
theorem arg_neg_eq_arg_sub_pi_iff {x : ℂ} :
    arg (-x) = arg x - π ↔ 0 < x.im ∨ x.im = 0 ∧ x.re < 0 := by
  rcases lt_trichotomy x.im 0 with (hi | hi | hi)
  · simp [hi, hi.ne, hi.not_gt, arg_neg_eq_arg_add_pi_of_im_neg, sub_eq_add_neg, ←
      add_eq_zero_iff_eq_neg, Real.pi_ne_zero]
  · rw [(ext rfl hi : x = x.re)]
    rcases lt_trichotomy x.re 0 with (hr | hr | hr)
    · rw [arg_ofReal_of_neg hr, ← ofReal_neg, arg_ofReal_of_nonneg (Left.neg_pos_iff.2 hr).le]
      simp [hr]
    · simp [hr, Real.pi_ne_zero]
    · rw [arg_ofReal_of_nonneg hr.le, ← ofReal_neg, arg_ofReal_of_neg (Left.neg_neg_iff.2 hr)]
      simp [hr.not_gt, ← add_eq_zero_iff_eq_neg, Real.pi_ne_zero]
  · simp [hi, arg_neg_eq_arg_sub_pi_of_im_pos]
/-
**Complex.arg_neg_eq_arg_add_pi_iff** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_neg_eq_arg_add_pi_iff {x : Complex} : arg (-x) = arg x + π ↔ x.im < 0 
∨ x.im = 0 ∧ 0 < x.re
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.arg_neg_eq_arg_add_pi_of_im_neg`：arg_neg_eq_arg_add_pi_of_im_neg
 {x : Complex} (hi : x.im < 0) : arg (-x) = arg x + π
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Complex.ext`：∀ {z w : ℂ}, z.re = w.re → z.im = w.im → z = w
· 使用定理 `Complex.arg_ofReal_of_neg`：arg_ofReal_of_neg {x : Real} (hx : x < 0) : a
rg x = π
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
· 使用定理 `Complex.arg_ofReal_of_nonneg`：arg_ofReal_of_nonneg {x : Real} (hx : 0 <=
 x) : arg x = 0
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Left.neg_pos_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [Ad
dLeftStrictMono α] {a : α}, 0 < -a ↔ a < 0
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
（共 43 条，此处仅展示前 30 条）
-/
theorem arg_neg_eq_arg_add_pi_iff {x : ℂ} :
    arg (-x) = arg x + π ↔ x.im < 0 ∨ x.im = 0 ∧ 0 < x.re := by
  rcases lt_trichotomy x.im 0 with (hi | hi | hi)
  · simp [hi, arg_neg_eq_arg_add_pi_of_im_neg]
  · rw [(ext rfl hi : x = x.re)]
    rcases lt_trichotomy x.re 0 with (hr | hr | hr)
    · rw [arg_ofReal_of_neg hr, ← ofReal_neg, arg_ofReal_of_nonneg (Left.neg_pos_iff.2 hr).le]
      simp [hr.not_gt, ← two_mul, Real.pi_ne_zero]
    · simp [hr, Real.pi_ne_zero.symm]
    · rw [arg_ofReal_of_nonneg hr.le, ← ofReal_neg, arg_ofReal_of_neg (Left.neg_neg_iff.2 hr)]
      simp [hr]
  · simp [hi, hi.ne.symm, hi.not_gt, arg_neg_eq_arg_sub_pi_of_im_pos, sub_eq_add_neg, ←
      add_eq_zero_iff_neg_eq, Real.pi_ne_zero]
/-
**Complex.arg_neg_coe_angle** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_neg_coe_angle {x : Complex} (hx : x != 0) : (arg (-x) : Real.Angle) = 
arg x + π
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.arg_neg_eq_arg_add_pi_of_im_neg`：arg_neg_eq_arg_add_pi_of_im_neg
 {x : Complex} (hi : x.im < 0) : arg (-x) = arg x + π
· 使用定理 `Real.Angle.coe_add`：coe_add (x y : Real) : ↑(x + y : Real) = (↑x + ↑y : 
Angle)
· 使用定理 `Complex.ext`：∀ {z w : ℂ}, z.re = w.re → z.im = w.im → z = w
· 使用定理 `Complex.arg_ofReal_of_neg`：arg_ofReal_of_neg {x : Real} (hx : x < 0) : a
rg x = π
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
· 使用定理 `Complex.arg_ofReal_of_nonneg`：arg_ofReal_of_nonneg {x : Real} (hx : 0 <=
 x) : arg x = 0
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Left.neg_pos_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [Ad
dLeftStrictMono α] {a : α}, 0 < -a ↔ a < 0
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `Real.Angle.coe_two_pi`：coe_two_pi : ↑(2 * π : Real) = (0 : Angle)
· 使用定理 `Real.Angle.coe_zero`：coe_zero : ↑(0 : Real) = (0 : Angle)
· 使用定理 `Left.neg_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [Ad
dLeftStrictMono α] {a : α}, -a < 0 ↔ 0 < a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Complex.arg_neg_eq_arg_sub_pi_of_im_pos`：arg_neg_eq_arg_sub_pi_of_im_pos
 {x : Complex} (hi : 0 < x.im) : arg (-x) = arg x - π
· 使用定理 `Real.Angle.coe_sub`：coe_sub (x y : Real) : ↑(x - y : Real) = (↑x - ↑y : 
Angle)
· 使用定理 `Real.Angle.sub_coe_pi_eq_add_coe_pi`：sub_coe_pi_eq_add_coe_pi (θ : Angle
) : θ - π = θ + π
-/
theorem arg_neg_coe_angle {x : ℂ} (hx : x ≠ 0) : (arg (-x) : Real.Angle) = arg x + π := by
  rcases lt_trichotomy x.im 0 with (hi | hi | hi)
  · rw [arg_neg_eq_arg_add_pi_of_im_neg hi, Real.Angle.coe_add]
  · rw [(ext rfl hi : x = x.re)]
    rcases lt_trichotomy x.re 0 with (hr | hr | hr)
    · rw [arg_ofReal_of_neg hr, ← ofReal_neg, arg_ofReal_of_nonneg (Left.neg_pos_iff.2 hr).le, ←
        Real.Angle.coe_add, ← two_mul, Real.Angle.coe_two_pi, Real.Angle.coe_zero]
    · exact False.elim (hx (ext hr hi))
    · rw [arg_ofReal_of_nonneg hr.le, ← ofReal_neg, arg_ofReal_of_neg (Left.neg_neg_iff.2 hr),
        Real.Angle.coe_zero, zero_add]
  · rw [arg_neg_eq_arg_sub_pi_of_im_pos hi, Real.Angle.coe_sub, Real.Angle.sub_coe_pi_eq_add_coe_pi]
/-
**Complex.arg_mul_cos_add_sin_mul_I_eq_toIocMod** 是 Mathlib 中的一个定理，位于命名空间 `Compl
ex`。
形式化陈述：arg_mul_cos_add_sin_mul_I_eq_toIocMod {r : Real} (hr : 0 < r) (θ : Real) :
 arg (r * (cos θ + sin θ * I)) = toIocMod Real.two_pi_pos (-π) θ
参数：hr : 0 < r；θ : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.two_pi_pos`：two_pi_pos : 0 < 2 * π
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.arg_real_mul`：arg_real_mul (x : Complex) {r : Real} (hr : 0 < r)
 : arg (r * x) = arg x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.exp_mul_I`：exp_mul_I : exp (x * I) = cos x + sin x * I
· 使用引理 `Complex.arg_exp_mul_I`：arg_exp_mul_I (θ : Real) : arg (exp (θ * I)) = to
IocMod Real.two_pi_pos (-π) θ
-/
theorem arg_mul_cos_add_sin_mul_I_eq_toIocMod {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    arg (r * (cos θ + sin θ * I)) = toIocMod Real.two_pi_pos (-π) θ := by
  rw [arg_real_mul _ hr, ← exp_mul_I, arg_exp_mul_I]
/-
**Complex.arg_cos_add_sin_mul_I_eq_toIocMod** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_cos_add_sin_mul_I_eq_toIocMod (θ : Real) : arg (cos θ + sin θ * I) = t
oIocMod Real.two_pi_pos (-π) θ
参数：θ : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.two_pi_pos`：two_pi_pos : 0 < 2 * π
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Complex.ofReal_one`：ofReal_one : ((1 : Real) : Complex) = 1
· 使用定理 `Complex.arg_mul_cos_add_sin_mul_I_eq_toIocMod`：arg_mul_cos_add_sin_mul_I
_eq_toIocMod {r : Real} (hr : 0 < r) (θ : Real) : arg (r * (cos θ + sin θ * I)) 
= toIocMod Real.two_pi_pos (-π) θ
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem arg_cos_add_sin_mul_I_eq_toIocMod (θ : ℝ) :
    arg (cos θ + sin θ * I) = toIocMod Real.two_pi_pos (-π) θ := by
  rw [← one_mul (_ + _), ← ofReal_one, arg_mul_cos_add_sin_mul_I_eq_toIocMod zero_lt_one]
/-
**Complex.arg_mul_cos_add_sin_mul_I_sub** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_mul_cos_add_sin_mul_I_sub {r : Real} (hr : 0 < r) (θ : Real) : arg (r 
* (cos θ + sin θ * I)) - θ = 2 * π * ⌊(π - θ) / (2 * π)⌋
参数：hr : 0 < r；θ : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.two_pi_pos`：two_pi_pos : 0 < 2 * π
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.arg_mul_cos_add_sin_mul_I_eq_toIocMod`：arg_mul_cos_add_sin_mul_I
_eq_toIocMod {r : Real} (hr : 0 < r) (θ : Real) : arg (r * (cos θ + sin θ * I)) 
= toIocMod Real.two_pi_pos (-π) θ
· 使用定理 `toIocMod_sub_self`：toIocMod_sub_self (a b : α) : toIocMod hp a b - b = -
toIocDiv hp a b • p
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `FloorRing.archimedean`：∀ (K : Type u_5) [inst : Field K] [inst_1 : Linea
rOrder K] [IsStrictOrderedRing K] [FloorRing K], Archimedean K
· 使用定理 `toIocDiv_eq_neg_floor`：toIocDiv_eq_neg_floor (a b : α) : toIocDiv hp a b
 = -⌊(a + p - b) / p⌋
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf'`：∀ {R : Type u_1} [inst : CommSemiri
ng R] {a a' b : R},   a = a' → ∀ {e : ℕ}, Nat.rawCast 1 = e → a' ^ e * Nat.rawCa
st 1 = b → a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
（共 74 条，此处仅展示前 30 条）
-/
theorem arg_mul_cos_add_sin_mul_I_sub {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    arg (r * (cos θ + sin θ * I)) - θ = 2 * π * ⌊(π - θ) / (2 * π)⌋ := by
  rw [arg_mul_cos_add_sin_mul_I_eq_toIocMod hr, toIocMod_sub_self, toIocDiv_eq_neg_floor,
    zsmul_eq_mul]
  ring_nf
/-
**Complex.arg_cos_add_sin_mul_I_sub** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_cos_add_sin_mul_I_sub (θ : Real) : arg (cos θ + sin θ * I) - θ = 2 * π
 * ⌊(π - θ) / (2 * π)⌋
参数：θ : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Complex.ofReal_one`：ofReal_one : ((1 : Real) : Complex) = 1
· 使用定理 `Complex.arg_mul_cos_add_sin_mul_I_sub`：arg_mul_cos_add_sin_mul_I_sub {r 
: Real} (hr : 0 < r) (θ : Real) : arg (r * (cos θ + sin θ * I)) - θ = 2 * π * ⌊(
π - θ) / (2 * π)⌋
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem arg_cos_add_sin_mul_I_sub (θ : ℝ) :
    arg (cos θ + sin θ * I) - θ = 2 * π * ⌊(π - θ) / (2 * π)⌋ := by
  rw [← one_mul (_ + _), ← ofReal_one, arg_mul_cos_add_sin_mul_I_sub zero_lt_one]
/-
**Complex.arg_mul_cos_add_sin_mul_I_coe_angle** 是 Mathlib 中的一个定理，位于命名空间 `Complex
`。
形式化陈述：arg_mul_cos_add_sin_mul_I_coe_angle {r : Real} (hr : 0 < r) (θ : Real.Angl
e) : (arg (r * (Real.Angle.cos θ + Real.Angle.sin θ * I)) : Real.Angle) = θ
参数：hr : 0 < r；θ : Real.Angle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.Angle.induction_on`：∀ {p : Real.Angle → Prop} (θ : Real.Angle), (∀ 
(x : ℝ), p ↑x) → p θ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.two_pi_pos`：two_pi_pos : 0 < 2 * π
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Complex.ofReal_cos`：ofReal_cos (x : Real) : (Real.cos x : Complex) = cos
 x
· 使用定理 `Complex.ofReal_sin`：ofReal_sin (x : Real) : (Real.sin x : Complex) = sin
 x
· 使用定理 `Complex.arg_mul_cos_add_sin_mul_I_eq_toIocMod`：arg_mul_cos_add_sin_mul_I
_eq_toIocMod {r : Real} (hr : 0 < r) (θ : Real) : arg (r * (cos θ + sin θ * I)) 
= toIocMod Real.two_pi_pos (-π) θ
· 使用定理 `Real.Angle.coe_toIocMod`：coe_toIocMod (θ ψ : Real) : ↑(toIocMod two_pi_p
os ψ θ) = (θ : Angle)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem arg_mul_cos_add_sin_mul_I_coe_angle {r : ℝ} (hr : 0 < r) (θ : Real.Angle) :
    (arg (r * (Real.Angle.cos θ + Real.Angle.sin θ * I)) : Real.Angle) = θ := by
  induction θ using Real.Angle.induction_on with | _ θ
  simp [arg_mul_cos_add_sin_mul_I_eq_toIocMod hr]
/-
**Complex.arg_cos_add_sin_mul_I_coe_angle** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_cos_add_sin_mul_I_coe_angle (θ : Real.Angle) : (arg (Real.Angle.cos θ 
+ Real.Angle.sin θ * I) : Real.Angle) = θ
参数：θ : Real.Angle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Complex.ofReal_one`：ofReal_one : ((1 : Real) : Complex) = 1
· 使用定理 `Complex.arg_mul_cos_add_sin_mul_I_coe_angle`：arg_mul_cos_add_sin_mul_I_c
oe_angle {r : Real} (hr : 0 < r) (θ : Real.Angle) : (arg (r * (Real.Angle.cos θ 
+ Real.Angle.sin θ * I)) : Real.A…
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem arg_cos_add_sin_mul_I_coe_angle (θ : Real.Angle) :
    (arg (Real.Angle.cos θ + Real.Angle.sin θ * I) : Real.Angle) = θ := by
  rw [← one_mul (_ + _), ← ofReal_one, arg_mul_cos_add_sin_mul_I_coe_angle zero_lt_one]
/-
**Complex.arg_mul_coe_angle** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_mul_coe_angle {x y : Complex} (hx : x != 0) (hy : y != 0) : (arg (x * 
y) : Real.Angle) = arg x + arg y
参数：hx : x != 0；hy : y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.ofReal_cos`：ofReal_cos (x : Real) : (Real.cos x : Complex) = cos
 x
· 使用定理 `Complex.ofReal_sin`：ofReal_sin (x : Real) : (Real.sin x : Complex) = sin
 x
· 使用定理 `Complex.cos_add_sin_I`：cos_add_sin_I : cos x + sin x * I = exp (x * I)
· 使用定理 `Complex.ofReal_add`：ofReal_add (r s : Real) : ((r + s : Real) : Complex)
 = r + s
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `Complex.exp_add`：exp_add : exp (x + y) = exp x * exp y
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Complex.norm_mul_exp_arg_mul_I`：norm_mul_exp_arg_mul_I (x : Complex) : ‖
x‖ * exp (arg x * I) = x
· 使用定理 `Complex.arg_mul_cos_add_sin_mul_I_coe_angle`：arg_mul_cos_add_sin_mul_I_c
oe_angle {r : Real} (hr : 0 < r) (θ : Real.Angle) : (arg (r * (Real.Angle.cos θ 
+ Real.Angle.sin θ * I)) : Real.A…
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
-/
theorem arg_mul_coe_angle {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    (arg (x * y) : Real.Angle) = arg x + arg y := by
  convert!
    arg_mul_cos_add_sin_mul_I_coe_angle (mul_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hy))
      (arg x + arg y : Real.Angle) using 3
  simp_rw [← Real.Angle.coe_add, Real.Angle.sin_coe, Real.Angle.cos_coe, ofReal_cos, ofReal_sin,
    cos_add_sin_I, ofReal_add, add_mul, exp_add, ofReal_mul]
  rw [mul_assoc, mul_comm (exp _), ← mul_assoc (‖y‖ : ℂ), norm_mul_exp_arg_mul_I, mul_comm y, ←
    mul_assoc, norm_mul_exp_arg_mul_I]
/-
**Complex.arg_div_coe_angle** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_div_coe_angle {x y : Complex} (hx : x != 0) (hy : y != 0) : (arg (x / 
y) : Real.Angle) = arg x - arg y
参数：hx : x != 0；hy : y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Complex.arg_mul_coe_angle`：arg_mul_coe_angle {x y : Complex} (hx : x != 
0) (hy : y != 0) : (arg (x * y) : Real.Angle) = arg x + arg y
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
· 使用定理 `Complex.arg_inv_coe_angle`：arg_inv_coe_angle (x : Complex) : (arg x⁻¹ : 
Real.Angle) = -arg x
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
-/
theorem arg_div_coe_angle {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    (arg (x / y) : Real.Angle) = arg x - arg y := by
  rw [div_eq_mul_inv, arg_mul_coe_angle hx (inv_ne_zero hy), arg_inv_coe_angle, sub_eq_add_neg]
/-
**Complex.arg_pow_coe_angle** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_pow_coe_angle (x : Complex) (n : Nat) : (arg (x ^ n) : Real.Angle) = n
 • (arg x : Real.Angle)
参数：x : Complex；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Complex.arg_one`：Complex.arg 1 = 0
· 使用定理 `Complex.arg_zero`：arg_zero : arg 0 = 0
· 使用定理 `nsmul_zero`：∀ {M : Type u_2} [inst : AddMonoid M] (n : ℕ), n • 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 0 • a = 0
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Complex.arg_mul_coe_angle`：arg_mul_coe_angle {x y : Complex} (hx : x != 
0) (hy : y != 0) : (arg (x * y) : Real.Angle) = arg x + arg y
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `succ_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (n : ℕ), (n + 
1) • a = n • a + a
-/
theorem arg_pow_coe_angle (x : ℂ) (n : ℕ) :
    (arg (x ^ n) : Real.Angle) = n • (arg x : Real.Angle) := by
  obtain rfl | x0 := eq_or_ne x 0
  · by_cases n0 : n = 0 <;> simp [n0]
  · induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, arg_mul_coe_angle (pow_ne_zero n x0) x0, ih, succ_nsmul]
/-
**Complex.arg_zpow_coe_angle** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_zpow_coe_angle (x : Complex) (n : Int) : (arg (x ^ n) : Real.Angle) = 
n • (arg x : Real.Angle)
参数：x : Complex；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Complex.arg_pow_coe_angle`：arg_pow_coe_angle (x : Complex) (n : Nat) : (
arg (x ^ n) : Real.Angle) = n • (arg x : Real.Angle)
· 使用定理 `natCast_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G) (n : ℕ),
 ↑n • a = n • a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `Complex.arg_inv_coe_angle`：arg_inv_coe_angle (x : Complex) : (arg x⁻¹ : 
Real.Angle) = -arg x
· 使用定理 `negSucc_zsmul`：negSucc_zsmul {G} [SubNegMonoid G] (a : G) (n : Nat) : In
t.negSucc n • a = -((n + 1) • a)
-/
theorem arg_zpow_coe_angle (x : ℂ) (n : ℤ) :
    (arg (x ^ n) : Real.Angle) = n • (arg x : Real.Angle) := by
  match n with
  | Int.ofNat m => simp [arg_pow_coe_angle]
  | Int.negSucc m => simp [arg_pow_coe_angle]

@[simp]
/-
**Complex.arg_coe_angle_toReal_eq_arg** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_coe_angle_toReal_eq_arg (z : Complex) : (arg z : Real.Angle).toReal = 
arg z
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Angle.toReal_coe_eq_self_iff_mem_Ioc`：toReal_coe_eq_self_iff_mem_Io
c {θ : Real} : (θ : Angle).toReal = θ ↔ θ in Set.Ioc (-π) π
· 使用定理 `Complex.arg_mem_Ioc`：arg_mem_Ioc (z : Complex) : arg z in Set.Ioc (-π) π
-/
theorem arg_coe_angle_toReal_eq_arg (z : ℂ) : (arg z : Real.Angle).toReal = arg z := by
  rw [Real.Angle.toReal_coe_eq_self_iff_mem_Ioc]
  exact arg_mem_Ioc _
/-
**Complex.arg_coe_angle_eq_iff_eq_toReal** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_coe_angle_eq_iff_eq_toReal {z : Complex} {θ : Real.Angle} : (arg z : R
eal.Angle) = θ ↔ arg z = θ.toReal
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.Angle.toReal_inj`：toReal_inj {θ ψ : Angle} : θ.toReal = ψ.toReal ↔ 
θ = ψ
· 使用定理 `Complex.arg_coe_angle_toReal_eq_arg`：arg_coe_angle_toReal_eq_arg (z : Co
mplex) : (arg z : Real.Angle).toReal = arg z
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem arg_coe_angle_eq_iff_eq_toReal {z : ℂ} {θ : Real.Angle} :
    (arg z : Real.Angle) = θ ↔ arg z = θ.toReal := by
  rw [← Real.Angle.toReal_inj, arg_coe_angle_toReal_eq_arg]

@[simp]
/-
**Complex.arg_coe_angle_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_coe_angle_eq_iff {x y : Complex} : (arg x : Real.Angle) = arg y ↔ arg 
x = arg y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Complex.arg_coe_angle_toReal_eq_arg`：arg_coe_angle_toReal_eq_arg (z : Co
mplex) : (arg z : Real.Angle).toReal = arg z
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem arg_coe_angle_eq_iff {x y : ℂ} : (arg x : Real.Angle) = arg y ↔ arg x = arg y := by
  simp_rw [← Real.Angle.toReal_inj, arg_coe_angle_toReal_eq_arg]
/-
**Complex.arg_mul_eq_add_arg_iff** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：arg_mul_eq_add_arg_iff {x y : Complex} (hx₀ : x != 0) (hy₀ : y != 0) : (x 
* y).arg = x.arg + y.arg ↔ arg x + arg y in Set.Ioc (-π) π
参数：hx₀ : x != 0；hy₀ : y != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.arg_coe_angle_toReal_eq_arg`：arg_coe_angle_toReal_eq_arg (z : Co
mplex) : (arg z : Real.Angle).toReal = arg z
· 使用定理 `Complex.arg_mul_coe_angle`：arg_mul_coe_angle {x y : Complex} (hx : x != 
0) (hy : y != 0) : (arg (x * y) : Real.Angle) = arg x + arg y
· 使用定理 `Real.Angle.coe_add`：coe_add (x y : Real) : ↑(x + y : Real) = (↑x + ↑y : 
Angle)
· 使用定理 `Real.Angle.toReal_coe_eq_self_iff_mem_Ioc`：toReal_coe_eq_self_iff_mem_Io
c {θ : Real} : (θ : Angle).toReal = θ ↔ θ in Set.Ioc (-π) π
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma arg_mul_eq_add_arg_iff {x y : ℂ} (hx₀ : x ≠ 0) (hy₀ : y ≠ 0) :
    (x * y).arg = x.arg + y.arg ↔ arg x + arg y ∈ Set.Ioc (-π) π := by
  rw [← arg_coe_angle_toReal_eq_arg, arg_mul_coe_angle hx₀ hy₀, ← Real.Angle.coe_add,
      Real.Angle.toReal_coe_eq_self_iff_mem_Ioc]

alias ⟨_, arg_mul⟩ := arg_mul_eq_add_arg_iff

section slitPlane

open ComplexOrder in
/-- An alternative description of the slit plane as consisting of nonzero complex numbers
whose argument is not π. -/
/-
**Complex.mem_slitPlane_iff_arg** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：mem_slitPlane_iff_arg {z : Complex} : z in slitPlane ↔ z.arg != π ∧ z != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
An alternative description of the slit plane as consisting of nonzero complex nu
mbers
whose argument is not π.
-/
lemma mem_slitPlane_iff_arg {z : ℂ} : z ∈ slitPlane ↔ z.arg ≠ π ∧ z ≠ 0 := by
  simp only [mem_slitPlane_iff_not_le_zero, le_iff_lt_or_eq, ne_eq, arg_eq_pi_iff_lt_zero, not_or]
/-
**Complex.slitPlane_arg_ne_pi** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：slitPlane_arg_ne_pi {z : Complex} (hz : z in slitPlane) : z.arg != Real.pi
参数：hz : z in slitPlane。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Complex.mem_slitPlane_iff_arg`：mem_slitPlane_iff_arg {z : Complex} : z i
n slitPlane ↔ z.arg != π ∧ z != 0
-/
lemma slitPlane_arg_ne_pi {z : ℂ} (hz : z ∈ slitPlane) : z.arg ≠ Real.pi :=
  (mem_slitPlane_iff_arg.mp hz).1
/-
**Complex.exp_mem_slitPlane** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：exp_mem_slitPlane {z : Complex} : exp z in slitPlane ↔ toIocMod Real.two_p
i_pos (-π) z.im != π
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.two_pi_pos`：two_pi_pos : 0 < 2 * π
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Complex.arg_exp`：arg_exp (z : Complex) : arg (exp z) = toIocMod Real.two
_pi_pos (-π) z.im
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem exp_mem_slitPlane {z : ℂ} : exp z ∈ slitPlane ↔ toIocMod Real.two_pi_pos (-π) z.im ≠ π := by
  simp [mem_slitPlane_iff_arg, arg_exp]

end slitPlane

section Continuity

/-
**Complex.arg_eq_nhds_of_re_pos** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_eq_nhds_of_re_pos (hx : 0 < x.re) : arg =ᶠ[𝓝 x] fun x => Real.arcsin (
x.im / ‖x‖)
参数：hx : 0 < x.re。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `Complex.continuous_re`：Continuous Complex.re
· 使用定理 `lt_mem_nhds`：lt_mem_nhds [OrderTopology α] {a b : α} (h : a < b) : foral
lᶠ x in 𝓝 b, a < x
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Complex.arg_of_re_nonneg`：arg_of_re_nonneg {x : Complex} (hx : 0 <= x.re
) : arg x = Real.arcsin (x.im / ‖x‖)
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem arg_eq_nhds_of_re_pos (hx : 0 < x.re) : arg =ᶠ[𝓝 x] fun x => Real.arcsin (x.im / ‖x‖) :=
  ((continuous_re.tendsto _).eventually (lt_mem_nhds hx)).mono fun _ hy => arg_of_re_nonneg hy.le
/-
**Complex.arg_eq_nhds_of_re_neg_of_im_pos** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_eq_nhds_of_re_neg_of_im_pos (hx_re : x.re < 0) (hx_im : 0 < x.im) : ar
g =ᶠ[𝓝 x] fun x => Real.arcsin ((-x).im / ‖x‖) + π
参数：hx_re : x.re < 0；hx_im : 0 < x.im。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.eventually_mem`：IsOpen.eventually_mem (hs : IsOpen s) (hx : x in 
s) : forallᶠ x in 𝓝 x, x in s
· 使用定理 `IsOpen.and`：IsOpen.and : IsOpen { x | p₁ x } -> IsOpen { x | p₂ x } -> I
sOpen { x | p₁ x ∧ p₂ x }
· 使用定理 `isOpen_lt`：isOpen_lt [TopologicalSpace β] {f g : β -> α} (hf : Continuou
s f) (hg : Continuous g) : IsOpen { b | f b < g b }
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Complex.continuous_re`：Continuous Complex.re
· 使用定理 `continuous_zero`：∀ {M : Type u_3} {X : Type u_5} [inst : TopologicalSpac
e X] [inst_1 : TopologicalSpace M] [inst_2 : Zero M],   Continuous 0
· 使用定理 `Complex.continuous_im`：Continuous Complex.im
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Complex.arg_of_re_neg_of_im_nonneg`：arg_of_re_neg_of_im_nonneg {x : Comp
lex} (hx_re : x.re < 0) (hx_im : 0 <= x.im) : arg x = Real.arcsin ((-x).im / ‖x‖
) + π
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem arg_eq_nhds_of_re_neg_of_im_pos (hx_re : x.re < 0) (hx_im : 0 < x.im) :
    arg =ᶠ[𝓝 x] fun x => Real.arcsin ((-x).im / ‖x‖) + π := by
  suffices h_forall_nhds : ∀ᶠ y : ℂ in 𝓝 x, y.re < 0 ∧ 0 < y.im from
    h_forall_nhds.mono fun y hy => arg_of_re_neg_of_im_nonneg hy.1 hy.2.le
  refine IsOpen.eventually_mem ?_ (⟨hx_re, hx_im⟩ : x.re < 0 ∧ 0 < x.im)
  exact
    IsOpen.and (isOpen_lt continuous_re continuous_zero) (isOpen_lt continuous_zero continuous_im)
/-
**Complex.arg_eq_nhds_of_re_neg_of_im_neg** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_eq_nhds_of_re_neg_of_im_neg (hx_re : x.re < 0) (hx_im : x.im < 0) : ar
g =ᶠ[𝓝 x] fun x => Real.arcsin ((-x).im / ‖x‖) - π
参数：hx_re : x.re < 0；hx_im : x.im < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.eventually_mem`：IsOpen.eventually_mem (hs : IsOpen s) (hx : x in 
s) : forallᶠ x in 𝓝 x, x in s
· 使用定理 `IsOpen.and`：IsOpen.and : IsOpen { x | p₁ x } -> IsOpen { x | p₂ x } -> I
sOpen { x | p₁ x ∧ p₂ x }
· 使用定理 `isOpen_lt`：isOpen_lt [TopologicalSpace β] {f g : β -> α} (hf : Continuou
s f) (hg : Continuous g) : IsOpen { b | f b < g b }
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Complex.continuous_re`：Continuous Complex.re
· 使用定理 `continuous_zero`：∀ {M : Type u_3} {X : Type u_5} [inst : TopologicalSpac
e X] [inst_1 : TopologicalSpace M] [inst_2 : Zero M],   Continuous 0
· 使用定理 `Complex.continuous_im`：Continuous Complex.im
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Complex.arg_of_re_neg_of_im_neg`：arg_of_re_neg_of_im_neg {x : Complex} (
hx_re : x.re < 0) (hx_im : x.im < 0) : arg x = Real.arcsin ((-x).im / ‖x‖) - π
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem arg_eq_nhds_of_re_neg_of_im_neg (hx_re : x.re < 0) (hx_im : x.im < 0) :
    arg =ᶠ[𝓝 x] fun x => Real.arcsin ((-x).im / ‖x‖) - π := by
  suffices h_forall_nhds : ∀ᶠ y : ℂ in 𝓝 x, y.re < 0 ∧ y.im < 0 from
    h_forall_nhds.mono fun y hy => arg_of_re_neg_of_im_neg hy.1 hy.2
  refine IsOpen.eventually_mem ?_ (⟨hx_re, hx_im⟩ : x.re < 0 ∧ x.im < 0)
  exact
    IsOpen.and (isOpen_lt continuous_re continuous_zero) (isOpen_lt continuous_im continuous_zero)
/-
**Complex.arg_eq_nhds_of_im_pos** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_eq_nhds_of_im_pos (hz : 0 < im z) : arg =ᶠ[𝓝 z] fun x => Real.arccos (
x.re / ‖x‖)
参数：hz : 0 < im z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `Complex.continuous_im`：Continuous Complex.im
· 使用定理 `lt_mem_nhds`：lt_mem_nhds [OrderTopology α] {a b : α} (h : a < b) : foral
lᶠ x in 𝓝 b, a < x
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Complex.arg_of_im_pos`：arg_of_im_pos {z : Complex} (hz : 0 < z.im) : arg
 z = Real.arccos (z.re / ‖z‖)
-/
theorem arg_eq_nhds_of_im_pos (hz : 0 < im z) : arg =ᶠ[𝓝 z] fun x => Real.arccos (x.re / ‖x‖) :=
  ((continuous_im.tendsto _).eventually (lt_mem_nhds hz)).mono fun _ => arg_of_im_pos
/-
**Complex.arg_eq_nhds_of_im_neg** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：arg_eq_nhds_of_im_neg (hz : im z < 0) : arg =ᶠ[𝓝 z] fun x => -Real.arccos 
(x.re / ‖x‖)
参数：hz : im z < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `Complex.continuous_im`：Continuous Complex.im
· 使用定理 `gt_mem_nhds`：∀ {α : Type u} [ts : TopologicalSpace α] [inst : Preorder α
] [OrderTopology α] {a b : α},   b < a → ∀ᶠ (x : α) in nhds b, x < a
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Complex.arg_of_im_neg`：arg_of_im_neg {z : Complex} (hz : z.im < 0) : arg
 z = -Real.arccos (z.re / ‖z‖)
-/
theorem arg_eq_nhds_of_im_neg (hz : im z < 0) : arg =ᶠ[𝓝 z] fun x => -Real.arccos (x.re / ‖x‖) :=
  ((continuous_im.tendsto _).eventually (gt_mem_nhds hz)).mono fun _ => arg_of_im_neg
/-
**Complex.continuousAt_arg** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：continuousAt_arg (h : x in slitPlane) : ContinuousAt arg x
参数：h : x in slitPlane。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_ne_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≠ 0 ↔ a ≠ 0
· 使用定理 `Complex.slitPlane_ne_zero`：∀ {z : ℂ}, z ∈ Complex.slitPlane → z ≠ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `lt_or_lt_iff_ne`：lt_or_lt_iff_ne : a < b ∨ b < a ↔ a != b
· 使用定理 `Complex.mem_slitPlane_iff`：∀ {z : ℂ}, z ∈ Complex.slitPlane ↔ 0 < z.re ∨
 z.im ≠ 0
· 使用定理 `ContinuousAt.congr`：ContinuousAt.congr {g : X -> Y} (hf : ContinuousAt f
 x) (h : f =ᶠ[𝓝 x] g) : ContinuousAt g x
· 使用定理 `ContinuousAt.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace
 Z] {f …
· 使用定理 `Real.continuousAt_arcsin`：continuousAt_arcsin {x : Real} : ContinuousAt 
arcsin x
· 使用定理 `ContinuousAt.div`：∀ {α : Type u_1} {G₀ : Type u_3} [inst : GroupWithZero
 G₀] [inst_1 : TopologicalSpace G₀] [ContinuousInv₀ G₀]   [ContinuousMul G₀] {f 
g : α …
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `instIsTopologicalDivisionRingReal`：IsTopologicalDivisionRing ℝ
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Complex.continuous_im`：Continuous Complex.im
· 使用定理 `continuous_norm`：∀ {E : Type u_4} [inst : SeminormedAddGroup E], Continu
ous fun a => ‖a‖
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Complex.arg_eq_nhds_of_re_pos`：arg_eq_nhds_of_re_pos (hx : 0 < x.re) : a
rg =ᶠ[𝓝 x] fun x => Real.arcsin (x.im / ‖x‖)
· 使用定理 `ContinuousAt.neg`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpa
ce X] [inst_1 : TopologicalSpace G] [inst_2 : Neg G]   [ContinuousNeg G] {f : X 
→ G} {…
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `Real.continuous_arccos`：continuous_arccos : Continuous arccos
· 使用定理 `Complex.continuous_re`：Continuous Complex.re
· 使用定理 `Complex.arg_eq_nhds_of_im_neg`：arg_eq_nhds_of_im_neg (hz : im z < 0) : a
rg =ᶠ[𝓝 z] fun x => -Real.arccos (x.re / ‖x‖)
· 使用定理 `Complex.arg_eq_nhds_of_im_pos`：arg_eq_nhds_of_im_pos (hz : 0 < im z) : a
rg =ᶠ[𝓝 z] fun x => Real.arccos (x.re / ‖x‖)
-/
theorem continuousAt_arg (h : x ∈ slitPlane) : ContinuousAt arg x := by
  have h₀ : ‖x‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    exact slitPlane_ne_zero h
  rw [mem_slitPlane_iff, ← lt_or_lt_iff_ne] at h
  rcases h with (hx_re | hx_im | hx_im)
  exacts [(Real.continuousAt_arcsin.comp
          (continuous_im.continuousAt.div continuous_norm.continuousAt h₀)).congr
      (arg_eq_nhds_of_re_pos hx_re).symm,
    (Real.continuous_arccos.continuousAt.comp
            (continuous_re.continuousAt.div continuous_norm.continuousAt h₀)).neg.congr
      (arg_eq_nhds_of_im_neg hx_im).symm,
    (Real.continuous_arccos.continuousAt.comp
          (continuous_re.continuousAt.div continuous_norm.continuousAt h₀)).congr
      (arg_eq_nhds_of_im_pos hx_im).symm]

@[fun_prop]
/-
**Complex.continuousOn_arg** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：continuousOn_arg : ContinuousOn arg slitPlane
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `Complex.continuousAt_arg`：continuousAt_arg (h : x in slitPlane) : Contin
uousAt arg x
-/
theorem continuousOn_arg : ContinuousOn arg slitPlane :=
  fun _ h ↦ continuousAt_arg h |>.continuousWithinAt
/-
**Complex.tendsto_arg_nhdsWithin_im_neg_of_re_neg_of_im_zero** 是 Mathlib 中的一个定理，
位于命名空间 `Complex`。
形式化陈述：tendsto_arg_nhdsWithin_im_neg_of_re_neg_of_im_zero {z : Complex} (hre : z.
re < 0) (him : z.im = 0) : Tendsto arg (𝓝[{ z : Complex | z.im < 0 }] z) (𝓝 (-π)
)
参数：hre : z.re < 0；him : z.im = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `Real.arcsin_zero`：arcsin_zero : arcsin 0 = 0
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.Tendsto.sub_const`：∀ {G : Type w} {α : Type u} [inst : Topologica
lSpace G] [inst_1 : Sub G] [ContinuousSub G] {c : G} {f : α → G}   {l : Filter α
}, Filter.Tend…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `ContinuousAt.comp_continuousWithinAt`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst_2
 : TopologicalSpace γ] {f …
· 使用定理 `Real.continuousAt_arcsin`：continuousAt_arcsin {x : Real} : ContinuousAt 
arcsin x
· 使用定理 `ContinuousWithinAt.div`：∀ {α : Type u_1} {G₀ : Type u_3} [inst : GroupWi
thZero G₀] [inst_1 : TopologicalSpace G₀] [ContinuousInv₀ G₀]   [ContinuousMul G
₀] {f g : α …
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `instIsTopologicalDivisionRingReal`：IsTopologicalDivisionRing ℝ
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Complex.continuous_im`：Continuous Complex.im
· 使用定理 `continuousWithinAt_neg`：∀ {G : Type w} [inst : TopologicalSpace G] [inst
_1 : Neg G] [ContinuousNeg G] {s : Set G} {x : G},   ContinuousWithinAt Neg.neg 
s x
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Continuous.continuousWithinAt`：Continuous.continuousWithinAt (h : Contin
uous f) : ContinuousWithinAt f s x
（共 48 条，此处仅展示前 30 条）
-/
theorem tendsto_arg_nhdsWithin_im_neg_of_re_neg_of_im_zero {z : ℂ} (hre : z.re < 0)
    (him : z.im = 0) : Tendsto arg (𝓝[{ z : ℂ | z.im < 0 }] z) (𝓝 (-π)) := by
  suffices H : Tendsto (fun x : ℂ => Real.arcsin ((-x).im / ‖x‖) - π)
      (𝓝[{ z : ℂ | z.im < 0 }] z) (𝓝 (-π)) by
    refine H.congr' ?_
    have : ∀ᶠ x : ℂ in 𝓝 z, x.re < 0 := continuous_re.tendsto z (gt_mem_nhds hre)
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds this] with _ him hre
    rw [arg, if_neg hre.not_ge, if_neg him.not_ge]
  convert!
    (Real.continuousAt_arcsin.comp_continuousWithinAt
          ((continuous_im.continuousAt.comp_continuousWithinAt continuousWithinAt_neg).div
            continuous_norm.continuousWithinAt _)).sub_const
      π using 1
  · simp [him]
  · lift z to ℝ using him
    simpa using hre.ne
/-
**Complex.continuousWithinAt_arg_of_re_neg_of_im_zero** 是 Mathlib 中的一个定理，位于命名空间 
`Complex`。
形式化陈述：continuousWithinAt_arg_of_re_neg_of_im_zero {z : Complex} (hre : z.re < 0)
 (him : z.im = 0) : ContinuousWithinAt arg { z : Complex | 0 <= z.im } z
参数：hre : z.re < 0；him : z.im = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `Complex.continuous_re`：Continuous Complex.re
· 使用定理 `gt_mem_nhds`：∀ {α : Type u} [ts : TopologicalSpace α] [inst : Preorder α
] [OrderTopology α] {a b : α},   b < a → ∀ᶠ (x : α) in nhds b, x < a
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `mem_nhdsWithin_of_mem_nhds`：mem_nhdsWithin_of_mem_nhds {s t : Set α} {a 
: α} (h : s in 𝓝 a) : s in 𝓝[t] a
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.arg.eq_1`：∀ (x : ℂ),   x.arg =     if 0 ≤ x.re then Real.arcsin 
(x.im / ‖x‖)     else if 0 ≤ x.im then Real.arcsin ((-x).im / ‖x‖) + Real.pi els
e Real…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `ContinuousWithinAt.congr_of_eventuallyEq`：ContinuousWithinAt.congr_of_ev
entuallyEq (h : ContinuousWithinAt f s x) (h₁ : g =ᶠ[𝓝[s] x] f) (hx : g x = f x)
 : ContinuousWithinAt g s x
· 使用定理 `ContinuousWithinAt.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [in
st_1 : Add M] [ContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {
f g : X → M}…
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
· 使用定理 `ContinuousAt.comp_continuousWithinAt`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst_2
 : TopologicalSpace γ] {f …
· 使用定理 `Real.continuousAt_arcsin`：continuousAt_arcsin {x : Real} : ContinuousAt 
arcsin x
· 使用定理 `ContinuousWithinAt.div`：∀ {α : Type u_1} {G₀ : Type u_3} [inst : GroupWi
thZero G₀] [inst_1 : TopologicalSpace G₀] [ContinuousInv₀ G₀]   [ContinuousMul G
₀] {f g : α …
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `instIsTopologicalDivisionRingReal`：IsTopologicalDivisionRing ℝ
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Complex.continuous_im`：Continuous Complex.im
· 使用定理 `continuousWithinAt_neg`：∀ {G : Type w} [inst : TopologicalSpace G] [inst
_1 : Neg G] [ContinuousNeg G] {s : Set G} {x : G},   ContinuousWithinAt Neg.neg 
s x
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
（共 43 条，此处仅展示前 30 条）
-/
theorem continuousWithinAt_arg_of_re_neg_of_im_zero {z : ℂ} (hre : z.re < 0) (him : z.im = 0) :
    ContinuousWithinAt arg { z : ℂ | 0 ≤ z.im } z := by
  have : arg =ᶠ[𝓝[{ z : ℂ | 0 ≤ z.im }] z] fun x => Real.arcsin ((-x).im / ‖x‖) + π := by
    have : ∀ᶠ x : ℂ in 𝓝 z, x.re < 0 := continuous_re.tendsto z (gt_mem_nhds hre)
    filter_upwards [self_mem_nhdsWithin (s := { z : ℂ | 0 ≤ z.im }),
      mem_nhdsWithin_of_mem_nhds this] with _ him hre
    rw [arg, if_neg hre.not_ge, if_pos him]
  refine ContinuousWithinAt.congr_of_eventuallyEq ?_ this ?_
  · refine
      (Real.continuousAt_arcsin.comp_continuousWithinAt
            ((continuous_im.continuousAt.comp_continuousWithinAt continuousWithinAt_neg).div
              continuous_norm.continuousWithinAt ?_)).add
        tendsto_const_nhds
    lift z to ℝ using him
    simpa using hre.ne
  · rw [arg, if_neg hre.not_ge, if_pos him.ge]
/-
**Complex.tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero** 是 Mathlib 中的一个
定理，位于命名空间 `Complex`。
形式化陈述：tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero {z : Complex} (hre :
 z.re < 0) (him : z.im = 0) : Tendsto arg (𝓝[{ z : Complex | 0 <= z.im }] z) (𝓝 
π)
参数：hre : z.re < 0；him : z.im = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Complex.arg_eq_pi_iff`：arg_eq_pi_iff {z : Complex} : arg z = π ↔ z.re < 
0 ∧ z.im = 0
· 使用定理 `ContinuousWithinAt.tendsto`：ContinuousWithinAt.tendsto (h : ContinuousWi
thinAt f s x) : Tendsto f (𝓝[s] x) (𝓝 (f x))
· 使用定理 `Complex.continuousWithinAt_arg_of_re_neg_of_im_zero`：continuousWithinAt_
arg_of_re_neg_of_im_zero {z : Complex} (hre : z.re < 0) (him : z.im = 0) : Conti
nuousWithinAt arg { z : Complex | 0 <= z.…
-/
theorem tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero {z : ℂ} (hre : z.re < 0)
    (him : z.im = 0) : Tendsto arg (𝓝[{ z : ℂ | 0 ≤ z.im }] z) (𝓝 π) := by
  simpa only [arg_eq_pi_iff.2 ⟨hre, him⟩] using
    (continuousWithinAt_arg_of_re_neg_of_im_zero hre him).tendsto
/-
**Complex.continuousAt_arg_coe_angle** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：continuousAt_arg_coe_angle (h : x != 0) : ContinuousAt ((↑) ∘ arg : Comple
x -> Real.Angle) x
参数：h : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace
 Z] {f …
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Real.Angle.continuous_coe`：continuous_coe : Continuous ((↑) : Real -> An
gle)
· 使用定理 `Complex.continuousAt_arg`：continuousAt_arg (h : x in slitPlane) : Contin
uousAt arg x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_id`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β), f ∘ id = 
f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Function.comp_assoc`：comp_assoc (f : φ -> δ) (g : β -> φ) (h : α -> β) :
 (f ∘ g) ∘ h = f ∘ g ∘ h
· 使用定理 `Function.update_eq_iff`：update_eq_iff {a : α} {b : β a} {f g : forall a,
 β a} : update f a b = g ↔ b = g a ∧ forall x != a, f x = g x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.arg_zero`：arg_zero : arg 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Complex.arg_neg_coe_angle`：arg_neg_coe_angle {x : Complex} (hx : x != 0)
 : (arg (-x) : Real.Angle) = arg x + π
· 使用定理 `Function.mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Complex.mem_slitPlane_iff`：∀ {z : ℂ}, z ∈ Complex.slitPlane ↔ 0 < z.re ∨
 z.im ≠ 0
· 使用定理 `ContinuousAt.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1 :
 Add M] [ContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f g : 
X → M}…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Complex.neg_re`：neg_re (z : Complex) : (-z).re = -z.re
· 使用定理 `neg_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStri
ctMono α] {a : α}, 0 < -a ↔ a < 0
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
（共 45 条，此处仅展示前 30 条）
-/
theorem continuousAt_arg_coe_angle (h : x ≠ 0) : ContinuousAt ((↑) ∘ arg : ℂ → Real.Angle) x := by
  by_cases hs : x ∈ slitPlane
  · exact Real.Angle.continuous_coe.continuousAt.comp (continuousAt_arg hs)
  · rw [← Function.comp_id (((↑) : ℝ → Real.Angle) ∘ arg),
      (funext_iff.2 fun _ => (neg_neg _).symm : (id : ℂ → ℂ) = Neg.neg ∘ Neg.neg), ←
      Function.comp_assoc]
    refine ContinuousAt.comp ?_ continuous_neg.continuousAt
    suffices ContinuousAt (Function.update (((↑) ∘ arg) ∘ Neg.neg : ℂ → Real.Angle) 0 π) (-x) by
      rwa [continuousAt_update_of_ne (neg_ne_zero.2 h)] at this
    have ha :
      Function.update (((↑) ∘ arg) ∘ Neg.neg : ℂ → Real.Angle) 0 π = fun z =>
        (arg z : Real.Angle) + π := by
      rw [Function.update_eq_iff]
      exact ⟨by simp, fun z hz => arg_neg_coe_angle hz⟩
    rw [ha]
    replace hs := mem_slitPlane_iff.mpr.mt hs
    push Not at hs
    refine
      (Real.Angle.continuous_coe.continuousAt.comp (continuousAt_arg (Or.inl ?_))).add
        continuousAt_const
    rw [neg_re, neg_pos]
    exact hs.1.lt_of_ne fun h0 => h (Complex.ext_iff.2 ⟨h0, hs.2⟩)

end Continuity

end Complex

