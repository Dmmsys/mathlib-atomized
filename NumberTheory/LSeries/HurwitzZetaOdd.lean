/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.NumberTheory.LSeries.AbstractFuncEq
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
public import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
public import Mathlib.NumberTheory.LSeries.Basic

/-!
# Odd Hurwitz zeta functions

In this file we study the functions on `ℂ` which are the analytic continuation of the following
series (convergent for `1 < re s`), where `a ∈ ℝ` is a parameter:

`hurwitzZetaOdd a s = 1 / 2 * ∑' n : ℤ, sgn (n + a) / |n + a| ^ s`

and

`sinZeta a s = ∑' n : ℕ, sin (2 * π * a * n) / n ^ s`.

The term for `n = -a` in the first sum is understood as 0 if `a` is an integer, as is the term for
`n = 0` in the second sum (for all `a`). Note that these functions are differentiable everywhere,
unlike their even counterparts which have poles.

Of course, we cannot *define* these functions by the above formulae (since existence of the
analytic continuation is not at all obvious); we in fact construct them as Mellin transforms of
various versions of the Jacobi theta function.

## Main definitions and theorems

* `completedHurwitzZetaOdd`: the completed Hurwitz zeta function
* `completedSinZeta`: the completed sine zeta function
* `differentiable_completedHurwitzZetaOdd` and `differentiable_completedSinZeta`:
  differentiability on `ℂ`
* `completedHurwitzZetaOdd_one_sub`: the functional equation
  `completedHurwitzZetaOdd a (1 - s) = completedSinZeta a s`
* `hasSum_int_hurwitzZetaOdd` and `hasSum_nat_sinZeta`: relation between
  the zeta functions and corresponding Dirichlet series for `1 < re s`
-/

@[expose] public section

noncomputable section

open Complex
open CharZero Filter Topology Asymptotics Real Set MeasureTheory
open scoped ComplexConjugate

namespace HurwitzZeta

section kernel_defs
/-!
## Definitions and elementary properties of kernels
-/

/-- Variant of `jacobiTheta₂'` which we introduce to simplify some formulae. -/
/-
**HurwitzZeta.jacobiTheta** 是 Mathlib 中的一个定义，位于命名空间 `HurwitzZeta`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Variant of `jacobiTheta₂'` which we introduce to simplify some formulae.
-/
def jacobiTheta₂'' (z τ : ℂ) : ℂ :=
  cexp (π * I * z ^ 2 * τ) * (jacobiTheta₂' (z * τ) τ / (2 * π * I) + z * jacobiTheta₂ (z * τ) τ)
/-
**HurwitzZeta.jacobiTheta** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma jacobiTheta₂''_conj (z τ : ℂ) :
    conj (jacobiTheta₂'' z τ) = jacobiTheta₂'' (conj z) (-conj τ) := by
  simp [jacobiTheta₂'', jacobiTheta₂'_conj, jacobiTheta₂_conj, ← exp_conj, map_ofNat, div_neg,
    neg_div, jacobiTheta₂'_neg_left]

/-- Restatement of `jacobiTheta₂'_add_left'`: the function `jacobiTheta₂''` is 1-periodic in `z`. -/
/-
**HurwitzZeta.jacobiTheta** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restatement of `jacobiTheta₂'_add_left'`: the function `jacobiTheta₂''` is 1-per
iodic in `z`.
-/
lemma jacobiTheta₂''_add_left (z τ : ℂ) : jacobiTheta₂'' (z + 1) τ = jacobiTheta₂'' z τ := by
  simp only [jacobiTheta₂'', add_mul z 1, one_mul, jacobiTheta₂'_add_left', jacobiTheta₂_add_left']
  generalize jacobiTheta₂ (z * τ) τ = J
  generalize jacobiTheta₂' (z * τ) τ = J'
  -- clear denominator
  simp_rw [div_add' _ _ _ two_pi_I_ne_zero, ← mul_div_assoc]
  refine congr_arg (· / (2 * π * I)) ?_
  -- get all exponential terms to left
  rw [mul_left_comm _ (cexp _), ← mul_add, mul_assoc (cexp _), ← mul_add, ← mul_assoc (cexp _),
    ← Complex.exp_add]
  congrm (cexp ?_ * ?_) <;> ring
/-
**HurwitzZeta.jacobiTheta** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma jacobiTheta₂''_neg_left (z τ : ℂ) : jacobiTheta₂'' (-z) τ = -jacobiTheta₂'' z τ := by
  simp [jacobiTheta₂'', jacobiTheta₂'_neg_left, neg_div, -neg_add_rev, ← neg_add]
/-
**HurwitzZeta.jacobiTheta** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma jacobiTheta₂'_functional_equation' (z τ : ℂ) :
    jacobiTheta₂' z τ = (-2 * π) / (-I * τ) ^ (3 / 2 : ℂ) * jacobiTheta₂'' z (-1 / τ) := by
  rcases eq_or_ne τ 0 with rfl | hτ
  · rw [jacobiTheta₂'_undef _ (by simp), mul_zero, zero_cpow (by simp), div_zero, zero_mul]
  have aux1 : (-2 * π : ℂ) / (2 * π * I) = I := by
    rw [div_eq_iff two_pi_I_ne_zero, mul_comm I, mul_assoc _ I I, I_mul_I, neg_mul, mul_neg,
      mul_one]
  rw [jacobiTheta₂'_functional_equation, ← mul_one_div _ τ, mul_right_comm _ (cexp _),
    (by rw [cpow_one, ← div_div, div_self (neg_ne_zero.mpr I_ne_zero)] :
      1 / τ = -I / (-I * τ) ^ (1 : ℂ)), div_mul_div_comm,
    ← cpow_add _ _ (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hτ), ← div_mul_eq_mul_div,
    (by norm_num : (1 / 2 + 1 : ℂ) = 3 / 2), mul_assoc (1 / _), mul_assoc (1 / _),
    ← mul_one_div (-2 * π : ℂ), mul_comm _ (1 / _), mul_assoc (1 / _)]
  congr 1
  rw [jacobiTheta₂'', div_add' _ _ _ two_pi_I_ne_zero, ← mul_div_assoc, ← mul_div_assoc,
    ← div_mul_eq_mul_div (-2 * π : ℂ), mul_assoc, aux1, mul_div z (-1), mul_neg_one, neg_div τ z,
    jacobiTheta₂_neg_left, jacobiTheta₂'_neg_left, neg_mul, ← mul_neg, ← mul_neg,
    mul_div, mul_neg_one, neg_div, neg_mul, neg_mul, neg_div]
  congr 2
  rw [neg_sub, ← sub_eq_neg_add, mul_comm _ (_ * I), ← mul_assoc]

/-- Odd Hurwitz zeta kernel (function whose Mellin transform will be the odd part of the completed
Hurwitz zeta function). See `oddKernel_def` for the defining formula, and `hasSum_int_oddKernel`
for an expression as a sum over `ℤ`.
-/
/-
**HurwitzZeta.oddKernel** 是 Mathlib 中的一个定义，位于命名空间 `HurwitzZeta`。
形式化陈述：UnitAddCircle → ℝ → ℝ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Odd Hurwitz zeta kernel (function whose Mellin transform will be the odd part of
 the completed
Hurwitz zeta function). See `oddKernel_def` for the defining formula, and `hasSu
m_int_oddKernel`
for an expression as a sum over `ℤ`.
-/
@[irreducible] def oddKernel (a : UnitAddCircle) (x : ℝ) : ℝ :=
  (show Function.Periodic (fun a : ℝ ↦ re (jacobiTheta₂'' a (I * x))) 1 by
    simp [jacobiTheta₂''_add_left]).lift a
/-
**HurwitzZeta.oddKernel_def** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：oddKernel_def (a x : Real) : ↑(oddKernel a x) = jacobiTheta₂'' a (I * x)
参数：a x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HurwitzZeta.oddKernel.eq_1`：∀ (a : UnitAddCircle) (x : ℝ), HurwitzZeta.o
ddKernel a x = ⋯.lift a
· 使用定理 `HurwitzZeta.jacobiTheta₂''_conj`：∀ (z τ : ℂ),   (starRingEnd ℂ) (Hurwitz
Zeta.jacobiTheta₂'' z τ) = HurwitzZeta.jacobiTheta₂'' ((starRingEnd ℂ) z) (-(sta
rRingEnd ℂ) τ)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Complex.conj_ofReal`：conj_ofReal (r : Real) : conj (r : Complex) = r
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Complex.conj_I`：conj_I : conj I = -I
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma oddKernel_def (a x : ℝ) : ↑(oddKernel a x) = jacobiTheta₂'' a (I * x) := by
  simp [oddKernel, ← conj_eq_iff_re, jacobiTheta₂''_conj]
/-
**HurwitzZeta.oddKernel_def'** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：oddKernel_def' (a x : Real) : ↑(oddKernel ↑a x) = cexp (-π * a ^ 2 * x) * 
(jacobiTheta₂' (a * I * x) (I * x) / (2 * π * I) + a * jacobiTheta₂ (a * I * x) 
(I * x))
参数：a x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HurwitzZeta.oddKernel_def`：oddKernel_def (a x : Real) : ↑(oddKernel a x)
 = jacobiTheta₂'' a (I * x)
· 使用定理 `HurwitzZeta.jacobiTheta₂''.eq_1`：∀ (z τ : ℂ),   HurwitzZeta.jacobiTheta₂
'' z τ =     Complex.exp (↑Real.pi * Complex.I * z ^ 2 * τ) *       (jacobiTheta
₂' (z * τ) τ / (2 * ↑…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pow_mul`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₂ c₂ : R} {ea₁ b c₁ : ℕ} {xa₁ c₃ d : R},   ea₁ * b = c₁ → a₂ ^ b = c₂
 → xa₁ ^ c₁ * Nat.rawCast 1 …
· 使用定理 `Mathlib.Tactic.Ring.Common.one_pow`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a : R} (b : ℕ), Mathlib.Meta.NormNum.IsNat a 1 → a ^ b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R) {e : R}, Nat.rawCast 1 = e → a ^ 0 = e + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pp_pf_overlap`：∀ {R : Type u_1} [inst : C
ommSemiring R] {a₂ b₂ c : R} {ea eb e : ℕ} (x : R),   ea + eb = e → a₂ * b₂ = c 
→ x ^ ea * a₂ * (x ^ eb * b₂) = x …
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
（共 32 条，此处仅展示前 30 条）
-/
lemma oddKernel_def' (a x : ℝ) : ↑(oddKernel ↑a x) = cexp (-π * a ^ 2 * x) *
    (jacobiTheta₂' (a * I * x) (I * x) / (2 * π * I) + a * jacobiTheta₂ (a * I * x) (I * x)) := by
  rw [oddKernel_def, jacobiTheta₂'', ← mul_assoc ↑a I x,
    (by ring : ↑π * I * ↑a ^ 2 * (I * ↑x) = I ^ 2 * ↑π * ↑a ^ 2 * x), I_sq, neg_one_mul]
/-
**HurwitzZeta.oddKernel_undef** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：oddKernel_undef (a : UnitAddCircle) {x : Real} (hx : x <= 0) : oddKernel a
 x = 0
参数：a : UnitAddCircle；hx : x <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientAddGroup.induction_on`：∀ {α : Type u_1} [inst : AddGroup α] {s :
 AddSubgroup α} {C : α ⧸ s → Prop} (x : α ⧸ s), (∀ (z : α), C ↑z) → C x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.ofReal_eq_zero`：ofReal_eq_zero {z : Real} : (z : Complex) = 0 ↔ 
z = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `HurwitzZeta.oddKernel_def'`：oddKernel_def' (a x : Real) : ↑(oddKernel ↑a
 x) = cexp (-π * a ^ 2 * x) * (jacobiTheta₂' (a * I * x) (I * x) / (2 * π * I) +
 a * jacobiTheta…
· 使用引理 `jacobiTheta₂_undef`：jacobiTheta₂_undef (z : Complex) {τ : Complex} (hτ :
 im τ <= 0) : jacobiTheta₂ z τ = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `jacobiTheta₂'_undef`：∀ (z : ℂ) {τ : ℂ}, τ.im ≤ 0 → jacobiTheta₂' z τ = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
-/
lemma oddKernel_undef (a : UnitAddCircle) {x : ℝ} (hx : x ≤ 0) : oddKernel a x = 0 := by
  induction a using QuotientAddGroup.induction_on with | H a' =>
  rw [← ofReal_eq_zero, oddKernel_def', jacobiTheta₂_undef, jacobiTheta₂'_undef, zero_div, zero_add,
    mul_zero, mul_zero] <;>
  simpa

/-- Auxiliary function appearing in the functional equation for the odd Hurwitz zeta kernel, equal
to `∑ (n : ℕ), 2 * n * sin (2 * π * n * a) * exp (-π * n ^ 2 * x)`. See `hasSum_nat_sinKernel`
for the defining sum. -/
/-
**HurwitzZeta.sinKernel** 是 Mathlib 中的一个定义，位于命名空间 `HurwitzZeta`。
形式化陈述：UnitAddCircle → ℝ → ℝ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary function appearing in the functional equation for the odd Hurwitz zeta
 kernel, equal
to `∑ (n : ℕ), 2 * n * sin (2 * π * n * a) * exp (-π * n ^ 2 * x)`. See `hasSum_
nat_sinKernel`
for the defining sum.
-/
@[irreducible] def sinKernel (a : UnitAddCircle) (x : ℝ) : ℝ :=
  (show Function.Periodic (fun ξ : ℝ ↦ re (jacobiTheta₂' ξ (I * x) / (-2 * π))) 1 by
    simp [jacobiTheta₂'_add_left]).lift a
/-
**HurwitzZeta.sinKernel_def** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：sinKernel_def (a x : Real) : ↑(sinKernel ↑a x) = jacobiTheta₂' a (I * x) /
 (-2 * π)
参数：a x : Real。
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `HurwitzZeta.sinKernel.eq_1`：∀ (a : UnitAddCircle) (x : ℝ), HurwitzZeta.s
inKernel a x = ⋯.lift a
· 使用定理 `Function.Periodic.lift.congr_simp`：∀ {α : Type u_1} {β : Type u_2} {f f_
1 : α → β} (e_f : f = f_1) {c : α} [inst : AddGroup α] (h : Function.Periodic f 
c)   (x x_1 : α ⧸ AddSu…
· 使用定理 `Complex.re_eq_add_conj`：re_eq_add_conj (z : Complex) : (z.re : Complex) 
= (z + conj z) / 2
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `jacobiTheta₂'_conj`：∀ (z τ : ℂ), (starRingEnd ℂ) (jacobiTheta₂' z τ) = j
acobiTheta₂' ((starRingEnd ℂ) z) (-(starRingEnd ℂ) τ)
· 使用定理 `Complex.conj_ofReal`：conj_ofReal (r : Real) : conj (r : Complex) = r
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Complex.conj_I`：conj_I : conj I = -I
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `RingHomClass.toLinearMapClassNNRat`：∀ {F : Type u_1} {R : Type u_2} {S :
 Type u_3} [inst : DivisionSemiring R] [inst_1 : CharZero R]   [inst_2 : Divisio
nSemiring S] [inst_3 : C…
· 使用定理 `map_ofNat`：map_ofNat [FunLike F R S] [RingHomClass F R S] (f : F) (n : N
at) [Nat.AtLeastTwo n] : (f ofNat(n) : S) = OfNat.ofNat n
· 使用定理 `add_self_div_two`：∀ {K : Type u_1} [inst : DivisionSemiring K] [NeZero 2
] (a : K), (a + a) / 2 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sinKernel_def (a x : ℝ) : ↑(sinKernel ↑a x) = jacobiTheta₂' a (I * x) / (-2 * π) := by
  simp [sinKernel, re_eq_add_conj, jacobiTheta₂'_conj, map_ofNat]
/-
**HurwitzZeta.sinKernel_undef** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：sinKernel_undef (a : UnitAddCircle) {x : Real} (hx : x <= 0) : sinKernel a
 x = 0
参数：a : UnitAddCircle；hx : x <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientAddGroup.induction_on`：∀ {α : Type u_1} [inst : AddGroup α] {s :
 AddSubgroup α} {C : α ⧸ s → Prop} (x : α ⧸ s), (∀ (z : α), C ↑z) → C x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.ofReal_eq_zero`：ofReal_eq_zero {z : Real} : (z : Complex) = 0 ↔ 
z = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `HurwitzZeta.sinKernel_def`：sinKernel_def (a x : Real) : ↑(sinKernel ↑a x
) = jacobiTheta₂' a (I * x) / (-2 * π)
· 使用定理 `jacobiTheta₂'_undef`：∀ (z : ℂ) {τ : ℂ}, τ.im ≤ 0 → jacobiTheta₂' z τ = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
-/
lemma sinKernel_undef (a : UnitAddCircle) {x : ℝ} (hx : x ≤ 0) : sinKernel a x = 0 := by
  induction a using QuotientAddGroup.induction_on with
  | H a => rw [← ofReal_eq_zero, sinKernel_def, jacobiTheta₂'_undef _ (by simpa), zero_div]
/-
**HurwitzZeta.oddKernel_neg** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：oddKernel_neg (a : UnitAddCircle) (x : Real) : oddKernel (-a) x = -oddKern
el a x
参数：a : UnitAddCircle；x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientAddGroup.induction_on`：∀ {α : Type u_1} [inst : AddGroup α] {s :
 AddSubgroup α} {C : α ⧸ s → Prop} (x : α ⧸ s), (∀ (z : α), C ↑z) → C x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HurwitzZeta.oddKernel_def`：oddKernel_def (a x : Real) : ↑(oddKernel a x)
 = jacobiTheta₂'' a (I * x)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
· 使用定理 `HurwitzZeta.jacobiTheta₂''_neg_left`：∀ (z τ : ℂ), HurwitzZeta.jacobiThet
a₂'' (-z) τ = -HurwitzZeta.jacobiTheta₂'' z τ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma oddKernel_neg (a : UnitAddCircle) (x : ℝ) : oddKernel (-a) x = -oddKernel a x := by
  induction a using QuotientAddGroup.induction_on with
  | H a => simp [← ofReal_inj, ← QuotientAddGroup.mk_neg, oddKernel_def, jacobiTheta₂''_neg_left]
/-
**HurwitzZeta.oddKernel_zero** 是 Mathlib 中的一个定理，位于命名空间 `HurwitzZeta`。
形式化陈述：∀ (x : ℝ), HurwitzZeta.oddKernel 0 x = 0
参数：x : ℝ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `HurwitzZeta.oddKernel_neg`：oddKernel_neg (a : UnitAddCircle) (x : Real) 
: oddKernel (-a) x = -oddKernel a x
-/
@[simp] lemma oddKernel_zero (x : ℝ) : oddKernel 0 x = 0 := by
  simpa using oddKernel_neg 0 x
/-
**HurwitzZeta.sinKernel_neg** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：sinKernel_neg (a : UnitAddCircle) (x : Real) : sinKernel (-a) x = -sinKern
el a x
参数：a : UnitAddCircle；x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientAddGroup.induction_on`：∀ {α : Type u_1} [inst : AddGroup α] {s :
 AddSubgroup α} {C : α ⧸ s → Prop} (x : α ⧸ s), (∀ (z : α), C ↑z) → C x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HurwitzZeta.sinKernel_def`：sinKernel_def (a x : Real) : ↑(sinKernel ↑a x
) = jacobiTheta₂' a (I * x) / (-2 * π)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
· 使用定理 `jacobiTheta₂'_neg_left`：∀ (z τ : ℂ), jacobiTheta₂' (-z) τ = -jacobiTheta
₂' z τ
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sinKernel_neg (a : UnitAddCircle) (x : ℝ) :
    sinKernel (-a) x = -sinKernel a x := by
  induction a using QuotientAddGroup.induction_on with
  | H a => simp [← ofReal_inj, ← QuotientAddGroup.mk_neg, sinKernel_def, jacobiTheta₂'_neg_left,
      neg_div]
/-
**HurwitzZeta.sinKernel_zero** 是 Mathlib 中的一个定理，位于命名空间 `HurwitzZeta`。
形式化陈述：∀ (x : ℝ), HurwitzZeta.sinKernel 0 x = 0
参数：x : ℝ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `HurwitzZeta.sinKernel_neg`：sinKernel_neg (a : UnitAddCircle) (x : Real) 
: sinKernel (-a) x = -sinKernel a x
-/
@[simp] lemma sinKernel_zero (x : ℝ) : sinKernel 0 x = 0 := by
  simpa using sinKernel_neg 0 x

/-- The odd kernel is continuous on `Ioi 0`. -/
/-
**HurwitzZeta.continuousOn_oddKernel** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：continuousOn_oddKernel (a : UnitAddCircle) : ContinuousOn (oddKernel a) (I
oi 0)
参数：a : UnitAddCircle。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientAddGroup.induction_on`：∀ {α : Type u_1} [inst : AddGroup α] {s :
 AddSubgroup α} {C : α ⧸ s → Prop} (x : α ⧸ s), (∀ (z : α), C ↑z) → C x
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `HurwitzZeta.oddKernel_def'`：oddKernel_def' (a x : Real) : ↑(oddKernel ↑a
 x) = cexp (-π * a ^ 2 * x) * (jacobiTheta₂' (a * I * x) (I * x) / (2 * π * I) +
 a * jacobiTheta…
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `ContinuousAt.mul`：ContinuousAt.mul (hf : ContinuousAt f x) (hg : Continu
ousAt g x) : ContinuousAt (f * g) x
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
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
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
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `ContinuousAt.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1 :
 Add M] [ContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f g : 
X → M}…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `ContinuousAt.div_const`：∀ {α : Type u_1} {G₀ : Type u_3} [inst : DivInvM
onoid G₀] [inst_1 : TopologicalSpace G₀] [SeparatelyContinuousMul G₀]   {f : α →
 G₀} [inst_3…
· 使用定理 `ContinuousAt.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace
 Z] {f …
· 使用引理 `continuousAt_jacobiTheta₂'`：continuousAt_jacobiTheta₂' (z : Complex) {τ 
: Complex} (hτ : 0 < im τ) : ContinuousAt (fun p : Complex × Complex => jacobiTh
eta₂' p.1 p.2) (…
· 使用定理 `Complex.I_mul_im`：I_mul_im (z : Complex) : (I * z).im = z.re
· 使用定理 `Complex.ofReal_re`：ofReal_re (r : Real) : Complex.re (r : Complex) = r
· 使用定理 `continuousAt_const`：continuousAt_const : ContinuousAt (fun _ : X => y) x
· 使用引理 `continuousAt_jacobiTheta₂`：continuousAt_jacobiTheta₂ (z : Complex) {τ : 
Complex} (hτ : 0 < im τ) : ContinuousAt (fun p : Complex × Complex => jacobiThet
a₂ p.1 p.2) (z,…
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
The odd kernel is continuous on `Ioi 0`.
-/
lemma continuousOn_oddKernel (a : UnitAddCircle) : ContinuousOn (oddKernel a) (Ioi 0) := by
  induction a using QuotientAddGroup.induction_on with | H a =>
  suffices ContinuousOn (fun x ↦ (oddKernel a x : ℂ)) (Ioi 0) from
    (continuous_re.comp_continuousOn this).congr fun a _ ↦ (ofReal_re _).symm
  simp_rw [oddKernel_def' a]
  refine fun x hx ↦ ((Continuous.continuousAt ?_).mul ?_).continuousWithinAt
  · fun_prop
  · have hf : Continuous fun u : ℝ ↦ (a * I * u, I * u) := by fun_prop
    apply ContinuousAt.add
    · exact ((continuousAt_jacobiTheta₂' (a * I * x) (by rwa [I_mul_im, ofReal_re])).comp
        (f := fun u : ℝ ↦ (a * I * u, I * u)) hf.continuousAt).div_const _
    · exact continuousAt_const.mul <| (continuousAt_jacobiTheta₂ (a * I * x)
        (by rwa [I_mul_im, ofReal_re])).comp (f := fun u : ℝ ↦ (a * I * u, I * u)) hf.continuousAt
/-
**HurwitzZeta.continuousOn_sinKernel** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：continuousOn_sinKernel (a : UnitAddCircle) : ContinuousOn (sinKernel a) (I
oi 0)
参数：a : UnitAddCircle。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientAddGroup.induction_on`：∀ {α : Type u_1} [inst : AddGroup α] {s :
 AddSubgroup α} {C : α ⧸ s → Prop} (x : α ⧸ s), (∀ (z : α), C ↑z) → C x
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `HurwitzZeta.sinKernel_def`：sinKernel_def (a x : Real) : ↑(sinKernel ↑a x
) = jacobiTheta₂' a (I * x) / (-2 * π)
· 使用定理 `ContinuousOn.div_const`：ContinuousOn.div_const (hf : ContinuousOn f s) (
y : G₀) : ContinuousOn (fun x => f x / y) s
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
· 使用定理 `continuousOn_of_forall_continuousAt`：continuousOn_of_forall_continuousAt
 (hcont : forall x in s, ContinuousAt f x) : ContinuousOn f s
· 使用引理 `continuousAt_jacobiTheta₂'`：continuousAt_jacobiTheta₂' (z : Complex) {τ 
: Complex} (hτ : 0 < im τ) : ContinuousAt (fun p : Complex × Complex => jacobiTh
eta₂' p.1 p.2) (…
· 使用定理 `Complex.I_mul_im`：I_mul_im (z : Complex) : (I * z).im = z.re
· 使用定理 `Complex.ofReal_re`：ofReal_re (r : Real) : Complex.re (r : Complex) = r
· 使用定理 `ContinuousAt.comp'`：ContinuousAt.comp' {g : Y -> Z} {x : X} (hg : Contin
uousAt g (f x)) (hf : ContinuousAt f x) : ContinuousAt (fun x => g (f x)) x
· 使用定理 `ContinuousAt.prodMk`：ContinuousAt.prodMk {f : X -> Y} {g : X -> Z} {x : 
X} (hf : ContinuousAt f x) (hg : ContinuousAt g x) : ContinuousAt (fun x => (f x
, g x)) x
· 使用定理 `continuousAt_const`：continuousAt_const : ContinuousAt (fun _ : X => y) x
· 使用定理 `ContinuousAt.const_mul`：ContinuousAt.const_mul (hf : ContinuousAt f x) (
b : M) : ContinuousAt (b * f ·) x
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
· 使用定理 `ContinuousOn.congr`：ContinuousOn.congr (h : ContinuousOn f s) (h' : EqOn
 g f s) : ContinuousOn g s
· 使用定理 `Continuous.comp_continuousOn`：Continuous.comp_continuousOn {g : β -> γ} 
{f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continuou
sOn (g ∘ f) s
· 使用定理 `Complex.continuous_re`：Continuous Complex.re
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma continuousOn_sinKernel (a : UnitAddCircle) : ContinuousOn (sinKernel a) (Ioi 0) := by
  induction a using QuotientAddGroup.induction_on with | H a =>
  suffices ContinuousOn (fun x ↦ (sinKernel a x : ℂ)) (Ioi 0) from
    (continuous_re.comp_continuousOn this).congr fun a _ ↦ (ofReal_re _).symm
  simp_rw [sinKernel_def]
  apply (continuousOn_of_forall_continuousAt (fun x hx ↦ ?_)).div_const
  have h := continuousAt_jacobiTheta₂' a (by rwa [I_mul_im, ofReal_re])
  fun_prop
/-
**HurwitzZeta.oddKernel_functional_equation** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZe
ta`。
形式化陈述：oddKernel_functional_equation (a : UnitAddCircle) (x : Real) : oddKernel a
 x = 1 / x ^ (3 / 2 : Real) * sinKernel a (1 / x)
参数：a : UnitAddCircle；x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HurwitzZeta.oddKernel_undef`：oddKernel_undef (a : UnitAddCircle) {x : Re
al} (hx : x <= 0) : oddKernel a x = 0
· 使用引理 `HurwitzZeta.sinKernel_undef`：sinKernel_undef (a : UnitAddCircle) {x : Re
al} (hx : x <= 0) : sinKernel a x = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `one_div_nonpos`：one_div_nonpos : 1 / a <= 0 ↔ a <= 0
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `QuotientAddGroup.induction_on`：∀ {α : Type u_1} [inst : AddGroup α] {s :
 AddSubgroup α} {C : α ⧸ s → Prop} (x : α ⧸ s), (∀ (z : α), C ↑z) → C x
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Complex.ofReal_inv`：ofReal_inv (r : Real) : ((r⁻¹ : Real) : Complex) = (
r : Complex)⁻¹
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_div`：div_div : a / b / c = a / (b * c)
· 使用定理 `div_inv_eq_mul`：div_inv_eq_mul : a / b⁻¹ = a * b
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Complex.inv_I`：inv_I : I⁻¹ = -I
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_one_mul`：neg_one_mul (a : α) : -1 * a = -a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Complex.I_mul_I`：I_mul_I : I * I = -1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Complex.ofReal_div`：ofReal_div (r s : Real) : ((r / s : Real) : Complex)
 = r / s
· 使用定理 `Complex.ofReal_one`：ofReal_one : ((1 : Real) : Complex) = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
（共 56 条，此处仅展示前 30 条）
-/
lemma oddKernel_functional_equation (a : UnitAddCircle) (x : ℝ) :
    oddKernel a x = 1 / x ^ (3 / 2 : ℝ) * sinKernel a (1 / x) := by
  -- first reduce to `0 < x`
  rcases le_or_gt x 0 with hx | hx
  · rw [oddKernel_undef _ hx, sinKernel_undef _ (one_div_nonpos.mpr hx), mul_zero]
  induction a using QuotientAddGroup.induction_on with | H a =>
  have h1 : -1 / (I * ↑(1 / x)) = I * x := by rw [one_div, ofReal_inv, mul_comm, ← div_div,
    div_inv_eq_mul, div_eq_mul_inv, inv_I, mul_neg, neg_one_mul, neg_mul, neg_neg, mul_comm]
  have h2 : (-I * (I * ↑(1 / x))) = 1 / x := by
    rw [← mul_assoc, neg_mul, I_mul_I, neg_neg, one_mul, ofReal_div, ofReal_one]
  have h3 : (x : ℂ) ^ (3 / 2 : ℂ) ≠ 0 := by
    simp only [Ne, cpow_eq_zero_iff, ofReal_eq_zero, hx.ne', false_and, not_false_eq_true]
  have h4 : arg x ≠ π := by rw [arg_ofReal_of_nonneg hx.le]; exact pi_ne_zero.symm
  rw [← ofReal_inj, oddKernel_def, ofReal_mul, sinKernel_def, jacobiTheta₂'_functional_equation',
    h1, h2]
  generalize jacobiTheta₂'' a (I * ↑x) = J
  rw [one_div (x : ℂ), inv_cpow _ _ h4, div_inv_eq_mul, one_div, ofReal_inv, ofReal_cpow hx.le,
    ofReal_div, ofReal_ofNat, ofReal_ofNat, ← mul_div_assoc _ _ (-2 * π : ℂ),
    eq_div_iff <| mul_ne_zero (neg_ne_zero.mpr two_ne_zero) (ofReal_ne_zero.mpr pi_ne_zero),
    ← div_eq_inv_mul, eq_div_iff h3, mul_comm J _, mul_right_comm]

end kernel_defs

section sum_formulas

/-!
## Formulae for the kernels as sums
-/

/-
**HurwitzZeta.hasSum_int_oddKernel** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：hasSum_int_oddKernel (a : Real) {x : Real} (hx : 0 < x) : HasSum (fun n : 
Int => (n + a) * rexp (-π * (n + a) ^ 2 * x)) (oddKernel ↑a x)
参数：a : Real；hx : 0 < x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.hasSum_ofReal`：∀ {α : Type u_1} {L : SummationFilter α} {f : α →
 ℝ} {x : ℝ}, HasSum (fun x => ↑(f x)) (↑x) L ↔ HasSum f x L
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `HurwitzZeta.oddKernel_def'`：oddKernel_def' (a x : Real) : ↑(oddKernel ↑a
 x) = cexp (-π * a ^ 2 * x) * (jacobiTheta₂' (a * I * x) (I * x) / (2 * π * I) +
 a * jacobiTheta…
· 使用引理 `hasSum_jacobiTheta₂_term`：hasSum_jacobiTheta₂_term (z : Complex) {τ : Co
mplex} (hτ : 0 < im τ) : HasSum (fun n => jacobiTheta₂_term n z τ) (jacobiTheta₂
 z τ)
· 使用定理 `Complex.I_mul_im`：I_mul_im (z : Complex) : (I * z).im = z.re
· 使用定理 `Complex.ofReal_re`：ofReal_re (r : Real) : Complex.re (r : Complex) = r
· 使用定理 `hasSum_jacobiTheta₂'_term`：∀ (z : ℂ) {τ : ℂ}, 0 < τ.im → HasSum (fun n =
> jacobiTheta₂'_term n z τ) (jacobiTheta₂' z τ)
· 使用定理 `HasSum.congr_fun`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid 
α] [inst_1 : TopologicalSpace α] {f g : β → α} {a : α}   {L : SummationFilter β}
, HasS…
· 使用定理 `HasSum.mul_left`：HasSum.mul_left (a₂) (h : HasSum f a₁ L) : HasSum (fun 
i => a₂ * f i) (a₂ * a₁) L
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `HasSum.add`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [in
st_1 : TopologicalSpace α] {f g : β → α} {a b : α}   {L : SummationFilter β} [Co
…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `HasSum.div_const`：HasSum.div_const (h : HasSum f a L) (b : α) : HasSum (
fun i => f i / b) (a / b) L
· 使用定理 `jacobiTheta₂'_term.eq_1`：∀ (n : ℤ) (z τ : ℂ), jacobiTheta₂'_term n z τ =
 2 * ↑Real.pi * Complex.I * ↑n * jacobiTheta₂_term n z τ
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
· 使用定理 `Complex.two_pi_I_ne_zero`：two_pi_I_ne_zero : (2 * π * I : Complex) != 0
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `jacobiTheta₂_term.eq_1`：∀ (n : ℤ) (z τ : ℂ),   jacobiTheta₂_term n z τ =
 Complex.exp (2 * ↑Real.pi * Complex.I * ↑n * z + ↑Real.pi * Complex.I * ↑n ^ 2 
* τ)
· 使用定理 `Complex.exp_add`：exp_add : exp (x + y) = exp x * exp y
（共 95 条，此处仅展示前 30 条）

--- 原说明 ---
## Formulae for the kernels as sums
-/
lemma hasSum_int_oddKernel (a : ℝ) {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℤ ↦ (n + a) * rexp (-π * (n + a) ^ 2 * x)) (oddKernel ↑a x) := by
  rw [← hasSum_ofReal, oddKernel_def' a x]
  have h1 := hasSum_jacobiTheta₂_term (a * I * x) (by rwa [I_mul_im, ofReal_re])
  have h2 := hasSum_jacobiTheta₂'_term (a * I * x) (by rwa [I_mul_im, ofReal_re])
  refine (((h2.div_const (2 * π * I)).add (h1.mul_left ↑a)).mul_left
    (cexp (-π * a ^ 2 * x))).congr_fun (fun n ↦ ?_)
  rw [jacobiTheta₂'_term, mul_assoc (2 * π * I), mul_div_cancel_left₀ _ two_pi_I_ne_zero, ← add_mul,
    mul_left_comm, jacobiTheta₂_term, ← Complex.exp_add]
  push_cast
  simp only [← mul_assoc, ← add_mul]
  congrm _ * cexp (?_ * x)
  simp only [mul_right_comm _ I, add_mul, mul_assoc _ I, I_mul_I]
  ring_nf
/-
**HurwitzZeta.hasSum_int_sinKernel** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：hasSum_int_sinKernel (a : Real) {t : Real} (ht : 0 < t) : HasSum (fun n : 
Int => -I * n * cexp (2 * π * I * a * n) * rexp (-π * n ^ 2 * t)) ↑(sinKernel a 
t)
参数：a : Real；ht : 0 < t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `HurwitzZeta.sinKernel_def`：sinKernel_def (a x : Real) : ↑(sinKernel ↑a x
) = jacobiTheta₂' a (I * x) / (-2 * π)
· 使用定理 `HasSum.congr_fun`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid 
α] [inst_1 : TopologicalSpace α] {f g : β → α} {a : α}   {L : SummationFilter β}
, HasS…
· 使用定理 `HasSum.div_const`：HasSum.div_const (h : HasSum f a L) (b : α) : HasSum (
fun i => f i / b) (a / b) L
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `hasSum_jacobiTheta₂'_term`：∀ (z : ℂ) {τ : ℂ}, 0 < τ.im → HasSum (fun n =
> jacobiTheta₂'_term n z τ) (jacobiTheta₂' z τ)
· 使用定理 `Complex.I_mul_im`：I_mul_im (z : Complex) : (I * z).im = z.re
· 使用定理 `Complex.ofReal_re`：ofReal_re (r : Real) : Complex.re (r : Complex) = r
· 使用定理 `jacobiTheta₂'_term.eq_1`：∀ (n : ℤ) (z τ : ℂ), jacobiTheta₂'_term n z τ =
 2 * ↑Real.pi * Complex.I * ↑n * jacobiTheta₂_term n z τ
· 使用定理 `jacobiTheta₂_term.eq_1`：∀ (n : ℤ) (z τ : ℂ),   jacobiTheta₂_term n z τ =
 Complex.exp (2 * ↑Real.pi * Complex.I * ↑n * z + ↑Real.pi * Complex.I * ↑n ^ 2 
* τ)
· 使用定理 `Complex.ofReal_exp`：ofReal_exp (x : Real) : (Real.exp x : Complex) = exp
 x
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.exp_add`：exp_add : exp (x + y) = exp x * exp y
· 使用引理 `eq_div_iff`：eq_div_iff (hb : b != 0) : c = a / b ↔ c * b = a
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `Complex.ofReal_pow`：ofReal_pow (r : Real) (n : Nat) : ((r ^ n : Real) : 
Complex) = (r : Complex) ^ n
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
（共 38 条，此处仅展示前 30 条）
-/
lemma hasSum_int_sinKernel (a : ℝ) {t : ℝ} (ht : 0 < t) : HasSum
    (fun n : ℤ ↦ -I * n * cexp (2 * π * I * a * n) * rexp (-π * n ^ 2 * t)) ↑(sinKernel a t) := by
  have h : -2 * (π : ℂ) ≠ (0 : ℂ) := by
    simp only [neg_mul, ne_eq, neg_eq_zero, mul_eq_zero,
      OfNat.ofNat_ne_zero, ofReal_eq_zero, pi_ne_zero, or_self, not_false_eq_true]
  rw [sinKernel_def]
  refine ((hasSum_jacobiTheta₂'_term a
    (by rwa [I_mul_im, ofReal_re])).div_const _).congr_fun fun n ↦ ?_
  rw [jacobiTheta₂'_term, jacobiTheta₂_term, ofReal_exp, mul_assoc (-I * n), ← Complex.exp_add,
    eq_div_iff h, ofReal_mul, ofReal_mul, ofReal_pow, ofReal_neg, ofReal_intCast,
    mul_comm _ (-2 * π : ℂ), ← mul_assoc]
  congrm ?_ * cexp (?_ + ?_)
  · simp [mul_assoc]
  · exact mul_right_comm (2 * π * I) a n
  · simp [← mul_assoc, mul_comm _ I]
/-
**HurwitzZeta.hasSum_nat_sinKernel** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：hasSum_nat_sinKernel (a : Real) {t : Real} (ht : 0 < t) : HasSum (fun n : 
Nat => 2 * n * Real.sin (2 * π * a * n) * rexp (-π * n ^ 2 * t)) (sinKernel ↑a t
)
参数：a : Real；ht : 0 < t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.hasSum_ofReal`：∀ {α : Type u_1} {L : SummationFilter α} {f : α →
 ℝ} {x : ℝ}, HasSum (fun x => ↑(f x)) (↑x) L ↔ HasSum f x L
· 使用定理 `HasSum.nat_add_neg`：∀ {M : Type u_1} [inst : AddCommMonoid M] [inst_1 : 
TopologicalSpace M] {m : M} [ContinuousAdd M] {f : ℤ → M},   HasSum f m → HasSum
 (fun n …
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
· 使用引理 `HurwitzZeta.hasSum_int_sinKernel`：hasSum_int_sinKernel (a : Real) {t : R
eal} (ht : 0 < t) : HasSum (fun n : Int => -I * n * cexp (2 * π * I * a * n) * r
exp (-π * n ^ 2 * t)) …
· 使用定理 `HasSum.congr_fun`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid 
α] [inst_1 : TopologicalSpace α] {f g : β → α} {a : α}   {L : SummationFilter β}
, HasS…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用引理 `neg_sq`：neg_sq (a : R) : (-a) ^ 2 = a ^ 2
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `Complex.ofReal_sin`：ofReal_sin (x : Real) : (Real.sin x : Complex) = sin
 x
· 使用定理 `Complex.ofReal_exp`：ofReal_exp (x : Real) : (Real.exp x : Complex) = exp
 x
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
· 使用定理 `Complex.ofReal_pow`：ofReal_pow (r : Real) (n : Nat) : ((r ^ n : Real) : 
Complex) = (r : Complex) ^ n
（共 64 条，此处仅展示前 30 条）
-/
lemma hasSum_nat_sinKernel (a : ℝ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ ↦ 2 * n * Real.sin (2 * π * a * n) * rexp (-π * n ^ 2 * t))
    (sinKernel ↑a t) := by
  rw [← hasSum_ofReal]
  have := (hasSum_int_sinKernel a ht).nat_add_neg
  simp only [Int.cast_zero, zero_mul, mul_zero, add_zero] at this
  refine this.congr_fun fun n ↦ ?_
  simp_rw [Int.cast_neg, neg_sq, mul_neg, ofReal_mul, Int.cast_natCast, ofReal_natCast,
      ofReal_ofNat, ← add_mul, ofReal_sin, Complex.sin]
  push_cast
  congr 1
  rw [← mul_div_assoc, ← div_mul_eq_mul_div, ← div_mul_eq_mul_div, div_self two_ne_zero, one_mul,
    neg_mul, neg_mul, neg_neg, mul_comm _ I, ← mul_assoc, mul_comm _ I, neg_mul,
    ← sub_eq_neg_add, mul_sub]
  congr 3 <;> ring

end sum_formulas

section asymp
/-!
## Asymptotics of the kernels as `t → ∞`
-/

/-- The function `oddKernel a` has exponential decay at `+∞`, for any `a`. -/
/-
**HurwitzZeta.isBigO_atTop_oddKernel** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：isBigO_atTop_oddKernel (a : UnitAddCircle) : exists p, 0 < p ∧ IsBigO atTo
p (oddKernel a) (fun x => Real.exp (-p * x))
参数：a : UnitAddCircle。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientAddGroup.induction_on`：∀ {α : Type u_1} [inst : AddGroup α] {s :
 AddSubgroup α} {C : α ⧸ s → Prop} (x : α ⧸ s), (∀ (z : α), C ↑z) → C x
· 使用引理 `HurwitzKernelBounds.isBigO_atTop_F_int_one`：isBigO_atTop_F_int_one (a : 
UnitAddCircle) : exists p, 0 < p ∧ F_int 1 a =O[atTop] fun t => exp (-p * t)
· 使用定理 `Asymptotics.IsBigO.trans`：∀ {α : Type u_1} {E : Type u_3} {G : Type u_5}
 {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : SeminormedAddComm
Group F'] {l :…
· 使用定理 `Filter.Eventually.isBigO`：∀ {α : Type u_1} {E : Type u_3} [inst : Norm E
] {f : α → E} {g : α → ℝ} {l : Filter α},   (∀ᶠ (x : α) in l, ‖f x‖ ≤ g x) → f =
O[l] g
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用引理 `HurwitzZeta.hasSum_int_oddKernel`：hasSum_int_oddKernel (a : Real) {x : R
eal} (hx : 0 < x) : HasSum (fun n : Int => (n + a) * rexp (-π * (n + a) ^ 2 * x)
) (oddKernel ↑a x)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Function.Periodic.lift.congr_simp`：∀ {α : Type u_1} {β : Type u_2} {f f_
1 : α → β} (e_f : f = f_1) {c : α} [inst : AddGroup α] (h : Function.Periodic f 
c)   (x x_1 : α ⧸ AddSu…
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `norm_tsum_le_tsum_norm`：norm_tsum_le_tsum_norm {f : ι -> E} (hf : Summab
le fun i => ‖f i‖) : ‖∑' i, f i‖ <= ∑' i, ‖f i‖
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
The function `oddKernel a` has exponential decay at `+∞`, for any `a`.
-/
lemma isBigO_atTop_oddKernel (a : UnitAddCircle) :
    ∃ p, 0 < p ∧ IsBigO atTop (oddKernel a) (fun x ↦ Real.exp (-p * x)) := by
  induction a using QuotientAddGroup.induction_on with | H b =>
  obtain ⟨p, hp, hp'⟩ := HurwitzKernelBounds.isBigO_atTop_F_int_one b
  refine ⟨p, hp, (Eventually.isBigO ?_).trans hp'⟩
  filter_upwards [eventually_gt_atTop 0] with t ht
  simpa [← (hasSum_int_oddKernel b ht).tsum_eq, HurwitzKernelBounds.F_int,
    HurwitzKernelBounds.f_int, abs_of_nonneg (exp_pos _).le] using
    norm_tsum_le_tsum_norm (hasSum_int_oddKernel b ht).summable.norm

/-- The function `sinKernel a` has exponential decay at `+∞`, for any `a`. -/
/-
**HurwitzZeta.isBigO_atTop_sinKernel** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：isBigO_atTop_sinKernel (a : UnitAddCircle) : exists p, 0 < p ∧ IsBigO atTo
p (sinKernel a) (fun x => Real.exp (-p * x))
参数：a : UnitAddCircle。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientAddGroup.induction_on`：∀ {α : Type u_1} [inst : AddGroup α] {s :
 AddSubgroup α} {C : α ⧸ s → Prop} (x : α ⧸ s), (∀ (z : α), C ↑z) → C x
· 使用引理 `HurwitzKernelBounds.isBigO_atTop_F_nat_one`：isBigO_atTop_F_nat_one {a : 
Real} (ha : 0 <= a) : exists p, 0 < p ∧ F_nat 1 a =O[atTop] fun t => exp (-p * t
)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Asymptotics.IsBigO.trans`：∀ {α : Type u_1} {E : Type u_3} {G : Type u_5}
 {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : SeminormedAddComm
Group F'] {l :…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Filter.Eventually.isBigO`：∀ {α : Type u_1} {E : Type u_3} [inst : Norm E
] {f : α → E} {g : α → ℝ} {l : Filter α},   (∀ᶠ (x : α) in l, ‖f x‖ ≤ g x) → f =
O[l] g
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HurwitzKernelBounds.F_nat.eq_1`：∀ (k : ℕ) (a t : ℝ), HurwitzKernelBounds
.F_nat k a t = ∑' (n : ℕ), HurwitzKernelBounds.f_nat k a t n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用引理 `HurwitzZeta.hasSum_nat_sinKernel`：hasSum_nat_sinKernel (a : Real) {t : R
eal} (ht : 0 < t) : HasSum (fun n : Nat => 2 * n * Real.sin (2 * π * a * n) * re
xp (-π * n ^ 2 * t)) (…
· 使用定理 `tsum_of_norm_bounded`：tsum_of_norm_bounded {f : ι -> E} {g : ι -> Real} 
{a : Real} (hg : HasSum g a) (h : forall i, ‖f i‖ <= g i) : ‖∑' i : ι, f i‖ <= a
· 使用定理 `HasSum.mul_left`：HasSum.mul_left (a₂) (h : HasSum f a₁ L) : HasSum (fun 
i => a₂ * f i) (a₂ * a₁) L
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
· 使用引理 `HurwitzKernelBounds.summable_f_nat`：summable_f_nat (k : Nat) (a : Real) 
{t : Real} (ht : 0 < t) : Summable (f_nat k a t)
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用引理 `Real.norm_two`：norm_two : ‖(2 : Real)‖ = 2
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
（共 53 条，此处仅展示前 30 条）

--- 原说明 ---
The function `sinKernel a` has exponential decay at `+∞`, for any `a`.
-/
lemma isBigO_atTop_sinKernel (a : UnitAddCircle) :
    ∃ p, 0 < p ∧ IsBigO atTop (sinKernel a) (fun x ↦ Real.exp (-p * x)) := by
  induction a using QuotientAddGroup.induction_on with | H a =>
  obtain ⟨p, hp, hp'⟩ := HurwitzKernelBounds.isBigO_atTop_F_nat_one (le_refl 0)
  refine ⟨p, hp, (Eventually.isBigO ?_).trans (hp'.const_mul_left 2)⟩
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [HurwitzKernelBounds.F_nat, ← (hasSum_nat_sinKernel a ht).tsum_eq]
  apply tsum_of_norm_bounded (g := fun n ↦ 2 * HurwitzKernelBounds.f_nat 1 0 t n)
  · exact (HurwitzKernelBounds.summable_f_nat 1 0 ht).hasSum.mul_left _
  · intro n
    rw [norm_mul, norm_mul, norm_mul, norm_two, mul_assoc, mul_assoc,
      mul_le_mul_iff_of_pos_left two_pos, HurwitzKernelBounds.f_nat, pow_one, add_zero,
      norm_of_nonneg (exp_pos _).le, Real.norm_eq_abs, Nat.abs_cast, ← mul_assoc,
      mul_le_mul_iff_of_pos_right (exp_pos _)]
    exact mul_le_of_le_one_right (Nat.cast_nonneg _) (abs_sin_le_one _)

end asymp

section FEPair
/-!
## Construction of an FE-pair
-/

/-- A `StrongFEPair` structure with `f = oddKernel a` and `g = sinKernel a`. -/
@[simps]
/-
**HurwitzZeta.hurwitzOddFEPair** 是 Mathlib 中的一个定义，位于命名空间 `HurwitzZeta`。
形式化陈述：hurwitzOddFEPair (a : UnitAddCircle) : WeakFEPair Complex where f
参数：a : UnitAddCircle。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `StrongFEPair` structure with `f = oddKernel a` and `g = sinKernel a`.
-/
def hurwitzOddFEPair (a : UnitAddCircle) : WeakFEPair ℂ where
  f := ofReal ∘ oddKernel a
  g := ofReal ∘ sinKernel a
  hf_int := (continuous_ofReal.comp_continuousOn (continuousOn_oddKernel a)).locallyIntegrableOn
    measurableSet_Ioi
  hg_int := (continuous_ofReal.comp_continuousOn (continuousOn_sinKernel a)).locallyIntegrableOn
    measurableSet_Ioi
  k := 3 / 2
  hk := by norm_num
  ε := 1
  hε := one_ne_zero
  f₀ := 0
  g₀ := 0
  hf_top r := by
    let ⟨v, hv, hv'⟩ := isBigO_atTop_oddKernel a
    rw [← isBigO_norm_left] at hv' ⊢
    simpa using hv'.trans (isLittleO_exp_neg_mul_rpow_atTop hv _).isBigO
  hg_top r := by
    let ⟨v, hv, hv'⟩ := isBigO_atTop_sinKernel a
    rw [← isBigO_norm_left] at hv' ⊢
    simpa using hv'.trans (isLittleO_exp_neg_mul_rpow_atTop hv _).isBigO
  h_feq x hx := by simp [← ofReal_mul, oddKernel_functional_equation a, inv_rpow (le_of_lt hx)]
/-
**HurwitzZeta.isStrong_hurwitzOddFEPair** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：isStrong_hurwitzOddFEPair (a : UnitAddCircle) : IsStrongFEPair (hurwitzOdd
FEPair a) where hf₀
参数：a : UnitAddCircle。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isStrong_hurwitzOddFEPair (a : UnitAddCircle) : IsStrongFEPair (hurwitzOddFEPair a) where
  hf₀ := rfl
  hg₀ := rfl

end FEPair

/-!
## Definition of the completed odd Hurwitz zeta function
-/

/-- The entire function of `s` which agrees with
`1 / 2 * Gamma ((s + 1) / 2) * π ^ (-(s + 1) / 2) * ∑' (n : ℤ), sgn (n + a) / |n + a| ^ s`
for `1 < re s`.
-/
/-
**HurwitzZeta.completedHurwitzZetaOdd** 是 Mathlib 中的一个定义，位于命名空间 `HurwitzZeta`。
形式化陈述：completedHurwitzZetaOdd (a : UnitAddCircle) (s : Complex) : Complex
参数：a : UnitAddCircle；s : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The entire function of `s` which agrees with
`1 / 2 * Gamma ((s + 1) / 2) * π ^ (-(s + 1) / 2) * ∑' (n : ℤ), sgn (n + a) / |n
 + a| ^ s`
for `1 < re s`.
-/
def completedHurwitzZetaOdd (a : UnitAddCircle) (s : ℂ) : ℂ :=
  ((hurwitzOddFEPair a).Λ ((s + 1) / 2)) / 2
/-
**HurwitzZeta.differentiable_completedHurwitzZetaOdd** 是 Mathlib 中的一个引理，位于命名空间 `
HurwitzZeta`。
形式化陈述：differentiable_completedHurwitzZetaOdd (a : UnitAddCircle) : Differentiabl
e Complex (completedHurwitzZetaOdd a)
参数：a : UnitAddCircle。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Differentiable.div_const`：Differentiable.div_const (hc : Differentiable 
𝕜 c) (d : 𝕜') : Differentiable 𝕜 fun x => c x / d
· 使用定理 `Differentiable.comp`：Differentiable.comp {g : F -> G} (hg : Differentiab
le 𝕜 g) (hf : Differentiable 𝕜 f) : Differentiable 𝕜 (g ∘ f)
· 使用定理 `IsStrongFEPair.differentiable_Λ`：differentiable_Λ : Differentiable Compl
ex P.Λ
· 使用引理 `HurwitzZeta.isStrong_hurwitzOddFEPair`：isStrong_hurwitzOddFEPair (a : Un
itAddCircle) : IsStrongFEPair (hurwitzOddFEPair a) where hf₀
· 使用定理 `Differentiable.add_const`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type u_…
· 使用定理 `differentiable_id`：differentiable_id : Differentiable 𝕜 (id : E -> E)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma differentiable_completedHurwitzZetaOdd (a : UnitAddCircle) :
    Differentiable ℂ (completedHurwitzZetaOdd a) :=
  ((isStrong_hurwitzOddFEPair a).differentiable_Λ.comp
    ((differentiable_id.add_const 1).div_const 2)).div_const 2

/-- The entire function of `s` which agrees with
` Gamma ((s + 1) / 2) * π ^ (-(s + 1) / 2) * ∑' (n : ℕ), sin (2 * π * a * n) / n ^ s`
for `1 < re s`.
-/
/-
**HurwitzZeta.completedSinZeta** 是 Mathlib 中的一个定义，位于命名空间 `HurwitzZeta`。
形式化陈述：completedSinZeta (a : UnitAddCircle) (s : Complex) : Complex
参数：a : UnitAddCircle；s : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The entire function of `s` which agrees with
` Gamma ((s + 1) / 2) * π ^ (-(s + 1) / 2) * ∑' (n : ℕ), sin (2 * π * a * n) / n
 ^ s`
for `1 < re s`.
-/
def completedSinZeta (a : UnitAddCircle) (s : ℂ) : ℂ :=
  ((hurwitzOddFEPair a).symm.Λ ((s + 1) / 2)) / 2
/-
**HurwitzZeta.differentiable_completedSinZeta** 是 Mathlib 中的一个引理，位于命名空间 `Hurwitz
Zeta`。
形式化陈述：differentiable_completedSinZeta (a : UnitAddCircle) : Differentiable Compl
ex (completedSinZeta a)
参数：a : UnitAddCircle。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Differentiable.div_const`：Differentiable.div_const (hc : Differentiable 
𝕜 c) (d : 𝕜') : Differentiable 𝕜 fun x => c x / d
· 使用定理 `Differentiable.comp`：Differentiable.comp {g : F -> G} (hg : Differentiab
le 𝕜 g) (hf : Differentiable 𝕜 f) : Differentiable 𝕜 (g ∘ f)
· 使用定理 `IsStrongFEPair.differentiable_Λ`：differentiable_Λ : Differentiable Compl
ex P.Λ
· 使用引理 `IsStrongFEPair.symm`：IsStrongFEPair.symm {P : WeakFEPair E} (hP : IsStro
ngFEPair P) : IsStrongFEPair P.symm
· 使用引理 `HurwitzZeta.isStrong_hurwitzOddFEPair`：isStrong_hurwitzOddFEPair (a : Un
itAddCircle) : IsStrongFEPair (hurwitzOddFEPair a) where hf₀
· 使用定理 `Differentiable.add_const`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type u_…
· 使用定理 `differentiable_id`：differentiable_id : Differentiable 𝕜 (id : E -> E)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma differentiable_completedSinZeta (a : UnitAddCircle) :
    Differentiable ℂ (completedSinZeta a) :=
  ((isStrong_hurwitzOddFEPair a).symm.differentiable_Λ.comp
    ((differentiable_id.add_const 1).div_const 2)).div_const 2

/-!
## Parity and functional equations
-/

/-
**HurwitzZeta.completedHurwitzZetaOdd_neg** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta
`。
形式化陈述：completedHurwitzZetaOdd_neg (a : UnitAddCircle) (s : Complex) : completedH
urwitzZetaOdd (-a) s = -completedHurwitzZetaOdd a s
参数：a : UnitAddCircle；s : Complex。
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
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `IsStrongFEPair.Λ_eq`：Λ_eq : P.Λ = mellin P.f
· 使用引理 `HurwitzZeta.isStrong_hurwitzOddFEPair`：isStrong_hurwitzOddFEPair (a : Un
itAddCircle) : IsStrongFEPair (hurwitzOddFEPair a) where hf₀
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `HurwitzZeta.hurwitzOddFEPair_f`：∀ (a : UnitAddCircle) (a_1 : ℝ), (Hurwit
zZeta.hurwitzOddFEPair a).f a_1 = (Complex.ofReal ∘ HurwitzZeta.oddKernel a) a_1
· 使用引理 `HurwitzZeta.oddKernel_neg`：oddKernel_neg (a : UnitAddCircle) (x : Real) 
: oddKernel (-a) x = -oddKernel a x
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `MeasureTheory.integral_neg`：integral_neg (f : α -> G) : ∫ a, -f a ∂μ = -
∫ a, f a ∂μ
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
## Parity and functional equations
-/
lemma completedHurwitzZetaOdd_neg (a : UnitAddCircle) (s : ℂ) :
    completedHurwitzZetaOdd (-a) s = -completedHurwitzZetaOdd a s := by
  simp [completedHurwitzZetaOdd, (isStrong_hurwitzOddFEPair _).Λ_eq, mellin,
    oddKernel_neg, integral_neg, neg_div]
/-
**HurwitzZeta.completedSinZeta_neg** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：completedSinZeta_neg (a : UnitAddCircle) (s : Complex) : completedSinZeta 
(-a) s = -completedSinZeta a s
参数：a : UnitAddCircle；s : Complex。
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
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `IsStrongFEPair.symm_Λ_eq`：symm_Λ_eq : P.symm.Λ = mellin P.g
· 使用引理 `HurwitzZeta.isStrong_hurwitzOddFEPair`：isStrong_hurwitzOddFEPair (a : Un
itAddCircle) : IsStrongFEPair (hurwitzOddFEPair a) where hf₀
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `HurwitzZeta.hurwitzOddFEPair_g`：∀ (a : UnitAddCircle) (a_1 : ℝ), (Hurwit
zZeta.hurwitzOddFEPair a).g a_1 = (Complex.ofReal ∘ HurwitzZeta.sinKernel a) a_1
· 使用引理 `HurwitzZeta.sinKernel_neg`：sinKernel_neg (a : UnitAddCircle) (x : Real) 
: sinKernel (-a) x = -sinKernel a x
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `MeasureTheory.integral_neg`：integral_neg (f : α -> G) : ∫ a, -f a ∂μ = -
∫ a, f a ∂μ
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma completedSinZeta_neg (a : UnitAddCircle) (s : ℂ) :
    completedSinZeta (-a) s = -completedSinZeta a s := by
  simp [completedSinZeta, (isStrong_hurwitzOddFEPair _).symm_Λ_eq, mellin, sinKernel_neg,
    integral_neg, neg_div]

/-- Functional equation for the odd Hurwitz zeta function. -/
/-
**HurwitzZeta.completedHurwitzZetaOdd_one_sub** 是 Mathlib 中的一个定理，位于命名空间 `Hurwitz
Zeta`。
形式化陈述：completedHurwitzZetaOdd_one_sub (a : UnitAddCircle) (s : Complex) : comple
tedHurwitzZetaOdd a (1 - s) = completedSinZeta a s
参数：a : UnitAddCircle；s : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HurwitzZeta.completedHurwitzZetaOdd.eq_1`：∀ (a : UnitAddCircle) (s : ℂ),
   HurwitzZeta.completedHurwitzZetaOdd a s = (HurwitzZeta.hurwitzOddFEPair a).Λ 
((s + 1) / 2) / 2
· 使用定理 `HurwitzZeta.completedSinZeta.eq_1`：∀ (a : UnitAddCircle) (s : ℂ),   Hurw
itzZeta.completedSinZeta a s = (HurwitzZeta.hurwitzOddFEPair a).symm.Λ ((s + 1) 
/ 2) / 2
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.ofReal_div`：ofReal_div (r s : Real) : ((r / s : Real) : Complex)
 = r / s
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap`：∀ {R : Type u_1} [inst : 
CommSemiring R] {a₁ a₂ b₁ b₂ c₁ c₂ : R},   a₁ + b₁ = c₁ → a₂ + b₂ = c₂ → a₁ + a₂
 + (b₁ + b₂) = c₁ + c₂
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
（共 61 条，此处仅展示前 30 条）

--- 原说明 ---
Functional equation for the odd Hurwitz zeta function.
-/
theorem completedHurwitzZetaOdd_one_sub (a : UnitAddCircle) (s : ℂ) :
    completedHurwitzZetaOdd a (1 - s) = completedSinZeta a s := by
  rw [completedHurwitzZetaOdd, completedSinZeta,
    (by { push_cast; ring } : (1 - s + 1) / 2 = ↑(3 / 2 : ℝ) - (s + 1) / 2),
    ← hurwitzOddFEPair_k, (hurwitzOddFEPair a).functional_equation ((s + 1) / 2),
    hurwitzOddFEPair_ε, one_smul]

/-- Functional equation for the odd Hurwitz zeta function (alternative form). -/
/-
**HurwitzZeta.completedSinZeta_one_sub** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：completedSinZeta_one_sub (a : UnitAddCircle) (s : Complex) : completedSinZ
eta a (1 - s) = completedHurwitzZetaOdd a s
参数：a : UnitAddCircle；s : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Functional equation for the odd Hurwitz zeta function (alternative form).
-/
lemma completedSinZeta_one_sub (a : UnitAddCircle) (s : ℂ) :
    completedSinZeta a (1 - s) = completedHurwitzZetaOdd a s := by
  simp [← completedHurwitzZetaOdd_one_sub]

/-!
## Relation to the Dirichlet series for `1 < re s`
-/

/-- Formula for `completedSinZeta` as a Dirichlet series in the convergence range
(first version, with sum over `ℤ`). -/
/-
**HurwitzZeta.hasSum_int_completedSinZeta** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta
`。
形式化陈述：hasSum_int_completedSinZeta (a : Real) {s : Complex} (hs : 1 < re s) : Has
Sum (fun n : Int => GammaReal (s + 1) * (-I) * Int.sign n * cexp (2 * π * I * a 
* n) / (↑|n| : Complex) ^ s / 2) (completedSinZeta a s)
参数：a : Real；hs : 1 < re s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `norm_div`：norm_div (a b : α) : ‖a / b‖ = ‖a‖ / ‖b‖
· 使用定理 `RCLike.norm_ofNat`：norm_ofNat (n : Nat) [n.AtLeastTwo] : ‖(ofNat(n) : K)
‖ = ofNat(n)
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `Complex.norm_I`：‖Complex.I‖ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
（共 92 条，此处仅展示前 30 条）

--- 原说明 ---
Formula for `completedSinZeta` as a Dirichlet series in the convergence range
(first version, with sum over `ℤ`).
-/
lemma hasSum_int_completedSinZeta (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℤ ↦ Gammaℝ (s + 1) * (-I) * Int.sign n *
    cexp (2 * π * I * a * n) / (↑|n| : ℂ) ^ s / 2) (completedSinZeta a s) := by
  let c (n : ℤ) : ℂ := -I * cexp (2 * π * I * a * n) / 2
  have hc (n : ℤ) : ‖c n‖ = 1 / 2 := by
    simp_rw [c, (by { push_cast; ring } : 2 * π * I * a * n = ↑(2 * π * a * n) * I), norm_div,
      RCLike.norm_ofNat, norm_mul, norm_neg, norm_I, one_mul, norm_exp_ofReal_mul_I]
  have hF t (ht : 0 < t) :
      HasSum (fun n ↦ c n * n * rexp (-π * n ^ 2 * t)) (sinKernel a t / 2) := by
    refine ((hasSum_int_sinKernel a ht).div_const 2).congr_fun fun n ↦ ?_
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, mul_right_comm (-I)]
  have h_sum : Summable fun i ↦ ‖c i‖ / |↑i| ^ s.re := by
    simp_rw [hc, div_right_comm]
    apply Summable.div_const
    apply Summable.of_nat_of_neg <;>
    simpa
  rw [completedSinZeta, (isStrong_hurwitzOddFEPair _).symm_Λ_eq]
  refine (mellin_div_const .. ▸ hasSum_mellin_pi_mul_sq' (zero_lt_one.trans hs) hF h_sum).congr_fun
    fun n ↦ ?_
  simp [Int.sign_eq_sign, ← Int.cast_abs] -- non-terminal simp OK when `ring` follows
  ring

/-- Formula for `completedSinZeta` as a Dirichlet series in the convergence range
(second version, with sum over `ℕ`). -/
/-
**HurwitzZeta.hasSum_nat_completedSinZeta** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta
`。
形式化陈述：hasSum_nat_completedSinZeta (a : Real) {s : Complex} (hs : 1 < re s) : Has
Sum (fun n : Nat => GammaReal (s + 1) * Real.sin (2 * π * a * n) / (n : Complex)
 ^ s) (completedSinZeta a s)
参数：a : Real；hs : 1 < re s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `HasSum.nat_add_neg`：∀ {M : Type u_1} [inst : AddCommMonoid M] [inst_1 : 
TopologicalSpace M] {m : M} [ContinuousAdd M] {f : ℤ → M},   HasSum f m → HasSum
 (fun n …
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
· 使用引理 `HurwitzZeta.hasSum_int_completedSinZeta`：hasSum_int_completedSinZeta (a 
: Real) {s : Complex} (hs : 1 < re s) : HasSum (fun n : Int => GammaReal (s + 1)
 * (-I) * Int.sign n * cexp (…
· 使用定理 `HasSum.congr_fun`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid 
α] [inst_1 : TopologicalSpace α] {f g : β → α} {a : α}   {L : SummationFilter β}
, HasS…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Nat.abs_cast`：abs_cast (n : Nat) : |(n : R)| = n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Int.sign_neg`：∀ (z : ℤ), (-z).sign = -z.sign
· 使用定理 `abs_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a : 
α), |(-a)| = |a|
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `div_right_comm`：div_right_comm : a / b / c = a / c / b
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
（共 73 条，此处仅展示前 30 条）

--- 原说明 ---
Formula for `completedSinZeta` as a Dirichlet series in the convergence range
(second version, with sum over `ℕ`).
-/
lemma hasSum_nat_completedSinZeta (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℕ ↦ Gammaℝ (s + 1) * Real.sin (2 * π * a * n) / (n : ℂ) ^ s)
    (completedSinZeta a s) := by
  have := (hasSum_int_completedSinZeta a hs).nat_add_neg
  simp_rw [Int.sign_zero, Int.cast_zero, mul_zero, zero_mul, zero_div, add_zero, abs_neg,
    Int.sign_neg, Nat.abs_cast, Int.cast_neg, Int.cast_natCast, ← add_div] at this
  refine this.congr_fun fun n ↦ ?_
  rw [div_right_comm]
  rcases eq_or_ne n 0 with rfl | h
  · simp
  simp_rw [Int.sign_natCast_of_ne_zero h, Int.cast_one, ofReal_sin, Complex.sin]
  simp only [← mul_div_assoc, push_cast, mul_assoc (Gammaℝ _), ← mul_add]
  congr 3
  rw [mul_one, mul_neg_one, neg_neg, neg_mul I, ← sub_eq_neg_add, ← mul_sub, mul_comm,
    mul_neg, neg_mul]
  congr 3 <;> ring

/-- Formula for `completedHurwitzZetaOdd` as a Dirichlet series in the convergence range. -/
/-
**HurwitzZeta.hasSum_int_completedHurwitzZetaOdd** 是 Mathlib 中的一个引理，位于命名空间 `Hurw
itzZeta`。
形式化陈述：hasSum_int_completedHurwitzZetaOdd (a : Real) {s : Complex} (hs : 1 < re s
) : HasSum (fun n : Int => GammaReal (s + 1) * SignType.sign (n + a) / (↑|n + a|
 : Complex) ^ s / 2) (completedHurwitzZetaOdd a s)
参数：a : Real；hs : 1 < re s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `HasSum.congr_fun`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid 
α] [inst_1 : TopologicalSpace α] {f g : β → α} {a : α}   {L : SummationFilter β}
, HasS…
· 使用定理 `HasSum.div_const`：HasSum.div_const (h : HasSum f a L) (b : α) : HasSum (
fun i => f i / b) (a / b) L
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Complex.hasSum_ofReal`：∀ {α : Type u_1} {L : SummationFilter α} {f : α →
 ℝ} {x : ℝ}, HasSum (fun x => ↑(f x)) (↑x) L ↔ HasSum f x L
· 使用引理 `HurwitzZeta.hasSum_int_oddKernel`：hasSum_int_oddKernel (a : Real) {x : R
eal} (hx : 0 < x) : HasSum (fun n : Int => (n + a) * rexp (-π * (n + a) ^ 2 * x)
) (oddKernel ↑a x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.ofReal_add`：ofReal_add (r s : Real) : ((r + s : Real) : Complex)
 = r + s
· 使用定理 `div_mul_eq_mul_div`：div_mul_eq_mul_div : a / b * c = a * c / b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Complex.ofReal_exp`：ofReal_exp (x : Real) : (Real.exp x : Complex) = exp
 x
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `Complex.ofReal_pow`：ofReal_pow (r : Real) (n : Nat) : ((r ^ n : Real) : 
Complex) = (r : Complex) ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one_div`：mul_one_div (x y : G) : x * (1 / y) = x / y
· 使用定理 `Summable.mul_left`：Summable.mul_left (a) (hf : Summable f L) : Summable 
(fun i => a * f i) L
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用引理 `Real.summable_one_div_int_add_rpow`：Real.summable_one_div_int_add_rpow (
a : Real) (s : Real) : Summable (fun n : Int => 1 / |n + a| ^ s) ↔ 1 < s
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
Formula for `completedHurwitzZetaOdd` as a Dirichlet series in the convergence r
ange.
-/
lemma hasSum_int_completedHurwitzZetaOdd (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℤ ↦ Gammaℝ (s + 1) * SignType.sign (n + a) / (↑|n + a| : ℂ) ^ s / 2)
    (completedHurwitzZetaOdd a s) := by
  let r (n : ℤ) : ℝ := n + a
  let c (n : ℤ) : ℂ := 1 / 2
  have hF t (ht : 0 < t) : HasSum (fun n ↦ c n * r n * rexp (-π * (r n) ^ 2 * t))
      (oddKernel a t / 2) := by
    refine ((hasSum_ofReal.mpr (hasSum_int_oddKernel a ht)).div_const 2).congr_fun fun n ↦ ?_
    simp [r, c, push_cast, div_mul_eq_mul_div, -one_div]
  have h_sum : Summable fun i ↦ ‖c i‖ / |r i| ^ s.re := by
    simp_rw [c, ← mul_one_div ‖_‖]
    apply Summable.mul_left
    rwa [summable_one_div_int_add_rpow]
  rw [completedHurwitzZetaOdd, (isStrong_hurwitzOddFEPair _).Λ_eq]
  have := mellin_div_const .. ▸ hasSum_mellin_pi_mul_sq' (zero_lt_one.trans hs) hF h_sum
  refine this.congr_fun fun n ↦ ?_
  simp only [r, c, mul_one_div, div_mul_eq_mul_div, div_right_comm]

/-!
## Non-completed zeta functions
-/

/-- The odd part of the Hurwitz zeta function, i.e. the meromorphic function of `s` which agrees
with `1 / 2 * ∑' (n : ℤ), sign (n + a) / |n + a| ^ s` for `1 < re s` -/
/-
**HurwitzZeta.hurwitzZetaOdd** 是 Mathlib 中的一个定义，位于命名空间 `HurwitzZeta`。
形式化陈述：hurwitzZetaOdd (a : UnitAddCircle) (s : Complex)
参数：a : UnitAddCircle；s : Complex。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The odd part of the Hurwitz zeta function, i.e. the meromorphic function of `s` 
which agrees
with `1 / 2 * ∑' (n : ℤ), sign (n + a) / |n + a| ^ s` for `1 < re s`
-/
noncomputable def hurwitzZetaOdd (a : UnitAddCircle) (s : ℂ) :=
  completedHurwitzZetaOdd a s / Gammaℝ (s + 1)
/-
**HurwitzZeta.hurwitzZetaOdd_neg** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：hurwitzZetaOdd_neg (a : UnitAddCircle) (s : Complex) : hurwitzZetaOdd (-a)
 s = -hurwitzZetaOdd a s
参数：a : UnitAddCircle；s : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HurwitzZeta.completedHurwitzZetaOdd_neg`：completedHurwitzZetaOdd_neg (a 
: UnitAddCircle) (s : Complex) : completedHurwitzZetaOdd (-a) s = -completedHurw
itzZetaOdd a s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma hurwitzZetaOdd_neg (a : UnitAddCircle) (s : ℂ) :
    hurwitzZetaOdd (-a) s = -hurwitzZetaOdd a s := by
  simp_rw [hurwitzZetaOdd, completedHurwitzZetaOdd_neg, neg_div]

/-- The odd Hurwitz zeta function is differentiable everywhere. -/
/-
**HurwitzZeta.differentiable_hurwitzZetaOdd** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZe
ta`。
形式化陈述：differentiable_hurwitzZetaOdd (a : UnitAddCircle) : Differentiable Complex
 (hurwitzZetaOdd a)
参数：a : UnitAddCircle。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Differentiable.mul`：Differentiable.mul (ha : Differentiable 𝕜 a) (hb : D
ifferentiable 𝕜 b) : Differentiable 𝕜 (a * b)
· 使用引理 `HurwitzZeta.differentiable_completedHurwitzZetaOdd`：differentiable_compl
etedHurwitzZetaOdd (a : UnitAddCircle) : Differentiable Complex (completedHurwit
zZetaOdd a)
· 使用定理 `Differentiable.comp`：Differentiable.comp {g : F -> G} (hg : Differentiab
le 𝕜 g) (hf : Differentiable 𝕜 f) : Differentiable 𝕜 (g ∘ f)
· 使用定理 `Complex.differentiable_Gammaℝ_inv`：Differentiable ℂ fun s => s.Gammaℝ⁻¹
· 使用定理 `Differentiable.add`：Differentiable.add (hf : Differentiable 𝕜 f) (hg : D
ifferentiable 𝕜 g) : Differentiable 𝕜 (f + g)
· 使用定理 `differentiable_id`：differentiable_id : Differentiable 𝕜 (id : E -> E)
· 使用定理 `differentiable_const`：differentiable_const (c : F) : Differentiable 𝕜 fu
n _ : E => c

--- 原说明 ---
The odd Hurwitz zeta function is differentiable everywhere.
-/
lemma differentiable_hurwitzZetaOdd (a : UnitAddCircle) :
    Differentiable ℂ (hurwitzZetaOdd a) :=
  (differentiable_completedHurwitzZetaOdd a).mul <| differentiable_Gammaℝ_inv.comp <|
    differentiable_id.add <| differentiable_const _

/-- The sine zeta function, i.e. the meromorphic function of `s` which agrees
with `∑' (n : ℕ), sin (2 * π * a * n) / n ^ s` for `1 < re s`. -/
/-
**HurwitzZeta.sinZeta** 是 Mathlib 中的一个定义，位于命名空间 `HurwitzZeta`。
形式化陈述：sinZeta (a : UnitAddCircle) (s : Complex)
参数：a : UnitAddCircle；s : Complex。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sine zeta function, i.e. the meromorphic function of `s` which agrees
with `∑' (n : ℕ), sin (2 * π * a * n) / n ^ s` for `1 < re s`.
-/
noncomputable def sinZeta (a : UnitAddCircle) (s : ℂ) :=
  completedSinZeta a s / Gammaℝ (s + 1)
/-
**HurwitzZeta.sinZeta_neg** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：sinZeta_neg (a : UnitAddCircle) (s : Complex) : sinZeta (-a) s = -sinZeta 
a s
参数：a : UnitAddCircle；s : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HurwitzZeta.completedSinZeta_neg`：completedSinZeta_neg (a : UnitAddCircl
e) (s : Complex) : completedSinZeta (-a) s = -completedSinZeta a s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sinZeta_neg (a : UnitAddCircle) (s : ℂ) :
    sinZeta (-a) s = -sinZeta a s := by
  simp_rw [sinZeta, completedSinZeta_neg, neg_div]

/-- The sine zeta function is differentiable everywhere. -/
/-
**HurwitzZeta.differentiableAt_sinZeta** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：differentiableAt_sinZeta (a : UnitAddCircle) : Differentiable Complex (sin
Zeta a)
参数：a : UnitAddCircle。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Differentiable.mul`：Differentiable.mul (ha : Differentiable 𝕜 a) (hb : D
ifferentiable 𝕜 b) : Differentiable 𝕜 (a * b)
· 使用引理 `HurwitzZeta.differentiable_completedSinZeta`：differentiable_completedSin
Zeta (a : UnitAddCircle) : Differentiable Complex (completedSinZeta a)
· 使用定理 `Differentiable.comp`：Differentiable.comp {g : F -> G} (hg : Differentiab
le 𝕜 g) (hf : Differentiable 𝕜 f) : Differentiable 𝕜 (g ∘ f)
· 使用定理 `Complex.differentiable_Gammaℝ_inv`：Differentiable ℂ fun s => s.Gammaℝ⁻¹
· 使用定理 `Differentiable.add`：Differentiable.add (hf : Differentiable 𝕜 f) (hg : D
ifferentiable 𝕜 g) : Differentiable 𝕜 (f + g)
· 使用定理 `differentiable_id`：differentiable_id : Differentiable 𝕜 (id : E -> E)
· 使用定理 `differentiable_const`：differentiable_const (c : F) : Differentiable 𝕜 fu
n _ : E => c

--- 原说明 ---
The sine zeta function is differentiable everywhere.
-/
lemma differentiableAt_sinZeta (a : UnitAddCircle) :
    Differentiable ℂ (sinZeta a) :=
  (differentiable_completedSinZeta a).mul <| differentiable_Gammaℝ_inv.comp <|
    differentiable_id.add <| differentiable_const _

/-- Formula for `hurwitzZetaOdd` as a Dirichlet series in the convergence range (sum over `ℤ`). -/
/-
**HurwitzZeta.hasSum_int_hurwitzZetaOdd** 是 Mathlib 中的一个定理，位于命名空间 `HurwitzZeta`。
形式化陈述：hasSum_int_hurwitzZetaOdd (a : Real) {s : Complex} (hs : 1 < re s) : HasSu
m (fun n : Int => SignType.sign (n + a) / (↑|n + a| : Complex) ^ s / 2) (hurwitz
ZetaOdd a s)
参数：a : Real；hs : 1 < re s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.congr_fun`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid 
α] [inst_1 : TopologicalSpace α] {f g : β → α} {a : α}   {L : SummationFilter β}
, HasS…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `HasSum.div_const`：HasSum.div_const (h : HasSum f a L) (b : α) : HasSum (
fun i => f i / b) (a / b) L
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用引理 `HurwitzZeta.hasSum_int_completedHurwitzZetaOdd`：hasSum_int_completedHurw
itzZetaOdd (a : Real) {s : Complex} (hs : 1 < re s) : HasSum (fun n : Int => Gam
maReal (s + 1) * SignType.sign (n + …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.add_re`：add_re (z w : Complex) : (z + w).re = z.re + w.re
· 使用定理 `Complex.one_re`：one_re : (1 : Complex).re = 1
· 使用定理 `add_pos'`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder α]
 [AddLeftMono α] {a b : α}, 0 < a → 0 < b → 0 < a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `div_right_comm`：div_right_comm : a / b / c = a / c / b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
· 使用定理 `Complex.Gammaℝ_ne_zero_of_re_pos`：∀ {s : ℂ}, 0 < s.re → s.Gammaℝ ≠ 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Formula for `hurwitzZetaOdd` as a Dirichlet series in the convergence range (sum
 over `ℤ`).
-/
theorem hasSum_int_hurwitzZetaOdd (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℤ ↦ SignType.sign (n + a) / (↑|n + a| : ℂ) ^ s / 2) (hurwitzZetaOdd a s) := by
  refine ((hasSum_int_completedHurwitzZetaOdd a hs).div_const (Gammaℝ _)).congr_fun fun n ↦ ?_
  have : 0 < re (s + 1) := by rw [add_re, one_re]; positivity
  simp [div_right_comm _ _ (Gammaℝ _), mul_div_cancel_left₀ _ (Gammaℝ_ne_zero_of_re_pos this)]

/-- Formula for `hurwitzZetaOdd` as a Dirichlet series in the convergence range, with sum over `ℕ`
(version with absolute values) -/
/-
**HurwitzZeta.hasSum_nat_hurwitzZetaOdd** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：hasSum_nat_hurwitzZetaOdd (a : Real) {s : Complex} (hs : 1 < re s) : HasSu
m (fun n : Nat => (SignType.sign (n + a) / (↑|n + a| : Complex) ^ s - SignType.s
ign (n + 1 - a) / (↑|n + 1 - a| : Complex) ^ s) / 2) (hurwitzZetaOdd a s)
参数：a : Real；hs : 1 < re s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.congr_fun`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid 
α] [inst_1 : TopologicalSpace α] {f g : β → α} {a : α}   {L : SummationFilter β}
, HasS…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `HasSum.nat_add_neg_add_one`：∀ {M : Type u_1} [inst : AddCommMonoid M] [i
nst_1 : TopologicalSpace M] {m : M} {f : ℤ → M},   HasSum f m → HasSum (fun n =>
 f ↑n + f (-(↑n …
· 使用定理 `HurwitzZeta.hasSum_int_hurwitzZetaOdd`：hasSum_int_hurwitzZetaOdd (a : Re
al) {s : Complex} (hs : 1 < re s) : HasSum (fun n : Int => SignType.sign (n + a)
 / (↑|n + a| : Complex) ^ s…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `sub_div`：sub_div (a b c : K) : (a - b) / c = a / c - b / c
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
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
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
（共 56 条，此处仅展示前 30 条）

--- 原说明 ---
Formula for `hurwitzZetaOdd` as a Dirichlet series in the convergence range, wit
h sum over `ℕ`
(version with absolute values)
-/
lemma hasSum_nat_hurwitzZetaOdd (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℕ ↦ (SignType.sign (n + a) / (↑|n + a| : ℂ) ^ s
      - SignType.sign (n + 1 - a) / (↑|n + 1 - a| : ℂ) ^ s) / 2) (hurwitzZetaOdd a s) := by
  refine (hasSum_int_hurwitzZetaOdd a hs).nat_add_neg_add_one.congr_fun fun n ↦ ?_
  rw [Int.cast_neg, Int.cast_add, Int.cast_one, sub_div, sub_eq_add_neg, Int.cast_natCast]
  have : -(n + 1) + a = -(n + 1 - a) := by ring_nf
  rw [this, Left.sign_neg, abs_neg, SignType.coe_neg, neg_div, neg_div]

/-- Formula for `hurwitzZetaOdd` as a Dirichlet series in the convergence range, with sum over `ℕ`
(version without absolute values, assuming `a ∈ Icc 0 1`) -/
/-
**HurwitzZeta.hasSum_nat_hurwitzZetaOdd_of_mem_Icc** 是 Mathlib 中的一个引理，位于命名空间 `Hu
rwitzZeta`。
形式化陈述：hasSum_nat_hurwitzZetaOdd_of_mem_Icc {a : Real} (ha : a in Icc 0 1) {s : C
omplex} (hs : 1 < re s) : HasSum (fun n : Nat => (1 / (n + a : Complex) ^ s - 1 
/ (n + 1 - a : Complex) ^ s) / 2) (hurwitzZetaOdd a s)
参数：ha : a in Icc 0 1；hs : 1 < re s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.congr_fun`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid 
α] [inst_1 : TopologicalSpace α] {f g : β → α} {a : α}   {L : SummationFilter β}
, HasS…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `HurwitzZeta.hasSum_nat_hurwitzZetaOdd`：hasSum_nat_hurwitzZetaOdd (a : Re
al) {s : Complex} (hs : 1 < re s) : HasSum (fun n : Nat => (SignType.sign (n + a
) / (↑|n + a| : Complex) ^ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.ofReal_add`：ofReal_add (r s : Real) : ((r + s : Real) : Complex)
 = r + s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `lt_or_eq_of_le`：lt_or_eq_of_le : a <= b -> a < b ∨ a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sign_pos`：sign_pos (ha : 0 < a) : sign a = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.ofReal_zero`：ofReal_zero : ((0 : Real) : Complex) = 0
· 使用定理 `Complex.zero_cpow`：zero_cpow {x : Complex} (h : x != 0) : (0 : Complex) 
^ x = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `Complex.zero_re`：zero_re : (0 : Complex).re = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `add_sub_assoc`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b c : G), a +
 b - c = a + (b - c)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
Formula for `hurwitzZetaOdd` as a Dirichlet series in the convergence range, wit
h sum over `ℕ`
(version without absolute values, assuming `a ∈ Icc 0 1`)
-/
lemma hasSum_nat_hurwitzZetaOdd_of_mem_Icc {a : ℝ} (ha : a ∈ Icc 0 1) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℕ ↦ (1 / (n + a : ℂ) ^ s - 1 / (n + 1 - a : ℂ) ^ s) / 2)
    (hurwitzZetaOdd a s) := by
  refine (hasSum_nat_hurwitzZetaOdd a hs).congr_fun fun n ↦ ?_
  suffices ∀ b : ℝ, 0 ≤ b → SignType.sign (n + b) / (↑|n + b| : ℂ) ^ s = 1 / (n + b) ^ s by
    simp only [add_sub_assoc, this a ha.1, this (1 - a) (sub_nonneg.mpr ha.2), push_cast]
  intro b hb
  rw [abs_of_nonneg (by positivity), (by simp : (n : ℂ) + b = ↑(n + b))]
  rcases lt_or_eq_of_le (by positivity : 0 ≤ n + b) with hb | hb
  · simp [sign_pos hb]
  · rw [← hb, ofReal_zero, zero_cpow ((not_lt.mpr zero_le_one) ∘ (zero_re ▸ · ▸ hs)),
      div_zero, div_zero]

/-- Formula for `sinZeta` as a Dirichlet series in the convergence range, with sum over `ℤ`. -/
/-
**HurwitzZeta.hasSum_int_sinZeta** 是 Mathlib 中的一个定理，位于命名空间 `HurwitzZeta`。
形式化陈述：hasSum_int_sinZeta (a : Real) {s : Complex} (hs : 1 < re s) : HasSum (fun 
n : Int => -I * n.sign * cexp (2 * π * I * a * n) / ↑|n| ^ s / 2) (sinZeta a s)
参数：a : Real；hs : 1 < re s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HurwitzZeta.sinZeta.eq_1`：∀ (a : UnitAddCircle) (s : ℂ), HurwitzZeta.sin
Zeta a s = HurwitzZeta.completedSinZeta a s / (s + 1).Gammaℝ
· 使用定理 `HasSum.congr_fun`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid 
α] [inst_1 : TopologicalSpace α] {f g : β → α} {a : α}   {L : SummationFilter β}
, HasS…
· 使用定理 `HasSum.div_const`：HasSum.div_const (h : HasSum f a L) (b : α) : HasSum (
fun i => f i / b) (a / b) L
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用引理 `HurwitzZeta.hasSum_int_completedSinZeta`：hasSum_int_completedSinZeta (a 
: Real) {s : Complex} (hs : 1 < re s) : HasSum (fun n : Int => GammaReal (s + 1)
 * (-I) * Int.sign n * cexp (…
· 使用定理 `Complex.add_re`：add_re (z w : Complex) : (z + w).re = z.re + w.re
· 使用定理 `Complex.one_re`：one_re : (1 : Complex).re = 1
· 使用定理 `add_pos'`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder α]
 [AddLeftMono α] {a b : α}, 0 < a → 0 < b → 0 < a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `div_right_comm`：div_right_comm : a / b / c = a / c / b
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
· 使用定理 `Complex.Gammaℝ_ne_zero_of_re_pos`：∀ {s : ℂ}, 0 < s.re → s.Gammaℝ ≠ 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Formula for `sinZeta` as a Dirichlet series in the convergence range, with sum o
ver `ℤ`.
-/
theorem hasSum_int_sinZeta (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℤ ↦ -I * n.sign * cexp (2 * π * I * a * n) / ↑|n| ^ s / 2) (sinZeta a s) := by
  rw [sinZeta]
  refine ((hasSum_int_completedSinZeta a hs).div_const (Gammaℝ (s + 1))).congr_fun fun n ↦ ?_
  have : 0 < re (s + 1) := by rw [add_re, one_re]; positivity
  simp only [mul_assoc, div_right_comm _ _ (Gammaℝ _),
    mul_div_cancel_left₀ _ (Gammaℝ_ne_zero_of_re_pos this)]

/-- Formula for `sinZeta` as a Dirichlet series in the convergence range, with sum over `ℕ`. -/
/-
**HurwitzZeta.hasSum_nat_sinZeta** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：hasSum_nat_sinZeta (a : Real) {s : Complex} (hs : 1 < re s) : HasSum (fun 
n : Nat => Real.sin (2 * π * a * n) / (n : Complex) ^ s) (sinZeta a s)
参数：a : Real；hs : 1 < re s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `HasSum.nat_add_neg`：∀ {M : Type u_1} [inst : AddCommMonoid M] [inst_1 : 
TopologicalSpace M] {m : M} [ContinuousAdd M] {f : ℤ → M},   HasSum f m → HasSum
 (fun n …
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
· 使用定理 `HurwitzZeta.hasSum_int_sinZeta`：hasSum_int_sinZeta (a : Real) {s : Compl
ex} (hs : 1 < re s) : HasSum (fun n : Int => -I * n.sign * cexp (2 * π * I * a *
 n) / ↑|n| ^ s / 2) …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.ofReal_sin`：ofReal_sin (x : Real) : (Real.sin x : Complex) = sin
 x
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `HasSum.congr_fun`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid 
α] [inst_1 : TopologicalSpace α] {f g : β → α} {a : α}   {L : SummationFilter β}
, HasS…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `Complex.zero_cpow`：zero_cpow {x : Complex} (h : x != 0) : (0 : Complex) 
^ x = 0
· 使用引理 `Complex.ne_zero_of_one_lt_re`：ne_zero_of_one_lt_re {s : Complex} (hs : 1
 < s.re) : s != 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Nat.abs_cast`：abs_cast (n : Nat) : |(n : R)| = n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.sign_neg`：∀ (z : ℤ), (-z).sign = -z.sign
（共 72 条，此处仅展示前 30 条）

--- 原说明 ---
Formula for `sinZeta` as a Dirichlet series in the convergence range, with sum o
ver `ℕ`.
-/
lemma hasSum_nat_sinZeta (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℕ ↦ Real.sin (2 * π * a * n) / (n : ℂ) ^ s) (sinZeta a s) := by
  have := (hasSum_int_sinZeta a hs).nat_add_neg
  simp_rw [abs_neg, Int.sign_neg, Int.cast_neg, Nat.abs_cast, Int.cast_natCast, mul_neg, abs_zero,
    Int.cast_zero, zero_cpow (ne_zero_of_one_lt_re hs), div_zero, zero_div, add_zero] at this
  simp_rw [push_cast, Complex.sin]
  refine this.congr_fun fun n ↦ ?_
  rcases ne_or_eq n 0 with h | rfl
  · simp only [neg_mul, sub_mul, div_right_comm _ (2 : ℂ), Int.sign_natCast_of_ne_zero h,
      Int.cast_one, mul_one, mul_comm I, neg_neg, ← add_div, ← sub_eq_neg_add]
    congr 5 <;> ring
  · simp

/-- Reformulation of `hasSum_nat_sinZeta` using `LSeriesHasSum`. -/
/-
**HurwitzZeta.LSeriesHasSum_sin** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：LSeriesHasSum_sin (a : Real) {s : Complex} (hs : 1 < re s) : LSeriesHasSum
 (Real.sin <| 2 * π * a * ·) s (sinZeta a s)
参数：a : Real；hs : 1 < re s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.congr_fun`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid 
α] [inst_1 : TopologicalSpace α] {f g : β → α} {a : α}   {L : SummationFilter β}
, HasS…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `HurwitzZeta.hasSum_nat_sinZeta`：hasSum_nat_sinZeta (a : Real) {s : Compl
ex} (hs : 1 < re s) : HasSum (fun n : Nat => Real.sin (2 * π * a * n) / (n : Com
plex) ^ s) (sinZeta …
· 使用引理 `LSeries.term_of_ne_zero'`：term_of_ne_zero' {s : Complex} (hs : s != 0) (
f : Nat -> Complex) (n : Nat) : term f s n = f n / n ^ s
· 使用引理 `Complex.ne_zero_of_one_lt_re`：ne_zero_of_one_lt_re {s : Complex} (hs : 1
 < s.re) : s != 0

--- 原说明 ---
Reformulation of `hasSum_nat_sinZeta` using `LSeriesHasSum`.
-/
lemma LSeriesHasSum_sin (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    LSeriesHasSum (Real.sin <| 2 * π * a * ·) s (sinZeta a s) :=
  (hasSum_nat_sinZeta a hs).congr_fun (LSeries.term_of_ne_zero' (ne_zero_of_one_lt_re hs) _)

/-- The trivial zeroes of the odd Hurwitz zeta function. -/
/-
**HurwitzZeta.hurwitzZetaOdd_neg_two_mul_nat_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `
HurwitzZeta`。
形式化陈述：hurwitzZetaOdd_neg_two_mul_nat_sub_one (a : UnitAddCircle) (n : Nat) : hur
witzZetaOdd a (-2 * n - 1) = 0
参数：a : UnitAddCircle；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HurwitzZeta.hurwitzZetaOdd.eq_1`：∀ (a : UnitAddCircle) (s : ℂ), HurwitzZ
eta.hurwitzZetaOdd a s = HurwitzZeta.completedHurwitzZetaOdd a s / (s + 1).Gamma
ℝ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Complex.Gammaℝ_eq_zero_iff`：∀ {s : ℂ}, s.Gammaℝ = 0 ↔ ∃ n, s = -(2 * ↑n)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0

--- 原说明 ---
The trivial zeroes of the odd Hurwitz zeta function.
-/
theorem hurwitzZetaOdd_neg_two_mul_nat_sub_one (a : UnitAddCircle) (n : ℕ) :
    hurwitzZetaOdd a (-2 * n - 1) = 0 := by
  rw [hurwitzZetaOdd, Gammaℝ_eq_zero_iff.mpr ⟨n, by rw [neg_mul, sub_add_cancel]⟩, div_zero]

/-- The trivial zeroes of the sine zeta function. -/
/-
**HurwitzZeta.sinZeta_neg_two_mul_nat_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `Hurwitz
Zeta`。
形式化陈述：sinZeta_neg_two_mul_nat_sub_one (a : UnitAddCircle) (n : Nat) : sinZeta a 
(-2 * n - 1) = 0
参数：a : UnitAddCircle；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HurwitzZeta.sinZeta.eq_1`：∀ (a : UnitAddCircle) (s : ℂ), HurwitzZeta.sin
Zeta a s = HurwitzZeta.completedSinZeta a s / (s + 1).Gammaℝ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Complex.Gammaℝ_eq_zero_iff`：∀ {s : ℂ}, s.Gammaℝ = 0 ↔ ∃ n, s = -(2 * ↑n)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0

--- 原说明 ---
The trivial zeroes of the sine zeta function.
-/
theorem sinZeta_neg_two_mul_nat_sub_one (a : UnitAddCircle) (n : ℕ) :
    sinZeta a (-2 * n - 1) = 0 := by
  rw [sinZeta, Gammaℝ_eq_zero_iff.mpr ⟨n, by rw [neg_mul, sub_add_cancel]⟩, div_zero]

/-- If `s` is not in `-ℕ`, then `hurwitzZetaOdd a (1 - s)` is an explicit multiple of
`sinZeta s`. -/
/-
**HurwitzZeta.hurwitzZetaOdd_one_sub** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：hurwitzZetaOdd_one_sub (a : UnitAddCircle) {s : Complex} (hs : forall (n :
 Nat), s != -n) : hurwitzZetaOdd a (1 - s) = 2 * (2 * π) ^ (-s) * Gamma s * sin 
(π * s / 2) * sinZeta a s
参数：a : UnitAddCircle；hs : forall (n : Nat), s != -n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.Gammaℂ.eq_1`：∀ (s : ℂ), s.Gammaℂ = 2 * (2 * ↑Real.pi) ^ (-s) * C
omplex.Gamma s
· 使用定理 `HurwitzZeta.hurwitzZetaOdd.eq_1`：∀ (a : UnitAddCircle) (s : ℂ), HurwitzZ
eta.hurwitzZetaOdd a s = HurwitzZeta.completedHurwitzZetaOdd a s / (s + 1).Gamma
ℝ
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap`：∀ {R : Type u_1} [inst : 
CommSemiring R] {a₁ a₂ b₁ b₂ c₁ c₂ : R},   a₁ + b₁ = c₁ → a₂ + b₂ = c₂ → a₁ + a₂
 + (b₁ + b₂) = c₁ + c₂
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Complex.inv_Gammaℝ_two_sub`：∀ {s : ℂ}, (∀ (n : ℕ), s ≠ -↑n) → (2 - s).Ga
mmaℝ⁻¹ = s.Gammaℂ * Complex.sin (↑Real.pi * s / 2) * (s + 1).Gammaℝ⁻¹
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
If `s` is not in `-ℕ`, then `hurwitzZetaOdd a (1 - s)` is an explicit multiple o
f
`sinZeta s`.
-/
lemma hurwitzZetaOdd_one_sub (a : UnitAddCircle) {s : ℂ} (hs : ∀ (n : ℕ), s ≠ -n) :
    hurwitzZetaOdd a (1 - s) = 2 * (2 * π) ^ (-s) * Gamma s * sin (π * s / 2) * sinZeta a s := by
  rw [← Gammaℂ, hurwitzZetaOdd, (by ring : 1 - s + 1 = 2 - s), div_eq_mul_inv,
    inv_Gammaℝ_two_sub hs, completedHurwitzZetaOdd_one_sub, sinZeta, ← div_eq_mul_inv,
    ← mul_div_assoc, ← mul_div_assoc, mul_comm]

/-- If `s` is not in `-ℕ`, then `sinZeta a (1 - s)` is an explicit multiple of
`hurwitzZetaOdd s`. -/
/-
**HurwitzZeta.sinZeta_one_sub** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：sinZeta_one_sub (a : UnitAddCircle) {s : Complex} (hs : forall (n : Nat), 
s != -n) : sinZeta a (1 - s) = 2 * (2 * π) ^ (-s) * Gamma s * sin (π * s / 2) * 
hurwitzZetaOdd a s
参数：a : UnitAddCircle；hs : forall (n : Nat), s != -n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.Gammaℂ.eq_1`：∀ (s : ℂ), s.Gammaℂ = 2 * (2 * ↑Real.pi) ^ (-s) * C
omplex.Gamma s
· 使用定理 `HurwitzZeta.sinZeta.eq_1`：∀ (a : UnitAddCircle) (s : ℂ), HurwitzZeta.sin
Zeta a s = HurwitzZeta.completedSinZeta a s / (s + 1).Gammaℝ
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap`：∀ {R : Type u_1} [inst : 
CommSemiring R] {a₁ a₂ b₁ b₂ c₁ c₂ : R},   a₁ + b₁ = c₁ → a₂ + b₂ = c₂ → a₁ + a₂
 + (b₁ + b₂) = c₁ + c₂
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Complex.inv_Gammaℝ_two_sub`：∀ {s : ℂ}, (∀ (n : ℕ), s ≠ -↑n) → (2 - s).Ga
mmaℝ⁻¹ = s.Gammaℂ * Complex.sin (↑Real.pi * s / 2) * (s + 1).Gammaℝ⁻¹
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
If `s` is not in `-ℕ`, then `sinZeta a (1 - s)` is an explicit multiple of
`hurwitzZetaOdd s`.
-/
lemma sinZeta_one_sub (a : UnitAddCircle) {s : ℂ} (hs : ∀ (n : ℕ), s ≠ -n) :
    sinZeta a (1 - s) = 2 * (2 * π) ^ (-s) * Gamma s * sin (π * s / 2) * hurwitzZetaOdd a s := by
  rw [← Gammaℂ, sinZeta, (by ring : 1 - s + 1 = 2 - s), div_eq_mul_inv, inv_Gammaℝ_two_sub hs,
    completedSinZeta_one_sub, hurwitzZetaOdd, ← div_eq_mul_inv, ← mul_div_assoc, ← mul_div_assoc,
    mul_comm]

end HurwitzZeta

