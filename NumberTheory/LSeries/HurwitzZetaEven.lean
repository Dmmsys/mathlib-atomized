/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.NumberTheory.LSeries.AbstractFuncEq
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Even Hurwitz zeta functions

In this file we study the functions on `ℂ` which are the meromorphic continuation of the following
series (convergent for `1 < re s`), where `a ∈ ℝ` is a parameter:

`hurwitzZetaEven a s = 1 / 2 * ∑' n : ℤ, 1 / |n + a| ^ s`

and

`cosZeta a s = ∑' n : ℕ, cos (2 * π * a * n) / |n| ^ s`.

Note that the term for `n = -a` in the first sum is omitted if `a` is an integer, and the term for
`n = 0` is omitted in the second sum (always).

Of course, we cannot *define* these functions by the above formulae (since existence of the
meromorphic continuation is not at all obvious); we in fact construct them as Mellin transforms of
various versions of the Jacobi theta function.

We also define completed versions of these functions with nicer functional equations (satisfying
`completedHurwitzZetaEven a s = Gammaℝ s * hurwitzZetaEven a s`, and similarly for `cosZeta`); and
modified versions with a subscript `0`, which are entire functions differing from the above by
multiples of `1 / s` and `1 / (1 - s)`.

## Main definitions and theorems
* `hurwitzZetaEven` and `cosZeta`: the zeta functions
* `completedHurwitzZetaEven` and `completedCosZeta`: completed variants
* `differentiableAt_hurwitzZetaEven` and `differentiableAt_cosZeta`:
  differentiability away from `s = 1`
* `completedHurwitzZetaEven_one_sub`: the functional equation
  `completedHurwitzZetaEven a (1 - s) = completedCosZeta a s`
* `hasSum_int_hurwitzZetaEven` and `hasSum_nat_cosZeta`: relation between the zeta functions and
  the corresponding Dirichlet series for `1 < re s`.
-/

@[expose] public section
noncomputable section

open Complex Filter Topology Asymptotics Real Set MeasureTheory

namespace HurwitzZeta

section kernel_defs
/-!
## Definitions and elementary properties of kernels
-/

/-- Even Hurwitz zeta kernel (function whose Mellin transform will be the even part of the
completed Hurwitz zeta function). See `evenKernel_def` for the defining formula, and
`hasSum_int_evenKernel` for an expression as a sum over `ℤ`. -/
/-
**HurwitzZeta.evenKernel** 是 Mathlib 中的一个定义，位于命名空间 `HurwitzZeta`。
形式化陈述：UnitAddCircle → ℝ → ℝ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Even Hurwitz zeta kernel (function whose Mellin transform will be the even part 
of the
completed Hurwitz zeta function). See `evenKernel_def` for the defining formula,
 and
`hasSum_int_evenKernel` for an expression as a sum over `ℤ`.
-/
@[irreducible] def evenKernel (a : UnitAddCircle) (x : ℝ) : ℝ :=
  (show Function.Periodic
    (fun ξ : ℝ ↦ rexp (-π * ξ ^ 2 * x) * re (jacobiTheta₂ (ξ * I * x) (I * x))) 1 by
      intro ξ
      simp only [ofReal_add, ofReal_one, add_mul, one_mul, jacobiTheta₂_add_left']
      have : cexp (-↑π * I * ((I * ↑x) + 2 * (↑ξ * I * ↑x))) = rexp (π * (x + 2 * ξ * x)) := by
        ring_nf
        simp [I_sq]
      rw [this, re_ofReal_mul, ← mul_assoc, ← Real.exp_add]
      congr
      ring).lift a
/-
**HurwitzZeta.evenKernel_def** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：evenKernel_def (a x : Real) : ↑(evenKernel ↑a x) = cexp (-π * a ^ 2 * x) *
 jacobiTheta₂ (a * I * x) (I * x)
参数：a x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `HurwitzZeta.evenKernel.eq_1`：∀ (a : UnitAddCircle) (x : ℝ), HurwitzZeta.
evenKernel a x = ⋯.lift a
· 使用定理 `Function.Periodic.lift.congr_simp`：∀ {α : Type u_1} {β : Type u_2} {f f_
1 : α → β} (e_f : f = f_1) {c : α} [inst : AddGroup α] (h : Function.Periodic f 
c)   (x x_1 : α ⧸ AddSu…
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `Complex.ofReal_exp`：ofReal_exp (x : Real) : (Real.exp x : Complex) = exp
 x
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
· 使用定理 `Complex.ofReal_pow`：ofReal_pow (r : Real) (n : Nat) : ((r ^ n : Real) : 
Complex) = (r : Complex) ^ n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Complex.re_eq_add_conj`：re_eq_add_conj (z : Complex) : (z.re : Complex) 
= (z + conj z) / 2
· 使用引理 `jacobiTheta₂_conj`：jacobiTheta₂_conj (z τ : Complex) : conj (jacobiTheta
₂ z τ) = jacobiTheta₂ (conj z) (-conj τ)
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Complex.conj_ofReal`：conj_ofReal (r : Real) : conj (r : Complex) = r
· 使用定理 `Complex.conj_I`：conj_I : conj I = -I
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用引理 `jacobiTheta₂_neg_left`：jacobiTheta₂_neg_left (z τ : Complex) : jacobiThe
ta₂ (-z) τ = jacobiTheta₂ z τ
· 使用定理 `mul_div_cancel_right₀`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [ins
t_1 : Div M₀] [MulDivCancelClass M₀] (a : M₀) {b : M₀},   b ≠ 0 → a * b / b = a
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
· 使用引理 `two_ne_zero'`：two_ne_zero' [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma evenKernel_def (a x : ℝ) :
    ↑(evenKernel ↑a x) = cexp (-π * a ^ 2 * x) * jacobiTheta₂ (a * I * x) (I * x) := by
  simp [evenKernel, re_eq_add_conj, jacobiTheta₂_conj, ← mul_two,
    mul_div_cancel_right₀ _ (two_ne_zero' ℂ)]

/-- For `x ≤ 0` the defining sum diverges, so the kernel is 0. -/
/-
**HurwitzZeta.evenKernel_undef** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：evenKernel_undef (a : UnitAddCircle) {x : Real} (hx : x <= 0) : evenKernel
 a x = 0
参数：a : UnitAddCircle；hx : x <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientAddGroup.induction_on`：∀ {α : Type u_1} [inst : AddGroup α] {s :
 AddSubgroup α} {C : α ⧸ s → Prop} (x : α ⧸ s), (∀ (z : α), C ↑z) → C x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HurwitzZeta.evenKernel_def`：evenKernel_def (a x : Real) : ↑(evenKernel ↑
a x) = cexp (-π * a ^ 2 * x) * jacobiTheta₂ (a * I * x) (I * x)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用引理 `jacobiTheta₂_undef`：jacobiTheta₂_undef (z : Complex) {τ : Complex} (hτ :
 im τ <= 0) : jacobiTheta₂ z τ = 0
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
For `x ≤ 0` the defining sum diverges, so the kernel is 0.
-/
lemma evenKernel_undef (a : UnitAddCircle) {x : ℝ} (hx : x ≤ 0) : evenKernel a x = 0 := by
  induction a using QuotientAddGroup.induction_on with
  | H a' => simp [← ofReal_inj, evenKernel_def, jacobiTheta₂_undef _ (by simpa : (I * ↑x).im ≤ 0)]

/-- Cosine Hurwitz zeta kernel. See `cosKernel_def` for the defining formula, and
`hasSum_int_cosKernel` for expression as a sum. -/
/-
**HurwitzZeta.cosKernel** 是 Mathlib 中的一个定义，位于命名空间 `HurwitzZeta`。
形式化陈述：UnitAddCircle → ℝ → ℝ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Cosine Hurwitz zeta kernel. See `cosKernel_def` for the defining formula, and
`hasSum_int_cosKernel` for expression as a sum.
-/
@[irreducible] def cosKernel (a : UnitAddCircle) (x : ℝ) : ℝ :=
  (show Function.Periodic (fun ξ : ℝ ↦ re (jacobiTheta₂ ξ (I * x))) 1 by
    intro ξ; simp [jacobiTheta₂_add_left]).lift a
/-
**HurwitzZeta.cosKernel_def** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：cosKernel_def (a x : Real) : ↑(cosKernel ↑a x) = jacobiTheta₂ a (I * x)
参数：a x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `HurwitzZeta.cosKernel.eq_1`：∀ (a : UnitAddCircle) (x : ℝ), HurwitzZeta.c
osKernel a x = ⋯.lift a
· 使用定理 `Complex.re_eq_add_conj`：re_eq_add_conj (z : Complex) : (z.re : Complex) 
= (z + conj z) / 2
· 使用引理 `jacobiTheta₂_conj`：jacobiTheta₂_conj (z τ : Complex) : conj (jacobiTheta
₂ z τ) = jacobiTheta₂ (conj z) (-conj τ)
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
· 使用定理 `mul_div_cancel_right₀`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [ins
t_1 : Div M₀] [MulDivCancelClass M₀] (a : M₀) {b : M₀},   b ≠ 0 → a * b / b = a
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
· 使用引理 `two_ne_zero'`：two_ne_zero' [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cosKernel_def (a x : ℝ) : ↑(cosKernel ↑a x) = jacobiTheta₂ a (I * x) := by
  simp [cosKernel, re_eq_add_conj, jacobiTheta₂_conj, ← mul_two,
    mul_div_cancel_right₀ _ (two_ne_zero' ℂ)]
/-
**HurwitzZeta.cosKernel_undef** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：cosKernel_undef (a : UnitAddCircle) {x : Real} (hx : x <= 0) : cosKernel a
 x = 0
参数：a : UnitAddCircle；hx : x <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientAddGroup.induction_on`：∀ {α : Type u_1} [inst : AddGroup α] {s :
 AddSubgroup α} {C : α ⧸ s → Prop} (x : α ⧸ s), (∀ (z : α), C ↑z) → C x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HurwitzZeta.cosKernel_def`：cosKernel_def (a x : Real) : ↑(cosKernel ↑a x
) = jacobiTheta₂ a (I * x)
· 使用引理 `jacobiTheta₂_undef`：jacobiTheta₂_undef (z : Complex) {τ : Complex} (hτ :
 im τ <= 0) : jacobiTheta₂ z τ = 0
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cosKernel_undef (a : UnitAddCircle) {x : ℝ} (hx : x ≤ 0) : cosKernel a x = 0 := by
  induction a using QuotientAddGroup.induction_on with
  | H => simp [← ofReal_inj, cosKernel_def, jacobiTheta₂_undef _ (by simpa : (I * ↑x).im ≤ 0)]

/-- For `a = 0`, both kernels agree. -/
/-
**HurwitzZeta.evenKernel_eq_cosKernel_of_zero** 是 Mathlib 中的一个引理，位于命名空间 `Hurwitz
Zeta`。
形式化陈述：evenKernel_eq_cosKernel_of_zero : evenKernel 0 = cosKernel 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HurwitzZeta.evenKernel_def`：evenKernel_def (a x : Real) : ↑(evenKernel ↑
a x) = cexp (-π * a ^ 2 * x) * jacobiTheta₂ (a * I * x) (I * x)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Complex.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `HurwitzZeta.cosKernel_def`：cosKernel_def (a x : Real) : ↑(cosKernel ↑a x
) = jacobiTheta₂ a (I * x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
For `a = 0`, both kernels agree.
-/
lemma evenKernel_eq_cosKernel_of_zero : evenKernel 0 = cosKernel 0 := by
  ext1 x
  simp [← QuotientAddGroup.mk_zero, ← ofReal_inj, evenKernel_def, cosKernel_def]

@[simp]
/-
**HurwitzZeta.evenKernel_neg** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：evenKernel_neg (a : UnitAddCircle) (x : Real) : evenKernel (-a) x = evenKe
rnel a x
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
· 使用引理 `HurwitzZeta.evenKernel_def`：evenKernel_def (a x : Real) : ↑(evenKernel ↑
a x) = cexp (-π * a ^ 2 * x) * jacobiTheta₂ (a * I * x) (I * x)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
· 使用定理 `Even.neg_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistribNeg
 α] {n : ℕ}, Even n → ∀ (a : α), (-a) ^ n = a ^ n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用引理 `jacobiTheta₂_neg_left`：jacobiTheta₂_neg_left (z τ : Complex) : jacobiThe
ta₂ (-z) τ = jacobiTheta₂ z τ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma evenKernel_neg (a : UnitAddCircle) (x : ℝ) : evenKernel (-a) x = evenKernel a x := by
  induction a using QuotientAddGroup.induction_on with
  | H => simp [← QuotientAddGroup.mk_neg, ← ofReal_inj, evenKernel_def, jacobiTheta₂_neg_left]

@[simp]
/-
**HurwitzZeta.cosKernel_neg** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：cosKernel_neg (a : UnitAddCircle) (x : Real) : cosKernel (-a) x = cosKerne
l a x
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
· 使用引理 `HurwitzZeta.cosKernel_def`：cosKernel_def (a x : Real) : ↑(cosKernel ↑a x
) = jacobiTheta₂ a (I * x)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
· 使用引理 `jacobiTheta₂_neg_left`：jacobiTheta₂_neg_left (z τ : Complex) : jacobiThe
ta₂ (-z) τ = jacobiTheta₂ z τ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cosKernel_neg (a : UnitAddCircle) (x : ℝ) : cosKernel (-a) x = cosKernel a x := by
  induction a using QuotientAddGroup.induction_on with
  | H => simp [← QuotientAddGroup.mk_neg, ← ofReal_inj, cosKernel_def]
/-
**HurwitzZeta.continuousOn_evenKernel** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：continuousOn_evenKernel (a : UnitAddCircle) : ContinuousOn (evenKernel a) 
(Ioi 0)
参数：a : UnitAddCircle。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientAddGroup.induction_on`：∀ {α : Type u_1} [inst : AddGroup α] {s :
 AddSubgroup α} {C : α ⧸ s → Prop} (x : α ⧸ s), (∀ (z : α), C ↑z) → C x
· 使用定理 `Continuous.comp_continuousOn`：Continuous.comp_continuousOn {g : β -> γ} 
{f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continuou
sOn (g ∘ f) s
· 使用定理 `Complex.continuous_re`：Continuous Complex.re
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `HurwitzZeta.evenKernel_def`：evenKernel_def (a x : Real) : ↑(evenKernel ↑
a x) = cexp (-π * a ^ 2 * x) * jacobiTheta₂ (a * I * x) (I * x)
· 使用定理 `continuousOn_of_forall_continuousAt`：continuousOn_of_forall_continuousAt
 (hcont : forall x in s, ContinuousAt f x) : ContinuousOn f s
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
· 使用定理 `ContinuousAt.cexp`：ContinuousAt.cexp (h : ContinuousAt f x) : Continuous
At (fun y => exp (f y)) x
· 使用定理 `ContinuousAt.const_mul`：ContinuousAt.const_mul (hf : ContinuousAt f x) (
b : M) : ContinuousAt (b * f ·) x
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
· 使用定理 `ContinuousAt.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace
 Z] {f …
· 使用引理 `continuousAt_jacobiTheta₂`：continuousAt_jacobiTheta₂ (z : Complex) {τ : 
Complex} (hτ : 0 < im τ) : ContinuousAt (fun p : Complex × Complex => jacobiThet
a₂ p.1 p.2) (z,…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `ContinuousAt.prodMk`：ContinuousAt.prodMk {f : X -> Y} {g : X -> Z} {x : 
X} (hf : ContinuousAt f x) (hg : ContinuousAt g x) : ContinuousAt (fun x => (f x
, g x)) x
-/
lemma continuousOn_evenKernel (a : UnitAddCircle) : ContinuousOn (evenKernel a) (Ioi 0) := by
  induction a using QuotientAddGroup.induction_on with | H a' =>
  apply continuous_re.comp_continuousOn (f := fun x ↦ (evenKernel a' x : ℂ))
  simp only [evenKernel_def]
  refine continuousOn_of_forall_continuousAt (fun x hx ↦ .mul (by fun_prop) ?_)
  exact (continuousAt_jacobiTheta₂ (a' * I * x) <| by simpa).comp
    (f := fun u : ℝ ↦ (a' * I * u, I * u)) (by fun_prop)
/-
**HurwitzZeta.continuousOn_cosKernel** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：continuousOn_cosKernel (a : UnitAddCircle) : ContinuousOn (cosKernel a) (I
oi 0)
参数：a : UnitAddCircle。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientAddGroup.induction_on`：∀ {α : Type u_1} [inst : AddGroup α] {s :
 AddSubgroup α} {C : α ⧸ s → Prop} (x : α ⧸ s), (∀ (z : α), C ↑z) → C x
· 使用定理 `Continuous.comp_continuousOn`：Continuous.comp_continuousOn {g : β -> γ} 
{f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continuou
sOn (g ∘ f) s
· 使用定理 `Complex.continuous_re`：Continuous Complex.re
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `HurwitzZeta.cosKernel_def`：cosKernel_def (a x : Real) : ↑(cosKernel ↑a x
) = jacobiTheta₂ a (I * x)
· 使用定理 `continuousOn_of_forall_continuousAt`：continuousOn_of_forall_continuousAt
 (hcont : forall x in s, ContinuousAt f x) : ContinuousOn f s
· 使用定理 `ContinuousAt.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace
 Z] {f …
· 使用引理 `continuousAt_jacobiTheta₂`：continuousAt_jacobiTheta₂ (z : Complex) {τ : 
Complex} (hτ : 0 < im τ) : ContinuousAt (fun p : Complex × Complex => jacobiThet
a₂ p.1 p.2) (z,…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `ContinuousAt.prodMk`：ContinuousAt.prodMk {f : X -> Y} {g : X -> Z} {x : 
X} (hf : ContinuousAt f x) (hg : ContinuousAt g x) : ContinuousAt (fun x => (f x
, g x)) x
· 使用定理 `continuousAt_const`：continuousAt_const : ContinuousAt (fun _ : X => y) x
· 使用定理 `ContinuousAt.const_mul`：ContinuousAt.const_mul (hf : ContinuousAt f x) (
b : M) : ContinuousAt (b * f ·) x
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
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
-/
lemma continuousOn_cosKernel (a : UnitAddCircle) : ContinuousOn (cosKernel a) (Ioi 0) := by
  induction a using QuotientAddGroup.induction_on with | H a' =>
  apply continuous_re.comp_continuousOn (f := fun x ↦ (cosKernel a' x : ℂ))
  simp only [cosKernel_def]
  refine continuousOn_of_forall_continuousAt (fun x hx ↦ ?_)
  exact (continuousAt_jacobiTheta₂ a' <| by simpa).comp
    (f := fun u : ℝ ↦ ((a' : ℂ), I * u)) (by fun_prop)
/-
**HurwitzZeta.evenKernel_functional_equation** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZ
eta`。
形式化陈述：evenKernel_functional_equation (a : UnitAddCircle) (x : Real) : evenKernel
 a x = 1 / x ^ (1 / 2 : Real) * cosKernel a (1 / x)
参数：a : UnitAddCircle；x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HurwitzZeta.evenKernel_undef`：evenKernel_undef (a : UnitAddCircle) {x : 
Real} (hx : x <= 0) : evenKernel a x = 0
· 使用引理 `HurwitzZeta.cosKernel_undef`：cosKernel_undef (a : UnitAddCircle) {x : Re
al} (hx : x <= 0) : cosKernel a x = 0
· 使用引理 `div_nonpos_of_nonneg_of_nonpos`：div_nonpos_of_nonneg_of_nonpos (ha : 0 <
= a) (hb : b <= 0) : a / b <= 0
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `QuotientAddGroup.induction_on`：∀ {α : Type u_1} [inst : AddGroup α] {s :
 AddSubgroup α} {C : α ⧸ s → Prop} (x : α ⧸ s), (∀ (z : α), C ↑z) → C x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.ofReal_inj`：ofReal_inj {z w : Real} : (z : Complex) = w ↔ z = w
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用引理 `HurwitzZeta.evenKernel_def`：evenKernel_def (a x : Real) : ↑(evenKernel ↑
a x) = cexp (-π * a ^ 2 * x) * jacobiTheta₂ (a * I * x) (I * x)
· 使用引理 `HurwitzZeta.cosKernel_def`：cosKernel_def (a x : Real) : ↑(cosKernel ↑a x
) = jacobiTheta₂ a (I * x)
· 使用定理 `jacobiTheta₂_functional_equation`：jacobiTheta₂_functional_equation (z τ 
: Complex) : jacobiTheta₂ z τ = 1 / (-I * τ) ^ (1 / 2 : Complex) * cexp (-π * I 
* z ^ 2 / τ) * jacobiT…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.ofReal_div`：ofReal_div (r s : Real) : ((r / s : Real) : Complex)
 = r / s
· 使用定理 `div_div`：div_div : a / b / c = a / (b * c)
· 使用定理 `mul_one_div`：mul_one_div (x y : G) : x * (1 / y) = x / y
· 使用定理 `Complex.div_I`：div_I (z : Complex) : z / I = -(z * I)
· 使用定理 `neg_one_mul`：neg_one_mul (a : α) : -1 * a = -a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Complex.I_ne_zero`：Complex.I ≠ 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Complex.ofReal_ne_zero`：ofReal_ne_zero {z : Real} : (z : Complex) != 0 ↔
 z != 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
（共 79 条，此处仅展示前 30 条）
-/
lemma evenKernel_functional_equation (a : UnitAddCircle) (x : ℝ) :
    evenKernel a x = 1 / x ^ (1 / 2 : ℝ) * cosKernel a (1 / x) := by
  rcases le_or_gt x 0 with hx | hx
  · rw [evenKernel_undef _ hx, cosKernel_undef, mul_zero]
    exact div_nonpos_of_nonneg_of_nonpos zero_le_one hx
  induction a using QuotientAddGroup.induction_on with | H a =>
  rw [← ofReal_inj, ofReal_mul, evenKernel_def, cosKernel_def, jacobiTheta₂_functional_equation]
  have h1 : I * ↑(1 / x) = -1 / (I * x) := by
    push_cast
    rw [← div_div, mul_one_div, div_I, neg_one_mul, neg_neg]
  have hx' : I * x ≠ 0 := mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hx.ne')
  have h2 : a * I * x / (I * x) = a := by
    rw [div_eq_iff hx']
    ring
  have h3 : 1 / (-I * (I * x)) ^ (1 / 2 : ℂ) = 1 / ↑(x ^ (1 / 2 : ℝ)) := by
    rw [neg_mul, ← mul_assoc, I_mul_I, neg_one_mul, neg_neg, ofReal_cpow hx.le, ofReal_div,
      ofReal_one, ofReal_ofNat]
  have h4 : -π * I * (a * I * x) ^ 2 / (I * x) = - (-π * a ^ 2 * x) := by
    rw [mul_pow, mul_pow, I_sq, div_eq_iff hx']
    ring
  rw [h1, h2, h3, h4, ← mul_assoc, mul_comm (cexp _), mul_assoc _ (cexp _) (cexp _),
    ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one, ofReal_div, ofReal_one]

end kernel_defs

section asymp

/-!
## Formulae for the kernels as sums
-/

/-
**HurwitzZeta.hasSum_int_evenKernel** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：hasSum_int_evenKernel (a : Real) {t : Real} (ht : 0 < t) : HasSum (fun n :
 Int => rexp (-π * (n + a) ^ 2 * t)) (evenKernel a t)
参数：a : Real；ht : 0 < t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.hasSum_ofReal`：∀ {α : Type u_1} {L : SummationFilter α} {f : α →
 ℝ} {x : ℝ}, HasSum (fun x => ↑(f x)) (↑x) L ↔ HasSum f x L
· 使用引理 `HurwitzZeta.evenKernel_def`：evenKernel_def (a x : Real) : ↑(evenKernel ↑
a x) = cexp (-π * a ^ 2 * x) * jacobiTheta₂ (a * I * x) (I * x)
· 使用定理 `jacobiTheta₂_term.eq_1`：∀ (n : ℤ) (z τ : ℂ),   jacobiTheta₂_term n z τ =
 Complex.exp (2 * ↑Real.pi * Complex.I * ↑n * z + ↑Real.pi * Complex.I * ↑n ^ 2 
* τ)
· 使用定理 `Complex.exp_add`：exp_add : exp (x + y) = exp x * exp y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Complex.ofReal_exp`：ofReal_exp (x : Real) : (Real.exp x : Complex) = exp
 x
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `Complex.ofReal_pow`：ofReal_pow (r : Real) (n : Nat) : ((r ^ n : Real) : 
Complex) = (r : Complex) ^ n
· 使用定理 `Complex.ofReal_add`：ofReal_add (r s : Real) : ((r + s : Real) : Complex)
 = r + s
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
· 使用引理 `hasSum_jacobiTheta₂_term`：hasSum_jacobiTheta₂_term (z : Complex) {τ : Co
mplex} (hτ : 0 < im τ) : HasSum (fun n => jacobiTheta₂_term n z τ) (jacobiTheta₂
 z τ)
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a

--- 原说明 ---
## Formulae for the kernels as sums
-/
lemma hasSum_int_evenKernel (a : ℝ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ ↦ rexp (-π * (n + a) ^ 2 * t)) (evenKernel a t) := by
  rw [← hasSum_ofReal, evenKernel_def]
  have (n : ℤ) : cexp (-(π * (n + a) ^ 2 * t)) = cexp (-(π * a ^ 2 * t)) *
      jacobiTheta₂_term n (a * I * t) (I * t) := by
    rw [jacobiTheta₂_term, ← Complex.exp_add]
    grind [I_sq]
  simpa [this] using (hasSum_jacobiTheta₂_term _ (by simpa)).mul_left _
/-
**HurwitzZeta.hasSum_int_cosKernel** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：hasSum_int_cosKernel (a : Real) {t : Real} (ht : 0 < t) : HasSum (fun n : 
Int => cexp (2 * π * I * a * n) * rexp (-π * n ^ 2 * t)) ↑(cosKernel a t)
参数：a : Real；ht : 0 < t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HurwitzZeta.cosKernel_def`：cosKernel_def (a x : Real) : ↑(cosKernel ↑a x
) = jacobiTheta₂ a (I * x)
· 使用定理 `jacobiTheta₂_term.eq_1`：∀ (n : ℤ) (z τ : ℂ),   jacobiTheta₂_term n z τ =
 Complex.exp (2 * ↑Real.pi * Complex.I * ↑n * z + ↑Real.pi * Complex.I * ↑n ^ 2 
* τ)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.exp_add`：exp_add : exp (x + y) = exp x * exp y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
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
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pow_mul`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₂ c₂ : R} {ea₁ b c₁ : ℕ} {xa₁ c₃ d : R},   ea₁ * b = c₁ → a₂ ^ b = c₂
 → xa₁ ^ c₁ * Nat.rawCast 1 …
（共 68 条，此处仅展示前 30 条）
-/
lemma hasSum_int_cosKernel (a : ℝ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ ↦ cexp (2 * π * I * a * n) * rexp (-π * n ^ 2 * t)) ↑(cosKernel a t) := by
  rw [cosKernel_def a t]
  have (n : ℤ) : cexp (2 * π * I * a * n) * cexp (-(π * n ^ 2 * t)) =
      jacobiTheta₂_term n a (I * ↑t) := by
    rw [jacobiTheta₂_term, ← Complex.exp_add]
    ring_nf
    simp [sub_eq_add_neg]
  simpa [this] using hasSum_jacobiTheta₂_term _ (by simpa)

/-- Modified version of `hasSum_int_evenKernel` omitting the constant term at `∞`. -/
/-
**HurwitzZeta.hasSum_int_evenKernel** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：hasSum_int_evenKernel (a : Real) {t : Real} (ht : 0 < t) : HasSum (fun n :
 Int => rexp (-π * (n + a) ^ 2 * t)) (evenKernel a t)
参数：a : Real；ht : 0 < t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.hasSum_ofReal`：∀ {α : Type u_1} {L : SummationFilter α} {f : α →
 ℝ} {x : ℝ}, HasSum (fun x => ↑(f x)) (↑x) L ↔ HasSum f x L
· 使用引理 `HurwitzZeta.evenKernel_def`：evenKernel_def (a x : Real) : ↑(evenKernel ↑
a x) = cexp (-π * a ^ 2 * x) * jacobiTheta₂ (a * I * x) (I * x)
· 使用定理 `jacobiTheta₂_term.eq_1`：∀ (n : ℤ) (z τ : ℂ),   jacobiTheta₂_term n z τ =
 Complex.exp (2 * ↑Real.pi * Complex.I * ↑n * z + ↑Real.pi * Complex.I * ↑n ^ 2 
* τ)
· 使用定理 `Complex.exp_add`：exp_add : exp (x + y) = exp x * exp y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Complex.ofReal_exp`：ofReal_exp (x : Real) : (Real.exp x : Complex) = exp
 x
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `Complex.ofReal_pow`：ofReal_pow (r : Real) (n : Nat) : ((r ^ n : Real) : 
Complex) = (r : Complex) ^ n
· 使用定理 `Complex.ofReal_add`：ofReal_add (r s : Real) : ((r + s : Real) : Complex)
 = r + s
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
· 使用引理 `hasSum_jacobiTheta₂_term`：hasSum_jacobiTheta₂_term (z : Complex) {τ : Co
mplex} (hτ : 0 < im τ) : HasSum (fun n => jacobiTheta₂_term n z τ) (jacobiTheta₂
 z τ)
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a

--- 原说明 ---
Modified version of `hasSum_int_evenKernel` omitting the constant term at `∞`.
-/
lemma hasSum_int_evenKernel₀ (a : ℝ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ ↦ if n + a = 0 then 0 else rexp (-π * (n + a) ^ 2 * t))
    (evenKernel a t - if (a : UnitAddCircle) = 0 then 1 else 0) := by
  have := Classical.propDecidable -- speed up instance search for `if / then / else`
  simp_rw [AddCircle.coe_eq_zero_iff, zsmul_one]
  split_ifs with h
  · obtain ⟨k, rfl⟩ := h
    simpa [← Int.cast_add, add_eq_zero_iff_eq_neg]
      using hasSum_ite_sub_hasSum (hasSum_int_evenKernel (k : ℝ) ht) (-k)
  · suffices ∀ (n : ℤ), n + a ≠ 0 by simpa [this] using hasSum_int_evenKernel a ht
    contrapose! h
    let ⟨n, hn⟩ := h
    exact ⟨-n, by simpa [neg_eq_iff_add_eq_zero]⟩
/-
**HurwitzZeta.hasSum_int_cosKernel** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：hasSum_int_cosKernel (a : Real) {t : Real} (ht : 0 < t) : HasSum (fun n : 
Int => cexp (2 * π * I * a * n) * rexp (-π * n ^ 2 * t)) ↑(cosKernel a t)
参数：a : Real；ht : 0 < t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HurwitzZeta.cosKernel_def`：cosKernel_def (a x : Real) : ↑(cosKernel ↑a x
) = jacobiTheta₂ a (I * x)
· 使用定理 `jacobiTheta₂_term.eq_1`：∀ (n : ℤ) (z τ : ℂ),   jacobiTheta₂_term n z τ =
 Complex.exp (2 * ↑Real.pi * Complex.I * ↑n * z + ↑Real.pi * Complex.I * ↑n ^ 2 
* τ)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.exp_add`：exp_add : exp (x + y) = exp x * exp y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
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
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pow_mul`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₂ c₂ : R} {ea₁ b c₁ : ℕ} {xa₁ c₃ d : R},   ea₁ * b = c₁ → a₂ ^ b = c₂
 → xa₁ ^ c₁ * Nat.rawCast 1 …
（共 68 条，此处仅展示前 30 条）
-/
lemma hasSum_int_cosKernel₀ (a : ℝ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ ↦ if n = 0 then 0 else cexp (2 * π * I * a * n) * rexp (-π * n ^ 2 * t))
    (↑(cosKernel a t) - 1) := by
  simpa using hasSum_ite_sub_hasSum (hasSum_int_cosKernel a ht) 0
/-
**HurwitzZeta.hasSum_nat_cosKernel** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hasSum_nat_cosKernel₀ (a : ℝ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ ↦ 2 * Real.cos (2 * π * a * (n + 1)) * rexp (-π * (n + 1) ^ 2 * t))
    (cosKernel a t - 1) := by
  rw [← hasSum_ofReal, ofReal_sub, ofReal_one]
  have := (hasSum_int_cosKernel a ht).nat_add_neg
  rw [← hasSum_nat_add_iff' 1] at this
  simp_rw [Finset.sum_range_one, Nat.cast_zero, neg_zero, Int.cast_zero, zero_pow two_ne_zero,
    mul_zero, zero_mul, Complex.exp_zero, Real.exp_zero, ofReal_one, mul_one, Int.cast_neg,
    Int.cast_natCast, neg_sq, ← add_mul, add_sub_assoc, ← sub_sub, sub_self, zero_sub,
    ← sub_eq_add_neg, mul_neg] at this
  refine this.congr_fun fun n ↦ ?_
  push_cast
  rw [Complex.cos, mul_div_cancel₀ _ two_ne_zero]
  congr 3 <;> ring

/-!
## Asymptotics of the kernels as `t → ∞`
-/

/-- The function `evenKernel a - L` has exponential decay at `+∞`, where `L = 1` if
`a = 0` and `L = 0` otherwise. -/
/-
**HurwitzZeta.isBigO_atTop_evenKernel_sub** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta
`。
形式化陈述：isBigO_atTop_evenKernel_sub (a : UnitAddCircle) : exists p : Real, 0 < p ∧
 (evenKernel a · - (if a = 0 then 1 else 0)) =O[atTop] (rexp <| -p * ·)
参数：a : UnitAddCircle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientAddGroup.induction_on`：∀ {α : Type u_1} [inst : AddGroup α] {s :
 AddSubgroup α} {C : α ⧸ s → Prop} (x : α ⧸ s), (∀ (z : α), C ↑z) → C x
· 使用引理 `HurwitzKernelBounds.isBigO_atTop_F_int_zero_sub`：isBigO_atTop_F_int_zero
_sub (a : UnitAddCircle) : exists p, 0 < p ∧ (fun t => F_int 0 a t - (if a = 0 t
hen 1 else 0)) =O[atTop] fun t => exp…
· 使用定理 `Asymptotics.IsBigO.trans`：∀ {α : Type u_1} {E : Type u_3} {G : Type u_5}
 {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : SeminormedAddComm
Group F'] {l :…
· 使用定理 `Filter.EventuallyEq.isBigO`：∀ {α : Type u_1} {E : Type u_3} [inst : Norm
 E] {l : Filter α} {f₁ f₂ : α → E}, f₁ =ᶠ[l] f₂ → f₁ =O[l] f₂
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用引理 `HurwitzZeta.hasSum_int_evenKernel`：hasSum_int_evenKernel (a : Real) {t :
 Real} (ht : 0 < t) : HasSum (fun n : Int => rexp (-π * (n + a) ^ 2 * t)) (evenK
ernel a t)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Function.Periodic.lift.congr_simp`：∀ {α : Type u_1} {β : Type u_2} {f f_
1 : α → β} (e_f : f = f_1) {c : α} [inst : AddGroup α] (h : Function.Periodic f 
c)   (x x_1 : α ⧸ AddSu…
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The function `evenKernel a - L` has exponential decay at `+∞`, where `L = 1` if
`a = 0` and `L = 0` otherwise.
-/
lemma isBigO_atTop_evenKernel_sub (a : UnitAddCircle) : ∃ p : ℝ, 0 < p ∧
    (evenKernel a · - (if a = 0 then 1 else 0)) =O[atTop] (rexp <| -p * ·) := by
  induction a using QuotientAddGroup.induction_on with | H b =>
  obtain ⟨p, hp, hp'⟩ := HurwitzKernelBounds.isBigO_atTop_F_int_zero_sub b
  refine ⟨p, hp, (EventuallyEq.isBigO ?_).trans hp'⟩
  filter_upwards [eventually_gt_atTop 0] with t h
  simp [← (hasSum_int_evenKernel b h).tsum_eq, HurwitzKernelBounds.F_int, HurwitzKernelBounds.f_int]

/-- The function `cosKernel a - 1` has exponential decay at `+∞`, for any `a`. -/
/-
**HurwitzZeta.isBigO_atTop_cosKernel_sub** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`
。
形式化陈述：isBigO_atTop_cosKernel_sub (a : UnitAddCircle) : exists p, 0 < p ∧ IsBigO 
atTop (cosKernel a · - 1) (fun x => Real.exp (-p * x))
参数：a : UnitAddCircle。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientAddGroup.induction_on`：∀ {α : Type u_1} [inst : AddGroup α] {s :
 AddSubgroup α} {C : α ⧸ s → Prop} (x : α ⧸ s), (∀ (z : α), C ↑z) → C x
· 使用引理 `HurwitzKernelBounds.isBigO_atTop_F_nat_zero_sub`：isBigO_atTop_F_nat_zero
_sub {a : Real} (ha : 0 <= a) : exists p, 0 < p ∧ (fun t => F_nat 0 a t - (if a 
= 0 then 1 else 0)) =O[atTop] fun t =…
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用引理 `HurwitzZeta.hasSum_nat_cosKernel₀`：hasSum_nat_cosKernel₀ (a : Real) {t :
 Real} (ht : 0 < t) : HasSum (fun n : Nat => 2 * Real.cos (2 * π * a * (n + 1)) 
* rexp (-π * (n + 1) ^ …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `eq_false_intro`：eq_false_intro {a : Prop} (h : ¬a) : a = False
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `if_false`：∀ {α : Sort u_1} {x : Decidable False} (t e : α), (if False th
en t else e) = e
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `tsum_of_norm_bounded`：tsum_of_norm_bounded {f : ι -> E} {g : ι -> Real} 
{a : Real} (hg : HasSum g a) (h : forall i, ‖f i‖ <= g i) : ‖∑' i : ι, f i‖ <= a
· 使用定理 `HasSum.mul_left`：HasSum.mul_left (a₂) (h : HasSum f a₁ L) : HasSum (fun 
i => a₂ * f i) (a₂ * a₁) L
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
（共 54 条，此处仅展示前 30 条）

--- 原说明 ---
The function `cosKernel a - 1` has exponential decay at `+∞`, for any `a`.
-/
lemma isBigO_atTop_cosKernel_sub (a : UnitAddCircle) :
    ∃ p, 0 < p ∧ IsBigO atTop (cosKernel a · - 1) (fun x ↦ Real.exp (-p * x)) := by
  induction a using QuotientAddGroup.induction_on with | H a =>
  obtain ⟨p, hp, hp'⟩ := HurwitzKernelBounds.isBigO_atTop_F_nat_zero_sub zero_le_one
  refine ⟨p, hp, (Eventually.isBigO ?_).trans (hp'.const_mul_left 2)⟩
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp only [eq_false_intro one_ne_zero, if_false, sub_zero,
    ← (hasSum_nat_cosKernel₀ a ht).tsum_eq, HurwitzKernelBounds.F_nat]
  apply tsum_of_norm_bounded ((HurwitzKernelBounds.summable_f_nat 0 1 ht).hasSum.mul_left 2)
  intro n
  rw [norm_mul, norm_mul, norm_two, mul_assoc, mul_le_mul_iff_of_pos_left two_pos,
    norm_of_nonneg (exp_pos _).le, HurwitzKernelBounds.f_nat, pow_zero, one_mul, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (exp_pos _).le (abs_cos_le_one _)

end asymp

section FEPair
/-!
## Construction of an FE-pair
-/

/-- A `WeakFEPair` structure with `f = evenKernel a` and `g = cosKernel a`. -/
/-
**HurwitzZeta.hurwitzEvenFEPair** 是 Mathlib 中的一个定义，位于命名空间 `HurwitzZeta`。
形式化陈述：hurwitzEvenFEPair (a : UnitAddCircle) : WeakFEPair Complex where f
参数：a : UnitAddCircle。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `WeakFEPair` structure with `f = evenKernel a` and `g = cosKernel a`.
-/
def hurwitzEvenFEPair (a : UnitAddCircle) : WeakFEPair ℂ where
  f := ofReal ∘ evenKernel a
  g := ofReal ∘ cosKernel a
  hf_int := (continuous_ofReal.comp_continuousOn (continuousOn_evenKernel a)).locallyIntegrableOn
    measurableSet_Ioi
  hg_int := (continuous_ofReal.comp_continuousOn (continuousOn_cosKernel a)).locallyIntegrableOn
    measurableSet_Ioi
  k := 1 / 2
  hk := one_half_pos
  ε := 1
  hε := one_ne_zero
  f₀ := if a = 0 then 1 else 0
  hf_top r := by
    let ⟨v, hv, hv'⟩ := isBigO_atTop_evenKernel_sub a
    rw [← isBigO_norm_left] at hv' ⊢
    conv at hv' =>
      enter [2, x]; rw [← norm_real, ofReal_sub, apply_ite ((↑) : ℝ → ℂ), ofReal_one, ofReal_zero]
    exact hv'.trans (isLittleO_exp_neg_mul_rpow_atTop hv _).isBigO
  g₀ := 1
  hg_top r := by
    obtain ⟨p, hp, hp'⟩ := isBigO_atTop_cosKernel_sub a
    simpa using isBigO_ofReal_left.mpr <| hp'.trans (isLittleO_exp_neg_mul_rpow_atTop hp r).isBigO
  h_feq x hx := by simp [← ofReal_mul, evenKernel_functional_equation, inv_rpow (le_of_lt hx)]

@[simp]
/-
**HurwitzZeta.hurwitzEvenFEPair_zero_symm** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta
`。
形式化陈述：hurwitzEvenFEPair_zero_symm : (hurwitzEvenFEPair 0).symm = hurwitzEvenFEPa
ir 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HurwitzZeta.evenKernel_eq_cosKernel_of_zero`：evenKernel_eq_cosKernel_of_
zero : evenKernel 0 = cosKernel 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `WeakFEPair.hg_int`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_
1 : NormedSpace ℂ E] (self : WeakFEPair E),   MeasureTheory.LocallyIntegrableOn 
self.g …
· 使用定理 `WeakFEPair.hf_int`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_
1 : NormedSpace ℂ E] (self : WeakFEPair E),   MeasureTheory.LocallyIntegrableOn 
self.f …
· 使用定理 `WeakFEPair.hk`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : 
NormedSpace ℂ E] (self : WeakFEPair E), 0 < self.k
· 使用引理 `WeakFEPair.h_feq'`：WeakFEPair.h_feq' (P : WeakFEPair E) (x : Real) (hx :
 0 < x) : P.g (1 / x) = (P.ε⁻¹ * ↑(x ^ P.k)) • P.f x
· 使用定理 `WeakFEPair.hg_top`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_
1 : NormedSpace ℂ E] (self : WeakFEPair E) (r : ℝ),   (fun x => self.g x - self.
g₀) =O[…
· 使用定理 `WeakFEPair.hf_top`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_
1 : NormedSpace ℂ E] (self : WeakFEPair E) (r : ℝ),   (fun x => self.f x - self.
f₀) =O[…
-/
lemma hurwitzEvenFEPair_zero_symm :
    (hurwitzEvenFEPair 0).symm = hurwitzEvenFEPair 0 := by
  unfold hurwitzEvenFEPair WeakFEPair.symm
  congr 1 <;> simp [evenKernel_eq_cosKernel_of_zero]

@[simp]
/-
**HurwitzZeta.hurwitzEvenFEPair_neg** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：hurwitzEvenFEPair_neg (a : UnitAddCircle) : hurwitzEvenFEPair (-a) = hurwi
tzEvenFEPair a
参数：a : UnitAddCircle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `HurwitzZeta.evenKernel_neg`：evenKernel_neg (a : UnitAddCircle) (x : Real
) : evenKernel (-a) x = evenKernel a x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `HurwitzZeta.cosKernel_neg`：cosKernel_neg (a : UnitAddCircle) (x : Real) 
: cosKernel (-a) x = cosKernel a x
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
-/
lemma hurwitzEvenFEPair_neg (a : UnitAddCircle) : hurwitzEvenFEPair (-a) = hurwitzEvenFEPair a := by
  unfold hurwitzEvenFEPair
  congr 1 <;> simp [Function.comp_def]

/-!
## Definition of the completed even Hurwitz zeta function
-/

/--
The meromorphic function of `s` which agrees with
`1 / 2 * Gamma (s / 2) * π ^ (-s / 2) * ∑' (n : ℤ), 1 / |n + a| ^ s` for `1 < re s`.
-/
/-
**HurwitzZeta.completedHurwitzZetaEven** 是 Mathlib 中的一个定义，位于命名空间 `HurwitzZeta`。
形式化陈述：completedHurwitzZetaEven (a : UnitAddCircle) (s : Complex) : Complex
参数：a : UnitAddCircle；s : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The meromorphic function of `s` which agrees with
`1 / 2 * Gamma (s / 2) * π ^ (-s / 2) * ∑' (n : ℤ), 1 / |n + a| ^ s` for `1 < re
 s`.
-/
def completedHurwitzZetaEven (a : UnitAddCircle) (s : ℂ) : ℂ :=
  ((hurwitzEvenFEPair a).Λ (s / 2)) / 2

/-- The entire function differing from `completedHurwitzZetaEven a s` by a linear combination of
`1 / s` and `1 / (1 - s)`. -/
/-
**HurwitzZeta.completedHurwitzZetaEven** 是 Mathlib 中的一个定义，位于命名空间 `HurwitzZeta`。
形式化陈述：completedHurwitzZetaEven (a : UnitAddCircle) (s : Complex) : Complex
参数：a : UnitAddCircle；s : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The entire function differing from `completedHurwitzZetaEven a s` by a linear co
mbination of
`1 / s` and `1 / (1 - s)`.
-/
def completedHurwitzZetaEven₀ (a : UnitAddCircle) (s : ℂ) : ℂ :=
  ((hurwitzEvenFEPair a).Λ₀ (s / 2)) / 2
/-
**HurwitzZeta.completedHurwitzZetaEven_eq** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta
`。
形式化陈述：completedHurwitzZetaEven_eq (a : UnitAddCircle) (s : Complex) : completedH
urwitzZetaEven a s = completedHurwitzZetaEven₀ a s - (if a = 0 then 1 else 0) / 
s - 1 / (1 - s)
参数：a : UnitAddCircle；s : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HurwitzZeta.completedHurwitzZetaEven.eq_1`：∀ (a : UnitAddCircle) (s : ℂ)
,   HurwitzZeta.completedHurwitzZetaEven a s = (HurwitzZeta.hurwitzEvenFEPair a)
.Λ (s / 2) / 2
· 使用定理 `WeakFEPair.Λ.eq_1`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_
1 : NormedSpace ℂ E] (P : WeakFEPair E) (s : ℂ),   P.Λ s = P.Λ₀ s - (1 / s) • P.
f₀ - (P…
· 使用定理 `sub_div`：sub_div (a b c : K) : (a - b) / c = a / c - b / c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用定理 `div_div`：div_div : a / b / c = a / (b * c)
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `mul_one_div`：mul_one_div (x y : G) : x * (1 / y) = x / y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.ofReal_div`：ofReal_div (r s : Real) : ((r / s : Real) : Complex)
 = r / s
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma completedHurwitzZetaEven_eq (a : UnitAddCircle) (s : ℂ) :
    completedHurwitzZetaEven a s =
    completedHurwitzZetaEven₀ a s - (if a = 0 then 1 else 0) / s - 1 / (1 - s) := by
  rw [completedHurwitzZetaEven, WeakFEPair.Λ, sub_div, sub_div]
  congr 1
  · change completedHurwitzZetaEven₀ a s - (1 / (s / 2)) • (if a = 0 then 1 else 0) / 2 =
      completedHurwitzZetaEven₀ a s - (if a = 0 then 1 else 0) / s
    rw [smul_eq_mul, mul_comm, mul_div_assoc, div_div, div_mul_cancel₀ _ two_ne_zero, mul_one_div]
  · change (1 / (↑(1 / 2 : ℝ) - s / 2)) • 1 / 2 = 1 / (1 - s)
    push_cast
    rw [smul_eq_mul, mul_one, ← sub_div, div_div, div_mul_cancel₀ _ two_ne_zero]

/--
The meromorphic function of `s` which agrees with
`Gamma (s / 2) * π ^ (-s / 2) * ∑' n : ℕ, cos (2 * π * a * n) / n ^ s` for `1 < re s`.
-/
/-
**HurwitzZeta.completedCosZeta** 是 Mathlib 中的一个定义，位于命名空间 `HurwitzZeta`。
形式化陈述：completedCosZeta (a : UnitAddCircle) (s : Complex) : Complex
参数：a : UnitAddCircle；s : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The meromorphic function of `s` which agrees with
`Gamma (s / 2) * π ^ (-s / 2) * ∑' n : ℕ, cos (2 * π * a * n) / n ^ s` for `1 < 
re s`.
-/
def completedCosZeta (a : UnitAddCircle) (s : ℂ) : ℂ :=
  ((hurwitzEvenFEPair a).symm.Λ (s / 2)) / 2

/-- The entire function differing from `completedCosZeta a s` by a linear combination of
`1 / s` and `1 / (1 - s)`. -/
/-
**HurwitzZeta.completedCosZeta** 是 Mathlib 中的一个定义，位于命名空间 `HurwitzZeta`。
形式化陈述：completedCosZeta (a : UnitAddCircle) (s : Complex) : Complex
参数：a : UnitAddCircle；s : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The entire function differing from `completedCosZeta a s` by a linear combinatio
n of
`1 / s` and `1 / (1 - s)`.
-/
def completedCosZeta₀ (a : UnitAddCircle) (s : ℂ) : ℂ :=
  ((hurwitzEvenFEPair a).symm.Λ₀ (s / 2)) / 2
/-
**HurwitzZeta.completedCosZeta_eq** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：completedCosZeta_eq (a : UnitAddCircle) (s : Complex) : completedCosZeta a
 s = completedCosZeta₀ a s - 1 / s - (if a = 0 then 1 else 0) / (1 - s)
参数：a : UnitAddCircle；s : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HurwitzZeta.completedCosZeta.eq_1`：∀ (a : UnitAddCircle) (s : ℂ), Hurwit
zZeta.completedCosZeta a s = (HurwitzZeta.hurwitzEvenFEPair a).symm.Λ (s / 2) / 
2
· 使用定理 `WeakFEPair.Λ.eq_1`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_
1 : NormedSpace ℂ E] (P : WeakFEPair E) (s : ℂ),   P.Λ s = P.Λ₀ s - (1 / s) • P.
f₀ - (P…
· 使用定理 `sub_div`：sub_div (a b c : K) : (a - b) / c = a / c - b / c
· 使用定理 `HurwitzZeta.completedCosZeta₀.eq_1`：∀ (a : UnitAddCircle) (s : ℂ), Hurwi
tzZeta.completedCosZeta₀ a s = (HurwitzZeta.hurwitzEvenFEPair a).symm.Λ₀ (s / 2)
 / 2
· 使用定理 `WeakFEPair.hg_int`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_
1 : NormedSpace ℂ E] (self : WeakFEPair E),   MeasureTheory.LocallyIntegrableOn 
self.g …
· 使用定理 `WeakFEPair.hf_int`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_
1 : NormedSpace ℂ E] (self : WeakFEPair E),   MeasureTheory.LocallyIntegrableOn 
self.f …
· 使用定理 `WeakFEPair.hk`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : 
NormedSpace ℂ E] (self : WeakFEPair E), 0 < self.k
· 使用引理 `WeakFEPair.h_feq'`：WeakFEPair.h_feq' (P : WeakFEPair E) (x : Real) (hx :
 0 < x) : P.g (1 / x) = (P.ε⁻¹ * ↑(x ^ P.k)) • P.f x
· 使用定理 `WeakFEPair.hg_top`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_
1 : NormedSpace ℂ E] (self : WeakFEPair E) (r : ℝ),   (fun x => self.g x - self.
g₀) =O[…
· 使用定理 `WeakFEPair.hf_top`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_
1 : NormedSpace ℂ E] (self : WeakFEPair E) (r : ℝ),   (fun x => self.f x - self.
f₀) =O[…
· 使用定理 `WeakFEPair.symm.eq_1`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [in
st_1 : NormedSpace ℂ E] (P : WeakFEPair E),   P.symm =     { f := P.g, g := P.f,
 k := P.k,…
· 使用定理 `HurwitzZeta.hurwitzEvenFEPair.eq_1`：∀ (a : UnitAddCircle),   HurwitzZeta
.hurwitzEvenFEPair a =     { f := Complex.ofReal ∘ HurwitzZeta.evenKernel a, g :
= Complex.ofReal ∘ Hurwi…
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `div_div`：div_div : a / b / c = a / (b * c)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
· 使用引理 `two_ne_zero'`：two_ne_zero' [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.ofReal_div`：ofReal_div (r s : Real) : ((r / s : Real) : Complex)
 = r / s
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_one_div`：mul_one_div (x y : G) : x * (1 / y) = x / y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma completedCosZeta_eq (a : UnitAddCircle) (s : ℂ) :
    completedCosZeta a s =
    completedCosZeta₀ a s - 1 / s - (if a = 0 then 1 else 0) / (1 - s) := by
  rw [completedCosZeta, WeakFEPair.Λ, sub_div, sub_div]
  congr 1
  · rw [completedCosZeta₀, WeakFEPair.symm, hurwitzEvenFEPair, smul_eq_mul, mul_one, div_div,
      div_mul_cancel₀ _ (two_ne_zero' ℂ)]
  · simp_rw [WeakFEPair.symm, hurwitzEvenFEPair, push_cast, inv_one, smul_eq_mul,
      mul_comm _ (if _ then _ else _), mul_div_assoc, div_div, ← sub_div,
      div_mul_cancel₀ _ (two_ne_zero' ℂ), mul_one_div]

/-!
## Parity and functional equations
-/

@[simp]
/-
**HurwitzZeta.completedHurwitzZetaEven_neg** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZet
a`。
形式化陈述：completedHurwitzZetaEven_neg (a : UnitAddCircle) (s : Complex) : completed
HurwitzZetaEven (-a) s = completedHurwitzZetaEven a s
参数：a : UnitAddCircle；s : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HurwitzZeta.hurwitzEvenFEPair_neg`：hurwitzEvenFEPair_neg (a : UnitAddCir
cle) : hurwitzEvenFEPair (-a) = hurwitzEvenFEPair a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
## Parity and functional equations
-/
lemma completedHurwitzZetaEven_neg (a : UnitAddCircle) (s : ℂ) :
    completedHurwitzZetaEven (-a) s = completedHurwitzZetaEven a s := by
  simp [completedHurwitzZetaEven]

@[simp]
/-
**HurwitzZeta.completedHurwitzZetaEven** 是 Mathlib 中的一个定义，位于命名空间 `HurwitzZeta`。
形式化陈述：completedHurwitzZetaEven (a : UnitAddCircle) (s : Complex) : Complex
参数：a : UnitAddCircle；s : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma completedHurwitzZetaEven₀_neg (a : UnitAddCircle) (s : ℂ) :
    completedHurwitzZetaEven₀ (-a) s = completedHurwitzZetaEven₀ a s := by
  simp [completedHurwitzZetaEven₀]

@[simp]
/-
**HurwitzZeta.completedCosZeta_neg** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：completedCosZeta_neg (a : UnitAddCircle) (s : Complex) : completedCosZeta 
(-a) s = completedCosZeta a s
参数：a : UnitAddCircle；s : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HurwitzZeta.hurwitzEvenFEPair_neg`：hurwitzEvenFEPair_neg (a : UnitAddCir
cle) : hurwitzEvenFEPair (-a) = hurwitzEvenFEPair a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma completedCosZeta_neg (a : UnitAddCircle) (s : ℂ) :
    completedCosZeta (-a) s = completedCosZeta a s := by
  simp [completedCosZeta]

@[simp]
/-
**HurwitzZeta.completedCosZeta** 是 Mathlib 中的一个定义，位于命名空间 `HurwitzZeta`。
形式化陈述：completedCosZeta (a : UnitAddCircle) (s : Complex) : Complex
参数：a : UnitAddCircle；s : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma completedCosZeta₀_neg (a : UnitAddCircle) (s : ℂ) :
    completedCosZeta₀ (-a) s = completedCosZeta₀ a s := by
  simp [completedCosZeta₀]

/-- Functional equation for the even Hurwitz zeta function. -/
/-
**HurwitzZeta.completedHurwitzZetaEven_one_sub** 是 Mathlib 中的一个引理，位于命名空间 `Hurwit
zZeta`。
形式化陈述：completedHurwitzZetaEven_one_sub (a : UnitAddCircle) (s : Complex) : compl
etedHurwitzZetaEven a (1 - s) = completedCosZeta a s
参数：a : UnitAddCircle；s : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HurwitzZeta.completedHurwitzZetaEven.eq_1`：∀ (a : UnitAddCircle) (s : ℂ)
,   HurwitzZeta.completedHurwitzZetaEven a s = (HurwitzZeta.hurwitzEvenFEPair a)
.Λ (s / 2) / 2
· 使用定理 `HurwitzZeta.completedCosZeta.eq_1`：∀ (a : UnitAddCircle) (s : ℂ), Hurwit
zZeta.completedCosZeta a s = (HurwitzZeta.hurwitzEvenFEPair a).symm.Λ (s / 2) / 
2
· 使用定理 `sub_div`：sub_div (a b c : K) : (a - b) / c = a / c - b / c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Complex.ofReal_inv`：ofReal_inv (r : Real) : ((r⁻¹ : Real) : Complex) = (
r : Complex)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `WeakFEPair.functional_equation`：functional_equation (s : Complex) : P.Λ 
(P.k - s) = P.ε • P.symm.Λ s
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b

--- 原说明 ---
Functional equation for the even Hurwitz zeta function.
-/
lemma completedHurwitzZetaEven_one_sub (a : UnitAddCircle) (s : ℂ) :
    completedHurwitzZetaEven a (1 - s) = completedCosZeta a s := by
  rw [completedHurwitzZetaEven, completedCosZeta, sub_div,
    (by simp : (1 / 2 : ℂ) = ↑(1 / 2 : ℝ)),
    (by rfl : (1 / 2 : ℝ) = (hurwitzEvenFEPair a).k),
    (hurwitzEvenFEPair a).functional_equation (s / 2),
    (by rfl : (hurwitzEvenFEPair a).ε = 1),
    one_smul]

/-- Functional equation for the even Hurwitz zeta function with poles removed. -/
/-
**HurwitzZeta.completedHurwitzZetaEven** 是 Mathlib 中的一个定义，位于命名空间 `HurwitzZeta`。
形式化陈述：completedHurwitzZetaEven (a : UnitAddCircle) (s : Complex) : Complex
参数：a : UnitAddCircle；s : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Functional equation for the even Hurwitz zeta function with poles removed.
-/
lemma completedHurwitzZetaEven₀_one_sub (a : UnitAddCircle) (s : ℂ) :
    completedHurwitzZetaEven₀ a (1 - s) = completedCosZeta₀ a s := by
  rw [completedHurwitzZetaEven₀, completedCosZeta₀, sub_div,
    (by simp : (1 / 2 : ℂ) = ↑(1 / 2 : ℝ)),
    (by rfl : (1 / 2 : ℝ) = (hurwitzEvenFEPair a).k),
    (hurwitzEvenFEPair a).functional_equation₀ (s / 2),
    (by rfl : (hurwitzEvenFEPair a).ε = 1),
    one_smul]

/-- Functional equation for the even Hurwitz zeta function (alternative form). -/
/-
**HurwitzZeta.completedCosZeta_one_sub** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：completedCosZeta_one_sub (a : UnitAddCircle) (s : Complex) : completedCosZ
eta a (1 - s) = completedHurwitzZetaEven a s
参数：a : UnitAddCircle；s : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `HurwitzZeta.completedHurwitzZetaEven_one_sub`：completedHurwitzZetaEven_o
ne_sub (a : UnitAddCircle) (s : Complex) : completedHurwitzZetaEven a (1 - s) = 
completedCosZeta a s
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b

--- 原说明 ---
Functional equation for the even Hurwitz zeta function (alternative form).
-/
lemma completedCosZeta_one_sub (a : UnitAddCircle) (s : ℂ) :
    completedCosZeta a (1 - s) = completedHurwitzZetaEven a s := by
  rw [← completedHurwitzZetaEven_one_sub, sub_sub_cancel]

/-- Functional equation for the even Hurwitz zeta function with poles removed (alternative form). -/
/-
**HurwitzZeta.completedCosZeta** 是 Mathlib 中的一个定义，位于命名空间 `HurwitzZeta`。
形式化陈述：completedCosZeta (a : UnitAddCircle) (s : Complex) : Complex
参数：a : UnitAddCircle；s : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Functional equation for the even Hurwitz zeta function with poles removed (alter
native form).
-/
lemma completedCosZeta₀_one_sub (a : UnitAddCircle) (s : ℂ) :
    completedCosZeta₀ a (1 - s) = completedHurwitzZetaEven₀ a s := by
  rw [← completedHurwitzZetaEven₀_one_sub, sub_sub_cancel]

end FEPair

/-!
## Differentiability and residues
-/

section FEPair

/--
The even Hurwitz completed zeta is differentiable away from `s = 0` and `s = 1` (and also at
`s = 0` if `a ≠ 0`)
-/
/-
**HurwitzZeta.differentiableAt_completedHurwitzZetaEven** 是 Mathlib 中的一个引理，位于命名空
间 `HurwitzZeta`。
形式化陈述：differentiableAt_completedHurwitzZetaEven (a : UnitAddCircle) {s : Complex
} (hs : s != 0 ∨ a != 0) (hs' : s != 1) : DifferentiableAt Complex (completedHur
witzZetaEven a) s
参数：a : UnitAddCircle；hs : s != 0 ∨ a != 0；hs' : s != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.div_const`：DifferentiableAt.div_const (hc : Differentia
bleAt 𝕜 c x) (d : 𝕜') : DifferentiableAt 𝕜 (fun x => c x / d) x
· 使用定理 `DifferentiableAt.comp`：DifferentiableAt.comp {g : F -> G} (hg : Differen
tiableAt 𝕜 g (f x)) (hf : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (g ∘ f) x
· 使用定理 `WeakFEPair.differentiableAt_Λ`：differentiableAt_Λ {s : Complex} (hs : s 
!= 0 ∨ P.f₀ = 0) (hs' : s != P.k ∨ P.g₀ = 0) : DifferentiableAt Complex P.Λ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `WeakFEPair.mk.congr_simp`：∀ {E : Type u_1} [inst : NormedAddCommGroup E]
 [inst_1 : NormedSpace ℂ E] (f f_1 : ℝ → E) (e_f : f = f_1)   (g g_1 : ℝ → E) (e
_g : g = g_1) …
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Complex.ofReal_div`：ofReal_div (r s : Real) : ((r / s : Real) : Complex)
 = r / s
· 使用定理 `Complex.ofReal_one`：ofReal_one : ((1 : Real) : Complex) = 1
· 使用定理 `Complex.ofReal_ofNat`：∀ (n : ℕ) [inst : n.AtLeastTwo], ↑(OfNat.ofNat n) 
= OfNat.ofNat n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `div_left_inj'`：div_left_inj' (hc : c != 0) : a / c = b / c ↔ a = b
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `differentiableAt_id`：differentiableAt_id : DifferentiableAt 𝕜 id x

--- 原说明 ---
The even Hurwitz completed zeta is differentiable away from `s = 0` and `s = 1` 
(and also at
`s = 0` if `a ≠ 0`)
-/
lemma differentiableAt_completedHurwitzZetaEven
    (a : UnitAddCircle) {s : ℂ} (hs : s ≠ 0 ∨ a ≠ 0) (hs' : s ≠ 1) :
    DifferentiableAt ℂ (completedHurwitzZetaEven a) s := by
  refine (((hurwitzEvenFEPair a).differentiableAt_Λ ?_ (Or.inl ?_)).comp s
      (differentiableAt_id.div_const _)).div_const _
  · rcases hs with h | h <;>
    simp [hurwitzEvenFEPair, h]
  · change s / 2 ≠ ↑(1 / 2 : ℝ)
    rw [ofReal_div, ofReal_one, ofReal_ofNat]
    exact hs' ∘ (div_left_inj' two_ne_zero).mp
/-
**HurwitzZeta.differentiable_completedHurwitzZetaEven** 是 Mathlib 中的一个引理，位于命名空间 
`HurwitzZeta`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma differentiable_completedHurwitzZetaEven₀ (a : UnitAddCircle) :
    Differentiable ℂ (completedHurwitzZetaEven₀ a) :=
  ((hurwitzEvenFEPair a).differentiable_Λ₀.comp (differentiable_id.div_const _)).div_const _

/-- The difference of two completed even Hurwitz zeta functions is differentiable at `s = 1`. -/
/-
**HurwitzZeta.differentiableAt_one_completedHurwitzZetaEven_sub_completedHurwitz
ZetaEven** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：differentiableAt_one_completedHurwitzZetaEven_sub_completedHurwitzZetaEven
 (a b : UnitAddCircle) : DifferentiableAt Complex (fun s => completedHurwitzZeta
Even a s - completedHurwitzZetaEven b s) 1
参数：a b : UnitAddCircle。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `HurwitzZeta.completedHurwitzZetaEven_eq`：completedHurwitzZetaEven_eq (a 
: UnitAddCircle) (s : Complex) : completedHurwitzZetaEven a s = completedHurwitz
ZetaEven₀ a s - (if a = 0 the…
· 使用定理 `sub_div`：sub_div (a b c : K) : (a - b) / c = a / c - b / c
· 使用定理 `_private.Mathlib.NumberTheory.LSeries.HurwitzZetaEven.0.HurwitzZeta.diff
erentiableAt_one_completedHurwitzZetaEven_sub_completedHurwitzZetaEven._abel_1_1
`：∀ (a b : UnitAddCircle) (s : ℂ),   HurwitzZeta.completedHurwitzZetaEven₀ a s -
 (if a = 0 then 1 else 0) / s - 1 / (1 - s) -       (HurwitzZe…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `DifferentiableAt.sub`：DifferentiableAt.sub (hf : DifferentiableAt 𝕜 f x)
 (hg : DifferentiableAt 𝕜 g x) : DifferentiableAt 𝕜 (f - g) x
· 使用引理 `HurwitzZeta.differentiable_completedHurwitzZetaEven₀`：differentiable_com
pletedHurwitzZetaEven₀ (a : UnitAddCircle) : Differentiable Complex (completedHu
rwitzZetaEven₀ a)
· 使用定理 `DifferentiableAt.div`：DifferentiableAt.div (hc : DifferentiableAt 𝕜 c x)
 (hd : DifferentiableAt 𝕜 d x) (hx : d x != 0) : DifferentiableAt 𝕜 (c / d) x
· 使用定理 `differentiable_const`：differentiable_const (c : F) : Differentiable 𝕜 fu
n _ : E => c
· 使用定理 `differentiable_id`：differentiable_id : Differentiable 𝕜 (id : E -> E)
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0

--- 原说明 ---
The difference of two completed even Hurwitz zeta functions is differentiable at
 `s = 1`.
-/
lemma differentiableAt_one_completedHurwitzZetaEven_sub_completedHurwitzZetaEven
    (a b : UnitAddCircle) :
    DifferentiableAt ℂ (fun s ↦ completedHurwitzZetaEven a s - completedHurwitzZetaEven b s) 1 := by
  have (s : _) : completedHurwitzZetaEven a s - completedHurwitzZetaEven b s =
      completedHurwitzZetaEven₀ a s - completedHurwitzZetaEven₀ b s -
      ((if a = 0 then 1 else 0) - (if b = 0 then 1 else 0)) / s := by
    simp_rw [completedHurwitzZetaEven_eq, sub_div]
    abel
  rw [funext this]
  refine .sub ?_ <| (differentiable_const _ _).div (differentiable_id _) one_ne_zero
  apply DifferentiableAt.sub <;> apply differentiable_completedHurwitzZetaEven₀
/-
**HurwitzZeta.differentiableAt_completedCosZeta** 是 Mathlib 中的一个引理，位于命名空间 `Hurwi
tzZeta`。
形式化陈述：differentiableAt_completedCosZeta (a : UnitAddCircle) {s : Complex} (hs : 
s != 0) (hs' : s != 1 ∨ a != 0) : DifferentiableAt Complex (completedCosZeta a) 
s
参数：a : UnitAddCircle；hs : s != 0；hs' : s != 1 ∨ a != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.div_const`：DifferentiableAt.div_const (hc : Differentia
bleAt 𝕜 c x) (d : 𝕜') : DifferentiableAt 𝕜 (fun x => c x / d) x
· 使用定理 `DifferentiableAt.comp`：DifferentiableAt.comp {g : F -> G} (hg : Differen
tiableAt 𝕜 g (f x)) (hf : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (g ∘ f) x
· 使用定理 `WeakFEPair.differentiableAt_Λ`：differentiableAt_Λ {s : Complex} (hs : s 
!= 0 ∨ P.f₀ = 0) (hs' : s != P.k ∨ P.g₀ = 0) : DifferentiableAt Complex P.Λ s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `div_ne_zero_iff`：div_ne_zero_iff : a / b != 0 ↔ a != 0 ∧ b != 0
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Complex.ofReal_inv`：ofReal_inv (r : Real) : ((r⁻¹ : Real) : Complex) = (
r : Complex)⁻¹
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `div_left_inj'`：div_left_inj' (hc : c != 0) : a / c = b / c ↔ a = b
· 使用定理 `differentiableAt_id`：differentiableAt_id : DifferentiableAt 𝕜 id x
-/
lemma differentiableAt_completedCosZeta
    (a : UnitAddCircle) {s : ℂ} (hs : s ≠ 0) (hs' : s ≠ 1 ∨ a ≠ 0) :
    DifferentiableAt ℂ (completedCosZeta a) s := by
  refine (((hurwitzEvenFEPair a).symm.differentiableAt_Λ (Or.inl ?_) ?_).comp s
      (differentiableAt_id.div_const _)).div_const _
  · exact div_ne_zero_iff.mpr ⟨hs, two_ne_zero⟩
  · change s / 2 ≠ ↑(1 / 2 : ℝ) ∨ (if a = 0 then 1 else 0) = 0
    refine Or.imp (fun h ↦ ?_) (fun ha ↦ ?_) hs'
    · simpa [push_cast] using h ∘ (div_left_inj' two_ne_zero).mp
    · simpa
/-
**HurwitzZeta.differentiable_completedCosZeta** 是 Mathlib 中的一个引理，位于命名空间 `Hurwitz
Zeta`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma differentiable_completedCosZeta₀ (a : UnitAddCircle) :
    Differentiable ℂ (completedCosZeta₀ a) :=
  ((hurwitzEvenFEPair a).symm.differentiable_Λ₀.comp (differentiable_id.div_const _)).div_const _
/-
**HurwitzZeta.tendsto_div_two_punctured_nhds** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZ
eta`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma tendsto_div_two_punctured_nhds (a : ℂ) :
    Tendsto (fun s : ℂ ↦ s / 2) (𝓝[≠] a) (𝓝[≠] (a / 2)) :=
  le_of_eq ((Homeomorph.mulRight₀ _ (inv_ne_zero (two_ne_zero' ℂ))).map_punctured_nhds_eq a)

/-- The residue of `completedHurwitzZetaEven a s` at `s = 1` is equal to `1`. -/
/-
**HurwitzZeta.completedHurwitzZetaEven_residue_one** 是 Mathlib 中的一个引理，位于命名空间 `Hu
rwitzZeta`。
形式化陈述：completedHurwitzZetaEven_residue_one (a : UnitAddCircle) : Tendsto (fun s 
=> (s - 1) * completedHurwitzZetaEven a s) (𝓝[!=] 1) (𝓝 1)
参数：a : UnitAddCircle。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `WeakFEPair.Λ_residue_k`：Λ_residue_k : Tendsto (fun s : Complex => (s - P
.k) • P.Λ s) (𝓝[!=] P.k) (𝓝 (P.ε • P.g₀))
· 使用定理 `Filter.Tendsto.congr`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {l
₁ : Filter α} {l₂ : Filter β},   (∀ (x : α), f₁ x = f₂ x) → Filter.Tendsto f₁ l₁
 l₂ → Filt…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HurwitzZeta.completedHurwitzZetaEven.eq_1`：∀ (a : UnitAddCircle) (s : ℂ)
,   HurwitzZeta.completedHurwitzZetaEven a s = (HurwitzZeta.hurwitzEvenFEPair a)
.Λ (s / 2) / 2
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_div`：sub_div (a b c : K) : (a - b) / c = a / c - b / c
· 使用定理 `div_mul_eq_mul_div`：div_mul_eq_mul_div : a / b * c = a * c / b
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.ofReal_div`：ofReal_div (r s : Real) : ((r / s : Real) : Complex)
 = r / s
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `_private.Mathlib.NumberTheory.LSeries.HurwitzZetaEven.0.HurwitzZeta.tend
sto_div_two_punctured_nhds`：∀ (a : ℂ), Filter.Tendsto (fun s => s / 2) (nhdsWith
in a {a}ᶜ) (nhdsWithin (a / 2) {a / 2}ᶜ)

--- 原说明 ---
The residue of `completedHurwitzZetaEven a s` at `s = 1` is equal to `1`.
-/
lemma completedHurwitzZetaEven_residue_one (a : UnitAddCircle) :
    Tendsto (fun s ↦ (s - 1) * completedHurwitzZetaEven a s) (𝓝[≠] 1) (𝓝 1) := by
  have h1 : Tendsto (fun s : ℂ ↦ (s - ↑(1 / 2 : ℝ)) * _) (𝓝[≠] ↑(1 / 2 : ℝ))
    (𝓝 ((1 : ℂ) * (1 : ℂ))) := (hurwitzEvenFEPair a).Λ_residue_k
  simp only [push_cast, one_mul] at h1
  refine (h1.comp <| tendsto_div_two_punctured_nhds 1).congr (fun s ↦ ?_)
  rw [completedHurwitzZetaEven, Function.comp_apply, ← sub_div, div_mul_eq_mul_div, mul_div_assoc]

/-- The residue of `completedHurwitzZetaEven a s` at `s = 0` is equal to `-1` if `a = 0`, and `0`
otherwise. -/
/-
**HurwitzZeta.completedHurwitzZetaEven_residue_zero** 是 Mathlib 中的一个引理，位于命名空间 `H
urwitzZeta`。
形式化陈述：completedHurwitzZetaEven_residue_zero (a : UnitAddCircle) : Tendsto (fun s
 => s * completedHurwitzZetaEven a s) (𝓝[!=] 0) (𝓝 (if a = 0 then -1 else 0))
参数：a : UnitAddCircle。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WeakFEPair.Λ_residue_zero`：Λ_residue_zero : Tendsto (fun s => s • P.Λ s)
 (𝓝[!=] 0) (𝓝 (-P.f₀))
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Filter.Tendsto.congr`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {l
₁ : Filter α} {l₂ : Filter β},   (∀ (x : α), f₁ x = f₂ x) → Filter.Tendsto f₁ l₁
 l₂ → Filt…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `div_mul_eq_mul_div`：div_mul_eq_mul_div : a / b * c = a * c / b
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `_private.Mathlib.NumberTheory.LSeries.HurwitzZetaEven.0.HurwitzZeta.tend
sto_div_two_punctured_nhds`：∀ (a : ℂ), Filter.Tendsto (fun s => s / 2) (nhdsWith
in a {a}ᶜ) (nhdsWithin (a / 2) {a / 2}ᶜ)
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0

--- 原说明 ---
The residue of `completedHurwitzZetaEven a s` at `s = 0` is equal to `-1` if `a 
= 0`, and `0`
otherwise.
-/
lemma completedHurwitzZetaEven_residue_zero (a : UnitAddCircle) :
    Tendsto (fun s ↦ s * completedHurwitzZetaEven a s) (𝓝[≠] 0) (𝓝 (if a = 0 then -1 else 0)) := by
  have h1 : Tendsto (fun s : ℂ ↦ s * _) (𝓝[≠] 0)
    (𝓝 (-(if a = 0 then 1 else 0))) := (hurwitzEvenFEPair a).Λ_residue_zero
  have : -(if a = 0 then (1 : ℂ) else 0) = (if a = 0 then -1 else 0) := by { split_ifs <;> simp }
  simp only [this, push_cast] at h1
  refine (h1.comp <| zero_div (2 : ℂ) ▸ (tendsto_div_two_punctured_nhds 0)).congr (fun s ↦ ?_)
  simp [completedHurwitzZetaEven, div_mul_eq_mul_div, mul_div_assoc]
/-
**HurwitzZeta.completedCosZeta_residue_zero** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZe
ta`。
形式化陈述：completedCosZeta_residue_zero (a : UnitAddCircle) : Tendsto (fun s => s * 
completedCosZeta a s) (𝓝[!=] 0) (𝓝 (-1))
参数：a : UnitAddCircle。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WeakFEPair.Λ_residue_zero`：Λ_residue_zero : Tendsto (fun s => s • P.Λ s)
 (𝓝[!=] 0) (𝓝 (-P.f₀))
· 使用定理 `Filter.Tendsto.congr`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {l
₁ : Filter α} {l₂ : Filter β},   (∀ (x : α), f₁ x = f₂ x) → Filter.Tendsto f₁ l₁
 l₂ → Filt…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_mul_eq_mul_div`：div_mul_eq_mul_div : a / b * c = a * c / b
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `_private.Mathlib.NumberTheory.LSeries.HurwitzZetaEven.0.HurwitzZeta.tend
sto_div_two_punctured_nhds`：∀ (a : ℂ), Filter.Tendsto (fun s => s / 2) (nhdsWith
in a {a}ᶜ) (nhdsWithin (a / 2) {a / 2}ᶜ)
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
-/
lemma completedCosZeta_residue_zero (a : UnitAddCircle) :
    Tendsto (fun s ↦ s * completedCosZeta a s) (𝓝[≠] 0) (𝓝 (-1)) := by
  have h1 : Tendsto (fun s : ℂ ↦ s * _) (𝓝[≠] 0)
    (𝓝 (-1)) := (hurwitzEvenFEPair a).symm.Λ_residue_zero
  refine (h1.comp <| zero_div (2 : ℂ) ▸ (tendsto_div_two_punctured_nhds 0)).congr (fun s ↦ ?_)
  simp [completedCosZeta, div_mul_eq_mul_div, mul_div_assoc]

end FEPair

/-!
## Relation to the Dirichlet series for `1 < re s`
-/

/-- Formula for `completedCosZeta` as a Dirichlet series in the convergence range
(first version, with sum over `ℤ`). -/
/-
**HurwitzZeta.hasSum_int_completedCosZeta** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta
`。
形式化陈述：hasSum_int_completedCosZeta (a : Real) {s : Complex} (hs : 1 < re s) : Has
Sum (fun n : Int => GammaReal s * cexp (2 * π * I * a * n) / (↑|n| : Complex) ^ 
s / 2) (completedCosZeta a s)
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
· 使用引理 `HurwitzZeta.hasSum_int_cosKernel₀`：hasSum_int_cosKernel₀ (a : Real) {t :
 Real} (ht : 0 < t) : HasSum (fun n : Int => if n = 0 then 0 else cexp (2 * π * 
I * a * n) * rexp (-π *…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Complex.ofReal_exp`：ofReal_exp (x : Real) : (Real.exp x : Complex) = exp
 x
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `Complex.ofReal_pow`：ofReal_pow (r : Real) (n : Nat) : ((r ^ n : Real) : 
Complex) = (r : Complex) ^ n
· 使用定理 `div_mul_eq_mul_div`：div_mul_eq_mul_div : a / b * c = a * c / b
· 使用定理 `mellin_div_const`：mellin_div_const (f : Real -> Complex) (s a : Complex)
 : mellin (fun t => f t / a) s = mellin f s / a
· 使用定理 `HurwitzZeta.completedCosZeta.eq_1`：∀ (a : UnitAddCircle) (s : ℂ), Hurwit
zZeta.completedCosZeta a s = (HurwitzZeta.hurwitzEvenFEPair a).symm.Λ (s / 2) / 
2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `WeakFEPair.hasMellin`：hasMellin [CompleteSpace E] {s : Complex} (hs : P.
k < s.re) : HasMellin (P.f · - P.f₀) s (P.Λ s)
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用引理 `Complex.div_ofNat_re`：div_ofNat_re (z : Complex) (n : Nat) [n.AtLeastTwo
] : (z / ofNat(n)).re = z.re / ofNat(n)
（共 79 条，此处仅展示前 30 条）

--- 原说明 ---
Formula for `completedCosZeta` as a Dirichlet series in the convergence range
(first version, with sum over `ℤ`).
-/
lemma hasSum_int_completedCosZeta (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℤ ↦ Gammaℝ s * cexp (2 * π * I * a * n) / (↑|n| : ℂ) ^ s / 2)
    (completedCosZeta a s) := by
  let c (n : ℤ) : ℂ := cexp (2 * π * I * a * n) / 2
  have hF t (ht : 0 < t) : HasSum (fun n : ℤ ↦ if n = 0 then 0 else c n * rexp (-π * n ^ 2 * t))
      ((cosKernel a t - 1) / 2) := by
    refine ((hasSum_int_cosKernel₀ a ht).div_const 2).congr_fun fun n ↦ ?_
    split_ifs <;> simp [c, div_mul_eq_mul_div]
  simp only [← Int.cast_eq_zero (α := ℝ)] at hF
  rw [show completedCosZeta a s = mellin (fun t ↦ (cosKernel a t - 1 : ℂ) / 2) (s / 2) by
    rw [mellin_div_const, completedCosZeta]
    congr 1
    refine ((hurwitzEvenFEPair a).symm.hasMellin (?_ : 1 / 2 < (s / 2).re)).2.symm
    rwa [div_ofNat_re, div_lt_div_iff_of_pos_right two_pos]]
  refine (hasSum_mellin_pi_mul_sq (zero_lt_one.trans hs) hF ?_).congr_fun fun n ↦ ?_
  · apply (((summable_one_div_int_add_rpow 0 s.re).mpr hs).div_const 2).of_norm_bounded
    intro i
    simp only [c, (by { push_cast; ring } : 2 * π * I * a * i = ↑(2 * π * a * i) * I), norm_div,
      RCLike.norm_ofNat, Complex.norm_exp_ofReal_mul_I, add_zero, norm_one,
      norm_of_nonneg (by positivity : 0 ≤ |(i : ℝ)| ^ s.re), div_right_comm, le_rfl]
  · simp [c, ← Int.cast_abs, div_right_comm, mul_div_assoc]

/-- Formula for `completedCosZeta` as a Dirichlet series in the convergence range
(second version, with sum over `ℕ`). -/
/-
**HurwitzZeta.hasSum_nat_completedCosZeta** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta
`。
形式化陈述：hasSum_nat_completedCosZeta (a : Real) {s : Complex} (hs : 1 < re s) : Has
Sum (fun n : Nat => if n = 0 then 0 else GammaReal s * Real.cos (2 * π * a * n) 
/ (n : Complex) ^ s) (completedCosZeta a s)
参数：a : Real；hs : 1 < re s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `Complex.zero_cpow`：zero_cpow {x : Complex} (h : x != 0) : (0 : Complex) 
^ x = 0
· 使用引理 `Complex.ne_zero_of_one_lt_re`：ne_zero_of_one_lt_re {s : Complex} (hs : 1
 < s.re) : s != 0
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
· 使用引理 `HurwitzZeta.hasSum_int_completedCosZeta`：hasSum_int_completedCosZeta (a 
: Real) {s : Complex} (hs : 1 < re s) : HasSum (fun n : Int => GammaReal s * cex
p (2 * π * I * a * n) / (↑|n|…
· 使用定理 `HasSum.congr_fun`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid 
α] [inst_1 : TopologicalSpace α] {f g : β → α} {a : α}   {L : SummationFilter β}
, HasS…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Complex.ofReal_cos`：ofReal_cos (x : Real) : (Real.cos x : Complex) = cos
 x
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
（共 57 条，此处仅展示前 30 条）

--- 原说明 ---
Formula for `completedCosZeta` as a Dirichlet series in the convergence range
(second version, with sum over `ℕ`).
-/
lemma hasSum_nat_completedCosZeta (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℕ ↦ if n = 0 then 0 else Gammaℝ s * Real.cos (2 * π * a * n) / (n : ℂ) ^ s)
    (completedCosZeta a s) := by
  have aux : ((|0| : ℤ) : ℂ) ^ s = 0 := by
    rw [abs_zero, Int.cast_zero, zero_cpow (ne_zero_of_one_lt_re hs)]
  have hint := (hasSum_int_completedCosZeta a hs).nat_add_neg
  rw [aux, div_zero, zero_div, add_zero] at hint
  refine hint.congr_fun fun n ↦ ?_
  split_ifs with h
  · simp only [h, Nat.cast_zero, aux, div_zero, zero_div, neg_zero, zero_add]
  · simp only [ofReal_cos, ofReal_mul, ofReal_ofNat, ofReal_natCast, Complex.cos,
      show 2 * π * a * n * I = 2 * π * I * a * n by ring, neg_mul, mul_div_assoc,
      div_right_comm _ (2 : ℂ), Int.cast_natCast, Nat.abs_cast, Int.cast_neg, mul_neg, abs_neg, ←
      mul_add, ← add_div]

/-- Formula for `completedHurwitzZetaEven` as a Dirichlet series in the convergence range. -/
/-
**HurwitzZeta.hasSum_int_completedHurwitzZetaEven** 是 Mathlib 中的一个引理，位于命名空间 `Hur
witzZeta`。
形式化陈述：hasSum_int_completedHurwitzZetaEven (a : Real) {s : Complex} (hs : 1 < re 
s) : HasSum (fun n : Int => GammaReal s / (↑|n + a| : Complex) ^ s / 2) (complet
edHurwitzZetaEven a s)
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
· 使用引理 `HurwitzZeta.hasSum_int_evenKernel₀`：hasSum_int_evenKernel₀ (a : Real) {t
 : Real} (ht : 0 < t) : HasSum (fun n : Int => if n + a = 0 then 0 else rexp (-π
 * (n + a) ^ 2 * t)) (ev…
· 使用定理 `Complex.ofReal_sub`：ofReal_sub (r s : Real) : ((r - s : Real) : Complex)
 = r - s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.ofReal_zero`：ofReal_zero : ((0 : Real) : Complex) = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_one_div`：mul_one_div (x y : G) : x * (1 / y) = x / y
· 使用定理 `mellin_div_const`：mellin_div_const (f : Real -> Complex) (s a : Complex)
 : mellin (fun t => f t / a) s = mellin f s / a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `WeakFEPair.hasMellin`：hasMellin [CompleteSpace E] {s : Complex} (hs : P.
k < s.re) : HasMellin (P.f · - P.f₀) s (P.Λ s)
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用引理 `Complex.div_ofNat_re`：div_ofNat_re (z : Complex) (n : Nat) [n.AtLeastTwo
] : (z / ofNat(n)).re = z.re / ofNat(n)
（共 45 条，此处仅展示前 30 条）

--- 原说明 ---
Formula for `completedHurwitzZetaEven` as a Dirichlet series in the convergence 
range.
-/
lemma hasSum_int_completedHurwitzZetaEven (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℤ ↦ Gammaℝ s / (↑|n + a| : ℂ) ^ s / 2) (completedHurwitzZetaEven a s) := by
  have hF (t : ℝ) (ht : 0 < t) : HasSum (fun n : ℤ ↦ if n + a = 0 then 0
      else (1 / 2 : ℂ) * rexp (-π * (n + a) ^ 2 * t))
      ((evenKernel a t - (if (a : UnitAddCircle) = 0 then 1 else 0 : ℝ)) / 2) := by
    refine (ofReal_sub .. ▸ (hasSum_ofReal.mpr (hasSum_int_evenKernel₀ a ht)).div_const
      2).congr_fun fun n ↦ ?_
    split_ifs
    · rw [ofReal_zero, zero_div]
    · rw [mul_comm, mul_one_div]
  rw [show completedHurwitzZetaEven a s = mellin (fun t ↦ ((evenKernel (↑a) t : ℂ) -
        ↑(if (a : UnitAddCircle) = 0 then 1 else 0 : ℝ)) / 2) (s / 2) by
    simp_rw [mellin_div_const, apply_ite ofReal, ofReal_one, ofReal_zero]
    refine congr_arg (· / 2) ((hurwitzEvenFEPair a).hasMellin (?_ : 1 / 2 < (s / 2).re)).2.symm
    rwa [div_ofNat_re, div_lt_div_iff_of_pos_right two_pos]]
  refine (hasSum_mellin_pi_mul_sq (zero_lt_one.trans hs) hF ?_).congr_fun fun n ↦ ?_
  · simp_rw [← mul_one_div ‖_‖]
    apply Summable.mul_left
    rwa [summable_one_div_int_add_rpow]
  · rw [mul_one_div, div_right_comm]

/-!
## The un-completed even Hurwitz zeta
-/

/-- Technical lemma which will give us differentiability of Hurwitz zeta at `s = 0`. -/
/-
**HurwitzZeta.differentiableAt_update_of_residue** 是 Mathlib 中的一个引理，位于命名空间 `Hurw
itzZeta`。
形式化陈述：differentiableAt_update_of_residue {Λ : Complex -> Complex} (hf : forall (
s : Complex) (_ : s != 0) (_ : s != 1), DifferentiableAt Complex Λ s) {L : Compl
ex} (h_lim : Tendsto (fun s => s * Λ s) (𝓝[!=] 0) (𝓝 L)) (s : Complex) (hs' : s 
!= 1) : DifferentiableAt Complex (Function.update (fun s => Λ s / GammaReal s) 0
 (L / 2)) s
参数：hf : forall (s : Complex) (_ : s != 0) (_ : s != 1), DifferentiableAt Complex
 Λ s；h_lim : Tendsto (fun s => s * Λ s) (𝓝[!=] 0) (𝓝 L)；s : Complex；hs' : s != 1
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.mul`：DifferentiableAt.mul (ha : DifferentiableAt 𝕜 a x)
 (hb : DifferentiableAt 𝕜 b x) : DifferentiableAt 𝕜 (a * b) x
· 使用定理 `Differentiable.differentiableAt`：Differentiable.differentiableAt (h : Di
fferentiable 𝕜 f) : DifferentiableAt 𝕜 f x
· 使用定理 `Complex.differentiable_Gammaℝ_inv`：Differentiable ℂ fun s => s.Gammaℝ⁻¹
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Pi.div_apply`：div_apply (f g : forall i, G i) (i : ι) : (f / g) i = f i 
/ g i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_div`：div_div : a / b / c = a / (b * c)
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
· 使用定理 `Filter.Tendsto.div`：Filter.Tendsto.div {l : Filter α} {a b : G₀} (hf : T
endsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) (hy : b != 0) : Tendsto (f / g) l (𝓝 
(a / b))
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
· 使用定理 `Complex.Gammaℝ_residue_zero`：Filter.Tendsto (fun s => s * s.Gammaℝ) (nhd
sWithin 0 {0}ᶜ) (nhds 2)
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `ne_or_eq`：ne_or_eq {α : Sort*} (x y : α) : x != y ∨ x = y
· 使用定理 `DifferentiableAt.congr_of_eventuallyEq`：DifferentiableAt.congr_of_eventu
allyEq (h : DifferentiableAt 𝕜 f x) (hL : f₁ =ᶠ[𝓝 x] f) : DifferentiableAt 𝕜 f₁ 
x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `isOpen_compl_singleton`：isOpen_compl_singleton [T1Space X] {x : X} : IsO
pen ({x}ᶜ : Set X)
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
（共 64 条，此处仅展示前 30 条）

--- 原说明 ---
Technical lemma which will give us differentiability of Hurwitz zeta at `s = 0`.
-/
lemma differentiableAt_update_of_residue
    {Λ : ℂ → ℂ} (hf : ∀ (s : ℂ) (_ : s ≠ 0) (_ : s ≠ 1), DifferentiableAt ℂ Λ s)
    {L : ℂ} (h_lim : Tendsto (fun s ↦ s * Λ s) (𝓝[≠] 0) (𝓝 L)) (s : ℂ) (hs' : s ≠ 1) :
    DifferentiableAt ℂ (Function.update (fun s ↦ Λ s / Gammaℝ s) 0 (L / 2)) s := by
  have claim (t) (ht : t ≠ 0) (ht' : t ≠ 1) : DifferentiableAt ℂ (fun u : ℂ ↦ Λ u / Gammaℝ u) t :=
    (hf t ht ht').mul differentiable_Gammaℝ_inv.differentiableAt
  have claim2 : Tendsto (fun s : ℂ ↦ Λ s / Gammaℝ s) (𝓝[≠] 0) (𝓝 <| L / 2) := by
    refine Tendsto.congr' ?_ (h_lim.div Gammaℝ_residue_zero two_ne_zero)
    filter_upwards [self_mem_nhdsWithin] with s (hs : s ≠ 0)
    rw [Pi.div_apply, ← div_div, mul_div_cancel_left₀ _ hs]
  rcases ne_or_eq s 0 with hs | rfl
  · -- Easy case : `s ≠ 0`
    refine (claim s hs hs').congr_of_eventuallyEq ?_
    filter_upwards [isOpen_compl_singleton.mem_nhds hs] with x hx
    simp [Function.update_of_ne hx]
  · -- Hard case : `s = 0`
    simp_rw [← claim2.limUnder_eq]
    have S_nhds : {(1 : ℂ)}ᶜ ∈ 𝓝 (0 : ℂ) := isOpen_compl_singleton.mem_nhds hs'
    refine ((Complex.differentiableOn_update_limUnder_of_isLittleO S_nhds
      (fun t ht ↦ (claim t ht.2 ht.1).differentiableWithinAt) ?_) 0 hs').differentiableAt S_nhds
    simp only [Gammaℝ, zero_div, div_zero, Complex.Gamma_zero, mul_zero, sub_zero]
    -- Remains to show completed zeta is `o (s ^ (-1))` near 0.
    refine (isBigO_const_of_tendsto claim2 <| one_ne_zero' ℂ).trans_isLittleO ?_
    rw [isLittleO_iff_tendsto']
    · exact Tendsto.congr (fun x ↦ by rw [← one_div, one_div_one_div]) nhdsWithin_le_nhds
    · exact eventually_of_mem self_mem_nhdsWithin fun x hx hx' ↦ (hx <| inv_eq_zero.mp hx').elim

/-- The even part of the Hurwitz zeta function, i.e. the meromorphic function of `s` which agrees
with `1 / 2 * ∑' (n : ℤ), 1 / |n + a| ^ s` for `1 < re s` -/
/-
**HurwitzZeta.hurwitzZetaEven** 是 Mathlib 中的一个定义，位于命名空间 `HurwitzZeta`。
形式化陈述：hurwitzZetaEven (a : UnitAddCircle)
参数：a : UnitAddCircle。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The even part of the Hurwitz zeta function, i.e. the meromorphic function of `s`
 which agrees
with `1 / 2 * ∑' (n : ℤ), 1 / |n + a| ^ s` for `1 < re s`
-/
noncomputable def hurwitzZetaEven (a : UnitAddCircle) :=
  Function.update (fun s ↦ completedHurwitzZetaEven a s / Gammaℝ s)
  0 (if a = 0 then -1 / 2 else 0)
/-
**HurwitzZeta.hurwitzZetaEven_def_of_ne_or_ne** 是 Mathlib 中的一个引理，位于命名空间 `Hurwitz
Zeta`。
形式化陈述：hurwitzZetaEven_def_of_ne_or_ne {a : UnitAddCircle} {s : Complex} (h : a !
= 0 ∨ s != 0) : hurwitzZetaEven a s = completedHurwitzZetaEven a s / GammaReal s
参数：h : a != 0 ∨ s != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HurwitzZeta.hurwitzZetaEven.eq_1`：∀ (a : UnitAddCircle),   HurwitzZeta.h
urwitzZetaEven a =     Function.update (fun s => HurwitzZeta.completedHurwitzZet
aEven a s / s.Gammaℝ) …
· 使用定理 `ne_or_eq`：ne_or_eq {α : Sort*} (x y : α) : x != y ∨ x = y
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `Complex.cpow_zero`：cpow_zero (x : Complex) : x ^ (0 : Complex) = 1
· 使用定理 `Complex.Gamma_zero`：Gamma_zero : Gamma 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma hurwitzZetaEven_def_of_ne_or_ne {a : UnitAddCircle} {s : ℂ} (h : a ≠ 0 ∨ s ≠ 0) :
    hurwitzZetaEven a s = completedHurwitzZetaEven a s / Gammaℝ s := by
  rw [hurwitzZetaEven]
  rcases ne_or_eq s 0 with h' | rfl
  · rw [Function.update_of_ne h']
  · simpa [Gammaℝ] using h
/-
**HurwitzZeta.hurwitzZetaEven_apply_zero** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`
。
形式化陈述：hurwitzZetaEven_apply_zero (a : UnitAddCircle) : hurwitzZetaEven a 0 = if 
a = 0 then -1 / 2 else 0
参数：a : UnitAddCircle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
-/
lemma hurwitzZetaEven_apply_zero (a : UnitAddCircle) :
    hurwitzZetaEven a 0 = if a = 0 then -1 / 2 else 0 :=
  Function.update_self ..
/-
**HurwitzZeta.hurwitzZetaEven_neg** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：hurwitzZetaEven_neg (a : UnitAddCircle) (s : Complex) : hurwitzZetaEven (-
a) s = hurwitzZetaEven a s
参数：a : UnitAddCircle；s : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Function.update_congr`：update_congr {β : Sort*} {f₁ f₂ : α -> β} (hf : f
₁ = f₂) {a'₁ a'₂ : α} (ha' : a'₁ = a'₂) {v₁ v₂ : β} (hv : v₁ = v₂) {a₁ a₂ : α} (
ha : a₁ = a…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `HurwitzZeta.completedHurwitzZetaEven_neg`：completedHurwitzZetaEven_neg (
a : UnitAddCircle) (s : Complex) : completedHurwitzZetaEven (-a) s = completedHu
rwitzZetaEven a s
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma hurwitzZetaEven_neg (a : UnitAddCircle) (s : ℂ) :
    hurwitzZetaEven (-a) s = hurwitzZetaEven a s := by
  simp [hurwitzZetaEven]

/-- The trivial zeroes of the even Hurwitz zeta function. -/
/-
**HurwitzZeta.hurwitzZetaEven_neg_two_mul_nat_add_one** 是 Mathlib 中的一个定理，位于命名空间 
`HurwitzZeta`。
形式化陈述：hurwitzZetaEven_neg_two_mul_nat_add_one (a : UnitAddCircle) (n : Nat) : hu
rwitzZetaEven a (-2 * (n + 1)) = 0
参数：a : UnitAddCircle；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_ne_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a ≠
 0 ↔ a ≠ 0
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.cast_add_one_ne_zero`：cast_add_one_ne_zero (n : Nat) : (n + 1 : R) !
= 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HurwitzZeta.hurwitzZetaEven.eq_1`：∀ (a : UnitAddCircle),   HurwitzZeta.h
urwitzZetaEven a =     Function.update (fun s => HurwitzZeta.completedHurwitzZet
aEven a s / s.Gammaℝ) …
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `Complex.Gammaℝ_eq_zero_iff`：∀ {s : ℂ}, s.Gammaℝ = 0 ↔ ∃ n, s = -(2 * ↑n)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0

--- 原说明 ---
The trivial zeroes of the even Hurwitz zeta function.
-/
theorem hurwitzZetaEven_neg_two_mul_nat_add_one (a : UnitAddCircle) (n : ℕ) :
    hurwitzZetaEven a (-2 * (n + 1)) = 0 := by
  have : (-2 : ℂ) * (n + 1) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr two_ne_zero) (Nat.cast_add_one_ne_zero n)
  rw [hurwitzZetaEven, Function.update_of_ne this, Gammaℝ_eq_zero_iff.mpr ⟨n + 1, by simp⟩,
    div_zero]

/-- The Hurwitz zeta function is differentiable everywhere except at `s = 1`. This is true
even in the delicate case `a = 0` and `s = 0` (where the completed zeta has a pole, but this is
cancelled out by the Gamma factor). -/
/-
**HurwitzZeta.differentiableAt_hurwitzZetaEven** 是 Mathlib 中的一个引理，位于命名空间 `Hurwit
zZeta`。
形式化陈述：differentiableAt_hurwitzZetaEven (a : UnitAddCircle) {s : Complex} (hs' : 
s != 1) : DifferentiableAt Complex (hurwitzZetaEven a) s
参数：a : UnitAddCircle；hs' : s != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `HurwitzZeta.differentiableAt_update_of_residue`：differentiableAt_update_
of_residue {Λ : Complex -> Complex} (hf : forall (s : Complex) (_ : s != 0) (_ :
 s != 1), DifferentiableAt Complex Λ…
· 使用引理 `HurwitzZeta.differentiableAt_completedHurwitzZetaEven`：differentiableAt_
completedHurwitzZetaEven (a : UnitAddCircle) {s : Complex} (hs : s != 0 ∨ a != 0
) (hs' : s != 1) : DifferentiableAt Complex…
· 使用引理 `HurwitzZeta.completedHurwitzZetaEven_residue_zero`：completedHurwitzZetaE
ven_residue_zero (a : UnitAddCircle) : Tendsto (fun s => s * completedHurwitzZet
aEven a s) (𝓝[!=] 0) (𝓝 (if a = 0 then …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹

--- 原说明 ---
The Hurwitz zeta function is differentiable everywhere except at `s = 1`. This i
s true
even in the delicate case `a = 0` and `s = 0` (where the completed zeta has a po
le, but this is
cancelled out by the Gamma factor).
-/
lemma differentiableAt_hurwitzZetaEven (a : UnitAddCircle) {s : ℂ} (hs' : s ≠ 1) :
    DifferentiableAt ℂ (hurwitzZetaEven a) s := by
  have := differentiableAt_update_of_residue
    (fun t ht ht' ↦ differentiableAt_completedHurwitzZetaEven a (Or.inl ht) ht')
    (completedHurwitzZetaEven_residue_zero a) s hs'
  simp_rw [div_eq_mul_inv, ite_mul, zero_mul, ← div_eq_mul_inv] at this
  exact this
/-
**HurwitzZeta.hurwitzZetaEven_residue_one** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta
`。
形式化陈述：hurwitzZetaEven_residue_one (a : UnitAddCircle) : Tendsto (fun s => (s - 1
) * hurwitzZetaEven a s) (𝓝[!=] 1) (𝓝 1)
参数：a : UnitAddCircle。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.Gammaℝ_one`：Complex.Gammaℝ 1 = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Filter.Tendsto.mul`：Filter.Tendsto.mul {α : Type*} {f g : α -> M} {x : F
ilter α} {a b : M} (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) : Tendsto (
fun x =>…
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
· 使用引理 `HurwitzZeta.completedHurwitzZetaEven_residue_one`：completedHurwitzZetaEv
en_residue_one (a : UnitAddCircle) : Tendsto (fun s => (s - 1) * completedHurwit
zZetaEven a s) (𝓝[!=] 1) (𝓝 1)
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `Differentiable.continuous`：Differentiable.continuous (h : Differentiable
 𝕜 f) : Continuous f
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `Complex.differentiable_Gammaℝ_inv`：Differentiable ℂ fun s => s.Gammaℝ⁻¹
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `eventually_ne_nhdsWithin`：eventually_ne_nhdsWithin [T1Space X] {a b : X}
 {s : Set X} (h : a != b) : forallᶠ x in 𝓝[s] a, x != b
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
（共 34 条，此处仅展示前 30 条）
-/
lemma hurwitzZetaEven_residue_one (a : UnitAddCircle) :
    Tendsto (fun s ↦ (s - 1) * hurwitzZetaEven a s) (𝓝[≠] 1) (𝓝 1) := by
  have : Tendsto (fun s ↦ (s - 1) * completedHurwitzZetaEven a s / Gammaℝ s) (𝓝[≠] 1) (𝓝 1) := by
    simpa only [Gammaℝ_one, inv_one, mul_one] using! (completedHurwitzZetaEven_residue_one a).mul
      <| (differentiable_Gammaℝ_inv.continuous.tendsto _).mono_left nhdsWithin_le_nhds
  refine this.congr' ?_
  filter_upwards [eventually_ne_nhdsWithin one_ne_zero] with s hs
  simp [hurwitzZetaEven_def_of_ne_or_ne (Or.inr hs), mul_div_assoc]
/-
**HurwitzZeta.differentiableAt_hurwitzZetaEven_sub_one_div** 是 Mathlib 中的一个引理，位于
命名空间 `HurwitzZeta`。
形式化陈述：differentiableAt_hurwitzZetaEven_sub_one_div (a : UnitAddCircle) : Differe
ntiableAt Complex (fun s => hurwitzZetaEven a s - 1 / (s - 1) / GammaReal s) 1
参数：a : UnitAddCircle。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `DifferentiableAt.mul`：DifferentiableAt.mul (ha : DifferentiableAt 𝕜 a x)
 (hb : DifferentiableAt 𝕜 b x) : DifferentiableAt 𝕜 (a * b) x
· 使用引理 `HurwitzZeta.completedHurwitzZetaEven_eq`：completedHurwitzZetaEven_eq (a 
: UnitAddCircle) (s : Complex) : completedHurwitzZetaEven a s = completedHurwitz
ZetaEven₀ a s - (if a = 0 the…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b - c = a - (b + c)
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用引理 `div_neg`：div_neg (a : R) : a / -b = -(a / b)
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `DifferentiableAt.sub`：DifferentiableAt.sub (hf : DifferentiableAt 𝕜 f x)
 (hg : DifferentiableAt 𝕜 g x) : DifferentiableAt 𝕜 (f - g) x
· 使用引理 `HurwitzZeta.differentiable_completedHurwitzZetaEven₀`：differentiable_com
pletedHurwitzZetaEven₀ (a : UnitAddCircle) : Differentiable Complex (completedHu
rwitzZetaEven₀ a)
· 使用定理 `DifferentiableAt.div`：DifferentiableAt.div (hc : DifferentiableAt 𝕜 c x)
 (hd : DifferentiableAt 𝕜 d x) (hx : d x != 0) : DifferentiableAt 𝕜 (c / d) x
· 使用定理 `differentiableAt_const`：differentiableAt_const (c : F) : DifferentiableA
t 𝕜 (fun _ => c) x
· 使用定理 `differentiableAt_id`：differentiableAt_id : DifferentiableAt 𝕜 id x
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Differentiable.differentiableAt`：Differentiable.differentiableAt (h : Di
fferentiable 𝕜 f) : DifferentiableAt 𝕜 f x
· 使用定理 `Complex.differentiable_Gammaℝ_inv`：Differentiable ℂ fun s => s.Gammaℝ⁻¹
· 使用定理 `DifferentiableAt.congr_of_eventuallyEq`：DifferentiableAt.congr_of_eventu
allyEq (h : DifferentiableAt 𝕜 f x) (hL : f₁ =ᶠ[𝓝 x] f) : DifferentiableAt 𝕜 f₁ 
x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `eventually_ne_nhds`：eventually_ne_nhds [T1Space X] {a b : X} (h : a != b
) : forallᶠ x in 𝓝 a, x != b
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
（共 32 条，此处仅展示前 30 条）
-/
lemma differentiableAt_hurwitzZetaEven_sub_one_div (a : UnitAddCircle) :
    DifferentiableAt ℂ (fun s ↦ hurwitzZetaEven a s - 1 / (s - 1) / Gammaℝ s) 1 := by
  suffices DifferentiableAt ℂ
      (fun s ↦ completedHurwitzZetaEven a s / Gammaℝ s - 1 / (s - 1) / Gammaℝ s) 1 by
    apply this.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds one_ne_zero] with x hx
    rw [hurwitzZetaEven, Function.update_of_ne hx]
  simp_rw [← sub_div, div_eq_mul_inv _ (Gammaℝ _)]
  refine DifferentiableAt.mul ?_ differentiable_Gammaℝ_inv.differentiableAt
  simp_rw [completedHurwitzZetaEven_eq, sub_sub, add_assoc]
  conv => enter [2, s, 2]; rw [← neg_sub, div_neg, neg_add_cancel, add_zero]
  exact (differentiable_completedHurwitzZetaEven₀ a _).sub
    <| (differentiableAt_const _).div differentiableAt_id one_ne_zero

/-- Expression for `hurwitzZetaEven a 1` as a limit. (Mathematically `hurwitzZetaEven a 1` is
undefined, but our construction assigns some value to it; this lemma is mostly of interest for
determining what that value is). -/
/-
**HurwitzZeta.tendsto_hurwitzZetaEven_sub_one_div_nhds_one** 是 Mathlib 中的一个引理，位于
命名空间 `HurwitzZeta`。
形式化陈述：tendsto_hurwitzZetaEven_sub_one_div_nhds_one (a : UnitAddCircle) : Tendsto
 (fun s => hurwitzZetaEven a s - 1 / (s - 1) / GammaReal s) (𝓝 1) (𝓝 (hurwitzZet
aEven a 1))
参数：a : UnitAddCircle。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `Complex.Gammaℝ_one`：Complex.Gammaℝ 1 = 1
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `DifferentiableAt.continuousAt`：DifferentiableAt.continuousAt (h : Differ
entiableAt 𝕜 f x) : ContinuousAt f x
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
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用引理 `HurwitzZeta.differentiableAt_hurwitzZetaEven_sub_one_div`：differentiable
At_hurwitzZetaEven_sub_one_div (a : UnitAddCircle) : DifferentiableAt Complex (f
un s => hurwitzZetaEven a s - 1 / (s - 1) / Ga…

--- 原说明 ---
Expression for `hurwitzZetaEven a 1` as a limit. (Mathematically `hurwitzZetaEve
n a 1` is
undefined, but our construction assigns some value to it; this lemma is mostly o
f interest for
determining what that value is).
-/
lemma tendsto_hurwitzZetaEven_sub_one_div_nhds_one (a : UnitAddCircle) :
    Tendsto (fun s ↦ hurwitzZetaEven a s - 1 / (s - 1) / Gammaℝ s) (𝓝 1)
    (𝓝 (hurwitzZetaEven a 1)) := by
  simpa using (differentiableAt_hurwitzZetaEven_sub_one_div a).continuousAt.tendsto
/-
**HurwitzZeta.differentiable_hurwitzZetaEven_sub_hurwitzZetaEven** 是 Mathlib 中的一
个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：differentiable_hurwitzZetaEven_sub_hurwitzZetaEven (a b : UnitAddCircle) :
 Differentiable Complex (fun s => hurwitzZetaEven a s - hurwitzZetaEven b s)
参数：a b : UnitAddCircle。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_or_eq`：ne_or_eq {α : Sort*} (x y : α) : x != y ∨ x = y
· 使用定理 `DifferentiableAt.sub`：DifferentiableAt.sub (hf : DifferentiableAt 𝕜 f x)
 (hg : DifferentiableAt 𝕜 g x) : DifferentiableAt 𝕜 (f - g) x
· 使用引理 `HurwitzZeta.differentiableAt_hurwitzZetaEven`：differentiableAt_hurwitzZe
taEven (a : UnitAddCircle) {s : Complex} (hs' : s != 1) : DifferentiableAt Compl
ex (hurwitzZetaEven a) s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `_private.Mathlib.NumberTheory.LSeries.HurwitzZetaEven.0.HurwitzZeta.diff
erentiable_hurwitzZetaEven_sub_hurwitzZetaEven._abel_1_1`：∀ (a b : UnitAddCircle
) (x : ℂ),   HurwitzZeta.hurwitzZetaEven a x - HurwitzZeta.hurwitzZetaEven b x =
     HurwitzZeta.hurwitzZetaEven a x -…
· 使用定理 `DifferentiableAt.fun_sub`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type u_…
· 使用引理 `HurwitzZeta.differentiableAt_hurwitzZetaEven_sub_one_div`：differentiable
At_hurwitzZetaEven_sub_one_div (a : UnitAddCircle) : DifferentiableAt Complex (f
un s => hurwitzZetaEven a s - 1 / (s - 1) / Ga…
-/
lemma differentiable_hurwitzZetaEven_sub_hurwitzZetaEven (a b : UnitAddCircle) :
    Differentiable ℂ (fun s ↦ hurwitzZetaEven a s - hurwitzZetaEven b s) := by
  intro z
  rcases ne_or_eq z 1 with hz | rfl
  · exact (differentiableAt_hurwitzZetaEven a hz).sub (differentiableAt_hurwitzZetaEven b hz)
  · convert!
    (differentiableAt_hurwitzZetaEven_sub_one_div a).fun_sub
      (differentiableAt_hurwitzZetaEven_sub_one_div b) using
    2 with s
    abel

/--
Formula for `hurwitzZetaEven` as a Dirichlet series in the convergence range, with sum over `ℤ`.
-/
/-
**HurwitzZeta.hasSum_int_hurwitzZetaEven** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`
。
形式化陈述：hasSum_int_hurwitzZetaEven (a : Real) {s : Complex} (hs : 1 < re s) : HasS
um (fun n : Int => 1 / (↑|n + a| : Complex) ^ s / 2) (hurwitzZetaEven a s)
参数：a : Real；hs : 1 < re s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HurwitzZeta.hurwitzZetaEven.eq_1`：∀ (a : UnitAddCircle),   HurwitzZeta.h
urwitzZetaEven a =     Function.update (fun s => HurwitzZeta.completedHurwitzZet
aEven a s / s.Gammaℝ) …
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用引理 `Complex.ne_zero_of_one_lt_re`：ne_zero_of_one_lt_re {s : Complex} (hs : 1
 < s.re) : s != 0
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
· 使用引理 `HurwitzZeta.hasSum_int_completedHurwitzZetaEven`：hasSum_int_completedHur
witzZetaEven (a : Real) {s : Complex} (hs : 1 < re s) : HasSum (fun n : Int => G
ammaReal s / (↑|n + a| : Complex) ^ s…
· 使用定理 `HasSum.congr_fun`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid 
α] [inst_1 : TopologicalSpace α] {f g : β → α} {a : α}   {L : SummationFilter β}
, HasS…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `div_right_comm`：div_right_comm : a / b / c = a / c / b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `Complex.Gammaℝ_ne_zero_of_re_pos`：∀ {s : ℂ}, 0 < s.re → s.Gammaℝ ≠ 0
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Formula for `hurwitzZetaEven` as a Dirichlet series in the convergence range, wi
th sum over `ℤ`.
-/
lemma hasSum_int_hurwitzZetaEven (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℤ ↦ 1 / (↑|n + a| : ℂ) ^ s / 2) (hurwitzZetaEven a s) := by
  rw [hurwitzZetaEven, Function.update_of_ne (ne_zero_of_one_lt_re hs)]
  have := (hasSum_int_completedHurwitzZetaEven a hs).div_const (Gammaℝ s)
  exact this.congr_fun fun n ↦ by simp only [div_right_comm _ _ (Gammaℝ _),
    div_self (Gammaℝ_ne_zero_of_re_pos (zero_lt_one.trans hs))]

/-- Formula for `hurwitzZetaEven` as a Dirichlet series in the convergence range, with sum over `ℕ`
(version with absolute values) -/
/-
**HurwitzZeta.hasSum_nat_hurwitzZetaEven** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`
。
形式化陈述：hasSum_nat_hurwitzZetaEven (a : Real) {s : Complex} (hs : 1 < re s) : HasS
um (fun n : Nat => (1 / (↑|n + a| : Complex) ^ s + 1 / (↑|n + 1 - a| : Complex) 
^ s) / 2) (hurwitzZetaEven a s)
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
· 使用引理 `HurwitzZeta.hasSum_int_hurwitzZetaEven`：hasSum_int_hurwitzZetaEven (a : 
Real) {s : Complex} (hs : 1 < re s) : HasSum (fun n : Int => 1 / (↑|n + a| : Com
plex) ^ s / 2) (hurwitzZetaE…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `abs_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a : 
α), |(-a)| = |a|
· 使用定理 `neg_sub'`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b : α), -
(a - b) = -a - -b
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Formula for `hurwitzZetaEven` as a Dirichlet series in the convergence range, wi
th sum over `ℕ`
(version with absolute values)
-/
lemma hasSum_nat_hurwitzZetaEven (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℕ ↦ (1 / (↑|n + a| : ℂ) ^ s + 1 / (↑|n + 1 - a| : ℂ) ^ s) / 2)
    (hurwitzZetaEven a s) := by
  refine (hasSum_int_hurwitzZetaEven a hs).nat_add_neg_add_one.congr_fun fun n ↦ ?_
  simp [← abs_neg (n + 1 - a), -neg_sub, neg_sub', add_div]

/-- Formula for `hurwitzZetaEven` as a Dirichlet series in the convergence range, with sum over `ℕ`
(version without absolute values, assuming `a ∈ Icc 0 1`) -/
/-
**HurwitzZeta.hasSum_nat_hurwitzZetaEven_of_mem_Icc** 是 Mathlib 中的一个引理，位于命名空间 `H
urwitzZeta`。
形式化陈述：hasSum_nat_hurwitzZetaEven_of_mem_Icc {a : Real} (ha : a in Icc 0 1) {s : 
Complex} (hs : 1 < re s) : HasSum (fun n : Nat => (1 / (n + a : Complex) ^ s + 1
 / (n + 1 - a : Complex) ^ s) / 2) (hurwitzZetaEven a s)
参数：ha : a in Icc 0 1；hs : 1 < re s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.congr_fun`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid 
α] [inst_1 : TopologicalSpace α] {f g : β → α} {a : α}   {L : SummationFilter β}
, HasS…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `HurwitzZeta.hasSum_nat_hurwitzZetaEven`：hasSum_nat_hurwitzZetaEven (a : 
Real) {s : Complex} (hs : 1 < re s) : HasSum (fun n : Nat => (1 / (↑|n + a| : Co
mplex) ^ s + 1 / (↑|n + 1 - …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
（共 51 条，此处仅展示前 30 条）

--- 原说明 ---
Formula for `hurwitzZetaEven` as a Dirichlet series in the convergence range, wi
th sum over `ℕ`
(version without absolute values, assuming `a ∈ Icc 0 1`)
-/
lemma hasSum_nat_hurwitzZetaEven_of_mem_Icc {a : ℝ} (ha : a ∈ Icc 0 1) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℕ ↦ (1 / (n + a : ℂ) ^ s + 1 / (n + 1 - a : ℂ) ^ s) / 2)
    (hurwitzZetaEven a s) := by
  refine (hasSum_nat_hurwitzZetaEven a hs).congr_fun fun n ↦ ?_
  congr 2 <;>
  rw [abs_of_nonneg (by linarith [ha.1, ha.2])] <;>
  simp

/-!
## The un-completed cosine zeta
-/

/-- The cosine zeta function, i.e. the meromorphic function of `s` which agrees
with `∑' (n : ℕ), cos (2 * π * a * n) / n ^ s` for `1 < re s`. -/
/-
**HurwitzZeta.cosZeta** 是 Mathlib 中的一个定义，位于命名空间 `HurwitzZeta`。
形式化陈述：cosZeta (a : UnitAddCircle)
参数：a : UnitAddCircle。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cosine zeta function, i.e. the meromorphic function of `s` which agrees
with `∑' (n : ℕ), cos (2 * π * a * n) / n ^ s` for `1 < re s`.
-/
noncomputable def cosZeta (a : UnitAddCircle) :=
  Function.update (fun s : ℂ ↦ completedCosZeta a s / Gammaℝ s) 0 (-1 / 2)
/-
**HurwitzZeta.cosZeta_apply_zero** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：cosZeta_apply_zero (a : UnitAddCircle) : cosZeta a 0 = -1 / 2
参数：a : UnitAddCircle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
-/
lemma cosZeta_apply_zero (a : UnitAddCircle) : cosZeta a 0 = -1 / 2 :=
  Function.update_self ..
/-
**HurwitzZeta.cosZeta_neg** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：cosZeta_neg (a : UnitAddCircle) (s : Complex) : cosZeta (-a) s = cosZeta a
 s
参数：a : UnitAddCircle；s : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Function.update_congr`：update_congr {β : Sort*} {f₁ f₂ : α -> β} (hf : f
₁ = f₂) {a'₁ a'₂ : α} (ha' : a'₁ = a'₂) {v₁ v₂ : β} (hv : v₁ = v₂) {a₁ a₂ : α} (
ha : a₁ = a…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `HurwitzZeta.completedCosZeta_neg`：completedCosZeta_neg (a : UnitAddCircl
e) (s : Complex) : completedCosZeta (-a) s = completedCosZeta a s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cosZeta_neg (a : UnitAddCircle) (s : ℂ) :
    cosZeta (-a) s = cosZeta a s := by
  simp [cosZeta]

/-- The trivial zeroes of the cosine zeta function. -/
/-
**HurwitzZeta.cosZeta_neg_two_mul_nat_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Hurwitz
Zeta`。
形式化陈述：cosZeta_neg_two_mul_nat_add_one (a : UnitAddCircle) (n : Nat) : cosZeta a 
(-2 * (n + 1)) = 0
参数：a : UnitAddCircle；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_ne_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a ≠
 0 ↔ a ≠ 0
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.cast_add_one_ne_zero`：cast_add_one_ne_zero (n : Nat) : (n + 1 : R) !
= 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HurwitzZeta.cosZeta.eq_1`：∀ (a : UnitAddCircle),   HurwitzZeta.cosZeta a
 = Function.update (fun s => HurwitzZeta.completedCosZeta a s / s.Gammaℝ) 0 (-1 
/ 2)
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `Complex.Gammaℝ_eq_zero_iff`：∀ {s : ℂ}, s.Gammaℝ = 0 ↔ ∃ n, s = -(2 * ↑n)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Nat.cast_add_one`：cast_add_one (n : Nat) : ((n + 1 : Nat) : R) = n + 1
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0

--- 原说明 ---
The trivial zeroes of the cosine zeta function.
-/
theorem cosZeta_neg_two_mul_nat_add_one (a : UnitAddCircle) (n : ℕ) :
    cosZeta a (-2 * (n + 1)) = 0 := by
  have : (-2 : ℂ) * (n + 1) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr two_ne_zero) (Nat.cast_add_one_ne_zero n)
  rw [cosZeta, Function.update_of_ne this,
    Gammaℝ_eq_zero_iff.mpr ⟨n + 1, by rw [neg_mul, Nat.cast_add_one]⟩, div_zero]

/-- The cosine zeta function is differentiable everywhere, except at `s = 1` if `a = 0`. -/
/-
**HurwitzZeta.differentiableAt_cosZeta** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：differentiableAt_cosZeta (a : UnitAddCircle) {s : Complex} (hs' : s != 1 ∨
 a != 0) : DifferentiableAt Complex (cosZeta a) s
参数：a : UnitAddCircle；hs' : s != 1 ∨ a != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_or_eq`：ne_or_eq {α : Sort*} (x y : α) : x != y ∨ x = y
· 使用引理 `HurwitzZeta.differentiableAt_update_of_residue`：differentiableAt_update_
of_residue {Λ : Complex -> Complex} (hf : forall (s : Complex) (_ : s != 0) (_ :
 s != 1), DifferentiableAt Complex Λ…
· 使用引理 `HurwitzZeta.differentiableAt_completedCosZeta`：differentiableAt_complete
dCosZeta (a : UnitAddCircle) {s : Complex} (hs : s != 0) (hs' : s != 1 ∨ a != 0)
 : DifferentiableAt Complex (comple…
· 使用引理 `HurwitzZeta.completedCosZeta_residue_zero`：completedCosZeta_residue_zero
 (a : UnitAddCircle) : Tendsto (fun s => s * completedCosZeta a s) (𝓝[!=] 0) (𝓝 
(-1))
· 使用定理 `DifferentiableAt.congr_of_eventuallyEq`：DifferentiableAt.congr_of_eventu
allyEq (h : DifferentiableAt 𝕜 f x) (hL : f₁ =ᶠ[𝓝 x] f) : DifferentiableAt 𝕜 f₁ 
x
· 使用定理 `DifferentiableAt.fun_mul`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {x : E} {𝔸 :…
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Differentiable.differentiableAt`：Differentiable.differentiableAt (h : Di
fferentiable 𝕜 f) : DifferentiableAt 𝕜 f x
· 使用定理 `Complex.differentiable_Gammaℝ_inv`：Differentiable ℂ fun s => s.Gammaℝ⁻¹
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `isOpen_compl_singleton`：isOpen_compl_singleton [T1Space X] {x : X} : IsO
pen ({x}ᶜ : Set X)
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HurwitzZeta.cosZeta.eq_1`：∀ (a : UnitAddCircle),   HurwitzZeta.cosZeta a
 = Function.update (fun s => HurwitzZeta.completedCosZeta a s / s.Gammaℝ) 0 (-1 
/ 2)
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The cosine zeta function is differentiable everywhere, except at `s = 1` if `a =
 0`.
-/
lemma differentiableAt_cosZeta (a : UnitAddCircle) {s : ℂ} (hs' : s ≠ 1 ∨ a ≠ 0) :
    DifferentiableAt ℂ (cosZeta a) s := by
  rcases ne_or_eq s 1 with hs' | rfl
  · exact differentiableAt_update_of_residue (fun _ ht ht' ↦
      differentiableAt_completedCosZeta a ht (Or.inl ht')) (completedCosZeta_residue_zero a) s hs'
  · apply ((differentiableAt_completedCosZeta a one_ne_zero hs').fun_mul
      (differentiable_Gammaℝ_inv.differentiableAt)).congr_of_eventuallyEq
    filter_upwards [isOpen_compl_singleton.mem_nhds one_ne_zero] with x hx
    rw [cosZeta, Function.update_of_ne hx, div_eq_mul_inv]

/-- If `a ≠ 0` then the cosine zeta function is entire. -/
/-
**HurwitzZeta.differentiable_cosZeta_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Hurwi
tzZeta`。
形式化陈述：differentiable_cosZeta_of_ne_zero {a : UnitAddCircle} (ha : a != 0) : Diff
erentiable Complex (cosZeta a)
参数：ha : a != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HurwitzZeta.differentiableAt_cosZeta`：differentiableAt_cosZeta (a : Unit
AddCircle) {s : Complex} (hs' : s != 1 ∨ a != 0) : DifferentiableAt Complex (cos
Zeta a) s

--- 原说明 ---
If `a ≠ 0` then the cosine zeta function is entire.
-/
lemma differentiable_cosZeta_of_ne_zero {a : UnitAddCircle} (ha : a ≠ 0) :
    Differentiable ℂ (cosZeta a) :=
  fun _ ↦ differentiableAt_cosZeta a (Or.inr ha)

/-- Formula for `cosZeta` as a Dirichlet series in the convergence range, with sum over `ℤ`. -/
/-
**HurwitzZeta.hasSum_int_cosZeta** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：hasSum_int_cosZeta (a : Real) {s : Complex} (hs : 1 < re s) : HasSum (fun 
n : Int => cexp (2 * π * I * a * n) / ↑|n| ^ s / 2) (cosZeta a s)
参数：a : Real；hs : 1 < re s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HurwitzZeta.cosZeta.eq_1`：∀ (a : UnitAddCircle),   HurwitzZeta.cosZeta a
 = Function.update (fun s => HurwitzZeta.completedCosZeta a s / s.Gammaℝ) 0 (-1 
/ 2)
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用引理 `Complex.ne_zero_of_one_lt_re`：ne_zero_of_one_lt_re {s : Complex} (hs : 1
 < s.re) : s != 0
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
· 使用引理 `HurwitzZeta.hasSum_int_completedCosZeta`：hasSum_int_completedCosZeta (a 
: Real) {s : Complex} (hs : 1 < re s) : HasSum (fun n : Int => GammaReal s * cex
p (2 * π * I * a * n) / (↑|n|…
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用定理 `div_right_comm`：div_right_comm : a / b / c = a / c / b
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
· 使用定理 `Complex.Gammaℝ_ne_zero_of_re_pos`：∀ {s : ℂ}, 0 < s.re → s.Gammaℝ ≠ 0
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α

--- 原说明 ---
Formula for `cosZeta` as a Dirichlet series in the convergence range, with sum o
ver `ℤ`.
-/
lemma hasSum_int_cosZeta (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℤ ↦ cexp (2 * π * I * a * n) / ↑|n| ^ s / 2) (cosZeta a s) := by
  rw [cosZeta, Function.update_of_ne (ne_zero_of_one_lt_re hs)]
  refine ((hasSum_int_completedCosZeta a hs).div_const (Gammaℝ s)).congr_fun fun n ↦ ?_
  rw [mul_div_assoc _ (cexp _), div_right_comm _ (2 : ℂ),
    mul_div_cancel_left₀ _ (Gammaℝ_ne_zero_of_re_pos (zero_lt_one.trans hs))]

/-- Formula for `cosZeta` as a Dirichlet series in the convergence range, with sum over `ℕ`. -/
/-
**HurwitzZeta.hasSum_nat_cosZeta** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：hasSum_nat_cosZeta (a : Real) {s : Complex} (hs : 1 < re s) : HasSum (fun 
n : Nat => Real.cos (2 * π * a * n) / (n : Complex) ^ s) (cosZeta a s)
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
· 使用引理 `HurwitzZeta.hasSum_int_cosZeta`：hasSum_int_cosZeta (a : Real) {s : Compl
ex} (hs : 1 < re s) : HasSum (fun n : Int => cexp (2 * π * I * a * n) / ↑|n| ^ s
 / 2) (cosZeta a s)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.ofReal_cos`：ofReal_cos (x : Real) : (Real.cos x : Complex) = cos
 x
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `HasSum.congr_fun`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid 
α] [inst_1 : TopologicalSpace α] {f g : β → α} {a : α}   {L : SummationFilter β}
, HasS…
· 使用定理 `div_right_comm`：div_right_comm : a / b / c = a / c / b
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
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
Formula for `cosZeta` as a Dirichlet series in the convergence range, with sum o
ver `ℕ`.
-/
lemma hasSum_nat_cosZeta (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℕ ↦ Real.cos (2 * π * a * n) / (n : ℂ) ^ s) (cosZeta a s) := by
  have := (hasSum_int_cosZeta a hs).nat_add_neg
  simp_rw [abs_neg, Int.cast_neg, Nat.abs_cast, Int.cast_natCast, mul_neg, abs_zero, Int.cast_zero,
    zero_cpow (ne_zero_of_one_lt_re hs), div_zero, zero_div, add_zero, ← add_div,
    div_right_comm _ _ (2 : ℂ)] at this
  simp_rw [push_cast, Complex.cos, neg_mul]
  exact this.congr_fun fun n ↦ by rw [show 2 * π * a * n * I = 2 * π * I * a * n by ring]

/-- Reformulation of `hasSum_nat_cosZeta` using `LSeriesHasSum`. -/
/-
**HurwitzZeta.LSeriesHasSum_cos** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：LSeriesHasSum_cos (a : Real) {s : Complex} (hs : 1 < re s) : LSeriesHasSum
 (Real.cos <| 2 * π * a * ·) s (cosZeta a s)
参数：a : Real；hs : 1 < re s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.congr_fun`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid 
α] [inst_1 : TopologicalSpace α] {f g : β → α} {a : α}   {L : SummationFilter β}
, HasS…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `HurwitzZeta.hasSum_nat_cosZeta`：hasSum_nat_cosZeta (a : Real) {s : Compl
ex} (hs : 1 < re s) : HasSum (fun n : Nat => Real.cos (2 * π * a * n) / (n : Com
plex) ^ s) (cosZeta …
· 使用引理 `LSeries.term_of_ne_zero'`：term_of_ne_zero' {s : Complex} (hs : s != 0) (
f : Nat -> Complex) (n : Nat) : term f s n = f n / n ^ s
· 使用引理 `Complex.ne_zero_of_one_lt_re`：ne_zero_of_one_lt_re {s : Complex} (hs : 1
 < s.re) : s != 0

--- 原说明 ---
Reformulation of `hasSum_nat_cosZeta` using `LSeriesHasSum`.
-/
lemma LSeriesHasSum_cos (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    LSeriesHasSum (Real.cos <| 2 * π * a * ·) s (cosZeta a s) :=
  (hasSum_nat_cosZeta a hs).congr_fun (LSeries.term_of_ne_zero' (ne_zero_of_one_lt_re hs) _)

/-!
## Functional equations for the un-completed zetas
-/

/-- If `s` is not in `-ℕ`, and either `a ≠ 0` or `s ≠ 1`, then
`hurwitzZetaEven a (1 - s)` is an explicit multiple of `cosZeta s`. -/
/-
**HurwitzZeta.hurwitzZetaEven_one_sub** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：hurwitzZetaEven_one_sub (a : UnitAddCircle) {s : Complex} (hs : forall (n 
: Nat), s != -n) (hs' : a != 0 ∨ s != 1) : hurwitzZetaEven a (1 - s) = 2 * (2 * 
π) ^ (-s) * Gamma s * cos (π * s / 2) * cosZeta a s
参数：a : UnitAddCircle；hs : forall (n : Nat), s != -n；hs' : a != 0 ∨ s != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HurwitzZeta.hurwitzZetaEven_def_of_ne_or_ne`：hurwitzZetaEven_def_of_ne_o
r_ne {a : UnitAddCircle} {s : Complex} (h : a != 0 ∨ s != 0) : hurwitzZetaEven a
 s = completedHurwitzZetaEven a s…
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `HurwitzZeta.completedHurwitzZetaEven_one_sub`：completedHurwitzZetaEven_o
ne_sub (a : UnitAddCircle) (s : Complex) : completedHurwitzZetaEven a (1 - s) = 
completedCosZeta a s
· 使用定理 `Complex.inv_Gammaℝ_one_sub`：∀ {s : ℂ}, (∀ (n : ℕ), s ≠ -↑n) → (1 - s).Ga
mmaℝ⁻¹ = s.Gammaℂ * Complex.cos (↑Real.pi * s / 2) * s.Gammaℝ⁻¹
· 使用定理 `HurwitzZeta.cosZeta.eq_1`：∀ (a : UnitAddCircle),   HurwitzZeta.cosZeta a
 = Function.update (fun s => HurwitzZeta.completedCosZeta a s / s.Gammaℝ) 0 (-1 
/ 2)
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.Gammaℂ.eq_1`：∀ (s : ℂ), s.Gammaℂ = 2 * (2 * ↑Real.pi) ^ (-s) * C
omplex.Gamma s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b : R}, a = a' → a'⁻¹ = b → a⁻¹ = b
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_single`：∀ {R : Type u_2} [inst : Semifiel
d R] {a b : R}, a⁻¹ = b → (a + 0)⁻¹ = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_mul`：∀ {R : Type u_2} [inst : Semifield R
] {a₁ : R} {a₂ : ℕ} {a₃ b₁ b₃ c : R},   a₁⁻¹ = b₁ → a₃⁻¹ = b₃ → b₃ * (b₁ ^ a₂ * 
Nat.rawCast 1) = c → (a₁…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isNat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n 1 → Mathlib.Meta.NormNum
.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
If `s` is not in `-ℕ`, and either `a ≠ 0` or `s ≠ 1`, then
`hurwitzZetaEven a (1 - s)` is an explicit multiple of `cosZeta s`.
-/
lemma hurwitzZetaEven_one_sub (a : UnitAddCircle) {s : ℂ}
    (hs : ∀ (n : ℕ), s ≠ -n) (hs' : a ≠ 0 ∨ s ≠ 1) :
    hurwitzZetaEven a (1 - s) = 2 * (2 * π) ^ (-s) * Gamma s * cos (π * s / 2) * cosZeta a s := by
  have : hurwitzZetaEven a (1 - s) = completedHurwitzZetaEven a (1 - s) * (Gammaℝ (1 - s))⁻¹ := by
    rw [hurwitzZetaEven_def_of_ne_or_ne, div_eq_mul_inv]
    simpa [sub_eq_zero, eq_comm (a := s)] using hs'
  rw [this, completedHurwitzZetaEven_one_sub, inv_Gammaℝ_one_sub hs, cosZeta,
    Function.update_of_ne (by simpa using hs 0), ← Gammaℂ]
  generalize Gammaℂ s * cos (π * s / 2) = A -- speeds up ring_nf call
  ring_nf

/-- If `s` is not of the form `1 - n` for `n ∈ ℕ`, then `cosZeta a (1 - s)` is an explicit
multiple of `hurwitzZetaEven s`. -/
/-
**HurwitzZeta.cosZeta_one_sub** 是 Mathlib 中的一个引理，位于命名空间 `HurwitzZeta`。
形式化陈述：cosZeta_one_sub (a : UnitAddCircle) {s : Complex} (hs : forall (n : Nat), 
s != 1 - n) : cosZeta a (1 - s) = 2 * (2 * π) ^ (-s) * Gamma s * cos (π * s / 2)
 * hurwitzZetaEven a s
参数：a : UnitAddCircle；hs : forall (n : Nat), s != 1 - n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.Gammaℂ.eq_1`：∀ (s : ℂ), s.Gammaℂ = 2 * (2 * ↑Real.pi) ^ (-s) * C
omplex.Gamma s
· 使用定理 `HurwitzZeta.cosZeta.eq_1`：∀ (a : UnitAddCircle),   HurwitzZeta.cosZeta a
 = Function.update (fun s => HurwitzZeta.completedCosZeta a s / s.Gammaℝ) 0 (-1 
/ 2)
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用引理 `HurwitzZeta.completedCosZeta_one_sub`：completedCosZeta_one_sub (a : Unit
AddCircle) (s : Complex) : completedCosZeta a (1 - s) = completedHurwitzZetaEven
 a s
· 使用定理 `Complex.inv_Gammaℝ_one_sub`：∀ {s : ℂ}, (∀ (n : ℕ), s ≠ -↑n) → (1 - s).Ga
mmaℝ⁻¹ = s.Gammaℂ * Complex.cos (↑Real.pi * s / 2) * s.Gammaℝ⁻¹
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `sub_add_cancel_right`：∀ {G : Type u_3} [inst : AddGroup G] (a b : G), a 
- (b + a) = -b
· 使用引理 `HurwitzZeta.hurwitzZetaEven_def_of_ne_or_ne`：hurwitzZetaEven_def_of_ne_o
r_ne {a : UnitAddCircle} {s : Complex} (h : a != 0 ∨ s != 0) : hurwitzZetaEven a
 s = completedHurwitzZetaEven a s…
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b : R}, a = a' → a'⁻¹ = b → a⁻¹ = b
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_single`：∀ {R : Type u_2} [inst : Semifiel
d R] {a b : R}, a⁻¹ = b → (a + 0)⁻¹ = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_mul`：∀ {R : Type u_2} [inst : Semifield R
] {a₁ : R} {a₂ : ℕ} {a₃ b₁ b₃ c : R},   a₁⁻¹ = b₁ → a₃⁻¹ = b₃ → b₃ * (b₁ ^ a₂ * 
Nat.rawCast 1) = c → (a₁…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isNat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n 1 → Mathlib.Meta.NormNum
.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
（共 48 条，此处仅展示前 30 条）

--- 原说明 ---
If `s` is not of the form `1 - n` for `n ∈ ℕ`, then `cosZeta a (1 - s)` is an ex
plicit
multiple of `hurwitzZetaEven s`.
-/
lemma cosZeta_one_sub (a : UnitAddCircle) {s : ℂ} (hs : ∀ (n : ℕ), s ≠ 1 - n) :
    cosZeta a (1 - s) = 2 * (2 * π) ^ (-s) * Gamma s * cos (π * s / 2) * hurwitzZetaEven a s := by
  rw [← Gammaℂ]
  have : cosZeta a (1 - s) = completedCosZeta a (1 - s) * (Gammaℝ (1 - s))⁻¹ := by
    rw [cosZeta, Function.update_of_ne, div_eq_mul_inv]
    simpa [sub_eq_zero] using (hs 0).symm
  rw [this, completedCosZeta_one_sub, inv_Gammaℝ_one_sub (fun n ↦ by simpa using hs (n + 1)),
    hurwitzZetaEven_def_of_ne_or_ne (Or.inr (by simpa using hs 1))]
  generalize Gammaℂ s * cos (π * s / 2) = A -- speeds up ring_nf call
  ring_nf

end HurwitzZeta

