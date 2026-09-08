/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Order.Filter.ZeroAndBoundedAtFilter

/-!
# Periodic holomorphic functions

We show that if `f : ℂ → ℂ` satisfies `f (z + h) = f z`, for some nonzero real `h`, then there is a
function `F` such that `f z = F (exp (2 * π * I * z / h))` for all `z`; and if `f` is holomorphic
at some `z`, then `F` is holomorphic at `exp (2 * π * I * z / h)`.

We also show (using Riemann's removable singularity theorem) that if `f` is holomorphic and bounded
for all sufficiently large `im z`, then `F` extends to a holomorphic function on a neighbourhood of
`0`. As a consequence, if `f` tends to zero as `im z → ∞`, then in fact it decays *exponentially*
to zero. These results are important in the theory of modular forms.
-/

@[expose] public section

open Complex Filter Asymptotics

open scoped Real Topology

noncomputable section

local notation "I∞" => comap im atTop

variable (h : ℝ)

namespace Function.Periodic

/-- Parameter for q-expansions, `qParam h z = exp (2 * π * I * z / h)` -/
/-
**Function.Periodic.qParam** 是 Mathlib 中的一个定义，位于命名空间 `Function.Periodic`。
形式化陈述：qParam (z : Complex) : Complex
参数：z : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Parameter for q-expansions, `qParam h z = exp (2 * π * I * z / h)`
-/
def qParam (z : ℂ) : ℂ := exp (2 * π * I * z / h)

/-- One-sided inverse of `qParam h`. -/
/-
**Function.Periodic.invQParam** 是 Mathlib 中的一个定义，位于命名空间 `Function.Periodic`。
形式化陈述：invQParam (q : Complex) : Complex
参数：q : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
One-sided inverse of `qParam h`.
-/
def invQParam (q : ℂ) : ℂ := h / (2 * π * I) * log q

local notation "𝕢" => qParam

section qParam

/-
**Function.Periodic.norm_qParam** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`。
形式化陈述：norm_qParam (z : Complex) : ‖𝕢 h z‖ = Real.exp (-2 * π * im z / h)
参数：z : Complex。
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
· 使用定理 `Complex.norm_exp`：norm_exp (z : Complex) : ‖exp z‖ = Real.exp z.re
· 使用定理 `Complex.div_ofReal_re`：∀ (z : ℂ) (x : ℝ), (z / ↑x).re = z.re / x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
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
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_qParam (z : ℂ) : ‖𝕢 h z‖ = Real.exp (-2 * π * im z / h) := by
  simp only [qParam, norm_exp, div_ofReal_re, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im,
    mul_zero, sub_zero, I_re, mul_im, zero_mul, add_zero, I_im, mul_one, sub_self, zero_sub,
    neg_mul]
/-
**Function.Periodic.im_invQParam** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`。
形式化陈述：im_invQParam (q : Complex) : im (invQParam h q) = -h / (2 * π) * Real.log 
‖q‖
参数：q : Complex。
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.div_I`：div_I (z : Complex) : z / I = -(z * I)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `Complex.div_ofReal_re`：∀ (z : ℂ) (x : ℝ), (z / ↑x).re = z.re / x
· 使用引理 `Complex.div_ofNat_re`：div_ofNat_re (z : Complex) (n : Nat) [n.AtLeastTwo
] : (z / ofNat(n)).re = z.re / ofNat(n)
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Complex.div_ofReal_im`：∀ (z : ℂ) (x : ℝ), (z / ↑x).im = z.im / x
· 使用引理 `Complex.div_ofNat_im`：div_ofNat_im (z : Complex) (n : Nat) [n.AtLeastTwo
] : (z / ofNat(n)).im = z.im / ofNat(n)
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Complex.log_re`：log_re (x : Complex) : x.log.re = Real.log ‖x‖
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem im_invQParam (q : ℂ) : im (invQParam h q) = -h / (2 * π) * Real.log ‖q‖ := by
  simp only [invQParam, ← div_div, div_I, neg_mul, neg_im, mul_im, mul_re, div_ofReal_re,
    div_ofNat_re, ofReal_re, I_re, mul_zero, div_ofReal_im, div_ofNat_im, ofReal_im, zero_div, I_im,
    mul_one, sub_self, zero_mul, add_zero, log_re, zero_add, neg_div]

variable {h} -- next few theorems all assume h ≠ 0 or 0 < h
/-
**Function.Periodic.qParam_right_inv** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodi
c`。
形式化陈述：qParam_right_inv (hh : h != 0) {q : Complex} (hq : q != 0) : 𝕢 h (invQPara
m h q) = q
参数：hh : h != 0；hq : q != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mul_div_cancel₀`：mul_div_cancel₀ (a : G₀) (hb : b != 0) : b * (a / b) = 
a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Complex.two_pi_I_ne_zero`：two_pi_I_ne_zero : (2 * π * I : Complex) != 0
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Complex.ofReal_ne_zero`：ofReal_ne_zero {z : Real} : (z : Complex) != 0 ↔
 z != 0
· 使用定理 `Complex.exp_log`：exp_log {x : Complex} (hx : x != 0) : exp (log x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem qParam_right_inv (hh : h ≠ 0) {q : ℂ} (hq : q ≠ 0) : 𝕢 h (invQParam h q) = q := by
  simp only [qParam, invQParam, ← mul_assoc, mul_div_cancel₀ _ two_pi_I_ne_zero,
    mul_div_cancel_left₀ _ (ofReal_ne_zero.mpr hh), exp_log hq]
/-
**Function.Periodic.qParam_left_inv_mod_period** 是 Mathlib 中的一个定理，位于命名空间 `Functi
on.Periodic`。
形式化陈述：qParam_left_inv_mod_period (hh : h != 0) (z : Complex) : exists m : Int, i
nvQParam h (𝕢 h z) = z + m * h
参数：hh : h != 0；z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Complex.log_exp_exists`：log_exp_exists (z : Complex) : exists n : Int, l
og (exp z) = z + n * (2 * π * I)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
· 使用定理 `Complex.two_pi_I_ne_zero`：two_pi_I_ne_zero : (2 * π * I : Complex) != 0
· 使用引理 `mul_div_cancel₀`：mul_div_cancel₀ (a : G₀) (hb : b != 0) : b * (a / b) = 
a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
-/
theorem qParam_left_inv_mod_period (hh : h ≠ 0) (z : ℂ) :
    ∃ m : ℤ, invQParam h (𝕢 h z) = z + m * h := by
  dsimp only [qParam, invQParam]
  obtain ⟨m, hm⟩ := log_exp_exists (2 * ↑π * I * z / ↑h)
  refine ⟨m, by rw [hm, mul_div_assoc, mul_comm (m : ℂ), ← mul_add, ← mul_assoc,
    div_mul_cancel₀ _ two_pi_I_ne_zero, mul_add, mul_div_cancel₀ _ (mod_cast hh), mul_comm]⟩
/-
**Function.Periodic.norm_qParam_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Function.Perio
dic`。
形式化陈述：norm_qParam_lt_iff (hh : 0 < h) (A : Real) (z : Complex) : ‖qParam h z‖ < 
Real.exp (-2 * π * A / h) ↔ A < im z
参数：hh : 0 < h；A : Real；z : Complex。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Periodic.norm_qParam`：norm_qParam (z : Complex) : ‖𝕢 h z‖ = Rea
l.exp (-2 * π * im z / h)
· 使用定理 `Real.exp_lt_exp`：exp_lt_exp {x y : Real} : exp x < exp y ↔ x < y
· 使用引理 `div_lt_div_iff_of_pos_right`：div_lt_div_iff_of_pos_right (hc : 0 < c) : 
a / c < b / c ↔ a < b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `mul_lt_mul_left_of_neg`：mul_lt_mul_left_of_neg [ExistsAddOfLE R] [PosMul
StrictMono R] [AddRightStrictMono R] [AddRightReflectLT R] {a b c : R} (h : c < 
0) : c * a <…
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
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
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
（共 31 条，此处仅展示前 30 条）
-/
theorem norm_qParam_lt_iff (hh : 0 < h) (A : ℝ) (z : ℂ) :
    ‖qParam h z‖ < Real.exp (-2 * π * A / h) ↔ A < im z := by
  rw [norm_qParam, Real.exp_lt_exp, div_lt_div_iff_of_pos_right hh, mul_lt_mul_left_of_neg]
  simpa using Real.pi_pos
/-
**Function.Periodic.norm_qParam_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Function.Perio
dic`。
形式化陈述：norm_qParam_lt_one (hh : 0 < h) {z : Complex} (hz : 0 < im z) : ‖𝕢 h z‖ < 
1
参数：hh : 0 < h；hz : 0 < im z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `Real.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Periodic.norm_qParam_lt_iff`：norm_qParam_lt_iff (hh : 0 < h) (A
 : Real) (z : Complex) : ‖qParam h z‖ < Real.exp (-2 * π * A / h) ↔ A < im z
-/
theorem norm_qParam_lt_one (hh : 0 < h) {z : ℂ} (hz : 0 < im z) : ‖𝕢 h z‖ < 1 := by
  simpa using (norm_qParam_lt_iff hh 0 z).mpr hz
/-
**Function.Periodic.qParam_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Function.Periodic`
。
形式化陈述：qParam_ne_zero (z : Complex) : 𝕢 h z != 0
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma qParam_ne_zero (z : ℂ) : 𝕢 h z ≠ 0 := by
  simp [qParam, exp_ne_zero]

@[fun_prop]
/-
**Function.Periodic.continuous_qParam** 是 Mathlib 中的一个引理，位于命名空间 `Function.Period
ic`。
形式化陈述：continuous_qParam : Continuous (𝕢 h)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.cexp`：Continuous.cexp (h : Continuous f) : Continuous fun y =
> exp (f y)
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `Continuous.div_const`：Continuous.div_const (hf : Continuous f) (y : G₀) 
: Continuous fun x => f x / y
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
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_const_mul`：continuous_const_mul (m : M) : Continuous (m * ·)
-/
lemma continuous_qParam : Continuous (𝕢 h) := by
  unfold qParam
  fun_prop

@[fun_prop]
/-
**Function.Periodic.differentiable_qParam** 是 Mathlib 中的一个引理，位于命名空间 `Function.Pe
riodic`。
形式化陈述：differentiable_qParam : Differentiable Complex (𝕢 h)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Differentiable.cexp`：Differentiable.cexp (hc : Differentiable 𝕜 f) : Dif
ferentiable 𝕜 fun x => Complex.exp (f x)
· 使用定理 `Differentiable.div_const`：Differentiable.div_const (hc : Differentiable 
𝕜 c) (d : 𝕜') : Differentiable 𝕜 fun x => c x / d
· 使用定理 `Differentiable.const_mul`：Differentiable.const_mul (ha : Differentiable 
𝕜 a) (b : 𝔸) : Differentiable 𝕜 fun y => b * a y
· 使用定理 `differentiable_id`：differentiable_id : Differentiable 𝕜 (id : E -> E)
-/
lemma differentiable_qParam : Differentiable ℂ (𝕢 h) := by
  unfold qParam
  fun_prop

@[fun_prop]
/-
**Function.Periodic.contDiff_qParam** 是 Mathlib 中的一个引理，位于命名空间 `Function.Periodic
`。
形式化陈述：contDiff_qParam (m : WithTop Nat∞) : ContDiff Complex m (𝕢 h)
参数：m : WithTop Nat∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.cexp`：ContDiff.cexp {n} (h : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun
 x => Complex.exp (f x)
· 使用定理 `ContDiff.div_const`：ContDiff.div_const {f : E -> 𝕜'} {n} (hf : ContDiff 
𝕜 n f) (c : 𝕜') : ContDiff 𝕜 n fun x => f x / c
· 使用定理 `ContDiff.mul`：ContDiff.mul {f g : E -> 𝔸} (hf : ContDiff 𝕜 n f) (hg : Co
ntDiff 𝕜 n g) : ContDiff 𝕜 n fun x => f x * g x
· 使用定理 `contDiff_const`：contDiff_const {c : F} : ContDiff 𝕜 n fun _ : E => c
· 使用定理 `contDiff_id`：contDiff_id : ContDiff 𝕜 n (id : E -> E)
-/
lemma contDiff_qParam (m : WithTop ℕ∞) : ContDiff ℂ m (𝕢 h) := by
  unfold qParam
  fun_prop
/-
**Function.Periodic.qParam_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic`
。
形式化陈述：qParam_tendsto (hh : 0 < h) : Tendsto (qParam h) I∞ (𝓝[!=] 0)
参数：hh : 0 < h。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within`：tendsto_nhdsWit
hin_of_tendsto_nhds_of_eventually_within {a : α} {l : Filter β} {s : Set α} (f :
 β -> α) (h1 : Tendsto f l (𝓝 a)) (h2 : foral…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendsto_zero_iff_norm_tendsto_zero`：∀ {α : Type u_1} {E : Type u_4} [ins
t : SeminormedAddGroup E] {f : α → E} {a : Filter α},   Filter.Tendsto f a (nhds
 0) ↔ Filter.Tendsto (fu…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.Periodic.norm_qParam`：norm_qParam (z : Complex) : ‖𝕢 h z‖ = Rea
l.exp (-2 * π * im z / h)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_comap'_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3
} {m : α → β} {f : Filter α} {g : Filter β} {i : γ → α},   Set.range i ∈ f → (Fi
lter.Tendsto (m…
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.range_im`：range_im : range im = univ
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Real.tendsto_exp_atBot`：tendsto_exp_atBot : Tendsto exp atBot (𝓝 0)
· 使用定理 `Filter.Tendsto.atBot_div_const`：∀ {α : Type u_1} {β : Type u_2} [inst : 
Field α] [inst_1 : LinearOrder α] [IsStrictOrderedRing α] {l : Filter β}   {f : 
β → α} {r : α}, 0 < …
· 使用定理 `Filter.Tendsto.const_mul_atTop_of_neg`：∀ {α : Type u_1} {β : Type u_2} [
inst : Field α] [inst_1 : LinearOrder α] [IsStrictOrderedRing α] {l : Filter β} 
  {f : β → α} {r : α}, r < …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
（共 31 条，此处仅展示前 30 条）
-/
theorem qParam_tendsto (hh : 0 < h) : Tendsto (qParam h) I∞ (𝓝[≠] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
    (.of_forall fun q ↦ exp_ne_zero _)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [norm_qParam]
  apply (tendsto_comap'_iff (m := fun y ↦ Real.exp (-2 * π * y / h)) (range_im ▸ univ_mem)).mpr
  refine Real.tendsto_exp_atBot.comp (.atBot_div_const hh (tendsto_id.const_mul_atTop_of_neg ?_))
  simpa using Real.pi_pos
/-
**Function.Periodic.invQParam_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `Function.Period
ic`。
形式化陈述：invQParam_tendsto (hh : 0 < h) : Tendsto (invQParam h) (𝓝[!=] 0) I∞
参数：hh : 0 < h。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.Periodic.im_invQParam`：im_invQParam (q : Complex) : im (invQPar
am h q) = -h / (2 * π) * Real.log ‖q‖
· 使用定理 `Filter.Tendsto.const_mul_atBot_of_neg`：∀ {α : Type u_1} {β : Type u_2} [
inst : Field α] [inst_1 : LinearOrder α] [IsStrictOrderedRing α] {l : Filter β} 
  {f : β → α} {r : α}, r < …
· 使用定理 `div_neg_of_neg_of_pos`：div_neg_of_neg_of_pos (ha : a < 0) (hb : 0 < b) :
 a / b < 0
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_lt_zero`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeft
StrictMono α] {a : α}, -a < 0 ↔ 0 < a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用引理 `Real.tendsto_log_nhdsGT_zero`：tendsto_log_nhdsGT_zero : Tendsto log (𝓝[>
] 0) atBot
· 使用定理 `tendsto_norm_nhdsNE_zero`：∀ {E : Type u_4} [inst : NormedAddGroup E], Fi
lter.Tendsto norm (nhdsWithin 0 {0}ᶜ) (nhdsWithin 0 (Set.Ioi 0))
-/
theorem invQParam_tendsto (hh : 0 < h) : Tendsto (invQParam h) (𝓝[≠] 0) I∞ := by
  simp only [tendsto_comap_iff, comp_def, im_invQParam]
  apply Tendsto.const_mul_atBot_of_neg (div_neg_of_neg_of_pos (neg_lt_zero.mpr hh) (by positivity))
  exact Real.tendsto_log_nhdsGT_zero.comp tendsto_norm_nhdsNE_zero

end qParam

section PeriodicOnℂ

variable (h : ℝ) (f : ℂ → ℂ)

/-- The function `q ↦ f (invQParam h q)`, extended by a non-canonical choice of limit at 0. -/
/-
**Function.Periodic.cuspFunction** 是 Mathlib 中的一个定义，位于命名空间 `Function.Periodic`。
形式化陈述：cuspFunction : Complex -> Complex
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α

--- 原说明 ---
The function `q ↦ f (invQParam h q)`, extended by a non-canonical choice of limi
t at 0.
-/
def cuspFunction : ℂ → ℂ :=
  update (f ∘ invQParam h) 0 (limUnder (𝓝[≠] 0) (f ∘ invQParam h))
/-
**Function.Periodic.cuspFunction_eq_of_nonzero** 是 Mathlib 中的一个定理，位于命名空间 `Functi
on.Periodic`。
形式化陈述：cuspFunction_eq_of_nonzero {q : Complex} (hq : q != 0) : cuspFunction h f 
q = f (invQParam h q)
参数：hq : q != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem cuspFunction_eq_of_nonzero {q : ℂ} (hq : q ≠ 0) :
    cuspFunction h f q = f (invQParam h q) :=
  update_of_ne hq ..
/-
**Function.Periodic.cuspFunction_zero_eq_limUnder_nhds_ne** 是 Mathlib 中的一个定理，位于命
名空间 `Function.Periodic`。
形式化陈述：cuspFunction_zero_eq_limUnder_nhds_ne : cuspFunction h f 0 = limUnder (𝓝[!
=] 0) (cuspFunction h f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Filter.map_congr`：map_congr {m₁ m₂ : α -> β} {f : Filter α} (h : m₁ =ᶠ[f
] m₂) : map m₁ f = map m₂ f
· 使用定理 `eventuallyEq_nhdsWithin_of_eqOn`：eventuallyEq_nhdsWithin_of_eqOn {f g : 
α -> β} {s : Set α} {a : α} (h : EqOn f g s) : f =ᶠ[𝓝[s] a] g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Periodic.cuspFunction.eq_1`：∀ (h : ℝ) (f : ℂ → ℂ),   Function.P
eriodic.cuspFunction h f =     Function.update (f ∘ Function.Periodic.invQParam 
h) 0       ((nhdsWithin 0…
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
-/
theorem cuspFunction_zero_eq_limUnder_nhds_ne :
    cuspFunction h f 0 = limUnder (𝓝[≠] 0) (cuspFunction h f) := by
  conv_lhs => simp only [cuspFunction, update_self]
  refine congr_arg lim (Filter.map_congr <| eventuallyEq_nhdsWithin_of_eqOn fun r hr ↦ ?_)
  rw [cuspFunction, update_of_ne hr]

variable {f h}
/-
**Function.Periodic.eq_cuspFunction** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodic
`。
形式化陈述：eq_cuspFunction (hh : h != 0) (hf : Periodic f h) (z : Complex) : (cuspFun
ction h f) (𝕢 h z) = f z
参数：hh : h != 0；hf : Periodic f h；z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Periodic.cuspFunction.eq_1`：∀ (h : ℝ) (f : ℂ → ℂ),   Function.P
eriodic.cuspFunction h f =     Function.update (f ∘ Function.Periodic.invQParam 
h) 0       ((nhdsWithin 0…
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `Complex.exp_ne_zero`：exp_ne_zero : exp x != 0
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Function.Periodic.qParam_left_inv_mod_period`：qParam_left_inv_mod_period
 (hh : h != 0) (z : Complex) : exists m : Int, invQParam h (𝕢 h z) = z + m * h
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Function.Periodic.int_mul`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
c : α} [inst : NonAssocRing α],   Function.Periodic f c → ∀ (n : ℤ), Function.Pe
riodic f (↑n * …
-/
theorem eq_cuspFunction (hh : h ≠ 0) (hf : Periodic f h) (z : ℂ) :
    (cuspFunction h f) (𝕢 h z) = f z := by
  have : (cuspFunction h f) (𝕢 h z) = f (invQParam h (𝕢 h z)) := by
    rw [cuspFunction, update_of_ne, comp_apply]
    exact exp_ne_zero _
  obtain ⟨m, hm⟩ := qParam_left_inv_mod_period hh z
  simpa only [this, hm] using hf.int_mul m z
/-
**Function.Periodic.tendsto_nhds_zero** 是 Mathlib 中的一个引理，位于命名空间 `Function.Period
ic`。
形式化陈述：tendsto_nhds_zero {f : Complex -> Complex} (hcts : ContinuousAt (cuspFunct
ion h f) 0) : Tendsto (fun x => f (invQParam h x)) (𝓝[!=] 0) (𝓝 (cuspFunction h 
f 0))
参数：hcts : ContinuousAt (cuspFunction h f) 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `tendsto_nhdsWithin_of_tendsto_nhds`：tendsto_nhdsWithin_of_tendsto_nhds {
f : α -> β} {a : α} {s : Set α} {l : Filter β} (h : Tendsto f (𝓝 a) l) : Tendsto
 f (𝓝[s] a) l
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Function.Periodic.cuspFunction_eq_of_nonzero`：cuspFunction_eq_of_nonzero
 {q : Complex} (hq : q != 0) : cuspFunction h f q = f (invQParam h q)
-/
lemma tendsto_nhds_zero {f : ℂ → ℂ} (hcts : ContinuousAt (cuspFunction h f) 0) :
    Tendsto (fun x ↦ f (invQParam h x)) (𝓝[≠] 0) (𝓝 (cuspFunction h f 0)) := by
  apply (tendsto_nhdsWithin_of_tendsto_nhds hcts.tendsto).congr'
  filter_upwards [self_mem_nhdsWithin] with a using cuspFunction_eq_of_nonzero h f

end PeriodicOnℂ

section HoloOnC

variable {h : ℝ} {f : ℂ → ℂ}

/--
Key technical lemma: the function `cuspFunction h f` is differentiable at the images of
differentiability points of `f` (even if `invQParam` is not differentiable there).
-/
/-
**Function.Periodic.differentiableAt_cuspFunction** 是 Mathlib 中的一个定理，位于命名空间 `Fun
ction.Periodic`。
形式化陈述：differentiableAt_cuspFunction (hh : h != 0) (hf : Periodic f h) {z : Compl
ex} (hol_z : DifferentiableAt Complex f z) : DifferentiableAt Complex (cuspFunct
ion h f) (𝕢 h z)
参数：hh : h != 0；hf : Periodic f h；hol_z : DifferentiableAt Complex f z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasStrictDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `HasStrictDerivAt.cexp`：HasStrictDerivAt.cexp (hf : HasStrictDerivAt f f'
 x) : HasStrictDerivAt (fun x => Complex.exp (f x)) (Complex.exp (f x) * f') x
· 使用定理 `HasStrictDerivAt.div_const`：HasStrictDerivAt.div_const (hc : HasStrictDe
rivAt c c' x) (d : 𝕜') : HasStrictDerivAt (fun x => c x / d) (c' / d) x
· 使用定理 `HasStrictDerivAt.const_mul`：HasStrictDerivAt.const_mul (c : 𝔸) (hd : Has
StrictDerivAt d d' x) : HasStrictDerivAt (fun y => c * d y) (c * d') x
· 使用定理 `hasStrictDerivAt_id`：hasStrictDerivAt_id : HasStrictDerivAt id 1 x
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Complex.exp_ne_zero`：exp_ne_zero : exp x != 0
· 使用定理 `div_ne_zero`：div_ne_zero (ha : a != 0) (hb : b != 0) : a / b != 0
· 使用定理 `Complex.two_pi_I_ne_zero`：two_pi_I_ne_zero : (2 * π * I : Complex) != 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `HasStrictFDerivAt.differentiableAt`：∀ {𝕜 : Type u_1} [inst : Nontriviall
yNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Modu
le 𝕜 E] [inst_3 : Topolo…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `HasStrictDerivAt.hasStrictFDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
· 使用定理 `HasStrictDerivAt.to_localInverse`：to_localInverse : HasStrictDerivAt (hf
.localInverse f f' a hf') f'⁻¹ (f a)
· 使用定理 `HasStrictFDerivAt.eventually_right_inverse`：eventually_right_inverse (hf
 : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) : forallᶠ y in 𝓝 (f a), f (hf.localI
nverse f f' a y) = y
· 使用定理 `HasStrictDerivAt.hasStrictFDerivAt_equiv`：HasStrictDerivAt.hasStrictFDer
ivAt_equiv {f : 𝕜 -> 𝕜} {f' x : 𝕜} (hf : HasStrictDerivAt f f' x) (hf' : f' != 0
) : HasStrictFDerivAt f (Conti…
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
Key technical lemma: the function `cuspFunction h f` is differentiable at the im
ages of
differentiability points of `f` (even if `invQParam` is not differentiable there
).
-/
theorem differentiableAt_cuspFunction (hh : h ≠ 0) (hf : Periodic f h)
    {z : ℂ} (hol_z : DifferentiableAt ℂ f z) :
    DifferentiableAt ℂ (cuspFunction h f) (𝕢 h z) := by
  let q := 𝕢 h z
  have qdiff : HasStrictDerivAt (𝕢 h) (q * (2 * π * I / h)) z := by
    simpa only [id_eq, mul_one] using! (((hasStrictDerivAt_id z).const_mul _).div_const _).cexp
  -- Now show that the q-map has a differentiable local inverse at z, say L : ℂ → ℂ with L q = z.
  have diff_ne : q * (2 * π * I / h) ≠ 0 :=
    mul_ne_zero (exp_ne_zero _) (div_ne_zero two_pi_I_ne_zero <| mod_cast hh)
  let L := (qdiff.localInverse (𝕢 h) _ z) diff_ne
  have diff_L : DifferentiableAt ℂ L q :=
    (qdiff.to_localInverse diff_ne).hasStrictFDerivAt.differentiableAt
  have hL : 𝕢 h ∘ L =ᶠ[𝓝 q] (id : ℂ → ℂ) :=
    (qdiff.hasStrictFDerivAt_equiv diff_ne).eventually_right_inverse
  -- Thus, if F = cuspFunction h f, we have F q' = f (L q') for q' near q.
  -- Since L is differentiable at q, and f is differentiable at L q [ = z], we conclude
  -- that F is differentiable at q.
  have hF := hL.fun_comp (cuspFunction h f)
  have : cuspFunction h f ∘ 𝕢 h ∘ L = f ∘ L := funext fun z ↦ eq_cuspFunction hh hf (L z)
  rw [this] at hF
  rw [← EventuallyEq.eq_of_nhds (qdiff.hasStrictFDerivAt_equiv diff_ne).eventually_left_inverse]
    at hol_z
  exact (hol_z.comp q diff_L).congr_of_eventuallyEq hF.symm
/-
**Function.Periodic.eventually_differentiableAt_cuspFunction_nhds_ne_zero** 是 Ma
thlib 中的一个定理，位于命名空间 `Function.Periodic`。
形式化陈述：eventually_differentiableAt_cuspFunction_nhds_ne_zero (hh : 0 < h) (hf : P
eriodic f h) (h_hol : forallᶠ z in I∞, DifferentiableAt Complex f z) : forallᶠ q
 in 𝓝[!=] 0, DifferentiableAt Complex (cuspFunction h f) q
参数：hh : 0 < h；hf : Periodic f h；h_hol : forallᶠ z in I∞, DifferentiableAt Comple
x f z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Function.Periodic.invQParam_tendsto`：invQParam_tendsto (hh : 0 < h) : Te
ndsto (invQParam h) (𝓝[!=] 0) I∞
· 使用定理 `eventually_nhdsWithin_of_forall`：eventually_nhdsWithin_of_forall {s : Se
t α} {a : α} {p : α -> Prop} (h : forall x in s, p x) : forallᶠ x in 𝓝[s] a, p x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Periodic.qParam_right_inv`：qParam_right_inv (hh : h != 0) {q : 
Complex} (hq : q != 0) : 𝕢 h (invQParam h q) = q
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Function.Periodic.differentiableAt_cuspFunction`：differentiableAt_cuspFu
nction (hh : h != 0) (hf : Periodic f h) {z : Complex} (hol_z : DifferentiableAt
 Complex f z) : DifferentiableAt Comp…
-/
theorem eventually_differentiableAt_cuspFunction_nhds_ne_zero (hh : 0 < h) (hf : Periodic f h)
    (h_hol : ∀ᶠ z in I∞, DifferentiableAt ℂ f z) :
    ∀ᶠ q in 𝓝[≠] 0, DifferentiableAt ℂ (cuspFunction h f) q := by
  refine ((invQParam_tendsto hh).eventually h_hol).mp ?_
  refine eventually_nhdsWithin_of_forall (fun q hq h_diff ↦ ?_)
  rw [← qParam_right_inv hh.ne' hq]
  exact differentiableAt_cuspFunction hh.ne' hf h_diff

end HoloOnC

section HoloAtInfC

variable {h : ℝ} {f : ℂ → ℂ}

/-
**Function.Periodic.boundedAtFilter_cuspFunction** 是 Mathlib 中的一个定理，位于命名空间 `Func
tion.Periodic`。
形式化陈述：boundedAtFilter_cuspFunction (hh : 0 < h) (h_bd : BoundedAtFilter I∞ f) : 
BoundedAtFilter (𝓝[!=] 0) (cuspFunction h f)
参数：hh : 0 < h；h_bd : BoundedAtFilter I∞ f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.congr'`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4
} [inst : Norm E] [inst_1 : Norm F] {l : Filter α} {f₁ f₂ : α → E}   {g₁ g₂ : α 
→ F}, f₁ =O[l] …
· 使用定理 `Asymptotics.IsBigO.comp_tendsto`：∀ {α : Type u_1} {β : Type u_2} {E : Ty
pe u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F}
   {l : Filter α}, f …
· 使用定理 `Function.Periodic.invQParam_tendsto`：invQParam_tendsto (hh : 0 < h) : Te
ndsto (invQParam h) (𝓝[!=] 0) I∞
· 使用定理 `eventually_nhdsWithin_of_forall`：eventually_nhdsWithin_of_forall {s : Se
t α} {a : α} {p : α -> Prop} (h : forall x in s, p x) : forallᶠ x in 𝓝[s] a, p x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Periodic.cuspFunction_eq_of_nonzero`：cuspFunction_eq_of_nonzero
 {q : Complex} (hq : q != 0) : cuspFunction h f q = f (invQParam h q)
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem boundedAtFilter_cuspFunction (hh : 0 < h) (h_bd : BoundedAtFilter I∞ f) :
    BoundedAtFilter (𝓝[≠] 0) (cuspFunction h f) := by
  refine (h_bd.comp_tendsto <| invQParam_tendsto hh).congr' ?_ (by simp)
  refine eventually_nhdsWithin_of_forall fun q hq ↦ ?_
  rw [cuspFunction_eq_of_nonzero _ _ hq, comp_def]
/-
**Function.Periodic.cuspFunction_zero_of_zero_at_inf** 是 Mathlib 中的一个定理，位于命名空间 `
Function.Periodic`。
形式化陈述：cuspFunction_zero_of_zero_at_inf (hh : 0 < h) (h_zer : ZeroAtFilter I∞ f) 
: cuspFunction h f 0 = 0
参数：hh : 0 < h；h_zer : ZeroAtFilter I∞ f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Filter.Tendsto.limUnder_eq`：Filter.Tendsto.limUnder_eq {x : X} {f : Filt
er Y} [NeBot f] {g : Y -> X} (h : Tendsto g f (𝓝 x)) : @limUnder _ _ _ ⟨x⟩ f g =
 x
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Function.Periodic.invQParam_tendsto`：invQParam_tendsto (hh : 0 < h) : Te
ndsto (invQParam h) (𝓝[!=] 0) I∞
-/
theorem cuspFunction_zero_of_zero_at_inf (hh : 0 < h) (h_zer : ZeroAtFilter I∞ f) :
    cuspFunction h f 0 = 0 := by
  simpa only [cuspFunction, update_self] using (h_zer.comp (invQParam_tendsto hh)).limUnder_eq
/-
**Function.Periodic.differentiableAt_cuspFunction_zero** 是 Mathlib 中的一个定理，位于命名空间
 `Function.Periodic`。
形式化陈述：differentiableAt_cuspFunction_zero (hh : 0 < h) (hf : Periodic f h) (h_hol
 : forallᶠ z in I∞, DifferentiableAt Complex f z) (h_bd : BoundedAtFilter I∞ f) 
: DifferentiableAt Complex (cuspFunction h f) 0
参数：hh : 0 < h；hf : Periodic f h；h_hol : forallᶠ z in I∞, DifferentiableAt Comple
x f z；h_bd : BoundedAtFilter I∞ f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.bound`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4}
 [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},   f =
O[l] g → ∃ c, …
· 使用定理 `Function.Periodic.boundedAtFilter_cuspFunction`：boundedAtFilter_cuspFunc
tion (hh : 0 < h) (h_bd : BoundedAtFilter I∞ f) : BoundedAtFilter (𝓝[!=] 0) (cus
pFunction h f)
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `Function.Periodic.eventually_differentiableAt_cuspFunction_nhds_ne_zero`
：eventually_differentiableAt_cuspFunction_nhds_ne_zero (hh : 0 < h) (hf : Period
ic f h) (h_hol : forallᶠ z in I∞, DifferentiableAt Complex f …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `eventually_nhds_iff`：eventually_nhds_iff {p : X -> Prop} : (forallᶠ y in
 𝓝 x, p y) ↔ exists t : Set X, (forall y in t, p y) ∧ IsOpen t ∧ x in t
· 使用定理 `eventually_nhdsWithin_iff`：eventually_nhdsWithin_iff {a : α} {s : Set α}
 {p : α -> Prop} : (forallᶠ x in 𝓝[s] a, p x) ↔ forallᶠ x in 𝓝 a, x in s -> p x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `Complex.differentiableOn_update_limUnder_of_bddAbove`：differentiableOn_u
pdate_limUnder_of_bddAbove {f : Complex -> E} {s : Set Complex} {c : Complex} (h
c : s in 𝓝 c) (hd : DifferentiableOn Compl…
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `DifferentiableOn.differentiableAt`：DifferentiableOn.differentiableAt (h 
: DifferentiableOn 𝕜 f s) (hs : s in 𝓝 x) : DifferentiableAt 𝕜 f x
· 使用定理 `Function.update_eq_self`：update_eq_self (a : α) (f : forall a, β a) : up
date f a (f a) = f
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Function.Periodic.cuspFunction_zero_eq_limUnder_nhds_ne`：cuspFunction_ze
ro_eq_limUnder_nhds_ne : cuspFunction h f 0 = limUnder (𝓝[!=] 0) (cuspFunction h
 f)
-/
theorem differentiableAt_cuspFunction_zero (hh : 0 < h) (hf : Periodic f h)
    (h_hol : ∀ᶠ z in I∞, DifferentiableAt ℂ f z) (h_bd : BoundedAtFilter I∞ f) :
    DifferentiableAt ℂ (cuspFunction h f) 0 := by
  obtain ⟨c, t⟩ := (boundedAtFilter_cuspFunction hh h_bd).bound
  replace t := (eventually_differentiableAt_cuspFunction_nhds_ne_zero hh hf h_hol).and t
  simp only [norm_one, Pi.one_apply, mul_one] at t
  obtain ⟨S, hS1, hS2, hS3⟩ := eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp t)
  have h_diff : DifferentiableOn ℂ (cuspFunction h f) (S \ {0}) :=
    fun x hx ↦ (hS1 x hx.1 hx.2).1.differentiableWithinAt
  have hF_bd : BddAbove (norm ∘ cuspFunction h f '' (S \ {0})) := by
    use c
    simp only [mem_upperBounds, Set.mem_image, Set.mem_sdiff, forall_exists_index, and_imp]
    intro y q hq hq2 hy
    simpa only [← hy, norm_one, mul_one] using! (hS1 q hq hq2).2
  have := differentiableOn_update_limUnder_of_bddAbove (IsOpen.mem_nhds hS2 hS3) h_diff hF_bd
  rw [← cuspFunction_zero_eq_limUnder_nhds_ne, update_eq_self] at this
  exact this.differentiableAt (IsOpen.mem_nhds hS2 hS3)

/--
If `f` is periodic, and holomorphic and bounded near `I∞`, then it tends to a limit at `I∞`,
and this limit is the value of its cusp function at 0.
-/
/-
**Function.Periodic.tendsto_at_I_inf** 是 Mathlib 中的一个定理，位于命名空间 `Function.Periodi
c`。
形式化陈述：tendsto_at_I_inf (hh : 0 < h) (hf : Periodic f h) (h_hol : forallᶠ z in I∞
, DifferentiableAt Complex f z) (h_bd : BoundedAtFilter I∞ f) : Tendsto f I∞ (𝓝 
<| cuspFunction h f 0)
参数：hh : 0 < h；hf : Periodic f h；h_hol : forallᶠ z in I∞, DifferentiableAt Comple
x f z；h_bd : BoundedAtFilter I∞ f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_nhdsWithin_of_tendsto_nhds`：tendsto_nhdsWithin_of_tendsto_nhds {
f : α -> β} {a : α} {s : Set α} {l : Filter β} (h : Tendsto f (𝓝 a) l) : Tendsto
 f (𝓝[s] a) l
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
· 使用定理 `Function.Periodic.differentiableAt_cuspFunction_zero`：differentiableAt_c
uspFunction_zero (hh : 0 < h) (hf : Periodic f h) (h_hol : forallᶠ z in I∞, Diff
erentiableAt Complex f z) (h_bd : BoundedA…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.Periodic.eq_cuspFunction`：eq_cuspFunction (hh : h != 0) (hf : P
eriodic f h) (z : Complex) : (cuspFunction h f) (𝕢 h z) = f z
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Function.Periodic.qParam_tendsto`：qParam_tendsto (hh : 0 < h) : Tendsto 
(qParam h) I∞ (𝓝[!=] 0)

--- 原说明 ---
If `f` is periodic, and holomorphic and bounded near `I∞`, then it tends to a li
mit at `I∞`,
and this limit is the value of its cusp function at 0.
-/
theorem tendsto_at_I_inf (hh : 0 < h) (hf : Periodic f h)
    (h_hol : ∀ᶠ z in I∞, DifferentiableAt ℂ f z) (h_bd : BoundedAtFilter I∞ f) :
    Tendsto f I∞ (𝓝 <| cuspFunction h f 0) := by
  suffices Tendsto (cuspFunction h f) (𝓝[≠] 0) (𝓝 <| cuspFunction h f 0) by
    simpa only [Function.comp_def, eq_cuspFunction hh.ne' hf] using this.comp (qParam_tendsto hh)
  exact tendsto_nhdsWithin_of_tendsto_nhds
    (differentiableAt_cuspFunction_zero hh hf h_hol h_bd).continuousAt.tendsto

/--
If `f` is periodic, and holomorphic and bounded at `I∞`, then it has the form (constant) +
(exponentially decaying term) as `z → I∞`.
-/
/-
**Function.Periodic.exp_decay_sub_of_bounded_at_inf** 是 Mathlib 中的一个定理，位于命名空间 `F
unction.Periodic`。
形式化陈述：exp_decay_sub_of_bounded_at_inf (hh : 0 < h) (hf : Periodic f h) (h_hol : 
forallᶠ z in I∞, DifferentiableAt Complex f z) (h_bd : BoundedAtFilter I∞ f) : (
fun z => f z - cuspFunction h f 0) =O[I∞] (fun z => Real.exp (-2 * π * im z / h)
)
参数：hh : 0 < h；hf : Periodic f h；h_hol : forallᶠ z in I∞, DifferentiableAt Comple
x f z；h_bd : BoundedAtFilter I∞ f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Function.Periodic.eq_cuspFunction`：eq_cuspFunction (hh : h != 0) (hf : P
eriodic f h) (z : Complex) : (cuspFunction h f) (𝕢 h z) = f z
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Function.Periodic.norm_qParam`：norm_qParam (z : Complex) : ‖𝕢 h z‖ = Rea
l.exp (-2 * π * im z / h)
· 使用定理 `Asymptotics.IsBigO.norm_right`：∀ {α : Type u_1} {E : Type u_3} {F' : Typ
e u_7} [inst : Norm E] [inst_1 : SeminormedAddCommGroup F'] {f : α → E}   {g' : 
α → F'} {l : Filter…
· 使用定理 `Asymptotics.IsBigO.comp_tendsto`：∀ {α : Type u_1} {β : Type u_2} {E : Ty
pe u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F}
   {l : Filter α}, f …
· 使用定理 `Asymptotics.IsBigO.mono`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} 
[inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F}   {l l' : Filter α}, f
 =O[l'] g → l…
· 使用定理 `DifferentiableAt.isBigO_sub`：DifferentiableAt.isBigO_sub (h : Differenti
ableAt 𝕜 f x₀) : (f · - f x₀) =O[𝓝 x₀] (· - x₀)
· 使用定理 `Function.Periodic.differentiableAt_cuspFunction_zero`：differentiableAt_c
uspFunction_zero (hh : 0 < h) (hf : Periodic f h) (h_hol : forallᶠ z in I∞, Diff
erentiableAt Complex f z) (h_bd : BoundedA…
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `Function.Periodic.qParam_tendsto`：qParam_tendsto (hh : 0 < h) : Tendsto 
(qParam h) I∞ (𝓝[!=] 0)

--- 原说明 ---
If `f` is periodic, and holomorphic and bounded at `I∞`, then it has the form (c
onstant) +
(exponentially decaying term) as `z → I∞`.
-/
theorem exp_decay_sub_of_bounded_at_inf (hh : 0 < h) (hf : Periodic f h)
    (h_hol : ∀ᶠ z in I∞, DifferentiableAt ℂ f z) (h_bd : BoundedAtFilter I∞ f) :
    (fun z ↦ f z - cuspFunction h f 0) =O[I∞] (fun z ↦ Real.exp (-2 * π * im z / h)) := by
  simpa [comp_def, eq_cuspFunction hh.ne' hf, norm_qParam] using
    differentiableAt_cuspFunction_zero hh hf h_hol h_bd |>.isBigO_sub.mono
      nhdsWithin_le_nhds |>.comp_tendsto (qParam_tendsto hh) |>.norm_right

/--
If `f` is periodic, holomorphic near `I∞`, and tends to zero at `I∞`, then in fact it tends to zero
exponentially fast.
-/
/-
**Function.Periodic.exp_decay_of_zero_at_inf** 是 Mathlib 中的一个定理，位于命名空间 `Function
.Periodic`。
形式化陈述：exp_decay_of_zero_at_inf (hh : 0 < h) (hf : Periodic f h) (h_hol : forallᶠ
 z in I∞, DifferentiableAt Complex f z) (h_zer : ZeroAtFilter I∞ f) : f =O[I∞] f
un z => Real.exp (-2 * π * im z / h)
参数：hh : 0 < h；hf : Periodic f h；h_hol : forallᶠ z in I∞, DifferentiableAt Comple
x f z；h_zer : ZeroAtFilter I∞ f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Function.Periodic.cuspFunction_zero_of_zero_at_inf`：cuspFunction_zero_of
_zero_at_inf (hh : 0 < h) (h_zer : ZeroAtFilter I∞ f) : cuspFunction h f 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Function.Periodic.exp_decay_sub_of_bounded_at_inf`：exp_decay_sub_of_boun
ded_at_inf (hh : 0 < h) (hf : Periodic f h) (h_hol : forallᶠ z in I∞, Differenti
ableAt Complex f z) (h_bd : BoundedAtFi…
· 使用定理 `Filter.ZeroAtFilter.boundedAtFilter`：∀ {α : Type u_2} {β : Type u_3} [in
st : SeminormedAddGroup β] {l : Filter α} {f : α → β},   l.ZeroAtFilter f → l.Bo
undedAtFilter f

--- 原说明 ---
If `f` is periodic, holomorphic near `I∞`, and tends to zero at `I∞`, then in fa
ct it tends to zero
exponentially fast.
-/
theorem exp_decay_of_zero_at_inf (hh : 0 < h) (hf : Periodic f h)
    (h_hol : ∀ᶠ z in I∞, DifferentiableAt ℂ f z) (h_zer : ZeroAtFilter I∞ f) :
    f =O[I∞] fun z ↦ Real.exp (-2 * π * im z / h) := by
  simpa [cuspFunction_zero_of_zero_at_inf hh h_zer, sub_zero] using
    exp_decay_sub_of_bounded_at_inf hh hf h_hol h_zer.boundedAtFilter

end HoloAtInfC

section arithmetic

/-
**Function.Periodic.cuspFunction_smul** 是 Mathlib 中的一个引理，位于命名空间 `Function.Period
ic`。
形式化陈述：cuspFunction_smul {h} {f : Complex -> Complex} (hfcts : ContinuousAt (cusp
Function h f) 0) (a : Complex) : cuspFunction h (a • f) = a • cuspFunction h f
参数：hfcts : ContinuousAt (cuspFunction h f) 0；a : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Filter.Tendsto.limUnder_eq`：Filter.Tendsto.limUnder_eq {x : X} {f : Filt
er Y} [NeBot f] {g : Y -> X} (h : Tendsto g f (𝓝 x)) : @limUnder _ _ _ ⟨x⟩ f g =
 x
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
· 使用定理 `Filter.Tendsto.const_mul`：Filter.Tendsto.const_mul {α : Type*} {f : α ->
 M} {x : Filter α} {a : M} (b : M) (hf : Tendsto f x (𝓝 a)) : Tendsto (b * f ·) 
x (𝓝 (b * a))
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cuspFunction_smul {h} {f : ℂ → ℂ} (hfcts : ContinuousAt (cuspFunction h f) 0) (a : ℂ) :
    cuspFunction h (a • f) = a • cuspFunction h f := by
  simp only [cuspFunction] at *
  ext y
  obtain rfl | hy := eq_or_ne y 0
  · simpa using! (Tendsto.const_mul _ (by simpa using! hfcts)).limUnder_eq
  · simp [hy]
/-
**Function.Periodic.cuspFunction_neg** 是 Mathlib 中的一个引理，位于命名空间 `Function.Periodi
c`。
形式化陈述：cuspFunction_neg {h} {f : Complex -> Complex} (hfcts : ContinuousAt (cuspF
unction h f) 0) : cuspFunction h (-f) = -cuspFunction h f
参数：hfcts : ContinuousAt (cuspFunction h f) 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用引理 `Function.Periodic.cuspFunction_smul`：cuspFunction_smul {h} {f : Complex 
-> Complex} (hfcts : ContinuousAt (cuspFunction h f) 0) (a : Complex) : cuspFunc
tion h (a • f) = a • cusp…
-/
lemma cuspFunction_neg {h} {f : ℂ → ℂ} (hfcts : ContinuousAt (cuspFunction h f) 0) :
    cuspFunction h (-f) = -cuspFunction h f := by
  simpa using cuspFunction_smul hfcts (-1)
/-
**Function.Periodic.cuspFunction_add** 是 Mathlib 中的一个引理，位于命名空间 `Function.Periodi
c`。
形式化陈述：cuspFunction_add {h} {f g : Complex -> Complex} (hfcts : ContinuousAt (cus
pFunction h f) 0) (hgcts : ContinuousAt (cuspFunction h g) 0) : cuspFunction h (
f + g) = cuspFunction h f + cuspFunction h g
参数：hfcts : ContinuousAt (cuspFunction h f) 0；hgcts : ContinuousAt (cuspFunction 
h g) 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `ne_or_eq`：ne_or_eq {α : Sort*} (x y : α) : x != y ∨ x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Filter.Tendsto.limUnder_eq`：Filter.Tendsto.limUnder_eq {x : X} {f : Filt
er Y} [NeBot f] {g : Y -> X} (h : Tendsto g f (𝓝 x)) : @limUnder _ _ _ ⟨x⟩ f g =
 x
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `Exists.nonempty`：∀ {α : Sort u_1} {p : α → Prop}, (∃ x, p x) → Nonempty 
α
· 使用引理 `Function.Periodic.tendsto_nhds_zero`：tendsto_nhds_zero {f : Complex -> C
omplex} (hcts : ContinuousAt (cuspFunction h f) 0) : Tendsto (fun x => f (invQPa
ram h x)) (𝓝[!=] 0) (𝓝 (c…
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
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
· 使用定理 `tendsto_nhds_limUnder`：tendsto_nhds_limUnder {f : Filter α} {g : α -> X}
 (h : exists x, Tendsto g f (𝓝 x)) : Tendsto g f (𝓝 (@limUnder _ _ _ h.nonempty 
f g))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma cuspFunction_add {h} {f g : ℂ → ℂ} (hfcts : ContinuousAt (cuspFunction h f) 0)
    (hgcts : ContinuousAt (cuspFunction h g) 0) :
    cuspFunction h (f + g) = cuspFunction h f + cuspFunction h g := by
  simp only [cuspFunction]
  ext y
  obtain hy | rfl := ne_or_eq y 0
  · simp [hy]
  · simpa using! (tendsto_nhds_limUnder ⟨_, tendsto_nhds_zero hfcts⟩).add
      (tendsto_nhds_limUnder ⟨_, tendsto_nhds_zero hgcts⟩) |>.limUnder_eq
/-
**Function.Periodic.cuspFunction_sub** 是 Mathlib 中的一个引理，位于命名空间 `Function.Periodi
c`。
形式化陈述：cuspFunction_sub {h} {f g : Complex -> Complex} (hfcts : ContinuousAt (cus
pFunction h f) 0) (hgcts : ContinuousAt (cuspFunction h g) 0) : cuspFunction h (
f - g) = cuspFunction h f - cuspFunction h g
参数：hfcts : ContinuousAt (cuspFunction h f) 0；hgcts : ContinuousAt (cuspFunction 
h g) 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Function.Periodic.cuspFunction_neg`：cuspFunction_neg {h} {f : Complex ->
 Complex} (hfcts : ContinuousAt (cuspFunction h f) 0) : cuspFunction h (-f) = -c
uspFunction h f
· 使用引理 `Function.Periodic.cuspFunction_add`：cuspFunction_add {h} {f g : Complex 
-> Complex} (hfcts : ContinuousAt (cuspFunction h f) 0) (hgcts : ContinuousAt (c
uspFunction h g) 0) : cu…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma cuspFunction_sub {h} {f g : ℂ → ℂ} (hfcts : ContinuousAt (cuspFunction h f) 0)
    (hgcts : ContinuousAt (cuspFunction h g) 0) :
    cuspFunction h (f - g) = cuspFunction h f - cuspFunction h g := by
  simpa [sub_eq_add_neg, ← cuspFunction_neg hgcts]
    using cuspFunction_add hfcts (by simp [cuspFunction_neg, hgcts])

end arithmetic

end Function.Periodic

