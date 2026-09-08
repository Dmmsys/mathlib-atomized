/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex

import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Square root on `RCLike`

This file contains the definitions `Complex.sqrt` and `RCLike.sqrt` and builds basic API.
-/

@[expose] public section

variable {𝕜 : Type*} [RCLike 𝕜]

open ComplexOrder

/-- The square root of a complex number. -/
/-
**Complex.sqrt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Complex.sqrt (a : Complex) : Complex
参数：a : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The square root of a complex number.
-/
noncomputable def Complex.sqrt (a : ℂ) : ℂ := a ^ (2⁻¹ : ℂ)
/-
**Complex.sqrt_zero** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：Complex.sqrt 0 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.zero_cpow`：zero_cpow {x : Complex} (h : x != 0) : (0 : Complex) 
^ x = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem Complex.sqrt_zero : (0 : ℂ).sqrt = 0 := by simp [sqrt]
/-
**Complex.sqrt_one** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：Complex.sqrt 1 = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.one_cpow`：one_cpow (x : Complex) : (1 : Complex) ^ x = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem Complex.sqrt_one : (1 : ℂ).sqrt = 1 := by simp [sqrt]
/-
**Complex.sqrt_eq_real_add_ite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Complex.sqrt_eq_real_add_ite {a : Complex} : a.sqrt = √((‖a‖ + a.re) / 2) 
+ (if 0 <= a.im then 1 else -1) * √((‖a‖ - a.re) / 2) * I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Complex.cpow_inv_two_re`：cpow_inv_two_re (x : Complex) : (x ^ (2⁻¹ : Com
plex)).re = √((‖x‖ + x.re) / 2)
· 使用定理 `Complex.sqrt.eq_1`：∀ (a : ℂ), a.sqrt = a ^ 2⁻¹
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `Complex.cpow_inv_two_im_eq_sqrt`：cpow_inv_two_im_eq_sqrt {x : Complex} (
hx : 0 <= x.im) : (x ^ (2⁻¹ : Complex)).im = √((‖x‖ - x.re) / 2)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Complex.re_add_im`：re_add_im (z : Complex) : (z.re : Complex) + z.im * I
 = z
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `neg_one_mul`：neg_one_mul (a : α) : -1 * a = -a
· 使用引理 `Complex.cpow_inv_two_im_eq_neg_sqrt`：cpow_inv_two_im_eq_neg_sqrt {x : Co
mplex} (hx : x.im < 0) : (x ^ (2⁻¹ : Complex)).im = -√((‖x‖ - x.re) / 2)
-/
theorem Complex.sqrt_eq_real_add_ite {a : ℂ} :
    a.sqrt = √((‖a‖ + a.re) / 2) + (if 0 ≤ a.im then 1 else -1) * √((‖a‖ - a.re) / 2) * I := by
  rw [← cpow_inv_two_re, sqrt]
  by_cases! h : 0 ≤ a.im
  · simp [← cpow_inv_two_im_eq_sqrt h, h]
  simp only [re_add_im, ↓reduceIte, h.not_ge, neg_one_mul, ← ofReal_neg,
    ← cpow_inv_two_im_eq_neg_sqrt h]

open Complex in
/-
**sqrt_eq_exp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sqrt_eq_exp {z : Complex} (hz : z != 0) : sqrt z = exp (log z / 2)
参数：hz : z != 0。
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
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sqrt_eq_exp {z : ℂ} (hz : z ≠ 0) : sqrt z = exp (log z / 2) := by
  simp [sqrt, cpow_def, hz, div_eq_mul_inv]

/-- The square root on `RCLike`. -/
/-
**RCLike.sqrt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RCLike.sqrt (a : 𝕜) : 𝕜
参数：a : 𝕜。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The square root on `RCLike`.
-/
noncomputable def RCLike.sqrt (a : 𝕜) : 𝕜 := map ℂ 𝕜 (map 𝕜 ℂ a).sqrt
/-
**RCLike.sqrt_eq_ite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RCLike.sqrt_eq_ite {a : 𝕜} : sqrt a = if h : im (I : 𝕜) = 1 then (complexR
ingEquiv h).symm (complexRingEquiv h a).sqrt else √(re a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.sqrt.eq_1`：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] (a : 𝕜), RCLike.sqr
t a = (RCLike.map ℂ 𝕜) ((RCLike.map 𝕜 ℂ) a).sqrt
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RCLike.complexRingEquiv_apply`：∀ {𝕜 : Type u_2} [inst : RCLike 𝕜] (h : R
CLike.im RCLike.I = 1) (x : 𝕜),   (RCLike.complexRingEquiv h) x = ↑(RCLike.re x)
 + ↑(RCLike.im x) *…
· 使用定理 `RCLike.complexRingEquiv_symm_apply`：∀ {𝕜 : Type u_2} [inst : RCLike 𝕜] (
h : RCLike.im RCLike.I = 1) (x : ℂ),   (RCLike.complexRingEquiv h).symm x = ↑x.r
e + ↑x.im * RCLike.I
· 使用定理 `RCLike.map_apply`：∀ (𝕜 : Type u_3) (𝕜' : Type u_4) [inst : RCLike 𝕜] [in
st_1 : RCLike 𝕜'] (x : 𝕜),   (RCLike.map 𝕜 𝕜') x = ↑(RCLike.re x) + ↑(RCLike.im 
x) * R…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `RCLike.im_eq_zero`：im_eq_zero (h : I = (0 : K)) (z : K) : im z = 0
· 使用引理 `Complex.cpow_inv_two_re`：cpow_inv_two_re (x : Complex) : (x ^ (2⁻¹ : Com
plex)).re = √((‖x‖ + x.re) / 2)
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `GroupWithZero.toMulDivCancelClass`：∀ {G₀ : Type u} [inst : GroupWithZero
 G₀], MulDivCancelClass G₀
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
（共 37 条，此处仅展示前 30 条）
-/
theorem RCLike.sqrt_eq_ite {a : 𝕜} :
    sqrt a = if h : im (I : 𝕜) = 1 then (complexRingEquiv h).symm (complexRingEquiv h a).sqrt
      else √(re a) := by
  rw [sqrt, eq_comm]
  split_ifs with h
  · simp
  have : (I : 𝕜) = 0 := by grind [I_eq_zero_or_im_I_eq_one]
  simp_all only [Complex.sqrt, im_eq_zero this, map_apply, add_zero, re_to_complex, im_to_complex,
    mul_zero, algebraMap.coe_inj, Complex.cpow_inv_two_re]
  by_cases! ha' : 0 ≤ re a
  · simp [abs_of_nonneg ha', ← two_mul]
  simp [abs_of_nonpos ha'.le, Real.sqrt_eq_zero', ha'.le]
/-
**RCLike.sqrt_eq_real_add_ite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RCLike.sqrt_eq_real_add_ite {a : 𝕜} : sqrt a = √((‖a‖ + re a) / 2) + (if 0
 <= im a then 1 else -1) * √((‖a‖ - re a) / 2) * I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.sqrt.eq_1`：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] (a : 𝕜), RCLike.sqr
t a = (RCLike.map ℂ 𝕜) ((RCLike.map 𝕜 ℂ) a).sqrt
· 使用定理 `Complex.sqrt_eq_real_add_ite`：Complex.sqrt_eq_real_add_ite {a : Complex}
 : a.sqrt = √((‖a‖ + a.re) / 2) + (if 0 <= a.im then 1 else -1) * √((‖a‖ - a.re)
 / 2) * I
· 使用引理 `RCLike.I_eq_zero_or_im_I_eq_one`：I_eq_zero_or_im_I_eq_one : (I : K) = 0 
∨ im (I : K) = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RCLike.re_add_im`：re_add_im (z : K) : (re z : K) + im z * I = z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `RCLike.im_eq_zero`：im_eq_zero (h : I = (0 : K)) (z : K) : im z = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `RCLike.map_apply`：∀ (𝕜 : Type u_3) (𝕜' : Type u_4) [inst : RCLike 𝕜] [in
st_1 : RCLike 𝕜'] (x : 𝕜),   (RCLike.map 𝕜 𝕜') x = ↑(RCLike.re x) + ↑(RCLike.im 
x) * R…
· 使用定理 `RCLike.ofReal_re`：ofReal_re : forall r : Real, re (r : K) = r
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
· 使用定理 `Real.sqrt_div'`：sqrt_div' (x) {y : Real} (hy : 0 <= y) : √(x / y) = √x /
 √y
· 使用定理 `Complex.ofReal_div`：ofReal_div (r s : Real) : ((r / s : Real) : Complex)
 = r / s
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Complex.div_ofReal_re`：∀ (z : ℂ) (x : ℝ), (z / ↑x).re = z.re / x
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `Complex.div_ofReal_im`：∀ (z : ℂ) (x : ℝ), (z / ↑x).im = z.im / x
（共 53 条，此处仅展示前 30 条）
-/
theorem RCLike.sqrt_eq_real_add_ite {a : 𝕜} :
    sqrt a = √((‖a‖ + re a) / 2) + (if 0 ≤ im a then 1 else -1) * √((‖a‖ - re a) / 2) * I := by
  rw [sqrt, Complex.sqrt_eq_real_add_ite]
  obtain (h | h) := I_eq_zero_or_im_I_eq_one (K := 𝕜)
  · rw [← re_add_im a]
    simp [h, im_eq_zero]
  aesop
/-
**RCLike.sqrt_zero** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜], RCLike.sqrt 0 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.map_apply`：∀ (𝕜 : Type u_3) (𝕜' : Type u_4) [inst : RCLike 𝕜] [in
st_1 : RCLike 𝕜'] (x : 𝕜),   (RCLike.map 𝕜 𝕜') x = ↑(RCLike.re x) + ↑(RCLike.im 
x) * R…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Complex.sqrt_zero`：Complex.sqrt 0 = 0
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem RCLike.sqrt_zero : sqrt (0 : 𝕜) = 0 := by simp [sqrt]
/-
**RCLike.sqrt_one** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜], RCLike.sqrt 1 = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.map_apply`：∀ (𝕜 : Type u_3) (𝕜' : Type u_4) [inst : RCLike 𝕜] [in
st_1 : RCLike 𝕜'] (x : 𝕜),   (RCLike.map 𝕜 𝕜') x = ↑(RCLike.re x) + ↑(RCLike.im 
x) * R…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RCLike.one_re`：one_re : re (1 : K) = 1
· 使用定理 `RCLike.one_im`：one_im : im (1 : K) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Complex.sqrt_one`：Complex.sqrt 1 = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem RCLike.sqrt_one : sqrt (1 : 𝕜) = 1 := by simp [sqrt]
/-
**Complex.re_sqrt_ofReal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Complex.re_sqrt_ofReal {a : Real} : (sqrt (a : Complex)).re = √a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Complex.cpow_inv_two_re`：cpow_inv_two_re (x : Complex) : (x ^ (2⁻¹ : Com
plex)).re = √((‖x‖ + x.re) / 2)
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
-/
theorem Complex.re_sqrt_ofReal {a : ℝ} :
    (sqrt (a : ℂ)).re = √a := by
  simp only [cpow_inv_two_re, norm_real, Real.norm_eq_abs, ofReal_re, Complex.sqrt]
  grind
/-
**RCLike.re_sqrt_ofReal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RCLike.re_sqrt_ofReal {a : Real} : re (sqrt (a : 𝕜)) = √a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.map_apply`：∀ (𝕜 : Type u_3) (𝕜' : Type u_4) [inst : RCLike 𝕜] [in
st_1 : RCLike 𝕜'] (x : 𝕜),   (RCLike.map 𝕜 𝕜') x = ↑(RCLike.re x) + ↑(RCLike.im 
x) * R…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RCLike.ofReal_re`：ofReal_re : forall r : Real, re (r : K) = r
· 使用定理 `RCLike.ofReal_im`：ofReal_im : forall r : Real, im (r : K) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Complex.re_sqrt_ofReal`：Complex.re_sqrt_ofReal {a : Real} : (sqrt (a : C
omplex)).re = √a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `RCLike.mul_re`：mul_re : forall z w : K, re (z * w) = re z * re w - im z 
* im w
· 使用定理 `RCLike.I_re`：I_re : re (I : K) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem RCLike.re_sqrt_ofReal {a : ℝ} :
    re (sqrt (a : 𝕜)) = √a := by
  aesop (add simp [sqrt, Complex.re_sqrt_ofReal])
/-
**RCLike.sqrt_real** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：∀ {a : ℝ}, RCLike.sqrt a = √a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RCLike.re_sqrt_ofReal`：RCLike.re_sqrt_ofReal {a : Real} : re (sqrt (a : 
𝕜)) = √a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem RCLike.sqrt_real {a : ℝ} :
    sqrt a = √a := by simp [← re_sqrt_ofReal (𝕜 := ℝ)]
/-
**RCLike.sqrt_complex** 是 Mathlib 中的一个定理，位于命名空间 `RCLike`。
形式化陈述：∀ {a : ℂ}, RCLike.sqrt a = a.sqrt
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RCLike.map_same_eq_id`：∀ {K : Type u_1} [inst : RCLike K], RCLike.map K 
K = ContinuousLinearMap.id ℝ K
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem RCLike.sqrt_complex {a : ℂ} :
    sqrt a = a.sqrt := by simp [sqrt]

set_option backward.isDefEq.respectTransparency false in
/-
**Complex.sqrt_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Complex.sqrt_of_nonneg {a : Complex} (ha : 0 <= a) : a.sqrt = √a.re
参数：ha : 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `RCLike.nonneg_iff_exists_ofReal`：nonneg_iff_exists_ofReal : 0 <= z ↔ exi
sts x >= (0 : Real), x = z
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.re_add_im`：re_add_im (z : Complex) : (z.re : Complex) + z.im * I
 = z
· 使用定理 `Complex.re_sqrt_ofReal`：Complex.re_sqrt_ofReal {a : Real} : (sqrt (a : C
omplex)).re = √a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Complex.cpow_inv_two_im_eq_sqrt`：cpow_inv_two_im_eq_sqrt {x : Complex} (
hx : 0 <= x.im) : (x ^ (2⁻¹ : Complex)).im = √((‖x‖ - x.re) / 2)
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `Real.sqrt_zero`：sqrt_zero : √0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Complex.sqrt_of_nonneg {a : ℂ} (ha : 0 ≤ a) :
    a.sqrt = √a.re := by
  obtain ⟨α : ℝ, hα, rfl⟩ := RCLike.nonneg_iff_exists_ofReal.mp ha
  simp only [coe_algebraMap, ofReal_re]
  rw [← re_add_im (α : ℂ).sqrt, re_sqrt_ofReal]
  simp [sqrt, cpow_inv_two_im_eq_sqrt, abs_of_nonneg hα]
/-
**RCLike.sqrt_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RCLike.sqrt_map {𝕜' : Type*} [RCLike 𝕜'] {a : 𝕜} (h : im (I : 𝕜) = im (I :
 𝕜')) : sqrt (map 𝕜 𝕜' a) = map 𝕜 𝕜' (sqrt a)
参数：h : im (I : 𝕜) = im (I : 𝕜')。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RCLike.I_eq_zero_or_im_I_eq_one`：I_eq_zero_or_im_I_eq_one : (I : K) = 0 
∨ im (I : K) = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `RCLike.map_apply`：∀ (𝕜 : Type u_3) (𝕜' : Type u_4) [inst : RCLike 𝕜] [in
st_1 : RCLike 𝕜'] (x : 𝕜),   (RCLike.map 𝕜 𝕜') x = ↑(RCLike.re x) + ↑(RCLike.im 
x) * R…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `RCLike.ofReal_re`：ofReal_re : forall r : Real, re (r : K) = r
· 使用定理 `RCLike.mul_re`：mul_re : forall z w : K, re (z * w) = re z * re w - im z 
* im w
· 使用定理 `RCLike.I_re`：I_re : re (I : K) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RCLike.ofReal_im`：ofReal_im : forall r : Real, im (r : K) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `RCLike.mul_im`：mul_im : forall z w : K, im (z * w) = re z * im w + im z 
* re w
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `RCLike.im_eq_zero`：im_eq_zero (h : I = (0 : K)) (z : K) : im z = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
（共 34 条，此处仅展示前 30 条）
-/
theorem RCLike.sqrt_map {𝕜' : Type*} [RCLike 𝕜'] {a : 𝕜} (h : im (I : 𝕜) = im (I : 𝕜')) :
    sqrt (map 𝕜 𝕜' a) = map 𝕜 𝕜' (sqrt a) := by
  have := I_eq_zero_or_im_I_eq_one (K := 𝕜)
  have := I_eq_zero_or_im_I_eq_one (K := 𝕜')
  aesop (add simp [RCLike.sqrt, im_eq_zero])
/-
**Complex.sqrt_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Complex.sqrt_map {a : 𝕜} (h : RCLike.im (RCLike.I : 𝕜) = 1) : (RCLike.map 
𝕜 Complex a).sqrt = RCLike.map 𝕜 Complex (RCLike.sqrt a)
参数：h : RCLike.im (RCLike.I : 𝕜) = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.map_apply`：∀ (𝕜 : Type u_3) (𝕜' : Type u_4) [inst : RCLike 𝕜] [in
st_1 : RCLike 𝕜'] (x : 𝕜),   (RCLike.map 𝕜 𝕜') x = ↑(RCLike.re x) + ↑(RCLike.im 
x) * R…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `RCLike.ofReal_re`：ofReal_re : forall r : Real, re (r : K) = r
· 使用定理 `RCLike.mul_re`：mul_re : forall z w : K, re (z * w) = re z * re w - im z 
* im w
· 使用定理 `RCLike.I_re`：I_re : re (I : K) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `RCLike.ofReal_im`：ofReal_im : forall r : Real, im (r : K) = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RCLike.mul_im`：mul_im : forall z w : K, im (z * w) = re z * im w + im z 
* re w
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Complex.re_add_im`：re_add_im (z : Complex) : (z.re : Complex) + z.im * I
 = z
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Complex.sqrt_map {a : 𝕜} (h : RCLike.im (RCLike.I : 𝕜) = 1) :
    (RCLike.map 𝕜 ℂ a).sqrt = RCLike.map 𝕜 ℂ (RCLike.sqrt a) := by
  aesop (add simp [RCLike.sqrt])
/-
**RCLike.sqrt_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RCLike.sqrt_of_nonneg {a : 𝕜} (ha : 0 <= a) : sqrt a = √(re a)
参数：ha : 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RCLike.I_eq_zero_or_im_I_eq_one`：I_eq_zero_or_im_I_eq_one : (I : K) = 0 
∨ im (I : K) = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.sqrt_eq_ite`：RCLike.sqrt_eq_ite {a : 𝕜} : sqrt a = if h : im (I :
 𝕜) = 1 then (complexRingEquiv h).symm (complexRingEquiv h a).sqrt else √(re a)
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `RingEquiv.symm_apply_eq`：symm_apply_eq (e : R ≃+* S) {x : S} {y : R} : e
.symm x = y ↔ x = e y
· 使用定理 `Complex.sqrt_of_nonneg`：Complex.sqrt_of_nonneg {a : Complex} (ha : 0 <= 
a) : a.sqrt = √a.re
· 使用定理 `RCLike.complexRingEquiv_apply`：∀ {𝕜 : Type u_2} [inst : RCLike 𝕜] (h : R
CLike.im RCLike.I = 1) (x : 𝕜),   (RCLike.complexRingEquiv h) x = ↑(RCLike.re x)
 + ↑(RCLike.im x) *…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `RCLike.ofReal_re`：ofReal_re : forall r : Real, re (r : K) = r
· 使用定理 `RCLike.ofReal_im`：ofReal_im : forall r : Real, im (r : K) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem RCLike.sqrt_of_nonneg {a : 𝕜} (ha : 0 ≤ a) :
    sqrt a = √(re a) := by
  obtain (h | h) := I_eq_zero_or_im_I_eq_one (K := 𝕜)
  · simp [h, sqrt_eq_ite]
  rw [sqrt_eq_ite, dif_pos h, RingEquiv.symm_apply_eq, Complex.sqrt_of_nonneg (by simpa)]
  simp
/-
**Complex.sqrt_neg_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Complex.sqrt_neg_of_nonneg {a : Complex} (ha : 0 <= a) : (-a).sqrt = I * a
.sqrt
参数：ha : 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `RCLike.nonneg_iff_exists_ofReal`：nonneg_iff_exists_ofReal : 0 <= z ↔ exi
sts x >= (0 : Real), x = z
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.sqrt_of_nonneg`：Complex.sqrt_of_nonneg {a : Complex} (ha : 0 <= 
a) : a.sqrt = √a.re
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.re_add_im`：re_add_im (z : Complex) : (z.re : Complex) + z.im * I
 = z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Complex.cpow_inv_two_re`：cpow_inv_two_re (x : Complex) : (x ^ (2⁻¹ : Com
plex)).re = √((‖x‖ + x.re) / 2)
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `Real.sqrt_zero`：sqrt_zero : √0 = 0
· 使用引理 `Complex.cpow_inv_two_im_eq_sqrt`：cpow_inv_two_im_eq_sqrt {x : Complex} (
hx : 0 <= x.im) : (x ^ (2⁻¹ : Complex)).im = √((‖x‖ - x.re) / 2)
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `add_self_div_two`：∀ {K : Type u_1} [inst : DivisionSemiring K] [NeZero 2
] (a : K), (a + a) / 2 = a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Complex.sqrt_neg_of_nonneg {a : ℂ} (ha : 0 ≤ a) :
    (-a).sqrt = I * a.sqrt := by
  obtain ⟨α, hα, rfl⟩ := RCLike.nonneg_iff_exists_ofReal.mp ha
  rw [Complex.sqrt_of_nonneg ha]
  simp only [coe_algebraMap, ofReal_re]
  rw [← re_add_im (-(α : ℂ)).sqrt]
  simp [sqrt, cpow_inv_two_im_eq_sqrt, abs_of_nonneg hα, cpow_inv_two_re, mul_comm]
/-
**RCLike.sqrt_neg_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RCLike.sqrt_neg_of_nonneg {a : 𝕜} (ha : 0 <= a) : sqrt (-a) = I * sqrt a
参数：ha : 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RCLike.I_eq_zero_or_im_I_eq_one`：I_eq_zero_or_im_I_eq_one : (I : K) = 0 
∨ im (I : K) = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.sqrt_eq_ite`：RCLike.sqrt_eq_ite {a : 𝕜} : sqrt a = if h : im (I :
 𝕜) = 1 then (complexRingEquiv h).symm (complexRingEquiv h a).sqrt else √(re a)
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `RCLike.nonneg_iff`：nonneg_iff : 0 <= z ↔ 0 <= re z ∧ im z = 0
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `RingEquiv.symm_apply_eq`：symm_apply_eq (e : R ≃+* S) {x : S} {y : R} : e
.symm x = y ↔ x = e y
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `RingHomClass.toLinearMapClassNNRat`：∀ {F : Type u_1} {R : Type u_2} {S :
 Type u_3} [inst : DivisionSemiring R] [inst_1 : CharZero R]   [inst_2 : Divisio
nSemiring S] [inst_3 : C…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `Complex.sqrt_neg_of_nonneg`：Complex.sqrt_neg_of_nonneg {a : Complex} (ha
 : 0 <= a) : (-a).sqrt = I * a.sqrt
· 使用定理 `RCLike.complexRingEquiv_apply`：∀ {𝕜 : Type u_2} [inst : RCLike 𝕜] (h : R
CLike.im RCLike.I = 1) (x : 𝕜),   (RCLike.complexRingEquiv h) x = ↑(RCLike.re x)
 + ↑(RCLike.im x) *…
（共 49 条，此处仅展示前 30 条）
-/
theorem RCLike.sqrt_neg_of_nonneg {a : 𝕜} (ha : 0 ≤ a) :
    sqrt (-a) = I * sqrt a := by
  obtain (h | h) := I_eq_zero_or_im_I_eq_one (K := 𝕜)
  · simp [h, sqrt_eq_ite, Real.sqrt_eq_zero', nonneg_iff.mp ha]
  rw [sqrt_eq_ite, dif_pos h, RingEquiv.symm_apply_eq, map_neg,
    Complex.sqrt_neg_of_nonneg (by simpa)]
  simp [h, sqrt, map_mul]
/-
**Complex.sqrt_neg_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Complex.sqrt_neg_one : sqrt (-1) = I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.sqrt_neg_of_nonneg`：Complex.sqrt_neg_of_nonneg {a : Complex} (ha
 : 0 <= a) : (-a).sqrt = I * a.sqrt
· 使用引理 `RCLike.toZeroLEOneClass`：toZeroLEOneClass : ZeroLEOneClass K where zero_
le_one
· 使用定理 `Complex.sqrt_one`：Complex.sqrt 1 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Complex.sqrt_neg_one : sqrt (-1) = I := by
  simp [sqrt_neg_of_nonneg (a := 1) (by simp)]
/-
**RCLike.sqrt_neg_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RCLike.sqrt_neg_one : sqrt (-1) = (I : 𝕜)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.sqrt_neg_of_nonneg`：RCLike.sqrt_neg_of_nonneg {a : 𝕜} (ha : 0 <= 
a) : sqrt (-a) = I * sqrt a
· 使用引理 `RCLike.toZeroLEOneClass`：toZeroLEOneClass : ZeroLEOneClass K where zero_
le_one
· 使用定理 `RCLike.sqrt_one`：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜], RCLike.sqrt 1 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem RCLike.sqrt_neg_one : sqrt (-1) = (I : 𝕜) := by
  simp [sqrt_neg_of_nonneg (a := (1 : 𝕜)) (by simp)]
/-
**Complex.sqrt_I** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Complex.sqrt_I : sqrt (I : Complex) = √2⁻¹ * (1 + I)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.sqrt.eq_1`：∀ (a : ℂ), a.sqrt = a ^ 2⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.re_add_im`：re_add_im (z : Complex) : (z.re : Complex) + z.im * I
 = z
· 使用引理 `Complex.cpow_inv_two_im_eq_sqrt`：cpow_inv_two_im_eq_sqrt {x : Complex} (
hx : 0 <= x.im) : (x ^ (2⁻¹ : Complex)).im = √((‖x‖ - x.re) / 2)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Complex.cpow_inv_two_re`：cpow_inv_two_re (x : Complex) : (x ^ (2⁻¹ : Com
plex)).re = √((‖x‖ + x.re) / 2)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.norm_I`：‖Complex.I‖ = 1
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Real.sqrt_inv`：sqrt_inv (x : Real) : √x⁻¹ = (√x)⁻¹
· 使用定理 `Complex.ofReal_inv`：ofReal_inv (r : Real) : ((r⁻¹ : Real) : Complex) = (
r : Complex)⁻¹
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Complex.sqrt_I : sqrt (I : ℂ) = √2⁻¹ * (1 + I) := by
  rw [sqrt, ← re_add_im (I ^ 2⁻¹), cpow_inv_two_im_eq_sqrt (by simp), cpow_inv_two_re]
  simp [mul_add]
/-
**Complex.sqrt_neg_I** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Complex.sqrt_neg_I : sqrt (-I : Complex) = √2⁻¹ * (1 - I)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.sqrt.eq_1`：∀ (a : ℂ), a.sqrt = a ^ 2⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.re_add_im`：re_add_im (z : Complex) : (z.re : Complex) + z.im * I
 = z
· 使用引理 `Complex.cpow_inv_two_im_eq_neg_sqrt`：cpow_inv_two_im_eq_neg_sqrt {x : Co
mplex} (hx : x.im < 0) : (x ^ (2⁻¹ : Complex)).im = -√((‖x‖ - x.re) / 2)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `Complex.cpow_inv_two_re`：cpow_inv_two_re (x : Complex) : (x ^ (2⁻¹ : Com
plex)).re = √((‖x‖ + x.re) / 2)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `Complex.norm_I`：‖Complex.I‖ = 1
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Real.sqrt_inv`：sqrt_inv (x : Real) : √x⁻¹ = (√x)⁻¹
· 使用定理 `Complex.ofReal_inv`：ofReal_inv (r : Real) : ((r⁻¹ : Real) : Complex) = (
r : Complex)⁻¹
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Complex.sqrt_neg_I : sqrt (-I : ℂ) = √2⁻¹ * (1 - I) := by
  rw [sqrt, ← re_add_im ((-I) ^ 2⁻¹), cpow_inv_two_im_eq_neg_sqrt (by simp), cpow_inv_two_re]
  simp [mul_sub, ← sub_eq_add_neg]
/-
**RCLike.sqrt_I** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RCLike.sqrt_I : sqrt (I : 𝕜) = √2⁻¹ * (1 - I) * I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.sqrt_eq_ite`：RCLike.sqrt_eq_ite {a : 𝕜} : sqrt a = if h : im (I :
 𝕜) = 1 then (complexRingEquiv h).symm (complexRingEquiv h a).sqrt else √(re a)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingEquivClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type u_4} 
{S : Type u_5} [inst : EquivLike F R S] [inst_1 : NonUnitalNonAssocSemiring R]  
 [inst_2 : NonUnitalNonAssoc…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RCLike.complexRingEquiv_apply`：∀ {𝕜 : Type u_2} [inst : RCLike 𝕜] (h : R
CLike.im RCLike.I = 1) (x : 𝕜),   (RCLike.complexRingEquiv h) x = ↑(RCLike.re x)
 + ↑(RCLike.im x) *…
· 使用定理 `RCLike.I_re`：I_re : re (I : K) = 0
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Complex.sqrt_I`：Complex.sqrt_I : sqrt (I : Complex) = √2⁻¹ * (1 + I)
· 使用定理 `Real.sqrt_inv`：sqrt_inv (x : Real) : √x⁻¹ = (√x)⁻¹
· 使用定理 `Complex.ofReal_inv`：ofReal_inv (r : Real) : ((r⁻¹ : Real) : Complex) = (
r : Complex)⁻¹
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RCLike.ofReal_re`：ofReal_re : forall r : Real, re (r : K) = r
· 使用定理 `RCLike.ofReal_im`：ofReal_im : forall r : Real, im (r : K) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
（共 47 条，此处仅展示前 30 条）
-/
theorem RCLike.sqrt_I : sqrt (I : 𝕜) = √2⁻¹ * (1 - I) * I := by
  rw [sqrt_eq_ite]
  split_ifs with h
  · simp_rw [RingEquiv.symm_apply_eq, map_mul]
    simp [h, mul_assoc, mul_add, add_comm, Complex.sqrt_I, add_mul]
  grind [I_eq_zero_or_im_I_eq_one]
/-
**RCLike.sqrt_neg_I** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RCLike.sqrt_neg_I : sqrt (-I : 𝕜) = √2⁻¹ * (1 + I) * -I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.sqrt_eq_ite`：RCLike.sqrt_eq_ite {a : 𝕜} : sqrt a = if h : im (I :
 𝕜) = 1 then (complexRingEquiv h).symm (complexRingEquiv h a).sqrt else √(re a)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingEquivClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type u_4} 
{S : Type u_5} [inst : EquivLike F R S] [inst_1 : NonUnitalNonAssocSemiring R]  
 [inst_2 : NonUnitalNonAssoc…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RCLike.complexRingEquiv_apply`：∀ {𝕜 : Type u_2} [inst : RCLike 𝕜] (h : R
CLike.im RCLike.I = 1) (x : 𝕜),   (RCLike.complexRingEquiv h) x = ↑(RCLike.re x)
 + ↑(RCLike.im x) *…
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `RCLike.I_re`：I_re : re (I : K) = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Complex.sqrt_neg_I`：Complex.sqrt_neg_I : sqrt (-I : Complex) = √2⁻¹ * (1
 - I)
· 使用定理 `Real.sqrt_inv`：sqrt_inv (x : Real) : √x⁻¹ = (√x)⁻¹
· 使用定理 `Complex.ofReal_inv`：ofReal_inv (r : Real) : ((r⁻¹ : Real) : Complex) = (
r : Complex)⁻¹
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
（共 50 条，此处仅展示前 30 条）
-/
theorem RCLike.sqrt_neg_I : sqrt (-I : 𝕜) = √2⁻¹ * (1 + I) * -I := by
  rw [sqrt_eq_ite]
  split_ifs with h
  · simp_rw [RingEquiv.symm_apply_eq, map_mul]
    simp [h, mul_assoc, add_comm, Complex.sqrt_neg_I, neg_mul, mul_add, add_mul, mul_sub,
      mul_comm Complex.I, ← sub_eq_add_neg]
  grind [I_eq_zero_or_im_I_eq_one]
