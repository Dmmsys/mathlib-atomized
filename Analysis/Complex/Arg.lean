/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
module

public import Mathlib.Analysis.InnerProductSpace.Convex
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Rays in the complex numbers

This file links the definition `SameRay ℝ x y` with the equality of arguments of complex numbers,
the usual way this is considered.

## Main statements

* `Complex.sameRay_iff` : Two complex numbers are on the same ray iff one of them is zero, or they
  have the same argument.
* `Complex.abs_add_eq/Complex.abs_sub_eq`: If two nonzero complex numbers have the same argument,
  then the triangle inequality is an equality.

-/

public section


variable {x y : ℂ}

namespace Complex

-- see https://github.com/leanprover-community/mathlib4/issues/29041
set_option linter.unusedSimpArgs false in
/-
**Complex.sameRay_iff** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：sameRay_iff : SameRay Real x y ↔ x = 0 ∨ y = 0 ∨ x.arg = y.arg
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.arg_zero`：arg_zero : arg 0 = 0
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Complex.arg_eq_arg_iff`：arg_eq_arg_iff {x y : Complex} (hx : x != 0) (hy
 : y != 0) : arg x = arg y ↔ (‖y‖ / ‖x‖ : Complex) * x = y
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
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
（共 40 条，此处仅展示前 30 条）
-/
theorem sameRay_iff : SameRay ℝ x y ↔ x = 0 ∨ y = 0 ∨ x.arg = y.arg := by
  rcases eq_or_ne x 0 with (rfl | hx)
  · simp
  rcases eq_or_ne y 0 with (rfl | hy)
  · simp
  simp only [hx, hy, sameRay_iff_norm_smul_eq, arg_eq_arg_iff hx hy]
  simp [field, hx, mul_comm, eq_comm]
/-
**Complex.sameRay_iff_arg_div_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：sameRay_iff_arg_div_eq_zero : SameRay Real x y ↔ arg (x / y) = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.Angle.toReal_zero`：toReal_zero : (0 : Angle).toReal = 0
· 使用定理 `Complex.arg_coe_angle_eq_iff_eq_toReal`：arg_coe_angle_eq_iff_eq_toReal {
z : Complex} {θ : Real.Angle} : (arg z : Real.Angle) = θ ↔ arg z = θ.toReal
· 使用定理 `Complex.sameRay_iff`：sameRay_iff : SameRay Real x y ↔ x = 0 ∨ y = 0 ∨ x.
arg = y.arg
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Complex.arg_zero`：arg_zero : arg 0 = 0
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Complex.arg_div_coe_angle`：arg_div_coe_angle {x y : Complex} (hx : x != 
0) (hy : y != 0) : (arg (x / y) : Real.Angle) = arg x - arg y
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem sameRay_iff_arg_div_eq_zero : SameRay ℝ x y ↔ arg (x / y) = 0 := by
  rw [← Real.Angle.toReal_zero, ← arg_coe_angle_eq_iff_eq_toReal, sameRay_iff]
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  simp [hx, hy, arg_div_coe_angle, sub_eq_zero]
/-
**Complex.norm_add_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：norm_add_eq_iff : ‖x + y‖ = ‖x‖ + ‖y‖ ↔ x = 0 ∨ y = 0 ∨ x.arg = y.arg
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `sameRay_iff_norm_add`：sameRay_iff_norm_add : SameRay Real x y ↔ ‖x + y‖ 
= ‖x‖ + ‖y‖
· 使用定理 `UniformConvexSpace.toStrictConvexSpace`：∀ {E : Type u_1} [inst : NormedA
ddCommGroup E] [inst_1 : NormedSpace ℝ E] [UniformConvexSpace E], StrictConvexSp
ace ℝ E
· 使用定理 `InnerProductSpace.toUniformConvexSpace`：∀ {F : Type u_3} [inst : Seminor
medAddCommGroup F] [InnerProductSpace ℝ F], UniformConvexSpace F
· 使用定理 `Complex.sameRay_iff`：sameRay_iff : SameRay Real x y ↔ x = 0 ∨ y = 0 ∨ x.
arg = y.arg
-/
theorem norm_add_eq_iff : ‖x + y‖ = ‖x‖ + ‖y‖ ↔ x = 0 ∨ y = 0 ∨ x.arg = y.arg :=
  sameRay_iff_norm_add.symm.trans sameRay_iff
/-
**Complex.norm_sub_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：norm_sub_eq_iff : ‖x - y‖ = |‖x‖ - ‖y‖| ↔ x = 0 ∨ y = 0 ∨ x.arg = y.arg
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `sameRay_iff_norm_sub`：sameRay_iff_norm_sub : SameRay Real x y ↔ ‖x - y‖ 
= |‖x‖ - ‖y‖|
· 使用定理 `UniformConvexSpace.toStrictConvexSpace`：∀ {E : Type u_1} [inst : NormedA
ddCommGroup E] [inst_1 : NormedSpace ℝ E] [UniformConvexSpace E], StrictConvexSp
ace ℝ E
· 使用定理 `InnerProductSpace.toUniformConvexSpace`：∀ {F : Type u_3} [inst : Seminor
medAddCommGroup F] [InnerProductSpace ℝ F], UniformConvexSpace F
· 使用定理 `Complex.sameRay_iff`：sameRay_iff : SameRay Real x y ↔ x = 0 ∨ y = 0 ∨ x.
arg = y.arg
-/
theorem norm_sub_eq_iff : ‖x - y‖ = |‖x‖ - ‖y‖| ↔ x = 0 ∨ y = 0 ∨ x.arg = y.arg :=
  sameRay_iff_norm_sub.symm.trans sameRay_iff
/-
**Complex.sameRay_of_arg_eq** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：sameRay_of_arg_eq (h : x.arg = y.arg) : SameRay Real x y
参数：h : x.arg = y.arg。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Complex.sameRay_iff`：sameRay_iff : SameRay Real x y ↔ x = 0 ∨ y = 0 ∨ x.
arg = y.arg
-/
theorem sameRay_of_arg_eq (h : x.arg = y.arg) : SameRay ℝ x y :=
  sameRay_iff.mpr <| Or.inr <| Or.inr h
/-
**Complex.norm_add_eq** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：norm_add_eq (h : x.arg = y.arg) : ‖x + y‖ = ‖x‖ + ‖y‖
参数：h : x.arg = y.arg。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SameRay.norm_add`：norm_add (h : SameRay Real x y) : ‖x + y‖ = ‖x‖ + ‖y‖
· 使用定理 `Complex.sameRay_of_arg_eq`：sameRay_of_arg_eq (h : x.arg = y.arg) : SameR
ay Real x y
-/
theorem norm_add_eq (h : x.arg = y.arg) : ‖x + y‖ = ‖x‖ + ‖y‖ :=
  (sameRay_of_arg_eq h).norm_add
/-
**Complex.norm_sub_eq** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：norm_sub_eq (h : x.arg = y.arg) : ‖x - y‖ = ‖‖x‖ - ‖y‖‖
参数：h : x.arg = y.arg。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SameRay.norm_sub`：norm_sub (h : SameRay Real x y) : ‖x - y‖ = |‖x‖ - ‖y‖
|
· 使用定理 `Complex.sameRay_of_arg_eq`：sameRay_of_arg_eq (h : x.arg = y.arg) : SameR
ay Real x y
-/
theorem norm_sub_eq (h : x.arg = y.arg) : ‖x - y‖ = ‖‖x‖ - ‖y‖‖ :=
  (sameRay_of_arg_eq h).norm_sub

end Complex

