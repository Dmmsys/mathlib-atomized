/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-!
# Angle between complex numbers

This file relates the Euclidean geometric notion of angle between complex numbers to the argument of
their quotient.

It also shows that the arc and chord distances between two unit complex numbers are equivalent up to
a factor of `π / 2`.

## TODO

Prove the corresponding results for oriented angles.

## Tags

arc-length, arc-distance
-/

public section

open InnerProductGeometry Set
open scoped Real

namespace Complex
variable {a x y : ℂ}

/-- The angle between two non-zero complex numbers is the absolute value of the argument of their
quotient.

Note that this does not hold when `x` or `y` is `0` as the LHS is `π / 2` while the RHS is `0`. -/
/-
**Complex.angle_eq_abs_arg** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：angle_eq_abs_arg (hx : x != 0) (hy : y != 0) : angle x y = |(x / y).arg|
参数：hx : x != 0；hy : y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.arccos_eq_of_eq_cos`：arccos_eq_of_eq_cos (hy₀ : 0 <= y) (hy₁ : y <=
 π) (hxy : x = cos y) : arccos x = y
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Complex.abs_arg_le_pi`：abs_arg_le_pi (z : Complex) : |arg z| <= π
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.cos_abs`：cos_abs : cos |x| = cos x
· 使用定理 `Complex.cos_arg`：cos_arg {x : Complex} (hx : x != 0) : Real.cos (arg x) 
= x.re / ‖x‖
· 使用定理 `div_ne_zero`：div_ne_zero (ha : a != 0) (hb : b != 0) : a / b != 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `Complex.inv_re`：inv_re (z : Complex) : z⁻¹.re = z.re / normSq z
· 使用引理 `Complex.normSq_eq_norm_sq`：normSq_eq_norm_sq (z : Complex) : normSq z = 
‖z‖ ^ 2
· 使用定理 `Complex.inv_im`：inv_im (z : Complex) : z⁻¹.im = -z.im / normSq z
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Complex.norm_mul`：∀ (z w : ℂ), ‖z * w‖ = ‖z‖ * ‖w‖
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
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
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
（共 71 条，此处仅展示前 30 条）

--- 原说明 ---
The angle between two non-zero complex numbers is the absolute value of the argu
ment of their
quotient.

Note that this does not hold when `x` or `y` is `0` as the LHS is `π / 2` while 
the RHS is `0`.
-/
lemma angle_eq_abs_arg (hx : x ≠ 0) (hy : y ≠ 0) : angle x y = |(x / y).arg| := by
  refine Real.arccos_eq_of_eq_cos (abs_nonneg _) (abs_arg_le_pi _) ?_
  rw [Real.cos_abs, Complex.cos_arg (div_ne_zero hx hy)]
  simp [div_eq_mul_inv, Complex.normSq_eq_norm_sq]
  field
/-
**Complex.angle_one_left** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：angle_one_left (hy : y != 0) : angle 1 y = |y.arg|
参数：hy : y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Complex.angle_eq_abs_arg`：angle_eq_abs_arg (hx : x != 0) (hy : y != 0) :
 angle x y = |(x / y).arg|
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Complex.abs_arg_inv`：∀ (x : ℂ), |x⁻¹.arg| = |x.arg|
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma angle_one_left (hy : y ≠ 0) : angle 1 y = |y.arg| := by simp [angle_eq_abs_arg, hy]
/-
**Complex.angle_one_right** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：angle_one_right (hx : x != 0) : angle x 1 = |x.arg|
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Complex.angle_eq_abs_arg`：angle_eq_abs_arg (hx : x != 0) (hy : y != 0) :
 angle x y = |(x / y).arg|
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma angle_one_right (hx : x ≠ 0) : angle x 1 = |x.arg| := by simp [angle_eq_abs_arg, hx]
/-
**Complex.angle_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ {a : ℂ}, a ≠ 0 → ∀ (x y : ℂ), InnerProductGeometry.angle (a * x) (a * y)
 = InnerProductGeometry.angle x y
参数：x y : ℂ；a * x；a * y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `InnerProductGeometry.angle_zero_right`：angle_zero_right (x : V) : angle 
x 0 = π / 2
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `InnerProductGeometry.angle_zero_left`：angle_zero_left (x : V) : angle 0 
x = π / 2
· 使用引理 `Complex.angle_eq_abs_arg`：angle_eq_abs_arg (hx : x != 0) (hy : y != 0) :
 angle x y = |(x / y).arg|
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `mul_div_mul_left`：mul_div_mul_left (a b : G₀) (hc : c != 0) : c * a / (c
 * b) = a / b
-/
@[simp] lemma angle_mul_left (ha : a ≠ 0) (x y : ℂ) : angle (a * x) (a * y) = angle x y := by
  obtain rfl | hx := eq_or_ne x 0 <;> obtain rfl | hy := eq_or_ne y 0 <;>
    simp [angle_eq_abs_arg, mul_div_mul_left, *]
/-
**Complex.angle_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ {a : ℂ}, a ≠ 0 → ∀ (x y : ℂ), InnerProductGeometry.angle (x * a) (y * a)
 = InnerProductGeometry.angle x y
参数：x y : ℂ；x * a；y * a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Complex.angle_mul_left`：∀ {a : ℂ}, a ≠ 0 → ∀ (x y : ℂ), InnerProductGeom
etry.angle (a * x) (a * y) = InnerProductGeometry.angle x y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma angle_mul_right (ha : a ≠ 0) (x y : ℂ) : angle (x * a) (y * a) = angle x y := by
  simp [mul_comm, angle_mul_left ha]
/-
**Complex.angle_div_left_eq_angle_mul_right** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：angle_div_left_eq_angle_mul_right (a x y : Complex) : angle (x / a) y = an
gle x (y * a)
参数：a x y : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `InnerProductGeometry.angle_zero_left`：angle_zero_left (x : V) : angle 0 
x = π / 2
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `InnerProductGeometry.angle_zero_right`：angle_zero_right (x : V) : angle 
x 0 = π / 2
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.angle_mul_right`：∀ {a : ℂ}, a ≠ 0 → ∀ (x y : ℂ), InnerProductGeo
metry.angle (x * a) (y * a) = InnerProductGeometry.angle x y
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
-/
lemma angle_div_left_eq_angle_mul_right (a x y : ℂ) : angle (x / a) y = angle x (y * a) := by
  obtain rfl | ha := eq_or_ne a 0
  · simp
  · rw [← angle_mul_right ha, div_mul_cancel₀ _ ha]
/-
**Complex.angle_div_right_eq_angle_mul_left** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：angle_div_right_eq_angle_mul_left (a x y : Complex) : angle x (y / a) = an
gle (x * a) y
参数：a x y : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InnerProductGeometry.angle_comm`：angle_comm (x y : V) : angle x y = angl
e y x
· 使用引理 `Complex.angle_div_left_eq_angle_mul_right`：angle_div_left_eq_angle_mul_r
ight (a x y : Complex) : angle (x / a) y = angle x (y * a)
-/
lemma angle_div_right_eq_angle_mul_left (a x y : ℂ) : angle x (y / a) = angle (x * a) y := by
  rw [angle_comm, angle_div_left_eq_angle_mul_right, angle_comm]
/-
**Complex.angle_exp_exp** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：angle_exp_exp (x y : Real) : angle (exp (x * I)) (exp (y * I)) = |toIocMod
 Real.two_pi_pos (-π) (x - y)|
参数：x y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.two_pi_pos`：two_pi_pos : 0 < 2 * π
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Complex.angle_eq_abs_arg`：angle_eq_abs_arg (hx : x != 0) (hy : y != 0) :
 angle x y = |(x / y).arg|
· 使用定理 `Complex.exp_ne_zero`：exp_ne_zero : exp x != 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Complex.arg_exp_mul_I`：arg_exp_mul_I (θ : Real) : arg (exp (θ * I)) = to
IocMod Real.two_pi_pos (-π) θ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma angle_exp_exp (x y : ℝ) :
    angle (exp (x * I)) (exp (y * I)) = |toIocMod Real.two_pi_pos (-π) (x - y)| := by
  simp_rw [angle_eq_abs_arg (exp_ne_zero _) (exp_ne_zero _), ← exp_sub, ← sub_mul, ← ofReal_sub,
    arg_exp_mul_I]
/-
**Complex.angle_exp_one** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：angle_exp_one (x : Real) : angle (exp (x * I)) 1 = |toIocMod Real.two_pi_p
os (-π) x|
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.two_pi_pos`：two_pi_pos : 0 < 2 * π
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Complex.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `toIocMod.congr_simp`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [inst_2 : IsOrderedAddMonoid α] [hα : Archimedean α]   {p p_1 : α
} (e_p : …
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用引理 `Complex.angle_exp_exp`：angle_exp_exp (x y : Real) : angle (exp (x * I)) 
(exp (y * I)) = |toIocMod Real.two_pi_pos (-π) (x - y)|
-/
lemma angle_exp_one (x : ℝ) : angle (exp (x * I)) 1 = |toIocMod Real.two_pi_pos (-π) x| := by
  simpa using angle_exp_exp x 0

/-!
### Arc-length and chord-length are equivalent

This section shows that the arc and chord distances between two unit complex numbers are equivalent
up to a factor of `π / 2`.
-/

/-- Chord-length is a multiple of arc-length up to constants. -/
/-
**Complex.norm_sub_mem_Icc_angle** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：norm_sub_mem_Icc_angle (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : ‖x - y‖ in Icc (2 /
 π * angle x y) (angle x y)
参数：hx : ‖x‖ = 1；hy : ‖y‖ = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Complex.norm_eq_one_iff'`：norm_eq_one_iff' : ‖x‖ = 1 ↔ exists θ in Set.I
oc (-π) π, exp (θ * I) = x
· 使用定理 `Real.two_pi_pos`：two_pi_pos : 0 < 2 * π
· 使用引理 `Complex.angle_exp_one`：angle_exp_one (x : Real) : angle (exp (x * I)) 1 
= |toIocMod Real.two_pi_pos (-π) x|
· 使用定理 `Complex.exp_mul_I`：exp_mul_I : exp (x * I) = cos x + sin x * I
· 使用定理 `add_sub_right_comm`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a
 b c : α), a + b - c = a - c + b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `toIocMod_eq_self`：toIocMod_eq_self : toIocMod hp a b = b ↔ b in Set.Ioc 
a (a + p)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
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
（共 126 条，此处仅展示前 30 条）

--- 原说明 ---
Chord-length is a multiple of arc-length up to constants.
-/
lemma norm_sub_mem_Icc_angle (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ‖x - y‖ ∈ Icc (2 / π * angle x y) (angle x y) := by
  wlog h : y = 1
  · have := @this (x / y) 1 (by simp only [norm_div, hx, hy, div_one]) norm_one rfl
    rwa [angle_div_left_eq_angle_mul_right, div_sub_one, norm_div, hy, div_one, one_mul]
      at this
    rintro rfl
    simp at hy
  subst y
  rw [norm_eq_one_iff'] at hx
  obtain ⟨θ, hθ, rfl⟩ := hx
  rw [angle_exp_one, exp_mul_I, add_sub_right_comm, (toIocMod_eq_self _).2]
  · norm_cast
    rw [norm_add_mul_I]
    refine ⟨Real.le_sqrt_of_sq_le ?_, ?_⟩
    · rw [mul_pow, ← abs_pow, abs_sq]
      calc
        _ = 2 * (1 - (1 - 2 / π ^ 2 * θ ^ 2)) := by ring
        _ ≤ 2 * (1 - θ.cos) := by
            gcongr; exact Real.cos_le_one_sub_mul_cos_sq <| abs_le.2 <| Ioc_subset_Icc_self hθ
        _ = _ := by linear_combination -θ.cos_sq_add_sin_sq
    · rw [Real.sqrt_le_left (by positivity), ← abs_pow, abs_sq]
      calc
        _ = 2 * (1 - θ.cos) := by linear_combination θ.cos_sq_add_sin_sq
        _ ≤ 2 * (1 - (1 - θ ^ 2 / 2)) := by gcongr; exact Real.one_sub_sq_div_two_le_cos
        _ = _ := by ring
  · convert! hθ
    ring

/-- Chord-length is always less than arc-length. -/
/-
**Complex.norm_sub_le_angle** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：norm_sub_le_angle (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : ‖x - y‖ <= angle x y
参数：hx : ‖x‖ = 1；hy : ‖y‖ = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Complex.norm_sub_mem_Icc_angle`：norm_sub_mem_Icc_angle (hx : ‖x‖ = 1) (h
y : ‖y‖ = 1) : ‖x - y‖ in Icc (2 / π * angle x y) (angle x y)

--- 原说明 ---
Chord-length is always less than arc-length.
-/
lemma norm_sub_le_angle (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : ‖x - y‖ ≤ angle x y :=
  (norm_sub_mem_Icc_angle hx hy).2

/-- Chord-length is always greater than a multiple of arc-length. -/
/-
**Complex.mul_angle_le_norm_sub** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：mul_angle_le_norm_sub (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : 2 / π * angle x y <=
 ‖x - y‖
参数：hx : ‖x‖ = 1；hy : ‖y‖ = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Complex.norm_sub_mem_Icc_angle`：norm_sub_mem_Icc_angle (hx : ‖x‖ = 1) (h
y : ‖y‖ = 1) : ‖x - y‖ in Icc (2 / π * angle x y) (angle x y)

--- 原说明 ---
Chord-length is always greater than a multiple of arc-length.
-/
lemma mul_angle_le_norm_sub (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : 2 / π * angle x y ≤ ‖x - y‖ :=
  (norm_sub_mem_Icc_angle hx hy).1

/-- Arc-length is always less than a multiple of chord-length. -/
/-
**Complex.angle_le_mul_norm_sub** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：angle_le_mul_norm_sub (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : angle x y <= π / 2 *
 ‖x - y‖
参数：hx : ‖x‖ = 1；hy : ‖y‖ = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `div_le_iff₀'`：div_le_iff₀' (hc : 0 < c) : b / c <= a ↔ b <= c * a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
· 使用引理 `Complex.mul_angle_le_norm_sub`：mul_angle_le_norm_sub (hx : ‖x‖ = 1) (hy 
: ‖y‖ = 1) : 2 / π * angle x y <= ‖x - y‖

--- 原说明 ---
Arc-length is always less than a multiple of chord-length.
-/
lemma angle_le_mul_norm_sub (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : angle x y ≤ π / 2 * ‖x - y‖ := by
  rw [← div_le_iff₀' <| by positivity, div_eq_inv_mul, inv_div]; exact mul_angle_le_norm_sub hx hy

end Complex

