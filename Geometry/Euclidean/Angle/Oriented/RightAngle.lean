/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.RightAngle

/-!
# Oriented angles in right-angled triangles.

This file proves basic geometric results about distances and oriented angles in (possibly
degenerate) right-angled triangles in real inner product spaces and Euclidean affine spaces.

-/

public section


noncomputable section

open scoped EuclideanGeometry

open scoped Real

open scoped RealInnerProductSpace

namespace Orientation

open Module

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [hd2 : Fact (finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2))

/-- An angle in a right-angled triangle expressed using `arccos`. -/
/-
**Orientation.oangle_add_right_eq_arccos_of_oangle_eq_pi_div_two** 是 Mathlib 中的一
个定理，位于命名空间 `Orientation`。
形式化陈述：oangle_add_right_eq_arccos_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle
 x y = ↑(π / 2)) : o.oangle x (x + y) = Real.arccos (‖x‖ / ‖x + y‖)
参数：h : o.oangle x y = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_sign_add_right`：oangle_sign_add_right (x y : V) : (o.
oangle x (x + y)).sign = (o.oangle x y).sign
· 使用定理 `Real.Angle.sign_coe_pi_div_two`：sign_coe_pi_div_two : (↑(π / 2) : Angle)
.sign = 1
· 使用定理 `Orientation.oangle_eq_angle_of_sign_eq_one`：oangle_eq_angle_of_sign_eq_o
ne {x y : V} (h : (o.oangle x y).sign = 1) : o.oangle x y = InnerProductGeometry
.angle x y
· 使用定理 `InnerProductGeometry.angle_add_eq_arccos_of_inner_eq_zero`：angle_add_eq_
arccos_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) : angle x (x + y) = Real.arcc
os (‖x‖ / ‖x + y‖)
· 使用定理 `Orientation.inner_eq_zero_of_oangle_eq_pi_div_two`：inner_eq_zero_of_oang
le_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : Real)) : ⟪x, y⟫ = 0

--- 原说明 ---
An angle in a right-angled triangle expressed using `arccos`.
-/
theorem oangle_add_right_eq_arccos_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle x (x + y) = Real.arccos (‖x‖ / ‖x + y‖) := by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs,
    InnerProductGeometry.angle_add_eq_arccos_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_div_two h)]

/-- An angle in a right-angled triangle expressed using `arccos`. -/
/-
**Orientation.oangle_add_left_eq_arccos_of_oangle_eq_pi_div_two** 是 Mathlib 中的一个
定理，位于命名空间 `Orientation`。
形式化陈述：oangle_add_left_eq_arccos_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle 
x y = ↑(π / 2)) : o.oangle (x + y) y = Real.arccos (‖y‖ / ‖x + y‖)
参数：h : o.oangle x y = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b
· 使用定理 `Orientation.oangle_rev`：oangle_rev (x y : V) : o.oangle y x = -o.oangle 
x y
· 使用定理 `Orientation.oangle_neg_orientation_eq_neg`：oangle_neg_orientation_eq_neg
 (x y : V) : (-o).oangle x y = -o.oangle x y
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Orientation.oangle_add_right_eq_arccos_of_oangle_eq_pi_div_two`：oangle_a
dd_right_eq_arccos_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2
)) : o.oangle x (x + y) = Real.arccos (‖x‖ / ‖x + y‖…

--- 原说明 ---
An angle in a right-angled triangle expressed using `arccos`.
-/
theorem oangle_add_left_eq_arccos_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle (x + y) y = Real.arccos (‖y‖ / ‖x + y‖) := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).oangle_add_right_eq_arccos_of_oangle_eq_pi_div_two h

/-- An angle in a right-angled triangle expressed using `arcsin`. -/
/-
**Orientation.oangle_add_right_eq_arcsin_of_oangle_eq_pi_div_two** 是 Mathlib 中的一
个定理，位于命名空间 `Orientation`。
形式化陈述：oangle_add_right_eq_arcsin_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle
 x y = ↑(π / 2)) : o.oangle x (x + y) = Real.arcsin (‖y‖ / ‖x + y‖)
参数：h : o.oangle x y = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_sign_add_right`：oangle_sign_add_right (x y : V) : (o.
oangle x (x + y)).sign = (o.oangle x y).sign
· 使用定理 `Real.Angle.sign_coe_pi_div_two`：sign_coe_pi_div_two : (↑(π / 2) : Angle)
.sign = 1
· 使用定理 `Orientation.oangle_eq_angle_of_sign_eq_one`：oangle_eq_angle_of_sign_eq_o
ne {x y : V} (h : (o.oangle x y).sign = 1) : o.oangle x y = InnerProductGeometry
.angle x y
· 使用定理 `InnerProductGeometry.angle_add_eq_arcsin_of_inner_eq_zero`：angle_add_eq_
arcsin_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0 ∨ y != 0) : angl
e x (x + y) = Real.arcsin (‖y‖ / ‖x + y‖)
· 使用定理 `Orientation.inner_eq_zero_of_oangle_eq_pi_div_two`：inner_eq_zero_of_oang
le_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : Real)) : ⟪x, y⟫ = 0
· 使用定理 `Orientation.left_ne_zero_of_oangle_eq_pi_div_two`：left_ne_zero_of_oangle
_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : Real)) : x != 0

--- 原说明 ---
An angle in a right-angled triangle expressed using `arcsin`.
-/
theorem oangle_add_right_eq_arcsin_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle x (x + y) = Real.arcsin (‖y‖ / ‖x + y‖) := by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs,
    InnerProductGeometry.angle_add_eq_arcsin_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_div_two h)
      (Or.inl (o.left_ne_zero_of_oangle_eq_pi_div_two h))]

/-- An angle in a right-angled triangle expressed using `arcsin`. -/
/-
**Orientation.oangle_add_left_eq_arcsin_of_oangle_eq_pi_div_two** 是 Mathlib 中的一个
定理，位于命名空间 `Orientation`。
形式化陈述：oangle_add_left_eq_arcsin_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle 
x y = ↑(π / 2)) : o.oangle (x + y) y = Real.arcsin (‖x‖ / ‖x + y‖)
参数：h : o.oangle x y = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b
· 使用定理 `Orientation.oangle_rev`：oangle_rev (x y : V) : o.oangle y x = -o.oangle 
x y
· 使用定理 `Orientation.oangle_neg_orientation_eq_neg`：oangle_neg_orientation_eq_neg
 (x y : V) : (-o).oangle x y = -o.oangle x y
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Orientation.oangle_add_right_eq_arcsin_of_oangle_eq_pi_div_two`：oangle_a
dd_right_eq_arcsin_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2
)) : o.oangle x (x + y) = Real.arcsin (‖y‖ / ‖x + y‖…

--- 原说明 ---
An angle in a right-angled triangle expressed using `arcsin`.
-/
theorem oangle_add_left_eq_arcsin_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle (x + y) y = Real.arcsin (‖x‖ / ‖x + y‖) := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).oangle_add_right_eq_arcsin_of_oangle_eq_pi_div_two h

/-- An angle in a right-angled triangle expressed using `arctan`. -/
/-
**Orientation.oangle_add_right_eq_arctan_of_oangle_eq_pi_div_two** 是 Mathlib 中的一
个定理，位于命名空间 `Orientation`。
形式化陈述：oangle_add_right_eq_arctan_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle
 x y = ↑(π / 2)) : o.oangle x (x + y) = Real.arctan (‖y‖ / ‖x‖)
参数：h : o.oangle x y = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_sign_add_right`：oangle_sign_add_right (x y : V) : (o.
oangle x (x + y)).sign = (o.oangle x y).sign
· 使用定理 `Real.Angle.sign_coe_pi_div_two`：sign_coe_pi_div_two : (↑(π / 2) : Angle)
.sign = 1
· 使用定理 `Orientation.oangle_eq_angle_of_sign_eq_one`：oangle_eq_angle_of_sign_eq_o
ne {x y : V} (h : (o.oangle x y).sign = 1) : o.oangle x y = InnerProductGeometry
.angle x y
· 使用定理 `InnerProductGeometry.angle_add_eq_arctan_of_inner_eq_zero`：angle_add_eq_
arctan_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0) : angle x (x + 
y) = Real.arctan (‖y‖ / ‖x‖)
· 使用定理 `Orientation.inner_eq_zero_of_oangle_eq_pi_div_two`：inner_eq_zero_of_oang
le_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : Real)) : ⟪x, y⟫ = 0
· 使用定理 `Orientation.left_ne_zero_of_oangle_eq_pi_div_two`：left_ne_zero_of_oangle
_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : Real)) : x != 0

--- 原说明 ---
An angle in a right-angled triangle expressed using `arctan`.
-/
theorem oangle_add_right_eq_arctan_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle x (x + y) = Real.arctan (‖y‖ / ‖x‖) := by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs,
    InnerProductGeometry.angle_add_eq_arctan_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_div_two h) (o.left_ne_zero_of_oangle_eq_pi_div_two h)]

/-- An angle in a right-angled triangle expressed using `arctan`. -/
/-
**Orientation.oangle_add_left_eq_arctan_of_oangle_eq_pi_div_two** 是 Mathlib 中的一个
定理，位于命名空间 `Orientation`。
形式化陈述：oangle_add_left_eq_arctan_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle 
x y = ↑(π / 2)) : o.oangle (x + y) y = Real.arctan (‖x‖ / ‖y‖)
参数：h : o.oangle x y = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b
· 使用定理 `Orientation.oangle_rev`：oangle_rev (x y : V) : o.oangle y x = -o.oangle 
x y
· 使用定理 `Orientation.oangle_neg_orientation_eq_neg`：oangle_neg_orientation_eq_neg
 (x y : V) : (-o).oangle x y = -o.oangle x y
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Orientation.oangle_add_right_eq_arctan_of_oangle_eq_pi_div_two`：oangle_a
dd_right_eq_arctan_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2
)) : o.oangle x (x + y) = Real.arctan (‖y‖ / ‖x‖)

--- 原说明 ---
An angle in a right-angled triangle expressed using `arctan`.
-/
theorem oangle_add_left_eq_arctan_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle (x + y) y = Real.arctan (‖x‖ / ‖y‖) := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).oangle_add_right_eq_arctan_of_oangle_eq_pi_div_two h

/-- The cosine of an angle in a right-angled triangle as a ratio of sides. -/
/-
**Orientation.cos_oangle_add_right_of_oangle_eq_pi_div_two** 是 Mathlib 中的一个定理，位于
命名空间 `Orientation`。
形式化陈述：cos_oangle_add_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y =
 ↑(π / 2)) : Real.Angle.cos (o.oangle x (x + y)) = ‖x‖ / ‖x + y‖
参数：h : o.oangle x y = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_sign_add_right`：oangle_sign_add_right (x y : V) : (o.
oangle x (x + y)).sign = (o.oangle x y).sign
· 使用定理 `Real.Angle.sign_coe_pi_div_two`：sign_coe_pi_div_two : (↑(π / 2) : Angle)
.sign = 1
· 使用定理 `Orientation.oangle_eq_angle_of_sign_eq_one`：oangle_eq_angle_of_sign_eq_o
ne {x y : V} (h : (o.oangle x y).sign = 1) : o.oangle x y = InnerProductGeometry
.angle x y
· 使用定理 `Real.Angle.cos_coe`：cos_coe (x : Real) : cos (x : Angle) = Real.cos x
· 使用定理 `InnerProductGeometry.cos_angle_add_of_inner_eq_zero`：cos_angle_add_of_in
ner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) : Real.cos (angle x (x + y)) = ‖x‖ / ‖x +
 y‖
· 使用定理 `Orientation.inner_eq_zero_of_oangle_eq_pi_div_two`：inner_eq_zero_of_oang
le_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : Real)) : ⟪x, y⟫ = 0

--- 原说明 ---
The cosine of an angle in a right-angled triangle as a ratio of sides.
-/
theorem cos_oangle_add_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.cos (o.oangle x (x + y)) = ‖x‖ / ‖x + y‖ := by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs, Real.Angle.cos_coe,
    InnerProductGeometry.cos_angle_add_of_inner_eq_zero (o.inner_eq_zero_of_oangle_eq_pi_div_two h)]

/-- The cosine of an angle in a right-angled triangle as a ratio of sides. -/
/-
**Orientation.cos_oangle_add_left_of_oangle_eq_pi_div_two** 是 Mathlib 中的一个定理，位于命
名空间 `Orientation`。
形式化陈述：cos_oangle_add_left_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = 
↑(π / 2)) : Real.Angle.cos (o.oangle (x + y) y) = ‖y‖ / ‖x + y‖
参数：h : o.oangle x y = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b
· 使用定理 `Orientation.oangle_rev`：oangle_rev (x y : V) : o.oangle y x = -o.oangle 
x y
· 使用定理 `Orientation.oangle_neg_orientation_eq_neg`：oangle_neg_orientation_eq_neg
 (x y : V) : (-o).oangle x y = -o.oangle x y
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Orientation.cos_oangle_add_right_of_oangle_eq_pi_div_two`：cos_oangle_add
_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) : Real.An
gle.cos (o.oangle x (x + y)) = ‖x‖ / ‖x + y‖

--- 原说明 ---
The cosine of an angle in a right-angled triangle as a ratio of sides.
-/
theorem cos_oangle_add_left_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.cos (o.oangle (x + y) y) = ‖y‖ / ‖x + y‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).cos_oangle_add_right_of_oangle_eq_pi_div_two h

/-- The sine of an angle in a right-angled triangle as a ratio of sides. -/
/-
**Orientation.sin_oangle_add_right_of_oangle_eq_pi_div_two** 是 Mathlib 中的一个定理，位于
命名空间 `Orientation`。
形式化陈述：sin_oangle_add_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y =
 ↑(π / 2)) : Real.Angle.sin (o.oangle x (x + y)) = ‖y‖ / ‖x + y‖
参数：h : o.oangle x y = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_sign_add_right`：oangle_sign_add_right (x y : V) : (o.
oangle x (x + y)).sign = (o.oangle x y).sign
· 使用定理 `Real.Angle.sign_coe_pi_div_two`：sign_coe_pi_div_two : (↑(π / 2) : Angle)
.sign = 1
· 使用定理 `Orientation.oangle_eq_angle_of_sign_eq_one`：oangle_eq_angle_of_sign_eq_o
ne {x y : V} (h : (o.oangle x y).sign = 1) : o.oangle x y = InnerProductGeometry
.angle x y
· 使用定理 `Real.Angle.sin_coe`：sin_coe (x : Real) : sin (x : Angle) = Real.sin x
· 使用定理 `InnerProductGeometry.sin_angle_add_of_inner_eq_zero`：sin_angle_add_of_in
ner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0 ∨ y != 0) : Real.sin (angle 
x (x + y)) = ‖y‖ / ‖x + y‖
· 使用定理 `Orientation.inner_eq_zero_of_oangle_eq_pi_div_two`：inner_eq_zero_of_oang
le_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : Real)) : ⟪x, y⟫ = 0
· 使用定理 `Orientation.left_ne_zero_of_oangle_eq_pi_div_two`：left_ne_zero_of_oangle
_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : Real)) : x != 0

--- 原说明 ---
The sine of an angle in a right-angled triangle as a ratio of sides.
-/
theorem sin_oangle_add_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.sin (o.oangle x (x + y)) = ‖y‖ / ‖x + y‖ := by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs, Real.Angle.sin_coe,
    InnerProductGeometry.sin_angle_add_of_inner_eq_zero (o.inner_eq_zero_of_oangle_eq_pi_div_two h)
      (Or.inl (o.left_ne_zero_of_oangle_eq_pi_div_two h))]

/-- The sine of an angle in a right-angled triangle as a ratio of sides. -/
/-
**Orientation.sin_oangle_add_left_of_oangle_eq_pi_div_two** 是 Mathlib 中的一个定理，位于命
名空间 `Orientation`。
形式化陈述：sin_oangle_add_left_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = 
↑(π / 2)) : Real.Angle.sin (o.oangle (x + y) y) = ‖x‖ / ‖x + y‖
参数：h : o.oangle x y = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b
· 使用定理 `Orientation.oangle_rev`：oangle_rev (x y : V) : o.oangle y x = -o.oangle 
x y
· 使用定理 `Orientation.oangle_neg_orientation_eq_neg`：oangle_neg_orientation_eq_neg
 (x y : V) : (-o).oangle x y = -o.oangle x y
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Orientation.sin_oangle_add_right_of_oangle_eq_pi_div_two`：sin_oangle_add
_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) : Real.An
gle.sin (o.oangle x (x + y)) = ‖y‖ / ‖x + y‖

--- 原说明 ---
The sine of an angle in a right-angled triangle as a ratio of sides.
-/
theorem sin_oangle_add_left_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.sin (o.oangle (x + y) y) = ‖x‖ / ‖x + y‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).sin_oangle_add_right_of_oangle_eq_pi_div_two h

/-- The tangent of an angle in a right-angled triangle as a ratio of sides. -/
/-
**Orientation.tan_oangle_add_right_of_oangle_eq_pi_div_two** 是 Mathlib 中的一个定理，位于
命名空间 `Orientation`。
形式化陈述：tan_oangle_add_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y =
 ↑(π / 2)) : Real.Angle.tan (o.oangle x (x + y)) = ‖y‖ / ‖x‖
参数：h : o.oangle x y = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_sign_add_right`：oangle_sign_add_right (x y : V) : (o.
oangle x (x + y)).sign = (o.oangle x y).sign
· 使用定理 `Real.Angle.sign_coe_pi_div_two`：sign_coe_pi_div_two : (↑(π / 2) : Angle)
.sign = 1
· 使用定理 `Orientation.oangle_eq_angle_of_sign_eq_one`：oangle_eq_angle_of_sign_eq_o
ne {x y : V} (h : (o.oangle x y).sign = 1) : o.oangle x y = InnerProductGeometry
.angle x y
· 使用定理 `Real.Angle.tan_coe`：tan_coe (x : Real) : tan (x : Angle) = Real.tan x
· 使用定理 `InnerProductGeometry.tan_angle_add_of_inner_eq_zero`：tan_angle_add_of_in
ner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) : Real.tan (angle x (x + y)) = ‖y‖ / ‖x‖
· 使用定理 `Orientation.inner_eq_zero_of_oangle_eq_pi_div_two`：inner_eq_zero_of_oang
le_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : Real)) : ⟪x, y⟫ = 0

--- 原说明 ---
The tangent of an angle in a right-angled triangle as a ratio of sides.
-/
theorem tan_oangle_add_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.tan (o.oangle x (x + y)) = ‖y‖ / ‖x‖ := by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs, Real.Angle.tan_coe,
    InnerProductGeometry.tan_angle_add_of_inner_eq_zero (o.inner_eq_zero_of_oangle_eq_pi_div_two h)]

/-- The tangent of an angle in a right-angled triangle as a ratio of sides. -/
/-
**Orientation.tan_oangle_add_left_of_oangle_eq_pi_div_two** 是 Mathlib 中的一个定理，位于命
名空间 `Orientation`。
形式化陈述：tan_oangle_add_left_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = 
↑(π / 2)) : Real.Angle.tan (o.oangle (x + y) y) = ‖x‖ / ‖y‖
参数：h : o.oangle x y = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b
· 使用定理 `Orientation.oangle_rev`：oangle_rev (x y : V) : o.oangle y x = -o.oangle 
x y
· 使用定理 `Orientation.oangle_neg_orientation_eq_neg`：oangle_neg_orientation_eq_neg
 (x y : V) : (-o).oangle x y = -o.oangle x y
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Orientation.tan_oangle_add_right_of_oangle_eq_pi_div_two`：tan_oangle_add
_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) : Real.An
gle.tan (o.oangle x (x + y)) = ‖y‖ / ‖x‖

--- 原说明 ---
The tangent of an angle in a right-angled triangle as a ratio of sides.
-/
theorem tan_oangle_add_left_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.tan (o.oangle (x + y) y) = ‖x‖ / ‖y‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).tan_oangle_add_right_of_oangle_eq_pi_div_two h

/-- The cosine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
adjacent side. -/
/-
**Orientation.cos_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two** 是 Mathlib 
中的一个定理，位于命名空间 `Orientation`。
形式化陈述：cos_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two {x y : V} (h : o.oan
gle x y = ↑(π / 2)) : Real.Angle.cos (o.oangle x (x + y)) * ‖x + y‖ = ‖x‖
参数：h : o.oangle x y = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_sign_add_right`：oangle_sign_add_right (x y : V) : (o.
oangle x (x + y)).sign = (o.oangle x y).sign
· 使用定理 `Real.Angle.sign_coe_pi_div_two`：sign_coe_pi_div_two : (↑(π / 2) : Angle)
.sign = 1
· 使用定理 `Orientation.oangle_eq_angle_of_sign_eq_one`：oangle_eq_angle_of_sign_eq_o
ne {x y : V} (h : (o.oangle x y).sign = 1) : o.oangle x y = InnerProductGeometry
.angle x y
· 使用定理 `Real.Angle.cos_coe`：cos_coe (x : Real) : cos (x : Angle) = Real.cos x
· 使用定理 `InnerProductGeometry.cos_angle_add_mul_norm_of_inner_eq_zero`：cos_angle_
add_mul_norm_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) : Real.cos (angle x (x 
+ y)) * ‖x + y‖ = ‖x‖
· 使用定理 `Orientation.inner_eq_zero_of_oangle_eq_pi_div_two`：inner_eq_zero_of_oang
le_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : Real)) : ⟪x, y⟫ = 0

--- 原说明 ---
The cosine of an angle in a right-angled triangle multiplied by the hypotenuse e
quals the
adjacent side.
-/
theorem cos_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : Real.Angle.cos (o.oangle x (x + y)) * ‖x + y‖ = ‖x‖ := by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs, Real.Angle.cos_coe,
    InnerProductGeometry.cos_angle_add_mul_norm_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_div_two h)]

/-- The cosine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
adjacent side. -/
/-
**Orientation.cos_oangle_add_left_mul_norm_of_oangle_eq_pi_div_two** 是 Mathlib 中
的一个定理，位于命名空间 `Orientation`。
形式化陈述：cos_oangle_add_left_mul_norm_of_oangle_eq_pi_div_two {x y : V} (h : o.oang
le x y = ↑(π / 2)) : Real.Angle.cos (o.oangle (x + y) y) * ‖x + y‖ = ‖y‖
参数：h : o.oangle x y = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b
· 使用定理 `Orientation.oangle_rev`：oangle_rev (x y : V) : o.oangle y x = -o.oangle 
x y
· 使用定理 `Orientation.oangle_neg_orientation_eq_neg`：oangle_neg_orientation_eq_neg
 (x y : V) : (-o).oangle x y = -o.oangle x y
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Orientation.cos_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two`：cos_o
angle_add_right_mul_norm_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑
(π / 2)) : Real.Angle.cos (o.oangle x (x + y)) * ‖x + y…

--- 原说明 ---
The cosine of an angle in a right-angled triangle multiplied by the hypotenuse e
quals the
adjacent side.
-/
theorem cos_oangle_add_left_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : Real.Angle.cos (o.oangle (x + y) y) * ‖x + y‖ = ‖y‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).cos_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two h

/-- The sine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
opposite side. -/
/-
**Orientation.sin_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two** 是 Mathlib 
中的一个定理，位于命名空间 `Orientation`。
形式化陈述：sin_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two {x y : V} (h : o.oan
gle x y = ↑(π / 2)) : Real.Angle.sin (o.oangle x (x + y)) * ‖x + y‖ = ‖y‖
参数：h : o.oangle x y = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_sign_add_right`：oangle_sign_add_right (x y : V) : (o.
oangle x (x + y)).sign = (o.oangle x y).sign
· 使用定理 `Real.Angle.sign_coe_pi_div_two`：sign_coe_pi_div_two : (↑(π / 2) : Angle)
.sign = 1
· 使用定理 `Orientation.oangle_eq_angle_of_sign_eq_one`：oangle_eq_angle_of_sign_eq_o
ne {x y : V} (h : (o.oangle x y).sign = 1) : o.oangle x y = InnerProductGeometry
.angle x y
· 使用定理 `Real.Angle.sin_coe`：sin_coe (x : Real) : sin (x : Angle) = Real.sin x
· 使用定理 `InnerProductGeometry.sin_angle_add_mul_norm_of_inner_eq_zero`：sin_angle_
add_mul_norm_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) : Real.sin (angle x (x 
+ y)) * ‖x + y‖ = ‖y‖
· 使用定理 `Orientation.inner_eq_zero_of_oangle_eq_pi_div_two`：inner_eq_zero_of_oang
le_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : Real)) : ⟪x, y⟫ = 0

--- 原说明 ---
The sine of an angle in a right-angled triangle multiplied by the hypotenuse equ
als the
opposite side.
-/
theorem sin_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : Real.Angle.sin (o.oangle x (x + y)) * ‖x + y‖ = ‖y‖ := by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs, Real.Angle.sin_coe,
    InnerProductGeometry.sin_angle_add_mul_norm_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_div_two h)]

/-- The sine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
opposite side. -/
/-
**Orientation.sin_oangle_add_left_mul_norm_of_oangle_eq_pi_div_two** 是 Mathlib 中
的一个定理，位于命名空间 `Orientation`。
形式化陈述：sin_oangle_add_left_mul_norm_of_oangle_eq_pi_div_two {x y : V} (h : o.oang
le x y = ↑(π / 2)) : Real.Angle.sin (o.oangle (x + y) y) * ‖x + y‖ = ‖x‖
参数：h : o.oangle x y = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b
· 使用定理 `Orientation.oangle_rev`：oangle_rev (x y : V) : o.oangle y x = -o.oangle 
x y
· 使用定理 `Orientation.oangle_neg_orientation_eq_neg`：oangle_neg_orientation_eq_neg
 (x y : V) : (-o).oangle x y = -o.oangle x y
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Orientation.sin_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two`：sin_o
angle_add_right_mul_norm_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑
(π / 2)) : Real.Angle.sin (o.oangle x (x + y)) * ‖x + y…

--- 原说明 ---
The sine of an angle in a right-angled triangle multiplied by the hypotenuse equ
als the
opposite side.
-/
theorem sin_oangle_add_left_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : Real.Angle.sin (o.oangle (x + y) y) * ‖x + y‖ = ‖x‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).sin_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two h

/-- The tangent of an angle in a right-angled triangle multiplied by the adjacent side equals
the opposite side. -/
/-
**Orientation.tan_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two** 是 Mathlib 
中的一个定理，位于命名空间 `Orientation`。
形式化陈述：tan_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two {x y : V} (h : o.oan
gle x y = ↑(π / 2)) : Real.Angle.tan (o.oangle x (x + y)) * ‖x‖ = ‖y‖
参数：h : o.oangle x y = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_sign_add_right`：oangle_sign_add_right (x y : V) : (o.
oangle x (x + y)).sign = (o.oangle x y).sign
· 使用定理 `Real.Angle.sign_coe_pi_div_two`：sign_coe_pi_div_two : (↑(π / 2) : Angle)
.sign = 1
· 使用定理 `Orientation.oangle_eq_angle_of_sign_eq_one`：oangle_eq_angle_of_sign_eq_o
ne {x y : V} (h : (o.oangle x y).sign = 1) : o.oangle x y = InnerProductGeometry
.angle x y
· 使用定理 `Real.Angle.tan_coe`：tan_coe (x : Real) : tan (x : Angle) = Real.tan x
· 使用定理 `InnerProductGeometry.tan_angle_add_mul_norm_of_inner_eq_zero`：tan_angle_
add_mul_norm_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0 ∨ y = 0) :
 Real.tan (angle x (x + y)) * ‖x‖ = ‖y‖
· 使用定理 `Orientation.inner_eq_zero_of_oangle_eq_pi_div_two`：inner_eq_zero_of_oang
le_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : Real)) : ⟪x, y⟫ = 0
· 使用定理 `Orientation.left_ne_zero_of_oangle_eq_pi_div_two`：left_ne_zero_of_oangle
_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : Real)) : x != 0

--- 原说明 ---
The tangent of an angle in a right-angled triangle multiplied by the adjacent si
de equals
the opposite side.
-/
theorem tan_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : Real.Angle.tan (o.oangle x (x + y)) * ‖x‖ = ‖y‖ := by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs, Real.Angle.tan_coe,
    InnerProductGeometry.tan_angle_add_mul_norm_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_div_two h)
      (Or.inl (o.left_ne_zero_of_oangle_eq_pi_div_two h))]

/-- The tangent of an angle in a right-angled triangle multiplied by the adjacent side equals
the opposite side. -/
/-
**Orientation.tan_oangle_add_left_mul_norm_of_oangle_eq_pi_div_two** 是 Mathlib 中
的一个定理，位于命名空间 `Orientation`。
形式化陈述：tan_oangle_add_left_mul_norm_of_oangle_eq_pi_div_two {x y : V} (h : o.oang
le x y = ↑(π / 2)) : Real.Angle.tan (o.oangle (x + y) y) * ‖y‖ = ‖x‖
参数：h : o.oangle x y = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b
· 使用定理 `Orientation.oangle_rev`：oangle_rev (x y : V) : o.oangle y x = -o.oangle 
x y
· 使用定理 `Orientation.oangle_neg_orientation_eq_neg`：oangle_neg_orientation_eq_neg
 (x y : V) : (-o).oangle x y = -o.oangle x y
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Orientation.tan_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two`：tan_o
angle_add_right_mul_norm_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑
(π / 2)) : Real.Angle.tan (o.oangle x (x + y)) * ‖x‖ = …

--- 原说明 ---
The tangent of an angle in a right-angled triangle multiplied by the adjacent si
de equals
the opposite side.
-/
theorem tan_oangle_add_left_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : Real.Angle.tan (o.oangle (x + y) y) * ‖y‖ = ‖x‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).tan_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two h

/-- A side of a right-angled triangle divided by the cosine of the adjacent angle equals the
hypotenuse. -/
/-
**Orientation.norm_div_cos_oangle_add_right_of_oangle_eq_pi_div_two** 是 Mathlib 
中的一个定理，位于命名空间 `Orientation`。
形式化陈述：norm_div_cos_oangle_add_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oan
gle x y = ↑(π / 2)) : ‖x‖ / Real.Angle.cos (o.oangle x (x + y)) = ‖x + y‖
参数：h : o.oangle x y = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_sign_add_right`：oangle_sign_add_right (x y : V) : (o.
oangle x (x + y)).sign = (o.oangle x y).sign
· 使用定理 `Real.Angle.sign_coe_pi_div_two`：sign_coe_pi_div_two : (↑(π / 2) : Angle)
.sign = 1
· 使用定理 `Orientation.oangle_eq_angle_of_sign_eq_one`：oangle_eq_angle_of_sign_eq_o
ne {x y : V} (h : (o.oangle x y).sign = 1) : o.oangle x y = InnerProductGeometry
.angle x y
· 使用定理 `Real.Angle.cos_coe`：cos_coe (x : Real) : cos (x : Angle) = Real.cos x
· 使用定理 `InnerProductGeometry.norm_div_cos_angle_add_of_inner_eq_zero`：norm_div_c
os_angle_add_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0 ∨ y = 0) :
 ‖x‖ / Real.cos (angle x (x + y)) = ‖x + y‖
· 使用定理 `Orientation.inner_eq_zero_of_oangle_eq_pi_div_two`：inner_eq_zero_of_oang
le_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : Real)) : ⟪x, y⟫ = 0
· 使用定理 `Orientation.left_ne_zero_of_oangle_eq_pi_div_two`：left_ne_zero_of_oangle
_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : Real)) : x != 0

--- 原说明 ---
A side of a right-angled triangle divided by the cosine of the adjacent angle eq
uals the
hypotenuse.
-/
theorem norm_div_cos_oangle_add_right_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : ‖x‖ / Real.Angle.cos (o.oangle x (x + y)) = ‖x + y‖ := by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs, Real.Angle.cos_coe,
    InnerProductGeometry.norm_div_cos_angle_add_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_div_two h)
      (Or.inl (o.left_ne_zero_of_oangle_eq_pi_div_two h))]

/-- A side of a right-angled triangle divided by the cosine of the adjacent angle equals the
hypotenuse. -/
/-
**Orientation.norm_div_cos_oangle_add_left_of_oangle_eq_pi_div_two** 是 Mathlib 中
的一个定理，位于命名空间 `Orientation`。
形式化陈述：norm_div_cos_oangle_add_left_of_oangle_eq_pi_div_two {x y : V} (h : o.oang
le x y = ↑(π / 2)) : ‖y‖ / Real.Angle.cos (o.oangle (x + y) y) = ‖x + y‖
参数：h : o.oangle x y = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b
· 使用定理 `Orientation.oangle_rev`：oangle_rev (x y : V) : o.oangle y x = -o.oangle 
x y
· 使用定理 `Orientation.oangle_neg_orientation_eq_neg`：oangle_neg_orientation_eq_neg
 (x y : V) : (-o).oangle x y = -o.oangle x y
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Orientation.norm_div_cos_oangle_add_right_of_oangle_eq_pi_div_two`：norm_
div_cos_oangle_add_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑
(π / 2)) : ‖x‖ / Real.Angle.cos (o.oangle x (x + y)) = …

--- 原说明 ---
A side of a right-angled triangle divided by the cosine of the adjacent angle eq
uals the
hypotenuse.
-/
theorem norm_div_cos_oangle_add_left_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : ‖y‖ / Real.Angle.cos (o.oangle (x + y) y) = ‖x + y‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).norm_div_cos_oangle_add_right_of_oangle_eq_pi_div_two h

/-- A side of a right-angled triangle divided by the sine of the opposite angle equals the
hypotenuse. -/
/-
**Orientation.norm_div_sin_oangle_add_right_of_oangle_eq_pi_div_two** 是 Mathlib 
中的一个定理，位于命名空间 `Orientation`。
形式化陈述：norm_div_sin_oangle_add_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oan
gle x y = ↑(π / 2)) : ‖y‖ / Real.Angle.sin (o.oangle x (x + y)) = ‖x + y‖
参数：h : o.oangle x y = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_sign_add_right`：oangle_sign_add_right (x y : V) : (o.
oangle x (x + y)).sign = (o.oangle x y).sign
· 使用定理 `Real.Angle.sign_coe_pi_div_two`：sign_coe_pi_div_two : (↑(π / 2) : Angle)
.sign = 1
· 使用定理 `Orientation.oangle_eq_angle_of_sign_eq_one`：oangle_eq_angle_of_sign_eq_o
ne {x y : V} (h : (o.oangle x y).sign = 1) : o.oangle x y = InnerProductGeometry
.angle x y
· 使用定理 `Real.Angle.sin_coe`：sin_coe (x : Real) : sin (x : Angle) = Real.sin x
· 使用定理 `InnerProductGeometry.norm_div_sin_angle_add_of_inner_eq_zero`：norm_div_s
in_angle_add_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x = 0 ∨ y != 0) :
 ‖y‖ / Real.sin (angle x (x + y)) = ‖x + y‖
· 使用定理 `Orientation.inner_eq_zero_of_oangle_eq_pi_div_two`：inner_eq_zero_of_oang
le_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : Real)) : ⟪x, y⟫ = 0
· 使用定理 `Orientation.right_ne_zero_of_oangle_eq_pi_div_two`：right_ne_zero_of_oang
le_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : Real)) : y != 0

--- 原说明 ---
A side of a right-angled triangle divided by the sine of the opposite angle equa
ls the
hypotenuse.
-/
theorem norm_div_sin_oangle_add_right_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : ‖y‖ / Real.Angle.sin (o.oangle x (x + y)) = ‖x + y‖ := by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs, Real.Angle.sin_coe,
    InnerProductGeometry.norm_div_sin_angle_add_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_div_two h)
      (Or.inr (o.right_ne_zero_of_oangle_eq_pi_div_two h))]

/-- A side of a right-angled triangle divided by the sine of the opposite angle equals the
hypotenuse. -/
/-
**Orientation.norm_div_sin_oangle_add_left_of_oangle_eq_pi_div_two** 是 Mathlib 中
的一个定理，位于命名空间 `Orientation`。
形式化陈述：norm_div_sin_oangle_add_left_of_oangle_eq_pi_div_two {x y : V} (h : o.oang
le x y = ↑(π / 2)) : ‖x‖ / Real.Angle.sin (o.oangle (x + y) y) = ‖x + y‖
参数：h : o.oangle x y = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b
· 使用定理 `Orientation.oangle_rev`：oangle_rev (x y : V) : o.oangle y x = -o.oangle 
x y
· 使用定理 `Orientation.oangle_neg_orientation_eq_neg`：oangle_neg_orientation_eq_neg
 (x y : V) : (-o).oangle x y = -o.oangle x y
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Orientation.norm_div_sin_oangle_add_right_of_oangle_eq_pi_div_two`：norm_
div_sin_oangle_add_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑
(π / 2)) : ‖y‖ / Real.Angle.sin (o.oangle x (x + y)) = …

--- 原说明 ---
A side of a right-angled triangle divided by the sine of the opposite angle equa
ls the
hypotenuse.
-/
theorem norm_div_sin_oangle_add_left_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : ‖x‖ / Real.Angle.sin (o.oangle (x + y) y) = ‖x + y‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).norm_div_sin_oangle_add_right_of_oangle_eq_pi_div_two h

/-- A side of a right-angled triangle divided by the tangent of the opposite angle equals the
adjacent side. -/
/-
**Orientation.norm_div_tan_oangle_add_right_of_oangle_eq_pi_div_two** 是 Mathlib 
中的一个定理，位于命名空间 `Orientation`。
形式化陈述：norm_div_tan_oangle_add_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oan
gle x y = ↑(π / 2)) : ‖y‖ / Real.Angle.tan (o.oangle x (x + y)) = ‖x‖
参数：h : o.oangle x y = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_sign_add_right`：oangle_sign_add_right (x y : V) : (o.
oangle x (x + y)).sign = (o.oangle x y).sign
· 使用定理 `Real.Angle.sign_coe_pi_div_two`：sign_coe_pi_div_two : (↑(π / 2) : Angle)
.sign = 1
· 使用定理 `Orientation.oangle_eq_angle_of_sign_eq_one`：oangle_eq_angle_of_sign_eq_o
ne {x y : V} (h : (o.oangle x y).sign = 1) : o.oangle x y = InnerProductGeometry
.angle x y
· 使用定理 `Real.Angle.tan_coe`：tan_coe (x : Real) : tan (x : Angle) = Real.tan x
· 使用定理 `InnerProductGeometry.norm_div_tan_angle_add_of_inner_eq_zero`：norm_div_t
an_angle_add_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x = 0 ∨ y != 0) :
 ‖y‖ / Real.tan (angle x (x + y)) = ‖x‖
· 使用定理 `Orientation.inner_eq_zero_of_oangle_eq_pi_div_two`：inner_eq_zero_of_oang
le_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : Real)) : ⟪x, y⟫ = 0
· 使用定理 `Orientation.right_ne_zero_of_oangle_eq_pi_div_two`：right_ne_zero_of_oang
le_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : Real)) : y != 0

--- 原说明 ---
A side of a right-angled triangle divided by the tangent of the opposite angle e
quals the
adjacent side.
-/
theorem norm_div_tan_oangle_add_right_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : ‖y‖ / Real.Angle.tan (o.oangle x (x + y)) = ‖x‖ := by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs, Real.Angle.tan_coe,
    InnerProductGeometry.norm_div_tan_angle_add_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_div_two h)
      (Or.inr (o.right_ne_zero_of_oangle_eq_pi_div_two h))]

/-- A side of a right-angled triangle divided by the tangent of the opposite angle equals the
adjacent side. -/
/-
**Orientation.norm_div_tan_oangle_add_left_of_oangle_eq_pi_div_two** 是 Mathlib 中
的一个定理，位于命名空间 `Orientation`。
形式化陈述：norm_div_tan_oangle_add_left_of_oangle_eq_pi_div_two {x y : V} (h : o.oang
le x y = ↑(π / 2)) : ‖x‖ / Real.Angle.tan (o.oangle (x + y) y) = ‖y‖
参数：h : o.oangle x y = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b
· 使用定理 `Orientation.oangle_rev`：oangle_rev (x y : V) : o.oangle y x = -o.oangle 
x y
· 使用定理 `Orientation.oangle_neg_orientation_eq_neg`：oangle_neg_orientation_eq_neg
 (x y : V) : (-o).oangle x y = -o.oangle x y
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Orientation.norm_div_tan_oangle_add_right_of_oangle_eq_pi_div_two`：norm_
div_tan_oangle_add_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑
(π / 2)) : ‖y‖ / Real.Angle.tan (o.oangle x (x + y)) = …

--- 原说明 ---
A side of a right-angled triangle divided by the tangent of the opposite angle e
quals the
adjacent side.
-/
theorem norm_div_tan_oangle_add_left_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : ‖x‖ / Real.Angle.tan (o.oangle (x + y) y) = ‖y‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).norm_div_tan_oangle_add_right_of_oangle_eq_pi_div_two h

/-- An angle in a right-angled triangle expressed using `arccos`, version subtracting vectors. -/
/-
**Orientation.oangle_sub_right_eq_arccos_of_oangle_eq_pi_div_two** 是 Mathlib 中的一
个定理，位于命名空间 `Orientation`。
形式化陈述：oangle_sub_right_eq_arccos_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle
 x y = ↑(π / 2)) : o.oangle y (y - x) = Real.arccos (‖y‖ / ‖y - x‖)
参数：h : o.oangle x y = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_sign_sub_right_swap`：oangle_sign_sub_right_swap (x y 
: V) : (o.oangle y (y - x)).sign = (o.oangle x y).sign
· 使用定理 `Real.Angle.sign_coe_pi_div_two`：sign_coe_pi_div_two : (↑(π / 2) : Angle)
.sign = 1
· 使用定理 `Orientation.oangle_eq_angle_of_sign_eq_one`：oangle_eq_angle_of_sign_eq_o
ne {x y : V} (h : (o.oangle x y).sign = 1) : o.oangle x y = InnerProductGeometry
.angle x y
· 使用定理 `InnerProductGeometry.angle_sub_eq_arccos_of_inner_eq_zero`：angle_sub_eq_
arccos_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) : angle x (x - y) = Real.arcc
os (‖x‖ / ‖x - y‖)
· 使用定理 `Orientation.inner_rev_eq_zero_of_oangle_eq_pi_div_two`：inner_rev_eq_zero
_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : Real)) : ⟪y, x⟫ 
= 0

--- 原说明 ---
An angle in a right-angled triangle expressed using `arccos`, version subtractin
g vectors.
-/
theorem oangle_sub_right_eq_arccos_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle y (y - x) = Real.arccos (‖y‖ / ‖y - x‖) := by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs,
    InnerProductGeometry.angle_sub_eq_arccos_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)]

/-- An angle in a right-angled triangle expressed using `arccos`, version subtracting vectors. -/
/-
**Orientation.oangle_sub_left_eq_arccos_of_oangle_eq_pi_div_two** 是 Mathlib 中的一个
定理，位于命名空间 `Orientation`。
形式化陈述：oangle_sub_left_eq_arccos_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle 
x y = ↑(π / 2)) : o.oangle (x - y) x = Real.arccos (‖x‖ / ‖x - y‖)
参数：h : o.oangle x y = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b
· 使用定理 `Orientation.oangle_rev`：oangle_rev (x y : V) : o.oangle y x = -o.oangle 
x y
· 使用定理 `Orientation.oangle_neg_orientation_eq_neg`：oangle_neg_orientation_eq_neg
 (x y : V) : (-o).oangle x y = -o.oangle x y
· 使用定理 `Orientation.oangle_sub_right_eq_arccos_of_oangle_eq_pi_div_two`：oangle_s
ub_right_eq_arccos_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2
)) : o.oangle y (y - x) = Real.arccos (‖y‖ / ‖y - x‖…

--- 原说明 ---
An angle in a right-angled triangle expressed using `arccos`, version subtractin
g vectors.
-/
theorem oangle_sub_left_eq_arccos_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle (x - y) x = Real.arccos (‖x‖ / ‖x - y‖) := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  exact (-o).oangle_sub_right_eq_arccos_of_oangle_eq_pi_div_two h

/-- An angle in a right-angled triangle expressed using `arcsin`, version subtracting vectors. -/
/-
**Orientation.oangle_sub_right_eq_arcsin_of_oangle_eq_pi_div_two** 是 Mathlib 中的一
个定理，位于命名空间 `Orientation`。
形式化陈述：oangle_sub_right_eq_arcsin_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle
 x y = ↑(π / 2)) : o.oangle y (y - x) = Real.arcsin (‖x‖ / ‖y - x‖)
参数：h : o.oangle x y = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_sign_sub_right_swap`：oangle_sign_sub_right_swap (x y 
: V) : (o.oangle y (y - x)).sign = (o.oangle x y).sign
· 使用定理 `Real.Angle.sign_coe_pi_div_two`：sign_coe_pi_div_two : (↑(π / 2) : Angle)
.sign = 1
· 使用定理 `Orientation.oangle_eq_angle_of_sign_eq_one`：oangle_eq_angle_of_sign_eq_o
ne {x y : V} (h : (o.oangle x y).sign = 1) : o.oangle x y = InnerProductGeometry
.angle x y
· 使用定理 `InnerProductGeometry.angle_sub_eq_arcsin_of_inner_eq_zero`：angle_sub_eq_
arcsin_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0 ∨ y != 0) : angl
e x (x - y) = Real.arcsin (‖y‖ / ‖x - y‖)
· 使用定理 `Orientation.inner_rev_eq_zero_of_oangle_eq_pi_div_two`：inner_rev_eq_zero
_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : Real)) : ⟪y, x⟫ 
= 0
· 使用定理 `Orientation.right_ne_zero_of_oangle_eq_pi_div_two`：right_ne_zero_of_oang
le_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : Real)) : y != 0

--- 原说明 ---
An angle in a right-angled triangle expressed using `arcsin`, version subtractin
g vectors.
-/
theorem oangle_sub_right_eq_arcsin_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle y (y - x) = Real.arcsin (‖x‖ / ‖y - x‖) := by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs,
    InnerProductGeometry.angle_sub_eq_arcsin_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)
      (Or.inl (o.right_ne_zero_of_oangle_eq_pi_div_two h))]

/-- An angle in a right-angled triangle expressed using `arcsin`, version subtracting vectors. -/
/-
**Orientation.oangle_sub_left_eq_arcsin_of_oangle_eq_pi_div_two** 是 Mathlib 中的一个
定理，位于命名空间 `Orientation`。
形式化陈述：oangle_sub_left_eq_arcsin_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle 
x y = ↑(π / 2)) : o.oangle (x - y) x = Real.arcsin (‖y‖ / ‖x - y‖)
参数：h : o.oangle x y = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b
· 使用定理 `Orientation.oangle_rev`：oangle_rev (x y : V) : o.oangle y x = -o.oangle 
x y
· 使用定理 `Orientation.oangle_neg_orientation_eq_neg`：oangle_neg_orientation_eq_neg
 (x y : V) : (-o).oangle x y = -o.oangle x y
· 使用定理 `Orientation.oangle_sub_right_eq_arcsin_of_oangle_eq_pi_div_two`：oangle_s
ub_right_eq_arcsin_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2
)) : o.oangle y (y - x) = Real.arcsin (‖x‖ / ‖y - x‖…

--- 原说明 ---
An angle in a right-angled triangle expressed using `arcsin`, version subtractin
g vectors.
-/
theorem oangle_sub_left_eq_arcsin_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle (x - y) x = Real.arcsin (‖y‖ / ‖x - y‖) := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  exact (-o).oangle_sub_right_eq_arcsin_of_oangle_eq_pi_div_two h

/-- An angle in a right-angled triangle expressed using `arctan`, version subtracting vectors. -/
/-
**Orientation.oangle_sub_right_eq_arctan_of_oangle_eq_pi_div_two** 是 Mathlib 中的一
个定理，位于命名空间 `Orientation`。
形式化陈述：oangle_sub_right_eq_arctan_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle
 x y = ↑(π / 2)) : o.oangle y (y - x) = Real.arctan (‖x‖ / ‖y‖)
参数：h : o.oangle x y = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_sign_sub_right_swap`：oangle_sign_sub_right_swap (x y 
: V) : (o.oangle y (y - x)).sign = (o.oangle x y).sign
· 使用定理 `Real.Angle.sign_coe_pi_div_two`：sign_coe_pi_div_two : (↑(π / 2) : Angle)
.sign = 1
· 使用定理 `Orientation.oangle_eq_angle_of_sign_eq_one`：oangle_eq_angle_of_sign_eq_o
ne {x y : V} (h : (o.oangle x y).sign = 1) : o.oangle x y = InnerProductGeometry
.angle x y
· 使用定理 `InnerProductGeometry.angle_sub_eq_arctan_of_inner_eq_zero`：angle_sub_eq_
arctan_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0) : angle x (x - 
y) = Real.arctan (‖y‖ / ‖x‖)
· 使用定理 `Orientation.inner_rev_eq_zero_of_oangle_eq_pi_div_two`：inner_rev_eq_zero
_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : Real)) : ⟪y, x⟫ 
= 0
· 使用定理 `Orientation.right_ne_zero_of_oangle_eq_pi_div_two`：right_ne_zero_of_oang
le_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : Real)) : y != 0

--- 原说明 ---
An angle in a right-angled triangle expressed using `arctan`, version subtractin
g vectors.
-/
theorem oangle_sub_right_eq_arctan_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle y (y - x) = Real.arctan (‖x‖ / ‖y‖) := by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs,
    InnerProductGeometry.angle_sub_eq_arctan_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h) (o.right_ne_zero_of_oangle_eq_pi_div_two h)]

/-- An angle in a right-angled triangle expressed using `arctan`, version subtracting vectors. -/
/-
**Orientation.oangle_sub_left_eq_arctan_of_oangle_eq_pi_div_two** 是 Mathlib 中的一个
定理，位于命名空间 `Orientation`。
形式化陈述：oangle_sub_left_eq_arctan_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle 
x y = ↑(π / 2)) : o.oangle (x - y) x = Real.arctan (‖y‖ / ‖x‖)
参数：h : o.oangle x y = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b
· 使用定理 `Orientation.oangle_rev`：oangle_rev (x y : V) : o.oangle y x = -o.oangle 
x y
· 使用定理 `Orientation.oangle_neg_orientation_eq_neg`：oangle_neg_orientation_eq_neg
 (x y : V) : (-o).oangle x y = -o.oangle x y
· 使用定理 `Orientation.oangle_sub_right_eq_arctan_of_oangle_eq_pi_div_two`：oangle_s
ub_right_eq_arctan_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2
)) : o.oangle y (y - x) = Real.arctan (‖x‖ / ‖y‖)

--- 原说明 ---
An angle in a right-angled triangle expressed using `arctan`, version subtractin
g vectors.
-/
theorem oangle_sub_left_eq_arctan_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle (x - y) x = Real.arctan (‖y‖ / ‖x‖) := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  exact (-o).oangle_sub_right_eq_arctan_of_oangle_eq_pi_div_two h

/-- The cosine of an angle in a right-angled triangle as a ratio of sides, version subtracting
vectors. -/
/-
**Orientation.cos_oangle_sub_right_of_oangle_eq_pi_div_two** 是 Mathlib 中的一个定理，位于
命名空间 `Orientation`。
形式化陈述：cos_oangle_sub_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y =
 ↑(π / 2)) : Real.Angle.cos (o.oangle y (y - x)) = ‖y‖ / ‖y - x‖
参数：h : o.oangle x y = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_sign_sub_right_swap`：oangle_sign_sub_right_swap (x y 
: V) : (o.oangle y (y - x)).sign = (o.oangle x y).sign
· 使用定理 `Real.Angle.sign_coe_pi_div_two`：sign_coe_pi_div_two : (↑(π / 2) : Angle)
.sign = 1
· 使用定理 `Orientation.oangle_eq_angle_of_sign_eq_one`：oangle_eq_angle_of_sign_eq_o
ne {x y : V} (h : (o.oangle x y).sign = 1) : o.oangle x y = InnerProductGeometry
.angle x y
· 使用定理 `Real.Angle.cos_coe`：cos_coe (x : Real) : cos (x : Angle) = Real.cos x
· 使用定理 `InnerProductGeometry.cos_angle_sub_of_inner_eq_zero`：cos_angle_sub_of_in
ner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) : Real.cos (angle x (x - y)) = ‖x‖ / ‖x -
 y‖
· 使用定理 `Orientation.inner_rev_eq_zero_of_oangle_eq_pi_div_two`：inner_rev_eq_zero
_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : Real)) : ⟪y, x⟫ 
= 0

--- 原说明 ---
The cosine of an angle in a right-angled triangle as a ratio of sides, version s
ubtracting
vectors.
-/
theorem cos_oangle_sub_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.cos (o.oangle y (y - x)) = ‖y‖ / ‖y - x‖ := by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs, Real.Angle.cos_coe,
    InnerProductGeometry.cos_angle_sub_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)]

/-- The cosine of an angle in a right-angled triangle as a ratio of sides, version subtracting
vectors. -/
/-
**Orientation.cos_oangle_sub_left_of_oangle_eq_pi_div_two** 是 Mathlib 中的一个定理，位于命
名空间 `Orientation`。
形式化陈述：cos_oangle_sub_left_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = 
↑(π / 2)) : Real.Angle.cos (o.oangle (x - y) x) = ‖x‖ / ‖x - y‖
参数：h : o.oangle x y = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b
· 使用定理 `Orientation.oangle_rev`：oangle_rev (x y : V) : o.oangle y x = -o.oangle 
x y
· 使用定理 `Orientation.oangle_neg_orientation_eq_neg`：oangle_neg_orientation_eq_neg
 (x y : V) : (-o).oangle x y = -o.oangle x y
· 使用定理 `Orientation.cos_oangle_sub_right_of_oangle_eq_pi_div_two`：cos_oangle_sub
_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) : Real.An
gle.cos (o.oangle y (y - x)) = ‖y‖ / ‖y - x‖

--- 原说明 ---
The cosine of an angle in a right-angled triangle as a ratio of sides, version s
ubtracting
vectors.
-/
theorem cos_oangle_sub_left_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.cos (o.oangle (x - y) x) = ‖x‖ / ‖x - y‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  exact (-o).cos_oangle_sub_right_of_oangle_eq_pi_div_two h

/-- The sine of an angle in a right-angled triangle as a ratio of sides, version subtracting
vectors. -/
/-
**Orientation.sin_oangle_sub_right_of_oangle_eq_pi_div_two** 是 Mathlib 中的一个定理，位于
命名空间 `Orientation`。
形式化陈述：sin_oangle_sub_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y =
 ↑(π / 2)) : Real.Angle.sin (o.oangle y (y - x)) = ‖x‖ / ‖y - x‖
参数：h : o.oangle x y = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_sign_sub_right_swap`：oangle_sign_sub_right_swap (x y 
: V) : (o.oangle y (y - x)).sign = (o.oangle x y).sign
· 使用定理 `Real.Angle.sign_coe_pi_div_two`：sign_coe_pi_div_two : (↑(π / 2) : Angle)
.sign = 1
· 使用定理 `Orientation.oangle_eq_angle_of_sign_eq_one`：oangle_eq_angle_of_sign_eq_o
ne {x y : V} (h : (o.oangle x y).sign = 1) : o.oangle x y = InnerProductGeometry
.angle x y
· 使用定理 `Real.Angle.sin_coe`：sin_coe (x : Real) : sin (x : Angle) = Real.sin x
· 使用定理 `InnerProductGeometry.sin_angle_sub_of_inner_eq_zero`：sin_angle_sub_of_in
ner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0 ∨ y != 0) : Real.sin (angle 
x (x - y)) = ‖y‖ / ‖x - y‖
· 使用定理 `Orientation.inner_rev_eq_zero_of_oangle_eq_pi_div_two`：inner_rev_eq_zero
_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : Real)) : ⟪y, x⟫ 
= 0
· 使用定理 `Orientation.right_ne_zero_of_oangle_eq_pi_div_two`：right_ne_zero_of_oang
le_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : Real)) : y != 0

--- 原说明 ---
The sine of an angle in a right-angled triangle as a ratio of sides, version sub
tracting
vectors.
-/
theorem sin_oangle_sub_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.sin (o.oangle y (y - x)) = ‖x‖ / ‖y - x‖ := by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs, Real.Angle.sin_coe,
    InnerProductGeometry.sin_angle_sub_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)
      (Or.inl (o.right_ne_zero_of_oangle_eq_pi_div_two h))]

/-- The sine of an angle in a right-angled triangle as a ratio of sides, version subtracting
vectors. -/
/-
**Orientation.sin_oangle_sub_left_of_oangle_eq_pi_div_two** 是 Mathlib 中的一个定理，位于命
名空间 `Orientation`。
形式化陈述：sin_oangle_sub_left_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = 
↑(π / 2)) : Real.Angle.sin (o.oangle (x - y) x) = ‖y‖ / ‖x - y‖
参数：h : o.oangle x y = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b
· 使用定理 `Orientation.oangle_rev`：oangle_rev (x y : V) : o.oangle y x = -o.oangle 
x y
· 使用定理 `Orientation.oangle_neg_orientation_eq_neg`：oangle_neg_orientation_eq_neg
 (x y : V) : (-o).oangle x y = -o.oangle x y
· 使用定理 `Orientation.sin_oangle_sub_right_of_oangle_eq_pi_div_two`：sin_oangle_sub
_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) : Real.An
gle.sin (o.oangle y (y - x)) = ‖x‖ / ‖y - x‖

--- 原说明 ---
The sine of an angle in a right-angled triangle as a ratio of sides, version sub
tracting
vectors.
-/
theorem sin_oangle_sub_left_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.sin (o.oangle (x - y) x) = ‖y‖ / ‖x - y‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  exact (-o).sin_oangle_sub_right_of_oangle_eq_pi_div_two h

/-- The tangent of an angle in a right-angled triangle as a ratio of sides, version subtracting
vectors. -/
/-
**Orientation.tan_oangle_sub_right_of_oangle_eq_pi_div_two** 是 Mathlib 中的一个定理，位于
命名空间 `Orientation`。
形式化陈述：tan_oangle_sub_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y =
 ↑(π / 2)) : Real.Angle.tan (o.oangle y (y - x)) = ‖x‖ / ‖y‖
参数：h : o.oangle x y = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_sign_sub_right_swap`：oangle_sign_sub_right_swap (x y 
: V) : (o.oangle y (y - x)).sign = (o.oangle x y).sign
· 使用定理 `Real.Angle.sign_coe_pi_div_two`：sign_coe_pi_div_two : (↑(π / 2) : Angle)
.sign = 1
· 使用定理 `Orientation.oangle_eq_angle_of_sign_eq_one`：oangle_eq_angle_of_sign_eq_o
ne {x y : V} (h : (o.oangle x y).sign = 1) : o.oangle x y = InnerProductGeometry
.angle x y
· 使用定理 `Real.Angle.tan_coe`：tan_coe (x : Real) : tan (x : Angle) = Real.tan x
· 使用定理 `InnerProductGeometry.tan_angle_sub_of_inner_eq_zero`：tan_angle_sub_of_in
ner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) : Real.tan (angle x (x - y)) = ‖y‖ / ‖x‖
· 使用定理 `Orientation.inner_rev_eq_zero_of_oangle_eq_pi_div_two`：inner_rev_eq_zero
_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : Real)) : ⟪y, x⟫ 
= 0

--- 原说明 ---
The tangent of an angle in a right-angled triangle as a ratio of sides, version 
subtracting
vectors.
-/
theorem tan_oangle_sub_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.tan (o.oangle y (y - x)) = ‖x‖ / ‖y‖ := by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs, Real.Angle.tan_coe,
    InnerProductGeometry.tan_angle_sub_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)]

/-- The tangent of an angle in a right-angled triangle as a ratio of sides, version subtracting
vectors. -/
/-
**Orientation.tan_oangle_sub_left_of_oangle_eq_pi_div_two** 是 Mathlib 中的一个定理，位于命
名空间 `Orientation`。
形式化陈述：tan_oangle_sub_left_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = 
↑(π / 2)) : Real.Angle.tan (o.oangle (x - y) x) = ‖y‖ / ‖x‖
参数：h : o.oangle x y = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b
· 使用定理 `Orientation.oangle_rev`：oangle_rev (x y : V) : o.oangle y x = -o.oangle 
x y
· 使用定理 `Orientation.oangle_neg_orientation_eq_neg`：oangle_neg_orientation_eq_neg
 (x y : V) : (-o).oangle x y = -o.oangle x y
· 使用定理 `Orientation.tan_oangle_sub_right_of_oangle_eq_pi_div_two`：tan_oangle_sub
_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) : Real.An
gle.tan (o.oangle y (y - x)) = ‖x‖ / ‖y‖

--- 原说明 ---
The tangent of an angle in a right-angled triangle as a ratio of sides, version 
subtracting
vectors.
-/
theorem tan_oangle_sub_left_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.tan (o.oangle (x - y) x) = ‖y‖ / ‖x‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  exact (-o).tan_oangle_sub_right_of_oangle_eq_pi_div_two h

/-- The cosine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
adjacent side, version subtracting vectors. -/
/-
**Orientation.cos_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two** 是 Mathlib 
中的一个定理，位于命名空间 `Orientation`。
形式化陈述：cos_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two {x y : V} (h : o.oan
gle x y = ↑(π / 2)) : Real.Angle.cos (o.oangle y (y - x)) * ‖y - x‖ = ‖y‖
参数：h : o.oangle x y = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_sign_sub_right_swap`：oangle_sign_sub_right_swap (x y 
: V) : (o.oangle y (y - x)).sign = (o.oangle x y).sign
· 使用定理 `Real.Angle.sign_coe_pi_div_two`：sign_coe_pi_div_two : (↑(π / 2) : Angle)
.sign = 1
· 使用定理 `Orientation.oangle_eq_angle_of_sign_eq_one`：oangle_eq_angle_of_sign_eq_o
ne {x y : V} (h : (o.oangle x y).sign = 1) : o.oangle x y = InnerProductGeometry
.angle x y
· 使用定理 `Real.Angle.cos_coe`：cos_coe (x : Real) : cos (x : Angle) = Real.cos x
· 使用定理 `InnerProductGeometry.cos_angle_sub_mul_norm_of_inner_eq_zero`：cos_angle_
sub_mul_norm_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) : Real.cos (angle x (x 
- y)) * ‖x - y‖ = ‖x‖
· 使用定理 `Orientation.inner_rev_eq_zero_of_oangle_eq_pi_div_two`：inner_rev_eq_zero
_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : Real)) : ⟪y, x⟫ 
= 0

--- 原说明 ---
The cosine of an angle in a right-angled triangle multiplied by the hypotenuse e
quals the
adjacent side, version subtracting vectors.
-/
theorem cos_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : Real.Angle.cos (o.oangle y (y - x)) * ‖y - x‖ = ‖y‖ := by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs, Real.Angle.cos_coe,
    InnerProductGeometry.cos_angle_sub_mul_norm_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)]

/-- The cosine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
adjacent side, version subtracting vectors. -/
/-
**Orientation.cos_oangle_sub_left_mul_norm_of_oangle_eq_pi_div_two** 是 Mathlib 中
的一个定理，位于命名空间 `Orientation`。
形式化陈述：cos_oangle_sub_left_mul_norm_of_oangle_eq_pi_div_two {x y : V} (h : o.oang
le x y = ↑(π / 2)) : Real.Angle.cos (o.oangle (x - y) x) * ‖x - y‖ = ‖x‖
参数：h : o.oangle x y = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b
· 使用定理 `Orientation.oangle_rev`：oangle_rev (x y : V) : o.oangle y x = -o.oangle 
x y
· 使用定理 `Orientation.oangle_neg_orientation_eq_neg`：oangle_neg_orientation_eq_neg
 (x y : V) : (-o).oangle x y = -o.oangle x y
· 使用定理 `Orientation.cos_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two`：cos_o
angle_sub_right_mul_norm_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑
(π / 2)) : Real.Angle.cos (o.oangle y (y - x)) * ‖y - x…

--- 原说明 ---
The cosine of an angle in a right-angled triangle multiplied by the hypotenuse e
quals the
adjacent side, version subtracting vectors.
-/
theorem cos_oangle_sub_left_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : Real.Angle.cos (o.oangle (x - y) x) * ‖x - y‖ = ‖x‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  exact (-o).cos_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two h

/-- The sine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
opposite side, version subtracting vectors. -/
/-
**Orientation.sin_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two** 是 Mathlib 
中的一个定理，位于命名空间 `Orientation`。
形式化陈述：sin_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two {x y : V} (h : o.oan
gle x y = ↑(π / 2)) : Real.Angle.sin (o.oangle y (y - x)) * ‖y - x‖ = ‖x‖
参数：h : o.oangle x y = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_sign_sub_right_swap`：oangle_sign_sub_right_swap (x y 
: V) : (o.oangle y (y - x)).sign = (o.oangle x y).sign
· 使用定理 `Real.Angle.sign_coe_pi_div_two`：sign_coe_pi_div_two : (↑(π / 2) : Angle)
.sign = 1
· 使用定理 `Orientation.oangle_eq_angle_of_sign_eq_one`：oangle_eq_angle_of_sign_eq_o
ne {x y : V} (h : (o.oangle x y).sign = 1) : o.oangle x y = InnerProductGeometry
.angle x y
· 使用定理 `Real.Angle.sin_coe`：sin_coe (x : Real) : sin (x : Angle) = Real.sin x
· 使用定理 `InnerProductGeometry.sin_angle_sub_mul_norm_of_inner_eq_zero`：sin_angle_
sub_mul_norm_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) : Real.sin (angle x (x 
- y)) * ‖x - y‖ = ‖y‖
· 使用定理 `Orientation.inner_rev_eq_zero_of_oangle_eq_pi_div_two`：inner_rev_eq_zero
_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : Real)) : ⟪y, x⟫ 
= 0

--- 原说明 ---
The sine of an angle in a right-angled triangle multiplied by the hypotenuse equ
als the
opposite side, version subtracting vectors.
-/
theorem sin_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : Real.Angle.sin (o.oangle y (y - x)) * ‖y - x‖ = ‖x‖ := by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs, Real.Angle.sin_coe,
    InnerProductGeometry.sin_angle_sub_mul_norm_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)]

/-- The sine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
opposite side, version subtracting vectors. -/
/-
**Orientation.sin_oangle_sub_left_mul_norm_of_oangle_eq_pi_div_two** 是 Mathlib 中
的一个定理，位于命名空间 `Orientation`。
形式化陈述：sin_oangle_sub_left_mul_norm_of_oangle_eq_pi_div_two {x y : V} (h : o.oang
le x y = ↑(π / 2)) : Real.Angle.sin (o.oangle (x - y) x) * ‖x - y‖ = ‖y‖
参数：h : o.oangle x y = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b
· 使用定理 `Orientation.oangle_rev`：oangle_rev (x y : V) : o.oangle y x = -o.oangle 
x y
· 使用定理 `Orientation.oangle_neg_orientation_eq_neg`：oangle_neg_orientation_eq_neg
 (x y : V) : (-o).oangle x y = -o.oangle x y
· 使用定理 `Orientation.sin_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two`：sin_o
angle_sub_right_mul_norm_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑
(π / 2)) : Real.Angle.sin (o.oangle y (y - x)) * ‖y - x…

--- 原说明 ---
The sine of an angle in a right-angled triangle multiplied by the hypotenuse equ
als the
opposite side, version subtracting vectors.
-/
theorem sin_oangle_sub_left_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : Real.Angle.sin (o.oangle (x - y) x) * ‖x - y‖ = ‖y‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  exact (-o).sin_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two h

/-- The tangent of an angle in a right-angled triangle multiplied by the adjacent side equals
the opposite side, version subtracting vectors. -/
/-
**Orientation.tan_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two** 是 Mathlib 
中的一个定理，位于命名空间 `Orientation`。
形式化陈述：tan_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two {x y : V} (h : o.oan
gle x y = ↑(π / 2)) : Real.Angle.tan (o.oangle y (y - x)) * ‖y‖ = ‖x‖
参数：h : o.oangle x y = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_sign_sub_right_swap`：oangle_sign_sub_right_swap (x y 
: V) : (o.oangle y (y - x)).sign = (o.oangle x y).sign
· 使用定理 `Real.Angle.sign_coe_pi_div_two`：sign_coe_pi_div_two : (↑(π / 2) : Angle)
.sign = 1
· 使用定理 `Orientation.oangle_eq_angle_of_sign_eq_one`：oangle_eq_angle_of_sign_eq_o
ne {x y : V} (h : (o.oangle x y).sign = 1) : o.oangle x y = InnerProductGeometry
.angle x y
· 使用定理 `Real.Angle.tan_coe`：tan_coe (x : Real) : tan (x : Angle) = Real.tan x
· 使用定理 `InnerProductGeometry.tan_angle_sub_mul_norm_of_inner_eq_zero`：tan_angle_
sub_mul_norm_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0 ∨ y = 0) :
 Real.tan (angle x (x - y)) * ‖x‖ = ‖y‖
· 使用定理 `Orientation.inner_rev_eq_zero_of_oangle_eq_pi_div_two`：inner_rev_eq_zero
_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : Real)) : ⟪y, x⟫ 
= 0
· 使用定理 `Orientation.right_ne_zero_of_oangle_eq_pi_div_two`：right_ne_zero_of_oang
le_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : Real)) : y != 0

--- 原说明 ---
The tangent of an angle in a right-angled triangle multiplied by the adjacent si
de equals
the opposite side, version subtracting vectors.
-/
theorem tan_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : Real.Angle.tan (o.oangle y (y - x)) * ‖y‖ = ‖x‖ := by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs, Real.Angle.tan_coe,
    InnerProductGeometry.tan_angle_sub_mul_norm_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)
      (Or.inl (o.right_ne_zero_of_oangle_eq_pi_div_two h))]

/-- The tangent of an angle in a right-angled triangle multiplied by the adjacent side equals
the opposite side, version subtracting vectors. -/
/-
**Orientation.tan_oangle_sub_left_mul_norm_of_oangle_eq_pi_div_two** 是 Mathlib 中
的一个定理，位于命名空间 `Orientation`。
形式化陈述：tan_oangle_sub_left_mul_norm_of_oangle_eq_pi_div_two {x y : V} (h : o.oang
le x y = ↑(π / 2)) : Real.Angle.tan (o.oangle (x - y) x) * ‖x‖ = ‖y‖
参数：h : o.oangle x y = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b
· 使用定理 `Orientation.oangle_rev`：oangle_rev (x y : V) : o.oangle y x = -o.oangle 
x y
· 使用定理 `Orientation.oangle_neg_orientation_eq_neg`：oangle_neg_orientation_eq_neg
 (x y : V) : (-o).oangle x y = -o.oangle x y
· 使用定理 `Orientation.tan_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two`：tan_o
angle_sub_right_mul_norm_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑
(π / 2)) : Real.Angle.tan (o.oangle y (y - x)) * ‖y‖ = …

--- 原说明 ---
The tangent of an angle in a right-angled triangle multiplied by the adjacent si
de equals
the opposite side, version subtracting vectors.
-/
theorem tan_oangle_sub_left_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : Real.Angle.tan (o.oangle (x - y) x) * ‖x‖ = ‖y‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  exact (-o).tan_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two h

/-- A side of a right-angled triangle divided by the cosine of the adjacent angle equals the
hypotenuse, version subtracting vectors. -/
/-
**Orientation.norm_div_cos_oangle_sub_right_of_oangle_eq_pi_div_two** 是 Mathlib 
中的一个定理，位于命名空间 `Orientation`。
形式化陈述：norm_div_cos_oangle_sub_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oan
gle x y = ↑(π / 2)) : ‖y‖ / Real.Angle.cos (o.oangle y (y - x)) = ‖y - x‖
参数：h : o.oangle x y = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_sign_sub_right_swap`：oangle_sign_sub_right_swap (x y 
: V) : (o.oangle y (y - x)).sign = (o.oangle x y).sign
· 使用定理 `Real.Angle.sign_coe_pi_div_two`：sign_coe_pi_div_two : (↑(π / 2) : Angle)
.sign = 1
· 使用定理 `Orientation.oangle_eq_angle_of_sign_eq_one`：oangle_eq_angle_of_sign_eq_o
ne {x y : V} (h : (o.oangle x y).sign = 1) : o.oangle x y = InnerProductGeometry
.angle x y
· 使用定理 `Real.Angle.cos_coe`：cos_coe (x : Real) : cos (x : Angle) = Real.cos x
· 使用定理 `InnerProductGeometry.norm_div_cos_angle_sub_of_inner_eq_zero`：norm_div_c
os_angle_sub_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0 ∨ y = 0) :
 ‖x‖ / Real.cos (angle x (x - y)) = ‖x - y‖
· 使用定理 `Orientation.inner_rev_eq_zero_of_oangle_eq_pi_div_two`：inner_rev_eq_zero
_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : Real)) : ⟪y, x⟫ 
= 0
· 使用定理 `Orientation.right_ne_zero_of_oangle_eq_pi_div_two`：right_ne_zero_of_oang
le_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : Real)) : y != 0

--- 原说明 ---
A side of a right-angled triangle divided by the cosine of the adjacent angle eq
uals the
hypotenuse, version subtracting vectors.
-/
theorem norm_div_cos_oangle_sub_right_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : ‖y‖ / Real.Angle.cos (o.oangle y (y - x)) = ‖y - x‖ := by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs, Real.Angle.cos_coe,
    InnerProductGeometry.norm_div_cos_angle_sub_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)
      (Or.inl (o.right_ne_zero_of_oangle_eq_pi_div_two h))]

/-- A side of a right-angled triangle divided by the cosine of the adjacent angle equals the
hypotenuse, version subtracting vectors. -/
/-
**Orientation.norm_div_cos_oangle_sub_left_of_oangle_eq_pi_div_two** 是 Mathlib 中
的一个定理，位于命名空间 `Orientation`。
形式化陈述：norm_div_cos_oangle_sub_left_of_oangle_eq_pi_div_two {x y : V} (h : o.oang
le x y = ↑(π / 2)) : ‖x‖ / Real.Angle.cos (o.oangle (x - y) x) = ‖x - y‖
参数：h : o.oangle x y = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b
· 使用定理 `Orientation.oangle_rev`：oangle_rev (x y : V) : o.oangle y x = -o.oangle 
x y
· 使用定理 `Orientation.oangle_neg_orientation_eq_neg`：oangle_neg_orientation_eq_neg
 (x y : V) : (-o).oangle x y = -o.oangle x y
· 使用定理 `Orientation.norm_div_cos_oangle_sub_right_of_oangle_eq_pi_div_two`：norm_
div_cos_oangle_sub_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑
(π / 2)) : ‖y‖ / Real.Angle.cos (o.oangle y (y - x)) = …

--- 原说明 ---
A side of a right-angled triangle divided by the cosine of the adjacent angle eq
uals the
hypotenuse, version subtracting vectors.
-/
theorem norm_div_cos_oangle_sub_left_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : ‖x‖ / Real.Angle.cos (o.oangle (x - y) x) = ‖x - y‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  exact (-o).norm_div_cos_oangle_sub_right_of_oangle_eq_pi_div_two h

/-- A side of a right-angled triangle divided by the sine of the opposite angle equals the
hypotenuse, version subtracting vectors. -/
/-
**Orientation.norm_div_sin_oangle_sub_right_of_oangle_eq_pi_div_two** 是 Mathlib 
中的一个定理，位于命名空间 `Orientation`。
形式化陈述：norm_div_sin_oangle_sub_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oan
gle x y = ↑(π / 2)) : ‖x‖ / Real.Angle.sin (o.oangle y (y - x)) = ‖y - x‖
参数：h : o.oangle x y = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_sign_sub_right_swap`：oangle_sign_sub_right_swap (x y 
: V) : (o.oangle y (y - x)).sign = (o.oangle x y).sign
· 使用定理 `Real.Angle.sign_coe_pi_div_two`：sign_coe_pi_div_two : (↑(π / 2) : Angle)
.sign = 1
· 使用定理 `Orientation.oangle_eq_angle_of_sign_eq_one`：oangle_eq_angle_of_sign_eq_o
ne {x y : V} (h : (o.oangle x y).sign = 1) : o.oangle x y = InnerProductGeometry
.angle x y
· 使用定理 `Real.Angle.sin_coe`：sin_coe (x : Real) : sin (x : Angle) = Real.sin x
· 使用定理 `InnerProductGeometry.norm_div_sin_angle_sub_of_inner_eq_zero`：norm_div_s
in_angle_sub_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x = 0 ∨ y != 0) :
 ‖y‖ / Real.sin (angle x (x - y)) = ‖x - y‖
· 使用定理 `Orientation.inner_rev_eq_zero_of_oangle_eq_pi_div_two`：inner_rev_eq_zero
_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : Real)) : ⟪y, x⟫ 
= 0
· 使用定理 `Orientation.left_ne_zero_of_oangle_eq_pi_div_two`：left_ne_zero_of_oangle
_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : Real)) : x != 0

--- 原说明 ---
A side of a right-angled triangle divided by the sine of the opposite angle equa
ls the
hypotenuse, version subtracting vectors.
-/
theorem norm_div_sin_oangle_sub_right_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : ‖x‖ / Real.Angle.sin (o.oangle y (y - x)) = ‖y - x‖ := by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs, Real.Angle.sin_coe,
    InnerProductGeometry.norm_div_sin_angle_sub_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)
      (Or.inr (o.left_ne_zero_of_oangle_eq_pi_div_two h))]

/-- A side of a right-angled triangle divided by the sine of the opposite angle equals the
hypotenuse, version subtracting vectors. -/
/-
**Orientation.norm_div_sin_oangle_sub_left_of_oangle_eq_pi_div_two** 是 Mathlib 中
的一个定理，位于命名空间 `Orientation`。
形式化陈述：norm_div_sin_oangle_sub_left_of_oangle_eq_pi_div_two {x y : V} (h : o.oang
le x y = ↑(π / 2)) : ‖y‖ / Real.Angle.sin (o.oangle (x - y) x) = ‖x - y‖
参数：h : o.oangle x y = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b
· 使用定理 `Orientation.oangle_rev`：oangle_rev (x y : V) : o.oangle y x = -o.oangle 
x y
· 使用定理 `Orientation.oangle_neg_orientation_eq_neg`：oangle_neg_orientation_eq_neg
 (x y : V) : (-o).oangle x y = -o.oangle x y
· 使用定理 `Orientation.norm_div_sin_oangle_sub_right_of_oangle_eq_pi_div_two`：norm_
div_sin_oangle_sub_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑
(π / 2)) : ‖x‖ / Real.Angle.sin (o.oangle y (y - x)) = …

--- 原说明 ---
A side of a right-angled triangle divided by the sine of the opposite angle equa
ls the
hypotenuse, version subtracting vectors.
-/
theorem norm_div_sin_oangle_sub_left_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : ‖y‖ / Real.Angle.sin (o.oangle (x - y) x) = ‖x - y‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  exact (-o).norm_div_sin_oangle_sub_right_of_oangle_eq_pi_div_two h

/-- A side of a right-angled triangle divided by the tangent of the opposite angle equals the
adjacent side, version subtracting vectors. -/
/-
**Orientation.norm_div_tan_oangle_sub_right_of_oangle_eq_pi_div_two** 是 Mathlib 
中的一个定理，位于命名空间 `Orientation`。
形式化陈述：norm_div_tan_oangle_sub_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oan
gle x y = ↑(π / 2)) : ‖x‖ / Real.Angle.tan (o.oangle y (y - x)) = ‖y‖
参数：h : o.oangle x y = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_sign_sub_right_swap`：oangle_sign_sub_right_swap (x y 
: V) : (o.oangle y (y - x)).sign = (o.oangle x y).sign
· 使用定理 `Real.Angle.sign_coe_pi_div_two`：sign_coe_pi_div_two : (↑(π / 2) : Angle)
.sign = 1
· 使用定理 `Orientation.oangle_eq_angle_of_sign_eq_one`：oangle_eq_angle_of_sign_eq_o
ne {x y : V} (h : (o.oangle x y).sign = 1) : o.oangle x y = InnerProductGeometry
.angle x y
· 使用定理 `Real.Angle.tan_coe`：tan_coe (x : Real) : tan (x : Angle) = Real.tan x
· 使用定理 `InnerProductGeometry.norm_div_tan_angle_sub_of_inner_eq_zero`：norm_div_t
an_angle_sub_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x = 0 ∨ y != 0) :
 ‖y‖ / Real.tan (angle x (x - y)) = ‖x‖
· 使用定理 `Orientation.inner_rev_eq_zero_of_oangle_eq_pi_div_two`：inner_rev_eq_zero
_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : Real)) : ⟪y, x⟫ 
= 0
· 使用定理 `Orientation.left_ne_zero_of_oangle_eq_pi_div_two`：left_ne_zero_of_oangle
_eq_pi_div_two {x y : V} (h : o.oangle x y = (π / 2 : Real)) : x != 0

--- 原说明 ---
A side of a right-angled triangle divided by the tangent of the opposite angle e
quals the
adjacent side, version subtracting vectors.
-/
theorem norm_div_tan_oangle_sub_right_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : ‖x‖ / Real.Angle.tan (o.oangle y (y - x)) = ‖y‖ := by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs, Real.Angle.tan_coe,
    InnerProductGeometry.norm_div_tan_angle_sub_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)
      (Or.inr (o.left_ne_zero_of_oangle_eq_pi_div_two h))]

/-- A side of a right-angled triangle divided by the tangent of the opposite angle equals the
adjacent side, version subtracting vectors. -/
/-
**Orientation.norm_div_tan_oangle_sub_left_of_oangle_eq_pi_div_two** 是 Mathlib 中
的一个定理，位于命名空间 `Orientation`。
形式化陈述：norm_div_tan_oangle_sub_left_of_oangle_eq_pi_div_two {x y : V} (h : o.oang
le x y = ↑(π / 2)) : ‖y‖ / Real.Angle.tan (o.oangle (x - y) x) = ‖x‖
参数：h : o.oangle x y = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b
· 使用定理 `Orientation.oangle_rev`：oangle_rev (x y : V) : o.oangle y x = -o.oangle 
x y
· 使用定理 `Orientation.oangle_neg_orientation_eq_neg`：oangle_neg_orientation_eq_neg
 (x y : V) : (-o).oangle x y = -o.oangle x y
· 使用定理 `Orientation.norm_div_tan_oangle_sub_right_of_oangle_eq_pi_div_two`：norm_
div_tan_oangle_sub_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑
(π / 2)) : ‖x‖ / Real.Angle.tan (o.oangle y (y - x)) = …

--- 原说明 ---
A side of a right-angled triangle divided by the tangent of the opposite angle e
quals the
adjacent side, version subtracting vectors.
-/
theorem norm_div_tan_oangle_sub_left_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : ‖y‖ / Real.Angle.tan (o.oangle (x - y) x) = ‖x‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  exact (-o).norm_div_tan_oangle_sub_right_of_oangle_eq_pi_div_two h

/-- An angle in a right-angled triangle expressed using `arctan`, where one side is a multiple
of a rotation of another by `π / 2`. -/
/-
**Orientation.oangle_add_right_smul_rotation_pi_div_two** 是 Mathlib 中的一个定理，位于命名空
间 `Orientation`。
形式化陈述：oangle_add_right_smul_rotation_pi_div_two {x : V} (h : x != 0) (r : Real) 
: o.oangle x (x + r • o.rotation (π / 2 : Real) x) = Real.arctan r
参数：h : x != 0；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_smul_right_of_neg`：oangle_smul_right_of_neg (x y : V)
 {r : Real} (hr : r < 0) : o.oangle x (r • y) = o.oangle x (-y)
· 使用定理 `Orientation.oangle_neg_right`：oangle_neg_right {x y : V} (hx : x != 0) (
hy : y != 0) : o.oangle x (-y) = o.oangle x y + π
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `SemilinearIsometryEquivClass.toSemilinearIsometryClass`：∀ {R : Type u_1}
 {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} (𝓕 : Type u_10) [inst : Semiring
 R]   [inst_1 : Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `Orientation.oangle_rotation_self_right`：oangle_rotation_self_right {x : 
V} (hx : x != 0) (θ : Real.Angle) : o.oangle x (o.rotation θ x) = θ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `Real.Angle.coe_add`：coe_add (x y : Real) : ↑(x + y : Real) = (↑x + ↑y : 
Angle)
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_halves`：∀ {K : Type u_1} [inst : DivisionSemiring K] [NeZero 2] (a :
 K), a / 2 + a / 2 = a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `Real.Angle.coe_two_pi`：coe_two_pi : ↑(2 * π : Real) = (0 : Angle)
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b
· 使用定理 `Orientation.oangle_rev`：oangle_rev (x y : V) : o.oangle y x = -o.oangle 
x y
· 使用定理 `Orientation.oangle_neg_orientation_eq_neg`：oangle_neg_orientation_eq_neg
 (x y : V) : (-o).oangle x y = -o.oangle x y
· 使用定理 `Orientation.oangle_add_right_eq_arctan_of_oangle_eq_pi_div_two`：oangle_a
dd_right_eq_arctan_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2
)) : o.oangle x (x + y) = Real.arctan (‖y‖ / ‖x‖)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
（共 52 条，此处仅展示前 30 条）

--- 原说明 ---
An angle in a right-angled triangle expressed using `arctan`, where one side is 
a multiple
of a rotation of another by `π / 2`.
-/
theorem oangle_add_right_smul_rotation_pi_div_two {x : V} (h : x ≠ 0) (r : ℝ) :
    o.oangle x (x + r • o.rotation (π / 2 : ℝ) x) = Real.arctan r := by
  rcases lt_trichotomy r 0 with (hr | rfl | hr)
  · have ha : o.oangle x (r • o.rotation (π / 2 : ℝ) x) = -(π / 2 : ℝ) := by
      rw [o.oangle_smul_right_of_neg _ _ hr, o.oangle_neg_right h, o.oangle_rotation_self_right h, ←
        sub_eq_zero, add_comm, sub_neg_eq_add, ← Real.Angle.coe_add, ← Real.Angle.coe_add,
        add_assoc, add_halves, ← two_mul, Real.Angle.coe_two_pi]
      simpa using h
    rw [← neg_inj, ← oangle_neg_orientation_eq_neg, neg_neg] at ha
    rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj, oangle_rev,
      (-o).oangle_add_right_eq_arctan_of_oangle_eq_pi_div_two ha, norm_smul,
      LinearIsometryEquiv.norm_map, mul_div_assoc, div_self (norm_ne_zero_iff.2 h), mul_one,
      Real.norm_eq_abs, abs_of_neg hr, Real.arctan_neg, Real.Angle.coe_neg, neg_neg]
  · simp
  · have ha : o.oangle x (r • o.rotation (π / 2 : ℝ) x) = (π / 2 : ℝ) := by
      rw [o.oangle_smul_right_of_pos _ _ hr, o.oangle_rotation_self_right h]
    rw [o.oangle_add_right_eq_arctan_of_oangle_eq_pi_div_two ha, norm_smul,
      LinearIsometryEquiv.norm_map, mul_div_assoc, div_self (norm_ne_zero_iff.2 h), mul_one,
      Real.norm_eq_abs, abs_of_pos hr]

/-- An angle in a right-angled triangle expressed using `arctan`, where one side is a multiple
of a rotation of another by `π / 2`. -/
/-
**Orientation.oangle_add_left_smul_rotation_pi_div_two** 是 Mathlib 中的一个定理，位于命名空间
 `Orientation`。
形式化陈述：oangle_add_left_smul_rotation_pi_div_two {x : V} (h : x != 0) (r : Real) :
 o.oangle (x + r • o.rotation (π / 2 : Real) x) (r • o.rotation (π / 2 : Real) x
) = Real.arctan r⁻¹
参数：h : x != 0；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle.congr_simp`：∀ {V : Type u_1} [inst : NormedAddCommGro
up V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Fact (Module.finrank ℝ V = 2)] 
  (o o_1 : Orientat…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Orientation.oangle_zero_right`：oangle_zero_right (x : V) : o.oangle x 0 
= 0
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `Real.arctan_zero`：arctan_zero : arctan 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b
· 使用定理 `Orientation.oangle_rev`：oangle_rev (x y : V) : o.oangle y x = -o.oangle 
x y
· 使用定理 `Orientation.oangle_neg_orientation_eq_neg`：oangle_neg_orientation_eq_neg
 (x y : V) : (-o).oangle x y = -o.oangle x y
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Orientation.rotation_neg_orientation_eq_neg`：rotation_neg_orientation_eq
_neg (θ : Real.Angle) : (-o).rotation θ = o.rotation (-θ)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `SemilinearIsometryEquivClass.toSemilinearIsometryClass`：∀ {R : Type u_1}
 {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} (𝓕 : Type u_10) [inst : Semiring
 R]   [inst_1 : Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `Orientation.rotation_rotation`：rotation_rotation (θ₁ θ₂ : Real.Angle) (x
 : V) : o.rotation θ₁ (o.rotation θ₂ x) = o.rotation (θ₁ + θ₂) x
· 使用定理 `Orientation.rotation.congr_simp`：∀ {V : Type u_1} [inst : NormedAddCommG
roup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Fact (Module.finrank ℝ V = 2)
]   (o o_1 : Orientat…
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `Orientation.rotation_zero`：rotation_zero : o.rotation 0 = LinearIsometry
Equiv.refl Real V
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
An angle in a right-angled triangle expressed using `arctan`, where one side is 
a multiple
of a rotation of another by `π / 2`.
-/
theorem oangle_add_left_smul_rotation_pi_div_two {x : V} (h : x ≠ 0) (r : ℝ) :
    o.oangle (x + r • o.rotation (π / 2 : ℝ) x) (r • o.rotation (π / 2 : ℝ) x)
      = Real.arctan r⁻¹ := by
  by_cases hr : r = 0; · simp [hr]
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj, ←
    neg_neg ((π / 2 : ℝ) : Real.Angle), ← rotation_neg_orientation_eq_neg, add_comm]
  have hx : x = r⁻¹ • (-o).rotation (π / 2 : ℝ) (r • (-o).rotation (-(π / 2 : ℝ)) x) := by simp [hr]
  nth_rw 3 [hx]
  refine (-o).oangle_add_right_smul_rotation_pi_div_two ?_ _
  simp [hr, h]

/-- The tangent of an angle in a right-angled triangle, where one side is a multiple of a
rotation of another by `π / 2`. -/
/-
**Orientation.tan_oangle_add_right_smul_rotation_pi_div_two** 是 Mathlib 中的一个定理，位
于命名空间 `Orientation`。
形式化陈述：tan_oangle_add_right_smul_rotation_pi_div_two {x : V} (h : x != 0) (r : Re
al) : Real.Angle.tan (o.oangle x (x + r • o.rotation (π / 2 : Real) x)) = r
参数：h : x != 0；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_add_right_smul_rotation_pi_div_two`：oangle_add_right_
smul_rotation_pi_div_two {x : V} (h : x != 0) (r : Real) : o.oangle x (x + r • o
.rotation (π / 2 : Real) x) = Real.arctan r
· 使用定理 `Real.Angle.tan_coe`：tan_coe (x : Real) : tan (x : Angle) = Real.tan x
· 使用定理 `Real.tan_arctan`：tan_arctan (x : Real) : tan (arctan x) = x

--- 原说明 ---
The tangent of an angle in a right-angled triangle, where one side is a multiple
 of a
rotation of another by `π / 2`.
-/
theorem tan_oangle_add_right_smul_rotation_pi_div_two {x : V} (h : x ≠ 0) (r : ℝ) :
    Real.Angle.tan (o.oangle x (x + r • o.rotation (π / 2 : ℝ) x)) = r := by
  rw [o.oangle_add_right_smul_rotation_pi_div_two h, Real.Angle.tan_coe, Real.tan_arctan]

/-- The tangent of an angle in a right-angled triangle, where one side is a multiple of a
rotation of another by `π / 2`. -/
/-
**Orientation.tan_oangle_add_left_smul_rotation_pi_div_two** 是 Mathlib 中的一个定理，位于
命名空间 `Orientation`。
形式化陈述：tan_oangle_add_left_smul_rotation_pi_div_two {x : V} (h : x != 0) (r : Rea
l) : Real.Angle.tan (o.oangle (x + r • o.rotation (π / 2 : Real) x) (r • o.rotat
ion (π / 2 : Real) x)) = r⁻¹
参数：h : x != 0；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle_add_left_smul_rotation_pi_div_two`：oangle_add_left_sm
ul_rotation_pi_div_two {x : V} (h : x != 0) (r : Real) : o.oangle (x + r • o.rot
ation (π / 2 : Real) x) (r • o.rotation (π…
· 使用定理 `Real.Angle.tan_coe`：tan_coe (x : Real) : tan (x : Angle) = Real.tan x
· 使用定理 `Real.tan_arctan`：tan_arctan (x : Real) : tan (arctan x) = x

--- 原说明 ---
The tangent of an angle in a right-angled triangle, where one side is a multiple
 of a
rotation of another by `π / 2`.
-/
theorem tan_oangle_add_left_smul_rotation_pi_div_two {x : V} (h : x ≠ 0) (r : ℝ) :
    Real.Angle.tan (o.oangle (x + r • o.rotation (π / 2 : ℝ) x) (r • o.rotation (π / 2 : ℝ) x)) =
      r⁻¹ := by
  rw [o.oangle_add_left_smul_rotation_pi_div_two h, Real.Angle.tan_coe, Real.tan_arctan]

/-- An angle in a right-angled triangle expressed using `arctan`, where one side is a multiple
of a rotation of another by `π / 2`, version subtracting vectors. -/
/-
**Orientation.oangle_sub_right_smul_rotation_pi_div_two** 是 Mathlib 中的一个定理，位于命名空
间 `Orientation`。
形式化陈述：oangle_sub_right_smul_rotation_pi_div_two {x : V} (h : x != 0) (r : Real) 
: o.oangle (r • o.rotation (π / 2 : Real) x) (r • o.rotation (π / 2 : Real) x - 
x) = Real.arctan r⁻¹
参数：h : x != 0；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle.congr_simp`：∀ {V : Type u_1} [inst : NormedAddCommGro
up V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Fact (Module.finrank ℝ V = 2)] 
  (o o_1 : Orientat…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `Orientation.oangle_zero_left`：oangle_zero_left (x : V) : o.oangle 0 x = 
0
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `Real.arctan_zero`：arctan_zero : arctan 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `SemilinearIsometryEquivClass.toSemilinearIsometryClass`：∀ {R : Type u_1}
 {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} (𝓕 : Type u_10) [inst : Semiring
 R]   [inst_1 : Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `Orientation.rotation_rotation`：rotation_rotation (θ₁ θ₂ : Real.Angle) (x
 : V) : o.rotation θ₁ (o.rotation θ₂ x) = o.rotation (θ₁ + θ₂) x
· 使用定理 `Orientation.rotation.congr_simp`：∀ {V : Type u_1} [inst : NormedAddCommG
roup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Fact (Module.finrank ℝ V = 2)
]   (o o_1 : Orientat…
· 使用定理 `add_halves`：∀ {K : Type u_1} [inst : DivisionSemiring K] [NeZero 2] (a :
 K), a / 2 + a / 2 = a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Orientation.rotation_pi`：rotation_pi : o.rotation π = LinearIsometryEqui
v.neg Real
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Orientation.oangle_add_right_smul_rotation_pi_div_two`：oangle_add_right_
smul_rotation_pi_div_two {x : V} (h : x != 0) (r : Real) : o.oangle x (x + r • o
.rotation (π / 2 : Real) x) = Real.arctan r
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
An angle in a right-angled triangle expressed using `arctan`, where one side is 
a multiple
of a rotation of another by `π / 2`, version subtracting vectors.
-/
theorem oangle_sub_right_smul_rotation_pi_div_two {x : V} (h : x ≠ 0) (r : ℝ) :
    o.oangle (r • o.rotation (π / 2 : ℝ) x) (r • o.rotation (π / 2 : ℝ) x - x)
      = Real.arctan r⁻¹ := by
  by_cases hr : r = 0; · simp [hr]
  have hx : -x = r⁻¹ • o.rotation (π / 2 : ℝ) (r • o.rotation (π / 2 : ℝ) x) := by
    simp [hr, ← Real.Angle.coe_add]
  rw [sub_eq_add_neg, hx, o.oangle_add_right_smul_rotation_pi_div_two]
  simpa [hr] using h

/-- An angle in a right-angled triangle expressed using `arctan`, where one side is a multiple
of a rotation of another by `π / 2`, version subtracting vectors. -/
/-
**Orientation.oangle_sub_left_smul_rotation_pi_div_two** 是 Mathlib 中的一个定理，位于命名空间
 `Orientation`。
形式化陈述：oangle_sub_left_smul_rotation_pi_div_two {x : V} (h : x != 0) (r : Real) :
 o.oangle (x - r • o.rotation (π / 2 : Real) x) x = Real.arctan r
参数：h : x != 0；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.oangle.congr_simp`：∀ {V : Type u_1} [inst : NormedAddCommGro
up V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Fact (Module.finrank ℝ V = 2)] 
  (o o_1 : Orientat…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Orientation.oangle_self`：oangle_self (x : V) : o.oangle x x = 0
· 使用定理 `Real.arctan_zero`：arctan_zero : arctan 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `SemilinearIsometryEquivClass.toSemilinearIsometryClass`：∀ {R : Type u_1}
 {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} (𝓕 : Type u_10) [inst : Semiring
 R]   [inst_1 : Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Orientation.rotation_rotation`：rotation_rotation (θ₁ θ₂ : Real.Angle) (x
 : V) : o.rotation θ₁ (o.rotation θ₂ x) = o.rotation (θ₁ + θ₂) x
· 使用定理 `Orientation.rotation.congr_simp`：∀ {V : Type u_1} [inst : NormedAddCommG
roup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Fact (Module.finrank ℝ V = 2)
]   (o o_1 : Orientat…
· 使用定理 `add_halves`：∀ {K : Type u_1} [inst : DivisionSemiring K] [NeZero 2] (a :
 K), a / 2 + a / 2 = a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Orientation.rotation_pi`：rotation_pi : o.rotation π = LinearIsometryEqui
v.neg Real
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
An angle in a right-angled triangle expressed using `arctan`, where one side is 
a multiple
of a rotation of another by `π / 2`, version subtracting vectors.
-/
theorem oangle_sub_left_smul_rotation_pi_div_two {x : V} (h : x ≠ 0) (r : ℝ) :
    o.oangle (x - r • o.rotation (π / 2 : ℝ) x) x = Real.arctan r := by
  by_cases hr : r = 0; · simp [hr]
  have hx : x = r⁻¹ • o.rotation (π / 2 : ℝ) (-(r • o.rotation (π / 2 : ℝ) x)) := by
    simp [hr, ← Real.Angle.coe_add]
  rw [sub_eq_add_neg, add_comm]
  nth_rw 3 [hx]
  nth_rw 2 [hx]
  rw [o.oangle_add_left_smul_rotation_pi_div_two, inv_inv]
  simpa [hr] using h

end Orientation

namespace EuclideanGeometry

open Module

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [hd2 : Fact (finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]

/-- An angle in a right-angled triangle expressed using `arccos`. -/
/-
**EuclideanGeometry.oangle_right_eq_arccos_of_oangle_eq_pi_div_two** 是 Mathlib 中
的一个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：oangle_right_eq_arccos_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂
 p₃ = ↑(π / 2)) : ∡ p₂ p₃ p₁ = Real.arccos (dist p₃ p₂ / dist p₁ p₃)
参数：h : ∡ p₁ p₂ p₃ = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.oangle_rotate_sign`：oangle_rotate_sign (p₁ p₂ p₃ : P) 
: (∡ p₂ p₃ p₁).sign = (∡ p₁ p₂ p₃).sign
· 使用定理 `Real.Angle.sign_coe_pi_div_two`：sign_coe_pi_div_two : (↑(π / 2) : Angle)
.sign = 1
· 使用定理 `EuclideanGeometry.oangle_eq_angle_of_sign_eq_one`：oangle_eq_angle_of_sig
n_eq_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1) : ∡ p₁ p₂ p₃ = ∠ p₁ p₂ p₃
· 使用定理 `EuclideanGeometry.angle_eq_arccos_of_angle_eq_pi_div_two`：angle_eq_arcco
s_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) : ∠ p₂ p₃ p₁ = 
Real.arccos (dist p₃ p₂ / dist p₁ p₃)
· 使用定理 `EuclideanGeometry.angle_eq_pi_div_two_of_oangle_eq_pi_div_two`：angle_eq_
pi_div_two_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : 
∠ p₁ p₂ p₃ = π / 2

--- 原说明 ---
An angle in a right-angled triangle expressed using `arccos`.
-/
theorem oangle_right_eq_arccos_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    ∡ p₂ p₃ p₁ = Real.arccos (dist p₃ p₂ / dist p₁ p₃) := by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs,
    angle_eq_arccos_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)]

/-- An angle in a right-angled triangle expressed using `arccos`. -/
/-
**EuclideanGeometry.oangle_left_eq_arccos_of_oangle_eq_pi_div_two** 是 Mathlib 中的
一个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：oangle_left_eq_arccos_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ 
p₃ = ↑(π / 2)) : ∡ p₃ p₁ p₂ = Real.arccos (dist p₁ p₂ / dist p₁ p₃)
参数：h : ∡ p₁ p₂ p₃ = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanGeometry.oangle_rotate_sign`：oangle_rotate_sign (p₁ p₂ p₃ : P) 
: (∡ p₂ p₃ p₁).sign = (∡ p₁ p₂ p₃).sign
· 使用定理 `Real.Angle.sign_coe_pi_div_two`：sign_coe_pi_div_two : (↑(π / 2) : Angle)
.sign = 1
· 使用定理 `EuclideanGeometry.oangle_eq_angle_of_sign_eq_one`：oangle_eq_angle_of_sig
n_eq_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1) : ∡ p₁ p₂ p₃ = ∠ p₁ p₂ p₃
· 使用定理 `EuclideanGeometry.angle_comm`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `EuclideanGeometry.angle_eq_arccos_of_angle_eq_pi_div_two`：angle_eq_arcco
s_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) : ∠ p₂ p₃ p₁ = 
Real.arccos (dist p₃ p₂ / dist p₁ p₃)
· 使用定理 `EuclideanGeometry.angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two`：angle
_rev_eq_pi_div_two_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π 
/ 2)) : ∠ p₃ p₂ p₁ = π / 2
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x

--- 原说明 ---
An angle in a right-angled triangle expressed using `arccos`.
-/
theorem oangle_left_eq_arccos_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    ∡ p₃ p₁ p₂ = Real.arccos (dist p₁ p₂ / dist p₁ p₃) := by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs, angle_comm,
    angle_eq_arccos_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h),
    dist_comm p₁ p₃]

/-- An angle in a right-angled triangle expressed using `arcsin`. -/
/-
**EuclideanGeometry.oangle_right_eq_arcsin_of_oangle_eq_pi_div_two** 是 Mathlib 中
的一个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：oangle_right_eq_arcsin_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂
 p₃ = ↑(π / 2)) : ∡ p₂ p₃ p₁ = Real.arcsin (dist p₁ p₂ / dist p₁ p₃)
参数：h : ∡ p₁ p₂ p₃ = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.oangle_rotate_sign`：oangle_rotate_sign (p₁ p₂ p₃ : P) 
: (∡ p₂ p₃ p₁).sign = (∡ p₁ p₂ p₃).sign
· 使用定理 `Real.Angle.sign_coe_pi_div_two`：sign_coe_pi_div_two : (↑(π / 2) : Angle)
.sign = 1
· 使用定理 `EuclideanGeometry.oangle_eq_angle_of_sign_eq_one`：oangle_eq_angle_of_sig
n_eq_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1) : ∡ p₁ p₂ p₃ = ∠ p₁ p₂ p₃
· 使用定理 `EuclideanGeometry.angle_eq_arcsin_of_angle_eq_pi_div_two`：angle_eq_arcsi
n_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) (h0 : p₁ != p₂ 
∨ p₃ != p₂) : ∠ p₂ p₃ p₁ = Real.arcsin (dist p…
· 使用定理 `EuclideanGeometry.angle_eq_pi_div_two_of_oangle_eq_pi_div_two`：angle_eq_
pi_div_two_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : 
∠ p₁ p₂ p₃ = π / 2
· 使用定理 `EuclideanGeometry.left_ne_of_oangle_eq_pi_div_two`：left_ne_of_oangle_eq_
pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (π / 2 : Real)) : p₁ != p₂

--- 原说明 ---
An angle in a right-angled triangle expressed using `arcsin`.
-/
theorem oangle_right_eq_arcsin_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    ∡ p₂ p₃ p₁ = Real.arcsin (dist p₁ p₂ / dist p₁ p₃) := by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs,
    angle_eq_arcsin_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inl (left_ne_of_oangle_eq_pi_div_two h))]

/-- An angle in a right-angled triangle expressed using `arcsin`. -/
/-
**EuclideanGeometry.oangle_left_eq_arcsin_of_oangle_eq_pi_div_two** 是 Mathlib 中的
一个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：oangle_left_eq_arcsin_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ 
p₃ = ↑(π / 2)) : ∡ p₃ p₁ p₂ = Real.arcsin (dist p₃ p₂ / dist p₁ p₃)
参数：h : ∡ p₁ p₂ p₃ = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanGeometry.oangle_rotate_sign`：oangle_rotate_sign (p₁ p₂ p₃ : P) 
: (∡ p₂ p₃ p₁).sign = (∡ p₁ p₂ p₃).sign
· 使用定理 `Real.Angle.sign_coe_pi_div_two`：sign_coe_pi_div_two : (↑(π / 2) : Angle)
.sign = 1
· 使用定理 `EuclideanGeometry.oangle_eq_angle_of_sign_eq_one`：oangle_eq_angle_of_sig
n_eq_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1) : ∡ p₁ p₂ p₃ = ∠ p₁ p₂ p₃
· 使用定理 `EuclideanGeometry.angle_comm`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `EuclideanGeometry.angle_eq_arcsin_of_angle_eq_pi_div_two`：angle_eq_arcsi
n_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) (h0 : p₁ != p₂ 
∨ p₃ != p₂) : ∠ p₂ p₃ p₁ = Real.arcsin (dist p…
· 使用定理 `EuclideanGeometry.angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two`：angle
_rev_eq_pi_div_two_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π 
/ 2)) : ∠ p₃ p₂ p₁ = π / 2
· 使用定理 `EuclideanGeometry.left_ne_of_oangle_eq_pi_div_two`：left_ne_of_oangle_eq_
pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (π / 2 : Real)) : p₁ != p₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x

--- 原说明 ---
An angle in a right-angled triangle expressed using `arcsin`.
-/
theorem oangle_left_eq_arcsin_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    ∡ p₃ p₁ p₂ = Real.arcsin (dist p₃ p₂ / dist p₁ p₃) := by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs, angle_comm,
    angle_eq_arcsin_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inr (left_ne_of_oangle_eq_pi_div_two h)),
    dist_comm p₁ p₃]

/-- An angle in a right-angled triangle expressed using `arctan`. -/
/-
**EuclideanGeometry.oangle_right_eq_arctan_of_oangle_eq_pi_div_two** 是 Mathlib 中
的一个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：oangle_right_eq_arctan_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂
 p₃ = ↑(π / 2)) : ∡ p₂ p₃ p₁ = Real.arctan (dist p₁ p₂ / dist p₃ p₂)
参数：h : ∡ p₁ p₂ p₃ = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.oangle_rotate_sign`：oangle_rotate_sign (p₁ p₂ p₃ : P) 
: (∡ p₂ p₃ p₁).sign = (∡ p₁ p₂ p₃).sign
· 使用定理 `Real.Angle.sign_coe_pi_div_two`：sign_coe_pi_div_two : (↑(π / 2) : Angle)
.sign = 1
· 使用定理 `EuclideanGeometry.oangle_eq_angle_of_sign_eq_one`：oangle_eq_angle_of_sig
n_eq_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1) : ∡ p₁ p₂ p₃ = ∠ p₁ p₂ p₃
· 使用定理 `EuclideanGeometry.angle_eq_arctan_of_angle_eq_pi_div_two`：angle_eq_arcta
n_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) (h0 : p₃ != p₂)
 : ∠ p₂ p₃ p₁ = Real.arctan (dist p₁ p₂ / dist…
· 使用定理 `EuclideanGeometry.angle_eq_pi_div_two_of_oangle_eq_pi_div_two`：angle_eq_
pi_div_two_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : 
∠ p₁ p₂ p₃ = π / 2
· 使用定理 `EuclideanGeometry.right_ne_of_oangle_eq_pi_div_two`：right_ne_of_oangle_e
q_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (π / 2 : Real)) : p₃ != p₂

--- 原说明 ---
An angle in a right-angled triangle expressed using `arctan`.
-/
theorem oangle_right_eq_arctan_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    ∡ p₂ p₃ p₁ = Real.arctan (dist p₁ p₂ / dist p₃ p₂) := by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs,
    angle_eq_arctan_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (right_ne_of_oangle_eq_pi_div_two h)]

/-- An angle in a right-angled triangle expressed using `arctan`. -/
/-
**EuclideanGeometry.oangle_left_eq_arctan_of_oangle_eq_pi_div_two** 是 Mathlib 中的
一个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：oangle_left_eq_arctan_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ 
p₃ = ↑(π / 2)) : ∡ p₃ p₁ p₂ = Real.arctan (dist p₃ p₂ / dist p₁ p₂)
参数：h : ∡ p₁ p₂ p₃ = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanGeometry.oangle_rotate_sign`：oangle_rotate_sign (p₁ p₂ p₃ : P) 
: (∡ p₂ p₃ p₁).sign = (∡ p₁ p₂ p₃).sign
· 使用定理 `Real.Angle.sign_coe_pi_div_two`：sign_coe_pi_div_two : (↑(π / 2) : Angle)
.sign = 1
· 使用定理 `EuclideanGeometry.oangle_eq_angle_of_sign_eq_one`：oangle_eq_angle_of_sig
n_eq_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1) : ∡ p₁ p₂ p₃ = ∠ p₁ p₂ p₃
· 使用定理 `EuclideanGeometry.angle_comm`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `EuclideanGeometry.angle_eq_arctan_of_angle_eq_pi_div_two`：angle_eq_arcta
n_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) (h0 : p₃ != p₂)
 : ∠ p₂ p₃ p₁ = Real.arctan (dist p₁ p₂ / dist…
· 使用定理 `EuclideanGeometry.angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two`：angle
_rev_eq_pi_div_two_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π 
/ 2)) : ∠ p₃ p₂ p₁ = π / 2
· 使用定理 `EuclideanGeometry.left_ne_of_oangle_eq_pi_div_two`：left_ne_of_oangle_eq_
pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (π / 2 : Real)) : p₁ != p₂

--- 原说明 ---
An angle in a right-angled triangle expressed using `arctan`.
-/
theorem oangle_left_eq_arctan_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    ∡ p₃ p₁ p₂ = Real.arctan (dist p₃ p₂ / dist p₁ p₂) := by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs, angle_comm,
    angle_eq_arctan_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (left_ne_of_oangle_eq_pi_div_two h)]

/-- An oriented angle in a right-angled triangle (even a degenerate one) has absolute value less
than `π / 2`. The right-angled property is expressed using unoriented angles to cover either
orientation of right-angled triangles and include degenerate cases. -/
/-
**EuclideanGeometry.abs_oangle_toReal_lt_pi_div_two_of_angle_eq_pi_div_two** 是 M
athlib 中的一个引理，位于命名空间 `EuclideanGeometry`。
形式化陈述：abs_oangle_toReal_lt_pi_div_two_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h :
 ∠ p₁ p₂ p₃ = π / 2) : |(∡ p₂ p₃ p₁).toReal| < π / 2
参数：h : ∠ p₁ p₂ p₃ = π / 2。
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
· 使用定理 `EuclideanGeometry.oangle.congr_simp`：∀ {V : Type u_1} {P : Type u_2} [in
st : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpac
e P]   [inst_3 : NormedAd…
· 使用定理 `EuclideanGeometry.oangle_self_left`：oangle_self_left (p₁ p₂ : P) : ∡ p₁ 
p₁ p₂ = 0
· 使用定理 `Real.Angle.toReal_zero`：toReal_zero : (0 : Angle).toReal = 0
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `EuclideanGeometry.oangle_self_right`：oangle_self_right (p₁ p₂ : P) : ∡ p
₁ p₂ p₂ = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanGeometry.angle_eq_abs_oangle_toReal`：angle_eq_abs_oangle_toReal
 {p p₁ p₂ : P} (hp₁ : p₁ != p) (hp₂ : p₂ != p) : ∠ p₁ p p₂ = |(∡ p₁ p p₂).toReal
|
· 使用定理 `EuclideanGeometry.angle_lt_pi_div_two_of_angle_eq_pi_div_two`：angle_lt_p
i_div_two_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) (h0 : p
₃ != p₂) : ∠ p₂ p₃ p₁ < π / 2
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a

--- 原说明 ---
An oriented angle in a right-angled triangle (even a degenerate one) has absolut
e value less
than `π / 2`. The right-angled property is expressed using unoriented angles to 
cover either
orientation of right-angled triangles and include degenerate cases.
-/
lemma abs_oangle_toReal_lt_pi_div_two_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∠ p₁ p₂ p₃ = π / 2) : |(∡ p₂ p₃ p₁).toReal| < π / 2 := by
  by_cases hp₂ : p₂ = p₃
  · simp [hp₂, Real.pi_pos]
  by_cases hp₁ : p₁ = p₃
  · simp [hp₁, Real.pi_pos]
  rw [← angle_eq_abs_oangle_toReal hp₂ hp₁]
  exact angle_lt_pi_div_two_of_angle_eq_pi_div_two h (Ne.symm hp₂)

/-- Two oriented angles in right-angled triangles are equal if twice those angles are equal. -/
/-
**EuclideanGeometry.oangle_eq_oangle_of_two_zsmul_eq_of_angle_eq_pi_div_two** 是 
Mathlib 中的一个引理，位于命名空间 `EuclideanGeometry`。
形式化陈述：oangle_eq_oangle_of_two_zsmul_eq_of_angle_eq_pi_div_two {p₁ p₂ p₃ p₄ p₅ p₆
 : P} (h : (2 : Int) • ∡ p₂ p₃ p₁ = (2 : Int) • ∡ p₅ p₆ p₄) (h₁₂₃ : ∠ p₁ p₂ p₃ =
 π / 2) (h₄₅₆ : ∠ p₄ p₅ p₆ = π / 2) : ∡ p₂ p₃ p₁ = ∡ p₅ p₆ p₄
参数：h : (2 : Int) • ∡ p₂ p₃ p₁ = (2 : Int) • ∡ p₅ p₆ p₄；h₁₂₃ : ∠ p₁ p₂ p₃ = π / 2
；h₄₅₆ : ∠ p₄ p₅ p₆ = π / 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Real.Angle.two_zsmul_eq_iff_eq_of_abs_toReal_lt_pi_div_two`：two_zsmul_eq
_iff_eq_of_abs_toReal_lt_pi_div_two {θ ψ : Angle} (hθ : |θ.toReal| < π / 2) (hψ 
: |ψ.toReal| < π / 2) : (2 : Int) • θ = (2 : Int…
· 使用引理 `EuclideanGeometry.abs_oangle_toReal_lt_pi_div_two_of_angle_eq_pi_div_two
`：abs_oangle_toReal_lt_pi_div_two_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p
₁ p₂ p₃ = π / 2) : |(∡ p₂ p₃ p₁).toReal| < π / 2

--- 原说明 ---
Two oriented angles in right-angled triangles are equal if twice those angles ar
e equal.
-/
lemma oangle_eq_oangle_of_two_zsmul_eq_of_angle_eq_pi_div_two {p₁ p₂ p₃ p₄ p₅ p₆ : P}
    (h : (2 : ℤ) • ∡ p₂ p₃ p₁ = (2 : ℤ) • ∡ p₅ p₆ p₄) (h₁₂₃ : ∠ p₁ p₂ p₃ = π / 2)
    (h₄₅₆ : ∠ p₄ p₅ p₆ = π / 2) : ∡ p₂ p₃ p₁ = ∡ p₅ p₆ p₄ := by
  rwa [Real.Angle.two_zsmul_eq_iff_eq_of_abs_toReal_lt_pi_div_two
    (abs_oangle_toReal_lt_pi_div_two_of_angle_eq_pi_div_two h₁₂₃)
    (abs_oangle_toReal_lt_pi_div_two_of_angle_eq_pi_div_two h₄₅₆)] at h

/-- Two oriented angles in oppositely-oriented right-angled triangles are equal if twice those
angles are equal. -/
/-
**EuclideanGeometry.oangle_eq_oangle_rev_of_two_zsmul_eq_of_angle_eq_pi_div_two*
* 是 Mathlib 中的一个引理，位于命名空间 `EuclideanGeometry`。
形式化陈述：oangle_eq_oangle_rev_of_two_zsmul_eq_of_angle_eq_pi_div_two {p₁ p₂ p₃ p₄ p
₅ p₆ : P} (h : (2 : Int) • ∡ p₂ p₃ p₁ = (2 : Int) • ∡ p₄ p₆ p₅) (h₁₂₃ : ∠ p₁ p₂ 
p₃ = π / 2) (h₄₅₆ : ∠ p₄ p₅ p₆ = π / 2) : ∡ p₂ p₃ p₁ = ∡ p₄ p₆ p₅
参数：h : (2 : Int) • ∡ p₂ p₃ p₁ = (2 : Int) • ∡ p₄ p₆ p₅；h₁₂₃ : ∠ p₁ p₂ p₃ = π / 2
；h₄₅₆ : ∠ p₄ p₅ p₆ = π / 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Real.Angle.two_zsmul_eq_iff_eq_of_abs_toReal_lt_pi_div_two`：two_zsmul_eq
_iff_eq_of_abs_toReal_lt_pi_div_two {θ ψ : Angle} (hθ : |θ.toReal| < π / 2) (hψ 
: |ψ.toReal| < π / 2) : (2 : Int) • θ = (2 : Int…
· 使用引理 `EuclideanGeometry.abs_oangle_toReal_lt_pi_div_two_of_angle_eq_pi_div_two
`：abs_oangle_toReal_lt_pi_div_two_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p
₁ p₂ p₃ = π / 2) : |(∡ p₂ p₃ p₁).toReal| < π / 2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.oangle_rev`：oangle_rev (p₁ p₂ p₃ : P) : ∡ p₃ p₂ p₁ = -
∡ p₁ p₂ p₃
· 使用定理 `Real.Angle.abs_toReal_neg`：∀ (θ : Real.Angle), |(-θ).toReal| = |θ.toReal
|

--- 原说明 ---
Two oriented angles in oppositely-oriented right-angled triangles are equal if t
wice those
angles are equal.
-/
lemma oangle_eq_oangle_rev_of_two_zsmul_eq_of_angle_eq_pi_div_two {p₁ p₂ p₃ p₄ p₅ p₆ : P}
    (h : (2 : ℤ) • ∡ p₂ p₃ p₁ = (2 : ℤ) • ∡ p₄ p₆ p₅) (h₁₂₃ : ∠ p₁ p₂ p₃ = π / 2)
    (h₄₅₆ : ∠ p₄ p₅ p₆ = π / 2) : ∡ p₂ p₃ p₁ = ∡ p₄ p₆ p₅ := by
  refine (Real.Angle.two_zsmul_eq_iff_eq_of_abs_toReal_lt_pi_div_two
    (abs_oangle_toReal_lt_pi_div_two_of_angle_eq_pi_div_two h₁₂₃) ?_).1 h
  rw [oangle_rev, Real.Angle.abs_toReal_neg]
  exact abs_oangle_toReal_lt_pi_div_two_of_angle_eq_pi_div_two h₄₅₆

/-- The cosine of an angle in a right-angled triangle as a ratio of sides. -/
/-
**EuclideanGeometry.cos_oangle_right_of_oangle_eq_pi_div_two** 是 Mathlib 中的一个定理，
位于命名空间 `EuclideanGeometry`。
形式化陈述：cos_oangle_right_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = 
↑(π / 2)) : Real.Angle.cos (∡ p₂ p₃ p₁) = dist p₃ p₂ / dist p₁ p₃
参数：h : ∡ p₁ p₂ p₃ = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.oangle_rotate_sign`：oangle_rotate_sign (p₁ p₂ p₃ : P) 
: (∡ p₂ p₃ p₁).sign = (∡ p₁ p₂ p₃).sign
· 使用定理 `Real.Angle.sign_coe_pi_div_two`：sign_coe_pi_div_two : (↑(π / 2) : Angle)
.sign = 1
· 使用定理 `EuclideanGeometry.oangle_eq_angle_of_sign_eq_one`：oangle_eq_angle_of_sig
n_eq_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1) : ∡ p₁ p₂ p₃ = ∠ p₁ p₂ p₃
· 使用定理 `Real.Angle.cos_coe`：cos_coe (x : Real) : cos (x : Angle) = Real.cos x
· 使用定理 `EuclideanGeometry.cos_angle_of_angle_eq_pi_div_two`：cos_angle_of_angle_e
q_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) : Real.cos (∠ p₂ p₃ p₁) = d
ist p₃ p₂ / dist p₁ p₃
· 使用定理 `EuclideanGeometry.angle_eq_pi_div_two_of_oangle_eq_pi_div_two`：angle_eq_
pi_div_two_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : 
∠ p₁ p₂ p₃ = π / 2

--- 原说明 ---
The cosine of an angle in a right-angled triangle as a ratio of sides.
-/
theorem cos_oangle_right_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    Real.Angle.cos (∡ p₂ p₃ p₁) = dist p₃ p₂ / dist p₁ p₃ := by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs, Real.Angle.cos_coe,
    cos_angle_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)]

/-- The cosine of an angle in a right-angled triangle as a ratio of sides. -/
/-
**EuclideanGeometry.cos_oangle_left_of_oangle_eq_pi_div_two** 是 Mathlib 中的一个定理，位
于命名空间 `EuclideanGeometry`。
形式化陈述：cos_oangle_left_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑
(π / 2)) : Real.Angle.cos (∡ p₃ p₁ p₂) = dist p₁ p₂ / dist p₁ p₃
参数：h : ∡ p₁ p₂ p₃ = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanGeometry.oangle_rotate_sign`：oangle_rotate_sign (p₁ p₂ p₃ : P) 
: (∡ p₂ p₃ p₁).sign = (∡ p₁ p₂ p₃).sign
· 使用定理 `Real.Angle.sign_coe_pi_div_two`：sign_coe_pi_div_two : (↑(π / 2) : Angle)
.sign = 1
· 使用定理 `EuclideanGeometry.oangle_eq_angle_of_sign_eq_one`：oangle_eq_angle_of_sig
n_eq_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1) : ∡ p₁ p₂ p₃ = ∠ p₁ p₂ p₃
· 使用定理 `EuclideanGeometry.angle_comm`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `Real.Angle.cos_coe`：cos_coe (x : Real) : cos (x : Angle) = Real.cos x
· 使用定理 `EuclideanGeometry.cos_angle_of_angle_eq_pi_div_two`：cos_angle_of_angle_e
q_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) : Real.cos (∠ p₂ p₃ p₁) = d
ist p₃ p₂ / dist p₁ p₃
· 使用定理 `EuclideanGeometry.angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two`：angle
_rev_eq_pi_div_two_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π 
/ 2)) : ∠ p₃ p₂ p₁ = π / 2
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x

--- 原说明 ---
The cosine of an angle in a right-angled triangle as a ratio of sides.
-/
theorem cos_oangle_left_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    Real.Angle.cos (∡ p₃ p₁ p₂) = dist p₁ p₂ / dist p₁ p₃ := by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs, angle_comm, Real.Angle.cos_coe,
    cos_angle_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h),
    dist_comm p₁ p₃]

/-- The sine of an angle in a right-angled triangle as a ratio of sides. -/
/-
**EuclideanGeometry.sin_oangle_right_of_oangle_eq_pi_div_two** 是 Mathlib 中的一个定理，
位于命名空间 `EuclideanGeometry`。
形式化陈述：sin_oangle_right_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = 
↑(π / 2)) : Real.Angle.sin (∡ p₂ p₃ p₁) = dist p₁ p₂ / dist p₁ p₃
参数：h : ∡ p₁ p₂ p₃ = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.oangle_rotate_sign`：oangle_rotate_sign (p₁ p₂ p₃ : P) 
: (∡ p₂ p₃ p₁).sign = (∡ p₁ p₂ p₃).sign
· 使用定理 `Real.Angle.sign_coe_pi_div_two`：sign_coe_pi_div_two : (↑(π / 2) : Angle)
.sign = 1
· 使用定理 `EuclideanGeometry.oangle_eq_angle_of_sign_eq_one`：oangle_eq_angle_of_sig
n_eq_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1) : ∡ p₁ p₂ p₃ = ∠ p₁ p₂ p₃
· 使用定理 `Real.Angle.sin_coe`：sin_coe (x : Real) : sin (x : Angle) = Real.sin x
· 使用定理 `EuclideanGeometry.sin_angle_of_angle_eq_pi_div_two`：sin_angle_of_angle_e
q_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) (h0 : p₁ != p₂ ∨ p₃ != p₂) 
: Real.sin (∠ p₂ p₃ p₁) = dist p₁ p₂ / d…
· 使用定理 `EuclideanGeometry.angle_eq_pi_div_two_of_oangle_eq_pi_div_two`：angle_eq_
pi_div_two_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : 
∠ p₁ p₂ p₃ = π / 2
· 使用定理 `EuclideanGeometry.left_ne_of_oangle_eq_pi_div_two`：left_ne_of_oangle_eq_
pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (π / 2 : Real)) : p₁ != p₂

--- 原说明 ---
The sine of an angle in a right-angled triangle as a ratio of sides.
-/
theorem sin_oangle_right_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    Real.Angle.sin (∡ p₂ p₃ p₁) = dist p₁ p₂ / dist p₁ p₃ := by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs, Real.Angle.sin_coe,
    sin_angle_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inl (left_ne_of_oangle_eq_pi_div_two h))]

/-- The sine of an angle in a right-angled triangle as a ratio of sides. -/
/-
**EuclideanGeometry.sin_oangle_left_of_oangle_eq_pi_div_two** 是 Mathlib 中的一个定理，位
于命名空间 `EuclideanGeometry`。
形式化陈述：sin_oangle_left_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑
(π / 2)) : Real.Angle.sin (∡ p₃ p₁ p₂) = dist p₃ p₂ / dist p₁ p₃
参数：h : ∡ p₁ p₂ p₃ = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanGeometry.oangle_rotate_sign`：oangle_rotate_sign (p₁ p₂ p₃ : P) 
: (∡ p₂ p₃ p₁).sign = (∡ p₁ p₂ p₃).sign
· 使用定理 `Real.Angle.sign_coe_pi_div_two`：sign_coe_pi_div_two : (↑(π / 2) : Angle)
.sign = 1
· 使用定理 `EuclideanGeometry.oangle_eq_angle_of_sign_eq_one`：oangle_eq_angle_of_sig
n_eq_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1) : ∡ p₁ p₂ p₃ = ∠ p₁ p₂ p₃
· 使用定理 `EuclideanGeometry.angle_comm`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `Real.Angle.sin_coe`：sin_coe (x : Real) : sin (x : Angle) = Real.sin x
· 使用定理 `EuclideanGeometry.sin_angle_of_angle_eq_pi_div_two`：sin_angle_of_angle_e
q_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) (h0 : p₁ != p₂ ∨ p₃ != p₂) 
: Real.sin (∠ p₂ p₃ p₁) = dist p₁ p₂ / d…
· 使用定理 `EuclideanGeometry.angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two`：angle
_rev_eq_pi_div_two_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π 
/ 2)) : ∠ p₃ p₂ p₁ = π / 2
· 使用定理 `EuclideanGeometry.left_ne_of_oangle_eq_pi_div_two`：left_ne_of_oangle_eq_
pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (π / 2 : Real)) : p₁ != p₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x

--- 原说明 ---
The sine of an angle in a right-angled triangle as a ratio of sides.
-/
theorem sin_oangle_left_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    Real.Angle.sin (∡ p₃ p₁ p₂) = dist p₃ p₂ / dist p₁ p₃ := by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs, angle_comm, Real.Angle.sin_coe,
    sin_angle_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inr (left_ne_of_oangle_eq_pi_div_two h)),
    dist_comm p₁ p₃]

/-- The tangent of an angle in a right-angled triangle as a ratio of sides. -/
/-
**EuclideanGeometry.tan_oangle_right_of_oangle_eq_pi_div_two** 是 Mathlib 中的一个定理，
位于命名空间 `EuclideanGeometry`。
形式化陈述：tan_oangle_right_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = 
↑(π / 2)) : Real.Angle.tan (∡ p₂ p₃ p₁) = dist p₁ p₂ / dist p₃ p₂
参数：h : ∡ p₁ p₂ p₃ = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.oangle_rotate_sign`：oangle_rotate_sign (p₁ p₂ p₃ : P) 
: (∡ p₂ p₃ p₁).sign = (∡ p₁ p₂ p₃).sign
· 使用定理 `Real.Angle.sign_coe_pi_div_two`：sign_coe_pi_div_two : (↑(π / 2) : Angle)
.sign = 1
· 使用定理 `EuclideanGeometry.oangle_eq_angle_of_sign_eq_one`：oangle_eq_angle_of_sig
n_eq_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1) : ∡ p₁ p₂ p₃ = ∠ p₁ p₂ p₃
· 使用定理 `Real.Angle.tan_coe`：tan_coe (x : Real) : tan (x : Angle) = Real.tan x
· 使用定理 `EuclideanGeometry.tan_angle_of_angle_eq_pi_div_two`：tan_angle_of_angle_e
q_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) : Real.tan (∠ p₂ p₃ p₁) = d
ist p₁ p₂ / dist p₃ p₂
· 使用定理 `EuclideanGeometry.angle_eq_pi_div_two_of_oangle_eq_pi_div_two`：angle_eq_
pi_div_two_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : 
∠ p₁ p₂ p₃ = π / 2

--- 原说明 ---
The tangent of an angle in a right-angled triangle as a ratio of sides.
-/
theorem tan_oangle_right_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    Real.Angle.tan (∡ p₂ p₃ p₁) = dist p₁ p₂ / dist p₃ p₂ := by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs, Real.Angle.tan_coe,
    tan_angle_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)]

/-- The tangent of an angle in a right-angled triangle as a ratio of sides. -/
/-
**EuclideanGeometry.tan_oangle_left_of_oangle_eq_pi_div_two** 是 Mathlib 中的一个定理，位
于命名空间 `EuclideanGeometry`。
形式化陈述：tan_oangle_left_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑
(π / 2)) : Real.Angle.tan (∡ p₃ p₁ p₂) = dist p₃ p₂ / dist p₁ p₂
参数：h : ∡ p₁ p₂ p₃ = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanGeometry.oangle_rotate_sign`：oangle_rotate_sign (p₁ p₂ p₃ : P) 
: (∡ p₂ p₃ p₁).sign = (∡ p₁ p₂ p₃).sign
· 使用定理 `Real.Angle.sign_coe_pi_div_two`：sign_coe_pi_div_two : (↑(π / 2) : Angle)
.sign = 1
· 使用定理 `EuclideanGeometry.oangle_eq_angle_of_sign_eq_one`：oangle_eq_angle_of_sig
n_eq_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1) : ∡ p₁ p₂ p₃ = ∠ p₁ p₂ p₃
· 使用定理 `EuclideanGeometry.angle_comm`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `Real.Angle.tan_coe`：tan_coe (x : Real) : tan (x : Angle) = Real.tan x
· 使用定理 `EuclideanGeometry.tan_angle_of_angle_eq_pi_div_two`：tan_angle_of_angle_e
q_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) : Real.tan (∠ p₂ p₃ p₁) = d
ist p₁ p₂ / dist p₃ p₂
· 使用定理 `EuclideanGeometry.angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two`：angle
_rev_eq_pi_div_two_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π 
/ 2)) : ∠ p₃ p₂ p₁ = π / 2

--- 原说明 ---
The tangent of an angle in a right-angled triangle as a ratio of sides.
-/
theorem tan_oangle_left_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    Real.Angle.tan (∡ p₃ p₁ p₂) = dist p₃ p₂ / dist p₁ p₂ := by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs, angle_comm, Real.Angle.tan_coe,
    tan_angle_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)]

/-- The cosine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
adjacent side. -/
/-
**EuclideanGeometry.cos_oangle_right_mul_dist_of_oangle_eq_pi_div_two** 是 Mathli
b 中的一个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：cos_oangle_right_mul_dist_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁
 p₂ p₃ = ↑(π / 2)) : Real.Angle.cos (∡ p₂ p₃ p₁) * dist p₁ p₃ = dist p₃ p₂
参数：h : ∡ p₁ p₂ p₃ = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.oangle_rotate_sign`：oangle_rotate_sign (p₁ p₂ p₃ : P) 
: (∡ p₂ p₃ p₁).sign = (∡ p₁ p₂ p₃).sign
· 使用定理 `Real.Angle.sign_coe_pi_div_two`：sign_coe_pi_div_two : (↑(π / 2) : Angle)
.sign = 1
· 使用定理 `EuclideanGeometry.oangle_eq_angle_of_sign_eq_one`：oangle_eq_angle_of_sig
n_eq_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1) : ∡ p₁ p₂ p₃ = ∠ p₁ p₂ p₃
· 使用定理 `Real.Angle.cos_coe`：cos_coe (x : Real) : cos (x : Angle) = Real.cos x
· 使用定理 `EuclideanGeometry.cos_angle_mul_dist_of_angle_eq_pi_div_two`：cos_angle_m
ul_dist_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) : Real.co
s (∠ p₂ p₃ p₁) * dist p₁ p₃ = dist p₃ p₂
· 使用定理 `EuclideanGeometry.angle_eq_pi_div_two_of_oangle_eq_pi_div_two`：angle_eq_
pi_div_two_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : 
∠ p₁ p₂ p₃ = π / 2

--- 原说明 ---
The cosine of an angle in a right-angled triangle multiplied by the hypotenuse e
quals the
adjacent side.
-/
theorem cos_oangle_right_mul_dist_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : Real.Angle.cos (∡ p₂ p₃ p₁) * dist p₁ p₃ = dist p₃ p₂ := by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs, Real.Angle.cos_coe,
    cos_angle_mul_dist_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)]

/-- The cosine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
adjacent side. -/
/-
**EuclideanGeometry.cos_oangle_left_mul_dist_of_oangle_eq_pi_div_two** 是 Mathlib
 中的一个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：cos_oangle_left_mul_dist_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ 
p₂ p₃ = ↑(π / 2)) : Real.Angle.cos (∡ p₃ p₁ p₂) * dist p₁ p₃ = dist p₁ p₂
参数：h : ∡ p₁ p₂ p₃ = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanGeometry.oangle_rotate_sign`：oangle_rotate_sign (p₁ p₂ p₃ : P) 
: (∡ p₂ p₃ p₁).sign = (∡ p₁ p₂ p₃).sign
· 使用定理 `Real.Angle.sign_coe_pi_div_two`：sign_coe_pi_div_two : (↑(π / 2) : Angle)
.sign = 1
· 使用定理 `EuclideanGeometry.oangle_eq_angle_of_sign_eq_one`：oangle_eq_angle_of_sig
n_eq_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1) : ∡ p₁ p₂ p₃ = ∠ p₁ p₂ p₃
· 使用定理 `EuclideanGeometry.angle_comm`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `Real.Angle.cos_coe`：cos_coe (x : Real) : cos (x : Angle) = Real.cos x
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `EuclideanGeometry.cos_angle_mul_dist_of_angle_eq_pi_div_two`：cos_angle_m
ul_dist_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) : Real.co
s (∠ p₂ p₃ p₁) * dist p₁ p₃ = dist p₃ p₂
· 使用定理 `EuclideanGeometry.angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two`：angle
_rev_eq_pi_div_two_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π 
/ 2)) : ∠ p₃ p₂ p₁ = π / 2

--- 原说明 ---
The cosine of an angle in a right-angled triangle multiplied by the hypotenuse e
quals the
adjacent side.
-/
theorem cos_oangle_left_mul_dist_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : Real.Angle.cos (∡ p₃ p₁ p₂) * dist p₁ p₃ = dist p₁ p₂ := by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs, angle_comm, Real.Angle.cos_coe, dist_comm p₁ p₃,
    cos_angle_mul_dist_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)]

/-- The sine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
opposite side. -/
/-
**EuclideanGeometry.sin_oangle_right_mul_dist_of_oangle_eq_pi_div_two** 是 Mathli
b 中的一个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：sin_oangle_right_mul_dist_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁
 p₂ p₃ = ↑(π / 2)) : Real.Angle.sin (∡ p₂ p₃ p₁) * dist p₁ p₃ = dist p₁ p₂
参数：h : ∡ p₁ p₂ p₃ = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.oangle_rotate_sign`：oangle_rotate_sign (p₁ p₂ p₃ : P) 
: (∡ p₂ p₃ p₁).sign = (∡ p₁ p₂ p₃).sign
· 使用定理 `Real.Angle.sign_coe_pi_div_two`：sign_coe_pi_div_two : (↑(π / 2) : Angle)
.sign = 1
· 使用定理 `EuclideanGeometry.oangle_eq_angle_of_sign_eq_one`：oangle_eq_angle_of_sig
n_eq_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1) : ∡ p₁ p₂ p₃ = ∠ p₁ p₂ p₃
· 使用定理 `Real.Angle.sin_coe`：sin_coe (x : Real) : sin (x : Angle) = Real.sin x
· 使用定理 `EuclideanGeometry.sin_angle_mul_dist_of_angle_eq_pi_div_two`：sin_angle_m
ul_dist_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) : Real.si
n (∠ p₂ p₃ p₁) * dist p₁ p₃ = dist p₁ p₂
· 使用定理 `EuclideanGeometry.angle_eq_pi_div_two_of_oangle_eq_pi_div_two`：angle_eq_
pi_div_two_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : 
∠ p₁ p₂ p₃ = π / 2

--- 原说明 ---
The sine of an angle in a right-angled triangle multiplied by the hypotenuse equ
als the
opposite side.
-/
theorem sin_oangle_right_mul_dist_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : Real.Angle.sin (∡ p₂ p₃ p₁) * dist p₁ p₃ = dist p₁ p₂ := by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs, Real.Angle.sin_coe,
    sin_angle_mul_dist_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)]

/-- The sine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
opposite side. -/
/-
**EuclideanGeometry.sin_oangle_left_mul_dist_of_oangle_eq_pi_div_two** 是 Mathlib
 中的一个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：sin_oangle_left_mul_dist_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ 
p₂ p₃ = ↑(π / 2)) : Real.Angle.sin (∡ p₃ p₁ p₂) * dist p₁ p₃ = dist p₃ p₂
参数：h : ∡ p₁ p₂ p₃ = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanGeometry.oangle_rotate_sign`：oangle_rotate_sign (p₁ p₂ p₃ : P) 
: (∡ p₂ p₃ p₁).sign = (∡ p₁ p₂ p₃).sign
· 使用定理 `Real.Angle.sign_coe_pi_div_two`：sign_coe_pi_div_two : (↑(π / 2) : Angle)
.sign = 1
· 使用定理 `EuclideanGeometry.oangle_eq_angle_of_sign_eq_one`：oangle_eq_angle_of_sig
n_eq_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1) : ∡ p₁ p₂ p₃ = ∠ p₁ p₂ p₃
· 使用定理 `EuclideanGeometry.angle_comm`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `Real.Angle.sin_coe`：sin_coe (x : Real) : sin (x : Angle) = Real.sin x
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `EuclideanGeometry.sin_angle_mul_dist_of_angle_eq_pi_div_two`：sin_angle_m
ul_dist_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) : Real.si
n (∠ p₂ p₃ p₁) * dist p₁ p₃ = dist p₁ p₂
· 使用定理 `EuclideanGeometry.angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two`：angle
_rev_eq_pi_div_two_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π 
/ 2)) : ∠ p₃ p₂ p₁ = π / 2

--- 原说明 ---
The sine of an angle in a right-angled triangle multiplied by the hypotenuse equ
als the
opposite side.
-/
theorem sin_oangle_left_mul_dist_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : Real.Angle.sin (∡ p₃ p₁ p₂) * dist p₁ p₃ = dist p₃ p₂ := by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs, angle_comm, Real.Angle.sin_coe, dist_comm p₁ p₃,
    sin_angle_mul_dist_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)]

/-- The tangent of an angle in a right-angled triangle multiplied by the adjacent side equals
the opposite side. -/
/-
**EuclideanGeometry.tan_oangle_right_mul_dist_of_oangle_eq_pi_div_two** 是 Mathli
b 中的一个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：tan_oangle_right_mul_dist_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁
 p₂ p₃ = ↑(π / 2)) : Real.Angle.tan (∡ p₂ p₃ p₁) * dist p₃ p₂ = dist p₁ p₂
参数：h : ∡ p₁ p₂ p₃ = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.oangle_rotate_sign`：oangle_rotate_sign (p₁ p₂ p₃ : P) 
: (∡ p₂ p₃ p₁).sign = (∡ p₁ p₂ p₃).sign
· 使用定理 `Real.Angle.sign_coe_pi_div_two`：sign_coe_pi_div_two : (↑(π / 2) : Angle)
.sign = 1
· 使用定理 `EuclideanGeometry.oangle_eq_angle_of_sign_eq_one`：oangle_eq_angle_of_sig
n_eq_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1) : ∡ p₁ p₂ p₃ = ∠ p₁ p₂ p₃
· 使用定理 `Real.Angle.tan_coe`：tan_coe (x : Real) : tan (x : Angle) = Real.tan x
· 使用定理 `EuclideanGeometry.tan_angle_mul_dist_of_angle_eq_pi_div_two`：tan_angle_m
ul_dist_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) (h0 : p₁ 
= p₂ ∨ p₃ != p₂) : Real.tan (∠ p₂ p₃ p₁) * dist p…
· 使用定理 `EuclideanGeometry.angle_eq_pi_div_two_of_oangle_eq_pi_div_two`：angle_eq_
pi_div_two_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : 
∠ p₁ p₂ p₃ = π / 2
· 使用定理 `EuclideanGeometry.right_ne_of_oangle_eq_pi_div_two`：right_ne_of_oangle_e
q_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (π / 2 : Real)) : p₃ != p₂

--- 原说明 ---
The tangent of an angle in a right-angled triangle multiplied by the adjacent si
de equals
the opposite side.
-/
theorem tan_oangle_right_mul_dist_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : Real.Angle.tan (∡ p₂ p₃ p₁) * dist p₃ p₂ = dist p₁ p₂ := by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs, Real.Angle.tan_coe,
    tan_angle_mul_dist_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inr (right_ne_of_oangle_eq_pi_div_two h))]

/-- The tangent of an angle in a right-angled triangle multiplied by the adjacent side equals
the opposite side. -/
/-
**EuclideanGeometry.tan_oangle_left_mul_dist_of_oangle_eq_pi_div_two** 是 Mathlib
 中的一个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：tan_oangle_left_mul_dist_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ 
p₂ p₃ = ↑(π / 2)) : Real.Angle.tan (∡ p₃ p₁ p₂) * dist p₁ p₂ = dist p₃ p₂
参数：h : ∡ p₁ p₂ p₃ = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanGeometry.oangle_rotate_sign`：oangle_rotate_sign (p₁ p₂ p₃ : P) 
: (∡ p₂ p₃ p₁).sign = (∡ p₁ p₂ p₃).sign
· 使用定理 `Real.Angle.sign_coe_pi_div_two`：sign_coe_pi_div_two : (↑(π / 2) : Angle)
.sign = 1
· 使用定理 `EuclideanGeometry.oangle_eq_angle_of_sign_eq_one`：oangle_eq_angle_of_sig
n_eq_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1) : ∡ p₁ p₂ p₃ = ∠ p₁ p₂ p₃
· 使用定理 `EuclideanGeometry.angle_comm`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `Real.Angle.tan_coe`：tan_coe (x : Real) : tan (x : Angle) = Real.tan x
· 使用定理 `EuclideanGeometry.tan_angle_mul_dist_of_angle_eq_pi_div_two`：tan_angle_m
ul_dist_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) (h0 : p₁ 
= p₂ ∨ p₃ != p₂) : Real.tan (∠ p₂ p₃ p₁) * dist p…
· 使用定理 `EuclideanGeometry.angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two`：angle
_rev_eq_pi_div_two_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π 
/ 2)) : ∠ p₃ p₂ p₁ = π / 2
· 使用定理 `EuclideanGeometry.left_ne_of_oangle_eq_pi_div_two`：left_ne_of_oangle_eq_
pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (π / 2 : Real)) : p₁ != p₂

--- 原说明 ---
The tangent of an angle in a right-angled triangle multiplied by the adjacent si
de equals
the opposite side.
-/
theorem tan_oangle_left_mul_dist_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : Real.Angle.tan (∡ p₃ p₁ p₂) * dist p₁ p₂ = dist p₃ p₂ := by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs, angle_comm, Real.Angle.tan_coe,
    tan_angle_mul_dist_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inr (left_ne_of_oangle_eq_pi_div_two h))]

/-- A side of a right-angled triangle divided by the cosine of the adjacent angle equals the
hypotenuse. -/
/-
**EuclideanGeometry.dist_div_cos_oangle_right_of_oangle_eq_pi_div_two** 是 Mathli
b 中的一个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：dist_div_cos_oangle_right_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁
 p₂ p₃ = ↑(π / 2)) : dist p₃ p₂ / Real.Angle.cos (∡ p₂ p₃ p₁) = dist p₁ p₃
参数：h : ∡ p₁ p₂ p₃ = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.oangle_rotate_sign`：oangle_rotate_sign (p₁ p₂ p₃ : P) 
: (∡ p₂ p₃ p₁).sign = (∡ p₁ p₂ p₃).sign
· 使用定理 `Real.Angle.sign_coe_pi_div_two`：sign_coe_pi_div_two : (↑(π / 2) : Angle)
.sign = 1
· 使用定理 `EuclideanGeometry.oangle_eq_angle_of_sign_eq_one`：oangle_eq_angle_of_sig
n_eq_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1) : ∡ p₁ p₂ p₃ = ∠ p₁ p₂ p₃
· 使用定理 `Real.Angle.cos_coe`：cos_coe (x : Real) : cos (x : Angle) = Real.cos x
· 使用定理 `EuclideanGeometry.dist_div_cos_angle_of_angle_eq_pi_div_two`：dist_div_co
s_angle_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) (h0 : p₁ 
= p₂ ∨ p₃ != p₂) : dist p₃ p₂ / Real.cos (∠ p₂ p₃…
· 使用定理 `EuclideanGeometry.angle_eq_pi_div_two_of_oangle_eq_pi_div_two`：angle_eq_
pi_div_two_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : 
∠ p₁ p₂ p₃ = π / 2
· 使用定理 `EuclideanGeometry.right_ne_of_oangle_eq_pi_div_two`：right_ne_of_oangle_e
q_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (π / 2 : Real)) : p₃ != p₂

--- 原说明 ---
A side of a right-angled triangle divided by the cosine of the adjacent angle eq
uals the
hypotenuse.
-/
theorem dist_div_cos_oangle_right_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : dist p₃ p₂ / Real.Angle.cos (∡ p₂ p₃ p₁) = dist p₁ p₃ := by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs, Real.Angle.cos_coe,
    dist_div_cos_angle_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inr (right_ne_of_oangle_eq_pi_div_two h))]

/-- A side of a right-angled triangle divided by the cosine of the adjacent angle equals the
hypotenuse. -/
/-
**EuclideanGeometry.dist_div_cos_oangle_left_of_oangle_eq_pi_div_two** 是 Mathlib
 中的一个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：dist_div_cos_oangle_left_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ 
p₂ p₃ = ↑(π / 2)) : dist p₁ p₂ / Real.Angle.cos (∡ p₃ p₁ p₂) = dist p₁ p₃
参数：h : ∡ p₁ p₂ p₃ = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanGeometry.oangle_rotate_sign`：oangle_rotate_sign (p₁ p₂ p₃ : P) 
: (∡ p₂ p₃ p₁).sign = (∡ p₁ p₂ p₃).sign
· 使用定理 `Real.Angle.sign_coe_pi_div_two`：sign_coe_pi_div_two : (↑(π / 2) : Angle)
.sign = 1
· 使用定理 `EuclideanGeometry.oangle_eq_angle_of_sign_eq_one`：oangle_eq_angle_of_sig
n_eq_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1) : ∡ p₁ p₂ p₃ = ∠ p₁ p₂ p₃
· 使用定理 `EuclideanGeometry.angle_comm`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `Real.Angle.cos_coe`：cos_coe (x : Real) : cos (x : Angle) = Real.cos x
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `EuclideanGeometry.dist_div_cos_angle_of_angle_eq_pi_div_two`：dist_div_co
s_angle_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) (h0 : p₁ 
= p₂ ∨ p₃ != p₂) : dist p₃ p₂ / Real.cos (∠ p₂ p₃…
· 使用定理 `EuclideanGeometry.angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two`：angle
_rev_eq_pi_div_two_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π 
/ 2)) : ∠ p₃ p₂ p₁ = π / 2
· 使用定理 `EuclideanGeometry.left_ne_of_oangle_eq_pi_div_two`：left_ne_of_oangle_eq_
pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (π / 2 : Real)) : p₁ != p₂

--- 原说明 ---
A side of a right-angled triangle divided by the cosine of the adjacent angle eq
uals the
hypotenuse.
-/
theorem dist_div_cos_oangle_left_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : dist p₁ p₂ / Real.Angle.cos (∡ p₃ p₁ p₂) = dist p₁ p₃ := by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs, angle_comm, Real.Angle.cos_coe, dist_comm p₁ p₃,
    dist_div_cos_angle_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inr (left_ne_of_oangle_eq_pi_div_two h))]

/-- A side of a right-angled triangle divided by the sine of the opposite angle equals the
hypotenuse. -/
/-
**EuclideanGeometry.dist_div_sin_oangle_right_of_oangle_eq_pi_div_two** 是 Mathli
b 中的一个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：dist_div_sin_oangle_right_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁
 p₂ p₃ = ↑(π / 2)) : dist p₁ p₂ / Real.Angle.sin (∡ p₂ p₃ p₁) = dist p₁ p₃
参数：h : ∡ p₁ p₂ p₃ = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.oangle_rotate_sign`：oangle_rotate_sign (p₁ p₂ p₃ : P) 
: (∡ p₂ p₃ p₁).sign = (∡ p₁ p₂ p₃).sign
· 使用定理 `Real.Angle.sign_coe_pi_div_two`：sign_coe_pi_div_two : (↑(π / 2) : Angle)
.sign = 1
· 使用定理 `EuclideanGeometry.oangle_eq_angle_of_sign_eq_one`：oangle_eq_angle_of_sig
n_eq_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1) : ∡ p₁ p₂ p₃ = ∠ p₁ p₂ p₃
· 使用定理 `Real.Angle.sin_coe`：sin_coe (x : Real) : sin (x : Angle) = Real.sin x
· 使用定理 `EuclideanGeometry.dist_div_sin_angle_of_angle_eq_pi_div_two`：dist_div_si
n_angle_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) (h0 : p₁ 
!= p₂ ∨ p₃ = p₂) : dist p₁ p₂ / Real.sin (∠ p₂ p₃…
· 使用定理 `EuclideanGeometry.angle_eq_pi_div_two_of_oangle_eq_pi_div_two`：angle_eq_
pi_div_two_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : 
∠ p₁ p₂ p₃ = π / 2
· 使用定理 `EuclideanGeometry.left_ne_of_oangle_eq_pi_div_two`：left_ne_of_oangle_eq_
pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (π / 2 : Real)) : p₁ != p₂

--- 原说明 ---
A side of a right-angled triangle divided by the sine of the opposite angle equa
ls the
hypotenuse.
-/
theorem dist_div_sin_oangle_right_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : dist p₁ p₂ / Real.Angle.sin (∡ p₂ p₃ p₁) = dist p₁ p₃ := by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs, Real.Angle.sin_coe,
    dist_div_sin_angle_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inl (left_ne_of_oangle_eq_pi_div_two h))]

/-- A side of a right-angled triangle divided by the sine of the opposite angle equals the
hypotenuse. -/
/-
**EuclideanGeometry.dist_div_sin_oangle_left_of_oangle_eq_pi_div_two** 是 Mathlib
 中的一个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：dist_div_sin_oangle_left_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ 
p₂ p₃ = ↑(π / 2)) : dist p₃ p₂ / Real.Angle.sin (∡ p₃ p₁ p₂) = dist p₁ p₃
参数：h : ∡ p₁ p₂ p₃ = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanGeometry.oangle_rotate_sign`：oangle_rotate_sign (p₁ p₂ p₃ : P) 
: (∡ p₂ p₃ p₁).sign = (∡ p₁ p₂ p₃).sign
· 使用定理 `Real.Angle.sign_coe_pi_div_two`：sign_coe_pi_div_two : (↑(π / 2) : Angle)
.sign = 1
· 使用定理 `EuclideanGeometry.oangle_eq_angle_of_sign_eq_one`：oangle_eq_angle_of_sig
n_eq_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1) : ∡ p₁ p₂ p₃ = ∠ p₁ p₂ p₃
· 使用定理 `EuclideanGeometry.angle_comm`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `Real.Angle.sin_coe`：sin_coe (x : Real) : sin (x : Angle) = Real.sin x
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `EuclideanGeometry.dist_div_sin_angle_of_angle_eq_pi_div_two`：dist_div_si
n_angle_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) (h0 : p₁ 
!= p₂ ∨ p₃ = p₂) : dist p₁ p₂ / Real.sin (∠ p₂ p₃…
· 使用定理 `EuclideanGeometry.angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two`：angle
_rev_eq_pi_div_two_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π 
/ 2)) : ∠ p₃ p₂ p₁ = π / 2
· 使用定理 `EuclideanGeometry.right_ne_of_oangle_eq_pi_div_two`：right_ne_of_oangle_e
q_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (π / 2 : Real)) : p₃ != p₂

--- 原说明 ---
A side of a right-angled triangle divided by the sine of the opposite angle equa
ls the
hypotenuse.
-/
theorem dist_div_sin_oangle_left_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : dist p₃ p₂ / Real.Angle.sin (∡ p₃ p₁ p₂) = dist p₁ p₃ := by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs, angle_comm, Real.Angle.sin_coe, dist_comm p₁ p₃,
    dist_div_sin_angle_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inl (right_ne_of_oangle_eq_pi_div_two h))]

/-- A side of a right-angled triangle divided by the tangent of the opposite angle equals the
adjacent side. -/
/-
**EuclideanGeometry.dist_div_tan_oangle_right_of_oangle_eq_pi_div_two** 是 Mathli
b 中的一个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：dist_div_tan_oangle_right_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁
 p₂ p₃ = ↑(π / 2)) : dist p₁ p₂ / Real.Angle.tan (∡ p₂ p₃ p₁) = dist p₃ p₂
参数：h : ∡ p₁ p₂ p₃ = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.oangle_rotate_sign`：oangle_rotate_sign (p₁ p₂ p₃ : P) 
: (∡ p₂ p₃ p₁).sign = (∡ p₁ p₂ p₃).sign
· 使用定理 `Real.Angle.sign_coe_pi_div_two`：sign_coe_pi_div_two : (↑(π / 2) : Angle)
.sign = 1
· 使用定理 `EuclideanGeometry.oangle_eq_angle_of_sign_eq_one`：oangle_eq_angle_of_sig
n_eq_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1) : ∡ p₁ p₂ p₃ = ∠ p₁ p₂ p₃
· 使用定理 `Real.Angle.tan_coe`：tan_coe (x : Real) : tan (x : Angle) = Real.tan x
· 使用定理 `EuclideanGeometry.dist_div_tan_angle_of_angle_eq_pi_div_two`：dist_div_ta
n_angle_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) (h0 : p₁ 
!= p₂ ∨ p₃ = p₂) : dist p₁ p₂ / Real.tan (∠ p₂ p₃…
· 使用定理 `EuclideanGeometry.angle_eq_pi_div_two_of_oangle_eq_pi_div_two`：angle_eq_
pi_div_two_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : 
∠ p₁ p₂ p₃ = π / 2
· 使用定理 `EuclideanGeometry.left_ne_of_oangle_eq_pi_div_two`：left_ne_of_oangle_eq_
pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (π / 2 : Real)) : p₁ != p₂

--- 原说明 ---
A side of a right-angled triangle divided by the tangent of the opposite angle e
quals the
adjacent side.
-/
theorem dist_div_tan_oangle_right_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : dist p₁ p₂ / Real.Angle.tan (∡ p₂ p₃ p₁) = dist p₃ p₂ := by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs, Real.Angle.tan_coe,
    dist_div_tan_angle_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inl (left_ne_of_oangle_eq_pi_div_two h))]

/-- A side of a right-angled triangle divided by the tangent of the opposite angle equals the
adjacent side. -/
/-
**EuclideanGeometry.dist_div_tan_oangle_left_of_oangle_eq_pi_div_two** 是 Mathlib
 中的一个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：dist_div_tan_oangle_left_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ 
p₂ p₃ = ↑(π / 2)) : dist p₃ p₂ / Real.Angle.tan (∡ p₃ p₁ p₂) = dist p₁ p₂
参数：h : ∡ p₁ p₂ p₃ = ↑(π / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanGeometry.oangle_rotate_sign`：oangle_rotate_sign (p₁ p₂ p₃ : P) 
: (∡ p₂ p₃ p₁).sign = (∡ p₁ p₂ p₃).sign
· 使用定理 `Real.Angle.sign_coe_pi_div_two`：sign_coe_pi_div_two : (↑(π / 2) : Angle)
.sign = 1
· 使用定理 `EuclideanGeometry.oangle_eq_angle_of_sign_eq_one`：oangle_eq_angle_of_sig
n_eq_one {p₁ p₂ p₃ : P} (h : (∡ p₁ p₂ p₃).sign = 1) : ∡ p₁ p₂ p₃ = ∠ p₁ p₂ p₃
· 使用定理 `EuclideanGeometry.angle_comm`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `Real.Angle.tan_coe`：tan_coe (x : Real) : tan (x : Angle) = Real.tan x
· 使用定理 `EuclideanGeometry.dist_div_tan_angle_of_angle_eq_pi_div_two`：dist_div_ta
n_angle_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) (h0 : p₁ 
!= p₂ ∨ p₃ = p₂) : dist p₁ p₂ / Real.tan (∠ p₂ p₃…
· 使用定理 `EuclideanGeometry.angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two`：angle
_rev_eq_pi_div_two_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π 
/ 2)) : ∠ p₃ p₂ p₁ = π / 2
· 使用定理 `EuclideanGeometry.right_ne_of_oangle_eq_pi_div_two`：right_ne_of_oangle_e
q_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = (π / 2 : Real)) : p₃ != p₂

--- 原说明 ---
A side of a right-angled triangle divided by the tangent of the opposite angle e
quals the
adjacent side.
-/
theorem dist_div_tan_oangle_left_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : dist p₃ p₂ / Real.Angle.tan (∡ p₃ p₁ p₂) = dist p₁ p₂ := by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs, angle_comm, Real.Angle.tan_coe,
    dist_div_tan_angle_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inl (right_ne_of_oangle_eq_pi_div_two h))]

end EuclideanGeometry

