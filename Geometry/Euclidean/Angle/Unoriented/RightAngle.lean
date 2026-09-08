/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine

/-!
# Right-angled triangles

This file proves basic geometric results about distances and angles in (possibly degenerate)
right-angled triangles in real inner product spaces and Euclidean affine spaces.

## Implementation notes

Results in this file are generally given in a form with only those non-degeneracy conditions
needed for the particular result, rather than requiring affine independence of the points of a
triangle unnecessarily.

## References

* https://en.wikipedia.org/wiki/Pythagorean_theorem

-/

public section


noncomputable section

open scoped EuclideanGeometry

open scoped Real

open scoped RealInnerProductSpace

namespace InnerProductGeometry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Pythagorean theorem, if-and-only-if vector angle form. -/
/-
**InnerProductGeometry.norm_add_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_tw
o** 是 Mathlib 中的一个定理，位于命名空间 `InnerProductGeometry`。
形式化陈述：norm_add_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two (x y : V) : ‖x 
+ y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ ↔ angle x y = π / 2
参数：x y : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero`：norm_add_sq_e
q_norm_sq_add_norm_sq_iff_real_inner_eq_zero (x y : F) : ‖x + y‖ * ‖x + y‖ = ‖x‖
 * ‖x‖ + ‖y‖ * ‖y‖ ↔ ⟪x, y⟫_Real = 0
· 使用定理 `InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two`：inner_eq_zer
o_iff_angle_eq_pi_div_two (x y : V) : ⟪x, y⟫ = 0 ↔ angle x y = π / 2

--- 原说明 ---
Pythagorean theorem, if-and-only-if vector angle form.
-/
theorem norm_add_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two (x y : V) :
    ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ ↔ angle x y = π / 2 := by
  rw [norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero]
  exact inner_eq_zero_iff_angle_eq_pi_div_two x y

/-- Pythagorean theorem, vector angle form. -/
/-
**InnerProductGeometry.norm_add_sq_eq_norm_sq_add_norm_sq'** 是 Mathlib 中的一个定理，位于
命名空间 `InnerProductGeometry`。
形式化陈述：norm_add_sq_eq_norm_sq_add_norm_sq' (x y : V) (h : angle x y = π / 2) : ‖x
 + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖
参数：x y : V；h : angle x y = π / 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `InnerProductGeometry.norm_add_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_
div_two`：norm_add_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two (x y : V) : 
‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ ↔ angle x y = π / 2

--- 原说明 ---
Pythagorean theorem, vector angle form.
-/
theorem norm_add_sq_eq_norm_sq_add_norm_sq' (x y : V) (h : angle x y = π / 2) :
    ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ :=
  (norm_add_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two x y).2 h

/-- Pythagorean theorem, subtracting vectors, if-and-only-if vector angle form. -/
/-
**InnerProductGeometry.norm_sub_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_tw
o** 是 Mathlib 中的一个定理，位于命名空间 `InnerProductGeometry`。
形式化陈述：norm_sub_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two (x y : V) : ‖x 
- y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ ↔ angle x y = π / 2
参数：x y : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero`：norm_sub_sq_e
q_norm_sq_add_norm_sq_iff_real_inner_eq_zero (x y : F) : ‖x - y‖ * ‖x - y‖ = ‖x‖
 * ‖x‖ + ‖y‖ * ‖y‖ ↔ ⟪x, y⟫_Real = 0
· 使用定理 `InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two`：inner_eq_zer
o_iff_angle_eq_pi_div_two (x y : V) : ⟪x, y⟫ = 0 ↔ angle x y = π / 2

--- 原说明 ---
Pythagorean theorem, subtracting vectors, if-and-only-if vector angle form.
-/
theorem norm_sub_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two (x y : V) :
    ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ ↔ angle x y = π / 2 := by
  rw [norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero]
  exact inner_eq_zero_iff_angle_eq_pi_div_two x y

/-- Pythagorean theorem, subtracting vectors, vector angle form. -/
/-
**InnerProductGeometry.norm_sub_sq_eq_norm_sq_add_norm_sq'** 是 Mathlib 中的一个定理，位于
命名空间 `InnerProductGeometry`。
形式化陈述：norm_sub_sq_eq_norm_sq_add_norm_sq' (x y : V) (h : angle x y = π / 2) : ‖x
 - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖
参数：x y : V；h : angle x y = π / 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `InnerProductGeometry.norm_sub_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_
div_two`：norm_sub_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two (x y : V) : 
‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ ↔ angle x y = π / 2

--- 原说明 ---
Pythagorean theorem, subtracting vectors, vector angle form.
-/
theorem norm_sub_sq_eq_norm_sq_add_norm_sq' (x y : V) (h : angle x y = π / 2) :
    ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ :=
  (norm_sub_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two x y).2 h

/-- An angle in a right-angled triangle expressed using `arccos`. -/
/-
**InnerProductGeometry.angle_add_eq_arccos_of_inner_eq_zero** 是 Mathlib 中的一个定理，位
于命名空间 `InnerProductGeometry`。
形式化陈述：angle_add_eq_arccos_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) : angle x 
(x + y) = Real.arccos (‖x‖ / ‖x + y‖)
参数：h : ⟪x, y⟫ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InnerProductGeometry.angle.eq_1`：∀ {V : Type u_1} [inst : NormedAddCommG
roup V] [inst_1 : InnerProductSpace ℝ V] (x y : V),   InnerProductGeometry.angle
 x y = Real.arccos (i…
· 使用定理 `inner_add_right`：inner_add_right (x y z : E) : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x,
 z⟫
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `real_inner_self_eq_norm_mul_norm`：real_inner_self_eq_norm_mul_norm (x : 
F) : ⟪x, x⟫_Real = ‖x‖ * ‖x‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `Real.arccos_zero`：arccos_zero : arccos 0 = π / 2
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `div_mul_eq_div_div`：div_mul_eq_div_div : a / (b * c) = a / b / c
· 使用定理 `mul_self_div_self`：mul_self_div_self (a : G₀) : a * a / a = a

--- 原说明 ---
An angle in a right-angled triangle expressed using `arccos`.
-/
theorem angle_add_eq_arccos_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
    angle x (x + y) = Real.arccos (‖x‖ / ‖x + y‖) := by
  rw [angle, inner_add_right, h, add_zero, real_inner_self_eq_norm_mul_norm]
  by_cases hx : ‖x‖ = 0; · simp [hx]
  rw [div_mul_eq_div_div, mul_self_div_self]

/-- An angle in a right-angled triangle expressed using `arcsin`. -/
/-
**InnerProductGeometry.angle_add_eq_arcsin_of_inner_eq_zero** 是 Mathlib 中的一个定理，位
于命名空间 `InnerProductGeometry`。
形式化陈述：angle_add_eq_arcsin_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x !=
 0 ∨ y != 0) : angle x (x + y) = Real.arcsin (‖y‖ / ‖x + y‖)
参数：h : ⟪x, y⟫ = 0；h0 : x != 0 ∨ y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `norm_add_sq_eq_norm_sq_add_norm_sq_real`：norm_add_sq_eq_norm_sq_add_norm
_sq_real {x y : F} (h : ⟪x, y⟫_Real = 0) : ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + ‖y‖ *
 ‖y‖
· 使用定理 `ne_comm`：∀ {α : Sort u_1} {a b : α}, a ≠ b ↔ b ≠ a
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `Left.add_pos_of_pos_of_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] 
[inst_1 : Preorder α] [AddLeftMono α] {a b : α}, 0 < a → 0 ≤ b → 0 < a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mul_self_pos`：mul_self_pos [ExistsAddOfLE R] [PosMulStrictMono R] [MulPo
sStrictMono R] [AddLeftStrictMono R] [AddLeftReflectLT R] {a : R} : 0 < a * a ↔ 
a …
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `norm_ne_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≠ 0 ↔ a ≠ 0
· 使用引理 `mul_self_nonneg`：mul_self_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLe
ftMono R] (a : R) : 0 <= a * a
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Left.add_pos_of_nonneg_of_pos`：∀ {α : Type u_1} [inst : AddZeroClass α] 
[inst_1 : Preorder α] [AddLeftStrictMono α] {a b : α},   0 ≤ a → 0 < b → 0 < a +
 b
· 使用定理 `InnerProductGeometry.angle_add_eq_arccos_of_inner_eq_zero`：angle_add_eq_
arccos_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) : angle x (x + y) = Real.arcc
os (‖x‖ / ‖x + y‖)
· 使用定理 `Real.arccos_eq_arcsin`：arccos_eq_arcsin {x : Real} (h : 0 <= x) : arccos
 x = arcsin (√(1 - x ^ 2))
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `div_pow`：div_pow (a b : α) (n : Nat) : (a / b) ^ n = a ^ n / b ^ n
· 使用定理 `one_sub_div`：one_sub_div {a b : K} (h : b != 0) : 1 - a / b = (b - a) / 
b
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.sqrt_sq`：sqrt_sq (h : 0 <= x) : √(x ^ 2) = x

--- 原说明 ---
An angle in a right-angled triangle expressed using `arcsin`.
-/
theorem angle_add_eq_arcsin_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x ≠ 0 ∨ y ≠ 0) :
    angle x (x + y) = Real.arcsin (‖y‖ / ‖x + y‖) := by
  have hxy : ‖x + y‖ ^ 2 ≠ 0 := by
    rw [pow_two, norm_add_sq_eq_norm_sq_add_norm_sq_real h, ne_comm]
    refine ne_of_lt ?_
    rcases h0 with (h0 | h0)
    · exact
        Left.add_pos_of_pos_of_nonneg (mul_self_pos.2 (norm_ne_zero_iff.2 h0)) (mul_self_nonneg _)
    · exact
        Left.add_pos_of_nonneg_of_pos (mul_self_nonneg _) (mul_self_pos.2 (norm_ne_zero_iff.2 h0))
  rw [angle_add_eq_arccos_of_inner_eq_zero h,
    Real.arccos_eq_arcsin (div_nonneg (norm_nonneg _) (norm_nonneg _)), div_pow, one_sub_div hxy]
  nth_rw 1 [pow_two]
  rw [norm_add_sq_eq_norm_sq_add_norm_sq_real h, pow_two, add_sub_cancel_left, ← pow_two, ← div_pow,
    Real.sqrt_sq (div_nonneg (norm_nonneg _) (norm_nonneg _))]

/-- An angle in a right-angled triangle expressed using `arctan`. -/
/-
**InnerProductGeometry.angle_add_eq_arctan_of_inner_eq_zero** 是 Mathlib 中的一个定理，位
于命名空间 `InnerProductGeometry`。
形式化陈述：angle_add_eq_arctan_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x !=
 0) : angle x (x + y) = Real.arctan (‖y‖ / ‖x‖)
参数：h : ⟪x, y⟫ = 0；h0 : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InnerProductGeometry.angle_add_eq_arcsin_of_inner_eq_zero`：angle_add_eq_
arcsin_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0 ∨ y != 0) : angl
e x (x + y) = Real.arcsin (‖y‖ / ‖x + y‖)
· 使用定理 `Real.arctan_eq_arcsin`：arctan_eq_arcsin (x : Real) : arctan x = arcsin (
x / √(1 + x ^ 2))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_mul_eq_div_div`：div_mul_eq_div_div : a / (b * c) = a / b / c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_add_eq_sqrt_iff_real_inner_eq_zero`：norm_add_eq_sqrt_iff_real_inner
_eq_zero {x y : F} : ‖x + y‖ = √(‖x‖ * ‖x‖ + ‖y‖ * ‖y‖) ↔ ⟪x, y⟫_Real = 0
· 使用定理 `Real.sqrt_sq`：sqrt_sq (h : 0 <= x) : √(x ^ 2) = x
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Real.sqrt_mul`：sqrt_mul {x : Real} (hx : 0 <= x) (y : Real) : √(x * y) =
 √x * √y
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `div_pow`：div_pow (a b : α) (n : Nat) : (a / b) ^ n = a ^ n / b ^ n
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_div`：mul_div (a b c : G) : a * (b / c) = a * b / c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `mul_self_pos`：mul_self_pos [ExistsAddOfLE R] [PosMulStrictMono R] [MulPo
sStrictMono R] [AddLeftStrictMono R] [AddLeftReflectLT R] {a : R} : 0 < a * a ↔ 
a …
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
An angle in a right-angled triangle expressed using `arctan`.
-/
theorem angle_add_eq_arctan_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x ≠ 0) :
    angle x (x + y) = Real.arctan (‖y‖ / ‖x‖) := by
  rw [angle_add_eq_arcsin_of_inner_eq_zero h (Or.inl h0), Real.arctan_eq_arcsin, ←
    div_mul_eq_div_div, norm_add_eq_sqrt_iff_real_inner_eq_zero.2 h]
  nth_rw 3 [← Real.sqrt_sq (norm_nonneg x)]
  rw_mod_cast [← Real.sqrt_mul (sq_nonneg _), div_pow, pow_two, pow_two, mul_add, mul_one, mul_div,
    mul_comm (‖x‖ * ‖x‖), ← mul_div, div_self (mul_self_pos.2 (norm_ne_zero_iff.2 h0)).ne', mul_one]

/-- An angle in a non-degenerate right-angled triangle is positive. -/
/-
**InnerProductGeometry.angle_add_pos_of_inner_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 
`InnerProductGeometry`。
形式化陈述：angle_add_pos_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x = 0 ∨ y 
!= 0) : 0 < angle x (x + y)
参数：h : ⟪x, y⟫ = 0；h0 : x = 0 ∨ y != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InnerProductGeometry.angle_add_eq_arccos_of_inner_eq_zero`：angle_add_eq_
arccos_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) : angle x (x + y) = Real.arcc
os (‖x‖ / ‖x + y‖)
· 使用定理 `Real.arccos_pos`：arccos_pos {x : Real} : 0 < arccos x ↔ x < 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_add_eq_sqrt_iff_real_inner_eq_zero`：norm_add_eq_sqrt_iff_real_inner
_eq_zero {x y : F} : ‖x + y‖ = √(‖x‖ * ‖x‖ + ‖y‖ * ‖y‖) ↔ ⟪x, y⟫_Real = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Real.sqrt_mul_self`：sqrt_mul_self (h : 0 <= x) : √(x * x) = x
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `div_lt_one`：div_lt_one (hb : 0 < b) : a / b < 1 ↔ a < b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Real.sqrt_pos`：sqrt_pos : 0 < √x ↔ 0 < x
· 使用定理 `Left.add_pos_of_pos_of_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] 
[inst_1 : Preorder α] [AddLeftMono α] {a b : α}, 0 < a → 0 ≤ b → 0 < a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `mul_self_pos`：mul_self_pos [ExistsAddOfLE R] [PosMulStrictMono R] [MulPo
sStrictMono R] [AddLeftStrictMono R] [AddLeftReflectLT R] {a : R} : 0 < a * a ↔ 
a …
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `norm_ne_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≠ 0 ↔ a ≠ 0
· 使用引理 `mul_self_nonneg`：mul_self_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLe
ftMono R] (a : R) : 0 <= a * a
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
An angle in a non-degenerate right-angled triangle is positive.
-/
theorem angle_add_pos_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x = 0 ∨ y ≠ 0) :
    0 < angle x (x + y) := by
  rw [angle_add_eq_arccos_of_inner_eq_zero h, Real.arccos_pos,
    norm_add_eq_sqrt_iff_real_inner_eq_zero.2 h]
  by_cases hx : x = 0; · simp [hx]
  rw [div_lt_one (Real.sqrt_pos.2 (Left.add_pos_of_pos_of_nonneg (mul_self_pos.2
    (norm_ne_zero_iff.2 hx)) (mul_self_nonneg _))), Real.lt_sqrt (norm_nonneg _), pow_two]
  simpa [hx] using h0

/-- An angle in a right-angled triangle is at most `π / 2`. -/
/-
**InnerProductGeometry.angle_add_le_pi_div_two_of_inner_eq_zero** 是 Mathlib 中的一个
定理，位于命名空间 `InnerProductGeometry`。
形式化陈述：angle_add_le_pi_div_two_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) : angl
e x (x + y) <= π / 2
参数：h : ⟪x, y⟫ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InnerProductGeometry.angle_add_eq_arccos_of_inner_eq_zero`：angle_add_eq_
arccos_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) : angle x (x + y) = Real.arcc
os (‖x‖ / ‖x + y‖)
· 使用定理 `Real.arccos_le_pi_div_two`：arccos_le_pi_div_two {x} : arccos x <= π / 2 
↔ 0 <= x
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖

--- 原说明 ---
An angle in a right-angled triangle is at most `π / 2`.
-/
theorem angle_add_le_pi_div_two_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
    angle x (x + y) ≤ π / 2 := by
  rw [angle_add_eq_arccos_of_inner_eq_zero h, Real.arccos_le_pi_div_two]
  exact div_nonneg (norm_nonneg _) (norm_nonneg _)

/-- An angle in a non-degenerate right-angled triangle is less than `π / 2`. -/
/-
**InnerProductGeometry.angle_add_lt_pi_div_two_of_inner_eq_zero** 是 Mathlib 中的一个
定理，位于命名空间 `InnerProductGeometry`。
形式化陈述：angle_add_lt_pi_div_two_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : 
x != 0) : angle x (x + y) < π / 2
参数：h : ⟪x, y⟫ = 0；h0 : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InnerProductGeometry.angle_add_eq_arccos_of_inner_eq_zero`：angle_add_eq_
arccos_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) : angle x (x + y) = Real.arcc
os (‖x‖ / ‖x + y‖)
· 使用定理 `Real.arccos_lt_pi_div_two`：arccos_lt_pi_div_two {x : Real} : arccos x < 
π / 2 ↔ 0 < x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_add_eq_sqrt_iff_real_inner_eq_zero`：norm_add_eq_sqrt_iff_real_inner
_eq_zero {x y : F} : ‖x + y‖ = √(‖x‖ * ‖x‖ + ‖y‖ * ‖y‖) ↔ ⟪x, y⟫_Real = 0
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
· 使用定理 `Real.sqrt_pos`：sqrt_pos : 0 < √x ↔ 0 < x
· 使用定理 `Left.add_pos_of_pos_of_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] 
[inst_1 : Preorder α] [AddLeftMono α] {a b : α}, 0 < a → 0 ≤ b → 0 < a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `mul_self_pos`：mul_self_pos [ExistsAddOfLE R] [PosMulStrictMono R] [MulPo
sStrictMono R] [AddLeftStrictMono R] [AddLeftReflectLT R] {a : R} : 0 < a * a ↔ 
a …
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `norm_ne_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≠ 0 ↔ a ≠ 0
· 使用引理 `mul_self_nonneg`：mul_self_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLe
ftMono R] (a : R) : 0 <= a * a
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R

--- 原说明 ---
An angle in a non-degenerate right-angled triangle is less than `π / 2`.
-/
theorem angle_add_lt_pi_div_two_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x ≠ 0) :
    angle x (x + y) < π / 2 := by
  rw [angle_add_eq_arccos_of_inner_eq_zero h, Real.arccos_lt_pi_div_two,
    norm_add_eq_sqrt_iff_real_inner_eq_zero.2 h]
  exact div_pos (norm_pos_iff.2 h0) (Real.sqrt_pos.2 (Left.add_pos_of_pos_of_nonneg
    (mul_self_pos.2 (norm_ne_zero_iff.2 h0)) (mul_self_nonneg _)))

/-- The cosine of an angle in a right-angled triangle as a ratio of sides. -/
/-
**InnerProductGeometry.cos_angle_add_of_inner_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 
`InnerProductGeometry`。
形式化陈述：cos_angle_add_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) : Real.cos (angl
e x (x + y)) = ‖x‖ / ‖x + y‖
参数：h : ⟪x, y⟫ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InnerProductGeometry.angle_add_eq_arccos_of_inner_eq_zero`：angle_add_eq_
arccos_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) : angle x (x + y) = Real.arcc
os (‖x‖ / ‖x + y‖)
· 使用定理 `Real.cos_arccos`：cos_arccos {x : Real} (hx₁ : -1 <= x) (hx₂ : x <= 1) : 
cos (arccos x) = x
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `div_le_one_of_le₀`：div_le_one_of_le₀ [ZeroLEOneClass G₀] (h : a <= b) (h
b : 0 <= b) : a / b <= 1
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `mul_self_le_mul_self_iff`：mul_self_le_mul_self_iff [PosMulStrictMono R] 
[MulPosMono R] {a b : R} (h1 : 0 <= a) (h2 : 0 <= b) : a <= b ↔ a * a <= b * b
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_add_sq_eq_norm_sq_add_norm_sq_real`：norm_add_sq_eq_norm_sq_add_norm
_sq_real {x y : F} (h : ⟪x, y⟫_Real = 0) : ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + ‖y‖ *
 ‖y‖
· 使用定理 `le_add_of_nonneg_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1
 : LE α] [AddLeftMono α] {a b : α}, 0 ≤ b → a ≤ a + b
· 使用引理 `mul_self_nonneg`：mul_self_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLe
ftMono R] (a : R) : 0 <= a * a
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R

--- 原说明 ---
The cosine of an angle in a right-angled triangle as a ratio of sides.
-/
theorem cos_angle_add_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
    Real.cos (angle x (x + y)) = ‖x‖ / ‖x + y‖ := by
  rw [angle_add_eq_arccos_of_inner_eq_zero h,
    Real.cos_arccos (le_trans (by simp) (div_nonneg (norm_nonneg _) (norm_nonneg _)))
      (div_le_one_of_le₀ _ (norm_nonneg _))]
  rw [mul_self_le_mul_self_iff (norm_nonneg _) (norm_nonneg _),
    norm_add_sq_eq_norm_sq_add_norm_sq_real h]
  exact le_add_of_nonneg_right (mul_self_nonneg _)

/-- The sine of an angle in a right-angled triangle as a ratio of sides. -/
/-
**InnerProductGeometry.sin_angle_add_of_inner_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 
`InnerProductGeometry`。
形式化陈述：sin_angle_add_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0 ∨ y
 != 0) : Real.sin (angle x (x + y)) = ‖y‖ / ‖x + y‖
参数：h : ⟪x, y⟫ = 0；h0 : x != 0 ∨ y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InnerProductGeometry.angle_add_eq_arcsin_of_inner_eq_zero`：angle_add_eq_
arcsin_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0 ∨ y != 0) : angl
e x (x + y) = Real.arcsin (‖y‖ / ‖x + y‖)
· 使用定理 `Real.sin_arcsin`：sin_arcsin {x : Real} (hx₁ : -1 <= x) (hx₂ : x <= 1) : 
sin (arcsin x) = x
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `div_le_one_of_le₀`：div_le_one_of_le₀ [ZeroLEOneClass G₀] (h : a <= b) (h
b : 0 <= b) : a / b <= 1
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `mul_self_le_mul_self_iff`：mul_self_le_mul_self_iff [PosMulStrictMono R] 
[MulPosMono R] {a b : R} (h1 : 0 <= a) (h2 : 0 <= b) : a <= b ↔ a * a <= b * b
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_add_sq_eq_norm_sq_add_norm_sq_real`：norm_add_sq_eq_norm_sq_add_norm
_sq_real {x y : F} (h : ⟪x, y⟫_Real = 0) : ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + ‖y‖ *
 ‖y‖
· 使用定理 `le_add_of_nonneg_left`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 
: LE α] [AddRightMono α] {a b : α}, 0 ≤ b → a ≤ b + a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `mul_self_nonneg`：mul_self_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLe
ftMono R] (a : R) : 0 <= a * a
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R

--- 原说明 ---
The sine of an angle in a right-angled triangle as a ratio of sides.
-/
theorem sin_angle_add_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x ≠ 0 ∨ y ≠ 0) :
    Real.sin (angle x (x + y)) = ‖y‖ / ‖x + y‖ := by
  rw [angle_add_eq_arcsin_of_inner_eq_zero h h0,
    Real.sin_arcsin (le_trans (by simp) (div_nonneg (norm_nonneg _) (norm_nonneg _)))
      (div_le_one_of_le₀ _ (norm_nonneg _))]
  rw [mul_self_le_mul_self_iff (norm_nonneg _) (norm_nonneg _),
    norm_add_sq_eq_norm_sq_add_norm_sq_real h]
  exact le_add_of_nonneg_left (mul_self_nonneg _)

/-- The tangent of an angle in a right-angled triangle as a ratio of sides. -/
/-
**InnerProductGeometry.tan_angle_add_of_inner_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 
`InnerProductGeometry`。
形式化陈述：tan_angle_add_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) : Real.tan (angl
e x (x + y)) = ‖y‖ / ‖x‖
参数：h : ⟪x, y⟫ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `InnerProductGeometry.angle_zero_left`：angle_zero_left (x : V) : angle 0 
x = π / 2
· 使用定理 `Real.tan_pi_div_two`：tan_pi_div_two : tan (π / 2) = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `InnerProductGeometry.angle_add_eq_arctan_of_inner_eq_zero`：angle_add_eq_
arctan_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0) : angle x (x + 
y) = Real.arctan (‖y‖ / ‖x‖)
· 使用定理 `Real.tan_arctan`：tan_arctan (x : Real) : tan (arctan x) = x

--- 原说明 ---
The tangent of an angle in a right-angled triangle as a ratio of sides.
-/
theorem tan_angle_add_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
    Real.tan (angle x (x + y)) = ‖y‖ / ‖x‖ := by
  by_cases h0 : x = 0; · simp [h0]
  rw [angle_add_eq_arctan_of_inner_eq_zero h h0, Real.tan_arctan]

/-- The cosine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
adjacent side. -/
/-
**InnerProductGeometry.cos_angle_add_mul_norm_of_inner_eq_zero** 是 Mathlib 中的一个定
理，位于命名空间 `InnerProductGeometry`。
形式化陈述：cos_angle_add_mul_norm_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) : Real.
cos (angle x (x + y)) * ‖x + y‖ = ‖x‖
参数：h : ⟪x, y⟫ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InnerProductGeometry.cos_angle_add_of_inner_eq_zero`：cos_angle_add_of_in
ner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) : Real.cos (angle x (x + y)) = ‖x‖ / ‖x +
 y‖
· 使用定理 `norm_add_sq_eq_norm_sq_add_norm_sq_real`：norm_add_sq_eq_norm_sq_add_norm
_sq_real {x y : F} (h : ⟪x, y⟫_Real = 0) : ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + ‖y‖ *
 ‖y‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `mul_self_eq_zero`：mul_self_eq_zero : a * a = 0 ↔ a = 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `add_eq_zero_iff_of_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [ins
t_1 : PartialOrder α] [AddLeftMono α] [AddRightMono α] {a b : α},   0 ≤ a → 0 ≤ 
b → (a + b = 0 …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `mul_self_nonneg`：mul_self_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLe
ftMono R] (a : R) : 0 <= a * a
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a

--- 原说明 ---
The cosine of an angle in a right-angled triangle multiplied by the hypotenuse e
quals the
adjacent side.
-/
theorem cos_angle_add_mul_norm_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
    Real.cos (angle x (x + y)) * ‖x + y‖ = ‖x‖ := by
  rw [cos_angle_add_of_inner_eq_zero h]
  by_cases hxy : ‖x + y‖ = 0
  · have h' := norm_add_sq_eq_norm_sq_add_norm_sq_real h
    rw [hxy, zero_mul, eq_comm,
      add_eq_zero_iff_of_nonneg (mul_self_nonneg ‖x‖) (mul_self_nonneg ‖y‖), mul_self_eq_zero] at h'
    simp [h'.1]
  · exact div_mul_cancel₀ _ hxy

/-- The sine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
opposite side. -/
/-
**InnerProductGeometry.sin_angle_add_mul_norm_of_inner_eq_zero** 是 Mathlib 中的一个定
理，位于命名空间 `InnerProductGeometry`。
形式化陈述：sin_angle_add_mul_norm_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) : Real.
sin (angle x (x + y)) * ‖x + y‖ = ‖y‖
参数：h : ⟪x, y⟫ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `InnerProductGeometry.angle_zero_right`：angle_zero_right (x : V) : angle 
x 0 = π / 2
· 使用定理 `Real.sin_pi_div_two`：sin_pi_div_two : sin (π / 2) = 1
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `InnerProductGeometry.sin_angle_add_of_inner_eq_zero`：sin_angle_add_of_in
ner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0 ∨ y != 0) : Real.sin (angle 
x (x + y)) = ‖y‖ / ‖x + y‖
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_self_ne_zero`：mul_self_ne_zero : a * a != 0 ↔ a != 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `norm_add_sq_eq_norm_sq_add_norm_sq_real`：norm_add_sq_eq_norm_sq_add_norm
_sq_real {x y : F} (h : ⟪x, y⟫_Real = 0) : ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + ‖y‖ *
 ‖y‖
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `Left.add_pos_of_pos_of_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] 
[inst_1 : Preorder α] [AddLeftMono α] {a b : α}, 0 < a → 0 ≤ b → 0 < a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mul_self_pos`：mul_self_pos [ExistsAddOfLE R] [PosMulStrictMono R] [MulPo
sStrictMono R] [AddLeftStrictMono R] [AddLeftReflectLT R] {a : R} : 0 < a * a ↔ 
a …
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
The sine of an angle in a right-angled triangle multiplied by the hypotenuse equ
als the
opposite side.
-/
theorem sin_angle_add_mul_norm_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
    Real.sin (angle x (x + y)) * ‖x + y‖ = ‖y‖ := by
  by_cases h0 : x = 0 ∧ y = 0; · simp [h0]
  rw [not_and_or] at h0
  rw [sin_angle_add_of_inner_eq_zero h h0, div_mul_cancel₀]
  rw [← mul_self_ne_zero, norm_add_sq_eq_norm_sq_add_norm_sq_real h]
  refine (ne_of_lt ?_).symm
  rcases h0 with (h0 | h0)
  · exact Left.add_pos_of_pos_of_nonneg (mul_self_pos.2 (norm_ne_zero_iff.2 h0)) (mul_self_nonneg _)
  · exact Left.add_pos_of_nonneg_of_pos (mul_self_nonneg _) (mul_self_pos.2 (norm_ne_zero_iff.2 h0))

/-- The tangent of an angle in a right-angled triangle multiplied by the adjacent side equals
the opposite side. -/
/-
**InnerProductGeometry.tan_angle_add_mul_norm_of_inner_eq_zero** 是 Mathlib 中的一个定
理，位于命名空间 `InnerProductGeometry`。
形式化陈述：tan_angle_add_mul_norm_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x
 != 0 ∨ y = 0) : Real.tan (angle x (x + y)) * ‖x‖ = ‖y‖
参数：h : ⟪x, y⟫ = 0；h0 : x != 0 ∨ y = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InnerProductGeometry.tan_angle_add_of_inner_eq_zero`：tan_angle_add_of_in
ner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) : Real.tan (angle x (x + y)) = ‖y‖ / ‖x‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsUnit.div_mul_cancel`：∀ {α : Type u} [inst : DivisionMonoid α] {b : α},
 IsUnit b → ∀ (a : α), a / b * b = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0

--- 原说明 ---
The tangent of an angle in a right-angled triangle multiplied by the adjacent si
de equals
the opposite side.
-/
theorem tan_angle_add_mul_norm_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x ≠ 0 ∨ y = 0) :
    Real.tan (angle x (x + y)) * ‖x‖ = ‖y‖ := by
  rw [tan_angle_add_of_inner_eq_zero h]
  rcases h0 with (h0 | h0) <;> simp [h0]

/-- A side of a right-angled triangle divided by the cosine of the adjacent angle equals the
hypotenuse. -/
/-
**InnerProductGeometry.norm_div_cos_angle_add_of_inner_eq_zero** 是 Mathlib 中的一个定
理，位于命名空间 `InnerProductGeometry`。
形式化陈述：norm_div_cos_angle_add_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x
 != 0 ∨ y = 0) : ‖x‖ / Real.cos (angle x (x + y)) = ‖x + y‖
参数：h : ⟪x, y⟫ = 0；h0 : x != 0 ∨ y = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InnerProductGeometry.cos_angle_add_of_inner_eq_zero`：cos_angle_add_of_in
ner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) : Real.cos (angle x (x + y)) = ‖x‖ / ‖x +
 y‖
· 使用定理 `div_div_eq_mul_div`：div_div_eq_mul_div : a / (b / c) = a * c / b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_inv_cancel_right₀`：mul_inv_cancel_right₀ (h : b != 0) (a : G₀) : a *
 b * b⁻¹ = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_ne_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≠ 0 ↔ a ≠ 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `div_div_self`：div_div_self (a : G₀) : a / (a / a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A side of a right-angled triangle divided by the cosine of the adjacent angle eq
uals the
hypotenuse.
-/
theorem norm_div_cos_angle_add_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x ≠ 0 ∨ y = 0) :
    ‖x‖ / Real.cos (angle x (x + y)) = ‖x + y‖ := by
  rw [cos_angle_add_of_inner_eq_zero h]
  rcases h0 with (h0 | h0)
  · rw [div_div_eq_mul_div, mul_comm, div_eq_mul_inv, mul_inv_cancel_right₀ (norm_ne_zero_iff.2 h0)]
  · simp [h0]

/-- A side of a right-angled triangle divided by the sine of the opposite angle equals the
hypotenuse. -/
/-
**InnerProductGeometry.norm_div_sin_angle_add_of_inner_eq_zero** 是 Mathlib 中的一个定
理，位于命名空间 `InnerProductGeometry`。
形式化陈述：norm_div_sin_angle_add_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x
 = 0 ∨ y != 0) : ‖y‖ / Real.sin (angle x (x + y)) = ‖x + y‖
参数：h : ⟪x, y⟫ = 0；h0 : x = 0 ∨ y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `InnerProductGeometry.angle_zero_left`：angle_zero_left (x : V) : angle 0 
x = π / 2
· 使用定理 `Real.sin_pi_div_two`：sin_pi_div_two : sin (π / 2) = 1
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `InnerProductGeometry.sin_angle_add_of_inner_eq_zero`：sin_angle_add_of_in
ner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0 ∨ y != 0) : Real.sin (angle 
x (x + y)) = ‖y‖ / ‖x + y‖
· 使用定理 `div_div_eq_mul_div`：div_div_eq_mul_div : a / (b / c) = a * c / b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_inv_cancel_right₀`：mul_inv_cancel_right₀ (h : b != 0) (a : G₀) : a *
 b * b⁻¹ = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_ne_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≠ 0 ↔ a ≠ 0

--- 原说明 ---
A side of a right-angled triangle divided by the sine of the opposite angle equa
ls the
hypotenuse.
-/
theorem norm_div_sin_angle_add_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x = 0 ∨ y ≠ 0) :
    ‖y‖ / Real.sin (angle x (x + y)) = ‖x + y‖ := by
  rcases h0 with (h0 | h0); · simp [h0]
  rw [sin_angle_add_of_inner_eq_zero h (Or.inr h0), div_div_eq_mul_div, mul_comm, div_eq_mul_inv,
    mul_inv_cancel_right₀ (norm_ne_zero_iff.2 h0)]

/-- A side of a right-angled triangle divided by the tangent of the opposite angle equals the
adjacent side. -/
/-
**InnerProductGeometry.norm_div_tan_angle_add_of_inner_eq_zero** 是 Mathlib 中的一个定
理，位于命名空间 `InnerProductGeometry`。
形式化陈述：norm_div_tan_angle_add_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x
 = 0 ∨ y != 0) : ‖y‖ / Real.tan (angle x (x + y)) = ‖x‖
参数：h : ⟪x, y⟫ = 0；h0 : x = 0 ∨ y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InnerProductGeometry.tan_angle_add_of_inner_eq_zero`：tan_angle_add_of_in
ner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) : Real.tan (angle x (x + y)) = ‖y‖ / ‖x‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `div_div_eq_mul_div`：div_div_eq_mul_div : a / (b / c) = a * c / b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_inv_cancel_right₀`：mul_inv_cancel_right₀ (h : b != 0) (a : G₀) : a *
 b * b⁻¹ = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_ne_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≠ 0 ↔ a ≠ 0

--- 原说明 ---
A side of a right-angled triangle divided by the tangent of the opposite angle e
quals the
adjacent side.
-/
theorem norm_div_tan_angle_add_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x = 0 ∨ y ≠ 0) :
    ‖y‖ / Real.tan (angle x (x + y)) = ‖x‖ := by
  rw [tan_angle_add_of_inner_eq_zero h]
  rcases h0 with (h0 | h0)
  · simp [h0]
  · rw [div_div_eq_mul_div, mul_comm, div_eq_mul_inv, mul_inv_cancel_right₀ (norm_ne_zero_iff.2 h0)]

/-- An angle in a right-angled triangle expressed using `arccos`, version subtracting vectors. -/
/-
**InnerProductGeometry.angle_sub_eq_arccos_of_inner_eq_zero** 是 Mathlib 中的一个定理，位
于命名空间 `InnerProductGeometry`。
形式化陈述：angle_sub_eq_arccos_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) : angle x 
(x - y) = Real.arccos (‖x‖ / ‖x - y‖)
参数：h : ⟪x, y⟫ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `InnerProductGeometry.angle_add_eq_arccos_of_inner_eq_zero`：angle_add_eq_
arccos_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) : angle x (x + y) = Real.arcc
os (‖x‖ / ‖x + y‖)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_neg_right`：inner_neg_right (x y : E) : ⟪x, -y⟫ = -⟪x, y⟫
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0

--- 原说明 ---
An angle in a right-angled triangle expressed using `arccos`, version subtractin
g vectors.
-/
theorem angle_sub_eq_arccos_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
    angle x (x - y) = Real.arccos (‖x‖ / ‖x - y‖) := by
  rw [← neg_eq_zero, ← inner_neg_right] at h
  rw [sub_eq_add_neg, angle_add_eq_arccos_of_inner_eq_zero h]

/-- An angle in a right-angled triangle expressed using `arcsin`, version subtracting vectors. -/
/-
**InnerProductGeometry.angle_sub_eq_arcsin_of_inner_eq_zero** 是 Mathlib 中的一个定理，位
于命名空间 `InnerProductGeometry`。
形式化陈述：angle_sub_eq_arcsin_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x !=
 0 ∨ y != 0) : angle x (x - y) = Real.arcsin (‖y‖ / ‖x - y‖)
参数：h : ⟪x, y⟫ = 0；h0 : x != 0 ∨ y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `InnerProductGeometry.angle_add_eq_arcsin_of_inner_eq_zero`：angle_add_eq_
arcsin_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0 ∨ y != 0) : angl
e x (x + y) = Real.arcsin (‖y‖ / ‖x + y‖)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_neg_right`：inner_neg_right (x y : E) : ⟪x, -y⟫ = -⟪x, y⟫
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `or_comm`：∀ {a b : Prop}, a ∨ b ↔ b ∨ a
· 使用定理 `neg_ne_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a ≠
 0 ↔ a ≠ 0
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖

--- 原说明 ---
An angle in a right-angled triangle expressed using `arcsin`, version subtractin
g vectors.
-/
theorem angle_sub_eq_arcsin_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x ≠ 0 ∨ y ≠ 0) :
    angle x (x - y) = Real.arcsin (‖y‖ / ‖x - y‖) := by
  rw [← neg_eq_zero, ← inner_neg_right] at h
  rw [or_comm, ← neg_ne_zero, or_comm] at h0
  rw [sub_eq_add_neg, angle_add_eq_arcsin_of_inner_eq_zero h h0, norm_neg]

/-- An angle in a right-angled triangle expressed using `arctan`, version subtracting vectors. -/
/-
**InnerProductGeometry.angle_sub_eq_arctan_of_inner_eq_zero** 是 Mathlib 中的一个定理，位
于命名空间 `InnerProductGeometry`。
形式化陈述：angle_sub_eq_arctan_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x !=
 0) : angle x (x - y) = Real.arctan (‖y‖ / ‖x‖)
参数：h : ⟪x, y⟫ = 0；h0 : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `InnerProductGeometry.angle_add_eq_arctan_of_inner_eq_zero`：angle_add_eq_
arctan_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0) : angle x (x + 
y) = Real.arctan (‖y‖ / ‖x‖)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_neg_right`：inner_neg_right (x y : E) : ⟪x, -y⟫ = -⟪x, y⟫
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖

--- 原说明 ---
An angle in a right-angled triangle expressed using `arctan`, version subtractin
g vectors.
-/
theorem angle_sub_eq_arctan_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x ≠ 0) :
    angle x (x - y) = Real.arctan (‖y‖ / ‖x‖) := by
  rw [← neg_eq_zero, ← inner_neg_right] at h
  rw [sub_eq_add_neg, angle_add_eq_arctan_of_inner_eq_zero h h0, norm_neg]

/-- An angle in a non-degenerate right-angled triangle is positive, version subtracting
vectors. -/
/-
**InnerProductGeometry.angle_sub_pos_of_inner_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 
`InnerProductGeometry`。
形式化陈述：angle_sub_pos_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x = 0 ∨ y 
!= 0) : 0 < angle x (x - y)
参数：h : ⟪x, y⟫ = 0；h0 : x = 0 ∨ y != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `InnerProductGeometry.angle_add_pos_of_inner_eq_zero`：angle_add_pos_of_in
ner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x = 0 ∨ y != 0) : 0 < angle x (x + 
y)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_neg_right`：inner_neg_right (x y : E) : ⟪x, -y⟫ = -⟪x, y⟫
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `neg_ne_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a ≠
 0 ↔ a ≠ 0

--- 原说明 ---
An angle in a non-degenerate right-angled triangle is positive, version subtract
ing
vectors.
-/
theorem angle_sub_pos_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x = 0 ∨ y ≠ 0) :
    0 < angle x (x - y) := by
  rw [← neg_eq_zero, ← inner_neg_right] at h
  rw [← neg_ne_zero] at h0
  rw [sub_eq_add_neg]
  exact angle_add_pos_of_inner_eq_zero h h0

/-- An angle in a right-angled triangle is at most `π / 2`, version subtracting vectors. -/
/-
**InnerProductGeometry.angle_sub_le_pi_div_two_of_inner_eq_zero** 是 Mathlib 中的一个
定理，位于命名空间 `InnerProductGeometry`。
形式化陈述：angle_sub_le_pi_div_two_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) : angl
e x (x - y) <= π / 2
参数：h : ⟪x, y⟫ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `InnerProductGeometry.angle_add_le_pi_div_two_of_inner_eq_zero`：angle_add
_le_pi_div_two_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) : angle x (x + y) <= 
π / 2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_neg_right`：inner_neg_right (x y : E) : ⟪x, -y⟫ = -⟪x, y⟫
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0

--- 原说明 ---
An angle in a right-angled triangle is at most `π / 2`, version subtracting vect
ors.
-/
theorem angle_sub_le_pi_div_two_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
    angle x (x - y) ≤ π / 2 := by
  rw [← neg_eq_zero, ← inner_neg_right] at h
  rw [sub_eq_add_neg]
  exact angle_add_le_pi_div_two_of_inner_eq_zero h

/-- An angle in a non-degenerate right-angled triangle is less than `π / 2`, version subtracting
vectors. -/
/-
**InnerProductGeometry.angle_sub_lt_pi_div_two_of_inner_eq_zero** 是 Mathlib 中的一个
定理，位于命名空间 `InnerProductGeometry`。
形式化陈述：angle_sub_lt_pi_div_two_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : 
x != 0) : angle x (x - y) < π / 2
参数：h : ⟪x, y⟫ = 0；h0 : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `InnerProductGeometry.angle_add_lt_pi_div_two_of_inner_eq_zero`：angle_add
_lt_pi_div_two_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0) : angle
 x (x + y) < π / 2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_neg_right`：inner_neg_right (x y : E) : ⟪x, -y⟫ = -⟪x, y⟫
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0

--- 原说明 ---
An angle in a non-degenerate right-angled triangle is less than `π / 2`, version
 subtracting
vectors.
-/
theorem angle_sub_lt_pi_div_two_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x ≠ 0) :
    angle x (x - y) < π / 2 := by
  rw [← neg_eq_zero, ← inner_neg_right] at h
  rw [sub_eq_add_neg]
  exact angle_add_lt_pi_div_two_of_inner_eq_zero h h0

/-- The cosine of an angle in a right-angled triangle as a ratio of sides, version subtracting
vectors. -/
/-
**InnerProductGeometry.cos_angle_sub_of_inner_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 
`InnerProductGeometry`。
形式化陈述：cos_angle_sub_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) : Real.cos (angl
e x (x - y)) = ‖x‖ / ‖x - y‖
参数：h : ⟪x, y⟫ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `InnerProductGeometry.cos_angle_add_of_inner_eq_zero`：cos_angle_add_of_in
ner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) : Real.cos (angle x (x + y)) = ‖x‖ / ‖x +
 y‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_neg_right`：inner_neg_right (x y : E) : ⟪x, -y⟫ = -⟪x, y⟫
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0

--- 原说明 ---
The cosine of an angle in a right-angled triangle as a ratio of sides, version s
ubtracting
vectors.
-/
theorem cos_angle_sub_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
    Real.cos (angle x (x - y)) = ‖x‖ / ‖x - y‖ := by
  rw [← neg_eq_zero, ← inner_neg_right] at h
  rw [sub_eq_add_neg, cos_angle_add_of_inner_eq_zero h]

/-- The sine of an angle in a right-angled triangle as a ratio of sides, version subtracting
vectors. -/
/-
**InnerProductGeometry.sin_angle_sub_of_inner_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 
`InnerProductGeometry`。
形式化陈述：sin_angle_sub_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0 ∨ y
 != 0) : Real.sin (angle x (x - y)) = ‖y‖ / ‖x - y‖
参数：h : ⟪x, y⟫ = 0；h0 : x != 0 ∨ y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `InnerProductGeometry.sin_angle_add_of_inner_eq_zero`：sin_angle_add_of_in
ner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0 ∨ y != 0) : Real.sin (angle 
x (x + y)) = ‖y‖ / ‖x + y‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_neg_right`：inner_neg_right (x y : E) : ⟪x, -y⟫ = -⟪x, y⟫
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `or_comm`：∀ {a b : Prop}, a ∨ b ↔ b ∨ a
· 使用定理 `neg_ne_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a ≠
 0 ↔ a ≠ 0
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖

--- 原说明 ---
The sine of an angle in a right-angled triangle as a ratio of sides, version sub
tracting
vectors.
-/
theorem sin_angle_sub_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x ≠ 0 ∨ y ≠ 0) :
    Real.sin (angle x (x - y)) = ‖y‖ / ‖x - y‖ := by
  rw [← neg_eq_zero, ← inner_neg_right] at h
  rw [or_comm, ← neg_ne_zero, or_comm] at h0
  rw [sub_eq_add_neg, sin_angle_add_of_inner_eq_zero h h0, norm_neg]

/-- The tangent of an angle in a right-angled triangle as a ratio of sides, version subtracting
vectors. -/
/-
**InnerProductGeometry.tan_angle_sub_of_inner_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 
`InnerProductGeometry`。
形式化陈述：tan_angle_sub_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) : Real.tan (angl
e x (x - y)) = ‖y‖ / ‖x‖
参数：h : ⟪x, y⟫ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `InnerProductGeometry.tan_angle_add_of_inner_eq_zero`：tan_angle_add_of_in
ner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) : Real.tan (angle x (x + y)) = ‖y‖ / ‖x‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_neg_right`：inner_neg_right (x y : E) : ⟪x, -y⟫ = -⟪x, y⟫
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖

--- 原说明 ---
The tangent of an angle in a right-angled triangle as a ratio of sides, version 
subtracting
vectors.
-/
theorem tan_angle_sub_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
    Real.tan (angle x (x - y)) = ‖y‖ / ‖x‖ := by
  rw [← neg_eq_zero, ← inner_neg_right] at h
  rw [sub_eq_add_neg, tan_angle_add_of_inner_eq_zero h, norm_neg]

/-- The cosine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
adjacent side, version subtracting vectors. -/
/-
**InnerProductGeometry.cos_angle_sub_mul_norm_of_inner_eq_zero** 是 Mathlib 中的一个定
理，位于命名空间 `InnerProductGeometry`。
形式化陈述：cos_angle_sub_mul_norm_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) : Real.
cos (angle x (x - y)) * ‖x - y‖ = ‖x‖
参数：h : ⟪x, y⟫ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `InnerProductGeometry.cos_angle_add_mul_norm_of_inner_eq_zero`：cos_angle_
add_mul_norm_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) : Real.cos (angle x (x 
+ y)) * ‖x + y‖ = ‖x‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_neg_right`：inner_neg_right (x y : E) : ⟪x, -y⟫ = -⟪x, y⟫
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0

--- 原说明 ---
The cosine of an angle in a right-angled triangle multiplied by the hypotenuse e
quals the
adjacent side, version subtracting vectors.
-/
theorem cos_angle_sub_mul_norm_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
    Real.cos (angle x (x - y)) * ‖x - y‖ = ‖x‖ := by
  rw [← neg_eq_zero, ← inner_neg_right] at h
  rw [sub_eq_add_neg, cos_angle_add_mul_norm_of_inner_eq_zero h]

/-- The sine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
opposite side, version subtracting vectors. -/
/-
**InnerProductGeometry.sin_angle_sub_mul_norm_of_inner_eq_zero** 是 Mathlib 中的一个定
理，位于命名空间 `InnerProductGeometry`。
形式化陈述：sin_angle_sub_mul_norm_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) : Real.
sin (angle x (x - y)) * ‖x - y‖ = ‖y‖
参数：h : ⟪x, y⟫ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `InnerProductGeometry.sin_angle_add_mul_norm_of_inner_eq_zero`：sin_angle_
add_mul_norm_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) : Real.sin (angle x (x 
+ y)) * ‖x + y‖ = ‖y‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_neg_right`：inner_neg_right (x y : E) : ⟪x, -y⟫ = -⟪x, y⟫
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖

--- 原说明 ---
The sine of an angle in a right-angled triangle multiplied by the hypotenuse equ
als the
opposite side, version subtracting vectors.
-/
theorem sin_angle_sub_mul_norm_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) :
    Real.sin (angle x (x - y)) * ‖x - y‖ = ‖y‖ := by
  rw [← neg_eq_zero, ← inner_neg_right] at h
  rw [sub_eq_add_neg, sin_angle_add_mul_norm_of_inner_eq_zero h, norm_neg]

/-- The tangent of an angle in a right-angled triangle multiplied by the adjacent side equals
the opposite side, version subtracting vectors. -/
/-
**InnerProductGeometry.tan_angle_sub_mul_norm_of_inner_eq_zero** 是 Mathlib 中的一个定
理，位于命名空间 `InnerProductGeometry`。
形式化陈述：tan_angle_sub_mul_norm_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x
 != 0 ∨ y = 0) : Real.tan (angle x (x - y)) * ‖x‖ = ‖y‖
参数：h : ⟪x, y⟫ = 0；h0 : x != 0 ∨ y = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `InnerProductGeometry.tan_angle_add_mul_norm_of_inner_eq_zero`：tan_angle_
add_mul_norm_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0 ∨ y = 0) :
 Real.tan (angle x (x + y)) * ‖x‖ = ‖y‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_neg_right`：inner_neg_right (x y : E) : ⟪x, -y⟫ = -⟪x, y⟫
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖

--- 原说明 ---
The tangent of an angle in a right-angled triangle multiplied by the adjacent si
de equals
the opposite side, version subtracting vectors.
-/
theorem tan_angle_sub_mul_norm_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x ≠ 0 ∨ y = 0) :
    Real.tan (angle x (x - y)) * ‖x‖ = ‖y‖ := by
  rw [← neg_eq_zero, ← inner_neg_right] at h
  rw [← neg_eq_zero] at h0
  rw [sub_eq_add_neg, tan_angle_add_mul_norm_of_inner_eq_zero h h0, norm_neg]

/-- A side of a right-angled triangle divided by the cosine of the adjacent angle equals the
hypotenuse, version subtracting vectors. -/
/-
**InnerProductGeometry.norm_div_cos_angle_sub_of_inner_eq_zero** 是 Mathlib 中的一个定
理，位于命名空间 `InnerProductGeometry`。
形式化陈述：norm_div_cos_angle_sub_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x
 != 0 ∨ y = 0) : ‖x‖ / Real.cos (angle x (x - y)) = ‖x - y‖
参数：h : ⟪x, y⟫ = 0；h0 : x != 0 ∨ y = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `InnerProductGeometry.norm_div_cos_angle_add_of_inner_eq_zero`：norm_div_c
os_angle_add_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0 ∨ y = 0) :
 ‖x‖ / Real.cos (angle x (x + y)) = ‖x + y‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_neg_right`：inner_neg_right (x y : E) : ⟪x, -y⟫ = -⟪x, y⟫
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0

--- 原说明 ---
A side of a right-angled triangle divided by the cosine of the adjacent angle eq
uals the
hypotenuse, version subtracting vectors.
-/
theorem norm_div_cos_angle_sub_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x ≠ 0 ∨ y = 0) :
    ‖x‖ / Real.cos (angle x (x - y)) = ‖x - y‖ := by
  rw [← neg_eq_zero, ← inner_neg_right] at h
  rw [← neg_eq_zero] at h0
  rw [sub_eq_add_neg, norm_div_cos_angle_add_of_inner_eq_zero h h0]

/-- A side of a right-angled triangle divided by the sine of the opposite angle equals the
hypotenuse, version subtracting vectors. -/
/-
**InnerProductGeometry.norm_div_sin_angle_sub_of_inner_eq_zero** 是 Mathlib 中的一个定
理，位于命名空间 `InnerProductGeometry`。
形式化陈述：norm_div_sin_angle_sub_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x
 = 0 ∨ y != 0) : ‖y‖ / Real.sin (angle x (x - y)) = ‖x - y‖
参数：h : ⟪x, y⟫ = 0；h0 : x = 0 ∨ y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `InnerProductGeometry.norm_div_sin_angle_add_of_inner_eq_zero`：norm_div_s
in_angle_add_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x = 0 ∨ y != 0) :
 ‖y‖ / Real.sin (angle x (x + y)) = ‖x + y‖
· 使用定理 `inner_neg_right`：inner_neg_right (x y : E) : ⟪x, -y⟫ = -⟪x, y⟫
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `neg_ne_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a ≠
 0 ↔ a ≠ 0

--- 原说明 ---
A side of a right-angled triangle divided by the sine of the opposite angle equa
ls the
hypotenuse, version subtracting vectors.
-/
theorem norm_div_sin_angle_sub_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x = 0 ∨ y ≠ 0) :
    ‖y‖ / Real.sin (angle x (x - y)) = ‖x - y‖ := by
  rw [← neg_eq_zero, ← inner_neg_right] at h
  rw [← neg_ne_zero] at h0
  rw [sub_eq_add_neg, ← norm_neg, norm_div_sin_angle_add_of_inner_eq_zero h h0]

/-- A side of a right-angled triangle divided by the tangent of the opposite angle equals the
adjacent side, version subtracting vectors. -/
/-
**InnerProductGeometry.norm_div_tan_angle_sub_of_inner_eq_zero** 是 Mathlib 中的一个定
理，位于命名空间 `InnerProductGeometry`。
形式化陈述：norm_div_tan_angle_sub_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x
 = 0 ∨ y != 0) : ‖y‖ / Real.tan (angle x (x - y)) = ‖x‖
参数：h : ⟪x, y⟫ = 0；h0 : x = 0 ∨ y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `InnerProductGeometry.norm_div_tan_angle_add_of_inner_eq_zero`：norm_div_t
an_angle_add_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x = 0 ∨ y != 0) :
 ‖y‖ / Real.tan (angle x (x + y)) = ‖x‖
· 使用定理 `inner_neg_right`：inner_neg_right (x y : E) : ⟪x, -y⟫ = -⟪x, y⟫
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `neg_ne_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a ≠
 0 ↔ a ≠ 0

--- 原说明 ---
A side of a right-angled triangle divided by the tangent of the opposite angle e
quals the
adjacent side, version subtracting vectors.
-/
theorem norm_div_tan_angle_sub_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x = 0 ∨ y ≠ 0) :
    ‖y‖ / Real.tan (angle x (x - y)) = ‖x‖ := by
  rw [← neg_eq_zero, ← inner_neg_right] at h
  rw [← neg_ne_zero] at h0
  rw [sub_eq_add_neg, ← norm_neg, norm_div_tan_angle_add_of_inner_eq_zero h h0]

end InnerProductGeometry

namespace EuclideanGeometry

open InnerProductGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- **Pythagorean theorem**, if-and-only-if angle-at-point form. -/
/-
**EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two** 是 M
athlib 中的一个定理，位于命名空间 `EuclideanGeometry`。
形式化陈述：dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two (p₁ p₂ p₃ : P) : di
st p₁ p₃ * dist p₁ p₃ = dist p₁ p₂ * dist p₁ p₂ + dist p₃ p₂ * dist p₃ p₂ ↔ ∠ p₁
 p₂ p₃ = π / 2
参数：p₁ p₂ p₃ : P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用定理 `EuclideanGeometry.angle.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `InnerProductGeometry.norm_sub_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_
div_two`：norm_sub_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two (x y : V) : 
‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ ↔ angle x y = π / 2
· 使用定理 `vsub_sub_vsub_cancel_right`：∀ {G : Type u_1} {P : Type u_2} [inst : AddG
roup G] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₃ - (p₂ -ᵥ p₃) = p₁ -ᵥ p₂
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
**Pythagorean theorem**, if-and-only-if angle-at-point form.
-/
theorem dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two (p₁ p₂ p₃ : P) :
    dist p₁ p₃ * dist p₁ p₃ = dist p₁ p₂ * dist p₁ p₂ + dist p₃ p₂ * dist p₃ p₂ ↔
      ∠ p₁ p₂ p₃ = π / 2 := by
  rw [dist_comm p₃ p₂, dist_eq_norm_vsub V p₁ p₃, dist_eq_norm_vsub V p₁ p₂,
    dist_eq_norm_vsub V p₂ p₃, angle, ← norm_sub_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two,
    vsub_sub_vsub_cancel_right p₁, ← neg_vsub_eq_vsub_rev p₂ p₃, norm_neg]

/-- An angle in a right-angled triangle expressed using `arccos`. -/
/-
**EuclideanGeometry.angle_eq_arccos_of_angle_eq_pi_div_two** 是 Mathlib 中的一个定理，位于
命名空间 `EuclideanGeometry`。
形式化陈述：angle_eq_arccos_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π 
/ 2) : ∠ p₂ p₃ p₁ = Real.arccos (dist p₃ p₂ / dist p₁ p₃)
参数：h : ∠ p₁ p₂ p₃ = π / 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.angle.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `dist_eq_norm_vsub'`：dist_eq_norm_vsub' (x y : P) : dist x y = ‖y -ᵥ x‖
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_add_vsub_cancel`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₂ + (p₂ -ᵥ p₃) = p₁ -ᵥ p₃
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `InnerProductGeometry.angle_add_eq_arccos_of_inner_eq_zero`：angle_add_eq_
arccos_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) : angle x (x + y) = Real.arcc
os (‖x‖ / ‖x + y‖)
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `inner_neg_left`：inner_neg_left (x y : E) : ⟪-x, y⟫ = -⟪x, y⟫
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `real_inner_comm`：real_inner_comm (x y : F) : ⟪y, x⟫_Real = ⟪x, y⟫_Real
· 使用定理 `InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two`：inner_eq_zer
o_iff_angle_eq_pi_div_two (x y : V) : ⟪x, y⟫ = 0 ↔ angle x y = π / 2

--- 原说明 ---
An angle in a right-angled triangle expressed using `arccos`.
-/
theorem angle_eq_arccos_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) :
    ∠ p₂ p₃ p₁ = Real.arccos (dist p₃ p₂ / dist p₁ p₃) := by
  rw [angle, ← inner_eq_zero_iff_angle_eq_pi_div_two, real_inner_comm, ← neg_eq_zero, ←
    inner_neg_left, neg_vsub_eq_vsub_rev] at h
  rw [angle, dist_eq_norm_vsub' V p₃ p₂, dist_eq_norm_vsub V p₁ p₃, ← vsub_add_vsub_cancel p₁ p₂ p₃,
    add_comm, angle_add_eq_arccos_of_inner_eq_zero h]

/-- An angle in a right-angled triangle expressed using `arcsin`. -/
/-
**EuclideanGeometry.angle_eq_arcsin_of_angle_eq_pi_div_two** 是 Mathlib 中的一个定理，位于
命名空间 `EuclideanGeometry`。
形式化陈述：angle_eq_arcsin_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π 
/ 2) (h0 : p₁ != p₂ ∨ p₃ != p₂) : ∠ p₂ p₃ p₁ = Real.arcsin (dist p₁ p₂ / dist p₁
 p₃)
参数：h : ∠ p₁ p₂ p₃ = π / 2；h0 : p₁ != p₂ ∨ p₃ != p₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.angle.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_add_vsub_cancel`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₂ + (p₂ -ᵥ p₃) = p₁ -ᵥ p₃
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `InnerProductGeometry.angle_add_eq_arcsin_of_inner_eq_zero`：angle_add_eq_
arcsin_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0 ∨ y != 0) : angl
e x (x + y) = Real.arcsin (‖y‖ / ‖x + y‖)
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `inner_neg_left`：inner_neg_left (x y : E) : ⟪-x, y⟫ = -⟪x, y⟫
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `real_inner_comm`：real_inner_comm (x y : F) : ⟪y, x⟫_Real = ⟪x, y⟫_Real
· 使用定理 `InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two`：inner_eq_zer
o_iff_angle_eq_pi_div_two (x y : V) : ⟪x, y⟫ = 0 ↔ angle x y = π / 2
· 使用定理 `or_comm`：∀ {a b : Prop}, a ∨ b ↔ b ∨ a
· 使用定理 `vsub_ne_zero`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : A
ddTorsor G P] {p q : P}, p -ᵥ q ≠ 0 ↔ p ≠ q
· 使用定理 `ne_comm`：∀ {α : Sort u_1} {a b : α}, a ≠ b ↔ b ≠ a

--- 原说明 ---
An angle in a right-angled triangle expressed using `arcsin`.
-/
theorem angle_eq_arcsin_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
    (h0 : p₁ ≠ p₂ ∨ p₃ ≠ p₂) : ∠ p₂ p₃ p₁ = Real.arcsin (dist p₁ p₂ / dist p₁ p₃) := by
  rw [angle, ← inner_eq_zero_iff_angle_eq_pi_div_two, real_inner_comm, ← neg_eq_zero, ←
    inner_neg_left, neg_vsub_eq_vsub_rev] at h
  rw [← @vsub_ne_zero V, @ne_comm _ p₃, ← @vsub_ne_zero V _ _ _ p₂, or_comm] at h0
  rw [angle, dist_eq_norm_vsub V p₁ p₂, dist_eq_norm_vsub V p₁ p₃, ← vsub_add_vsub_cancel p₁ p₂ p₃,
    add_comm, angle_add_eq_arcsin_of_inner_eq_zero h h0]

/-- An angle in a right-angled triangle expressed using `arctan`. -/
/-
**EuclideanGeometry.angle_eq_arctan_of_angle_eq_pi_div_two** 是 Mathlib 中的一个定理，位于
命名空间 `EuclideanGeometry`。
形式化陈述：angle_eq_arctan_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π 
/ 2) (h0 : p₃ != p₂) : ∠ p₂ p₃ p₁ = Real.arctan (dist p₁ p₂ / dist p₃ p₂)
参数：h : ∠ p₁ p₂ p₃ = π / 2；h0 : p₃ != p₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.angle.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用定理 `dist_eq_norm_vsub'`：dist_eq_norm_vsub' (x y : P) : dist x y = ‖y -ᵥ x‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_add_vsub_cancel`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₂ + (p₂ -ᵥ p₃) = p₁ -ᵥ p₃
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `InnerProductGeometry.angle_add_eq_arctan_of_inner_eq_zero`：angle_add_eq_
arctan_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0) : angle x (x + 
y) = Real.arctan (‖y‖ / ‖x‖)
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `inner_neg_left`：inner_neg_left (x y : E) : ⟪-x, y⟫ = -⟪x, y⟫
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `real_inner_comm`：real_inner_comm (x y : F) : ⟪y, x⟫_Real = ⟪x, y⟫_Real
· 使用定理 `InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two`：inner_eq_zer
o_iff_angle_eq_pi_div_two (x y : V) : ⟪x, y⟫ = 0 ↔ angle x y = π / 2
· 使用定理 `vsub_ne_zero`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : A
ddTorsor G P] {p q : P}, p -ᵥ q ≠ 0 ↔ p ≠ q
· 使用定理 `ne_comm`：∀ {α : Sort u_1} {a b : α}, a ≠ b ↔ b ≠ a

--- 原说明 ---
An angle in a right-angled triangle expressed using `arctan`.
-/
theorem angle_eq_arctan_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
    (h0 : p₃ ≠ p₂) : ∠ p₂ p₃ p₁ = Real.arctan (dist p₁ p₂ / dist p₃ p₂) := by
  rw [angle, ← inner_eq_zero_iff_angle_eq_pi_div_two, real_inner_comm, ← neg_eq_zero, ←
    inner_neg_left, neg_vsub_eq_vsub_rev] at h
  rw [ne_comm, ← @vsub_ne_zero V] at h0
  rw [angle, dist_eq_norm_vsub V p₁ p₂, dist_eq_norm_vsub' V p₃ p₂, ← vsub_add_vsub_cancel p₁ p₂ p₃,
    add_comm, angle_add_eq_arctan_of_inner_eq_zero h h0]

/-- An angle in a non-degenerate right-angled triangle is positive. -/
/-
**EuclideanGeometry.angle_pos_of_angle_eq_pi_div_two** 是 Mathlib 中的一个定理，位于命名空间 `
EuclideanGeometry`。
形式化陈述：angle_pos_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) (
h0 : p₁ != p₂ ∨ p₃ = p₂) : 0 < ∠ p₂ p₃ p₁
参数：h : ∠ p₁ p₂ p₃ = π / 2；h0 : p₁ != p₂ ∨ p₃ = p₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.angle.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_add_vsub_cancel`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₂ + (p₂ -ᵥ p₃) = p₁ -ᵥ p₃
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `InnerProductGeometry.angle_add_pos_of_inner_eq_zero`：angle_add_pos_of_in
ner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x = 0 ∨ y != 0) : 0 < angle x (x + 
y)
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `inner_neg_left`：inner_neg_left (x y : E) : ⟪-x, y⟫ = -⟪x, y⟫
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `real_inner_comm`：real_inner_comm (x y : F) : ⟪y, x⟫_Real = ⟪x, y⟫_Real
· 使用定理 `InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two`：inner_eq_zer
o_iff_angle_eq_pi_div_two (x y : V) : ⟪x, y⟫ = 0 ↔ angle x y = π / 2
· 使用定理 `or_comm`：∀ {a b : Prop}, a ∨ b ↔ b ∨ a
· 使用定理 `vsub_eq_zero_iff_eq`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] {p₁ p₂ : P}, p₁ -ᵥ p₂ = 0 ↔ p₁ = p₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `vsub_ne_zero`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : A
ddTorsor G P] {p q : P}, p -ᵥ q ≠ 0 ↔ p ≠ q

--- 原说明 ---
An angle in a non-degenerate right-angled triangle is positive.
-/
theorem angle_pos_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
    (h0 : p₁ ≠ p₂ ∨ p₃ = p₂) : 0 < ∠ p₂ p₃ p₁ := by
  rw [angle, ← inner_eq_zero_iff_angle_eq_pi_div_two, real_inner_comm, ← neg_eq_zero, ←
    inner_neg_left, neg_vsub_eq_vsub_rev] at h
  rw [← @vsub_ne_zero V, eq_comm, ← @vsub_eq_zero_iff_eq V, or_comm] at h0
  rw [angle, ← vsub_add_vsub_cancel p₁ p₂ p₃, add_comm]
  exact angle_add_pos_of_inner_eq_zero h h0

/-- An angle in a right-angled triangle is at most `π / 2`. -/
/-
**EuclideanGeometry.angle_le_pi_div_two_of_angle_eq_pi_div_two** 是 Mathlib 中的一个定
理，位于命名空间 `EuclideanGeometry`。
形式化陈述：angle_le_pi_div_two_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ 
= π / 2) : ∠ p₂ p₃ p₁ <= π / 2
参数：h : ∠ p₁ p₂ p₃ = π / 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.angle.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_add_vsub_cancel`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₂ + (p₂ -ᵥ p₃) = p₁ -ᵥ p₃
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `InnerProductGeometry.angle_add_le_pi_div_two_of_inner_eq_zero`：angle_add
_le_pi_div_two_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) : angle x (x + y) <= 
π / 2
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `inner_neg_left`：inner_neg_left (x y : E) : ⟪-x, y⟫ = -⟪x, y⟫
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `real_inner_comm`：real_inner_comm (x y : F) : ⟪y, x⟫_Real = ⟪x, y⟫_Real
· 使用定理 `InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two`：inner_eq_zer
o_iff_angle_eq_pi_div_two (x y : V) : ⟪x, y⟫ = 0 ↔ angle x y = π / 2

--- 原说明 ---
An angle in a right-angled triangle is at most `π / 2`.
-/
theorem angle_le_pi_div_two_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) :
    ∠ p₂ p₃ p₁ ≤ π / 2 := by
  rw [angle, ← inner_eq_zero_iff_angle_eq_pi_div_two, real_inner_comm, ← neg_eq_zero, ←
    inner_neg_left, neg_vsub_eq_vsub_rev] at h
  rw [angle, ← vsub_add_vsub_cancel p₁ p₂ p₃, add_comm]
  exact angle_add_le_pi_div_two_of_inner_eq_zero h

/-- An angle in a non-degenerate right-angled triangle is less than `π / 2`. -/
/-
**EuclideanGeometry.angle_lt_pi_div_two_of_angle_eq_pi_div_two** 是 Mathlib 中的一个定
理，位于命名空间 `EuclideanGeometry`。
形式化陈述：angle_lt_pi_div_two_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ 
= π / 2) (h0 : p₃ != p₂) : ∠ p₂ p₃ p₁ < π / 2
参数：h : ∠ p₁ p₂ p₃ = π / 2；h0 : p₃ != p₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.angle.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_add_vsub_cancel`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₂ + (p₂ -ᵥ p₃) = p₁ -ᵥ p₃
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `InnerProductGeometry.angle_add_lt_pi_div_two_of_inner_eq_zero`：angle_add
_lt_pi_div_two_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0) : angle
 x (x + y) < π / 2
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `inner_neg_left`：inner_neg_left (x y : E) : ⟪-x, y⟫ = -⟪x, y⟫
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `real_inner_comm`：real_inner_comm (x y : F) : ⟪y, x⟫_Real = ⟪x, y⟫_Real
· 使用定理 `InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two`：inner_eq_zer
o_iff_angle_eq_pi_div_two (x y : V) : ⟪x, y⟫ = 0 ↔ angle x y = π / 2
· 使用定理 `vsub_ne_zero`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : A
ddTorsor G P] {p q : P}, p -ᵥ q ≠ 0 ↔ p ≠ q
· 使用定理 `ne_comm`：∀ {α : Sort u_1} {a b : α}, a ≠ b ↔ b ≠ a

--- 原说明 ---
An angle in a non-degenerate right-angled triangle is less than `π / 2`.
-/
theorem angle_lt_pi_div_two_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
    (h0 : p₃ ≠ p₂) : ∠ p₂ p₃ p₁ < π / 2 := by
  rw [angle, ← inner_eq_zero_iff_angle_eq_pi_div_two, real_inner_comm, ← neg_eq_zero, ←
    inner_neg_left, neg_vsub_eq_vsub_rev] at h
  rw [ne_comm, ← @vsub_ne_zero V] at h0
  rw [angle, ← vsub_add_vsub_cancel p₁ p₂ p₃, add_comm]
  exact angle_add_lt_pi_div_two_of_inner_eq_zero h h0

/-- The cosine of an angle in a right-angled triangle as a ratio of sides. -/
/-
**EuclideanGeometry.cos_angle_of_angle_eq_pi_div_two** 是 Mathlib 中的一个定理，位于命名空间 `
EuclideanGeometry`。
形式化陈述：cos_angle_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) :
 Real.cos (∠ p₂ p₃ p₁) = dist p₃ p₂ / dist p₁ p₃
参数：h : ∠ p₁ p₂ p₃ = π / 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.angle.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `dist_eq_norm_vsub'`：dist_eq_norm_vsub' (x y : P) : dist x y = ‖y -ᵥ x‖
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_add_vsub_cancel`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₂ + (p₂ -ᵥ p₃) = p₁ -ᵥ p₃
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `InnerProductGeometry.cos_angle_add_of_inner_eq_zero`：cos_angle_add_of_in
ner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) : Real.cos (angle x (x + y)) = ‖x‖ / ‖x +
 y‖
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `inner_neg_left`：inner_neg_left (x y : E) : ⟪-x, y⟫ = -⟪x, y⟫
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `real_inner_comm`：real_inner_comm (x y : F) : ⟪y, x⟫_Real = ⟪x, y⟫_Real
· 使用定理 `InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two`：inner_eq_zer
o_iff_angle_eq_pi_div_two (x y : V) : ⟪x, y⟫ = 0 ↔ angle x y = π / 2

--- 原说明 ---
The cosine of an angle in a right-angled triangle as a ratio of sides.
-/
theorem cos_angle_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) :
    Real.cos (∠ p₂ p₃ p₁) = dist p₃ p₂ / dist p₁ p₃ := by
  rw [angle, ← inner_eq_zero_iff_angle_eq_pi_div_two, real_inner_comm, ← neg_eq_zero, ←
    inner_neg_left, neg_vsub_eq_vsub_rev] at h
  rw [angle, dist_eq_norm_vsub' V p₃ p₂, dist_eq_norm_vsub V p₁ p₃, ← vsub_add_vsub_cancel p₁ p₂ p₃,
    add_comm, cos_angle_add_of_inner_eq_zero h]

/-- The sine of an angle in a right-angled triangle as a ratio of sides. -/
/-
**EuclideanGeometry.sin_angle_of_angle_eq_pi_div_two** 是 Mathlib 中的一个定理，位于命名空间 `
EuclideanGeometry`。
形式化陈述：sin_angle_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) (
h0 : p₁ != p₂ ∨ p₃ != p₂) : Real.sin (∠ p₂ p₃ p₁) = dist p₁ p₂ / dist p₁ p₃
参数：h : ∠ p₁ p₂ p₃ = π / 2；h0 : p₁ != p₂ ∨ p₃ != p₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.angle.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_add_vsub_cancel`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₂ + (p₂ -ᵥ p₃) = p₁ -ᵥ p₃
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `InnerProductGeometry.sin_angle_add_of_inner_eq_zero`：sin_angle_add_of_in
ner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0 ∨ y != 0) : Real.sin (angle 
x (x + y)) = ‖y‖ / ‖x + y‖
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `inner_neg_left`：inner_neg_left (x y : E) : ⟪-x, y⟫ = -⟪x, y⟫
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `real_inner_comm`：real_inner_comm (x y : F) : ⟪y, x⟫_Real = ⟪x, y⟫_Real
· 使用定理 `InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two`：inner_eq_zer
o_iff_angle_eq_pi_div_two (x y : V) : ⟪x, y⟫ = 0 ↔ angle x y = π / 2
· 使用定理 `or_comm`：∀ {a b : Prop}, a ∨ b ↔ b ∨ a
· 使用定理 `vsub_ne_zero`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : A
ddTorsor G P] {p q : P}, p -ᵥ q ≠ 0 ↔ p ≠ q
· 使用定理 `ne_comm`：∀ {α : Sort u_1} {a b : α}, a ≠ b ↔ b ≠ a

--- 原说明 ---
The sine of an angle in a right-angled triangle as a ratio of sides.
-/
theorem sin_angle_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
    (h0 : p₁ ≠ p₂ ∨ p₃ ≠ p₂) : Real.sin (∠ p₂ p₃ p₁) = dist p₁ p₂ / dist p₁ p₃ := by
  rw [angle, ← inner_eq_zero_iff_angle_eq_pi_div_two, real_inner_comm, ← neg_eq_zero, ←
    inner_neg_left, neg_vsub_eq_vsub_rev] at h
  rw [← @vsub_ne_zero V, @ne_comm _ p₃, ← @vsub_ne_zero V _ _ _ p₂, or_comm] at h0
  rw [angle, dist_eq_norm_vsub V p₁ p₂, dist_eq_norm_vsub V p₁ p₃, ← vsub_add_vsub_cancel p₁ p₂ p₃,
    add_comm, sin_angle_add_of_inner_eq_zero h h0]

/-- The tangent of an angle in a right-angled triangle as a ratio of sides. -/
/-
**EuclideanGeometry.tan_angle_of_angle_eq_pi_div_two** 是 Mathlib 中的一个定理，位于命名空间 `
EuclideanGeometry`。
形式化陈述：tan_angle_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) :
 Real.tan (∠ p₂ p₃ p₁) = dist p₁ p₂ / dist p₃ p₂
参数：h : ∠ p₁ p₂ p₃ = π / 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.angle.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用定理 `dist_eq_norm_vsub'`：dist_eq_norm_vsub' (x y : P) : dist x y = ‖y -ᵥ x‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_add_vsub_cancel`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₂ + (p₂ -ᵥ p₃) = p₁ -ᵥ p₃
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `InnerProductGeometry.tan_angle_add_of_inner_eq_zero`：tan_angle_add_of_in
ner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) : Real.tan (angle x (x + y)) = ‖y‖ / ‖x‖
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `inner_neg_left`：inner_neg_left (x y : E) : ⟪-x, y⟫ = -⟪x, y⟫
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `real_inner_comm`：real_inner_comm (x y : F) : ⟪y, x⟫_Real = ⟪x, y⟫_Real
· 使用定理 `InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two`：inner_eq_zer
o_iff_angle_eq_pi_div_two (x y : V) : ⟪x, y⟫ = 0 ↔ angle x y = π / 2

--- 原说明 ---
The tangent of an angle in a right-angled triangle as a ratio of sides.
-/
theorem tan_angle_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) :
    Real.tan (∠ p₂ p₃ p₁) = dist p₁ p₂ / dist p₃ p₂ := by
  rw [angle, ← inner_eq_zero_iff_angle_eq_pi_div_two, real_inner_comm, ← neg_eq_zero, ←
    inner_neg_left, neg_vsub_eq_vsub_rev] at h
  rw [angle, dist_eq_norm_vsub V p₁ p₂, dist_eq_norm_vsub' V p₃ p₂, ← vsub_add_vsub_cancel p₁ p₂ p₃,
    add_comm, tan_angle_add_of_inner_eq_zero h]

/-- The cosine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
adjacent side. -/
/-
**EuclideanGeometry.cos_angle_mul_dist_of_angle_eq_pi_div_two** 是 Mathlib 中的一个定理
，位于命名空间 `EuclideanGeometry`。
形式化陈述：cos_angle_mul_dist_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ =
 π / 2) : Real.cos (∠ p₂ p₃ p₁) * dist p₁ p₃ = dist p₃ p₂
参数：h : ∠ p₁ p₂ p₃ = π / 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.angle.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `dist_eq_norm_vsub'`：dist_eq_norm_vsub' (x y : P) : dist x y = ‖y -ᵥ x‖
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_add_vsub_cancel`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₂ + (p₂ -ᵥ p₃) = p₁ -ᵥ p₃
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `InnerProductGeometry.cos_angle_add_mul_norm_of_inner_eq_zero`：cos_angle_
add_mul_norm_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) : Real.cos (angle x (x 
+ y)) * ‖x + y‖ = ‖x‖
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `inner_neg_left`：inner_neg_left (x y : E) : ⟪-x, y⟫ = -⟪x, y⟫
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `real_inner_comm`：real_inner_comm (x y : F) : ⟪y, x⟫_Real = ⟪x, y⟫_Real
· 使用定理 `InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two`：inner_eq_zer
o_iff_angle_eq_pi_div_two (x y : V) : ⟪x, y⟫ = 0 ↔ angle x y = π / 2

--- 原说明 ---
The cosine of an angle in a right-angled triangle multiplied by the hypotenuse e
quals the
adjacent side.
-/
theorem cos_angle_mul_dist_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) :
    Real.cos (∠ p₂ p₃ p₁) * dist p₁ p₃ = dist p₃ p₂ := by
  rw [angle, ← inner_eq_zero_iff_angle_eq_pi_div_two, real_inner_comm, ← neg_eq_zero, ←
    inner_neg_left, neg_vsub_eq_vsub_rev] at h
  rw [angle, dist_eq_norm_vsub' V p₃ p₂, dist_eq_norm_vsub V p₁ p₃, ← vsub_add_vsub_cancel p₁ p₂ p₃,
    add_comm, cos_angle_add_mul_norm_of_inner_eq_zero h]

/-- The sine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
opposite side. -/
/-
**EuclideanGeometry.sin_angle_mul_dist_of_angle_eq_pi_div_two** 是 Mathlib 中的一个定理
，位于命名空间 `EuclideanGeometry`。
形式化陈述：sin_angle_mul_dist_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ =
 π / 2) : Real.sin (∠ p₂ p₃ p₁) * dist p₁ p₃ = dist p₁ p₂
参数：h : ∠ p₁ p₂ p₃ = π / 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.angle.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_add_vsub_cancel`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₂ + (p₂ -ᵥ p₃) = p₁ -ᵥ p₃
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `InnerProductGeometry.sin_angle_add_mul_norm_of_inner_eq_zero`：sin_angle_
add_mul_norm_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) : Real.sin (angle x (x 
+ y)) * ‖x + y‖ = ‖y‖
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `inner_neg_left`：inner_neg_left (x y : E) : ⟪-x, y⟫ = -⟪x, y⟫
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `real_inner_comm`：real_inner_comm (x y : F) : ⟪y, x⟫_Real = ⟪x, y⟫_Real
· 使用定理 `InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two`：inner_eq_zer
o_iff_angle_eq_pi_div_two (x y : V) : ⟪x, y⟫ = 0 ↔ angle x y = π / 2

--- 原说明 ---
The sine of an angle in a right-angled triangle multiplied by the hypotenuse equ
als the
opposite side.
-/
theorem sin_angle_mul_dist_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2) :
    Real.sin (∠ p₂ p₃ p₁) * dist p₁ p₃ = dist p₁ p₂ := by
  rw [angle, ← inner_eq_zero_iff_angle_eq_pi_div_two, real_inner_comm, ← neg_eq_zero, ←
    inner_neg_left, neg_vsub_eq_vsub_rev] at h
  rw [angle, dist_eq_norm_vsub V p₁ p₂, dist_eq_norm_vsub V p₁ p₃, ← vsub_add_vsub_cancel p₁ p₂ p₃,
    add_comm, sin_angle_add_mul_norm_of_inner_eq_zero h]

/-- The tangent of an angle in a right-angled triangle multiplied by the adjacent side equals
the opposite side. -/
/-
**EuclideanGeometry.tan_angle_mul_dist_of_angle_eq_pi_div_two** 是 Mathlib 中的一个定理
，位于命名空间 `EuclideanGeometry`。
形式化陈述：tan_angle_mul_dist_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ =
 π / 2) (h0 : p₁ = p₂ ∨ p₃ != p₂) : Real.tan (∠ p₂ p₃ p₁) * dist p₃ p₂ = dist p₁
 p₂
参数：h : ∠ p₁ p₂ p₃ = π / 2；h0 : p₁ = p₂ ∨ p₃ != p₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.angle.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用定理 `dist_eq_norm_vsub'`：dist_eq_norm_vsub' (x y : P) : dist x y = ‖y -ᵥ x‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_add_vsub_cancel`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₂ + (p₂ -ᵥ p₃) = p₁ -ᵥ p₃
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `InnerProductGeometry.tan_angle_add_mul_norm_of_inner_eq_zero`：tan_angle_
add_mul_norm_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0 ∨ y = 0) :
 Real.tan (angle x (x + y)) * ‖x‖ = ‖y‖
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `inner_neg_left`：inner_neg_left (x y : E) : ⟪-x, y⟫ = -⟪x, y⟫
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `real_inner_comm`：real_inner_comm (x y : F) : ⟪y, x⟫_Real = ⟪x, y⟫_Real
· 使用定理 `InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two`：inner_eq_zer
o_iff_angle_eq_pi_div_two (x y : V) : ⟪x, y⟫ = 0 ↔ angle x y = π / 2
· 使用定理 `or_comm`：∀ {a b : Prop}, a ∨ b ↔ b ∨ a
· 使用定理 `vsub_eq_zero_iff_eq`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] {p₁ p₂ : P}, p₁ -ᵥ p₂ = 0 ↔ p₁ = p₂
· 使用定理 `vsub_ne_zero`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : A
ddTorsor G P] {p q : P}, p -ᵥ q ≠ 0 ↔ p ≠ q
· 使用定理 `ne_comm`：∀ {α : Sort u_1} {a b : α}, a ≠ b ↔ b ≠ a

--- 原说明 ---
The tangent of an angle in a right-angled triangle multiplied by the adjacent si
de equals
the opposite side.
-/
theorem tan_angle_mul_dist_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
    (h0 : p₁ = p₂ ∨ p₃ ≠ p₂) : Real.tan (∠ p₂ p₃ p₁) * dist p₃ p₂ = dist p₁ p₂ := by
  rw [angle, ← inner_eq_zero_iff_angle_eq_pi_div_two, real_inner_comm, ← neg_eq_zero, ←
    inner_neg_left, neg_vsub_eq_vsub_rev] at h
  rw [ne_comm, ← @vsub_ne_zero V, ← @vsub_eq_zero_iff_eq V, or_comm] at h0
  rw [angle, dist_eq_norm_vsub V p₁ p₂, dist_eq_norm_vsub' V p₃ p₂, ← vsub_add_vsub_cancel p₁ p₂ p₃,
    add_comm, tan_angle_add_mul_norm_of_inner_eq_zero h h0]

/-- A side of a right-angled triangle divided by the cosine of the adjacent angle equals the
hypotenuse. -/
/-
**EuclideanGeometry.dist_div_cos_angle_of_angle_eq_pi_div_two** 是 Mathlib 中的一个定理
，位于命名空间 `EuclideanGeometry`。
形式化陈述：dist_div_cos_angle_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ =
 π / 2) (h0 : p₁ = p₂ ∨ p₃ != p₂) : dist p₃ p₂ / Real.cos (∠ p₂ p₃ p₁) = dist p₁
 p₃
参数：h : ∠ p₁ p₂ p₃ = π / 2；h0 : p₁ = p₂ ∨ p₃ != p₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.angle.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `dist_eq_norm_vsub'`：dist_eq_norm_vsub' (x y : P) : dist x y = ‖y -ᵥ x‖
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_add_vsub_cancel`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₂ + (p₂ -ᵥ p₃) = p₁ -ᵥ p₃
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `InnerProductGeometry.norm_div_cos_angle_add_of_inner_eq_zero`：norm_div_c
os_angle_add_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x != 0 ∨ y = 0) :
 ‖x‖ / Real.cos (angle x (x + y)) = ‖x + y‖
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `inner_neg_left`：inner_neg_left (x y : E) : ⟪-x, y⟫ = -⟪x, y⟫
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `real_inner_comm`：real_inner_comm (x y : F) : ⟪y, x⟫_Real = ⟪x, y⟫_Real
· 使用定理 `InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two`：inner_eq_zer
o_iff_angle_eq_pi_div_two (x y : V) : ⟪x, y⟫ = 0 ↔ angle x y = π / 2
· 使用定理 `or_comm`：∀ {a b : Prop}, a ∨ b ↔ b ∨ a
· 使用定理 `vsub_eq_zero_iff_eq`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] {p₁ p₂ : P}, p₁ -ᵥ p₂ = 0 ↔ p₁ = p₂
· 使用定理 `vsub_ne_zero`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : A
ddTorsor G P] {p q : P}, p -ᵥ q ≠ 0 ↔ p ≠ q
· 使用定理 `ne_comm`：∀ {α : Sort u_1} {a b : α}, a ≠ b ↔ b ≠ a

--- 原说明 ---
A side of a right-angled triangle divided by the cosine of the adjacent angle eq
uals the
hypotenuse.
-/
theorem dist_div_cos_angle_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
    (h0 : p₁ = p₂ ∨ p₃ ≠ p₂) : dist p₃ p₂ / Real.cos (∠ p₂ p₃ p₁) = dist p₁ p₃ := by
  rw [angle, ← inner_eq_zero_iff_angle_eq_pi_div_two, real_inner_comm, ← neg_eq_zero, ←
    inner_neg_left, neg_vsub_eq_vsub_rev] at h
  rw [ne_comm, ← @vsub_ne_zero V, ← @vsub_eq_zero_iff_eq V, or_comm] at h0
  rw [angle, dist_eq_norm_vsub' V p₃ p₂, dist_eq_norm_vsub V p₁ p₃, ← vsub_add_vsub_cancel p₁ p₂ p₃,
    add_comm, norm_div_cos_angle_add_of_inner_eq_zero h h0]

/-- A side of a right-angled triangle divided by the sine of the opposite angle equals the
hypotenuse. -/
/-
**EuclideanGeometry.dist_div_sin_angle_of_angle_eq_pi_div_two** 是 Mathlib 中的一个定理
，位于命名空间 `EuclideanGeometry`。
形式化陈述：dist_div_sin_angle_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ =
 π / 2) (h0 : p₁ != p₂ ∨ p₃ = p₂) : dist p₁ p₂ / Real.sin (∠ p₂ p₃ p₁) = dist p₁
 p₃
参数：h : ∠ p₁ p₂ p₃ = π / 2；h0 : p₁ != p₂ ∨ p₃ = p₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.angle.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_add_vsub_cancel`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₂ + (p₂ -ᵥ p₃) = p₁ -ᵥ p₃
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `InnerProductGeometry.norm_div_sin_angle_add_of_inner_eq_zero`：norm_div_s
in_angle_add_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x = 0 ∨ y != 0) :
 ‖y‖ / Real.sin (angle x (x + y)) = ‖x + y‖
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `inner_neg_left`：inner_neg_left (x y : E) : ⟪-x, y⟫ = -⟪x, y⟫
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `real_inner_comm`：real_inner_comm (x y : F) : ⟪y, x⟫_Real = ⟪x, y⟫_Real
· 使用定理 `InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two`：inner_eq_zer
o_iff_angle_eq_pi_div_two (x y : V) : ⟪x, y⟫ = 0 ↔ angle x y = π / 2
· 使用定理 `or_comm`：∀ {a b : Prop}, a ∨ b ↔ b ∨ a
· 使用定理 `vsub_eq_zero_iff_eq`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] {p₁ p₂ : P}, p₁ -ᵥ p₂ = 0 ↔ p₁ = p₂
· 使用定理 `vsub_ne_zero`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : A
ddTorsor G P] {p q : P}, p -ᵥ q ≠ 0 ↔ p ≠ q
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a

--- 原说明 ---
A side of a right-angled triangle divided by the sine of the opposite angle equa
ls the
hypotenuse.
-/
theorem dist_div_sin_angle_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
    (h0 : p₁ ≠ p₂ ∨ p₃ = p₂) : dist p₁ p₂ / Real.sin (∠ p₂ p₃ p₁) = dist p₁ p₃ := by
  rw [angle, ← inner_eq_zero_iff_angle_eq_pi_div_two, real_inner_comm, ← neg_eq_zero, ←
    inner_neg_left, neg_vsub_eq_vsub_rev] at h
  rw [eq_comm, ← @vsub_ne_zero V, ← @vsub_eq_zero_iff_eq V, or_comm] at h0
  rw [angle, dist_eq_norm_vsub V p₁ p₂, dist_eq_norm_vsub V p₁ p₃, ← vsub_add_vsub_cancel p₁ p₂ p₃,
    add_comm, norm_div_sin_angle_add_of_inner_eq_zero h h0]

/-- A side of a right-angled triangle divided by the tangent of the opposite angle equals the
adjacent side. -/
/-
**EuclideanGeometry.dist_div_tan_angle_of_angle_eq_pi_div_two** 是 Mathlib 中的一个定理
，位于命名空间 `EuclideanGeometry`。
形式化陈述：dist_div_tan_angle_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ =
 π / 2) (h0 : p₁ != p₂ ∨ p₃ = p₂) : dist p₁ p₂ / Real.tan (∠ p₂ p₃ p₁) = dist p₃
 p₂
参数：h : ∠ p₁ p₂ p₃ = π / 2；h0 : p₁ != p₂ ∨ p₃ = p₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.angle.eq_1`：∀ {V : Type u_1} {P : Type u_2} [inst : No
rmedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   
[inst_3 : NormedAd…
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用定理 `dist_eq_norm_vsub'`：dist_eq_norm_vsub' (x y : P) : dist x y = ‖y -ᵥ x‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_add_vsub_cancel`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₂ + (p₂ -ᵥ p₃) = p₁ -ᵥ p₃
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `InnerProductGeometry.norm_div_tan_angle_add_of_inner_eq_zero`：norm_div_t
an_angle_add_of_inner_eq_zero {x y : V} (h : ⟪x, y⟫ = 0) (h0 : x = 0 ∨ y != 0) :
 ‖y‖ / Real.tan (angle x (x + y)) = ‖x‖
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `inner_neg_left`：inner_neg_left (x y : E) : ⟪-x, y⟫ = -⟪x, y⟫
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `real_inner_comm`：real_inner_comm (x y : F) : ⟪y, x⟫_Real = ⟪x, y⟫_Real
· 使用定理 `InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two`：inner_eq_zer
o_iff_angle_eq_pi_div_two (x y : V) : ⟪x, y⟫ = 0 ↔ angle x y = π / 2
· 使用定理 `or_comm`：∀ {a b : Prop}, a ∨ b ↔ b ∨ a
· 使用定理 `vsub_eq_zero_iff_eq`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] {p₁ p₂ : P}, p₁ -ᵥ p₂ = 0 ↔ p₁ = p₂
· 使用定理 `vsub_ne_zero`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : A
ddTorsor G P] {p q : P}, p -ᵥ q ≠ 0 ↔ p ≠ q
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a

--- 原说明 ---
A side of a right-angled triangle divided by the tangent of the opposite angle e
quals the
adjacent side.
-/
theorem dist_div_tan_angle_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = π / 2)
    (h0 : p₁ ≠ p₂ ∨ p₃ = p₂) : dist p₁ p₂ / Real.tan (∠ p₂ p₃ p₁) = dist p₃ p₂ := by
  rw [angle, ← inner_eq_zero_iff_angle_eq_pi_div_two, real_inner_comm, ← neg_eq_zero, ←
    inner_neg_left, neg_vsub_eq_vsub_rev] at h
  rw [eq_comm, ← @vsub_ne_zero V, ← @vsub_eq_zero_iff_eq V, or_comm] at h0
  rw [angle, dist_eq_norm_vsub V p₁ p₂, dist_eq_norm_vsub' V p₃ p₂, ← vsub_add_vsub_cancel p₁ p₂ p₃,
    add_comm, norm_div_tan_angle_add_of_inner_eq_zero h h0]

end EuclideanGeometry

