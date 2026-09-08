/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Geometry.Euclidean.Inversion.Basic

/-!
# Metric on the upper half-plane

In this file we define a `MetricSpace` structure on the `UpperHalfPlane`. We use hyperbolic
(Poincaré) distance given by
`dist z w = 2 * arsinh (dist (z : ℂ) w / (2 * √(z.im * w.im)))` instead of the induced
Euclidean distance because the hyperbolic distance is invariant under holomorphic automorphisms of
the upper half-plane. However, we ensure that the projection to `TopologicalSpace` is
definitionally equal to the induced topological space structure.

We also prove that a metric ball/closed ball/sphere in Poincaré metric is a Euclidean ball/closed
ball/sphere with another center and radius.

-/

@[expose] public section


noncomputable section

open Filter Metric Real Set Topology
open scoped UpperHalfPlane ComplexConjugate NNReal Topology MatrixGroups

variable {z w : ℍ} {r : ℝ}

namespace UpperHalfPlane

/-
**UpperHalfPlane.** 是 Mathlib 中的一个实例，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Dist ℍ :=
  ⟨fun z w => 2 * arsinh (dist (z : ℂ) w / (2 * √(z.im * w.im)))⟩
/-
**UpperHalfPlane.dist_eq** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：dist_eq (z w : ℍ) : dist z w = 2 * arsinh (dist (z : Complex) w / (2 * √(z
.im * w.im)))
参数：z w : ℍ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dist_eq (z w : ℍ) : dist z w = 2 * arsinh (dist (z : ℂ) w / (2 * √(z.im * w.im))) :=
  rfl
/-
**UpperHalfPlane.sinh_half_dist** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：sinh_half_dist (z w : ℍ) : sinh (dist z w / 2) = dist (z : Complex) w / (2
 * √(z.im * w.im))
参数：z w : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UpperHalfPlane.dist_eq`：dist_eq (z w : ℍ) : dist z w = 2 * arsinh (dist 
(z : Complex) w / (2 * √(z.im * w.im)))
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Real.sinh_arsinh`：sinh_arsinh (x : Real) : sinh (arsinh x) = x
-/
theorem sinh_half_dist (z w : ℍ) :
    sinh (dist z w / 2) = dist (z : ℂ) w / (2 * √(z.im * w.im)) := by
  rw [dist_eq, mul_div_cancel_left₀ (arsinh _) two_ne_zero, sinh_arsinh]
/-
**UpperHalfPlane.cosh_half_dist** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：cosh_half_dist (z w : ℍ) : cosh (dist z w / 2) = dist (z : Complex) (conj 
(w : Complex)) / (2 * √(z.im * w.im))
参数：z w : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `sq_eq_sq₀`：sq_eq_sq₀ (ha : 0 <= a) (hb : 0 <= b) : a ^ 2 = b ^ 2 ↔ a = b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.cosh_pos`：cosh_pos (x : Real) : 0 < Real.cosh x
· 使用引理 `Mathlib.Meta.Positivity.div_nonneg_of_nonneg_of_pos`：div_nonneg_of_nonne
g_of_pos [PosMulReflectLT α] (ha : 0 <= a) (hb : 0 < b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Real.sqrt_pos_of_pos`：∀ {x : ℝ}, 0 < x → 0 < √x
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
· 使用定理 `Real.cosh_sq'`：cosh_sq' : cosh x ^ 2 = 1 + sinh x ^ 2
· 使用定理 `UpperHalfPlane.sinh_half_dist`：sinh_half_dist (z w : ℍ) : sinh (dist z w
 / 2) = dist (z : Complex) w / (2 * √(z.im * w.im))
· 使用引理 `div_pow`：div_pow (a b : α) (n : Nat) : (a / b) ^ n = a ^ n / b ^ n
· 使用定理 `one_add_div`：one_add_div (h : b != 0) : 1 + a / b = (b + a) / b
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `Real.sq_sqrt`：sq_sqrt (h : 0 <= x) : √x ^ 2 = x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
（共 78 条，此处仅展示前 30 条）
-/
theorem cosh_half_dist (z w : ℍ) :
    cosh (dist z w / 2) = dist (z : ℂ) (conj (w : ℂ)) / (2 * √(z.im * w.im)) := by
  rw [← sq_eq_sq₀, cosh_sq', sinh_half_dist, div_pow, div_pow, one_add_div, mul_pow, sq_sqrt]
  · congr 1
    simp only [Complex.dist_eq, Complex.sq_norm, Complex.normSq_sub, Complex.normSq_conj,
      Complex.conj_conj, Complex.mul_re, Complex.conj_re, Complex.conj_im, coe_im]
    ring
  all_goals positivity
/-
**UpperHalfPlane.tanh_half_dist** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：tanh_half_dist (z w : ℍ) : tanh (dist z w / 2) = dist (z : Complex) w / di
st (z : Complex) (conj ↑w)
参数：z w : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.tanh_eq_sinh_div_cosh`：∀ (x : ℝ), Real.tanh x = Real.sinh x / Real.
cosh x
· 使用定理 `UpperHalfPlane.sinh_half_dist`：sinh_half_dist (z w : ℍ) : sinh (dist z w
 / 2) = dist (z : Complex) w / (2 * √(z.im * w.im))
· 使用定理 `UpperHalfPlane.cosh_half_dist`：cosh_half_dist (z w : ℍ) : cosh (dist z w
 / 2) = dist (z : Complex) (conj (w : Complex)) / (2 * √(z.im * w.im))
· 使用定理 `div_div_div_comm`：div_div_div_comm : a / b / (c / d) = a / c / (b / d)
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
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
· 使用定理 `Real.sqrt_pos_of_pos`：∀ {x : ℝ}, 0 < x → 0 < √x
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
-/
theorem tanh_half_dist (z w : ℍ) :
    tanh (dist z w / 2) = dist (z : ℂ) w / dist (z : ℂ) (conj ↑w) := by
  rw [tanh_eq_sinh_div_cosh, sinh_half_dist, cosh_half_dist, div_div_div_comm, div_self, div_one]
  positivity
/-
**UpperHalfPlane.exp_half_dist** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：exp_half_dist (z w : ℍ) : exp (dist z w / 2) = (dist (z : Complex) w + dis
t (z : Complex) (conj ↑w)) / (2 * √(z.im * w.im))
参数：z w : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.sinh_add_cosh`：sinh_add_cosh : sinh x + cosh x = exp x
· 使用定理 `UpperHalfPlane.sinh_half_dist`：sinh_half_dist (z w : ℍ) : sinh (dist z w
 / 2) = dist (z : Complex) w / (2 * √(z.im * w.im))
· 使用定理 `UpperHalfPlane.cosh_half_dist`：cosh_half_dist (z w : ℍ) : cosh (dist z w
 / 2) = dist (z : Complex) (conj (w : Complex)) / (2 * √(z.im * w.im))
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
-/
theorem exp_half_dist (z w : ℍ) :
    exp (dist z w / 2) = (dist (z : ℂ) w + dist (z : ℂ) (conj ↑w)) / (2 * √(z.im * w.im)) := by
  rw [← sinh_add_cosh, sinh_half_dist, cosh_half_dist, add_div]
/-
**UpperHalfPlane.cosh_dist** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：cosh_dist (z w : ℍ) : cosh (dist z w) = 1 + dist (z : Complex) w ^ 2 / (2 
* z.im * w.im)
参数：z w : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UpperHalfPlane.dist_eq`：dist_eq (z w : ℍ) : dist z w = 2 * arsinh (dist 
(z : Complex) w / (2 * √(z.im * w.im)))
· 使用定理 `Real.cosh_two_mul`：∀ (x : ℝ), Real.cosh (2 * x) = Real.cosh x ^ 2 + Real
.sinh x ^ 2
· 使用定理 `Real.cosh_sq'`：cosh_sq' : cosh x ^ 2 = 1 + sinh x ^ 2
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `Real.sinh_arsinh`：sinh_arsinh (x : Real) : sinh (arsinh x) = x
· 使用引理 `div_pow`：div_pow (a b : α) (n : Nat) : (a / b) ^ n = a ^ n / b ^ n
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `Real.sq_sqrt`：sq_sqrt (h : 0 <= x) : √x ^ 2 = x
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用引理 `mul_div_mul_left`：mul_div_mul_left (a b : G₀) (hc : c != 0) : c * a / (c
 * b) = a / b
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
-/
theorem cosh_dist (z w : ℍ) : cosh (dist z w) = 1 + dist (z : ℂ) w ^ 2 / (2 * z.im * w.im) := by
  rw [dist_eq, cosh_two_mul, cosh_sq', add_assoc, ← two_mul, sinh_arsinh, div_pow, mul_pow,
    sq_sqrt, sq (2 : ℝ), mul_assoc, ← mul_div_assoc, mul_assoc, mul_div_mul_left] <;> positivity
/-
**UpperHalfPlane.sinh_half_dist_add_dist** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPla
ne`。
形式化陈述：sinh_half_dist_add_dist (a b c : ℍ) : sinh ((dist a b + dist b c) / 2) = (
dist (a : Complex) b * dist (c : Complex) (conj ↑b) + dist (b : Complex) c * dis
t (a : Complex) (conj ↑b)) / (2 * √(a.im * c.im) * dist (b : Complex) (conj ↑b))
参数：a b c : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
· 使用定理 `Real.sinh_add`：∀ (x y : ℝ), Real.sinh (x + y) = Real.sinh x * Real.cosh 
y + Real.cosh x * Real.sinh y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `UpperHalfPlane.sinh_half_dist`：sinh_half_dist (z w : ℍ) : sinh (dist z w
 / 2) = dist (z : Complex) w / (2 * √(z.im * w.im))
· 使用定理 `UpperHalfPlane.cosh_half_dist`：cosh_half_dist (z w : ℍ) : cosh (dist z w
 / 2) = dist (z : Complex) (conj (w : Complex)) / (2 * √(z.im * w.im))
· 使用定理 `div_mul_div_comm`：div_mul_div_comm : a / b * (c / d) = a * c / (b * d)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.dist_self_conj`：dist_self_conj (z : Complex) : dist z (conj z) =
 2 * |z.im|
· 使用定理 `UpperHalfPlane.coe_im`：coe_im (z : ℍ) : (z : Complex).im = z.im
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `Complex.dist_conj_comm`：∀ (z w : ℂ), dist ((starRingEnd ℂ) z) w = dist z
 ((starRingEnd ℂ) w)
· 使用定理 `mul_mul_mul_comm`：mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a *
 c * (b * d)
· 使用定理 `Real.sqrt_mul`：sqrt_mul {x : Real} (hx : 0 <= x) (y : Real) : √(x * y) =
 √x * √y
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.mul_self_sqrt`：mul_self_sqrt (h : 0 <= x) : √x * √x = x
-/
theorem sinh_half_dist_add_dist (a b c : ℍ) : sinh ((dist a b + dist b c) / 2) =
    (dist (a : ℂ) b * dist (c : ℂ) (conj ↑b) + dist (b : ℂ) c * dist (a : ℂ) (conj ↑b)) /
      (2 * √(a.im * c.im) * dist (b : ℂ) (conj ↑b)) := by
  simp only [add_div _ _ (2 : ℝ), sinh_add, sinh_half_dist, cosh_half_dist, div_mul_div_comm]
  rw [← add_div, Complex.dist_self_conj, coe_im, abs_of_pos b.im_pos, mul_comm (dist (b : ℂ) _),
    dist_comm (b : ℂ), Complex.dist_conj_comm, mul_mul_mul_comm, mul_mul_mul_comm _ _ _ b.im]
  congr 2
  rw [sqrt_mul, sqrt_mul, sqrt_mul, mul_comm (√a.im), mul_mul_mul_comm, mul_self_sqrt,
      mul_comm] <;> exact (im_pos _).le
/-
**UpperHalfPlane.dist_comm** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：∀ (z w : UpperHalfPlane), dist z w = dist w z
参数：z w : UpperHalfPlane。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem dist_comm (z w : ℍ) : dist z w = dist w z := by
  simp only [dist_eq, dist_comm (z : ℂ), mul_comm]
/-
**UpperHalfPlane.dist_le_iff_le_sinh** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：dist_le_iff_le_sinh : dist z w <= r ↔ dist (z : Complex) w / (2 * √(z.im *
 w.im)) <= sinh (r / 2)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `div_le_div_iff_of_pos_right`：div_le_div_iff_of_pos_right (hc : 0 < c) : 
a / c <= b / c ↔ a <= b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用引理 `zero_lt_two'`：zero_lt_two' : (0 : α) < 2
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Real.sinh_le_sinh`：sinh_le_sinh : sinh x <= sinh y ↔ x <= y
· 使用定理 `UpperHalfPlane.sinh_half_dist`：sinh_half_dist (z w : ℍ) : sinh (dist z w
 / 2) = dist (z : Complex) w / (2 * √(z.im * w.im))
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem dist_le_iff_le_sinh :
    dist z w ≤ r ↔ dist (z : ℂ) w / (2 * √(z.im * w.im)) ≤ sinh (r / 2) := by
  rw [← div_le_div_iff_of_pos_right (zero_lt_two' ℝ), ← sinh_le_sinh, sinh_half_dist]
/-
**UpperHalfPlane.dist_eq_iff_eq_sinh** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：dist_eq_iff_eq_sinh : dist z w = r ↔ dist (z : Complex) w / (2 * √(z.im * 
w.im)) = sinh (r / 2)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `div_left_inj'`：div_left_inj' (hc : c != 0) : a / c = b / c ↔ a = b
· 使用引理 `two_ne_zero'`：two_ne_zero' [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Real.sinh_inj`：sinh_inj : sinh x = sinh y ↔ x = y
· 使用定理 `UpperHalfPlane.sinh_half_dist`：sinh_half_dist (z w : ℍ) : sinh (dist z w
 / 2) = dist (z : Complex) w / (2 * √(z.im * w.im))
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem dist_eq_iff_eq_sinh :
    dist z w = r ↔ dist (z : ℂ) w / (2 * √(z.im * w.im)) = sinh (r / 2) := by
  rw [← div_left_inj' (two_ne_zero' ℝ), ← sinh_inj, sinh_half_dist]
/-
**UpperHalfPlane.dist_eq_iff_eq_sq_sinh** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlan
e`。
形式化陈述：dist_eq_iff_eq_sq_sinh (hr : 0 <= r) : dist z w = r ↔ dist (z : Complex) w
 ^ 2 / (4 * z.im * w.im) = sinh (r / 2) ^ 2
参数：hr : 0 <= r。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UpperHalfPlane.dist_eq_iff_eq_sinh`：dist_eq_iff_eq_sinh : dist z w = r ↔
 dist (z : Complex) w / (2 * √(z.im * w.im)) = sinh (r / 2)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `sq_eq_sq₀`：sq_eq_sq₀ (ha : 0 <= a) (hb : 0 <= b) : a ^ 2 = b ^ 2 ↔ a = b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用引理 `Mathlib.Meta.Positivity.div_nonneg_of_nonneg_of_pos`：div_nonneg_of_nonne
g_of_pos [PosMulReflectLT α] (ha : 0 <= a) (hb : 0 < b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Real.sqrt_pos_of_pos`：∀ {x : ℝ}, 0 < x → 0 < √x
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
· 使用定理 `Mathlib.Meta.Positivity.sinh_nonneg_of_nonneg`：∀ {x : ℝ}, 0 ≤ x → 0 ≤ Re
al.sinh x
· 使用引理 `div_pow`：div_pow (a b : α) (n : Nat) : (a / b) ^ n = a ^ n / b ^ n
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `Real.sq_sqrt`：sq_sqrt (h : 0 <= x) : √x ^ 2 = x
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_eq`：∀ {α : Type u} [inst : AddMonoidWithOn
e α] {n : ℕ} {a a' : α}, Mathlib.Meta.NormNum.IsNat a n → ↑n = a' → a = a'
· 使用定理 `Mathlib.Meta.NormNum.isNat_pow`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → ℕ → α} {a : α} {b a' b' c : ℕ},   f = HPow.hPow →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNatPowT.run`：∀ {a b c : ℕ}, Mathlib.Meta.NormNum.
IsNatPowT (a.pow 1 = a) a b c → a.pow b = c
（共 33 条，此处仅展示前 30 条）
-/
theorem dist_eq_iff_eq_sq_sinh (hr : 0 ≤ r) :
    dist z w = r ↔ dist (z : ℂ) w ^ 2 / (4 * z.im * w.im) = sinh (r / 2) ^ 2 := by
  rw [dist_eq_iff_eq_sinh, ← sq_eq_sq₀, div_pow, mul_pow, sq_sqrt, mul_assoc]
  · norm_num
  all_goals positivity
/-
**UpperHalfPlane.dist_triangle** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：∀ (a b c : UpperHalfPlane), dist a c ≤ dist a b + dist b c
参数：a b c : UpperHalfPlane。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UpperHalfPlane.dist_le_iff_le_sinh`：dist_le_iff_le_sinh : dist z w <= r 
↔ dist (z : Complex) w / (2 * √(z.im * w.im)) <= sinh (r / 2)
· 使用定理 `UpperHalfPlane.sinh_half_dist_add_dist`：sinh_half_dist_add_dist (a b c :
 ℍ) : sinh ((dist a b + dist b c) / 2) = (dist (a : Complex) b * dist (c : Compl
ex) (conj ↑b) + dist (b : Co…
· 使用定理 `div_mul_eq_div_div`：div_mul_eq_div_div : a / (b * c) = a / b / c
· 使用引理 `le_div_iff₀`：le_div_iff₀ (hc : 0 < c) : a <= b / c ↔ a * c <= b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `dist_pos`：dist_pos {x y : γ} : 0 < dist x y ↔ x != y
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Complex.conj_eq_iff_im`：conj_eq_iff_im {z : Complex} : conj z = z ↔ z.im
 = 0
· 使用定理 `UpperHalfPlane.im_ne_zero`：im_ne_zero (z : ℍ) : z.im != 0
· 使用定理 `div_mul_eq_mul_div`：div_mul_eq_mul_div : a / b * c = a * c / b
· 使用引理 `div_le_div_of_nonneg_right`：div_le_div_of_nonneg_right (hab : a <= b) (h
c : 0 <= c) : a / c <= b / c
· 使用定理 `EuclideanGeometry.mul_dist_le_mul_dist_add_mul_dist`：mul_dist_le_mul_dis
t_add_mul_dist (a b c d : P) : dist a c * dist b d <= dist a b * dist c d + dist
 b c * dist a d
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
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
· 使用定理 `Real.sqrt_pos_of_pos`：∀ {x : ℝ}, 0 < x → 0 < √x
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
-/
protected theorem dist_triangle (a b c : ℍ) : dist a c ≤ dist a b + dist b c := by
  rw [dist_le_iff_le_sinh, sinh_half_dist_add_dist, div_mul_eq_div_div _ _ (dist _ _), le_div_iff₀,
    div_mul_eq_mul_div]
  · gcongr
    exact EuclideanGeometry.mul_dist_le_mul_dist_add_mul_dist (a : ℂ) b c (conj (b : ℂ))
  · rw [dist_comm, dist_pos, Ne, Complex.conj_eq_iff_im]
    exact b.im_ne_zero
/-
**UpperHalfPlane.dist_le_dist_coe_div_sqrt** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfP
lane`。
形式化陈述：dist_le_dist_coe_div_sqrt (z w : ℍ) : dist z w <= dist (z : Complex) w / √
(z.im * w.im)
参数：z w : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UpperHalfPlane.dist_le_iff_le_sinh`：dist_le_iff_le_sinh : dist z w <= r 
↔ dist (z : Complex) w / (2 * √(z.im * w.im)) <= sinh (r / 2)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_mul_eq_div_div_swap`：div_mul_eq_div_div_swap : a / (b * c) = a / c /
 b
· 使用定理 `Real.self_le_sinh_iff`：self_le_sinh_iff : x <= sinh x ↔ 0 <= x
· 使用引理 `Mathlib.Meta.Positivity.div_nonneg_of_nonneg_of_pos`：div_nonneg_of_nonne
g_of_pos [PosMulReflectLT α] (ha : 0 <= a) (hb : 0 < b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Real.sqrt_pos_of_pos`：∀ {x : ℝ}, 0 < x → 0 < √x
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
-/
theorem dist_le_dist_coe_div_sqrt (z w : ℍ) : dist z w ≤ dist (z : ℂ) w / √(z.im * w.im) := by
  rw [dist_le_iff_le_sinh, ← div_mul_eq_div_div_swap, self_le_sinh_iff]
  positivity

/-- An auxiliary `MetricSpace` instance on the upper half-plane. This instance has bad projection
to `TopologicalSpace`. We replace it later. -/
@[instance_reducible]
/-
**UpperHalfPlane.metricSpaceAux** 是 Mathlib 中的一个定义，位于命名空间 `UpperHalfPlane`。
形式化陈述：metricSpaceAux : MetricSpace ℍ where dist
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `UpperHalfPlane.dist_comm`：∀ (z w : UpperHalfPlane), dist z w = dist w z
· 使用定理 `UpperHalfPlane.dist_triangle`：∀ (a b c : UpperHalfPlane), dist a c ≤ dis
t a b + dist b c

--- 原说明 ---
An auxiliary `MetricSpace` instance on the upper half-plane. This instance has b
ad projection
to `TopologicalSpace`. We replace it later.
-/
def metricSpaceAux : MetricSpace ℍ where
  dist := dist
  dist_self z := by rw [dist_eq, dist_self, zero_div, arsinh_zero, mul_zero]
  dist_comm := UpperHalfPlane.dist_comm
  dist_triangle := UpperHalfPlane.dist_triangle
  eq_of_dist_eq_zero {z w} h := by
    simpa [dist_eq, Real.sqrt_eq_zero', (mul_pos z.im_pos w.im_pos).not_ge, Set.ext_iff] using h

open Complex
/-
**UpperHalfPlane.cosh_dist'** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：cosh_dist' (z w : ℍ) : Real.cosh (dist z w) = ((z.re - w.re) ^ 2 + z.im ^ 
2 + w.im ^ 2) / (2 * z.im * w.im)
参数：z w : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UpperHalfPlane.cosh_dist`：cosh_dist (z w : ℍ) : cosh (dist z w) = 1 + di
st (z : Complex) w ^ 2 / (2 * z.im * w.im)
· 使用定理 `Complex.dist_eq`：dist_eq (z w : Complex) : dist z w = ‖z - w‖
· 使用定理 `Complex.sq_norm`：∀ (z : ℂ), ‖z‖ ^ 2 = Complex.normSq z
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
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_add`：subst_add {M : Type*} [Semiring M] {
x₁ x₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ + X₂ =
 Y) (hy : a * Y = y) : x…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.one_eq_eval`：one_eq_eval [GroupWithZero M] :
 (1:M) = NF.eval (M
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval_cons_neg`：eval_cons_mul_e
val_cons_neg [CommGroupWithZero M] (n : Int) {e : M} (he : e != 0) {L l l' : NF 
M} (h : L.eval * l.eval = l'.eval) : ((n, e) …
· 使用定理 `Mathlib.Meta.NormNum.isNat_eq_false`：∀ {α : Type u_1} [inst : AddMonoidW
ithOne α] [CharZero α] {a b : α} {a' b' : ℕ},   Mathlib.Meta.NormNum.IsNat a a' 
→ Mathlib.Meta.NormNum.Is…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
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
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
（共 97 条，此处仅展示前 30 条）
-/
theorem cosh_dist' (z w : ℍ) :
    Real.cosh (dist z w) = ((z.re - w.re) ^ 2 + z.im ^ 2 + w.im ^ 2) / (2 * z.im * w.im) := by
  simp [field, cosh_dist, Complex.dist_eq, Complex.sq_norm, normSq_apply]
  ring

/-- Euclidean center of the circle with center `z` and radius `r` in the hyperbolic metric. -/
/-
**UpperHalfPlane.center** 是 Mathlib 中的一个定义，位于命名空间 `UpperHalfPlane`。
形式化陈述：center (z : ℍ) (r : Real) : ℍ
参数：z : ℍ；r : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Euclidean center of the circle with center `z` and radius `r` in the hyperbolic 
metric.
-/
def center (z : ℍ) (r : ℝ) : ℍ :=
  ⟨⟨z.re, z.im * Real.cosh r⟩, by positivity⟩

@[simp]
/-
**UpperHalfPlane.center_re** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：center_re (z r) : (center z r).re = z.re
参数：z r。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem center_re (z r) : (center z r).re = z.re :=
  rfl

@[simp]
/-
**UpperHalfPlane.center_im** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：center_im (z r) : (center z r).im = z.im * Real.cosh r
参数：z r。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem center_im (z r) : (center z r).im = z.im * Real.cosh r :=
  rfl

@[simp]
/-
**UpperHalfPlane.center_zero** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：center_zero (z : ℍ) : center z 0 = z
参数：z : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperHalfPlane.ext_re_im`：ext_re_im {a b : ℍ} (hre : a.re = b.re) (him :
 a.im = b.im) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.cosh_zero`：cosh_zero : cosh 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem center_zero (z : ℍ) : center z 0 = z := by
  apply ext_re_im <;> simp
/-
**UpperHalfPlane.dist_coe_center_sq** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：dist_coe_center_sq (z w : ℍ) (r : Real) : dist (z : Complex) (w.center r) 
^ 2 = 2 * z.im * w.im * (Real.cosh (dist z w) - Real.cosh r) + (w.im * Real.sinh
 r) ^ 2
参数：z w : ℍ；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
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
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.dist_eq`：dist_eq (z w : Complex) : dist z w = ‖z - w‖
· 使用定理 `Complex.sq_norm`：∀ (z : ℂ), ‖z‖ ^ 2 = Complex.normSq z
· 使用引理 `sub_sq`：sub_sq (a b : R) : (a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `Real.cosh_sq`：∀ (x : ℝ), Real.cosh x ^ 2 = Real.sinh x ^ 2 + 1
· 使用定理 `UpperHalfPlane.cosh_dist'`：cosh_dist' (z w : ℍ) : Real.cosh (dist z w) =
 ((z.re - w.re) ^ 2 + z.im ^ 2 + w.im ^ 2) / (2 * z.im * w.im)
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用引理 `mul_div_cancel₀`：mul_div_cancel₀ (a : G₀) (hb : b != 0) : b * (a / b) = 
a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
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
（共 68 条，此处仅展示前 30 条）
-/
theorem dist_coe_center_sq (z w : ℍ) (r : ℝ) : dist (z : ℂ) (w.center r) ^ 2 =
    2 * z.im * w.im * (Real.cosh (dist z w) - Real.cosh r) + (w.im * Real.sinh r) ^ 2 := by
  have H : 2 * z.im * w.im ≠ 0 := by positivity
  simp only [Complex.dist_eq, Complex.sq_norm, normSq_apply, coe_re, coe_im, center_re, center_im,
    cosh_dist', mul_div_cancel₀ _ H, sub_sq z.im, mul_pow, Real.cosh_sq, sub_re, sub_im, mul_sub, ←
    sq]
  ring
/-
**UpperHalfPlane.dist_coe_center** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：dist_coe_center (z w : ℍ) (r : Real) : dist (z : Complex) (w.center r) = √
(2 * z.im * w.im * (Real.cosh (dist z w) - Real.cosh r) + (w.im * Real.sinh r) ^
 2)
参数：z w : ℍ；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.sqrt_sq`：sqrt_sq (h : 0 <= x) : √(x ^ 2) = x
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `UpperHalfPlane.dist_coe_center_sq`：dist_coe_center_sq (z w : ℍ) (r : Rea
l) : dist (z : Complex) (w.center r) ^ 2 = 2 * z.im * w.im * (Real.cosh (dist z 
w) - Real.cosh r) + (w.…
-/
theorem dist_coe_center (z w : ℍ) (r : ℝ) : dist (z : ℂ) (w.center r) =
    √(2 * z.im * w.im * (Real.cosh (dist z w) - Real.cosh r) + (w.im * Real.sinh r) ^ 2) := by
  rw [← sqrt_sq dist_nonneg, dist_coe_center_sq]
/-
**UpperHalfPlane.cmp_dist_eq_cmp_dist_coe_center** 是 Mathlib 中的一个定理，位于命名空间 `Uppe
rHalfPlane`。
形式化陈述：cmp_dist_eq_cmp_dist_coe_center (z w : ℍ) (r : Real) : cmp (dist z w) r = 
cmp (dist (z : Complex) (w.center r)) (w.im * Real.sinh r)
参数：z w : ℍ；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `LT.lt.cmp_eq_gt`：LT.lt.cmp_eq_gt (h : x < y) : cmp y x = Ordering.gt
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_neg_of_pos_of_neg`：mul_neg_of_pos_of_neg [PosMulStrictMono α] (ha : 
0 < a) (hb : b < 0) : a * b < 0
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.sinh_neg_iff`：sinh_neg_iff : sinh x < 0 ↔ x < 0
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Mathlib.Meta.Positivity.sinh_nonneg_of_nonneg`：∀ {x : ℝ}, 0 ≤ x → 0 ≤ Re
al.sinh x
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StrictMonoOn.cmp_map_eq`：StrictMonoOn.cmp_map_eq (hf : StrictMonoOn f s)
 (hx : x in s) (hy : y in s) : cmp (f x) (f y) = cmp x y
· 使用定理 `Real.cosh_strictMonoOn`：cosh_strictMonoOn : StrictMonoOn cosh (Ici 0)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `pow_left_strictMonoOn₀`：pow_left_strictMonoOn₀ [MulPosMono M₀] (hn : n !
= 0) : StrictMonoOn (· ^ n : M₀ -> M₀) {a | 0 <= a}
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `cmp.congr_simp`：∀ {α : Type u} [inst : LT α] {inst_1 : DecidableLT α} [i
nst_2 : DecidableLT α] (a a_1 : α),   a = a_1 → ∀ (b b_1 : α), b = b_1 → cmp a b
 = c…
· 使用定理 `UpperHalfPlane.dist_coe_center_sq`：dist_coe_center_sq (z w : ℍ) (r : Rea
l) : dist (z : Complex) (w.center r) ^ 2 = 2 * z.im * w.im * (Real.cosh (dist z 
w) - Real.cosh r) + (w.…
（共 42 条，此处仅展示前 30 条）
-/
theorem cmp_dist_eq_cmp_dist_coe_center (z w : ℍ) (r : ℝ) :
    cmp (dist z w) r = cmp (dist (z : ℂ) (w.center r)) (w.im * Real.sinh r) := by
  let := metricSpaceAux
  rcases lt_or_ge r 0 with hr₀ | hr₀
  · trans Ordering.gt
    exacts [(hr₀.trans_le dist_nonneg).cmp_eq_gt,
      ((mul_neg_of_pos_of_neg w.im_pos (sinh_neg_iff.2 hr₀)).trans_le dist_nonneg).cmp_eq_gt.symm]
  have hr₀' : 0 ≤ w.im * Real.sinh r := by positivity
  have hzw₀ : 0 < 2 * z.im * w.im := by positivity
  simp only [← cosh_strictMonoOn.cmp_map_eq dist_nonneg hr₀,
    ← (pow_left_strictMonoOn₀ (M₀ := ℝ) two_ne_zero).cmp_map_eq dist_nonneg hr₀',
    dist_coe_center_sq]
  rw [← cmp_mul_pos_left hzw₀, ← cmp_sub_zero, ← mul_sub, ← cmp_add_right, zero_add]
/-
**UpperHalfPlane.dist_eq_iff_dist_coe_center_eq** 是 Mathlib 中的一个定理，位于命名空间 `Upper
HalfPlane`。
形式化陈述：dist_eq_iff_dist_coe_center_eq : dist z w = r ↔ dist (z : Complex) (w.cent
er r) = w.im * Real.sinh r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_iff_eq_of_cmp_eq_cmp`：eq_iff_eq_of_cmp_eq_cmp (h : cmp x y = cmp x' y
') : x = y ↔ x' = y'
· 使用定理 `UpperHalfPlane.cmp_dist_eq_cmp_dist_coe_center`：cmp_dist_eq_cmp_dist_coe
_center (z w : ℍ) (r : Real) : cmp (dist z w) r = cmp (dist (z : Complex) (w.cen
ter r)) (w.im * Real.sinh r)
-/
theorem dist_eq_iff_dist_coe_center_eq :
    dist z w = r ↔ dist (z : ℂ) (w.center r) = w.im * Real.sinh r :=
  eq_iff_eq_of_cmp_eq_cmp (cmp_dist_eq_cmp_dist_coe_center z w r)

@[simp]
/-
**UpperHalfPlane.dist_self_center** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：dist_self_center (z : ℍ) (r : Real) : dist (z : Complex) (z.center r) = z.
im * (Real.cosh r - 1)
参数：z : ℍ；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.dist_of_re_eq`：dist_of_re_eq {z w : Complex} (h : z.re = w.re) :
 dist z w = dist z.im w.im
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `UpperHalfPlane.center_re`：center_re (z r) : (center z r).re = z.re
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `Real.dist_eq`：Real.dist_eq (x y : Real) : dist x y = |x - y|
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_mul_of_one_le_right`：le_mul_of_one_le_right [PosMulMono α] (ha : 0 <=
 a) (h : 1 <= b) : a <= a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
· 使用定理 `Real.one_le_cosh`：one_le_cosh (x : Real) : 1 <= cosh x
-/
theorem dist_self_center (z : ℍ) (r : ℝ) :
    dist (z : ℂ) (z.center r) = z.im * (Real.cosh r - 1) := by
  rw [dist_of_re_eq (z.center_re r).symm, dist_comm, Real.dist_eq, mul_sub, mul_one]
  exact abs_of_nonneg (sub_nonneg.2 <| le_mul_of_one_le_right z.im_pos.le (one_le_cosh _))

@[simp]
/-
**UpperHalfPlane.dist_center_dist** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：dist_center_dist (z w : ℍ) : dist (z : Complex) (w.center (dist z w)) = w.
im * Real.sinh (dist z w)
参数：z w : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `UpperHalfPlane.dist_eq_iff_dist_coe_center_eq`：dist_eq_iff_dist_coe_cent
er_eq : dist z w = r ↔ dist (z : Complex) (w.center r) = w.im * Real.sinh r
-/
theorem dist_center_dist (z w : ℍ) :
    dist (z : ℂ) (w.center (dist z w)) = w.im * Real.sinh (dist z w) :=
  dist_eq_iff_dist_coe_center_eq.1 rfl
/-
**UpperHalfPlane.dist_lt_iff_dist_coe_center_lt** 是 Mathlib 中的一个定理，位于命名空间 `Upper
HalfPlane`。
形式化陈述：dist_lt_iff_dist_coe_center_lt : dist z w < r ↔ dist (z : Complex) (w.cent
er r) < w.im * Real.sinh r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_iff_lt_of_cmp_eq_cmp`：lt_iff_lt_of_cmp_eq_cmp (h : cmp x y = cmp x' y
') : x < y ↔ x' < y'
· 使用定理 `UpperHalfPlane.cmp_dist_eq_cmp_dist_coe_center`：cmp_dist_eq_cmp_dist_coe
_center (z w : ℍ) (r : Real) : cmp (dist z w) r = cmp (dist (z : Complex) (w.cen
ter r)) (w.im * Real.sinh r)
-/
theorem dist_lt_iff_dist_coe_center_lt :
    dist z w < r ↔ dist (z : ℂ) (w.center r) < w.im * Real.sinh r :=
  lt_iff_lt_of_cmp_eq_cmp (cmp_dist_eq_cmp_dist_coe_center z w r)
/-
**UpperHalfPlane.lt_dist_iff_lt_dist_coe_center** 是 Mathlib 中的一个定理，位于命名空间 `Upper
HalfPlane`。
形式化陈述：lt_dist_iff_lt_dist_coe_center : r < dist z w ↔ w.im * Real.sinh r < dist 
(z : Complex) (w.center r)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_iff_lt_of_cmp_eq_cmp`：lt_iff_lt_of_cmp_eq_cmp (h : cmp x y = cmp x' y
') : x < y ↔ x' < y'
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `cmp_eq_cmp_symm`：cmp_eq_cmp_symm : cmp x y = cmp x' y' ↔ cmp y x = cmp y
' x'
· 使用定理 `UpperHalfPlane.cmp_dist_eq_cmp_dist_coe_center`：cmp_dist_eq_cmp_dist_coe
_center (z w : ℍ) (r : Real) : cmp (dist z w) r = cmp (dist (z : Complex) (w.cen
ter r)) (w.im * Real.sinh r)
-/
theorem lt_dist_iff_lt_dist_coe_center :
    r < dist z w ↔ w.im * Real.sinh r < dist (z : ℂ) (w.center r) :=
  lt_iff_lt_of_cmp_eq_cmp (cmp_eq_cmp_symm.1 <| cmp_dist_eq_cmp_dist_coe_center z w r)
/-
**UpperHalfPlane.dist_le_iff_dist_coe_center_le** 是 Mathlib 中的一个定理，位于命名空间 `Upper
HalfPlane`。
形式化陈述：dist_le_iff_dist_coe_center_le : dist z w <= r ↔ dist (z : Complex) (w.cen
ter r) <= w.im * Real.sinh r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iff_le_of_cmp_eq_cmp`：le_iff_le_of_cmp_eq_cmp (h : cmp x y = cmp x' y
') : x <= y ↔ x' <= y'
· 使用定理 `UpperHalfPlane.cmp_dist_eq_cmp_dist_coe_center`：cmp_dist_eq_cmp_dist_coe
_center (z w : ℍ) (r : Real) : cmp (dist z w) r = cmp (dist (z : Complex) (w.cen
ter r)) (w.im * Real.sinh r)
-/
theorem dist_le_iff_dist_coe_center_le :
    dist z w ≤ r ↔ dist (z : ℂ) (w.center r) ≤ w.im * Real.sinh r :=
  le_iff_le_of_cmp_eq_cmp (cmp_dist_eq_cmp_dist_coe_center z w r)
/-
**UpperHalfPlane.le_dist_iff_le_dist_coe_center** 是 Mathlib 中的一个定理，位于命名空间 `Upper
HalfPlane`。
形式化陈述：le_dist_iff_le_dist_coe_center : r < dist z w ↔ w.im * Real.sinh r < dist 
(z : Complex) (w.center r)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_iff_lt_of_cmp_eq_cmp`：lt_iff_lt_of_cmp_eq_cmp (h : cmp x y = cmp x' y
') : x < y ↔ x' < y'
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `cmp_eq_cmp_symm`：cmp_eq_cmp_symm : cmp x y = cmp x' y' ↔ cmp y x = cmp y
' x'
· 使用定理 `UpperHalfPlane.cmp_dist_eq_cmp_dist_coe_center`：cmp_dist_eq_cmp_dist_coe
_center (z w : ℍ) (r : Real) : cmp (dist z w) r = cmp (dist (z : Complex) (w.cen
ter r)) (w.im * Real.sinh r)
-/
theorem le_dist_iff_le_dist_coe_center :
    r < dist z w ↔ w.im * Real.sinh r < dist (z : ℂ) (w.center r) :=
  lt_iff_lt_of_cmp_eq_cmp (cmp_eq_cmp_symm.1 <| cmp_dist_eq_cmp_dist_coe_center z w r)

/-- For two points on the same vertical line, the distance is equal to the distance between the
logarithms of their imaginary parts. -/
nonrec theorem dist_of_re_eq (h : z.re = w.re) : dist z w = dist (log z.im) (log w.im) := by
  have h₀ : 0 < z.im / w.im := by positivity
  rw [dist_eq_iff_dist_coe_center_eq, Real.dist_eq, ← abs_sinh, ← log_div z.im_ne_zero w.im_ne_zero,
    sinh_log h₀, dist_of_re_eq, coe_im, coe_im, center_im, cosh_abs, cosh_log h₀, inv_div] <;>
  [skip; exact h]
  nth_rw 4 [← abs_of_pos w.im_pos]
  simp only [← _root_.abs_mul, Real.dist_eq]
  congr 1
  field

/-- Hyperbolic distance between two points is greater than or equal to the distance between the
logarithms of their imaginary parts. -/
/-
**UpperHalfPlane.dist_log_im_le** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：dist_log_im_le (z w : ℍ) : dist (log z.im) (log w.im) <= dist z w
参数：z w : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `UpperHalfPlane.dist_of_re_eq`：∀ {z w : UpperHalfPlane}, z.re = w.re → di
st z w = dist (Real.log z.im) (Real.log w.im)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Real.arsinh_le_arsinh._gcongr_1`：∀ {x y : ℝ}, x ≤ y → Real.arsinh x ≤ Re
al.arsinh y
· 使用引理 `div_le_div_of_nonneg_right`：div_le_div_of_nonneg_right (hab : a <= b) (h
c : 0 <= c) : a / c <= b / c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.dist_mk`：dist_mk (x₁ y₁ x₂ y₂ : Real) : dist (mk x₁ y₁) (mk x₂ y
₂) = √((x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2)
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Real.sqrt_sq_eq_abs`：sqrt_sq_eq_abs (x : Real) : √(x ^ 2) = |x|
· 使用定理 `Complex.abs_im_le_norm`：abs_im_le_norm (z : Complex) : |z.im| <= ‖z‖
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
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
· 使用定理 `Real.sqrt_pos_of_pos`：∀ {x : ℝ}, 0 < x → 0 < √x

--- 原说明 ---
Hyperbolic distance between two points is greater than or equal to the distance 
between the
logarithms of their imaginary parts.
-/
theorem dist_log_im_le (z w : ℍ) : dist (log z.im) (log w.im) ≤ dist z w :=
  calc
    dist (log z.im) (log w.im) = dist (mk ⟨0, z.im⟩ z.im_pos) (mk ⟨0, w.im⟩ w.im_pos) :=
      Eq.symm <| dist_of_re_eq rfl
    _ ≤ dist z w := by
      simp_rw [dist_eq]
      dsimp only [coe_mk, mk_im]
      gcongr
      simpa [sqrt_sq_eq_abs, ← dist_eq_norm] using Complex.abs_im_le_norm (z - w)
/-
**UpperHalfPlane.im_le_im_mul_exp_dist** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane
`。
形式化陈述：im_le_im_mul_exp_dist (z w : ℍ) : z.im <= w.im * Real.exp (dist z w)
参数：z w : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
· 使用定理 `Real.exp_log`：exp_log (hx : 0 < x) : exp (log x) = x
· 使用定理 `Real.exp_sub`：exp_sub : exp (x - y) = exp x / exp y
· 使用定理 `Real.exp_le_exp`：exp_le_exp {x y : Real} : exp x <= exp y ↔ x <= y
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
· 使用定理 `UpperHalfPlane.dist_log_im_le`：dist_log_im_le (z w : ℍ) : dist (log z.im
) (log w.im) <= dist z w
-/
theorem im_le_im_mul_exp_dist (z w : ℍ) : z.im ≤ w.im * Real.exp (dist z w) := by
  rw [← div_le_iff₀' w.im_pos, ← exp_log z.im_pos, ← exp_log w.im_pos, ← Real.exp_sub, exp_le_exp]
  exact (le_abs_self _).trans (dist_log_im_le z w)
/-
**UpperHalfPlane.im_div_exp_dist_le** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：im_div_exp_dist_le (z w : ℍ) : z.im / Real.exp (dist z w) <= w.im
参数：z w : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `div_le_iff₀`：div_le_iff₀ (hc : 0 < c) : b / c <= a ↔ b <= a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `UpperHalfPlane.im_le_im_mul_exp_dist`：im_le_im_mul_exp_dist (z w : ℍ) : 
z.im <= w.im * Real.exp (dist z w)
-/
theorem im_div_exp_dist_le (z w : ℍ) : z.im / Real.exp (dist z w) ≤ w.im :=
  (div_le_iff₀ (exp_pos _)).2 (im_le_im_mul_exp_dist z w)

/-- An upper estimate on the complex distance between two points in terms of the hyperbolic distance
and the imaginary part of one of the points. -/
/-
**UpperHalfPlane.dist_coe_le** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：dist_coe_le (z w : ℍ) : dist (z : Complex) w <= w.im * (Real.exp (dist z w
) - 1)
参数：z w : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dist_triangle_right`：dist_triangle_right (x y z : α) : dist x y <= dist 
x z + dist y z
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UpperHalfPlane.dist_center_dist`：dist_center_dist (z w : ℍ) : dist (z : 
Complex) (w.center (dist z w)) = w.im * Real.sinh (dist z w)
· 使用定理 `UpperHalfPlane.dist_self_center`：dist_self_center (z : ℍ) (r : Real) : d
ist (z : Complex) (z.center r) = z.im * (Real.cosh r - 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `add_sub_assoc`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b c : G), a +
 b - c = a + (b - c)
· 使用定理 `Real.sinh_add_cosh`：sinh_add_cosh : sinh x + cosh x = exp x

--- 原说明 ---
An upper estimate on the complex distance between two points in terms of the hyp
erbolic distance
and the imaginary part of one of the points.
-/
theorem dist_coe_le (z w : ℍ) : dist (z : ℂ) w ≤ w.im * (Real.exp (dist z w) - 1) :=
  calc
    dist (z : ℂ) w ≤ dist (z : ℂ) (w.center (dist z w)) + dist (w : ℂ) (w.center (dist z w)) :=
      dist_triangle_right _ _ _
    _ = w.im * (Real.exp (dist z w) - 1) := by
      rw [dist_center_dist, dist_self_center, ← mul_add, ← add_sub_assoc, Real.sinh_add_cosh]

/-- An upper estimate on the complex distance between two points in terms of the hyperbolic distance
and the imaginary part of one of the points. -/
/-
**UpperHalfPlane.le_dist_coe** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：le_dist_coe (z w : ℍ) : w.im * (1 - Real.exp (-dist z w)) <= dist (z : Com
plex) w
参数：z w : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UpperHalfPlane.dist_center_dist`：dist_center_dist (z w : ℍ) : dist (z : 
Complex) (w.center (dist z w)) = w.im * Real.sinh (dist z w)
· 使用定理 `UpperHalfPlane.dist_self_center`：dist_self_center (z : ℍ) (r : Real) : d
ist (z : Complex) (z.center r) = z.im * (Real.cosh r - 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.cosh_sub_sinh`：cosh_sub_sinh : cosh x - sinh x = exp (-x)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
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
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
An upper estimate on the complex distance between two points in terms of the hyp
erbolic distance
and the imaginary part of one of the points.
-/
theorem le_dist_coe (z w : ℍ) : w.im * (1 - Real.exp (-dist z w)) ≤ dist (z : ℂ) w :=
  calc
    w.im * (1 - Real.exp (-dist z w)) =
        dist (z : ℂ) (w.center (dist z w)) - dist (w : ℂ) (w.center (dist z w)) := by
      rw [dist_center_dist, dist_self_center, ← Real.cosh_sub_sinh]; ring
    _ ≤ dist (z : ℂ) w := sub_le_iff_le_add.2 <| dist_triangle _ _ _

/-- The hyperbolic metric on the upper half plane. We ensure that the projection to
`TopologicalSpace` is definitionally equal to the subtype topology. -/
/-
**UpperHalfPlane.** 是 Mathlib 中的一个实例，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The hyperbolic metric on the upper half plane. We ensure that the projection to
`TopologicalSpace` is definitionally equal to the subtype topology.
-/
instance : MetricSpace ℍ :=
  metricSpaceAux.replaceTopology <| by
    refine le_antisymm (continuous_id_iff_le.1 ?_) ?_
    · refine (@continuous_iff_continuous_dist ℍ ℍ metricSpaceAux.toPseudoMetricSpace _ _).2 ?_
      have : ∀ x : ℍ × ℍ, 2 * √(x.1.im * x.2.im) ≠ 0 := fun x => by positivity
      -- `continuity` fails to apply `Continuous.div`
      apply_rules [Continuous.div, Continuous.mul, continuous_const, Continuous.arsinh,
        Continuous.dist, continuous_coe.comp, continuous_fst, continuous_snd,
        Real.continuous_sqrt.comp, continuous_im.comp]
    · let : MetricSpace ℍ := metricSpaceAux
      refine le_of_nhds_le_nhds fun z => ?_
      rw [nhds_induced]
      refine (nhds_basis_ball.le_basis_iff (nhds_basis_ball.comap _)).2 fun R hR => ?_
      have h₁ : 1 < R / im z + 1 := lt_add_of_pos_left _ (div_pos hR z.im_pos)
      have h₀ : 0 < R / im z + 1 := one_pos.trans h₁
      refine ⟨log (R / im z + 1), Real.log_pos h₁, ?_⟩
      refine fun w hw => (dist_coe_le w z).trans_lt ?_
      rwa [← lt_div_iff₀' z.im_pos, sub_lt_iff_lt_add, ← Real.lt_log_iff_exp_lt h₀]
/-
**UpperHalfPlane.im_pos_of_dist_center_le** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPl
ane`。
形式化陈述：im_pos_of_dist_center_le {z : ℍ} {r : Real} {w : Complex} (h : dist w (cen
ter z r) <= z.im * Real.sinh r) : 0 < w.im
参数：h : dist w (center z r) <= z.im * Real.sinh r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
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
· 使用定理 `Real.sinh_lt_cosh`：sinh_lt_cosh : sinh x < cosh x
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `sub_le_sub_left`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Add
LeftMono α] [AddRightMono α] {a b : α},   a ≤ b → ∀ (c : α), c - b ≤ c - a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_le_comm`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : LE α] [Add
LeftMono α] {a b c : α}, a - b ≤ c ↔ a - c ≤ b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Complex.abs_im_le_norm`：abs_im_le_norm (z : Complex) : |z.im| <= ‖z‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
-/
theorem im_pos_of_dist_center_le {z : ℍ} {r : ℝ} {w : ℂ}
    (h : dist w (center z r) ≤ z.im * Real.sinh r) : 0 < w.im :=
  calc
    0 < z.im * (Real.cosh r - Real.sinh r) := mul_pos z.im_pos (sub_pos.2 <| sinh_lt_cosh _)
    _ = (z.center r).im - z.im * Real.sinh r := mul_sub _ _ _
    _ ≤ (z.center r).im - dist (z.center r : ℂ) w := sub_le_sub_left (by rwa [dist_comm]) _
    _ ≤ w.im := sub_le_comm.1 <|
      (le_abs_self _).trans ((abs_im_le_norm <| z.center r - w).trans_eq (dist_eq_norm _ _).symm)
/-
**UpperHalfPlane.image_coe_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`
。
形式化陈述：image_coe_closedBall (z : ℍ) (r : Real) : ((↑) : ℍ -> Complex) '' closedBa
ll (α
参数：z : ℍ；r : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `UpperHalfPlane.dist_le_iff_dist_coe_center_le`：dist_le_iff_dist_coe_cent
er_le : dist z w <= r ↔ dist (z : Complex) (w.center r) <= w.im * Real.sinh r
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `UpperHalfPlane.im_pos_of_dist_center_le`：im_pos_of_dist_center_le {z : ℍ
} {r : Real} {w : Complex} (h : dist w (center z r) <= z.im * Real.sinh r) : 0 <
 w.im
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem image_coe_closedBall (z : ℍ) (r : ℝ) :
    ((↑) : ℍ → ℂ) '' closedBall (α := ℍ) z r = closedBall ↑(z.center r) (z.im * Real.sinh r) := by
  ext w; constructor
  · rintro ⟨w, hw, rfl⟩
    exact dist_le_iff_dist_coe_center_le.1 hw
  · intro hw
    lift w to ℍ using im_pos_of_dist_center_le hw
    exact mem_image_of_mem _ (dist_le_iff_dist_coe_center_le.2 hw)
/-
**UpperHalfPlane.image_coe_ball** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：image_coe_ball (z : ℍ) (r : Real) : ((↑) : ℍ -> Complex) '' ball (α
参数：z : ℍ；r : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `UpperHalfPlane.dist_lt_iff_dist_coe_center_lt`：dist_lt_iff_dist_coe_cent
er_lt : dist z w < r ↔ dist (z : Complex) (w.center r) < w.im * Real.sinh r
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `UpperHalfPlane.im_pos_of_dist_center_le`：im_pos_of_dist_center_le {z : ℍ
} {r : Real} {w : Complex} (h : dist w (center z r) <= z.im * Real.sinh r) : 0 <
 w.im
· 使用定理 `Metric.ball_subset_closedBall`：ball_subset_closedBall : ball x ε subsete
q closedBall x ε
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem image_coe_ball (z : ℍ) (r : ℝ) :
    ((↑) : ℍ → ℂ) '' ball (α := ℍ) z r = ball ↑(z.center r) (z.im * Real.sinh r) := by
  ext w; constructor
  · rintro ⟨w, hw, rfl⟩
    exact dist_lt_iff_dist_coe_center_lt.1 hw
  · intro hw
    lift w to ℍ using im_pos_of_dist_center_le (ball_subset_closedBall hw)
    exact mem_image_of_mem _ (dist_lt_iff_dist_coe_center_lt.2 hw)
/-
**UpperHalfPlane.image_coe_sphere** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：image_coe_sphere (z : ℍ) (r : Real) : ((↑) : ℍ -> Complex) '' sphere (α
参数：z : ℍ；r : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `UpperHalfPlane.dist_eq_iff_dist_coe_center_eq`：dist_eq_iff_dist_coe_cent
er_eq : dist z w = r ↔ dist (z : Complex) (w.center r) = w.im * Real.sinh r
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `UpperHalfPlane.im_pos_of_dist_center_le`：im_pos_of_dist_center_le {z : ℍ
} {r : Real} {w : Complex} (h : dist w (center z r) <= z.im * Real.sinh r) : 0 <
 w.im
· 使用定理 `Metric.sphere_subset_closedBall`：sphere_subset_closedBall : sphere x ε s
ubseteq closedBall x ε
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem image_coe_sphere (z : ℍ) (r : ℝ) :
    ((↑) : ℍ → ℂ) '' sphere (α := ℍ) z r = sphere ↑(z.center r) (z.im * Real.sinh r) := by
  ext w; constructor
  · rintro ⟨w, hw, rfl⟩
    exact dist_eq_iff_dist_coe_center_eq.1 hw
  · intro hw
    lift w to ℍ using im_pos_of_dist_center_le (sphere_subset_closedBall hw)
    exact mem_image_of_mem _ (dist_eq_iff_dist_coe_center_eq.2 hw)
/-
**UpperHalfPlane.** 是 Mathlib 中的一个实例，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ProperSpace ℍ := by
  refine ⟨fun z r => ?_⟩
  rw [isEmbedding_coe.isCompact_iff (f := ((↑) : ℍ → ℂ)), image_coe_closedBall]
  apply isCompact_closedBall
/-
**UpperHalfPlane.isometry_vertical_line** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlan
e`。
形式化陈述：isometry_vertical_line (a : Real) : Isometry fun y => mk ⟨a, exp y⟩ (exp_p
os y)
参数：a : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.of_dist_eq`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpa
ce α] [inst_1 : PseudoMetricSpace β] {f : α → β},   (∀ (x y : α), dist (f x) (f 
y) = dist…
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UpperHalfPlane.dist_of_re_eq`：∀ {z w : UpperHalfPlane}, z.re = w.re → di
st z w = dist (Real.log z.im) (Real.log w.im)
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Real.log_exp`：log_exp (x : Real) : log (exp x) = x
-/
theorem isometry_vertical_line (a : ℝ) : Isometry fun y => mk ⟨a, exp y⟩ (exp_pos y) := by
  refine Isometry.of_dist_eq fun y₁ y₂ => ?_
  rw [dist_of_re_eq]
  exacts [congr_arg₂ _ (log_exp _) (log_exp _), rfl]
/-
**UpperHalfPlane.isometry_real_vadd** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：isometry_real_vadd (a : Real) : Isometry (a +ᵥ · : ℍ -> ℍ)
参数：a : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.of_dist_eq`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpa
ce α] [inst_1 : PseudoMetricSpace β] {f : α → β},   (∀ (x y : α), dist (f x) (f 
y) = dist…
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
· 使用定理 `dist_add_left`：∀ {M : Type u} [inst : PseudoMetricSpace M] [inst_1 : Add
 M] [IsIsometricVAdd M M] (a b c : M),   dist (a + b) (a + c) = dist b c
· 使用定理 `NormedAddGroup.to_isIsometricVAdd`：∀ {E : Type u_2} [inst : SeminormedAd
dGroup E], IsIsometricVAdd E E
· 使用定理 `UpperHalfPlane.vadd_im`：vadd_im : (x +ᵥ z).im = z.im
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isometry_real_vadd (a : ℝ) : Isometry (a +ᵥ · : ℍ → ℍ) :=
  Isometry.of_dist_eq fun y₁ y₂ => by simp only [dist_eq, coe_vadd, vadd_im, dist_add_left]
/-
**UpperHalfPlane.isometry_pos_mul** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：isometry_pos_mul (a : { x : Real // 0 < x }) : Isometry (a • · : ℍ -> ℍ)
参数：a : { x : Real // 0 < x }。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.of_dist_eq`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpa
ce α] [inst_1 : PseudoMetricSpace β] {f : α → β},   (∀ (x y : α), dist (f x) (f 
y) = dist…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `UpperHalfPlane.pos_real_im`：pos_real_im : (x • z).im = x * z.im
· 使用定理 `dist_smul₀`：dist_smul₀ (s : α) (x y : β) : dist (s • x) (s • y) = ‖s‖ * 
dist x y
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `mul_mul_mul_comm`：mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a *
 c * (b * d)
· 使用定理 `Real.sqrt_mul`：sqrt_mul {x : Real} (hx : 0 <= x) (y : Real) : √(x * y) =
 √x * √y
· 使用引理 `mul_self_nonneg`：mul_self_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLe
ftMono R] (a : R) : 0 <= a * a
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Real.sqrt_mul_self_eq_abs`：sqrt_mul_self_eq_abs (x : Real) : √(x * x) = 
|x|
· 使用定理 `Real.norm_eq_abs`：norm_eq_abs (r : Real) : ‖r‖ = |r|
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用引理 `mul_div_mul_left`：mul_div_mul_left (a b : G₀) (hc : c != 0) : c * a / (c
 * b) = a / b
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `abs_eq_zero`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder 
α] [AddLeftMono α] {a : α} [AddRightMono α], |a| = 0 ↔ a = 0
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem isometry_pos_mul (a : { x : ℝ // 0 < x }) : Isometry (a • · : ℍ → ℍ) := by
  refine Isometry.of_dist_eq fun y₁ y₂ => ?_
  simp only [dist_eq, coe_pos_real_smul, pos_real_im]; congr 2
  rw [dist_smul₀, mul_mul_mul_comm, Real.sqrt_mul (mul_self_nonneg _), Real.sqrt_mul_self_eq_abs,
    Real.norm_eq_abs, mul_left_comm]
  exact mul_div_mul_left _ _ (mt _root_.abs_eq_zero.1 a.2.ne')

/-- `SL(2, ℝ)` acts on the upper half plane as an isometry. -/
/-
**UpperHalfPlane.** 是 Mathlib 中的一个实例，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`SL(2, ℝ)` acts on the upper half plane as an isometry.
-/
instance : IsIsometricSMul SL(2, ℝ) ℍ :=
  ⟨fun g => by
    have h₀ : Isometry (fun z => ModularGroup.S • z : ℍ → ℍ) :=
      Isometry.of_dist_eq fun y₁ y₂ => by
        have h₁ : 0 ≤ im y₁ * im y₂ := by positivity
        have h₂ : ‖(y₁ * y₂ : ℂ)‖ ≠ 0 := by simp [y₁.ne_zero, y₂.ne_zero]
        simp_rw [modular_S_smul, inv_neg, dist_eq, dist_neg_neg,
          dist_inv_inv₀ y₁.ne_zero y₂.ne_zero, mk_im, neg_im, inv_im, coe_im, neg_div, neg_neg,
          div_mul_div_comm, ← normSq_mul, Real.sqrt_div h₁, ← norm_def, mul_div (2 : ℝ)]
        rw [div_div_div_comm, ← norm_mul, div_self h₂, div_one]
    by_cases hc : g 1 0 = 0
    · obtain ⟨u, v, h⟩ := exists_SL2_smul_eq_of_apply_zero_one_eq_zero g hc
      rw [h]
      exact (isometry_real_vadd v).comp (isometry_pos_mul u)
    · obtain ⟨u, v, w, h⟩ := exists_SL2_smul_eq_of_apply_zero_one_ne_zero g hc
      rw [h]
      exact
        (isometry_real_vadd w).comp (h₀.comp <| (isometry_real_vadd v).comp <| isometry_pos_mul u)⟩

end UpperHalfPlane

