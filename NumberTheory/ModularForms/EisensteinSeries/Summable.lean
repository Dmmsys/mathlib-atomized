/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.Analysis.PSeries
public import Mathlib.Order.Interval.Finset.Box
public import Mathlib.Analysis.Asymptotics.Defs

/-!
# Summability of Eisenstein series

We gather results about the summability of Eisenstein series, particularly
the summability of the Eisenstein series summands, which are used in the proof of the
boundedness of Eisenstein series at infinity.
-/

@[expose] public section
noncomputable section

open Complex UpperHalfPlane Set Finset Topology Filter Asymptotics

open scoped UpperHalfPlane Topology Nat

variable (z : ℍ)

namespace EisensteinSeries

/-
**EisensteinSeries.norm_eq_max_natAbs** 是 Mathlib 中的一个引理，位于命名空间 `EisensteinSerie
s`。
形式化陈述：norm_eq_max_natAbs (x : Fin 2 -> Int) : ‖x‖ = max (x 0).natAbs (x 1).natAb
s
参数：x : Fin 2 -> Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `coe_nnnorm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ↑‖a‖
₊ = ‖a‖
· 使用定理 `NNReal.coe_natCast`：∀ (n : ℕ), ↑↑n = ↑n
· 使用定理 `NNReal.coe_inj`：∀ {r₁ r₂ : NNReal}, ↑r₁ = ↑r₂ ↔ r₁ = r₂
· 使用定理 `Nat.cast_max`：cast_max {α} [Semiring α] [LinearOrder α] [IsStrictOrdered
Ring α] (m n : Nat) : (↑(max m n : Nat) : α) = max (m : α) n
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NNReal.natCast_natAbs`：∀ (n : ℤ), ↑n.natAbs = ‖n‖₊
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma norm_eq_max_natAbs (x : Fin 2 → ℤ) : ‖x‖ = max (x 0).natAbs (x 1).natAbs := by
  rw [← coe_nnnorm, ← NNReal.coe_natCast, NNReal.coe_inj, Nat.cast_max]
  refine eq_of_forall_ge_iff fun c ↦ ?_
  simp only [pi_nnnorm_le_iff, Fin.forall_fin_two, max_le_iff, NNReal.natCast_natAbs]
/-
**EisensteinSeries.norm_symm** 是 Mathlib 中的一个引理，位于命名空间 `EisensteinSeries`。
形式化陈述：norm_symm (x y : Int) : ‖![x, y]‖ = ‖![y, x]‖
参数：x y : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `EisensteinSeries.norm_eq_max_natAbs`：norm_eq_max_natAbs (x : Fin 2 -> In
t) : ‖x‖ = max (x 0).natAbs (x 1).natAbs
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Nat.cast_max`：cast_max {α} [Semiring α] [LinearOrder α] [IsStrictOrdered
Ring α] (m n : Nat) : (↑(max m n : Nat) : α) = max (m : α) n
· 使用定理 `Nat.cast_natAbs`：∀ {α : Type u_1} [inst : AddGroupWithOne α] (n : ℤ), ↑n
.natAbs = ↑|n|
· 使用引理 `Int.cast_abs`：cast_abs : (↑|a| : R) = |(a : R)|
· 使用定理 `max_comm`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), max a b = m
ax b a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma norm_symm (x y : ℤ) : ‖![x, y]‖ = ‖![y, x]‖ := by
  simp [EisensteinSeries.norm_eq_max_natAbs, max_comm]
/-
**EisensteinSeries.abs_le_left_of_norm** 是 Mathlib 中的一个定理，位于命名空间 `EisensteinSeri
es`。
形式化陈述：abs_le_left_of_norm (m n : Int) : |n| <= ‖![n, m]‖
参数：m n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `EisensteinSeries.norm_eq_max_natAbs`：norm_eq_max_natAbs (x : Fin 2 -> In
t) : ‖x‖ = max (x 0).natAbs (x 1).natAbs
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Nat.cast_max`：cast_max {α} [Semiring α] [LinearOrder α] [IsStrictOrdered
Ring α] (m n : Nat) : (↑(max m n : Nat) : α) = max (m : α) n
· 使用定理 `Int.abs_eq_natAbs`：∀ (a : ℤ), |a| = ↑a.natAbs
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem abs_le_left_of_norm (m n : ℤ) : |n| ≤ ‖![n, m]‖ := by
  simp only [EisensteinSeries.norm_eq_max_natAbs, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Nat.cast_max, le_sup_iff]
  left
  rw [Int.abs_eq_natAbs]
  exact le_refl _
/-
**EisensteinSeries.abs_le_right_of_norm** 是 Mathlib 中的一个定理，位于命名空间 `EisensteinSer
ies`。
形式化陈述：abs_le_right_of_norm (m n : Int) : |m| <= ‖![n, m]‖
参数：m n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `EisensteinSeries.norm_eq_max_natAbs`：norm_eq_max_natAbs (x : Fin 2 -> In
t) : ‖x‖ = max (x 0).natAbs (x 1).natAbs
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Nat.cast_max`：cast_max {α} [Semiring α] [LinearOrder α] [IsStrictOrdered
Ring α] (m n : Nat) : (↑(max m n : Nat) : α) = max (m : α) n
· 使用定理 `Int.abs_eq_natAbs`：∀ (a : ℤ), |a| = ↑a.natAbs
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem abs_le_right_of_norm (m n : ℤ) : |m| ≤ ‖![n, m]‖ := by
  simp only [EisensteinSeries.norm_eq_max_natAbs, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Nat.cast_max, le_sup_iff]
  right
  rw [Int.abs_eq_natAbs]
  exact le_refl _
/-
**EisensteinSeries.abs_norm_eq_max_natAbs** 是 Mathlib 中的一个引理，位于命名空间 `EisensteinS
eries`。
形式化陈述：abs_norm_eq_max_natAbs (n : Nat) : ‖![1, (n + 1 : Int)]‖ = n + 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `EisensteinSeries.norm_eq_max_natAbs`：norm_eq_max_natAbs (x : Fin 2 -> In
t) : ‖x‖ = max (x 0).natAbs (x 1).natAbs
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
lemma abs_norm_eq_max_natAbs (n : ℕ) : ‖![1, (n + 1 : ℤ)]‖ = n + 1 := by
  simp only [EisensteinSeries.norm_eq_max_natAbs, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  norm_cast
/-
**EisensteinSeries.abs_norm_eq_max_natAbs_neg** 是 Mathlib 中的一个引理，位于命名空间 `Eisenst
einSeries`。
形式化陈述：abs_norm_eq_max_natAbs_neg (n : Nat) : ‖![1, -(n + 1 : Int)]‖ = n + 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `EisensteinSeries.norm_eq_max_natAbs`：norm_eq_max_natAbs (x : Fin 2 -> In
t) : ‖x‖ = max (x 0).natAbs (x 1).natAbs
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
lemma abs_norm_eq_max_natAbs_neg (n : ℕ) : ‖![1, -(n + 1 : ℤ)]‖ = n + 1 := by
  simp only [EisensteinSeries.norm_eq_max_natAbs, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  norm_cast

section bounding_functions

/-- Auxiliary function used for bounding Eisenstein series, defined as
  `z.im ^ 2 / (z.re ^ 2 + z.im ^ 2)`. -/
/-
**EisensteinSeries.r1** 是 Mathlib 中的一个定义，位于命名空间 `EisensteinSeries`。
形式化陈述：r1 : Real
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary function used for bounding Eisenstein series, defined as
  `z.im ^ 2 / (z.re ^ 2 + z.im ^ 2)`.
-/
def r1 : ℝ := z.im ^ 2 / (z.re ^ 2 + z.im ^ 2)
/-
**EisensteinSeries.r1_eq** 是 Mathlib 中的一个引理，位于命名空间 `EisensteinSeries`。
形式化陈述：r1_eq : r1 z = 1 / ((z.re / z.im) ^ 2 + 1)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `div_pow`：div_pow (a b : α) (n : Nat) : (a / b) ^ n = a ^ n / b ^ n
· 使用定理 `div_add_one`：div_add_one (h : b != 0) : a / b + 1 = (a + b) / b
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
· 使用定理 `one_div_div`：one_div_div : 1 / (a / b) = b / a
· 使用定理 `EisensteinSeries.r1.eq_1`：∀ (z : UpperHalfPlane), EisensteinSeries.r1 z 
= z.im ^ 2 / (z.re ^ 2 + z.im ^ 2)
-/
lemma r1_eq : r1 z = 1 / ((z.re / z.im) ^ 2 + 1) := by
  rw [div_pow, div_add_one (by positivity), one_div_div, r1]
/-
**EisensteinSeries.r1_pos** 是 Mathlib 中的一个引理，位于命名空间 `EisensteinSeries`。
形式化陈述：r1_pos : 0 < r1 z
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
· 使用定理 `Right.add_pos_of_nonneg_of_pos`：∀ {α : Type u_1} [inst : AddZeroClass α]
 [inst_1 : Preorder α] [AddRightMono α] {a b : α}, 0 ≤ a → 0 < b → 0 < a + b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Even.pow_nonneg`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : LinearOr
der R] [IsOrderedRing R] [ExistsAddOfLE R] {n : ℕ},   Even n → ∀ (a : R), 0 ≤ a 
^ n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `even_two_mul`：even_two_mul (a : α) : Even (2 * a)
-/
lemma r1_pos : 0 < r1 z := by
  dsimp only [r1]
  positivity

/-- For `c, d ∈ ℝ` with `1 ≤ d ^ 2`, we have `r1 z ≤ |c * z + d| ^ 2`. -/
/-
**EisensteinSeries.r1_aux_bound** 是 Mathlib 中的一个引理，位于命名空间 `EisensteinSeries`。
形式化陈述：r1_aux_bound (c : Real) {d : Real} (hd : 1 <= d ^ 2) : r1 z <= (c * z.re +
 d) ^ 2 + (c * z.im) ^ 2
参数：c : Real；hd : 1 <= d ^ 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_nat`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a : R} {b c k : ℕ} {d e : R}, b = c * k → a ^ c = d → d ^ k = e → a ^ b = 
e
· 使用定理 `Mathlib.Tactic.Ring.Common.coeff_one`：∀ (k : ℕ) {e : ℕ}, Nat.rawCast 1 =
 e → k.rawCast = e * k
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_one_cast_of_isNat`：∀ {R : Type u_1} [inst
 : CommSemiring R] (a : R) (b : ℕ), Mathlib.Meta.NormNum.IsNat b 1 → a ^ b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_bit0`：∀ {R : Type u_1} [inst : CommSemiri
ng R] {a b c : R} {k : ℕ}, a ^ k = b → b * b = c → a ^ Nat.mul 2 k = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_one`：∀ {R : Type u_1} [inst : CommSemirin
g R] (a : R), a ^ 1 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pp_pf_overlap`：∀ {R : Type u_1} [inst : C
ommSemiring R] {a₂ b₂ c : R} {ea eb e : ℕ} (x : R),   ea + eb = e → a₂ * b₂ = c 
→ x ^ ea * a₂ * (x ^ eb * b₂) = x …
（共 72 条，此处仅展示前 30 条）

--- 原说明 ---
For `c, d ∈ ℝ` with `1 ≤ d ^ 2`, we have `r1 z ≤ |c * z + d| ^ 2`.
-/
lemma r1_aux_bound (c : ℝ) {d : ℝ} (hd : 1 ≤ d ^ 2) :
    r1 z ≤ (c * z.re + d) ^ 2 + (c * z.im) ^ 2 := by
  have H1 : (c * z.re + d) ^ 2 + (c * z.im) ^ 2 =
    c ^ 2 * (z.re ^ 2 + z.im ^ 2) + d * 2 * c * z.re + d ^ 2 := by ring
  have H2 : (c ^ 2 * (z.re ^ 2 + z.im ^ 2) + d * 2 * c * z.re + d ^ 2) * (z.re ^ 2 + z.im ^ 2)
    - z.im ^ 2 = (c * (z.re ^ 2 + z.im ^ 2) + d * z.re) ^ 2 + (d ^ 2 - 1) * z.im ^ 2 := by ring
  rw [r1, H1, div_le_iff₀ (by positivity), ← sub_nonneg, H2]
  exact add_nonneg (sq_nonneg _) (mul_nonneg (sub_nonneg.mpr hd) (sq_nonneg _))

/-- This function is used to give an upper bound on the summands in Eisenstein series; it is
defined by `z ↦ min z.im √(z.im ^ 2 / (z.re ^ 2 + z.im ^ 2))`. -/
/-
**EisensteinSeries.r** 是 Mathlib 中的一个定义，位于命名空间 `EisensteinSeries`。
形式化陈述：r : Real
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This function is used to give an upper bound on the summands in Eisenstein serie
s; it is
defined by `z ↦ min z.im √(z.im ^ 2 / (z.re ^ 2 + z.im ^ 2))`.
-/
def r : ℝ := min z.im √(r1 z)
/-
**EisensteinSeries.r_pos** 是 Mathlib 中的一个引理，位于命名空间 `EisensteinSeries`。
形式化陈述：r_pos : 0 < r z
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma r_pos : 0 < r z := by
  simp only [r, lt_min_iff, im_pos, Real.sqrt_pos, r1_pos, and_self]
/-
**EisensteinSeries.r_lower_bound_on_verticalStrip** 是 Mathlib 中的一个引理，位于命名空间 `Eis
ensteinSeries`。
形式化陈述：r_lower_bound_on_verticalStrip {A B : Real} (h : 0 < B) (hz : z in vertica
lStrip A B) : r ⟨⟨A, B⟩, h⟩ <= r z
参数：h : 0 < B；hz : z in verticalStrip A B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `min_le_min`：∀ {α : Type u} [inst : LinearOrder α] {a b c d : α}, c ≤ a →
 d ≤ b → min c d ≤ min a b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Real.sqrt_monotone`：sqrt_monotone : Monotone Real.sqrt
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `EisensteinSeries.r1_eq`：r1_eq : r1 z = 1 / ((z.re / z.im) ^ 2 + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `div_pow`：div_pow (a b : α) (n : Nat) : (a / b) ^ n = a ^ n / b ^ n
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用引理 `inv_le_inv₀`：inv_le_inv₀ (ha : 0 < a) (hb : 0 < b) : a⁻¹ <= b⁻¹ ↔ b <= a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Right.add_pos_of_nonneg_of_pos`：∀ {α : Type u_1} [inst : AddZeroClass α]
 [inst_1 : Preorder α] [AddRightMono α] {a b : α}, 0 ≤ a → 0 < b → 0 < a + b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `Mathlib.Meta.Positivity.div_nonneg_of_nonneg_of_pos`：div_nonneg_of_nonne
g_of_pos [PosMulReflectLT α] (ha : 0 <= a) (hb : 0 < b) : 0 <= a / b
· 使用定理 `Even.pow_nonneg`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : LinearOr
der R] [IsOrderedRing R] [ExistsAddOfLE R] {n : ℕ},   Even n → ∀ (a : R), 0 ≤ a 
^ n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `even_two_mul`：even_two_mul (a : α) : Even (2 * a)
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
（共 47 条，此处仅展示前 30 条）
-/
lemma r_lower_bound_on_verticalStrip {A B : ℝ} (h : 0 < B) (hz : z ∈ verticalStrip A B) :
    r ⟨⟨A, B⟩, h⟩ ≤ r z := by
  apply min_le_min hz.2
  gcongr
  simp only [r1_eq, div_pow, one_div]
  rw [inv_le_inv₀ (by positivity) (by positivity), add_le_add_iff_right, ← even_two.pow_abs]
  gcongr
  exacts [hz.1, hz.2]
/-
**EisensteinSeries.auxbound1** 是 Mathlib 中的一个引理，位于命名空间 `EisensteinSeries`。
形式化陈述：auxbound1 {c : Real} (d : Real) (hc : 1 <= c ^ 2) : r z <= ‖c * (z : Compl
ex) + d‖
参数：d : Real；hc : 1 <= c ^ 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.le_sqrt'`：le_sqrt' (hx : 0 < x) : x <= √y ↔ x ^ 2 <= y
· 使用定理 `Complex.im_ofReal_mul`：im_ofReal_mul (r : Real) (z : Complex) : (r * z).
im = r * z.im
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_mul_of_one_le_left`：le_mul_of_one_le_left [MulPosMono α] (hb : 0 <= b
) (h : 1 <= a) : b <= a * b
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `le_add_of_nonneg_left`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 
: LE α] [AddRightMono α] {a b : α}, 0 ≤ b → a ≤ b + a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.norm_def`：norm_def (z : Complex) : ‖z‖ = √(normSq z)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.re_ofReal_mul`：re_ofReal_mul (r : Real) (z : Complex) : (r * z).
re = r * z.re
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
lemma auxbound1 {c : ℝ} (d : ℝ) (hc : 1 ≤ c ^ 2) : r z ≤ ‖c * (z : ℂ) + d‖ := by
  rcases z with ⟨z, hz⟩
  have H1 : z.im ≤ √((c * z.re + d) ^ 2 + (c * z).im ^ 2) := by
    rw [Real.le_sqrt' hz, im_ofReal_mul, mul_pow]
    exact (le_mul_of_one_le_left (sq_nonneg _) hc).trans <| le_add_of_nonneg_left (sq_nonneg _)
  simpa only [r, norm_def, normSq_apply, add_re, re_ofReal_mul, coe_re, ← pow_two, add_im, mul_im,
    coe_im, ofReal_im, zero_mul, add_zero, min_le_iff] using! Or.inl H1
/-
**EisensteinSeries.auxbound2** 是 Mathlib 中的一个引理，位于命名空间 `EisensteinSeries`。
形式化陈述：auxbound2 (c : Real) {d : Real} (hd : 1 <= d ^ 2) : r z <= ‖c * (z : Compl
ex) + d‖
参数：c : Real；hd : 1 <= d ^ 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.sqrt_le_sqrt_iff`：sqrt_le_sqrt_iff (hy : 0 <= y) : √x <= √y ↔ x <= 
y
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Even.pow_nonneg`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : LinearOr
der R] [IsOrderedRing R] [ExistsAddOfLE R] {n : ℕ},   Even n → ∀ (a : R), 0 ≤ a 
^ n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `even_two_mul`：even_two_mul (a : α) : Even (2 * a)
· 使用引理 `EisensteinSeries.r1_aux_bound`：r1_aux_bound (c : Real) {d : Real} (hd : 
1 <= d ^ 2) : r1 z <= (c * z.re + d) ^ 2 + (c * z.im) ^ 2
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.norm_def`：norm_def (z : Complex) : ‖z‖ = √(normSq z)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.re_ofReal_mul`：re_ofReal_mul (r : Real) (z : Complex) : (r * z).
re = r * z.re
· 使用定理 `Complex.im_ofReal_mul`：im_ofReal_mul (r : Real) (z : Complex) : (r * z).
im = r * z.im
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
lemma auxbound2 (c : ℝ) {d : ℝ} (hd : 1 ≤ d ^ 2) : r z ≤ ‖c * (z : ℂ) + d‖ := by
  have H1 : √(r1 z) ≤ √((c * z.re + d) ^ 2 + (c * z.im) ^ 2) :=
    (Real.sqrt_le_sqrt_iff (by positivity)).mpr (r1_aux_bound _ _ hd)
  simpa only [r, norm_def, normSq_apply, add_re, re_ofReal_mul, coe_re, ofReal_re, ← pow_two,
    add_im, im_ofReal_mul, coe_im, ofReal_im, add_zero, min_le_iff] using Or.inr H1
/-
**EisensteinSeries.div_max_sq_ge_one** 是 Mathlib 中的一个引理，位于命名空间 `EisensteinSeries
`。
形式化陈述：div_max_sq_ge_one (x : Fin 2 -> Int) (hx : x != 0) : 1 <= (x 0 / ‖x‖) ^ 2 
∨ 1 <= (x 1 / ‖x‖) ^ 2
参数：x : Fin 2 -> Int；hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.natAbs_ne_zero`：∀ {a : ℤ}, a.natAbs ≠ 0 ↔ a ≠ 0
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `EisensteinSeries.norm_eq_max_natAbs`：norm_eq_max_natAbs (x : Fin 2 -> In
t) : ‖x‖ = max (x 0).natAbs (x 1).natAbs
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_ne_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≠ 0 ↔ a ≠ 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_natAbs`：∀ {α : Type u_1} [inst : AddGroupWithOne α] (n : ℤ), ↑n
.natAbs = ↑|n|
· 使用引理 `Int.cast_abs`：cast_abs : (↑|a| : R) = |(a : R)|
· 使用引理 `div_pow`：div_pow (a b : α) (n : Nat) : (a / b) ^ n = a ^ n / b ^ n
· 使用定理 `sq_abs`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] (a : α
), |a| ^ 2 = a ^ 2
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `max_choice`：∀ {α : Type u} [inst : LinearOrder α] (a b : α), max a b = a
 ∨ max a b = b
-/
lemma div_max_sq_ge_one (x : Fin 2 → ℤ) (hx : x ≠ 0) :
    1 ≤ (x 0 / ‖x‖) ^ 2 ∨ 1 ≤ (x 1 / ‖x‖) ^ 2 := by
  refine (max_choice (x 0).natAbs (x 1).natAbs).imp (fun H0 ↦ ?_) (fun H1 ↦ ?_)
  · have : x 0 ≠ 0 := by
      rwa [← norm_ne_zero_iff, norm_eq_max_natAbs, H0, Nat.cast_ne_zero, Int.natAbs_ne_zero] at hx
    simp only [norm_eq_max_natAbs, H0, Nat.cast_natAbs, Int.cast_abs, div_pow, sq_abs, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, Int.cast_eq_zero, this, div_self,
      le_refl]
  · have : x 1 ≠ 0 := by
      rwa [← norm_ne_zero_iff, norm_eq_max_natAbs, H1, Nat.cast_ne_zero, Int.natAbs_ne_zero] at hx
    simp only [norm_eq_max_natAbs, H1, Nat.cast_natAbs, Int.cast_abs, div_pow, sq_abs, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, Int.cast_eq_zero, this, div_self,
      le_refl]
/-
**EisensteinSeries.r_mul_max_le** 是 Mathlib 中的一个引理，位于命名空间 `EisensteinSeries`。
形式化陈述：r_mul_max_le {x : Fin 2 -> Int} (hx : x != 0) : r z * ‖x‖ <= ‖x 0 * (z : C
omplex) + x 1‖
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_ne_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≠ 0 ↔ a ≠ 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `div_mul_eq_mul_div`：div_mul_eq_mul_div : a / b * c = a * c / b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用引理 `EisensteinSeries.norm_eq_max_natAbs`：norm_eq_max_natAbs (x : Fin 2 -> In
t) : ‖x‖ = max (x 0).natAbs (x 1).natAbs
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用引理 `EisensteinSeries.div_max_sq_ge_one`：div_max_sq_ge_one (x : Fin 2 -> Int)
 (hx : x != 0) : 1 <= (x 0 / ‖x‖) ^ 2 ∨ 1 <= (x 1 / ‖x‖) ^ 2
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.ofReal_div`：ofReal_div (r s : Real) : ((r / s : Real) : Complex)
 = r / s
· 使用引理 `EisensteinSeries.auxbound1`：auxbound1 {c : Real} (d : Real) (hc : 1 <= c
 ^ 2) : r z <= ‖c * (z : Complex) + d‖
· 使用引理 `EisensteinSeries.auxbound2`：auxbound2 (c : Real) {d : Real} (hd : 1 <= d
 ^ 2) : r z <= ‖c * (z : Complex) + d‖
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
lemma r_mul_max_le {x : Fin 2 → ℤ} (hx : x ≠ 0) : r z * ‖x‖ ≤ ‖x 0 * (z : ℂ) + x 1‖ := by
  have hn0 : ‖x‖ ≠ 0 := by rwa [norm_ne_zero_iff]
  have h11 : x 0 * (z : ℂ) + x 1 = (x 0 / ‖x‖ * z + x 1 / ‖x‖) * ‖x‖ := by
    rw [div_mul_eq_mul_div, ← add_div, div_mul_cancel₀ _ (mod_cast hn0)]
  rw [norm_eq_max_natAbs, h11, norm_mul, norm_real, norm_norm, norm_eq_max_natAbs]
  gcongr
  · rcases div_max_sq_ge_one x hx with H1 | H2
    · simpa only [norm_eq_max_natAbs, ofReal_div, ofReal_intCast] using auxbound1 z (x 1 / ‖x‖) H1
    · simpa only [norm_eq_max_natAbs, ofReal_div, ofReal_intCast] using auxbound2 z (x 0 / ‖x‖) H2

/-- Upper bound for the summand `|c * z + d| ^ (-k)`, as a product of a function of `z` and a
function of `c, d`. -/
/-
**EisensteinSeries.summand_bound** 是 Mathlib 中的一个引理，位于命名空间 `EisensteinSeries`。
形式化陈述：summand_bound {k : Real} (hk : 0 <= k) (x : Fin 2 -> Int) : ‖x 0 * (z : Co
mplex) + x 1‖ ^ (-k) <= (r z) ^ (-k) * ‖x‖ ^ (-k)
参数：hk : 0 <= k；x : Fin 2 -> Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Real.zero_rpow`：zero_rpow {x : Real} (h : x != 0) : (0 : Real) ^ x = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.mul_rpow`：mul_rpow (hx : 0 <= x) (hy : 0 <= y) : (x * y) ^ z = x ^ 
z * y ^ z
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `EisensteinSeries.r_pos`：r_pos : 0 < r z
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `Real.rpow_le_rpow_of_nonpos`：rpow_le_rpow_of_nonpos (hx : 0 < x) (hxy : 
x <= y) (hz : z <= 0) : y ^ z <= x ^ z
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用引理 `EisensteinSeries.r_mul_max_le`：r_mul_max_le {x : Fin 2 -> Int} (hx : x !
= 0) : r z * ‖x‖ <= ‖x 0 * (z : Complex) + x 1‖
· 使用定理 `neg_nonpos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, -a ≤ 0 ↔ 0 ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α

--- 原说明 ---
Upper bound for the summand `|c * z + d| ^ (-k)`, as a product of a function of 
`z` and a
function of `c, d`.
-/
lemma summand_bound {k : ℝ} (hk : 0 ≤ k) (x : Fin 2 → ℤ) :
    ‖x 0 * (z : ℂ) + x 1‖ ^ (-k) ≤ (r z) ^ (-k) * ‖x‖ ^ (-k) := by
  by_cases hx : x = 0
  · simp only [hx, Pi.zero_apply, Int.cast_zero, zero_mul, add_zero, norm_zero]
    by_cases h : -k = 0
    · rw [h, Real.rpow_zero, Real.rpow_zero, one_mul]
    · rw [Real.zero_rpow h, mul_zero]
  · rw [← Real.mul_rpow (r_pos _).le (norm_nonneg _)]
    exact Real.rpow_le_rpow_of_nonpos (mul_pos (r_pos _) (norm_pos_iff.mpr hx)) (r_mul_max_le z hx)
      (neg_nonpos.mpr hk)

variable {z} in
/-
**EisensteinSeries.summand_bound_of_mem_verticalStrip** 是 Mathlib 中的一个引理，位于命名空间 
`EisensteinSeries`。
形式化陈述：summand_bound_of_mem_verticalStrip {k : Real} (hk : 0 <= k) (x : Fin 2 -> 
Int) {A B : Real} (hB : 0 < B) (hz : z in verticalStrip A B) : ‖x 0 * (z : Compl
ex) + x 1‖ ^ (-k) <= r ⟨⟨A, B⟩, hB⟩ ^ (-k) * ‖x‖ ^ (-k)
参数：hk : 0 <= k；x : Fin 2 -> Int；hB : 0 < B；hz : z in verticalStrip A B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `EisensteinSeries.summand_bound`：summand_bound {k : Real} (hk : 0 <= k) (
x : Fin 2 -> Int) : ‖x 0 * (z : Complex) + x 1‖ ^ (-k) <= (r z) ^ (-k) * ‖x‖ ^ (
-k)
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用引理 `Real.rpow_le_rpow_of_nonpos`：rpow_le_rpow_of_nonpos (hx : 0 < x) (hxy : 
x <= y) (hz : z <= 0) : y ^ z <= x ^ z
· 使用引理 `EisensteinSeries.r_pos`：r_pos : 0 < r z
· 使用引理 `EisensteinSeries.r_lower_bound_on_verticalStrip`：r_lower_bound_on_vertic
alStrip {A B : Real} (h : 0 < B) (hz : z in verticalStrip A B) : r ⟨⟨A, B⟩, h⟩ <
= r z
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_nonpos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, -a ≤ 0 ↔ 0 ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
lemma summand_bound_of_mem_verticalStrip {k : ℝ} (hk : 0 ≤ k) (x : Fin 2 → ℤ)
    {A B : ℝ} (hB : 0 < B) (hz : z ∈ verticalStrip A B) :
    ‖x 0 * (z : ℂ) + x 1‖ ^ (-k) ≤ r ⟨⟨A, B⟩, hB⟩ ^ (-k) * ‖x‖ ^ (-k) := by
  refine (summand_bound z hk x).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  exact Real.rpow_le_rpow_of_nonpos (r_pos _) (r_lower_bound_on_verticalStrip z hB hz)
    (neg_nonpos.mpr hk)
/-
**EisensteinSeries.linear_isTheta_right_add** 是 Mathlib 中的一个引理，位于命名空间 `Eisenstei
nSeries`。
形式化陈述：linear_isTheta_right_add (c e : Int) (z : Complex) : (fun d : Int => c * z
 + d + e) =Θ[cofinite] fun n => (n : Real)
参数：c e : Int；z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsTheta.add_isLittleO`：∀ {α : Type u_1} {F : Type u_4} {E' :
 Type u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {l : Filter α}  
 {f₁ f₂ : α → E'} {g : …
· 使用定理 `Asymptotics.IsLittleO.add_isTheta`：∀ {α : Type u_1} {F : Type u_4} {E' :
 Type u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {l : Filter α}  
 {f₁ f₂ : α → E'} {g : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding`：∀ {E : Type u_2} 
[inst : SeminormedAddGroup E] {X : Type u_5} [inst_1 : TopologicalSpace X] [Disc
reteTopology X]   [ProperSpace E] {e : X → …
· 使用定理 `instDiscreteTopologyInt`：DiscreteTopology ℤ
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `Int.isClosedEmbedding_coe_real`：isClosedEmbedding_coe_real : IsClosedEmb
edding ((↑) : Int -> Real)
· 使用引理 `Int.cast_complex_isTheta_cast_real`：Int.cast_complex_isTheta_cast_real :
 Int.cast (R
-/
lemma linear_isTheta_right_add (c e : ℤ) (z : ℂ) :
    (fun d : ℤ ↦ c * z + d + e) =Θ[cofinite] fun n ↦ (n : ℝ) := by
  apply IsTheta.add_isLittleO <;>
  [refine Asymptotics.IsLittleO.add_isTheta ?_ (Int.cast_complex_isTheta_cast_real); skip] <;>
  simpa [-Int.cofinite_eq] using
    .inr <| tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding Int.isClosedEmbedding_coe_real
/-
**EisensteinSeries.linear_isTheta_left** 是 Mathlib 中的一个引理，位于命名空间 `EisensteinSeri
es`。
形式化陈述：linear_isTheta_left (d : Int) {z : Complex} (hz : z != 0) : (fun (c : Int)
 => (c * z + d)) =Θ[cofinite] fun n => (n : Real)
参数：d : Int；hz : z != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsTheta.add_isLittleO`：∀ {α : Type u_1} {F : Type u_4} {E' :
 Type u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {l : Filter α}  
 {f₁ f₂ : α → E'} {g : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Asymptotics.IsTheta.const_mul_left`：∀ {α : Type u_1} {F : Type u_4} {𝕜 :
 Type u_14} [inst : Norm F] [inst_1 : NormedField 𝕜] {g : α → F} {l : Filter α} 
  {c : 𝕜} {f : α → 𝕜}, c…
· 使用引理 `Int.cast_complex_isTheta_cast_real`：Int.cast_complex_isTheta_cast_real :
 Int.cast (R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding`：∀ {E : Type u_2} 
[inst : SeminormedAddGroup E] {X : Type u_5} [inst_1 : TopologicalSpace X] [Disc
reteTopology X]   [ProperSpace E] {e : X → …
· 使用定理 `instDiscreteTopologyInt`：DiscreteTopology ℤ
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `Int.isClosedEmbedding_coe_real`：isClosedEmbedding_coe_real : IsClosedEmb
edding ((↑) : Int -> Real)
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
lemma linear_isTheta_left (d : ℤ) {z : ℂ} (hz : z ≠ 0) :
    (fun (c : ℤ) ↦ (c * z + d)) =Θ[cofinite] fun n ↦ (n : ℝ) := by
  apply IsTheta.add_isLittleO
  · simp_rw [mul_comm]
    apply Asymptotics.IsTheta.const_mul_left hz Int.cast_complex_isTheta_cast_real
  · simp only [isLittleO_const_left, Int.cast_eq_zero,
      tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding Int.isClosedEmbedding_coe_real, or_true]
/-
**EisensteinSeries.linear_inv_isBigO_right_add** 是 Mathlib 中的一个引理，位于命名空间 `Eisens
teinSeries`。
形式化陈述：linear_inv_isBigO_right_add (c e : Int) (z : Complex) : (fun (d : Int) => 
(c * z + d + e)⁻¹) =O[cofinite] fun n => (n : Real)⁻¹
参数：c e : Int；z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsTheta.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_
4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},   f
 =Θ[l] g → f =O[…
· 使用定理 `Asymptotics.IsTheta.inv`：∀ {α : Type u_1} {𝕜 : Type u_14} {𝕜' : Type u_1
5} [inst : NormedField 𝕜] [inst_1 : NormedField 𝕜'] {l : Filter α}   {f : α → 𝕜}
 {g : α → 𝕜'}…
· 使用引理 `EisensteinSeries.linear_isTheta_right_add`：linear_isTheta_right_add (c e
 : Int) (z : Complex) : (fun d : Int => c * z + d + e) =Θ[cofinite] fun n => (n 
: Real)
-/
lemma linear_inv_isBigO_right_add (c e : ℤ) (z : ℂ) :
    (fun (d : ℤ) ↦ (c * z + d + e)⁻¹) =O[cofinite] fun n ↦ (n : ℝ)⁻¹ :=
  (linear_isTheta_right_add c e z).inv.isBigO
/-
**EisensteinSeries.linear_inv_isBigO_right** 是 Mathlib 中的一个引理，位于命名空间 `Eisenstein
Series`。
形式化陈述：linear_inv_isBigO_right (c : Int) (z : Complex) : (fun (d : Int) => (c * z
 + d)⁻¹) =O[cofinite] fun n => (n : Real)⁻¹
参数：c : Int；z : Complex。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma linear_inv_isBigO_right (c : ℤ) (z : ℂ) :
    (fun (d : ℤ) ↦ (c * z + d)⁻¹) =O[cofinite] fun n ↦ (n : ℝ)⁻¹ := by
  grind [add_zero, (linear_isTheta_right_add c 0 z).inv.isBigO]
/-
**EisensteinSeries.linear_inv_isBigO_left** 是 Mathlib 中的一个引理，位于命名空间 `EisensteinS
eries`。
形式化陈述：linear_inv_isBigO_left (d : Int) {z : Complex} (hz : z != 0) : (fun (c : I
nt) => (c * z + d)⁻¹) =O[cofinite] fun n => (n : Real)⁻¹
参数：d : Int；hz : z != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsTheta.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_
4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},   f
 =Θ[l] g → f =O[…
· 使用定理 `Asymptotics.IsTheta.inv`：∀ {α : Type u_1} {𝕜 : Type u_14} {𝕜' : Type u_1
5} [inst : NormedField 𝕜] [inst_1 : NormedField 𝕜'] {l : Filter α}   {f : α → 𝕜}
 {g : α → 𝕜'}…
· 使用引理 `EisensteinSeries.linear_isTheta_left`：linear_isTheta_left (d : Int) {z :
 Complex} (hz : z != 0) : (fun (c : Int) => (c * z + d)) =Θ[cofinite] fun n => (
n : Real)
-/
lemma linear_inv_isBigO_left (d : ℤ) {z : ℂ} (hz : z ≠ 0) :
    (fun (c : ℤ) ↦ (c * z + d)⁻¹) =O[cofinite] fun n ↦ (n : ℝ)⁻¹ :=
  (linear_isTheta_left d hz).inv.isBigO
/-
**EisensteinSeries.tendsto_zero_inv_linear** 是 Mathlib 中的一个引理，位于命名空间 `Eisenstein
Series`。
形式化陈述：tendsto_zero_inv_linear (z : Complex) (b : Int) : Tendsto (fun d : Nat => 
1 / ((b : Complex) * z + d)) atTop (𝓝 0)
参数：z : Complex；b : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.trans_tendsto`：∀ {α : Type u_1} {E'' : Type u_9} {F''
 : Type u_10} [inst : NormedAddCommGroup E''] [inst_1 : NormedAddCommGroup F''] 
  {f'' : α → E''} {g''…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Asymptotics.isBigO_sup`：isBigO_sup : f =O[l ⊔ l'] g' ↔ f =O[l] g' ∧ f =O
[l'] g'
· 使用引理 `EisensteinSeries.linear_inv_isBigO_right`：linear_inv_isBigO_right (c : I
nt) (z : Complex) : (fun (d : Int) => (c * z + d)⁻¹) =O[cofinite] fun n => (n : 
Real)⁻¹
· 使用定理 `Int.cofinite_eq`：cofinite_eq : (cofinite : Filter Int) = atBot ⊔ atTop
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `tendsto_inv_atTop_nhds_zero_nat`：tendsto_inv_atTop_nhds_zero_nat {𝕜 : Ty
pe*} [DivisionSemiring 𝕜] [CharZero 𝕜] [TopologicalSpace 𝕜] [ContinuousSMul Rat>
=0 𝕜] : Tendsto (fun …
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `NNRat.instContinuousSMulOfIsScalarTowerOfRat`：∀ {R : Type u_1} [inst : T
opologicalSpace R] [inst_1 : MulAction ℚ R] [inst_2 : MulAction ℚ≥0 R] [IsScalar
Tower ℚ≥0 ℚ R]   [ContinuousSMul ℚ…
· 使用定理 `NNRat.instContinuousSMulRatReal`：ContinuousSMul ℚ ℝ
-/
lemma tendsto_zero_inv_linear (z : ℂ) (b : ℤ) :
    Tendsto (fun d : ℕ ↦ 1 / ((b : ℂ) * z + d)) atTop (𝓝 0) := by
  apply IsBigO.trans_tendsto ?_ tendsto_inv_atTop_nhds_zero_nat (F'' := ℝ)
  have := (isBigO_sup.mp (Int.cofinite_eq ▸ linear_inv_isBigO_right b z)).2
  simpa [← Nat.map_cast_int_atTop, isBigO_map]
/-
**EisensteinSeries.tendsto_zero_inv_linear_sub** 是 Mathlib 中的一个引理，位于命名空间 `Eisens
teinSeries`。
形式化陈述：tendsto_zero_inv_linear_sub (z : Complex) (b : Int) : Tendsto (fun d : Nat
 => 1 / ((b : Complex) * z - d)) atTop (𝓝 0)
参数：z : Complex；b : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tendsto_zero_inv_linear_sub (z : ℂ) (b : ℤ) :
    Tendsto (fun d : ℕ ↦ 1 / ((b : ℂ) * z - d)) atTop (𝓝 0) := by
  grind [neg_zero, (tendsto_zero_inv_linear z (-b)).neg]

end bounding_functions

/-- The function `ℤ ^ 2 → ℝ` given by `x ↦ ‖x‖ ^ (-k)` is summable if `2 < k`. We prove this by
splitting into boxes using `Finset.box`. -/
/-
**EisensteinSeries.summable_one_div_norm_rpow** 是 Mathlib 中的一个引理，位于命名空间 `Eisenst
einSeries`。
形式化陈述：summable_one_div_norm_rpow {k : Real} (hk : 2 < k) : Summable fun (x : Fin
 2 -> Int) => ‖x‖ ^ (-k)
参数：hk : 2 < k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.summable_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst
 : AddCommMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   (e : γ ≃ β), Sum
mable (f…
· 使用引理 `summable_partition`：summable_partition {α β : Type*} {f : β -> Real} (hf
 : 0 <= f) {s : α -> Set β} (hs : forall i, exists! j, i in s j) : Summable f ↔ 
(forall …
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `Int.existsUnique_mem_box`：existsUnique_mem_box (x : Int × Int) : exists!
 n : Nat, x in box n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `finTwoArrowEquiv_symm_apply`：∀ (α : Type u_1), ⇑(finTwoArrowEquiv α).sym
m = fun x => ![x.1, x.2]
· 使用定理 `HasSum.summable`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α}, H
asSum…
· 使用定理 `hasSum_fintype`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] [inst_2 : Fintype β] (f : β → α)   (L : optParam 
(Sum…
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `tsum_fintype`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [
inst_1 : TopologicalSpace α] {L : SummationFilter β}   [L.LeAtTop] [inst_3 : Fin
ty…
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_attach`：card_attach : #s.attach = #s
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `Summable.of_norm_bounded_eventually_nat`：Summable.of_norm_bounded_eventu
ally_nat {f : Nat -> E} {g : Nat -> Real} (hg : Summable g) (h : forallᶠ i in at
Top, ‖f i‖ <= g i) : Summable…
· 使用定理 `Summable.mul_left`：Summable.mul_left (a) (hf : Summable f L) : Summable 
(fun i => a * f i) L
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.summable_nat_rpow`：summable_nat_rpow {p : Real} : Summable (fun n =
> (n : Real) ^ p : Nat -> Real) ↔ p < -1
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
（共 96 条，此处仅展示前 30 条）

--- 原说明 ---
The function `ℤ ^ 2 → ℝ` given by `x ↦ ‖x‖ ^ (-k)` is summable if `2 < k`. We pr
ove this by
splitting into boxes using `Finset.box`.
-/
lemma summable_one_div_norm_rpow {k : ℝ} (hk : 2 < k) :
    Summable fun (x : Fin 2 → ℤ) ↦ ‖x‖ ^ (-k) := by
  rw [← (finTwoArrowEquiv _).symm.summable_iff, summable_partition _ Int.existsUnique_mem_box]
  · simp only [finTwoArrowEquiv_symm_apply, Function.comp_def]
    refine ⟨fun n ↦ (hasSum_fintype (β := box (α := ℤ × ℤ) n) _).summable, ?_⟩
    suffices Summable fun n : ℕ ↦ ∑' (_ : box (α := ℤ × ℤ) n), (n : ℝ) ^ (-k) by
      refine this.congr fun n ↦ tsum_congr fun p ↦ ?_
      simp only [← Int.mem_box.mp p.2, Nat.cast_max, norm_eq_max_natAbs, Matrix.cons_val_zero,
        Matrix.cons_val_one]
    simp only [tsum_fintype, univ_eq_attach, sum_const, card_attach, nsmul_eq_mul]
    apply ((Real.summable_nat_rpow.mpr (by linarith : 1 - k < -1)).mul_left
      8).of_norm_bounded_eventually_nat
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    rw [Int.card_box hn.ne', Real.norm_of_nonneg (by positivity), sub_eq_add_neg,
      Real.rpow_add (Nat.cast_pos.mpr hn), Real.rpow_one, Nat.cast_mul, Nat.cast_ofNat, mul_assoc]
  · exact fun n ↦ Real.rpow_nonneg (norm_nonneg _) _

/-- If the inverse of a function `isBigO` to `(|(n : ℝ)| ^ a)⁻¹` for `1 < a`, then the function is
Summable. -/
/-
**EisensteinSeries.summable_inv_of_isBigO_rpow_inv** 是 Mathlib 中的一个引理，位于命名空间 `Ei
sensteinSeries`。
形式化陈述：summable_inv_of_isBigO_rpow_inv {α : Type*} [NormedField α] [CompleteSpace
 α] {f : Int -> α} {a : Real} (hab : 1 < a) (hf : (fun n => (f n)⁻¹) =O[cofinite
] fun n => (|(n : Real)| ^ a)⁻¹) : Summable fun n => (f n)⁻¹
参数：hab : 1 < a；hf : (fun n => (f n)⁻¹) =O[cofinite] fun n => (|(n : Real)| ^ a)⁻
¹。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `summable_of_isBigO`：summable_of_isBigO {ι E} [SeminormedAddCommGroup E] 
[CompleteSpace E] {f : ι -> E} {g : ι -> Real} (hg : Summable g) (h : f =O[cofin
ite] g) …
· 使用定理 `Summable.congr`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {f g : β → α}   {L : SummationFilter β}, Summable
 f L…
· 使用定理 `Real.summable_abs_int_rpow`：summable_abs_int_rpow {b : Real} (hb : 1 < b
) : Summable fun n : Int => |(n : Real)| ^ (-b)
· 使用定理 `Real.rpow_neg`：rpow_neg {x : Real} (hx : 0 <= x) (y : Real) : x ^ (-y) =
 (x ^ y)⁻¹
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…

--- 原说明 ---
If the inverse of a function `isBigO` to `(|(n : ℝ)| ^ a)⁻¹` for `1 < a`, then t
he function is
Summable.
-/
lemma summable_inv_of_isBigO_rpow_inv {α : Type*} [NormedField α] [CompleteSpace α]
    {f : ℤ → α} {a : ℝ} (hab : 1 < a)
    (hf : (fun n ↦ (f n)⁻¹) =O[cofinite] fun n ↦ (|(n : ℝ)| ^ a)⁻¹) :
    Summable fun n ↦ (f n)⁻¹ :=
  summable_of_isBigO
    ((Real.summable_abs_int_rpow hab).congr fun b ↦ Real.rpow_neg (abs_nonneg ↑b) a) hf

/-- For `z : ℂ` the function `d : ℤ ↦ ((c z + d) ^ k)⁻¹` is Summable for `2 ≤ k`. -/
/-
**EisensteinSeries.linear_right_summable** 是 Mathlib 中的一个引理，位于命名空间 `EisensteinSe
ries`。
形式化陈述：linear_right_summable (z : Complex) (c : Int) {k : Int} (hk : 2 <= k) : Su
mmable fun d : Int => ((c * z + d) ^ k)⁻¹
参数：z : Complex；c : Int；hk : 2 <= k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `EisensteinSeries.summable_inv_of_isBigO_rpow_inv`：summable_inv_of_isBigO
_rpow_inv {α : Type*} [NormedField α] [CompleteSpace α] {f : Int -> α} {a : Real
} (hab : 1 < a) (hf : (fun n => (f n)⁻…
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftIntNatCastLeOfNat`：CanLift ℤ ℕ (fun n => ↑n) fun x => 0 ≤ x

--- 原说明 ---
For `z : ℂ` the function `d : ℤ ↦ ((c z + d) ^ k)⁻¹` is Summable for `2 ≤ k`.
-/
lemma linear_right_summable (z : ℂ) (c : ℤ) {k : ℤ} (hk : 2 ≤ k) :
    Summable fun d : ℤ ↦ ((c * z + d) ^ k)⁻¹ := by
  apply summable_inv_of_isBigO_rpow_inv (a := k) (by norm_cast)
  lift k to ℕ using by lia
  grind [(linear_inv_isBigO_right c z).abs_right.pow k,
    zpow_natCast, Int.cast_natCast, Real.rpow_natCast, ← inv_pow]

/-- For `z : ℂ` the function `c : ℤ ↦ ((c z + d) ^ k)⁻¹` is Summable for `2 ≤ k`. -/
/-
**EisensteinSeries.linear_left_summable** 是 Mathlib 中的一个引理，位于命名空间 `EisensteinSer
ies`。
形式化陈述：linear_left_summable {z : Complex} (hz : z != 0) (d : Int) {k : Int} (hk :
 2 <= k) : Summable fun c : Int => ((c * z + d) ^ k)⁻¹
参数：hz : z != 0；d : Int；hk : 2 <= k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `EisensteinSeries.summable_inv_of_isBigO_rpow_inv`：summable_inv_of_isBigO
_rpow_inv {α : Type*} [NormedField α] [CompleteSpace α] {f : Int -> α} {a : Real
} (hab : 1 < a) (hf : (fun n => (f n)⁻…
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftIntNatCastLeOfNat`：CanLift ℤ ℕ (fun n => ↑n) fun x => 0 ≤ x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
· 使用定理 `Asymptotics.IsBigO.pow`：∀ {α : Type u_1} {R : Type u_13} [inst : Seminor
medRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   {l : Filte
r α} [NormOn…
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Asymptotics.IsBigO.abs_right`：∀ {α : Type u_1} {E : Type u_3} [inst : No
rm E] {f : α → E} {l : Filter α} {u : α → ℝ},   f =O[l] u → f =O[l] fun x => |u 
x|
· 使用引理 `EisensteinSeries.linear_inv_isBigO_left`：linear_inv_isBigO_left (d : Int
) {z : Complex} (hz : z != 0) : (fun (c : Int) => (c * z + d)⁻¹) =O[cofinite] fu
n n => (n : Real)⁻¹

--- 原说明 ---
For `z : ℂ` the function `c : ℤ ↦ ((c z + d) ^ k)⁻¹` is Summable for `2 ≤ k`.
-/
lemma linear_left_summable {z : ℂ} (hz : z ≠ 0) (d : ℤ) {k : ℤ} (hk : 2 ≤ k) :
    Summable fun c : ℤ ↦ ((c * z + d) ^ k)⁻¹ := by
  apply summable_inv_of_isBigO_rpow_inv (a := k) (by norm_cast)
  lift k to ℕ using (by lia)
  simp only [zpow_natCast, Int.cast_natCast, Real.rpow_natCast, ← inv_pow, ← abs_inv]
  apply (linear_inv_isBigO_left d hz).abs_right.pow
/-
**EisensteinSeries.summable_linear_sub_mul_linear_add** 是 Mathlib 中的一个引理，位于命名空间 
`EisensteinSeries`。
形式化陈述：summable_linear_sub_mul_linear_add (z : Complex) (c₁ c₂ : Int) : Summable 
fun n : Int => ((c₁ * z - n) * (c₂ * z + n))⁻¹
参数：z : Complex；c₁ c₂ : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `EisensteinSeries.summable_inv_of_isBigO_rpow_inv`：summable_inv_of_isBigO
_rpow_inv {α : Type*} [NormedField α] [CompleteSpace α] {f : Int -> α} {a : Real
} (hab : 1 < a) (hf : (fun n => (f n)⁻…
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.cofinite_eq`：cofinite_eq : (cofinite : Filter Int) = atBot ⊔ atTop
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用引理 `Real.rpow_ofNat`：rpow_ofNat (x : Real) (n : Nat) [n.AtLeastTwo] : x ^ (o
fNat(n) : Real) = x ^ (ofNat(n) : Nat)
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `abs_mul_abs_self`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder
 α] (a : α), |a| * |a| = a * a
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用引理 `inv_neg`：inv_neg : (-a)⁻¹ = -a⁻¹
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `Asymptotics.IsBigO.mul`：∀ {α : Type u_1} {R : Type u_13} [inst : Seminor
medRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   {l : Filte
r α} {f₁ f₂ …
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用引理 `EisensteinSeries.linear_inv_isBigO_right`：linear_inv_isBigO_right (c : I
nt) (z : Complex) : (fun (d : Int) => (c * z + d)⁻¹) =O[cofinite] fun n => (n : 
Real)⁻¹
· 使用定理 `Asymptotics.IsBigO.comp_neg_int`：∀ {E : Type u_3} {F : Type u_4} [inst :
 Norm E] [inst_1 : Norm F] {f : ℤ → E} {g : ℤ → F},   f =O[Filter.cofinite] g → 
(fun n => f (-n)) =O[…
-/
lemma summable_linear_sub_mul_linear_add (z : ℂ) (c₁ c₂ : ℤ) :
    Summable fun n : ℤ ↦ ((c₁ * z - n) * (c₂ * z + n))⁻¹ := by
  apply summable_inv_of_isBigO_rpow_inv (a := 2) (by norm_cast)
  simpa [pow_two] using! (linear_inv_isBigO_right c₂ z).mul
      (linear_inv_isBigO_right c₁ z).comp_neg_int
/-
**EisensteinSeries.summable_linear_right_add_one_mul_linear_right** 是 Mathlib 中的
一个引理，位于命名空间 `EisensteinSeries`。
形式化陈述：summable_linear_right_add_one_mul_linear_right (z : Complex) (c₁ c₂ : Int)
 : Summable fun n : Int => ((c₁ * z + n + 1) * (c₂ * z + n))⁻¹
参数：z : Complex；c₁ c₂ : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `EisensteinSeries.summable_inv_of_isBigO_rpow_inv`：summable_inv_of_isBigO
_rpow_inv {α : Type*} [NormedField α] [CompleteSpace α] {f : Int -> α} {a : Real
} (hab : 1 < a) (hf : (fun n => (f n)⁻…
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.cofinite_eq`：cofinite_eq : (cofinite : Filter Int) = atBot ⊔ atTop
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用引理 `Real.rpow_ofNat`：rpow_ofNat (x : Real) (n : Nat) [n.AtLeastTwo] : x ^ (o
fNat(n) : Real) = x ^ (ofNat(n) : Nat)
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `abs_mul_abs_self`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder
 α] (a : α), |a| * |a| = a * a
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Asymptotics.IsBigO.mul`：∀ {α : Type u_1} {R : Type u_13} [inst : Seminor
medRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   {l : Filte
r α} {f₁ f₂ …
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用引理 `EisensteinSeries.linear_inv_isBigO_right`：linear_inv_isBigO_right (c : I
nt) (z : Complex) : (fun (d : Int) => (c * z + d)⁻¹) =O[cofinite] fun n => (n : 
Real)⁻¹
· 使用引理 `EisensteinSeries.linear_inv_isBigO_right_add`：linear_inv_isBigO_right_ad
d (c e : Int) (z : Complex) : (fun (d : Int) => (c * z + d + e)⁻¹) =O[cofinite] 
fun n => (n : Real)⁻¹
-/
lemma summable_linear_right_add_one_mul_linear_right (z : ℂ) (c₁ c₂ : ℤ) :
    Summable fun n : ℤ ↦ ((c₁ * z + n + 1) * (c₂ * z + n))⁻¹ := by
  apply summable_inv_of_isBigO_rpow_inv (a := 2) (by norm_cast)
  simpa [pow_two] using (linear_inv_isBigO_right c₂ z).mul
    (linear_inv_isBigO_right_add c₁ 1 z)
/-
**EisensteinSeries.summable_linear_left_mul_linear_left** 是 Mathlib 中的一个引理，位于命名空
间 `EisensteinSeries`。
形式化陈述：summable_linear_left_mul_linear_left {z : Complex} (hz : z != 0) (c₁ c₂ : 
Int) : Summable fun n : Int => ((n * z + c₁) * (n * z + c₂))⁻¹
参数：hz : z != 0；c₁ c₂ : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `EisensteinSeries.summable_inv_of_isBigO_rpow_inv`：summable_inv_of_isBigO
_rpow_inv {α : Type*} [NormedField α] [CompleteSpace α] {f : Int -> α} {a : Real
} (hab : 1 < a) (hf : (fun n => (f n)⁻…
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.rpow_two`：rpow_two (x : Real) : x ^ (2 : Real) = x ^ 2
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `abs_mul_abs_self`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder
 α] (a : α), |a| * |a| = a * a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.cofinite_eq`：cofinite_eq : (cofinite : Filter Int) = atBot ⊔ atTop
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `Asymptotics.IsBigO.mul`：∀ {α : Type u_1} {R : Type u_13} [inst : Seminor
medRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   {l : Filte
r α} {f₁ f₂ …
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用引理 `EisensteinSeries.linear_inv_isBigO_left`：linear_inv_isBigO_left (d : Int
) {z : Complex} (hz : z != 0) : (fun (c : Int) => (c * z + d)⁻¹) =O[cofinite] fu
n n => (n : Real)⁻¹
-/
lemma summable_linear_left_mul_linear_left {z : ℂ} (hz : z ≠ 0) (c₁ c₂ : ℤ) :
    Summable fun n : ℤ ↦ ((n * z + c₁) * (n * z + c₂))⁻¹ := by
  apply summable_inv_of_isBigO_rpow_inv (a := 2) (by norm_cast)
  simp only [Real.rpow_two, abs_mul_abs_self, pow_two]
  simpa using (linear_inv_isBigO_left c₂ hz).mul (linear_inv_isBigO_left c₁ hz)
/-
**EisensteinSeries.aux_isBigO_linear** 是 Mathlib 中的一个引理，位于命名空间 `EisensteinSeries
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma aux_isBigO_linear (z : ℍ) (a b : ℤ) :
    (fun (m : Fin 2 → ℤ) ↦ ((m 0 + a : ℂ) * z + m 1 + b)⁻¹) =O[cofinite]
    fun (m : Fin 2 → ℤ) ↦ ‖![m 0 + a, m 1 + b]‖⁻¹ := by
  rw [Asymptotics.isBigO_iff]
  have h0 : z ∈ verticalStrip |z.re| (z.im) := by simp [mem_verticalStrip_iff]
  use ‖r ⟨⟨|z.re|, z.im⟩, z.2⟩‖⁻¹
  filter_upwards with m
  apply le_trans (by simpa [Real.rpow_neg_one, add_assoc] using
    summand_bound_of_mem_verticalStrip zero_le_one ![m 0 + a, m 1 + b] z.2 h0)
  simp [abs_of_pos (r_pos _)]
/-
**EisensteinSeries.isLittleO_const_left_of_properSpace_of_discreteTopology** 是 M
athlib 中的一个引理，位于命名空间 `EisensteinSeries`。
形式化陈述：isLittleO_const_left_of_properSpace_of_discreteTopology {α : Type*} (a : α
) [NormedAddCommGroup α] [DiscreteTopology α] [ProperSpace α] : (fun _ : α => a)
 =o[cofinite] (‖·‖)
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用定理 `tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding`：∀ {E : Type u_2} 
[inst : SeminormedAddGroup E] {X : Type u_5} [inst_1 : TopologicalSpace X] [Disc
reteTopology X]   [ProperSpace E] {e : X → …
· 使用定理 `Topology.IsClosedEmbedding.id`：∀ {X : Type u_1} [inst : TopologicalSpace
 X], Topology.IsClosedEmbedding id
-/
lemma isLittleO_const_left_of_properSpace_of_discreteTopology
    {α : Type*} (a : α) [NormedAddCommGroup α] [DiscreteTopology α]
    [ProperSpace α] : (fun _ : α ↦ a) =o[cofinite] (‖·‖) := by
  simpa [isLittleO_const_left, Function.comp_def] using
    .inr <| tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding IsClosedEmbedding.id
/-
**EisensteinSeries.vec_add_const_isTheta** 是 Mathlib 中的一个引理，位于命名空间 `EisensteinSe
ries`。
形式化陈述：vec_add_const_isTheta (a b : Int) : (fun (m : Fin 2 -> Int) => ‖![m 0 + a,
 m 1 + b]‖⁻¹) =Θ[cofinite] (fun m => ‖m‖⁻¹)
参数：a b : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.ofFn_inj`：ofFn_inj {n : Nat} {f g : Fin n -> α} : ofFn f = ofFn g ↔
 f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Asymptotics.IsTheta.add_isLittleO`：∀ {α : Type u_1} {F : Type u_4} {E' :
 Type u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {l : Filter α}  
 {f₁ f₂ : α → E'} {g : …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Asymptotics.isTheta_norm_left`：isTheta_norm_left : (fun x => ‖f' x‖) =Θ[
l] g ↔ f' =Θ[l] g
· 使用定理 `Asymptotics.isTheta_refl`：isTheta_refl (f : α -> E) (l : Filter α) : f =
Θ[l] f
· 使用引理 `EisensteinSeries.isLittleO_const_left_of_properSpace_of_discreteTopology
`：isLittleO_const_left_of_properSpace_of_discreteTopology {α : Type*} (a : α) [N
ormedAddCommGroup α] [DiscreteTopology α] [ProperSpace α] : (f…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instDiscreteTopologyInt`：DiscreteTopology ℤ
· 使用定理 `Int.instProperSpace`：ProperSpace ℤ
-/
lemma vec_add_const_isTheta (a b : ℤ) :
    (fun (m : Fin 2 → ℤ) => ‖![m 0 + a, m 1 + b]‖⁻¹) =Θ[cofinite] (fun m => ‖m‖⁻¹) := by
  have (x : Fin 2 → ℤ) : ![x 0 + a, x 1 + b] = x + ![a, b] := List.ofFn_inj.mp rfl
  simpa only [isTheta_inv, isTheta_norm_left, this] using! (IsTheta.add_isLittleO
  (by rw [← isTheta_norm_left]) (isLittleO_const_left_of_properSpace_of_discreteTopology ![a, b]))
/-
**EisensteinSeries.isBigO_linear_add_const_vec** 是 Mathlib 中的一个引理，位于命名空间 `Eisens
teinSeries`。
形式化陈述：isBigO_linear_add_const_vec (z : ℍ) (a b : Int) : (fun m : (Fin 2 -> Int) 
=> (((m 0 : Complex) + a) * z + m 1 + b)⁻¹) =O[cofinite] (fun m => ‖m‖⁻¹)
参数：z : ℍ；a b : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.trans`：∀ {α : Type u_1} {E : Type u_3} {G : Type u_5}
 {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : SeminormedAddComm
Group F'] {l :…
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `_private.Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable.0.E
isensteinSeries.aux_isBigO_linear`：∀ (z : UpperHalfPlane) (a b : ℤ),   (fun m =>
 ((↑(m 0) + ↑a) * ↑z + ↑(m 1) + ↑b)⁻¹) =O[Filter.cofinite] fun m => ‖![m 0 + a, 
m 1 + b]‖⁻¹
· 使用定理 `Asymptotics.IsTheta.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_
4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},   f
 =Θ[l] g → f =O[…
· 使用引理 `EisensteinSeries.vec_add_const_isTheta`：vec_add_const_isTheta (a b : Int
) : (fun (m : Fin 2 -> Int) => ‖![m 0 + a, m 1 + b]‖⁻¹) =Θ[cofinite] (fun m => ‖
m‖⁻¹)
-/
lemma isBigO_linear_add_const_vec (z : ℍ) (a b : ℤ) :
    (fun m : (Fin 2 → ℤ) => (((m 0 : ℂ) + a) * z + m 1 + b)⁻¹) =O[cofinite] (fun m => ‖m‖⁻¹) :=
  (aux_isBigO_linear z a b).trans (vec_add_const_isTheta a b).isBigO

/-- If a function `ℤ² → ℂ` is `O (‖n‖ ^ a)⁻¹` for `2 < a`, then the function is summable. -/
/-
**EisensteinSeries.summable_of_isBigO_rpow_norm** 是 Mathlib 中的一个引理，位于命名空间 `Eisen
steinSeries`。
形式化陈述：summable_of_isBigO_rpow_norm {E : Type*} [NormedAddCommGroup E] [CompleteS
pace E] {f : (Fin 2 -> Int) -> E} {a : Real} (hab : 2 < a) (hf : f =O[cofinite] 
fun n => (‖n‖ ^ a)⁻¹) : Summable f
参数：Fin 2 -> Int；hab : 2 < a；hf : f =O[cofinite] fun n => (‖n‖ ^ a)⁻¹。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `summable_of_isBigO`：summable_of_isBigO {ι E} [SeminormedAddCommGroup E] 
[CompleteSpace E] {f : ι -> E} {g : ι -> Real} (hg : Summable g) (h : f =O[cofin
ite] g) …
· 使用定理 `Summable.congr`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {f g : β → α}   {L : SummationFilter β}, Summable
 f L…
· 使用引理 `EisensteinSeries.summable_one_div_norm_rpow`：summable_one_div_norm_rpow 
{k : Real} (hk : 2 < k) : Summable fun (x : Fin 2 -> Int) => ‖x‖ ^ (-k)
· 使用定理 `Real.rpow_neg`：rpow_neg {x : Real} (hx : 0 <= x) (y : Real) : x ^ (-y) =
 (x ^ y)⁻¹
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖

--- 原说明 ---
If a function `ℤ² → ℂ` is `O (‖n‖ ^ a)⁻¹` for `2 < a`, then the function is summ
able.
-/
lemma summable_of_isBigO_rpow_norm {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {f : (Fin 2 → ℤ) → E} {a : ℝ} (hab : 2 < a)
    (hf : f =O[cofinite] fun n ↦ (‖n‖ ^ a)⁻¹) : Summable f :=
  summable_of_isBigO
    ((summable_one_div_norm_rpow hab).congr fun b ↦ Real.rpow_neg (norm_nonneg b) a) hf

end EisensteinSeries

