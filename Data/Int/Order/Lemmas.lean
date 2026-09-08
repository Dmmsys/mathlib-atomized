/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
module

public import Mathlib.Algebra.Order.Ring.Abs

/-!
# Further lemmas about the integers

The distinction between this file and `Mathlib/Data/Int/Order/Basic.lean` is not particularly clear.
They are separated by now to minimize the porting requirements for tactics during the transition to
mathlib4. Please feel free to reorganize these two files.
-/

public section

open Function Nat

namespace Int

/-! ### nat abs -/

/-
**Int.natAbs_eq_iff_mul_self_eq** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：natAbs_eq_iff_mul_self_eq {a b : Int} : a.natAbs = b.natAbs ↔ a * a = b * 
b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `abs_eq_iff_mul_self_eq`：abs_eq_iff_mul_self_eq : |a| = |b| ↔ a * a = b *
 b
· 使用定理 `Int.abs_eq_natAbs`：∀ (a : ℤ), |a| = ↑a.natAbs
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Int.natCast_inj`：∀ {m n : ℕ}, ↑m = ↑n ↔ m = n

--- 原说明 ---
### nat abs
-/
theorem natAbs_eq_iff_mul_self_eq {a b : ℤ} : a.natAbs = b.natAbs ↔ a * a = b * b := by
  rw [← abs_eq_iff_mul_self_eq, abs_eq_natAbs, abs_eq_natAbs]
  exact Int.natCast_inj.symm
/-
**Int.natAbs_lt_iff_mul_self_lt** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：natAbs_lt_iff_mul_self_lt {a b : Int} : a.natAbs < b.natAbs ↔ a * a < b * 
b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `abs_lt_iff_mul_self_lt`：abs_lt_iff_mul_self_lt : |a| < |b| ↔ a * a < b *
 b
· 使用定理 `Int.abs_eq_natAbs`：∀ (a : ℤ), |a| = ↑a.natAbs
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Int.ofNat_lt`：∀ {n m : ℕ}, ↑n < ↑m ↔ n < m
-/
theorem natAbs_lt_iff_mul_self_lt {a b : ℤ} : a.natAbs < b.natAbs ↔ a * a < b * b := by
  rw [← abs_lt_iff_mul_self_lt, abs_eq_natAbs, abs_eq_natAbs]
  exact Int.ofNat_lt.symm
/-
**Int.natAbs_le_iff_mul_self_le** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：natAbs_le_iff_mul_self_le {a b : Int} : a.natAbs <= b.natAbs ↔ a * a <= b 
* b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `abs_le_iff_mul_self_le`：abs_le_iff_mul_self_le : |a| <= |b| ↔ a * a <= b
 * b
· 使用定理 `Int.abs_eq_natAbs`：∀ (a : ℤ), |a| = ↑a.natAbs
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Int.ofNat_le`：∀ {m n : ℕ}, ↑m ≤ ↑n ↔ m ≤ n
-/
theorem natAbs_le_iff_mul_self_le {a b : ℤ} : a.natAbs ≤ b.natAbs ↔ a * a ≤ b * b := by
  rw [← abs_le_iff_mul_self_le, abs_eq_natAbs, abs_eq_natAbs]
  exact Int.ofNat_le.symm

/-! ### Integer sqrt -/

/-
**Int.abs_le_sqrt** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：abs_le_sqrt {a b : Int} (hn : 0 <= b) : |a| <= b.sqrt ↔ a * a <= b
参数：hn : 0 <= b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `abs_mul_abs_self`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder
 α] (a : α), |a| * |a| = a * a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.eq_natCast_toNat`：∀ {a : ℤ}, a = ↑a.toNat ↔ 0 ≤ a
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Int.sqrt_natCast`：sqrt_natCast (n : Nat) : Int.sqrt (n : Int) = Nat.sqrt
 n
· 使用定理 `Int.natCast_mul`：∀ (n m : ℕ), ↑(n * m) = ↑n * ↑m
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用引理 `Nat.le_sqrt`：le_sqrt : m <= sqrt n ↔ m * m <= n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
### Integer sqrt
-/
theorem abs_le_sqrt {a b : ℤ} (hn : 0 ≤ b) :
    |a| ≤ b.sqrt ↔ a * a ≤ b := by
  rw [← abs_mul_abs_self, eq_natCast_toNat.mpr hn, eq_natCast_toNat.mpr (abs_nonneg a),
    Int.sqrt_natCast, ← Int.natCast_mul, Nat.cast_le, Nat.cast_le, Nat.le_sqrt]
/-
**Int.abs_le_sqrt_iff_sq_le** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：abs_le_sqrt_iff_sq_le {a b : Int} (hn : 0 <= b) : |a| <= b.sqrt ↔ a ^ 2 <=
 b
参数：hn : 0 <= b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.abs_le_sqrt`：abs_le_sqrt {a b : Int} (hn : 0 <= b) : |a| <= b.sqrt ↔
 a * a <= b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
-/
theorem abs_le_sqrt_iff_sq_le {a b : ℤ} (hn : 0 ≤ b) :
    |a| ≤ b.sqrt ↔ a ^ 2 ≤ b :=
  pow_two a ▸ abs_le_sqrt hn

end Int

