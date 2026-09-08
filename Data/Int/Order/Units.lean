/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
module

public import Mathlib.Algebra.Order.Ring.Abs

/-!
# Lemmas about units in `ℤ`, which interact with the order structure.
-/

public section


namespace Int

/-
**Int.isUnit_iff_abs_eq** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：isUnit_iff_abs_eq {x : Int} : IsUnit x ↔ abs x = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Int.isUnit_iff_natAbs_eq`：isUnit_iff_natAbs_eq : IsUnit u ↔ u.natAbs = 1
· 使用定理 `Int.abs_eq_natAbs`：∀ (a : ℤ), |a| = ↑a.natAbs
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.ofNat_one`：↑1 = 1
· 使用定理 `Int.natCast_inj`：∀ {m n : ℕ}, ↑m = ↑n ↔ m = n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isUnit_iff_abs_eq {x : ℤ} : IsUnit x ↔ abs x = 1 := by
  rw [isUnit_iff_natAbs_eq, abs_eq_natAbs, ← Int.ofNat_one, natCast_inj]
/-
**Int.isUnit_sq** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：isUnit_sq {a : Int} (ha : IsUnit a) : a ^ 2 = 1
参数：ha : IsUnit a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用引理 `Int.isUnit_mul_self`：isUnit_mul_self (hu : IsUnit u) : u * u = 1
-/
theorem isUnit_sq {a : ℤ} (ha : IsUnit a) : a ^ 2 = 1 := by rw [sq, isUnit_mul_self ha]

@[simp]
/-
**Int.units_sq** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：units_sq (u : Intˣ) : u ^ 2 = 1
参数：u : Intˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Units.ext_iff`：∀ {α : Type u} [inst : Monoid α] {u v : αˣ}, u = v ↔ ↑u =
 ↑v
· 使用引理 `Units.val_pow_eq_pow_val`：val_pow_eq_pow_val (n : Nat) : ↑(a ^ n) = (a ^
 n : α)
· 使用定理 `Units.val_one`：val_one : ((1 : αˣ) : α) = 1
· 使用定理 `Int.isUnit_sq`：isUnit_sq {a : Int} (ha : IsUnit a) : a ^ 2 = 1
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
-/
theorem units_sq (u : ℤˣ) : u ^ 2 = 1 := by
  rw [Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one, isUnit_sq u.isUnit]

alias units_pow_two := units_sq

@[simp]
/-
**Int.units_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：units_mul_self (u : Intˣ) : u * u = 1
参数：u : Intˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Int.units_sq`：units_sq (u : Intˣ) : u ^ 2 = 1
-/
theorem units_mul_self (u : ℤˣ) : u * u = 1 := by rw [← sq, units_sq]

@[simp]
/-
**Int.units_inv_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：units_inv_eq_self (u : Intˣ) : u⁻¹ = u
参数：u : Intˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_eq_iff_mul_eq_one`：inv_eq_iff_mul_eq_one : a⁻¹ = b ↔ a * b = 1
· 使用定理 `Int.units_mul_self`：units_mul_self (u : Intˣ) : u * u = 1
-/
theorem units_inv_eq_self (u : ℤˣ) : u⁻¹ = u := by rw [inv_eq_iff_mul_eq_one, units_mul_self]
/-
**Int.units_div_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：units_div_eq_mul (u₁ u₂ : Intˣ) : u₁ / u₂ = u₁ * u₂
参数：u₁ u₂ : Intˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Int.units_inv_eq_self`：units_inv_eq_self (u : Intˣ) : u⁻¹ = u
-/
theorem units_div_eq_mul (u₁ u₂ : ℤˣ) : u₁ / u₂ = u₁ * u₂ := by
  rw [div_eq_mul_inv, units_inv_eq_self]

-- `Units.val_mul` is a "wrong turn" for the simplifier, this undoes it and simplifies further
@[simp]
/-
**Int.units_coe_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：units_coe_mul_self (u : Intˣ) : (u * u : Int) = 1
参数：u : Intˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.val_mul`：val_mul : (↑(a * b) : α) = a * b
· 使用定理 `Int.units_mul_self`：units_mul_self (u : Intˣ) : u * u = 1
· 使用定理 `Units.val_one`：val_one : ((1 : αˣ) : α) = 1
-/
theorem units_coe_mul_self (u : ℤˣ) : (u * u : ℤ) = 1 := by
  rw [← Units.val_mul, units_mul_self, Units.val_one]
/-
**Int.neg_one_pow_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：neg_one_pow_ne_zero {n : Nat} : (-1 : Int) ^ n != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem neg_one_pow_ne_zero {n : ℕ} : (-1 : ℤ) ^ n ≠ 0 := by simp
/-
**Int.sq_eq_one_of_sq_lt_four** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：sq_eq_one_of_sq_lt_four {x : Int} (h1 : x ^ 2 < 4) (h2 : x != 0) : x ^ 2 =
 1
参数：h1 : x ^ 2 < 4；h2 : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sq_eq_one_iff`：∀ {R : Type u} [inst : Ring R] {a : R} [NoZeroDivisors R]
, a ^ 2 = 1 ↔ a = 1 ∨ a = -1
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `abs_eq`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrder G
] [IsOrderedAddMonoid G] {a b : G},   0 ≤ b → (|a| = b ↔ a = b ∨ a = -b)
· 使用引理 `zero_le_one'`：zero_le_one' (α) [Zero α] [One α] [LE α] [ZeroLEOneClass α
] : (0 : α) <= 1
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Int.lt_add_one_iff`：∀ {a b : ℤ}, a < b + 1 ↔ a ≤ b
· 使用引理 `abs_lt_of_sq_lt_sq`：abs_lt_of_sq_lt_sq (h : a ^ 2 < b ^ 2) (hb : 0 <= b)
 : |a| < b
· 使用引理 `zero_le_two`：zero_le_two [Preorder α] [ZeroLEOneClass α] [AddLeftMono α]
 : (0 : α) <= 2
· 使用定理 `Int.sub_one_lt_iff`：∀ {m n : ℤ}, m - 1 < n ↔ m ≤ n
· 使用定理 `abs_pos`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [
AddLeftMono α] {a : α}, 0 < |a| ↔ a ≠ 0
-/
theorem sq_eq_one_of_sq_lt_four {x : ℤ} (h1 : x ^ 2 < 4) (h2 : x ≠ 0) : x ^ 2 = 1 :=
  sq_eq_one_iff.mpr
    ((abs_eq (zero_le_one' ℤ)).mp
      (le_antisymm (lt_add_one_iff.mp (abs_lt_of_sq_lt_sq h1 zero_le_two))
        (sub_one_lt_iff.mp (abs_pos.mpr h2))))
/-
**Int.sq_eq_one_of_sq_le_three** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：sq_eq_one_of_sq_le_three {x : Int} (h1 : x ^ 2 <= 3) (h2 : x != 0) : x ^ 2
 = 1
参数：h1 : x ^ 2 <= 3；h2 : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.sq_eq_one_of_sq_lt_four`：sq_eq_one_of_sq_lt_four {x : Int} (h1 : x ^
 2 < 4) (h2 : x != 0) : x ^ 2 = 1
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
-/
theorem sq_eq_one_of_sq_le_three {x : ℤ} (h1 : x ^ 2 ≤ 3) (h2 : x ≠ 0) : x ^ 2 = 1 :=
  sq_eq_one_of_sq_lt_four (lt_of_le_of_lt h1 (lt_add_one (3 : ℤ))) h2
/-
**Int.units_pow_eq_pow_mod_two** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：units_pow_eq_pow_mod_two (u : Intˣ) (n : Nat) : u ^ n = u ^ (n % 2)
参数：u : Intˣ；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.mod_add_div`：∀ (m k : ℕ), m % k + k * (m / k) = m
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `Int.units_sq`：units_sq (u : Intˣ) : u ^ 2 = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem units_pow_eq_pow_mod_two (u : ℤˣ) (n : ℕ) : u ^ n = u ^ (n % 2) := by
  conv =>
    lhs
    rw [← Nat.mod_add_div n 2]
    rw [pow_add, pow_mul, units_sq, one_pow, mul_one]

end Int

