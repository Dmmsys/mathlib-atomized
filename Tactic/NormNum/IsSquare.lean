/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public meta import Batteries.Data.Nat.Basic
public import Mathlib.Tactic.NormNum.GCD

/-!
# `norm_num` extension for `IsSquare`

The extension in this file handles natural, integer, and rational numbers.

## TODO
Add extensions for `ℚ≥0`, `ℝ`, `ℝ≥0`, `ℝ≥0∞`, `ℂ` (or any algebraically closed field?), `ZMod n`.
Probably, these extensions should go to different files.
-/

public meta section

namespace Mathlib.Meta.NormNum
open Qq

/-
**Mathlib.Meta.NormNum.isSquare_nat_of_isNat** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.
Meta.NormNum`。
形式化陈述：isSquare_nat_of_isNat (a n : Nat) (h : IsNat a n) (m : Nat) (hm : m * m = 
n) : IsSquare a
参数：a n : Nat；h : IsNat a n；m : Nat；hm : m * m = n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.out`：∀ {α : Type u} [inst : AddMonoidWithOne 
α] {a : α} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = ↑n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isSquare_nat_of_isNat (a n : ℕ) (h : IsNat a n) (m : ℕ) (hm : m * m = n) :
    IsSquare a :=
  ⟨m, h.1.trans hm.symm⟩

/-- If `m ^ 2 < n < (m + 1) ^ 2`, then `n` is not a square.
We write this condition as `k < n ≤ k + 2 * m`, where `k = m * m`. -/
/-
**Mathlib.Meta.NormNum.not_isSquare_nat_of_isNat** 是 Mathlib 中的一个定理，位于命名空间 `Math
lib.Meta.NormNum`。
形式化陈述：not_isSquare_nat_of_isNat (a n : Nat) (h : IsNat a n) (m k : Nat) (hm : m 
* m = k) (hk₁ : Nat.blt k n) (hk₂ : Nat.ble n (k + 2 * m)) : ¬IsSquare a
参数：a n : Nat；h : IsNat a n；m k : Nat；hm : m * m = k；hk₁ : Nat.blt k n；hk₂ : Nat.
ble n (k + 2 * m)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.pow_le_pow_iff_left`：∀ {a b n : ℕ}, n ≠ 0 → (a ^ n ≤ b ^ n ↔ a ≤ b)
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.add_one_le_iff`：∀ {n m : ℕ}, n + 1 ≤ m ↔ n < m
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.blt_eq`：∀ {x y : ℕ}, (x.blt y = true) = (x < y)
· 使用定理 `Nat.pow_lt_pow_iff_left`：∀ {a b n : ℕ}, n ≠ 0 → (a ^ n < b ^ n ↔ a < b)
· 使用定理 `Nat.ble_eq`：∀ {x y : ℕ}, (x.ble y = true) = (x ≤ y)

--- 原说明 ---
If `m ^ 2 < n < (m + 1) ^ 2`, then `n` is not a square.
We write this condition as `k < n ≤ k + 2 * m`, where `k = m * m`.
-/
theorem not_isSquare_nat_of_isNat (a n : ℕ) (h : IsNat a n) (m k : ℕ) (hm : m * m = k)
    (hk₁ : Nat.blt k n) (hk₂ : Nat.ble n (k + 2 * m)) :
    ¬IsSquare a := by
  rcases h with ⟨rfl⟩
  subst k
  rintro ⟨b, rfl⟩
  simp only [Nat.blt_eq, Nat.ble_eq, ← sq, Nat.pow_lt_pow_iff_left two_ne_zero] at hk₁ hk₂
  rw [← Nat.add_one_le_iff, ← Nat.pow_le_pow_iff_left two_ne_zero] at hk₁
  grind
/-
**Mathlib.Meta.NormNum.iff_isSquare_int_of_isNat** 是 Mathlib 中的一个定理，位于命名空间 `Math
lib.Meta.NormNum`。
形式化陈述：iff_isSquare_int_of_isNat (a : Int) (n : Nat) (h : IsNat a n) : IsSquare n
 ↔ IsSquare a
参数：a : Int；n : Nat；h : IsNat a n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.IsNat.out`：∀ {α : Type u} [inst : AddMonoidWithOne 
α] {a : α} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = ↑n
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem iff_isSquare_int_of_isNat (a : ℤ) (n : ℕ) (h : IsNat a n) : IsSquare n ↔ IsSquare a := by
  simp [h.1, Int.isSquare_natCast_iff]
/-
**Mathlib.Meta.NormNum.iff_isSquare_of_isInt_int** 是 Mathlib 中的一个定理，位于命名空间 `Math
lib.Meta.NormNum`。
形式化陈述：iff_isSquare_of_isInt_int (a : Int) (n : Nat) (h : IsInt a (.negOfNat n)) 
: n = 0 ↔ IsSquare a
参数：a : Int；n : Nat；h : IsInt a (.negOfNat n)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.out`：∀ {α : Type u} [inst : Ring α] {a : α} {
n : ℤ}, Mathlib.Meta.NormNum.IsInt a n → a = ↑n
· 使用定理 `Int.cast_negOfNat`：cast_negOfNat (n : Nat) : ((negOfNat n : Int) : R) = 
-n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
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
-/
theorem iff_isSquare_of_isInt_int (a : ℤ) (n : ℕ) (h : IsInt a (.negOfNat n)) :
    n = 0 ↔ IsSquare a := by
  refine ⟨fun h' ↦ by simp [h.1, h'], fun ⟨b, hb⟩ ↦ ?_⟩
  rw [h.1, Int.cast_negOfNat] at hb
  rcases eq_or_ne b 0 with rfl | hb₀
  · simp_all
  · refine absurd hb (ne_of_lt ?_)
    exact lt_of_le_of_lt (by simp) (mul_self_pos.mpr hb₀)
/-
**Mathlib.Meta.NormNum.iff_isSquare_of_isNat_rat** 是 Mathlib 中的一个定理，位于命名空间 `Math
lib.Meta.NormNum`。
形式化陈述：iff_isSquare_of_isNat_rat (a : Rat) (n : Nat) (h : IsNat a n) : IsSquare n
 ↔ IsSquare a
参数：a : Rat；n : Nat；h : IsNat a n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.IsNat.out`：∀ {α : Type u} [inst : AddMonoidWithOne 
α] {a : α} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = ↑n
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem iff_isSquare_of_isNat_rat (a : ℚ) (n : ℕ) (h : IsNat a n) :
    IsSquare n ↔ IsSquare a := by
  simp [h.1]
/-
**Mathlib.Meta.NormNum.iff_isSquare_of_isInt_rat** 是 Mathlib 中的一个定理，位于命名空间 `Math
lib.Meta.NormNum`。
形式化陈述：iff_isSquare_of_isInt_rat (a : Rat) (n : Nat) (h : IsInt a (.negOfNat n)) 
: n = 0 ↔ IsSquare a
参数：a : Rat；n : Nat；h : IsInt a (.negOfNat n)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.out`：∀ {α : Type u} [inst : Ring α] {a : α} {
n : ℤ}, Mathlib.Meta.NormNum.IsInt a n → a = ↑n
· 使用定理 `Int.cast_negOfNat`：cast_negOfNat (n : Nat) : ((negOfNat n : Int) : R) = 
-n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
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
-/
theorem iff_isSquare_of_isInt_rat (a : ℚ) (n : ℕ) (h : IsInt a (.negOfNat n)) :
    n = 0 ↔ IsSquare a := by
  refine ⟨fun h' ↦ by simp [h.1, h'], fun ⟨b, hb⟩ ↦ ?_⟩
  rw [h.1, Int.cast_negOfNat] at hb
  rcases eq_or_ne b 0 with rfl | hb₀
  · simp_all
  · refine absurd hb (ne_of_lt ?_)
    exact lt_of_le_of_lt (by simp) (mul_self_pos.mpr hb₀)
/-
**Mathlib.Meta.NormNum.isSquare_of_isNNRat_rat** 是 Mathlib 中的一个定理，位于命名空间 `Mathli
b.Meta.NormNum`。
形式化陈述：isSquare_of_isNNRat_rat (a : Rat) (n d : Nat) (hn : IsSquare n) (hd : IsSq
uare d) (ha : IsNNRat a n d) : IsSquare a
参数：a : Rat；n d : Nat；hn : IsSquare n；hd : IsSquare d；ha : IsNNRat a n d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_eq`：∀ {α : Type u_1} [inst : DivisionSem
iring α] {n d : ℕ} {a n' d' : α},   Mathlib.Meta.NormNum.IsNNRat a n d → ↑n = n'
 → ↑d = d' → a = n' / d'
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `div_mul_div_comm`：div_mul_div_comm : a / b * (c / d) = a * c / (b * d)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isSquare_of_isNNRat_rat (a : ℚ) (n d : ℕ) (hn : IsSquare n) (hd : IsSquare d)
    (ha : IsNNRat a n d) : IsSquare a := by
  rcases hn with ⟨n, rfl⟩
  rcases hd with ⟨d, rfl⟩
  use n / d
  simp [ha.to_eq, div_mul_div_comm]
/-
**Mathlib.Meta.NormNum.not_isSquare_of_isNNRat_rat_of_num** 是 Mathlib 中的一个定理，位于命
名空间 `Mathlib.Meta.NormNum`。
形式化陈述：not_isSquare_of_isNNRat_rat_of_num (a : Rat) (n d : Nat) (hn : ¬IsSquare n
) (hnd : n.Coprime d) (ha : IsNNRat a n d) : ¬IsSquare a
参数：a : Rat；n d : Nat；hn : ¬IsSquare n；hnd : n.Coprime d；ha : IsNNRat a n d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_eq`：∀ {α : Type u_1} [inst : DivisionSem
iring α] {n d : ℕ} {a n' d' : α},   Mathlib.Meta.NormNum.IsNNRat a n d → ↑n = n'
 → ↑d = d' → a = n' / d'
· 使用定理 `Rat.isSquare_iff`：isSquare_iff {q : Rat} : IsSquare q ↔ IsSquare q.num ∧
 IsSquare q.den
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Rat.num_div_eq_of_coprime`：num_div_eq_of_coprime {a b : Int} (hb0 : 0 < 
b) (h : Nat.Coprime a.natAbs b.natAbs) : (a / b : Rat).num = a
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.gcd_zero_right`：∀ (n : ℕ), n.gcd 0 = n
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
-/
theorem not_isSquare_of_isNNRat_rat_of_num (a : ℚ) (n d : ℕ) (hn : ¬IsSquare n)
    (hnd : n.Coprime d) (ha : IsNNRat a n d) : ¬IsSquare a := by
  rw [ha.to_eq rfl rfl, Rat.isSquare_iff, ← Int.cast_natCast n, ← Int.cast_natCast d,
    Rat.num_div_eq_of_coprime]
  · simp [hn]
  · contrapose! hnd
    have : n ≠ 1 := by rintro rfl; simp at hn
    simp_all
  · simpa
/-
**Mathlib.Meta.NormNum.not_isSquare_of_isNNRat_rat_of_den** 是 Mathlib 中的一个定理，位于命
名空间 `Mathlib.Meta.NormNum`。
形式化陈述：not_isSquare_of_isNNRat_rat_of_den (a : Rat) (n d : Nat) (hd : ¬IsSquare d
) (hnd : n.Coprime d) (ha : IsNNRat a n d) : ¬IsSquare a
参数：a : Rat；n d : Nat；hd : ¬IsSquare d；hnd : n.Coprime d；ha : IsNNRat a n d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_eq`：∀ {α : Type u_1} [inst : DivisionSem
iring α] {n d : ℕ} {a n' d' : α},   Mathlib.Meta.NormNum.IsNNRat a n d → ↑n = n'
 → ↑d = d' → a = n' / d'
· 使用定理 `Rat.isSquare_iff`：isSquare_iff {q : Rat} : IsSquare q ↔ IsSquare q.num ∧
 IsSquare q.den
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Int.isSquare_natCast_iff`：isSquare_natCast_iff {n : Nat} : IsSquare (n :
 Int) ↔ IsSquare n
· 使用定理 `Rat.den_div_eq_of_coprime`：den_div_eq_of_coprime {a b : Int} (hb0 : 0 < 
b) (h : Nat.Coprime a.natAbs b.natAbs) : ((a / b : Rat).den : Int) = b
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.gcd_zero_right`：∀ (n : ℕ), n.gcd 0 = n
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem not_isSquare_of_isNNRat_rat_of_den (a : ℚ) (n d : ℕ) (hd : ¬IsSquare d) (hnd : n.Coprime d)
    (ha : IsNNRat a n d) : ¬IsSquare a := by
  rw [ha.to_eq rfl rfl, Rat.isSquare_iff, ← Int.cast_natCast n, ← Int.cast_natCast d,
    ← Int.isSquare_natCast_iff (n := Rat.den _), Rat.den_div_eq_of_coprime]
  · simp [hd]
  · contrapose! hnd
    simp_all
  · simpa
/-
**Mathlib.Meta.NormNum.not_isSquare_of_isRat_neg** 是 Mathlib 中的一个定理，位于命名空间 `Math
lib.Meta.NormNum`。
形式化陈述：not_isSquare_of_isRat_neg (a : Rat) (n d : Nat) (hn : n != 0) (hd : d != 0
) (ha : IsRat a (Int.negOfNat n) d) : ¬IsSquare a
参数：a : Rat；n d : Nat；hn : n != 0；hd : d != 0；ha : IsRat a (Int.negOfNat n) d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.IsRat.neg_to_eq`：∀ {α : Type u_1} [inst : DivisionR
ing α] {n d : ℕ} {a n' d' : α},   Mathlib.Meta.NormNum.IsRat a (Int.negOfNat n) 
d → ↑n = n' → ↑d = d' → a …
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `Left.neg_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [Ad
dLeftStrictMono α] {a : α}, -a < 0 ↔ 0 < a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用引理 `mul_self_nonneg`：mul_self_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLe
ftMono R] (a : R) : 0 <= a * a
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
-/
theorem not_isSquare_of_isRat_neg (a : ℚ) (n d : ℕ) (hn : n ≠ 0) (hd : d ≠ 0)
    (ha : IsRat a (Int.negOfNat n) d) : ¬IsSquare a := by
  rw [ha.neg_to_eq rfl rfl]
  rintro ⟨q, hq⟩
  refine absurd hq (ne_of_lt ?_)
  calc
    -(n / d : ℚ) < 0 := by rw [Left.neg_neg_iff]; apply div_pos <;> simpa [Nat.pos_iff_ne_zero]
    _ ≤ q * q := mul_self_nonneg _

open Lean

/-- `norm_num` extension for `IsSquare` on `ℕ`. -/
@[norm_num @IsSquare ℕ _ _]
/-
**Mathlib.Meta.NormNum.evalIsSquareNat** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.N
ormNum`。
形式化陈述：evalIsSquareNat : NormNumExt where eval {u αP} e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`norm_num` extension for `IsSquare` on `ℕ`.
-/
def evalIsSquareNat : NormNumExt where eval {u αP} e := do
  match u, αP, e with
  | 0, ~q(Prop), ~q(@IsSquare ℕ $mulN $a) => do
    let ⟨n, pa⟩ ← deriveNat (u := 0) (α := q(ℕ)) a q(inferInstance)
    let m := Nat.sqrt n.natLit!
    if m * m = n.natLit! then
      have em : Q(ℕ) := mkRawNatLit m
      have hm : Q($em * $em = $n) := (q(Eq.refl $n) : Expr)
      assertInstancesCommute
      return .isTrue (x := q(IsSquare $a)) q(isSquare_nat_of_isNat $a $n $pa $em $hm)
    else
      have em : Q(ℕ) := mkRawNatLit m
      have ek : Q(ℕ) := mkRawNatLit (m * m)
      have hm : Q($em * $em = $ek) := (q(Eq.refl $ek) : Expr)
      have hk₁ : Q(Nat.blt $ek $n) := (q(Eq.refl true) : Expr)
      have hk₂ : Q(Nat.ble $n ($ek + 2 * $em)) := (q(Eq.refl true) : Expr)
      assertInstancesCommute
      return .isFalse q(not_isSquare_nat_of_isNat $a $n $pa $em $ek $hm $hk₁ $hk₂)
  | _ => failure

/-- `norm_num` extension for `IsSquare` on `ℤ`. -/
@[norm_num @IsSquare ℤ _ _]
/-
**Mathlib.Meta.NormNum.evalIsSquareInt** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.N
ormNum`。
形式化陈述：evalIsSquareInt : NormNumExt where eval {u αP} e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`norm_num` extension for `IsSquare` on `ℤ`.
-/
def evalIsSquareInt : NormNumExt where eval {u αP} e := do
  match u, αP, e with
  | 0, ~q(Prop), ~q(@IsSquare ℤ $mulZ $a) => do
    match ← derive a with
    | .isNat sa n pa => do
      assertInstancesCommute
      let ⟨b, pb⟩ ← deriveBoolOfIff q(IsSquare $n) q(IsSquare $a)
        q(iff_isSquare_int_of_isNat $a $n $pa)
      return .ofBoolResult pb
    | .isNegNat sa n pa => do
      assertInstancesCommute
      let ⟨b, pb⟩ ← deriveBoolOfIff q($n = 0) q(IsSquare $a) q(iff_isSquare_of_isInt_int $a $n $pa)
      return .ofBoolResult pb
    | _ => failure
  | _ => failure

/-- `norm_num` extension for `IsSquare` on `ℚ`. -/
@[norm_num @IsSquare ℚ _ _]
/-
**Mathlib.Meta.NormNum.evalIsSquareRat** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.N
ormNum`。
形式化陈述：evalIsSquareRat : NormNumExt where eval {u αP} e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`norm_num` extension for `IsSquare` on `ℚ`.
-/
def evalIsSquareRat : NormNumExt where eval {u αP} e := do
  match u, αP, e with
  | 0, ~q(Prop), ~q(@IsSquare ℚ $mulQ $a) => do
    match ← derive a with
    | .isNat sa n pa => do
      assertInstancesCommute
      let ⟨b, pb⟩ ← deriveBoolOfIff q(IsSquare $n) q(IsSquare $a)
        q(iff_isSquare_of_isNat_rat $a $n $pa)
      return .ofBoolResult pb
    | .isNegNat sa n pa => do
      assertInstancesCommute
      let ⟨b, pb⟩ ← deriveBoolOfIff q($n = 0) q(IsSquare $a) q(iff_isSquare_of_isInt_rat $a $n $pa)
      return .ofBoolResult pb
    | .isNNRat sQ q n d pa => do
      -- We make sure to avoid proving `Nat.Coprime $n $d` unless we need to.
      -- Also, we do not derive `IsSquare $d` unless `$n` is a square
      match ← deriveBool q(IsSquare $n) with
      | .mk true pn =>
        match ← deriveBool q(IsSquare $d) with
        | .mk true pd =>
          assertInstancesCommute
          return .isTrue q(isSquare_of_isNNRat_rat $a $n $d $pn $pd $pa)
        | .mk false pd =>
          let ⟨e, he⟩ := proveNatGCD n d
          have : $e =Q 1 := ⟨⟩
          assertInstancesCommute
          return .isFalse q(not_isSquare_of_isNNRat_rat_of_den $a $n $d $pd $he $pa)
      | .mk false pn =>
        let ⟨e, he⟩ := proveNatGCD n d
        have : $e =Q 1 := ⟨⟩
        assertInstancesCommute
        return .isFalse q(not_isSquare_of_isNNRat_rat_of_num $a $n $d $pn $he $pa)
    | .isNegNNRat sQ q n d pa => do
      match ← deriveBool q($n = 0), ← deriveBool q($d = 0) with
      | .mk false pn, .mk false pd =>
        assertInstancesCommute
        return .isFalse q(not_isSquare_of_isRat_neg $a $n $d $pn $pd $pa)
      | _, _ => failure
    | _ => failure
  | _ => failure

end Mathlib.Meta.NormNum

