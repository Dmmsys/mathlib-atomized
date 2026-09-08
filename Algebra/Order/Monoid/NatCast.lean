/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl, Yuyang Zhao
-/
module

public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Data.Nat.Cast.Defs

/-!
# Order of numerals in an `AddMonoidWithOne`.
-/

public section

variable {α : Type*}

open Function

/-
**lt_add_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLEOneClass α] [N
eZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
参数：1 : α；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_add_of_pos_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : 
LT α] [AddLeftStrictMono α] (a : α) {b : α}, 0 < b → a < a + b
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
-/
lemma lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLEOneClass α]
    [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1 :=
  lt_add_of_pos_right _ zero_lt_one
/-
**lt_one_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lt_one_add [One α] [AddZeroClass α] [PartialOrder α] [ZeroLEOneClass α] [N
eZero (1 : α)] [AddRightStrictMono α] (a : α) : a < 1 + a
参数：1 : α；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_add_of_pos_left`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : L
T α] [AddRightStrictMono α] (a : α) {b : α}, 0 < b → a < b + a
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
-/
lemma lt_one_add [One α] [AddZeroClass α] [PartialOrder α] [ZeroLEOneClass α]
    [NeZero (1 : α)] [AddRightStrictMono α] (a : α) : a < 1 + a :=
  lt_add_of_pos_left _ zero_lt_one

variable [AddMonoidWithOne α]
/-
**zero_le_two** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zero_le_two [Preorder α] [ZeroLEOneClass α] [AddLeftMono α] : (0 : α) <= 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_add_one_eq_two`：one_add_one_eq_two [AddMonoidWithOne R] : 1 + 1 = (2
 : R)
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
-/
lemma zero_le_two [Preorder α] [ZeroLEOneClass α] [AddLeftMono α] :
    (0 : α) ≤ 2 := by
  rw [← one_add_one_eq_two]
  exact add_nonneg zero_le_one zero_le_one
/-
**zero_le_three** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zero_le_three [Preorder α] [ZeroLEOneClass α] [AddLeftMono α] : (0 : α) <=
 3
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_add_one_eq_three`：two_add_one_eq_three [AddMonoidWithOne R] : 2 + 1 
= (3 : R)
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用引理 `zero_le_two`：zero_le_two [Preorder α] [ZeroLEOneClass α] [AddLeftMono α]
 : (0 : α) <= 2
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
-/
lemma zero_le_three [Preorder α] [ZeroLEOneClass α] [AddLeftMono α] :
    (0 : α) ≤ 3 := by
  rw [← two_add_one_eq_three]
  exact add_nonneg zero_le_two zero_le_one
/-
**zero_le_four** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zero_le_four [Preorder α] [ZeroLEOneClass α] [AddLeftMono α] : (0 : α) <= 
4
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `three_add_one_eq_four`：three_add_one_eq_four [AddMonoidWithOne R] : 3 + 
1 = (4 : R)
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用引理 `zero_le_three`：zero_le_three [Preorder α] [ZeroLEOneClass α] [AddLeftMon
o α] : (0 : α) <= 3
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
-/
lemma zero_le_four [Preorder α] [ZeroLEOneClass α] [AddLeftMono α] :
    (0 : α) ≤ 4 := by
  rw [← three_add_one_eq_four]
  exact add_nonneg zero_le_three zero_le_one
/-
**one_le_two** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：one_le_two [LE α] [ZeroLEOneClass α] [AddLeftMono α] : (1 : α) <= 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `add_le_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [AddLe
ftMono α] {b c : α}, b ≤ c → ∀ (a : α), a + b ≤ a + c
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `one_add_one_eq_two`：one_add_one_eq_two [AddMonoidWithOne R] : 1 + 1 = (2
 : R)
-/
lemma one_le_two [LE α] [ZeroLEOneClass α] [AddLeftMono α] :
    (1 : α) ≤ 2 :=
  calc (1 : α) = 1 + 0 := (add_zero 1).symm
     _ ≤ 1 + 1 := by gcongr; exact zero_le_one
     _ = 2 := one_add_one_eq_two
/-
**one_le_two'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：one_le_two' [LE α] [ZeroLEOneClass α] [AddRightMono α] : (1 : α) <= 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_le_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [i : Ad
dRightMono α] {b c : α}, b ≤ c → ∀ (a : α), b + a ≤ c + a
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `one_add_one_eq_two`：one_add_one_eq_two [AddMonoidWithOne R] : 1 + 1 = (2
 : R)
-/
lemma one_le_two' [LE α] [ZeroLEOneClass α] [AddRightMono α] :
    (1 : α) ≤ 2 :=
  calc (1 : α) = 0 + 1 := (zero_add 1).symm
     _ ≤ 1 + 1 := by gcongr; exact zero_le_one
     _ = 2 := one_add_one_eq_two

section
variable [PartialOrder α] [ZeroLEOneClass α] [NeZero (1 : α)]

section
variable [AddLeftMono α]

/-- See `zero_lt_two'` for a version with the type explicit. -/
/-
**zero_lt_two** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : PartialOrder α] [Ze
roLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用引理 `one_le_two`：one_le_two [LE α] [ZeroLEOneClass α] [AddLeftMono α] : (1 : 
α) <= 2

--- 原说明 ---
See `zero_lt_two'` for a version with the type explicit.
-/
@[simp] lemma zero_lt_two : (0 : α) < 2 := zero_lt_one.trans_le one_le_two

/-- See `zero_lt_three'` for a version with the type explicit. -/
/-
**zero_lt_three** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : PartialOrder α] [Ze
roLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 3
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_add_one_eq_three`：two_add_one_eq_three [AddMonoidWithOne R] : 2 + 1 
= (3 : R)
· 使用定理 `lt_add_of_lt_of_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1
 : Preorder α] [AddLeftMono α] {a b c : α}, b < c → 0 ≤ a → b < c + a
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1

--- 原说明 ---
See `zero_lt_three'` for a version with the type explicit.
-/
@[simp] lemma zero_lt_three : (0 : α) < 3 := by
  rw [← two_add_one_eq_three]
  exact lt_add_of_lt_of_nonneg zero_lt_two zero_le_one

/-- See `zero_lt_four'` for a version with the type explicit. -/
/-
**zero_lt_four** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : PartialOrder α] [Ze
roLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 4
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `three_add_one_eq_four`：three_add_one_eq_four [AddMonoidWithOne R] : 3 + 
1 = (4 : R)
· 使用定理 `lt_add_of_lt_of_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1
 : Preorder α] [AddLeftMono α] {a b c : α}, b < c → 0 ≤ a → b < c + a
· 使用定理 `zero_lt_three`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Pa
rtialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 3
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1

--- 原说明 ---
See `zero_lt_four'` for a version with the type explicit.
-/
@[simp] lemma zero_lt_four : (0 : α) < 4 := by
  rw [← three_add_one_eq_four]
  exact lt_add_of_lt_of_nonneg zero_lt_three zero_le_one

variable (α)

/-- See `zero_lt_two` for a version with the type implicit. -/
/-
**zero_lt_two'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zero_lt_two' : (0 : α) < 2
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2

--- 原说明 ---
See `zero_lt_two` for a version with the type implicit.
-/
lemma zero_lt_two' : (0 : α) < 2 := zero_lt_two

/-- See `zero_lt_three` for a version with the type implicit. -/
/-
**zero_lt_three'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zero_lt_three' : (0 : α) < 3
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_lt_three`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Pa
rtialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 3

--- 原说明 ---
See `zero_lt_three` for a version with the type implicit.
-/
lemma zero_lt_three' : (0 : α) < 3 := zero_lt_three

/-- See `zero_lt_four` for a version with the type implicit. -/
/-
**zero_lt_four'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zero_lt_four' : (0 : α) < 4
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_lt_four`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 4

--- 原说明 ---
See `zero_lt_four` for a version with the type implicit.
-/
lemma zero_lt_four' : (0 : α) < 4 := zero_lt_four
/-
**ZeroLEOneClass.neZero.two** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ZeroLEOneClass.neZero.two : NeZero (2 : α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
-/
instance ZeroLEOneClass.neZero.two : NeZero (2 : α) := ⟨zero_lt_two.ne'⟩
/-
**ZeroLEOneClass.neZero.three** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ZeroLEOneClass.neZero.three : NeZero (3 : α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `zero_lt_three`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Pa
rtialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 3
-/
instance ZeroLEOneClass.neZero.three : NeZero (3 : α) := ⟨zero_lt_three.ne'⟩
/-
**ZeroLEOneClass.neZero.four** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ZeroLEOneClass.neZero.four : NeZero (4 : α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `zero_lt_four`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 4
-/
instance ZeroLEOneClass.neZero.four : NeZero (4 : α) := ⟨zero_lt_four.ne'⟩

end

/-
**one_lt_two** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：one_lt_two [AddLeftStrictMono α] : (1 : α) < 2
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_add_one_eq_two`：one_add_one_eq_two [AddMonoidWithOne R] : 1 + 1 = (2
 : R)
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
-/
lemma one_lt_two [AddLeftStrictMono α] : (1 : α) < 2 := by
  rw [← one_add_one_eq_two]
  exact lt_add_one _

end

alias two_pos := zero_lt_two

alias three_pos := zero_lt_three

alias four_pos := zero_lt_four

