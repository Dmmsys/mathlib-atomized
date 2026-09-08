/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.NeZero
public import Mathlib.Order.Hom.Basic

/-!
# Cast of natural numbers: lemmas about order

-/

@[expose] public section

assert_not_exists IsOrderedMonoid

variable {α : Type*}

namespace Nat
variable [AddMonoidWithOne α] [PartialOrder α]
variable [AddLeftMono α] [ZeroLEOneClass α]

@[gcongr, mono]
/-
**Nat.mono_cast** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：mono_cast : Monotone (Nat.cast : Nat -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `monotone_nat_of_le_succ`：monotone_nat_of_le_succ {f : Nat -> α} (hf : fo
rall n, f n <= f (n + 1)) : Monotone f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
· 使用定理 `le_add_of_nonneg_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1
 : LE α] [AddLeftMono α] {a b : α}, 0 ≤ b → a ≤ a + b
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
-/
theorem mono_cast : Monotone (Nat.cast : ℕ → α) :=
  monotone_nat_of_le_succ fun n ↦ by
    rw [Nat.cast_succ]; exact le_add_of_nonneg_right zero_le_one

/-- See also `Nat.cast_nonneg`, specialised to `IsOrderedRing`. -/
@[simp low]
/-
**Nat.cast_nonneg'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：cast_nonneg' (n : Nat) : 0 <= (n : α)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.mono_cast`：mono_cast : Monotone (Nat.cast : Nat -> α)
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0

--- 原说明 ---
See also `Nat.cast_nonneg`, specialised to `IsOrderedRing`.
-/
theorem cast_nonneg' (n : ℕ) : 0 ≤ (n : α) :=
  @Nat.cast_zero α _ ▸ mono_cast (Nat.zero_le n)

/-- See also `Nat.ofNat_nonneg`, specialised to `IsOrderedRing`. -/
@[simp low]
/-
**Nat.ofNat_nonneg'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ofNat_nonneg' (n : Nat) [n.AtLeastTwo] : 0 <= (ofNat(n) : α)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)

--- 原说明 ---
See also `Nat.ofNat_nonneg`, specialised to `IsOrderedRing`.
-/
theorem ofNat_nonneg' (n : ℕ) [n.AtLeastTwo] : 0 ≤ (ofNat(n) : α) := cast_nonneg' n

section Nontrivial

variable [NeZero (1 : α)]

/-
**Nat.cast_add_one_pos** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：cast_add_one_pos (n : Nat) : 0 < (n : α) + 1
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Monotone.imp`：Monotone.imp (hf : Monotone f) (h : a <= b) : f a <= f b
· 使用定理 `Nat.mono_cast`：mono_cast : Monotone (Nat.cast : Nat -> α)
-/
theorem cast_add_one_pos (n : ℕ) : 0 < (n : α) + 1 := by
  apply zero_lt_one.trans_le
  convert! (@mono_cast α _).imp (?_ : 1 ≤ n + 1)
  <;> simp

/-- See also `Nat.cast_pos`, specialised to `IsOrderedRing`. -/
@[simp low]
/-
**Nat.cast_pos'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1

--- 原说明 ---
See also `Nat.cast_pos`, specialised to `IsOrderedRing`.
-/
theorem cast_pos' {n : ℕ} : (0 : α) < n ↔ 0 < n := by cases n <;> simp [cast_add_one_pos]

end Nontrivial

variable [CharZero α] {m n : ℕ}

@[gcongr]
/-
**Nat.strictMono_cast** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：strictMono_cast : StrictMono (Nat.cast : Nat -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.strictMono_of_injective`：Monotone.strictMono_of_injective (h₁ :
 Monotone f) (h₂ : Injective f) : StrictMono f
· 使用定理 `Nat.mono_cast`：mono_cast : Monotone (Nat.cast : Nat -> α)
· 使用定理 `Nat.cast_injective`：cast_injective : Function.Injective (Nat.cast : Nat 
-> R)
-/
theorem strictMono_cast : StrictMono (Nat.cast : ℕ → α) :=
  mono_cast.strictMono_of_injective cast_injective

/-- `Nat.cast : ℕ → α` as an `OrderEmbedding` -/
@[simps! -fullyApplied]
/-
**Nat.castOrderEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：castOrderEmbedding : Nat ↪o α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.strictMono_cast`：strictMono_cast : StrictMono (Nat.cast : Nat -> α)

--- 原说明 ---
`Nat.cast : ℕ → α` as an `OrderEmbedding`
-/
def castOrderEmbedding : ℕ ↪o α :=
  OrderEmbedding.ofStrictMono Nat.cast Nat.strictMono_cast

@[simp, norm_cast]
/-
**Nat.cast_le** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：cast_le : (m : α) <= n ↔ m <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用定理 `Nat.strictMono_cast`：strictMono_cast : StrictMono (Nat.cast : Nat -> α)
-/
theorem cast_le : (m : α) ≤ n ↔ m ≤ n :=
  strictMono_cast.le_iff_le

@[simp, norm_cast, mono]
/-
**Nat.cast_lt** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：cast_lt : (m : α) < n ↔ m < n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用定理 `Nat.strictMono_cast`：strictMono_cast : StrictMono (Nat.cast : Nat -> α)
-/
theorem cast_lt : (m : α) < n ↔ m < n :=
  strictMono_cast.lt_iff_lt

@[simp, norm_cast]
/-
**Nat.one_lt_cast** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：one_lt_cast : 1 < (n : α) ↔ 1 < n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem one_lt_cast : 1 < (n : α) ↔ 1 < n := by rw [← cast_one, cast_lt]

@[simp, norm_cast]
/-
**Nat.one_le_cast** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：one_le_cast : 1 <= (n : α) ↔ 1 <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem one_le_cast : 1 ≤ (n : α) ↔ 1 ≤ n := by rw [← cast_one, cast_le]
/-
**Nat.one_le_cast_iff_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：one_le_cast_iff_ne_zero : 1 <= (n : α) ↔ n != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Nat.one_le_cast`：one_le_cast : 1 <= (n : α) ↔ 1 <= n
· 使用定理 `Nat.one_le_iff_ne_zero`：∀ {n : ℕ}, 1 ≤ n ↔ n ≠ 0
-/
theorem one_le_cast_iff_ne_zero : 1 ≤ (n : α) ↔ n ≠ 0 :=
  one_le_cast.trans one_le_iff_ne_zero

@[simp, norm_cast]
/-
**Nat.cast_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：cast_lt_one : (n : α) < 1 ↔ n = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
· 使用定理 `Nat.le_zero`：∀ {i : ℕ}, i ≤ 0 ↔ i = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem cast_lt_one : (n : α) < 1 ↔ n = 0 := by
  rw [← cast_one, cast_lt, Nat.lt_succ_iff, le_zero]

@[simp, norm_cast]
/-
**Nat.cast_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：cast_le_one : (n : α) <= 1 ↔ n <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem cast_le_one : (n : α) ≤ 1 ↔ n ≤ 1 := by rw [← cast_one, cast_le]
/-
**Nat.cast_nonpos** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : PartialOrder α] [Ad
dLeftMono α] [ZeroLEOneClass α] [CharZero α]   {n : ℕ}, ↑n ≤ 0 ↔ n = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
-/
@[simp] lemma cast_nonpos : (n : α) ≤ 0 ↔ n = 0 := by norm_cast; lia

section
variable [m.AtLeastTwo]

@[simp]
/-
**Nat.ofNat_le_cast** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ofNat_le_cast : (ofNat(m) : α) <= n ↔ (OfNat.ofNat m : Nat) <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
-/
theorem ofNat_le_cast : (ofNat(m) : α) ≤ n ↔ (OfNat.ofNat m : ℕ) ≤ n :=
  cast_le

@[simp]
/-
**Nat.ofNat_lt_cast** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ofNat_lt_cast : (ofNat(m) : α) < n ↔ (OfNat.ofNat m : Nat) < n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
-/
theorem ofNat_lt_cast : (ofNat(m) : α) < n ↔ (OfNat.ofNat m : ℕ) < n :=
  cast_lt

end

variable [n.AtLeastTwo]

@[simp]
/-
**Nat.cast_le_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：cast_le_ofNat : (m : α) <= (ofNat(n) : α) ↔ m <= OfNat.ofNat n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
-/
theorem cast_le_ofNat : (m : α) ≤ (ofNat(n) : α) ↔ m ≤ OfNat.ofNat n :=
  cast_le

@[simp]
/-
**Nat.cast_lt_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：cast_lt_ofNat : (m : α) < (ofNat(n) : α) ↔ m < OfNat.ofNat n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
-/
theorem cast_lt_ofNat : (m : α) < (ofNat(n) : α) ↔ m < OfNat.ofNat n :=
  cast_lt

@[simp]
/-
**Nat.one_lt_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：one_lt_ofNat : 1 < (ofNat(n) : α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.one_lt_cast`：one_lt_cast : 1 < (n : α) ↔ 1 < n
· 使用引理 `Nat.AtLeastTwo.one_lt`：one_lt : 1 < n
-/
theorem one_lt_ofNat : 1 < (ofNat(n) : α) :=
  one_lt_cast.mpr AtLeastTwo.one_lt

@[simp]
/-
**Nat.one_le_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：one_le_ofNat : 1 <= (ofNat(n) : α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.one_le_cast`：one_le_cast : 1 <= (n : α) ↔ 1 <= n
· 使用定理 `NeZero.one_le`：one_le {n : Nat} [NeZero n] : 1 <= n
· 使用定理 `Nat.AtLeastTwo.toNeZero`：∀ (n : ℕ) [n.AtLeastTwo], NeZero n
-/
theorem one_le_ofNat : 1 ≤ (ofNat(n) : α) :=
  one_le_cast.mpr NeZero.one_le

@[simp]
/-
**Nat.not_ofNat_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：not_ofNat_le_one : ¬(ofNat(n) : α) <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Nat.cast_le_one`：cast_le_one : (n : α) <= 1 ↔ n <= 1
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用引理 `Nat.AtLeastTwo.one_lt`：one_lt : 1 < n
-/
theorem not_ofNat_le_one : ¬(ofNat(n) : α) ≤ 1 :=
  (cast_le_one.not.trans not_le).mpr AtLeastTwo.one_lt

@[simp]
/-
**Nat.not_ofNat_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：not_ofNat_lt_one : ¬(ofNat(n) : α) < 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.not_ofNat_le_one`：not_ofNat_le_one : ¬(ofNat(n) : α) <= 1
-/
theorem not_ofNat_lt_one : ¬(ofNat(n) : α) < 1 :=
  mt le_of_lt not_ofNat_le_one

variable [m.AtLeastTwo]

-- TODO: These lemmas need to be `@[simp]` for confluence in the presence of `cast_lt`, `cast_le`,
-- and `Nat.cast_ofNat`, but their LHSs match literally every inequality, so they're too expensive.
-- If https://github.com/leanprover/lean4/issues/2867 is fixed in a performant way, these can be made `@[simp]`.

-- @[simp]
/-
**Nat.ofNat_le** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ofNat_le : (ofNat(m) : α) <= (ofNat(n) : α) ↔ (OfNat.ofNat m : Nat) <= OfN
at.ofNat n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
-/
theorem ofNat_le :
    (ofNat(m) : α) ≤ (ofNat(n) : α) ↔ (OfNat.ofNat m : ℕ) ≤ OfNat.ofNat n :=
  cast_le

-- @[simp]
/-
**Nat.ofNat_lt** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ofNat_lt : (ofNat(m) : α) < (ofNat(n) : α) ↔ (OfNat.ofNat m : Nat) < OfNat
.ofNat n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
-/
theorem ofNat_lt :
    (ofNat(m) : α) < (ofNat(n) : α) ↔ (OfNat.ofNat m : ℕ) < OfNat.ofNat n :=
  cast_lt

end Nat

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddMonoidWithOne α] [CharZero α] : Nontrivial α where exists_pair_ne :=
  ⟨1, 0, (Nat.cast_one (R := α) ▸ Nat.cast_ne_zero.2 (by decide))⟩

section RingHomClass

variable {R S F : Type*} [NonAssocSemiring R] [NonAssocSemiring S] [FunLike F R S]

/-
**NeZero.nat_of_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NeZero.nat_of_injective {n : Nat} [NeZero (n : R)] [RingHomClass F R S] {f
 : F} (hf : Function.Injective f) : NeZero (n : S)
参数：n : R；hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `NeZero.natCast_ne`：natCast_ne (n : Nat) (R) [AddMonoidWithOne R] [h : Ne
Zero (n : R)] : (n : R) != 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem NeZero.nat_of_injective {n : ℕ} [NeZero (n : R)] [RingHomClass F R S] {f : F}
    (hf : Function.Injective f) : NeZero (n : S) :=
  ⟨fun h ↦ NeZero.natCast_ne n R <| hf <| by simpa only [map_natCast, map_zero f]⟩

end RingHomClass

