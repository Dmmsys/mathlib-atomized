/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Data.Int.Interval
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Membership in intervals via `Int.floor` / `Nat.floor` / `Int.ceil` / `Nat.ceil`

For a `FloorRing` (resp. `FloorSemiring`) `α`, we relate membership of a cast `↑n` in an interval
of `α` to membership of the integer (resp. natural number) `n` in the corresponding interval with
floor/ceil endpoints, for instance `Int.cast_mem_Ioc_iff : ↑n ∈ Set.Ioc a b ↔ n ∈ Set.Ioc ⌊a⌋ ⌊b⌋`.
If the right-hand side set is finite, we express it as `Finset` instead.

In the natural number case, non-negativity hypotheses are required when the `Nat.floor` function
is involved.  In the `IsStrictOrderedRing` case, one of these hypotheses can be omitted.
-/

@[expose] public section

namespace Int

variable {α : Type*} [Ring α] [LinearOrder α] [FloorRing α] {a b : α} {n : ℤ}

/-
**Int.cast_mem_Ioc_iff** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：cast_mem_Ioc_iff : ↑n in Set.Ioc a b ↔ n in Finset.Ioc ⌊a⌋ ⌊b⌋
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma cast_mem_Ioc_iff : ↑n ∈ Set.Ioc a b ↔ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋ := by
  simp [floor_lt, le_floor]
/-
**Int.cast_mem_Ico_iff** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：cast_mem_Ico_iff : ↑n in Set.Ico a b ↔ n in Finset.Ico ⌈a⌉ ⌈b⌉
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma cast_mem_Ico_iff : ↑n ∈ Set.Ico a b ↔ n ∈ Finset.Ico ⌈a⌉ ⌈b⌉ := by
  simp [ceil_le, lt_ceil]
/-
**Int.cast_mem_Icc_iff** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：cast_mem_Icc_iff : ↑n in Set.Icc a b ↔ n in Finset.Icc ⌈a⌉ ⌊b⌋
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma cast_mem_Icc_iff : ↑n ∈ Set.Icc a b ↔ n ∈ Finset.Icc ⌈a⌉ ⌊b⌋ := by
  simp [ceil_le, le_floor]
/-
**Int.cast_mem_Ioo_iff** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：cast_mem_Ioo_iff : ↑n in Set.Ioo a b ↔ n in Finset.Ioo ⌊a⌋ ⌈b⌉
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma cast_mem_Ioo_iff : ↑n ∈ Set.Ioo a b ↔ n ∈ Finset.Ioo ⌊a⌋ ⌈b⌉ := by
  simp [floor_lt, lt_ceil]
/-
**Int.cast_mem_Ioi_iff** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：cast_mem_Ioi_iff : ↑n in Set.Ioi a ↔ n in Set.Ioi ⌊a⌋
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma cast_mem_Ioi_iff : ↑n ∈ Set.Ioi a ↔ n ∈ Set.Ioi ⌊a⌋ := by simp [floor_lt]
/-
**Int.cast_mem_Ici_iff** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：cast_mem_Ici_iff : ↑n in Set.Ici a ↔ n in Set.Ici ⌈a⌉
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma cast_mem_Ici_iff : ↑n ∈ Set.Ici a ↔ n ∈ Set.Ici ⌈a⌉ := by simp [ceil_le]
/-
**Int.cast_mem_Iic_iff** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：cast_mem_Iic_iff : ↑n in Set.Iic b ↔ n in Set.Iic ⌊b⌋
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma cast_mem_Iic_iff : ↑n ∈ Set.Iic b ↔ n ∈ Set.Iic ⌊b⌋ := by simp [le_floor]
/-
**Int.cast_mem_Iio_iff** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：cast_mem_Iio_iff : ↑n in Set.Iio b ↔ n in Set.Iio ⌈b⌉
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma cast_mem_Iio_iff : ↑n ∈ Set.Iio b ↔ n ∈ Set.Iio ⌈b⌉ := by simp [lt_ceil]

end Int

namespace Nat

variable {α : Type*} [Semiring α] [LinearOrder α] [FloorSemiring α] {a b : α} {n : ℕ}

/-
**Nat.cast_mem_Ioc_iff** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：cast_mem_Ioc_iff (ha : 0 <= a) (hb : 0 <= b) : ↑n in Set.Ioc a b ↔ n in Fi
nset.Ioc ⌊a⌋₊ ⌊b⌋₊
参数：ha : 0 <= a；hb : 0 <= b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.floor_lt`：floor_lt (ha : 0 <= a) : ⌊a⌋₊ < n ↔ a < n
· 使用定理 `Nat.le_floor_iff`：le_floor_iff (ha : 0 <= a) : n <= ⌊a⌋₊ ↔ (n : α) <= a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma cast_mem_Ioc_iff (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ↑n ∈ Set.Ioc a b ↔ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ := by simp [floor_lt ha, le_floor_iff hb]

/-- The `0 ≤ b` hypothesis in `cast_mem_Ioc_iff` can be dropped if `IsStrictOrderedRing α`. -/
/-
**Nat.cast_mem_Ioc_iff'** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：cast_mem_Ioc_iff' [IsStrictOrderedRing α] (ha : 0 <= a) : ↑n in Set.Ioc a 
b ↔ n in Finset.Ioc ⌊a⌋₊ ⌊b⌋₊
参数：ha : 0 <= a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用引理 `Nat.cast_mem_Ioc_iff`：cast_mem_Ioc_iff (ha : 0 <= a) (hb : 0 <= b) : ↑n 
in Set.Ioc a b ↔ n in Finset.Ioc ⌊a⌋₊ ⌊b⌋₊

--- 原说明 ---
The `0 ≤ b` hypothesis in `cast_mem_Ioc_iff` can be dropped if `IsStrictOrderedR
ing α`.
-/
lemma cast_mem_Ioc_iff' [IsStrictOrderedRing α] (ha : 0 ≤ a) :
    ↑n ∈ Set.Ioc a b ↔ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ := by
  rcases le_or_gt 0 b with hb | hb
  · exact cast_mem_Ioc_iff ha hb
  · grind [floor_of_nonpos hb.le]
/-
**Nat.cast_mem_Ico_iff** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：cast_mem_Ico_iff : ↑n in Set.Ico a b ↔ n in Finset.Ico ⌈a⌉₊ ⌈b⌉₊
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma cast_mem_Ico_iff : ↑n ∈ Set.Ico a b ↔ n ∈ Finset.Ico ⌈a⌉₊ ⌈b⌉₊ := by
  simp [ceil_le, lt_ceil]
/-
**Nat.cast_mem_Icc_iff** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：cast_mem_Icc_iff (hb : 0 <= b) : ↑n in Set.Icc a b ↔ n in Finset.Icc ⌈a⌉₊ 
⌊b⌋₊
参数：hb : 0 <= b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.le_floor_iff`：le_floor_iff (ha : 0 <= a) : n <= ⌊a⌋₊ ↔ (n : α) <= a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma cast_mem_Icc_iff (hb : 0 ≤ b) : ↑n ∈ Set.Icc a b ↔ n ∈ Finset.Icc ⌈a⌉₊ ⌊b⌋₊ := by
  simp [ceil_le, le_floor_iff hb]
/-
**Nat.cast_mem_Ioo_iff** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：cast_mem_Ioo_iff (ha : 0 <= a) : ↑n in Set.Ioo a b ↔ n in Finset.Ioo ⌊a⌋₊ 
⌈b⌉₊
参数：ha : 0 <= a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.floor_lt`：floor_lt (ha : 0 <= a) : ⌊a⌋₊ < n ↔ a < n
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma cast_mem_Ioo_iff (ha : 0 ≤ a) : ↑n ∈ Set.Ioo a b ↔ n ∈ Finset.Ioo ⌊a⌋₊ ⌈b⌉₊ := by
  simp [floor_lt ha, lt_ceil]
/-
**Nat.cast_mem_Iic_iff** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：cast_mem_Iic_iff (hb : 0 <= b) : ↑n in Set.Iic b ↔ n in Finset.Iic ⌊b⌋₊
参数：hb : 0 <= b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.le_floor_iff`：le_floor_iff (ha : 0 <= a) : n <= ⌊a⌋₊ ↔ (n : α) <= a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma cast_mem_Iic_iff (hb : 0 ≤ b) : ↑n ∈ Set.Iic b ↔ n ∈ Finset.Iic ⌊b⌋₊ := by
  simp [le_floor_iff hb]
/-
**Nat.cast_mem_Iio_iff** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：cast_mem_Iio_iff : ↑n in Set.Iio b ↔ n in Finset.Iio ⌈b⌉₊
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma cast_mem_Iio_iff : ↑n ∈ Set.Iio b ↔ n ∈ Finset.Iio ⌈b⌉₊ := by simp [lt_ceil]
/-
**Nat.cast_mem_Ioi_iff** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：cast_mem_Ioi_iff (ha : 0 <= a) : ↑n in Set.Ioi a ↔ n in Set.Ioi ⌊a⌋₊
参数：ha : 0 <= a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.floor_lt`：floor_lt (ha : 0 <= a) : ⌊a⌋₊ < n ↔ a < n
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma cast_mem_Ioi_iff (ha : 0 ≤ a) : ↑n ∈ Set.Ioi a ↔ n ∈ Set.Ioi ⌊a⌋₊ := by simp [floor_lt ha]
/-
**Nat.cast_mem_Ici_iff** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：cast_mem_Ici_iff : ↑n in Set.Ici a ↔ n in Set.Ici ⌈a⌉₊
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma cast_mem_Ici_iff : ↑n ∈ Set.Ici a ↔ n ∈ Set.Ici ⌈a⌉₊ := by simp [ceil_le]

end Nat

