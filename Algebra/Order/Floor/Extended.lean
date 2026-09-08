/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.NNReal.Basic
public import Mathlib.Data.Real.ENatENNReal

import Mathlib.Data.ENNReal.Operations

/-!
# Extended floor and ceil

This file defines the extended floor and ceil functions `ENat.floor, ENat.ceil : ℝ≥0∞ → ℕ∞`.

## Main declarations

* `ENat.floor r`: Greatest extended natural `n` such that `n ≤ r`.
* `ENat.ceil r`: Least extended natural `n` such that `r ≤ n`.

## Notation

* `⌊r⌋ₑ` is `ENat.floor r`.
* `⌈r⌉ₑ` is `ENat.ceil r`.

The index `ₑ` is used in analogy to the notation for `enorm`.

## TODO

The day Mathlib acquires `ENNRat`, it would be good to generalise this file to an `EFloorSemiring`
typeclass.

## Tags

efloor, eceil
-/

public section

open Set
open scoped ENNReal NNReal

namespace ENat
variable {r s : ℝ≥0∞} {n : ℕ∞}

/-- `⌊r⌋ₑ` is the greatest extended natural `n` such that `n ≤ r`. -/
/-
**ENat.floor** 是 Mathlib 中的一个定义，位于命名空间 `ENat`。
形式化陈述：ENNReal → ℕ∞
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`⌊r⌋ₑ` is the greatest extended natural `n` such that `n ≤ r`.
-/
@[expose] noncomputable def floor : ℝ≥0∞ → ℕ∞
  | ∞ => ⊤
  | (r : ℝ≥0) => ⌊r⌋₊

/-- `⌈r⌉ₑ` is the least extended natural `n` such that `r ≤ n` -/
/-
**ENat.ceil** 是 Mathlib 中的一个定义，位于命名空间 `ENat`。
形式化陈述：ENNReal → ℕ∞
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`⌈r⌉ₑ` is the least extended natural `n` such that `r ≤ n`
-/
@[expose] noncomputable def ceil : ℝ≥0∞ → ℕ∞
  | ∞ => ⊤
  | (r : ℝ≥0) => ⌈r⌉₊

@[inherit_doc] notation "⌊" r "⌋ₑ" => ENat.floor r
@[inherit_doc] notation "⌈" r "⌉ₑ" => ENat.ceil r
/-
**ENat.floor_top** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：⌊⊤⌋ₑ = ⊤
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma floor_top : ⌊∞⌋ₑ = ⊤ := rfl
/-
**ENat.ceil_top** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：⌈⊤⌉ₑ = ⊤
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ceil_top : ⌈∞⌉ₑ = ⊤ := rfl
/-
**ENat.floor_coe** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ (r : NNReal), ⌊↑r⌋ₑ = ↑⌊r⌋₊
参数：r : NNReal。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma floor_coe (r : ℝ≥0) : ⌊r⌋ₑ = ⌊r⌋₊ := rfl
/-
**ENat.ceil_coe** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ (r : NNReal), ⌈↑r⌉ₑ = ↑⌈r⌉₊
参数：r : NNReal。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma ceil_coe (r : ℝ≥0) : ⌈r⌉ₑ = ⌈r⌉₊ := rfl
/-
**ENat.floor_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {r : ENNReal}, ⌊r⌋ₑ = ⊤ ↔ r = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] lemma floor_eq_top : ⌊r⌋ₑ = ⊤ ↔ r = ∞ := by cases r <;> simp
/-
**ENat.ceil_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {r : ENNReal}, ⌈r⌉ₑ = ⊤ ↔ r = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] lemma ceil_eq_top : ⌈r⌉ₑ = ⊤ ↔ r = ∞ := by cases r <;> simp
/-
**ENat.floor_lt_top** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：floor_lt_top : ⌊r⌋ₑ < ⊤ ↔ r < ∞
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma floor_lt_top : ⌊r⌋ₑ < ⊤ ↔ r < ∞ := by cases r <;> simp
/-
**ENat.ceil_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {r : ENNReal}, ⌈r⌉ₑ < ⊤ ↔ r < ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] lemma ceil_lt_top : ⌈r⌉ₑ < ⊤ ↔ r < ∞ := by cases r <;> simp
/-
**ENat.le_floor** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {r : ENNReal} {n : ℕ∞}, n ≤ ⌊r⌋ₑ ↔ ↑n ≤ r
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
@[simp] lemma le_floor : n ≤ ⌊r⌋ₑ ↔ n ≤ r := by cases r <;> cases n <;> simp [Nat.le_floor_iff]
/-
**ENat.ceil_le** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {r : ENNReal} {n : ℕ∞}, ⌈r⌉ₑ ≤ n ↔ r ≤ ↑n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
@[simp] lemma ceil_le : ⌈r⌉ₑ ≤ n ↔ r ≤ n := by cases r <;> cases n <;> simp
/-
**ENat.floor_lt** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {r : ENNReal} {n : ℕ∞}, ⌊r⌋ₑ < n ↔ r < ↑n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le`：lt_iff_lt_of_le_iff_le {β} [LinearOrder α] [Line
arOrder β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) : b < a ↔ d < c
· 使用定理 `ENat.le_floor`：∀ {r : ENNReal} {n : ℕ∞}, n ≤ ⌊r⌋ₑ ↔ ↑n ≤ r
-/
@[simp] lemma floor_lt : ⌊r⌋ₑ < n ↔ r < n := lt_iff_lt_of_le_iff_le le_floor
/-
**ENat.lt_ceil** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {r : ENNReal} {n : ℕ∞}, n < ⌈r⌉ₑ ↔ ↑n < r
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le`：lt_iff_lt_of_le_iff_le {β} [LinearOrder α] [Line
arOrder β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) : b < a ↔ d < c
· 使用定理 `ENat.ceil_le`：∀ {r : ENNReal} {n : ℕ∞}, ⌈r⌉ₑ ≤ n ↔ r ≤ ↑n
-/
@[simp] lemma lt_ceil : n < ⌈r⌉ₑ ↔ n < r := lt_iff_lt_of_le_iff_le ceil_le
/-
**ENat.gc_toENNReal_floor** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：gc_toENNReal_floor : GaloisConnection (↑) floor
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `ENat.le_floor`：∀ {r : ENNReal} {n : ℕ∞}, n ≤ ⌊r⌋ₑ ↔ ↑n ≤ r
-/
lemma gc_toENNReal_floor : GaloisConnection (↑) floor := fun _ _ ↦ le_floor.symm
/-
**ENat.gc_ceil_toENNReal** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：gc_ceil_toENNReal : GaloisConnection ceil (↑)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENat.ceil_le`：∀ {r : ENNReal} {n : ℕ∞}, ⌈r⌉ₑ ≤ n ↔ r ≤ ↑n
-/
lemma gc_ceil_toENNReal : GaloisConnection ceil (↑) := fun _ _ ↦ ceil_le
/-
**ENat.floor_le_self** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {r : ENNReal}, ↑⌊r⌋ₑ ≤ r
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENat.le_floor`：∀ {r : ENNReal} {n : ℕ∞}, n ≤ ⌊r⌋ₑ ↔ ↑n ≤ r
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
@[bound] lemma floor_le_self : ⌊r⌋ₑ ≤ r := le_floor.1 le_rfl
/-
**ENat.le_ceil_self** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {r : ENNReal}, r ≤ ↑⌈r⌉ₑ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENat.ceil_le`：∀ {r : ENNReal} {n : ℕ∞}, ⌈r⌉ₑ ≤ n ↔ r ≤ ↑n
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
@[bound] lemma le_ceil_self : r ≤ ⌈r⌉ₑ := ceil_le.1 le_rfl
/-
**ENat.floor_le** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {r : ENNReal} {n : ℕ∞}, n ≠ ⊤ → (⌊r⌋ₑ ≤ n ↔ r < ↑n + 1)
参数：⌊r⌋ₑ ≤ n ↔ r < ↑n + 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENat.lt_add_one_iff`：lt_add_one_iff (hn : n != ⊤) : m < n + 1 ↔ m <= n
· 使用定理 `ENat.toENNReal_add`：toENNReal_add (m n : Nat∞) : ↑(m + n) = (m + n : Rea
l>=0∞)
· 使用定理 `ENat.toENNReal_one`：toENNReal_one : ((1 : Nat∞) : Real>=0∞) = 1
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma floor_le (hn : n ≠ ⊤) : ⌊r⌋ₑ ≤ n ↔ r < n + 1 := by simp [← lt_add_one_iff hn]
/-
**ENat.le_ceil** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {r : ENNReal} {n : ℕ∞}, n ≠ 0 → n ≠ ⊤ → (n ≤ ⌈r⌉ₑ ↔ ↑n - 1 < r)
参数：n ≤ ⌈r⌉ₑ ↔ ↑n - 1 < r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `ENNReal.coe_lt_top`：∀ {r : NNReal}, ↑r < ⊤
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `ENNReal.natCast_sub`：natCast_sub (m n : Nat) : ↑(m - n) = (m - n : Real>
=0∞)
· 使用定理 `Nat.cast_tsub`：cast_tsub [CommSemiring α] [PartialOrder α] [IsOrderedRin
g α] [CanonicallyOrderedAdd α] [Sub α] [OrderedSub α] [AddLeftReflectLE α] (m n 
: N…
· 使用定理 `NNReal.instIsOrderedRing_1`：IsOrderedRing NNReal
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `NNReal.instOrderedSub`：OrderedSub NNReal
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `ENNReal.coe_sub`：∀ {r p : NNReal}, ↑(r - p) = ↑r - ↑p
· 使用定理 `Nat.add_one_le_ceil_iff`：add_one_le_ceil_iff : n + 1 <= ⌈a⌉₊ ↔ (n : R) <
 a
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma le_ceil (hn₀ : n ≠ 0) (hn : n ≠ ⊤) : n ≤ ⌈r⌉ₑ ↔ n - 1 < r := by
  lift n to ℕ using hn
  cases r
  · simp only [ceil_top, le_top, toENNReal_coe, true_iff]
    norm_cast
    exact ENNReal.coe_lt_top
  · simp only [ne_eq, Nat.cast_eq_zero, ceil_coe, Nat.cast_le, toENNReal_coe] at hn₀ ⊢
    norm_cast
    rw [← Nat.add_one_le_ceil_iff, Nat.sub_add_cancel]
    lia
/-
**ENat.lt_floor** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {r : ENNReal} {n : ℕ∞}, n ≠ ⊤ → (n < ⌊r⌋ₑ ↔ ↑n + 1 ≤ r)
参数：n < ⌊r⌋ₑ ↔ ↑n + 1 ≤ r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENat.add_one_le_iff`：add_one_le_iff (hm : m != ⊤) : m + 1 <= n ↔ m < n
· 使用定理 `ENat.toENNReal_add`：toENNReal_add (m n : Nat∞) : ↑(m + n) = (m + n : Rea
l>=0∞)
· 使用定理 `ENat.toENNReal_one`：toENNReal_one : ((1 : Nat∞) : Real>=0∞) = 1
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma lt_floor (hn : n ≠ ⊤) : n < ⌊r⌋ₑ ↔ n + 1 ≤ r := by simp [← add_one_le_iff hn]
/-
**ENat.ceil_lt** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {r : ENNReal} {n : ℕ∞}, n ≠ 0 → n ≠ ⊤ → (⌈r⌉ₑ < n ↔ r ≤ ↑n - 1)
参数：⌈r⌉ₑ < n ↔ r ≤ ↑n - 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `ENat.le_ceil`：∀ {r : ENNReal} {n : ℕ∞}, n ≠ 0 → n ≠ ⊤ → (n ≤ ⌈r⌉ₑ ↔ ↑n -
 1 < r)
-/
@[simp] lemma ceil_lt (hn₀ : n ≠ 0) (hn : n ≠ ⊤) : ⌈r⌉ₑ < n ↔ r ≤ n - 1 := by
  simpa using (le_ceil hn₀ hn).not
/-
**ENat.floor_mono** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：floor_mono : Monotone (floor : Real>=0∞ -> Nat∞)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a → 
c ≤ b → c ≤ a
· 使用定理 `ENat.floor_le_self`：∀ {r : ENNReal}, ↑⌊r⌋ₑ ≤ r
-/
lemma floor_mono : Monotone (floor : ℝ≥0∞ → ℕ∞) :=
  fun r s hrs ↦ by simpa using hrs.trans' floor_le_self
/-
**ENat.ceil_mono** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：ceil_mono : Monotone (ceil : Real>=0∞ -> Nat∞)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `ENat.le_ceil_self`：∀ {r : ENNReal}, r ≤ ↑⌈r⌉ₑ
-/
lemma ceil_mono : Monotone (ceil : ℝ≥0∞ → ℕ∞) := fun r s hrs ↦ by simpa using hrs.trans le_ceil_self
/-
**ENat.floor_le_floor** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {r s : ENNReal}, r ≤ s → ⌊r⌋ₑ ≤ ⌊s⌋ₑ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENat.floor_mono`：floor_mono : Monotone (floor : Real>=0∞ -> Nat∞)
-/
@[gcongr, bound] lemma floor_le_floor (hrs : r ≤ s) : ⌊r⌋ₑ ≤ ⌊s⌋ₑ := floor_mono hrs
/-
**ENat.ceil_le_ceil** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {r s : ENNReal}, r ≤ s → ⌈r⌉ₑ ≤ ⌈s⌉ₑ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENat.ceil_mono`：ceil_mono : Monotone (ceil : Real>=0∞ -> Nat∞)
-/
@[gcongr, bound] lemma ceil_le_ceil (hrs : r ≤ s) : ⌈r⌉ₑ ≤ ⌈s⌉ₑ := ceil_mono hrs
/-
**ENat.floor_natCast** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ (n : ℕ∞), ⌊↑n⌋ₑ = n
参数：n : ℕ∞。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `eq_of_forall_le_iff`：eq_of_forall_le_iff (H : forall c, c <= a ↔ c <= b)
 : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma floor_natCast (n : ℕ∞) : ⌊n⌋ₑ = n := eq_of_forall_le_iff fun r ↦ by simp
/-
**ENat.ceil_natCast** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ (n : ℕ∞), ⌈↑n⌉ₑ = n
参数：n : ℕ∞。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma ceil_natCast (n : ℕ∞) : ⌈n⌉ₑ = n := eq_of_forall_ge_iff fun r ↦ by simp
/-
**ENat.floor_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：⌊0⌋ₑ = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENat.toENNReal_zero`：toENNReal_zero : ((0 : Nat∞) : Real>=0∞) = 0
· 使用定理 `ENat.floor_natCast`：∀ (n : ℕ∞), ⌊↑n⌋ₑ = n
-/
@[simp] lemma floor_zero : ⌊0⌋ₑ = 0 := by simpa using floor_natCast 0
/-
**ENat.ceil_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：⌈0⌉ₑ = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENat.toENNReal_zero`：toENNReal_zero : ((0 : Nat∞) : Real>=0∞) = 0
· 使用定理 `ENat.ceil_natCast`：∀ (n : ℕ∞), ⌈↑n⌉ₑ = n
-/
@[simp] lemma ceil_zero : ⌈0⌉ₑ = 0 := by simpa using ceil_natCast 0
/-
**ENat.floor_one** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：⌊1⌋ₑ = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENat.toENNReal_one`：toENNReal_one : ((1 : Nat∞) : Real>=0∞) = 1
· 使用定理 `ENat.floor_natCast`：∀ (n : ℕ∞), ⌊↑n⌋ₑ = n
-/
@[simp] lemma floor_one : ⌊1⌋ₑ = 1 := by simpa using floor_natCast 1
/-
**ENat.ceil_one** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：⌈1⌉ₑ = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENat.toENNReal_one`：toENNReal_one : ((1 : Nat∞) : Real>=0∞) = 1
· 使用定理 `ENat.ceil_natCast`：∀ (n : ℕ∞), ⌈↑n⌉ₑ = n
-/
@[simp] lemma ceil_one : ⌈1⌉ₑ = 1 := by simpa using ceil_natCast 1
/-
**ENat.floor_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ (n : ℕ) [inst : n.AtLeastTwo], ⌊OfNat.ofNat n⌋ₑ = OfNat.ofNat n
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENat.floor_natCast`：∀ (n : ℕ∞), ⌊↑n⌋ₑ = n
-/
@[simp] lemma floor_ofNat (n : ℕ) [n.AtLeastTwo] : ⌊ofNat(n)⌋ₑ = ofNat(n) := ENat.floor_natCast n
/-
**ENat.ceil_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ (n : ℕ) [inst : n.AtLeastTwo], ⌈OfNat.ofNat n⌉ₑ = OfNat.ofNat n
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENat.ceil_natCast`：∀ (n : ℕ∞), ⌈↑n⌉ₑ = n
-/
@[simp] lemma ceil_ofNat (n : ℕ) [n.AtLeastTwo] : ⌈ofNat(n)⌉ₑ = ofNat(n) := ENat.ceil_natCast n
/-
**ENat.floor_pos** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：floor_pos : 0 < ⌊r⌋ₑ ↔ 1 <= r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ENat.toENNReal_zero`：toENNReal_zero : ((0 : Nat∞) : Real>=0∞) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma floor_pos : 0 < ⌊r⌋ₑ ↔ 1 ≤ r := by simp
/-
**ENat.ceil_pos** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：ceil_pos : 0 < ⌈r⌉ₑ ↔ 0 < r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENat.toENNReal_zero`：toENNReal_zero : ((0 : Nat∞) : Real>=0∞) = 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma ceil_pos : 0 < ⌈r⌉ₑ ↔ 0 < r := by simp
/-
**ENat.floor_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {r : ENNReal}, ⌊r⌋ₑ = 0 ↔ r < 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ENat.toENNReal_zero`：toENNReal_zero : ((0 : Nat∞) : Real>=0∞) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma floor_eq_zero : ⌊r⌋ₑ = 0 ↔ r < 1 := by simp [← nonpos_iff_eq_zero]
/-
**ENat.ceil_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {r : ENNReal}, ⌈r⌉ₑ = 0 ↔ r = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ENat.toENNReal_zero`：toENNReal_zero : ((0 : Nat∞) : Real>=0∞) = 0
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENat.ceil_le`：∀ {r : ENNReal} {n : ℕ∞}, ⌈r⌉ₑ ≤ n ↔ r ≤ ↑n
-/
@[simp] lemma ceil_eq_zero : ⌈r⌉ₑ = 0 ↔ r = 0 := by simpa using ceil_le (n := 0)
/-
**ENat.floor_le_ceil** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {r : ENNReal}, ⌊r⌋ₑ ≤ ⌈r⌉ₑ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `ENat.floor_le_self`：∀ {r : ENNReal}, ↑⌊r⌋ₑ ≤ r
· 使用定理 `ENat.le_ceil_self`：∀ {r : ENNReal}, r ≤ ↑⌈r⌉ₑ
-/
@[bound] lemma floor_le_ceil : ⌊r⌋ₑ ≤ ⌈r⌉ₑ := mod_cast floor_le_self.trans le_ceil_self
/-
**ENat.ceil_le_floor_add_one** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ (r : ENNReal), ⌈r⌉ₑ ≤ ⌊r⌋ₑ + 1
参数：r : ENNReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Nat.ceil_le_floor_add_one`：ceil_le_floor_add_one (a : R) : ⌈a⌉₊ <= ⌊a⌋₊ 
+ 1
-/
@[bound] lemma ceil_le_floor_add_one : ∀ r : ℝ≥0∞, ⌈r⌉ₑ ≤ ⌊r⌋ₑ + 1
  | ∞ => le_rfl
  | (r : ℝ≥0) => by simpa using mod_cast Nat.ceil_le_floor_add_one r
/-
**ENat.floor_lt_ceil** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：floor_lt_ceil (hrs : r < s) : ⌊r⌋ₑ < ⌈s⌉ₑ
参数：hrs : r < s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENat.floor_lt`：∀ {r : ENNReal} {n : ℕ∞}, ⌊r⌋ₑ < n ↔ r < ↑n
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `ENat.le_ceil_self`：∀ {r : ENNReal}, r ≤ ↑⌈r⌉ₑ
-/
lemma floor_lt_ceil (hrs : r < s) : ⌊r⌋ₑ < ⌈s⌉ₑ := floor_lt.2 <| hrs.trans_le le_ceil_self
/-
**ENat.floor_congr** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：floor_congr (h : forall n : Nat∞, n <= r ↔ n <= s) : ⌊r⌋ₑ = ⌊s⌋ₑ
参数：h : forall n : Nat∞, n <= r ↔ n <= s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `eq_of_forall_le_iff`：eq_of_forall_le_iff (H : forall c, c <= a ↔ c <= b)
 : a = b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma floor_congr (h : ∀ n : ℕ∞, n ≤ r ↔ n ≤ s) : ⌊r⌋ₑ = ⌊s⌋ₑ := eq_of_forall_le_iff <| by simpa
/-
**ENat.ceil_congr** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：ceil_congr (h : forall n : Nat∞, r <= n ↔ s <= n) : ⌈r⌉ₑ = ⌈s⌉ₑ
参数：h : forall n : Nat∞, r <= n ↔ s <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma ceil_congr (h : ∀ n : ℕ∞, r ≤ n ↔ s ≤ n) : ⌈r⌉ₑ = ⌈s⌉ₑ := eq_of_forall_ge_iff <| by simpa
/-
**ENat.floor_add_toENNReal** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ (r : ENNReal) (n : ℕ∞), ⌊r + ↑n⌋ₑ = ⌊r⌋ₑ + n
参数：r : ENNReal；n : ℕ∞。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `top_add`：top_add (a : α) : ⊤ + a = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_top`：add_top (a : α) : a + ⊤ = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.ofNNReal_add_natCast`：∀ (r : NNReal) (n : ℕ), ↑(r + ↑n) = ↑r + ↑
n
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Nat.floor_add_natCast`：floor_add_natCast [IsStrictOrderedRing R] (ha : 0
 <= a) (n : Nat) : ⌊a + n⌋₊ = ⌊a⌋₊ + n
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
@[simp] lemma floor_add_toENNReal : ∀ (r : ℝ≥0∞) (n : ℕ∞), ⌊r + n⌋ₑ = ⌊r⌋ₑ + n
  | ∞, _ => by simp
  | _, ⊤ => by simp
  | (r : ℝ≥0), (n : ℕ) => by
    -- FIXME: Why does `norm_cast` not use `ENNReal.ofNNReal_add_natCast`?
    norm_cast; rw [← ENNReal.ofNNReal_add_natCast]; norm_cast; exact n.floor_add_natCast zero_le
/-
**ENat.ceil_add_toENNReal** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ (r : ENNReal) (n : ℕ∞), ⌈r + ↑n⌉ₑ = ⌈r⌉ₑ + n
参数：r : ENNReal；n : ℕ∞。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `top_add`：top_add (a : α) : ⊤ + a = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_top`：add_top (a : α) : a + ⊤ = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.ofNNReal_add_natCast`：∀ (r : NNReal) (n : ℕ), ↑(r + ↑n) = ↑r + ↑
n
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Nat.ceil_add_natCast`：ceil_add_natCast (ha : 0 <= a) (n : Nat) : ⌈a + n⌉
₊ = ⌈a⌉₊ + n
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
@[simp] lemma ceil_add_toENNReal : ∀ (r : ℝ≥0∞) (n : ℕ∞), ⌈r + n⌉ₑ = ⌈r⌉ₑ + n
  | ∞, _ => by simp
  | _, ⊤ => by simp
  | (r : ℝ≥0), (n : ℕ) => by
    -- FIXME: Why does `norm_cast` not use `ENNReal.ofNNReal_sub_natCast`?
    norm_cast; rw [← ENNReal.ofNNReal_add_natCast]; norm_cast; exact Nat.ceil_add_natCast zero_le _
/-
**ENat.floor_toENNReal_add** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ (r : ENNReal) (n : ℕ∞), ⌊↑n + r⌋ₑ = n + ⌊r⌋ₑ
参数：r : ENNReal；n : ℕ∞。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `ENat.floor_add_toENNReal`：∀ (r : ENNReal) (n : ℕ∞), ⌊r + ↑n⌋ₑ = ⌊r⌋ₑ + n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma floor_toENNReal_add (r : ℝ≥0∞) (n : ℕ∞) : ⌊n + r⌋ₑ = n + ⌊r⌋ₑ := by
  simp [add_comm, floor_add_toENNReal]
/-
**ENat.ceil_toENNReal_add** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ (r : ENNReal) (n : ℕ∞), ⌈↑n + r⌉ₑ = n + ⌈r⌉ₑ
参数：r : ENNReal；n : ℕ∞。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `ENat.ceil_add_toENNReal`：∀ (r : ENNReal) (n : ℕ∞), ⌈r + ↑n⌉ₑ = ⌈r⌉ₑ + n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma ceil_toENNReal_add (r : ℝ≥0∞) (n : ℕ∞) : ⌈n + r⌉ₑ = n + ⌈r⌉ₑ := by
  simp [add_comm, ceil_add_toENNReal]
/-
**ENat.floor_add_natCast** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ (r : ENNReal) (n : ℕ), ⌊r + ↑n⌋ₑ = ⌊r⌋ₑ + ↑n
参数：r : ENNReal；n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENat.floor_add_toENNReal`：∀ (r : ENNReal) (n : ℕ∞), ⌊r + ↑n⌋ₑ = ⌊r⌋ₑ + n
-/
@[simp] lemma floor_add_natCast (r : ℝ≥0∞) (n : ℕ) : ⌊r + n⌋ₑ = ⌊r⌋ₑ + n := floor_add_toENNReal r n
/-
**ENat.ceil_add_natCast** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ (r : ENNReal) (n : ℕ), ⌈r + ↑n⌉ₑ = ⌈r⌉ₑ + ↑n
参数：r : ENNReal；n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENat.ceil_add_toENNReal`：∀ (r : ENNReal) (n : ℕ∞), ⌈r + ↑n⌉ₑ = ⌈r⌉ₑ + n
-/
@[simp] lemma ceil_add_natCast (r : ℝ≥0∞) (n : ℕ) : ⌈r + n⌉ₑ = ⌈r⌉ₑ + n := ceil_add_toENNReal r n
/-
**ENat.floor_natCast_add** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ (r : ENNReal) (n : ℕ), ⌊↑n + r⌋ₑ = ↑n + ⌊r⌋ₑ
参数：r : ENNReal；n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENat.floor_toENNReal_add`：∀ (r : ENNReal) (n : ℕ∞), ⌊↑n + r⌋ₑ = n + ⌊r⌋ₑ
-/
@[simp] lemma floor_natCast_add (r : ℝ≥0∞) (n : ℕ) : ⌊n + r⌋ₑ = n + ⌊r⌋ₑ := floor_toENNReal_add r n
/-
**ENat.ceil_natCast_add** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ (r : ENNReal) (n : ℕ), ⌈↑n + r⌉ₑ = ↑n + ⌈r⌉ₑ
参数：r : ENNReal；n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENat.ceil_toENNReal_add`：∀ (r : ENNReal) (n : ℕ∞), ⌈↑n + r⌉ₑ = n + ⌈r⌉ₑ
-/
@[simp] lemma ceil_natCast_add (r : ℝ≥0∞) (n : ℕ) : ⌈n + r⌉ₑ = n + ⌈r⌉ₑ := ceil_toENNReal_add r n
/-
**ENat.floor_add_one** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ (r : ENNReal), ⌊r + 1⌋ₑ = ⌊r⌋ₑ + 1
参数：r : ENNReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENat.floor_add_natCast`：∀ (r : ENNReal) (n : ℕ), ⌊r + ↑n⌋ₑ = ⌊r⌋ₑ + ↑n
-/
@[simp] lemma floor_add_one (r : ℝ≥0∞) : ⌊r + 1⌋ₑ = ⌊r⌋ₑ + 1 := mod_cast floor_add_natCast r 1
/-
**ENat.ceil_add_one** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ (r : ENNReal), ⌈r + 1⌉ₑ = ⌈r⌉ₑ + 1
参数：r : ENNReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENat.ceil_add_natCast`：∀ (r : ENNReal) (n : ℕ), ⌈r + ↑n⌉ₑ = ⌈r⌉ₑ + ↑n
-/
@[simp] lemma ceil_add_one (r : ℝ≥0∞) : ⌈r + 1⌉ₑ = ⌈r⌉ₑ + 1 := mod_cast ceil_add_natCast r 1

@[simp]
/-
**ENat.floor_add_ofNat** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：floor_add_ofNat (r : Real>=0∞) (n : Nat) [n.AtLeastTwo] : ⌊r + ofNat(n)⌋ₑ 
= ⌊r⌋ₑ + ofNat(n)
参数：r : Real>=0∞；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENat.floor_add_natCast`：∀ (r : ENNReal) (n : ℕ), ⌊r + ↑n⌋ₑ = ⌊r⌋ₑ + ↑n
-/
lemma floor_add_ofNat (r : ℝ≥0∞) (n : ℕ) [n.AtLeastTwo] : ⌊r + ofNat(n)⌋ₑ = ⌊r⌋ₑ + ofNat(n) :=
  floor_add_natCast r n

@[simp]
/-
**ENat.ceil_add_ofNat** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：ceil_add_ofNat (r : Real>=0∞) (n : Nat) [n.AtLeastTwo] : ⌈r + ofNat(n)⌉ₑ =
 ⌈r⌉ₑ + ofNat(n)
参数：r : Real>=0∞；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENat.ceil_add_natCast`：∀ (r : ENNReal) (n : ℕ), ⌈r + ↑n⌉ₑ = ⌈r⌉ₑ + ↑n
-/
lemma ceil_add_ofNat (r : ℝ≥0∞) (n : ℕ) [n.AtLeastTwo] : ⌈r + ofNat(n)⌉ₑ = ⌈r⌉ₑ + ofNat(n) :=
  ceil_add_natCast r n
/-
**ENat.floor_sub_toENNReal** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ (r : ENNReal) (n : ℕ∞), ⌊r - ↑n⌋ₑ = ⌊r⌋ₑ - n
参数：r : ENNReal；n : ℕ∞。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `ENat.floor_zero`：⌊0⌋ₑ = 0
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `instOrderedSubENat`：OrderedSub ℕ∞
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.top_sub`：∀ {a : ENNReal}, a ≠ ⊤ → ⊤ - a = ⊤
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ENNReal.sub_top`：∀ {a : ENNReal}, a - ⊤ = 0
· 使用定理 `ENat.sub_top`：∀ (a : ℕ∞), a - ⊤ = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.ofNNReal_sub_natCast`：∀ (r : NNReal) (n : ℕ), ↑(r - ↑n) = ↑r - ↑
n
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Nat.floor_sub_natCast`：floor_sub_natCast [Sub R] [OrderedSub R] [ExistsA
ddOfLE R] (a : R) (n : Nat) : ⌊a - n⌋₊ = ⌊a⌋₊ - n
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `NNReal.instOrderedSub`：OrderedSub NNReal
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
-/
@[simp] lemma floor_sub_toENNReal : ∀ (r : ℝ≥0∞) (n : ℕ∞), ⌊r - n⌋ₑ = ⌊r⌋ₑ - n
  | ∞, ⊤ => by simp
  | ∞, (n : ℕ) => by simp
  | (r : ℝ≥0), ⊤ => by simp
  | (r : ℝ≥0), (n : ℕ) => by
    -- FIXME: Why does `norm_cast` not use `ENNReal.ofNNReal_sub_natCast`?
    norm_cast; rw [← ENNReal.ofNNReal_sub_natCast]; norm_cast; exact Nat.floor_sub_natCast ..
/-
**ENat.ceil_sub_toENNReal** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ (r : ENNReal) (n : ℕ∞), ⌈r - ↑n⌉ₑ = ⌈r⌉ₑ - n
参数：r : ENNReal；n : ℕ∞。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `ENat.ceil_zero`：⌈0⌉ₑ = 0
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `instOrderedSubENat`：OrderedSub ℕ∞
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.top_sub`：∀ {a : ENNReal}, a ≠ ⊤ → ⊤ - a = ⊤
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ENNReal.sub_top`：∀ {a : ENNReal}, a - ⊤ = 0
· 使用定理 `ENat.sub_top`：∀ (a : ℕ∞), a - ⊤ = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.ofNNReal_sub_natCast`：∀ (r : NNReal) (n : ℕ), ↑(r - ↑n) = ↑r - ↑
n
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Nat.ceil_sub_natCast`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : Lin
earOrder R] [inst_2 : FloorSemiring R] [IsStrictOrderedRing R]   [inst_4 : Sub R
] [Ordered…
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `NNReal.instOrderedSub`：OrderedSub NNReal
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
-/
@[simp] lemma ceil_sub_toENNReal : ∀ (r : ℝ≥0∞) (n : ℕ∞), ⌈r - n⌉ₑ = ⌈r⌉ₑ - n
  | ∞, ⊤ => by simp
  | ∞, (n : ℕ) => by simp
  | (r : ℝ≥0), ⊤ => by simp
  | (r : ℝ≥0), (n : ℕ) => by
    -- FIXME: Why does `norm_cast` not use `ENNReal.ofNNReal_sub_natCast`?
    norm_cast; rw [← ENNReal.ofNNReal_sub_natCast]; norm_cast; exact Nat.ceil_sub_natCast ..
/-
**ENat.floor_sub_natCast** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ (r : ENNReal) (n : ℕ), ⌊r - ↑n⌋ₑ = ⌊r⌋ₑ - ↑n
参数：r : ENNReal；n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENat.floor_sub_toENNReal`：∀ (r : ENNReal) (n : ℕ∞), ⌊r - ↑n⌋ₑ = ⌊r⌋ₑ - n
-/
@[simp] lemma floor_sub_natCast (r : ℝ≥0∞) (n : ℕ) : ⌊r - n⌋ₑ = ⌊r⌋ₑ - n := floor_sub_toENNReal r n
/-
**ENat.ceil_sub_natCast** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ (r : ENNReal) (n : ℕ), ⌈r - ↑n⌉ₑ = ⌈r⌉ₑ - ↑n
参数：r : ENNReal；n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENat.ceil_sub_toENNReal`：∀ (r : ENNReal) (n : ℕ∞), ⌈r - ↑n⌉ₑ = ⌈r⌉ₑ - n
-/
@[simp] lemma ceil_sub_natCast (r : ℝ≥0∞) (n : ℕ) : ⌈r - n⌉ₑ = ⌈r⌉ₑ - n := ceil_sub_toENNReal r n
/-
**ENat.floor_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ (r : ENNReal), ⌊r - 1⌋ₑ = ⌊r⌋ₑ - 1
参数：r : ENNReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `ENat.toENNReal_one`：toENNReal_one : ((1 : Nat∞) : Real>=0∞) = 1
· 使用定理 `ENat.floor_sub_toENNReal`：∀ (r : ENNReal) (n : ℕ∞), ⌊r - ↑n⌋ₑ = ⌊r⌋ₑ - n
-/
@[simp] lemma floor_sub_one (r : ℝ≥0∞) : ⌊r - 1⌋ₑ = ⌊r⌋ₑ - 1 := mod_cast floor_sub_toENNReal r 1
/-
**ENat.ceil_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ (r : ENNReal), ⌈r - 1⌉ₑ = ⌈r⌉ₑ - 1
参数：r : ENNReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `ENat.toENNReal_one`：toENNReal_one : ((1 : Nat∞) : Real>=0∞) = 1
· 使用定理 `ENat.ceil_sub_toENNReal`：∀ (r : ENNReal) (n : ℕ∞), ⌈r - ↑n⌉ₑ = ⌈r⌉ₑ - n
-/
@[simp] lemma ceil_sub_one (r : ℝ≥0∞) : ⌈r - 1⌉ₑ = ⌈r⌉ₑ - 1 := mod_cast ceil_sub_toENNReal r 1

@[simp]
/-
**ENat.floor_sub_ofNat** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：floor_sub_ofNat (r : Real>=0∞) (n : Nat) [n.AtLeastTwo] : ⌊r - ofNat(n)⌋ₑ 
= ⌊r⌋ₑ - ofNat(n)
参数：r : Real>=0∞；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENat.floor_sub_toENNReal`：∀ (r : ENNReal) (n : ℕ∞), ⌊r - ↑n⌋ₑ = ⌊r⌋ₑ - n
-/
lemma floor_sub_ofNat (r : ℝ≥0∞) (n : ℕ) [n.AtLeastTwo] : ⌊r - ofNat(n)⌋ₑ = ⌊r⌋ₑ - ofNat(n) :=
  floor_sub_toENNReal r n
/-
**ENat.ceil_sub_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ (r : ENNReal) (n : ℕ) [inst : n.AtLeastTwo], ⌈r - OfNat.ofNat n⌉ₑ = ⌈r⌉ₑ
 - OfNat.ofNat n
参数：r : ENNReal；n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENat.ceil_sub_toENNReal`：∀ (r : ENNReal) (n : ℕ∞), ⌈r - ↑n⌉ₑ = ⌈r⌉ₑ - n
-/
@[simp] lemma ceil_sub_ofNat (r : ℝ≥0∞) (n : ℕ) [n.AtLeastTwo] :
    ⌈r - ofNat(n)⌉ₑ = ⌈r⌉ₑ - ofNat(n) := ceil_sub_toENNReal r n

@[bound]
/-
**ENat.ceil_lt_add_one** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：ceil_lt_add_one (hr : r != ∞) : (⌈r⌉ₑ : Real>=0∞) < r + 1
参数：hr : r != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.ceil_lt_add_one`：ceil_lt_add_one (ha : 0 <= a) : (⌈a⌉₊ : R) < a + 1
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
lemma ceil_lt_add_one (hr : r ≠ ∞) : (⌈r⌉ₑ : ℝ≥0∞) < r + 1 := by
  lift r to ℝ≥0 using hr; simpa using mod_cast Nat.ceil_lt_add_one zero_le

@[bound]
/-
**ENat.ceil_add_le** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ (r s : ENNReal), ⌈r + s⌉ₑ ≤ ⌈r⌉ₑ + ⌈s⌉ₑ
参数：r s : ENNReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `top_add`：top_add (a : α) : ⊤ + a = ⊤
· 使用定理 `add_top`：add_top (a : α) : a + ⊤ = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Nat.ceil_add_le`：ceil_add_le (a b : R) : ⌈a + b⌉₊ <= ⌈a⌉₊ + ⌈b⌉₊
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
-/
lemma ceil_add_le : ∀ (r s : ℝ≥0∞), ⌈r + s⌉ₑ ≤ ⌈r⌉ₑ + ⌈s⌉ₑ
  | ∞, _ => by simp
  | _, ∞ => by simp
  | (r : ℝ≥0), (s : ℝ≥0) => mod_cast Nat.ceil_add_le r s
/-
**ENat.toENNReal_iSup** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {ι : Sort u_1} (f : ι → ℕ∞), ↑(⨆ i, f i) = ⨆ i, ↑(f i)
参数：f : ι → ℕ∞；⨆ i, f i；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma toENNReal_iSup {ι : Sort*} (f : ι → ℕ∞) :
    toENNReal (⨆ i, f i) = ⨆ i, toENNReal (f i) := eq_of_forall_ge_iff fun _ ↦ by simp [← le_floor]
/-
**ENat.toENNReal_iInf** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {ι : Sort u_1} (f : ι → ℕ∞), ↑(⨅ i, f i) = ⨅ i, ↑(f i)
参数：f : ι → ℕ∞；⨅ i, f i；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `eq_of_forall_le_iff`：eq_of_forall_le_iff (H : forall c, c <= a ↔ c <= b)
 : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma toENNReal_iInf {ι : Sort*} (f : ι → ℕ∞) :
    toENNReal (⨅ i, f i) = ⨅ i, toENNReal (f i) := eq_of_forall_le_iff fun _ ↦ by simp [← ceil_le]
/-
**ENat.preimage_toENNReal_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ (a : ENNReal), ENat.toENNReal ⁻¹' Set.Ioi a = Set.Ioi ⌊a⌋ₑ
参数：a : ENNReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma preimage_toENNReal_Ioi (a : ℝ≥0∞) :
    toENNReal ⁻¹' Set.Ioi a = Set.Ioi ⌊a⌋ₑ := by ext; simp
/-
**ENat.preimage_toENNReal_Iio** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ (a : ENNReal), ENat.toENNReal ⁻¹' Set.Iio a = Set.Iio ⌈a⌉ₑ
参数：a : ENNReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma preimage_toENNReal_Iio (a : ℝ≥0∞) :
    toENNReal ⁻¹' Set.Iio a = Set.Iio ⌈a⌉ₑ := by ext; simp
/-
**ENat.preimage_toENNReal_Iic** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ (a : ENNReal), ENat.toENNReal ⁻¹' Set.Iic a = Set.Iic ⌊a⌋ₑ
参数：a : ENNReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma preimage_toENNReal_Iic (a : ℝ≥0∞) :
    toENNReal ⁻¹' Set.Iic a = Set.Iic ⌊a⌋ₑ := by ext; simp
/-
**ENat.preimage_toENNReal_Ici** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ (a : ENNReal), ENat.toENNReal ⁻¹' Set.Ici a = Set.Ici ⌈a⌉ₑ
参数：a : ENNReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma preimage_toENNReal_Ici (a : ℝ≥0∞) :
    toENNReal ⁻¹' Set.Ici a = Set.Ici ⌈a⌉ₑ := by ext; simp
/-
**ENat.preimage_toENNReal_Icc** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ (a b : ENNReal), ENat.toENNReal ⁻¹' Set.Icc a b = Set.Icc ⌈a⌉ₑ ⌊b⌋ₑ
参数：a b : ENNReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma preimage_toENNReal_Icc (a b : ℝ≥0∞) :
    toENNReal ⁻¹' Set.Icc a b = Set.Icc ⌈a⌉ₑ ⌊b⌋ₑ := by ext; simp
/-
**ENat.preimage_toENNReal_Ico** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ (a b : ENNReal), ENat.toENNReal ⁻¹' Set.Ico a b = Set.Ico ⌈a⌉ₑ ⌈b⌉ₑ
参数：a b : ENNReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma preimage_toENNReal_Ico (a b : ℝ≥0∞) :
    toENNReal ⁻¹' Set.Ico a b = Set.Ico ⌈a⌉ₑ ⌈b⌉ₑ := by ext; simp
/-
**ENat.preimage_toENNReal_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ (a b : ENNReal), ENat.toENNReal ⁻¹' Set.Ioc a b = Set.Ioc ⌊a⌋ₑ ⌊b⌋ₑ
参数：a b : ENNReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma preimage_toENNReal_Ioc (a b : ℝ≥0∞) :
    toENNReal ⁻¹' Set.Ioc a b = Set.Ioc ⌊a⌋ₑ ⌊b⌋ₑ := by ext; simp
/-
**ENat.preimage_toENNReal_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ (a b : ENNReal), ENat.toENNReal ⁻¹' Set.Ioo a b = Set.Ioo ⌊a⌋ₑ ⌈b⌉ₑ
参数：a b : ENNReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma preimage_toENNReal_Ioo (a b : ℝ≥0∞) :
    toENNReal ⁻¹' Set.Ioo a b = Set.Ioo ⌊a⌋ₑ ⌈b⌉ₑ := by ext; simp

end ENat

namespace Mathlib.Meta.Positivity
open Lean.Meta Qq

alias ⟨_, natCeil_pos⟩ := ENat.ceil_pos

/-- Extension for the `positivity` tactic: `ENat.ceil` is positive if its input is. -/
@[positivity ⌈_⌉ₑ]
meta def evalENatCeil : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℕ∞), ~q(ENat.ceil $r) =>
    match ← core q(inferInstance) (some q(inferInstance)) r with
    | .positive pr =>
      assertInstancesCommute
      pure (.positive q(natCeil_pos $pr))
    | _ => pure .none
  | _, _, _ => throwError "failed to match on ENat.ceil application"

/-
**Mathlib.Meta.Positivity.** 是 Mathlib 中的一个示例，位于命名空间 `Mathlib.Meta.Positivity`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example {r : ℝ≥0∞} (hr : 0 < r) : 0 < ⌈r⌉ₑ := by positivity

end Mathlib.Meta.Positivity

