/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Data.Fintype.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.RelClasses

import Mathlib.Order.WellFounded


/-!
# Row echelon forms

This file defines the row echelon form of matrices and the leading entries of their rows.

## Main definitions

- `Matrix.IsRowEchelon` expresses that `A` is in row echelon form: an entry of a lower row
  vanishes whenever a higher row is zero at every column strictly to its left.
- `Matrix.IsLeadingEntry`: `c : n` is the leading position of row `i` of `A`.
- `Matrix.IsReducedRowEchelon` additionally requires each leading entry to be `1` and the
  entries above it to vanish.

## Tags

matrix, echelon form

-/

@[expose] public section

universe v

variable {m n : Type*}
variable {R : Type v} {A : Matrix m n R}

namespace Matrix

variable [Zero R]

/-- `A` is in row echelon form: for rows `i₁ < i₂`, if the higher row `i₁` is zero at every
column strictly left of `j₂`, then the lower row `i₂` is zero at `j₂`. -/
/-
**Matrix.IsRowEchelon** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：IsRowEchelon [LT m] [LT n] (A : Matrix m n R) : Prop
参数：A : Matrix m n R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`A` is in row echelon form: for rows `i₁ < i₂`, if the higher row `i₁` is zero a
t every
column strictly left of `j₂`, then the lower row `i₂` is zero at `j₂`.
-/
def IsRowEchelon [LT m] [LT n] (A : Matrix m n R) : Prop :=
  ∀ ⦃i₁ i₂⦄, i₁ < i₂ → ∀ ⦃j₂⦄, (∀ j₁ < j₂, A i₁ j₁ = 0) → A i₂ j₂ = 0

/-- In an echelon matrix, rows below a zero row are zero. -/
/-
**Matrix.IsRowEchelon.row_eq_zero_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsRowE
chelon`。
形式化陈述：∀ {m : Type u_1} {n : Type u_2} {R : Type v} {A : Matrix m n R} [inst : Ze
ro R] [inst_1 : LT m] [inst_2 : LT n]   {i₁ i₂ : m}, A.IsRowEchelon → i₁ < i₂ → 
A i₁ = 0 → A i₂ = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a

--- 原说明 ---
In an echelon matrix, rows below a zero row are zero.
-/
theorem IsRowEchelon.row_eq_zero_of_lt [LT m] [LT n] {i₁ i₂ : m} (he : A.IsRowEchelon)
    (hlt : i₁ < i₂) (h0 : A i₁ = 0) : A i₂ = 0 := by
  funext j
  exact he hlt fun j₁ _ => congrFun h0 j₁

/-! ### Leading entries -/

/-- `c` is the leading position of row `i`. -/
/-
**Matrix.IsLeadingEntry** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：IsLeadingEntry [LT n] (A : Matrix m n R) (i : m) (c : n) : Prop
参数：A : Matrix m n R；i : m；c : n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`c` is the leading position of row `i`.
-/
def IsLeadingEntry [LT n] (A : Matrix m n R) (i : m) (c : n) : Prop :=
  (∀ j < c, A i j = 0) ∧ A i c ≠ 0
/-
**Matrix.IsLeadingEntry.row_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsLeadingE
ntry`。
形式化陈述：∀ {m : Type u_1} {n : Type u_2} {R : Type v} {A : Matrix m n R} [inst : Ze
ro R] [inst_1 : LT n] {i : m} {c : n},   A.IsLeadingEntry i c → A i ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
-/
theorem IsLeadingEntry.row_ne_zero [LT n] {i : m} {c : n} (hc : A.IsLeadingEntry i c) :
    A i ≠ 0 :=
  fun contra => hc.2 (congrFun contra c)
/-
**Matrix.row_ne_zero_iff_exists_isLeadingEntry** 是 Mathlib 中的一个定理，位于命名空间 `Matrix
`。
形式化陈述：row_ne_zero_iff_exists_isLeadingEntry [LT n] [WellFoundedLT n] {i : m} : A
 i != 0 ↔ exists c, A.IsLeadingEntry i c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFounded.has_min`：∀ {α : Type u_4} {r : α → α → Prop}, WellFounded r 
→ ∀ (s : Set α), s.Nonempty → ∃ a ∈ s, ∀ x ∈ s, ¬r x a
· 使用引理 `wellFounded_lt`：wellFounded_lt [LT α] [WellFoundedLT α] : @WellFounded α
 (· < ·)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.ne_iff`：ne_iff {β : α -> Sort*} {f₁ f₂ : forall a, β a} : f₁ !=
 f₂ ↔ exists a, f₁ a != f₂ a
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Matrix.IsLeadingEntry.row_ne_zero`：∀ {m : Type u_1} {n : Type u_2} {R : 
Type v} {A : Matrix m n R} [inst : Zero R] [inst_1 : LT n] {i : m} {c : n},   A.
IsLeadingEntry i c → A …
-/
theorem row_ne_zero_iff_exists_isLeadingEntry [LT n] [WellFoundedLT n] {i : m} :
    A i ≠ 0 ↔ ∃ c, A.IsLeadingEntry i c := by
  refine ⟨fun h => ?_, fun ⟨c, hc⟩ => hc.row_ne_zero⟩
  obtain ⟨c, hc, hmin⟩ := wellFounded_lt.has_min {j | A i j ≠ 0} <| Function.ne_iff.mp h
  refine ⟨c, ?_, hc⟩
  by_contra
  aesop

/-- If column indices have a linear order, then there's at most one leading position per row. -/
/-
**Matrix.IsLeadingEntry.unique** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsLeadingEntry`
。
形式化陈述：∀ {m : Type u_1} {n : Type u_2} {R : Type v} {A : Matrix m n R} [inst : Ze
ro R] [inst_1 : LinearOrder n] {i : m}   {c₁ c₂ : n}, A.IsLeadingEntry i c₁ → A.
IsLeadingEntry i c₂ → c₁ = c₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
If column indices have a linear order, then there's at most one leading position
 per row.
-/
theorem IsLeadingEntry.unique [LinearOrder n] {i : m} {c₁ c₂ : n}
    (h₁ : A.IsLeadingEntry i c₁) (h₂ : A.IsLeadingEntry i c₂) : c₁ = c₂ :=
  le_antisymm (not_lt.mp fun hlt => h₂.2 (h₁.1 c₂ hlt)) (not_lt.mp fun hlt => h₁.2 (h₂.1 c₁ hlt))
/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq R] [Fintype n] [LT n] [DecidableLT n]
    (A : Matrix m n R) (i : m) (c : n) : Decidable (A.IsLeadingEntry i c) :=
  decidable_of_iff ((∀ j < c, A i j = 0) ∧ A i c ≠ 0) Iff.rfl

/-! ### Reduced row echelon form -/

/-- `A` is in reduced row echelon form: it is in row echelon form, each leading entry is
`1`, and entries above a leading entry vanish (entries below one vanish by
`isRowEchelon`). -/
/-
**Matrix.IsReducedRowEchelon** 是 Mathlib 中的一个归纳类型，位于命名空间 `Matrix`。
形式化陈述：{m : Type u_1} → {n : Type u_2} → {R : Type v} → [Zero R] → [LT m] → [LT n
] → [One R] → Matrix m n R → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`A` is in reduced row echelon form: it is in row echelon form, each leading entr
y is
`1`, and entries above a leading entry vanish (entries below one vanish by
`isRowEchelon`).
-/
structure IsReducedRowEchelon [LT m] [LT n] [One R] (A : Matrix m n R) : Prop where
  isRowEchelon : A.IsRowEchelon
  eq_one ⦃i : m⦄ ⦃c : n⦄ (hA : A.IsLeadingEntry i c) : A i c = 1
  eq_zero ⦃i₁ i₂ : m⦄ ⦃c : n⦄ (hlt : i₁ < i₂) (hA : A.IsLeadingEntry i₂ c) : A i₁ c = 0

/-- If the row indices have a linear order, then every entry in a pivot column vanishes
except for the pivot. -/
/-
**Matrix.IsReducedRowEchelon.eq_zero_of_ne_of_isLeadingEntry** 是 Mathlib 中的一个定理，
位于命名空间 `Matrix.IsReducedRowEchelon`。
形式化陈述：∀ {m : Type u_1} {n : Type u_2} {R : Type v} {A : Matrix m n R} [inst : Ze
ro R] [inst_1 : LinearOrder m] [inst_2 : LT n]   [inst_3 : One R] {i₁ i₂ : m} {c
 : n}, A.IsReducedRowEchelon → i₁ ≠ i₂ → A.IsLeadingEntry i₂ c → A i₁ c = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `Matrix.IsReducedRowEchelon.eq_zero`：∀ {m : Type u_1} {n : Type u_2} {R :
 Type v} [inst : Zero R] [inst_1 : LT m] [inst_2 : LT n] [inst_3 : One R]   {A :
 Matrix m n R}, A.IsRedu…
· 使用定理 `Matrix.IsReducedRowEchelon.isRowEchelon`：∀ {m : Type u_1} {n : Type u_2}
 {R : Type v} [inst : Zero R] [inst_1 : LT m] [inst_2 : LT n] [inst_3 : One R]  
 {A : Matrix m n R}, A.IsRedu…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
If the row indices have a linear order, then every entry in a pivot column vanis
hes
except for the pivot.
-/
theorem IsReducedRowEchelon.eq_zero_of_ne_of_isLeadingEntry [LinearOrder m] [LT n] [One R]
    {i₁ i₂ : m} {c : n} (hA : A.IsReducedRowEchelon) (hne : i₁ ≠ i₂)
    (hlead : A.IsLeadingEntry i₂ c) : A i₁ c = 0 := by
  rcases hne.lt_or_gt with hlt | hlt
  · exact hA.eq_zero hlt hlead
  · exact hA.isRowEchelon hlt hlead.1

end Matrix

