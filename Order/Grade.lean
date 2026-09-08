/-
Copyright (c) 2022 Yaël Dillies, Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Violeta Hernández Palacios, Grayson Burton, Vladimir Ivanov
-/
module

public import Mathlib.Data.Int.SuccPred
public import Mathlib.Order.Fin.Basic

/-!
# Graded orders

This file defines graded orders, also known as ranked orders.

An `𝕆`-graded order is an order `α` equipped with a distinguished "grade" function `α → 𝕆` which
should be understood as giving the "height" of the elements. Usual graded orders are `ℕ`-graded,
cograded orders are `ℕᵒᵈ`-graded, but we can also grade by `ℤ`, and polytopes are naturally
`Fin n`-graded.

Visually, `grade ℕ a` is the height of `a` in the Hasse diagram of `α`.

## Main declarations

* `GradeOrder`: Graded order.
* `GradeMinOrder`: Graded order where minimal elements have minimal grades.
* `GradeMaxOrder`: Graded order where maximal elements have maximal grades.
* `GradeBoundedOrder`: Graded order where minimal elements have minimal grades and maximal
  elements have maximal grades.
* `grade`: The grade of an element. Because an order can admit several gradings, the first argument
  is the order we grade by.

## How to grade your order

Here are the translations between common references and our `GradeOrder`:
* [Stanley][stanley2012] defines a graded order of rank `n` as an order where all maximal chains
  have "length" `n` (so the number of elements of a chain is `n + 1`). This corresponds to
  `GradeBoundedOrder (Fin (n + 1)) α`.
* [Engel][engel1997]'s ranked orders are somewhere between `GradeOrder ℕ α` and
  `GradeMinOrder ℕ α`, in that he requires `∃ a, IsMin a ∧ grade ℕ a = 0` rather than
  `∀ a, IsMin a → grade ℕ a = 0`. He defines a graded order as an order where all minimal elements
  have grade `0` and all maximal elements have the same grade. This is roughly a less bundled
  version of `GradeBoundedOrder (Fin n) α`, assuming we discard orders with infinite chains.

## Implementation notes

One possible definition of graded orders is as the bounded orders whose flags (maximal chains)
all have the same finite length (see Stanley p. 99). However, this means that all graded orders must
have minimal and maximal elements and that the grade is not data.

Instead, we define graded orders by their grade function, without talking about flags yet.

## References

* [Konrad Engel, *Sperner Theory*][engel1997]
* [Richard Stanley, *Enumerative Combinatorics*][stanley2012]
-/

@[expose] public section

open Nat OrderDual

variable {𝕆 ℙ α β : Type*}

/-- An `𝕆`-graded order is an order `α` equipped with a strictly monotone function
`grade 𝕆 : α → 𝕆` which preserves order covering (`CovBy`). -/
/-
**GradeOrder** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(𝕆 : Type u_5) → (α : Type u_6) → [Preorder 𝕆] → [Preorder α] → Type (max 
u_5 u_6)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `𝕆`-graded order is an order `α` equipped with a strictly monotone function
`grade 𝕆 : α → 𝕆` which preserves order covering (`CovBy`).
-/
class GradeOrder (𝕆 α : Type*) [Preorder 𝕆] [Preorder α] where
  /-- The grading function. -/
  protected grade : α → 𝕆
  /-- `grade` is strictly monotonic. -/
  grade_strictMono : StrictMono grade
  /-- `grade` preserves `CovBy`. -/
  covBy_grade ⦃a b : α⦄ : a ⋖ b → grade a ⋖ grade b

/-- An `𝕆`-graded order where minimal elements have minimal grades. -/
/-
**GradeMinOrder** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(𝕆 : Type u_5) → (α : Type u_6) → [Preorder 𝕆] → [Preorder α] → Type (max 
u_5 u_6)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `𝕆`-graded order where minimal elements have minimal grades.
-/
class GradeMinOrder (𝕆 α : Type*) [Preorder 𝕆] [Preorder α] extends GradeOrder 𝕆 α where
  /-- Minimal elements have minimal grades. -/
  isMin_grade ⦃a : α⦄ : IsMin a → IsMin (grade a)

/-- An `𝕆`-graded order where maximal elements have maximal grades. -/
/-
**GradeMaxOrder** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(𝕆 : Type u_5) → (α : Type u_6) → [Preorder 𝕆] → [Preorder α] → Type (max 
u_5 u_6)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `𝕆`-graded order where maximal elements have maximal grades.
-/
class GradeMaxOrder (𝕆 α : Type*) [Preorder 𝕆] [Preorder α] extends GradeOrder 𝕆 α where
  /-- Maximal elements have maximal grades. -/
  isMax_grade ⦃a : α⦄ : IsMax a → IsMax (grade a)

/-- An `𝕆`-graded order where minimal elements have minimal grades and maximal elements have maximal
grades. -/
/-
**GradeBoundedOrder** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(𝕆 : Type u_5) → (α : Type u_6) → [Preorder 𝕆] → [Preorder α] → Type (max 
u_5 u_6)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `𝕆`-graded order where minimal elements have minimal grades and maximal eleme
nts have maximal
grades.
-/
class GradeBoundedOrder (𝕆 α : Type*) [Preorder 𝕆] [Preorder α] extends GradeMinOrder 𝕆 α,
  GradeMaxOrder 𝕆 α

section Preorder -- grading
variable [Preorder 𝕆]

section Preorder -- graded order
variable [Preorder α]

section GradeOrder
variable (𝕆)
variable [GradeOrder 𝕆 α] {a b : α}

/-- The grade of an element in a graded order. Morally, this is the number of elements you need to
go down by to get to `⊥`. -/
/-
**grade** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：grade : α -> 𝕆
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The grade of an element in a graded order. Morally, this is the number of elemen
ts you need to
go down by to get to `⊥`.
-/
def grade : α → 𝕆 :=
  GradeOrder.grade
/-
**CovBy.grade** 是 Mathlib 中的一个定理，位于命名空间 `CovBy`。
形式化陈述：∀ (𝕆 : Type u_1) {α : Type u_3} [inst : Preorder 𝕆] [inst_1 : Preorder α] 
[inst_2 : GradeOrder 𝕆 α] {a b : α},   a ⋖ b → grade 𝕆 a ⋖ grade 𝕆 b
参数：𝕆 : Type u_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GradeOrder.covBy_grade`：∀ {𝕆 : Type u_5} {α : Type u_6} {inst : Preorder
 𝕆} {inst_1 : Preorder α} [self : GradeOrder 𝕆 α] ⦃a b : α⦄,   a ⋖ b → GradeOrde
r.grade a ⋖ …
-/
protected theorem CovBy.grade (h : a ⋖ b) : grade 𝕆 a ⋖ grade 𝕆 b :=
  GradeOrder.covBy_grade h

variable {𝕆}
/-
**grade_strictMono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：grade_strictMono : StrictMono (grade 𝕆 : α -> 𝕆)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GradeOrder.grade_strictMono`：∀ {𝕆 : Type u_5} {α : Type u_6} {inst : Pre
order 𝕆} {inst_1 : Preorder α} [self : GradeOrder 𝕆 α],   StrictMono GradeOrder.
grade
-/
theorem grade_strictMono : StrictMono (grade 𝕆 : α → 𝕆) :=
  GradeOrder.grade_strictMono
/-
**covBy_iff_lt_covBy_grade** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：covBy_iff_lt_covBy_grade : a ⋖ b ↔ a < b ∧ grade 𝕆 a ⋖ grade 𝕆 b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `CovBy.grade`：∀ (𝕆 : Type u_1) {α : Type u_3} [inst : Preorder 𝕆] [inst_1
 : Preorder α] [inst_2 : GradeOrder 𝕆 α] {a b : α},   a ⋖ b → grade 𝕆 a ⋖ grade 
𝕆…
· 使用定理 `And.imp_right`：∀ {a b c : Prop}, (a → b) → c ∧ a → c ∧ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `grade_strictMono`：grade_strictMono : StrictMono (grade 𝕆 : α -> 𝕆)
-/
theorem covBy_iff_lt_covBy_grade : a ⋖ b ↔ a < b ∧ grade 𝕆 a ⋖ grade 𝕆 b :=
  ⟨fun h => ⟨h.1, h.grade _⟩,
    And.imp_right fun h _ ha hb => h.2 (grade_strictMono ha) <| grade_strictMono hb⟩

end GradeOrder

section GradeMinOrder

variable (𝕆)
variable [GradeMinOrder 𝕆 α] {a : α}

/-
**IsMin.grade** 是 Mathlib 中的一个定理，位于命名空间 `IsMin`。
形式化陈述：∀ (𝕆 : Type u_1) {α : Type u_3} [inst : Preorder 𝕆] [inst_1 : Preorder α] 
[inst_2 : GradeMinOrder 𝕆 α] {a : α},   IsMin a → IsMin (grade 𝕆 a)
参数：𝕆 : Type u_1；grade 𝕆 a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GradeMinOrder.isMin_grade`：∀ {𝕆 : Type u_5} {α : Type u_6} {inst : Preor
der 𝕆} {inst_1 : Preorder α} [self : GradeMinOrder 𝕆 α] ⦃a : α⦄,   IsMin a → IsM
in (GradeOrder.…
-/
protected theorem IsMin.grade (h : IsMin a) : IsMin (grade 𝕆 a) :=
  GradeMinOrder.isMin_grade h

variable {𝕆}

@[simp]
/-
**isMin_grade_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isMin_grade_iff : IsMin (grade 𝕆 a) ↔ IsMin a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.isMin_of_apply`：∀ {α : Type u} {β : Type v} [inst : Preorder 
α] [inst_1 : Preorder β] {f : α → β} {a : α},   StrictMono f → IsMin (f a) → IsM
in a
· 使用定理 `grade_strictMono`：grade_strictMono : StrictMono (grade 𝕆 : α -> 𝕆)
· 使用定理 `IsMin.grade`：∀ (𝕆 : Type u_1) {α : Type u_3} [inst : Preorder 𝕆] [inst_1
 : Preorder α] [inst_2 : GradeMinOrder 𝕆 α] {a : α},   IsMin a → IsMin (grade 𝕆 
a…
-/
theorem isMin_grade_iff : IsMin (grade 𝕆 a) ↔ IsMin a :=
  ⟨grade_strictMono.isMin_of_apply, IsMin.grade _⟩

end GradeMinOrder

section GradeMaxOrder

variable (𝕆)
variable [GradeMaxOrder 𝕆 α] {a : α}

/-
**IsMax.grade** 是 Mathlib 中的一个定理，位于命名空间 `IsMax`。
形式化陈述：∀ (𝕆 : Type u_1) {α : Type u_3} [inst : Preorder 𝕆] [inst_1 : Preorder α] 
[inst_2 : GradeMaxOrder 𝕆 α] {a : α},   IsMax a → IsMax (grade 𝕆 a)
参数：𝕆 : Type u_1；grade 𝕆 a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GradeMaxOrder.isMax_grade`：∀ {𝕆 : Type u_5} {α : Type u_6} {inst : Preor
der 𝕆} {inst_1 : Preorder α} [self : GradeMaxOrder 𝕆 α] ⦃a : α⦄,   IsMax a → IsM
ax (GradeOrder.…
-/
protected theorem IsMax.grade (h : IsMax a) : IsMax (grade 𝕆 a) :=
  GradeMaxOrder.isMax_grade h

variable {𝕆}

@[simp]
/-
**isMax_grade_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isMax_grade_iff : IsMax (grade 𝕆 a) ↔ IsMax a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.isMax_of_apply`：StrictMono.isMax_of_apply (hf : StrictMono f)
 (ha : IsMax (f a)) : IsMax a
· 使用定理 `grade_strictMono`：grade_strictMono : StrictMono (grade 𝕆 : α -> 𝕆)
· 使用定理 `IsMax.grade`：∀ (𝕆 : Type u_1) {α : Type u_3} [inst : Preorder 𝕆] [inst_1
 : Preorder α] [inst_2 : GradeMaxOrder 𝕆 α] {a : α},   IsMax a → IsMax (grade 𝕆 
a…
-/
theorem isMax_grade_iff : IsMax (grade 𝕆 a) ↔ IsMax a :=
  ⟨grade_strictMono.isMax_of_apply, IsMax.grade _⟩

end GradeMaxOrder

end Preorder

-- graded order
/-
**grade_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：grade_mono [PartialOrder α] [GradeOrder 𝕆 α] : Monotone (grade 𝕆 : α -> 𝕆)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `grade_strictMono`：grade_strictMono : StrictMono (grade 𝕆 : α -> 𝕆)
-/
theorem grade_mono [PartialOrder α] [GradeOrder 𝕆 α] : Monotone (grade 𝕆 : α → 𝕆) :=
  grade_strictMono.monotone

section LinearOrder

-- graded order
variable [LinearOrder α] [GradeOrder 𝕆 α] {a b : α}

/-
**grade_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：grade_injective : Function.Injective (grade 𝕆 : α -> 𝕆)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用定理 `grade_strictMono`：grade_strictMono : StrictMono (grade 𝕆 : α -> 𝕆)
-/
theorem grade_injective : Function.Injective (grade 𝕆 : α → 𝕆) :=
  grade_strictMono.injective

@[simp]
/-
**grade_le_grade_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：grade_le_grade_iff : grade 𝕆 a <= grade 𝕆 b ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用定理 `grade_strictMono`：grade_strictMono : StrictMono (grade 𝕆 : α -> 𝕆)
-/
theorem grade_le_grade_iff : grade 𝕆 a ≤ grade 𝕆 b ↔ a ≤ b :=
  grade_strictMono.le_iff_le

@[simp]
/-
**grade_lt_grade_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：grade_lt_grade_iff : grade 𝕆 a < grade 𝕆 b ↔ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用定理 `grade_strictMono`：grade_strictMono : StrictMono (grade 𝕆 : α -> 𝕆)
-/
theorem grade_lt_grade_iff : grade 𝕆 a < grade 𝕆 b ↔ a < b :=
  grade_strictMono.lt_iff_lt

@[simp]
/-
**grade_eq_grade_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：grade_eq_grade_iff : grade 𝕆 a = grade 𝕆 b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `grade_injective`：grade_injective : Function.Injective (grade 𝕆 : α -> 𝕆)
-/
theorem grade_eq_grade_iff : grade 𝕆 a = grade 𝕆 b ↔ a = b :=
  grade_injective.eq_iff
/-
**grade_ne_grade_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：grade_ne_grade_iff : grade 𝕆 a != grade 𝕆 b ↔ a != b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.ne_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {x y : α}, f x ≠ f y ↔ x ≠ y
· 使用定理 `grade_injective`：grade_injective : Function.Injective (grade 𝕆 : α -> 𝕆)
-/
theorem grade_ne_grade_iff : grade 𝕆 a ≠ grade 𝕆 b ↔ a ≠ b :=
  grade_injective.ne_iff
/-
**grade_covBy_grade_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：grade_covBy_grade_iff : grade 𝕆 a ⋖ grade 𝕆 b ↔ a ⋖ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `covBy_iff_lt_covBy_grade`：covBy_iff_lt_covBy_grade : a ⋖ b ↔ a < b ∧ gra
de 𝕆 a ⋖ grade 𝕆 b
· 使用定理 `and_iff_right_of_imp`：∀ {b a : Prop}, (b → a) → (a ∧ b ↔ b)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `grade_lt_grade_iff`：grade_lt_grade_iff : grade 𝕆 a < grade 𝕆 b ↔ a < b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem grade_covBy_grade_iff : grade 𝕆 a ⋖ grade 𝕆 b ↔ a ⋖ b :=
  (covBy_iff_lt_covBy_grade.trans <| and_iff_right_of_imp fun h => grade_lt_grade_iff.1 h.1).symm

end LinearOrder

-- graded order
end Preorder

-- grading
section PartialOrder

variable [PartialOrder 𝕆] [Preorder α]

@[simp]
/-
**grade_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：grade_bot [OrderBot 𝕆] [OrderBot α] [GradeMinOrder 𝕆 α] : grade 𝕆 (⊥ : α) 
= ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMin.eq_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot 
α] {a : α}, IsMin a → a = ⊥
· 使用定理 `IsMin.grade`：∀ (𝕆 : Type u_1) {α : Type u_3} [inst : Preorder 𝕆] [inst_1
 : Preorder α] [inst_2 : GradeMinOrder 𝕆 α] {a : α},   IsMin a → IsMin (grade 𝕆 
a…
· 使用定理 `isMin_bot`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α], IsM
in ⊥
-/
theorem grade_bot [OrderBot 𝕆] [OrderBot α] [GradeMinOrder 𝕆 α] : grade 𝕆 (⊥ : α) = ⊥ :=
  (isMin_bot.grade _).eq_bot

@[simp]
/-
**grade_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：grade_top [OrderTop 𝕆] [OrderTop α] [GradeMaxOrder 𝕆 α] : grade 𝕆 (⊤ : α) 
= ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMax.eq_top`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderTop 
α] {a : α}, IsMax a → a = ⊤
· 使用定理 `IsMax.grade`：∀ (𝕆 : Type u_1) {α : Type u_3} [inst : Preorder 𝕆] [inst_1
 : Preorder α] [inst_2 : GradeMaxOrder 𝕆 α] {a : α},   IsMax a → IsMax (grade 𝕆 
a…
· 使用定理 `isMax_top`：isMax_top : IsMax (⊤ : α)
-/
theorem grade_top [OrderTop 𝕆] [OrderTop α] [GradeMaxOrder 𝕆 α] : grade 𝕆 (⊤ : α) = ⊤ :=
  (isMax_top.grade _).eq_top

end PartialOrder

/-! ### Instances -/

section Preorder
variable [Preorder 𝕆] [Preorder ℙ] [Preorder α] [Preorder β]

/-
**Preorder.toGradeBoundedOrder** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Preorder.toGradeBoundedOrder : GradeBoundedOrder α α where grade
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `strictMono_id`：strictMono_id [Preorder α] : StrictMono (id : α -> α)
-/
instance Preorder.toGradeBoundedOrder : GradeBoundedOrder α α where
  grade := id
  isMin_grade _ := id
  isMax_grade _ := id
  grade_strictMono := strictMono_id
  covBy_grade _ _ := id

@[simp]
/-
**grade_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：grade_self (a : α) : grade α a = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem grade_self (a : α) : grade α a = a :=
  rfl

/-! #### Dual -/

/-
**OrderDual.gradeOrder** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OrderDual.gradeOrder [GradeOrder 𝕆 α] : GradeOrder 𝕆ᵒᵈ αᵒᵈ where grade
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
#### Dual
-/
instance OrderDual.gradeOrder [GradeOrder 𝕆 α] : GradeOrder 𝕆ᵒᵈ αᵒᵈ where
  grade := toDual ∘ grade 𝕆 ∘ ofDual
  grade_strictMono := grade_strictMono.dual
  covBy_grade _ _ h := (h.ofDual.grade _).toDual
/-
**OrderDual.gradeMinOrder** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OrderDual.gradeMinOrder [GradeMaxOrder 𝕆 α] : GradeMinOrder 𝕆ᵒᵈ αᵒᵈ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMax.grade`：∀ (𝕆 : Type u_1) {α : Type u_3} [inst : Preorder 𝕆] [inst_1
 : Preorder α] [inst_2 : GradeMaxOrder 𝕆 α] {a : α},   IsMax a → IsMax (grade 𝕆 
a…
-/
instance OrderDual.gradeMinOrder [GradeMaxOrder 𝕆 α] : GradeMinOrder 𝕆ᵒᵈ αᵒᵈ :=
  { OrderDual.gradeOrder with isMin_grade := fun _ => IsMax.grade (α := α) 𝕆 }
/-
**OrderDual.gradeMaxOrder** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OrderDual.gradeMaxOrder [GradeMinOrder 𝕆 α] : GradeMaxOrder 𝕆ᵒᵈ αᵒᵈ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMin.grade`：∀ (𝕆 : Type u_1) {α : Type u_3} [inst : Preorder 𝕆] [inst_1
 : Preorder α] [inst_2 : GradeMinOrder 𝕆 α] {a : α},   IsMin a → IsMin (grade 𝕆 
a…
-/
instance OrderDual.gradeMaxOrder [GradeMinOrder 𝕆 α] : GradeMaxOrder 𝕆ᵒᵈ αᵒᵈ :=
  { OrderDual.gradeOrder with isMax_grade := fun _ => IsMin.grade (α := α) 𝕆 }
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [GradeBoundedOrder 𝕆 α] : GradeBoundedOrder 𝕆ᵒᵈ αᵒᵈ :=
  { OrderDual.gradeMinOrder, OrderDual.gradeMaxOrder with }

@[simp]
/-
**grade_toDual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：grade_toDual [GradeOrder 𝕆 α] (a : α) : grade 𝕆ᵒᵈ (toDual a) = toDual (gra
de 𝕆 a)
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem grade_toDual [GradeOrder 𝕆 α] (a : α) : grade 𝕆ᵒᵈ (toDual a) = toDual (grade 𝕆 a) :=
  rfl

@[simp]
/-
**grade_ofDual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：grade_ofDual [GradeOrder 𝕆 α] (a : αᵒᵈ) : grade 𝕆 (ofDual a) = ofDual (gra
de 𝕆ᵒᵈ a)
参数：a : αᵒᵈ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem grade_ofDual [GradeOrder 𝕆 α] (a : αᵒᵈ) : grade 𝕆 (ofDual a) = ofDual (grade 𝕆ᵒᵈ a) :=
  rfl

/-! #### Lifting a graded order -/

-- See note [reducible non-instances]
/-- Lifts a graded order along a strictly monotone function. -/
/-
**GradeOrder.liftLeft** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：GradeOrder.liftLeft [GradeOrder 𝕆 α] (f : 𝕆 -> ℙ) (hf : StrictMono f) (hco
vBy : forall a b, a ⋖ b -> f a ⋖ f b) : GradeOrder ℙ α where grade
参数：f : 𝕆 -> ℙ；hf : StrictMono f；hcovBy : forall a b, a ⋖ b -> f a ⋖ f b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lifts a graded order along a strictly monotone function.
-/
abbrev GradeOrder.liftLeft [GradeOrder 𝕆 α] (f : 𝕆 → ℙ) (hf : StrictMono f)
    (hcovBy : ∀ a b, a ⋖ b → f a ⋖ f b) : GradeOrder ℙ α where
  grade := f ∘ grade 𝕆
  grade_strictMono := hf.comp grade_strictMono
  covBy_grade _ _ h := hcovBy _ _ <| h.grade _

-- See note [reducible non-instances]
/-- Lifts a graded order along a strictly monotone function. -/
/-
**GradeMinOrder.liftLeft** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：GradeMinOrder.liftLeft [GradeMinOrder 𝕆 α] (f : 𝕆 -> ℙ) (hf : StrictMono f
) (hcovBy : forall a b, a ⋖ b -> f a ⋖ f b) (hmin : forall a, IsMin a -> IsMin (
f a)) : GradeMinOrder ℙ α
参数：f : 𝕆 -> ℙ；hf : StrictMono f；hcovBy : forall a b, a ⋖ b -> f a ⋖ f b；hmin : f
orall a, IsMin a -> IsMin (f a)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lifts a graded order along a strictly monotone function.
-/
abbrev GradeMinOrder.liftLeft [GradeMinOrder 𝕆 α] (f : 𝕆 → ℙ) (hf : StrictMono f)
    (hcovBy : ∀ a b, a ⋖ b → f a ⋖ f b) (hmin : ∀ a, IsMin a → IsMin (f a)) : GradeMinOrder ℙ α :=
  { GradeOrder.liftLeft f hf hcovBy with isMin_grade := fun _ ha => hmin _ <| ha.grade _ }

-- See note [reducible non-instances]
/-- Lifts a graded order along a strictly monotone function. -/
/-
**GradeMaxOrder.liftLeft** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：GradeMaxOrder.liftLeft [GradeMaxOrder 𝕆 α] (f : 𝕆 -> ℙ) (hf : StrictMono f
) (hcovBy : forall a b, a ⋖ b -> f a ⋖ f b) (hmax : forall a, IsMax a -> IsMax (
f a)) : GradeMaxOrder ℙ α
参数：f : 𝕆 -> ℙ；hf : StrictMono f；hcovBy : forall a b, a ⋖ b -> f a ⋖ f b；hmax : f
orall a, IsMax a -> IsMax (f a)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lifts a graded order along a strictly monotone function.
-/
abbrev GradeMaxOrder.liftLeft [GradeMaxOrder 𝕆 α] (f : 𝕆 → ℙ) (hf : StrictMono f)
    (hcovBy : ∀ a b, a ⋖ b → f a ⋖ f b) (hmax : ∀ a, IsMax a → IsMax (f a)) : GradeMaxOrder ℙ α :=
  { GradeOrder.liftLeft f hf hcovBy with isMax_grade := fun _ ha => hmax _ <| ha.grade _ }

-- See note [reducible non-instances]
/-- Lifts a graded order along a strictly monotone function. -/
/-
**GradeBoundedOrder.liftLeft** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：GradeBoundedOrder.liftLeft [GradeBoundedOrder 𝕆 α] (f : 𝕆 -> ℙ) (hf : Stri
ctMono f) (hcovBy : forall a b, a ⋖ b -> f a ⋖ f b) (hmin : forall a, IsMin a ->
 IsMin (f a)) (hmax : forall a, IsMax a -> IsMax (f a)) : GradeBoundedOrder ℙ α
参数：f : 𝕆 -> ℙ；hf : StrictMono f；hcovBy : forall a b, a ⋖ b -> f a ⋖ f b；hmin : f
orall a, IsMin a -> IsMin (f a)；hmax : forall a, IsMax a -> IsMax (f a)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `GradeMaxOrder.isMax_grade`：∀ {𝕆 : Type u_5} {α : Type u_6} {inst : Preor
der 𝕆} {inst_1 : Preorder α} [self : GradeMaxOrder 𝕆 α] ⦃a : α⦄,   IsMax a → IsM
ax (GradeOrder.…

--- 原说明 ---
Lifts a graded order along a strictly monotone function.
-/
abbrev GradeBoundedOrder.liftLeft [GradeBoundedOrder 𝕆 α] (f : 𝕆 → ℙ) (hf : StrictMono f)
    (hcovBy : ∀ a b, a ⋖ b → f a ⋖ f b) (hmin : ∀ a, IsMin a → IsMin (f a))
    (hmax : ∀ a, IsMax a → IsMax (f a)) : GradeBoundedOrder ℙ α :=
  { GradeMinOrder.liftLeft f hf hcovBy hmin, GradeMaxOrder.liftLeft f hf hcovBy hmax with }

-- See note [reducible non-instances]
/-- Lifts a graded order along a strictly monotone function. -/
/-
**GradeOrder.liftRight** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：GradeOrder.liftRight [GradeOrder 𝕆 β] (f : α -> β) (hf : StrictMono f) (hc
ovBy : forall a b, a ⋖ b -> f a ⋖ f b) : GradeOrder 𝕆 α where grade
参数：f : α -> β；hf : StrictMono f；hcovBy : forall a b, a ⋖ b -> f a ⋖ f b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lifts a graded order along a strictly monotone function.
-/
abbrev GradeOrder.liftRight [GradeOrder 𝕆 β] (f : α → β) (hf : StrictMono f)
    (hcovBy : ∀ a b, a ⋖ b → f a ⋖ f b) : GradeOrder 𝕆 α where
  grade := grade 𝕆 ∘ f
  grade_strictMono := grade_strictMono.comp hf
  covBy_grade _ _ h := (hcovBy _ _ h).grade _

-- See note [reducible non-instances]
/-- Lifts a graded order along a strictly monotone function. -/
/-
**GradeMinOrder.liftRight** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：GradeMinOrder.liftRight [GradeMinOrder 𝕆 β] (f : α -> β) (hf : StrictMono 
f) (hcovBy : forall a b, a ⋖ b -> f a ⋖ f b) (hmin : forall a, IsMin a -> IsMin 
(f a)) : GradeMinOrder 𝕆 α
参数：f : α -> β；hf : StrictMono f；hcovBy : forall a b, a ⋖ b -> f a ⋖ f b；hmin : f
orall a, IsMin a -> IsMin (f a)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lifts a graded order along a strictly monotone function.
-/
abbrev GradeMinOrder.liftRight [GradeMinOrder 𝕆 β] (f : α → β) (hf : StrictMono f)
    (hcovBy : ∀ a b, a ⋖ b → f a ⋖ f b) (hmin : ∀ a, IsMin a → IsMin (f a)) : GradeMinOrder 𝕆 α :=
  { GradeOrder.liftRight f hf hcovBy with isMin_grade := fun _ ha => (hmin _ ha).grade _ }

-- See note [reducible non-instances]
/-- Lifts a graded order along a strictly monotone function. -/
/-
**GradeMaxOrder.liftRight** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：GradeMaxOrder.liftRight [GradeMaxOrder 𝕆 β] (f : α -> β) (hf : StrictMono 
f) (hcovBy : forall a b, a ⋖ b -> f a ⋖ f b) (hmax : forall a, IsMax a -> IsMax 
(f a)) : GradeMaxOrder 𝕆 α
参数：f : α -> β；hf : StrictMono f；hcovBy : forall a b, a ⋖ b -> f a ⋖ f b；hmax : f
orall a, IsMax a -> IsMax (f a)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lifts a graded order along a strictly monotone function.
-/
abbrev GradeMaxOrder.liftRight [GradeMaxOrder 𝕆 β] (f : α → β) (hf : StrictMono f)
    (hcovBy : ∀ a b, a ⋖ b → f a ⋖ f b) (hmax : ∀ a, IsMax a → IsMax (f a)) : GradeMaxOrder 𝕆 α :=
  { GradeOrder.liftRight f hf hcovBy with isMax_grade := fun _ ha => (hmax _ ha).grade _ }

-- See note [reducible non-instances]
/-- Lifts a graded order along a strictly monotone function. -/
/-
**GradeBoundedOrder.liftRight** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：GradeBoundedOrder.liftRight [GradeBoundedOrder 𝕆 β] (f : α -> β) (hf : Str
ictMono f) (hcovBy : forall a b, a ⋖ b -> f a ⋖ f b) (hmin : forall a, IsMin a -
> IsMin (f a)) (hmax : forall a, IsMax a -> IsMax (f a)) : GradeBoundedOrder 𝕆 α
参数：f : α -> β；hf : StrictMono f；hcovBy : forall a b, a ⋖ b -> f a ⋖ f b；hmin : f
orall a, IsMin a -> IsMin (f a)；hmax : forall a, IsMax a -> IsMax (f a)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `GradeMaxOrder.isMax_grade`：∀ {𝕆 : Type u_5} {α : Type u_6} {inst : Preor
der 𝕆} {inst_1 : Preorder α} [self : GradeMaxOrder 𝕆 α] ⦃a : α⦄,   IsMax a → IsM
ax (GradeOrder.…

--- 原说明 ---
Lifts a graded order along a strictly monotone function.
-/
abbrev GradeBoundedOrder.liftRight [GradeBoundedOrder 𝕆 β] (f : α → β) (hf : StrictMono f)
    (hcovBy : ∀ a b, a ⋖ b → f a ⋖ f b) (hmin : ∀ a, IsMin a → IsMin (f a))
    (hmax : ∀ a, IsMax a → IsMax (f a)) : GradeBoundedOrder 𝕆 α :=
  { GradeMinOrder.liftRight f hf hcovBy hmin, GradeMaxOrder.liftRight f hf hcovBy hmax with }

/-! #### `Fin n`-graded to `ℕ`-graded to `ℤ`-graded -/


-- See note [reducible non-instances]
/-- A `Fin n`-graded order is also `ℕ`-graded. We do not mark this an instance because `n` is not
inferable. -/
/-
**GradeOrder.finToNat** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：GradeOrder.finToNat (n : Nat) [GradeOrder (Fin n) α] : GradeOrder Nat α
参数：n : Nat；Fin n。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.val_strictMono`：val_strictMono : StrictMono (val : Fin n -> Nat)
· 使用定理 `CovBy.coe_fin`：∀ {n : ℕ} {a b : Fin n}, a ⋖ b → ↑a ⋖ ↑b

--- 原说明 ---
A `Fin n`-graded order is also `ℕ`-graded. We do not mark this an instance becau
se `n` is not
inferable.
-/
abbrev GradeOrder.finToNat (n : ℕ) [GradeOrder (Fin n) α] : GradeOrder ℕ α :=
  (GradeOrder.liftLeft (_ : Fin n → ℕ) Fin.val_strictMono) fun _ _ => CovBy.coe_fin

-- See note [reducible non-instances]
/-- A `Fin n`-graded order is also `ℕ`-graded. We do not mark this an instance because `n` is not
inferable. -/
/-
**GradeMinOrder.finToNat** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：GradeMinOrder.finToNat (n : Nat) [GradeMinOrder (Fin n) α] : GradeMinOrder
 Nat α
参数：n : Nat；Fin n。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.val_strictMono`：val_strictMono : StrictMono (val : Fin n -> Nat)
· 使用定理 `CovBy.coe_fin`：∀ {n : ℕ} {a b : Fin n}, a ⋖ b → ↑a ⋖ ↑b

--- 原说明 ---
A `Fin n`-graded order is also `ℕ`-graded. We do not mark this an instance becau
se `n` is not
inferable.
-/
abbrev GradeMinOrder.finToNat (n : ℕ) [GradeMinOrder (Fin n) α] : GradeMinOrder ℕ α :=
  (GradeMinOrder.liftLeft (_ : Fin n → ℕ) Fin.val_strictMono fun _ _ => CovBy.coe_fin) fun a h => by
    cases n
    · exact a.elim0
    rw [h.eq_bot, bot_eq_zero]
    exact isMin_bot
/-
**GradeOrder.natToInt** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：GradeOrder.natToInt [GradeOrder Nat α] : GradeOrder Int α
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.natCast_strictMono`：natCast_strictMono : StrictMono (· : Nat -> Int)
· 使用定理 `CovBy.intCast`：∀ {a b : ℕ}, a ⋖ b → ↑a ⋖ ↑b
-/
instance GradeOrder.natToInt [GradeOrder ℕ α] : GradeOrder ℤ α :=
  (GradeOrder.liftLeft _ Int.natCast_strictMono) fun _ _ => CovBy.intCast
/-
**GradeOrder.wellFoundedLT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：GradeOrder.wellFoundedLT (𝕆 : Type*) [Preorder 𝕆] [GradeOrder 𝕆 α] [WellFo
undedLT 𝕆] : WellFoundedLT α
参数：𝕆 : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.wellFoundedLT`：StrictMono.wellFoundedLT [WellFoundedLT β] (hf
 : StrictMono f) : WellFoundedLT α
· 使用定理 `GradeOrder.grade_strictMono`：∀ {𝕆 : Type u_5} {α : Type u_6} {inst : Pre
order 𝕆} {inst_1 : Preorder α} [self : GradeOrder 𝕆 α],   StrictMono GradeOrder.
grade
-/
theorem GradeOrder.wellFoundedLT (𝕆 : Type*) [Preorder 𝕆] [GradeOrder 𝕆 α]
    [WellFoundedLT 𝕆] : WellFoundedLT α :=
  (grade_strictMono (𝕆 := 𝕆)).wellFoundedLT
/-
**GradeOrder.wellFoundedGT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：GradeOrder.wellFoundedGT (𝕆 : Type*) [Preorder 𝕆] [GradeOrder 𝕆 α] [WellFo
undedGT 𝕆] : WellFoundedGT α
参数：𝕆 : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.wellFoundedGT`：∀ {α : Type u} {β : Type v} [inst : Preorder α
] [inst_1 : Preorder β] {f : α → β} [WellFoundedGT β],   StrictMono f → WellFoun
dedGT α
· 使用定理 `GradeOrder.grade_strictMono`：∀ {𝕆 : Type u_5} {α : Type u_6} {inst : Pre
order 𝕆} {inst_1 : Preorder α} [self : GradeOrder 𝕆 α],   StrictMono GradeOrder.
grade
-/
theorem GradeOrder.wellFoundedGT (𝕆 : Type*) [Preorder 𝕆] [GradeOrder 𝕆 α]
    [WellFoundedGT 𝕆] : WellFoundedGT α :=
  (grade_strictMono (𝕆 := 𝕆)).wellFoundedGT
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [GradeOrder ℕ α] : WellFoundedLT α :=
  GradeOrder.wellFoundedLT ℕ
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [GradeOrder ℕᵒᵈ α] : WellFoundedGT α :=
  GradeOrder.wellFoundedGT ℕᵒᵈ

end Preorder

/-!
### Grading a flag

A flag inherits the grading of its ambient order.
-/

namespace Flag
variable [PartialOrder α] {s : Flag α} {a b : s}

@[simp, norm_cast]
/-
**Flag.coe_wcovBy_coe** 是 Mathlib 中的一个引理，位于命名空间 `Flag`。
形式化陈述：coe_wcovBy_coe : (a : α) ⩿ b ↔ a ⩿ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_congr_right'`：∀ {b c a : Prop}, (b ↔ c) → (a ∧ b ↔ a ∧ c)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Flag.mem_iff_forall_le_or_ge`：mem_iff_forall_le_or_ge : a in s ↔ forall 
⦃b⦄, b in s -> a <= b ∨ b <= a
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Subtype.coe_le_coe`：coe_le_coe [LE α] {p : α -> Prop} {x y : Subtype p} 
: (x : α) <= y ↔ x <= y
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma coe_wcovBy_coe : (a : α) ⩿ b ↔ a ⩿ b := by
  refine and_congr_right' ⟨fun h c hac ↦ h hac, fun h c hac hcb ↦
    @h ⟨c, mem_iff_forall_le_or_ge.2 fun d hd ↦ ?_⟩ hac hcb⟩
  classical
  obtain hda | had := le_or_gt (⟨d, hd⟩ : s) a
  · exact .inr ((Subtype.coe_le_coe.2 hda).trans hac.le)
  obtain hbd | hdb := le_or_gt b ⟨d, hd⟩
  · exact .inl (hcb.le.trans hbd)
  · cases h had hdb

@[simp, norm_cast]
/-
**Flag.coe_covBy_coe** 是 Mathlib 中的一个引理，位于命名空间 `Flag`。
形式化陈述：coe_covBy_coe : (a : α) ⋖ b ↔ a ⋖ b
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
lemma coe_covBy_coe : (a : α) ⋖ b ↔ a ⋖ b := by simp [covBy_iff_wcovBy_and_not_le]

@[simp]
/-
**Flag.isMax_coe** 是 Mathlib 中的一个引理，位于命名空间 `Flag`。
形式化陈述：isMax_coe : IsMax (a : α) ↔ IsMax a where mp h b hab
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Flag.mem_iff_forall_le_or_ge`：mem_iff_forall_le_or_ge : a in s ↔ forall 
⦃b⦄, b in s -> a <= b ∨ b <= a
· 使用定理 `LE.le.trans'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a → 
c ≤ b → c ≤ a
· 使用定理 `IsMax.isTop`：∀ {α : Type u_1} [inst : Preorder α] {a : α} [IsDirectedOrd
er α], IsMax a → IsTop a
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
-/
lemma isMax_coe : IsMax (a : α) ↔ IsMax a where
  mp h b hab := h hab
  mpr h b hab := by
    refine @h ⟨b, mem_iff_forall_le_or_ge.2 fun c hc ↦ ?_⟩ hab
    classical
    exact .inr <| hab.trans' <| h.isTop ⟨c, hc⟩

@[simp]
/-
**Flag.isMin_coe** 是 Mathlib 中的一个引理，位于命名空间 `Flag`。
形式化陈述：isMin_coe : IsMin (a : α) ↔ IsMin a where mp h b hba
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Flag.mem_iff_forall_le_or_ge`：mem_iff_forall_le_or_ge : a in s ↔ forall 
⦃b⦄, b in s -> a <= b ∨ b <= a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `IsMin.isBot`：∀ {α : Type u_1} [inst : Preorder α] {a : α} [IsCodirectedO
rder α], IsMin a → IsBot a
· 使用定理 `SemilatticeInf.instIsCodirectedOrder`：∀ {α : Type u_1} [inst : Semilatti
ceInf α], IsCodirectedOrder α
-/
lemma isMin_coe : IsMin (a : α) ↔ IsMin a where
  mp h b hba := h hba
  mpr h b hba := by
    refine @h ⟨b, mem_iff_forall_le_or_ge.2 fun c hc ↦ ?_⟩ hba
    classical
    exact .inl <| hba.trans <| h.isBot ⟨c, hc⟩

variable [Preorder 𝕆]
/-
**Flag.** 是 Mathlib 中的一个实例，位于命名空间 `Flag`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [GradeOrder 𝕆 α] (s : Flag α) : GradeOrder 𝕆 s :=
  .liftRight _ (Subtype.strictMono_coe _) fun _ _ ↦ coe_covBy_coe.2
/-
**Flag.** 是 Mathlib 中的一个实例，位于命名空间 `Flag`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [GradeMinOrder 𝕆 α] (s : Flag α) : GradeMinOrder 𝕆 s :=
  .liftRight _ (Subtype.strictMono_coe _) (fun _ _ ↦ coe_covBy_coe.2) fun _ ↦ isMin_coe.2
/-
**Flag.** 是 Mathlib 中的一个实例，位于命名空间 `Flag`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [GradeMaxOrder 𝕆 α] (s : Flag α) : GradeMaxOrder 𝕆 s :=
  .liftRight _ (Subtype.strictMono_coe _) (fun _ _ ↦ coe_covBy_coe.2) fun _ ↦ isMax_coe.2
/-
**Flag.** 是 Mathlib 中的一个实例，位于命名空间 `Flag`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [GradeBoundedOrder 𝕆 α] (s : Flag α) : GradeBoundedOrder 𝕆 s :=
  .liftRight _ (Subtype.strictMono_coe _) (fun _ _ ↦ coe_covBy_coe.2) (fun _ ↦ isMin_coe.2)
    fun _ ↦ isMax_coe.2
/-
**Flag.grade_coe** 是 Mathlib 中的一个定理，位于命名空间 `Flag`。
形式化陈述：∀ {𝕆 : Type u_1} {α : Type u_3} [inst : PartialOrder α] {s : Flag α} [inst
_1 : Preorder 𝕆] [inst_2 : GradeOrder 𝕆 α]   (a : ↥s), grade 𝕆 ↑a = grade 𝕆 a
参数：a : ↥s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma grade_coe [GradeOrder 𝕆 α] (a : s) : grade 𝕆 (a : α) = grade 𝕆 a := rfl

end Flag

