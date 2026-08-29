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

/--
Definition of `GradeOrder` / `GradeOrder` 的定义

English:
class GradeOrder
  parameters: (𝕆 α : Type*) [Preorder 𝕆] [Preorder α]
  axioms and operations (3):
    - grade : α -> 𝕆
    - grade_strictMono : StrictMono grade
    - covBy_grade(⦃a b) : α⦄ : a ⋖ b -> grade a ⋖ grade b

中文:
类 GradeOrder
  参数: (𝕆 α : 类型) [Preorder 𝕆] [Preorder α]
  公理与运算 (3 个):
    - grade : α -> 𝕆
    - grade_strictMono : StrictMono grade
    - covBy_grade(⦃a b) : α⦄ : a ⋖ b -> grade a ⋖ grade b
-/
class GradeOrder (𝕆 α : Type*) [Preorder 𝕆] [Preorder α] where
  /-- The grading function. -/
  protected grade : α -> 𝕆
  /-- `grade` is strictly monotonic. -/
  grade_strictMono : StrictMono grade
  /-- `grade` preserves `CovBy`. -/
  covBy_grade ⦃a b : α⦄ : a ⋖ b -> grade a ⋖ grade b

/--
Definition of `GradeMinOrder` / `GradeMinOrder` 的定义

English:
class GradeMinOrder
  parameters: (𝕆 α : Type*) [Preorder 𝕆] [Preorder α]
  extends: GradeOrder 𝕆 α
  axioms and operations (1):
    - isMin_grade(⦃a) : α⦄ : IsMin a -> IsMin (grade a)

中文:
类 GradeMinOrder
  参数: (𝕆 α : 类型) [Preorder 𝕆] [Preorder α]
  继承: GradeOrder 𝕆 α
  公理与运算 (1 个):
    - isMin_grade(⦃a) : α⦄ : IsMin a -> IsMin (grade a)
-/
class GradeMinOrder (𝕆 α : Type*) [Preorder 𝕆] [Preorder α] extends GradeOrder 𝕆 α where
  /-- Minimal elements have minimal grades. -/
  isMin_grade ⦃a : α⦄ : IsMin a -> IsMin (grade a)

/--
Definition of `GradeMaxOrder` / `GradeMaxOrder` 的定义

English:
class GradeMaxOrder
  parameters: (𝕆 α : Type*) [Preorder 𝕆] [Preorder α]
  extends: GradeOrder 𝕆 α
  axioms and operations (1):
    - isMax_grade(⦃a) : α⦄ : IsMax a -> IsMax (grade a)

中文:
类 GradeMaxOrder
  参数: (𝕆 α : 类型) [Preorder 𝕆] [Preorder α]
  继承: GradeOrder 𝕆 α
  公理与运算 (1 个):
    - isMax_grade(⦃a) : α⦄ : IsMax a -> IsMax (grade a)
-/
class GradeMaxOrder (𝕆 α : Type*) [Preorder 𝕆] [Preorder α] extends GradeOrder 𝕆 α where
  /-- Maximal elements have maximal grades. -/
  isMax_grade ⦃a : α⦄ : IsMax a -> IsMax (grade a)

/--
Definition of `GradeBoundedOrder` / `GradeBoundedOrder` 的定义

English:
class GradeBoundedOrder
  parameters: (𝕆 α : Type*) [Preorder 𝕆] [Preorder α]
  extends: GradeMinOrder 𝕆 α, 
  (no additional axioms)

中文:
类 GradeBoundedOrder
  参数: (𝕆 α : 类型) [Preorder 𝕆] [Preorder α]
  继承: GradeMinOrder 𝕆 α, 
  (无附加公理)
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

/--
Definition of `grade` / `grade` 的定义

English:
definition grade
  signature: : α -> 𝕆
  body: GradeOrder.grade

中文:
定义 grade
  签名: : α -> 𝕆
  定义体: GradeOrder.grade

Depends on / 依赖: GradeOrder, GradeOrder.grade
-/
def grade : α -> 𝕆 :=
  GradeOrder.grade

/--
theorem `CovBy.grade` / 定理 `CovBy.grade`

English:
theorem CovBy.grade
  given: (h : a ⋖ b)
  statement: grade 𝕆 a ⋖ grade 𝕆 b
  proof: GradeOrder.covBy_grade h

中文:
定理 CovBy.grade
  条件: (h : a ⋖ b)
  结论: grade 𝕆 a ⋖ grade 𝕆 b
  证明: GradeOrder.covBy_grade h

Depends on / 依赖: adicValued, adicValued.has_uniform_continuous_const_smul, has_uniform_continuous_const_smul
-/
protected theorem CovBy.grade (h : a ⋖ b) : grade 𝕆 a ⋖ grade 𝕆 b :=
  GradeOrder.covBy_grade h

variable {𝕆}

/--
theorem `grade_strictMono` / 定理 `grade_strictMono`

English:
theorem grade_strictMono
  statement: StrictMono (grade 𝕆 : α -> 𝕆)
  proof: GradeOrder.grade_strictMono

中文:
定理 grade_strictMono
  结论: StrictMono (grade 𝕆 : α -> 𝕆)
  证明: GradeOrder.grade_strictMono

Depends on / 依赖: GradeOrder, GradeOrder.grade_strictMono, grade_strictMono
-/
theorem grade_strictMono : StrictMono (grade 𝕆 : α -> 𝕆) :=
  GradeOrder.grade_strictMono

/--
theorem `covBy_iff_lt_covBy_grade` / 定理 `covBy_iff_lt_covBy_grade`

English:
theorem covBy_iff_lt_covBy_grade
  statement: a ⋖ b ↔ a < b ∧ grade 𝕆 a ⋖ grade 𝕆 b
  proof: ⟨fun h => ⟨h.1, h.grade _⟩,
And.imp_right fun h _ ha hb => h.2 (grade_strictMono ha) grade_strictMono hb⟩

中文:
定理 covBy_iff_lt_covBy_grade
  结论: a ⋖ b ↔ a < b ∧ grade 𝕆 a ⋖ grade 𝕆 b
  证明: ⟨fun h => ⟨h.1, h.grade _⟩,
And.imp_right fun h _ ha hb => h.2 (grade_strictMono ha) grade_strictMono hb⟩

Depends on / 依赖: And.imp_right, grade_strictMono, h.grade, imp_right
-/
theorem covBy_iff_lt_covBy_grade : a ⋖ b ↔ a < b ∧ grade 𝕆 a ⋖ grade 𝕆 b :=
  ⟨fun h => ⟨h.1, h.grade _⟩,
And.imp_right fun h _ ha hb => h.2 (grade_strictMono ha) grade_strictMono hb⟩

end GradeOrder

section GradeMinOrder

variable (𝕆)
variable [GradeMinOrder 𝕆 α] {a : α}

/--
theorem `IsMin.grade` / 定理 `IsMin.grade`

English:
theorem IsMin.grade
  given: (h : IsMin a)
  statement: IsMin (grade 𝕆 a)
  proof: GradeMinOrder.isMin_grade h

中文:
定理 IsMin.grade
  条件: (h : IsMin a)
  结论: IsMin (grade 𝕆 a)
  证明: GradeMinOrder.isMin_grade h
-/
protected theorem IsMin.grade (h : IsMin a) : IsMin (grade 𝕆 a) :=
  GradeMinOrder.isMin_grade h

variable {𝕆}

@[simp]
/--
theorem `isMin_grade_iff` / 定理 `isMin_grade_iff`

English:
theorem isMin_grade_iff
  statement: IsMin (grade 𝕆 a) ↔ IsMin a
  proof: ⟨grade_strictMono.isMin_of_apply, IsMin.grade _⟩

中文:
定理 isMin_grade_iff
  结论: IsMin (grade 𝕆 a) ↔ IsMin a
  证明: ⟨grade_strictMono.isMin_of_apply, IsMin.grade _⟩

Depends on / 依赖: IsMin.grade, grade_strictMono, grade_strictMono.isMin_of_apply, isMin_of_apply
-/
theorem isMin_grade_iff : IsMin (grade 𝕆 a) ↔ IsMin a :=
  ⟨grade_strictMono.isMin_of_apply, IsMin.grade _⟩

end GradeMinOrder

section GradeMaxOrder

variable (𝕆)
variable [GradeMaxOrder 𝕆 α] {a : α}

/--
theorem `IsMax.grade` / 定理 `IsMax.grade`

English:
theorem IsMax.grade
  given: (h : IsMax a)
  statement: IsMax (grade 𝕆 a)
  proof: GradeMaxOrder.isMax_grade h

中文:
定理 IsMax.grade
  条件: (h : IsMax a)
  结论: IsMax (grade 𝕆 a)
  证明: GradeMaxOrder.isMax_grade h

Depends on / 依赖: Completion, IsScalarTower, IsScalarTower.algebraMap_apply, UniformSpace, UniformSpace.Completion.coeRingHom, WithVal, algebraMap_apply, coeRingHom, of_algebraMap_eq, v.valuation, valuation
-/
protected theorem IsMax.grade (h : IsMax a) : IsMax (grade 𝕆 a) :=
  GradeMaxOrder.isMax_grade h

variable {𝕆}

@[simp]
/--
theorem `isMax_grade_iff` / 定理 `isMax_grade_iff`

English:
theorem isMax_grade_iff
  statement: IsMax (grade 𝕆 a) ↔ IsMax a
  proof: ⟨grade_strictMono.isMax_of_apply, IsMax.grade _⟩

中文:
定理 isMax_grade_iff
  结论: IsMax (grade 𝕆 a) ↔ IsMax a
  证明: ⟨grade_strictMono.isMax_of_apply, IsMax.grade _⟩

Depends on / 依赖: Completion, IsMax.grade, IsScalarTower, IsScalarTower.algebraMap_apply, adicCompletion, adicCompletion.ext, algebraMap_adicCompletion_toCompletion, algebraMap_apply, grade_strictMono, grade_strictMono.isMax_of_apply, isMax_of_apply, of_algebraMap_eq, v.valuation, valuation
-/
theorem isMax_grade_iff : IsMax (grade 𝕆 a) ↔ IsMax a :=
  ⟨grade_strictMono.isMax_of_apply, IsMax.grade _⟩

end GradeMaxOrder

end Preorder

-- graded order
/--
theorem `grade_mono` / 定理 `grade_mono`

English:
theorem grade_mono
  given: [PartialOrder α] [GradeOrder 𝕆 α]
  statement: Monotone (grade 𝕆 : α -> 𝕆)
  proof: grade_strictMono.monotone

中文:
定理 grade_mono
  条件: [PartialOrder α] [GradeOrder 𝕆 α]
  结论: Monotone (grade 𝕆 : α -> 𝕆)
  证明: grade_strictMono.monotone

Depends on / 依赖: grade_strictMono, grade_strictMono.monotone, monotone
-/
theorem grade_mono [PartialOrder α] [GradeOrder 𝕆 α] : Monotone (grade 𝕆 : α -> 𝕆) :=
  grade_strictMono.monotone

section LinearOrder

-- graded order
variable [LinearOrder α] [GradeOrder 𝕆 α] {a b : α}

/--
theorem `grade_injective` / 定理 `grade_injective`

English:
theorem grade_injective
  statement: Function.Injective (grade 𝕆 : α -> 𝕆)
  proof: grade_strictMono.injective

@[simp]

中文:
定理 grade_injective
  结论: Function.Injective (grade 𝕆 : α -> 𝕆)
  证明: grade_strictMono.injective

@[simp]

Depends on / 依赖: grade_strictMono, grade_strictMono.injective, injective
-/
theorem grade_injective : Function.Injective (grade 𝕆 : α -> 𝕆) :=
  grade_strictMono.injective

@[simp]
/--
theorem `grade_le_grade_iff` / 定理 `grade_le_grade_iff`

English:
theorem grade_le_grade_iff
  statement: grade 𝕆 a <= grade 𝕆 b ↔ a <= b
  proof: grade_strictMono.le_iff_le

@[simp]

中文:
定理 grade_le_grade_iff
  结论: grade 𝕆 a <= grade 𝕆 b ↔ a <= b
  证明: grade_strictMono.le_iff_le

@[simp]

Depends on / 依赖: grade_strictMono, grade_strictMono.le_iff_le, le_iff_le
-/
theorem grade_le_grade_iff : grade 𝕆 a <= grade 𝕆 b ↔ a <= b :=
  grade_strictMono.le_iff_le

@[simp]
/--
theorem `grade_lt_grade_iff` / 定理 `grade_lt_grade_iff`

English:
theorem grade_lt_grade_iff
  statement: grade 𝕆 a < grade 𝕆 b ↔ a < b
  proof: grade_strictMono.lt_iff_lt

@[simp]

中文:
定理 grade_lt_grade_iff
  结论: grade 𝕆 a < grade 𝕆 b ↔ a < b
  证明: grade_strictMono.lt_iff_lt

@[simp]

Depends on / 依赖: grade_strictMono, grade_strictMono.lt_iff_lt, lt_iff_lt
-/
theorem grade_lt_grade_iff : grade 𝕆 a < grade 𝕆 b ↔ a < b :=
  grade_strictMono.lt_iff_lt

@[simp]
/--
theorem `grade_eq_grade_iff` / 定理 `grade_eq_grade_iff`

English:
theorem grade_eq_grade_iff
  statement: grade 𝕆 a = grade 𝕆 b ↔ a = b
  proof: grade_injective.eq_iff

中文:
定理 grade_eq_grade_iff
  结论: grade 𝕆 a = grade 𝕆 b ↔ a = b
  证明: grade_injective.eq_iff

Depends on / 依赖: eq_iff, grade_injective, grade_injective.eq_iff
-/
theorem grade_eq_grade_iff : grade 𝕆 a = grade 𝕆 b ↔ a = b :=
  grade_injective.eq_iff

/--
theorem `grade_ne_grade_iff` / 定理 `grade_ne_grade_iff`

English:
theorem grade_ne_grade_iff
  statement: grade 𝕆 a != grade 𝕆 b ↔ a != b
  proof: grade_injective.ne_iff

中文:
定理 grade_ne_grade_iff
  结论: grade 𝕆 a != grade 𝕆 b ↔ a != b
  证明: grade_injective.ne_iff

Depends on / 依赖: grade_injective, grade_injective.ne_iff, ne_iff
-/
theorem grade_ne_grade_iff : grade 𝕆 a != grade 𝕆 b ↔ a != b :=
  grade_injective.ne_iff

/--
theorem `grade_covBy_grade_iff` / 定理 `grade_covBy_grade_iff`

English:
theorem grade_covBy_grade_iff
  statement: grade 𝕆 a ⋖ grade 𝕆 b ↔ a ⋖ b
  proof: (covBy_iff_lt_covBy_grade.trans <| and_iff_right_of_imp fun h => grade_lt_grade_iff.1 h.1).symm

中文:
定理 grade_covBy_grade_iff
  结论: grade 𝕆 a ⋖ grade 𝕆 b ↔ a ⋖ b
  证明: (covBy_iff_lt_covBy_grade.trans <| and_iff_right_of_imp fun h => grade_lt_grade_iff.1 h.1).symm

Depends on / 依赖: and_iff_right_of_imp, covBy_iff_lt_covBy_grade, covBy_iff_lt_covBy_grade.trans, grade_lt_grade_iff
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
/--
theorem `grade_bot` / 定理 `grade_bot`

English:
theorem grade_bot
  given: [OrderBot 𝕆] [OrderBot α] [GradeMinOrder 𝕆 α]
  statement: grade 𝕆 (⊥ : α) = ⊥
  proof: (isMin_bot.grade _).eq_bot

@[simp]

中文:
定理 grade_bot
  条件: [OrderBot 𝕆] [OrderBot α] [GradeMinOrder 𝕆 α]
  结论: grade 𝕆 (⊥ : α) = ⊥
  证明: (isMin_bot.grade _).eq_bot

@[simp]

Depends on / 依赖: eq_bot, isMin_bot, isMin_bot.grade
-/
theorem grade_bot [OrderBot 𝕆] [OrderBot α] [GradeMinOrder 𝕆 α] : grade 𝕆 (⊥ : α) = ⊥ :=
  (isMin_bot.grade _).eq_bot

@[simp]
/--
theorem `grade_top` / 定理 `grade_top`

English:
theorem grade_top
  given: [OrderTop 𝕆] [OrderTop α] [GradeMaxOrder 𝕆 α]
  statement: grade 𝕆 (⊤ : α) = ⊤
  proof: (isMax_top.grade _).eq_top

中文:
定理 grade_top
  条件: [OrderTop 𝕆] [OrderTop α] [GradeMaxOrder 𝕆 α]
  结论: grade 𝕆 (⊤ : α) = ⊤
  证明: (isMax_top.grade _).eq_top

Depends on / 依赖: eq_top, isMax_top, isMax_top.grade
-/
theorem grade_top [OrderTop 𝕆] [OrderTop α] [GradeMaxOrder 𝕆 α] : grade 𝕆 (⊤ : α) = ⊤ :=
  (isMax_top.grade _).eq_top

end PartialOrder

/-! ### Instances -/

section Preorder
variable [Preorder 𝕆] [Preorder ℙ] [Preorder α] [Preorder β]

/--
Instance `Preorder.toGradeBoundedOrder` / 实例 `Preorder.toGradeBoundedOrder`

English:
instance Preorder.toGradeBoundedOrder
  signature: : GradeBoundedOrder α α where
  body: id
  isMin_grade _ := id
  isMax_grade _ := id
  grade_strictMono := strictMono_id
  covBy_grade _ _ := id

@[simp]

中文:
实例 Preorder.toGradeBoundedOrder
  签名: : GradeBoundedOrder α α where
  定义体: id
  isMin_grade _ := id
  isMax_grade _ := id
  grade_strictMono := strictMono_id
  covBy_grade _ _ := id

@[simp]
-/
instance Preorder.toGradeBoundedOrder : GradeBoundedOrder α α where
  grade := id
  isMin_grade _ := id
  isMax_grade _ := id
  grade_strictMono := strictMono_id
  covBy_grade _ _ := id

@[simp]
/--
theorem `grade_self` / 定理 `grade_self`

English:
theorem grade_self
  given: (a : α)
  statement: grade α a = a
  proof: rfl

中文:
定理 grade_self
  条件: (a : α)
  结论: grade α a = a
  证明: rfl
-/
theorem grade_self (a : α) : grade α a = a :=
  rfl


/--
Instance `OrderDual.gradeOrder` / 实例 `OrderDual.gradeOrder`

English:
instance OrderDual.gradeOrder
  signature: [GradeOrder 𝕆 α]
  body: toDual ∘ grade 𝕆 ∘ ofDual
  grade_strictMono := grade_strictMono.dual
  covBy_grade _ _ h := (h.ofDual.grade _).toDual

中文:
实例 OrderDual.gradeOrder
  签名: [GradeOrder 𝕆 α]
  定义体: toDual ∘ grade 𝕆 ∘ ofDual
  grade_strictMono := grade_strictMono.dual
  covBy_grade _ _ h := (h.ofDual.grade _).toDual

Depends on / 依赖: ofDual, toDual
-/
instance OrderDual.gradeOrder [GradeOrder 𝕆 α] : GradeOrder 𝕆ᵒᵈ αᵒᵈ where
  grade := toDual ∘ grade 𝕆 ∘ ofDual
  grade_strictMono := grade_strictMono.dual
  covBy_grade _ _ h := (h.ofDual.grade _).toDual

/--
Instance `OrderDual.gradeMinOrder` / 实例 `OrderDual.gradeMinOrder`

English:
instance OrderDual.gradeMinOrder
  signature: [GradeMaxOrder 𝕆 α]
  body: { OrderDual.gradeOrder with isMin_grade := fun _ => IsMax.grade (α := α) 𝕆 }

中文:
实例 OrderDual.gradeMinOrder
  签名: [GradeMaxOrder 𝕆 α]
  定义体: { OrderDual.gradeOrder with isMin_grade := fun _ => IsMax.grade (α := α) 𝕆 }

Depends on / 依赖: IsMax.grade, OrderDual, OrderDual.gradeOrder, gradeOrder, isMin_grade
-/
instance OrderDual.gradeMinOrder [GradeMaxOrder 𝕆 α] : GradeMinOrder 𝕆ᵒᵈ αᵒᵈ :=
  { OrderDual.gradeOrder with isMin_grade := fun _ => IsMax.grade (α := α) 𝕆 }

/--
Instance `OrderDual.gradeMaxOrder` / 实例 `OrderDual.gradeMaxOrder`

English:
instance OrderDual.gradeMaxOrder
  signature: [GradeMinOrder 𝕆 α]
  body: { OrderDual.gradeOrder with isMax_grade := fun _ => IsMin.grade (α := α) 𝕆 }

中文:
实例 OrderDual.gradeMaxOrder
  签名: [GradeMinOrder 𝕆 α]
  定义体: { OrderDual.gradeOrder with isMax_grade := fun _ => IsMin.grade (α := α) 𝕆 }

Depends on / 依赖: IsMin.grade, OrderDual, OrderDual.gradeOrder, gradeOrder, isMax_grade
-/
instance OrderDual.gradeMaxOrder [GradeMinOrder 𝕆 α] : GradeMaxOrder 𝕆ᵒᵈ αᵒᵈ :=
  { OrderDual.gradeOrder with isMax_grade := fun _ => IsMin.grade (α := α) 𝕆 }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [GradeBoundedOrder
  signature: 𝕆 α] : GradeBoundedOrder 𝕆ᵒᵈ αᵒᵈ
  body: { OrderDual.gradeMinOrder, OrderDual.gradeMaxOrder with }

@[simp]

中文:
实例 [GradeBoundedOrder
  签名: 𝕆 α] : GradeBoundedOrder 𝕆ᵒᵈ αᵒᵈ
  定义体: { OrderDual.gradeMinOrder, OrderDual.gradeMaxOrder with }

@[simp]

Depends on / 依赖: OrderDual, OrderDual.gradeMaxOrder, OrderDual.gradeMinOrder, gradeMaxOrder, gradeMinOrder
-/
instance [GradeBoundedOrder 𝕆 α] : GradeBoundedOrder 𝕆ᵒᵈ αᵒᵈ :=
  { OrderDual.gradeMinOrder, OrderDual.gradeMaxOrder with }

@[simp]
/--
theorem `grade_toDual` / 定理 `grade_toDual`

English:
theorem grade_toDual
  given: [GradeOrder 𝕆 α] (a : α)
  statement: grade 𝕆ᵒᵈ (toDual a) = toDual (grade 𝕆 a)
  proof: rfl

@[simp]

中文:
定理 grade_toDual
  条件: [GradeOrder 𝕆 α] (a : α)
  结论: grade 𝕆ᵒᵈ (toDual a) = toDual (grade 𝕆 a)
  证明: rfl

@[simp]
-/
theorem grade_toDual [GradeOrder 𝕆 α] (a : α) : grade 𝕆ᵒᵈ (toDual a) = toDual (grade 𝕆 a) :=
  rfl

@[simp]
/--
theorem `grade_ofDual` / 定理 `grade_ofDual`

English:
theorem grade_ofDual
  given: [GradeOrder 𝕆 α] (a : αᵒᵈ)
  statement: grade 𝕆 (ofDual a) = ofDual (grade 𝕆ᵒᵈ a)
  proof: rfl

中文:
定理 grade_ofDual
  条件: [GradeOrder 𝕆 α] (a : αᵒᵈ)
  结论: grade 𝕆 (ofDual a) = ofDual (grade 𝕆ᵒᵈ a)
  证明: rfl
-/
theorem grade_ofDual [GradeOrder 𝕆 α] (a : αᵒᵈ) : grade 𝕆 (ofDual a) = ofDual (grade 𝕆ᵒᵈ a) :=
  rfl

/-! #### Lifting a graded order -/

-- See note [reducible non-instances]
/--
Definition of `GradeOrder.liftLeft` / `GradeOrder.liftLeft` 的定义

English:
abbreviation GradeOrder.liftLeft
  signature: [GradeOrder 𝕆 α] (f : 𝕆 -> ℙ) (hf : StrictMono f)
  body: f ∘ grade 𝕆
  grade_strictMono := hf.comp grade_strictMono
covBy_grade _ _ h := hcovBy _ _ h.grade _

中文:
缩写 GradeOrder.liftLeft
  签名: [GradeOrder 𝕆 α] (f : 𝕆 -> ℙ) (hf : StrictMono f)
  定义体: f ∘ grade 𝕆
  grade_strictMono := hf.comp grade_strictMono
covBy_grade _ _ h := hcovBy _ _ h.grade _
-/
abbrev GradeOrder.liftLeft [GradeOrder 𝕆 α] (f : 𝕆 -> ℙ) (hf : StrictMono f)
    (hcovBy : forall a b, a ⋖ b -> f a ⋖ f b) : GradeOrder ℙ α where
  grade := f ∘ grade 𝕆
  grade_strictMono := hf.comp grade_strictMono
covBy_grade _ _ h := hcovBy _ _ h.grade _

-- See note [reducible non-instances]
/--
Definition of `GradeMinOrder.liftLeft` / `GradeMinOrder.liftLeft` 的定义

English:
abbreviation GradeMinOrder.liftLeft
  signature: [GradeMinOrder 𝕆 α] (f : 𝕆 -> ℙ) (hf : StrictMono f)
  body: { GradeOrder.liftLeft f hf hcovBy with isMin_grade := fun _ ha => hmin _ <| ha.grade _ }

中文:
缩写 GradeMinOrder.liftLeft
  签名: [GradeMinOrder 𝕆 α] (f : 𝕆 -> ℙ) (hf : StrictMono f)
  定义体: { GradeOrder.liftLeft f hf hcovBy with isMin_grade := fun _ ha => hmin _ <| ha.grade _ }

Depends on / 依赖: GradeOrder, GradeOrder.liftLeft, ha.grade, hcovBy, isMin_grade, liftLeft
-/
abbrev GradeMinOrder.liftLeft [GradeMinOrder 𝕆 α] (f : 𝕆 -> ℙ) (hf : StrictMono f)
    (hcovBy : forall a b, a ⋖ b -> f a ⋖ f b) (hmin : forall a, IsMin a -> IsMin (f a)) : GradeMinOrder ℙ α :=
  { GradeOrder.liftLeft f hf hcovBy with isMin_grade := fun _ ha => hmin _ <| ha.grade _ }

-- See note [reducible non-instances]
/--
Definition of `GradeMaxOrder.liftLeft` / `GradeMaxOrder.liftLeft` 的定义

English:
abbreviation GradeMaxOrder.liftLeft
  signature: [GradeMaxOrder 𝕆 α] (f : 𝕆 -> ℙ) (hf : StrictMono f)
  body: { GradeOrder.liftLeft f hf hcovBy with isMax_grade := fun _ ha => hmax _ <| ha.grade _ }

中文:
缩写 GradeMaxOrder.liftLeft
  签名: [GradeMaxOrder 𝕆 α] (f : 𝕆 -> ℙ) (hf : StrictMono f)
  定义体: { GradeOrder.liftLeft f hf hcovBy with isMax_grade := fun _ ha => hmax _ <| ha.grade _ }

Depends on / 依赖: GradeOrder, GradeOrder.liftLeft, ha.grade, hcovBy, isMax_grade, liftLeft
-/
abbrev GradeMaxOrder.liftLeft [GradeMaxOrder 𝕆 α] (f : 𝕆 -> ℙ) (hf : StrictMono f)
    (hcovBy : forall a b, a ⋖ b -> f a ⋖ f b) (hmax : forall a, IsMax a -> IsMax (f a)) : GradeMaxOrder ℙ α :=
  { GradeOrder.liftLeft f hf hcovBy with isMax_grade := fun _ ha => hmax _ <| ha.grade _ }

-- See note [reducible non-instances]
/--
Definition of `GradeBoundedOrder.liftLeft` / `GradeBoundedOrder.liftLeft` 的定义

English:
abbreviation GradeBoundedOrder.liftLeft
  signature: [GradeBoundedOrder 𝕆 α] (f : 𝕆 -> ℙ) (hf : StrictMono f)
  body: { GradeMinOrder.liftLeft f hf hcovBy hmin, GradeMaxOrder.liftLeft f hf hcovBy hmax with }

中文:
缩写 GradeBoundedOrder.liftLeft
  签名: [GradeBoundedOrder 𝕆 α] (f : 𝕆 -> ℙ) (hf : StrictMono f)
  定义体: { GradeMinOrder.liftLeft f hf hcovBy hmin, GradeMaxOrder.liftLeft f hf hcovBy hmax with }

Depends on / 依赖: GradeMaxOrder, GradeMaxOrder.liftLeft, GradeMinOrder, GradeMinOrder.liftLeft, hcovBy, liftLeft
-/
abbrev GradeBoundedOrder.liftLeft [GradeBoundedOrder 𝕆 α] (f : 𝕆 -> ℙ) (hf : StrictMono f)
    (hcovBy : forall a b, a ⋖ b -> f a ⋖ f b) (hmin : forall a, IsMin a -> IsMin (f a))
    (hmax : forall a, IsMax a -> IsMax (f a)) : GradeBoundedOrder ℙ α :=
  { GradeMinOrder.liftLeft f hf hcovBy hmin, GradeMaxOrder.liftLeft f hf hcovBy hmax with }

-- See note [reducible non-instances]
/--
Definition of `GradeOrder.liftRight` / `GradeOrder.liftRight` 的定义

English:
abbreviation GradeOrder.liftRight
  signature: [GradeOrder 𝕆 β] (f : α -> β) (hf : StrictMono f)
  body: grade 𝕆 ∘ f
  grade_strictMono := grade_strictMono.comp hf
  covBy_grade _ _ h := (hcovBy _ _ h).grade _

中文:
缩写 GradeOrder.liftRight
  签名: [GradeOrder 𝕆 β] (f : α -> β) (hf : StrictMono f)
  定义体: grade 𝕆 ∘ f
  grade_strictMono := grade_strictMono.comp hf
  covBy_grade _ _ h := (hcovBy _ _ h).grade _
-/
abbrev GradeOrder.liftRight [GradeOrder 𝕆 β] (f : α -> β) (hf : StrictMono f)
    (hcovBy : forall a b, a ⋖ b -> f a ⋖ f b) : GradeOrder 𝕆 α where
  grade := grade 𝕆 ∘ f
  grade_strictMono := grade_strictMono.comp hf
  covBy_grade _ _ h := (hcovBy _ _ h).grade _

-- See note [reducible non-instances]
/--
Definition of `GradeMinOrder.liftRight` / `GradeMinOrder.liftRight` 的定义

English:
abbreviation GradeMinOrder.liftRight
  signature: [GradeMinOrder 𝕆 β] (f : α -> β) (hf : StrictMono f)
  body: { GradeOrder.liftRight f hf hcovBy with isMin_grade := fun _ ha => (hmin _ ha).grade _ }

中文:
缩写 GradeMinOrder.liftRight
  签名: [GradeMinOrder 𝕆 β] (f : α -> β) (hf : StrictMono f)
  定义体: { GradeOrder.liftRight f hf hcovBy with isMin_grade := fun _ ha => (hmin _ ha).grade _ }

Depends on / 依赖: GradeOrder, GradeOrder.liftRight, hcovBy, isMin_grade, liftRight
-/
abbrev GradeMinOrder.liftRight [GradeMinOrder 𝕆 β] (f : α -> β) (hf : StrictMono f)
    (hcovBy : forall a b, a ⋖ b -> f a ⋖ f b) (hmin : forall a, IsMin a -> IsMin (f a)) : GradeMinOrder 𝕆 α :=
  { GradeOrder.liftRight f hf hcovBy with isMin_grade := fun _ ha => (hmin _ ha).grade _ }

-- See note [reducible non-instances]
/--
Definition of `GradeMaxOrder.liftRight` / `GradeMaxOrder.liftRight` 的定义

English:
abbreviation GradeMaxOrder.liftRight
  signature: [GradeMaxOrder 𝕆 β] (f : α -> β) (hf : StrictMono f)
  body: { GradeOrder.liftRight f hf hcovBy with isMax_grade := fun _ ha => (hmax _ ha).grade _ }

中文:
缩写 GradeMaxOrder.liftRight
  签名: [GradeMaxOrder 𝕆 β] (f : α -> β) (hf : StrictMono f)
  定义体: { GradeOrder.liftRight f hf hcovBy with isMax_grade := fun _ ha => (hmax _ ha).grade _ }

Depends on / 依赖: GradeOrder, GradeOrder.liftRight, hcovBy, isMax_grade, liftRight
-/
abbrev GradeMaxOrder.liftRight [GradeMaxOrder 𝕆 β] (f : α -> β) (hf : StrictMono f)
    (hcovBy : forall a b, a ⋖ b -> f a ⋖ f b) (hmax : forall a, IsMax a -> IsMax (f a)) : GradeMaxOrder 𝕆 α :=
  { GradeOrder.liftRight f hf hcovBy with isMax_grade := fun _ ha => (hmax _ ha).grade _ }

-- See note [reducible non-instances]
/--
Definition of `GradeBoundedOrder.liftRight` / `GradeBoundedOrder.liftRight` 的定义

English:
abbreviation GradeBoundedOrder.liftRight
  signature: [GradeBoundedOrder 𝕆 β] (f : α -> β) (hf : StrictMono f)
  body: { GradeMinOrder.liftRight f hf hcovBy hmin, GradeMaxOrder.liftRight f hf hcovBy hmax with }

中文:
缩写 GradeBoundedOrder.liftRight
  签名: [GradeBoundedOrder 𝕆 β] (f : α -> β) (hf : StrictMono f)
  定义体: { GradeMinOrder.liftRight f hf hcovBy hmin, GradeMaxOrder.liftRight f hf hcovBy hmax with }

Depends on / 依赖: GradeMaxOrder, GradeMaxOrder.liftRight, GradeMinOrder, GradeMinOrder.liftRight, hcovBy, liftRight
-/
abbrev GradeBoundedOrder.liftRight [GradeBoundedOrder 𝕆 β] (f : α -> β) (hf : StrictMono f)
    (hcovBy : forall a b, a ⋖ b -> f a ⋖ f b) (hmin : forall a, IsMin a -> IsMin (f a))
    (hmax : forall a, IsMax a -> IsMax (f a)) : GradeBoundedOrder 𝕆 α :=
  { GradeMinOrder.liftRight f hf hcovBy hmin, GradeMaxOrder.liftRight f hf hcovBy hmax with }

/-! #### `Fin n`-graded to `ℕ`-graded to `ℤ`-graded -/


-- See note [reducible non-instances]
/--
Definition of `GradeOrder.finToNat` / `GradeOrder.finToNat` 的定义

English:
abbreviation GradeOrder.finToNat
  signature: (n : Nat) [GradeOrder (Fin n) α]
  body: (GradeOrder.liftLeft (_ : Fin n -> Nat) Fin.val_strictMono) fun _ _ => CovBy.coe_fin

中文:
缩写 GradeOrder.finToNat
  签名: (n : 自然数) [GradeOrder (Fin n) α]
  定义体: (GradeOrder.liftLeft (_ : Fin n -> Nat) Fin.val_strictMono) fun _ _ => CovBy.coe_fin

Depends on / 依赖: CovBy.coe_fin, Fin.val_strictMono, GradeOrder, GradeOrder.liftLeft, coe_fin, liftLeft, val_strictMono
-/
abbrev GradeOrder.finToNat (n : Nat) [GradeOrder (Fin n) α] : GradeOrder Nat α :=
  (GradeOrder.liftLeft (_ : Fin n -> Nat) Fin.val_strictMono) fun _ _ => CovBy.coe_fin

-- See note [reducible non-instances]
/--
Definition of `GradeMinOrder.finToNat` / `GradeMinOrder.finToNat` 的定义

English:
abbreviation GradeMinOrder.finToNat
  signature: (n : Nat) [GradeMinOrder (Fin n) α]
  body: (GradeMinOrder.liftLeft (_ : Fin n -> Nat) Fin.val_strictMono fun _ _ => CovBy.coe_fin) fun a h => by
    cases n
    · exact a.elim0
    rw [h.eq_bot]; rw [bot_eq_zero]
    exact isMin_bot

中文:
缩写 GradeMinOrder.finToNat
  签名: (n : 自然数) [GradeMinOrder (Fin n) α]
  定义体: (GradeMinOrder.liftLeft (_ : Fin n -> Nat) Fin.val_strictMono fun _ _ => CovBy.coe_fin) fun a h => by
    cases n
    · exact a.elim0
    rw [h.eq_bot]; rw [bot_eq_zero]
    exact isMin_bot

Depends on / 依赖: CovBy.coe_fin, Fin.val_strictMono, GradeMinOrder, GradeMinOrder.liftLeft, a.elim0, bot_eq_zero, coe_fin, eq_bot, h.eq_bot, isMin_bot, liftLeft, val_strictMono
-/
abbrev GradeMinOrder.finToNat (n : Nat) [GradeMinOrder (Fin n) α] : GradeMinOrder Nat α :=
  (GradeMinOrder.liftLeft (_ : Fin n -> Nat) Fin.val_strictMono fun _ _ => CovBy.coe_fin) fun a h => by
    cases n
    · exact a.elim0
    rw [h.eq_bot]; rw [bot_eq_zero]
    exact isMin_bot

/--
Instance `GradeOrder.natToInt` / 实例 `GradeOrder.natToInt`

English:
instance GradeOrder.natToInt
  signature: [GradeOrder Nat α]
  body: (GradeOrder.liftLeft _ Int.natCast_strictMono) fun _ _ => CovBy.intCast

中文:
实例 GradeOrder.natToInt
  签名: [GradeOrder 自然数 α]
  定义体: (GradeOrder.liftLeft _ Int.natCast_strictMono) fun _ _ => CovBy.intCast

Depends on / 依赖: CovBy.intCast, GradeOrder, GradeOrder.liftLeft, Int.natCast_strictMono, intCast, liftLeft, natCast_strictMono
-/
instance GradeOrder.natToInt [GradeOrder Nat α] : GradeOrder Int α :=
  (GradeOrder.liftLeft _ Int.natCast_strictMono) fun _ _ => CovBy.intCast

/--
theorem `GradeOrder.wellFoundedLT` / 定理 `GradeOrder.wellFoundedLT`

English:
theorem GradeOrder.wellFoundedLT
  statement: (𝕆 : Type*) [Preorder 𝕆] [GradeOrder 𝕆 α]
  proof: (grade_strictMono (𝕆 := 𝕆)).wellFoundedLT

中文:
定理 GradeOrder.wellFoundedLT
  结论: (𝕆 : 类型) [Preorder 𝕆] [GradeOrder 𝕆 α]
  证明: (grade_strictMono (𝕆 := 𝕆)).wellFoundedLT

Depends on / 依赖: grade_strictMono, wellFoundedLT
-/
theorem GradeOrder.wellFoundedLT (𝕆 : Type*) [Preorder 𝕆] [GradeOrder 𝕆 α]
    [WellFoundedLT 𝕆] : WellFoundedLT α :=
  (grade_strictMono (𝕆 := 𝕆)).wellFoundedLT

/--
theorem `GradeOrder.wellFoundedGT` / 定理 `GradeOrder.wellFoundedGT`

English:
theorem GradeOrder.wellFoundedGT
  statement: (𝕆 : Type*) [Preorder 𝕆] [GradeOrder 𝕆 α]
  proof: (grade_strictMono (𝕆 := 𝕆)).wellFoundedGT

中文:
定理 GradeOrder.wellFoundedGT
  结论: (𝕆 : 类型) [Preorder 𝕆] [GradeOrder 𝕆 α]
  证明: (grade_strictMono (𝕆 := 𝕆)).wellFoundedGT

Depends on / 依赖: grade_strictMono, wellFoundedGT
-/
theorem GradeOrder.wellFoundedGT (𝕆 : Type*) [Preorder 𝕆] [GradeOrder 𝕆 α]
    [WellFoundedGT 𝕆] : WellFoundedGT α :=
  (grade_strictMono (𝕆 := 𝕆)).wellFoundedGT

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [GradeOrder
  signature: Nat α] : WellFoundedLT α
  body: GradeOrder.wellFoundedLT Nat

中文:
实例 [GradeOrder
  签名: 自然数 α] : WellFoundedLT α
  定义体: GradeOrder.wellFoundedLT Nat

Depends on / 依赖: GradeOrder, GradeOrder.wellFoundedLT, wellFoundedLT
-/
instance [GradeOrder Nat α] : WellFoundedLT α :=
  GradeOrder.wellFoundedLT Nat

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [GradeOrder
  signature: Natᵒᵈ α] : WellFoundedGT α
  body: GradeOrder.wellFoundedGT Natᵒᵈ

中文:
实例 [GradeOrder
  签名: 自然数ᵒᵈ α] : WellFoundedGT α
  定义体: GradeOrder.wellFoundedGT Natᵒᵈ

Depends on / 依赖: GradeOrder, GradeOrder.wellFoundedGT, wellFoundedGT
-/
instance [GradeOrder Natᵒᵈ α] : WellFoundedGT α :=
  GradeOrder.wellFoundedGT Natᵒᵈ

end Preorder

/-!
### Grading a flag

A flag inherits the grading of its ambient order.
-/

namespace Flag
variable [PartialOrder α] {s : Flag α} {a b : s}

@[simp, norm_cast]
/--
lemma `coe_wcovBy_coe` / 引理 `coe_wcovBy_coe`

English:
lemma coe_wcovBy_coe
  statement: (a : α) ⩿ b ↔ a ⩿ b
  proof: by
  refine and_congr_right' ⟨fun h c hac => h hac, fun h c hac hcb =>
    @h ⟨c, mem_iff_forall_le_or_ge.2 fun d hd => ?_⟩ hac hcb⟩
  classical
  obtain hda | had := le_or_gt (⟨d, hd⟩ : s) a
  · exact .inr ((Subtype.coe_le_coe.2 hda).trans hac.le)
  obtain hbd | hdb := le_or_gt b ⟨d, hd⟩
  · exact 

中文:
引理 coe_wcovBy_coe
  结论: (a : α) ⩿ b ↔ a ⩿ b
  证明: by
  refine and_congr_right' ⟨fun h c hac => h hac, fun h c hac hcb =>
    @h ⟨c, mem_iff_forall_le_or_ge.2 fun d hd => ?_⟩ hac hcb⟩
  classical
  obtain hda | had := le_or_gt (⟨d, hd⟩ : s) a
  · exact .inr ((Subtype.coe_le_coe.2 hda).trans hac.le)
  obtain hbd | hdb := le_or_gt b ⟨d, hd⟩
  · exact 

Depends on / 依赖: Subtype, Subtype.coe_le_coe, and_congr_right, classical, coe_le_coe, hac.le, hcb.le.trans, le_or_gt, mem_iff_forall_le_or_ge
-/
lemma coe_wcovBy_coe : (a : α) ⩿ b ↔ a ⩿ b := by
  refine and_congr_right' ⟨fun h c hac => h hac, fun h c hac hcb =>
    @h ⟨c, mem_iff_forall_le_or_ge.2 fun d hd => ?_⟩ hac hcb⟩
  classical
  obtain hda | had := le_or_gt (⟨d, hd⟩ : s) a
  · exact .inr ((Subtype.coe_le_coe.2 hda).trans hac.le)
  obtain hbd | hdb := le_or_gt b ⟨d, hd⟩
  · exact .inl (hcb.le.trans hbd)
  · cases h had hdb

@[simp, norm_cast]
/--
lemma `coe_covBy_coe` / 引理 `coe_covBy_coe`

English:
lemma coe_covBy_coe
  statement: (a : α) ⋖ b ↔ a ⋖ b
  proof: by simp [covBy_iff_wcovBy_and_not_le]

@[simp]

中文:
引理 coe_covBy_coe
  结论: (a : α) ⋖ b ↔ a ⋖ b
  证明: by simp [covBy_iff_wcovBy_and_not_le]

@[simp]

Depends on / 依赖: covBy_iff_wcovBy_and_not_le
-/
lemma coe_covBy_coe : (a : α) ⋖ b ↔ a ⋖ b := by simp [covBy_iff_wcovBy_and_not_le]

@[simp]
/--
lemma `isMax_coe` / 引理 `isMax_coe`

English:
lemma isMax_coe
  statement: IsMax (a : α) ↔ IsMax a where
  proof: h hab
  mpr h b hab := by
    refine @h ⟨b, mem_iff_forall_le_or_ge.2 fun c hc => ?_⟩ hab
    classical
exact .inr hab.trans' h.isTop ⟨c, hc⟩

@[simp]

中文:
引理 isMax_coe
  结论: IsMax (a : α) ↔ IsMax a where
  证明: h hab
  mpr h b hab := by
    refine @h ⟨b, mem_iff_forall_le_or_ge.2 fun c hc => ?_⟩ hab
    classical
exact .inr hab.trans' h.isTop ⟨c, hc⟩

@[simp]
-/
lemma isMax_coe : IsMax (a : α) ↔ IsMax a where
  mp h b hab := h hab
  mpr h b hab := by
    refine @h ⟨b, mem_iff_forall_le_or_ge.2 fun c hc => ?_⟩ hab
    classical
exact .inr hab.trans' h.isTop ⟨c, hc⟩

@[simp]
/--
lemma `isMin_coe` / 引理 `isMin_coe`

English:
lemma isMin_coe
  statement: IsMin (a : α) ↔ IsMin a where
  proof: h hba
  mpr h b hba := by
    refine @h ⟨b, mem_iff_forall_le_or_ge.2 fun c hc => ?_⟩ hba
    classical
exact .inl hba.trans h.isBot ⟨c, hc⟩

中文:
引理 isMin_coe
  结论: IsMin (a : α) ↔ IsMin a where
  证明: h hba
  mpr h b hba := by
    refine @h ⟨b, mem_iff_forall_le_or_ge.2 fun c hc => ?_⟩ hba
    classical
exact .inl hba.trans h.isBot ⟨c, hc⟩
-/
lemma isMin_coe : IsMin (a : α) ↔ IsMin a where
  mp h b hba := h hba
  mpr h b hba := by
    refine @h ⟨b, mem_iff_forall_le_or_ge.2 fun c hc => ?_⟩ hba
    classical
exact .inl hba.trans h.isBot ⟨c, hc⟩

variable [Preorder 𝕆]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [GradeOrder
  signature: 𝕆 α] (s
  body: .liftRight _ (Subtype.strictMono_coe _) fun _ _ => coe_covBy_coe.2

中文:
实例 [GradeOrder
  签名: 𝕆 α] (s
  定义体: .liftRight _ (Subtype.strictMono_coe _) fun _ _ => coe_covBy_coe.2

Depends on / 依赖: Subtype, Subtype.strictMono_coe, coe_covBy_coe, liftRight, strictMono_coe
-/
instance [GradeOrder 𝕆 α] (s : Flag α) : GradeOrder 𝕆 s :=
  .liftRight _ (Subtype.strictMono_coe _) fun _ _ => coe_covBy_coe.2

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [GradeMinOrder
  signature: 𝕆 α] (s
  body: .liftRight _ (Subtype.strictMono_coe _) (fun _ _ => coe_covBy_coe.2) fun _ => isMin_coe.2

中文:
实例 [GradeMinOrder
  签名: 𝕆 α] (s
  定义体: .liftRight _ (Subtype.strictMono_coe _) (fun _ _ => coe_covBy_coe.2) fun _ => isMin_coe.2

Depends on / 依赖: Subtype, Subtype.strictMono_coe, coe_covBy_coe, isMin_coe, liftRight, strictMono_coe
-/
instance [GradeMinOrder 𝕆 α] (s : Flag α) : GradeMinOrder 𝕆 s :=
  .liftRight _ (Subtype.strictMono_coe _) (fun _ _ => coe_covBy_coe.2) fun _ => isMin_coe.2

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [GradeMaxOrder
  signature: 𝕆 α] (s
  body: .liftRight _ (Subtype.strictMono_coe _) (fun _ _ => coe_covBy_coe.2) fun _ => isMax_coe.2

中文:
实例 [GradeMaxOrder
  签名: 𝕆 α] (s
  定义体: .liftRight _ (Subtype.strictMono_coe _) (fun _ _ => coe_covBy_coe.2) fun _ => isMax_coe.2

Depends on / 依赖: Subtype, Subtype.strictMono_coe, coe_covBy_coe, isMax_coe, liftRight, strictMono_coe
-/
instance [GradeMaxOrder 𝕆 α] (s : Flag α) : GradeMaxOrder 𝕆 s :=
  .liftRight _ (Subtype.strictMono_coe _) (fun _ _ => coe_covBy_coe.2) fun _ => isMax_coe.2

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [GradeBoundedOrder
  signature: 𝕆 α] (s
  body: .liftRight _ (Subtype.strictMono_coe _) (fun _ _ => coe_covBy_coe.2) (fun _ => isMin_coe.2)
    fun _ => isMax_coe.2

中文:
实例 [GradeBoundedOrder
  签名: 𝕆 α] (s
  定义体: .liftRight _ (Subtype.strictMono_coe _) (fun _ _ => coe_covBy_coe.2) (fun _ => isMin_coe.2)
    fun _ => isMax_coe.2

Depends on / 依赖: Subtype, Subtype.strictMono_coe, coe_covBy_coe, isMax_coe, isMin_coe, liftRight, strictMono_coe
-/
instance [GradeBoundedOrder 𝕆 α] (s : Flag α) : GradeBoundedOrder 𝕆 s :=
  .liftRight _ (Subtype.strictMono_coe _) (fun _ _ => coe_covBy_coe.2) (fun _ => isMin_coe.2)
    fun _ => isMax_coe.2

/--
lemma `grade_coe` / 引理 `grade_coe`

English:
lemma grade_coe
  given: [GradeOrder 𝕆 α] (a : s)
  statement: grade 𝕆 (a : α) = grade 𝕆 a
  proof: rfl

中文:
引理 grade_coe
  条件: [GradeOrder 𝕆 α] (a : s)
  结论: grade 𝕆 (a : α) = grade 𝕆 a
  证明: rfl

Depends on / 依赖: CommRing, DimensionLEOne, KrullDimLE, Ring.DimensionLEOne, Ring.KrullDimLE
-/
@[simp, norm_cast] lemma grade_coe [GradeOrder 𝕆 α] (a : s) : grade 𝕆 (a : α) = grade 𝕆 a := rfl

end Flag
