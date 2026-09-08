/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Order.Lattice

/-!
# Ordered Subtraction

This file proves lemmas relating (truncated) subtraction with an order. We provide a class
`OrderedSub` stating that `a - b ≤ c ↔ a ≤ c + b`.

The subtraction discussed here could both be normal subtraction in an additive group or truncated
subtraction on a canonically ordered monoid (`ℕ`, `Multiset`, `ENNReal`, ...)

## Implementation details

`OrderedSub` is a mixin type-class, so that we can use the results in this file even in cases
where we don't have a `CanonicallyOrderedAdd` instance
(even though that is our main focus). Conversely, this means we can use
`CanonicallyOrderedAdd` without necessarily having to define a subtraction.

The results in this file are ordered by the type-class assumption needed to prove it.
This means that similar results might not be close to each other. Furthermore, we don't prove
implications if a bi-implication can be proven under the same assumptions.

Lemmas using this class are named using `tsub` instead of `sub` (short for "truncated subtraction").
This is to avoid naming conflicts with similar lemmas about ordered groups.

We provide a second version of most results that require `[AddLeftReflectLE α]`. In the
second version we replace this type-class assumption by explicit `AddLECancellable` assumptions.

TODO: maybe we should make a multiplicative version of this, so that we can replace some identical
lemmas about subtraction/division in `Ordered[Add]CommGroup` with these.

TODO: generalize `Nat.le_of_le_of_sub_le_sub_right`, `Nat.sub_le_sub_right_iff`,
  `Nat.mul_self_sub_mul_self_eq`
-/

public section


variable {α : Type*}

/-- `OrderedSub α` means that `α` has a subtraction characterized by `a - b ≤ c ↔ a ≤ c + b`.
In other words, `a - b` is the least `c` such that `a ≤ b + c`.

This is satisfied both by the subtraction in additive ordered groups and by truncated subtraction
in canonically ordered monoids on many specific types.
-/
/-
**OrderedSub** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_2) → [LE α] → [Add α] → [Sub α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`OrderedSub α` means that `α` has a subtraction characterized by `a - b ≤ c ↔ a 
≤ c + b`.
In other words, `a - b` is the least `c` such that `a ≤ b + c`.

This is satisfied both by the subtraction in additive ordered groups and by trun
cated subtraction
in canonically ordered monoids on many specific types.
-/
class OrderedSub (α : Type*) [LE α] [Add α] [Sub α] : Prop where
  /-- `a - b` provides a lower bound on `c` such that `a ≤ c + b`. -/
  tsub_le_iff_right : ∀ a b c : α, a - b ≤ c ↔ a ≤ c + b

section Add

@[simp]
/-
**tsub_le_iff_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_le_iff_right [LE α] [Add α] [Sub α] [OrderedSub α] {a b c : α} : a - 
b <= c ↔ a <= c + b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderedSub.tsub_le_iff_right`：∀ {α : Type u_2} {inst : LE α} {inst_1 : A
dd α} {inst_2 : Sub α} [self : OrderedSub α] (a b c : α),   a - b ≤ c ↔ a ≤ c + 
b
-/
theorem tsub_le_iff_right [LE α] [Add α] [Sub α] [OrderedSub α] {a b c : α} :
    a - b ≤ c ↔ a ≤ c + b :=
  OrderedSub.tsub_le_iff_right a b c

variable [Preorder α] [Add α] [Sub α] [OrderedSub α] {a b : α}

/-- See `add_tsub_cancel_right` for the equality if `AddLeftReflectLE α`. -/
/-
**add_tsub_le_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：add_tsub_le_right : a + b - b <= a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tsub_le_iff_right`：tsub_le_iff_right [LE α] [Add α] [Sub α] [OrderedSub 
α] {a b c : α} : a - b <= c ↔ a <= c + b
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
See `add_tsub_cancel_right` for the equality if `AddLeftReflectLE α`.
-/
theorem add_tsub_le_right : a + b - b ≤ a :=
  tsub_le_iff_right.mpr le_rfl
/-
**le_tsub_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_tsub_add : b <= b - a + a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tsub_le_iff_right`：tsub_le_iff_right [LE α] [Add α] [Sub α] [OrderedSub 
α] {a b c : α} : a - b <= c ↔ a <= c + b
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem le_tsub_add : b ≤ b - a + a :=
  tsub_le_iff_right.mp le_rfl

end Add

/-! ### Preorder -/


section OrderedAddCommSemigroup

section Preorder

variable [Preorder α]

section AddCommSemigroup

variable [AddCommSemigroup α] [Sub α] [OrderedSub α] {a b c d : α}

-- TODO: Most results can be generalized to `[Add α] [IsAddCommutative α]`

/-
**tsub_le_iff_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_le_iff_left : a - b <= c ↔ a <= b + c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsub_le_iff_right`：tsub_le_iff_right [LE α] [Add α] [Sub α] [OrderedSub 
α] {a b c : α} : a - b <= c ↔ a <= c + b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tsub_le_iff_left : a - b ≤ c ↔ a ≤ b + c := by rw [tsub_le_iff_right, add_comm]
/-
**le_add_tsub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_add_tsub : a <= b + (a - b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tsub_le_iff_left`：tsub_le_iff_left : a - b <= c ↔ a <= b + c
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem le_add_tsub : a ≤ b + (a - b) :=
  tsub_le_iff_left.mp le_rfl

/-- See `add_tsub_cancel_left` for the equality if `AddLeftReflectLE α`. -/
/-
**add_tsub_le_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：add_tsub_le_left : a + b - a <= b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tsub_le_iff_left`：tsub_le_iff_left : a - b <= c ↔ a <= b + c
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
See `add_tsub_cancel_left` for the equality if `AddLeftReflectLE α`.
-/
theorem add_tsub_le_left : a + b - a ≤ b :=
  tsub_le_iff_left.mpr le_rfl
/-
**tsub_le_tsub_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_le_tsub_right (h : a <= b) (c : α) : a - c <= b - c
参数：h : a <= b；c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tsub_le_iff_left`：tsub_le_iff_left : a - b <= c ↔ a <= b + c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_add_tsub`：le_add_tsub : a <= b + (a - b)
-/
theorem tsub_le_tsub_right (h : a ≤ b) (c : α) : a - c ≤ b - c :=
  tsub_le_iff_left.mpr <| h.trans le_add_tsub
/-
**tsub_le_iff_tsub_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_le_iff_tsub_le : a - b <= c ↔ a - c <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsub_le_iff_left`：tsub_le_iff_left : a - b <= c ↔ a <= b + c
· 使用定理 `tsub_le_iff_right`：tsub_le_iff_right [LE α] [Add α] [Sub α] [OrderedSub 
α] {a b c : α} : a - b <= c ↔ a <= c + b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tsub_le_iff_tsub_le : a - b ≤ c ↔ a - c ≤ b := by rw [tsub_le_iff_left, tsub_le_iff_right]

/-- See `tsub_tsub_cancel_of_le` for the equality. -/
/-
**tsub_tsub_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_tsub_le : b - (b - a) <= a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tsub_le_iff_right`：tsub_le_iff_right [LE α] [Add α] [Sub α] [OrderedSub 
α] {a b c : α} : a - b <= c ↔ a <= c + b
· 使用定理 `le_add_tsub`：le_add_tsub : a <= b + (a - b)

--- 原说明 ---
See `tsub_tsub_cancel_of_le` for the equality.
-/
theorem tsub_tsub_le : b - (b - a) ≤ a :=
  tsub_le_iff_right.mpr le_add_tsub

section Cov

variable [AddLeftMono α]

/-
**tsub_le_tsub_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_le_tsub_left (h : a <= b) (c : α) : c - b <= c - a
参数：h : a <= b；c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsub_le_iff_left`：tsub_le_iff_left : a - b <= c ↔ a <= b + c
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_add_tsub`：le_add_tsub : a <= b + (a - b)
-/
theorem tsub_le_tsub_left (h : a ≤ b) (c : α) : c - b ≤ c - a := by
  grw [tsub_le_iff_left, ← h, ← le_add_tsub]
/-
**tsub_le_tsub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : AddCommSemigroup α] [inst_2
 : Sub α] [OrderedSub α] {a b c d : α}   [AddLeftMono α], a ≤ b → c ≤ d → a - d 
≤ b - c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `tsub_le_tsub_right`：tsub_le_tsub_right (h : a <= b) (c : α) : a - c <= b
 - c
· 使用定理 `tsub_le_tsub_left`：tsub_le_tsub_left (h : a <= b) (c : α) : c - b <= c -
 a
-/
@[gcongr] theorem tsub_le_tsub (hab : a ≤ b) (hcd : c ≤ d) : a - d ≤ b - c :=
  (tsub_le_tsub_right hab _).trans <| tsub_le_tsub_left hcd _
/-
**antitone_const_tsub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antitone_const_tsub : Antitone fun x => c - x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tsub_le_tsub`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : AddCommSemi
group α] [inst_2 : Sub α] [OrderedSub α] {a b c d : α}   [AddLeftMono α], a ≤ b 
→ …
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
theorem antitone_const_tsub : Antitone fun x => c - x := fun _ _ hxy => tsub_le_tsub rfl.le hxy

/-- See `add_tsub_assoc_of_le` for the equality. -/
/-
**add_tsub_le_assoc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：add_tsub_le_assoc : a + b - c <= a + (b - c)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsub_le_iff_left`：tsub_le_iff_left : a - b <= c ↔ a <= b + c
· 使用定理 `add_left_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G),
 a + (b + c) = b + (a + c)
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_add_tsub`：le_add_tsub : a <= b + (a - b)

--- 原说明 ---
See `add_tsub_assoc_of_le` for the equality.
-/
theorem add_tsub_le_assoc : a + b - c ≤ a + (b - c) := by
  grw [tsub_le_iff_left, add_left_comm, ← le_add_tsub]

/-- See `tsub_add_eq_add_tsub` for the equality. -/
/-
**add_tsub_le_tsub_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：add_tsub_le_tsub_add : a + b - c <= a - c + b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_tsub_le_assoc`：add_tsub_le_assoc : a + b - c <= a + (b - c)

--- 原说明 ---
See `tsub_add_eq_add_tsub` for the equality.
-/
theorem add_tsub_le_tsub_add : a + b - c ≤ a - c + b := by
  rw [add_comm, add_comm _ b]
  exact add_tsub_le_assoc
/-
**add_le_add_add_tsub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：add_le_add_add_tsub : a + b <= a + c + (b - c)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_add_tsub`：le_add_tsub : a <= b + (a - b)
-/
theorem add_le_add_add_tsub : a + b ≤ a + c + (b - c) := by grw [add_assoc, ← le_add_tsub]
/-
**le_tsub_add_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_tsub_add_add : a + b <= a - c + (b + c)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_le_add_add_tsub`：add_le_add_add_tsub : a + b <= a + c + (b - c)
-/
theorem le_tsub_add_add : a + b ≤ a - c + (b + c) := by
  rw [add_comm a, add_comm (a - c)]
  exact add_le_add_add_tsub
/-
**tsub_le_tsub_add_tsub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_le_tsub_add_tsub : a - c <= a - b + (b - c)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsub_le_iff_left`：tsub_le_iff_left : a - b <= c ↔ a <= b + c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_right_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G)
, a + b + c = a + c + b
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_add_tsub`：le_add_tsub : a <= b + (a - b)
-/
theorem tsub_le_tsub_add_tsub : a - c ≤ a - b + (b - c) := by
  grw [tsub_le_iff_left, ← add_assoc, add_right_comm, ← le_add_tsub, ← le_add_tsub]
/-
**tsub_tsub_tsub_le_tsub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_tsub_tsub_le_tsub : c - a - (c - b) <= b - a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsub_le_iff_left`：tsub_le_iff_left : a - b <= c ↔ a <= b + c
· 使用定理 `add_left_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G),
 a + (b + c) = b + (a + c)
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_add_tsub`：le_add_tsub : a <= b + (a - b)
· 使用定理 `le_tsub_add`：le_tsub_add : b <= b - a + a
-/
theorem tsub_tsub_tsub_le_tsub : c - a - (c - b) ≤ b - a := by
  grw [tsub_le_iff_left, tsub_le_iff_left, add_left_comm, ← le_add_tsub, ← le_tsub_add]
/-
**tsub_tsub_le_tsub_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_tsub_le_tsub_add {a b c : α} : a - (b - c) <= a - b + c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tsub_le_iff_right`：tsub_le_iff_right [LE α] [Add α] [Sub α] [OrderedSub 
α] {a b c : α} : a - b <= c ↔ a <= c + b
· 使用定理 `le_tsub_add`：le_tsub_add : b <= b - a + a
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_add_tsub`：le_add_tsub : a <= b + (a - b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
-/
theorem tsub_tsub_le_tsub_add {a b c : α} : a - (b - c) ≤ a - b + c :=
  tsub_le_iff_right.2 <|
    calc
      a ≤ a - b + b := le_tsub_add
      _ ≤ a - b + (c + (b - c)) := by grw [← le_add_tsub]
      _ = a - b + c + (b - c) := (add_assoc _ _ _).symm

/-- See `tsub_add_tsub_comm` for the equality. -/
/-
**add_tsub_add_le_tsub_add_tsub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：add_tsub_add_le_tsub_add_tsub : a + b - (c + d) <= a - c + (b - d)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `tsub_le_iff_left`：tsub_le_iff_left : a - b <= c ↔ a <= b + c
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `tsub_le_tsub_right`：tsub_le_tsub_right (h : a <= b) (c : α) : a - c <= b
 - c
· 使用定理 `add_tsub_le_assoc`：add_tsub_le_assoc : a + b - c <= a + (b - c)

--- 原说明 ---
See `tsub_add_tsub_comm` for the equality.
-/
theorem add_tsub_add_le_tsub_add_tsub : a + b - (c + d) ≤ a - c + (b - d) := by
  rw [add_comm c, tsub_le_iff_left, add_assoc, ← tsub_le_iff_left, ← tsub_le_iff_left]
  refine (tsub_le_tsub_right add_tsub_le_assoc c).trans ?_
  rw [add_comm a, add_comm (a - c)]
  exact add_tsub_le_assoc

/-- See `add_tsub_add_eq_tsub_left` for the equality. -/
/-
**add_tsub_add_le_tsub_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：add_tsub_add_le_tsub_left : a + b - (a + c) <= b - c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsub_le_iff_left`：tsub_le_iff_left : a - b <= c ↔ a <= b + c
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_add_tsub`：le_add_tsub : a <= b + (a - b)

--- 原说明 ---
See `add_tsub_add_eq_tsub_left` for the equality.
-/
theorem add_tsub_add_le_tsub_left : a + b - (a + c) ≤ b - c := by
  grw [tsub_le_iff_left, add_assoc, ← le_add_tsub]

/-- See `add_tsub_add_eq_tsub_right` for the equality. -/
/-
**add_tsub_add_le_tsub_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：add_tsub_add_le_tsub_right : a + c - (b + c) <= a - b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsub_le_iff_left`：tsub_le_iff_left : a - b <= c ↔ a <= b + c
· 使用定理 `add_right_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G)
, a + b + c = a + c + b
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_add_tsub`：le_add_tsub : a <= b + (a - b)

--- 原说明 ---
See `add_tsub_add_eq_tsub_right` for the equality.
-/
theorem add_tsub_add_le_tsub_right : a + c - (b + c) ≤ a - b := by
  grw [tsub_le_iff_left, add_right_comm, ← le_add_tsub]

end Cov

/-! #### Lemmas that assume that an element is `AddLECancellable` -/


namespace AddLECancellable

/-
**AddLECancellable.le_add_tsub_swap** 是 Mathlib 中的一个定理，位于命名空间 `AddLECancellable`
。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : AddCommSemigroup α] [inst_2
 : Sub α] [OrderedSub α] {a b : α},   AddLECancellable b → a ≤ b + a - b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_add_tsub`：le_add_tsub : a <= b + (a - b)
-/
protected theorem le_add_tsub_swap (hb : AddLECancellable b) : a ≤ b + a - b :=
  hb le_add_tsub
/-
**AddLECancellable.le_add_tsub** 是 Mathlib 中的一个定理，位于命名空间 `AddLECancellable`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : AddCommSemigroup α] [inst_2
 : Sub α] [OrderedSub α] {a b : α},   AddLECancellable b → a ≤ a + b - b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `AddLECancellable.le_add_tsub_swap`：∀ {α : Type u_1} [inst : Preorder α] 
[inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b : α},   AddLE
Cancellable b → a ≤ b +…
-/
protected theorem le_add_tsub (hb : AddLECancellable b) : a ≤ a + b - b := by
  rw [add_comm]
  exact hb.le_add_tsub_swap
/-
**AddLECancellable.le_tsub_of_add_le_left** 是 Mathlib 中的一个定理，位于命名空间 `AddLECancel
lable`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : AddCommSemigroup α] [inst_2
 : Sub α] [OrderedSub α] {a b c : α},   AddLECancellable a → a + b ≤ c → b ≤ c -
 a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_add_tsub`：le_add_tsub : a <= b + (a - b)
-/
protected theorem le_tsub_of_add_le_left (ha : AddLECancellable a) (h : a + b ≤ c) : b ≤ c - a :=
  ha <| h.trans le_add_tsub
/-
**AddLECancellable.le_tsub_of_add_le_right** 是 Mathlib 中的一个定理，位于命名空间 `AddLECance
llable`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : AddCommSemigroup α] [inst_2
 : Sub α] [OrderedSub α] {a b c : α},   AddLECancellable b → a + b ≤ c → a ≤ c -
 b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.le_tsub_of_add_le_left`：∀ {α : Type u_1} [inst : Preord
er α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b c : α},
   AddLECancellable a → a + b…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
protected theorem le_tsub_of_add_le_right (hb : AddLECancellable b) (h : a + b ≤ c) : a ≤ c - b :=
  hb.le_tsub_of_add_le_left <| by rwa [add_comm]

end AddLECancellable

/-! ### Lemmas where addition is order-reflecting -/


section Contra

variable [AddLeftReflectLE α]

/-
**le_add_tsub_swap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_add_tsub_swap : a <= b + a - b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.le_add_tsub_swap`：∀ {α : Type u_1} [inst : Preorder α] 
[inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b : α},   AddLE
Cancellable b → a ≤ b +…
· 使用定理 `Contravariant.AddLECancellable`：∀ {α : Type u_1} [inst : Add α] [inst_1 
: LE α] [AddLeftReflectLE α] {a : α}, AddLECancellable a
-/
theorem le_add_tsub_swap : a ≤ b + a - b :=
  Contravariant.AddLECancellable.le_add_tsub_swap
/-
**le_add_tsub'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_add_tsub' : a <= a + b - b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.le_add_tsub`：∀ {α : Type u_1} [inst : Preorder α] [inst
_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b : α},   AddLECance
llable b → a ≤ a +…
· 使用定理 `Contravariant.AddLECancellable`：∀ {α : Type u_1} [inst : Add α] [inst_1 
: LE α] [AddLeftReflectLE α] {a : α}, AddLECancellable a
-/
theorem le_add_tsub' : a ≤ a + b - b :=
  Contravariant.AddLECancellable.le_add_tsub
/-
**le_tsub_of_add_le_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_tsub_of_add_le_left (h : a + b <= c) : b <= c - a
参数：h : a + b <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.le_tsub_of_add_le_left`：∀ {α : Type u_1} [inst : Preord
er α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b c : α},
   AddLECancellable a → a + b…
· 使用定理 `Contravariant.AddLECancellable`：∀ {α : Type u_1} [inst : Add α] [inst_1 
: LE α] [AddLeftReflectLE α] {a : α}, AddLECancellable a
-/
theorem le_tsub_of_add_le_left (h : a + b ≤ c) : b ≤ c - a :=
  Contravariant.AddLECancellable.le_tsub_of_add_le_left h
/-
**le_tsub_of_add_le_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_tsub_of_add_le_right (h : a + b <= c) : a <= c - b
参数：h : a + b <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.le_tsub_of_add_le_right`：∀ {α : Type u_1} [inst : Preor
der α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b c : α}
,   AddLECancellable b → a + b…
· 使用定理 `Contravariant.AddLECancellable`：∀ {α : Type u_1} [inst : Add α] [inst_1 
: LE α] [AddLeftReflectLE α] {a : α}, AddLECancellable a
-/
theorem le_tsub_of_add_le_right (h : a + b ≤ c) : a ≤ c - b :=
  Contravariant.AddLECancellable.le_tsub_of_add_le_right h

end Contra

end AddCommSemigroup

variable [AddCommMonoid α] [Sub α] [OrderedSub α] {a b : α}

/-
**tsub_nonpos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_nonpos : a - b <= 0 ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsub_le_iff_left`：tsub_le_iff_left : a - b <= c ↔ a <= b + c
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tsub_nonpos : a - b ≤ 0 ↔ a ≤ b := by rw [tsub_le_iff_left, add_zero]

alias ⟨_, tsub_nonpos_of_le⟩ := tsub_nonpos

end Preorder

/-! ### Partial order -/


variable [PartialOrder α] [AddCommSemigroup α] [Sub α] [OrderedSub α] {a b c d : α}

/-
**tsub_tsub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_tsub (b a c : α) : b - a - c = b - (a + c)
参数：b a c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsub_le_iff_left`：tsub_le_iff_left : a - b <= c ↔ a <= b + c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem tsub_tsub (b a c : α) : b - a - c = b - (a + c) := by
  apply le_antisymm
  · rw [tsub_le_iff_left, tsub_le_iff_left, ← add_assoc, ← tsub_le_iff_left]
  · rw [tsub_le_iff_left, add_assoc, ← tsub_le_iff_left, ← tsub_le_iff_left]
/-
**tsub_add_eq_tsub_tsub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_add_eq_tsub_tsub (a b c : α) : a - (b + c) = a - b - c
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tsub_tsub`：tsub_tsub (b a c : α) : b - a - c = b - (a + c)
-/
theorem tsub_add_eq_tsub_tsub (a b c : α) : a - (b + c) = a - b - c :=
  (tsub_tsub _ _ _).symm
/-
**tsub_add_eq_tsub_tsub_swap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_add_eq_tsub_tsub_swap (a b c : α) : a - (b + c) = a - c - b
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `tsub_add_eq_tsub_tsub`：tsub_add_eq_tsub_tsub (a b c : α) : a - (b + c) =
 a - b - c
-/
theorem tsub_add_eq_tsub_tsub_swap (a b c : α) : a - (b + c) = a - c - b := by
  rw [add_comm]
  apply tsub_add_eq_tsub_tsub
/-
**tsub_right_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_right_comm : a - b - c = a - c - b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tsub_add_eq_tsub_tsub`：tsub_add_eq_tsub_tsub (a b c : α) : a - (b + c) =
 a - b - c
· 使用定理 `tsub_add_eq_tsub_tsub_swap`：tsub_add_eq_tsub_tsub_swap (a b c : α) : a -
 (b + c) = a - c - b
-/
theorem tsub_right_comm : a - b - c = a - c - b := by
  rw [← tsub_add_eq_tsub_tsub, tsub_add_eq_tsub_tsub_swap]

/-! ### Lemmas that assume that an element is `AddLECancellable`. -/


namespace AddLECancellable

/-- See `AddLECancellable.tsub_eq_of_eq_add'` for a version assuming that `a = c + b` itself is
cancellable rather than `b`. -/
/-
**AddLECancellable.tsub_eq_of_eq_add** 是 Mathlib 中的一个定理，位于命名空间 `AddLECancellable
`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : AddCommSemigroup α] [in
st_2 : Sub α] [OrderedSub α] {a b c : α},   AddLECancellable b → a = c + b → a -
 b = c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tsub_le_iff_right`：tsub_le_iff_right [LE α] [Add α] [Sub α] [OrderedSub 
α] {a b c : α} : a - b <= c ↔ a <= c + b
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddLECancellable.le_add_tsub`：∀ {α : Type u_1} [inst : Preorder α] [inst
_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b : α},   AddLECance
llable b → a ≤ a +…

--- 原说明 ---
See `AddLECancellable.tsub_eq_of_eq_add'` for a version assuming that `a = c + b
` itself is
cancellable rather than `b`.
-/
protected theorem tsub_eq_of_eq_add (hb : AddLECancellable b) (h : a = c + b) : a - b = c :=
  le_antisymm (tsub_le_iff_right.mpr h.le) <| by
    rw [h]
    exact hb.le_add_tsub

/-- Weaker version of `AddLECancellable.tsub_eq_of_eq_add` assuming that `a = c + b` itself is
cancellable rather than `b`. -/
/-
**AddLECancellable.tsub_eq_of_eq_add'** 是 Mathlib 中的一个定理，位于命名空间 `AddLECancellabl
e`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : AddCommSemigroup α] [in
st_2 : Sub α] [OrderedSub α] {a b c : α}   [AddLeftMono α], AddLECancellable a →
 a = c + b → a - b = c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.tsub_eq_of_eq_add`：∀ {α : Type u_1} [inst : PartialOrde
r α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b c : α}, 
  AddLECancellable b → a…
· 使用定理 `AddLECancellable.of_add_right`：∀ {α : Type u_1} [inst : LE α] [inst_1 : 
AddSemigroup α] [AddLeftMono α] {a b : α},   AddLECancellable (a + b) → AddLECan
cellable b

--- 原说明 ---
Weaker version of `AddLECancellable.tsub_eq_of_eq_add` assuming that `a = c + b`
 itself is
cancellable rather than `b`.
-/
protected lemma tsub_eq_of_eq_add' [AddLeftMono α] (ha : AddLECancellable a)
    (h : a = c + b) : a - b = c := (h ▸ ha).of_add_right.tsub_eq_of_eq_add h

/-- See `AddLECancellable.eq_tsub_of_add_eq'` for a version assuming that `b = a + c` itself is
cancellable rather than `c`. -/
/-
**AddLECancellable.eq_tsub_of_add_eq** 是 Mathlib 中的一个定理，位于命名空间 `AddLECancellable
`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : AddCommSemigroup α] [in
st_2 : Sub α] [OrderedSub α] {a b c : α},   AddLECancellable c → a + c = b → a =
 b - c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddLECancellable.tsub_eq_of_eq_add`：∀ {α : Type u_1} [inst : PartialOrde
r α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b c : α}, 
  AddLECancellable b → a…

--- 原说明 ---
See `AddLECancellable.eq_tsub_of_add_eq'` for a version assuming that `b = a + c
` itself is
cancellable rather than `c`.
-/
protected theorem eq_tsub_of_add_eq (hc : AddLECancellable c) (h : a + c = b) : a = b - c :=
  (hc.tsub_eq_of_eq_add h.symm).symm

/-- Weaker version of `AddLECancellable.eq_tsub_of_add_eq` assuming that `b = a + c` itself is
cancellable rather than `c`. -/
/-
**AddLECancellable.eq_tsub_of_add_eq'** 是 Mathlib 中的一个定理，位于命名空间 `AddLECancellabl
e`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : AddCommSemigroup α] [in
st_2 : Sub α] [OrderedSub α] {a b c : α}   [AddLeftMono α], AddLECancellable b →
 a + c = b → a = b - c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddLECancellable.tsub_eq_of_eq_add'`：∀ {α : Type u_1} [inst : PartialOrd
er α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b c : α} 
  [AddLeftMono α], AddLEC…

--- 原说明 ---
Weaker version of `AddLECancellable.eq_tsub_of_add_eq` assuming that `b = a + c`
 itself is
cancellable rather than `c`.
-/
protected lemma eq_tsub_of_add_eq' [AddLeftMono α] (hb : AddLECancellable b)
    (h : a + c = b) : a = b - c := (hb.tsub_eq_of_eq_add' h.symm).symm

/-- See `AddLECancellable.tsub_eq_of_eq_add_rev'` for a version assuming that `a = b + c` itself is
cancellable rather than `b`. -/
/-
**AddLECancellable.tsub_eq_of_eq_add_rev** 是 Mathlib 中的一个定理，位于命名空间 `AddLECancell
able`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : AddCommSemigroup α] [in
st_2 : Sub α] [OrderedSub α] {a b c : α},   AddLECancellable b → a = b + c → a -
 b = c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.tsub_eq_of_eq_add`：∀ {α : Type u_1} [inst : PartialOrde
r α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b c : α}, 
  AddLECancellable b → a…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a

--- 原说明 ---
See `AddLECancellable.tsub_eq_of_eq_add_rev'` for a version assuming that `a = b
 + c` itself is
cancellable rather than `b`.
-/
protected theorem tsub_eq_of_eq_add_rev (hb : AddLECancellable b) (h : a = b + c) : a - b = c :=
  hb.tsub_eq_of_eq_add <| by rw [add_comm, h]

/-- Weaker version of `AddLECancellable.tsub_eq_of_eq_add_rev` assuming that `a = b + c` itself is
cancellable rather than `b`. -/
/-
**AddLECancellable.tsub_eq_of_eq_add_rev'** 是 Mathlib 中的一个定理，位于命名空间 `AddLECancel
lable`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : AddCommSemigroup α] [in
st_2 : Sub α] [OrderedSub α] {a b c : α}   [AddLeftMono α], AddLECancellable a →
 a = b + c → a - b = c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.tsub_eq_of_eq_add'`：∀ {α : Type u_1} [inst : PartialOrd
er α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b c : α} 
  [AddLeftMono α], AddLEC…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a

--- 原说明 ---
Weaker version of `AddLECancellable.tsub_eq_of_eq_add_rev` assuming that `a = b 
+ c` itself is
cancellable rather than `b`.
-/
protected lemma tsub_eq_of_eq_add_rev' [AddLeftMono α]
    (ha : AddLECancellable a) (h : a = b + c) : a - b = c :=
  ha.tsub_eq_of_eq_add' <| by rw [add_comm, h]

@[simp]
/-
**AddLECancellable.add_tsub_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `AddLECancell
able`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : AddCommSemigroup α] [in
st_2 : Sub α] [OrderedSub α] {a b : α},   AddLECancellable b → a + b - b = a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.tsub_eq_of_eq_add`：∀ {α : Type u_1} [inst : PartialOrde
r α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b c : α}, 
  AddLECancellable b → a…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
protected theorem add_tsub_cancel_right (hb : AddLECancellable b) : a + b - b = a :=
  hb.tsub_eq_of_eq_add <| by rw [add_comm]

@[simp]
/-
**AddLECancellable.add_tsub_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `AddLECancella
ble`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : AddCommSemigroup α] [in
st_2 : Sub α] [OrderedSub α] {a b : α},   AddLECancellable a → a + b - a = b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.tsub_eq_of_eq_add`：∀ {α : Type u_1} [inst : PartialOrde
r α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b c : α}, 
  AddLECancellable b → a…
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
protected theorem add_tsub_cancel_left (ha : AddLECancellable a) : a + b - a = b :=
  ha.tsub_eq_of_eq_add <| add_comm a b
/-
**AddLECancellable.lt_add_of_tsub_lt_left** 是 Mathlib 中的一个定理，位于命名空间 `AddLECancel
lable`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : AddCommSemigroup α] [in
st_2 : Sub α] [OrderedSub α] {a b c : α},   AddLECancellable b → a - b < c → a <
 b + c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lt_iff_le_and_ne`：lt_iff_le_and_ne : a < b ↔ a <= b ∧ a != b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tsub_le_iff_left`：tsub_le_iff_left : a - b <= c ↔ a <= b + c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AddLECancellable.add_tsub_cancel_left`：∀ {α : Type u_1} [inst : PartialO
rder α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b : α},
   AddLECancellable a → a +…
-/
protected theorem lt_add_of_tsub_lt_left (hb : AddLECancellable b) (h : a - b < c) : a < b + c := by
  rw [lt_iff_le_and_ne, ← tsub_le_iff_left]
  refine ⟨h.le, ?_⟩
  rintro rfl
  simp [hb] at h
/-
**AddLECancellable.lt_add_of_tsub_lt_right** 是 Mathlib 中的一个定理，位于命名空间 `AddLECance
llable`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : AddCommSemigroup α] [in
st_2 : Sub α] [OrderedSub α] {a b c : α},   AddLECancellable c → a - c < b → a <
 b + c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lt_iff_le_and_ne`：lt_iff_le_and_ne : a < b ↔ a <= b ∧ a != b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tsub_le_iff_right`：tsub_le_iff_right [LE α] [Add α] [Sub α] [OrderedSub 
α] {a b c : α} : a - b <= c ↔ a <= c + b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AddLECancellable.add_tsub_cancel_right`：∀ {α : Type u_1} [inst : Partial
Order α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b : α}
,   AddLECancellable b → a +…
-/
protected theorem lt_add_of_tsub_lt_right (hc : AddLECancellable c) (h : a - c < b) :
    a < b + c := by
  rw [lt_iff_le_and_ne, ← tsub_le_iff_right]
  refine ⟨h.le, ?_⟩
  rintro rfl
  simp [hc] at h
/-
**AddLECancellable.lt_tsub_of_add_lt_right** 是 Mathlib 中的一个定理，位于命名空间 `AddLECance
llable`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : AddCommSemigroup α] [in
st_2 : Sub α] [OrderedSub α] {a b c : α},   AddLECancellable c → a + c < b → a <
 b - c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `AddLECancellable.le_tsub_of_add_le_right`：∀ {α : Type u_1} [inst : Preor
der α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b c : α}
,   AddLECancellable b → a + b…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `le_tsub_add`：le_tsub_add : b <= b - a + a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
protected theorem lt_tsub_of_add_lt_right (hc : AddLECancellable c) (h : a + c < b) : a < b - c :=
  (hc.le_tsub_of_add_le_right h.le).lt_of_ne <| by
    rintro rfl
    exact h.not_ge le_tsub_add
/-
**AddLECancellable.lt_tsub_of_add_lt_left** 是 Mathlib 中的一个定理，位于命名空间 `AddLECancel
lable`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : AddCommSemigroup α] [in
st_2 : Sub α] [OrderedSub α] {a b c : α},   AddLECancellable a → a + c < b → c <
 b - a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.lt_tsub_of_add_lt_right`：∀ {α : Type u_1} [inst : Parti
alOrder α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b c 
: α},   AddLECancellable c → a…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
protected theorem lt_tsub_of_add_lt_left (ha : AddLECancellable a) (h : a + c < b) : c < b - a :=
  ha.lt_tsub_of_add_lt_right <| by rwa [add_comm]

end AddLECancellable

/-! #### Lemmas where addition is order-reflecting. -/


section Contra

variable [AddLeftReflectLE α]

/-
**tsub_eq_of_eq_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_eq_of_eq_add (h : a = c + b) : a - b = c
参数：h : a = c + b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.tsub_eq_of_eq_add`：∀ {α : Type u_1} [inst : PartialOrde
r α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b c : α}, 
  AddLECancellable b → a…
· 使用定理 `Contravariant.AddLECancellable`：∀ {α : Type u_1} [inst : Add α] [inst_1 
: LE α] [AddLeftReflectLE α] {a : α}, AddLECancellable a
-/
theorem tsub_eq_of_eq_add (h : a = c + b) : a - b = c :=
  Contravariant.AddLECancellable.tsub_eq_of_eq_add h
/-
**eq_tsub_of_add_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_tsub_of_add_eq (h : a + c = b) : a = b - c
参数：h : a + c = b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.eq_tsub_of_add_eq`：∀ {α : Type u_1} [inst : PartialOrde
r α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b c : α}, 
  AddLECancellable c → a…
· 使用定理 `Contravariant.AddLECancellable`：∀ {α : Type u_1} [inst : Add α] [inst_1 
: LE α] [AddLeftReflectLE α] {a : α}, AddLECancellable a
-/
theorem eq_tsub_of_add_eq (h : a + c = b) : a = b - c :=
  Contravariant.AddLECancellable.eq_tsub_of_add_eq h
/-
**tsub_eq_of_eq_add_rev** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_eq_of_eq_add_rev (h : a = b + c) : a - b = c
参数：h : a = b + c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.tsub_eq_of_eq_add_rev`：∀ {α : Type u_1} [inst : Partial
Order α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b c : 
α},   AddLECancellable b → a…
· 使用定理 `Contravariant.AddLECancellable`：∀ {α : Type u_1} [inst : Add α] [inst_1 
: LE α] [AddLeftReflectLE α] {a : α}, AddLECancellable a
-/
theorem tsub_eq_of_eq_add_rev (h : a = b + c) : a - b = c :=
  Contravariant.AddLECancellable.tsub_eq_of_eq_add_rev h

@[simp]
/-
**add_tsub_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：add_tsub_cancel_right (a b : α) : a + b - b = a
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.add_tsub_cancel_right`：∀ {α : Type u_1} [inst : Partial
Order α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b : α}
,   AddLECancellable b → a +…
· 使用定理 `Contravariant.AddLECancellable`：∀ {α : Type u_1} [inst : Add α] [inst_1 
: LE α] [AddLeftReflectLE α] {a : α}, AddLECancellable a
-/
theorem add_tsub_cancel_right (a b : α) : a + b - b = a :=
  Contravariant.AddLECancellable.add_tsub_cancel_right

@[simp]
/-
**add_tsub_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：add_tsub_cancel_left (a b : α) : a + b - a = b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.add_tsub_cancel_left`：∀ {α : Type u_1} [inst : PartialO
rder α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b : α},
   AddLECancellable a → a +…
· 使用定理 `Contravariant.AddLECancellable`：∀ {α : Type u_1} [inst : Add α] [inst_1 
: LE α] [AddLeftReflectLE α] {a : α}, AddLECancellable a
-/
theorem add_tsub_cancel_left (a b : α) : a + b - a = b :=
  Contravariant.AddLECancellable.add_tsub_cancel_left

/-- A more general version of the reverse direction of `sub_eq_sub_iff_add_eq_add` -/
/-
**tsub_eq_tsub_of_add_eq_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_eq_tsub_of_add_eq_add (h : a + d = c + b) : a - b = c - d
参数：h : a + d = c + b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `tsub_right_comm`：tsub_right_comm : a - b - c = a - c - b

--- 原说明 ---
A more general version of the reverse direction of `sub_eq_sub_iff_add_eq_add`
-/
theorem tsub_eq_tsub_of_add_eq_add (h : a + d = c + b) : a - b = c - d := by
  calc a - b = a + d - d - b := by rw [add_tsub_cancel_right]
           _ = c + b - b - d := by rw [h, tsub_right_comm]
           _ = c - d := by rw [add_tsub_cancel_right]
/-
**lt_add_of_tsub_lt_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_add_of_tsub_lt_left (h : a - b < c) : a < b + c
参数：h : a - b < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.lt_add_of_tsub_lt_left`：∀ {α : Type u_1} [inst : Partia
lOrder α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b c :
 α},   AddLECancellable b → a…
· 使用定理 `Contravariant.AddLECancellable`：∀ {α : Type u_1} [inst : Add α] [inst_1 
: LE α] [AddLeftReflectLE α] {a : α}, AddLECancellable a
-/
theorem lt_add_of_tsub_lt_left (h : a - b < c) : a < b + c :=
  Contravariant.AddLECancellable.lt_add_of_tsub_lt_left h
/-
**lt_add_of_tsub_lt_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_add_of_tsub_lt_right (h : a - c < b) : a < b + c
参数：h : a - c < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.lt_add_of_tsub_lt_right`：∀ {α : Type u_1} [inst : Parti
alOrder α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b c 
: α},   AddLECancellable c → a…
· 使用定理 `Contravariant.AddLECancellable`：∀ {α : Type u_1} [inst : Add α] [inst_1 
: LE α] [AddLeftReflectLE α] {a : α}, AddLECancellable a
-/
theorem lt_add_of_tsub_lt_right (h : a - c < b) : a < b + c :=
  Contravariant.AddLECancellable.lt_add_of_tsub_lt_right h

/-- This lemma (and some of its corollaries) also holds for `ENNReal`, but this proof doesn't work
for it. Maybe we should add this lemma as field to `OrderedSub`? -/
/-
**lt_tsub_of_add_lt_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_tsub_of_add_lt_left : a + c < b -> c < b - a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.lt_tsub_of_add_lt_left`：∀ {α : Type u_1} [inst : Partia
lOrder α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b c :
 α},   AddLECancellable a → a…
· 使用定理 `Contravariant.AddLECancellable`：∀ {α : Type u_1} [inst : Add α] [inst_1 
: LE α] [AddLeftReflectLE α] {a : α}, AddLECancellable a

--- 原说明 ---
This lemma (and some of its corollaries) also holds for `ENNReal`, but this proo
f doesn't work
for it. Maybe we should add this lemma as field to `OrderedSub`?
-/
theorem lt_tsub_of_add_lt_left : a + c < b → c < b - a :=
  Contravariant.AddLECancellable.lt_tsub_of_add_lt_left
/-
**lt_tsub_of_add_lt_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_tsub_of_add_lt_right : a + c < b -> a < b - c
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.lt_tsub_of_add_lt_right`：∀ {α : Type u_1} [inst : Parti
alOrder α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b c 
: α},   AddLECancellable c → a…
· 使用定理 `Contravariant.AddLECancellable`：∀ {α : Type u_1} [inst : Add α] [inst_1 
: LE α] [AddLeftReflectLE α] {a : α}, AddLECancellable a
-/
theorem lt_tsub_of_add_lt_right : a + c < b → a < b - c :=
  Contravariant.AddLECancellable.lt_tsub_of_add_lt_right

end Contra

section Both

variable [AddLeftMono α] [AddLeftReflectLE α]

/-
**add_tsub_add_eq_tsub_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：add_tsub_add_eq_tsub_right (a c b : α) : a + c - (b + c) = a - b
参数：a c b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `add_tsub_add_le_tsub_right`：add_tsub_add_le_tsub_right : a + c - (b + c)
 <= a - b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tsub_le_iff_right`：tsub_le_iff_right [LE α] [Add α] [Sub α] [OrderedSub 
α] {a b c : α} : a - b <= c ↔ a <= c + b
· 使用定理 `le_of_add_le_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] 
[AddRightReflectLE α] {a b c : α}, b + a ≤ c + a → b ≤ c
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `le_tsub_add`：le_tsub_add : b <= b - a + a
-/
theorem add_tsub_add_eq_tsub_right (a c b : α) : a + c - (b + c) = a - b := by
  refine add_tsub_add_le_tsub_right.antisymm (tsub_le_iff_right.2 <| ?_)
  apply le_of_add_le_add_right
  rw [add_assoc]
  exact le_tsub_add
/-
**add_tsub_add_eq_tsub_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：add_tsub_add_eq_tsub_left (a b c : α) : a + b - (a + c) = b - c
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_tsub_add_eq_tsub_right`：add_tsub_add_eq_tsub_right (a c b : α) : a +
 c - (b + c) = a - b
-/
theorem add_tsub_add_eq_tsub_left (a b c : α) : a + b - (a + c) = b - c := by
  rw [add_comm a b, add_comm a c, add_tsub_add_eq_tsub_right]

end Both

end OrderedAddCommSemigroup

/-! ### Lemmas in a linearly ordered monoid. -/


section LinearOrder

variable {a b c : α} [LinearOrder α] [AddCommSemigroup α] [Sub α] [OrderedSub α]

/-- See `lt_of_tsub_lt_tsub_right_of_le` for a weaker statement in a partial order. -/
/-
**lt_of_tsub_lt_tsub_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_of_tsub_lt_tsub_right (h : a - c < b - c) : a < b
参数：h : a - c < b - c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_imp_lt_of_le_imp_le`：lt_imp_lt_of_le_imp_le {β} [LinearOrder α] [Preo
rder β] {a b : α} {c d : β} (H : a <= b -> c <= d) (h : d < c) : b < a
· 使用定理 `tsub_le_tsub_right`：tsub_le_tsub_right (h : a <= b) (c : α) : a - c <= b
 - c

--- 原说明 ---
See `lt_of_tsub_lt_tsub_right_of_le` for a weaker statement in a partial order.
-/
theorem lt_of_tsub_lt_tsub_right (h : a - c < b - c) : a < b :=
  lt_imp_lt_of_le_imp_le (fun h => tsub_le_tsub_right h c) h

/-- See `lt_tsub_iff_right_of_le` for a weaker statement in a partial order. -/
/-
**lt_tsub_iff_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_tsub_iff_right : a < b - c ↔ a + c < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le`：lt_iff_lt_of_le_iff_le {β} [LinearOrder α] [Line
arOrder β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) : b < a ↔ d < c
· 使用定理 `tsub_le_iff_right`：tsub_le_iff_right [LE α] [Add α] [Sub α] [OrderedSub 
α] {a b c : α} : a - b <= c ↔ a <= c + b

--- 原说明 ---
See `lt_tsub_iff_right_of_le` for a weaker statement in a partial order.
-/
theorem lt_tsub_iff_right : a < b - c ↔ a + c < b :=
  lt_iff_lt_of_le_iff_le tsub_le_iff_right

/-- See `lt_tsub_iff_left_of_le` for a weaker statement in a partial order. -/
/-
**lt_tsub_iff_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_tsub_iff_left : a < b - c ↔ c + a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le`：lt_iff_lt_of_le_iff_le {β} [LinearOrder α] [Line
arOrder β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) : b < a ↔ d < c
· 使用定理 `tsub_le_iff_left`：tsub_le_iff_left : a - b <= c ↔ a <= b + c

--- 原说明 ---
See `lt_tsub_iff_left_of_le` for a weaker statement in a partial order.
-/
theorem lt_tsub_iff_left : a < b - c ↔ c + a < b :=
  lt_iff_lt_of_le_iff_le tsub_le_iff_left
/-
**lt_tsub_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_tsub_comm : a < b - c ↔ c < b - a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `lt_tsub_iff_left`：lt_tsub_iff_left : a < b - c ↔ c + a < b
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `lt_tsub_iff_right`：lt_tsub_iff_right : a < b - c ↔ a + c < b
-/
theorem lt_tsub_comm : a < b - c ↔ c < b - a :=
  lt_tsub_iff_left.trans lt_tsub_iff_right.symm

section Cov

variable [AddLeftMono α]

/-- See `lt_of_tsub_lt_tsub_left_of_le` for a weaker statement in a partial order. -/
/-
**lt_of_tsub_lt_tsub_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_of_tsub_lt_tsub_left (h : a - b < a - c) : c < b
参数：h : a - b < a - c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_imp_lt_of_le_imp_le`：lt_imp_lt_of_le_imp_le {β} [LinearOrder α] [Preo
rder β] {a b : α} {c d : β} (H : a <= b -> c <= d) (h : d < c) : b < a
· 使用定理 `tsub_le_tsub_left`：tsub_le_tsub_left (h : a <= b) (c : α) : c - b <= c -
 a

--- 原说明 ---
See `lt_of_tsub_lt_tsub_left_of_le` for a weaker statement in a partial order.
-/
theorem lt_of_tsub_lt_tsub_left (h : a - b < a - c) : c < b :=
  lt_imp_lt_of_le_imp_le (fun h => tsub_le_tsub_left h a) h

end Cov

end LinearOrder

section OrderedAddCommMonoid

variable [PartialOrder α] [AddCommMonoid α] [Sub α] [OrderedSub α]

@[simp]
/-
**tsub_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_zero (a : α) : a - 0 = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.tsub_eq_of_eq_add`：∀ {α : Type u_1} [inst : PartialOrde
r α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b c : α}, 
  AddLECancellable b → a…
· 使用定理 `addLECancellable_zero`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 
: LE α], AddLECancellable 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem tsub_zero (a : α) : a - 0 = a :=
  AddLECancellable.tsub_eq_of_eq_add addLECancellable_zero (add_zero _).symm

end OrderedAddCommMonoid

