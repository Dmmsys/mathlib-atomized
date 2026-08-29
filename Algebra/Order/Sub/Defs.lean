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

/--
Definition of `OrderedSub` / `OrderedSub` 的定义

English:
class OrderedSub
  parameters: (α : Type*) [LE α] [Add α] [Sub α]
  axioms and operations (1):
    - tsub_le_iff_right : forall a b c : α, a - b <= c ↔ a <= c + b

中文:
类 OrderedSub
  参数: (α : 类型) [LE α] [Add α] [Sub α]
  公理与运算 (1 个):
    - tsub_le_iff_right : 对任意 a b c : α, a - b <= c ↔ a <= c + b
-/
class OrderedSub (α : Type*) [LE α] [Add α] [Sub α] : Prop where
  /-- `a - b` provides a lower bound on `c` such that `a ≤ c + b`. -/
  tsub_le_iff_right : forall a b c : α, a - b <= c ↔ a <= c + b

section Add

@[simp]
/--
theorem `tsub_le_iff_right` / 定理 `tsub_le_iff_right`

English:
theorem tsub_le_iff_right
  given: [LE α] [Add α] [Sub α] [OrderedSub α] {a b c : α}
  proof: OrderedSub.tsub_le_iff_right a b c

中文:
定理 tsub_le_iff_right
  条件: [LE α] [Add α] [Sub α] [OrderedSub α] {a b c : α}
  证明: OrderedSub.tsub_le_iff_right a b c

Depends on / 依赖: OrderedSub, OrderedSub.tsub_le_iff_right, tsub_le_iff_right
-/
theorem tsub_le_iff_right [LE α] [Add α] [Sub α] [OrderedSub α] {a b c : α} :
    a - b <= c ↔ a <= c + b :=
  OrderedSub.tsub_le_iff_right a b c

variable [Preorder α] [Add α] [Sub α] [OrderedSub α] {a b : α}

/--
theorem `add_tsub_le_right` / 定理 `add_tsub_le_right`

English:
theorem add_tsub_le_right
  statement: a + b - b <= a
  proof: tsub_le_iff_right.mpr le_rfl

中文:
定理 add_tsub_le_right
  结论: a + b - b <= a
  证明: tsub_le_iff_right.mpr le_rfl

Depends on / 依赖: le_rfl, tsub_le_iff_right, tsub_le_iff_right.mpr
-/
theorem add_tsub_le_right : a + b - b <= a :=
  tsub_le_iff_right.mpr le_rfl

/--
theorem `le_tsub_add` / 定理 `le_tsub_add`

English:
theorem le_tsub_add
  statement: b <= b - a + a
  proof: tsub_le_iff_right.mp le_rfl

中文:
定理 le_tsub_add
  结论: b <= b - a + a
  证明: tsub_le_iff_right.mp le_rfl

Depends on / 依赖: le_rfl, tsub_le_iff_right, tsub_le_iff_right.mp
-/
theorem le_tsub_add : b <= b - a + a :=
  tsub_le_iff_right.mp le_rfl

end Add

/-! ### Preorder -/


section OrderedAddCommSemigroup

section Preorder

variable [Preorder α]

section AddCommSemigroup

variable [AddCommSemigroup α] [Sub α] [OrderedSub α] {a b c d : α}

-- TODO: Most results can be generalized to `[Add α] [IsAddCommutative α]`

/--
theorem `tsub_le_iff_left` / 定理 `tsub_le_iff_left`

English:
theorem tsub_le_iff_left
  statement: a - b <= c ↔ a <= b + c
  proof: by rw [tsub_le_iff_right, add_comm]

中文:
定理 tsub_le_iff_left
  结论: a - b <= c ↔ a <= b + c
  证明: by rw [tsub_le_iff_right, add_comm]

Depends on / 依赖: add_comm, tsub_le_iff_right
-/
theorem tsub_le_iff_left : a - b <= c ↔ a <= b + c := by rw [tsub_le_iff_right, add_comm]

/--
theorem `le_add_tsub` / 定理 `le_add_tsub`

English:
theorem le_add_tsub
  statement: a <= b + (a - b)
  proof: tsub_le_iff_left.mp le_rfl

中文:
定理 le_add_tsub
  结论: a <= b + (a - b)
  证明: tsub_le_iff_left.mp le_rfl

Depends on / 依赖: le_rfl, tsub_le_iff_left, tsub_le_iff_left.mp
-/
theorem le_add_tsub : a <= b + (a - b) :=
  tsub_le_iff_left.mp le_rfl

/--
theorem `add_tsub_le_left` / 定理 `add_tsub_le_left`

English:
theorem add_tsub_le_left
  statement: a + b - a <= b
  proof: tsub_le_iff_left.mpr le_rfl

中文:
定理 add_tsub_le_left
  结论: a + b - a <= b
  证明: tsub_le_iff_left.mpr le_rfl

Depends on / 依赖: le_rfl, tsub_le_iff_left, tsub_le_iff_left.mpr
-/
theorem add_tsub_le_left : a + b - a <= b :=
  tsub_le_iff_left.mpr le_rfl

/--
theorem `tsub_le_tsub_right` / 定理 `tsub_le_tsub_right`

English:
theorem tsub_le_tsub_right
  given: (h : a <= b) (c : α)
  statement: a - c <= b - c
  proof: tsub_le_iff_left.mpr h.trans le_add_tsub

中文:
定理 tsub_le_tsub_right
  条件: (h : a <= b) (c : α)
  结论: a - c <= b - c
  证明: tsub_le_iff_left.mpr h.trans le_add_tsub

Depends on / 依赖: h.trans, le_add_tsub, tsub_le_iff_left, tsub_le_iff_left.mpr
-/
theorem tsub_le_tsub_right (h : a <= b) (c : α) : a - c <= b - c :=
tsub_le_iff_left.mpr h.trans le_add_tsub

/--
theorem `tsub_le_iff_tsub_le` / 定理 `tsub_le_iff_tsub_le`

English:
theorem tsub_le_iff_tsub_le
  statement: a - b <= c ↔ a - c <= b
  proof: by rw [tsub_le_iff_left, tsub_le_iff_right]

中文:
定理 tsub_le_iff_tsub_le
  结论: a - b <= c ↔ a - c <= b
  证明: by rw [tsub_le_iff_left, tsub_le_iff_right]

Depends on / 依赖: tsub_le_iff_left, tsub_le_iff_right
-/
theorem tsub_le_iff_tsub_le : a - b <= c ↔ a - c <= b := by rw [tsub_le_iff_left, tsub_le_iff_right]

/--
theorem `tsub_tsub_le` / 定理 `tsub_tsub_le`

English:
theorem tsub_tsub_le
  statement: b - (b - a) <= a
  proof: tsub_le_iff_right.mpr le_add_tsub

中文:
定理 tsub_tsub_le
  结论: b - (b - a) <= a
  证明: tsub_le_iff_right.mpr le_add_tsub

Depends on / 依赖: le_add_tsub, tsub_le_iff_right, tsub_le_iff_right.mpr
-/
theorem tsub_tsub_le : b - (b - a) <= a :=
  tsub_le_iff_right.mpr le_add_tsub

section Cov

variable [AddLeftMono α]

/--
theorem `tsub_le_tsub_left` / 定理 `tsub_le_tsub_left`

English:
theorem tsub_le_tsub_left
  given: (h : a <= b) (c : α)
  statement: c - b <= c - a
  proof: by
  grw [tsub_le_iff_left, ← h, ← le_add_tsub]

中文:
定理 tsub_le_tsub_left
  条件: (h : a <= b) (c : α)
  结论: c - b <= c - a
  证明: by
  grw [tsub_le_iff_left, ← h, ← le_add_tsub]

Depends on / 依赖: le_add_tsub, tsub_le_iff_left
-/
theorem tsub_le_tsub_left (h : a <= b) (c : α) : c - b <= c - a := by
  grw [tsub_le_iff_left, ← h, ← le_add_tsub]

/--
theorem `tsub_le_tsub` / 定理 `tsub_le_tsub`

English:
theorem tsub_le_tsub
  given: (hab : a <= b) (hcd : c <= d)
  statement: a - d <= b - c
  proof: (tsub_le_tsub_right hab _).trans tsub_le_tsub_left hcd _

中文:
定理 tsub_le_tsub
  条件: (hab : a <= b) (hcd : c <= d)
  结论: a - d <= b - c
  证明: (tsub_le_tsub_right hab _).trans tsub_le_tsub_left hcd _
-/
@[gcongr] theorem tsub_le_tsub (hab : a <= b) (hcd : c <= d) : a - d <= b - c :=
(tsub_le_tsub_right hab _).trans tsub_le_tsub_left hcd _

/--
theorem `antitone_const_tsub` / 定理 `antitone_const_tsub`

English:
theorem antitone_const_tsub
  statement: Antitone fun x => c - x
  proof: fun _ _ hxy => tsub_le_tsub rfl.le hxy

中文:
定理 antitone_const_tsub
  结论: Antitone fun x => c - x
  证明: fun _ _ hxy => tsub_le_tsub rfl.le hxy

Depends on / 依赖: rfl.le, tsub_le_tsub
-/
theorem antitone_const_tsub : Antitone fun x => c - x := fun _ _ hxy => tsub_le_tsub rfl.le hxy

/--
theorem `add_tsub_le_assoc` / 定理 `add_tsub_le_assoc`

English:
theorem add_tsub_le_assoc
  statement: a + b - c <= a + (b - c)
  proof: by
  grw [tsub_le_iff_left, add_left_comm, ← le_add_tsub]

中文:
定理 add_tsub_le_assoc
  结论: a + b - c <= a + (b - c)
  证明: by
  grw [tsub_le_iff_left, add_left_comm, ← le_add_tsub]

Depends on / 依赖: add_left_comm, le_add_tsub, tsub_le_iff_left
-/
theorem add_tsub_le_assoc : a + b - c <= a + (b - c) := by
  grw [tsub_le_iff_left, add_left_comm, ← le_add_tsub]

/--
theorem `add_tsub_le_tsub_add` / 定理 `add_tsub_le_tsub_add`

English:
theorem add_tsub_le_tsub_add
  statement: a + b - c <= a - c + b
  proof: by
  rw [add_comm]; rw [add_comm _ b]
  exact add_tsub_le_assoc

中文:
定理 add_tsub_le_tsub_add
  结论: a + b - c <= a - c + b
  证明: by
  rw [add_comm]; rw [add_comm _ b]
  exact add_tsub_le_assoc

Depends on / 依赖: add_comm, add_tsub_le_assoc
-/
theorem add_tsub_le_tsub_add : a + b - c <= a - c + b := by
  rw [add_comm]; rw [add_comm _ b]
  exact add_tsub_le_assoc

/--
theorem `add_le_add_add_tsub` / 定理 `add_le_add_add_tsub`

English:
theorem add_le_add_add_tsub
  statement: a + b <= a + c + (b - c)
  proof: by grw [add_assoc, ← le_add_tsub]

中文:
定理 add_le_add_add_tsub
  结论: a + b <= a + c + (b - c)
  证明: by grw [add_assoc, ← le_add_tsub]

Depends on / 依赖: add_assoc, le_add_tsub
-/
theorem add_le_add_add_tsub : a + b <= a + c + (b - c) := by grw [add_assoc, ← le_add_tsub]

/--
theorem `le_tsub_add_add` / 定理 `le_tsub_add_add`

English:
theorem le_tsub_add_add
  statement: a + b <= a - c + (b + c)
  proof: by
  rw [add_comm a]; rw [add_comm (a - c)]
  exact add_le_add_add_tsub

中文:
定理 le_tsub_add_add
  结论: a + b <= a - c + (b + c)
  证明: by
  rw [add_comm a]; rw [add_comm (a - c)]
  exact add_le_add_add_tsub

Depends on / 依赖: add_comm, add_le_add_add_tsub
-/
theorem le_tsub_add_add : a + b <= a - c + (b + c) := by
  rw [add_comm a]; rw [add_comm (a - c)]
  exact add_le_add_add_tsub

/--
theorem `tsub_le_tsub_add_tsub` / 定理 `tsub_le_tsub_add_tsub`

English:
theorem tsub_le_tsub_add_tsub
  statement: a - c <= a - b + (b - c)
  proof: by
  grw [tsub_le_iff_left, ← add_assoc, add_right_comm, ← le_add_tsub, ← le_add_tsub]

中文:
定理 tsub_le_tsub_add_tsub
  结论: a - c <= a - b + (b - c)
  证明: by
  grw [tsub_le_iff_left, ← add_assoc, add_right_comm, ← le_add_tsub, ← le_add_tsub]

Depends on / 依赖: add_assoc, add_right_comm, le_add_tsub, tsub_le_iff_left
-/
theorem tsub_le_tsub_add_tsub : a - c <= a - b + (b - c) := by
  grw [tsub_le_iff_left, ← add_assoc, add_right_comm, ← le_add_tsub, ← le_add_tsub]

/--
theorem `tsub_tsub_tsub_le_tsub` / 定理 `tsub_tsub_tsub_le_tsub`

English:
theorem tsub_tsub_tsub_le_tsub
  statement: c - a - (c - b) <= b - a
  proof: by
  grw [tsub_le_iff_left, tsub_le_iff_left, add_left_comm, ← le_add_tsub, ← le_tsub_add]

中文:
定理 tsub_tsub_tsub_le_tsub
  结论: c - a - (c - b) <= b - a
  证明: by
  grw [tsub_le_iff_left, tsub_le_iff_left, add_left_comm, ← le_add_tsub, ← le_tsub_add]

Depends on / 依赖: add_left_comm, le_add_tsub, le_tsub_add, tsub_le_iff_left
-/
theorem tsub_tsub_tsub_le_tsub : c - a - (c - b) <= b - a := by
  grw [tsub_le_iff_left, tsub_le_iff_left, add_left_comm, ← le_add_tsub, ← le_tsub_add]

/--
theorem `tsub_tsub_le_tsub_add` / 定理 `tsub_tsub_le_tsub_add`

English:
theorem tsub_tsub_le_tsub_add
  given: {a b c : α}
  statement: a - (b - c) <= a - b + c
  proof: tsub_le_iff_right.2
    calc
      a <= a - b + b := le_tsub_add
      _ <= a - b + (c + (b - c)) := by grw [← le_add_tsub]
      _ = a - b + c + (b - c) := (add_assoc _ _ _).symm

中文:
定理 tsub_tsub_le_tsub_add
  条件: {a b c : α}
  结论: a - (b - c) <= a - b + c
  证明: tsub_le_iff_right.2
    calc
      a <= a - b + b := le_tsub_add
      _ <= a - b + (c + (b - c)) := by grw [← le_add_tsub]
      _ = a - b + c + (b - c) := (add_assoc _ _ _).symm

Depends on / 依赖: add_assoc, le_add_tsub, le_tsub_add, tsub_le_iff_right
-/
theorem tsub_tsub_le_tsub_add {a b c : α} : a - (b - c) <= a - b + c :=
tsub_le_iff_right.2
    calc
      a <= a - b + b := le_tsub_add
      _ <= a - b + (c + (b - c)) := by grw [← le_add_tsub]
      _ = a - b + c + (b - c) := (add_assoc _ _ _).symm

/--
theorem `add_tsub_add_le_tsub_add_tsub` / 定理 `add_tsub_add_le_tsub_add_tsub`

English:
theorem add_tsub_add_le_tsub_add_tsub
  statement: a + b - (c + d) <= a - c + (b - d)
  proof: by
  rw [add_comm c]; rw [tsub_le_iff_left]; rw [add_assoc]; rw [← tsub_le_iff_left]; rw [← tsub_le_iff_left]
  refine (tsub_le_tsub_right add_tsub_le_assoc c).trans ?_
  rw [add_comm a]; rw [add_comm (a - c)]
  exact add_tsub_le_assoc

中文:
定理 add_tsub_add_le_tsub_add_tsub
  结论: a + b - (c + d) <= a - c + (b - d)
  证明: by
  rw [add_comm c]; rw [tsub_le_iff_left]; rw [add_assoc]; rw [← tsub_le_iff_left]; rw [← tsub_le_iff_left]
  refine (tsub_le_tsub_right add_tsub_le_assoc c).trans ?_
  rw [add_comm a]; rw [add_comm (a - c)]
  exact add_tsub_le_assoc

Depends on / 依赖: add_assoc, add_comm, add_tsub_le_assoc, tsub_le_iff_left, tsub_le_tsub_right
-/
theorem add_tsub_add_le_tsub_add_tsub : a + b - (c + d) <= a - c + (b - d) := by
  rw [add_comm c]; rw [tsub_le_iff_left]; rw [add_assoc]; rw [← tsub_le_iff_left]; rw [← tsub_le_iff_left]
  refine (tsub_le_tsub_right add_tsub_le_assoc c).trans ?_
  rw [add_comm a]; rw [add_comm (a - c)]
  exact add_tsub_le_assoc

/--
theorem `add_tsub_add_le_tsub_left` / 定理 `add_tsub_add_le_tsub_left`

English:
theorem add_tsub_add_le_tsub_left
  statement: a + b - (a + c) <= b - c
  proof: by
  grw [tsub_le_iff_left, add_assoc, ← le_add_tsub]

中文:
定理 add_tsub_add_le_tsub_left
  结论: a + b - (a + c) <= b - c
  证明: by
  grw [tsub_le_iff_left, add_assoc, ← le_add_tsub]

Depends on / 依赖: add_assoc, le_add_tsub, tsub_le_iff_left
-/
theorem add_tsub_add_le_tsub_left : a + b - (a + c) <= b - c := by
  grw [tsub_le_iff_left, add_assoc, ← le_add_tsub]

/--
theorem `add_tsub_add_le_tsub_right` / 定理 `add_tsub_add_le_tsub_right`

English:
theorem add_tsub_add_le_tsub_right
  statement: a + c - (b + c) <= a - b
  proof: by
  grw [tsub_le_iff_left, add_right_comm, ← le_add_tsub]

中文:
定理 add_tsub_add_le_tsub_right
  结论: a + c - (b + c) <= a - b
  证明: by
  grw [tsub_le_iff_left, add_right_comm, ← le_add_tsub]

Depends on / 依赖: add_right_comm, le_add_tsub, tsub_le_iff_left
-/
theorem add_tsub_add_le_tsub_right : a + c - (b + c) <= a - b := by
  grw [tsub_le_iff_left, add_right_comm, ← le_add_tsub]

end Cov

/-! #### Lemmas that assume that an element is `AddLECancellable` -/


namespace AddLECancellable

/--
theorem `le_add_tsub_swap` / 定理 `le_add_tsub_swap`

English:
theorem le_add_tsub_swap
  given: (hb : AddLECancellable b)
  statement: a <= b + a - b
  proof: hb le_add_tsub

中文:
定理 le_add_tsub_swap
  条件: (hb : AddLECancellable b)
  结论: a <= b + a - b
  证明: hb le_add_tsub
-/
protected theorem le_add_tsub_swap (hb : AddLECancellable b) : a <= b + a - b :=
  hb le_add_tsub

/--
theorem `le_add_tsub` / 定理 `le_add_tsub`

English:
theorem le_add_tsub
  given: (hb : AddLECancellable b)
  statement: a <= a + b - b
  proof: by
  rw [add_comm]
  exact hb.le_add_tsub_swap

中文:
定理 le_add_tsub
  条件: (hb : AddLECancellable b)
  结论: a <= a + b - b
  证明: by
  rw [add_comm]
  exact hb.le_add_tsub_swap
-/
protected theorem le_add_tsub (hb : AddLECancellable b) : a <= a + b - b := by
  rw [add_comm]
  exact hb.le_add_tsub_swap

/--
theorem `le_tsub_of_add_le_left` / 定理 `le_tsub_of_add_le_left`

English:
theorem le_tsub_of_add_le_left
  given: (ha : AddLECancellable a) (h : a + b <= c)
  statement: b <= c - a
  proof: ha h.trans le_add_tsub

中文:
定理 le_tsub_of_add_le_left
  条件: (ha : AddLECancellable a) (h : a + b <= c)
  结论: b <= c - a
  证明: ha h.trans le_add_tsub
-/
protected theorem le_tsub_of_add_le_left (ha : AddLECancellable a) (h : a + b <= c) : b <= c - a :=
ha h.trans le_add_tsub

/--
theorem `le_tsub_of_add_le_right` / 定理 `le_tsub_of_add_le_right`

English:
theorem le_tsub_of_add_le_right
  given: (hb : AddLECancellable b) (h : a + b <= c)
  statement: a <= c - b
  proof: hb.le_tsub_of_add_le_left by rwa [add_comm]

中文:
定理 le_tsub_of_add_le_right
  条件: (hb : AddLECancellable b) (h : a + b <= c)
  结论: a <= c - b
  证明: hb.le_tsub_of_add_le_left by rwa [add_comm]
-/
protected theorem le_tsub_of_add_le_right (hb : AddLECancellable b) (h : a + b <= c) : a <= c - b :=
hb.le_tsub_of_add_le_left by rwa [add_comm]

end AddLECancellable

/-! ### Lemmas where addition is order-reflecting -/


section Contra

variable [AddLeftReflectLE α]

/--
theorem `le_add_tsub_swap` / 定理 `le_add_tsub_swap`

English:
theorem le_add_tsub_swap
  statement: a <= b + a - b
  proof: Contravariant.AddLECancellable.le_add_tsub_swap

中文:
定理 le_add_tsub_swap
  结论: a <= b + a - b
  证明: Contravariant.AddLECancellable.le_add_tsub_swap

Depends on / 依赖: AddLECancellable, Contravariant, Contravariant.AddLECancellable.le_add_tsub_swap, le_add_tsub_swap
-/
theorem le_add_tsub_swap : a <= b + a - b :=
  Contravariant.AddLECancellable.le_add_tsub_swap

/--
theorem `le_add_tsub'` / 定理 `le_add_tsub'`

English:
theorem le_add_tsub'
  statement: a <= a + b - b
  proof: Contravariant.AddLECancellable.le_add_tsub

中文:
定理 le_add_tsub'
  结论: a <= a + b - b
  证明: Contravariant.AddLECancellable.le_add_tsub

Depends on / 依赖: AddLECancellable, Contravariant, Contravariant.AddLECancellable.le_add_tsub, le_add_tsub
-/
theorem le_add_tsub' : a <= a + b - b :=
  Contravariant.AddLECancellable.le_add_tsub

/--
theorem `le_tsub_of_add_le_left` / 定理 `le_tsub_of_add_le_left`

English:
theorem le_tsub_of_add_le_left
  given: (h : a + b <= c)
  statement: b <= c - a
  proof: Contravariant.AddLECancellable.le_tsub_of_add_le_left h

中文:
定理 le_tsub_of_add_le_left
  条件: (h : a + b <= c)
  结论: b <= c - a
  证明: Contravariant.AddLECancellable.le_tsub_of_add_le_left h

Depends on / 依赖: AddLECancellable, Contravariant, Contravariant.AddLECancellable.le_tsub_of_add_le_left, le_tsub_of_add_le_left
-/
theorem le_tsub_of_add_le_left (h : a + b <= c) : b <= c - a :=
  Contravariant.AddLECancellable.le_tsub_of_add_le_left h

/--
theorem `le_tsub_of_add_le_right` / 定理 `le_tsub_of_add_le_right`

English:
theorem le_tsub_of_add_le_right
  given: (h : a + b <= c)
  statement: a <= c - b
  proof: Contravariant.AddLECancellable.le_tsub_of_add_le_right h

中文:
定理 le_tsub_of_add_le_right
  条件: (h : a + b <= c)
  结论: a <= c - b
  证明: Contravariant.AddLECancellable.le_tsub_of_add_le_right h

Depends on / 依赖: AddLECancellable, Contravariant, Contravariant.AddLECancellable.le_tsub_of_add_le_right, le_tsub_of_add_le_right
-/
theorem le_tsub_of_add_le_right (h : a + b <= c) : a <= c - b :=
  Contravariant.AddLECancellable.le_tsub_of_add_le_right h

end Contra

end AddCommSemigroup

variable [AddCommMonoid α] [Sub α] [OrderedSub α] {a b : α}

/--
theorem `tsub_nonpos` / 定理 `tsub_nonpos`

English:
theorem tsub_nonpos
  statement: a - b <= 0 ↔ a <= b
  proof: by rw [tsub_le_iff_left, add_zero]

alias ⟨_, tsub_nonpos_of_le⟩ := tsub_nonpos

中文:
定理 tsub_nonpos
  结论: a - b <= 0 ↔ a <= b
  证明: by rw [tsub_le_iff_left, add_zero]

alias ⟨_, tsub_nonpos_of_le⟩ := tsub_nonpos

Depends on / 依赖: add_zero, tsub_le_iff_left
-/
theorem tsub_nonpos : a - b <= 0 ↔ a <= b := by rw [tsub_le_iff_left, add_zero]

alias ⟨_, tsub_nonpos_of_le⟩ := tsub_nonpos

end Preorder

/-! ### Partial order -/


variable [PartialOrder α] [AddCommSemigroup α] [Sub α] [OrderedSub α] {a b c d : α}

/--
theorem `tsub_tsub` / 定理 `tsub_tsub`

English:
theorem tsub_tsub
  given: (b a c : α)
  statement: b - a - c = b - (a + c)
  proof: by
  apply le_antisymm
  · rw [tsub_le_iff_left, tsub_le_iff_left, ← add_assoc, ← tsub_le_iff_left]
  · rw [tsub_le_iff_left, add_assoc, ← tsub_le_iff_left, ← tsub_le_iff_left]

中文:
定理 tsub_tsub
  条件: (b a c : α)
  结论: b - a - c = b - (a + c)
  证明: by
  apply le_antisymm
  · rw [tsub_le_iff_left, tsub_le_iff_left, ← add_assoc, ← tsub_le_iff_left]
  · rw [tsub_le_iff_left, add_assoc, ← tsub_le_iff_left, ← tsub_le_iff_left]

Depends on / 依赖: add_assoc, le_antisymm, tsub_le_iff_left
-/
theorem tsub_tsub (b a c : α) : b - a - c = b - (a + c) := by
  apply le_antisymm
  · rw [tsub_le_iff_left, tsub_le_iff_left, ← add_assoc, ← tsub_le_iff_left]
  · rw [tsub_le_iff_left, add_assoc, ← tsub_le_iff_left, ← tsub_le_iff_left]

/--
theorem `tsub_add_eq_tsub_tsub` / 定理 `tsub_add_eq_tsub_tsub`

English:
theorem tsub_add_eq_tsub_tsub
  given: (a b c : α)
  statement: a - (b + c) = a - b - c
  proof: (tsub_tsub _ _ _).symm

中文:
定理 tsub_add_eq_tsub_tsub
  条件: (a b c : α)
  结论: a - (b + c) = a - b - c
  证明: (tsub_tsub _ _ _).symm

Depends on / 依赖: tsub_tsub
-/
theorem tsub_add_eq_tsub_tsub (a b c : α) : a - (b + c) = a - b - c :=
  (tsub_tsub _ _ _).symm

/--
theorem `tsub_add_eq_tsub_tsub_swap` / 定理 `tsub_add_eq_tsub_tsub_swap`

English:
theorem tsub_add_eq_tsub_tsub_swap
  given: (a b c : α)
  statement: a - (b + c) = a - c - b
  proof: by
  rw [add_comm]
  apply tsub_add_eq_tsub_tsub

中文:
定理 tsub_add_eq_tsub_tsub_swap
  条件: (a b c : α)
  结论: a - (b + c) = a - c - b
  证明: by
  rw [add_comm]
  apply tsub_add_eq_tsub_tsub

Depends on / 依赖: add_comm, tsub_add_eq_tsub_tsub
-/
theorem tsub_add_eq_tsub_tsub_swap (a b c : α) : a - (b + c) = a - c - b := by
  rw [add_comm]
  apply tsub_add_eq_tsub_tsub

/--
theorem `tsub_right_comm` / 定理 `tsub_right_comm`

English:
theorem tsub_right_comm
  statement: a - b - c = a - c - b
  proof: by
  rw [← tsub_add_eq_tsub_tsub]; rw [tsub_add_eq_tsub_tsub_swap]

中文:
定理 tsub_right_comm
  结论: a - b - c = a - c - b
  证明: by
  rw [← tsub_add_eq_tsub_tsub]; rw [tsub_add_eq_tsub_tsub_swap]

Depends on / 依赖: tsub_add_eq_tsub_tsub, tsub_add_eq_tsub_tsub_swap
-/
theorem tsub_right_comm : a - b - c = a - c - b := by
  rw [← tsub_add_eq_tsub_tsub]; rw [tsub_add_eq_tsub_tsub_swap]

/-! ### Lemmas that assume that an element is `AddLECancellable`. -/


namespace AddLECancellable

/--
theorem `tsub_eq_of_eq_add` / 定理 `tsub_eq_of_eq_add`

English:
theorem tsub_eq_of_eq_add
  given: (hb : AddLECancellable b) (h : a = c + b)
  statement: a - b = c
  proof: le_antisymm (tsub_le_iff_right.mpr h.le) by
    rw [h]
    exact hb.le_add_tsub

中文:
定理 tsub_eq_of_eq_add
  条件: (hb : AddLECancellable b) (h : a = c + b)
  结论: a - b = c
  证明: le_antisymm (tsub_le_iff_right.mpr h.le) by
    rw [h]
    exact hb.le_add_tsub
-/
protected theorem tsub_eq_of_eq_add (hb : AddLECancellable b) (h : a = c + b) : a - b = c :=
le_antisymm (tsub_le_iff_right.mpr h.le) by
    rw [h]
    exact hb.le_add_tsub

/--
lemma `tsub_eq_of_eq_add'` / 引理 `tsub_eq_of_eq_add'`

English:
lemma tsub_eq_of_eq_add'
  statement: [AddLeftMono α] (ha : AddLECancellable a)
  proof: (h ▸ ha).of_add_right.tsub_eq_of_eq_add h

中文:
引理 tsub_eq_of_eq_add'
  结论: [AddLeftMono α] (ha : AddLECancellable a)
  证明: (h ▸ ha).of_add_right.tsub_eq_of_eq_add h
-/
protected lemma tsub_eq_of_eq_add' [AddLeftMono α] (ha : AddLECancellable a)
    (h : a = c + b) : a - b = c := (h ▸ ha).of_add_right.tsub_eq_of_eq_add h

/--
theorem `eq_tsub_of_add_eq` / 定理 `eq_tsub_of_add_eq`

English:
theorem eq_tsub_of_add_eq
  given: (hc : AddLECancellable c) (h : a + c = b)
  statement: a = b - c
  proof: (hc.tsub_eq_of_eq_add h.symm).symm

中文:
定理 eq_tsub_of_add_eq
  条件: (hc : AddLECancellable c) (h : a + c = b)
  结论: a = b - c
  证明: (hc.tsub_eq_of_eq_add h.symm).symm
-/
protected theorem eq_tsub_of_add_eq (hc : AddLECancellable c) (h : a + c = b) : a = b - c :=
  (hc.tsub_eq_of_eq_add h.symm).symm

/--
lemma `eq_tsub_of_add_eq'` / 引理 `eq_tsub_of_add_eq'`

English:
lemma eq_tsub_of_add_eq'
  statement: [AddLeftMono α] (hb : AddLECancellable b)
  proof: (hb.tsub_eq_of_eq_add' h.symm).symm

中文:
引理 eq_tsub_of_add_eq'
  结论: [AddLeftMono α] (hb : AddLECancellable b)
  证明: (hb.tsub_eq_of_eq_add' h.symm).symm
-/
protected lemma eq_tsub_of_add_eq' [AddLeftMono α] (hb : AddLECancellable b)
    (h : a + c = b) : a = b - c := (hb.tsub_eq_of_eq_add' h.symm).symm

/--
theorem `tsub_eq_of_eq_add_rev` / 定理 `tsub_eq_of_eq_add_rev`

English:
theorem tsub_eq_of_eq_add_rev
  given: (hb : AddLECancellable b) (h : a = b + c)
  statement: a - b = c
  proof: hb.tsub_eq_of_eq_add by rw [add_comm, h]

中文:
定理 tsub_eq_of_eq_add_rev
  条件: (hb : AddLECancellable b) (h : a = b + c)
  结论: a - b = c
  证明: hb.tsub_eq_of_eq_add by rw [add_comm, h]
-/
protected theorem tsub_eq_of_eq_add_rev (hb : AddLECancellable b) (h : a = b + c) : a - b = c :=
hb.tsub_eq_of_eq_add by rw [add_comm, h]

/--
lemma `tsub_eq_of_eq_add_rev'` / 引理 `tsub_eq_of_eq_add_rev'`

English:
lemma tsub_eq_of_eq_add_rev'
  statement: [AddLeftMono α]
  proof: ha.tsub_eq_of_eq_add' by rw [add_comm, h]

@[simp]

中文:
引理 tsub_eq_of_eq_add_rev'
  结论: [AddLeftMono α]
  证明: ha.tsub_eq_of_eq_add' by rw [add_comm, h]

@[simp]
-/
protected lemma tsub_eq_of_eq_add_rev' [AddLeftMono α]
    (ha : AddLECancellable a) (h : a = b + c) : a - b = c :=
ha.tsub_eq_of_eq_add' by rw [add_comm, h]

@[simp]
/--
theorem `add_tsub_cancel_right` / 定理 `add_tsub_cancel_right`

English:
theorem add_tsub_cancel_right
  given: (hb : AddLECancellable b)
  statement: a + b - b = a
  proof: hb.tsub_eq_of_eq_add by rw [add_comm]

@[simp]

中文:
定理 add_tsub_cancel_right
  条件: (hb : AddLECancellable b)
  结论: a + b - b = a
  证明: hb.tsub_eq_of_eq_add by rw [add_comm]

@[simp]
-/
protected theorem add_tsub_cancel_right (hb : AddLECancellable b) : a + b - b = a :=
hb.tsub_eq_of_eq_add by rw [add_comm]

@[simp]
/--
theorem `add_tsub_cancel_left` / 定理 `add_tsub_cancel_left`

English:
theorem add_tsub_cancel_left
  given: (ha : AddLECancellable a)
  statement: a + b - a = b
  proof: ha.tsub_eq_of_eq_add add_comm a b

中文:
定理 add_tsub_cancel_left
  条件: (ha : AddLECancellable a)
  结论: a + b - a = b
  证明: ha.tsub_eq_of_eq_add add_comm a b
-/
protected theorem add_tsub_cancel_left (ha : AddLECancellable a) : a + b - a = b :=
ha.tsub_eq_of_eq_add add_comm a b

/--
theorem `lt_add_of_tsub_lt_left` / 定理 `lt_add_of_tsub_lt_left`

English:
theorem lt_add_of_tsub_lt_left
  given: (hb : AddLECancellable b) (h : a - b < c)
  statement: a < b + c
  proof: by
  rw [lt_iff_le_and_ne]; rw [← tsub_le_iff_left]
  refine ⟨h.le, ?_⟩
  rintro rfl
  simp [hb] at h

中文:
定理 lt_add_of_tsub_lt_left
  条件: (hb : AddLECancellable b) (h : a - b < c)
  结论: a < b + c
  证明: by
  rw [lt_iff_le_and_ne]; rw [← tsub_le_iff_left]
  refine ⟨h.le, ?_⟩
  rintro rfl
  simp [hb] at h
-/
protected theorem lt_add_of_tsub_lt_left (hb : AddLECancellable b) (h : a - b < c) : a < b + c := by
  rw [lt_iff_le_and_ne]; rw [← tsub_le_iff_left]
  refine ⟨h.le, ?_⟩
  rintro rfl
  simp [hb] at h

/--
theorem `lt_add_of_tsub_lt_right` / 定理 `lt_add_of_tsub_lt_right`

English:
theorem lt_add_of_tsub_lt_right
  given: (hc : AddLECancellable c) (h : a - c < b)
  proof: by
  rw [lt_iff_le_and_ne]; rw [← tsub_le_iff_right]
  refine ⟨h.le, ?_⟩
  rintro rfl
  simp [hc] at h

中文:
定理 lt_add_of_tsub_lt_right
  条件: (hc : AddLECancellable c) (h : a - c < b)
  证明: by
  rw [lt_iff_le_and_ne]; rw [← tsub_le_iff_right]
  refine ⟨h.le, ?_⟩
  rintro rfl
  simp [hc] at h
-/
protected theorem lt_add_of_tsub_lt_right (hc : AddLECancellable c) (h : a - c < b) :
    a < b + c := by
  rw [lt_iff_le_and_ne]; rw [← tsub_le_iff_right]
  refine ⟨h.le, ?_⟩
  rintro rfl
  simp [hc] at h

/--
theorem `lt_tsub_of_add_lt_right` / 定理 `lt_tsub_of_add_lt_right`

English:
theorem lt_tsub_of_add_lt_right
  given: (hc : AddLECancellable c) (h : a + c < b)
  statement: a < b - c
  proof: (hc.le_tsub_of_add_le_right h.le).lt_of_ne by
    rintro rfl
    exact h.not_ge le_tsub_add

中文:
定理 lt_tsub_of_add_lt_right
  条件: (hc : AddLECancellable c) (h : a + c < b)
  结论: a < b - c
  证明: (hc.le_tsub_of_add_le_right h.le).lt_of_ne by
    rintro rfl
    exact h.not_ge le_tsub_add
-/
protected theorem lt_tsub_of_add_lt_right (hc : AddLECancellable c) (h : a + c < b) : a < b - c :=
(hc.le_tsub_of_add_le_right h.le).lt_of_ne by
    rintro rfl
    exact h.not_ge le_tsub_add

/--
theorem `lt_tsub_of_add_lt_left` / 定理 `lt_tsub_of_add_lt_left`

English:
theorem lt_tsub_of_add_lt_left
  given: (ha : AddLECancellable a) (h : a + c < b)
  statement: c < b - a
  proof: ha.lt_tsub_of_add_lt_right by rwa [add_comm]

中文:
定理 lt_tsub_of_add_lt_left
  条件: (ha : AddLECancellable a) (h : a + c < b)
  结论: c < b - a
  证明: ha.lt_tsub_of_add_lt_right by rwa [add_comm]
-/
protected theorem lt_tsub_of_add_lt_left (ha : AddLECancellable a) (h : a + c < b) : c < b - a :=
ha.lt_tsub_of_add_lt_right by rwa [add_comm]

end AddLECancellable

/-! #### Lemmas where addition is order-reflecting. -/


section Contra

variable [AddLeftReflectLE α]

/--
theorem `tsub_eq_of_eq_add` / 定理 `tsub_eq_of_eq_add`

English:
theorem tsub_eq_of_eq_add
  given: (h : a = c + b)
  statement: a - b = c
  proof: Contravariant.AddLECancellable.tsub_eq_of_eq_add h

中文:
定理 tsub_eq_of_eq_add
  条件: (h : a = c + b)
  结论: a - b = c
  证明: Contravariant.AddLECancellable.tsub_eq_of_eq_add h

Depends on / 依赖: AddLECancellable, Contravariant, Contravariant.AddLECancellable.tsub_eq_of_eq_add, tsub_eq_of_eq_add
-/
theorem tsub_eq_of_eq_add (h : a = c + b) : a - b = c :=
  Contravariant.AddLECancellable.tsub_eq_of_eq_add h

/--
theorem `eq_tsub_of_add_eq` / 定理 `eq_tsub_of_add_eq`

English:
theorem eq_tsub_of_add_eq
  given: (h : a + c = b)
  statement: a = b - c
  proof: Contravariant.AddLECancellable.eq_tsub_of_add_eq h

中文:
定理 eq_tsub_of_add_eq
  条件: (h : a + c = b)
  结论: a = b - c
  证明: Contravariant.AddLECancellable.eq_tsub_of_add_eq h

Depends on / 依赖: AddLECancellable, Contravariant, Contravariant.AddLECancellable.eq_tsub_of_add_eq, eq_tsub_of_add_eq
-/
theorem eq_tsub_of_add_eq (h : a + c = b) : a = b - c :=
  Contravariant.AddLECancellable.eq_tsub_of_add_eq h

/--
theorem `tsub_eq_of_eq_add_rev` / 定理 `tsub_eq_of_eq_add_rev`

English:
theorem tsub_eq_of_eq_add_rev
  given: (h : a = b + c)
  statement: a - b = c
  proof: Contravariant.AddLECancellable.tsub_eq_of_eq_add_rev h

@[simp]

中文:
定理 tsub_eq_of_eq_add_rev
  条件: (h : a = b + c)
  结论: a - b = c
  证明: Contravariant.AddLECancellable.tsub_eq_of_eq_add_rev h

@[simp]

Depends on / 依赖: AddLECancellable, Contravariant, Contravariant.AddLECancellable.tsub_eq_of_eq_add_rev, tsub_eq_of_eq_add_rev
-/
theorem tsub_eq_of_eq_add_rev (h : a = b + c) : a - b = c :=
  Contravariant.AddLECancellable.tsub_eq_of_eq_add_rev h

@[simp]
/--
theorem `add_tsub_cancel_right` / 定理 `add_tsub_cancel_right`

English:
theorem add_tsub_cancel_right
  given: (a b : α)
  statement: a + b - b = a
  proof: Contravariant.AddLECancellable.add_tsub_cancel_right

@[simp]

中文:
定理 add_tsub_cancel_right
  条件: (a b : α)
  结论: a + b - b = a
  证明: Contravariant.AddLECancellable.add_tsub_cancel_right

@[simp]

Depends on / 依赖: AddLECancellable, Contravariant, Contravariant.AddLECancellable.add_tsub_cancel_right, add_tsub_cancel_right
-/
theorem add_tsub_cancel_right (a b : α) : a + b - b = a :=
  Contravariant.AddLECancellable.add_tsub_cancel_right

@[simp]
/--
theorem `add_tsub_cancel_left` / 定理 `add_tsub_cancel_left`

English:
theorem add_tsub_cancel_left
  given: (a b : α)
  statement: a + b - a = b
  proof: Contravariant.AddLECancellable.add_tsub_cancel_left

中文:
定理 add_tsub_cancel_left
  条件: (a b : α)
  结论: a + b - a = b
  证明: Contravariant.AddLECancellable.add_tsub_cancel_left

Depends on / 依赖: AddLECancellable, Contravariant, Contravariant.AddLECancellable.add_tsub_cancel_left, add_tsub_cancel_left
-/
theorem add_tsub_cancel_left (a b : α) : a + b - a = b :=
  Contravariant.AddLECancellable.add_tsub_cancel_left

/--
theorem `tsub_eq_tsub_of_add_eq_add` / 定理 `tsub_eq_tsub_of_add_eq_add`

English:
theorem tsub_eq_tsub_of_add_eq_add
  given: (h : a + d = c + b)
  statement: a - b = c - d
  proof: by
  calc a - b = a + d - d - b := by rw [add_tsub_cancel_right]
           _ = c + b - b - d := by rw [h, tsub_right_comm]
           _ = c - d := by rw [add_tsub_cancel_right]

中文:
定理 tsub_eq_tsub_of_add_eq_add
  条件: (h : a + d = c + b)
  结论: a - b = c - d
  证明: by
  calc a - b = a + d - d - b := by rw [add_tsub_cancel_right]
           _ = c + b - b - d := by rw [h, tsub_right_comm]
           _ = c - d := by rw [add_tsub_cancel_right]

Depends on / 依赖: add_tsub_cancel_right, tsub_right_comm
-/
theorem tsub_eq_tsub_of_add_eq_add (h : a + d = c + b) : a - b = c - d := by
  calc a - b = a + d - d - b := by rw [add_tsub_cancel_right]
           _ = c + b - b - d := by rw [h, tsub_right_comm]
           _ = c - d := by rw [add_tsub_cancel_right]

/--
theorem `lt_add_of_tsub_lt_left` / 定理 `lt_add_of_tsub_lt_left`

English:
theorem lt_add_of_tsub_lt_left
  given: (h : a - b < c)
  statement: a < b + c
  proof: Contravariant.AddLECancellable.lt_add_of_tsub_lt_left h

中文:
定理 lt_add_of_tsub_lt_left
  条件: (h : a - b < c)
  结论: a < b + c
  证明: Contravariant.AddLECancellable.lt_add_of_tsub_lt_left h

Depends on / 依赖: AddLECancellable, Contravariant, Contravariant.AddLECancellable.lt_add_of_tsub_lt_left, lt_add_of_tsub_lt_left
-/
theorem lt_add_of_tsub_lt_left (h : a - b < c) : a < b + c :=
  Contravariant.AddLECancellable.lt_add_of_tsub_lt_left h

/--
theorem `lt_add_of_tsub_lt_right` / 定理 `lt_add_of_tsub_lt_right`

English:
theorem lt_add_of_tsub_lt_right
  given: (h : a - c < b)
  statement: a < b + c
  proof: Contravariant.AddLECancellable.lt_add_of_tsub_lt_right h

中文:
定理 lt_add_of_tsub_lt_right
  条件: (h : a - c < b)
  结论: a < b + c
  证明: Contravariant.AddLECancellable.lt_add_of_tsub_lt_right h

Depends on / 依赖: AddLECancellable, Contravariant, Contravariant.AddLECancellable.lt_add_of_tsub_lt_right, lt_add_of_tsub_lt_right
-/
theorem lt_add_of_tsub_lt_right (h : a - c < b) : a < b + c :=
  Contravariant.AddLECancellable.lt_add_of_tsub_lt_right h

/--
theorem `lt_tsub_of_add_lt_left` / 定理 `lt_tsub_of_add_lt_left`

English:
theorem lt_tsub_of_add_lt_left
  statement: a + c < b -> c < b - a
  proof: Contravariant.AddLECancellable.lt_tsub_of_add_lt_left

中文:
定理 lt_tsub_of_add_lt_left
  结论: a + c < b -> c < b - a
  证明: Contravariant.AddLECancellable.lt_tsub_of_add_lt_left

Depends on / 依赖: AddLECancellable, Contravariant, Contravariant.AddLECancellable.lt_tsub_of_add_lt_left, lt_tsub_of_add_lt_left
-/
theorem lt_tsub_of_add_lt_left : a + c < b -> c < b - a :=
  Contravariant.AddLECancellable.lt_tsub_of_add_lt_left

/--
theorem `lt_tsub_of_add_lt_right` / 定理 `lt_tsub_of_add_lt_right`

English:
theorem lt_tsub_of_add_lt_right
  statement: a + c < b -> a < b - c
  proof: Contravariant.AddLECancellable.lt_tsub_of_add_lt_right

中文:
定理 lt_tsub_of_add_lt_right
  结论: a + c < b -> a < b - c
  证明: Contravariant.AddLECancellable.lt_tsub_of_add_lt_right

Depends on / 依赖: AddLECancellable, Contravariant, Contravariant.AddLECancellable.lt_tsub_of_add_lt_right, lt_tsub_of_add_lt_right
-/
theorem lt_tsub_of_add_lt_right : a + c < b -> a < b - c :=
  Contravariant.AddLECancellable.lt_tsub_of_add_lt_right

end Contra

section Both

variable [AddLeftMono α] [AddLeftReflectLE α]

/--
theorem `add_tsub_add_eq_tsub_right` / 定理 `add_tsub_add_eq_tsub_right`

English:
theorem add_tsub_add_eq_tsub_right
  given: (a c b : α)
  statement: a + c - (b + c) = a - b
  proof: by
  refine add_tsub_add_le_tsub_right.antisymm (tsub_le_iff_right.2 <| ?_)
  apply le_of_add_le_add_right
  rw [add_assoc]
  exact le_tsub_add

中文:
定理 add_tsub_add_eq_tsub_right
  条件: (a c b : α)
  结论: a + c - (b + c) = a - b
  证明: by
  refine add_tsub_add_le_tsub_right.antisymm (tsub_le_iff_right.2 <| ?_)
  apply le_of_add_le_add_right
  rw [add_assoc]
  exact le_tsub_add

Depends on / 依赖: add_assoc, add_tsub_add_le_tsub_right, add_tsub_add_le_tsub_right.antisymm, antisymm, le_of_add_le_add_right, le_tsub_add, tsub_le_iff_right
-/
theorem add_tsub_add_eq_tsub_right (a c b : α) : a + c - (b + c) = a - b := by
  refine add_tsub_add_le_tsub_right.antisymm (tsub_le_iff_right.2 <| ?_)
  apply le_of_add_le_add_right
  rw [add_assoc]
  exact le_tsub_add

/--
theorem `add_tsub_add_eq_tsub_left` / 定理 `add_tsub_add_eq_tsub_left`

English:
theorem add_tsub_add_eq_tsub_left
  given: (a b c : α)
  statement: a + b - (a + c) = b - c
  proof: by
  rw [add_comm a b]; rw [add_comm a c]; rw [add_tsub_add_eq_tsub_right]

中文:
定理 add_tsub_add_eq_tsub_left
  条件: (a b c : α)
  结论: a + b - (a + c) = b - c
  证明: by
  rw [add_comm a b]; rw [add_comm a c]; rw [add_tsub_add_eq_tsub_right]

Depends on / 依赖: add_comm, add_tsub_add_eq_tsub_right
-/
theorem add_tsub_add_eq_tsub_left (a b c : α) : a + b - (a + c) = b - c := by
  rw [add_comm a b]; rw [add_comm a c]; rw [add_tsub_add_eq_tsub_right]

end Both

end OrderedAddCommSemigroup

/-! ### Lemmas in a linearly ordered monoid. -/


section LinearOrder

variable {a b c : α} [LinearOrder α] [AddCommSemigroup α] [Sub α] [OrderedSub α]

/--
theorem `lt_of_tsub_lt_tsub_right` / 定理 `lt_of_tsub_lt_tsub_right`

English:
theorem lt_of_tsub_lt_tsub_right
  given: (h : a - c < b - c)
  statement: a < b
  proof: lt_imp_lt_of_le_imp_le (fun h => tsub_le_tsub_right h c) h

中文:
定理 lt_of_tsub_lt_tsub_right
  条件: (h : a - c < b - c)
  结论: a < b
  证明: lt_imp_lt_of_le_imp_le (fun h => tsub_le_tsub_right h c) h

Depends on / 依赖: lt_imp_lt_of_le_imp_le, tsub_le_tsub_right
-/
theorem lt_of_tsub_lt_tsub_right (h : a - c < b - c) : a < b :=
  lt_imp_lt_of_le_imp_le (fun h => tsub_le_tsub_right h c) h

/--
theorem `lt_tsub_iff_right` / 定理 `lt_tsub_iff_right`

English:
theorem lt_tsub_iff_right
  statement: a < b - c ↔ a + c < b
  proof: lt_iff_lt_of_le_iff_le tsub_le_iff_right

中文:
定理 lt_tsub_iff_right
  结论: a < b - c ↔ a + c < b
  证明: lt_iff_lt_of_le_iff_le tsub_le_iff_right

Depends on / 依赖: lt_iff_lt_of_le_iff_le, tsub_le_iff_right
-/
theorem lt_tsub_iff_right : a < b - c ↔ a + c < b :=
  lt_iff_lt_of_le_iff_le tsub_le_iff_right

/--
theorem `lt_tsub_iff_left` / 定理 `lt_tsub_iff_left`

English:
theorem lt_tsub_iff_left
  statement: a < b - c ↔ c + a < b
  proof: lt_iff_lt_of_le_iff_le tsub_le_iff_left

中文:
定理 lt_tsub_iff_left
  结论: a < b - c ↔ c + a < b
  证明: lt_iff_lt_of_le_iff_le tsub_le_iff_left

Depends on / 依赖: lt_iff_lt_of_le_iff_le, tsub_le_iff_left
-/
theorem lt_tsub_iff_left : a < b - c ↔ c + a < b :=
  lt_iff_lt_of_le_iff_le tsub_le_iff_left

/--
theorem `lt_tsub_comm` / 定理 `lt_tsub_comm`

English:
theorem lt_tsub_comm
  statement: a < b - c ↔ c < b - a
  proof: lt_tsub_iff_left.trans lt_tsub_iff_right.symm

中文:
定理 lt_tsub_comm
  结论: a < b - c ↔ c < b - a
  证明: lt_tsub_iff_left.trans lt_tsub_iff_right.symm

Depends on / 依赖: lt_tsub_iff_left, lt_tsub_iff_left.trans, lt_tsub_iff_right, lt_tsub_iff_right.symm
-/
theorem lt_tsub_comm : a < b - c ↔ c < b - a :=
  lt_tsub_iff_left.trans lt_tsub_iff_right.symm

section Cov

variable [AddLeftMono α]

/--
theorem `lt_of_tsub_lt_tsub_left` / 定理 `lt_of_tsub_lt_tsub_left`

English:
theorem lt_of_tsub_lt_tsub_left
  given: (h : a - b < a - c)
  statement: c < b
  proof: lt_imp_lt_of_le_imp_le (fun h => tsub_le_tsub_left h a) h

中文:
定理 lt_of_tsub_lt_tsub_left
  条件: (h : a - b < a - c)
  结论: c < b
  证明: lt_imp_lt_of_le_imp_le (fun h => tsub_le_tsub_left h a) h

Depends on / 依赖: lt_imp_lt_of_le_imp_le, tsub_le_tsub_left
-/
theorem lt_of_tsub_lt_tsub_left (h : a - b < a - c) : c < b :=
  lt_imp_lt_of_le_imp_le (fun h => tsub_le_tsub_left h a) h

end Cov

end LinearOrder

section OrderedAddCommMonoid

variable [PartialOrder α] [AddCommMonoid α] [Sub α] [OrderedSub α]

@[simp]
/--
theorem `tsub_zero` / 定理 `tsub_zero`

English:
theorem tsub_zero
  given: (a : α)
  statement: a - 0 = a
  proof: AddLECancellable.tsub_eq_of_eq_add addLECancellable_zero (add_zero _).symm

中文:
定理 tsub_zero
  条件: (a : α)
  结论: a - 0 = a
  证明: AddLECancellable.tsub_eq_of_eq_add addLECancellable_zero (add_zero _).symm

Depends on / 依赖: AddLECancellable, AddLECancellable.tsub_eq_of_eq_add, addLECancellable_zero, add_zero, tsub_eq_of_eq_add
-/
theorem tsub_zero (a : α) : a - 0 = a :=
  AddLECancellable.tsub_eq_of_eq_add addLECancellable_zero (add_zero _).symm

end OrderedAddCommMonoid
