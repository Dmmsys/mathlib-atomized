/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Finset.Preimage
public import Mathlib.Data.Finset.Prod
public import Mathlib.Order.Hom.WithTopBot
public import Mathlib.Order.Interval.Set.UnorderedInterval

/-!
# Locally finite orders

This file defines locally finite orders.

A locally finite order is an order for which all bounded intervals are finite. This allows to make
sense of `Icc`/`Ico`/`Ioc`/`Ioo` as lists, multisets, or finsets.
Further, if the order is bounded above (resp. below), then we can also make sense of the
"unbounded" intervals `Ici`/`Ioi` (resp. `Iic`/`Iio`).

Many theorems about these intervals can be found in `Mathlib/Order/Interval/Finset/Basic.lean`.

## Examples

Naturally occurring locally finite orders are `ℕ`, `ℤ`, `ℕ+`, `Fin n`, `α × β` the product of two
locally finite orders, `α →₀ β` the finitely supported functions to a locally finite order `β`...

## Main declarations

In a `LocallyFiniteOrder`,
* `Finset.Icc`: Closed-closed interval as a finset.
* `Finset.Ico`: Closed-open interval as a finset.
* `Finset.Ioc`: Open-closed interval as a finset.
* `Finset.Ioo`: Open-open interval as a finset.
* `Finset.uIcc`: Unordered closed interval as a finset.

In a `LocallyFiniteOrderTop`,
* `Finset.Ici`: Closed-infinite interval as a finset.
* `Finset.Ioi`: Open-infinite interval as a finset.

In a `LocallyFiniteOrderBot`,
* `Finset.Iic`: Infinite-open interval as a finset.
* `Finset.Iio`: Infinite-closed interval as a finset.

## Instances

A `LocallyFiniteOrder` instance can be built
* for a subtype of a locally finite order. See `Subtype.locallyFiniteOrder`.
* for the product of two locally finite orders. See `Prod.locallyFiniteOrder`.
* for any fintype (but not as an instance). See `Fintype.toLocallyFiniteOrder`.
* from a definition of `Finset.Icc` alone. See `LocallyFiniteOrder.ofIcc`.
* by pulling back `LocallyFiniteOrder β` through an order embedding `f : α →o β`. See
  `OrderEmbedding.locallyFiniteOrder`.

Instances for concrete types are proved in their respective files:
* `ℕ` is in `Order.Interval.Finset.Nat`
* `ℤ` is in `Data.Int.Interval`
* `ℕ+` is in `Data.PNat.Interval`
* `Fin n` is in `Order.Interval.Finset.Fin`
* `Finset α` is in `Data.Finset.Interval`
* `Σ i, α i` is in `Data.Sigma.Interval`

Along, you will find lemmas about the cardinality of those finite intervals.

## TODO

Provide the `LocallyFiniteOrder` instance for `α ×ₗ β` where `LocallyFiniteOrder α` and
`Fintype β`.

Provide the `LocallyFiniteOrder` instance for `α →₀ β` where `β` is locally finite. Provide the
`LocallyFiniteOrder` instance for `Π₀ i, β i` where all the `β i` are locally finite.

From `LinearOrder α`, `NoMaxOrder α`, `LocallyFiniteOrder α`, we can also define an
order isomorphism `α ≃ ℕ` or `α ≃ ℤ`, depending on whether we have `OrderBot α` or
`NoMinOrder α` and `Nonempty α`. When `OrderBot α`, we can match `a : α` to `#(Iio a)`.

We can provide `SuccOrder α` from `LinearOrder α` and `LocallyFiniteOrder α` using

```lean
lemma exists_min_greater [LinearOrder α] [LocallyFiniteOrder α] {x ub : α} (hx : x < ub) :
    ∃ lub, x < lub ∧ ∀ y, x < y → lub ≤ y := by
  -- very non-golfed
  have h : (Finset.Ioc x ub).Nonempty := ⟨ub, Finset.mem_Ioc.2 ⟨hx, le_rfl⟩⟩
  use Finset.min' (Finset.Ioc x ub) h
  constructor
  · exact (Finset.mem_Ioc.mp <| Finset.min'_mem _ h).1
  rintro y hxy
  obtain hy | hy := le_total y ub
  · refine Finset.min'_le (Ioc x ub) y ?_
    simp [*] at *
  · exact (Finset.min'_le _ _ (Finset.mem_Ioc.2 ⟨hx, le_rfl⟩)).trans hy
```
Note that the converse is not true. Consider `{-2^z | z : ℤ} ∪ {2^z | z : ℤ}`. Any element has a
successor (and actually a predecessor as well), so it is a `SuccOrder`, but it's not locally finite
as `Icc (-1) 1` is infinite.
-/

@[expose] public section

open Finset Function

/--
Definition of `LocallyFiniteOrder` / `LocallyFiniteOrder` 的定义

English:
class LocallyFiniteOrder
  parameters: (α : Type*) [Preorder α]
  axioms and operations (8):
    - finsetIcc : α -> α -> Finset α
    - finsetIco : α -> α -> Finset α
    - finsetIoc : α -> α -> Finset α
    - finsetIoo : α -> α -> Finset α
    - finset_mem_Icc : forall a b x : α, x in finsetIcc a b ↔ a <= x ∧ x <= b
    - finset_mem_Ico : forall a b x : α, x in finsetIco a b ↔ a <= x ∧ x < b
    - finset_mem_Ioc : forall a b x : α, x in finsetIoc a b ↔ a < x ∧ x <= b
    - finset_mem_Ioo : forall a b x : α, x in finsetIoo a b ↔ a < x ∧ x < b

中文:
类 LocallyFiniteOrder
  参数: (α : 类型) [Preorder α]
  公理与运算 (8 个):
    - finsetIcc : α -> α -> Finset α
    - finsetIco : α -> α -> Finset α
    - finsetIoc : α -> α -> Finset α
    - finsetIoo : α -> α -> Finset α
    - finset_mem_Icc : 对任意 a b x : α, x in finsetIcc a b ↔ a <= x ∧ x <= b
    - finset_mem_Ico : 对任意 a b x : α, x in finsetIco a b ↔ a <= x ∧ x < b
    - finset_mem_Ioc : 对任意 a b x : α, x in finsetIoc a b ↔ a < x ∧ x <= b
    - finset_mem_Ioo : 对任意 a b x : α, x in finsetIoo a b ↔ a < x ∧ x < b
-/
class LocallyFiniteOrder (α : Type*) [Preorder α] where
  /-- Left-closed right-closed interval -/
  finsetIcc : α -> α -> Finset α
  /-- Left-closed right-open interval -/
  finsetIco : α -> α -> Finset α
  /-- Left-open right-closed interval -/
  finsetIoc : α -> α -> Finset α
  /-- Left-open right-open interval -/
  finsetIoo : α -> α -> Finset α
  /-- `x ∈ finsetIcc a b ↔ a ≤ x ∧ x ≤ b` -/
  finset_mem_Icc : forall a b x : α, x in finsetIcc a b ↔ a <= x ∧ x <= b
  /-- `x ∈ finsetIco a b ↔ a ≤ x ∧ x < b` -/
  finset_mem_Ico : forall a b x : α, x in finsetIco a b ↔ a <= x ∧ x < b
  /-- `x ∈ finsetIoc a b ↔ a < x ∧ x ≤ b` -/
  finset_mem_Ioc : forall a b x : α, x in finsetIoc a b ↔ a < x ∧ x <= b
  /-- `x ∈ finsetIoo a b ↔ a < x ∧ x < b` -/
  finset_mem_Ioo : forall a b x : α, x in finsetIoo a b ↔ a < x ∧ x < b

/-- `LocallyFiniteOrder.mk'` is the dual of `LocallyFiniteOrder.mk`, which we need for `to_dual`.
Please avoid using this directly. -/
@[to_dual existing mk]
/--
Definition of `LocallyFiniteOrder.mk'` / `LocallyFiniteOrder.mk'` 的定义

English:
abbreviation LocallyFiniteOrder.mk'
  signature: {α : Type*} [Preorder α]
  body: swap finsetIcc
  finsetIco := swap finsetIoc
  finsetIoc := swap finsetIco
  finsetIoo := swap finsetIoo
  finset_mem_Icc := by grind
  finset_mem_Ico := by grind
  finset_mem_Ioc := by grind
  finset_mem_Ioo := by grind

中文:
缩写 LocallyFiniteOrder.mk'
  签名: {α : 类型} [Preorder α]
  定义体: swap finsetIcc
  finsetIco := swap finsetIoc
  finsetIoc := swap finsetIco
  finsetIoo := swap finsetIoo
  finset_mem_Icc := by grind
  finset_mem_Ico := by grind
  finset_mem_Ioc := by grind
  finset_mem_Ioo := by grind

Depends on / 依赖: finsetIcc
-/
abbrev LocallyFiniteOrder.mk' {α : Type*} [Preorder α]
    (finsetIcc finsetIco finsetIoc finsetIoo : α -> α -> Finset α)
    (finset_mem_Icc : forall (a b x : α), x in finsetIcc a b ↔ x <= a ∧ b <= x)
    (finset_mem_Ico : forall (a b x : α), x in finsetIco a b ↔ x <= a ∧ b < x)
    (finset_mem_Ioc : forall (a b x : α), x in finsetIoc a b ↔ x < a ∧ b <= x)
    (finset_mem_Ioo : forall (a b x : α), x in finsetIoo a b ↔ x < a ∧ b < x) : LocallyFiniteOrder α where
  finsetIcc := swap finsetIcc
  finsetIco := swap finsetIoc
  finsetIoc := swap finsetIco
  finsetIoo := swap finsetIoo
  finset_mem_Icc := by grind
  finset_mem_Ico := by grind
  finset_mem_Ioc := by grind
  finset_mem_Ioo := by grind

/--
Definition of `LocallyFiniteOrderTop` / `LocallyFiniteOrderTop` 的定义

English:
class LocallyFiniteOrderTop
  parameters: (α : Type*) [Preorder α]
  axioms and operations (4):
    - finsetIoi : α -> Finset α
    - finsetIci : α -> Finset α
    - finset_mem_Ici : forall a x : α, x in finsetIci a ↔ a <= x
    - finset_mem_Ioi : forall a x : α, x in finsetIoi a ↔ a < x

中文:
类 LocallyFiniteOrderTop
  参数: (α : 类型) [Preorder α]
  公理与运算 (4 个):
    - finsetIoi : α -> Finset α
    - finsetIci : α -> Finset α
    - finset_mem_Ici : 对任意 a x : α, x in finsetIci a ↔ a <= x
    - finset_mem_Ioi : 对任意 a x : α, x in finsetIoi a ↔ a < x
-/
class LocallyFiniteOrderTop (α : Type*) [Preorder α] where
  /-- Left-open right-infinite interval -/
  finsetIoi : α -> Finset α
  /-- Left-closed right-infinite interval -/
  finsetIci : α -> Finset α
  /-- `x ∈ finsetIci a ↔ a ≤ x` -/
  finset_mem_Ici : forall a x : α, x in finsetIci a ↔ a <= x
  /-- `x ∈ finsetIoi a ↔ a < x` -/
  finset_mem_Ioi : forall a x : α, x in finsetIoi a ↔ a < x

/-- This mixin class describes an order where all intervals bounded above are finite. This is
slightly weaker than `LocallyFiniteOrder` + `OrderBot` as it allows empty types. -/
@[to_dual]
/--
Definition of `LocallyFiniteOrderBot` / `LocallyFiniteOrderBot` 的定义

English:
class LocallyFiniteOrderBot
  parameters: (α : Type*) [Preorder α]
  axioms and operations (4):
    - finsetIio : α -> Finset α
    - finsetIic : α -> Finset α
    - finset_mem_Iic : forall a x : α, x in finsetIic a ↔ x <= a
    - finset_mem_Iio : forall a x : α, x in finsetIio a ↔ x < a

中文:
类 LocallyFiniteOrderBot
  参数: (α : 类型) [Preorder α]
  公理与运算 (4 个):
    - finsetIio : α -> Finset α
    - finsetIic : α -> Finset α
    - finset_mem_Iic : 对任意 a x : α, x in finsetIic a ↔ x <= a
    - finset_mem_Iio : 对任意 a x : α, x in finsetIio a ↔ x < a
-/
class LocallyFiniteOrderBot (α : Type*) [Preorder α] where
  /-- Left-infinite right-open interval -/
  finsetIio : α -> Finset α
  /-- Left-infinite right-closed interval -/
  finsetIic : α -> Finset α
  /-- `x ∈ finsetIic a ↔ x ≤ a` -/
  finset_mem_Iic : forall a x : α, x in finsetIic a ↔ x <= a
  /-- `x ∈ finsetIio a ↔ x < a` -/
  finset_mem_Iio : forall a x : α, x in finsetIio a ↔ x < a

/-- A constructor from a definition of `Finset.Icc` alone, the other ones being derived by removing
the ends. As opposed to `LocallyFiniteOrder.ofIcc`, this one requires `DecidableLE` but
only `Preorder`. -/
@[instance_reducible]
/--
Definition of `LocallyFiniteOrder.ofIcc'` / `LocallyFiniteOrder.ofIcc'` 的定义

English:
definition LocallyFiniteOrder.ofIcc'
  signature: (α : Type*) [Preorder α] [DecidableLE α]
  body: finsetIcc
  finsetIco a b := {x in finsetIcc a b | ¬b <= x}
  finsetIoc a b := {x in finsetIcc a b | ¬x <= a}
  finsetIoo a b := {x in finsetIcc a b | ¬x <= a ∧ ¬b <= x}
  finset_mem_Icc := mem_Icc
  finset_mem_Ico a b x := by rw [Finset.mem_filter, mem_Icc, and_assoc, lt_iff_le_not_ge]
  finset_mem

中文:
定义 LocallyFiniteOrder.ofIcc'
  签名: (α : 类型) [Preorder α] [DecidableLE α]
  定义体: finsetIcc
  finsetIco a b := {x in finsetIcc a b | ¬b <= x}
  finsetIoc a b := {x in finsetIcc a b | ¬x <= a}
  finsetIoo a b := {x in finsetIcc a b | ¬x <= a ∧ ¬b <= x}
  finset_mem_Icc := mem_Icc
  finset_mem_Ico a b x := by rw [Finset.mem_filter, mem_Icc, and_assoc, lt_iff_le_not_ge]
  finset_mem

Depends on / 依赖: finsetIcc
-/
def LocallyFiniteOrder.ofIcc' (α : Type*) [Preorder α] [DecidableLE α]
    (finsetIcc : α -> α -> Finset α) (mem_Icc : forall a b x, x in finsetIcc a b ↔ a <= x ∧ x <= b) :
    LocallyFiniteOrder α where
  finsetIcc := finsetIcc
  finsetIco a b := {x in finsetIcc a b | ¬b <= x}
  finsetIoc a b := {x in finsetIcc a b | ¬x <= a}
  finsetIoo a b := {x in finsetIcc a b | ¬x <= a ∧ ¬b <= x}
  finset_mem_Icc := mem_Icc
  finset_mem_Ico a b x := by rw [Finset.mem_filter, mem_Icc, and_assoc, lt_iff_le_not_ge]
  finset_mem_Ioc a b x := by rw [Finset.mem_filter, mem_Icc, and_right_comm, lt_iff_le_not_ge]
  finset_mem_Ioo a b x := by
    rw [Finset.mem_filter]; rw [mem_Icc]; rw [and_and_and_comm]; rw [lt_iff_le_not_ge]; rw [lt_iff_le_not_ge]

/-- A constructor from a definition of `Finset.Icc` alone, the other ones being derived by removing
the ends. As opposed to `LocallyFiniteOrder.ofIcc'`, this one requires `PartialOrder` but only
`DecidableEq`. -/
@[instance_reducible]
/--
Definition of `LocallyFiniteOrder.ofIcc` / `LocallyFiniteOrder.ofIcc` 的定义

English:
definition LocallyFiniteOrder.ofIcc
  signature: (α : Type*) [PartialOrder α] [DecidableEq α]
  body: finsetIcc
  finsetIco a b := {x in finsetIcc a b | x != b}
  finsetIoc a b := {x in finsetIcc a b | a != x}
  finsetIoo a b := {x in finsetIcc a b | a != x ∧ x != b}
  finset_mem_Icc := mem_Icc
  finset_mem_Ico a b x := by rw [Finset.mem_filter, mem_Icc, and_assoc, lt_iff_le_and_ne]
  finset_mem_Ioc

中文:
定义 LocallyFiniteOrder.ofIcc
  签名: (α : 类型) [PartialOrder α] [DecidableEq α]
  定义体: finsetIcc
  finsetIco a b := {x in finsetIcc a b | x != b}
  finsetIoc a b := {x in finsetIcc a b | a != x}
  finsetIoo a b := {x in finsetIcc a b | a != x ∧ x != b}
  finset_mem_Icc := mem_Icc
  finset_mem_Ico a b x := by rw [Finset.mem_filter, mem_Icc, and_assoc, lt_iff_le_and_ne]
  finset_mem_Ioc

Depends on / 依赖: finsetIcc
-/
def LocallyFiniteOrder.ofIcc (α : Type*) [PartialOrder α] [DecidableEq α]
    (finsetIcc : α -> α -> Finset α) (mem_Icc : forall a b x, x in finsetIcc a b ↔ a <= x ∧ x <= b) :
    LocallyFiniteOrder α where
  finsetIcc := finsetIcc
  finsetIco a b := {x in finsetIcc a b | x != b}
  finsetIoc a b := {x in finsetIcc a b | a != x}
  finsetIoo a b := {x in finsetIcc a b | a != x ∧ x != b}
  finset_mem_Icc := mem_Icc
  finset_mem_Ico a b x := by rw [Finset.mem_filter, mem_Icc, and_assoc, lt_iff_le_and_ne]
  finset_mem_Ioc a b x := by rw [Finset.mem_filter, mem_Icc, and_right_comm, lt_iff_le_and_ne]
  finset_mem_Ioo a b x := by
    rw [Finset.mem_filter]; rw [mem_Icc]; rw [and_and_and_comm]; rw [lt_iff_le_and_ne]; rw [lt_iff_le_and_ne]

/-- A constructor from a definition of `Finset.Ici` alone, the other ones being derived by removing
the ends. As opposed to `LocallyFiniteOrderTop.ofIci`, this one requires `DecidableLE` but
only `Preorder`. -/
@[to_dual (attr := instance_reducible)
/-- A constructor from a definition of `Finset.Iic` alone, the other ones being derived by removing
the ends. As opposed to `LocallyFiniteOrderBot.ofIic`, this one requires `DecidableLE` but
only `Preorder`. -/]
/--
Definition of `LocallyFiniteOrderTop.ofIci'` / `LocallyFiniteOrderTop.ofIci'` 的定义

English:
definition LocallyFiniteOrderTop.ofIci'
  signature: (α : Type*) [Preorder α] [DecidableLE α]
  body: finsetIci
  finsetIoi a := {x in finsetIci a | ¬x <= a}
  finset_mem_Ici := mem_Ici
  finset_mem_Ioi a x := by rw [mem_filter, mem_Ici, lt_iff_le_not_ge]

中文:
定义 LocallyFiniteOrderTop.ofIci'
  签名: (α : 类型) [Preorder α] [DecidableLE α]
  定义体: finsetIci
  finsetIoi a := {x in finsetIci a | ¬x <= a}
  finset_mem_Ici := mem_Ici
  finset_mem_Ioi a x := by rw [mem_filter, mem_Ici, lt_iff_le_not_ge]

Depends on / 依赖: finsetIci
-/
def LocallyFiniteOrderTop.ofIci' (α : Type*) [Preorder α] [DecidableLE α]
    (finsetIci : α -> Finset α) (mem_Ici : forall a x, x in finsetIci a ↔ a <= x) :
    LocallyFiniteOrderTop α where
  finsetIci := finsetIci
  finsetIoi a := {x in finsetIci a | ¬x <= a}
  finset_mem_Ici := mem_Ici
  finset_mem_Ioi a x := by rw [mem_filter, mem_Ici, lt_iff_le_not_ge]

/-- A constructor from a definition of `Finset.Ici` alone, the other ones being derived by removing
the ends. As opposed to `LocallyFiniteOrderTop.ofIci'`, this one requires `PartialOrder` but
only `DecidableEq`. -/
@[to_dual (attr := instance_reducible)
/-- A constructor from a definition of `Finset.Iic` alone, the other ones being derived by removing
the ends. As opposed to `LocallyFiniteOrderBot.ofIic'`, this one requires `PartialOrder` but
only `DecidableEq`. -/]
/--
Definition of `LocallyFiniteOrderTop.ofIci` / `LocallyFiniteOrderTop.ofIci` 的定义

English:
definition LocallyFiniteOrderTop.ofIci
  signature: (α : Type*) [PartialOrder α] [DecidableEq α]
  body: finsetIci
  finsetIoi a := {x in finsetIci a | a != x}
  finset_mem_Ici := mem_Ici
  finset_mem_Ioi a x := by rw [mem_filter, mem_Ici, lt_iff_le_and_ne]

中文:
定义 LocallyFiniteOrderTop.ofIci
  签名: (α : 类型) [PartialOrder α] [DecidableEq α]
  定义体: finsetIci
  finsetIoi a := {x in finsetIci a | a != x}
  finset_mem_Ici := mem_Ici
  finset_mem_Ioi a x := by rw [mem_filter, mem_Ici, lt_iff_le_and_ne]

Depends on / 依赖: finsetIci
-/
def LocallyFiniteOrderTop.ofIci (α : Type*) [PartialOrder α] [DecidableEq α]
    (finsetIci : α -> Finset α) (mem_Ici : forall a x, x in finsetIci a ↔ a <= x) :
    LocallyFiniteOrderTop α where
  finsetIci := finsetIci
  finsetIoi a := {x in finsetIci a | a != x}
  finset_mem_Ici := mem_Ici
  finset_mem_Ioi a x := by rw [mem_filter, mem_Ici, lt_iff_le_and_ne]

variable {α β : Type*}

-- See note [reducible non-instances]
/--
Definition of `IsEmpty.toLocallyFiniteOrder` / `IsEmpty.toLocallyFiniteOrder` 的定义

English:
abbreviation IsEmpty.toLocallyFiniteOrder
  signature: [Preorder α] [IsEmpty α]
  body: isEmptyElim
  finsetIco := isEmptyElim
  finsetIoc := isEmptyElim
  finsetIoo := isEmptyElim
  finset_mem_Icc := isEmptyElim
  finset_mem_Ico := isEmptyElim
  finset_mem_Ioc := isEmptyElim
  finset_mem_Ioo := isEmptyElim

中文:
缩写 IsEmpty.toLocallyFiniteOrder
  签名: [Preorder α] [IsEmpty α]
  定义体: isEmptyElim
  finsetIco := isEmptyElim
  finsetIoc := isEmptyElim
  finsetIoo := isEmptyElim
  finset_mem_Icc := isEmptyElim
  finset_mem_Ico := isEmptyElim
  finset_mem_Ioc := isEmptyElim
  finset_mem_Ioo := isEmptyElim
-/
protected abbrev IsEmpty.toLocallyFiniteOrder [Preorder α] [IsEmpty α] : LocallyFiniteOrder α where
  finsetIcc := isEmptyElim
  finsetIco := isEmptyElim
  finsetIoc := isEmptyElim
  finsetIoo := isEmptyElim
  finset_mem_Icc := isEmptyElim
  finset_mem_Ico := isEmptyElim
  finset_mem_Ioc := isEmptyElim
  finset_mem_Ioo := isEmptyElim

-- See note [reducible non-instances]
/-- An empty type is locally finite.

This is not an instance as it would not be defeq to more specific instances. -/
@[to_dual
/-- An empty type is locally finite.

This is not an instance as it would not be defeq to more specific instances. -/]
/--
Definition of `IsEmpty.toLocallyFiniteOrderTop` / `IsEmpty.toLocallyFiniteOrderTop` 的定义

English:
abbreviation IsEmpty.toLocallyFiniteOrderTop
  signature: [Preorder α] [IsEmpty α]
  body: isEmptyElim
  finsetIoi := isEmptyElim
  finset_mem_Ici := isEmptyElim
  finset_mem_Ioi := isEmptyElim

中文:
缩写 IsEmpty.toLocallyFiniteOrderTop
  签名: [Preorder α] [IsEmpty α]
  定义体: isEmptyElim
  finsetIoi := isEmptyElim
  finset_mem_Ici := isEmptyElim
  finset_mem_Ioi := isEmptyElim
-/
protected abbrev IsEmpty.toLocallyFiniteOrderTop [Preorder α] [IsEmpty α] :
    LocallyFiniteOrderTop α where
  finsetIci := isEmptyElim
  finsetIoi := isEmptyElim
  finset_mem_Ici := isEmptyElim
  finset_mem_Ioi := isEmptyElim

/-! ### Intervals as finsets -/


namespace Finset

section Preorder

variable [Preorder α]

section LocallyFiniteOrder

variable [LocallyFiniteOrder α] {a b x : α}

/-- The finset $[a, b]$ of elements `x` such that `a ≤ x` and `x ≤ b`. Basically `Set.Icc a b` as a
finset. -/
@[to_dual self (reorder := a b)]
/--
Definition of `Icc` / `Icc` 的定义

English:
definition Icc
  signature: (a b : α)
  body: LocallyFiniteOrder.finsetIcc a b

中文:
定义 Icc
  签名: (a b : α)
  定义体: LocallyFiniteOrder.finsetIcc a b

Depends on / 依赖: LocallyFiniteOrder, LocallyFiniteOrder.finsetIcc, finsetIcc
-/
def Icc (a b : α) : Finset α :=
  LocallyFiniteOrder.finsetIcc a b

/--
Definition of `Ico` / `Ico` 的定义

English:
definition Ico
  signature: (a b : α)
  body: LocallyFiniteOrder.finsetIco a b

中文:
定义 Ico
  签名: (a b : α)
  定义体: LocallyFiniteOrder.finsetIco a b

Depends on / 依赖: LocallyFiniteOrder, LocallyFiniteOrder.finsetIco, finsetIco
-/
def Ico (a b : α) : Finset α :=
  LocallyFiniteOrder.finsetIco a b

/-- The finset $(a, b]$ of elements `x` such that `a < x` and `x ≤ b`. Basically `Set.Ioc a b` as a
finset. -/
@[to_dual existing (reorder := a b)]
/--
Definition of `Ioc` / `Ioc` 的定义

English:
definition Ioc
  signature: (a b : α)
  body: LocallyFiniteOrder.finsetIoc a b

中文:
定义 Ioc
  签名: (a b : α)
  定义体: LocallyFiniteOrder.finsetIoc a b

Depends on / 依赖: LocallyFiniteOrder, LocallyFiniteOrder.finsetIoc, finsetIoc
-/
def Ioc (a b : α) : Finset α :=
  LocallyFiniteOrder.finsetIoc a b

/-- The finset $(a, b)$ of elements `x` such that `a < x` and `x < b`. Basically `Set.Ioo a b` as a
finset. -/
@[to_dual self (reorder := a b)]
/--
Definition of `Ioo` / `Ioo` 的定义

English:
definition Ioo
  signature: (a b : α)
  body: LocallyFiniteOrder.finsetIoo a b

@[simp, grind =]

中文:
定义 Ioo
  签名: (a b : α)
  定义体: LocallyFiniteOrder.finsetIoo a b

@[simp, grind =]

Depends on / 依赖: LocallyFiniteOrder, LocallyFiniteOrder.finsetIoo, finsetIoo
-/
def Ioo (a b : α) : Finset α :=
  LocallyFiniteOrder.finsetIoo a b

@[simp, grind =]
/--
theorem `mem_Icc` / 定理 `mem_Icc`

English:
theorem mem_Icc
  statement: x in Icc a b ↔ a <= x ∧ x <= b
  proof: LocallyFiniteOrder.finset_mem_Icc a b x

@[simp, grind =]

中文:
定理 mem_Icc
  结论: x in Icc a b ↔ a <= x ∧ x <= b
  证明: LocallyFiniteOrder.finset_mem_Icc a b x

@[simp, grind =]

Depends on / 依赖: LocallyFiniteOrder, LocallyFiniteOrder.finset_mem_Icc, finset_mem_Icc
-/
theorem mem_Icc : x in Icc a b ↔ a <= x ∧ x <= b :=
  LocallyFiniteOrder.finset_mem_Icc a b x

@[simp, grind =]
/--
theorem `mem_Ico` / 定理 `mem_Ico`

English:
theorem mem_Ico
  statement: x in Ico a b ↔ a <= x ∧ x < b
  proof: LocallyFiniteOrder.finset_mem_Ico a b x

@[simp, grind =]

中文:
定理 mem_Ico
  结论: x in Ico a b ↔ a <= x ∧ x < b
  证明: LocallyFiniteOrder.finset_mem_Ico a b x

@[simp, grind =]

Depends on / 依赖: LocallyFiniteOrder, LocallyFiniteOrder.finset_mem_Ico, finset_mem_Ico
-/
theorem mem_Ico : x in Ico a b ↔ a <= x ∧ x < b :=
  LocallyFiniteOrder.finset_mem_Ico a b x

@[simp, grind =]
/--
theorem `mem_Ioc` / 定理 `mem_Ioc`

English:
theorem mem_Ioc
  statement: x in Ioc a b ↔ a < x ∧ x <= b
  proof: LocallyFiniteOrder.finset_mem_Ioc a b x

@[simp, grind =]

中文:
定理 mem_Ioc
  结论: x in Ioc a b ↔ a < x ∧ x <= b
  证明: LocallyFiniteOrder.finset_mem_Ioc a b x

@[simp, grind =]

Depends on / 依赖: LocallyFiniteOrder, LocallyFiniteOrder.finset_mem_Ioc, finset_mem_Ioc
-/
theorem mem_Ioc : x in Ioc a b ↔ a < x ∧ x <= b :=
  LocallyFiniteOrder.finset_mem_Ioc a b x

@[simp, grind =]
/--
theorem `mem_Ioo` / 定理 `mem_Ioo`

English:
theorem mem_Ioo
  statement: x in Ioo a b ↔ a < x ∧ x < b
  proof: LocallyFiniteOrder.finset_mem_Ioo a b x

中文:
定理 mem_Ioo
  结论: x in Ioo a b ↔ a < x ∧ x < b
  证明: LocallyFiniteOrder.finset_mem_Ioo a b x

Depends on / 依赖: LocallyFiniteOrder, LocallyFiniteOrder.finset_mem_Ioo, finset_mem_Ioo
-/
theorem mem_Ioo : x in Ioo a b ↔ a < x ∧ x < b :=
  LocallyFiniteOrder.finset_mem_Ioo a b x

/--
theorem `mem_Icc'` / 定理 `mem_Icc'`

English:
theorem mem_Icc'
  statement: x in Icc a b ↔ x <= b ∧ a <= x
  proof: by grind

中文:
定理 mem_Icc'
  结论: x in Icc a b ↔ x <= b ∧ a <= x
  证明: by grind
-/
@[to_dual existing mem_Icc] theorem mem_Icc' : x in Icc a b ↔ x <= b ∧ a <= x := by grind
/--
theorem `mem_Ico'` / 定理 `mem_Ico'`

English:
theorem mem_Ico'
  statement: x in Ico a b ↔ x < b ∧ a <= x
  proof: by grind

中文:
定理 mem_Ico'
  结论: x in Ico a b ↔ x < b ∧ a <= x
  证明: by grind
-/
@[to_dual existing mem_Ioc] theorem mem_Ico' : x in Ico a b ↔ x < b ∧ a <= x := by grind
/--
theorem `mem_Ioc'` / 定理 `mem_Ioc'`

English:
theorem mem_Ioc'
  statement: x in Ioc a b ↔ x <= b ∧ a < x
  proof: by grind

中文:
定理 mem_Ioc'
  结论: x in Ioc a b ↔ x <= b ∧ a < x
  证明: by grind
-/
@[to_dual existing mem_Ico] theorem mem_Ioc' : x in Ioc a b ↔ x <= b ∧ a < x := by grind
/--
theorem `mem_Ioo'` / 定理 `mem_Ioo'`

English:
theorem mem_Ioo'
  statement: x in Ioo a b ↔ x < b ∧ a < x
  proof: by grind

@[simp, norm_cast, to_dual self]

中文:
定理 mem_Ioo'
  结论: x in Ioo a b ↔ x < b ∧ a < x
  证明: by grind

@[simp, norm_cast, to_dual self]

Depends on / 依赖: IsScalarTower, IsScalarTower.toAlgHom, of_isLocalizedModule, toAlgHom, toLinearMap
-/
@[to_dual existing mem_Ioo] theorem mem_Ioo' : x in Ioo a b ↔ x < b ∧ a < x := by grind

@[simp, norm_cast, to_dual self]
/--
theorem `coe_Icc` / 定理 `coe_Icc`

English:
theorem coe_Icc
  given: (a b : α)
  statement: (Icc a b : Set α) = Set.Icc a b
  proof: Set.ext fun _ => mem_Icc

@[to_dual (reorder := a b) (attr := simp, norm_cast)]

中文:
定理 coe_Icc
  条件: (a b : α)
  结论: (Icc a b : Set α) = Set.Icc a b
  证明: Set.ext fun _ => mem_Icc

@[to_dual (reorder := a b) (attr := simp, norm_cast)]

Depends on / 依赖: Set.ext, mem_Icc
-/
theorem coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b :=
  Set.ext fun _ => mem_Icc

@[to_dual (reorder := a b) (attr := simp, norm_cast)]
/--
theorem `coe_Ico` / 定理 `coe_Ico`

English:
theorem coe_Ico
  given: (a b : α)
  statement: (Ico a b : Set α) = Set.Ico a b
  proof: Set.ext fun _ => mem_Ico

@[simp, norm_cast, to_dual self]

中文:
定理 coe_Ico
  条件: (a b : α)
  结论: (Ico a b : Set α) = Set.Ico a b
  证明: Set.ext fun _ => mem_Ico

@[simp, norm_cast, to_dual self]

Depends on / 依赖: Set.ext, mem_Ico
-/
theorem coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b :=
  Set.ext fun _ => mem_Ico

@[simp, norm_cast, to_dual self]
/--
theorem `coe_Ioo` / 定理 `coe_Ioo`

English:
theorem coe_Ioo
  given: (a b : α)
  statement: (Ioo a b : Set α) = Set.Ioo a b
  proof: Set.ext fun _ => mem_Ioo

@[to_dual self]

中文:
定理 coe_Ioo
  条件: (a b : α)
  结论: (Ioo a b : Set α) = Set.Ioo a b
  证明: Set.ext fun _ => mem_Ioo

@[to_dual self]

Depends on / 依赖: Set.ext, mem_Ioo
-/
theorem coe_Ioo (a b : α) : (Ioo a b : Set α) = Set.Ioo a b :=
  Set.ext fun _ => mem_Ioo

@[to_dual self]
/--
theorem `_root_.Fintype.card_Icc` / 定理 `_root_.Fintype.card_Icc`

English:
theorem _root_.Fintype.card_Icc
  given: (a b : α) [Fintype (Set.Icc a b)]
  proof: Fintype.card_of_finset' _ fun _ => by simp

@[to_dual (reorder := a b)]

中文:
定理 _root_.Fintype.card_Icc
  条件: (a b : α) [Fintype (Set.Icc a b)]
  证明: Fintype.card_of_finset' _ fun _ => by simp

@[to_dual (reorder := a b)]

Depends on / 依赖: Fintype, Fintype.card_of_finset, card_of_finset
-/
theorem _root_.Fintype.card_Icc (a b : α) [Fintype (Set.Icc a b)] :
    Fintype.card (Set.Icc a b) = #(Icc a b) :=
  Fintype.card_of_finset' _ fun _ => by simp

@[to_dual (reorder := a b)]
/--
theorem `_root_.Fintype.card_Ico` / 定理 `_root_.Fintype.card_Ico`

English:
theorem _root_.Fintype.card_Ico
  given: (a b : α) [Fintype (Set.Ico a b)]
  proof: Fintype.card_of_finset' _ fun _ => by simp

@[to_dual self]

中文:
定理 _root_.Fintype.card_Ico
  条件: (a b : α) [Fintype (Set.Ico a b)]
  证明: Fintype.card_of_finset' _ fun _ => by simp

@[to_dual self]

Depends on / 依赖: Fintype, Fintype.card_of_finset, card_of_finset
-/
theorem _root_.Fintype.card_Ico (a b : α) [Fintype (Set.Ico a b)] :
    Fintype.card (Set.Ico a b) = #(Ico a b) :=
  Fintype.card_of_finset' _ fun _ => by simp

@[to_dual self]
/--
theorem `_root_.Fintype.card_Ioo` / 定理 `_root_.Fintype.card_Ioo`

English:
theorem _root_.Fintype.card_Ioo
  given: (a b : α) [Fintype (Set.Ioo a b)]
  proof: Fintype.card_of_finset' _ fun _ => by simp

中文:
定理 _root_.Fintype.card_Ioo
  条件: (a b : α) [Fintype (Set.Ioo a b)]
  证明: Fintype.card_of_finset' _ fun _ => by simp

Depends on / 依赖: Fintype, Fintype.card_of_finset, card_of_finset
-/
theorem _root_.Fintype.card_Ioo (a b : α) [Fintype (Set.Ioo a b)] :
    Fintype.card (Set.Ioo a b) = #(Ioo a b) :=
  Fintype.card_of_finset' _ fun _ => by simp

end LocallyFiniteOrder

section LocallyFiniteOrderTop

variable [LocallyFiniteOrderTop α] {a x : α}

/-- The finset $[a, ∞)$ of elements `x` such that `a ≤ x`. Basically `Set.Ici a` as a finset. -/
@[to_dual
/-- The finset $(-∞, b]$ of elements `x` such that `x ≤ b`. Basically `Set.Iic b` as a finset. -/]
/--
Definition of `Ici` / `Ici` 的定义

English:
definition Ici
  signature: (a : α)
  body: LocallyFiniteOrderTop.finsetIci a

中文:
定义 Ici
  签名: (a : α)
  定义体: LocallyFiniteOrderTop.finsetIci a

Depends on / 依赖: LocallyFiniteOrderTop, LocallyFiniteOrderTop.finsetIci, finsetIci
-/
def Ici (a : α) : Finset α :=
  LocallyFiniteOrderTop.finsetIci a

/-- The finset $(a, ∞)$ of elements `x` such that `a < x`. Basically `Set.Ioi a` as a finset. -/
@[to_dual
/-- The finset $(-∞, b)$ of elements `x` such that `x < b`. Basically `Set.Iio b` as a finset. -/]
/--
Definition of `Ioi` / `Ioi` 的定义

English:
definition Ioi
  signature: (a : α)
  body: LocallyFiniteOrderTop.finsetIoi a

@[to_dual (attr := simp, grind =)]

中文:
定义 Ioi
  签名: (a : α)
  定义体: LocallyFiniteOrderTop.finsetIoi a

@[to_dual (attr := simp, grind =)]

Depends on / 依赖: LocallyFiniteOrderTop, LocallyFiniteOrderTop.finsetIoi, finsetIoi
-/
def Ioi (a : α) : Finset α :=
  LocallyFiniteOrderTop.finsetIoi a

@[to_dual (attr := simp, grind =)]
/--
theorem `mem_Ici` / 定理 `mem_Ici`

English:
theorem mem_Ici
  statement: x in Ici a ↔ a <= x
  proof: LocallyFiniteOrderTop.finset_mem_Ici _ _

@[to_dual (attr := simp, grind =)]

中文:
定理 mem_Ici
  结论: x in Ici a ↔ a <= x
  证明: LocallyFiniteOrderTop.finset_mem_Ici _ _

@[to_dual (attr := simp, grind =)]

Depends on / 依赖: LocallyFiniteOrderTop, LocallyFiniteOrderTop.finset_mem_Ici, finset_mem_Ici
-/
theorem mem_Ici : x in Ici a ↔ a <= x :=
  LocallyFiniteOrderTop.finset_mem_Ici _ _

@[to_dual (attr := simp, grind =)]
/--
theorem `mem_Ioi` / 定理 `mem_Ioi`

English:
theorem mem_Ioi
  statement: x in Ioi a ↔ a < x
  proof: LocallyFiniteOrderTop.finset_mem_Ioi _ _

@[to_dual (attr := simp, norm_cast)]

中文:
定理 mem_Ioi
  结论: x in Ioi a ↔ a < x
  证明: LocallyFiniteOrderTop.finset_mem_Ioi _ _

@[to_dual (attr := simp, norm_cast)]

Depends on / 依赖: LocallyFiniteOrderTop, LocallyFiniteOrderTop.finset_mem_Ioi, finset_mem_Ioi
-/
theorem mem_Ioi : x in Ioi a ↔ a < x :=
  LocallyFiniteOrderTop.finset_mem_Ioi _ _

@[to_dual (attr := simp, norm_cast)]
/--
theorem `coe_Ici` / 定理 `coe_Ici`

English:
theorem coe_Ici
  given: (a : α)
  statement: (Ici a : Set α) = Set.Ici a
  proof: Set.ext fun _ => mem_Ici

@[to_dual (attr := simp, norm_cast)]

中文:
定理 coe_Ici
  条件: (a : α)
  结论: (Ici a : Set α) = Set.Ici a
  证明: Set.ext fun _ => mem_Ici

@[to_dual (attr := simp, norm_cast)]

Depends on / 依赖: Set.ext, mem_Ici
-/
theorem coe_Ici (a : α) : (Ici a : Set α) = Set.Ici a :=
  Set.ext fun _ => mem_Ici

@[to_dual (attr := simp, norm_cast)]
/--
theorem `coe_Ioi` / 定理 `coe_Ioi`

English:
theorem coe_Ioi
  given: (a : α)
  statement: (Ioi a : Set α) = Set.Ioi a
  proof: Set.ext fun _ => mem_Ioi

@[to_dual]

中文:
定理 coe_Ioi
  条件: (a : α)
  结论: (Ioi a : Set α) = Set.Ioi a
  证明: Set.ext fun _ => mem_Ioi

@[to_dual]

Depends on / 依赖: Set.ext, mem_Ioi
-/
theorem coe_Ioi (a : α) : (Ioi a : Set α) = Set.Ioi a :=
  Set.ext fun _ => mem_Ioi

@[to_dual]
/--
theorem `_root_.Fintype.card_Ici` / 定理 `_root_.Fintype.card_Ici`

English:
theorem _root_.Fintype.card_Ici
  given: (a : α) [Fintype (Set.Ici a)]
  proof: Fintype.card_of_finset' _ fun _ => by simp

@[to_dual]

中文:
定理 _root_.Fintype.card_Ici
  条件: (a : α) [Fintype (Set.Ici a)]
  证明: Fintype.card_of_finset' _ fun _ => by simp

@[to_dual]

Depends on / 依赖: Fintype, Fintype.card_of_finset, card_of_finset
-/
theorem _root_.Fintype.card_Ici (a : α) [Fintype (Set.Ici a)] :
    Fintype.card (Set.Ici a) = #(Ici a) :=
  Fintype.card_of_finset' _ fun _ => by simp

@[to_dual]
/--
theorem `_root_.Fintype.card_Ioi` / 定理 `_root_.Fintype.card_Ioi`

English:
theorem _root_.Fintype.card_Ioi
  given: (a : α) [Fintype (Set.Ioi a)]
  proof: Fintype.card_of_finset' _ fun _ => by simp

@[to_additive (attr := simp)]

中文:
定理 _root_.Fintype.card_Ioi
  条件: (a : α) [Fintype (Set.Ioi a)]
  证明: Fintype.card_of_finset' _ fun _ => by simp

@[to_additive (attr := simp)]

Depends on / 依赖: Fintype, Fintype.card_of_finset, card_of_finset
-/
theorem _root_.Fintype.card_Ioi (a : α) [Fintype (Set.Ioi a)] :
    Fintype.card (Set.Ioi a) = #(Ioi a) :=
  Fintype.card_of_finset' _ fun _ => by simp

@[to_additive (attr := simp)]
/--
lemma `Ici_one_eq_univ` / 引理 `Ici_one_eq_univ`

English:
lemma Ici_one_eq_univ
  given: [One α] [IsBotOneClass α] [Fintype α]
  statement: Ici (1 : α) = univ
  proof: by ext; simp

中文:
引理 Ici_one_eq_univ
  条件: [One α] [IsBotOneClass α] [Fintype α]
  结论: Ici (1 : α) = univ
  证明: by ext; simp
-/
lemma Ici_one_eq_univ [One α] [IsBotOneClass α] [Fintype α] : Ici (1 : α) = univ := by ext; simp

end LocallyFiniteOrderTop

section OrderTop

variable [LocallyFiniteOrder α] [OrderTop α] {a x : α}

-- See note [lower priority instance]
@[to_dual]
instance (priority := 100) _root_.LocallyFiniteOrder.toLocallyFiniteOrderTop :
    LocallyFiniteOrderTop α where
  finsetIci b := Icc b ⊤
  finsetIoi b := Ioc b ⊤
  finset_mem_Ici a x := by rw [mem_Icc, and_iff_left le_top]
  finset_mem_Ioi a x := by rw [mem_Ioc, and_iff_left le_top]

@[to_dual]
/--
theorem `Ici_eq_Icc` / 定理 `Ici_eq_Icc`

English:
theorem Ici_eq_Icc
  given: (a : α)
  statement: Ici a = Icc a ⊤
  proof: rfl

@[to_dual]

中文:
定理 Ici_eq_Icc
  条件: (a : α)
  结论: Ici a = Icc a ⊤
  证明: rfl

@[to_dual]
-/
theorem Ici_eq_Icc (a : α) : Ici a = Icc a ⊤ :=
  rfl

@[to_dual]
/--
theorem `Ioi_eq_Ioc` / 定理 `Ioi_eq_Ioc`

English:
theorem Ioi_eq_Ioc
  given: (a : α)
  statement: Ioi a = Ioc a ⊤
  proof: rfl

中文:
定理 Ioi_eq_Ioc
  条件: (a : α)
  结论: Ioi a = Ioc a ⊤
  证明: rfl
-/
theorem Ioi_eq_Ioc (a : α) : Ioi a = Ioc a ⊤ :=
  rfl

end OrderTop

end Preorder

section Lattice

variable [Lattice α] [LocallyFiniteOrder α] {a b x : α}

/--
Definition of `uIcc` / `uIcc` 的定义

English:
definition uIcc
  signature: (a b : α)
  body: Icc (a ⊓ b) (a ⊔ b)

@[inherit_doc]
scoped[FinsetInterval] notation "[[" a ", " b "]]" => Finset.uIcc a b

@[simp]

中文:
定义 uIcc
  签名: (a b : α)
  定义体: Icc (a ⊓ b) (a ⊔ b)

@[inherit_doc]
scoped[FinsetInterval] notation "[[" a ", " b "]]" => Finset.uIcc a b

@[simp]
-/
def uIcc (a b : α) : Finset α :=
  Icc (a ⊓ b) (a ⊔ b)

@[inherit_doc]
scoped[FinsetInterval] notation "[[" a ", " b "]]" => Finset.uIcc a b

@[simp]
/--
theorem `mem_uIcc` / 定理 `mem_uIcc`

English:
theorem mem_uIcc
  statement: x in uIcc a b ↔ a ⊓ b <= x ∧ x <= a ⊔ b
  proof: mem_Icc

@[simp, norm_cast]

中文:
定理 mem_uIcc
  结论: x in uIcc a b ↔ a ⊓ b <= x ∧ x <= a ⊔ b
  证明: mem_Icc

@[simp, norm_cast]

Depends on / 依赖: mem_Icc
-/
theorem mem_uIcc : x in uIcc a b ↔ a ⊓ b <= x ∧ x <= a ⊔ b :=
  mem_Icc

@[simp, norm_cast]
/--
theorem `coe_uIcc` / 定理 `coe_uIcc`

English:
theorem coe_uIcc
  given: (a b : α)
  statement: (Finset.uIcc a b : Set α) = Set.uIcc a b
  proof: coe_Icc _ _

中文:
定理 coe_uIcc
  条件: (a b : α)
  结论: (Finset.uIcc a b : Set α) = Set.uIcc a b
  证明: coe_Icc _ _

Depends on / 依赖: coe_Icc
-/
theorem coe_uIcc (a b : α) : (Finset.uIcc a b : Set α) = Set.uIcc a b :=
  coe_Icc _ _

/--
theorem `_root_.Fintype.card_uIcc` / 定理 `_root_.Fintype.card_uIcc`

English:
theorem _root_.Fintype.card_uIcc
  given: (a b : α) [Fintype (Set.uIcc a b)]
  proof: Fintype.card_of_finset' _ fun _ => by simp [Set.uIcc]

中文:
定理 _root_.Fintype.card_uIcc
  条件: (a b : α) [Fintype (Set.uIcc a b)]
  证明: Fintype.card_of_finset' _ fun _ => by simp [Set.uIcc]

Depends on / 依赖: Fintype, Fintype.card_of_finset, Set.uIcc, card_of_finset
-/
theorem _root_.Fintype.card_uIcc (a b : α) [Fintype (Set.uIcc a b)] :
    Fintype.card (Set.uIcc a b) = #(uIcc a b) :=
  Fintype.card_of_finset' _ fun _ => by simp [Set.uIcc]

end Lattice

end Finset

namespace Mathlib.Meta
open Lean Elab Term Meta Batteries.ExtendedBinder

/-- Elaborate set builder notation for `Finset`.

* `{x ≤ a | p x}` is elaborated as `Finset.filter (fun x ↦ p x) (Finset.Iic a)` if the expected type
  is `Finset ?α`.
* `{x ≥ a | p x}` is elaborated as `Finset.filter (fun x ↦ p x) (Finset.Ici a)` if the expected type
  is `Finset ?α`.
* `{x < a | p x}` is elaborated as `Finset.filter (fun x ↦ p x) (Finset.Iio a)` if the expected type
  is `Finset ?α`.
* `{x > a | p x}` is elaborated as `Finset.filter (fun x ↦ p x) (Finset.Ioi a)` if the expected type
  is `Finset ?α`.

See also
* `Data.Set.Defs` for the `Set` builder notation elaborator that this elaborator partly overrides.
* `Data.Finset.Basic` for the `Finset` builder notation elaborator partly overriding this one for
  syntax of the form `{x ∈ s | p x}`.
* `Data.Fintype.Basic` for the `Finset` builder notation elaborator handling syntax of the form
  `{x | p x}`, `{x : α | p x}`, `{x ∉ s | p x}`, `{x ≠ a | p x}`.

TODO: Write a delaborator
-/
@[term_elab setBuilder]
meta def elabFinsetBuilderIxx : TermElab
  | `({ $x:ident <= $a | $p }), expectedType? => do
    -- If the expected type is not known to be `Finset ?α`, give up.
    unless ← knownToBeFinsetNotSet expectedType? do throwUnsupportedSyntax
    elabTerm (← `(Finset.filter (fun $x:ident => $p) (Finset.Iic $a))) expectedType?
  | `({ $x:ident >= $a | $p }), expectedType? => do
    -- If the expected type is not known to be `Finset ?α`, give up.
    unless ← knownToBeFinsetNotSet expectedType? do throwUnsupportedSyntax
    elabTerm (← `(Finset.filter (fun $x:ident => $p) (Finset.Ici $a))) expectedType?
  | `({ $x:ident < $a | $p }), expectedType? => do
    -- If the expected type is not known to be `Finset ?α`, give up.
    unless ← knownToBeFinsetNotSet expectedType? do throwUnsupportedSyntax
    elabTerm (← `(Finset.filter (fun $x:ident => $p) (Finset.Iio $a))) expectedType?
  | `({ $x:ident > $a | $p }), expectedType? => do
    -- If the expected type is not known to be `Finset ?α`, give up.
    unless ← knownToBeFinsetNotSet expectedType? do throwUnsupportedSyntax
    elabTerm (← `(Finset.filter (fun $x:ident => $p) (Finset.Ioi $a))) expectedType?
  | _, _ => throwUnsupportedSyntax

end Mathlib.Meta

/-! ### Finiteness of `Set` intervals -/


namespace Set

section Preorder

variable [Preorder α] [LocallyFiniteOrder α] (a b : α)

@[to_dual self]
/--
Instance `instFintypeIcc` / 实例 `instFintypeIcc`

English:
instance instFintypeIcc
  signature: : Fintype (Icc a b)
  body: .ofFinset (Finset.Icc a b) fun _ => by simp

@[to_dual (reorder := a b)]

中文:
实例 instFintypeIcc
  签名: : Fintype (Icc a b)
  定义体: .ofFinset (Finset.Icc a b) fun _ => by simp

@[to_dual (reorder := a b)]

Depends on / 依赖: Finset, Finset.Icc, ofFinset
-/
instance instFintypeIcc : Fintype (Icc a b) := .ofFinset (Finset.Icc a b) fun _ => by simp

@[to_dual (reorder := a b)]
/--
Instance `instFintypeIco` / 实例 `instFintypeIco`

English:
instance instFintypeIco
  signature: : Fintype (Ico a b)
  body: .ofFinset (Finset.Ico a b) fun _ => by simp

@[to_dual self]

中文:
实例 instFintypeIco
  签名: : Fintype (Ico a b)
  定义体: .ofFinset (Finset.Ico a b) fun _ => by simp

@[to_dual self]

Depends on / 依赖: Finset, Finset.Ico, ofFinset
-/
instance instFintypeIco : Fintype (Ico a b) := .ofFinset (Finset.Ico a b) fun _ => by simp

@[to_dual self]
/--
Instance `instFintypeIoo` / 实例 `instFintypeIoo`

English:
instance instFintypeIoo
  signature: : Fintype (Ioo a b)
  body: .ofFinset (Finset.Ioo a b) fun _ => by simp

@[simp, to_dual self]

中文:
实例 instFintypeIoo
  签名: : Fintype (Ioo a b)
  定义体: .ofFinset (Finset.Ioo a b) fun _ => by simp

@[simp, to_dual self]

Depends on / 依赖: Finset, Finset.Ioo, ofFinset
-/
instance instFintypeIoo : Fintype (Ioo a b) := .ofFinset (Finset.Ioo a b) fun _ => by simp

@[simp, to_dual self]
/--
lemma `finite_Icc` / 引理 `finite_Icc`

English:
lemma finite_Icc
  statement: (Icc a b).Finite
  proof: (Icc a b).toFinite

@[to_dual (reorder := a b) (attr := simp)]

中文:
引理 finite_Icc
  结论: (Icc a b).Finite
  证明: (Icc a b).toFinite

@[to_dual (reorder := a b) (attr := simp)]

Depends on / 依赖: toFinite
-/
lemma finite_Icc : (Icc a b).Finite := (Icc a b).toFinite

@[to_dual (reorder := a b) (attr := simp)]
/--
lemma `finite_Ico` / 引理 `finite_Ico`

English:
lemma finite_Ico
  statement: (Ico a b).Finite
  proof: (Ico a b).toFinite

@[simp, to_dual self]

中文:
引理 finite_Ico
  结论: (Ico a b).Finite
  证明: (Ico a b).toFinite

@[simp, to_dual self]

Depends on / 依赖: toFinite
-/
lemma finite_Ico : (Ico a b).Finite := (Ico a b).toFinite

@[simp, to_dual self]
/--
lemma `finite_Ioo` / 引理 `finite_Ioo`

English:
lemma finite_Ioo
  statement: (Ioo a b).Finite
  proof: (Ioo a b).toFinite

中文:
引理 finite_Ioo
  结论: (Ioo a b).Finite
  证明: (Ioo a b).toFinite

Depends on / 依赖: toFinite
-/
lemma finite_Ioo : (Ioo a b).Finite := (Ioo a b).toFinite

end Preorder

section OrderTop

variable [Preorder α] [LocallyFiniteOrderTop α] (a : α)

@[to_dual]
/--
Instance `instFintypeIci` / 实例 `instFintypeIci`

English:
instance instFintypeIci
  signature: : Fintype (Ici a)
  body: .ofFinset (Finset.Ici a) fun _ => Finset.mem_Ici

@[to_dual]

中文:
实例 instFintypeIci
  签名: : Fintype (Ici a)
  定义体: .ofFinset (Finset.Ici a) fun _ => Finset.mem_Ici

@[to_dual]

Depends on / 依赖: Finset, Finset.Ici, Finset.mem_Ici, mem_Ici, ofFinset
-/
instance instFintypeIci : Fintype (Ici a) := .ofFinset (Finset.Ici a) fun _ => Finset.mem_Ici

@[to_dual]
/--
Instance `instFintypeIoi` / 实例 `instFintypeIoi`

English:
instance instFintypeIoi
  signature: : Fintype (Ioi a)
  body: .ofFinset (Finset.Ioi a) fun _ => Finset.mem_Ioi

中文:
实例 instFintypeIoi
  签名: : Fintype (Ioi a)
  定义体: .ofFinset (Finset.Ioi a) fun _ => Finset.mem_Ioi

Depends on / 依赖: Finset, Finset.Ioi, Finset.mem_Ioi, mem_Ioi, ofFinset
-/
instance instFintypeIoi : Fintype (Ioi a) := .ofFinset (Finset.Ioi a) fun _ => Finset.mem_Ioi

/--
lemma `finite_Ici` / 引理 `finite_Ici`

English:
lemma finite_Ici
  statement: (Ici a).Finite
  proof: (Ici a).toFinite

中文:
引理 finite_Ici
  结论: (Ici a).Finite
  证明: (Ici a).toFinite
-/
@[to_dual (attr := simp)] lemma finite_Ici : (Ici a).Finite := (Ici a).toFinite
/--
lemma `finite_Ioi` / 引理 `finite_Ioi`

English:
lemma finite_Ioi
  statement: (Ioi a).Finite
  proof: (Ioi a).toFinite

中文:
引理 finite_Ioi
  结论: (Ioi a).Finite
  证明: (Ioi a).toFinite
-/
@[to_dual (attr := simp)] lemma finite_Ioi : (Ioi a).Finite := (Ioi a).toFinite

end OrderTop

section Lattice
variable [Lattice α] [LocallyFiniteOrder α] (a b : α)

/--
Instance `fintypeUIcc` / 实例 `fintypeUIcc`

English:
instance fintypeUIcc
  signature: : Fintype (uIcc a b)
  body: Fintype.ofFinset (Finset.uIcc a b) fun _ => Finset.mem_uIcc

中文:
实例 fintypeUIcc
  签名: : Fintype (uIcc a b)
  定义体: Fintype.ofFinset (Finset.uIcc a b) fun _ => Finset.mem_uIcc

Depends on / 依赖: Finset, Finset.mem_uIcc, Finset.uIcc, Fintype, Fintype.ofFinset, mem_uIcc, ofFinset
-/
instance fintypeUIcc : Fintype (uIcc a b) :=
  Fintype.ofFinset (Finset.uIcc a b) fun _ => Finset.mem_uIcc

/--
lemma `finite_uIcc` / 引理 `finite_uIcc`

English:
lemma finite_uIcc
  statement: (uIcc a b).Finite
  proof: (uIcc _ _).toFinite

@[deprecated (since := "2026-02-03")] alias finite_interval := finite_uIcc

中文:
引理 finite_uIcc
  结论: (uIcc a b).Finite
  证明: (uIcc _ _).toFinite

@[deprecated (since := "2026-02-03")] alias finite_interval := finite_uIcc
-/
@[simp] lemma finite_uIcc : (uIcc a b).Finite := (uIcc _ _).toFinite

@[deprecated (since := "2026-02-03")] alias finite_interval := finite_uIcc

end Lattice

end Set

/-! ### Instances -/

section Preorder

variable [Preorder α] [Preorder β]

/-- A noncomputable constructor from the finiteness of all closed intervals. -/
@[instance_reducible]
/--
Definition of `LocallyFiniteOrder.ofFiniteIcc` / `LocallyFiniteOrder.ofFiniteIcc` 的定义

English:
definition LocallyFiniteOrder.ofFiniteIcc
  signature: (h : forall a b : α, (Set.Icc a b).Finite)
  body: @LocallyFiniteOrder.ofIcc' α _ (Classical.decRel _) (fun a b => (h a b).toFinset) fun a b x => by
    rw [Set.Finite.mem_toFinset]; rw [Set.mem_Icc]

中文:
定义 LocallyFiniteOrder.ofFiniteIcc
  签名: (h : 对任意 a b : α, (Set.Icc a b).Finite)
  定义体: @LocallyFiniteOrder.ofIcc' α _ (Classical.decRel _) (fun a b => (h a b).toFinset) fun a b x => by
    rw [Set.Finite.mem_toFinset]; rw [Set.mem_Icc]

Depends on / 依赖: Classical, Classical.decRel, Finite, LocallyFiniteOrder, LocallyFiniteOrder.ofIcc, Set.Finite.mem_toFinset, Set.mem_Icc, decRel, mem_Icc, mem_toFinset, toFinset
-/
noncomputable def LocallyFiniteOrder.ofFiniteIcc (h : forall a b : α, (Set.Icc a b).Finite) :
    LocallyFiniteOrder α :=
  @LocallyFiniteOrder.ofIcc' α _ (Classical.decRel _) (fun a b => (h a b).toFinset) fun a b x => by
    rw [Set.Finite.mem_toFinset]; rw [Set.mem_Icc]

/--
Definition of `Fintype.toLocallyFiniteOrder` / `Fintype.toLocallyFiniteOrder` 的定义

English:
abbreviation Fintype.toLocallyFiniteOrder
  signature: [Fintype α] [DecidableLT α] [DecidableLE α]
  body: (Set.Icc a b).toFinset
  finsetIco a b := (Set.Ico a b).toFinset
  finsetIoc a b := (Set.Ioc a b).toFinset
  finsetIoo a b := (Set.Ioo a b).toFinset
  finset_mem_Icc a b x := by simp only [Set.mem_toFinset, Set.mem_Icc]
  finset_mem_Ico a b x := by simp only [Set.mem_toFinset, Set.mem_Ico]
  finset_

中文:
缩写 Fintype.toLocallyFiniteOrder
  签名: [Fintype α] [DecidableLT α] [DecidableLE α]
  定义体: (Set.Icc a b).toFinset
  finsetIco a b := (Set.Ico a b).toFinset
  finsetIoc a b := (Set.Ioc a b).toFinset
  finsetIoo a b := (Set.Ioo a b).toFinset
  finset_mem_Icc a b x := by simp only [Set.mem_toFinset, Set.mem_Icc]
  finset_mem_Ico a b x := by simp only [Set.mem_toFinset, Set.mem_Ico]
  finset_

Depends on / 依赖: Set.Icc, toFinset
-/
abbrev Fintype.toLocallyFiniteOrder [Fintype α] [DecidableLT α] [DecidableLE α] :
    LocallyFiniteOrder α where
  finsetIcc a b := (Set.Icc a b).toFinset
  finsetIco a b := (Set.Ico a b).toFinset
  finsetIoc a b := (Set.Ioc a b).toFinset
  finsetIoo a b := (Set.Ioo a b).toFinset
  finset_mem_Icc a b x := by simp only [Set.mem_toFinset, Set.mem_Icc]
  finset_mem_Ico a b x := by simp only [Set.mem_toFinset, Set.mem_Ico]
  finset_mem_Ioc a b x := by simp only [Set.mem_toFinset, Set.mem_Ioc]
  finset_mem_Ioo a b x := by simp only [Set.mem_toFinset, Set.mem_Ioo]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Subsingleton (LocallyFiniteOrder α)
  body: Subsingleton.intro fun h₀ h₁ => by
    obtain ⟨h₀_finset_Icc, h₀_finset_Ico, h₀_finset_Ioc, h₀_finset_Ioo,
      h₀_finset_mem_Icc, h₀_finset_mem_Ico, h₀_finset_mem_Ioc, h₀_finset_mem_Ioo⟩ := h₀
    obtain ⟨h₁_finset_Icc, h₁_finset_Ico, h₁_finset_Ioc, h₁_finset_Ioo,
      h₁_finset_mem_Icc, h₁_finse

中文:
实例 :
  签名: Subsingleton (LocallyFiniteOrder α)
  定义体: Subsingleton.intro fun h₀ h₁ => by
    obtain ⟨h₀_finset_Icc, h₀_finset_Ico, h₀_finset_Ioc, h₀_finset_Ioo,
      h₀_finset_mem_Icc, h₀_finset_mem_Ico, h₀_finset_mem_Ioc, h₀_finset_mem_Ioo⟩ := h₀
    obtain ⟨h₁_finset_Icc, h₁_finset_Ico, h₁_finset_Ioc, h₁_finset_Ioo,
      h₁_finset_mem_Icc, h₁_finse

Depends on / 依赖: Subsingleton, Subsingleton.intro
-/
instance : Subsingleton (LocallyFiniteOrder α) :=
  Subsingleton.intro fun h₀ h₁ => by
    obtain ⟨h₀_finset_Icc, h₀_finset_Ico, h₀_finset_Ioc, h₀_finset_Ioo,
      h₀_finset_mem_Icc, h₀_finset_mem_Ico, h₀_finset_mem_Ioc, h₀_finset_mem_Ioo⟩ := h₀
    obtain ⟨h₁_finset_Icc, h₁_finset_Ico, h₁_finset_Ioc, h₁_finset_Ioo,
      h₁_finset_mem_Icc, h₁_finset_mem_Ico, h₁_finset_mem_Ioc, h₁_finset_mem_Ioo⟩ := h₁
    have hIcc : h₀_finset_Icc = h₁_finset_Icc := by
      ext a b x
      rw [h₀_finset_mem_Icc]; rw [h₁_finset_mem_Icc]
    have hIco : h₀_finset_Ico = h₁_finset_Ico := by
      ext a b x
      rw [h₀_finset_mem_Ico]; rw [h₁_finset_mem_Ico]
    have hIoc : h₀_finset_Ioc = h₁_finset_Ioc := by
      ext a b x
      rw [h₀_finset_mem_Ioc]; rw [h₁_finset_mem_Ioc]
    have hIoo : h₀_finset_Ioo = h₁_finset_Ioo := by
      ext a b x
      rw [h₀_finset_mem_Ioo]; rw [h₁_finset_mem_Ioo]
    simp_rw [hIcc, hIco, hIoc, hIoo]

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Subsingleton (LocallyFiniteOrderTop α)
  body: Subsingleton.intro fun h₀ h₁ => by
    obtain ⟨h₀_finset_Ioi, h₀_finset_Ici, h₀_finset_mem_Ici, h₀_finset_mem_Ioi⟩ := h₀
    obtain ⟨h₁_finset_Ioi, h₁_finset_Ici, h₁_finset_mem_Ici, h₁_finset_mem_Ioi⟩ := h₁
    have hIci : h₀_finset_Ici = h₁_finset_Ici := by
      ext a b
      rw [h₀_finset_mem_Ici

中文:
实例 :
  签名: Subsingleton (LocallyFiniteOrderTop α)
  定义体: Subsingleton.intro fun h₀ h₁ => by
    obtain ⟨h₀_finset_Ioi, h₀_finset_Ici, h₀_finset_mem_Ici, h₀_finset_mem_Ioi⟩ := h₀
    obtain ⟨h₁_finset_Ioi, h₁_finset_Ici, h₁_finset_mem_Ici, h₁_finset_mem_Ioi⟩ := h₁
    have hIci : h₀_finset_Ici = h₁_finset_Ici := by
      ext a b
      rw [h₀_finset_mem_Ici

Depends on / 依赖: Subsingleton, Subsingleton.intro, simp_rw
-/
instance : Subsingleton (LocallyFiniteOrderTop α) :=
  Subsingleton.intro fun h₀ h₁ => by
    obtain ⟨h₀_finset_Ioi, h₀_finset_Ici, h₀_finset_mem_Ici, h₀_finset_mem_Ioi⟩ := h₀
    obtain ⟨h₁_finset_Ioi, h₁_finset_Ici, h₁_finset_mem_Ici, h₁_finset_mem_Ioi⟩ := h₁
    have hIci : h₀_finset_Ici = h₁_finset_Ici := by
      ext a b
      rw [h₀_finset_mem_Ici]; rw [h₁_finset_mem_Ici]
    have hIoi : h₀_finset_Ioi = h₁_finset_Ioi := by
      ext a b
      rw [h₀_finset_mem_Ioi]; rw [h₁_finset_mem_Ioi]
    simp_rw [hIci, hIoi]

-- Should this be called `LocallyFiniteOrder.lift`?
/-- Given an order embedding `α ↪o β`, pulls back the `LocallyFiniteOrder` on `β` to `α`. -/
@[instance_reducible]
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def OrderEmbedding.locallyFiniteOrder [LocallyFiniteOrder β] (f : α ↪o β)
  body: (Icc (f a) (f b)).preimage f f.toEmbedding.injective.injOn
  finsetIco a b := (Ico (f a) (f b)).preimage f f.toEmbedding.injective.injOn
  finsetIoc a b := (Ioc (f a) (f b)).preimage f f.toEmbedding.injective.injOn
  finsetIoo a b := (Ioo (f a) (f b)).preimage f f.toEmbedding.injective.injOn
  finse

中文:
定义 noncomputable
  签名: def OrderEmbedding.locallyFiniteOrder [LocallyFiniteOrder β] (f : α ↪o β)
  定义体: (Icc (f a) (f b)).preimage f f.toEmbedding.injective.injOn
  finsetIco a b := (Ico (f a) (f b)).preimage f f.toEmbedding.injective.injOn
  finsetIoc a b := (Ioc (f a) (f b)).preimage f f.toEmbedding.injective.injOn
  finsetIoo a b := (Ioo (f a) (f b)).preimage f f.toEmbedding.injective.injOn
  finse
-/
protected noncomputable def OrderEmbedding.locallyFiniteOrder [LocallyFiniteOrder β] (f : α ↪o β) :
    LocallyFiniteOrder α where
  finsetIcc a b := (Icc (f a) (f b)).preimage f f.toEmbedding.injective.injOn
  finsetIco a b := (Ico (f a) (f b)).preimage f f.toEmbedding.injective.injOn
  finsetIoc a b := (Ioc (f a) (f b)).preimage f f.toEmbedding.injective.injOn
  finsetIoo a b := (Ioo (f a) (f b)).preimage f f.toEmbedding.injective.injOn
  finset_mem_Icc a b x := by rw [mem_preimage, mem_Icc, f.le_iff_le, f.le_iff_le]
  finset_mem_Ico a b x := by rw [mem_preimage, mem_Ico, f.le_iff_le, f.lt_iff_lt]
  finset_mem_Ioc a b x := by rw [mem_preimage, mem_Ioc, f.lt_iff_lt, f.le_iff_le]
  finset_mem_Ioo a b x := by rw [mem_preimage, mem_Ioo, f.lt_iff_lt, f.lt_iff_lt]

/-! ### `OrderDual` -/

open OrderDual

section LocallyFiniteOrder

variable [LocallyFiniteOrder α] (a b : α)

/--
Instance `OrderDual.instLocallyFiniteOrder` / 实例 `OrderDual.instLocallyFiniteOrder`

English:
instance OrderDual.instLocallyFiniteOrder
  signature: : LocallyFiniteOrder αᵒᵈ where
  body: @Icc α _ _ (ofDual b) (ofDual a)
  finsetIco a b := @Ioc α _ _ (ofDual b) (ofDual a)
  finsetIoc a b := @Ico α _ _ (ofDual b) (ofDual a)
  finsetIoo a b := @Ioo α _ _ (ofDual b) (ofDual a)
  finset_mem_Icc _ _ _ := (mem_Icc (α := α)).trans and_comm
  finset_mem_Ico _ _ _ := (mem_Ioc (α := α)).trans 

中文:
实例 OrderDual.instLocallyFiniteOrder
  签名: : LocallyFiniteOrder αᵒᵈ where
  定义体: @Icc α _ _ (ofDual b) (ofDual a)
  finsetIco a b := @Ioc α _ _ (ofDual b) (ofDual a)
  finsetIoc a b := @Ico α _ _ (ofDual b) (ofDual a)
  finsetIoo a b := @Ioo α _ _ (ofDual b) (ofDual a)
  finset_mem_Icc _ _ _ := (mem_Icc (α := α)).trans and_comm
  finset_mem_Ico _ _ _ := (mem_Ioc (α := α)).trans 

Depends on / 依赖: ofDual
-/
instance OrderDual.instLocallyFiniteOrder : LocallyFiniteOrder αᵒᵈ where
  finsetIcc a b := @Icc α _ _ (ofDual b) (ofDual a)
  finsetIco a b := @Ioc α _ _ (ofDual b) (ofDual a)
  finsetIoc a b := @Ico α _ _ (ofDual b) (ofDual a)
  finsetIoo a b := @Ioo α _ _ (ofDual b) (ofDual a)
  finset_mem_Icc _ _ _ := (mem_Icc (α := α)).trans and_comm
  finset_mem_Ico _ _ _ := (mem_Ioc (α := α)).trans and_comm
  finset_mem_Ioc _ _ _ := (mem_Ico (α := α)).trans and_comm
  finset_mem_Ioo _ _ _ := (mem_Ioo (α := α)).trans and_comm

@[to_dual self]
/--
lemma `Finset.Icc_orderDual_def` / 引理 `Finset.Icc_orderDual_def`

English:
lemma Finset.Icc_orderDual_def
  given: (a b : αᵒᵈ)
  proof: map_refl.symm

@[to_dual (reorder := a b)]

中文:
引理 Finset.Icc_orderDual_def
  条件: (a b : αᵒᵈ)
  证明: map_refl.symm

@[to_dual (reorder := a b)]

Depends on / 依赖: map_refl, map_refl.symm
-/
lemma Finset.Icc_orderDual_def (a b : αᵒᵈ) :
    Icc a b = (Icc (ofDual b) (ofDual a)).map toDual.toEmbedding := map_refl.symm

@[to_dual (reorder := a b)]
/--
lemma `Finset.Ico_orderDual_def` / 引理 `Finset.Ico_orderDual_def`

English:
lemma Finset.Ico_orderDual_def
  given: (a b : αᵒᵈ)
  proof: map_refl.symm

@[to_dual self]

中文:
引理 Finset.Ico_orderDual_def
  条件: (a b : αᵒᵈ)
  证明: map_refl.symm

@[to_dual self]

Depends on / 依赖: map_refl, map_refl.symm
-/
lemma Finset.Ico_orderDual_def (a b : αᵒᵈ) :
    Ico a b = (Ioc (ofDual b) (ofDual a)).map toDual.toEmbedding := map_refl.symm

@[to_dual self]
/--
lemma `Finset.Ioo_orderDual_def` / 引理 `Finset.Ioo_orderDual_def`

English:
lemma Finset.Ioo_orderDual_def
  given: (a b : αᵒᵈ)
  proof: map_refl.symm

@[to_dual self]

中文:
引理 Finset.Ioo_orderDual_def
  条件: (a b : αᵒᵈ)
  证明: map_refl.symm

@[to_dual self]

Depends on / 依赖: map_refl, map_refl.symm
-/
lemma Finset.Ioo_orderDual_def (a b : αᵒᵈ) :
    Ioo a b = (Ioo (ofDual b) (ofDual a)).map toDual.toEmbedding := map_refl.symm

@[to_dual self]
/--
lemma `Finset.Icc_toDual` / 引理 `Finset.Icc_toDual`

English:
lemma Finset.Icc_toDual
  statement: Icc (toDual a) (toDual b) = (Icc b a).map toDual.toEmbedding
  proof: map_refl.symm

@[to_dual (reorder := a b)]

中文:
引理 Finset.Icc_toDual
  结论: Icc (toDual a) (toDual b) = (Icc b a).map toDual.toEmbedding
  证明: map_refl.symm

@[to_dual (reorder := a b)]

Depends on / 依赖: map_refl, map_refl.symm
-/
lemma Finset.Icc_toDual : Icc (toDual a) (toDual b) = (Icc b a).map toDual.toEmbedding :=
  map_refl.symm

@[to_dual (reorder := a b)]
/--
lemma `Finset.Ico_toDual` / 引理 `Finset.Ico_toDual`

English:
lemma Finset.Ico_toDual
  statement: Ico (toDual a) (toDual b) = (Ioc b a).map toDual.toEmbedding
  proof: map_refl.symm

@[to_dual self]

中文:
引理 Finset.Ico_toDual
  结论: Ico (toDual a) (toDual b) = (Ioc b a).map toDual.toEmbedding
  证明: map_refl.symm

@[to_dual self]

Depends on / 依赖: map_refl, map_refl.symm
-/
lemma Finset.Ico_toDual : Ico (toDual a) (toDual b) = (Ioc b a).map toDual.toEmbedding :=
  map_refl.symm

@[to_dual self]
/--
lemma `Finset.Ioo_toDual` / 引理 `Finset.Ioo_toDual`

English:
lemma Finset.Ioo_toDual
  statement: Ioo (toDual a) (toDual b) = (Ioo b a).map toDual.toEmbedding
  proof: map_refl.symm

@[to_dual self]

中文:
引理 Finset.Ioo_toDual
  结论: Ioo (toDual a) (toDual b) = (Ioo b a).map toDual.toEmbedding
  证明: map_refl.symm

@[to_dual self]

Depends on / 依赖: map_refl, map_refl.symm
-/
lemma Finset.Ioo_toDual : Ioo (toDual a) (toDual b) = (Ioo b a).map toDual.toEmbedding :=
  map_refl.symm

@[to_dual self]
/--
lemma `Finset.Icc_ofDual` / 引理 `Finset.Icc_ofDual`

English:
lemma Finset.Icc_ofDual
  given: (a b : αᵒᵈ)
  proof: map_refl.symm

@[to_dual (reorder := a b)]

中文:
引理 Finset.Icc_ofDual
  条件: (a b : αᵒᵈ)
  证明: map_refl.symm

@[to_dual (reorder := a b)]

Depends on / 依赖: map_refl, map_refl.symm
-/
lemma Finset.Icc_ofDual (a b : αᵒᵈ) :
    Icc (ofDual a) (ofDual b) = (Icc b a).map ofDual.toEmbedding := map_refl.symm

@[to_dual (reorder := a b)]
/--
lemma `Finset.Ico_ofDual` / 引理 `Finset.Ico_ofDual`

English:
lemma Finset.Ico_ofDual
  given: (a b : αᵒᵈ)
  proof: map_refl.symm

@[to_dual self]

中文:
引理 Finset.Ico_ofDual
  条件: (a b : αᵒᵈ)
  证明: map_refl.symm

@[to_dual self]

Depends on / 依赖: map_refl, map_refl.symm
-/
lemma Finset.Ico_ofDual (a b : αᵒᵈ) :
    Ico (ofDual a) (ofDual b) = (Ioc b a).map ofDual.toEmbedding := map_refl.symm

@[to_dual self]
/--
lemma `Finset.Ioo_ofDual` / 引理 `Finset.Ioo_ofDual`

English:
lemma Finset.Ioo_ofDual
  given: (a b : αᵒᵈ)
  proof: map_refl.symm

中文:
引理 Finset.Ioo_ofDual
  条件: (a b : αᵒᵈ)
  证明: map_refl.symm

Depends on / 依赖: map_refl, map_refl.symm
-/
lemma Finset.Ioo_ofDual (a b : αᵒᵈ) :
    Ioo (ofDual a) (ofDual b) = (Ioo b a).map ofDual.toEmbedding := map_refl.symm

end LocallyFiniteOrder

section LocallyFiniteOrderTop

variable [LocallyFiniteOrderTop α]

/-- Note we define `Iic (toDual a)` as `Ici a` (which has type `Finset α` not `Finset αᵒᵈ`!)
instead of `(Ici a).map toDual.toEmbedding` as this means the following is defeq:
```
lemma this : (Iic (toDual (toDual a)) :) = (Iic a :) := rfl
```
-/
@[to_dual
/-- Note we define `Ici (toDual a)` as `Iic a` (which has type `Finset α` not `Finset αᵒᵈ`!)
instead of `(Iic a).map toDual.toEmbedding` as this means the following is defeq:
```
lemma this : (Ici (toDual (toDual a)) :) = (Ici a :) := rfl
```
-/]
/--
Instance `OrderDual.instLocallyFiniteOrderBot` / 实例 `OrderDual.instLocallyFiniteOrderBot`

English:
instance OrderDual.instLocallyFiniteOrderBot
  signature: : LocallyFiniteOrderBot αᵒᵈ where
  body: @Ici α _ _ (ofDual a)
  finsetIio a := @Ioi α _ _ (ofDual a)
  finset_mem_Iic _ _ := mem_Ici (α := α)
  finset_mem_Iio _ _ := mem_Ioi (α := α)

@[to_dual]

中文:
实例 OrderDual.instLocallyFiniteOrderBot
  签名: : LocallyFiniteOrderBot αᵒᵈ where
  定义体: @Ici α _ _ (ofDual a)
  finsetIio a := @Ioi α _ _ (ofDual a)
  finset_mem_Iic _ _ := mem_Ici (α := α)
  finset_mem_Iio _ _ := mem_Ioi (α := α)

@[to_dual]

Depends on / 依赖: ofDual
-/
instance OrderDual.instLocallyFiniteOrderBot : LocallyFiniteOrderBot αᵒᵈ where
  finsetIic a := @Ici α _ _ (ofDual a)
  finsetIio a := @Ioi α _ _ (ofDual a)
  finset_mem_Iic _ _ := mem_Ici (α := α)
  finset_mem_Iio _ _ := mem_Ioi (α := α)

@[to_dual]
/--
lemma `Iic_orderDual_def` / 引理 `Iic_orderDual_def`

English:
lemma Iic_orderDual_def
  given: (a : αᵒᵈ)
  statement: Iic a = (Ici (ofDual a)).map toDual.toEmbedding
  proof: map_refl.symm

@[to_dual]

中文:
引理 Iic_orderDual_def
  条件: (a : αᵒᵈ)
  结论: Iic a = (Ici (ofDual a)).map toDual.toEmbedding
  证明: map_refl.symm

@[to_dual]

Depends on / 依赖: map_refl, map_refl.symm
-/
lemma Iic_orderDual_def (a : αᵒᵈ) : Iic a = (Ici (ofDual a)).map toDual.toEmbedding := map_refl.symm

@[to_dual]
/--
lemma `Iio_orderDual_def` / 引理 `Iio_orderDual_def`

English:
lemma Iio_orderDual_def
  given: (a : αᵒᵈ)
  statement: Iio a = (Ioi (ofDual a)).map toDual.toEmbedding
  proof: map_refl.symm

@[to_dual]

中文:
引理 Iio_orderDual_def
  条件: (a : αᵒᵈ)
  结论: Iio a = (Ioi (ofDual a)).map toDual.toEmbedding
  证明: map_refl.symm

@[to_dual]

Depends on / 依赖: map_refl, map_refl.symm
-/
lemma Iio_orderDual_def (a : αᵒᵈ) : Iio a = (Ioi (ofDual a)).map toDual.toEmbedding := map_refl.symm

@[to_dual]
/--
lemma `Finset.Iic_toDual` / 引理 `Finset.Iic_toDual`

English:
lemma Finset.Iic_toDual
  given: (a : α)
  statement: Iic (toDual a) = (Ici a).map toDual.toEmbedding
  proof: map_refl.symm

@[to_dual]

中文:
引理 Finset.Iic_toDual
  条件: (a : α)
  结论: Iic (toDual a) = (Ici a).map toDual.toEmbedding
  证明: map_refl.symm

@[to_dual]

Depends on / 依赖: map_refl, map_refl.symm
-/
lemma Finset.Iic_toDual (a : α) : Iic (toDual a) = (Ici a).map toDual.toEmbedding :=
  map_refl.symm

@[to_dual]
/--
lemma `Finset.Iio_toDual` / 引理 `Finset.Iio_toDual`

English:
lemma Finset.Iio_toDual
  given: (a : α)
  statement: Iio (toDual a) = (Ioi a).map toDual.toEmbedding
  proof: map_refl.symm

@[to_dual]

中文:
引理 Finset.Iio_toDual
  条件: (a : α)
  结论: Iio (toDual a) = (Ioi a).map toDual.toEmbedding
  证明: map_refl.symm

@[to_dual]

Depends on / 依赖: map_refl, map_refl.symm
-/
lemma Finset.Iio_toDual (a : α) : Iio (toDual a) = (Ioi a).map toDual.toEmbedding :=
  map_refl.symm

@[to_dual]
/--
lemma `Finset.Ici_ofDual` / 引理 `Finset.Ici_ofDual`

English:
lemma Finset.Ici_ofDual
  given: (a : αᵒᵈ)
  statement: Ici (ofDual a) = (Iic a).map ofDual.toEmbedding
  proof: map_refl.symm

@[to_dual]

中文:
引理 Finset.Ici_ofDual
  条件: (a : αᵒᵈ)
  结论: Ici (ofDual a) = (Iic a).map ofDual.toEmbedding
  证明: map_refl.symm

@[to_dual]

Depends on / 依赖: map_refl, map_refl.symm
-/
lemma Finset.Ici_ofDual (a : αᵒᵈ) : Ici (ofDual a) = (Iic a).map ofDual.toEmbedding :=
  map_refl.symm

@[to_dual]
/--
lemma `Finset.Ioi_ofDual` / 引理 `Finset.Ioi_ofDual`

English:
lemma Finset.Ioi_ofDual
  given: (a : αᵒᵈ)
  statement: Ioi (ofDual a) = (Iio a).map ofDual.toEmbedding
  proof: map_refl.symm

中文:
引理 Finset.Ioi_ofDual
  条件: (a : αᵒᵈ)
  结论: Ioi (ofDual a) = (Iio a).map ofDual.toEmbedding
  证明: map_refl.symm

Depends on / 依赖: map_refl, map_refl.symm
-/
lemma Finset.Ioi_ofDual (a : αᵒᵈ) : Ioi (ofDual a) = (Iio a).map ofDual.toEmbedding :=
  map_refl.symm

end LocallyFiniteOrderTop

/-! ### `Prod` -/

section LocallyFiniteOrder
variable [LocallyFiniteOrder α] [LocallyFiniteOrder β] [DecidableLE (α × β)]

/--
Instance `Prod.instLocallyFiniteOrder` / 实例 `Prod.instLocallyFiniteOrder`

English:
instance Prod.instLocallyFiniteOrder
  signature: : LocallyFiniteOrder (α × β)
  body: LocallyFiniteOrder.ofIcc' (α × β) (fun x y => Icc x.1 y.1 ×ˢ Icc x.2 y.2) fun a b x => by
    rw [mem_product]; rw [mem_Icc]; rw [mem_Icc]; rw [and_and_and_comm]; rw [le_def]; rw [le_def]

@[to_dual self]

中文:
实例 Prod.instLocallyFiniteOrder
  签名: : LocallyFiniteOrder (α × β)
  定义体: LocallyFiniteOrder.ofIcc' (α × β) (fun x y => Icc x.1 y.1 ×ˢ Icc x.2 y.2) fun a b x => by
    rw [mem_product]; rw [mem_Icc]; rw [mem_Icc]; rw [and_and_and_comm]; rw [le_def]; rw [le_def]

@[to_dual self]

Depends on / 依赖: LocallyFiniteOrder, LocallyFiniteOrder.ofIcc, and_and_and_comm, le_def, mem_Icc, mem_product
-/
instance Prod.instLocallyFiniteOrder : LocallyFiniteOrder (α × β) :=
  LocallyFiniteOrder.ofIcc' (α × β) (fun x y => Icc x.1 y.1 ×ˢ Icc x.2 y.2) fun a b x => by
    rw [mem_product]; rw [mem_Icc]; rw [mem_Icc]; rw [and_and_and_comm]; rw [le_def]; rw [le_def]

@[to_dual self]
/--
lemma `Finset.Icc_prod_def` / 引理 `Finset.Icc_prod_def`

English:
lemma Finset.Icc_prod_def
  given: (x y : α × β)
  statement: Icc x y = Icc x.1 y.1 ×ˢ Icc x.2 y.2
  proof: rfl

@[to_dual self]

中文:
引理 Finset.Icc_prod_def
  条件: (x y : α × β)
  结论: Icc x y = Icc x.1 y.1 ×ˢ Icc x.2 y.2
  证明: rfl

@[to_dual self]
-/
lemma Finset.Icc_prod_def (x y : α × β) : Icc x y = Icc x.1 y.1 ×ˢ Icc x.2 y.2 := rfl

@[to_dual self]
/--
lemma `Finset.Icc_product_Icc` / 引理 `Finset.Icc_product_Icc`

English:
lemma Finset.Icc_product_Icc
  given: (a₁ a₂ : α) (b₁ b₂ : β)
  proof: rfl

@[to_dual self]

中文:
引理 Finset.Icc_product_Icc
  条件: (a₁ a₂ : α) (b₁ b₂ : β)
  证明: rfl

@[to_dual self]
-/
lemma Finset.Icc_product_Icc (a₁ a₂ : α) (b₁ b₂ : β) :
    Icc a₁ a₂ ×ˢ Icc b₁ b₂ = Icc (a₁, b₁) (a₂, b₂) := rfl

@[to_dual self]
/--
lemma `Finset.card_Icc_prod` / 引理 `Finset.card_Icc_prod`

English:
lemma Finset.card_Icc_prod
  given: (x y : α × β)
  statement: #(Icc x y) = #(Icc x.1 y.1) * #(Icc x.2 y.2)
  proof: card_product ..

中文:
引理 Finset.card_Icc_prod
  条件: (x y : α × β)
  结论: #(Icc x y) = #(Icc x.1 y.1) * #(Icc x.2 y.2)
  证明: card_product ..

Depends on / 依赖: card_product
-/
lemma Finset.card_Icc_prod (x y : α × β) : #(Icc x y) = #(Icc x.1 y.1) * #(Icc x.2 y.2) :=
  card_product ..

end LocallyFiniteOrder

section LocallyFiniteOrderTop
variable [LocallyFiniteOrderTop α] [LocallyFiniteOrderTop β] [DecidableLE (α × β)]

@[to_dual]
/--
Instance `Prod.instLocallyFiniteOrderTop` / 实例 `Prod.instLocallyFiniteOrderTop`

English:
instance Prod.instLocallyFiniteOrderTop
  signature: : LocallyFiniteOrderTop (α × β)
  body: LocallyFiniteOrderTop.ofIci' (α × β) (fun x => Ici x.1 ×ˢ Ici x.2) fun a x => by
    rw [mem_product]; rw [mem_Ici]; rw [mem_Ici]; rw [le_def]

@[to_dual]

中文:
实例 Prod.instLocallyFiniteOrderTop
  签名: : LocallyFiniteOrderTop (α × β)
  定义体: LocallyFiniteOrderTop.ofIci' (α × β) (fun x => Ici x.1 ×ˢ Ici x.2) fun a x => by
    rw [mem_product]; rw [mem_Ici]; rw [mem_Ici]; rw [le_def]

@[to_dual]

Depends on / 依赖: LocallyFiniteOrderTop, LocallyFiniteOrderTop.ofIci, le_def, mem_Ici, mem_product
-/
instance Prod.instLocallyFiniteOrderTop : LocallyFiniteOrderTop (α × β) :=
  LocallyFiniteOrderTop.ofIci' (α × β) (fun x => Ici x.1 ×ˢ Ici x.2) fun a x => by
    rw [mem_product]; rw [mem_Ici]; rw [mem_Ici]; rw [le_def]

@[to_dual]
/--
lemma `Finset.Ici_prod_def` / 引理 `Finset.Ici_prod_def`

English:
lemma Finset.Ici_prod_def
  given: (x : α × β)
  statement: Ici x = Ici x.1 ×ˢ Ici x.2
  proof: rfl

@[to_dual Iic_product_Iic]

中文:
引理 Finset.Ici_prod_def
  条件: (x : α × β)
  结论: Ici x = Ici x.1 ×ˢ Ici x.2
  证明: rfl

@[to_dual Iic_product_Iic]
-/
lemma Finset.Ici_prod_def (x : α × β) : Ici x = Ici x.1 ×ˢ Ici x.2 := rfl

@[to_dual Iic_product_Iic]
/--
lemma `Finset.Ici_product_Ici` / 引理 `Finset.Ici_product_Ici`

English:
lemma Finset.Ici_product_Ici
  given: (a : α) (b : β)
  statement: Ici a ×ˢ Ici b = Ici (a, b)
  proof: rfl

@[to_dual]

中文:
引理 Finset.Ici_product_Ici
  条件: (a : α) (b : β)
  结论: Ici a ×ˢ Ici b = Ici (a, b)
  证明: rfl

@[to_dual]
-/
lemma Finset.Ici_product_Ici (a : α) (b : β) : Ici a ×ˢ Ici b = Ici (a, b) := rfl

@[to_dual]
/--
lemma `Finset.card_Ici_prod` / 引理 `Finset.card_Ici_prod`

English:
lemma Finset.card_Ici_prod
  given: (x : α × β)
  statement: #(Ici x) = #(Ici x.1) * #(Ici x.2)
  proof: card_product _ _

中文:
引理 Finset.card_Ici_prod
  条件: (x : α × β)
  结论: #(Ici x) = #(Ici x.1) * #(Ici x.2)
  证明: card_product _ _

Depends on / 依赖: card_product
-/
lemma Finset.card_Ici_prod (x : α × β) : #(Ici x) = #(Ici x.1) * #(Ici x.2) :=
  card_product _ _

end LocallyFiniteOrderTop
end Preorder

section Lattice
variable [Lattice α] [Lattice β] [LocallyFiniteOrder α] [LocallyFiniteOrder β] [DecidableLE (α × β)]

/--
lemma `Finset.uIcc_prod_def` / 引理 `Finset.uIcc_prod_def`

English:
lemma Finset.uIcc_prod_def
  given: (x y : α × β)
  statement: uIcc x y = uIcc x.1 y.1 ×ˢ uIcc x.2 y.2
  proof: rfl

中文:
引理 Finset.uIcc_prod_def
  条件: (x y : α × β)
  结论: uIcc x y = uIcc x.1 y.1 ×ˢ uIcc x.2 y.2
  证明: rfl

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.cancelBaseChange, FaithfullyFlat, FaithfullyFlat.rTensor_reflects_triviality, IsScalarTower, IsScalarTower.of_algebraMap_smul, Module, Module.FaithfullyFlat.iff_flat_and_rTensor_reflects_triviality, Module.compHom, algebraMap, cancelBaseChange, compHom, iff_flat_and_rTensor_reflects_triviality, of_algebraMap_smul, rTensor_reflects_triviality, subsingleton, symm.subsingleton
-/
lemma Finset.uIcc_prod_def (x y : α × β) : uIcc x y = uIcc x.1 y.1 ×ˢ uIcc x.2 y.2 := rfl

/--
lemma `Finset.uIcc_product_uIcc` / 引理 `Finset.uIcc_product_uIcc`

English:
lemma Finset.uIcc_product_uIcc
  given: (a₁ a₂ : α) (b₁ b₂ : β)
  proof: rfl

中文:
引理 Finset.uIcc_product_uIcc
  条件: (a₁ a₂ : α) (b₁ b₂ : β)
  证明: rfl
-/
lemma Finset.uIcc_product_uIcc (a₁ a₂ : α) (b₁ b₂ : β) :
    uIcc a₁ a₂ ×ˢ uIcc b₁ b₂ = uIcc (a₁, b₁) (a₂, b₂) := rfl

/--
lemma `Finset.card_uIcc_prod` / 引理 `Finset.card_uIcc_prod`

English:
lemma Finset.card_uIcc_prod
  given: (x y : α × β)
  statement: #(uIcc x y) = #(uIcc x.1 y.1) * #(uIcc x.2 y.2)
  proof: card_product ..

中文:
引理 Finset.card_uIcc_prod
  条件: (x y : α × β)
  结论: #(uIcc x y) = #(uIcc x.1 y.1) * #(uIcc x.2 y.2)
  证明: card_product ..

Depends on / 依赖: card_product
-/
lemma Finset.card_uIcc_prod (x y : α × β) : #(uIcc x y) = #(uIcc x.1 y.1) * #(uIcc x.2 y.2) :=
  card_product ..

end Lattice

/-!
#### `WithTop`, `WithBot`

Adding a `⊤` to a locally finite `OrderTop` keeps it locally finite.
Adding a `⊥` to a locally finite `OrderBot` keeps it locally finite.
-/


namespace WithTop

/-- Given a finset on `α`, lift it to being a finset on `WithTop α`
using `WithTop.some` and then insert `⊤`. -/
@[to_dual /-- Given a finset on `α`, lift it to being a finset on `WithBot α`
using `WithBot.some` and then insert `⊥`. -/]
/--
Definition of `insertTop` / `insertTop` 的定义

English:
definition insertTop
  signature: : Finset α ↪o Finset (WithTop α)
  body: OrderEmbedding.ofMapLEIff
    (fun s => cons ⊤ (s.map Embedding.coeWithTop) <| by simp)
    (fun s t => by rw [cons_subset_cons, map_subset_map])

@[to_dual (attr := simp)]

中文:
定义 insertTop
  签名: : Finset α ↪o Finset (WithTop α)
  定义体: OrderEmbedding.ofMapLEIff
    (fun s => cons ⊤ (s.map Embedding.coeWithTop) <| by simp)
    (fun s t => by rw [cons_subset_cons, map_subset_map])

@[to_dual (attr := simp)]

Depends on / 依赖: Embedding, Embedding.coeWithTop, OrderEmbedding, OrderEmbedding.ofMapLEIff, coeWithTop, cons_subset_cons, map_subset_map, ofMapLEIff, s.map
-/
def insertTop : Finset α ↪o Finset (WithTop α) :=
  OrderEmbedding.ofMapLEIff
    (fun s => cons ⊤ (s.map Embedding.coeWithTop) <| by simp)
    (fun s t => by rw [cons_subset_cons, map_subset_map])

@[to_dual (attr := simp)]
/--
theorem `some_mem_insertTop` / 定理 `some_mem_insertTop`

English:
theorem some_mem_insertTop
  given: {s : Finset α} {a : α}
  statement: ↑a in insertTop s ↔ a in s
  proof: by
  simp [insertTop]

@[to_dual (attr := simp)]

中文:
定理 some_mem_insertTop
  条件: {s : Finset α} {a : α}
  结论: ↑a in insertTop s ↔ a in s
  证明: by
  simp [insertTop]

@[to_dual (attr := simp)]

Depends on / 依赖: insertTop
-/
theorem some_mem_insertTop {s : Finset α} {a : α} : ↑a in insertTop s ↔ a in s := by
  simp [insertTop]

@[to_dual (attr := simp)]
/--
theorem `top_mem_insertTop` / 定理 `top_mem_insertTop`

English:
theorem top_mem_insertTop
  given: {s : Finset α}
  statement: ⊤ in insertTop s
  proof: by
  simp [insertTop]

中文:
定理 top_mem_insertTop
  条件: {s : Finset α}
  结论: ⊤ in insertTop s
  证明: by
  simp [insertTop]

Depends on / 依赖: insertTop
-/
theorem top_mem_insertTop {s : Finset α} : ⊤ in insertTop s := by
  simp [insertTop]

variable (α) [PartialOrder α] [OrderTop α] [LocallyFiniteOrder α]

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LocallyFiniteOrder (WithTop α)
  body: match a, b with
    | ⊤, ⊤ => {⊤}
    | ⊤, (b : α) => ∅
    | (a : α), ⊤ => insertTop (Ici a)
    | (a : α), (b : α) => (Icc a b).map Embedding.coeWithTop
  finsetIco a b :=
    match a, b with
    | ⊤, _ => ∅
    | (a : α), ⊤ => (Ici a).map Embedding.coeWithTop
    | (a : α), (b : α) => (Ico a b).m

中文:
实例 :
  签名: LocallyFiniteOrder (WithTop α)
  定义体: match a, b with
    | ⊤, ⊤ => {⊤}
    | ⊤, (b : α) => ∅
    | (a : α), ⊤ => insertTop (Ici a)
    | (a : α), (b : α) => (Icc a b).map Embedding.coeWithTop
  finsetIco a b :=
    match a, b with
    | ⊤, _ => ∅
    | (a : α), ⊤ => (Ici a).map Embedding.coeWithTop
    | (a : α), (b : α) => (Ico a b).m

Depends on / 依赖: Embedding, Embedding.coeWithTop, coeWithTop, finsetIco, finsetIoc, finsetIoo, insertTop
-/
instance : LocallyFiniteOrder (WithTop α) where
  finsetIcc a b :=
    match a, b with
    | ⊤, ⊤ => {⊤}
    | ⊤, (b : α) => ∅
    | (a : α), ⊤ => insertTop (Ici a)
    | (a : α), (b : α) => (Icc a b).map Embedding.coeWithTop
  finsetIco a b :=
    match a, b with
    | ⊤, _ => ∅
    | (a : α), ⊤ => (Ici a).map Embedding.coeWithTop
    | (a : α), (b : α) => (Ico a b).map Embedding.coeWithTop
  finsetIoc a b :=
    match a, b with
    | ⊤, _ => ∅
    | (a : α), ⊤ => insertTop (Ioi a)
    | (a : α), (b : α) => (Ioc a b).map Embedding.coeWithTop
  finsetIoo a b :=
    match a, b with
    | ⊤, _ => ∅
    | (a : α), ⊤ => (Ioi a).map Embedding.coeWithTop
    | (a : α), (b : α) => (Ioo a b).map Embedding.coeWithTop
  finset_mem_Icc a b x := by
    cases a <;> cases b <;> cases x <;> simp
  finset_mem_Ico a b x := by
    cases a <;> cases b <;> cases x <;> simp
  finset_mem_Ioc a b x := by
    cases a <;> cases b <;> cases x <;> simp
  finset_mem_Ioo a b x := by
    cases a <;> cases b <;> cases x <;> simp

variable (a b : α)

@[to_dual Icc_bot_coe]
/--
theorem `Icc_coe_top` / 定理 `Icc_coe_top`

English:
theorem Icc_coe_top
  statement: Icc (a : WithTop α) ⊤ = insertNone (Ici a)
  proof: rfl

@[to_dual]

中文:
定理 Icc_coe_top
  结论: Icc (a : WithTop α) ⊤ = insertNone (Ici a)
  证明: rfl

@[to_dual]
-/
theorem Icc_coe_top : Icc (a : WithTop α) ⊤ = insertNone (Ici a) :=
  rfl

@[to_dual]
/--
theorem `Icc_coe_coe` / 定理 `Icc_coe_coe`

English:
theorem Icc_coe_coe
  statement: Icc (a : WithTop α) b = (Icc a b).map Embedding.some
  proof: rfl

@[to_dual Ioc_bot_coe]

中文:
定理 Icc_coe_coe
  结论: Icc (a : WithTop α) b = (Icc a b).map Embedding.some
  证明: rfl

@[to_dual Ioc_bot_coe]
-/
theorem Icc_coe_coe : Icc (a : WithTop α) b = (Icc a b).map Embedding.some :=
  rfl

@[to_dual Ioc_bot_coe]
/--
theorem `Ico_coe_top` / 定理 `Ico_coe_top`

English:
theorem Ico_coe_top
  statement: Ico (a : WithTop α) ⊤ = (Ici a).map Embedding.some
  proof: rfl

@[to_dual]

中文:
定理 Ico_coe_top
  结论: Ico (a : WithTop α) ⊤ = (Ici a).map Embedding.some
  证明: rfl

@[to_dual]
-/
theorem Ico_coe_top : Ico (a : WithTop α) ⊤ = (Ici a).map Embedding.some :=
  rfl

@[to_dual]
/--
theorem `Ico_coe_coe` / 定理 `Ico_coe_coe`

English:
theorem Ico_coe_coe
  statement: Ico (a : WithTop α) b = (Ico a b).map Embedding.some
  proof: rfl

@[to_dual Ico_bot_coe]

中文:
定理 Ico_coe_coe
  结论: Ico (a : WithTop α) b = (Ico a b).map Embedding.some
  证明: rfl

@[to_dual Ico_bot_coe]
-/
theorem Ico_coe_coe : Ico (a : WithTop α) b = (Ico a b).map Embedding.some :=
  rfl

@[to_dual Ico_bot_coe]
/--
theorem `Ioc_coe_top` / 定理 `Ioc_coe_top`

English:
theorem Ioc_coe_top
  statement: Ioc (a : WithTop α) ⊤ = insertNone (Ioi a)
  proof: rfl

@[to_dual]

中文:
定理 Ioc_coe_top
  结论: Ioc (a : WithTop α) ⊤ = insertNone (Ioi a)
  证明: rfl

@[to_dual]
-/
theorem Ioc_coe_top : Ioc (a : WithTop α) ⊤ = insertNone (Ioi a) :=
  rfl

@[to_dual]
/--
theorem `Ioc_coe_coe` / 定理 `Ioc_coe_coe`

English:
theorem Ioc_coe_coe
  statement: Ioc (a : WithTop α) b = (Ioc a b).map Embedding.some
  proof: rfl

@[to_dual Ioo_bot_coe]

中文:
定理 Ioc_coe_coe
  结论: Ioc (a : WithTop α) b = (Ioc a b).map Embedding.some
  证明: rfl

@[to_dual Ioo_bot_coe]
-/
theorem Ioc_coe_coe : Ioc (a : WithTop α) b = (Ioc a b).map Embedding.some :=
  rfl

@[to_dual Ioo_bot_coe]
/--
theorem `Ioo_coe_top` / 定理 `Ioo_coe_top`

English:
theorem Ioo_coe_top
  statement: Ioo (a : WithTop α) ⊤ = (Ioi a).map Embedding.some
  proof: rfl

@[to_dual]

中文:
定理 Ioo_coe_top
  结论: Ioo (a : WithTop α) ⊤ = (Ioi a).map Embedding.some
  证明: rfl

@[to_dual]
-/
theorem Ioo_coe_top : Ioo (a : WithTop α) ⊤ = (Ioi a).map Embedding.some :=
  rfl

@[to_dual]
/--
theorem `Ioo_coe_coe` / 定理 `Ioo_coe_coe`

English:
theorem Ioo_coe_coe
  statement: Ioo (a : WithTop α) b = (Ioo a b).map Embedding.some
  proof: rfl

中文:
定理 Ioo_coe_coe
  结论: Ioo (a : WithTop α) b = (Ioo a b).map Embedding.some
  证明: rfl
-/
theorem Ioo_coe_coe : Ioo (a : WithTop α) b = (Ioo a b).map Embedding.some :=
  rfl

end WithTop

namespace OrderIso

variable [Preorder α] [Preorder β]

/-! #### Transfer locally finite orders across order isomorphisms -/


-- See note [reducible non-instances]
/--
Definition of `locallyFiniteOrder` / `locallyFiniteOrder` 的定义

English:
abbreviation locallyFiniteOrder
  signature: [LocallyFiniteOrder β] (f : α ≃o β)
  body: (Icc (f a) (f b)).map f.symm.toEquiv.toEmbedding
  finsetIco a b := (Ico (f a) (f b)).map f.symm.toEquiv.toEmbedding
  finsetIoc a b := (Ioc (f a) (f b)).map f.symm.toEquiv.toEmbedding
  finsetIoo a b := (Ioo (f a) (f b)).map f.symm.toEquiv.toEmbedding
  finset_mem_Icc := by simp
  finset_mem_Ico :=

中文:
缩写 locallyFiniteOrder
  签名: [LocallyFiniteOrder β] (f : α ≃o β)
  定义体: (Icc (f a) (f b)).map f.symm.toEquiv.toEmbedding
  finsetIco a b := (Ico (f a) (f b)).map f.symm.toEquiv.toEmbedding
  finsetIoc a b := (Ioc (f a) (f b)).map f.symm.toEquiv.toEmbedding
  finsetIoo a b := (Ioo (f a) (f b)).map f.symm.toEquiv.toEmbedding
  finset_mem_Icc := by simp
  finset_mem_Ico :=

Depends on / 依赖: f.symm.toEquiv.toEmbedding, toEmbedding, toEquiv
-/
abbrev locallyFiniteOrder [LocallyFiniteOrder β] (f : α ≃o β) : LocallyFiniteOrder α where
  finsetIcc a b := (Icc (f a) (f b)).map f.symm.toEquiv.toEmbedding
  finsetIco a b := (Ico (f a) (f b)).map f.symm.toEquiv.toEmbedding
  finsetIoc a b := (Ioc (f a) (f b)).map f.symm.toEquiv.toEmbedding
  finsetIoo a b := (Ioo (f a) (f b)).map f.symm.toEquiv.toEmbedding
  finset_mem_Icc := by simp
  finset_mem_Ico := by simp
  finset_mem_Ioc := by simp
  finset_mem_Ioo := by simp

-- See note [reducible non-instances]
/-- Transfer `LocallyFiniteOrderTop` across an `OrderIso`. -/
@[to_dual /-- Transfer `LocallyFiniteOrderBot` across an `OrderIso`. -/]
/--
Definition of `locallyFiniteOrderTop` / `locallyFiniteOrderTop` 的定义

English:
abbreviation locallyFiniteOrderTop
  signature: [LocallyFiniteOrderTop β] (f : α ≃o β)
  body: (Ici (f a)).map f.symm.toEquiv.toEmbedding
  finsetIoi a := (Ioi (f a)).map f.symm.toEquiv.toEmbedding
  finset_mem_Ici := by simp
  finset_mem_Ioi := by simp

中文:
缩写 locallyFiniteOrderTop
  签名: [LocallyFiniteOrderTop β] (f : α ≃o β)
  定义体: (Ici (f a)).map f.symm.toEquiv.toEmbedding
  finsetIoi a := (Ioi (f a)).map f.symm.toEquiv.toEmbedding
  finset_mem_Ici := by simp
  finset_mem_Ioi := by simp

Depends on / 依赖: f.symm.toEquiv.toEmbedding, toEmbedding, toEquiv
-/
abbrev locallyFiniteOrderTop [LocallyFiniteOrderTop β] (f : α ≃o β) : LocallyFiniteOrderTop α where
  finsetIci a := (Ici (f a)).map f.symm.toEquiv.toEmbedding
  finsetIoi a := (Ioi (f a)).map f.symm.toEquiv.toEmbedding
  finset_mem_Ici := by simp
  finset_mem_Ioi := by simp

end OrderIso

/-! #### Subtype of a locally finite order -/


variable [Preorder α] (p : α -> Prop) [DecidablePred p]

/--
Instance `Subtype.instLocallyFiniteOrder` / 实例 `Subtype.instLocallyFiniteOrder`

English:
instance Subtype.instLocallyFiniteOrder
  signature: [LocallyFiniteOrder α]
  body: (Icc (a : α) b).subtype p
  finsetIco a b := (Ico (a : α) b).subtype p
  finsetIoc a b := (Ioc (a : α) b).subtype p
  finsetIoo a b := (Ioo (a : α) b).subtype p
  finset_mem_Icc a b x := by simp_rw [Finset.mem_subtype, mem_Icc, Subtype.coe_le_coe]
  finset_mem_Ico a b x := by
    simp_rw [Finset.mem

中文:
实例 Subtype.instLocallyFiniteOrder
  签名: [LocallyFiniteOrder α]
  定义体: (Icc (a : α) b).subtype p
  finsetIco a b := (Ico (a : α) b).subtype p
  finsetIoc a b := (Ioc (a : α) b).subtype p
  finsetIoo a b := (Ioo (a : α) b).subtype p
  finset_mem_Icc a b x := by simp_rw [Finset.mem_subtype, mem_Icc, Subtype.coe_le_coe]
  finset_mem_Ico a b x := by
    simp_rw [Finset.mem

Depends on / 依赖: subtype
-/
instance Subtype.instLocallyFiniteOrder [LocallyFiniteOrder α] :
    LocallyFiniteOrder (Subtype p) where
  finsetIcc a b := (Icc (a : α) b).subtype p
  finsetIco a b := (Ico (a : α) b).subtype p
  finsetIoc a b := (Ioc (a : α) b).subtype p
  finsetIoo a b := (Ioo (a : α) b).subtype p
  finset_mem_Icc a b x := by simp_rw [Finset.mem_subtype, mem_Icc, Subtype.coe_le_coe]
  finset_mem_Ico a b x := by
    simp_rw [Finset.mem_subtype, mem_Ico, Subtype.coe_le_coe, Subtype.coe_lt_coe]
  finset_mem_Ioc a b x := by
    simp_rw [Finset.mem_subtype, mem_Ioc, Subtype.coe_le_coe, Subtype.coe_lt_coe]
  finset_mem_Ioo a b x := by simp_rw [Finset.mem_subtype, mem_Ioo, Subtype.coe_lt_coe]

@[to_dual]
/--
Instance `Subtype.instLocallyFiniteOrderTop` / 实例 `Subtype.instLocallyFiniteOrderTop`

English:
instance Subtype.instLocallyFiniteOrderTop
  signature: [LocallyFiniteOrderTop α]
  body: (Ici (a : α)).subtype p
  finsetIoi a := (Ioi (a : α)).subtype p
  finset_mem_Ici a x := by simp_rw [Finset.mem_subtype, mem_Ici, Subtype.coe_le_coe]
  finset_mem_Ioi a x := by simp_rw [Finset.mem_subtype, mem_Ioi, Subtype.coe_lt_coe]

中文:
实例 Subtype.instLocallyFiniteOrderTop
  签名: [LocallyFiniteOrderTop α]
  定义体: (Ici (a : α)).subtype p
  finsetIoi a := (Ioi (a : α)).subtype p
  finset_mem_Ici a x := by simp_rw [Finset.mem_subtype, mem_Ici, Subtype.coe_le_coe]
  finset_mem_Ioi a x := by simp_rw [Finset.mem_subtype, mem_Ioi, Subtype.coe_lt_coe]

Depends on / 依赖: subtype
-/
instance Subtype.instLocallyFiniteOrderTop [LocallyFiniteOrderTop α] :
    LocallyFiniteOrderTop (Subtype p) where
  finsetIci a := (Ici (a : α)).subtype p
  finsetIoi a := (Ioi (a : α)).subtype p
  finset_mem_Ici a x := by simp_rw [Finset.mem_subtype, mem_Ici, Subtype.coe_le_coe]
  finset_mem_Ioi a x := by simp_rw [Finset.mem_subtype, mem_Ioi, Subtype.coe_lt_coe]

namespace Finset

section LocallyFiniteOrder

variable [LocallyFiniteOrder α] (a b : Subtype p)

@[to_dual self]
/--
theorem `subtype_Icc_eq` / 定理 `subtype_Icc_eq`

English:
theorem subtype_Icc_eq
  statement: Icc a b = (Icc (a : α) b).subtype p
  proof: rfl

@[to_dual (reorder := a b)]

中文:
定理 subtype_Icc_eq
  结论: Icc a b = (Icc (a : α) b).subtype p
  证明: rfl

@[to_dual (reorder := a b)]
-/
theorem subtype_Icc_eq : Icc a b = (Icc (a : α) b).subtype p :=
  rfl

@[to_dual (reorder := a b)]
/--
theorem `subtype_Ico_eq` / 定理 `subtype_Ico_eq`

English:
theorem subtype_Ico_eq
  statement: Ico a b = (Ico (a : α) b).subtype p
  proof: rfl

@[to_dual self]

中文:
定理 subtype_Ico_eq
  结论: Ico a b = (Ico (a : α) b).subtype p
  证明: rfl

@[to_dual self]
-/
theorem subtype_Ico_eq : Ico a b = (Ico (a : α) b).subtype p :=
  rfl

@[to_dual self]
/--
theorem `subtype_Ioo_eq` / 定理 `subtype_Ioo_eq`

English:
theorem subtype_Ioo_eq
  statement: Ioo a b = (Ioo (a : α) b).subtype p
  proof: rfl

中文:
定理 subtype_Ioo_eq
  结论: Ioo a b = (Ioo (a : α) b).subtype p
  证明: rfl
-/
theorem subtype_Ioo_eq : Ioo a b = (Ioo (a : α) b).subtype p :=
  rfl

/--
theorem `map_subtype_embedding_Icc` / 定理 `map_subtype_embedding_Icc`

English:
theorem map_subtype_embedding_Icc
  given: (hp : forall ⦃a b x⦄, a <= x -> x <= b -> p a -> p b -> p x)
  proof: by
  rw [subtype_Icc_eq]
  refine Finset.subtype_map_of_mem fun x hx => ?_
  rw [mem_Icc] at hx
  exact hp hx.1 hx.2 a.prop b.prop

中文:
定理 map_subtype_embedding_Icc
  条件: (hp : 对任意 ⦃a b x⦄, a <= x -> x <= b -> p a -> p b -> p x)
  证明: by
  rw [subtype_Icc_eq]
  refine Finset.subtype_map_of_mem fun x hx => ?_
  rw [mem_Icc] at hx
  exact hp hx.1 hx.2 a.prop b.prop

Depends on / 依赖: Finset, Finset.subtype_map_of_mem, a.prop, b.prop, mem_Icc, subtype_Icc_eq, subtype_map_of_mem
-/
theorem map_subtype_embedding_Icc (hp : forall ⦃a b x⦄, a <= x -> x <= b -> p a -> p b -> p x) :
    (Icc a b).map (Embedding.subtype p) = (Icc a b : Finset α) := by
  rw [subtype_Icc_eq]
  refine Finset.subtype_map_of_mem fun x hx => ?_
  rw [mem_Icc] at hx
  exact hp hx.1 hx.2 a.prop b.prop

/--
theorem `map_subtype_embedding_Ico` / 定理 `map_subtype_embedding_Ico`

English:
theorem map_subtype_embedding_Ico
  given: (hp : forall ⦃a b x⦄, a <= x -> x <= b -> p a -> p b -> p x)
  proof: by
  rw [subtype_Ico_eq]
  refine Finset.subtype_map_of_mem fun x hx => ?_
  rw [mem_Ico] at hx
  exact hp hx.1 hx.2.le a.prop b.prop

中文:
定理 map_subtype_embedding_Ico
  条件: (hp : 对任意 ⦃a b x⦄, a <= x -> x <= b -> p a -> p b -> p x)
  证明: by
  rw [subtype_Ico_eq]
  refine Finset.subtype_map_of_mem fun x hx => ?_
  rw [mem_Ico] at hx
  exact hp hx.1 hx.2.le a.prop b.prop

Depends on / 依赖: Finset, Finset.subtype_map_of_mem, a.prop, b.prop, mem_Ico, subtype_Ico_eq, subtype_map_of_mem
-/
theorem map_subtype_embedding_Ico (hp : forall ⦃a b x⦄, a <= x -> x <= b -> p a -> p b -> p x) :
    (Ico a b).map (Embedding.subtype p) = (Ico a b : Finset α) := by
  rw [subtype_Ico_eq]
  refine Finset.subtype_map_of_mem fun x hx => ?_
  rw [mem_Ico] at hx
  exact hp hx.1 hx.2.le a.prop b.prop

/--
theorem `map_subtype_embedding_Ioc` / 定理 `map_subtype_embedding_Ioc`

English:
theorem map_subtype_embedding_Ioc
  given: (hp : forall ⦃a b x⦄, a <= x -> x <= b -> p a -> p b -> p x)
  proof: by
  rw [subtype_Ioc_eq]
  refine Finset.subtype_map_of_mem fun x hx => ?_
  rw [mem_Ioc] at hx
  exact hp hx.1.le hx.2 a.prop b.prop

中文:
定理 map_subtype_embedding_Ioc
  条件: (hp : 对任意 ⦃a b x⦄, a <= x -> x <= b -> p a -> p b -> p x)
  证明: by
  rw [subtype_Ioc_eq]
  refine Finset.subtype_map_of_mem fun x hx => ?_
  rw [mem_Ioc] at hx
  exact hp hx.1.le hx.2 a.prop b.prop

Depends on / 依赖: Finset, Finset.subtype_map_of_mem, a.prop, b.prop, mem_Ioc, subtype_Ioc_eq, subtype_map_of_mem
-/
theorem map_subtype_embedding_Ioc (hp : forall ⦃a b x⦄, a <= x -> x <= b -> p a -> p b -> p x) :
    (Ioc a b).map (Embedding.subtype p) = (Ioc a b : Finset α) := by
  rw [subtype_Ioc_eq]
  refine Finset.subtype_map_of_mem fun x hx => ?_
  rw [mem_Ioc] at hx
  exact hp hx.1.le hx.2 a.prop b.prop

/--
theorem `map_subtype_embedding_Ioo` / 定理 `map_subtype_embedding_Ioo`

English:
theorem map_subtype_embedding_Ioo
  given: (hp : forall ⦃a b x⦄, a <= x -> x <= b -> p a -> p b -> p x)
  proof: by
  rw [subtype_Ioo_eq]
  refine Finset.subtype_map_of_mem fun x hx => ?_
  rw [mem_Ioo] at hx
  exact hp hx.1.le hx.2.le a.prop b.prop

中文:
定理 map_subtype_embedding_Ioo
  条件: (hp : 对任意 ⦃a b x⦄, a <= x -> x <= b -> p a -> p b -> p x)
  证明: by
  rw [subtype_Ioo_eq]
  refine Finset.subtype_map_of_mem fun x hx => ?_
  rw [mem_Ioo] at hx
  exact hp hx.1.le hx.2.le a.prop b.prop

Depends on / 依赖: Finset, Finset.subtype_map_of_mem, a.prop, b.prop, mem_Ioo, subtype_Ioo_eq, subtype_map_of_mem
-/
theorem map_subtype_embedding_Ioo (hp : forall ⦃a b x⦄, a <= x -> x <= b -> p a -> p b -> p x) :
    (Ioo a b).map (Embedding.subtype p) = (Ioo a b : Finset α) := by
  rw [subtype_Ioo_eq]
  refine Finset.subtype_map_of_mem fun x hx => ?_
  rw [mem_Ioo] at hx
  exact hp hx.1.le hx.2.le a.prop b.prop

end LocallyFiniteOrder

section LocallyFiniteOrderTop

variable [LocallyFiniteOrderTop α] (a : Subtype p)

@[to_dual]
/--
theorem `subtype_Ici_eq` / 定理 `subtype_Ici_eq`

English:
theorem subtype_Ici_eq
  statement: Ici a = (Ici (a : α)).subtype p
  proof: rfl

@[to_dual]

中文:
定理 subtype_Ici_eq
  结论: Ici a = (Ici (a : α)).subtype p
  证明: rfl

@[to_dual]
-/
theorem subtype_Ici_eq : Ici a = (Ici (a : α)).subtype p :=
  rfl

@[to_dual]
/--
theorem `subtype_Ioi_eq` / 定理 `subtype_Ioi_eq`

English:
theorem subtype_Ioi_eq
  statement: Ioi a = (Ioi (a : α)).subtype p
  proof: rfl

@[to_dual]

中文:
定理 subtype_Ioi_eq
  结论: Ioi a = (Ioi (a : α)).subtype p
  证明: rfl

@[to_dual]
-/
theorem subtype_Ioi_eq : Ioi a = (Ioi (a : α)).subtype p :=
  rfl

@[to_dual]
/--
theorem `map_subtype_embedding_Ici` / 定理 `map_subtype_embedding_Ici`

English:
theorem map_subtype_embedding_Ici
  given: (hp : forall ⦃a x⦄, a <= x -> p a -> p x)
  proof: by
  rw [subtype_Ici_eq]
  exact Finset.subtype_map_of_mem fun x hx => hp (mem_Ici.1 hx) a.prop

@[to_dual]

中文:
定理 map_subtype_embedding_Ici
  条件: (hp : 对任意 ⦃a x⦄, a <= x -> p a -> p x)
  证明: by
  rw [subtype_Ici_eq]
  exact Finset.subtype_map_of_mem fun x hx => hp (mem_Ici.1 hx) a.prop

@[to_dual]

Depends on / 依赖: Finset, Finset.subtype_map_of_mem, a.prop, mem_Ici, subtype_Ici_eq, subtype_map_of_mem
-/
theorem map_subtype_embedding_Ici (hp : forall ⦃a x⦄, a <= x -> p a -> p x) :
    (Ici a).map (Embedding.subtype p) = (Ici a : Finset α) := by
  rw [subtype_Ici_eq]
  exact Finset.subtype_map_of_mem fun x hx => hp (mem_Ici.1 hx) a.prop

@[to_dual]
/--
theorem `map_subtype_embedding_Ioi` / 定理 `map_subtype_embedding_Ioi`

English:
theorem map_subtype_embedding_Ioi
  given: (hp : forall ⦃a x⦄, a <= x -> p a -> p x)
  proof: by
  rw [subtype_Ioi_eq]
  exact Finset.subtype_map_of_mem fun x hx => hp (mem_Ioi.1 hx).le a.prop

中文:
定理 map_subtype_embedding_Ioi
  条件: (hp : 对任意 ⦃a x⦄, a <= x -> p a -> p x)
  证明: by
  rw [subtype_Ioi_eq]
  exact Finset.subtype_map_of_mem fun x hx => hp (mem_Ioi.1 hx).le a.prop

Depends on / 依赖: Finset, Finset.subtype_map_of_mem, a.prop, mem_Ioi, subtype_Ioi_eq, subtype_map_of_mem
-/
theorem map_subtype_embedding_Ioi (hp : forall ⦃a x⦄, a <= x -> p a -> p x) :
    (Ioi a).map (Embedding.subtype p) = (Ioi a : Finset α) := by
  rw [subtype_Ioi_eq]
  exact Finset.subtype_map_of_mem fun x hx => hp (mem_Ioi.1 hx).le a.prop

end LocallyFiniteOrderTop


end Finset

section Finite

variable {α : Type*} {s : Set α}

@[to_dual]
/--
theorem `BddBelow.finite_of_bddAbove` / 定理 `BddBelow.finite_of_bddAbove`

English:
theorem BddBelow.finite_of_bddAbove
  statement: [Preorder α] [LocallyFiniteOrder α]
  proof: let ⟨a, ha⟩ := h₀
  let ⟨b, hb⟩ := h₁
  (Set.finite_Icc a b).subset fun _x hx => ⟨ha hx, hb hx⟩

@[to_dual]

中文:
定理 BddBelow.finite_of_bddAbove
  结论: [Preorder α] [LocallyFiniteOrder α]
  证明: let ⟨a, ha⟩ := h₀
  let ⟨b, hb⟩ := h₁
  (Set.finite_Icc a b).subset fun _x hx => ⟨ha hx, hb hx⟩

@[to_dual]

Depends on / 依赖: Set.finite_Icc, finite_Icc, subset
-/
theorem BddBelow.finite_of_bddAbove [Preorder α] [LocallyFiniteOrder α]
    {s : Set α} (h₀ : BddBelow s) (h₁ : BddAbove s) :
    s.Finite :=
  let ⟨a, ha⟩ := h₀
  let ⟨b, hb⟩ := h₁
  (Set.finite_Icc a b).subset fun _x hx => ⟨ha hx, hb hx⟩

@[to_dual]
/--
theorem `Set.finite_iff_bddAbove` / 定理 `Set.finite_iff_bddAbove`

English:
theorem Set.finite_iff_bddAbove
  given: [SemilatticeSup α] [LocallyFiniteOrder α] [OrderBot α]
  proof: ⟨fun h => ⟨h.toFinset.sup id, fun _ hx => Finset.le_sup (f := id) ((Finite.mem_toFinset h).mpr hx)⟩,
    fun ⟨m, hm⟩ => (Set.finite_Icc ⊥ m).subset (fun _ hx => ⟨bot_le, hm hx⟩)⟩

@[to_dual]

中文:
定理 Set.finite_iff_bddAbove
  条件: [SemilatticeSup α] [LocallyFiniteOrder α] [OrderBot α]
  证明: ⟨fun h => ⟨h.toFinset.sup id, fun _ hx => Finset.le_sup (f := id) ((Finite.mem_toFinset h).mpr hx)⟩,
    fun ⟨m, hm⟩ => (Set.finite_Icc ⊥ m).subset (fun _ hx => ⟨bot_le, hm hx⟩)⟩

@[to_dual]

Depends on / 依赖: Finite, Finite.mem_toFinset, Finset, Finset.le_sup, Set.finite_Icc, bot_le, finite_Icc, h.toFinset.sup, le_sup, mem_toFinset, subset, toFinset
-/
theorem Set.finite_iff_bddAbove [SemilatticeSup α] [LocallyFiniteOrder α] [OrderBot α] :
    s.Finite ↔ BddAbove s :=
  ⟨fun h => ⟨h.toFinset.sup id, fun _ hx => Finset.le_sup (f := id) ((Finite.mem_toFinset h).mpr hx)⟩,
    fun ⟨m, hm⟩ => (Set.finite_Icc ⊥ m).subset (fun _ hx => ⟨bot_le, hm hx⟩)⟩

@[to_dual]
/--
theorem `Set.finite_iff_bddBelow_bddAbove` / 定理 `Set.finite_iff_bddBelow_bddAbove`

English:
theorem Set.finite_iff_bddBelow_bddAbove
  given: [Nonempty α] [Lattice α] [LocallyFiniteOrder α]
  proof: by
  obtain (rfl | hs) := s.eq_empty_or_nonempty
  · simp only [Set.finite_empty, bddBelow_empty, bddAbove_empty, and_self]
  exact ⟨fun h => ⟨⟨h.toFinset.inf' ((Finite.toFinset_nonempty h).mpr hs) id,
    fun x hx => Finset.inf'_le id ((Finite.mem_toFinset h).mpr hx)⟩,
    ⟨h.toFinset.sup' ((Finite

中文:
定理 Set.finite_iff_bddBelow_bddAbove
  条件: [Nonempty α] [Lattice α] [LocallyFiniteOrder α]
  证明: by
  obtain (rfl | hs) := s.eq_empty_or_nonempty
  · simp only [Set.finite_empty, bddBelow_empty, bddAbove_empty, and_self]
  exact ⟨fun h => ⟨⟨h.toFinset.inf' ((Finite.toFinset_nonempty h).mpr hs) id,
    fun x hx => Finset.inf'_le id ((Finite.mem_toFinset h).mpr hx)⟩,
    ⟨h.toFinset.sup' ((Finite

Depends on / 依赖: BddBelow, BddBelow.finite_of_bddAbove, Finite, Finite.mem_toFinset, Finite.toFinset_nonempty, Finset, Finset.inf, Finset.le_sup, Set.finite_empty, and_self, bddAbove_empty, bddBelow_empty, eq_empty_or_nonempty, finite_empty, finite_of_bddAbove, h.toFinset.inf, h.toFinset.sup, le_sup, mem_toFinset, s.eq_empty_or_nonempty
-/
theorem Set.finite_iff_bddBelow_bddAbove [Nonempty α] [Lattice α] [LocallyFiniteOrder α] :
    s.Finite ↔ BddBelow s ∧ BddAbove s := by
  obtain (rfl | hs) := s.eq_empty_or_nonempty
  · simp only [Set.finite_empty, bddBelow_empty, bddAbove_empty, and_self]
  exact ⟨fun h => ⟨⟨h.toFinset.inf' ((Finite.toFinset_nonempty h).mpr hs) id,
    fun x hx => Finset.inf'_le id ((Finite.mem_toFinset h).mpr hx)⟩,
    ⟨h.toFinset.sup' ((Finite.toFinset_nonempty h).mpr hs) id, fun x hx => Finset.le_sup' id
    ((Finite.mem_toFinset h).mpr hx)⟩⟩,
    fun ⟨h₀, h₁⟩ => BddBelow.finite_of_bddAbove h₀ h₁⟩

end Finite

/-! We make the instances below low priority
so when alternative constructions are available they are preferred. -/

variable {y : α}

@[to_dual]
instance (priority := low) [DecidableLE α] [LocallyFiniteOrder α] :
    LocallyFiniteOrderTop { x : α // x <= y } where
  finsetIoi a := Finset.Ioc a ⟨y, by rfl⟩
  finsetIci a := Finset.Icc a ⟨y, by rfl⟩
  finset_mem_Ici a b := by
    simp only [Finset.mem_Icc, and_iff_left_iff_imp]
    exact fun _ => b.property
  finset_mem_Ioi a b := by
    simp only [Finset.mem_Ioc, and_iff_left_iff_imp]
    exact fun _ => b.property

@[to_dual]
instance (priority := low) [DecidableLT α] [LocallyFiniteOrder α] :
    LocallyFiniteOrderTop { x : α // x < y } where
  finsetIoi a := (Finset.Ioo ↑a y).subtype _
  finsetIci a := (Finset.Ico ↑a y).subtype _
  finset_mem_Ici a b := by
    simp only [Finset.mem_subtype, Finset.mem_Ico, Subtype.coe_le_coe, and_iff_left_iff_imp]
    exact fun _ => b.property
  finset_mem_Ioi a b := by
    simp only [Finset.mem_subtype, Finset.mem_Ioo, Subtype.coe_lt_coe, and_iff_left_iff_imp]
    exact fun _ => b.property

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LocallyFiniteOrderBot
  signature: α] : Finite { x
  body: by
  simpa only [coe_Iic] using! (Finset.Iic y).finite_toSet

@[to_dual]

中文:
实例 [LocallyFiniteOrderBot
  签名: α] : Finite { x
  定义体: by
  simpa only [coe_Iic] using! (Finset.Iic y).finite_toSet

@[to_dual]

Depends on / 依赖: Finset, Finset.Iic, coe_Iic, finite_toSet
-/
instance [LocallyFiniteOrderBot α] : Finite { x : α // x <= y } := by
  simpa only [coe_Iic] using! (Finset.Iic y).finite_toSet

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LocallyFiniteOrderBot
  signature: α] : Finite { x
  body: by
  simpa only [coe_Iio] using! (Finset.Iio y).finite_toSet

中文:
实例 [LocallyFiniteOrderBot
  签名: α] : Finite { x
  定义体: by
  simpa only [coe_Iio] using! (Finset.Iio y).finite_toSet

Depends on / 依赖: Finset, Finset.Iio, coe_Iio, finite_toSet
-/
instance [LocallyFiniteOrderBot α] : Finite { x : α // x < y } := by
  simpa only [coe_Iio] using! (Finset.Iio y).finite_toSet

namespace Set
variable {α : Type*} [Preorder α]

section LocallyFiniteOrder
variable [LocallyFiniteOrder α]

@[simp, to_dual self]
/--
lemma `toFinset_Icc` / 引理 `toFinset_Icc`

English:
lemma toFinset_Icc
  given: (a b : α) [Fintype (Icc a b)]
  statement: (Icc a b).toFinset = Finset.Icc a b
  proof: by
  ext; simp

@[to_dual (reorder := a b) (attr := simp)]

中文:
引理 toFinset_Icc
  条件: (a b : α) [Fintype (Icc a b)]
  结论: (Icc a b).toFinset = Finset.Icc a b
  证明: by
  ext; simp

@[to_dual (reorder := a b) (attr := simp)]
-/
lemma toFinset_Icc (a b : α) [Fintype (Icc a b)] : (Icc a b).toFinset = Finset.Icc a b := by
  ext; simp

@[to_dual (reorder := a b) (attr := simp)]
/--
lemma `toFinset_Ico` / 引理 `toFinset_Ico`

English:
lemma toFinset_Ico
  given: (a b : α) [Fintype (Ico a b)]
  statement: (Ico a b).toFinset = Finset.Ico a b
  proof: by
  ext; simp

@[simp, to_dual self]

中文:
引理 toFinset_Ico
  条件: (a b : α) [Fintype (Ico a b)]
  结论: (Ico a b).toFinset = Finset.Ico a b
  证明: by
  ext; simp

@[simp, to_dual self]
-/
lemma toFinset_Ico (a b : α) [Fintype (Ico a b)] : (Ico a b).toFinset = Finset.Ico a b := by
  ext; simp

@[simp, to_dual self]
/--
lemma `toFinset_Ioo` / 引理 `toFinset_Ioo`

English:
lemma toFinset_Ioo
  given: (a b : α) [Fintype (Ioo a b)]
  statement: (Ioo a b).toFinset = Finset.Ioo a b
  proof: by
  ext; simp

中文:
引理 toFinset_Ioo
  条件: (a b : α) [Fintype (Ioo a b)]
  结论: (Ioo a b).toFinset = Finset.Ioo a b
  证明: by
  ext; simp
-/
lemma toFinset_Ioo (a b : α) [Fintype (Ioo a b)] : (Ioo a b).toFinset = Finset.Ioo a b := by
  ext; simp

end LocallyFiniteOrder

section LocallyFiniteOrderTop
variable [LocallyFiniteOrderTop α]

@[to_dual (attr := simp)]
/--
lemma `toFinset_Ici` / 引理 `toFinset_Ici`

English:
lemma toFinset_Ici
  given: (a : α) [Fintype (Ici a)]
  statement: (Ici a).toFinset = Finset.Ici a
  proof: by ext; simp

@[to_dual (attr := simp)]

中文:
引理 toFinset_Ici
  条件: (a : α) [Fintype (Ici a)]
  结论: (Ici a).toFinset = Finset.Ici a
  证明: by ext; simp

@[to_dual (attr := simp)]
-/
lemma toFinset_Ici (a : α) [Fintype (Ici a)] : (Ici a).toFinset = Finset.Ici a := by ext; simp

@[to_dual (attr := simp)]
/--
lemma `toFinset_Ioi` / 引理 `toFinset_Ioi`

English:
lemma toFinset_Ioi
  given: (a : α) [Fintype (Ioi a)]
  statement: (Ioi a).toFinset = Finset.Ioi a
  proof: by ext; simp

中文:
引理 toFinset_Ioi
  条件: (a : α) [Fintype (Ioi a)]
  结论: (Ioi a).toFinset = Finset.Ioi a
  证明: by ext; simp
-/
lemma toFinset_Ioi (a : α) [Fintype (Ioi a)] : (Ioi a).toFinset = Finset.Ioi a := by ext; simp

end LocallyFiniteOrderTop
end Set

-- See note [reducible non-instances]
/--
Definition of `LocallyFiniteOrder.ofOrderIsoClass` / `LocallyFiniteOrder.ofOrderIsoClass` 的定义

English:
abbreviation LocallyFiniteOrder.ofOrderIsoClass
  signature: {F M N : Type*} [Preorder M] [Preorder N]
  body: (finsetIcc (f x) (f y)).map ⟨EquivLike.inv f, (EquivLike.right_inv f).injective⟩
  finsetIco x y := (finsetIco (f x) (f y)).map ⟨EquivLike.inv f, (EquivLike.right_inv f).injective⟩
  finsetIoc x y := (finsetIoc (f x) (f y)).map ⟨EquivLike.inv f, (EquivLike.right_inv f).injective⟩
  finsetIoo x y := 

中文:
缩写 LocallyFiniteOrder.ofOrderIsoClass
  签名: {F M N : 类型} [Preorder M] [Preorder N]
  定义体: (finsetIcc (f x) (f y)).map ⟨EquivLike.inv f, (EquivLike.right_inv f).injective⟩
  finsetIco x y := (finsetIco (f x) (f y)).map ⟨EquivLike.inv f, (EquivLike.right_inv f).injective⟩
  finsetIoc x y := (finsetIoc (f x) (f y)).map ⟨EquivLike.inv f, (EquivLike.right_inv f).injective⟩
  finsetIoo x y := 

Depends on / 依赖: EquivLike, EquivLike.inv, EquivLike.right_inv, finsetIcc, injective, right_inv
-/
abbrev LocallyFiniteOrder.ofOrderIsoClass {F M N : Type*} [Preorder M] [Preorder N]
    [EquivLike F M N] [OrderIsoClass F M N] (f : F) [LocallyFiniteOrder N] :
    LocallyFiniteOrder M where
  finsetIcc x y := (finsetIcc (f x) (f y)).map ⟨EquivLike.inv f, (EquivLike.right_inv f).injective⟩
  finsetIco x y := (finsetIco (f x) (f y)).map ⟨EquivLike.inv f, (EquivLike.right_inv f).injective⟩
  finsetIoc x y := (finsetIoc (f x) (f y)).map ⟨EquivLike.inv f, (EquivLike.right_inv f).injective⟩
  finsetIoo x y := (finsetIoo (f x) (f y)).map ⟨EquivLike.inv f, (EquivLike.right_inv f).injective⟩
  finset_mem_Icc := by simp [finset_mem_Icc, EquivLike.inv_apply_eq]
  finset_mem_Ico := by
    simp [finset_mem_Ico, EquivLike.inv_apply_eq, map_lt_map_iff]
  finset_mem_Ioc := by
    simp [finset_mem_Ioc, EquivLike.inv_apply_eq, map_lt_map_iff]
  finset_mem_Ioo := by
    simp [finset_mem_Ioo, EquivLike.inv_apply_eq, map_lt_map_iff]
