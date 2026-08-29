/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Defs

/-!
# Equitable functions

This file defines equitable functions.

A function `f` is equitable on a set `s` if `f a₁ ≤ f a₂ + 1` for all `a₁, a₂ ∈ s`. This is mostly
useful when the codomain of `f` is `ℕ` or `ℤ` (or more generally a successor order).

## TODO

`ℕ` can be replaced by any `SuccOrder` + `ConditionallyCompleteMonoid`, but we don't have the
latter yet.
-/

@[expose] public section


variable {α β : Type*}

namespace Set

/--
Definition of `EquitableOn` / `EquitableOn` 的定义

English:
definition EquitableOn
  signature: [LE β] [Add β] [One β] (s : Set α) (f : α -> β)
  body: forall ⦃a₁ a₂⦄, a₁ in s -> a₂ in s -> f a₁ <= f a₂ + 1

@[simp]

中文:
定义 EquitableOn
  签名: [LE β] [Add β] [One β] (s : Set α) (f : α -> β)
  定义体: forall ⦃a₁ a₂⦄, a₁ in s -> a₂ in s -> f a₁ <= f a₂ + 1

@[simp]
-/
def EquitableOn [LE β] [Add β] [One β] (s : Set α) (f : α -> β) : Prop :=
  forall ⦃a₁ a₂⦄, a₁ in s -> a₂ in s -> f a₁ <= f a₂ + 1

@[simp]
/--
theorem `equitableOn_empty` / 定理 `equitableOn_empty`

English:
theorem equitableOn_empty
  given: [LE β] [Add β] [One β] (f : α -> β)
  statement: EquitableOn ∅ f
  proof: fun a _ ha =>
  (Set.notMem_empty a ha).elim

中文:
定理 equitableOn_empty
  条件: [LE β] [Add β] [One β] (f : α -> β)
  结论: EquitableOn ∅ f
  证明: fun a _ ha =>
  (Set.notMem_empty a ha).elim
-/
theorem equitableOn_empty [LE β] [Add β] [One β] (f : α -> β) : EquitableOn ∅ f := fun a _ ha =>
  (Set.notMem_empty a ha).elim

/--
theorem `equitableOn_iff_exists_le_le_add_one` / 定理 `equitableOn_iff_exists_le_le_add_one`

English:
theorem equitableOn_iff_exists_le_le_add_one
  given: {s : Set α} {f : α -> Nat}
  proof: by
  refine ⟨?_, fun ⟨b, hb⟩ x y hx hy => by grw [(hb x hx).2, (hb y hy).1]⟩
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
  · simp
  intro hs
  by_cases! h : forall y in s, f x <= f y
  · exact ⟨f x, fun y hy => ⟨h _ hy, hs hy hx⟩⟩
  obtain ⟨w, hw, hwx⟩ := h
  refine ⟨f w, fun y hy => ⟨Nat.le_of

中文:
定理 equitableOn_iff_exists_le_le_add_one
  条件: {s : Set α} {f : α -> 自然数}
  证明: by
  refine ⟨?_, fun ⟨b, hb⟩ x y hx hy => by grw [(hb x hx).2, (hb y hy).1]⟩
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
  · simp
  intro hs
  by_cases! h : forall y in s, f x <= f y
  · exact ⟨f x, fun y hy => ⟨h _ hy, hs hy hx⟩⟩
  obtain ⟨w, hw, hwx⟩ := h
  refine ⟨f w, fun y hy => ⟨Nat.le_of

Depends on / 依赖: Nat.le_of_succ_le_succ, Nat.succ_le_of_lt, antisymm, eq_empty_or_nonempty, le_of_succ_le_succ, s.eq_empty_or_nonempty, succ_le_of_lt
-/
theorem equitableOn_iff_exists_le_le_add_one {s : Set α} {f : α -> Nat} :
    s.EquitableOn f ↔ exists b, forall a in s, b <= f a ∧ f a <= b + 1 := by
  refine ⟨?_, fun ⟨b, hb⟩ x y hx hy => by grw [(hb x hx).2, (hb y hy).1]⟩
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
  · simp
  intro hs
  by_cases! h : forall y in s, f x <= f y
  · exact ⟨f x, fun y hy => ⟨h _ hy, hs hy hx⟩⟩
  obtain ⟨w, hw, hwx⟩ := h
  refine ⟨f w, fun y hy => ⟨Nat.le_of_succ_le_succ ?_, hs hy hw⟩⟩
  rw [(Nat.succ_le_of_lt hwx).antisymm (hs hx hw)]
  exact hs hx hy

/--
theorem `equitableOn_iff_exists_image_subset_icc` / 定理 `equitableOn_iff_exists_image_subset_icc`

English:
theorem equitableOn_iff_exists_image_subset_icc
  given: {s : Set α} {f : α -> Nat}
  proof: by
  simpa only [image_subset_iff] using! equitableOn_iff_exists_le_le_add_one

中文:
定理 equitableOn_iff_exists_image_subset_icc
  条件: {s : Set α} {f : α -> 自然数}
  证明: by
  simpa only [image_subset_iff] using! equitableOn_iff_exists_le_le_add_one

Depends on / 依赖: equitableOn_iff_exists_le_le_add_one, image_subset_iff
-/
theorem equitableOn_iff_exists_image_subset_icc {s : Set α} {f : α -> Nat} :
    s.EquitableOn f ↔ exists b, f '' s subseteq Icc b (b + 1) := by
  simpa only [image_subset_iff] using! equitableOn_iff_exists_le_le_add_one

/--
theorem `equitableOn_iff_exists_eq_eq_add_one` / 定理 `equitableOn_iff_exists_eq_eq_add_one`

English:
theorem equitableOn_iff_exists_eq_eq_add_one
  given: {s : Set α} {f : α -> Nat}
  proof: by
  simp_rw [equitableOn_iff_exists_le_le_add_one, Nat.le_and_le_add_one_iff]

中文:
定理 equitableOn_iff_exists_eq_eq_add_one
  条件: {s : Set α} {f : α -> 自然数}
  证明: by
  simp_rw [equitableOn_iff_exists_le_le_add_one, Nat.le_and_le_add_one_iff]

Depends on / 依赖: Nat.le_and_le_add_one_iff, equitableOn_iff_exists_le_le_add_one, le_and_le_add_one_iff, simp_rw
-/
theorem equitableOn_iff_exists_eq_eq_add_one {s : Set α} {f : α -> Nat} :
    s.EquitableOn f ↔ exists b, forall a in s, f a = b ∨ f a = b + 1 := by
  simp_rw [equitableOn_iff_exists_le_le_add_one, Nat.le_and_le_add_one_iff]

section LinearOrder
variable [LinearOrder β] [Add β] [One β] {s : Set α} {f : α -> β}

@[simp]
/--
lemma `not_equitableOn` / 引理 `not_equitableOn`

English:
lemma not_equitableOn
  statement: ¬s.EquitableOn f ↔ exists a in s, exists b in s, f b + 1 < f a
  proof: by
  simp [EquitableOn]

中文:
引理 not_equitableOn
  结论: ¬s.EquitableOn f ↔ 存在 a in s, 存在 b in s, f b + 1 < f a
  证明: by
  simp [EquitableOn]

Depends on / 依赖: EquitableOn
-/
lemma not_equitableOn : ¬s.EquitableOn f ↔ exists a in s, exists b in s, f b + 1 < f a := by
  simp [EquitableOn]

end LinearOrder

section OrderedSemiring

variable [Semiring β] [PartialOrder β] [IsOrderedRing β]

/--
theorem `Subsingleton.equitableOn` / 定理 `Subsingleton.equitableOn`

English:
theorem Subsingleton.equitableOn
  given: {s : Set α} (hs : s.Subsingleton) (f : α -> β)
  statement: s.EquitableOn f
  proof: fun i j hi hj => by
  rw [hs hi hj]
  exact le_add_of_nonneg_right zero_le_one

中文:
定理 Subsingleton.equitableOn
  条件: {s : Set α} (hs : s.Subsingleton) (f : α -> β)
  结论: s.EquitableOn f
  证明: fun i j hi hj => by
  rw [hs hi hj]
  exact le_add_of_nonneg_right zero_le_one

Depends on / 依赖: le_add_of_nonneg_right, zero_le_one
-/
theorem Subsingleton.equitableOn {s : Set α} (hs : s.Subsingleton) (f : α -> β) : s.EquitableOn f :=
  fun i j hi hj => by
  rw [hs hi hj]
  exact le_add_of_nonneg_right zero_le_one

/--
theorem `equitableOn_singleton` / 定理 `equitableOn_singleton`

English:
theorem equitableOn_singleton
  given: (a : α) (f : α -> β)
  statement: Set.EquitableOn {a} f
  proof: Set.subsingleton_singleton.equitableOn f

中文:
定理 equitableOn_singleton
  条件: (a : α) (f : α -> β)
  结论: Set.EquitableOn {a} f
  证明: Set.subsingleton_singleton.equitableOn f

Depends on / 依赖: Set.subsingleton_singleton.equitableOn, equitableOn, subsingleton_singleton
-/
theorem equitableOn_singleton (a : α) (f : α -> β) : Set.EquitableOn {a} f :=
  Set.subsingleton_singleton.equitableOn f

end OrderedSemiring

end Set

open Set

namespace Finset

variable {s : Finset α} {f : α -> Nat} {a : α}

/--
theorem `equitableOn_iff_le_le_add_one` / 定理 `equitableOn_iff_le_le_add_one`

English:
theorem equitableOn_iff_le_le_add_one
  proof: by
  rw [Set.equitableOn_iff_exists_le_le_add_one]
  refine ⟨?_, fun h => ⟨_, h⟩⟩
  rintro ⟨b, hb⟩
  by_cases! h : forall a in s, f a = b + 1
  · intro a ha
    rw [h _ ha]; rw [sum_const_nat h]; rw [Nat.mul_div_cancel_left _ (card_pos.2 ⟨a]; rw [ha⟩)]
    exact ⟨le_rfl, Nat.le_succ _⟩
  obtain ⟨x, 

中文:
定理 equitableOn_iff_le_le_add_one
  证明: by
  rw [Set.equitableOn_iff_exists_le_le_add_one]
  refine ⟨?_, fun h => ⟨_, h⟩⟩
  rintro ⟨b, hb⟩
  by_cases! h : forall a in s, f a = b + 1
  · intro a ha
    rw [h _ ha]; rw [sum_const_nat h]; rw [Nat.mul_div_cancel_left _ (card_pos.2 ⟨a]; rw [ha⟩)]
    exact ⟨le_rfl, Nat.le_succ _⟩
  obtain ⟨x, 

Depends on / 依赖: Nat.div_eq_of_lt_le, Nat.le_succ, Nat.mul_div_cancel_left, Set.equitableOn_iff_exists_le_le_add_one, card_pos, div_eq_of_lt_le, equitableOn_iff_exists_le_le_add_one, le_rfl, le_succ, le_trans, mul_comm, mul_div_cancel_left, s.card, simp_rw, sum_const_nat, sum_le_sum, sum_lt_sum
-/
theorem equitableOn_iff_le_le_add_one :
    EquitableOn (s : Set α) f ↔
      forall a in s, (∑ i in s, f i) / s.card <= f a ∧ f a <= (∑ i in s, f i) / s.card + 1 := by
  rw [Set.equitableOn_iff_exists_le_le_add_one]
  refine ⟨?_, fun h => ⟨_, h⟩⟩
  rintro ⟨b, hb⟩
  by_cases! h : forall a in s, f a = b + 1
  · intro a ha
    rw [h _ ha]; rw [sum_const_nat h]; rw [Nat.mul_div_cancel_left _ (card_pos.2 ⟨a]; rw [ha⟩)]
    exact ⟨le_rfl, Nat.le_succ _⟩
  obtain ⟨x, hx₁, hx₂⟩ := h
  suffices h : b = (∑ i in s, f i) / s.card by
    simp_rw [← h]
    apply hb
  symm
  refine
    Nat.div_eq_of_lt_le (le_trans (by simp [mul_comm]) (sum_le_sum fun a ha => (hb a ha).1))
      ((sum_lt_sum (fun a ha => (hb a ha).2) ⟨_, hx₁, (hb _ hx₁).2.lt_of_ne hx₂⟩).trans_le ?_)
  rw [mul_comm]; rw [sum_const_nat]
  exact fun _ _ => rfl

/--
theorem `EquitableOn.le` / 定理 `EquitableOn.le`

English:
theorem EquitableOn.le
  given: (h : EquitableOn (s : Set α) f) (ha : a in s)
  proof: (equitableOn_iff_le_le_add_one.1 h a ha).1

中文:
定理 EquitableOn.le
  条件: (h : EquitableOn (s : Set α) f) (ha : a in s)
  证明: (equitableOn_iff_le_le_add_one.1 h a ha).1

Depends on / 依赖: equitableOn_iff_le_le_add_one
-/
theorem EquitableOn.le (h : EquitableOn (s : Set α) f) (ha : a in s) :
    (∑ i in s, f i) / s.card <= f a :=
  (equitableOn_iff_le_le_add_one.1 h a ha).1

/--
theorem `EquitableOn.le_add_one` / 定理 `EquitableOn.le_add_one`

English:
theorem EquitableOn.le_add_one
  given: (h : EquitableOn (s : Set α) f) (ha : a in s)
  proof: (equitableOn_iff_le_le_add_one.1 h a ha).2

中文:
定理 EquitableOn.le_add_one
  条件: (h : EquitableOn (s : Set α) f) (ha : a in s)
  证明: (equitableOn_iff_le_le_add_one.1 h a ha).2

Depends on / 依赖: equitableOn_iff_le_le_add_one
-/
theorem EquitableOn.le_add_one (h : EquitableOn (s : Set α) f) (ha : a in s) :
    f a <= (∑ i in s, f i) / s.card + 1 :=
  (equitableOn_iff_le_le_add_one.1 h a ha).2

/--
theorem `equitableOn_iff` / 定理 `equitableOn_iff`

English:
theorem equitableOn_iff
  proof: by
  simp_rw [equitableOn_iff_le_le_add_one, Nat.le_and_le_add_one_iff]

中文:
定理 equitableOn_iff
  证明: by
  simp_rw [equitableOn_iff_le_le_add_one, Nat.le_and_le_add_one_iff]

Depends on / 依赖: Nat.le_and_le_add_one_iff, equitableOn_iff_le_le_add_one, le_and_le_add_one_iff, simp_rw
-/
theorem equitableOn_iff :
    EquitableOn (s : Set α) f ↔
      forall a in s, f a = (∑ i in s, f i) / s.card ∨ f a = (∑ i in s, f i) / s.card + 1 := by
  simp_rw [equitableOn_iff_le_le_add_one, Nat.le_and_le_add_one_iff]

end Finset
