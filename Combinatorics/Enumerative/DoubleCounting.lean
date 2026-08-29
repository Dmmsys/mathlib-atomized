/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Nat

/-!
# Double counting

This file gathers a few double counting arguments.

## Bipartite graphs

In a bipartite graph (considered as a relation `r : α → β → Prop`), we can bound the number of edges
between `s : Finset α` and `t : Finset β` by the minimum/maximum of edges over all `a ∈ s` times the
size of `s`. Similarly for `t`. Combining those two yields inequalities between the sizes of `s`
and `t`.

* `bipartiteBelow`: `s.bipartiteBelow r b` are the elements of `s` below `b` w.r.t. `r`. Its size
  is the number of edges of `b` in `s`.
* `bipartiteAbove`: `t.bipartite_Above r a` are the elements of `t` above `a` w.r.t. `r`. Its size
  is the number of edges of `a` in `t`.
* `card_mul_le_card_mul`, `card_mul_le_card_mul'`: Double counting the edges of a bipartite graph
  from below and from above.
* `card_mul_eq_card_mul`: Equality combination of the previous.

## Implementation notes

For the formulation of double-counting arguments where a bipartite graph is considered as a
bipartite simple graph `G : SimpleGraph V`, see `Mathlib/Combinatorics/SimpleGraph/Bipartite.lean`.
-/

@[expose] public section

assert_not_exists Field

open Finset Function Relator

variable {R α β : Type*}

/-! ### Bipartite graph -/


namespace Finset

section Bipartite

variable (r : α -> β -> Prop) (s : Finset α) (t : Finset β) (a : α) (b : β)
  [DecidablePred (r a)] [forall a, Decidable (r a b)] {m n : Nat}

/--
Definition of `bipartiteBelow` / `bipartiteBelow` 的定义

English:
definition bipartiteBelow
  signature: : Finset α
  body: {a in s | r a b}

中文:
定义 bipartiteBelow
  签名: : 有限集 α
  定义体: {a in s | r a b}
-/
def bipartiteBelow : Finset α := {a in s | r a b}

/--
Definition of `bipartiteAbove` / `bipartiteAbove` 的定义

English:
definition bipartiteAbove
  signature: : Finset β
  body: {b in t | r a b}

中文:
定义 bipartiteAbove
  签名: : 有限集 β
  定义体: {b in t | r a b}
-/
def bipartiteAbove : Finset β := {b in t | r a b}

/--
theorem `bipartiteBelow_swap` / 定理 `bipartiteBelow_swap`

English:
theorem bipartiteBelow_swap
  statement: t.bipartiteBelow (swap r) a = t.bipartiteAbove r a
  proof: rfl

中文:
定理 bipartiteBelow_swap
  结论: t.bipartiteBelow (swap r) a = t.bipartiteAbove r a
  证明: rfl
-/
theorem bipartiteBelow_swap : t.bipartiteBelow (swap r) a = t.bipartiteAbove r a := rfl

/--
theorem `bipartiteAbove_swap` / 定理 `bipartiteAbove_swap`

English:
theorem bipartiteAbove_swap
  statement: s.bipartiteAbove (swap r) b = s.bipartiteBelow r b
  proof: rfl

@[simp, norm_cast]

中文:
定理 bipartiteAbove_swap
  结论: s.bipartiteAbove (swap r) b = s.bipartiteBelow r b
  证明: rfl

@[simp, norm_cast]
-/
theorem bipartiteAbove_swap : s.bipartiteAbove (swap r) b = s.bipartiteBelow r b := rfl

@[simp, norm_cast]
/--
theorem `coe_bipartiteBelow` / 定理 `coe_bipartiteBelow`

English:
theorem coe_bipartiteBelow
  statement: s.bipartiteBelow r b = ({a in s | r a b} : Set α)
  proof: coe_filter _ _

@[simp, norm_cast]

中文:
定理 coe_bipartiteBelow
  结论: s.bipartiteBelow r b = ({a in s | r a b} : 集合 α)
  证明: coe_filter _ _

@[simp, norm_cast]

Depends on / 依赖: coe_filter
-/
theorem coe_bipartiteBelow : s.bipartiteBelow r b = ({a in s | r a b} : Set α) := coe_filter _ _

@[simp, norm_cast]
/--
theorem `coe_bipartiteAbove` / 定理 `coe_bipartiteAbove`

English:
theorem coe_bipartiteAbove
  statement: t.bipartiteAbove r a = ({b in t | r a b} : Set β)
  proof: coe_filter _ _

中文:
定理 coe_bipartiteAbove
  结论: t.bipartiteAbove r a = ({b in t | r a b} : 集合 β)
  证明: coe_filter _ _

Depends on / 依赖: coe_filter
-/
theorem coe_bipartiteAbove : t.bipartiteAbove r a = ({b in t | r a b} : Set β) := coe_filter _ _

variable {s t a b}

@[simp]
/--
theorem `mem_bipartiteBelow` / 定理 `mem_bipartiteBelow`

English:
theorem mem_bipartiteBelow
  given: {a : α}
  statement: a in s.bipartiteBelow r b ↔ a in s ∧ r a b
  proof: mem_filter

@[simp]

中文:
定理 mem_bipartiteBelow
  条件: {a : α}
  结论: a in s.bipartiteBelow r b ↔ a in s ∧ r a b
  证明: mem_filter

@[simp]

Depends on / 依赖: CostructuredArrow, CostructuredArrow.pre, Skeleton, Skeleton.incl.op, asEquivalence, hasColimitsOfShape_of_equivalence, mem_filter
-/
theorem mem_bipartiteBelow {a : α} : a in s.bipartiteBelow r b ↔ a in s ∧ r a b := mem_filter

@[simp]
/--
theorem `mem_bipartiteAbove` / 定理 `mem_bipartiteAbove`

English:
theorem mem_bipartiteAbove
  given: {b : β}
  statement: b in t.bipartiteAbove r a ↔ b in t ∧ r a b
  proof: mem_filter

@[to_additive]

中文:
定理 mem_bipartiteAbove
  条件: {b : β}
  结论: b in t.bipartiteAbove r a ↔ b in t ∧ r a b
  证明: mem_filter

@[to_additive]

Depends on / 依赖: mem_filter
-/
theorem mem_bipartiteAbove {b : β} : b in t.bipartiteAbove r a ↔ b in t ∧ r a b := mem_filter

@[to_additive]
/--
theorem `prod_prod_bipartiteAbove_eq_prod_prod_bipartiteBelow` / 定理 `prod_prod_bipartiteAbove_eq_prod_prod_bipartiteBelow`

English:
theorem prod_prod_bipartiteAbove_eq_prod_prod_bipartiteBelow
  proof: by
  simp_rw [bipartiteAbove, bipartiteBelow, prod_filter]
  exact prod_comm

中文:
定理 prod_prod_bipartiteAbove_eq_prod_prod_bipartiteBelow
  证明: by
  simp_rw [bipartiteAbove, bipartiteBelow, prod_filter]
  exact prod_comm

Depends on / 依赖: bipartiteAbove, bipartiteBelow, prod_comm, prod_filter, simp_rw
-/
theorem prod_prod_bipartiteAbove_eq_prod_prod_bipartiteBelow
    [CommMonoid R] (f : α -> β -> R) [forall a b, Decidable (r a b)] :
    ∏ a in s, ∏ b in t.bipartiteAbove r a, f a b = ∏ b in t, ∏ a in s.bipartiteBelow r b, f a b := by
  simp_rw [bipartiteAbove, bipartiteBelow, prod_filter]
  exact prod_comm

/--
theorem `sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow` / 定理 `sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow`

English:
theorem sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
  given: [forall a b, Decidable (r a b)]
  proof: by
  simp_rw [card_eq_sum_ones, sum_sum_bipartiteAbove_eq_sum_sum_bipartiteBelow]

中文:
定理 sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
  条件: [对任意 a b, 可判定 (r a b)]
  证明: by
  simp_rw [card_eq_sum_ones, sum_sum_bipartiteAbove_eq_sum_sum_bipartiteBelow]

Depends on / 依赖: card_eq_sum_ones, simp_rw, sum_sum_bipartiteAbove_eq_sum_sum_bipartiteBelow
-/
theorem sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow [forall a b, Decidable (r a b)] :
    (∑ a in s, #(t.bipartiteAbove r a)) = ∑ b in t, #(s.bipartiteBelow r b) := by
  simp_rw [card_eq_sum_ones, sum_sum_bipartiteAbove_eq_sum_sum_bipartiteBelow]

section OrderedSemiring
variable [Semiring R] [PartialOrder R] [IsOrderedRing R] {m n : R}

/--
theorem `card_nsmul_le_card_nsmul` / 定理 `card_nsmul_le_card_nsmul`

English:
theorem card_nsmul_le_card_nsmul
  statement: [forall a b, Decidable (r a b)]
  proof: calc
    _ <= ∑ a in s, (#(t.bipartiteAbove r a) : R) := s.card_nsmul_le_sum _ _ hm
    _ = ∑ b in t, (#(s.bipartiteBelow r b) : R) := by
      norm_cast; rw [sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
    _ <= _ := t.sum_le_card_nsmul _ _ hn

中文:
定理 card_nsmul_le_card_nsmul
  结论: [对任意 a b, 可判定 (r a b)]
  证明: calc
    _ <= ∑ a in s, (#(t.bipartiteAbove r a) : R) := s.card_nsmul_le_sum _ _ hm
    _ = ∑ b in t, (#(s.bipartiteBelow r b) : R) := by
      norm_cast; rw [sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
    _ <= _ := t.sum_le_card_nsmul _ _ hn

Depends on / 依赖: bipartiteAbove, bipartiteBelow, card_nsmul_le_sum, s.bipartiteBelow, s.card_nsmul_le_sum, sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow, sum_le_card_nsmul, t.bipartiteAbove, t.sum_le_card_nsmul
-/
theorem card_nsmul_le_card_nsmul [forall a b, Decidable (r a b)]
    (hm : forall a in s, m <= #(t.bipartiteAbove r a))
    (hn : forall b in t, #(s.bipartiteBelow r b) <= n) : #s • m <= #t • n :=
  calc
    _ <= ∑ a in s, (#(t.bipartiteAbove r a) : R) := s.card_nsmul_le_sum _ _ hm
    _ = ∑ b in t, (#(s.bipartiteBelow r b) : R) := by
      norm_cast; rw [sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
    _ <= _ := t.sum_le_card_nsmul _ _ hn

/--
theorem `card_nsmul_le_card_nsmul'` / 定理 `card_nsmul_le_card_nsmul'`

English:
theorem card_nsmul_le_card_nsmul'
  statement: [forall a b, Decidable (r a b)]
  proof: card_nsmul_le_card_nsmul (swap r) hn hm

中文:
定理 card_nsmul_le_card_nsmul'
  结论: [对任意 a b, 可判定 (r a b)]
  证明: card_nsmul_le_card_nsmul (swap r) hn hm

Depends on / 依赖: card_nsmul_le_card_nsmul
-/
theorem card_nsmul_le_card_nsmul' [forall a b, Decidable (r a b)]
    (hn : forall b in t, n <= #(s.bipartiteBelow r b))
    (hm : forall a in s, #(t.bipartiteAbove r a) <= m) : #t • n <= #s • m :=
  card_nsmul_le_card_nsmul (swap r) hn hm

end OrderedSemiring

section StrictOrderedSemiring
variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] (r : α -> β -> Prop)
  {s : Finset α} {t : Finset β} (a b) {m n : R}

/--
theorem `card_nsmul_lt_card_nsmul_of_lt_of_le` / 定理 `card_nsmul_lt_card_nsmul_of_lt_of_le`

English:
theorem card_nsmul_lt_card_nsmul_of_lt_of_le
  statement: [forall a b, Decidable (r a b)] (hs : s.Nonempty)
  proof: calc
    _ = ∑ _a in s, m := by rw [sum_const]
    _ < ∑ a in s, (#(t.bipartiteAbove r a) : R) := sum_lt_sum_of_nonempty hs hm
    _ = ∑ b in t, (#(s.bipartiteBelow r b) : R) := by
      norm_cast; rw [sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
    _ <= _ := t.sum_le_card_nsmul _ _ hn

中文:
定理 card_nsmul_lt_card_nsmul_of_lt_of_le
  结论: [对任意 a b, 可判定 (r a b)] (hs : s.非空)
  证明: calc
    _ = ∑ _a in s, m := by rw [sum_const]
    _ < ∑ a in s, (#(t.bipartiteAbove r a) : R) := sum_lt_sum_of_nonempty hs hm
    _ = ∑ b in t, (#(s.bipartiteBelow r b) : R) := by
      norm_cast; rw [sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
    _ <= _ := t.sum_le_card_nsmul _ _ hn

Depends on / 依赖: bipartiteAbove, bipartiteBelow, s.bipartiteBelow, sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow, sum_const, sum_le_card_nsmul, sum_lt_sum_of_nonempty, t.bipartiteAbove, t.sum_le_card_nsmul
-/
theorem card_nsmul_lt_card_nsmul_of_lt_of_le [forall a b, Decidable (r a b)] (hs : s.Nonempty)
    (hm : forall a in s, m < #(t.bipartiteAbove r a))
    (hn : forall b in t, #(s.bipartiteBelow r b) <= n) : #s • m < #t • n :=
  calc
    _ = ∑ _a in s, m := by rw [sum_const]
    _ < ∑ a in s, (#(t.bipartiteAbove r a) : R) := sum_lt_sum_of_nonempty hs hm
    _ = ∑ b in t, (#(s.bipartiteBelow r b) : R) := by
      norm_cast; rw [sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
    _ <= _ := t.sum_le_card_nsmul _ _ hn

/--
theorem `card_nsmul_lt_card_nsmul_of_le_of_lt` / 定理 `card_nsmul_lt_card_nsmul_of_le_of_lt`

English:
theorem card_nsmul_lt_card_nsmul_of_le_of_lt
  statement: [forall a b, Decidable (r a b)] (ht : t.Nonempty)
  proof: calc
    _ <= ∑ a in s, (#(t.bipartiteAbove r a) : R) := s.card_nsmul_le_sum _ _ hm
    _ = ∑ b in t, (#(s.bipartiteBelow r b) : R) := by
      norm_cast; rw [sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
    _ < ∑ _b in t, n := sum_lt_sum_of_nonempty ht hn
    _ = _ := sum_const _

中文:
定理 card_nsmul_lt_card_nsmul_of_le_of_lt
  结论: [对任意 a b, 可判定 (r a b)] (ht : t.非空)
  证明: calc
    _ <= ∑ a in s, (#(t.bipartiteAbove r a) : R) := s.card_nsmul_le_sum _ _ hm
    _ = ∑ b in t, (#(s.bipartiteBelow r b) : R) := by
      norm_cast; rw [sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
    _ < ∑ _b in t, n := sum_lt_sum_of_nonempty ht hn
    _ = _ := sum_const _

Depends on / 依赖: bipartiteAbove, bipartiteBelow, card_nsmul_le_sum, s.bipartiteBelow, s.card_nsmul_le_sum, sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow, sum_const, sum_lt_sum_of_nonempty, t.bipartiteAbove
-/
theorem card_nsmul_lt_card_nsmul_of_le_of_lt [forall a b, Decidable (r a b)] (ht : t.Nonempty)
    (hm : forall a in s, m <= #(t.bipartiteAbove r a))
    (hn : forall b in t, #(s.bipartiteBelow r b) < n) : #s • m < #t • n :=
  calc
    _ <= ∑ a in s, (#(t.bipartiteAbove r a) : R) := s.card_nsmul_le_sum _ _ hm
    _ = ∑ b in t, (#(s.bipartiteBelow r b) : R) := by
      norm_cast; rw [sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
    _ < ∑ _b in t, n := sum_lt_sum_of_nonempty ht hn
    _ = _ := sum_const _

/--
theorem `card_nsmul_lt_card_nsmul_of_lt_of_le'` / 定理 `card_nsmul_lt_card_nsmul_of_lt_of_le'`

English:
theorem card_nsmul_lt_card_nsmul_of_lt_of_le'
  statement: [forall a b, Decidable (r a b)] (ht : t.Nonempty)
  proof: card_nsmul_lt_card_nsmul_of_lt_of_le (swap r) ht hn hm

中文:
定理 card_nsmul_lt_card_nsmul_of_lt_of_le'
  结论: [对任意 a b, 可判定 (r a b)] (ht : t.非空)
  证明: card_nsmul_lt_card_nsmul_of_lt_of_le (swap r) ht hn hm

Depends on / 依赖: card_nsmul_lt_card_nsmul_of_lt_of_le
-/
theorem card_nsmul_lt_card_nsmul_of_lt_of_le' [forall a b, Decidable (r a b)] (ht : t.Nonempty)
    (hn : forall b in t, n < #(s.bipartiteBelow r b))
    (hm : forall a in s, #(t.bipartiteAbove r a) <= m) : #t • n < #s • m :=
  card_nsmul_lt_card_nsmul_of_lt_of_le (swap r) ht hn hm

/--
theorem `card_nsmul_lt_card_nsmul_of_le_of_lt'` / 定理 `card_nsmul_lt_card_nsmul_of_le_of_lt'`

English:
theorem card_nsmul_lt_card_nsmul_of_le_of_lt'
  statement: [forall a b, Decidable (r a b)] (hs : s.Nonempty)
  proof: card_nsmul_lt_card_nsmul_of_le_of_lt (swap r) hs hn hm

中文:
定理 card_nsmul_lt_card_nsmul_of_le_of_lt'
  结论: [对任意 a b, 可判定 (r a b)] (hs : s.非空)
  证明: card_nsmul_lt_card_nsmul_of_le_of_lt (swap r) hs hn hm

Depends on / 依赖: card_nsmul_lt_card_nsmul_of_le_of_lt
-/
theorem card_nsmul_lt_card_nsmul_of_le_of_lt' [forall a b, Decidable (r a b)] (hs : s.Nonempty)
    (hn : forall b in t, n <= #(s.bipartiteBelow r b))
    (hm : forall a in s, #(t.bipartiteAbove r a) < m) : #t • n < #s • m :=
  card_nsmul_lt_card_nsmul_of_le_of_lt (swap r) hs hn hm

end StrictOrderedSemiring

/--
theorem `card_mul_le_card_mul` / 定理 `card_mul_le_card_mul`

English:
theorem card_mul_le_card_mul
  statement: [forall a b, Decidable (r a b)]
  proof: card_nsmul_le_card_nsmul _ hm hn

中文:
定理 card_mul_le_card_mul
  结论: [对任意 a b, 可判定 (r a b)]
  证明: card_nsmul_le_card_nsmul _ hm hn

Depends on / 依赖: card_nsmul_le_card_nsmul
-/
theorem card_mul_le_card_mul [forall a b, Decidable (r a b)]
    (hm : forall a in s, m <= #(t.bipartiteAbove r a))
    (hn : forall b in t, #(s.bipartiteBelow r b) <= n) : #s * m <= #t * n :=
  card_nsmul_le_card_nsmul _ hm hn

/--
theorem `card_mul_le_card_mul'` / 定理 `card_mul_le_card_mul'`

English:
theorem card_mul_le_card_mul'
  statement: [forall a b, Decidable (r a b)]
  proof: card_nsmul_le_card_nsmul' _ hn hm

中文:
定理 card_mul_le_card_mul'
  结论: [对任意 a b, 可判定 (r a b)]
  证明: card_nsmul_le_card_nsmul' _ hn hm

Depends on / 依赖: card_nsmul_le_card_nsmul
-/
theorem card_mul_le_card_mul' [forall a b, Decidable (r a b)]
    (hn : forall b in t, n <= #(s.bipartiteBelow r b))
    (hm : forall a in s, #(t.bipartiteAbove r a) <= m) : #t * n <= #s * m :=
  card_nsmul_le_card_nsmul' _ hn hm

/--
theorem `card_mul_eq_card_mul` / 定理 `card_mul_eq_card_mul`

English:
theorem card_mul_eq_card_mul
  statement: [forall a b, Decidable (r a b)]
  proof: (card_mul_le_card_mul _ (fun a ha => (hm a ha).ge) fun b hb => (hn b hb).le).antisymm
    card_mul_le_card_mul' _ (fun a ha => (hn a ha).ge) fun b hb => (hm b hb).le

中文:
定理 card_mul_eq_card_mul
  结论: [对任意 a b, 可判定 (r a b)]
  证明: (card_mul_le_card_mul _ (fun a ha => (hm a ha).ge) fun b hb => (hn b hb).le).antisymm
    card_mul_le_card_mul' _ (fun a ha => (hn a ha).ge) fun b hb => (hm b hb).le

Depends on / 依赖: antisymm, card_mul_le_card_mul
-/
theorem card_mul_eq_card_mul [forall a b, Decidable (r a b)]
    (hm : forall a in s, #(t.bipartiteAbove r a) = m)
    (hn : forall b in t, #(s.bipartiteBelow r b) = n) : #s * m = #t * n :=
(card_mul_le_card_mul _ (fun a ha => (hm a ha).ge) fun b hb => (hn b hb).le).antisymm
    card_mul_le_card_mul' _ (fun a ha => (hn a ha).ge) fun b hb => (hm b hb).le

/--
theorem `card_le_card_of_forall_subsingleton` / 定理 `card_le_card_of_forall_subsingleton`

English:
theorem card_le_card_of_forall_subsingleton
  statement: (hs : forall a in s, exists b, b in t ∧ r a b)
  proof: by
  classical
    rw [← mul_one #s]; rw [← mul_one #t]
    exact card_mul_le_card_mul r
      (fun a h => card_pos.2 (by
        rw [← coe_nonempty]; rw [coe_bipartiteAbove]
        exact hs _ h : (t.bipartiteAbove r a).Nonempty))
      (fun b h => card_le_one.2 (by
        simp_rw [mem_bipartiteBelow]
        exact ht _ h))

中文:
定理 card_le_card_of_对任意_subsingleton
  结论: (hs : 对任意 a in s, 存在 b, b in t ∧ r a b)
  证明: by
  classical
    rw [← mul_one #s]; rw [← mul_one #t]
    exact card_mul_le_card_mul r
      (fun a h => card_pos.2 (by
        rw [← coe_nonempty]; rw [coe_bipartiteAbove]
        exact hs _ h : (t.bipartiteAbove r a).Nonempty))
      (fun b h => card_le_one.2 (by
        simp_rw [mem_bipartiteBelow]
        exact ht _ h))

Depends on / 依赖: Nonempty, bipartiteAbove, card_le_one, card_mul_le_card_mul, card_pos, classical, coe_bipartiteAbove, coe_nonempty, mem_bipartiteBelow, mul_one, simp_rw, t.bipartiteAbove
-/
theorem card_le_card_of_forall_subsingleton (hs : forall a in s, exists b, b in t ∧ r a b)
    (ht : forall b in t, ({ a in s | r a b } : Set α).Subsingleton) : #s <= #t := by
  classical
    rw [← mul_one #s]; rw [← mul_one #t]
    exact card_mul_le_card_mul r
      (fun a h => card_pos.2 (by
        rw [← coe_nonempty]; rw [coe_bipartiteAbove]
        exact hs _ h : (t.bipartiteAbove r a).Nonempty))
      (fun b h => card_le_one.2 (by
        simp_rw [mem_bipartiteBelow]
        exact ht _ h))

/--
theorem `card_le_card_of_forall_subsingleton'` / 定理 `card_le_card_of_forall_subsingleton'`

English:
theorem card_le_card_of_forall_subsingleton'
  statement: (ht : forall b in t, exists a, a in s ∧ r a b)
  proof: card_le_card_of_forall_subsingleton (swap r) ht hs

中文:
定理 card_le_card_of_对任意_subsingleton'
  结论: (ht : 对任意 b in t, 存在 a, a in s ∧ r a b)
  证明: card_le_card_of_forall_subsingleton (swap r) ht hs

Depends on / 依赖: card_le_card_of_forall_subsingleton
-/
theorem card_le_card_of_forall_subsingleton' (ht : forall b in t, exists a, a in s ∧ r a b)
    (hs : forall a in s, ({ b in t | r a b } : Set β).Subsingleton) : #t <= #s :=
  card_le_card_of_forall_subsingleton (swap r) ht hs

/--
lemma `sum_card_eq_sum_biUnion_card` / 引理 `sum_card_eq_sum_biUnion_card`

English:
lemma sum_card_eq_sum_biUnion_card
  statement: [Fintype α] [DecidableEq α] [DecidableEq β]
  proof: by
  convert sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun j x => x in B j)
  · grind [bipartiteAbove]
  · grind [bipartiteBelow]

中文:
引理 sum_card_eq_sum_biUnion_card
  结论: [有限类型 α] [DecidableEq α] [DecidableEq β]
  证明: by
  convert sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun j x => x in B j)
  · grind [bipartiteAbove]
  · grind [bipartiteBelow]

Depends on / 依赖: Countable, Countable.toSmall, Discrete, Discrete.equivalence, Finite, Finite.of_equiv, bipartiteAbove, bipartiteBelow, choose_spec, convert, e.symm, equiv_small, equiv_small.choose, equiv_small.choose_spec.some, equivalence, of_equiv, preservesLimitsOfShape_of_equiv, sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow, toSmall
-/
lemma sum_card_eq_sum_biUnion_card [Fintype α] [DecidableEq α] [DecidableEq β]
    (B : α -> Finset β) (s : Finset α) :
    ∑ j in s, #(B j) = ∑ x in s.biUnion B, #{j | j in s ∧ x in B j} := by
  convert sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun j x => x in B j)
  · grind [bipartiteAbove]
  · grind [bipartiteBelow]

end Bipartite

end Finset

namespace Fintype

variable [Fintype α] [Fintype β] {r : α -> β -> Prop}

/--
theorem `card_le_card_of_leftTotal_unique` / 定理 `card_le_card_of_leftTotal_unique`

English:
theorem card_le_card_of_leftTotal_unique
  given: (h₁ : LeftTotal r) (h₂ : LeftUnique r)
  proof: card_le_card_of_forall_subsingleton r (by simpa using! h₁) fun _ _ _ ha₁ _ ha₂ => h₂ ha₁.2 ha₂.2

中文:
定理 card_le_card_of_leftTotal_unique
  条件: (h₁ : LeftTotal r) (h₂ : LeftUnique r)
  证明: card_le_card_of_forall_subsingleton r (by simpa using! h₁) fun _ _ _ ha₁ _ ha₂ => h₂ ha₁.2 ha₂.2

Depends on / 依赖: card_le_card_of_forall_subsingleton
-/
theorem card_le_card_of_leftTotal_unique (h₁ : LeftTotal r) (h₂ : LeftUnique r) :
    Fintype.card α <= Fintype.card β :=
  card_le_card_of_forall_subsingleton r (by simpa using! h₁) fun _ _ _ ha₁ _ ha₂ => h₂ ha₁.2 ha₂.2

/--
theorem `card_le_card_of_rightTotal_unique` / 定理 `card_le_card_of_rightTotal_unique`

English:
theorem card_le_card_of_rightTotal_unique
  given: (h₁ : RightTotal r) (h₂ : RightUnique r)
  proof: card_le_card_of_forall_subsingleton' r (by simpa using! h₁) fun _ _ _ ha₁ _ ha₂ => h₂ ha₁.2 ha₂.2

中文:
定理 card_le_card_of_rightTotal_unique
  条件: (h₁ : RightTotal r) (h₂ : RightUnique r)
  证明: card_le_card_of_forall_subsingleton' r (by simpa using! h₁) fun _ _ _ ha₁ _ ha₂ => h₂ ha₁.2 ha₂.2

Depends on / 依赖: card_le_card_of_forall_subsingleton
-/
theorem card_le_card_of_rightTotal_unique (h₁ : RightTotal r) (h₂ : RightUnique r) :
    Fintype.card β <= Fintype.card α :=
  card_le_card_of_forall_subsingleton' r (by simpa using! h₁) fun _ _ _ ha₁ _ ha₂ => h₂ ha₁.2 ha₂.2

end Fintype
