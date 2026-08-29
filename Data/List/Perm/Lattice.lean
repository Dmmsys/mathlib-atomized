/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Data.List.Forall2
public import Mathlib.Data.List.TakeDrop
public import Mathlib.Data.List.Lattice
public import Mathlib.Data.List.Nodup

/-!
# List Permutations and list lattice operations.

This file develops theory about the `List.Perm` relation and the lattice structure on lists.
-/

public section

-- Make sure we don't import algebra
assert_not_exists Monoid

open Nat

namespace List
variable {α : Type*}

open Perm (swap)

variable [DecidableEq α]

/--
theorem `Perm.bagInter_right` / 定理 `Perm.bagInter_right`

English:
theorem Perm.bagInter_right
  given: {l₁ l₂ : List α} (t : List α) (h : l₁ ~ l₂)
  proof: by
  induction h generalizing t with grind

中文:
定理 置换.bag整数er_right
  条件: {l₁ l₂ : 列表 α} (t : 列表 α) (h : l₁ ~ l₂)
  证明: by
  induction h generalizing t with grind

Depends on / 依赖: generalizing
-/
theorem Perm.bagInter_right {l₁ l₂ : List α} (t : List α) (h : l₁ ~ l₂) :
    l₁.bagInter t ~ l₂.bagInter t := by
  induction h generalizing t with grind

/--
theorem `Perm.bagInter_left` / 定理 `Perm.bagInter_left`

English:
theorem Perm.bagInter_left
  given: (l : List α) {t₁ t₂ : List α} (p : t₁ ~ t₂)
  proof: by
  induction l generalizing t₁ t₂ p with | nil => simp | cons a l IH => ?_
  by_cases h : a in t₁
  · simp [h, p.subset h, IH (p.erase _)]
  · simp [h, mt p.mem_iff.2 h, IH p]

中文:
定理 置换.bag整数er_left
  条件: (l : 列表 α) {t₁ t₂ : 列表 α} (p : t₁ ~ t₂)
  证明: by
  induction l generalizing t₁ t₂ p with | nil => simp | cons a l IH => ?_
  by_cases h : a in t₁
  · simp [h, p.subset h, IH (p.erase _)]
  · simp [h, mt p.mem_iff.2 h, IH p]

Depends on / 依赖: generalizing, mem_iff, p.erase, p.mem_iff, p.subset, subset
-/
theorem Perm.bagInter_left (l : List α) {t₁ t₂ : List α} (p : t₁ ~ t₂) :
    l.bagInter t₁ = l.bagInter t₂ := by
  induction l generalizing t₁ t₂ p with | nil => simp | cons a l IH => ?_
  by_cases h : a in t₁
  · simp [h, p.subset h, IH (p.erase _)]
  · simp [h, mt p.mem_iff.2 h, IH p]

/--
theorem `Perm.bagInter` / 定理 `Perm.bagInter`

English:
theorem Perm.bagInter
  given: {l₁ l₂ t₁ t₂ : List α} (hl : l₁ ~ l₂) (ht : t₁ ~ t₂)
  proof: ht.bagInter_left l₂ ▸ hl.bagInter_right _

中文:
定理 置换.bag整数er
  条件: {l₁ l₂ t₁ t₂ : 列表 α} (hl : l₁ ~ l₂) (ht : t₁ ~ t₂)
  证明: ht.bagInter_left l₂ ▸ hl.bagInter_right _

Depends on / 依赖: bagInter_left, bagInter_right, hl.bagInter_right, ht.bagInter_left
-/
theorem Perm.bagInter {l₁ l₂ t₁ t₂ : List α} (hl : l₁ ~ l₂) (ht : t₁ ~ t₂) :
    l₁.bagInter t₁ ~ l₂.bagInter t₂ :=
  ht.bagInter_left l₂ ▸ hl.bagInter_right _

/--
theorem `Perm.bagInter_symm` / 定理 `Perm.bagInter_symm`

English:
theorem Perm.bagInter_symm
  given: (l₁ l₂ : List α)
  statement: (l₁.bagInter l₂).Perm (l₂.bagInter l₁)
  proof: perm_iff_count.mpr fun _ => (by simp [List.count_bagInter, Nat.min_comm])

中文:
定理 置换.bag整数er_symm
  条件: (l₁ l₂ : 列表 α)
  结论: (l₁.bag整数er l₂).置换 (l₂.bag整数er l₁)
  证明: perm_iff_count.mpr fun _ => (by simp [List.count_bagInter, Nat.min_comm])

Depends on / 依赖: List.count_bagInter, Nat.min_comm, count_bagInter, min_comm, perm_iff_count, perm_iff_count.mpr
-/
theorem Perm.bagInter_symm (l₁ l₂ : List α) : (l₁.bagInter l₂).Perm (l₂.bagInter l₁) :=
  perm_iff_count.mpr fun _ => (by simp [List.count_bagInter, Nat.min_comm])

/--
theorem `Perm.inter_append` / 定理 `Perm.inter_append`

English:
theorem Perm.inter_append
  given: {l t₁ t₂ : List α} (h : Disjoint t₁ t₂)
  proof: by
  induction l with
  | nil => simp
  | cons x xs l_ih =>
    by_cases h₁ : x in t₁
    · have h₂ : x ∉ t₂ := h h₁
      simp [*]
    by_cases h₂ : x in t₂
    · simp only [*, inter_cons_of_notMem, false_or, mem_append, inter_cons_of_mem,
        not_false_iff]
      exact perm_cons_append_cons _ l_ih
    · simp [*]

中文:
定理 置换.inter_append
  条件: {l t₁ t₂ : 列表 α} (h : Disjoint t₁ t₂)
  证明: by
  induction l with
  | nil => simp
  | cons x xs l_ih =>
    by_cases h₁ : x in t₁
    · have h₂ : x ∉ t₂ := h h₁
      simp [*]
    by_cases h₂ : x in t₂
    · simp only [*, inter_cons_of_notMem, false_or, mem_append, inter_cons_of_mem,
        not_false_iff]
      exact perm_cons_append_cons _ l_ih
    · simp [*]

Depends on / 依赖: false_or, inter_cons_of_mem, inter_cons_of_notMem, l_ih, mem_append, not_false_iff, perm_cons_append_cons
-/
theorem Perm.inter_append {l t₁ t₂ : List α} (h : Disjoint t₁ t₂) :
    l inter (t₁ ++ t₂) ~ l inter t₁ ++ l inter t₂ := by
  induction l with
  | nil => simp
  | cons x xs l_ih =>
    by_cases h₁ : x in t₁
    · have h₂ : x ∉ t₂ := h h₁
      simp [*]
    by_cases h₂ : x in t₂
    · simp only [*, inter_cons_of_notMem, false_or, mem_append, inter_cons_of_mem,
        not_false_iff]
      exact perm_cons_append_cons _ l_ih
    · simp [*]

/--
theorem `Perm.take_inter` / 定理 `Perm.take_inter`

English:
theorem Perm.take_inter
  statement: {xs ys : List α} (n : Nat) (h : xs ~ ys)
  proof: calc
  xs.take n ~ xs.filter (xs.take n).elem := by
    conv_lhs => rw [Nodup.take_eq_filter_mem ((Perm.nodup_iff h).2 h')]
  _ ~ ys inter (xs.take n) := Perm.filter _ h

中文:
定理 置换.take_inter
  结论: {xs ys : 列表 α} (n : 自然数) (h : xs ~ ys)
  证明: calc
  xs.take n ~ xs.filter (xs.take n).elem := by
    conv_lhs => rw [Nodup.take_eq_filter_mem ((Perm.nodup_iff h).2 h')]
  _ ~ ys inter (xs.take n) := Perm.filter _ h
-/
theorem Perm.take_inter {xs ys : List α} (n : Nat) (h : xs ~ ys)
    (h' : ys.Nodup) : xs.take n ~ ys inter (xs.take n) := calc
  xs.take n ~ xs.filter (xs.take n).elem := by
    conv_lhs => rw [Nodup.take_eq_filter_mem ((Perm.nodup_iff h).2 h')]
  _ ~ ys inter (xs.take n) := Perm.filter _ h

/--
theorem `Perm.drop_inter` / 定理 `Perm.drop_inter`

English:
theorem Perm.drop_inter
  given: {xs ys : List α} (n : Nat) (h : xs ~ ys) (h' : ys.Nodup)
  proof: by
  by_cases h'' : n <= xs.length
  · let n' := xs.length - n
    have h₀ : n = xs.length - n' := by rwa [Nat.sub_sub_self]
    have h₁ : xs.drop n = (xs.reverse.take n').reverse := by
      rw [take_reverse]; rw [h₀]; rw [reverse_reverse]
    rw [h₁]
    apply (reverse_perm _).trans
    rw [inter_reverse]
    apply Perm.take_inter _ _ h'
    apply (reverse_perm _).trans; assumption
  · grind [drop_eq_nil_of_le]

中文:
定理 置换.drop_inter
  条件: {xs ys : 列表 α} (n : 自然数) (h : xs ~ ys) (h' : ys.Nodup)
  证明: by
  by_cases h'' : n <= xs.length
  · let n' := xs.length - n
    have h₀ : n = xs.length - n' := by rwa [Nat.sub_sub_self]
    have h₁ : xs.drop n = (xs.reverse.take n').reverse := by
      rw [take_reverse]; rw [h₀]; rw [reverse_reverse]
    rw [h₁]
    apply (reverse_perm _).trans
    rw [inter_reverse]
    apply Perm.take_inter _ _ h'
    apply (reverse_perm _).trans; assumption
  · grind [drop_eq_nil_of_le]

Depends on / 依赖: Nat.sub_sub_self, Perm.take_inter, drop_eq_nil_of_le, inter_reverse, length, reverse, reverse_perm, reverse_reverse, sub_sub_self, take_inter, take_reverse, xs.drop, xs.length, xs.reverse.take
-/
theorem Perm.drop_inter {xs ys : List α} (n : Nat) (h : xs ~ ys) (h' : ys.Nodup) :
    xs.drop n ~ ys inter (xs.drop n) := by
  by_cases h'' : n <= xs.length
  · let n' := xs.length - n
    have h₀ : n = xs.length - n' := by rwa [Nat.sub_sub_self]
    have h₁ : xs.drop n = (xs.reverse.take n').reverse := by
      rw [take_reverse]; rw [h₀]; rw [reverse_reverse]
    rw [h₁]
    apply (reverse_perm _).trans
    rw [inter_reverse]
    apply Perm.take_inter _ _ h'
    apply (reverse_perm _).trans; assumption
  · grind [drop_eq_nil_of_le]

/--
theorem `Perm.dropSlice_inter` / 定理 `Perm.dropSlice_inter`

English:
theorem Perm.dropSlice_inter
  statement: {xs ys : List α} (n m : Nat) (h : xs ~ ys)
  proof: by
  simp only [dropSlice_eq]
  have : n <= n + m := Nat.le_add_right _ _
  have h₂ := h.nodup_iff.2 h'
  apply Perm.trans _ (Perm.inter_append _).symm
  · exact Perm.append (Perm.take_inter _ h h') (Perm.drop_inter _ h h')
  · exact disjoint_take_drop h₂ this

中文:
定理 置换.dropSlice_inter
  结论: {xs ys : 列表 α} (n m : 自然数) (h : xs ~ ys)
  证明: by
  simp only [dropSlice_eq]
  have : n <= n + m := Nat.le_add_right _ _
  have h₂ := h.nodup_iff.2 h'
  apply Perm.trans _ (Perm.inter_append _).symm
  · exact Perm.append (Perm.take_inter _ h h') (Perm.drop_inter _ h h')
  · exact disjoint_take_drop h₂ this

Depends on / 依赖: Nat.le_add_right, Perm.append, Perm.drop_inter, Perm.inter_append, Perm.take_inter, Perm.trans, append, disjoint_take_drop, dropSlice_eq, drop_inter, h.nodup_iff, inter_append, le_add_right, nodup_iff, take_inter
-/
theorem Perm.dropSlice_inter {xs ys : List α} (n m : Nat) (h : xs ~ ys)
    (h' : ys.Nodup) : List.dropSlice n m xs ~ ys inter List.dropSlice n m xs := by
  simp only [dropSlice_eq]
  have : n <= n + m := Nat.le_add_right _ _
  have h₂ := h.nodup_iff.2 h'
  apply Perm.trans _ (Perm.inter_append _).symm
  · exact Perm.append (Perm.take_inter _ h h') (Perm.drop_inter _ h h')
  · exact disjoint_take_drop h₂ this

end List
