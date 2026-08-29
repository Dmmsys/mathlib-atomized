/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.Lattice
public import Batteries.Data.List.Pairwise

/-!
# Erasure of duplicates in a list

This file proves basic results about `List.dedup` (definition in `Data.List.Defs`).
`dedup l` returns `l` without its duplicates. It keeps the earliest (that is, rightmost)
occurrence of each.

## Tags

duplicate, multiplicity, nodup, `nub`
-/

public section


universe u

namespace List

variable {α β : Type*} [DecidableEq α]

@[simp]
/--
theorem `dedup_nil` / 定理 `dedup_nil`

English:
theorem dedup_nil
  statement: dedup [] = ([] : List α)
  proof: rfl

中文:
定理 dedup_nil
  结论: dedup [] = ([] : List α)
  证明: rfl
-/
theorem dedup_nil : dedup [] = ([] : List α) :=
  rfl

/--
theorem `dedup_cons_of_mem'` / 定理 `dedup_cons_of_mem'`

English:
theorem dedup_cons_of_mem'
  given: {a : α} {l : List α} (h : a in dedup l)
  statement: dedup (a :: l) = dedup l
  proof: pwFilter_cons_of_neg by simpa only [forall_mem_ne, not_not] using! h

中文:
定理 dedup_cons_of_mem'
  条件: {a : α} {l : List α} (h : a in dedup l)
  结论: dedup (a :: l) = dedup l
  证明: pwFilter_cons_of_neg by simpa only [forall_mem_ne, not_not] using! h

Depends on / 依赖: forall_mem_ne, not_not, pwFilter_cons_of_neg
-/
theorem dedup_cons_of_mem' {a : α} {l : List α} (h : a in dedup l) : dedup (a :: l) = dedup l :=
pwFilter_cons_of_neg by simpa only [forall_mem_ne, not_not] using! h

/--
theorem `dedup_cons_of_notMem'` / 定理 `dedup_cons_of_notMem'`

English:
theorem dedup_cons_of_notMem'
  given: {a : α} {l : List α} (h : a ∉ dedup l)
  proof: pwFilter_cons_of_pos by simpa only [forall_mem_ne] using! h

中文:
定理 dedup_cons_of_notMem'
  条件: {a : α} {l : List α} (h : a ∉ dedup l)
  证明: pwFilter_cons_of_pos by simpa only [forall_mem_ne] using! h

Depends on / 依赖: forall_mem_ne, pwFilter_cons_of_pos
-/
theorem dedup_cons_of_notMem' {a : α} {l : List α} (h : a ∉ dedup l) :
    dedup (a :: l) = a :: dedup l :=
pwFilter_cons_of_pos by simpa only [forall_mem_ne] using! h

/--
theorem `dedup_cons'` / 定理 `dedup_cons'`

English:
theorem dedup_cons'
  given: (a : α) (l : List α)
  proof: by
  split <;> simp [dedup_cons_of_mem', dedup_cons_of_notMem', *]

@[simp]

中文:
定理 dedup_cons'
  条件: (a : α) (l : List α)
  证明: by
  split <;> simp [dedup_cons_of_mem', dedup_cons_of_notMem', *]

@[simp]

Depends on / 依赖: dedup_cons_of_mem, dedup_cons_of_notMem
-/
theorem dedup_cons' (a : α) (l : List α) :
    dedup (a :: l) = if a in dedup l then dedup l else a :: dedup l := by
  split <;> simp [dedup_cons_of_mem', dedup_cons_of_notMem', *]

@[simp]
/--
theorem `mem_dedup` / 定理 `mem_dedup`

English:
theorem mem_dedup
  given: {a : α} {l : List α}
  statement: a in dedup l ↔ a in l
  proof: by
  have := not_congr (@forall_mem_pwFilter α (· != ·) _ ?_ a l)
  · simpa only [dedup, forall_mem_ne, not_not] using this
  · intro x y z xz
exact not_and_or.1 mt (fun h => h.1.trans h.2) xz

@[simp]

中文:
定理 mem_dedup
  条件: {a : α} {l : List α}
  结论: a in dedup l ↔ a in l
  证明: by
  have := not_congr (@forall_mem_pwFilter α (· != ·) _ ?_ a l)
  · simpa only [dedup, forall_mem_ne, not_not] using this
  · intro x y z xz
exact not_and_or.1 mt (fun h => h.1.trans h.2) xz

@[simp]

Depends on / 依赖: forall_mem_ne, forall_mem_pwFilter, not_and_or, not_congr, not_not
-/
theorem mem_dedup {a : α} {l : List α} : a in dedup l ↔ a in l := by
  have := not_congr (@forall_mem_pwFilter α (· != ·) _ ?_ a l)
  · simpa only [dedup, forall_mem_ne, not_not] using this
  · intro x y z xz
exact not_and_or.1 mt (fun h => h.1.trans h.2) xz

@[simp]
/--
theorem `dedup_cons_of_mem` / 定理 `dedup_cons_of_mem`

English:
theorem dedup_cons_of_mem
  given: {a : α} {l : List α} (h : a in l)
  statement: dedup (a :: l) = dedup l
  proof: dedup_cons_of_mem' mem_dedup.2 h

@[simp]

中文:
定理 dedup_cons_of_mem
  条件: {a : α} {l : List α} (h : a in l)
  结论: dedup (a :: l) = dedup l
  证明: dedup_cons_of_mem' mem_dedup.2 h

@[simp]

Depends on / 依赖: dedup_cons_of_mem, mem_dedup
-/
theorem dedup_cons_of_mem {a : α} {l : List α} (h : a in l) : dedup (a :: l) = dedup l :=
dedup_cons_of_mem' mem_dedup.2 h

@[simp]
/--
theorem `dedup_cons_of_notMem` / 定理 `dedup_cons_of_notMem`

English:
theorem dedup_cons_of_notMem
  given: {a : α} {l : List α} (h : a ∉ l)
  statement: dedup (a :: l) = a :: dedup l
  proof: dedup_cons_of_notMem' mt mem_dedup.1 h

中文:
定理 dedup_cons_of_notMem
  条件: {a : α} {l : List α} (h : a ∉ l)
  结论: dedup (a :: l) = a :: dedup l
  证明: dedup_cons_of_notMem' mt mem_dedup.1 h

Depends on / 依赖: dedup_cons_of_notMem, mem_dedup
-/
theorem dedup_cons_of_notMem {a : α} {l : List α} (h : a ∉ l) : dedup (a :: l) = a :: dedup l :=
dedup_cons_of_notMem' mt mem_dedup.1 h

/--
theorem `dedup_cons` / 定理 `dedup_cons`

English:
theorem dedup_cons
  given: (a : α) (l : List α)
  proof: by
  simpa using dedup_cons' a l

中文:
定理 dedup_cons
  条件: (a : α) (l : List α)
  证明: by
  simpa using dedup_cons' a l

Depends on / 依赖: dedup_cons
-/
theorem dedup_cons (a : α) (l : List α) :
    dedup (a :: l) = if a in l then dedup l else a :: dedup l := by
  simpa using dedup_cons' a l

/--
theorem `dedup_sublist` / 定理 `dedup_sublist`

English:
theorem dedup_sublist
  statement: forall l : List α, dedup l <+ l
  proof: pwFilter_sublist

中文:
定理 dedup_sublist
  结论: 对任意 l : List α, dedup l <+ l
  证明: pwFilter_sublist

Depends on / 依赖: pwFilter_sublist
-/
theorem dedup_sublist : forall l : List α, dedup l <+ l :=
  pwFilter_sublist

/--
theorem `dedup_subset` / 定理 `dedup_subset`

English:
theorem dedup_subset
  statement: forall l : List α, dedup l subseteq l
  proof: pwFilter_subset

中文:
定理 dedup_subset
  结论: 对任意 l : List α, dedup l subseteq l
  证明: pwFilter_subset

Depends on / 依赖: pwFilter_subset
-/
theorem dedup_subset : forall l : List α, dedup l subseteq l :=
  pwFilter_subset

/--
theorem `subset_dedup` / 定理 `subset_dedup`

English:
theorem subset_dedup
  given: (l : List α)
  statement: l subseteq dedup l
  proof: fun _ => mem_dedup.2

中文:
定理 subset_dedup
  条件: (l : List α)
  结论: l subseteq dedup l
  证明: fun _ => mem_dedup.2

Depends on / 依赖: mem_dedup
-/
theorem subset_dedup (l : List α) : l subseteq dedup l := fun _ => mem_dedup.2

/--
theorem `nodup_dedup` / 定理 `nodup_dedup`

English:
theorem nodup_dedup
  statement: forall l : List α, Nodup (dedup l)
  proof: pairwise_pwFilter

中文:
定理 nodup_dedup
  结论: 对任意 l : List α, Nodup (dedup l)
  证明: pairwise_pwFilter

Depends on / 依赖: pairwise_pwFilter
-/
theorem nodup_dedup : forall l : List α, Nodup (dedup l) :=
  pairwise_pwFilter

/--
theorem `headI_dedup` / 定理 `headI_dedup`

English:
theorem headI_dedup
  given: [Inhabited α] (l : List α)
  proof: match l with
  | [] => rfl
  | a :: l => by by_cases ha : a in l <;> simp [ha, List.dedup_cons_of_mem]

中文:
定理 headI_dedup
  条件: [Inhabited α] (l : List α)
  证明: match l with
  | [] => rfl
  | a :: l => by by_cases ha : a in l <;> simp [ha, List.dedup_cons_of_mem]

Depends on / 依赖: List.dedup_cons_of_mem, dedup_cons_of_mem
-/
theorem headI_dedup [Inhabited α] (l : List α) :
    l.dedup.headI = if l.headI in l.tail then l.tail.dedup.headI else l.headI :=
  match l with
  | [] => rfl
  | a :: l => by by_cases ha : a in l <;> simp [ha, List.dedup_cons_of_mem]

/--
theorem `tail_dedup` / 定理 `tail_dedup`

English:
theorem tail_dedup
  given: [Inhabited α] (l : List α)
  proof: match l with
  | [] => rfl
  | a :: l => by by_cases ha : a in l <;> simp [ha, List.dedup_cons_of_mem]

中文:
定理 tail_dedup
  条件: [Inhabited α] (l : List α)
  证明: match l with
  | [] => rfl
  | a :: l => by by_cases ha : a in l <;> simp [ha, List.dedup_cons_of_mem]

Depends on / 依赖: List.dedup_cons_of_mem, dedup_cons_of_mem
-/
theorem tail_dedup [Inhabited α] (l : List α) :
    l.dedup.tail = if l.headI in l.tail then l.tail.dedup.tail else l.tail.dedup :=
  match l with
  | [] => rfl
  | a :: l => by by_cases ha : a in l <;> simp [ha, List.dedup_cons_of_mem]

/--
theorem `dedup_eq_self` / 定理 `dedup_eq_self`

English:
theorem dedup_eq_self
  given: {l : List α}
  statement: dedup l = l ↔ Nodup l
  proof: pwFilter_eq_self

中文:
定理 dedup_eq_self
  条件: {l : List α}
  结论: dedup l = l ↔ Nodup l
  证明: pwFilter_eq_self

Depends on / 依赖: pwFilter_eq_self
-/
theorem dedup_eq_self {l : List α} : dedup l = l ↔ Nodup l :=
  pwFilter_eq_self

/--
theorem `dedup_eq_cons` / 定理 `dedup_eq_cons`

English:
theorem dedup_eq_cons
  given: (l : List α) (a : α) (l' : List α)
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine ⟨mem_dedup.1 (h.symm ▸ mem_cons_self), fun ha => ?_, by rw [h, tail_cons]⟩
    have := count_pos_iff.2 ha
    have : count a l.dedup <= 1 := nodup_iff_count_le_one.1 (nodup_dedup l) a
    rw [h]; rw [count_cons_self] at this
    lia
  · have := @List

中文:
定理 dedup_eq_cons
  条件: (l : List α) (a : α) (l' : List α)
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine ⟨mem_dedup.1 (h.symm ▸ mem_cons_self), fun ha => ?_, by rw [h, tail_cons]⟩
    have := count_pos_iff.2 ha
    have : count a l.dedup <= 1 := nodup_iff_count_le_one.1 (nodup_dedup l) a
    rw [h]; rw [count_cons_self] at this
    lia
  · have := @List

Depends on / 依赖: List.cons_head, _tail, cons_eq_cons, cons_head, count_cons_self, count_pos_iff, h.symm, l.dedup, mem_cons, mem_cons_self, mem_dedup, ne_nil_of_mem, nodup_dedup, nodup_iff_count_le_one, or_iff_not_imp_right, tail_cons
-/
theorem dedup_eq_cons (l : List α) (a : α) (l' : List α) :
    l.dedup = a :: l' ↔ a in l ∧ a ∉ l' ∧ l.dedup.tail = l' := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine ⟨mem_dedup.1 (h.symm ▸ mem_cons_self), fun ha => ?_, by rw [h, tail_cons]⟩
    have := count_pos_iff.2 ha
    have : count a l.dedup <= 1 := nodup_iff_count_le_one.1 (nodup_dedup l) a
    rw [h]; rw [count_cons_self] at this
    lia
  · have := @List.cons_head!_tail α ⟨a⟩ _ (ne_nil_of_mem (mem_dedup.2 h.1))
    have hal : a in l.dedup := mem_dedup.2 h.1
    rw [← this]; rw [mem_cons]; rw [or_iff_not_imp_right] at hal
    exact this ▸ h.2.2.symm ▸ cons_eq_cons.2 ⟨(hal (h.2.2.symm ▸ h.2.1)).symm, rfl⟩

@[simp]
/--
theorem `dedup_eq_nil` / 定理 `dedup_eq_nil`

English:
theorem dedup_eq_nil
  given: (l : List α)
  statement: l.dedup = [] ↔ l = []
  proof: by
  induction l with
  | nil => exact Iff.rfl
  | cons a l hl =>
    by_cases h : a in l
    · simp only [List.dedup_cons_of_mem h, hl, List.ne_nil_of_mem h, reduceCtorEq]
    · simp only [List.dedup_cons_of_notMem h, List.cons_ne_nil]

中文:
定理 dedup_eq_nil
  条件: (l : List α)
  结论: l.dedup = [] ↔ l = []
  证明: by
  induction l with
  | nil => exact Iff.rfl
  | cons a l hl =>
    by_cases h : a in l
    · simp only [List.dedup_cons_of_mem h, hl, List.ne_nil_of_mem h, reduceCtorEq]
    · simp only [List.dedup_cons_of_notMem h, List.cons_ne_nil]

Depends on / 依赖: Iff.rfl, List.cons_ne_nil, List.dedup_cons_of_mem, List.dedup_cons_of_notMem, List.ne_nil_of_mem, cons_ne_nil, dedup_cons_of_mem, dedup_cons_of_notMem, ne_nil_of_mem, reduceCtorEq
-/
theorem dedup_eq_nil (l : List α) : l.dedup = [] ↔ l = [] := by
  induction l with
  | nil => exact Iff.rfl
  | cons a l hl =>
    by_cases h : a in l
    · simp only [List.dedup_cons_of_mem h, hl, List.ne_nil_of_mem h, reduceCtorEq]
    · simp only [List.dedup_cons_of_notMem h, List.cons_ne_nil]

/--
theorem `Nodup.dedup` / 定理 `Nodup.dedup`

English:
theorem Nodup.dedup
  given: {l : List α} (h : l.Nodup)
  statement: l.dedup = l
  proof: List.dedup_eq_self.2 h

@[simp]

中文:
定理 Nodup.dedup
  条件: {l : List α} (h : l.Nodup)
  结论: l.dedup = l
  证明: List.dedup_eq_self.2 h

@[simp]
-/
protected theorem Nodup.dedup {l : List α} (h : l.Nodup) : l.dedup = l :=
  List.dedup_eq_self.2 h

@[simp]
/--
theorem `dedup_idem` / 定理 `dedup_idem`

English:
theorem dedup_idem
  given: {l : List α}
  statement: dedup (dedup l) = dedup l
  proof: pwFilter_idem

中文:
定理 dedup_idem
  条件: {l : List α}
  结论: dedup (dedup l) = dedup l
  证明: pwFilter_idem

Depends on / 依赖: pwFilter_idem
-/
theorem dedup_idem {l : List α} : dedup (dedup l) = dedup l :=
  pwFilter_idem

/--
theorem `dedup_append` / 定理 `dedup_append`

English:
theorem dedup_append
  given: (l₁ l₂ : List α)
  statement: dedup (l₁ ++ l₂) = l₁ union dedup l₂
  proof: by
  induction l₁ with | nil => rfl | cons a l₁ IH => ?_
  simp only [cons_union] at *
  rw [← IH]; rw [cons_append]
  by_cases h : a in dedup (l₁ ++ l₂)
  · rw [dedup_cons_of_mem' h, insert_of_mem h]
  · rw [dedup_cons_of_notMem' h, insert_of_not_mem h]

中文:
定理 dedup_append
  条件: (l₁ l₂ : List α)
  结论: dedup (l₁ ++ l₂) = l₁ union dedup l₂
  证明: by
  induction l₁ with | nil => rfl | cons a l₁ IH => ?_
  simp only [cons_union] at *
  rw [← IH]; rw [cons_append]
  by_cases h : a in dedup (l₁ ++ l₂)
  · rw [dedup_cons_of_mem' h, insert_of_mem h]
  · rw [dedup_cons_of_notMem' h, insert_of_not_mem h]

Depends on / 依赖: cons_append, cons_union, dedup_cons_of_mem, dedup_cons_of_notMem, insert_of_mem, insert_of_not_mem
-/
theorem dedup_append (l₁ l₂ : List α) : dedup (l₁ ++ l₂) = l₁ union dedup l₂ := by
  induction l₁ with | nil => rfl | cons a l₁ IH => ?_
  simp only [cons_union] at *
  rw [← IH]; rw [cons_append]
  by_cases h : a in dedup (l₁ ++ l₂)
  · rw [dedup_cons_of_mem' h, insert_of_mem h]
  · rw [dedup_cons_of_notMem' h, insert_of_not_mem h]

/--
theorem `dedup_map_of_injective` / 定理 `dedup_map_of_injective`

English:
theorem dedup_map_of_injective
  statement: [DecidableEq β] {f : α -> β} (hf : Function.Injective f)
  proof: by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [map_cons]
    by_cases h : x in xs
    · rw [dedup_cons_of_mem h, dedup_cons_of_mem (mem_map_of_mem h), ih]
    · rw [dedup_cons_of_notMem h, dedup_cons_of_notMem <| (mem_map_of_injective hf).not.mpr h, ih,
        map_cons]

中文:
定理 dedup_map_of_injective
  结论: [DecidableEq β] {f : α -> β} (hf : Function.Injective f)
  证明: by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [map_cons]
    by_cases h : x in xs
    · rw [dedup_cons_of_mem h, dedup_cons_of_mem (mem_map_of_mem h), ih]
    · rw [dedup_cons_of_notMem h, dedup_cons_of_notMem <| (mem_map_of_injective hf).not.mpr h, ih,
        map_cons]

Depends on / 依赖: dedup_cons_of_mem, dedup_cons_of_notMem, map_cons, mem_map_of_injective, mem_map_of_mem, not.mpr
-/
theorem dedup_map_of_injective [DecidableEq β] {f : α -> β} (hf : Function.Injective f)
    (xs : List α) :
    (xs.map f).dedup = xs.dedup.map f := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [map_cons]
    by_cases h : x in xs
    · rw [dedup_cons_of_mem h, dedup_cons_of_mem (mem_map_of_mem h), ih]
    · rw [dedup_cons_of_notMem h, dedup_cons_of_notMem <| (mem_map_of_injective hf).not.mpr h, ih,
        map_cons]

/--
theorem `Subset.dedup_append_right` / 定理 `Subset.dedup_append_right`

English:
theorem Subset.dedup_append_right
  given: {xs ys : List α} (h : xs subseteq ys)
  proof: by
  rw [List.dedup_append]; rw [Subset.union_eq_right (List.Subset.trans h <| subset_dedup _)]

中文:
定理 Subset.dedup_append_right
  条件: {xs ys : List α} (h : xs subseteq ys)
  证明: by
  rw [List.dedup_append]; rw [Subset.union_eq_right (List.Subset.trans h <| subset_dedup _)]

Depends on / 依赖: List.Subset.trans, List.dedup_append, Subset, Subset.union_eq_right, dedup_append, subset_dedup, union_eq_right
-/
theorem Subset.dedup_append_right {xs ys : List α} (h : xs subseteq ys) :
    dedup (xs ++ ys) = dedup ys := by
  rw [List.dedup_append]; rw [Subset.union_eq_right (List.Subset.trans h <| subset_dedup _)]

/--
theorem `Disjoint.union_eq` / 定理 `Disjoint.union_eq`

English:
theorem Disjoint.union_eq
  given: {xs ys : List α} (h : Disjoint xs ys)
  proof: by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [cons_union]
    rw [disjoint_cons_left] at h
    by_cases hx : x in xs
    · rw [dedup_cons_of_mem hx, insert_of_mem (mem_union_left hx _), ih h.2]
    · rw [dedup_cons_of_notMem hx, insert_of_not_mem, ih h.2, cons_append]
      rw [

中文:
定理 Disjoint.union_eq
  条件: {xs ys : List α} (h : Disjoint xs ys)
  证明: by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [cons_union]
    rw [disjoint_cons_left] at h
    by_cases hx : x in xs
    · rw [dedup_cons_of_mem hx, insert_of_mem (mem_union_left hx _), ih h.2]
    · rw [dedup_cons_of_notMem hx, insert_of_not_mem, ih h.2, cons_append]
      rw [

Depends on / 依赖: cons_append, cons_union, dedup_cons_of_mem, dedup_cons_of_notMem, disjoint_cons_left, insert_of_mem, insert_of_not_mem, mem_union_iff, mem_union_left, not_or
-/
theorem Disjoint.union_eq {xs ys : List α} (h : Disjoint xs ys) :
    xs union ys = xs.dedup ++ ys := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [cons_union]
    rw [disjoint_cons_left] at h
    by_cases hx : x in xs
    · rw [dedup_cons_of_mem hx, insert_of_mem (mem_union_left hx _), ih h.2]
    · rw [dedup_cons_of_notMem hx, insert_of_not_mem, ih h.2, cons_append]
      rw [mem_union_iff]; rw [not_or]
      exact ⟨hx, h.1⟩

/--
theorem `Disjoint.dedup_append` / 定理 `Disjoint.dedup_append`

English:
theorem Disjoint.dedup_append
  given: {xs ys : List α} (h : Disjoint xs ys)
  proof: by
  rw [List.dedup_append]; rw [Disjoint.union_eq]
  intro a hx hy
  exact h hx (mem_dedup.mp hy)

中文:
定理 Disjoint.dedup_append
  条件: {xs ys : List α} (h : Disjoint xs ys)
  证明: by
  rw [List.dedup_append]; rw [Disjoint.union_eq]
  intro a hx hy
  exact h hx (mem_dedup.mp hy)

Depends on / 依赖: Disjoint, Disjoint.union_eq, List.dedup_append, dedup_append, mem_dedup, mem_dedup.mp, union_eq
-/
theorem Disjoint.dedup_append {xs ys : List α} (h : Disjoint xs ys) :
    dedup (xs ++ ys) = dedup xs ++ dedup ys := by
  rw [List.dedup_append]; rw [Disjoint.union_eq]
  intro a hx hy
  exact h hx (mem_dedup.mp hy)

/--
theorem `replicate_dedup` / 定理 `replicate_dedup`

English:
theorem replicate_dedup
  given: {x : α}
  statement: forall {k}, k != 0 -> (replicate k x).dedup = [x]

中文:
定理 replicate_dedup
  条件: {x : α}
  结论: 对任意 {k}, k != 0 -> (replicate k x).dedup = [x]
-/
theorem replicate_dedup {x : α} : forall {k}, k != 0 -> (replicate k x).dedup = [x]
  | 0, h => (h rfl).elim
  | 1, _ => rfl
  | n + 2, _ => by
    rw [replicate_succ]; rw [dedup_cons_of_mem (mem_replicate.2 ⟨n.succ_ne_zero]; rw [rfl⟩)]; rw [replicate_dedup n.succ_ne_zero]

/--
theorem `count_dedup` / 定理 `count_dedup`

English:
theorem count_dedup
  given: (l : List α) (a : α)
  statement: l.dedup.count a = if a in l then 1 else 0
  proof: by
  simp_rw [List.Nodup.count <| nodup_dedup l, mem_dedup]

中文:
定理 count_dedup
  条件: (l : List α) (a : α)
  结论: l.dedup.count a = if a in l then 1 else 0
  证明: by
  simp_rw [List.Nodup.count <| nodup_dedup l, mem_dedup]

Depends on / 依赖: List.Nodup.count, mem_dedup, nodup_dedup, simp_rw
-/
theorem count_dedup (l : List α) (a : α) : l.dedup.count a = if a in l then 1 else 0 := by
  simp_rw [List.Nodup.count <| nodup_dedup l, mem_dedup]

/--
theorem `Perm.dedup` / 定理 `Perm.dedup`

English:
theorem Perm.dedup
  given: {l₁ l₂ : List α} (p : l₁ ~ l₂)
  statement: dedup l₁ ~ dedup l₂
  proof: perm_iff_count.2 fun a =>
    if h : a in l₁ then by
      simp [h, nodup_dedup, p.subset h]
    else by
      simp [h, count_eq_zero_of_not_mem, mt p.mem_iff.2]

中文:
定理 Perm.dedup
  条件: {l₁ l₂ : List α} (p : l₁ ~ l₂)
  结论: dedup l₁ ~ dedup l₂
  证明: perm_iff_count.2 fun a =>
    if h : a in l₁ then by
      simp [h, nodup_dedup, p.subset h]
    else by
      simp [h, count_eq_zero_of_not_mem, mt p.mem_iff.2]

Depends on / 依赖: count_eq_zero_of_not_mem, mem_iff, nodup_dedup, p.mem_iff, p.subset, perm_iff_count, subset
-/
theorem Perm.dedup {l₁ l₂ : List α} (p : l₁ ~ l₂) : dedup l₁ ~ dedup l₂ :=
  perm_iff_count.2 fun a =>
    if h : a in l₁ then by
      simp [h, nodup_dedup, p.subset h]
    else by
      simp [h, count_eq_zero_of_not_mem, mt p.mem_iff.2]

end List
