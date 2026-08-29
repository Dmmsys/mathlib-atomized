/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky, Chris Hughes
-/
module

public import Mathlib.Data.List.Nodup

/-!
# List duplicates

## Main definitions

* `List.Duplicate x l : Prop` is an inductive property that holds when `x` is a duplicate in `l`

## Implementation details

In this file, `x ∈+ l` notation is shorthand for `List.Duplicate x l`.

-/

public section


variable {α : Type*}

namespace List

/--
Inductive type `Duplicate` / 归纳类型 `Duplicate`

English:
inductive Duplicate
  parameters: (x : α)
  constructors (2):
    - cons_mem: {l : List α} : x in l -> Duplicate x (x :: l)
    - cons_duplicate: {y : α} {l : List α} : Duplicate x l -> Duplicate x (y :: l)

中文:
归纳类型 Duplicate
  参数: (x : α)
  构造子 (2 个):
    - cons_mem: {l : 列表 α} : x in l -> Duplicate x (x :: l)
    - cons_duplicate: {y : α} {l : 列表 α} : Duplicate x l -> Duplicate x (y :: l)
-/
inductive Duplicate (x : α) : List α -> Prop
  | cons_mem {l : List α} : x in l -> Duplicate x (x :: l)
  | cons_duplicate {y : α} {l : List α} : Duplicate x l -> Duplicate x (y :: l)

local infixl:50 " in+ " => List.Duplicate

variable {l : List α} {x : α}

/--
theorem `Mem.duplicate_cons_self` / 定理 `Mem.duplicate_cons_self`

English:
theorem Mem.duplicate_cons_self
  given: (h : x in l)
  statement: x in+ x :: l
  proof: Duplicate.cons_mem h

中文:
定理 Mem.duplicate_cons_self
  条件: (h : x in l)
  结论: x in+ x :: l
  证明: Duplicate.cons_mem h

Depends on / 依赖: Duplicate, Duplicate.cons_mem, cons_mem
-/
theorem Mem.duplicate_cons_self (h : x in l) : x in+ x :: l :=
  Duplicate.cons_mem h

/--
theorem `Duplicate.duplicate_cons` / 定理 `Duplicate.duplicate_cons`

English:
theorem Duplicate.duplicate_cons
  given: (h : x in+ l) (y : α)
  statement: x in+ y :: l
  proof: Duplicate.cons_duplicate h

中文:
定理 Duplicate.duplicate_cons
  条件: (h : x in+ l) (y : α)
  结论: x in+ y :: l
  证明: Duplicate.cons_duplicate h

Depends on / 依赖: Duplicate, Duplicate.cons_duplicate, cons_duplicate
-/
theorem Duplicate.duplicate_cons (h : x in+ l) (y : α) : x in+ y :: l :=
  Duplicate.cons_duplicate h

/--
theorem `Duplicate.mem` / 定理 `Duplicate.mem`

English:
theorem Duplicate.mem
  given: (h : x in+ l)
  statement: x in l
  proof: by
  induction h with
  | cons_mem => exact mem_cons_self
  | cons_duplicate _ hm => exact mem_cons_of_mem _ hm

中文:
定理 Duplicate.mem
  条件: (h : x in+ l)
  结论: x in l
  证明: by
  induction h with
  | cons_mem => exact mem_cons_self
  | cons_duplicate _ hm => exact mem_cons_of_mem _ hm

Depends on / 依赖: cons_duplicate, cons_mem, mem_cons_of_mem, mem_cons_self
-/
theorem Duplicate.mem (h : x in+ l) : x in l := by
  induction h with
  | cons_mem => exact mem_cons_self
  | cons_duplicate _ hm => exact mem_cons_of_mem _ hm

/--
theorem `Duplicate.mem_cons_self` / 定理 `Duplicate.mem_cons_self`

English:
theorem Duplicate.mem_cons_self
  given: (h : x in+ x :: l)
  statement: x in l
  proof: by
  obtain h | h := h
  · exact h
  · exact h.mem

@[simp]

中文:
定理 Duplicate.mem_cons_self
  条件: (h : x in+ x :: l)
  结论: x in l
  证明: by
  obtain h | h := h
  · exact h
  · exact h.mem

@[simp]

Depends on / 依赖: h.mem
-/
theorem Duplicate.mem_cons_self (h : x in+ x :: l) : x in l := by
  obtain h | h := h
  · exact h
  · exact h.mem

@[simp]
/--
theorem `duplicate_cons_self_iff` / 定理 `duplicate_cons_self_iff`

English:
theorem duplicate_cons_self_iff
  statement: x in+ x :: l ↔ x in l
  proof: ⟨Duplicate.mem_cons_self, Mem.duplicate_cons_self⟩

中文:
定理 duplicate_cons_self_iff
  结论: x in+ x :: l ↔ x in l
  证明: ⟨Duplicate.mem_cons_self, Mem.duplicate_cons_self⟩

Depends on / 依赖: Duplicate, Duplicate.mem_cons_self, Mem.duplicate_cons_self, duplicate_cons_self, mem_cons_self
-/
theorem duplicate_cons_self_iff : x in+ x :: l ↔ x in l :=
  ⟨Duplicate.mem_cons_self, Mem.duplicate_cons_self⟩

/--
theorem `Duplicate.ne_nil` / 定理 `Duplicate.ne_nil`

English:
theorem Duplicate.ne_nil
  given: (h : x in+ l)
  statement: l != []
  proof: fun H => (mem_nil_iff x).mp (H ▸ h.mem)

@[simp]

中文:
定理 Duplicate.ne_nil
  条件: (h : x in+ l)
  结论: l != []
  证明: fun H => (mem_nil_iff x).mp (H ▸ h.mem)

@[simp]

Depends on / 依赖: h.mem, mem_nil_iff
-/
theorem Duplicate.ne_nil (h : x in+ l) : l != [] := fun H => (mem_nil_iff x).mp (H ▸ h.mem)

@[simp]
/--
theorem `not_duplicate_nil` / 定理 `not_duplicate_nil`

English:
theorem not_duplicate_nil
  given: (x : α)
  statement: ¬x in+ []
  proof: fun H => H.ne_nil rfl

中文:
定理 not_duplicate_nil
  条件: (x : α)
  结论: ¬x in+ []
  证明: fun H => H.ne_nil rfl

Depends on / 依赖: H.ne_nil, ne_nil
-/
theorem not_duplicate_nil (x : α) : ¬x in+ [] := fun H => H.ne_nil rfl

/--
theorem `Duplicate.ne_singleton` / 定理 `Duplicate.ne_singleton`

English:
theorem Duplicate.ne_singleton
  given: (h : x in+ l) (y : α)
  statement: l != [y]
  proof: by
  induction h with
  | cons_mem h => simp [ne_nil_of_mem h]
  | cons_duplicate h => simp [ne_nil_of_mem h.mem]

@[simp]

中文:
定理 Duplicate.ne_singleton
  条件: (h : x in+ l) (y : α)
  结论: l != [y]
  证明: by
  induction h with
  | cons_mem h => simp [ne_nil_of_mem h]
  | cons_duplicate h => simp [ne_nil_of_mem h.mem]

@[simp]

Depends on / 依赖: cons_duplicate, cons_mem, h.mem, ne_nil_of_mem
-/
theorem Duplicate.ne_singleton (h : x in+ l) (y : α) : l != [y] := by
  induction h with
  | cons_mem h => simp [ne_nil_of_mem h]
  | cons_duplicate h => simp [ne_nil_of_mem h.mem]

@[simp]
/--
theorem `not_duplicate_singleton` / 定理 `not_duplicate_singleton`

English:
theorem not_duplicate_singleton
  given: (x y : α)
  statement: ¬x in+ [y]
  proof: fun H => H.ne_singleton _ rfl

中文:
定理 not_duplicate_singleton
  条件: (x y : α)
  结论: ¬x in+ [y]
  证明: fun H => H.ne_singleton _ rfl

Depends on / 依赖: H.ne_singleton, ne_singleton
-/
theorem not_duplicate_singleton (x y : α) : ¬x in+ [y] := fun H => H.ne_singleton _ rfl

/--
theorem `Duplicate.elim_nil` / 定理 `Duplicate.elim_nil`

English:
theorem Duplicate.elim_nil
  given: (h : x in+ [])
  statement: False
  proof: not_duplicate_nil x h

中文:
定理 Duplicate.elim_nil
  条件: (h : x in+ [])
  结论: 假
  证明: not_duplicate_nil x h

Depends on / 依赖: not_duplicate_nil
-/
theorem Duplicate.elim_nil (h : x in+ []) : False :=
  not_duplicate_nil x h

/--
theorem `Duplicate.elim_singleton` / 定理 `Duplicate.elim_singleton`

English:
theorem Duplicate.elim_singleton
  given: {y : α} (h : x in+ [y])
  statement: False
  proof: not_duplicate_singleton x y h

中文:
定理 Duplicate.elim_singleton
  条件: {y : α} (h : x in+ [y])
  结论: 假
  证明: not_duplicate_singleton x y h

Depends on / 依赖: not_duplicate_singleton
-/
theorem Duplicate.elim_singleton {y : α} (h : x in+ [y]) : False :=
  not_duplicate_singleton x y h

/--
theorem `duplicate_cons_iff` / 定理 `duplicate_cons_iff`

English:
theorem duplicate_cons_iff
  given: {y : α}
  statement: x in+ y :: l ↔ y = x ∧ x in l ∨ x in+ l
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain hm | hm := h
    · exact Or.inl ⟨rfl, hm⟩
    · exact Or.inr hm
  · rcases h with (⟨rfl | h⟩ | h)
    · simpa
    · exact h.cons_duplicate

中文:
定理 duplicate_cons_iff
  条件: {y : α}
  结论: x in+ y :: l ↔ y = x ∧ x in l ∨ x in+ l
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain hm | hm := h
    · exact Or.inl ⟨rfl, hm⟩
    · exact Or.inr hm
  · rcases h with (⟨rfl | h⟩ | h)
    · simpa
    · exact h.cons_duplicate

Depends on / 依赖: Or.inl, Or.inr, cons_duplicate, h.cons_duplicate
-/
theorem duplicate_cons_iff {y : α} : x in+ y :: l ↔ y = x ∧ x in l ∨ x in+ l := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain hm | hm := h
    · exact Or.inl ⟨rfl, hm⟩
    · exact Or.inr hm
  · rcases h with (⟨rfl | h⟩ | h)
    · simpa
    · exact h.cons_duplicate

/--
theorem `Duplicate.of_duplicate_cons` / 定理 `Duplicate.of_duplicate_cons`

English:
theorem Duplicate.of_duplicate_cons
  given: {y : α} (h : x in+ y :: l) (hx : x != y)
  statement: x in+ l
  proof: by
  simpa [duplicate_cons_iff, hx.symm] using h

中文:
定理 Duplicate.of_duplicate_cons
  条件: {y : α} (h : x in+ y :: l) (hx : x != y)
  结论: x in+ l
  证明: by
  simpa [duplicate_cons_iff, hx.symm] using h

Depends on / 依赖: duplicate_cons_iff, hx.symm
-/
theorem Duplicate.of_duplicate_cons {y : α} (h : x in+ y :: l) (hx : x != y) : x in+ l := by
  simpa [duplicate_cons_iff, hx.symm] using h

/--
theorem `duplicate_cons_iff_of_ne` / 定理 `duplicate_cons_iff_of_ne`

English:
theorem duplicate_cons_iff_of_ne
  given: {y : α} (hne : x != y)
  statement: x in+ y :: l ↔ x in+ l
  proof: by
  simp [duplicate_cons_iff, hne.symm]

中文:
定理 duplicate_cons_iff_of_ne
  条件: {y : α} (hne : x != y)
  结论: x in+ y :: l ↔ x in+ l
  证明: by
  simp [duplicate_cons_iff, hne.symm]

Depends on / 依赖: duplicate_cons_iff, hne.symm
-/
theorem duplicate_cons_iff_of_ne {y : α} (hne : x != y) : x in+ y :: l ↔ x in+ l := by
  simp [duplicate_cons_iff, hne.symm]

/--
theorem `Duplicate.mono_sublist` / 定理 `Duplicate.mono_sublist`

English:
theorem Duplicate.mono_sublist
  given: {l' : List α} (hx : x in+ l) (h : l <+ l')
  statement: x in+ l'
  proof: by
  induction h with
  | slnil => exact hx
  | cons y _ IH => exact (IH hx).duplicate_cons _
  | cons_cons y h IH =>
    rw [duplicate_cons_iff] at hx ⊢
    rcases hx with (⟨rfl, hx⟩ | hx)
    · simp [h.subset hx]
    · simp [IH hx]

中文:
定理 Duplicate.mono_sublist
  条件: {l' : 列表 α} (hx : x in+ l) (h : l <+ l')
  结论: x in+ l'
  证明: by
  induction h with
  | slnil => exact hx
  | cons y _ IH => exact (IH hx).duplicate_cons _
  | cons_cons y h IH =>
    rw [duplicate_cons_iff] at hx ⊢
    rcases hx with (⟨rfl, hx⟩ | hx)
    · simp [h.subset hx]
    · simp [IH hx]

Depends on / 依赖: cons_cons, duplicate_cons, duplicate_cons_iff, h.subset, subset
-/
theorem Duplicate.mono_sublist {l' : List α} (hx : x in+ l) (h : l <+ l') : x in+ l' := by
  induction h with
  | slnil => exact hx
  | cons y _ IH => exact (IH hx).duplicate_cons _
  | cons_cons y h IH =>
    rw [duplicate_cons_iff] at hx ⊢
    rcases hx with (⟨rfl, hx⟩ | hx)
    · simp [h.subset hx]
    · simp [IH hx]

/--
theorem `duplicate_iff_sublist` / 定理 `duplicate_iff_sublist`

English:
theorem duplicate_iff_sublist
  statement: x in+ l ↔ [x, x] <+ l
  proof: by
  induction l with
  | nil => simp
  | cons y l IH =>
    by_cases hx : x = y
    · simp [hx, cons_sublist_cons, singleton_sublist]
    · rw [duplicate_cons_iff_of_ne hx, IH]
      refine ⟨sublist_cons_of_sublist y, fun h => ?_⟩
      cases h
      · assumption
      · contradiction

中文:
定理 duplicate_iff_sublist
  结论: x in+ l ↔ [x, x] <+ l
  证明: by
  induction l with
  | nil => simp
  | cons y l IH =>
    by_cases hx : x = y
    · simp [hx, cons_sublist_cons, singleton_sublist]
    · rw [duplicate_cons_iff_of_ne hx, IH]
      refine ⟨sublist_cons_of_sublist y, fun h => ?_⟩
      cases h
      · assumption
      · contradiction

Depends on / 依赖: cons_sublist_cons, duplicate_cons_iff_of_ne, singleton_sublist, sublist_cons_of_sublist
-/
theorem duplicate_iff_sublist : x in+ l ↔ [x, x] <+ l := by
  induction l with
  | nil => simp
  | cons y l IH =>
    by_cases hx : x = y
    · simp [hx, cons_sublist_cons, singleton_sublist]
    · rw [duplicate_cons_iff_of_ne hx, IH]
      refine ⟨sublist_cons_of_sublist y, fun h => ?_⟩
      cases h
      · assumption
      · contradiction

/--
theorem `nodup_iff_forall_not_duplicate` / 定理 `nodup_iff_forall_not_duplicate`

English:
theorem nodup_iff_forall_not_duplicate
  statement: Nodup l ↔ forall x : α, ¬x in+ l
  proof: by
  simp_rw [nodup_iff_sublist, duplicate_iff_sublist]

中文:
定理 nodup_iff_对任意_not_duplicate
  结论: Nodup l ↔ 对任意 x : α, ¬x in+ l
  证明: by
  simp_rw [nodup_iff_sublist, duplicate_iff_sublist]

Depends on / 依赖: duplicate_iff_sublist, nodup_iff_sublist, simp_rw
-/
theorem nodup_iff_forall_not_duplicate : Nodup l ↔ forall x : α, ¬x in+ l := by
  simp_rw [nodup_iff_sublist, duplicate_iff_sublist]

/--
theorem `exists_duplicate_iff_not_nodup` / 定理 `exists_duplicate_iff_not_nodup`

English:
theorem exists_duplicate_iff_not_nodup
  statement: (exists x : α, x in+ l) ↔ ¬Nodup l
  proof: by
  simp [nodup_iff_forall_not_duplicate]

中文:
定理 存在_duplicate_iff_not_nodup
  结论: (存在 x : α, x in+ l) ↔ ¬Nodup l
  证明: by
  simp [nodup_iff_forall_not_duplicate]

Depends on / 依赖: nodup_iff_forall_not_duplicate
-/
theorem exists_duplicate_iff_not_nodup : (exists x : α, x in+ l) ↔ ¬Nodup l := by
  simp [nodup_iff_forall_not_duplicate]

/--
theorem `Duplicate.not_nodup` / 定理 `Duplicate.not_nodup`

English:
theorem Duplicate.not_nodup
  given: (h : x in+ l)
  statement: ¬Nodup l
  proof: fun H =>
  nodup_iff_forall_not_duplicate.mp H _ h

中文:
定理 Duplicate.not_nodup
  条件: (h : x in+ l)
  结论: ¬Nodup l
  证明: fun H =>
  nodup_iff_forall_not_duplicate.mp H _ h
-/
theorem Duplicate.not_nodup (h : x in+ l) : ¬Nodup l := fun H =>
  nodup_iff_forall_not_duplicate.mp H _ h

/--
theorem `duplicate_iff_two_le_count` / 定理 `duplicate_iff_two_le_count`

English:
theorem duplicate_iff_two_le_count
  given: [DecidableEq α]
  statement: x in+ l ↔ 2 <= count x l
  proof: by
  simp [replicate_succ, duplicate_iff_sublist, ← replicate_sublist_iff]

中文:
定理 duplicate_iff_two_le_count
  条件: [DecidableEq α]
  结论: x in+ l ↔ 2 <= count x l
  证明: by
  simp [replicate_succ, duplicate_iff_sublist, ← replicate_sublist_iff]

Depends on / 依赖: duplicate_iff_sublist, replicate_sublist_iff, replicate_succ
-/
theorem duplicate_iff_two_le_count [DecidableEq α] : x in+ l ↔ 2 <= count x l := by
  simp [replicate_succ, duplicate_iff_sublist, ← replicate_sublist_iff]

/--
Instance `decidableDuplicate` / 实例 `decidableDuplicate`

English:
instance decidableDuplicate
  signature: [DecidableEq α] (x : α)

中文:
实例 decidableDuplicate
  签名: [DecidableEq α] (x : α)
-/
instance decidableDuplicate [DecidableEq α] (x : α) : forall l : List α, Decidable (x in+ l)
  | [] => isFalse (not_duplicate_nil x)
  | y :: l =>
    match decidableDuplicate x l with
    | isTrue h => isTrue (h.duplicate_cons y)
    | isFalse h =>
      if hx : y = x ∧ x in l then isTrue (hx.left.symm ▸ List.Mem.duplicate_cons_self hx.right)
      else isFalse (by simpa [duplicate_cons_iff, h] using hx)

end List
