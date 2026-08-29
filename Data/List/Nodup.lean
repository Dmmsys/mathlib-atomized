/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau
-/
module

public import Mathlib.Data.List.Forall2

/-!
# Lists with no duplicates

`List.Nodup` is defined in `Data/List/Basic`. In this file we prove various properties of this
predicate.
-/

public section

universe u v

open Function

variable {α : Type u} {β : Type v} {l l₁ l₂ : List α} {r : α -> α -> Prop} {a : α}

namespace List

/--
theorem `Pairwise.nodup` / 定理 `Pairwise.nodup`

English:
theorem Pairwise.nodup
  given: {l : List α} {r : α -> α -> Prop} [Std.Irrefl r] (h : Pairwise r l)
  proof: h.imp ne_of_irrefl

中文:
定理 两两.nodup
  条件: {l : 列表 α} {r : α -> α -> 命题} [Std.Irrefl r] (h : 两两 r l)
  证明: h.imp ne_of_irrefl
-/
protected theorem Pairwise.nodup {l : List α} {r : α -> α -> Prop} [Std.Irrefl r] (h : Pairwise r l) :
    Nodup l :=
  h.imp ne_of_irrefl

open scoped Relator in
/--
theorem `rel_nodup` / 定理 `rel_nodup`

English:
theorem rel_nodup
  given: {r : α -> β -> Prop} (hr : Relator.BiUnique r)
  statement: (Forall₂ r ⇒ (· ↔ ·)) Nodup Nodup

中文:
定理 rel_nodup
  条件: {r : α -> β -> 命题} (hr : Relator.BiUnique r)
  结论: (Forall₂ r ⇒ (· ↔ ·)) Nodup Nodup

Depends on / 依赖: nodup_cons
-/
theorem rel_nodup {r : α -> β -> Prop} (hr : Relator.BiUnique r) : (Forall₂ r ⇒ (· ↔ ·)) Nodup Nodup
  | _, _, Forall₂.nil => by simp only [nodup_nil]
  | _, _, Forall₂.cons hab h => by
    simpa only [nodup_cons] using
      Relator.rel_and (Relator.rel_not (rel_mem hr hab h)) (rel_nodup hr h)

/--
theorem `Nodup.cons` / 定理 `Nodup.cons`

English:
theorem Nodup.cons
  given: (ha : a ∉ l) (hl : Nodup l)
  statement: Nodup (a :: l)
  proof: nodup_cons.2 ⟨ha, hl⟩

中文:
定理 Nodup.cons
  条件: (ha : a ∉ l) (hl : Nodup l)
  结论: Nodup (a :: l)
  证明: nodup_cons.2 ⟨ha, hl⟩
-/
protected theorem Nodup.cons (ha : a ∉ l) (hl : Nodup l) : Nodup (a :: l) :=
  nodup_cons.2 ⟨ha, hl⟩

/--
theorem `nodup_singleton` / 定理 `nodup_singleton`

English:
theorem nodup_singleton
  given: (a : α)
  statement: Nodup [a]
  proof: pairwise_singleton _ _

中文:
定理 nodup_singleton
  条件: (a : α)
  结论: Nodup [a]
  证明: pairwise_singleton _ _

Depends on / 依赖: pairwise_singleton
-/
theorem nodup_singleton (a : α) : Nodup [a] :=
  pairwise_singleton _ _

/--
theorem `Nodup.of_cons` / 定理 `Nodup.of_cons`

English:
theorem Nodup.of_cons
  given: (h : Nodup (a :: l))
  statement: Nodup l
  proof: (nodup_cons.1 h).2

中文:
定理 Nodup.of_cons
  条件: (h : Nodup (a :: l))
  结论: Nodup l
  证明: (nodup_cons.1 h).2

Depends on / 依赖: nodup_cons
-/
theorem Nodup.of_cons (h : Nodup (a :: l)) : Nodup l :=
  (nodup_cons.1 h).2

/--
theorem `Nodup.notMem` / 定理 `Nodup.notMem`

English:
theorem Nodup.notMem
  given: (h : (a :: l).Nodup)
  statement: a ∉ l
  proof: (nodup_cons.1 h).1

中文:
定理 Nodup.notMem
  条件: (h : (a :: l).Nodup)
  结论: a ∉ l
  证明: (nodup_cons.1 h).1

Depends on / 依赖: nodup_cons
-/
theorem Nodup.notMem (h : (a :: l).Nodup) : a ∉ l :=
  (nodup_cons.1 h).1

/--
theorem `not_nodup_cons_of_mem` / 定理 `not_nodup_cons_of_mem`

English:
theorem not_nodup_cons_of_mem
  statement: a in l -> ¬Nodup (a :: l)
  proof: imp_not_comm.1 Nodup.notMem

中文:
定理 not_nodup_cons_of_mem
  结论: a in l -> ¬Nodup (a :: l)
  证明: imp_not_comm.1 Nodup.notMem

Depends on / 依赖: Nodup.notMem, imp_not_comm, notMem
-/
theorem not_nodup_cons_of_mem : a in l -> ¬Nodup (a :: l) :=
  imp_not_comm.1 Nodup.notMem


/--
theorem `not_nodup_pair` / 定理 `not_nodup_pair`

English:
theorem not_nodup_pair
  given: (a : α)
  statement: ¬Nodup [a, a]
  proof: not_nodup_cons_of_mem mem_singleton_self _

中文:
定理 not_nodup_pair
  条件: (a : α)
  结论: ¬Nodup [a, a]
  证明: not_nodup_cons_of_mem mem_singleton_self _

Depends on / 依赖: mem_singleton_self, not_nodup_cons_of_mem
-/
theorem not_nodup_pair (a : α) : ¬Nodup [a, a] :=
not_nodup_cons_of_mem mem_singleton_self _

/--
theorem `nodup_iff_sublist` / 定理 `nodup_iff_sublist`

English:
theorem nodup_iff_sublist
  given: {l : List α}
  statement: Nodup l ↔ forall a, ¬[a, a] <+ l
  proof: ⟨fun d a h => not_nodup_pair a (d.sublist h),
    by
      induction l <;> intro h; · exact nodup_nil
      case cons a l IH =>
        exact (IH fun a s => h a <| sublist_cons_of_sublist _ s).cons
fun al => h a (singleton_sublist.2 al).cons_cons _⟩

@[simp]

中文:
定理 nodup_iff_sublist
  条件: {l : 列表 α}
  结论: Nodup l ↔ 对任意 a, ¬[a, a] <+ l
  证明: ⟨fun d a h => not_nodup_pair a (d.sublist h),
    by
      induction l <;> intro h; · exact nodup_nil
      case cons a l IH =>
        exact (IH fun a s => h a <| sublist_cons_of_sublist _ s).cons
fun al => h a (singleton_sublist.2 al).cons_cons _⟩

@[simp]

Depends on / 依赖: cons_cons, d.sublist, nodup_nil, not_nodup_pair, singleton_sublist, sublist, sublist_cons_of_sublist
-/
theorem nodup_iff_sublist {l : List α} : Nodup l ↔ forall a, ¬[a, a] <+ l :=
  ⟨fun d a h => not_nodup_pair a (d.sublist h),
    by
      induction l <;> intro h; · exact nodup_nil
      case cons a l IH =>
        exact (IH fun a s => h a <| sublist_cons_of_sublist _ s).cons
fun al => h a (singleton_sublist.2 al).cons_cons _⟩

@[simp]
/--
theorem `nodup_mergeSort` / 定理 `nodup_mergeSort`

English:
theorem nodup_mergeSort
  given: {l : List α} {le : α -> α -> Bool}
  statement: (l.mergeSort le).Nodup ↔ l.Nodup
  proof: (mergeSort_perm l le).nodup_iff

protected alias ⟨_, Nodup.mergeSort⟩ := nodup_mergeSort

中文:
定理 nodup_mergeSort
  条件: {l : 列表 α} {le : α -> α -> 布尔值}
  结论: (l.mergeSort le).Nodup ↔ l.Nodup
  证明: (mergeSort_perm l le).nodup_iff

protected alias ⟨_, Nodup.mergeSort⟩ := nodup_mergeSort

Depends on / 依赖: mergeSort_perm, nodup_iff
-/
theorem nodup_mergeSort {l : List α} {le : α -> α -> Bool} : (l.mergeSort le).Nodup ↔ l.Nodup :=
  (mergeSort_perm l le).nodup_iff

protected alias ⟨_, Nodup.mergeSort⟩ := nodup_mergeSort

/--
theorem `nodup_iff_injective_getElem` / 定理 `nodup_iff_injective_getElem`

English:
theorem nodup_iff_injective_getElem
  given: {l : List α}
  proof: pairwise_iff_getElem.trans
    ⟨fun h i j hg => by
      obtain ⟨i, hi⟩ := i; obtain ⟨j, hj⟩ := j
      rcases Nat.lt_trichotomy i j with (hij | rfl | hji)
      · exact (h i j hi hj hij hg).elim
      · rfl
      · exact (h j i hj hi hji hg.symm).elim,
      fun hinj i j hi hj hij h => Nat.ne_of_lt hij (Fin.val_eq_of_eq (@hinj ⟨i, hi⟩ ⟨j, hj⟩ h))⟩

中文:
定理 nodup_iff_injective_getElem
  条件: {l : 列表 α}
  证明: pairwise_iff_getElem.trans
    ⟨fun h i j hg => by
      obtain ⟨i, hi⟩ := i; obtain ⟨j, hj⟩ := j
      rcases Nat.lt_trichotomy i j with (hij | rfl | hji)
      · exact (h i j hi hj hij hg).elim
      · rfl
      · exact (h j i hj hi hji hg.symm).elim,
      fun hinj i j hi hj hij h => Nat.ne_of_lt hij (Fin.val_eq_of_eq (@hinj ⟨i, hi⟩ ⟨j, hj⟩ h))⟩

Depends on / 依赖: Fin.val_eq_of_eq, Nat.lt_trichotomy, Nat.ne_of_lt, hg.symm, lt_trichotomy, ne_of_lt, pairwise_iff_getElem, pairwise_iff_getElem.trans, val_eq_of_eq
-/
theorem nodup_iff_injective_getElem {l : List α} :
    Nodup l ↔ Function.Injective (fun i : Fin l.length => l[i.1]) :=
  pairwise_iff_getElem.trans
    ⟨fun h i j hg => by
      obtain ⟨i, hi⟩ := i; obtain ⟨j, hj⟩ := j
      rcases Nat.lt_trichotomy i j with (hij | rfl | hji)
      · exact (h i j hi hj hij hg).elim
      · rfl
      · exact (h j i hj hi hji hg.symm).elim,
      fun hinj i j hi hj hij h => Nat.ne_of_lt hij (Fin.val_eq_of_eq (@hinj ⟨i, hi⟩ ⟨j, hj⟩ h))⟩

/--
theorem `nodup_iff_injective_get` / 定理 `nodup_iff_injective_get`

English:
theorem nodup_iff_injective_get
  given: {l : List α}
  statement: Nodup l ↔ Function.Injective l.get
  proof: nodup_iff_injective_getElem

中文:
定理 nodup_iff_injective_get
  条件: {l : 列表 α}
  结论: Nodup l ↔ 函数.单射 l.get
  证明: nodup_iff_injective_getElem

Depends on / 依赖: nodup_iff_injective_getElem
-/
theorem nodup_iff_injective_get {l : List α} : Nodup l ↔ Function.Injective l.get :=
  nodup_iff_injective_getElem

/--
theorem `Nodup.injective_get` / 定理 `Nodup.injective_get`

English:
theorem Nodup.injective_get
  given: {l : List α} (h : Nodup l)
  statement: Function.Injective l.get
  proof: nodup_iff_injective_get.mp h

中文:
定理 Nodup.injective_get
  条件: {l : 列表 α} (h : Nodup l)
  结论: 函数.单射 l.get
  证明: nodup_iff_injective_get.mp h
-/
protected theorem Nodup.injective_get {l : List α} (h : Nodup l) : Function.Injective l.get :=
  nodup_iff_injective_get.mp h

/--
theorem `_root_.Function.Injective.nodup` / 定理 `_root_.Function.Injective.nodup`

English:
theorem _root_.Function.Injective.nodup
  statement: {l : List α}
  proof: nodup_iff_injective_get.mpr h

中文:
定理 _root_.函数.单射.nodup
  结论: {l : 列表 α}
  证明: nodup_iff_injective_get.mpr h
-/
protected theorem _root_.Function.Injective.nodup {l : List α}
    (h : Function.Injective l.get) : l.Nodup := nodup_iff_injective_get.mpr h

/--
theorem `Nodup.get_inj_iff` / 定理 `Nodup.get_inj_iff`

English:
theorem Nodup.get_inj_iff
  given: {l : List α} (h : Nodup l) {i j : Fin l.length}
  proof: (nodup_iff_injective_get.1 h).eq_iff

中文:
定理 Nodup.get_inj_iff
  条件: {l : 列表 α} (h : Nodup l) {i j : 有限集 l.length}
  证明: (nodup_iff_injective_get.1 h).eq_iff

Depends on / 依赖: eq_iff, nodup_iff_injective_get
-/
theorem Nodup.get_inj_iff {l : List α} (h : Nodup l) {i j : Fin l.length} :
    l.get i = l.get j ↔ i = j :=
  (nodup_iff_injective_get.1 h).eq_iff

/--
theorem `Nodup.getElem_inj_iff` / 定理 `Nodup.getElem_inj_iff`

English:
theorem Nodup.getElem_inj_iff
  statement: {l : List α} (h : Nodup l)
  proof: by
  have := @Nodup.get_inj_iff _ _ h ⟨i, hi⟩ ⟨j, hj⟩
  simpa

中文:
定理 Nodup.getElem_inj_iff
  结论: {l : 列表 α} (h : Nodup l)
  证明: by
  have := @Nodup.get_inj_iff _ _ h ⟨i, hi⟩ ⟨j, hj⟩
  simpa

Depends on / 依赖: Nodup.get_inj_iff, get_inj_iff
-/
theorem Nodup.getElem_inj_iff {l : List α} (h : Nodup l)
    {i : Nat} {hi : i < l.length} {j : Nat} {hj : j < l.length} :
    l[i] = l[j] ↔ i = j := by
  have := @Nodup.get_inj_iff _ _ h ⟨i, hi⟩ ⟨j, hj⟩
  simpa

/--
theorem `nodup_iff_getElem?_ne_getElem?` / 定理 `nodup_iff_getElem?_ne_getElem?`

English:
theorem nodup_iff_getElem?_ne_getElem?
  given: {l : List α}
  proof: by
  grind [List.pairwise_iff_getElem]

中文:
定理 nodup_iff_getElem?_ne_getElem?
  条件: {l : 列表 α}
  证明: by
  grind [List.pairwise_iff_getElem]

Depends on / 依赖: List.pairwise_iff_getElem, pairwise_iff_getElem
-/
theorem nodup_iff_getElem?_ne_getElem? {l : List α} :
    l.Nodup ↔ forall i j : Nat, i < j -> j < l.length -> l[i]? != l[j]? := by
  grind [List.pairwise_iff_getElem]

/--
theorem `Nodup.ne_singleton_iff` / 定理 `Nodup.ne_singleton_iff`

English:
theorem Nodup.ne_singleton_iff
  given: {l : List α} (h : Nodup l) (x : α)
  proof: by
  induction l with
  | nil => simp
  | cons hd tl hl =>
    specialize hl h.of_cons
    by_cases hx : tl = [x]
    · simpa [hx, and_comm, and_or_left] using h
    · rw [← Ne, hl] at hx
      rcases hx with (rfl | ⟨y, hy, hx⟩)
      · simp
      · suffices exists y in hd :: tl, y != x by simpa [ne_nil_of_mem hy]
        exact ⟨y, mem_cons_of_mem _ hy, hx⟩

中文:
定理 Nodup.ne_singleton_iff
  条件: {l : 列表 α} (h : Nodup l) (x : α)
  证明: by
  induction l with
  | nil => simp
  | cons hd tl hl =>
    specialize hl h.of_cons
    by_cases hx : tl = [x]
    · simpa [hx, and_comm, and_or_left] using h
    · rw [← Ne, hl] at hx
      rcases hx with (rfl | ⟨y, hy, hx⟩)
      · simp
      · suffices exists y in hd :: tl, y != x by simpa [ne_nil_of_mem hy]
        exact ⟨y, mem_cons_of_mem _ hy, hx⟩

Depends on / 依赖: and_comm, and_or_left, h.of_cons, mem_cons_of_mem, ne_nil_of_mem, of_cons, specialize
-/
theorem Nodup.ne_singleton_iff {l : List α} (h : Nodup l) (x : α) :
    l != [x] ↔ l = [] ∨ exists y in l, y != x := by
  induction l with
  | nil => simp
  | cons hd tl hl =>
    specialize hl h.of_cons
    by_cases hx : tl = [x]
    · simpa [hx, and_comm, and_or_left] using h
    · rw [← Ne, hl] at hx
      rcases hx with (rfl | ⟨y, hy, hx⟩)
      · simp
      · suffices exists y in hd :: tl, y != x by simpa [ne_nil_of_mem hy]
        exact ⟨y, mem_cons_of_mem _ hy, hx⟩

/--
theorem `not_nodup_of_get_eq_of_ne` / 定理 `not_nodup_of_get_eq_of_ne`

English:
theorem not_nodup_of_get_eq_of_ne
  statement: (xs : List α) (n m : Fin xs.length)
  proof: by
  rw [nodup_iff_injective_get]
  exact fun hinj => hne (hinj h)

中文:
定理 not_nodup_of_get_eq_of_ne
  结论: (xs : 列表 α) (n m : 有限集 xs.length)
  证明: by
  rw [nodup_iff_injective_get]
  exact fun hinj => hne (hinj h)

Depends on / 依赖: nodup_iff_injective_get
-/
theorem not_nodup_of_get_eq_of_ne (xs : List α) (n m : Fin xs.length)
    (h : xs.get n = xs.get m) (hne : n != m) : ¬Nodup xs := by
  rw [nodup_iff_injective_get]
  exact fun hinj => hne (hinj h)

/--
lemma `Nodup.head_eq_getLast_iff` / 引理 `Nodup.head_eq_getLast_iff`

English:
lemma Nodup.head_eq_getLast_iff
  given: (hne : l != []) (hnd : l.Nodup)
  proof: by
  cases l <;> grind

中文:
引理 Nodup.head_eq_getLast_iff
  条件: (hne : l != []) (hnd : l.Nodup)
  证明: by
  cases l <;> grind
-/
lemma Nodup.head_eq_getLast_iff (hne : l != []) (hnd : l.Nodup) :
    l.head hne = l.getLast hne ↔ exists x, l = [x] := by
  cases l <;> grind

-- This is incorrectly named and should be `idxOf_get`;
-- this already exists, so will require a deprecation dance.
/--
theorem `get_idxOf` / 定理 `get_idxOf`

English:
theorem get_idxOf
  given: [BEq α] [LawfulBEq α] {l : List α} (H : Nodup l) (i : Fin l.length)
  proof: by
  simp [H]

中文:
定理 get_idxOf
  条件: [BEq α] [LawfulBEq α] {l : 列表 α} (H : Nodup l) (i : 有限集 l.length)
  证明: by
  simp [H]
-/
theorem get_idxOf [BEq α] [LawfulBEq α] {l : List α} (H : Nodup l) (i : Fin l.length) :
    idxOf (get l i) l = i := by
  simp [H]

/--
theorem `nodup_iff_count_le_one` / 定理 `nodup_iff_count_le_one`

English:
theorem nodup_iff_count_le_one
  given: [BEq α] [LawfulBEq α] {l : List α}
  statement: Nodup l ↔ forall a, count a l <= 1
  proof: nodup_iff_sublist.trans
    forall_congr' fun a =>
      have : replicate 2 a <+ l ↔ 1 < count a l := replicate_sublist_iff ..
      (not_congr this).trans Nat.not_lt

中文:
定理 nodup_iff_count_le_one
  条件: [BEq α] [LawfulBEq α] {l : 列表 α}
  结论: Nodup l ↔ 对任意 a, count a l <= 1
  证明: nodup_iff_sublist.trans
    forall_congr' fun a =>
      have : replicate 2 a <+ l ↔ 1 < count a l := replicate_sublist_iff ..
      (not_congr this).trans Nat.not_lt

Depends on / 依赖: Nat.not_lt, forall_congr, nodup_iff_sublist, nodup_iff_sublist.trans, not_congr, not_lt, replicate, replicate_sublist_iff
-/
theorem nodup_iff_count_le_one [BEq α] [LawfulBEq α] {l : List α} : Nodup l ↔ forall a, count a l <= 1 :=
nodup_iff_sublist.trans
    forall_congr' fun a =>
      have : replicate 2 a <+ l ↔ 1 < count a l := replicate_sublist_iff ..
      (not_congr this).trans Nat.not_lt

/--
theorem `nodup_iff_count_eq_one` / 定理 `nodup_iff_count_eq_one`

English:
theorem nodup_iff_count_eq_one
  given: [BEq α] [LawfulBEq α]
  statement: Nodup l ↔ forall a in l, count a l = 1
  proof: nodup_iff_count_le_one.trans forall_congr' fun x => by rw [← count_pos_iff]; grind

中文:
定理 nodup_iff_count_eq_one
  条件: [BEq α] [LawfulBEq α]
  结论: Nodup l ↔ 对任意 a in l, count a l = 1
  证明: nodup_iff_count_le_one.trans forall_congr' fun x => by rw [← count_pos_iff]; grind

Depends on / 依赖: count_pos_iff, forall_congr, nodup_iff_count_le_one, nodup_iff_count_le_one.trans
-/
theorem nodup_iff_count_eq_one [BEq α] [LawfulBEq α] : Nodup l ↔ forall a in l, count a l = 1 :=
nodup_iff_count_le_one.trans forall_congr' fun x => by rw [← count_pos_iff]; grind

/--
theorem `get_bijective_iff` / 定理 `get_bijective_iff`

English:
theorem get_bijective_iff
  given: [BEq α] [LawfulBEq α]
  statement: l.get.Bijective ↔ forall a, l.count a = 1
  proof: ⟨fun h a => (nodup_iff_count_eq_one.mp <| nodup_iff_injective_get.mpr h.injective)
a mem_iff_get.mpr h.surjective a,
fun h => ⟨nodup_iff_injective_get.mp nodup_iff_count_eq_one.mpr fun a _ => h a,
fun a => mem_iff_get.mp List.one_le_count_iff.mp by grind⟩⟩

中文:
定理 get_bijective_iff
  条件: [BEq α] [LawfulBEq α]
  结论: l.get.双射 ↔ 对任意 a, l.count a = 1
  证明: ⟨fun h a => (nodup_iff_count_eq_one.mp <| nodup_iff_injective_get.mpr h.injective)
a mem_iff_get.mpr h.surjective a,
fun h => ⟨nodup_iff_injective_get.mp nodup_iff_count_eq_one.mpr fun a _ => h a,
fun a => mem_iff_get.mp List.one_le_count_iff.mp by grind⟩⟩

Depends on / 依赖: List.one_le_count_iff.mp, h.injective, h.surjective, injective, mem_iff_get, mem_iff_get.mp, mem_iff_get.mpr, nodup_iff_count_eq_one, nodup_iff_count_eq_one.mp, nodup_iff_count_eq_one.mpr, nodup_iff_injective_get, nodup_iff_injective_get.mp, nodup_iff_injective_get.mpr, one_le_count_iff, surjective
-/
theorem get_bijective_iff [BEq α] [LawfulBEq α] : l.get.Bijective ↔ forall a, l.count a = 1 :=
  ⟨fun h a => (nodup_iff_count_eq_one.mp <| nodup_iff_injective_get.mpr h.injective)
a mem_iff_get.mpr h.surjective a,
fun h => ⟨nodup_iff_injective_get.mp nodup_iff_count_eq_one.mpr fun a _ => h a,
fun a => mem_iff_get.mp List.one_le_count_iff.mp by grind⟩⟩

/--
theorem `getElem_bijective_iff` / 定理 `getElem_bijective_iff`

English:
theorem getElem_bijective_iff
  given: [BEq α] [LawfulBEq α]
  proof: get_bijective_iff

@[simp]

中文:
定理 getElem_bijective_iff
  条件: [BEq α] [LawfulBEq α]
  证明: get_bijective_iff

@[simp]

Depends on / 依赖: get_bijective_iff
-/
theorem getElem_bijective_iff [BEq α] [LawfulBEq α] :
    (fun (n : Fin l.length) => l[n]).Bijective ↔ forall a, l.count a = 1 :=
  get_bijective_iff

@[simp]
/--
theorem `count_eq_one_of_mem` / 定理 `count_eq_one_of_mem`

English:
theorem count_eq_one_of_mem
  given: [BEq α] [LawfulBEq α] {a : α} {l : List α} (d : Nodup l) (h : a in l)
  proof: nodup_iff_count_eq_one.mp d a h

中文:
定理 count_eq_one_of_mem
  条件: [BEq α] [LawfulBEq α] {a : α} {l : 列表 α} (d : Nodup l) (h : a in l)
  证明: nodup_iff_count_eq_one.mp d a h

Depends on / 依赖: nodup_iff_count_eq_one, nodup_iff_count_eq_one.mp
-/
theorem count_eq_one_of_mem [BEq α] [LawfulBEq α] {a : α} {l : List α} (d : Nodup l) (h : a in l) :
    count a l = 1 :=
  nodup_iff_count_eq_one.mp d a h

/--
theorem `Nodup.of_append_left` / 定理 `Nodup.of_append_left`

English:
theorem Nodup.of_append_left
  statement: Nodup (l₁ ++ l₂) -> Nodup l₁
  proof: Nodup.sublist (sublist_append_left l₁ l₂)

中文:
定理 Nodup.of_append_left
  结论: Nodup (l₁ ++ l₂) -> Nodup l₁
  证明: Nodup.sublist (sublist_append_left l₁ l₂)

Depends on / 依赖: Nodup.sublist, sublist, sublist_append_left
-/
theorem Nodup.of_append_left : Nodup (l₁ ++ l₂) -> Nodup l₁ :=
  Nodup.sublist (sublist_append_left l₁ l₂)

/--
theorem `Nodup.of_append_right` / 定理 `Nodup.of_append_right`

English:
theorem Nodup.of_append_right
  statement: Nodup (l₁ ++ l₂) -> Nodup l₂
  proof: Nodup.sublist (sublist_append_right l₁ l₂)

中文:
定理 Nodup.of_append_right
  结论: Nodup (l₁ ++ l₂) -> Nodup l₂
  证明: Nodup.sublist (sublist_append_right l₁ l₂)

Depends on / 依赖: Nodup.sublist, sublist, sublist_append_right
-/
theorem Nodup.of_append_right : Nodup (l₁ ++ l₂) -> Nodup l₂ :=
  Nodup.sublist (sublist_append_right l₁ l₂)

/--
theorem `nodup_append'` / 定理 `nodup_append'`

English:
theorem nodup_append'
  given: {l₁ l₂ : List α}
  proof: by
  simp only [Nodup, pairwise_append, disjoint_iff_ne]

中文:
定理 nodup_append'
  条件: {l₁ l₂ : 列表 α}
  证明: by
  simp only [Nodup, pairwise_append, disjoint_iff_ne]

Depends on / 依赖: disjoint_iff_ne, pairwise_append
-/
theorem nodup_append' {l₁ l₂ : List α} :
    Nodup (l₁ ++ l₂) ↔ Nodup l₁ ∧ Nodup l₂ ∧ Disjoint l₁ l₂ := by
  simp only [Nodup, pairwise_append, disjoint_iff_ne]

/--
theorem `disjoint_of_nodup_append` / 定理 `disjoint_of_nodup_append`

English:
theorem disjoint_of_nodup_append
  given: {l₁ l₂ : List α} (d : Nodup (l₁ ++ l₂))
  statement: Disjoint l₁ l₂
  proof: (nodup_append'.1 d).2.2

protected alias Nodup.disjoint := disjoint_of_nodup_append

中文:
定理 disjoint_of_nodup_append
  条件: {l₁ l₂ : 列表 α} (d : Nodup (l₁ ++ l₂))
  结论: Disjoint l₁ l₂
  证明: (nodup_append'.1 d).2.2

protected alias Nodup.disjoint := disjoint_of_nodup_append

Depends on / 依赖: nodup_append
-/
theorem disjoint_of_nodup_append {l₁ l₂ : List α} (d : Nodup (l₁ ++ l₂)) : Disjoint l₁ l₂ :=
  (nodup_append'.1 d).2.2

protected alias Nodup.disjoint := disjoint_of_nodup_append

/--
theorem `Nodup.append` / 定理 `Nodup.append`

English:
theorem Nodup.append
  given: (d₁ : Nodup l₁) (d₂ : Nodup l₂) (dj : Disjoint l₁ l₂)
  statement: Nodup (l₁ ++ l₂)
  proof: nodup_append'.2 ⟨d₁, d₂, dj⟩

中文:
定理 Nodup.append
  条件: (d₁ : Nodup l₁) (d₂ : Nodup l₂) (dj : Disjoint l₁ l₂)
  结论: Nodup (l₁ ++ l₂)
  证明: nodup_append'.2 ⟨d₁, d₂, dj⟩

Depends on / 依赖: nodup_append
-/
theorem Nodup.append (d₁ : Nodup l₁) (d₂ : Nodup l₂) (dj : Disjoint l₁ l₂) : Nodup (l₁ ++ l₂) :=
  nodup_append'.2 ⟨d₁, d₂, dj⟩

/--
theorem `nodup_append_comm` / 定理 `nodup_append_comm`

English:
theorem nodup_append_comm
  given: {l₁ l₂ : List α}
  statement: Nodup (l₁ ++ l₂) ↔ Nodup (l₂ ++ l₁)
  proof: by
  simp only [nodup_append', and_left_comm, disjoint_comm]

中文:
定理 nodup_append_comm
  条件: {l₁ l₂ : 列表 α}
  结论: Nodup (l₁ ++ l₂) ↔ Nodup (l₂ ++ l₁)
  证明: by
  simp only [nodup_append', and_left_comm, disjoint_comm]

Depends on / 依赖: and_left_comm, disjoint_comm, nodup_append
-/
theorem nodup_append_comm {l₁ l₂ : List α} : Nodup (l₁ ++ l₂) ↔ Nodup (l₂ ++ l₁) := by
  simp only [nodup_append', and_left_comm, disjoint_comm]

/--
theorem `nodup_middle` / 定理 `nodup_middle`

English:
theorem nodup_middle
  given: {a : α} {l₁ l₂ : List α}
  proof: by
  simp only [nodup_append', not_or, and_left_comm, and_assoc, nodup_cons, mem_append,
    disjoint_cons_right]

中文:
定理 nodup_middle
  条件: {a : α} {l₁ l₂ : 列表 α}
  证明: by
  simp only [nodup_append', not_or, and_left_comm, and_assoc, nodup_cons, mem_append,
    disjoint_cons_right]

Depends on / 依赖: and_assoc, and_left_comm, disjoint_cons_right, mem_append, nodup_append, nodup_cons, not_or
-/
theorem nodup_middle {a : α} {l₁ l₂ : List α} :
    Nodup (l₁ ++ a :: l₂) ↔ Nodup (a :: (l₁ ++ l₂)) := by
  simp only [nodup_append', not_or, and_left_comm, and_assoc, nodup_cons, mem_append,
    disjoint_cons_right]

/--
theorem `Nodup.of_map` / 定理 `Nodup.of_map`

English:
theorem Nodup.of_map
  given: (f : α -> β) {l : List α}
  statement: Nodup (map f l) -> Nodup l
  proof: (Pairwise.of_map f) fun _ _ => mt congr_arg f

中文:
定理 Nodup.of_map
  条件: (f : α -> β) {l : 列表 α}
  结论: Nodup (map f l) -> Nodup l
  证明: (Pairwise.of_map f) fun _ _ => mt congr_arg f

Depends on / 依赖: Pairwise, Pairwise.of_map, congr_arg, of_map
-/
theorem Nodup.of_map (f : α -> β) {l : List α} : Nodup (map f l) -> Nodup l :=
(Pairwise.of_map f) fun _ _ => mt congr_arg f

/--
theorem `Nodup.map_on` / 定理 `Nodup.map_on`

English:
theorem Nodup.map_on
  given: {f : α -> β} (H : forall x in l, forall y in l, f x = f y -> x = y) (d : Nodup l)
  proof: Pairwise.map _ (fun a b ⟨ma, mb, n⟩ e => n (H a ma b mb e)) (Pairwise.and_mem.1 d)

中文:
定理 Nodup.map_on
  条件: {f : α -> β} (H : 对任意 x in l, 对任意 y in l, f x = f y -> x = y) (d : Nodup l)
  证明: Pairwise.map _ (fun a b ⟨ma, mb, n⟩ e => n (H a ma b mb e)) (Pairwise.and_mem.1 d)

Depends on / 依赖: Pairwise, Pairwise.and_mem, Pairwise.map, and_mem
-/
theorem Nodup.map_on {f : α -> β} (H : forall x in l, forall y in l, f x = f y -> x = y) (d : Nodup l) :
    (map f l).Nodup :=
  Pairwise.map _ (fun a b ⟨ma, mb, n⟩ e => n (H a ma b mb e)) (Pairwise.and_mem.1 d)

/--
theorem `inj_on_of_nodup_map` / 定理 `inj_on_of_nodup_map`

English:
theorem inj_on_of_nodup_map
  given: {f : α -> β} {l : List α} (d : Nodup (map f l))
  proof: by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [map, nodup_cons, mem_map, not_exists, not_and, ← Ne.eq_def] at d
    simp only [mem_cons]
    rintro _ (rfl | h₁) _ (rfl | h₂) h₃
    · rfl
    · apply (d.1 _ h₂ h₃.symm).elim
    · apply (d.1 _ h₁ h₃).elim
    · apply ih d.2 h₁ h₂ h₃

中文:
定理 inj_on_of_nodup_map
  条件: {f : α -> β} {l : 列表 α} (d : Nodup (map f l))
  证明: by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [map, nodup_cons, mem_map, not_exists, not_and, ← Ne.eq_def] at d
    simp only [mem_cons]
    rintro _ (rfl | h₁) _ (rfl | h₂) h₃
    · rfl
    · apply (d.1 _ h₂ h₃.symm).elim
    · apply (d.1 _ h₁ h₃).elim
    · apply ih d.2 h₁ h₂ h₃

Depends on / 依赖: Ne.eq_def, eq_def, mem_cons, mem_map, nodup_cons, not_and, not_exists
-/
theorem inj_on_of_nodup_map {f : α -> β} {l : List α} (d : Nodup (map f l)) :
    forall ⦃x⦄, x in l -> forall ⦃y⦄, y in l -> f x = f y -> x = y := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [map, nodup_cons, mem_map, not_exists, not_and, ← Ne.eq_def] at d
    simp only [mem_cons]
    rintro _ (rfl | h₁) _ (rfl | h₂) h₃
    · rfl
    · apply (d.1 _ h₂ h₃.symm).elim
    · apply (d.1 _ h₁ h₃).elim
    · apply ih d.2 h₁ h₂ h₃

/--
theorem `nodup_map_iff_inj_on` / 定理 `nodup_map_iff_inj_on`

English:
theorem nodup_map_iff_inj_on
  given: {f : α -> β} {l : List α} (d : Nodup l)
  proof: ⟨inj_on_of_nodup_map, fun h => d.map_on h⟩

中文:
定理 nodup_map_iff_inj_on
  条件: {f : α -> β} {l : 列表 α} (d : Nodup l)
  证明: ⟨inj_on_of_nodup_map, fun h => d.map_on h⟩

Depends on / 依赖: d.map_on, inj_on_of_nodup_map, map_on
-/
theorem nodup_map_iff_inj_on {f : α -> β} {l : List α} (d : Nodup l) :
    Nodup (map f l) ↔ forall x in l, forall y in l, f x = f y -> x = y :=
  ⟨inj_on_of_nodup_map, fun h => d.map_on h⟩

/--
theorem `Nodup.map` / 定理 `Nodup.map`

English:
theorem Nodup.map
  given: {f : α -> β} (hf : Injective f)
  statement: Nodup l -> Nodup (map f l)
  proof: Nodup.map_on fun _ _ _ _ h => hf h

中文:
定理 Nodup.map
  条件: {f : α -> β} (hf : 单射 f)
  结论: Nodup l -> Nodup (map f l)
  证明: Nodup.map_on fun _ _ _ _ h => hf h
-/
protected theorem Nodup.map {f : α -> β} (hf : Injective f) : Nodup l -> Nodup (map f l) :=
  Nodup.map_on fun _ _ _ _ h => hf h

/--
theorem `nodup_map_iff` / 定理 `nodup_map_iff`

English:
theorem nodup_map_iff
  given: {f : α -> β} {l : List α} (hf : Injective f)
  statement: Nodup (map f l) ↔ Nodup l
  proof: ⟨Nodup.of_map _, Nodup.map hf⟩

@[simp]

中文:
定理 nodup_map_iff
  条件: {f : α -> β} {l : 列表 α} (hf : 单射 f)
  结论: Nodup (map f l) ↔ Nodup l
  证明: ⟨Nodup.of_map _, Nodup.map hf⟩

@[simp]

Depends on / 依赖: Nodup.map, Nodup.of_map, of_map
-/
theorem nodup_map_iff {f : α -> β} {l : List α} (hf : Injective f) : Nodup (map f l) ↔ Nodup l :=
  ⟨Nodup.of_map _, Nodup.map hf⟩

@[simp]
/--
theorem `nodup_attach` / 定理 `nodup_attach`

English:
theorem nodup_attach
  given: {l : List α}
  statement: Nodup (attach l) ↔ Nodup l
  proof: ⟨fun h => attach_map_subtype_val l ▸ h.map fun _ _ => Subtype.ext, fun h =>
    Nodup.of_map Subtype.val ((attach_map_subtype_val l).symm ▸ h)⟩

protected alias ⟨Nodup.of_attach, Nodup.attach⟩ := nodup_attach

中文:
定理 nodup_attach
  条件: {l : 列表 α}
  结论: Nodup (attach l) ↔ Nodup l
  证明: ⟨fun h => attach_map_subtype_val l ▸ h.map fun _ _ => Subtype.ext, fun h =>
    Nodup.of_map Subtype.val ((attach_map_subtype_val l).symm ▸ h)⟩

protected alias ⟨Nodup.of_attach, Nodup.attach⟩ := nodup_attach

Depends on / 依赖: Nodup.of_map, Subtype, Subtype.ext, Subtype.val, attach_map_subtype_val, h.map, of_map
-/
theorem nodup_attach {l : List α} : Nodup (attach l) ↔ Nodup l :=
  ⟨fun h => attach_map_subtype_val l ▸ h.map fun _ _ => Subtype.ext, fun h =>
    Nodup.of_map Subtype.val ((attach_map_subtype_val l).symm ▸ h)⟩

protected alias ⟨Nodup.of_attach, Nodup.attach⟩ := nodup_attach

/--
theorem `Nodup.pmap` / 定理 `Nodup.pmap`

English:
theorem Nodup.pmap
  statement: {p : α -> Prop} {f : forall a, p a -> β} {l : List α} {H}
  proof: by
  grind

中文:
定理 Nodup.pmap
  结论: {p : α -> 命题} {f : 对任意 a, p a -> β} {l : 列表 α} {H}
  证明: by
  grind
-/
theorem Nodup.pmap {p : α -> Prop} {f : forall a, p a -> β} {l : List α} {H}
    (hf : forall a ha b hb, f a ha = f b hb -> a = b) (h : Nodup l) : Nodup (pmap f l H) := by
  grind

/--
theorem `Nodup.filter` / 定理 `Nodup.filter`

English:
theorem Nodup.filter
  given: (p : α -> Bool) {l}
  statement: Nodup l -> Nodup (filter p l)
  proof: by
  simpa using! Pairwise.filter p

@[simp]

中文:
定理 Nodup.filter
  条件: (p : α -> 布尔值) {l}
  结论: Nodup l -> Nodup (filter p l)
  证明: by
  simpa using! Pairwise.filter p

@[simp]

Depends on / 依赖: Pairwise, Pairwise.filter, filter
-/
theorem Nodup.filter (p : α -> Bool) {l} : Nodup l -> Nodup (filter p l) := by
  simpa using! Pairwise.filter p

@[simp]
/--
theorem `nodup_reverse` / 定理 `nodup_reverse`

English:
theorem nodup_reverse
  given: {l : List α}
  statement: Nodup (reverse l) ↔ Nodup l
  proof: pairwise_reverse.trans by simp only [Nodup, Ne, eq_comm]

中文:
定理 nodup_reverse
  条件: {l : 列表 α}
  结论: Nodup (reverse l) ↔ Nodup l
  证明: pairwise_reverse.trans by simp only [Nodup, Ne, eq_comm]

Depends on / 依赖: eq_comm, pairwise_reverse, pairwise_reverse.trans
-/
theorem nodup_reverse {l : List α} : Nodup (reverse l) ↔ Nodup l :=
pairwise_reverse.trans by simp only [Nodup, Ne, eq_comm]

/--
theorem `nodup_concat` / 定理 `nodup_concat`

English:
theorem nodup_concat
  given: (l : List α) (u : α)
  statement: (l.concat u).Nodup ↔ u ∉ l ∧ l.Nodup
  proof: by
  rw [← nodup_reverse]
  simp

中文:
定理 nodup_concat
  条件: (l : 列表 α) (u : α)
  结论: (l.concat u).Nodup ↔ u ∉ l ∧ l.Nodup
  证明: by
  rw [← nodup_reverse]
  simp

Depends on / 依赖: nodup_reverse
-/
theorem nodup_concat (l : List α) (u : α) : (l.concat u).Nodup ↔ u ∉ l ∧ l.Nodup := by
  rw [← nodup_reverse]
  simp

/--
lemma `Nodup.tail` / 引理 `Nodup.tail`

English:
lemma Nodup.tail
  given: {l : List α} (h : Nodup l)
  statement: Nodup l.tail
  proof: l.tail_sublist.nodup h

中文:
引理 Nodup.tail
  条件: {l : 列表 α} (h : Nodup l)
  结论: Nodup l.tail
  证明: l.tail_sublist.nodup h
-/
@[simp, grind ←] protected lemma Nodup.tail {l : List α} (h : Nodup l) : Nodup l.tail :=
  l.tail_sublist.nodup h

/--
lemma `nodup_tail_reverse` / 引理 `nodup_tail_reverse`

English:
lemma nodup_tail_reverse
  given: (l : List α) (h : l[0]? = l.getLast?)
  proof: by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases hl : l = []
    · simp_all
    · simp_all only [List.tail_reverse, List.nodup_reverse,
        List.dropLast_cons_of_ne_nil hl, List.tail_cons]
      simp only [length_cons, Nat.zero_lt_succ, getElem?_eq_getElem,
        Nat.add_one_sub_one, Nat.lt_add_one, Option.some.injEq, List.getElem_cons,
        show l.length != 0 by aesop, ↓reduceDIte, getLast?_eq_getElem?] at h
      rw [h]; rw [show l.Nodup = (l.dropLast ++ [l.getLast hl]).Nodup by
          simp [List.dropLast_eq_take],
        List.nodup_append_comm]
      simp [List.getLast_eq_getElem]

中文:
引理 nodup_tail_reverse
  条件: (l : 列表 α) (h : l[0]? = l.getLast?)
  证明: by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases hl : l = []
    · simp_all
    · simp_all only [List.tail_reverse, List.nodup_reverse,
        List.dropLast_cons_of_ne_nil hl, List.tail_cons]
      simp only [length_cons, Nat.zero_lt_succ, getElem?_eq_getElem,
        Nat.add_one_sub_one, Nat.lt_add_one, Option.some.injEq, List.getElem_cons,
        show l.length != 0 by aesop, ↓reduceDIte, getLast?_eq_getElem?] at h
      rw [h]; rw [show l.Nodup = (l.dropLast ++ [l.getLast hl]).Nodup by
          simp [List.dropLast_eq_take],
        List.nodup_append_comm]
      simp [List.getLast_eq_getElem]

Depends on / 依赖: List.dropLast_cons_of_ne_nil, List.dropLast_eq_take, List.getElem_cons, List.nod, List.nodup_reverse, List.tail_cons, List.tail_reverse, Nat.add_one_sub_one, Nat.lt_add_one, Nat.zero_lt_succ, Option.some.injEq, _eq_getElem, add_one_sub_one, dropLast, dropLast_cons_of_ne_nil, dropLast_eq_take, getElem, getElem_cons, getLast, l.Nodup
-/
lemma nodup_tail_reverse (l : List α) (h : l[0]? = l.getLast?) :
    Nodup l.reverse.tail ↔ Nodup l.tail := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases hl : l = []
    · simp_all
    · simp_all only [List.tail_reverse, List.nodup_reverse,
        List.dropLast_cons_of_ne_nil hl, List.tail_cons]
      simp only [length_cons, Nat.zero_lt_succ, getElem?_eq_getElem,
        Nat.add_one_sub_one, Nat.lt_add_one, Option.some.injEq, List.getElem_cons,
        show l.length != 0 by aesop, ↓reduceDIte, getLast?_eq_getElem?] at h
      rw [h]; rw [show l.Nodup = (l.dropLast ++ [l.getLast hl]).Nodup by
          simp [List.dropLast_eq_take],
        List.nodup_append_comm]
      simp [List.getLast_eq_getElem]

/--
lemma `Nodup.eq_of_head_mem_of_suffix` / 引理 `Nodup.eq_of_head_mem_of_suffix`

English:
lemma Nodup.eq_of_head_mem_of_suffix
  statement: (h : l₁ <:+ l₂) {hne : l₂ != []} (hl : l₂.head hne in l₁)
  proof: by
  grind [List.IsSuffix]

中文:
引理 Nodup.eq_of_head_mem_of_suffix
  结论: (h : l₁ <:+ l₂) {hne : l₂ != []} (hl : l₂.head hne in l₁)
  证明: by
  grind [List.IsSuffix]

Depends on / 依赖: IsSuffix, List.IsSuffix
-/
lemma Nodup.eq_of_head_mem_of_suffix (h : l₁ <:+ l₂) {hne : l₂ != []} (hl : l₂.head hne in l₁)
    (hnd : l₂.Nodup) : l₁ = l₂ := by
  grind [List.IsSuffix]

/--
lemma `Nodup.eq_of_getLast_mem_of_prefix` / 引理 `Nodup.eq_of_getLast_mem_of_prefix`

English:
lemma Nodup.eq_of_getLast_mem_of_prefix
  statement: (h : l₁ <+: l₂) {hne : l₂ != []} (hl : l₂.getLast hne in l₁)
  proof: by
  grind [List.IsPrefix]

中文:
引理 Nodup.eq_of_getLast_mem_of_prefix
  结论: (h : l₁ <+: l₂) {hne : l₂ != []} (hl : l₂.getLast hne in l₁)
  证明: by
  grind [List.IsPrefix]

Depends on / 依赖: IsPrefix, List.IsPrefix
-/
lemma Nodup.eq_of_getLast_mem_of_prefix (h : l₁ <+: l₂) {hne : l₂ != []} (hl : l₂.getLast hne in l₁)
    (hnd : l₂.Nodup) : l₁ = l₂ := by
  grind [List.IsPrefix]

/--
lemma `Nodup.prefix_of_head_mem_of_infix` / 引理 `Nodup.prefix_of_head_mem_of_infix`

English:
lemma Nodup.prefix_of_head_mem_of_infix
  statement: (h : l₁ <:+: l₂) {hne : l₂ != []} (hl : l₂.head hne in l₁)
  proof: by
  grind [List.IsInfix]

中文:
引理 Nodup.prefix_of_head_mem_of_infix
  结论: (h : l₁ <:+: l₂) {hne : l₂ != []} (hl : l₂.head hne in l₁)
  证明: by
  grind [List.IsInfix]

Depends on / 依赖: IsInfix, List.IsInfix
-/
lemma Nodup.prefix_of_head_mem_of_infix (h : l₁ <:+: l₂) {hne : l₂ != []} (hl : l₂.head hne in l₁)
    (hnd : l₂.Nodup) : l₁ <+: l₂ := by
  grind [List.IsInfix]

/--
lemma `Nodup.suffix_of_getLast_mem_of_infix` / 引理 `Nodup.suffix_of_getLast_mem_of_infix`

English:
lemma Nodup.suffix_of_getLast_mem_of_infix
  statement: (h : l₁ <:+: l₂) {hne : l₂ != []}
  proof: by
  grind [List.IsInfix]

中文:
引理 Nodup.suffix_of_getLast_mem_of_infix
  结论: (h : l₁ <:+: l₂) {hne : l₂ != []}
  证明: by
  grind [List.IsInfix]

Depends on / 依赖: IsInfix, List.IsInfix
-/
lemma Nodup.suffix_of_getLast_mem_of_infix (h : l₁ <:+: l₂) {hne : l₂ != []}
    (hl : l₂.getLast hne in l₁) (hnd : l₂.Nodup) : l₁ <:+ l₂ := by
  grind [List.IsInfix]

/--
lemma `Nodup.eq_of_head_mem_of_getLast_mem_of_infix` / 引理 `Nodup.eq_of_head_mem_of_getLast_mem_of_infix`

English:
lemma Nodup.eq_of_head_mem_of_getLast_mem_of_infix
  statement: (h : l₁ <:+: l₂) {hne : l₂ != []}
  proof: by
  grind [List.IsInfix]

中文:
引理 Nodup.eq_of_head_mem_of_getLast_mem_of_infix
  结论: (h : l₁ <:+: l₂) {hne : l₂ != []}
  证明: by
  grind [List.IsInfix]

Depends on / 依赖: IsInfix, List.IsInfix
-/
lemma Nodup.eq_of_head_mem_of_getLast_mem_of_infix (h : l₁ <:+: l₂) {hne : l₂ != []}
    (hlh : l₂.head hne in l₁) (hlg : l₂.getLast hne in l₁) (hnd : l₂.Nodup) : l₁ = l₂ := by
  grind [List.IsInfix]

/--
theorem `Nodup.erase_getElem` / 定理 `Nodup.erase_getElem`

English:
theorem Nodup.erase_getElem
  statement: [BEq α] [LawfulBEq α] {l : List α} (hl : l.Nodup)
  proof: by
  induction l generalizing i with
  | nil => simp
  | cons a l IH =>
    cases i with
    | zero => simp
    | succ i => grind

中文:
定理 Nodup.erase_getElem
  结论: [BEq α] [LawfulBEq α] {l : 列表 α} (hl : l.Nodup)
  证明: by
  induction l generalizing i with
  | nil => simp
  | cons a l IH =>
    cases i with
    | zero => simp
    | succ i => grind

Depends on / 依赖: generalizing
-/
theorem Nodup.erase_getElem [BEq α] [LawfulBEq α] {l : List α} (hl : l.Nodup)
    (i : Nat) (h : i < l.length) : l.erase l[i] = l.eraseIdx ↑i := by
  induction l generalizing i with
  | nil => simp
  | cons a l IH =>
    cases i with
    | zero => simp
    | succ i => grind

/--
theorem `Nodup.erase_get` / 定理 `Nodup.erase_get`

English:
theorem Nodup.erase_get
  given: [BEq α] [LawfulBEq α] {l : List α} (hl : l.Nodup) (i : Fin l.length)
  proof: by
  simp [erase_getElem, hl]

中文:
定理 Nodup.erase_get
  条件: [BEq α] [LawfulBEq α] {l : 列表 α} (hl : l.Nodup) (i : 有限集 l.length)
  证明: by
  simp [erase_getElem, hl]

Depends on / 依赖: erase_getElem
-/
theorem Nodup.erase_get [BEq α] [LawfulBEq α] {l : List α} (hl : l.Nodup) (i : Fin l.length) :
    l.erase (l.get i) = l.eraseIdx ↑i := by
  simp [erase_getElem, hl]

/--
theorem `Nodup.diff` / 定理 `Nodup.diff`

English:
theorem Nodup.diff
  given: [BEq α] [LawfulBEq α]
  statement: l₁.Nodup -> (l₁.diff l₂).Nodup
  proof: Nodup.sublist diff_sublist _ _

中文:
定理 Nodup.diff
  条件: [BEq α] [LawfulBEq α]
  结论: l₁.Nodup -> (l₁.diff l₂).Nodup
  证明: Nodup.sublist diff_sublist _ _

Depends on / 依赖: Nodup.sublist, diff_sublist, sublist
-/
theorem Nodup.diff [BEq α] [LawfulBEq α] : l₁.Nodup -> (l₁.diff l₂).Nodup :=
Nodup.sublist diff_sublist _ _

/--
theorem `nodup_flatten` / 定理 `nodup_flatten`

English:
theorem nodup_flatten
  given: {L : List (List α)}
  proof: by
  simp only [Nodup, pairwise_flatten, disjoint_left.symm, forall_mem_ne]

中文:
定理 nodup_flatten
  条件: {L : 列表 (列表 α)}
  证明: by
  simp only [Nodup, pairwise_flatten, disjoint_left.symm, forall_mem_ne]

Depends on / 依赖: disjoint_left, disjoint_left.symm, forall_mem_ne, pairwise_flatten
-/
theorem nodup_flatten {L : List (List α)} :
    Nodup (flatten L) ↔ (forall l in L, Nodup l) ∧ Pairwise Disjoint L := by
  simp only [Nodup, pairwise_flatten, disjoint_left.symm, forall_mem_ne]

/--
theorem `nodup_flatMap` / 定理 `nodup_flatMap`

English:
theorem nodup_flatMap
  given: {l₁ : List α} {f : α -> List β}
  proof: by
  simp only [List.flatMap, nodup_flatten, pairwise_map, and_comm, mem_map,
    exists_imp, and_imp]
  rw [show (forall (l : List β) (x : α)]; rw [f x = l -> x in l₁ -> Nodup l) ↔ forall x : α]; rw [x in l₁ -> Nodup (f x)
from forall_comm.trans forall_congr' fun _ => forall_eq']

中文:
定理 nodup_flatMap
  条件: {l₁ : 列表 α} {f : α -> 列表 β}
  证明: by
  simp only [List.flatMap, nodup_flatten, pairwise_map, and_comm, mem_map,
    exists_imp, and_imp]
  rw [show (forall (l : List β) (x : α)]; rw [f x = l -> x in l₁ -> Nodup l) ↔ forall x : α]; rw [x in l₁ -> Nodup (f x)
from forall_comm.trans forall_congr' fun _ => forall_eq']

Depends on / 依赖: List.flatMap, and_comm, and_imp, exists_imp, flatMap, forall_comm, forall_comm.trans, forall_congr, forall_eq, mem_map, nodup_flatten, pairwise_map
-/
theorem nodup_flatMap {l₁ : List α} {f : α -> List β} :
    Nodup (l₁.flatMap f) ↔
      (forall x in l₁, Nodup (f x)) ∧ Pairwise (Disjoint on f) l₁ := by
  simp only [List.flatMap, nodup_flatten, pairwise_map, and_comm, mem_map,
    exists_imp, and_imp]
  rw [show (forall (l : List β) (x : α)]; rw [f x = l -> x in l₁ -> Nodup l) ↔ forall x : α]; rw [x in l₁ -> Nodup (f x)
from forall_comm.trans forall_congr' fun _ => forall_eq']

/--
theorem `Nodup.product` / 定理 `Nodup.product`

English:
theorem Nodup.product
  given: {l₂ : List β} (d₁ : l₁.Nodup) (d₂ : l₂.Nodup)
  proof: nodup_flatMap.2
⟨fun a _ => d₂.map LeftInverse.injective fun b => (rfl : (a, b).2 = b),
      d₁.imp fun {a₁ a₂} n x h₁ h₂ => by
        rcases mem_map.1 h₁ with ⟨b₁, _, rfl⟩
        rcases mem_map.1 h₂ with ⟨b₂, mb₂, ⟨⟩⟩
        exact n rfl⟩

中文:
定理 Nodup.product
  条件: {l₂ : 列表 β} (d₁ : l₁.Nodup) (d₂ : l₂.Nodup)
  证明: nodup_flatMap.2
⟨fun a _ => d₂.map LeftInverse.injective fun b => (rfl : (a, b).2 = b),
      d₁.imp fun {a₁ a₂} n x h₁ h₂ => by
        rcases mem_map.1 h₁ with ⟨b₁, _, rfl⟩
        rcases mem_map.1 h₂ with ⟨b₂, mb₂, ⟨⟩⟩
        exact n rfl⟩
-/
protected theorem Nodup.product {l₂ : List β} (d₁ : l₁.Nodup) (d₂ : l₂.Nodup) :
    (l₁ ×ˢ l₂).Nodup :=
  nodup_flatMap.2
⟨fun a _ => d₂.map LeftInverse.injective fun b => (rfl : (a, b).2 = b),
      d₁.imp fun {a₁ a₂} n x h₁ h₂ => by
        rcases mem_map.1 h₁ with ⟨b₁, _, rfl⟩
        rcases mem_map.1 h₂ with ⟨b₂, mb₂, ⟨⟩⟩
        exact n rfl⟩

/--
theorem `Nodup.sigma` / 定理 `Nodup.sigma`

English:
theorem Nodup.sigma
  statement: {σ : α -> Type*} {l₂ : forall a, List (σ a)} (d₁ : Nodup l₁)
  proof: nodup_flatMap.2
    ⟨fun a _ => (d₂ a).map fun b b' h => by injection h with _ h,
      d₁.imp fun {a₁ a₂} n x h₁ h₂ => by
        rcases mem_map.1 h₁ with ⟨b₁, _, rfl⟩
        rcases mem_map.1 h₂ with ⟨b₂, mb₂, ⟨⟩⟩
        exact n rfl⟩

中文:
定理 Nodup.sigma
  结论: {σ : α -> 类型} {l₂ : 对任意 a, 列表 (σ a)} (d₁ : Nodup l₁)
  证明: nodup_flatMap.2
    ⟨fun a _ => (d₂ a).map fun b b' h => by injection h with _ h,
      d₁.imp fun {a₁ a₂} n x h₁ h₂ => by
        rcases mem_map.1 h₁ with ⟨b₁, _, rfl⟩
        rcases mem_map.1 h₂ with ⟨b₂, mb₂, ⟨⟩⟩
        exact n rfl⟩

Depends on / 依赖: injection, mem_map, nodup_flatMap
-/
theorem Nodup.sigma {σ : α -> Type*} {l₂ : forall a, List (σ a)} (d₁ : Nodup l₁)
    (d₂ : forall a, Nodup (l₂ a)) : (l₁.sigma l₂).Nodup :=
  nodup_flatMap.2
    ⟨fun a _ => (d₂ a).map fun b b' h => by injection h with _ h,
      d₁.imp fun {a₁ a₂} n x h₁ h₂ => by
        rcases mem_map.1 h₁ with ⟨b₁, _, rfl⟩
        rcases mem_map.1 h₂ with ⟨b₂, mb₂, ⟨⟩⟩
        exact n rfl⟩

/--
theorem `Nodup.filterMap` / 定理 `Nodup.filterMap`

English:
theorem Nodup.filterMap
  given: {f : α -> Option β} (h : forall a a' b, b in f a -> b in f a' -> a = a')
  proof: (Pairwise.filterMap f) @fun a a' n b bm b' bm' e => n h a a' b' (by rw [← e]; exact bm) bm'

中文:
定理 Nodup.filterMap
  条件: {f : α -> 选项类型 β} (h : 对任意 a a' b, b in f a -> b in f a' -> a = a')
  证明: (Pairwise.filterMap f) @fun a a' n b bm b' bm' e => n h a a' b' (by rw [← e]; exact bm) bm'
-/
protected theorem Nodup.filterMap {f : α -> Option β} (h : forall a a' b, b in f a -> b in f a' -> a = a') :
    Nodup l -> Nodup (filterMap f l) :=
(Pairwise.filterMap f) @fun a a' n b bm b' bm' e => n h a a' b' (by rw [← e]; exact bm) bm'

/--
theorem `Nodup.concat` / 定理 `Nodup.concat`

English:
theorem Nodup.concat
  given: (h : a ∉ l) (h' : l.Nodup)
  statement: (l.concat a).Nodup
  proof: by
  rw [concat_eq_append]; exact h'.append (nodup_singleton _) (disjoint_singleton.2 h)

中文:
定理 Nodup.concat
  条件: (h : a ∉ l) (h' : l.Nodup)
  结论: (l.concat a).Nodup
  证明: by
  rw [concat_eq_append]; exact h'.append (nodup_singleton _) (disjoint_singleton.2 h)
-/
protected theorem Nodup.concat (h : a ∉ l) (h' : l.Nodup) : (l.concat a).Nodup := by
  rw [concat_eq_append]; exact h'.append (nodup_singleton _) (disjoint_singleton.2 h)

/--
theorem `Nodup.insert` / 定理 `Nodup.insert`

English:
theorem Nodup.insert
  given: [BEq α] [LawfulBEq α] (h : l.Nodup)
  statement: (l.insert a).Nodup
  proof: if h' : a in l then by rw [insert_of_mem h']; exact h
  else by rw [insert_of_not_mem h', nodup_cons]; constructor <;> assumption

中文:
定理 Nodup.insert
  条件: [BEq α] [LawfulBEq α] (h : l.Nodup)
  结论: (l.insert a).Nodup
  证明: if h' : a in l then by rw [insert_of_mem h']; exact h
  else by rw [insert_of_not_mem h', nodup_cons]; constructor <;> assumption
-/
protected theorem Nodup.insert [BEq α] [LawfulBEq α] (h : l.Nodup) : (l.insert a).Nodup :=
  if h' : a in l then by rw [insert_of_mem h']; exact h
  else by rw [insert_of_not_mem h', nodup_cons]; constructor <;> assumption

/--
theorem `Nodup.union` / 定理 `Nodup.union`

English:
theorem Nodup.union
  given: [BEq α] [LawfulBEq α] (l₁ : List α) (h : Nodup l₂)
  statement: (l₁ union l₂).Nodup
  proof: by
  induction l₁ generalizing l₂ with
  | nil => exact h
  | cons a l₁ ih => exact (ih h).insert

中文:
定理 Nodup.union
  条件: [BEq α] [LawfulBEq α] (l₁ : 列表 α) (h : Nodup l₂)
  结论: (l₁ union l₂).Nodup
  证明: by
  induction l₁ generalizing l₂ with
  | nil => exact h
  | cons a l₁ ih => exact (ih h).insert

Depends on / 依赖: generalizing, insert
-/
theorem Nodup.union [BEq α] [LawfulBEq α] (l₁ : List α) (h : Nodup l₂) : (l₁ union l₂).Nodup := by
  induction l₁ generalizing l₂ with
  | nil => exact h
  | cons a l₁ ih => exact (ih h).insert

/--
theorem `Nodup.inter` / 定理 `Nodup.inter`

English:
theorem Nodup.inter
  given: [BEq α] (l₂ : List α)
  statement: Nodup l₁ -> Nodup (l₁ inter l₂)
  proof: Nodup.filter _

中文:
定理 Nodup.inter
  条件: [BEq α] (l₂ : 列表 α)
  结论: Nodup l₁ -> Nodup (l₁ inter l₂)
  证明: Nodup.filter _

Depends on / 依赖: Nodup.filter, filter
-/
theorem Nodup.inter [BEq α] (l₂ : List α) : Nodup l₁ -> Nodup (l₁ inter l₂) :=
  Nodup.filter _

/--
theorem `Nodup.sdiff_eq_filter` / 定理 `Nodup.sdiff_eq_filter`

English:
theorem Nodup.sdiff_eq_filter
  given: [BEq α] [LawfulBEq α]
  proof: Nodup.sdiff_eq_filter

中文:
定理 Nodup.sdiff_eq_filter
  条件: [BEq α] [LawfulBEq α]
  证明: Nodup.sdiff_eq_filter
-/
theorem Nodup.sdiff_eq_filter [BEq α] [LawfulBEq α] :
    forall {l₁ l₂ : List α} (_ : l₁.Nodup), l₁.diff l₂ = l₁.filter (· ∉ l₂)
  | l₁, [], _ => by simp
  | l₁, a :: l₂, hl₁ => by
    rw [diff_cons]; rw [(hl₁.erase _).sdiff_eq_filter]; rw [hl₁.erase_eq_filter]; rw [filter_filter]
    simp only [decide_not, bne, Bool.and_comm, decide_mem_cons, Bool.not_or]

@[deprecated (since := "2026-06-03")] alias Nodup.diff_eq_filter := Nodup.sdiff_eq_filter

/--
theorem `Nodup.mem_sdiff_iff` / 定理 `Nodup.mem_sdiff_iff`

English:
theorem Nodup.mem_sdiff_iff
  given: [BEq α] [LawfulBEq α] (hl₁ : l₁.Nodup)
  proof: by
  rw [hl₁.sdiff_eq_filter]; rw [mem_filter]; rw [decide_eq_true_iff]

@[deprecated (since := "2026-06-03")] alias Nodup.mem_diff_iff := Nodup.mem_sdiff_iff

中文:
定理 Nodup.mem_sdiff_iff
  条件: [BEq α] [LawfulBEq α] (hl₁ : l₁.Nodup)
  证明: by
  rw [hl₁.sdiff_eq_filter]; rw [mem_filter]; rw [decide_eq_true_iff]

@[deprecated (since := "2026-06-03")] alias Nodup.mem_diff_iff := Nodup.mem_sdiff_iff

Depends on / 依赖: decide_eq_true_iff, mem_filter, sdiff_eq_filter
-/
theorem Nodup.mem_sdiff_iff [BEq α] [LawfulBEq α] (hl₁ : l₁.Nodup) :
    a in l₁.diff l₂ ↔ a in l₁ ∧ a ∉ l₂ := by
  rw [hl₁.sdiff_eq_filter]; rw [mem_filter]; rw [decide_eq_true_iff]

@[deprecated (since := "2026-06-03")] alias Nodup.mem_diff_iff := Nodup.mem_sdiff_iff

/--
theorem `Nodup.set` / 定理 `Nodup.set`

English:
theorem Nodup.set

中文:
定理 Nodup.set
-/
protected theorem Nodup.set :
    forall {l : List α} {n : Nat} {a : α} (_ : l.Nodup) (_ : a ∉ l), (l.set n a).Nodup
  | [], _, _, _, _ => nodup_nil
  | _ :: _, 0, _, hl, ha => nodup_cons.2 ⟨mt (mem_cons_of_mem _) ha, (nodup_cons.1 hl).2⟩
  | _ :: _, _ + 1, _, hl, ha =>
    nodup_cons.2
      ⟨fun h =>
        (mem_or_eq_of_mem_set h).elim (nodup_cons.1 hl).1 fun hba => ha (hba ▸ mem_cons_self),
        hl.of_cons.set (mt (mem_cons_of_mem _) ha)⟩

/--
theorem `Nodup.map_update` / 定理 `Nodup.map_update`

English:
theorem Nodup.map_update
  given: [DecidableEq α] {l : List α} (hl : l.Nodup) (f : α -> β) (x : α) (y : β)
  proof: by
  induction l with | nil => simp | cons hd tl ihl => ?_
  rw [nodup_cons] at hl
  simp only [mem_cons, map, ihl hl.2]
  by_cases H : hd = x
  · subst hd
    simp [hl.1]
  · simp [Ne.symm H, H, ← apply_ite (cons (f hd))]

中文:
定理 Nodup.map_update
  条件: [DecidableEq α] {l : 列表 α} (hl : l.Nodup) (f : α -> β) (x : α) (y : β)
  证明: by
  induction l with | nil => simp | cons hd tl ihl => ?_
  rw [nodup_cons] at hl
  simp only [mem_cons, map, ihl hl.2]
  by_cases H : hd = x
  · subst hd
    simp [hl.1]
  · simp [Ne.symm H, H, ← apply_ite (cons (f hd))]

Depends on / 依赖: Ne.symm, apply_ite, mem_cons, nodup_cons
-/
theorem Nodup.map_update [DecidableEq α] {l : List α} (hl : l.Nodup) (f : α -> β) (x : α) (y : β) :
    l.map (Function.update f x y) =
      if x in l then (l.map f).set (l.idxOf x) y else l.map f := by
  induction l with | nil => simp | cons hd tl ihl => ?_
  rw [nodup_cons] at hl
  simp only [mem_cons, map, ihl hl.2]
  by_cases H : hd = x
  · subst hd
    simp [hl.1]
  · simp [Ne.symm H, H, ← apply_ite (cons (f hd))]

/--
theorem `Nodup.pairwise_of_forall_ne` / 定理 `Nodup.pairwise_of_forall_ne`

English:
theorem Nodup.pairwise_of_forall_ne
  statement: {l : List α} {r : α -> α -> Prop} (hl : l.Nodup)
  proof: by
  grind [List.pairwise_iff_forall_sublist]

中文:
定理 Nodup.pairwise_of_对任意_ne
  结论: {l : 列表 α} {r : α -> α -> 命题} (hl : l.Nodup)
  证明: by
  grind [List.pairwise_iff_forall_sublist]

Depends on / 依赖: List.pairwise_iff_forall_sublist, pairwise_iff_forall_sublist
-/
theorem Nodup.pairwise_of_forall_ne {l : List α} {r : α -> α -> Prop} (hl : l.Nodup)
    (h : forall a in l, forall b in l, a != b -> r a b) : l.Pairwise r := by
  grind [List.pairwise_iff_forall_sublist]

/--
theorem `Nodup.take_eq_filter_mem` / 定理 `Nodup.take_eq_filter_mem`

English:
theorem Nodup.take_eq_filter_mem
  given: [BEq α] [LawfulBEq α]
  proof: fun h => (nodup_cons.1 hl).1 (h ▸ hx)
    simp +contextual [List.mem_filter, this, hx]

中文:
定理 Nodup.take_eq_filter_mem
  条件: [BEq α] [LawfulBEq α]
  证明: fun h => (nodup_cons.1 hl).1 (h ▸ hx)
    simp +contextual [List.mem_filter, this, hx]

Depends on / 依赖: nodup_cons
-/
theorem Nodup.take_eq_filter_mem [BEq α] [LawfulBEq α] :
    forall {l : List α} {n : Nat} (_ : l.Nodup), l.take n = l.filter (l.take n).elem
  | [], n, _ => by simp
  | b::l, 0, _ => by simp
  | b::l, n + 1, hl => by
    rw [take_succ_cons]; rw [Nodup.take_eq_filter_mem (Nodup.of_cons hl)]; rw [filter_cons_of_pos (by simp)]
    congr 1
    refine List.filter_congr ?_
    intro x hx
    have : x != b := fun h => (nodup_cons.1 hl).1 (h ▸ hx)
    simp +contextual [List.mem_filter, this, hx]
end List

/--
theorem `Option.toList_nodup` / 定理 `Option.toList_nodup`

English:
theorem Option.toList_nodup
  statement: forall o : Option α, o.toList.Nodup

中文:
定理 选项类型.toList_nodup
  结论: 对任意 o : 选项类型 α, o.toList.Nodup
-/
theorem Option.toList_nodup : forall o : Option α, o.toList.Nodup
  | none => List.nodup_nil
  | some x => List.nodup_singleton x
