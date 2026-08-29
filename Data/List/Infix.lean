/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.List.TakeDrop
public import Mathlib.Data.List.Induction
public import Mathlib.Data.Nat.Basic
public import Mathlib.Order.Basic
public import Mathlib.Data.List.Basic

/-!
# Prefixes, suffixes, infixes

This file proves properties about
* `List.isPrefix`: `l₁` is a prefix of `l₂` if `l₂` starts with `l₁`.
* `List.isSuffix`: `l₁` is a suffix of `l₂` if `l₂` ends with `l₁`.
* `List.isInfix`: `l₁` is an infix of `l₂` if `l₁` is a prefix of some suffix of `l₂`.
* `List.inits`: The list of prefixes of a list.
* `List.tails`: The list of prefixes of a list.
* `insert` on lists

All those (except `insert`) are defined in `Mathlib/Data/List/Defs.lean`.

## Notation

* `l₁ <+: l₂`: `l₁` is a prefix of `l₂`.
* `l₁ <:+ l₂`: `l₁` is a suffix of `l₂`.
* `l₁ <:+: l₂`: `l₁` is an infix of `l₂`.
-/

public section

variable {α β : Type*}

namespace List

variable {l l₁ l₂ l₃ : List α} {a b : α}

/-! ### prefix, suffix, infix -/

section Fix

/--
lemma `IsPrefix.take` / 引理 `IsPrefix.take`

English:
lemma IsPrefix.take
  given: (h : l₁ <+: l₂) (n : Nat)
  statement: l₁.take n <+: l₂.take n
  proof: by
  simpa [prefix_take_iff, Nat.min_le_left] using (take_prefix n l₁).trans h

中文:
引理 IsPrefix.take
  条件: (h : l₁ <+: l₂) (n : 自然数)
  结论: l₁.take n <+: l₂.take n
  证明: by
  simpa [prefix_take_iff, Nat.min_le_left] using (take_prefix n l₁).trans h
-/
@[gcongr] lemma IsPrefix.take (h : l₁ <+: l₂) (n : Nat) : l₁.take n <+: l₂.take n := by
  simpa [prefix_take_iff, Nat.min_le_left] using (take_prefix n l₁).trans h

/--
lemma `IsPrefix.drop` / 引理 `IsPrefix.drop`

English:
lemma IsPrefix.drop
  given: (h : l₁ <+: l₂) (n : Nat)
  statement: l₁.drop n <+: l₂.drop n
  proof: by
  rw [prefix_iff_eq_take.mp h]; rw [drop_take]; apply take_prefix

中文:
引理 IsPrefix.drop
  条件: (h : l₁ <+: l₂) (n : 自然数)
  结论: l₁.drop n <+: l₂.drop n
  证明: by
  rw [prefix_iff_eq_take.mp h]; rw [drop_take]; apply take_prefix
-/
@[gcongr] lemma IsPrefix.drop (h : l₁ <+: l₂) (n : Nat) : l₁.drop n <+: l₂.drop n := by
  rw [prefix_iff_eq_take.mp h]; rw [drop_take]; apply take_prefix

attribute [gcongr] take_prefix_take_left

/--
lemma `isPrefix_append_of_length` / 引理 `isPrefix_append_of_length`

English:
lemma isPrefix_append_of_length
  given: (h : l₁.length <= l₂.length)
  statement: l₁ <+: l₂ ++ l₃ ↔ l₁ <+: l₂
  proof: ⟨fun h => by rw [prefix_iff_eq_take] at *; nth_rw 1 [h, take_eq_left_iff]; tauto,
fun h => h.trans l₂.prefix_append l₃⟩

中文:
引理 isPrefix_append_of_length
  条件: (h : l₁.length <= l₂.length)
  结论: l₁ <+: l₂ ++ l₃ ↔ l₁ <+: l₂
  证明: ⟨fun h => by rw [prefix_iff_eq_take] at *; nth_rw 1 [h, take_eq_left_iff]; tauto,
fun h => h.trans l₂.prefix_append l₃⟩

Depends on / 依赖: h.trans, nth_rw, prefix_append, prefix_iff_eq_take, take_eq_left_iff
-/
lemma isPrefix_append_of_length (h : l₁.length <= l₂.length) : l₁ <+: l₂ ++ l₃ ↔ l₁ <+: l₂ :=
  ⟨fun h => by rw [prefix_iff_eq_take] at *; nth_rw 1 [h, take_eq_left_iff]; tauto,
fun h => h.trans l₂.prefix_append l₃⟩

/--
lemma `take_isPrefix_take` / 引理 `take_isPrefix_take`

English:
lemma take_isPrefix_take
  given: {m n : Nat}
  statement: l.take m <+: l.take n ↔ m <= n ∨ l.length <= n
  proof: by
  simp [prefix_take_iff, take_prefix]; omega

@[gcongr]

中文:
引理 take_isPrefix_take
  条件: {m n : 自然数}
  结论: l.take m <+: l.take n ↔ m <= n ∨ l.length <= n
  证明: by
  simp [prefix_take_iff, take_prefix]; omega

@[gcongr]
-/
@[simp] lemma take_isPrefix_take {m n : Nat} : l.take m <+: l.take n ↔ m <= n ∨ l.length <= n := by
  simp [prefix_take_iff, take_prefix]; omega

@[gcongr]
/--
theorem `IsPrefix.flatten` / 定理 `IsPrefix.flatten`

English:
theorem IsPrefix.flatten
  given: {l₁ l₂ : List (List α)} (h : l₁ <+: l₂)
  proof: by
  rcases h with ⟨l, rfl⟩
  simp

@[gcongr]

中文:
定理 IsPrefix.flatten
  条件: {l₁ l₂ : 列表 (列表 α)} (h : l₁ <+: l₂)
  证明: by
  rcases h with ⟨l, rfl⟩
  simp

@[gcongr]
-/
protected theorem IsPrefix.flatten {l₁ l₂ : List (List α)} (h : l₁ <+: l₂) :
    l₁.flatten <+: l₂.flatten := by
  rcases h with ⟨l, rfl⟩
  simp

@[gcongr]
/--
theorem `IsPrefix.flatMap` / 定理 `IsPrefix.flatMap`

English:
theorem IsPrefix.flatMap
  given: (h : l₁ <+: l₂) (f : α -> List β)
  proof: (h.map _).flatten

@[gcongr]

中文:
定理 IsPrefix.flatMap
  条件: (h : l₁ <+: l₂) (f : α -> 列表 β)
  证明: (h.map _).flatten

@[gcongr]
-/
protected theorem IsPrefix.flatMap (h : l₁ <+: l₂) (f : α -> List β) :
    l₁.flatMap f <+: l₂.flatMap f :=
  (h.map _).flatten

@[gcongr]
/--
theorem `IsSuffix.flatten` / 定理 `IsSuffix.flatten`

English:
theorem IsSuffix.flatten
  given: {l₁ l₂ : List (List α)} (h : l₁ <:+ l₂)
  proof: by
  rcases h with ⟨l, rfl⟩
  simp

@[gcongr]

中文:
定理 IsSuffix.flatten
  条件: {l₁ l₂ : 列表 (列表 α)} (h : l₁ <:+ l₂)
  证明: by
  rcases h with ⟨l, rfl⟩
  simp

@[gcongr]
-/
protected theorem IsSuffix.flatten {l₁ l₂ : List (List α)} (h : l₁ <:+ l₂) :
    l₁.flatten <:+ l₂.flatten := by
  rcases h with ⟨l, rfl⟩
  simp

@[gcongr]
/--
theorem `IsSuffix.flatMap` / 定理 `IsSuffix.flatMap`

English:
theorem IsSuffix.flatMap
  given: (h : l₁ <:+ l₂) (f : α -> List β)
  proof: (h.map _).flatten

@[gcongr]

中文:
定理 IsSuffix.flatMap
  条件: (h : l₁ <:+ l₂) (f : α -> 列表 β)
  证明: (h.map _).flatten

@[gcongr]
-/
protected theorem IsSuffix.flatMap (h : l₁ <:+ l₂) (f : α -> List β) :
    l₁.flatMap f <:+ l₂.flatMap f :=
  (h.map _).flatten

@[gcongr]
/--
theorem `IsInfix.flatten` / 定理 `IsInfix.flatten`

English:
theorem IsInfix.flatten
  given: {l₁ l₂ : List (List α)} (h : l₁ <:+: l₂)
  proof: by
  rcases h with ⟨l, l', rfl⟩
  simp

@[gcongr]

中文:
定理 IsInfix.flatten
  条件: {l₁ l₂ : 列表 (列表 α)} (h : l₁ <:+: l₂)
  证明: by
  rcases h with ⟨l, l', rfl⟩
  simp

@[gcongr]
-/
protected theorem IsInfix.flatten {l₁ l₂ : List (List α)} (h : l₁ <:+: l₂) :
    l₁.flatten <:+: l₂.flatten := by
  rcases h with ⟨l, l', rfl⟩
  simp

@[gcongr]
/--
theorem `IsInfix.flatMap` / 定理 `IsInfix.flatMap`

English:
theorem IsInfix.flatMap
  given: (h : l₁ <:+: l₂) (f : α -> List β)
  proof: (h.map _).flatten

中文:
定理 IsInfix.flatMap
  条件: (h : l₁ <:+: l₂) (f : α -> 列表 β)
  证明: (h.map _).flatten
-/
protected theorem IsInfix.flatMap (h : l₁ <:+: l₂) (f : α -> List β) :
    l₁.flatMap f <:+: l₂.flatMap f :=
  (h.map _).flatten

/--
lemma `dropSlice_sublist` / 引理 `dropSlice_sublist`

English:
lemma dropSlice_sublist
  given: (n m : Nat) (l : List α)
  statement: l.dropSlice n m <+ l
  proof: calc
    l.dropSlice n m = take n l ++ drop m (drop n l) := by rw [dropSlice_eq, drop_drop, Nat.add_comm]
  _ <+ take n l ++ drop n l := (Sublist.refl _).append (drop_sublist _ _)
  _ = _ := take_append_drop _ _

中文:
引理 dropSlice_sublist
  条件: (n m : 自然数) (l : 列表 α)
  结论: l.dropSlice n m <+ l
  证明: calc
    l.dropSlice n m = take n l ++ drop m (drop n l) := by rw [dropSlice_eq, drop_drop, Nat.add_comm]
  _ <+ take n l ++ drop n l := (Sublist.refl _).append (drop_sublist _ _)
  _ = _ := take_append_drop _ _

Depends on / 依赖: Nat.add_comm, Sublist, Sublist.refl, add_comm, append, dropSlice, dropSlice_eq, drop_drop, drop_sublist, l.dropSlice, take_append_drop
-/
lemma dropSlice_sublist (n m : Nat) (l : List α) : l.dropSlice n m <+ l :=
  calc
    l.dropSlice n m = take n l ++ drop m (drop n l) := by rw [dropSlice_eq, drop_drop, Nat.add_comm]
  _ <+ take n l ++ drop n l := (Sublist.refl _).append (drop_sublist _ _)
  _ = _ := take_append_drop _ _

/--
lemma `dropSlice_subset` / 引理 `dropSlice_subset`

English:
lemma dropSlice_subset
  given: (n m : Nat) (l : List α)
  statement: l.dropSlice n m subseteq l
  proof: (dropSlice_sublist n m l).subset

中文:
引理 dropSlice_subset
  条件: (n m : 自然数) (l : 列表 α)
  结论: l.dropSlice n m subseteq l
  证明: (dropSlice_sublist n m l).subset

Depends on / 依赖: dropSlice_sublist, subset
-/
lemma dropSlice_subset (n m : Nat) (l : List α) : l.dropSlice n m subseteq l :=
  (dropSlice_sublist n m l).subset

/--
lemma `mem_of_mem_dropSlice` / 引理 `mem_of_mem_dropSlice`

English:
lemma mem_of_mem_dropSlice
  given: {n m : Nat} {l : List α} {a : α} (h : a in l.dropSlice n m)
  statement: a in l
  proof: dropSlice_subset n m l h

中文:
引理 mem_of_mem_dropSlice
  条件: {n m : 自然数} {l : 列表 α} {a : α} (h : a in l.dropSlice n m)
  结论: a in l
  证明: dropSlice_subset n m l h

Depends on / 依赖: dropSlice_subset
-/
lemma mem_of_mem_dropSlice {n m : Nat} {l : List α} {a : α} (h : a in l.dropSlice n m) : a in l :=
  dropSlice_subset n m l h

/--
theorem `tail_subset` / 定理 `tail_subset`

English:
theorem tail_subset
  given: (l : List α)
  statement: tail l subseteq l
  proof: (tail_sublist l).subset

中文:
定理 tail_subset
  条件: (l : 列表 α)
  结论: tail l subseteq l
  证明: (tail_sublist l).subset

Depends on / 依赖: subset, tail_sublist
-/
theorem tail_subset (l : List α) : tail l subseteq l :=
  (tail_sublist l).subset

/--
theorem `mem_of_mem_dropLast` / 定理 `mem_of_mem_dropLast`

English:
theorem mem_of_mem_dropLast
  given: (h : a in l.dropLast)
  statement: a in l
  proof: dropLast_subset l h

中文:
定理 mem_of_mem_dropLast
  条件: (h : a in l.dropLast)
  结论: a in l
  证明: dropLast_subset l h

Depends on / 依赖: dropLast_subset
-/
theorem mem_of_mem_dropLast (h : a in l.dropLast) : a in l :=
  dropLast_subset l h

attribute [gcongr] Sublist.drop
attribute [refl] prefix_refl suffix_refl infix_refl

/--
theorem `concat_get_prefix` / 定理 `concat_get_prefix`

English:
theorem concat_get_prefix
  given: {x y : List α} (h : x <+: y) (hl : x.length < y.length)
  proof: by
  use y.drop (x.length + 1)
  nth_rw 1 [List.prefix_iff_eq_take.mp h]
  convert! List.take_append_drop (x.length + 1) y using 2
  rw [← List.take_concat_get]; rw [List.concat_eq_append]; rfl

中文:
定理 concat_get_prefix
  条件: {x y : 列表 α} (h : x <+: y) (hl : x.length < y.length)
  证明: by
  use y.drop (x.length + 1)
  nth_rw 1 [List.prefix_iff_eq_take.mp h]
  convert! List.take_append_drop (x.length + 1) y using 2
  rw [← List.take_concat_get]; rw [List.concat_eq_append]; rfl

Depends on / 依赖: List.concat_eq_append, List.prefix_iff_eq_take.mp, List.take_append_drop, List.take_concat_get, concat_eq_append, convert, length, nth_rw, prefix_iff_eq_take, take_append_drop, take_concat_get, x.length, y.drop
-/
theorem concat_get_prefix {x y : List α} (h : x <+: y) (hl : x.length < y.length) :
    x ++ [y.get ⟨x.length, hl⟩] <+: y := by
  use y.drop (x.length + 1)
  nth_rw 1 [List.prefix_iff_eq_take.mp h]
  convert! List.take_append_drop (x.length + 1) y using 2
  rw [← List.take_concat_get]; rw [List.concat_eq_append]; rfl

/--
theorem `prefix_append_drop` / 定理 `prefix_append_drop`

English:
theorem prefix_append_drop
  given: {l₁ l₂ : List α} (h : l₁ <+: l₂)
  proof: by
  induction l₂ generalizing l₁ with
  | nil => simp [List.prefix_nil.mp h]
  | cons _ _ ih =>
    cases l₁ with
    | nil => rfl
    | cons =>
      obtain ⟨rfl, h'⟩ := List.cons_prefix_cons.mp h
      simpa using ih h'

中文:
定理 prefix_append_drop
  条件: {l₁ l₂ : 列表 α} (h : l₁ <+: l₂)
  证明: by
  induction l₂ generalizing l₁ with
  | nil => simp [List.prefix_nil.mp h]
  | cons _ _ ih =>
    cases l₁ with
    | nil => rfl
    | cons =>
      obtain ⟨rfl, h'⟩ := List.cons_prefix_cons.mp h
      simpa using ih h'

Depends on / 依赖: List.cons_prefix_cons.mp, List.prefix_nil.mp, cons_prefix_cons, generalizing, prefix_nil
-/
theorem prefix_append_drop {l₁ l₂ : List α} (h : l₁ <+: l₂) :
    l₂ = l₁ ++ l₂.drop l₁.length := by
  induction l₂ generalizing l₁ with
  | nil => simp [List.prefix_nil.mp h]
  | cons _ _ ih =>
    cases l₁ with
    | nil => rfl
    | cons =>
      obtain ⟨rfl, h'⟩ := List.cons_prefix_cons.mp h
      simpa using ih h'

/--
Instance `decidableInfix` / 实例 `decidableInfix`

English:
instance decidableInfix
  signature: [DecidableEq α]
  body: l₁.decidableInfix l₂
    @decidable_of_decidable_of_iff (l₁ <+: b :: l₂ ∨ l₁ <:+: l₂) _ _
      infix_cons_iff.symm

中文:
实例 decidableInfix
  签名: [DecidableEq α]
  定义体: l₁.decidableInfix l₂
    @decidable_of_decidable_of_iff (l₁ <+: b :: l₂ ∨ l₁ <:+: l₂) _ _
      infix_cons_iff.symm

Depends on / 依赖: decidableInfix
-/
instance decidableInfix [DecidableEq α] : forall l₁ l₂ : List α, Decidable (l₁ <:+: l₂)
  | [], l₂ => isTrue ⟨[], l₂, rfl⟩
  | a :: l₁, [] => isFalse fun ⟨s, t, te⟩ => by simp at te
  | l₁, b :: l₂ =>
    letI := l₁.decidableInfix l₂
    @decidable_of_decidable_of_iff (l₁ <+: b :: l₂ ∨ l₁ <:+: l₂) _ _
      infix_cons_iff.symm

/--
theorem `IsPrefix.reduceOption` / 定理 `IsPrefix.reduceOption`

English:
theorem IsPrefix.reduceOption
  given: {l₁ l₂ : List (Option α)} (h : l₁ <+: l₂)
  proof: h.filterMap id

中文:
定理 IsPrefix.reduceOption
  条件: {l₁ l₂ : 列表 (选项类型 α)} (h : l₁ <+: l₂)
  证明: h.filterMap id
-/
protected theorem IsPrefix.reduceOption {l₁ l₂ : List (Option α)} (h : l₁ <+: l₂) :
    l₁.reduceOption <+: l₂.reduceOption :=
  h.filterMap id

/--
theorem `singleton_infix_iff` / 定理 `singleton_infix_iff`

English:
theorem singleton_infix_iff
  given: (x : α) (xs : List α)
  proof: by
  rw [List.mem_iff_append]; rw [List.IsInfix]
  congr! 4
  simp [eq_comm]

@[simp]

中文:
定理 singleton_infix_iff
  条件: (x : α) (xs : 列表 α)
  证明: by
  rw [List.mem_iff_append]; rw [List.IsInfix]
  congr! 4
  simp [eq_comm]

@[simp]

Depends on / 依赖: IsInfix, List.IsInfix, List.mem_iff_append, eq_comm, mem_iff_append
-/
theorem singleton_infix_iff (x : α) (xs : List α) :
    [x] <:+: xs ↔ x in xs := by
  rw [List.mem_iff_append]; rw [List.IsInfix]
  congr! 4
  simp [eq_comm]

@[simp]
/--
theorem `singleton_infix_singleton_iff` / 定理 `singleton_infix_singleton_iff`

English:
theorem singleton_infix_singleton_iff
  given: {x y : α}
  proof: by
  constructor
  · rintro ⟨_ | _, bs, h⟩ <;> simp_all
  · rintro rfl; rfl

中文:
定理 singleton_infix_singleton_iff
  条件: {x y : α}
  证明: by
  constructor
  · rintro ⟨_ | _, bs, h⟩ <;> simp_all
  · rintro rfl; rfl
-/
theorem singleton_infix_singleton_iff {x y : α} :
    [x] <:+: [y] ↔ x = y := by
  constructor
  · rintro ⟨_ | _, bs, h⟩ <;> simp_all
  · rintro rfl; rfl

/--
theorem `infix_singleton_iff` / 定理 `infix_singleton_iff`

English:
theorem infix_singleton_iff
  given: (xs : List α) (x : α)
  proof: by
  match xs with
  | [] => simp
  | [_] => simp [List.singleton_infix_singleton_iff]
  | _ :: _ :: _ =>
    constructor
    · rintro ⟨_ | _, _, h⟩ <;> simp at h
    · simp

中文:
定理 infix_singleton_iff
  条件: (xs : 列表 α) (x : α)
  证明: by
  match xs with
  | [] => simp
  | [_] => simp [List.singleton_infix_singleton_iff]
  | _ :: _ :: _ =>
    constructor
    · rintro ⟨_ | _, _, h⟩ <;> simp at h
    · simp

Depends on / 依赖: List.singleton_infix_singleton_iff, singleton_infix_singleton_iff
-/
theorem infix_singleton_iff (xs : List α) (x : α) :
    xs <:+: [x] ↔ xs = [] ∨ xs = [x] := by
  match xs with
  | [] => simp
  | [_] => simp [List.singleton_infix_singleton_iff]
  | _ :: _ :: _ =>
    constructor
    · rintro ⟨_ | _, _, h⟩ <;> simp at h
    · simp

/--
lemma `infix_antisymm` / 引理 `infix_antisymm`

English:
lemma infix_antisymm
  given: {l₁ l₂ : List α} (h₁ : l₁ <:+: l₂) (h₂ : l₂ <:+: l₁)
  proof: h₁.sublist.antisymm h₂.sublist

中文:
引理 infix_antisymm
  条件: {l₁ l₂ : 列表 α} (h₁ : l₁ <:+: l₂) (h₂ : l₂ <:+: l₁)
  证明: h₁.sublist.antisymm h₂.sublist

Depends on / 依赖: antisymm, sublist, sublist.antisymm
-/
lemma infix_antisymm {l₁ l₂ : List α} (h₁ : l₁ <:+: l₂) (h₂ : l₂ <:+: l₁) :
    l₁ = l₂ :=
  h₁.sublist.antisymm h₂.sublist

/--
theorem `IsPrefix.nodup` / 定理 `IsPrefix.nodup`

English:
theorem IsPrefix.nodup
  given: {l₁ l₂ : List α} (h : l₁ <+: l₂) (hn : l₂.Nodup)
  proof: hn.sublist h.sublist

中文:
定理 IsPrefix.nodup
  条件: {l₁ l₂ : 列表 α} (h : l₁ <+: l₂) (hn : l₂.Nodup)
  证明: hn.sublist h.sublist
-/
protected theorem IsPrefix.nodup {l₁ l₂ : List α} (h : l₁ <+: l₂) (hn : l₂.Nodup) :
    l₁.Nodup :=
  hn.sublist h.sublist

/--
theorem `IsInfix.nodup` / 定理 `IsInfix.nodup`

English:
theorem IsInfix.nodup
  given: {l₁ l₂ : List α} (h : l₁ <:+: l₂) (hn : l₂.Nodup)
  proof: hn.sublist h.sublist

中文:
定理 IsInfix.nodup
  条件: {l₁ l₂ : 列表 α} (h : l₁ <:+: l₂) (hn : l₂.Nodup)
  证明: hn.sublist h.sublist
-/
protected theorem IsInfix.nodup {l₁ l₂ : List α} (h : l₁ <:+: l₂) (hn : l₂.Nodup) :
    l₁.Nodup :=
  hn.sublist h.sublist

/--
theorem `IsSuffix.nodup` / 定理 `IsSuffix.nodup`

English:
theorem IsSuffix.nodup
  given: {l₁ l₂ : List α} (h : l₁ <:+ l₂) (hn : l₂.Nodup)
  proof: hn.sublist h.sublist

中文:
定理 IsSuffix.nodup
  条件: {l₁ l₂ : 列表 α} (h : l₁ <:+ l₂) (hn : l₂.Nodup)
  证明: hn.sublist h.sublist
-/
protected theorem IsSuffix.nodup {l₁ l₂ : List α} (h : l₁ <:+ l₂) (hn : l₂.Nodup) :
    l₁.Nodup :=
  hn.sublist h.sublist

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsPartialOrder (List α) (· <+: ·)
  body: prefix_rfl
  trans _ _ _ := IsPrefix.trans
antisymm _ _ h₁ h₂ := h₁.eq_of_length h₁.length_le.antisymm h₂.length_le

中文:
实例 :
  签名: 是偏序 (列表 α) (· <+: ·)
  定义体: prefix_rfl
  trans _ _ _ := IsPrefix.trans
antisymm _ _ h₁ h₂ := h₁.eq_of_length h₁.length_le.antisymm h₂.length_le

Depends on / 依赖: prefix_rfl
-/
instance : IsPartialOrder (List α) (· <+: ·) where
  refl _ := prefix_rfl
  trans _ _ _ := IsPrefix.trans
antisymm _ _ h₁ h₂ := h₁.eq_of_length h₁.length_le.antisymm h₂.length_le

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsPartialOrder (List α) (· <:+ ·)
  body: suffix_rfl
  trans _ _ _ := IsSuffix.trans
antisymm _ _ h₁ h₂ := h₁.eq_of_length h₁.length_le.antisymm h₂.length_le

中文:
实例 :
  签名: 是偏序 (列表 α) (· <:+ ·)
  定义体: suffix_rfl
  trans _ _ _ := IsSuffix.trans
antisymm _ _ h₁ h₂ := h₁.eq_of_length h₁.length_le.antisymm h₂.length_le

Depends on / 依赖: suffix_rfl
-/
instance : IsPartialOrder (List α) (· <:+ ·) where
  refl _ := suffix_rfl
  trans _ _ _ := IsSuffix.trans
antisymm _ _ h₁ h₂ := h₁.eq_of_length h₁.length_le.antisymm h₂.length_le

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsPartialOrder (List α) (· <:+: ·)
  body: infix_rfl
  trans _ _ _ := IsInfix.trans
antisymm _ _ h₁ h₂ := h₁.eq_of_length h₁.length_le.antisymm h₂.length_le

中文:
实例 :
  签名: 是偏序 (列表 α) (· <:+: ·)
  定义体: infix_rfl
  trans _ _ _ := IsInfix.trans
antisymm _ _ h₁ h₂ := h₁.eq_of_length h₁.length_le.antisymm h₂.length_le

Depends on / 依赖: infix_rfl
-/
instance : IsPartialOrder (List α) (· <:+: ·) where
  refl _ := infix_rfl
  trans _ _ _ := IsInfix.trans
antisymm _ _ h₁ h₂ := h₁.eq_of_length h₁.length_le.antisymm h₂.length_le

end Fix

section InitsTails

@[simp]
/--
theorem `mem_inits` / 定理 `mem_inits`

English:
theorem mem_inits
  statement: forall s t : List α, s in inits t ↔ s <+: t
  proof: (mem_inits _ _).1 hr
        rw [← hs]; rw [← ht]; exact ⟨s, rfl⟩,
      fun mi =>
      match s, mi with
      | [], ⟨_, rfl⟩ => Or.inl rfl
      | b :: s, ⟨r, hr⟩ =>
        (List.noConfusion rfl (heq_of_eq hr)) fun ba (st : s ++ r ≍ t) =>
Or.inr by rw [eq_of_heq ba]; exact ⟨_, (mem_inits _ _).2 ⟨_, eq_of_heq st⟩, rfl⟩⟩

@[simp]

中文:
定理 mem_inits
  结论: 对任意 s t : 列表 α, s in inits t ↔ s <+: t
  证明: (mem_inits _ _).1 hr
        rw [← hs]; rw [← ht]; exact ⟨s, rfl⟩,
      fun mi =>
      match s, mi with
      | [], ⟨_, rfl⟩ => Or.inl rfl
      | b :: s, ⟨r, hr⟩ =>
        (List.noConfusion rfl (heq_of_eq hr)) fun ba (st : s ++ r ≍ t) =>
Or.inr by rw [eq_of_heq ba]; exact ⟨_, (mem_inits _ _).2 ⟨_, eq_of_heq st⟩, rfl⟩⟩

@[simp]

Depends on / 依赖: mem_inits
-/
theorem mem_inits : forall s t : List α, s in inits t ↔ s <+: t
  | s, [] =>
    suffices s = nil ↔ s <+: nil by simpa only [inits, mem_singleton]
    ⟨fun h => h.symm ▸ prefix_rfl, eq_nil_of_prefix_nil⟩
  | s, a :: t =>
    suffices (s = nil ∨ exists l in inits t, a :: l = s) ↔ s <+: a :: t by simpa
    ⟨fun o =>
      match s, o with
      | _, Or.inl rfl => ⟨_, rfl⟩
      | s, Or.inr ⟨r, hr, hs⟩ => by
        let ⟨s, ht⟩ := (mem_inits _ _).1 hr
        rw [← hs]; rw [← ht]; exact ⟨s, rfl⟩,
      fun mi =>
      match s, mi with
      | [], ⟨_, rfl⟩ => Or.inl rfl
      | b :: s, ⟨r, hr⟩ =>
        (List.noConfusion rfl (heq_of_eq hr)) fun ba (st : s ++ r ≍ t) =>
Or.inr by rw [eq_of_heq ba]; exact ⟨_, (mem_inits _ _).2 ⟨_, eq_of_heq st⟩, rfl⟩⟩

@[simp]
/--
theorem `mem_tails` / 定理 `mem_tails`

English:
theorem mem_tails
  statement: forall s t : List α, s in tails t ↔ s <:+ t

中文:
定理 mem_tails
  结论: 对任意 s t : 列表 α, s in tails t ↔ s <:+ t
-/
theorem mem_tails : forall s t : List α, s in tails t ↔ s <:+ t
  | s, [] => by
    simp only [tails, mem_singleton, suffix_nil]
  | s, a :: t => by
    simp only [tails, mem_cons, mem_tails s t]
    exact
      show s = a :: t ∨ s <:+ t ↔ s <:+ a :: t from
        ⟨fun o =>
          match s, t, o with
          | _, t, Or.inl rfl => suffix_rfl
          | s, _, Or.inr ⟨l, rfl⟩ => ⟨a :: l, rfl⟩,
          fun e =>
          match s, t, e with
          | _, t, ⟨[], rfl⟩ => Or.inl rfl
          | s, t, ⟨b :: l, he⟩ =>
            List.noConfusion rfl (heq_of_eq he) fun _ lt => Or.inr ⟨l, eq_of_heq lt⟩⟩

/--
theorem `inits_cons` / 定理 `inits_cons`

English:
theorem inits_cons
  given: (a : α) (l : List α)
  statement: inits (a :: l) = [] :: l.inits.map fun t => a :: t
  proof: by
  simp

中文:
定理 inits_cons
  条件: (a : α) (l : 列表 α)
  结论: inits (a :: l) = [] :: l.inits.map fun t => a :: t
  证明: by
  simp
-/
theorem inits_cons (a : α) (l : List α) : inits (a :: l) = [] :: l.inits.map fun t => a :: t := by
  simp

/--
theorem `tails_cons` / 定理 `tails_cons`

English:
theorem tails_cons
  given: (a : α) (l : List α)
  statement: tails (a :: l) = (a :: l) :: l.tails
  proof: by simp

@[simp]

中文:
定理 tails_cons
  条件: (a : α) (l : 列表 α)
  结论: tails (a :: l) = (a :: l) :: l.tails
  证明: by simp

@[simp]
-/
theorem tails_cons (a : α) (l : List α) : tails (a :: l) = (a :: l) :: l.tails := by simp

@[simp]
/--
theorem `inits_append` / 定理 `inits_append`

English:
theorem inits_append
  statement: forall s t : List α, inits (s ++ t) = s.inits ++ t.inits.tail.map fun l => s ++ l

中文:
定理 inits_append
  结论: 对任意 s t : 列表 α, inits (s ++ t) = s.inits ++ t.inits.tail.map fun l => s ++ l
-/
theorem inits_append : forall s t : List α, inits (s ++ t) = s.inits ++ t.inits.tail.map fun l => s ++ l
  | [], [] => by simp
  | [], a :: t => by simp
  | a :: s, t => by simp [inits_append s t, Function.comp_def]

@[simp]
/--
theorem `tails_append` / 定理 `tails_append`

English:
theorem tails_append

中文:
定理 tails_append
-/
theorem tails_append :
    forall s t : List α, tails (s ++ t) = (s.tails.map fun l => l ++ t) ++ t.tails.tail
  | [], [] => by simp
  | [], a :: t => by simp
  | a :: s, t => by simp [tails_append s t]

-- the lemma names `inits_eq_tails` and `tails_eq_inits` are like `sublists_eq_sublists'`
/--
theorem `inits_eq_tails` / 定理 `inits_eq_tails`

English:
theorem inits_eq_tails
  statement: forall l : List α, l.inits = (reverse <| map reverse <| tails <| reverse l)

中文:
定理 inits_eq_tails
  结论: 对任意 l : 列表 α, l.inits = (reverse <| map reverse <| tails <| reverse l)
-/
theorem inits_eq_tails : forall l : List α, l.inits = (reverse <| map reverse <| tails <| reverse l)
  | [] => by simp
  | a :: l => by simp [inits_eq_tails l, map_inj_left, ← map_reverse]

/--
theorem `tails_eq_inits` / 定理 `tails_eq_inits`

English:
theorem tails_eq_inits
  statement: forall l : List α, l.tails = (reverse <| map reverse <| inits <| reverse l)

中文:
定理 tails_eq_inits
  结论: 对任意 l : 列表 α, l.tails = (reverse <| map reverse <| inits <| reverse l)
-/
theorem tails_eq_inits : forall l : List α, l.tails = (reverse <| map reverse <| inits <| reverse l)
  | [] => by simp
  | a :: l => by simp [tails_eq_inits l]

/--
theorem `inits_reverse` / 定理 `inits_reverse`

English:
theorem inits_reverse
  given: (l : List α)
  statement: inits (reverse l) = reverse (map reverse l.tails)
  proof: by
  rw [tails_eq_inits l]
  simp [← map_reverse]

中文:
定理 inits_reverse
  条件: (l : 列表 α)
  结论: inits (reverse l) = reverse (map reverse l.tails)
  证明: by
  rw [tails_eq_inits l]
  simp [← map_reverse]

Depends on / 依赖: map_reverse, tails_eq_inits
-/
theorem inits_reverse (l : List α) : inits (reverse l) = reverse (map reverse l.tails) := by
  rw [tails_eq_inits l]
  simp [← map_reverse]

/--
theorem `tails_reverse` / 定理 `tails_reverse`

English:
theorem tails_reverse
  given: (l : List α)
  statement: tails (reverse l) = reverse (map reverse l.inits)
  proof: by
  rw [inits_eq_tails l]
  simp [← map_reverse]

中文:
定理 tails_reverse
  条件: (l : 列表 α)
  结论: tails (reverse l) = reverse (map reverse l.inits)
  证明: by
  rw [inits_eq_tails l]
  simp [← map_reverse]

Depends on / 依赖: inits_eq_tails, map_reverse
-/
theorem tails_reverse (l : List α) : tails (reverse l) = reverse (map reverse l.inits) := by
  rw [inits_eq_tails l]
  simp [← map_reverse]

/--
theorem `map_reverse_inits` / 定理 `map_reverse_inits`

English:
theorem map_reverse_inits
  given: (l : List α)
  statement: map reverse l.inits = (reverse <| tails <| reverse l)
  proof: by
  rw [inits_eq_tails l]
  simp [← map_reverse]

中文:
定理 map_reverse_inits
  条件: (l : 列表 α)
  结论: map reverse l.inits = (reverse <| tails <| reverse l)
  证明: by
  rw [inits_eq_tails l]
  simp [← map_reverse]

Depends on / 依赖: inits_eq_tails, map_reverse
-/
theorem map_reverse_inits (l : List α) : map reverse l.inits = (reverse <| tails <| reverse l) := by
  rw [inits_eq_tails l]
  simp [← map_reverse]

/--
theorem `map_reverse_tails` / 定理 `map_reverse_tails`

English:
theorem map_reverse_tails
  given: (l : List α)
  statement: map reverse l.tails = (reverse <| inits <| reverse l)
  proof: by
  rw [tails_eq_inits l]
  simp [← map_reverse]

@[simp]

中文:
定理 map_reverse_tails
  条件: (l : 列表 α)
  结论: map reverse l.tails = (reverse <| inits <| reverse l)
  证明: by
  rw [tails_eq_inits l]
  simp [← map_reverse]

@[simp]

Depends on / 依赖: map_reverse, tails_eq_inits
-/
theorem map_reverse_tails (l : List α) : map reverse l.tails = (reverse <| inits <| reverse l) := by
  rw [tails_eq_inits l]
  simp [← map_reverse]

@[simp]
/--
theorem `length_tails` / 定理 `length_tails`

English:
theorem length_tails
  given: (l : List α)
  statement: length (tails l) = length l + 1
  proof: by
  induction l with
  | nil => simp
  | cons x l IH => simpa using IH

@[simp]

中文:
定理 length_tails
  条件: (l : 列表 α)
  结论: length (tails l) = length l + 1
  证明: by
  induction l with
  | nil => simp
  | cons x l IH => simpa using IH

@[simp]
-/
theorem length_tails (l : List α) : length (tails l) = length l + 1 := by
  induction l with
  | nil => simp
  | cons x l IH => simpa using IH

@[simp]
/--
theorem `length_inits` / 定理 `length_inits`

English:
theorem length_inits
  given: (l : List α)
  statement: length (inits l) = length l + 1
  proof: by simp [inits_eq_tails]

@[simp]

中文:
定理 length_inits
  条件: (l : 列表 α)
  结论: length (inits l) = length l + 1
  证明: by simp [inits_eq_tails]

@[simp]

Depends on / 依赖: inits_eq_tails
-/
theorem length_inits (l : List α) : length (inits l) = length l + 1 := by simp [inits_eq_tails]

@[simp]
/--
theorem `getElem_tails` / 定理 `getElem_tails`

English:
theorem getElem_tails
  given: (l : List α) (n : Nat) (h : n < (tails l).length)
  proof: by
  induction l generalizing n with
  | nil => simp
  | cons a l ihl =>
    cases n with
    | zero => simp
    | succ n => simp [ihl]

中文:
定理 getElem_tails
  条件: (l : 列表 α) (n : 自然数) (h : n < (tails l).length)
  证明: by
  induction l generalizing n with
  | nil => simp
  | cons a l ihl =>
    cases n with
    | zero => simp
    | succ n => simp [ihl]

Depends on / 依赖: generalizing
-/
theorem getElem_tails (l : List α) (n : Nat) (h : n < (tails l).length) :
    (tails l)[n] = l.drop n := by
  induction l generalizing n with
  | nil => simp
  | cons a l ihl =>
    cases n with
    | zero => simp
    | succ n => simp [ihl]

/--
theorem `get_tails` / 定理 `get_tails`

English:
theorem get_tails
  given: (l : List α) (n : Fin (length (tails l)))
  statement: (tails l).get n = l.drop n
  proof: by
  simp

@[simp]

中文:
定理 get_tails
  条件: (l : 列表 α) (n : 有限集 (length (tails l)))
  结论: (tails l).get n = l.drop n
  证明: by
  simp

@[simp]
-/
theorem get_tails (l : List α) (n : Fin (length (tails l))) : (tails l).get n = l.drop n := by
  simp

@[simp]
/--
theorem `getElem_inits` / 定理 `getElem_inits`

English:
theorem getElem_inits
  given: (l : List α) (n : Nat) (h : n < length (inits l))
  proof: by
  induction l generalizing n with
  | nil => simp
  | cons a l ihl =>
    cases n with
    | zero => simp
    | succ n => simp [ihl]

中文:
定理 getElem_inits
  条件: (l : 列表 α) (n : 自然数) (h : n < length (inits l))
  证明: by
  induction l generalizing n with
  | nil => simp
  | cons a l ihl =>
    cases n with
    | zero => simp
    | succ n => simp [ihl]

Depends on / 依赖: generalizing
-/
theorem getElem_inits (l : List α) (n : Nat) (h : n < length (inits l)) :
    (inits l)[n] = l.take n := by
  induction l generalizing n with
  | nil => simp
  | cons a l ihl =>
    cases n with
    | zero => simp
    | succ n => simp [ihl]

/--
theorem `get_inits` / 定理 `get_inits`

English:
theorem get_inits
  given: (l : List α) (n : Fin (length (inits l)))
  statement: (inits l).get n = l.take n
  proof: by
  simp

中文:
定理 get_inits
  条件: (l : 列表 α) (n : 有限集 (length (inits l)))
  结论: (inits l).get n = l.take n
  证明: by
  simp
-/
theorem get_inits (l : List α) (n : Fin (length (inits l))) : (inits l).get n = l.take n := by
  simp

/--
lemma `map_inits` / 引理 `map_inits`

English:
lemma map_inits
  given: {β : Type*} (g : α -> β)
  statement: (l.map g).inits = l.inits.map (map g)
  proof: by
  induction l using reverseRecOn <;> simp [*]

中文:
引理 map_inits
  条件: {β : 类型} (g : α -> β)
  结论: (l.map g).inits = l.inits.map (map g)
  证明: by
  induction l using reverseRecOn <;> simp [*]

Depends on / 依赖: reverseRecOn
-/
lemma map_inits {β : Type*} (g : α -> β) : (l.map g).inits = l.inits.map (map g) := by
  induction l using reverseRecOn <;> simp [*]

/--
lemma `map_tails` / 引理 `map_tails`

English:
lemma map_tails
  given: {β : Type*} (g : α -> β)
  statement: (l.map g).tails = l.tails.map (map g)
  proof: by
  induction l using reverseRecOn <;> simp [*]

中文:
引理 map_tails
  条件: {β : 类型} (g : α -> β)
  结论: (l.map g).tails = l.tails.map (map g)
  证明: by
  induction l using reverseRecOn <;> simp [*]

Depends on / 依赖: reverseRecOn
-/
lemma map_tails {β : Type*} (g : α -> β) : (l.map g).tails = l.tails.map (map g) := by
  induction l using reverseRecOn <;> simp [*]

/--
lemma `take_inits` / 引理 `take_inits`

English:
lemma take_inits
  given: {n}
  statement: (l.take n).inits = l.inits.take (n + 1)
  proof: by
  apply ext_getElem <;> (simp [take_take] <;> grind)

中文:
引理 take_inits
  条件: {n}
  结论: (l.take n).inits = l.inits.take (n + 1)
  证明: by
  apply ext_getElem <;> (simp [take_take] <;> grind)

Depends on / 依赖: ext_getElem, take_take
-/
lemma take_inits {n} : (l.take n).inits = l.inits.take (n + 1) := by
  apply ext_getElem <;> (simp [take_take] <;> grind)

end InitsTails

/-! ### insert -/


section Insert

variable [DecidableEq α]

/--
theorem `insert_eq_ite` / 定理 `insert_eq_ite`

English:
theorem insert_eq_ite
  given: (a : α) (l : List α)
  statement: insert a l = if a in l then l else a :: l
  proof: by
  simp only [← elem_iff]
  rfl

@[simp]

中文:
定理 insert_eq_ite
  条件: (a : α) (l : 列表 α)
  结论: insert a l = if a in l then l else a :: l
  证明: by
  simp only [← elem_iff]
  rfl

@[simp]

Depends on / 依赖: elem_iff
-/
theorem insert_eq_ite (a : α) (l : List α) : insert a l = if a in l then l else a :: l := by
  simp only [← elem_iff]
  rfl

@[simp]
/--
theorem `suffix_insert` / 定理 `suffix_insert`

English:
theorem suffix_insert
  given: (a : α) (l : List α)
  statement: l <:+ l.insert a
  proof: by
  by_cases h : a in l
  · simp only [insert_of_mem h, suffix_refl]
  · simp only [insert_of_not_mem h, suffix_cons]

中文:
定理 suffix_insert
  条件: (a : α) (l : 列表 α)
  结论: l <:+ l.insert a
  证明: by
  by_cases h : a in l
  · simp only [insert_of_mem h, suffix_refl]
  · simp only [insert_of_not_mem h, suffix_cons]

Depends on / 依赖: insert_of_mem, insert_of_not_mem, suffix_cons, suffix_refl
-/
theorem suffix_insert (a : α) (l : List α) : l <:+ l.insert a := by
  by_cases h : a in l
  · simp only [insert_of_mem h, suffix_refl]
  · simp only [insert_of_not_mem h, suffix_cons]

/--
theorem `infix_insert` / 定理 `infix_insert`

English:
theorem infix_insert
  given: (a : α) (l : List α)
  statement: l <:+: l.insert a
  proof: (suffix_insert a l).isInfix

中文:
定理 infix_insert
  条件: (a : α) (l : 列表 α)
  结论: l <:+: l.insert a
  证明: (suffix_insert a l).isInfix

Depends on / 依赖: isInfix, suffix_insert
-/
theorem infix_insert (a : α) (l : List α) : l <:+: l.insert a :=
  (suffix_insert a l).isInfix

/--
theorem `sublist_insert` / 定理 `sublist_insert`

English:
theorem sublist_insert
  given: (a : α) (l : List α)
  statement: l <+ l.insert a
  proof: (suffix_insert a l).sublist

中文:
定理 sublist_insert
  条件: (a : α) (l : 列表 α)
  结论: l <+ l.insert a
  证明: (suffix_insert a l).sublist

Depends on / 依赖: sublist, suffix_insert
-/
theorem sublist_insert (a : α) (l : List α) : l <+ l.insert a :=
  (suffix_insert a l).sublist

/--
theorem `subset_insert` / 定理 `subset_insert`

English:
theorem subset_insert
  given: (a : α) (l : List α)
  statement: l subseteq l.insert a
  proof: (sublist_insert a l).subset

中文:
定理 subset_insert
  条件: (a : α) (l : 列表 α)
  结论: l subseteq l.insert a
  证明: (sublist_insert a l).subset

Depends on / 依赖: sublist_insert, subset
-/
theorem subset_insert (a : α) (l : List α) : l subseteq l.insert a :=
  (sublist_insert a l).subset

end Insert

end List
