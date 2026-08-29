/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
module

public import Mathlib.Data.List.Defs
public import Mathlib.Data.List.Monad
public import Mathlib.Logic.OpClass
public import Mathlib.Logic.Unique
public import Mathlib.Tactic.Common
public import Batteries.Data.List.Lemmas
public import Batteries.Tactic.Lint.Simp
public import Batteries.Tactic.SeqFocus
public import Mathlib.Data.Subtype
public import Mathlib.Tactic.Attr.Core

/-!
# Basic properties of lists
-/

public section

assert_not_exists Lattice
assert_not_exists Monoid
assert_not_exists Preorder
assert_not_exists Prod.swap_eq_iff_eq_swap
assert_not_exists Set.range

open Function

open Nat hiding one_pos

namespace List

universe u v w

variable {ι : Type*} {α : Type u} {β : Type v} {γ : Type w} {l l₁ l₂ : List α}

/--
Instance `uniqueOfIsEmpty` / 实例 `uniqueOfIsEmpty`

English:
instance uniqueOfIsEmpty
  signature: [IsEmpty α]
  body: { instInhabitedList with
    uniq := fun l =>
      match l with
      | [] => rfl
      | a :: _ => isEmptyElim a }

中文:
实例 uniqueOfIsEmpty
  签名: [是空 α]
  定义体: { instInhabitedList with
    uniq := fun l =>
      match l with
      | [] => rfl
      | a :: _ => isEmptyElim a }

Depends on / 依赖: instInhabitedList, isEmptyElim
-/
instance uniqueOfIsEmpty [IsEmpty α] : Unique (List α) :=
  { instInhabitedList with
    uniq := fun l =>
      match l with
      | [] => rfl
      | a :: _ => isEmptyElim a }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Std.LawfulIdentity (α := List α) Append.append []
  body: nil_append
  right_id := append_nil

中文:
实例 :
  签名: Std.LawfulIdentity (α := 列表 α) Append.append []
  定义体: nil_append
  right_id := append_nil

Depends on / 依赖: Append, Append.append, append
-/
instance : Std.LawfulIdentity (α := List α) Append.append [] where
  left_id := nil_append
  right_id := append_nil

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Std.Associative (α := List α) Append.append
  body: append_assoc

中文:
实例 :
  签名: Std.结合 (α := 列表 α) Append.append
  定义体: append_assoc

Depends on / 依赖: Append, Append.append, append
-/
instance : Std.Associative (α := List α) Append.append where
  assoc := append_assoc

/--
theorem `cons_injective` / 定理 `cons_injective`

English:
theorem cons_injective
  given: {a : α}
  statement: Injective (cons a)
  proof: fun _ _ => tail_eq_of_cons_eq

中文:
定理 cons_injective
  条件: {a : α}
  结论: 单射 (cons a)
  证明: fun _ _ => tail_eq_of_cons_eq
-/
@[simp] theorem cons_injective {a : α} : Injective (cons a) := fun _ _ => tail_eq_of_cons_eq

/--
theorem `singleton_injective` / 定理 `singleton_injective`

English:
theorem singleton_injective
  statement: Injective fun a : α => [a]
  proof: fun _ _ h => (cons_eq_cons.1 h).1

中文:
定理 singleton_injective
  结论: 单射 fun a : α => [a]
  证明: fun _ _ h => (cons_eq_cons.1 h).1

Depends on / 依赖: cons_eq_cons
-/
theorem singleton_injective : Injective fun a : α => [a] := fun _ _ h => (cons_eq_cons.1 h).1

/--
theorem `setOfPred_mem_cons` / 定理 `setOfPred_mem_cons`

English:
theorem setOfPred_mem_cons
  given: (l : List α) (a : α)
  statement: { x | x in a :: l } = insert a { x | x in l }
  proof: Set.ext fun _ => mem_cons

@[deprecated (since := "2026-07-13")] alias set_of_mem_cons := setOfPred_mem_cons

中文:
定理 setOfPred_mem_cons
  条件: (l : 列表 α) (a : α)
  结论: { x | x in a :: l } = insert a { x | x in l }
  证明: Set.ext fun _ => mem_cons

@[deprecated (since := "2026-07-13")] alias set_of_mem_cons := setOfPred_mem_cons

Depends on / 依赖: Set.ext, mem_cons
-/
theorem setOfPred_mem_cons (l : List α) (a : α) : { x | x in a :: l } = insert a { x | x in l } :=
  Set.ext fun _ => mem_cons

@[deprecated (since := "2026-07-13")] alias set_of_mem_cons := setOfPred_mem_cons


/--
theorem `_root_.Decidable.List.eq_or_ne_mem_of_mem` / 定理 `_root_.Decidable.List.eq_or_ne_mem_of_mem`

English:
theorem _root_.Decidable.List.eq_or_ne_mem_of_mem
  statement: [DecidableEq α]
  proof: by
  by_cases hab : a = b
  · exact Or.inl hab
  · exact ((List.mem_cons.1 h).elim Or.inl (fun h => Or.inr ⟨hab, h⟩))

中文:
定理 _root_.可判定.列表.eq_or_ne_mem_of_mem
  结论: [DecidableEq α]
  证明: by
  by_cases hab : a = b
  · exact Or.inl hab
  · exact ((List.mem_cons.1 h).elim Or.inl (fun h => Or.inr ⟨hab, h⟩))

Depends on / 依赖: List.mem_cons, Or.inl, Or.inr, mem_cons
-/
theorem _root_.Decidable.List.eq_or_ne_mem_of_mem [DecidableEq α]
    {a b : α} {l : List α} (h : a in b :: l) : a = b ∨ a != b ∧ a in l := by
  by_cases hab : a = b
  · exact Or.inl hab
  · exact ((List.mem_cons.1 h).elim Or.inl (fun h => Or.inr ⟨hab, h⟩))

/--
lemma `mem_pair` / 引理 `mem_pair`

English:
lemma mem_pair
  given: {a b c : α}
  statement: a in [b, c] ↔ a = b ∨ a = c
  proof: by
  rw [mem_cons]; rw [mem_singleton]

@[simp 1100]

中文:
引理 mem_pair
  条件: {a b c : α}
  结论: a in [b, c] ↔ a = b ∨ a = c
  证明: by
  rw [mem_cons]; rw [mem_singleton]

@[simp 1100]

Depends on / 依赖: mem_cons, mem_singleton
-/
lemma mem_pair {a b c : α} : a in [b, c] ↔ a = b ∨ a = c := by
  rw [mem_cons]; rw [mem_singleton]

@[simp 1100]
/--
theorem `mem_map_of_injective` / 定理 `mem_map_of_injective`

English:
theorem mem_map_of_injective
  given: {f : α -> β} (H : Injective f) {a : α} {l : List α}
  proof: ⟨fun m => let ⟨_, m', e⟩ := exists_of_mem_map m; H e ▸ m', mem_map_of_mem⟩

@[simp]

中文:
定理 mem_map_of_injective
  条件: {f : α -> β} (H : 单射 f) {a : α} {l : 列表 α}
  证明: ⟨fun m => let ⟨_, m', e⟩ := exists_of_mem_map m; H e ▸ m', mem_map_of_mem⟩

@[simp]

Depends on / 依赖: exists_of_mem_map, mem_map_of_mem
-/
theorem mem_map_of_injective {f : α -> β} (H : Injective f) {a : α} {l : List α} :
    f a in map f l ↔ a in l :=
  ⟨fun m => let ⟨_, m', e⟩ := exists_of_mem_map m; H e ▸ m', mem_map_of_mem⟩

@[simp]
/--
theorem `_root_.Function.Involutive.exists_mem_and_apply_eq_iff` / 定理 `_root_.Function.Involutive.exists_mem_and_apply_eq_iff`

English:
theorem _root_.Function.Involutive.exists_mem_and_apply_eq_iff
  statement: {f : α -> α}
  proof: ⟨by rintro ⟨y, h, rfl⟩; rwa [hf y], fun h => ⟨f x, h, hf _⟩⟩

中文:
定理 _root_.函数.对合.存在_mem_and_apply_eq_iff
  结论: {f : α -> α}
  证明: ⟨by rintro ⟨y, h, rfl⟩; rwa [hf y], fun h => ⟨f x, h, hf _⟩⟩
-/
theorem _root_.Function.Involutive.exists_mem_and_apply_eq_iff {f : α -> α}
    (hf : Function.Involutive f) (x : α) (l : List α) : (exists y : α, y in l ∧ f y = x) ↔ f x in l :=
  ⟨by rintro ⟨y, h, rfl⟩; rwa [hf y], fun h => ⟨f x, h, hf _⟩⟩

/--
theorem `mem_map_of_involutive` / 定理 `mem_map_of_involutive`

English:
theorem mem_map_of_involutive
  given: {f : α -> α} (hf : Involutive f) {a : α} {l : List α}
  proof: by rw [mem_map, hf.exists_mem_and_apply_eq_iff]

中文:
定理 mem_map_of_involutive
  条件: {f : α -> α} (hf : 对合 f) {a : α} {l : 列表 α}
  证明: by rw [mem_map, hf.exists_mem_and_apply_eq_iff]

Depends on / 依赖: exists_mem_and_apply_eq_iff, hf.exists_mem_and_apply_eq_iff, mem_map
-/
theorem mem_map_of_involutive {f : α -> α} (hf : Involutive f) {a : α} {l : List α} :
    a in map f l ↔ f a in l := by rw [mem_map, hf.exists_mem_and_apply_eq_iff]

/-! ### length -/

alias ⟨_, length_pos_of_ne_nil⟩ := length_pos_iff

/--
theorem `length_pos_iff_ne_nil` / 定理 `length_pos_iff_ne_nil`

English:
theorem length_pos_iff_ne_nil
  given: {l : List α}
  statement: 0 < length l ↔ l != []
  proof: ⟨ne_nil_of_length_pos, length_pos_of_ne_nil⟩

中文:
定理 length_pos_iff_ne_nil
  条件: {l : 列表 α}
  结论: 0 < length l ↔ l != []
  证明: ⟨ne_nil_of_length_pos, length_pos_of_ne_nil⟩

Depends on / 依赖: length_pos_of_ne_nil, ne_nil_of_length_pos
-/
theorem length_pos_iff_ne_nil {l : List α} : 0 < length l ↔ l != [] :=
  ⟨ne_nil_of_length_pos, length_pos_of_ne_nil⟩

/--
theorem `exists_of_length_succ` / 定理 `exists_of_length_succ`

English:
theorem exists_of_length_succ
  given: {n}
  statement: forall l : List α, l.length = n + 1 -> exists h t, l = h :: t

中文:
定理 存在_of_length_succ
  条件: {n}
  结论: 对任意 l : 列表 α, l.length = n + 1 -> 存在 h t, l = h :: t
-/
theorem exists_of_length_succ {n} : forall l : List α, l.length = n + 1 -> exists h t, l = h :: t
| [], H => absurd H.symm succ_ne_zero n
  | h :: t, _ => ⟨h, t, rfl⟩

/--
theorem `length_eq_succ_iff` / 定理 `length_eq_succ_iff`

English:
theorem length_eq_succ_iff
  given: {n} {l : List α}
  proof: by
  grind [cases List]

中文:
定理 length_eq_succ_iff
  条件: {n} {l : 列表 α}
  证明: by
  grind [cases List]
-/
theorem length_eq_succ_iff {n} {l : List α} :
    l.length = n + 1 ↔ exists h t, h :: t = l ∧ t.length = n := by
  grind [cases List]

/--
lemma `length_injective_iff` / 引理 `length_injective_iff`

English:
lemma length_injective_iff
  statement: Injective (List.length : List α -> Nat) ↔ Subsingleton α
  proof: by
  constructor
  · intro h; refine ⟨fun x y => ?_⟩; (suffices [x] = [y] by simpa using this); apply h; rfl
  · intro hα l1 l2 hl
    induction l1 generalizing l2 <;> cases l2
    · rfl
    · cases hl
    · cases hl
    · next ih _ _ =>
      congr
      · subsingleton
      · apply ih; simpa using

中文:
引理 length_injective_iff
  结论: 单射 (列表.length : 列表 α -> 自然数) ↔ 子单例 α
  证明: by
  constructor
  · intro h; refine ⟨fun x y => ?_⟩; (suffices [x] = [y] by simpa using this); apply h; rfl
  · intro hα l1 l2 hl
    induction l1 generalizing l2 <;> cases l2
    · rfl
    · cases hl
    · cases hl
    · next ih _ _ =>
      congr
      · subsingleton
      · apply ih; simpa using
-/
@[simp] lemma length_injective_iff : Injective (List.length : List α -> Nat) ↔ Subsingleton α := by
  constructor
  · intro h; refine ⟨fun x y => ?_⟩; (suffices [x] = [y] by simpa using this); apply h; rfl
  · intro hα l1 l2 hl
    induction l1 generalizing l2 <;> cases l2
    · rfl
    · cases hl
    · cases hl
    · next ih _ _ =>
      congr
      · subsingleton
      · apply ih; simpa using hl

@[simp default + 1] -- Raise priority above `length_injective_iff`.
/--
lemma `length_injective` / 引理 `length_injective`

English:
lemma length_injective
  given: [Subsingleton α]
  statement: Injective (length : List α -> Nat)
  proof: length_injective_iff.mpr inferInstance

中文:
引理 length_injective
  条件: [子单例 α]
  结论: 单射 (length : 列表 α -> 自然数)
  证明: length_injective_iff.mpr inferInstance

Depends on / 依赖: length_injective_iff, length_injective_iff.mpr
-/
lemma length_injective [Subsingleton α] : Injective (length : List α -> Nat) :=
  length_injective_iff.mpr inferInstance

/--
theorem `length_eq_two` / 定理 `length_eq_two`

English:
theorem length_eq_two
  given: {l : List α}
  statement: l.length = 2 ↔ exists a b, l = [a, b]
  proof: ⟨fun _ => let [a, b] := l; ⟨a, b, rfl⟩, fun ⟨_, _, e⟩ => e ▸ rfl⟩

中文:
定理 length_eq_two
  条件: {l : 列表 α}
  结论: l.length = 2 ↔ 存在 a b, l = [a, b]
  证明: ⟨fun _ => let [a, b] := l; ⟨a, b, rfl⟩, fun ⟨_, _, e⟩ => e ▸ rfl⟩
-/
theorem length_eq_two {l : List α} : l.length = 2 ↔ exists a b, l = [a, b] :=
  ⟨fun _ => let [a, b] := l; ⟨a, b, rfl⟩, fun ⟨_, _, e⟩ => e ▸ rfl⟩

/--
theorem `length_eq_two'` / 定理 `length_eq_two'`

English:
theorem length_eq_two'
  given: {l : List α} (h : l != [])
  statement: l.length = 2 ↔ l = [l.head h, l.getLast h]
  proof: by
  rw [length_eq_two]; grind

中文:
定理 length_eq_two'
  条件: {l : 列表 α} (h : l != [])
  结论: l.length = 2 ↔ l = [l.head h, l.getLast h]
  证明: by
  rw [length_eq_two]; grind

Depends on / 依赖: length_eq_two
-/
theorem length_eq_two' {l : List α} (h : l != []) : l.length = 2 ↔ l = [l.head h, l.getLast h] := by
  rw [length_eq_two]; grind

/--
theorem `length_eq_three` / 定理 `length_eq_three`

English:
theorem length_eq_three
  given: {l : List α}
  statement: l.length = 3 ↔ exists a b c, l = [a, b, c]
  proof: ⟨fun _ => let [a, b, c] := l; ⟨a, b, c, rfl⟩, fun ⟨_, _, _, e⟩ => e ▸ rfl⟩

中文:
定理 length_eq_three
  条件: {l : 列表 α}
  结论: l.length = 3 ↔ 存在 a b c, l = [a, b, c]
  证明: ⟨fun _ => let [a, b, c] := l; ⟨a, b, c, rfl⟩, fun ⟨_, _, _, e⟩ => e ▸ rfl⟩
-/
theorem length_eq_three {l : List α} : l.length = 3 ↔ exists a b c, l = [a, b, c] :=
  ⟨fun _ => let [a, b, c] := l; ⟨a, b, c, rfl⟩, fun ⟨_, _, _, e⟩ => e ▸ rfl⟩

/--
theorem `length_eq_four` / 定理 `length_eq_four`

English:
theorem length_eq_four
  given: {l : List α}
  statement: l.length = 4 ↔ exists a b c d, l = [a, b, c, d]
  proof: ⟨fun _ => let [a, b, c, d] := l; ⟨a, b, c, d, rfl⟩, fun ⟨_, _, _, _, e⟩ => e ▸ rfl⟩

中文:
定理 length_eq_four
  条件: {l : 列表 α}
  结论: l.length = 4 ↔ 存在 a b c d, l = [a, b, c, d]
  证明: ⟨fun _ => let [a, b, c, d] := l; ⟨a, b, c, d, rfl⟩, fun ⟨_, _, _, _, e⟩ => e ▸ rfl⟩
-/
theorem length_eq_four {l : List α} : l.length = 4 ↔ exists a b c d, l = [a, b, c, d] :=
  ⟨fun _ => let [a, b, c, d] := l; ⟨a, b, c, d, rfl⟩, fun ⟨_, _, _, _, e⟩ => e ▸ rfl⟩


/--
Instance `instSingletonList` / 实例 `instSingletonList`

English:
instance instSingletonList
  signature: : Singleton α (List α)
  body: ⟨fun x => [x]⟩

中文:
实例 instSingletonList
  签名: : 单例 α (列表 α)
  定义体: ⟨fun x => [x]⟩
-/
instance instSingletonList : Singleton α (List α) := ⟨fun x => [x]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: α] : Insert α (List α)
  body: ⟨List.insert⟩

中文:
实例 [DecidableEq
  签名: α] : Insert α (列表 α)
  定义体: ⟨List.insert⟩

Depends on / 依赖: List.insert, insert
-/
instance [DecidableEq α] : Insert α (List α) := ⟨List.insert⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: α] : LawfulSingleton α (List α)
  body: { insert_empty_eq := fun x =>
      show (if x in ([] : List α) then [] else [x]) = [x] from if_neg not_mem_nil }

中文:
实例 [DecidableEq
  签名: α] : LawfulSingleton α (列表 α)
  定义体: { insert_empty_eq := fun x =>
      show (if x in ([] : List α) then [] else [x]) = [x] from if_neg not_mem_nil }

Depends on / 依赖: if_neg, insert_empty_eq, not_mem_nil
-/
instance [DecidableEq α] : LawfulSingleton α (List α) :=
  { insert_empty_eq := fun x =>
      show (if x in ([] : List α) then [] else [x]) = [x] from if_neg not_mem_nil }

/--
theorem `singleton_eq` / 定理 `singleton_eq`

English:
theorem singleton_eq
  given: (x : α)
  statement: ({x} : List α) = [x]
  proof: rfl

中文:
定理 singleton_eq
  条件: (x : α)
  结论: ({x} : 列表 α) = [x]
  证明: rfl
-/
theorem singleton_eq (x : α) : ({x} : List α) = [x] :=
  rfl

/--
theorem `insert_neg` / 定理 `insert_neg`

English:
theorem insert_neg
  given: [DecidableEq α] {x : α} {l : List α} (h : x ∉ l)
  proof: insert_of_not_mem h

中文:
定理 insert_neg
  条件: [DecidableEq α] {x : α} {l : 列表 α} (h : x ∉ l)
  证明: insert_of_not_mem h

Depends on / 依赖: insert_of_not_mem
-/
theorem insert_neg [DecidableEq α] {x : α} {l : List α} (h : x ∉ l) :
    Insert.insert x l = x :: l :=
  insert_of_not_mem h

/--
theorem `insert_pos` / 定理 `insert_pos`

English:
theorem insert_pos
  given: [DecidableEq α] {x : α} {l : List α} (h : x in l)
  statement: Insert.insert x l = l
  proof: insert_of_mem h

中文:
定理 insert_pos
  条件: [DecidableEq α] {x : α} {l : 列表 α} (h : x in l)
  结论: Insert.insert x l = l
  证明: insert_of_mem h

Depends on / 依赖: insert_of_mem
-/
theorem insert_pos [DecidableEq α] {x : α} {l : List α} (h : x in l) : Insert.insert x l = l :=
  insert_of_mem h

/--
theorem `doubleton_eq` / 定理 `doubleton_eq`

English:
theorem doubleton_eq
  given: [DecidableEq α] {x y : α} (h : x != y)
  statement: ({x, y} : List α) = [x, y]
  proof: by
  rw [insert_neg]; rw [singleton_eq]
  rwa [singleton_eq, mem_singleton]

中文:
定理 doubleton_eq
  条件: [DecidableEq α] {x y : α} (h : x != y)
  结论: ({x, y} : 列表 α) = [x, y]
  证明: by
  rw [insert_neg]; rw [singleton_eq]
  rwa [singleton_eq, mem_singleton]

Depends on / 依赖: insert_neg, mem_singleton, singleton_eq
-/
theorem doubleton_eq [DecidableEq α] {x y : α} (h : x != y) : ({x, y} : List α) = [x, y] := by
  rw [insert_neg]; rw [singleton_eq]
  rwa [singleton_eq, mem_singleton]


/--
theorem `forall_mem_of_forall_mem_cons` / 定理 `forall_mem_of_forall_mem_cons`

English:
theorem forall_mem_of_forall_mem_cons
  given: {p : α -> Prop} {a : α} {l : List α} (h : forall x in a :: l, p x)
  proof: (forall_mem_cons.1 h).2

中文:
定理 对任意_mem_of_对任意_mem_cons
  条件: {p : α -> 命题} {a : α} {l : 列表 α} (h : 对任意 x in a :: l, p x)
  证明: (forall_mem_cons.1 h).2

Depends on / 依赖: forall_mem_cons
-/
theorem forall_mem_of_forall_mem_cons {p : α -> Prop} {a : α} {l : List α} (h : forall x in a :: l, p x) :
    forall x in l, p x := (forall_mem_cons.1 h).2

/--
theorem `exists_mem_cons_of` / 定理 `exists_mem_cons_of`

English:
theorem exists_mem_cons_of
  given: {p : α -> Prop} {a : α} (l : List α) (h : p a)
  statement: exists x in a :: l, p x
  proof: ⟨a, mem_cons_self, h⟩

中文:
定理 存在_mem_cons_of
  条件: {p : α -> 命题} {a : α} (l : 列表 α) (h : p a)
  结论: 存在 x in a :: l, p x
  证明: ⟨a, mem_cons_self, h⟩

Depends on / 依赖: mem_cons_self
-/
theorem exists_mem_cons_of {p : α -> Prop} {a : α} (l : List α) (h : p a) : exists x in a :: l, p x :=
  ⟨a, mem_cons_self, h⟩

/--
theorem `exists_mem_cons_of_exists` / 定理 `exists_mem_cons_of_exists`

English:
theorem exists_mem_cons_of_exists
  given: {p : α -> Prop} {a : α} {l : List α}
  statement: (exists x in l, p x) ->
  proof: fun ⟨x, xl, px⟩ => ⟨x, mem_cons_of_mem _ xl, px⟩

中文:
定理 存在_mem_cons_of_存在
  条件: {p : α -> 命题} {a : α} {l : 列表 α}
  结论: (存在 x in l, p x) ->
  证明: fun ⟨x, xl, px⟩ => ⟨x, mem_cons_of_mem _ xl, px⟩

Depends on / 依赖: mem_cons_of_mem
-/
theorem exists_mem_cons_of_exists {p : α -> Prop} {a : α} {l : List α} : (exists x in l, p x) ->
    exists x in a :: l, p x :=
  fun ⟨x, xl, px⟩ => ⟨x, mem_cons_of_mem _ xl, px⟩

/--
theorem `or_exists_of_exists_mem_cons` / 定理 `or_exists_of_exists_mem_cons`

English:
theorem or_exists_of_exists_mem_cons
  given: {p : α -> Prop} {a : α} {l : List α}
  statement: (exists x in a :: l, p x) ->
  proof: by grind

中文:
定理 or_存在_of_存在_mem_cons
  条件: {p : α -> 命题} {a : α} {l : 列表 α}
  结论: (存在 x in a :: l, p x) ->
  证明: by grind
-/
theorem or_exists_of_exists_mem_cons {p : α -> Prop} {a : α} {l : List α} : (exists x in a :: l, p x) ->
    p a ∨ exists x in l, p x := by grind

/--
theorem `exists_mem_cons_iff` / 定理 `exists_mem_cons_iff`

English:
theorem exists_mem_cons_iff
  given: (p : α -> Prop) (a : α) (l : List α)
  proof: by grind

中文:
定理 存在_mem_cons_iff
  条件: (p : α -> 命题) (a : α) (l : 列表 α)
  证明: by grind
-/
theorem exists_mem_cons_iff (p : α -> Prop) (a : α) (l : List α) :
    (exists x in a :: l, p x) ↔ p a ∨ exists x in l, p x := by grind


/--
theorem `cons_subset_of_subset_of_mem` / 定理 `cons_subset_of_subset_of_mem`

English:
theorem cons_subset_of_subset_of_mem
  statement: {a : α} {l m : List α}
  proof: cons_subset.2 ⟨ainm, lsubm⟩

中文:
定理 cons_subset_of_subset_of_mem
  结论: {a : α} {l m : 列表 α}
  证明: cons_subset.2 ⟨ainm, lsubm⟩

Depends on / 依赖: cons_subset
-/
theorem cons_subset_of_subset_of_mem {a : α} {l m : List α}
    (ainm : a in m) (lsubm : l subseteq m) : a::l subseteq m :=
  cons_subset.2 ⟨ainm, lsubm⟩

/--
theorem `append_subset_of_subset_of_subset` / 定理 `append_subset_of_subset_of_subset`

English:
theorem append_subset_of_subset_of_subset
  given: {l₁ l₂ l : List α} (l₁subl : l₁ subseteq l) (l₂subl : l₂ subseteq l)
  proof: fun _ h => (mem_append.1 h).elim (@l₁subl _) (@l₂subl _)

中文:
定理 append_subset_of_subset_of_subset
  条件: {l₁ l₂ l : 列表 α} (l₁subl : l₁ subseteq l) (l₂subl : l₂ subseteq l)
  证明: fun _ h => (mem_append.1 h).elim (@l₁subl _) (@l₂subl _)

Depends on / 依赖: mem_append
-/
theorem append_subset_of_subset_of_subset {l₁ l₂ l : List α} (l₁subl : l₁ subseteq l) (l₂subl : l₂ subseteq l) :
    l₁ ++ l₂ subseteq l :=
  fun _ h => (mem_append.1 h).elim (@l₁subl _) (@l₂subl _)

/--
theorem `map_subset_iff` / 定理 `map_subset_iff`

English:
theorem map_subset_iff
  given: {l₁ l₂ : List α} (f : α -> β) (h : Injective f)
  proof: by
  refine ⟨?_, map_subset f⟩; intro h2 x hx
  rcases mem_map.1 (h2 (mem_map_of_mem hx)) with ⟨x', hx', hxx'⟩
  cases h hxx'; exact hx'

中文:
定理 map_subset_iff
  条件: {l₁ l₂ : 列表 α} (f : α -> β) (h : 单射 f)
  证明: by
  refine ⟨?_, map_subset f⟩; intro h2 x hx
  rcases mem_map.1 (h2 (mem_map_of_mem hx)) with ⟨x', hx', hxx'⟩
  cases h hxx'; exact hx'

Depends on / 依赖: map_subset, mem_map, mem_map_of_mem
-/
theorem map_subset_iff {l₁ l₂ : List α} (f : α -> β) (h : Injective f) :
    map f l₁ subseteq map f l₂ ↔ l₁ subseteq l₂ := by
  refine ⟨?_, map_subset f⟩; intro h2 x hx
  rcases mem_map.1 (h2 (mem_map_of_mem hx)) with ⟨x', hx', hxx'⟩
  cases h hxx'; exact hx'

/--
lemma `notMem_of_subset` / 引理 `notMem_of_subset`

English:
lemma notMem_of_subset
  given: (h : l subseteq l₁) {a : α} (ha : a ∉ l₁)
  statement: a ∉ l
  proof: (ha <| h ·)

中文:
引理 notMem_of_subset
  条件: (h : l subseteq l₁) {a : α} (ha : a ∉ l₁)
  结论: a ∉ l
  证明: (ha <| h ·)
-/
lemma notMem_of_subset (h : l subseteq l₁) {a : α} (ha : a ∉ l₁) : a ∉ l := (ha <| h ·)


/--
theorem `append_eq_has_append` / 定理 `append_eq_has_append`

English:
theorem append_eq_has_append
  given: {L₁ L₂ : List α}
  statement: List.append L₁ L₂ = L₁ ++ L₂
  proof: rfl

中文:
定理 append_eq_has_append
  条件: {L₁ L₂ : 列表 α}
  结论: 列表.append L₁ L₂ = L₁ ++ L₂
  证明: rfl
-/
theorem append_eq_has_append {L₁ L₂ : List α} : List.append L₁ L₂ = L₁ ++ L₂ :=
  rfl

/--
theorem `append_right_injective` / 定理 `append_right_injective`

English:
theorem append_right_injective
  given: (s : List α)
  statement: Injective fun t => s ++ t
  proof: fun _ _ => append_cancel_left

中文:
定理 append_right_injective
  条件: (s : 列表 α)
  结论: 单射 fun t => s ++ t
  证明: fun _ _ => append_cancel_left

Depends on / 依赖: append_cancel_left
-/
theorem append_right_injective (s : List α) : Injective fun t => s ++ t :=
  fun _ _ => append_cancel_left

/--
theorem `append_left_injective` / 定理 `append_left_injective`

English:
theorem append_left_injective
  given: (t : List α)
  statement: Injective fun s => s ++ t
  proof: fun _ _ => append_cancel_right

中文:
定理 append_left_injective
  条件: (t : 列表 α)
  结论: 单射 fun s => s ++ t
  证明: fun _ _ => append_cancel_right

Depends on / 依赖: append_cancel_right
-/
theorem append_left_injective (t : List α) : Injective fun s => s ++ t :=
  fun _ _ => append_cancel_right


/--
theorem `eq_replicate_length` / 定理 `eq_replicate_length`

English:
theorem eq_replicate_length
  given: {a : α}
  statement: forall {l : List α}, l = replicate l.length a ↔ forall b in l, b = a

中文:
定理 eq_replicate_length
  条件: {a : α}
  结论: 对任意 {l : 列表 α}, l = replicate l.length a ↔ 对任意 b in l, b = a
-/
theorem eq_replicate_length {a : α} : forall {l : List α}, l = replicate l.length a ↔ forall b in l, b = a
  | [] => by simp
  | (b :: l) => by simp [eq_replicate_length, replicate_succ]

/--
theorem `replicate_add` / 定理 `replicate_add`

English:
theorem replicate_add
  given: (m n) (a : α)
  statement: replicate (m + n) a = replicate m a ++ replicate n a
  proof: by
  rw [replicate_append_replicate]

中文:
定理 replicate_add
  条件: (m n) (a : α)
  结论: replicate (m + n) a = replicate m a ++ replicate n a
  证明: by
  rw [replicate_append_replicate]

Depends on / 依赖: replicate_append_replicate
-/
theorem replicate_add (m n) (a : α) : replicate (m + n) a = replicate m a ++ replicate n a := by
  rw [replicate_append_replicate]

/--
theorem `replicate_subset_singleton` / 定理 `replicate_subset_singleton`

English:
theorem replicate_subset_singleton
  given: (n) (a : α)
  statement: replicate n a subseteq [a]
  proof: fun _ h =>
  mem_singleton.2 (eq_of_mem_replicate h)

中文:
定理 replicate_subset_singleton
  条件: (n) (a : α)
  结论: replicate n a subseteq [a]
  证明: fun _ h =>
  mem_singleton.2 (eq_of_mem_replicate h)
-/
theorem replicate_subset_singleton (n) (a : α) : replicate n a subseteq [a] := fun _ h =>
  mem_singleton.2 (eq_of_mem_replicate h)

/--
theorem `subset_singleton_iff` / 定理 `subset_singleton_iff`

English:
theorem subset_singleton_iff
  given: {a : α} {L : List α}
  statement: L subseteq [a] ↔ exists n, L = replicate n a
  proof: by
  simp only [eq_replicate_iff, subset_def, mem_singleton, exists_eq_left']

中文:
定理 subset_singleton_iff
  条件: {a : α} {L : 列表 α}
  结论: L subseteq [a] ↔ 存在 n, L = replicate n a
  证明: by
  simp only [eq_replicate_iff, subset_def, mem_singleton, exists_eq_left']

Depends on / 依赖: eq_replicate_iff, exists_eq_left, mem_singleton, subset_def
-/
theorem subset_singleton_iff {a : α} {L : List α} : L subseteq [a] ↔ exists n, L = replicate n a := by
  simp only [eq_replicate_iff, subset_def, mem_singleton, exists_eq_left']

/--
theorem `replicate_right_injective` / 定理 `replicate_right_injective`

English:
theorem replicate_right_injective
  given: {n : Nat} (hn : n != 0)
  statement: Injective (@replicate α n)
  proof: fun _ _ h => (eq_replicate_iff.1 h).2 _ mem_replicate.2 ⟨hn, rfl⟩

中文:
定理 replicate_right_injective
  条件: {n : 自然数} (hn : n != 0)
  结论: 单射 (@replicate α n)
  证明: fun _ _ h => (eq_replicate_iff.1 h).2 _ mem_replicate.2 ⟨hn, rfl⟩

Depends on / 依赖: eq_replicate_iff, mem_replicate
-/
theorem replicate_right_injective {n : Nat} (hn : n != 0) : Injective (@replicate α n) :=
fun _ _ h => (eq_replicate_iff.1 h).2 _ mem_replicate.2 ⟨hn, rfl⟩

/--
theorem `replicate_right_inj` / 定理 `replicate_right_inj`

English:
theorem replicate_right_inj
  given: {a b : α} {n : Nat} (hn : n != 0)
  proof: (replicate_right_injective hn).eq_iff

中文:
定理 replicate_right_inj
  条件: {a b : α} {n : 自然数} (hn : n != 0)
  证明: (replicate_right_injective hn).eq_iff

Depends on / 依赖: eq_iff, replicate_right_injective
-/
theorem replicate_right_inj {a b : α} {n : Nat} (hn : n != 0) :
    replicate n a = replicate n b ↔ a = b :=
  (replicate_right_injective hn).eq_iff

/--
theorem `replicate_right_inj'` / 定理 `replicate_right_inj'`

English:
theorem replicate_right_inj'
  given: {a b : α}
  statement: forall {n},

中文:
定理 replicate_right_inj'
  条件: {a b : α}
  结论: 对任意 {n},
-/
theorem replicate_right_inj' {a b : α} : forall {n},
    replicate n a = replicate n b ↔ n = 0 ∨ a = b
  | 0 => by simp
| n + 1 => (replicate_right_inj n.succ_ne_zero).trans by simp only [n.succ_ne_zero, false_or]

/--
theorem `replicate_left_injective` / 定理 `replicate_left_injective`

English:
theorem replicate_left_injective
  given: (a : α)
  statement: Injective (replicate · a)
  proof: LeftInverse.injective (length_replicate (n := ·))

中文:
定理 replicate_left_injective
  条件: (a : α)
  结论: 单射 (replicate · a)
  证明: LeftInverse.injective (length_replicate (n := ·))

Depends on / 依赖: LeftInverse, LeftInverse.injective, injective, length_replicate
-/
theorem replicate_left_injective (a : α) : Injective (replicate · a) :=
  LeftInverse.injective (length_replicate (n := ·))

/--
theorem `replicate_left_inj` / 定理 `replicate_left_inj`

English:
theorem replicate_left_inj
  given: {a : α} {n m : Nat}
  statement: replicate n a = replicate m a ↔ n = m
  proof: (replicate_left_injective a).eq_iff

@[simp]

中文:
定理 replicate_left_inj
  条件: {a : α} {n m : 自然数}
  结论: replicate n a = replicate m a ↔ n = m
  证明: (replicate_left_injective a).eq_iff

@[simp]

Depends on / 依赖: eq_iff, replicate_left_injective
-/
theorem replicate_left_inj {a : α} {n m : Nat} : replicate n a = replicate m a ↔ n = m :=
  (replicate_left_injective a).eq_iff

@[simp]
/--
theorem `head?_flatten_replicate` / 定理 `head?_flatten_replicate`

English:
theorem head?_flatten_replicate
  given: {n : Nat} (h : n != 0) (l : List α)
  proof: by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h
  induction l <;> simp [replicate]

@[simp]

中文:
定理 head?_flatten_replicate
  条件: {n : 自然数} (h : n != 0) (l : 列表 α)
  证明: by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h
  induction l <;> simp [replicate]

@[simp]

Depends on / 依赖: Nat.exists_eq_succ_of_ne_zero, exists_eq_succ_of_ne_zero, replicate
-/
theorem head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
    (List.replicate n l).flatten.head? = l.head? := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h
  induction l <;> simp [replicate]

@[simp]
/--
theorem `getLast?_flatten_replicate` / 定理 `getLast?_flatten_replicate`

English:
theorem getLast?_flatten_replicate
  given: {n : Nat} (h : n != 0) (l : List α)
  proof: by
  rw [← List.head?_reverse]; rw [← List.head?_reverse]; rw [List.reverse_flatten]; rw [List.map_replicate]; rw [List.reverse_replicate]; rw [head?_flatten_replicate h]

中文:
定理 getLast?_flatten_replicate
  条件: {n : 自然数} (h : n != 0) (l : 列表 α)
  证明: by
  rw [← List.head?_reverse]; rw [← List.head?_reverse]; rw [List.reverse_flatten]; rw [List.map_replicate]; rw [List.reverse_replicate]; rw [head?_flatten_replicate h]

Depends on / 依赖: List.head, List.map_replicate, List.reverse_flatten, List.reverse_replicate, _flatten_replicate, _reverse, map_replicate, reverse_flatten, reverse_replicate
-/
theorem getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
    (List.replicate n l).flatten.getLast? = l.getLast? := by
  rw [← List.head?_reverse]; rw [← List.head?_reverse]; rw [List.reverse_flatten]; rw [List.map_replicate]; rw [List.reverse_replicate]; rw [head?_flatten_replicate h]


/--
theorem `mem_pure` / 定理 `mem_pure`

English:
theorem mem_pure
  given: (x y : α)
  statement: x in (pure y : List α) ↔ x = y
  proof: by simp

中文:
定理 mem_pure
  条件: (x y : α)
  结论: x in (pure y : 列表 α) ↔ x = y
  证明: by simp
-/
theorem mem_pure (x y : α) : x in (pure y : List α) ↔ x = y := by simp

/-! ### bind -/

@[simp]
/--
theorem `bind_eq_flatMap` / 定理 `bind_eq_flatMap`

English:
theorem bind_eq_flatMap
  given: {α β} (f : α -> List β) (l : List α)
  statement: l >>= f = l.flatMap f
  proof: rfl

中文:
定理 bind_eq_flatMap
  条件: {α β} (f : α -> 列表 β) (l : 列表 α)
  结论: l >>= f = l.flatMap f
  证明: rfl
-/
theorem bind_eq_flatMap {α β} (f : α -> List β) (l : List α) : l >>= f = l.flatMap f :=
  rfl

/-! ### concat -/


/--
theorem `reverse_cons'` / 定理 `reverse_cons'`

English:
theorem reverse_cons'
  given: (a : α) (l : List α)
  statement: reverse (a :: l) = concat (reverse l) a
  proof: by
  simp only [reverse_cons, concat_eq_append]

中文:
定理 reverse_cons'
  条件: (a : α) (l : 列表 α)
  结论: reverse (a :: l) = concat (reverse l) a
  证明: by
  simp only [reverse_cons, concat_eq_append]

Depends on / 依赖: concat_eq_append, reverse_cons
-/
theorem reverse_cons' (a : α) (l : List α) : reverse (a :: l) = concat (reverse l) a := by
  simp only [reverse_cons, concat_eq_append]

/--
theorem `reverse_concat'` / 定理 `reverse_concat'`

English:
theorem reverse_concat'
  given: (l : List α) (a : α)
  statement: (l ++ [a]).reverse = a :: l.reverse
  proof: by
  rw [reverse_append]; rfl

@[simp]

中文:
定理 reverse_concat'
  条件: (l : 列表 α) (a : α)
  结论: (l ++ [a]).reverse = a :: l.reverse
  证明: by
  rw [reverse_append]; rfl

@[simp]

Depends on / 依赖: reverse_append
-/
theorem reverse_concat' (l : List α) (a : α) : (l ++ [a]).reverse = a :: l.reverse := by
  rw [reverse_append]; rfl

@[simp]
/--
theorem `reverse_involutive` / 定理 `reverse_involutive`

English:
theorem reverse_involutive
  statement: Involutive (@reverse α)
  proof: reverse_reverse

@[simp]

中文:
定理 reverse_involutive
  结论: 对合 (@reverse α)
  证明: reverse_reverse

@[simp]

Depends on / 依赖: reverse_reverse
-/
theorem reverse_involutive : Involutive (@reverse α) :=
  reverse_reverse

@[simp]
/--
theorem `reverse_injective` / 定理 `reverse_injective`

English:
theorem reverse_injective
  statement: Injective (@reverse α)
  proof: reverse_involutive.injective

中文:
定理 reverse_injective
  结论: 单射 (@reverse α)
  证明: reverse_involutive.injective

Depends on / 依赖: injective, reverse_involutive, reverse_involutive.injective
-/
theorem reverse_injective : Injective (@reverse α) :=
  reverse_involutive.injective

/--
theorem `reverse_surjective` / 定理 `reverse_surjective`

English:
theorem reverse_surjective
  statement: Surjective (@reverse α)
  proof: reverse_involutive.surjective

中文:
定理 reverse_surjective
  结论: 满射 (@reverse α)
  证明: reverse_involutive.surjective

Depends on / 依赖: reverse_involutive, reverse_involutive.surjective, surjective
-/
theorem reverse_surjective : Surjective (@reverse α) :=
  reverse_involutive.surjective

/--
theorem `reverse_bijective` / 定理 `reverse_bijective`

English:
theorem reverse_bijective
  statement: Bijective (@reverse α)
  proof: reverse_involutive.bijective

中文:
定理 reverse_bijective
  结论: 双射 (@reverse α)
  证明: reverse_involutive.bijective

Depends on / 依赖: bijective, reverse_involutive, reverse_involutive.bijective
-/
theorem reverse_bijective : Bijective (@reverse α) :=
  reverse_involutive.bijective

/--
theorem `concat_eq_reverse_cons` / 定理 `concat_eq_reverse_cons`

English:
theorem concat_eq_reverse_cons
  given: (a : α) (l : List α)
  statement: concat l a = reverse (a :: reverse l)
  proof: by
  grind

中文:
定理 concat_eq_reverse_cons
  条件: (a : α) (l : 列表 α)
  结论: concat l a = reverse (a :: reverse l)
  证明: by
  grind
-/
theorem concat_eq_reverse_cons (a : α) (l : List α) : concat l a = reverse (a :: reverse l) := by
  grind

/--
theorem `map_reverseAux` / 定理 `map_reverseAux`

English:
theorem map_reverseAux
  given: (f : α -> β) (l₁ l₂ : List α)
  proof: by
  simp only [reverseAux_eq, map_append, map_reverse]

中文:
定理 map_reverseAux
  条件: (f : α -> β) (l₁ l₂ : 列表 α)
  证明: by
  simp only [reverseAux_eq, map_append, map_reverse]

Depends on / 依赖: map_append, map_reverse, reverseAux_eq
-/
theorem map_reverseAux (f : α -> β) (l₁ l₂ : List α) :
    map f (reverseAux l₁ l₂) = reverseAux (map f l₁) (map f l₂) := by
  simp only [reverseAux_eq, map_append, map_reverse]

-- TODO: Rename `List.reverse_perm` to `List.reverse_perm_self`
/--
lemma `reverse_perm'` / 引理 `reverse_perm'`

English:
lemma reverse_perm'
  statement: l₁.reverse ~ l₂ ↔ l₁ ~ l₂ where
  proof: l₁.reverse_perm.symm.trans
  mpr := l₁.reverse_perm.trans

中文:
引理 reverse_perm'
  结论: l₁.reverse ~ l₂ ↔ l₁ ~ l₂ where
  证明: l₁.reverse_perm.symm.trans
  mpr := l₁.reverse_perm.trans
-/
@[simp] lemma reverse_perm' : l₁.reverse ~ l₂ ↔ l₁ ~ l₂ where
  mp := l₁.reverse_perm.symm.trans
  mpr := l₁.reverse_perm.trans

/--
lemma `perm_reverse` / 引理 `perm_reverse`

English:
lemma perm_reverse
  statement: l₁ ~ l₂.reverse ↔ l₁ ~ l₂ where
  proof: hl.trans l₂.reverse_perm
  mpr hl := hl.trans l₂.reverse_perm.symm

中文:
引理 perm_reverse
  结论: l₁ ~ l₂.reverse ↔ l₁ ~ l₂ where
  证明: hl.trans l₂.reverse_perm
  mpr hl := hl.trans l₂.reverse_perm.symm
-/
@[simp] lemma perm_reverse : l₁ ~ l₂.reverse ↔ l₁ ~ l₂ where
  mp hl := hl.trans l₂.reverse_perm
  mpr hl := hl.trans l₂.reverse_perm.symm

/-! ### getLast -/

attribute [simp] getLast_cons

/--
theorem `getLast_append_singleton` / 定理 `getLast_append_singleton`

English:
theorem getLast_append_singleton
  given: {a : α} (l : List α)
  proof: by
  simp

中文:
定理 getLast_append_singleton
  条件: {a : α} (l : 列表 α)
  证明: by
  simp
-/
theorem getLast_append_singleton {a : α} (l : List α) :
    getLast (l ++ [a]) (append_ne_nil_of_right_ne_nil l (cons_ne_nil a _)) = a := by
  simp

/--
theorem `getLast_append_of_right_ne_nil` / 定理 `getLast_append_of_right_ne_nil`

English:
theorem getLast_append_of_right_ne_nil
  given: (l₁ l₂ : List α) (h : l₂ != [])
  proof: by
  induction l₁ with grind

中文:
定理 getLast_append_of_right_ne_nil
  条件: (l₁ l₂ : 列表 α) (h : l₂ != [])
  证明: by
  induction l₁ with grind
-/
theorem getLast_append_of_right_ne_nil (l₁ l₂ : List α) (h : l₂ != []) :
    getLast (l₁ ++ l₂) (append_ne_nil_of_right_ne_nil l₁ h) = getLast l₂ h := by
  induction l₁ with grind

/--
theorem `getLast_concat'` / 定理 `getLast_concat'`

English:
theorem getLast_concat'
  given: {a : α} (l : List α)
  statement: getLast (concat l a) (by simp) = a
  proof: by
  simp

@[simp]

中文:
定理 getLast_concat'
  条件: {a : α} (l : 列表 α)
  结论: getLast (concat l a) (by simp) = a
  证明: by
  simp

@[simp]
-/
theorem getLast_concat' {a : α} (l : List α) : getLast (concat l a) (by simp) = a := by
  simp

@[simp]
/--
theorem `getLast_singleton'` / 定理 `getLast_singleton'`

English:
theorem getLast_singleton'
  given: (a : α)
  statement: getLast [a] (cons_ne_nil a []) = a
  proof: rfl

中文:
定理 getLast_singleton'
  条件: (a : α)
  结论: getLast [a] (cons_ne_nil a []) = a
  证明: rfl
-/
theorem getLast_singleton' (a : α) : getLast [a] (cons_ne_nil a []) = a := rfl

/--
theorem `dropLast_append_getLast` / 定理 `dropLast_append_getLast`

English:
theorem dropLast_append_getLast
  statement: forall {l : List α} (h : l != []), dropLast l ++ [getLast l h] = l

中文:
定理 dropLast_append_getLast
  结论: 对任意 {l : 列表 α} (h : l != []), dropLast l ++ [getLast l h] = l
-/
theorem dropLast_append_getLast : forall {l : List α} (h : l != []), dropLast l ++ [getLast l h] = l
  | [], h => absurd rfl h
  | [_], _ => rfl
  | a :: b :: l, h => by
    rw [dropLast_cons_cons]; rw [cons_append]; rw [getLast_cons (cons_ne_nil _ _)]
    congr
    exact dropLast_append_getLast (cons_ne_nil b l)

/--
theorem `getLast_congr` / 定理 `getLast_congr`

English:
theorem getLast_congr
  given: {l₁ l₂ : List α} (h₁ : l₁ != []) (h₂ : l₂ != []) (h₃ : l₁ = l₂)
  proof: by subst l₁; rfl

中文:
定理 getLast_congr
  条件: {l₁ l₂ : 列表 α} (h₁ : l₁ != []) (h₂ : l₂ != []) (h₃ : l₁ = l₂)
  证明: by subst l₁; rfl
-/
theorem getLast_congr {l₁ l₂ : List α} (h₁ : l₁ != []) (h₂ : l₂ != []) (h₃ : l₁ = l₂) :
    getLast l₁ h₁ = getLast l₂ h₂ := by subst l₁; rfl

/--
theorem `getLast_replicate_succ` / 定理 `getLast_replicate_succ`

English:
theorem getLast_replicate_succ
  given: (m : Nat) (a : α)
  proof: by
  simp only [replicate_succ']
  exact getLast_append_singleton _

中文:
定理 getLast_replicate_succ
  条件: (m : 自然数) (a : α)
  证明: by
  simp only [replicate_succ']
  exact getLast_append_singleton _

Depends on / 依赖: getLast_append_singleton, replicate_succ
-/
theorem getLast_replicate_succ (m : Nat) (a : α) :
    (replicate (m + 1) a).getLast (ne_nil_of_length_eq_add_one length_replicate) = a := by
  simp only [replicate_succ']
  exact getLast_append_singleton _


/--
theorem `mem_getLast?_eq_getLast` / 定理 `mem_getLast?_eq_getLast`

English:
theorem mem_getLast?_eq_getLast
  statement: forall {l : List α} {x : α}, x in l.getLast? -> exists h, x = getLast l h

中文:
定理 mem_getLast?_eq_getLast
  结论: 对任意 {l : 列表 α} {x : α}, x in l.getLast? -> 存在 h, x = getLast l h
-/
theorem mem_getLast?_eq_getLast : forall {l : List α} {x : α}, x in l.getLast? -> exists h, x = getLast l h
  | [], x, hx
  | [a], x, hx
  | a :: b :: l, x, hx => by grind

/--
theorem `getLast?_eq_getLast_of_ne_nil` / 定理 `getLast?_eq_getLast_of_ne_nil`

English:
theorem getLast?_eq_getLast_of_ne_nil
  statement: forall {l : List α} (h : l != []), l.getLast? = some (l.getLast h)

中文:
定理 getLast?_eq_getLast_of_ne_nil
  结论: 对任意 {l : 列表 α} (h : l != []), l.getLast? = some (l.getLast h)
-/
theorem getLast?_eq_getLast_of_ne_nil : forall {l : List α} (h : l != []), l.getLast? = some (l.getLast h)
  | [], h => (h rfl).elim
  | [_], _ => rfl
  | _ :: b :: l, _ => @getLast?_eq_getLast_of_ne_nil (b :: l) (cons_ne_nil _ _)

/--
theorem `mem_getLast?_cons` / 定理 `mem_getLast?_cons`

English:
theorem mem_getLast?_cons
  given: {x y : α}
  statement: forall {l : List α}, x in l.getLast? -> x in (y :: l).getLast?

中文:
定理 mem_getLast?_cons
  条件: {x y : α}
  结论: 对任意 {l : 列表 α}, x in l.getLast? -> x in (y :: l).getLast?
-/
theorem mem_getLast?_cons {x y : α} : forall {l : List α}, x in l.getLast? -> x in (y :: l).getLast?
  | [], _ => by contradiction
  | _ :: _, h => h

/--
theorem `dropLast_append_getLast?` / 定理 `dropLast_append_getLast?`

English:
theorem dropLast_append_getLast?
  statement: forall {l : List α}, forall a in l.getLast?, dropLast l ++ [a] = l

中文:
定理 dropLast_append_getLast?
  结论: 对任意 {l : 列表 α}, 对任意 a in l.getLast?, dropLast l ++ [a] = l
-/
theorem dropLast_append_getLast? : forall {l : List α}, forall a in l.getLast?, dropLast l ++ [a] = l
  | [], a, ha => (Option.not_mem_none a ha).elim
  | [a], _, rfl => rfl
  | a :: b :: l, c, hc => by
    rw [getLast?_cons_cons] at hc
    rw [dropLast_cons_cons]; rw [cons_append]; rw [dropLast_append_getLast? _ hc]

/--
theorem `getLastI_eq_getLast?_getD` / 定理 `getLastI_eq_getLast?_getD`

English:
theorem getLastI_eq_getLast?_getD
  given: [Inhabited α]
  statement: forall l : List α, l.getLastI = l.getLast?.getD default

中文:
定理 getLastI_eq_getLast?_getD
  条件: [可居 α]
  结论: 对任意 l : 列表 α, l.getLastI = l.getLast?.getD default
-/
theorem getLastI_eq_getLast?_getD [Inhabited α] : forall l : List α, l.getLastI = l.getLast?.getD default
  | [] => by simp [getLastI]
  | [_] => rfl
  | [_, _] => rfl
  | [_, _, _] => rfl
  | _ :: _ :: c :: l => by simp [getLastI, getLastI_eq_getLast?_getD (c :: l)]

@[deprecated getLastI_eq_getLast?_getD (since := "2026-01-05")]
/--
theorem `getLastI_eq_getLast?` / 定理 `getLastI_eq_getLast?`

English:
theorem getLastI_eq_getLast?
  given: [Inhabited α]
  statement: forall l : List α, l.getLastI = l.getLast?.getD default
  proof: getLastI_eq_getLast?_getD

中文:
定理 getLastI_eq_getLast?
  条件: [可居 α]
  结论: 对任意 l : 列表 α, l.getLastI = l.getLast?.getD default
  证明: getLastI_eq_getLast?_getD

Depends on / 依赖: _getD, getLastI_eq_getLast
-/
theorem getLastI_eq_getLast? [Inhabited α] : forall l : List α, l.getLastI = l.getLast?.getD default :=
  getLastI_eq_getLast?_getD

/--
theorem `getLast?_append_cons` / 定理 `getLast?_append_cons`

English:
theorem getLast?_append_cons

中文:
定理 getLast?_append_cons
-/
theorem getLast?_append_cons :
    forall (l₁ : List α) (a : α) (l₂ : List α), getLast? (l₁ ++ a :: l₂) = getLast? (a :: l₂)
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | b :: c :: l₁, a, l₂ => by rw [cons_append, cons_append, getLast?_cons_cons,
    ← cons_append, getLast?_append_cons (c :: l₁)]

/--
theorem `getLast?_append_of_ne_nil` / 定理 `getLast?_append_of_ne_nil`

English:
theorem getLast?_append_of_ne_nil
  given: (l₁ : List α)

中文:
定理 getLast?_append_of_ne_nil
  条件: (l₁ : 列表 α)
-/
theorem getLast?_append_of_ne_nil (l₁ : List α) :
    forall {l₂ : List α} (_ : l₂ != []), getLast? (l₁ ++ l₂) = getLast? l₂
  | [], hl₂ => by contradiction
  | b :: l₂, _ => getLast?_append_cons l₁ b l₂

/--
theorem `mem_getLast?_append_of_mem_getLast?` / 定理 `mem_getLast?_append_of_mem_getLast?`

English:
theorem mem_getLast?_append_of_mem_getLast?
  given: {l₁ l₂ : List α} {x : α} (h : x in l₂.getLast?)
  proof: by grind

中文:
定理 mem_getLast?_append_of_mem_getLast?
  条件: {l₁ l₂ : 列表 α} {x : α} (h : x in l₂.getLast?)
  证明: by grind
-/
theorem mem_getLast?_append_of_mem_getLast? {l₁ l₂ : List α} {x : α} (h : x in l₂.getLast?) :
    x in (l₁ ++ l₂).getLast? := by grind

/--
theorem `mem_dropLast_of_mem_of_ne_getLast` / 定理 `mem_dropLast_of_mem_of_ne_getLast`

English:
theorem mem_dropLast_of_mem_of_ne_getLast
  statement: {a : α} (ha : a in l)
  proof: by
  grind [dropLast_concat_getLast]

中文:
定理 mem_dropLast_of_mem_of_ne_getLast
  结论: {a : α} (ha : a in l)
  证明: by
  grind [dropLast_concat_getLast]

Depends on / 依赖: dropLast_concat_getLast
-/
theorem mem_dropLast_of_mem_of_ne_getLast {a : α} (ha : a in l)
    (ha' : a != l.getLast (ne_nil_of_mem ha)) : a in l.dropLast := by
  grind [dropLast_concat_getLast]

/--
theorem `mem_dropLast_of_mem_of_ne_getLastD` / 定理 `mem_dropLast_of_mem_of_ne_getLastD`

English:
theorem mem_dropLast_of_mem_of_ne_getLastD
  given: {a d : α} (ha : a in l) (ha' : a != l.getLastD d)
  proof: mem_dropLast_of_mem_of_ne_getLast ha by grind

中文:
定理 mem_dropLast_of_mem_of_ne_getLastD
  条件: {a d : α} (ha : a in l) (ha' : a != l.getLastD d)
  证明: mem_dropLast_of_mem_of_ne_getLast ha by grind

Depends on / 依赖: mem_dropLast_of_mem_of_ne_getLast
-/
theorem mem_dropLast_of_mem_of_ne_getLastD {a d : α} (ha : a in l) (ha' : a != l.getLastD d) :
    a in l.dropLast :=
mem_dropLast_of_mem_of_ne_getLast ha by grind

/--
theorem `mem_dropLast_of_mem_of_ne_getLast?` / 定理 `mem_dropLast_of_mem_of_ne_getLast?`

English:
theorem mem_dropLast_of_mem_of_ne_getLast?
  given: {a : α} (ha : a in l) (ha' : a != l.getLast?)
  proof: mem_dropLast_of_mem_of_ne_getLast ha by grind

中文:
定理 mem_dropLast_of_mem_of_ne_getLast?
  条件: {a : α} (ha : a in l) (ha' : a != l.getLast?)
  证明: mem_dropLast_of_mem_of_ne_getLast ha by grind
-/
theorem mem_dropLast_of_mem_of_ne_getLast? {a : α} (ha : a in l) (ha' : a != l.getLast?) :
    a in l.dropLast :=
mem_dropLast_of_mem_of_ne_getLast ha by grind

/-! ### head(!?) and tail -/

@[simp]
/--
theorem `head!_nil` / 定理 `head!_nil`

English:
theorem head!_nil
  given: [Inhabited α]
  statement: ([] : List α).head! = default
  proof: rfl

中文:
定理 head!_nil
  条件: [可居 α]
  结论: ([] : 列表 α).head! = default
  证明: rfl
-/
theorem head!_nil [Inhabited α] : ([] : List α).head! = default := rfl

/--
theorem `head_eq_getElem_zero` / 定理 `head_eq_getElem_zero`

English:
theorem head_eq_getElem_zero
  given: {l : List α} (hl : l != [])
  proof: (getElem_zero _).symm

中文:
定理 head_eq_getElem_zero
  条件: {l : 列表 α} (hl : l != [])
  证明: (getElem_zero _).symm

Depends on / 依赖: getElem_zero
-/
theorem head_eq_getElem_zero {l : List α} (hl : l != []) :
    l.head hl = l[0]'(length_pos_iff.2 hl) :=
  (getElem_zero _).symm

/--
theorem `head!_eq_head?_getD` / 定理 `head!_eq_head?_getD`

English:
theorem head!_eq_head?_getD
  given: [Inhabited α] (l : List α)
  statement: head! l = (head? l).getD default
  proof: by
  cases l <;> rfl

@[deprecated head!_eq_head?_getD (since := "2026-01-05")]

中文:
定理 head!_eq_head?_getD
  条件: [可居 α] (l : 列表 α)
  结论: head! l = (head? l).getD default
  证明: by
  cases l <;> rfl

@[deprecated head!_eq_head?_getD (since := "2026-01-05")]
-/
theorem head!_eq_head?_getD [Inhabited α] (l : List α) : head! l = (head? l).getD default := by
  cases l <;> rfl

@[deprecated head!_eq_head?_getD (since := "2026-01-05")]
/--
theorem `head!_eq_head?` / 定理 `head!_eq_head?`

English:
theorem head!_eq_head?
  given: [Inhabited α] (l : List α)
  statement: head! l = (head? l).getD default
  proof: head!_eq_head?_getD l

中文:
定理 head!_eq_head?
  条件: [可居 α] (l : 列表 α)
  结论: head! l = (head? l).getD default
  证明: head!_eq_head?_getD l
-/
theorem head!_eq_head? [Inhabited α] (l : List α) : head! l = (head? l).getD default :=
  head!_eq_head?_getD l

/--
theorem `surjective_head!` / 定理 `surjective_head!`

English:
theorem surjective_head!
  given: [Inhabited α]
  statement: Surjective (@head! α _)
  proof: fun x => ⟨[x], rfl⟩

中文:
定理 surjective_head!
  条件: [可居 α]
  结论: 满射 (@head! α _)
  证明: fun x => ⟨[x], rfl⟩
-/
theorem surjective_head! [Inhabited α] : Surjective (@head! α _) := fun x => ⟨[x], rfl⟩

/--
theorem `surjective_head?` / 定理 `surjective_head?`

English:
theorem surjective_head?
  statement: Surjective (@head? α)
  proof: Option.forall.2 ⟨⟨[], rfl⟩, fun x => ⟨[x], rfl⟩⟩

中文:
定理 surjective_head?
  结论: 满射 (@head? α)
  证明: Option.forall.2 ⟨⟨[], rfl⟩, fun x => ⟨[x], rfl⟩⟩
-/
theorem surjective_head? : Surjective (@head? α) :=
  Option.forall.2 ⟨⟨[], rfl⟩, fun x => ⟨[x], rfl⟩⟩

/--
theorem `surjective_tail` / 定理 `surjective_tail`

English:
theorem surjective_tail
  statement: Surjective (@tail α)

中文:
定理 surjective_tail
  结论: 满射 (@tail α)
-/
theorem surjective_tail : Surjective (@tail α)
  | [] => ⟨[], rfl⟩
  | a :: l => ⟨a :: a :: l, rfl⟩

/--
theorem `eq_cons_of_mem_head?` / 定理 `eq_cons_of_mem_head?`

English:
theorem eq_cons_of_mem_head?
  given: {x : α}
  statement: forall {l : List α}, x in l.head? -> l = x :: tail l

中文:
定理 eq_cons_of_mem_head?
  条件: {x : α}
  结论: 对任意 {l : 列表 α}, x in l.head? -> l = x :: tail l
-/
theorem eq_cons_of_mem_head? {x : α} : forall {l : List α}, x in l.head? -> l = x :: tail l
  | [], h => (Option.not_mem_none _ h).elim
  | a :: l, h => by
    simp only [head?, Option.mem_def, Option.some_inj] at h
    exact h ▸ rfl

/--
theorem `head!_cons` / 定理 `head!_cons`

English:
theorem head!_cons
  given: [Inhabited α] (a : α) (l : List α)
  statement: head! (a :: l) = a
  proof: rfl

@[simp]

中文:
定理 head!_cons
  条件: [可居 α] (a : α) (l : 列表 α)
  结论: head! (a :: l) = a
  证明: rfl

@[simp]
-/
@[simp] theorem head!_cons [Inhabited α] (a : α) (l : List α) : head! (a :: l) = a := rfl

@[simp]
/--
theorem `head!_append` / 定理 `head!_append`

English:
theorem head!_append
  given: [Inhabited α] (t : List α) {s : List α} (h : s != [])
  proof: by
  induction s
  · contradiction
  · rfl

中文:
定理 head!_append
  条件: [可居 α] (t : 列表 α) {s : 列表 α} (h : s != [])
  证明: by
  induction s
  · contradiction
  · rfl
-/
theorem head!_append [Inhabited α] (t : List α) {s : List α} (h : s != []) :
    head! (s ++ t) = head! s := by
  induction s
  · contradiction
  · rfl

/--
theorem `mem_head?_append_of_mem_head?` / 定理 `mem_head?_append_of_mem_head?`

English:
theorem mem_head?_append_of_mem_head?
  given: {s t : List α} {x : α} (h : x in s.head?)
  proof: by
  grind [Option.mem_def]

中文:
定理 mem_head?_append_of_mem_head?
  条件: {s t : 列表 α} {x : α} (h : x in s.head?)
  证明: by
  grind [Option.mem_def]

Depends on / 依赖: Option.mem_def, mem_def
-/
theorem mem_head?_append_of_mem_head? {s t : List α} {x : α} (h : x in s.head?) :
    x in (s ++ t).head? := by
  grind [Option.mem_def]

/--
theorem `head?_append_of_ne_nil` / 定理 `head?_append_of_ne_nil`

English:
theorem head?_append_of_ne_nil

中文:
定理 head?_append_of_ne_nil
-/
theorem head?_append_of_ne_nil :
    forall (l₁ : List α) {l₂ : List α} (_ : l₁ != []), head? (l₁ ++ l₂) = head? l₁
  | _ :: _, _, _ => rfl

/--
theorem `tail_append_singleton_of_ne_nil` / 定理 `tail_append_singleton_of_ne_nil`

English:
theorem tail_append_singleton_of_ne_nil
  given: {a : α} {l : List α} (h : l != nil)
  proof: by grind

中文:
定理 tail_append_singleton_of_ne_nil
  条件: {a : α} {l : 列表 α} (h : l != nil)
  证明: by grind
-/
theorem tail_append_singleton_of_ne_nil {a : α} {l : List α} (h : l != nil) :
    tail (l ++ [a]) = tail l ++ [a] := by grind

/--
theorem `cons_head?_tail` / 定理 `cons_head?_tail`

English:
theorem cons_head?_tail
  statement: forall {l : List α} {a : α}, a in head? l -> a :: tail l = l
  proof: by simpa using h
    simp [this]

中文:
定理 cons_head?_tail
  结论: 对任意 {l : 列表 α} {a : α}, a in head? l -> a :: tail l = l
  证明: by simpa using h
    simp [this]
-/
theorem cons_head?_tail : forall {l : List α} {a : α}, a in head? l -> a :: tail l = l
  | [], a, h => by contradiction
  | b :: l, a, h => by
    have : b = a := by simpa using h
    simp [this]

/--
theorem `head!_mem_head?` / 定理 `head!_mem_head?`

English:
theorem head!_mem_head?
  given: [Inhabited α]
  statement: forall {l : List α}, l != [] -> head! l in head? l

中文:
定理 head!_mem_head?
  条件: [可居 α]
  结论: 对任意 {l : 列表 α}, l != [] -> head! l in head? l
-/
theorem head!_mem_head? [Inhabited α] : forall {l : List α}, l != [] -> head! l in head? l
  | [], h => by contradiction
  | _ :: _, _ => rfl

/--
theorem `cons_head!_tail` / 定理 `cons_head!_tail`

English:
theorem cons_head!_tail
  given: [Inhabited α] {l : List α} (h : l != [])
  statement: head! l :: tail l = l
  proof: cons_head?_tail (head!_mem_head? h)

中文:
定理 cons_head!_tail
  条件: [可居 α] {l : 列表 α} (h : l != [])
  结论: head! l :: tail l = l
  证明: cons_head?_tail (head!_mem_head? h)
-/
theorem cons_head!_tail [Inhabited α] {l : List α} (h : l != []) : head! l :: tail l = l :=
  cons_head?_tail (head!_mem_head? h)

/--
theorem `head!_mem_self` / 定理 `head!_mem_self`

English:
theorem head!_mem_self
  given: [Inhabited α] {l : List α} (h : l != nil)
  statement: l.head! in l
  proof: by
  have h' : l.head! in l.head! :: l.tail := mem_cons_self
  rwa [cons_head!_tail h] at h'

中文:
定理 head!_mem_self
  条件: [可居 α] {l : 列表 α} (h : l != nil)
  结论: l.head! in l
  证明: by
  have h' : l.head! in l.head! :: l.tail := mem_cons_self
  rwa [cons_head!_tail h] at h'
-/
theorem head!_mem_self [Inhabited α] {l : List α} (h : l != nil) : l.head! in l := by
  have h' : l.head! in l.head! :: l.tail := mem_cons_self
  rwa [cons_head!_tail h] at h'

/--
theorem `get_eq_getElem?` / 定理 `get_eq_getElem?`

English:
theorem get_eq_getElem?
  given: (l : List α) (i : Fin l.length)
  proof: by
  simp

中文:
定理 get_eq_getElem?
  条件: (l : 列表 α) (i : 有限集 l.length)
  证明: by
  simp
-/
theorem get_eq_getElem? (l : List α) (i : Fin l.length) :
    l.get i = l[i]?.get (by simp) := by
  simp

/--
theorem `exists_mem_iff_getElem` / 定理 `exists_mem_iff_getElem`

English:
theorem exists_mem_iff_getElem
  given: {l : List α} {p : α -> Prop}
  proof: by
  simp only [mem_iff_getElem]
  exact ⟨fun ⟨_x, ⟨i, hi, hix⟩, hxp⟩ => ⟨i, hi, hix ▸ hxp⟩, fun ⟨i, hi, hp⟩ => ⟨_, ⟨i, hi, rfl⟩, hp⟩⟩

中文:
定理 存在_mem_iff_getElem
  条件: {l : 列表 α} {p : α -> 命题}
  证明: by
  simp only [mem_iff_getElem]
  exact ⟨fun ⟨_x, ⟨i, hi, hix⟩, hxp⟩ => ⟨i, hi, hix ▸ hxp⟩, fun ⟨i, hi, hp⟩ => ⟨_, ⟨i, hi, rfl⟩, hp⟩⟩

Depends on / 依赖: mem_iff_getElem
-/
theorem exists_mem_iff_getElem {l : List α} {p : α -> Prop} :
    (exists x in l, p x) ↔ exists (i : Nat) (_ : i < l.length), p l[i] := by
  simp only [mem_iff_getElem]
  exact ⟨fun ⟨_x, ⟨i, hi, hix⟩, hxp⟩ => ⟨i, hi, hix ▸ hxp⟩, fun ⟨i, hi, hp⟩ => ⟨_, ⟨i, hi, rfl⟩, hp⟩⟩

/--
theorem `exists_mem_iff_get` / 定理 `exists_mem_iff_get`

English:
theorem exists_mem_iff_get
  given: {l : List α} {p : α -> Prop}
  proof: exists_mem_iff_getElem.trans ⟨fun ⟨i, hi, h⟩ => ⟨⟨i, hi⟩, h⟩, fun ⟨i, h⟩ => ⟨i, i.isLt, h⟩⟩

中文:
定理 存在_mem_iff_get
  条件: {l : 列表 α} {p : α -> 命题}
  证明: exists_mem_iff_getElem.trans ⟨fun ⟨i, hi, h⟩ => ⟨⟨i, hi⟩, h⟩, fun ⟨i, h⟩ => ⟨i, i.isLt, h⟩⟩

Depends on / 依赖: exists_mem_iff_getElem, exists_mem_iff_getElem.trans, i.isLt
-/
theorem exists_mem_iff_get {l : List α} {p : α -> Prop} :
    (exists x in l, p x) ↔ exists (i : Fin l.length), p (l.get i) :=
  exists_mem_iff_getElem.trans ⟨fun ⟨i, hi, h⟩ => ⟨⟨i, hi⟩, h⟩, fun ⟨i, h⟩ => ⟨i, i.isLt, h⟩⟩

/--
theorem `forall_mem_iff_getElem` / 定理 `forall_mem_iff_getElem`

English:
theorem forall_mem_iff_getElem
  given: {l : List α} {p : α -> Prop}
  proof: by
  simp [mem_iff_getElem, @forall_comm α]

中文:
定理 对任意_mem_iff_getElem
  条件: {l : 列表 α} {p : α -> 命题}
  证明: by
  simp [mem_iff_getElem, @forall_comm α]

Depends on / 依赖: forall_comm, mem_iff_getElem
-/
theorem forall_mem_iff_getElem {l : List α} {p : α -> Prop} :
    (forall x in l, p x) ↔ forall (i : Nat) (_ : i < l.length), p l[i] := by
  simp [mem_iff_getElem, @forall_comm α]

/--
theorem `forall_mem_iff_get` / 定理 `forall_mem_iff_get`

English:
theorem forall_mem_iff_get
  given: {l : List α} {p : α -> Prop}
  proof: forall_mem_iff_getElem.trans ⟨fun h i => h i i.isLt, fun h i hi => h ⟨i, hi⟩⟩

@[simp]

中文:
定理 对任意_mem_iff_get
  条件: {l : 列表 α} {p : α -> 命题}
  证明: forall_mem_iff_getElem.trans ⟨fun h i => h i i.isLt, fun h i hi => h ⟨i, hi⟩⟩

@[simp]

Depends on / 依赖: forall_mem_iff_getElem, forall_mem_iff_getElem.trans, i.isLt
-/
theorem forall_mem_iff_get {l : List α} {p : α -> Prop} :
    (forall x in l, p x) ↔ forall (i : Fin l.length), p (l.get i) :=
  forall_mem_iff_getElem.trans ⟨fun h i => h i i.isLt, fun h i hi => h ⟨i, hi⟩⟩

@[simp]
/--
theorem `get_surjective_iff` / 定理 `get_surjective_iff`

English:
theorem get_surjective_iff
  given: {l : List α}
  statement: l.get.Surjective ↔ (forall x, x in l)
  proof: forall_congr' fun _ => mem_iff_get.symm

@[simp]

中文:
定理 get_surjective_iff
  条件: {l : 列表 α}
  结论: l.get.满射 ↔ (对任意 x, x in l)
  证明: forall_congr' fun _ => mem_iff_get.symm

@[simp]

Depends on / 依赖: forall_congr, mem_iff_get, mem_iff_get.symm
-/
theorem get_surjective_iff {l : List α} : l.get.Surjective ↔ (forall x, x in l) :=
  forall_congr' fun _ => mem_iff_get.symm

@[simp]
/--
theorem `getElem_fin_surjective_iff` / 定理 `getElem_fin_surjective_iff`

English:
theorem getElem_fin_surjective_iff
  given: {l : List α}
  proof: get_surjective_iff

@[simp]

中文:
定理 getElem_fin_surjective_iff
  条件: {l : 列表 α}
  证明: get_surjective_iff

@[simp]

Depends on / 依赖: get_surjective_iff
-/
theorem getElem_fin_surjective_iff {l : List α} :
    (fun (n : Fin l.length) => l[n.val]).Surjective ↔ (forall x, x in l) :=
  get_surjective_iff

@[simp]
/--
theorem `getElem?_surjective_iff` / 定理 `getElem?_surjective_iff`

English:
theorem getElem?_surjective_iff
  given: {l : List α}
  statement: (fun (n : Nat) => l[n]?).Surjective ↔ (forall x, x in l)
  proof: by
refine ⟨fun h x => mem_iff_getElem?.mpr h x, fun h x => ?_⟩
  cases x with
| none => exact ⟨l.length, getElem?_eq_none Nat.le_refl _⟩
| some x => exact mem_iff_getElem?.mp h x

中文:
定理 getElem?_surjective_iff
  条件: {l : 列表 α}
  结论: (fun (n : 自然数) => l[n]?).满射 ↔ (对任意 x, x in l)
  证明: by
refine ⟨fun h x => mem_iff_getElem?.mpr h x, fun h x => ?_⟩
  cases x with
| none => exact ⟨l.length, getElem?_eq_none Nat.le_refl _⟩
| some x => exact mem_iff_getElem?.mp h x
-/
theorem getElem?_surjective_iff {l : List α} : (fun (n : Nat) => l[n]?).Surjective ↔ (forall x, x in l) := by
refine ⟨fun h x => mem_iff_getElem?.mpr h x, fun h x => ?_⟩
  cases x with
| none => exact ⟨l.length, getElem?_eq_none Nat.le_refl _⟩
| some x => exact mem_iff_getElem?.mp h x

/--
theorem `get_tail` / 定理 `get_tail`

English:
theorem get_tail
  statement: (l : List α) (i) (h : i < l.tail.length)
  proof: by
  simp

中文:
定理 get_tail
  结论: (l : 列表 α) (i) (h : i < l.tail.length)
  证明: by
  simp

Depends on / 依赖: length_tail
-/
theorem get_tail (l : List α) (i) (h : i < l.tail.length)
    (h' : i + 1 < l.length := (by simp only [length_tail] at h; lia)) :
    l.tail.get ⟨i, h⟩ = l.get ⟨i + 1, h'⟩ := by
  simp

/--
theorem `getElem_mem_tail` / 定理 `getElem_mem_tail`

English:
theorem getElem_mem_tail
  given: {k : Nat} (l : List α) (h : k != 0) (hk : k < l.length)
  proof: by
  cases l <;> grind

中文:
定理 getElem_mem_tail
  条件: {k : 自然数} (l : 列表 α) (h : k != 0) (hk : k < l.length)
  证明: by
  cases l <;> grind
-/
theorem getElem_mem_tail {k : Nat} (l : List α) (h : k != 0) (hk : k < l.length) :
    l[k]'hk in l.tail := by
  cases l <;> grind

/-! ### sublists -/

attribute [refl] List.Sublist.refl

/--
lemma `cons_sublist_cons'` / 引理 `cons_sublist_cons'`

English:
lemma cons_sublist_cons'
  given: {a b : α}
  statement: a :: l₁ <+ b :: l₂ ↔ a :: l₁ <+ l₂ ∨ a = b ∧ l₁ <+ l₂
  proof: by
  grind

中文:
引理 cons_sublist_cons'
  条件: {a b : α}
  结论: a :: l₁ <+ b :: l₂ ↔ a :: l₁ <+ l₂ ∨ a = b ∧ l₁ <+ l₂
  证明: by
  grind
-/
lemma cons_sublist_cons' {a b : α} : a :: l₁ <+ b :: l₂ ↔ a :: l₁ <+ l₂ ∨ a = b ∧ l₁ <+ l₂ := by
  grind

/--
theorem `sublist_cons_of_sublist` / 定理 `sublist_cons_of_sublist`

English:
theorem sublist_cons_of_sublist
  given: (a : α) (h : l₁ <+ l₂)
  statement: l₁ <+ a :: l₂
  proof: h.cons _

中文:
定理 sublist_cons_of_sublist
  条件: (a : α) (h : l₁ <+ l₂)
  结论: l₁ <+ a :: l₂
  证明: h.cons _

Depends on / 依赖: h.cons
-/
theorem sublist_cons_of_sublist (a : α) (h : l₁ <+ l₂) : l₁ <+ a :: l₂ := h.cons _

/--
lemma `sublist_singleton` / 引理 `sublist_singleton`

English:
lemma sublist_singleton
  given: {l : List α} {a : α}
  statement: l <+ [a] ↔ l = [] ∨ l = [a]
  proof: by
  constructor <;> rintro (_ | _) <;> aesop

中文:
引理 sublist_singleton
  条件: {l : 列表 α} {a : α}
  结论: l <+ [a] ↔ l = [] ∨ l = [a]
  证明: by
  constructor <;> rintro (_ | _) <;> aesop
-/
@[simp] lemma sublist_singleton {l : List α} {a : α} : l <+ [a] ↔ l = [] ∨ l = [a] := by
  constructor <;> rintro (_ | _) <;> aesop

/--
theorem `Sublist.antisymm` / 定理 `Sublist.antisymm`

English:
theorem Sublist.antisymm
  given: (s₁ : l₁ <+ l₂) (s₂ : l₂ <+ l₁)
  statement: l₁ = l₂
  proof: s₁.eq_of_length_le s₂.length_le

中文:
定理 子表.antisymm
  条件: (s₁ : l₁ <+ l₂) (s₂ : l₂ <+ l₁)
  结论: l₁ = l₂
  证明: s₁.eq_of_length_le s₂.length_le

Depends on / 依赖: eq_of_length_le, length_le
-/
theorem Sublist.antisymm (s₁ : l₁ <+ l₂) (s₂ : l₂ <+ l₁) : l₁ = l₂ :=
  s₁.eq_of_length_le s₂.length_le

/--
theorem `Sublist.of_cons_of_ne` / 定理 `Sublist.of_cons_of_ne`

English:
theorem Sublist.of_cons_of_ne
  given: {a b} (h₁ : a != b) (h₂ : a :: l₁ <+ b :: l₂)
  statement: a :: l₁ <+ l₂
  proof: match h₁, h₂ with
  | _, .cons _ h => h

中文:
定理 子表.of_cons_of_ne
  条件: {a b} (h₁ : a != b) (h₂ : a :: l₁ <+ b :: l₂)
  结论: a :: l₁ <+ l₂
  证明: match h₁, h₂ with
  | _, .cons _ h => h
-/
theorem Sublist.of_cons_of_ne {a b} (h₁ : a != b) (h₂ : a :: l₁ <+ b :: l₂) : a :: l₁ <+ l₂ :=
  match h₁, h₂ with
  | _, .cons _ h => h

/-! ### indexOf -/

section IndexOf

variable [BEq α] [LawfulBEq α]

/--
theorem `idxOf_cons_eq` / 定理 `idxOf_cons_eq`

English:
theorem idxOf_cons_eq
  given: {a b : α} (l : List α)
  statement: b = a -> idxOf a (b :: l) = 0

中文:
定理 idxOf_cons_eq
  条件: {a b : α} (l : 列表 α)
  结论: b = a -> idxOf a (b :: l) = 0
-/
theorem idxOf_cons_eq {a b : α} (l : List α) : b = a -> idxOf a (b :: l) = 0
  | e => by rw [← e]; exact idxOf_cons_self

@[simp]
/--
theorem `idxOf_cons_ne` / 定理 `idxOf_cons_ne`

English:
theorem idxOf_cons_ne
  given: {a b : α} (l : List α) (h : b != a)
  statement: idxOf a (b :: l) = succ (idxOf a l)
  proof: by
  simp [idxOf_cons, beq_false_of_ne h]

中文:
定理 idxOf_cons_ne
  条件: {a b : α} (l : 列表 α) (h : b != a)
  结论: idxOf a (b :: l) = succ (idxOf a l)
  证明: by
  simp [idxOf_cons, beq_false_of_ne h]

Depends on / 依赖: beq_false_of_ne, idxOf_cons
-/
theorem idxOf_cons_ne {a b : α} (l : List α) (h : b != a) : idxOf a (b :: l) = succ (idxOf a l) := by
  simp [idxOf_cons, beq_false_of_ne h]

/--
theorem `idxOf_eq_length_iff` / 定理 `idxOf_eq_length_iff`

English:
theorem idxOf_eq_length_iff
  given: {a : α} {l : List α}
  statement: idxOf a l = length l ↔ a ∉ l
  proof: by
  grind

@[simp]

中文:
定理 idxOf_eq_length_iff
  条件: {a : α} {l : 列表 α}
  结论: idxOf a l = length l ↔ a ∉ l
  证明: by
  grind

@[simp]
-/
theorem idxOf_eq_length_iff {a : α} {l : List α} : idxOf a l = length l ↔ a ∉ l := by
  grind

@[simp]
/--
theorem `idxOf_of_notMem` / 定理 `idxOf_of_notMem`

English:
theorem idxOf_of_notMem
  given: {l : List α} {a : α}
  statement: a ∉ l -> idxOf a l = length l
  proof: idxOf_eq_length_iff.2

中文:
定理 idxOf_of_notMem
  条件: {l : 列表 α} {a : α}
  结论: a ∉ l -> idxOf a l = length l
  证明: idxOf_eq_length_iff.2

Depends on / 依赖: idxOf_eq_length_iff
-/
theorem idxOf_of_notMem {l : List α} {a : α} : a ∉ l -> idxOf a l = length l :=
  idxOf_eq_length_iff.2

/--
theorem `idxOf_eq_zero_iff_eq_nil_or_head_eq` / 定理 `idxOf_eq_zero_iff_eq_nil_or_head_eq`

English:
theorem idxOf_eq_zero_iff_eq_nil_or_head_eq
  given: {l : List α} (a : α)
  proof: by
  cases l
  · simp
  · grind

中文:
定理 idxOf_eq_zero_iff_eq_nil_or_head_eq
  条件: {l : 列表 α} (a : α)
  证明: by
  cases l
  · simp
  · grind
-/
theorem idxOf_eq_zero_iff_eq_nil_or_head_eq {l : List α} (a : α) :
    l.idxOf a = 0 ↔ l = [] ∨ l.head? = a := by
  cases l
  · simp
  · grind

/--
theorem `idxOf_eq_zero_iff_head_eq` / 定理 `idxOf_eq_zero_iff_head_eq`

English:
theorem idxOf_eq_zero_iff_head_eq
  given: {l : List α} (hl : l != []) {a : α}
  proof: by
  simp [hl, idxOf_eq_zero_iff_eq_nil_or_head_eq, head?_eq_some_head]

中文:
定理 idxOf_eq_zero_iff_head_eq
  条件: {l : 列表 α} (hl : l != []) {a : α}
  证明: by
  simp [hl, idxOf_eq_zero_iff_eq_nil_or_head_eq, head?_eq_some_head]

Depends on / 依赖: _eq_some_head, idxOf_eq_zero_iff_eq_nil_or_head_eq
-/
theorem idxOf_eq_zero_iff_head_eq {l : List α} (hl : l != []) {a : α} :
    l.idxOf a = 0 ↔ l.head hl = a := by
  simp [hl, idxOf_eq_zero_iff_eq_nil_or_head_eq, head?_eq_some_head]

/--
theorem `idxOf_append_of_mem` / 定理 `idxOf_append_of_mem`

English:
theorem idxOf_append_of_mem
  given: {a : α} (h : a in l₁)
  statement: idxOf a (l₁ ++ l₂) = idxOf a l₁
  proof: by grind

中文:
定理 idxOf_append_of_mem
  条件: {a : α} (h : a in l₁)
  结论: idxOf a (l₁ ++ l₂) = idxOf a l₁
  证明: by grind
-/
theorem idxOf_append_of_mem {a : α} (h : a in l₁) : idxOf a (l₁ ++ l₂) = idxOf a l₁ := by grind

/--
theorem `idxOf_append_of_notMem` / 定理 `idxOf_append_of_notMem`

English:
theorem idxOf_append_of_notMem
  given: {a : α} (h : a ∉ l₁)
  proof: by grind

中文:
定理 idxOf_append_of_notMem
  条件: {a : α} (h : a ∉ l₁)
  证明: by grind
-/
theorem idxOf_append_of_notMem {a : α} (h : a ∉ l₁) :
    idxOf a (l₁ ++ l₂) = l₁.length + idxOf a l₂ := by grind

/--
theorem `IsPrefix.idxOf_le` / 定理 `IsPrefix.idxOf_le`

English:
theorem IsPrefix.idxOf_le
  given: (hl : l₁ <+: l₂) (a : α)
  statement: l₁.idxOf a <= l₂.idxOf a
  proof: by
  obtain ⟨l₃, rfl⟩ := hl
  grind

中文:
定理 IsPrefix.idxOf_le
  条件: (hl : l₁ <+: l₂) (a : α)
  结论: l₁.idxOf a <= l₂.idxOf a
  证明: by
  obtain ⟨l₃, rfl⟩ := hl
  grind
-/
theorem IsPrefix.idxOf_le (hl : l₁ <+: l₂) (a : α) : l₁.idxOf a <= l₂.idxOf a := by
  obtain ⟨l₃, rfl⟩ := hl
  grind

/--
theorem `IsPrefix.idxOf_eq_of_mem` / 定理 `IsPrefix.idxOf_eq_of_mem`

English:
theorem IsPrefix.idxOf_eq_of_mem
  given: (hl : l₁ <+: l₂) {a : α} (ha : a in l₁)
  proof: by
  obtain ⟨l₃, rfl⟩ := hl
.symm exact idxOf_append_of_mem ha

中文:
定理 IsPrefix.idxOf_eq_of_mem
  条件: (hl : l₁ <+: l₂) {a : α} (ha : a in l₁)
  证明: by
  obtain ⟨l₃, rfl⟩ := hl
.symm exact idxOf_append_of_mem ha

Depends on / 依赖: idxOf_append_of_mem
-/
theorem IsPrefix.idxOf_eq_of_mem (hl : l₁ <+: l₂) {a : α} (ha : a in l₁) :
    l₁.idxOf a = l₂.idxOf a := by
  obtain ⟨l₃, rfl⟩ := hl
.symm exact idxOf_append_of_mem ha

/--
theorem `IsPrefix.mem_iff_idxOf_lt_length` / 定理 `IsPrefix.mem_iff_idxOf_lt_length`

English:
theorem IsPrefix.mem_iff_idxOf_lt_length
  given: (hl : l₁ <+: l₂) (a : α)
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact hl.idxOf_eq_of_mem h ▸ idxOf_lt_length_of_mem h
  · have := hl.idxOf_le a
    grind [List.idxOf_lt_length_iff]

中文:
定理 IsPrefix.mem_iff_idxOf_lt_length
  条件: (hl : l₁ <+: l₂) (a : α)
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact hl.idxOf_eq_of_mem h ▸ idxOf_lt_length_of_mem h
  · have := hl.idxOf_le a
    grind [List.idxOf_lt_length_iff]

Depends on / 依赖: List.idxOf_lt_length_iff, hl.idxOf_eq_of_mem, hl.idxOf_le, idxOf_eq_of_mem, idxOf_le, idxOf_lt_length_iff, idxOf_lt_length_of_mem
-/
theorem IsPrefix.mem_iff_idxOf_lt_length (hl : l₁ <+: l₂) (a : α) :
    a in l₁ ↔ l₂.idxOf a < l₁.length := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact hl.idxOf_eq_of_mem h ▸ idxOf_lt_length_of_mem h
  · have := hl.idxOf_le a
    grind [List.idxOf_lt_length_iff]

/--
theorem `IsSuffix.idxOf_le` / 定理 `IsSuffix.idxOf_le`

English:
theorem IsSuffix.idxOf_le
  given: (hl : l₁ <:+ l₂) (a : α)
  proof: by
  obtain ⟨l₃, rfl⟩ := hl
  grind

中文:
定理 IsSuffix.idxOf_le
  条件: (hl : l₁ <:+ l₂) (a : α)
  证明: by
  obtain ⟨l₃, rfl⟩ := hl
  grind
-/
theorem IsSuffix.idxOf_le (hl : l₁ <:+ l₂) (a : α) :
    l₂.idxOf a <= l₂.length - l₁.length + l₁.idxOf a := by
  obtain ⟨l₃, rfl⟩ := hl
  grind

/--
theorem `IsSuffix.idxOf_add_length_le` / 定理 `IsSuffix.idxOf_add_length_le`

English:
theorem IsSuffix.idxOf_add_length_le
  given: (hl : l₁ <:+ l₂) (a : α)
  proof: by
  obtain ⟨l₃, rfl⟩ := hl
  grind

中文:
定理 IsSuffix.idxOf_add_length_le
  条件: (hl : l₁ <:+ l₂) (a : α)
  证明: by
  obtain ⟨l₃, rfl⟩ := hl
  grind
-/
theorem IsSuffix.idxOf_add_length_le (hl : l₁ <:+ l₂) (a : α) :
    l₂.idxOf a + l₁.length <= l₁.idxOf a + l₂.length := by
  obtain ⟨l₃, rfl⟩ := hl
  grind

/--
theorem `mem_take_iff_idxOf_lt` / 定理 `mem_take_iff_idxOf_lt`

English:
theorem mem_take_iff_idxOf_lt
  given: {a : α} {n : Nat} {l : List α} (ha : a in l)
  proof: by
  rw [l.take_prefix n |>.mem_iff_idxOf_lt_length]
  grind

中文:
定理 mem_take_iff_idxOf_lt
  条件: {a : α} {n : 自然数} {l : 列表 α} (ha : a in l)
  证明: by
  rw [l.take_prefix n |>.mem_iff_idxOf_lt_length]
  grind

Depends on / 依赖: l.take_prefix, mem_iff_idxOf_lt_length, take_prefix
-/
theorem mem_take_iff_idxOf_lt {a : α} {n : Nat} {l : List α} (ha : a in l) :
    a in l.take n ↔ l.idxOf a < n := by
  rw [l.take_prefix n |>.mem_iff_idxOf_lt_length]
  grind

/--
theorem `mem_dropLast_iff_idxOf_lt` / 定理 `mem_dropLast_iff_idxOf_lt`

English:
theorem mem_dropLast_iff_idxOf_lt
  given: {l : List α} {a : α} (ha : a in l)
  proof: by
  rw [dropLast_eq_take]; rw [mem_take_iff_idxOf_lt ha]

中文:
定理 mem_dropLast_iff_idxOf_lt
  条件: {l : 列表 α} {a : α} (ha : a in l)
  证明: by
  rw [dropLast_eq_take]; rw [mem_take_iff_idxOf_lt ha]

Depends on / 依赖: dropLast_eq_take, mem_take_iff_idxOf_lt
-/
theorem mem_dropLast_iff_idxOf_lt {l : List α} {a : α} (ha : a in l) :
    a in l.dropLast ↔ l.idxOf a < l.length - 1 := by
  rw [dropLast_eq_take]; rw [mem_take_iff_idxOf_lt ha]

/--
theorem `succ_idxOf_lt_length_of_mem_dropLast` / 定理 `succ_idxOf_lt_length_of_mem_dropLast`

English:
theorem succ_idxOf_lt_length_of_mem_dropLast
  given: {l : List α} {a : α} (ha : a in l.dropLast)
  proof: by
  have := idxOf_lt_length_of_mem ha
  grind [IsPrefix.idxOf_eq_of_mem]

中文:
定理 succ_idxOf_lt_length_of_mem_dropLast
  条件: {l : 列表 α} {a : α} (ha : a in l.dropLast)
  证明: by
  have := idxOf_lt_length_of_mem ha
  grind [IsPrefix.idxOf_eq_of_mem]

Depends on / 依赖: IsPrefix, IsPrefix.idxOf_eq_of_mem, idxOf_eq_of_mem, idxOf_lt_length_of_mem
-/
theorem succ_idxOf_lt_length_of_mem_dropLast {l : List α} {a : α} (ha : a in l.dropLast) :
    l.idxOf a + 1 < l.length := by
  have := idxOf_lt_length_of_mem ha
  grind [IsPrefix.idxOf_eq_of_mem]

/--
theorem `idxOf_getLast` / 定理 `idxOf_getLast`

English:
theorem idxOf_getLast
  given: {l : List α} (hl : l != []) (hl' : l.getLast hl ∉ l.dropLast)
  proof: Nat.le_antisymm (Nat.le_pred_of_lt <| l.idxOf_lt_length_of_mem <| getLast_mem hl) by
    contrapose hl'
    rwa [mem_dropLast_iff_idxOf_lt <| getLast_mem hl, ← Nat.not_le]

中文:
定理 idxOf_getLast
  条件: {l : 列表 α} (hl : l != []) (hl' : l.getLast hl ∉ l.dropLast)
  证明: Nat.le_antisymm (Nat.le_pred_of_lt <| l.idxOf_lt_length_of_mem <| getLast_mem hl) by
    contrapose hl'
    rwa [mem_dropLast_iff_idxOf_lt <| getLast_mem hl, ← Nat.not_le]

Depends on / 依赖: Nat.le_antisymm, Nat.le_pred_of_lt, Nat.not_le, contrapose, getLast_mem, idxOf_lt_length_of_mem, l.idxOf_lt_length_of_mem, le_antisymm, le_pred_of_lt, mem_dropLast_iff_idxOf_lt, not_le
-/
theorem idxOf_getLast {l : List α} (hl : l != []) (hl' : l.getLast hl ∉ l.dropLast) :
    l.idxOf (l.getLast hl) = l.length - 1 :=
Nat.le_antisymm (Nat.le_pred_of_lt <| l.idxOf_lt_length_of_mem <| getLast_mem hl) by
    contrapose hl'
    rwa [mem_dropLast_iff_idxOf_lt <| getLast_mem hl, ← Nat.not_le]

end IndexOf

/-! ### nth element -/

section deprecated

/--
theorem `getElem?_length` / 定理 `getElem?_length`

English:
theorem getElem?_length
  given: (l : List α)
  statement: l[l.length]? = none
  proof: getElem?_eq_none (Nat.le_refl _)

中文:
定理 getElem?_length
  条件: (l : 列表 α)
  结论: l[l.length]? = none
  证明: getElem?_eq_none (Nat.le_refl _)
-/
theorem getElem?_length (l : List α) : l[l.length]? = none := getElem?_eq_none (Nat.le_refl _)

/--
theorem `getElem_map_rev` / 定理 `getElem_map_rev`

English:
theorem getElem_map_rev
  given: (f : α -> β) {l} {n : Nat} {h : n < l.length}
  proof: Eq.symm (getElem_map _)

中文:
定理 getElem_map_rev
  条件: (f : α -> β) {l} {n : 自然数} {h : n < l.length}
  证明: Eq.symm (getElem_map _)

Depends on / 依赖: Eq.symm, getElem_map
-/
theorem getElem_map_rev (f : α -> β) {l} {n : Nat} {h : n < l.length} :
    f l[n] = (map f l)[n]'((l.length_map f).symm ▸ h) := Eq.symm (getElem_map _)

/--
theorem `get_length_sub_one` / 定理 `get_length_sub_one`

English:
theorem get_length_sub_one
  given: {l : List α} (h : l.length - 1 < l.length)
  proof: (getLast_eq_getElem _).symm

中文:
定理 get_length_sub_one
  条件: {l : 列表 α} (h : l.length - 1 < l.length)
  证明: (getLast_eq_getElem _).symm

Depends on / 依赖: getLast_eq_getElem
-/
theorem get_length_sub_one {l : List α} (h : l.length - 1 < l.length) :
    l.get ⟨l.length - 1, h⟩ = l.getLast (by rintro rfl; exact Nat.lt_irrefl 0 h) :=
  (getLast_eq_getElem _).symm

/--
theorem `ext_getElem?'` / 定理 `ext_getElem?'`

English:
theorem ext_getElem?'
  given: {l₁ l₂ : List α} (h' : forall n < max l₁.length l₂.length, l₁[n]? = l₂[n]?)
  proof: by
  apply ext_getElem?
  grind

中文:
定理 ext_getElem?'
  条件: {l₁ l₂ : 列表 α} (h' : 对任意 n < 最大值 l₁.length l₂.length, l₁[n]? = l₂[n]?)
  证明: by
  apply ext_getElem?
  grind

Depends on / 依赖: ext_getElem
-/
theorem ext_getElem?' {l₁ l₂ : List α} (h' : forall n < max l₁.length l₂.length, l₁[n]? = l₂[n]?) :
    l₁ = l₂ := by
  apply ext_getElem?
  grind

/--
theorem `ext_get_iff` / 定理 `ext_get_iff`

English:
theorem ext_get_iff
  given: {l₁ l₂ : List α}
  proof: by
  constructor
  · rintro rfl
    exact ⟨rfl, fun _ _ _ => rfl⟩
  · intro ⟨h₁, h₂⟩
    exact ext_get h₁ h₂

中文:
定理 ext_get_iff
  条件: {l₁ l₂ : 列表 α}
  证明: by
  constructor
  · rintro rfl
    exact ⟨rfl, fun _ _ _ => rfl⟩
  · intro ⟨h₁, h₂⟩
    exact ext_get h₁ h₂

Depends on / 依赖: ext_get
-/
theorem ext_get_iff {l₁ l₂ : List α} :
    l₁ = l₂ ↔ l₁.length = l₂.length ∧ forall n h₁ h₂, get l₁ ⟨n, h₁⟩ = get l₂ ⟨n, h₂⟩ := by
  constructor
  · rintro rfl
    exact ⟨rfl, fun _ _ _ => rfl⟩
  · intro ⟨h₁, h₂⟩
    exact ext_get h₁ h₂

/--
theorem `ext_getElem?_iff'` / 定理 `ext_getElem?_iff'`

English:
theorem ext_getElem?_iff'
  given: {l₁ l₂ : List α}
  statement: l₁ = l₂ ↔
  proof: ⟨by rintro rfl _ _; rfl, ext_getElem?'⟩

中文:
定理 ext_getElem?_iff'
  条件: {l₁ l₂ : 列表 α}
  结论: l₁ = l₂ ↔
  证明: ⟨by rintro rfl _ _; rfl, ext_getElem?'⟩
-/
theorem ext_getElem?_iff' {l₁ l₂ : List α} : l₁ = l₂ ↔
    forall n < max l₁.length l₂.length, l₁[n]? = l₂[n]? :=
  ⟨by rintro rfl _ _; rfl, ext_getElem?'⟩

/--
theorem `ext_getElem!` / 定理 `ext_getElem!`

English:
theorem ext_getElem!
  given: [Inhabited α] (hl : length l₁ = length l₂) (h : forall n : Nat, l₁[n]! = l₂[n]!)
  proof: ext_getElem hl fun n h₁ h₂ => by simpa only [← getElem!_pos] using h n

中文:
定理 ext_getElem!
  条件: [可居 α] (hl : length l₁ = length l₂) (h : 对任意 n : 自然数, l₁[n]! = l₂[n]!)
  证明: ext_getElem hl fun n h₁ h₂ => by simpa only [← getElem!_pos] using h n
-/
theorem ext_getElem! [Inhabited α] (hl : length l₁ = length l₂) (h : forall n : Nat, l₁[n]! = l₂[n]!) :
    l₁ = l₂ :=
  ext_getElem hl fun n h₁ h₂ => by simpa only [← getElem!_pos] using h n

-- This is incorrectly named and should be `get_idxOf`;
-- this already exists, so will require a deprecation dance.
/--
theorem `idxOf_get` / 定理 `idxOf_get`

English:
theorem idxOf_get
  given: [BEq α] [LawfulBEq α] {a : α} {l : List α} (h)
  statement: get l ⟨idxOf a l, h⟩ = a
  proof: by
  simp

@[simp]

中文:
定理 idxOf_get
  条件: [BEq α] [LawfulBEq α] {a : α} {l : 列表 α} (h)
  结论: get l ⟨idxOf a l, h⟩ = a
  证明: by
  simp

@[simp]
-/
theorem idxOf_get [BEq α] [LawfulBEq α] {a : α} {l : List α} (h) : get l ⟨idxOf a l, h⟩ = a := by
  simp

@[simp]
/--
theorem `getElem?_idxOf` / 定理 `getElem?_idxOf`

English:
theorem getElem?_idxOf
  given: [BEq α] [LawfulBEq α] {a : α} {l : List α} (h : a in l)
  proof: by
  rw [getElem?_eq_getElem (idxOf_lt_length_iff.2 h)]; rw [getElem_idxOf]

中文:
定理 getElem?_idxOf
  条件: [BEq α] [LawfulBEq α] {a : α} {l : 列表 α} (h : a in l)
  证明: by
  rw [getElem?_eq_getElem (idxOf_lt_length_iff.2 h)]; rw [getElem_idxOf]
-/
theorem getElem?_idxOf [BEq α] [LawfulBEq α] {a : α} {l : List α} (h : a in l) :
    l[idxOf a l]? = some a := by
  rw [getElem?_eq_getElem (idxOf_lt_length_iff.2 h)]; rw [getElem_idxOf]

/--
theorem `idxOf_inj` / 定理 `idxOf_inj`

English:
theorem idxOf_inj
  given: [BEq α] [LawfulBEq α] {l : List α} {x y : α} (hx : x in l)
  proof: by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  rw [← getElem_idxOf (idxOf_lt_length_iff.mpr hx)]
  simp [h]

中文:
定理 idxOf_inj
  条件: [BEq α] [LawfulBEq α] {l : 列表 α} {x y : α} (hx : x in l)
  证明: by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  rw [← getElem_idxOf (idxOf_lt_length_iff.mpr hx)]
  simp [h]

Depends on / 依赖: getElem_idxOf, idxOf_lt_length_iff, idxOf_lt_length_iff.mpr
-/
theorem idxOf_inj [BEq α] [LawfulBEq α] {l : List α} {x y : α} (hx : x in l) :
    idxOf x l = idxOf y l ↔ x = y := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  rw [← getElem_idxOf (idxOf_lt_length_iff.mpr hx)]
  simp [h]

/--
theorem `get_reverse'` / 定理 `get_reverse'`

English:
theorem get_reverse'
  given: (l : List α) (n) (hn')
  proof: by
  simp

中文:
定理 get_reverse'
  条件: (l : 列表 α) (n) (hn')
  证明: by
  simp
-/
theorem get_reverse' (l : List α) (n) (hn') :
    l.reverse.get n = l.get ⟨l.length - 1 - n, hn'⟩ := by
  simp

/--
theorem `eq_cons_of_length_one` / 定理 `eq_cons_of_length_one`

English:
theorem eq_cons_of_length_one
  given: {l : List α} (h : l.length = 1)
  statement: l = [l.get ⟨0, by lia⟩]
  proof: by
  refine ext_get (by convert! h) (by grind)

中文:
定理 eq_cons_of_length_one
  条件: {l : 列表 α} (h : l.length = 1)
  结论: l = [l.get ⟨0, by lia⟩]
  证明: by
  refine ext_get (by convert! h) (by grind)

Depends on / 依赖: convert, ext_get
-/
theorem eq_cons_of_length_one {l : List α} (h : l.length = 1) : l = [l.get ⟨0, by lia⟩] := by
  refine ext_get (by convert! h) (by grind)

end deprecated

/--
theorem `getElem_set_of_ne` / 定理 `getElem_set_of_ne`

English:
theorem getElem_set_of_ne
  statement: {l : List α} {i j : Nat} (h : i != j) (a : α)
  proof: by
  simp [h]

中文:
定理 getElem_set_of_ne
  结论: {l : 列表 α} {i j : 自然数} (h : i != j) (a : α)
  证明: by
  simp [h]
-/
theorem getElem_set_of_ne {l : List α} {i j : Nat} (h : i != j) (a : α)
    (hj : j < (l.set i a).length) :
    (l.set i a)[j] = l[j]'(by simpa using hj) := by
  simp [h]

/-! ### map -/

-- `List.map_const` (the version with `Function.const` instead of a lambda) is already tagged
-- `simp` in Core
-- TODO: Upstream the tagging to Core?
attribute [simp] map_const'

/--
theorem `flatMap_pure_eq_map` / 定理 `flatMap_pure_eq_map`

English:
theorem flatMap_pure_eq_map
  given: (f : α -> β) (l : List α)
  statement: l.flatMap (pure ∘ f) = map f l
  proof: .symm map_eq_flatMap ..

中文:
定理 flatMap_pure_eq_map
  条件: (f : α -> β) (l : 列表 α)
  结论: l.flatMap (pure ∘ f) = map f l
  证明: .symm map_eq_flatMap ..

Depends on / 依赖: map_eq_flatMap
-/
theorem flatMap_pure_eq_map (f : α -> β) (l : List α) : l.flatMap (pure ∘ f) = map f l :=
.symm map_eq_flatMap ..

/--
theorem `flatMap_congr` / 定理 `flatMap_congr`

English:
theorem flatMap_congr
  given: {l : List α} {f g : α -> List β} (h : forall x in l, f x = g x)
  proof: (congr_arg List.flatten <| map_congr_left h :)

中文:
定理 flatMap_congr
  条件: {l : 列表 α} {f g : α -> 列表 β} (h : 对任意 x in l, f x = g x)
  证明: (congr_arg List.flatten <| map_congr_left h :)

Depends on / 依赖: List.flatten, congr_arg, flatten, map_congr_left
-/
theorem flatMap_congr {l : List α} {f g : α -> List β} (h : forall x in l, f x = g x) :
    l.flatMap f = l.flatMap g :=
  (congr_arg List.flatten <| map_congr_left h :)

/--
theorem `infix_flatMap_of_mem` / 定理 `infix_flatMap_of_mem`

English:
theorem infix_flatMap_of_mem
  given: {a : α} {as : List α} (h : a in as) (f : α -> List α)
  proof: infix_of_mem_flatten (mem_map_of_mem h)

@[simp]

中文:
定理 infix_flatMap_of_mem
  条件: {a : α} {as : 列表 α} (h : a in as) (f : α -> 列表 α)
  证明: infix_of_mem_flatten (mem_map_of_mem h)

@[simp]

Depends on / 依赖: infix_of_mem_flatten, mem_map_of_mem
-/
theorem infix_flatMap_of_mem {a : α} {as : List α} (h : a in as) (f : α -> List α) :
    f a <:+: as.flatMap f :=
  infix_of_mem_flatten (mem_map_of_mem h)

@[simp]
/--
theorem `map_eq_map` / 定理 `map_eq_map`

English:
theorem map_eq_map
  given: {α β} (f : α -> β) (l : List α)
  statement: f < > l = map f l
  proof: rfl

中文:
定理 map_eq_map
  条件: {α β} (f : α -> β) (l : 列表 α)
  结论: f < > l = map f l
  证明: rfl
-/
theorem map_eq_map {α β} (f : α -> β) (l : List α) : f < > l = map f l :=
  rfl

/--
theorem `comp_map` / 定理 `comp_map`

English:
theorem comp_map
  given: (h : β -> γ) (g : α -> β) (l : List α)
  statement: map (h ∘ g) l = map h (map g l)
  proof: map_map.symm

中文:
定理 comp_map
  条件: (h : β -> γ) (g : α -> β) (l : 列表 α)
  结论: map (h ∘ g) l = map h (map g l)
  证明: map_map.symm

Depends on / 依赖: map_map, map_map.symm
-/
theorem comp_map (h : β -> γ) (g : α -> β) (l : List α) : map (h ∘ g) l = map h (map g l) :=
  map_map.symm

/-- Composing a `List.map` with another `List.map` is equal to
a single `List.map` of composed functions.
-/
@[simp]
/--
theorem `map_comp_map` / 定理 `map_comp_map`

English:
theorem map_comp_map
  given: (g : β -> γ) (f : α -> β)
  statement: map g ∘ map f = map (g ∘ f)
  proof: by
  ext l; rw [comp_map, Function.comp_apply]

中文:
定理 map_comp_map
  条件: (g : β -> γ) (f : α -> β)
  结论: map g ∘ map f = map (g ∘ f)
  证明: by
  ext l; rw [comp_map, Function.comp_apply]

Depends on / 依赖: Function, Function.comp_apply, comp_apply, comp_map
-/
theorem map_comp_map (g : β -> γ) (f : α -> β) : map g ∘ map f = map (g ∘ f) := by
  ext l; rw [comp_map, Function.comp_apply]

section map_bijectivity

/--
theorem `_root_.Function.LeftInverse.list_map` / 定理 `_root_.Function.LeftInverse.list_map`

English:
theorem _root_.Function.LeftInverse.list_map
  given: {f : α -> β} {g : β -> α} (h : LeftInverse f g)
  proof: h.list_map

nonrec theorem _root_.Function.Involutive.list_map {f : α -> α}
    (h : Involutive f) : Involutive (map f) :=
  Function.LeftInverse.list_map h

@[simp]

中文:
定理 _root_.函数.左逆.list_map
  条件: {f : α -> β} {g : β -> α} (h : 左逆 f g)
  证明: h.list_map

nonrec theorem _root_.Function.Involutive.list_map {f : α -> α}
    (h : Involutive f) : Involutive (map f) :=
  Function.LeftInverse.list_map h

@[simp]

Depends on / 依赖: h.list_map, list_map
-/
theorem _root_.Function.LeftInverse.list_map {f : α -> β} {g : β -> α} (h : LeftInverse f g) :
    LeftInverse (map f) (map g)
  | [] => by simp_rw [map_nil]
  | x :: xs => by simp_rw [map_cons, h x, h.list_map xs]

nonrec theorem _root_.Function.RightInverse.list_map {f : α -> β} {g : β -> α}
    (h : RightInverse f g) : RightInverse (map f) (map g) :=
  h.list_map

nonrec theorem _root_.Function.Involutive.list_map {f : α -> α}
    (h : Involutive f) : Involutive (map f) :=
  Function.LeftInverse.list_map h

@[simp]
/--
theorem `map_leftInverse_iff` / 定理 `map_leftInverse_iff`

English:
theorem map_leftInverse_iff
  given: {f : α -> β} {g : β -> α}
  proof: ⟨fun h x => by injection h [x], (·.list_map)⟩

@[simp]

中文:
定理 map_leftInverse_iff
  条件: {f : α -> β} {g : β -> α}
  证明: ⟨fun h x => by injection h [x], (·.list_map)⟩

@[simp]

Depends on / 依赖: Nonempty, Set.Nonempty.image, injection, list_map, of_subtype, to_subtype
-/
theorem map_leftInverse_iff {f : α -> β} {g : β -> α} :
    LeftInverse (map f) (map g) ↔ LeftInverse f g :=
  ⟨fun h x => by injection h [x], (·.list_map)⟩

@[simp]
/--
theorem `map_rightInverse_iff` / 定理 `map_rightInverse_iff`

English:
theorem map_rightInverse_iff
  given: {f : α -> β} {g : β -> α}
  proof: map_leftInverse_iff

@[simp]

中文:
定理 map_rightInverse_iff
  条件: {f : α -> β} {g : β -> α}
  证明: map_leftInverse_iff

@[simp]

Depends on / 依赖: map_leftInverse_iff
-/
theorem map_rightInverse_iff {f : α -> β} {g : β -> α} :
    RightInverse (map f) (map g) ↔ RightInverse f g := map_leftInverse_iff

@[simp]
/--
theorem `map_involutive_iff` / 定理 `map_involutive_iff`

English:
theorem map_involutive_iff
  given: {f : α -> α}
  proof: map_leftInverse_iff

中文:
定理 map_involutive_iff
  条件: {f : α -> α}
  证明: map_leftInverse_iff

Depends on / 依赖: map_leftInverse_iff
-/
theorem map_involutive_iff {f : α -> α} :
    Involutive (map f) ↔ Involutive f := map_leftInverse_iff

/--
theorem `_root_.Function.Injective.list_map` / 定理 `_root_.Function.Injective.list_map`

English:
theorem _root_.Function.Injective.list_map
  given: {f : α -> β} (h : Injective f)

中文:
定理 _root_.函数.单射.list_map
  条件: {f : α -> β} (h : 单射 f)
-/
theorem _root_.Function.Injective.list_map {f : α -> β} (h : Injective f) :
    Injective (map f)
  | [], [], _ => rfl
  | x :: xs, y :: ys, hxy => by
    injection hxy with hxy hxys
    rw [h hxy]; rw [h.list_map hxys]

@[simp]
/--
theorem `map_injective_iff` / 定理 `map_injective_iff`

English:
theorem map_injective_iff
  given: {f : α -> β}
  statement: Injective (map f) ↔ Injective f
  proof: by
  refine ⟨fun h x y hxy => ?_, (·.list_map)⟩
  suffices [x] = [y] by simpa using this
  apply h
  simp [hxy]

中文:
定理 map_injective_iff
  条件: {f : α -> β}
  结论: 单射 (map f) ↔ 单射 f
  证明: by
  refine ⟨fun h x y hxy => ?_, (·.list_map)⟩
  suffices [x] = [y] by simpa using this
  apply h
  simp [hxy]

Depends on / 依赖: list_map
-/
theorem map_injective_iff {f : α -> β} : Injective (map f) ↔ Injective f := by
  refine ⟨fun h x y hxy => ?_, (·.list_map)⟩
  suffices [x] = [y] by simpa using this
  apply h
  simp [hxy]

/--
theorem `_root_.Function.Surjective.list_map` / 定理 `_root_.Function.Surjective.list_map`

English:
theorem _root_.Function.Surjective.list_map
  given: {f : α -> β} (h : Surjective f)
  proof: let ⟨_, h⟩ := h.hasRightInverse; h.list_map.surjective

@[simp]

中文:
定理 _root_.函数.满射.list_map
  条件: {f : α -> β} (h : 满射 f)
  证明: let ⟨_, h⟩ := h.hasRightInverse; h.list_map.surjective

@[simp]

Depends on / 依赖: h.hasRightInverse, h.list_map.surjective, hasRightInverse, list_map, surjective
-/
theorem _root_.Function.Surjective.list_map {f : α -> β} (h : Surjective f) :
    Surjective (map f) :=
  let ⟨_, h⟩ := h.hasRightInverse; h.list_map.surjective

@[simp]
/--
theorem `map_surjective_iff` / 定理 `map_surjective_iff`

English:
theorem map_surjective_iff
  given: {f : α -> β}
  statement: Surjective (map f) ↔ Surjective f
  proof: by
  refine ⟨fun h x => ?_, (·.list_map)⟩
  let ⟨[y], hxy⟩ := h [x]
  exact ⟨_, List.singleton_injective hxy⟩

中文:
定理 map_surjective_iff
  条件: {f : α -> β}
  结论: 满射 (map f) ↔ 满射 f
  证明: by
  refine ⟨fun h x => ?_, (·.list_map)⟩
  let ⟨[y], hxy⟩ := h [x]
  exact ⟨_, List.singleton_injective hxy⟩

Depends on / 依赖: List.singleton_injective, list_map, singleton_injective
-/
theorem map_surjective_iff {f : α -> β} : Surjective (map f) ↔ Surjective f := by
  refine ⟨fun h x => ?_, (·.list_map)⟩
  let ⟨[y], hxy⟩ := h [x]
  exact ⟨_, List.singleton_injective hxy⟩

/--
theorem `_root_.Function.Bijective.list_map` / 定理 `_root_.Function.Bijective.list_map`

English:
theorem _root_.Function.Bijective.list_map
  given: {f : α -> β} (h : Bijective f)
  statement: Bijective (map f)
  proof: ⟨h.1.list_map, h.2.list_map⟩

@[simp]

中文:
定理 _root_.函数.双射.list_map
  条件: {f : α -> β} (h : 双射 f)
  结论: 双射 (map f)
  证明: ⟨h.1.list_map, h.2.list_map⟩

@[simp]

Depends on / 依赖: list_map
-/
theorem _root_.Function.Bijective.list_map {f : α -> β} (h : Bijective f) : Bijective (map f) :=
  ⟨h.1.list_map, h.2.list_map⟩

@[simp]
/--
theorem `map_bijective_iff` / 定理 `map_bijective_iff`

English:
theorem map_bijective_iff
  given: {f : α -> β}
  statement: Bijective (map f) ↔ Bijective f
  proof: by
  simp_rw [Function.Bijective, map_injective_iff, map_surjective_iff]

中文:
定理 map_bijective_iff
  条件: {f : α -> β}
  结论: 双射 (map f) ↔ 双射 f
  证明: by
  simp_rw [Function.Bijective, map_injective_iff, map_surjective_iff]

Depends on / 依赖: Bijective, Function, Function.Bijective, map_injective_iff, map_surjective_iff, simp_rw
-/
theorem map_bijective_iff {f : α -> β} : Bijective (map f) ↔ Bijective f := by
  simp_rw [Function.Bijective, map_injective_iff, map_surjective_iff]

end map_bijectivity

/--
theorem `eq_of_mem_map_const` / 定理 `eq_of_mem_map_const`

English:
theorem eq_of_mem_map_const
  given: {b₁ b₂ : β} {l : List α} (h : b₁ in map (const α b₂) l)
  proof: by rw [map_const] at h; exact eq_of_mem_replicate h

中文:
定理 eq_of_mem_map_const
  条件: {b₁ b₂ : β} {l : 列表 α} (h : b₁ in map (const α b₂) l)
  证明: by rw [map_const] at h; exact eq_of_mem_replicate h

Depends on / 依赖: eq_of_mem_replicate, map_const
-/
theorem eq_of_mem_map_const {b₁ b₂ : β} {l : List α} (h : b₁ in map (const α b₂) l) :
    b₁ = b₂ := by rw [map_const] at h; exact eq_of_mem_replicate h

/--
lemma `eq_nil_or_concat'` / 引理 `eq_nil_or_concat'`

English:
lemma eq_nil_or_concat'
  given: (l : List α)
  statement: l = [] ∨ exists L b, l = L ++ [b]
  proof: by
  simpa using l.eq_nil_or_concat

中文:
引理 eq_nil_or_concat'
  条件: (l : 列表 α)
  结论: l = [] ∨ 存在 L b, l = L ++ [b]
  证明: by
  simpa using l.eq_nil_or_concat

Depends on / 依赖: eq_nil_or_concat, l.eq_nil_or_concat
-/
lemma eq_nil_or_concat' (l : List α) : l = [] ∨ exists L b, l = L ++ [b] := by
  simpa using l.eq_nil_or_concat


/--
theorem `foldl_ext` / 定理 `foldl_ext`

English:
theorem foldl_ext
  given: (f g : α -> β -> α) (a : α) {l : List β} (H : forall a : α, forall b in l, f a b = g a b)
  proof: by
  induction l generalizing a with
  | nil => rfl
  | cons hd tl ih =>
    unfold foldl
    rw [ih _ fun a b bin => H a b <| mem_cons_of_mem _ bin]; rw [H a hd mem_cons_self]

中文:
定理 foldl_ext
  条件: (f g : α -> β -> α) (a : α) {l : 列表 β} (H : 对任意 a : α, 对任意 b in l, f a b = g a b)
  证明: by
  induction l generalizing a with
  | nil => rfl
  | cons hd tl ih =>
    unfold foldl
    rw [ih _ fun a b bin => H a b <| mem_cons_of_mem _ bin]; rw [H a hd mem_cons_self]

Depends on / 依赖: generalizing, mem_cons_of_mem, mem_cons_self
-/
theorem foldl_ext (f g : α -> β -> α) (a : α) {l : List β} (H : forall a : α, forall b in l, f a b = g a b) :
    foldl f a l = foldl g a l := by
  induction l generalizing a with
  | nil => rfl
  | cons hd tl ih =>
    unfold foldl
    rw [ih _ fun a b bin => H a b <| mem_cons_of_mem _ bin]; rw [H a hd mem_cons_self]

/--
theorem `foldr_ext` / 定理 `foldr_ext`

English:
theorem foldr_ext
  given: (f g : α -> β -> β) (b : β) {l : List α} (H : forall a in l, forall b : β, f a b = g a b)
  proof: by
  induction l with | nil => rfl | cons hd tl ih => ?_
  simp only [mem_cons, or_imp, forall_and, forall_eq] at H
  simp only [foldr, ih H.2, H.1]

中文:
定理 foldr_ext
  条件: (f g : α -> β -> β) (b : β) {l : 列表 α} (H : 对任意 a in l, 对任意 b : β, f a b = g a b)
  证明: by
  induction l with | nil => rfl | cons hd tl ih => ?_
  simp only [mem_cons, or_imp, forall_and, forall_eq] at H
  simp only [foldr, ih H.2, H.1]

Depends on / 依赖: forall_and, forall_eq, mem_cons, or_imp
-/
theorem foldr_ext (f g : α -> β -> β) (b : β) {l : List α} (H : forall a in l, forall b : β, f a b = g a b) :
    foldr f b l = foldr g b l := by
  induction l with | nil => rfl | cons hd tl ih => ?_
  simp only [mem_cons, or_imp, forall_and, forall_eq] at H
  simp only [foldr, ih H.2, H.1]

/--
theorem `foldl_concat` / 定理 `foldl_concat`

English:
theorem foldl_concat
  proof: by
  simp only [List.foldl_append, List.foldl]

中文:
定理 foldl_concat
  证明: by
  simp only [List.foldl_append, List.foldl]

Depends on / 依赖: List.foldl, List.foldl_append, foldl_append
-/
theorem foldl_concat
    (f : β -> α -> β) (b : β) (x : α) (xs : List α) :
    List.foldl f b (xs ++ [x]) = f (List.foldl f b xs) x := by
  simp only [List.foldl_append, List.foldl]

/--
theorem `foldr_concat` / 定理 `foldr_concat`

English:
theorem foldr_concat
  proof: by
  simp only [List.foldr_append, List.foldr]

中文:
定理 foldr_concat
  证明: by
  simp only [List.foldr_append, List.foldr]

Depends on / 依赖: List.foldr, List.foldr_append, foldr_append
-/
theorem foldr_concat
    (f : α -> β -> β) (b : β) (x : α) (xs : List α) :
    List.foldr f b (xs ++ [x]) = (List.foldr f (f x b) xs) := by
  simp only [List.foldr_append, List.foldr]

/--
theorem `foldl_fixed'` / 定理 `foldl_fixed'`

English:
theorem foldl_fixed'
  given: {f : α -> β -> α} {a : α} (hf : forall b, f a b = a)
  statement: forall l : List β, foldl f a l = a

中文:
定理 foldl_fixed'
  条件: {f : α -> β -> α} {a : α} (hf : 对任意 b, f a b = a)
  结论: 对任意 l : 列表 β, foldl f a l = a
-/
theorem foldl_fixed' {f : α -> β -> α} {a : α} (hf : forall b, f a b = a) : forall l : List β, foldl f a l = a
  | [] => rfl
  | b :: l => by rw [foldl_cons, hf b, foldl_fixed' hf l]

/--
theorem `foldr_fixed'` / 定理 `foldr_fixed'`

English:
theorem foldr_fixed'
  given: {f : α -> β -> β} {b : β} (hf : forall a, f a b = b)
  statement: forall l : List α, foldr f b l = b

中文:
定理 foldr_fixed'
  条件: {f : α -> β -> β} {b : β} (hf : 对任意 a, f a b = b)
  结论: 对任意 l : 列表 α, foldr f b l = b
-/
theorem foldr_fixed' {f : α -> β -> β} {b : β} (hf : forall a, f a b = b) : forall l : List α, foldr f b l = b
  | [] => rfl
  | a :: l => by rw [foldr_cons, foldr_fixed' hf l, hf a]

@[simp]
/--
theorem `foldl_fixed` / 定理 `foldl_fixed`

English:
theorem foldl_fixed
  given: {a : α}
  statement: forall l : List β, foldl (fun a _ => a) a l = a
  proof: foldl_fixed' fun _ => rfl

@[simp]

中文:
定理 foldl_fixed
  条件: {a : α}
  结论: 对任意 l : 列表 β, foldl (fun a _ => a) a l = a
  证明: foldl_fixed' fun _ => rfl

@[simp]

Depends on / 依赖: foldl_fixed
-/
theorem foldl_fixed {a : α} : forall l : List β, foldl (fun a _ => a) a l = a :=
  foldl_fixed' fun _ => rfl

@[simp]
/--
theorem `foldr_fixed` / 定理 `foldr_fixed`

English:
theorem foldr_fixed
  given: {b : β}
  statement: forall l : List α, foldr (fun _ b => b) b l = b
  proof: foldr_fixed' fun _ => rfl

中文:
定理 foldr_fixed
  条件: {b : β}
  结论: 对任意 l : 列表 α, foldr (fun _ b => b) b l = b
  证明: foldr_fixed' fun _ => rfl

Depends on / 依赖: foldr_fixed
-/
theorem foldr_fixed {b : β} : forall l : List α, foldr (fun _ b => b) b l = b :=
  foldr_fixed' fun _ => rfl

/--
theorem `reverse_foldl` / 定理 `reverse_foldl`

English:
theorem reverse_foldl
  given: {l : List α}
  statement: reverse (foldl (fun t h => h :: t) [] l) = l
  proof: by
  simp

中文:
定理 reverse_foldl
  条件: {l : 列表 α}
  结论: reverse (foldl (fun t h => h :: t) [] l) = l
  证明: by
  simp
-/
theorem reverse_foldl {l : List α} : reverse (foldl (fun t h => h :: t) [] l) = l := by
  simp

/--
theorem `foldl_hom₂` / 定理 `foldl_hom₂`

English:
theorem foldl_hom₂
  statement: (l : List ι) (f : α -> β -> γ) (op₁ : α -> ι -> α) (op₂ : β -> ι -> β)
  proof: Eq.symm by
    revert a b
    induction l <;> intros <;> [rfl; simp only [*, foldl]]

中文:
定理 foldl_hom₂
  结论: (l : 列表 ι) (f : α -> β -> γ) (op₁ : α -> ι -> α) (op₂ : β -> ι -> β)
  证明: Eq.symm by
    revert a b
    induction l <;> intros <;> [rfl; simp only [*, foldl]]

Depends on / 依赖: Eq.symm, intros, revert
-/
theorem foldl_hom₂ (l : List ι) (f : α -> β -> γ) (op₁ : α -> ι -> α) (op₂ : β -> ι -> β)
    (op₃ : γ -> ι -> γ) (a : α) (b : β) (h : forall a b i, f (op₁ a i) (op₂ b i) = op₃ (f a b) i) :
    foldl op₃ (f a b) l = f (foldl op₁ a l) (foldl op₂ b l) :=
Eq.symm by
    revert a b
    induction l <;> intros <;> [rfl; simp only [*, foldl]]

/--
theorem `foldr_hom₂` / 定理 `foldr_hom₂`

English:
theorem foldr_hom₂
  statement: (l : List ι) (f : α -> β -> γ) (op₁ : ι -> α -> α) (op₂ : ι -> β -> β)
  proof: by
  revert a
  induction l <;> intros <;> [rfl; simp only [*, foldr]]

中文:
定理 foldr_hom₂
  结论: (l : 列表 ι) (f : α -> β -> γ) (op₁ : ι -> α -> α) (op₂ : ι -> β -> β)
  证明: by
  revert a
  induction l <;> intros <;> [rfl; simp only [*, foldr]]

Depends on / 依赖: intros, revert
-/
theorem foldr_hom₂ (l : List ι) (f : α -> β -> γ) (op₁ : ι -> α -> α) (op₂ : ι -> β -> β)
    (op₃ : ι -> γ -> γ) (a : α) (b : β) (h : forall a b i, f (op₁ i a) (op₂ i b) = op₃ i (f a b)) :
    foldr op₃ (f a b) l = f (foldr op₁ a l) (foldr op₂ b l) := by
  revert a
  induction l <;> intros <;> [rfl; simp only [*, foldr]]

/--
theorem `injective_foldl_comp` / 定理 `injective_foldl_comp`

English:
theorem injective_foldl_comp
  statement: {l : List (α -> α)} {f : α -> α}
  proof: by
  induction l generalizing f with
  | nil => exact hf
  | cons lh lt l_ih =>
    apply l_ih fun _ h => hl _ (List.mem_cons_of_mem _ h)
    apply Function.Injective.comp hf
    apply hl _ mem_cons_self

中文:
定理 injective_foldl_comp
  结论: {l : 列表 (α -> α)} {f : α -> α}
  证明: by
  induction l generalizing f with
  | nil => exact hf
  | cons lh lt l_ih =>
    apply l_ih fun _ h => hl _ (List.mem_cons_of_mem _ h)
    apply Function.Injective.comp hf
    apply hl _ mem_cons_self

Depends on / 依赖: Function, Function.Injective.comp, Injective, List.mem_cons_of_mem, generalizing, l_ih, mem_cons_of_mem, mem_cons_self
-/
theorem injective_foldl_comp {l : List (α -> α)} {f : α -> α}
    (hl : forall f in l, Function.Injective f) (hf : Function.Injective f) :
    Function.Injective (@List.foldl (α -> α) (α -> α) Function.comp f l) := by
  induction l generalizing f with
  | nil => exact hf
  | cons lh lt l_ih =>
    apply l_ih fun _ h => hl _ (List.mem_cons_of_mem _ h)
    apply Function.Injective.comp hf
    apply hl _ mem_cons_self

/--
lemma `append_cons_inj_of_notMem` / 引理 `append_cons_inj_of_notMem`

English:
lemma append_cons_inj_of_notMem
  statement: {x₁ x₂ z₁ z₂ : List α} {a₁ a₂ : α}
  proof: by
  constructor
  · simp only [append_eq_append_iff, cons_eq_append_iff, cons_eq_cons]
    rintro (⟨c, rfl, ⟨rfl, rfl, rfl⟩ | ⟨d, rfl, rfl⟩⟩ |
      ⟨c, rfl, ⟨rfl, rfl, rfl⟩ | ⟨d, rfl, rfl⟩⟩) <;> simp_all
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

中文:
引理 append_cons_inj_of_notMem
  结论: {x₁ x₂ z₁ z₂ : 列表 α} {a₁ a₂ : α}
  证明: by
  constructor
  · simp only [append_eq_append_iff, cons_eq_append_iff, cons_eq_cons]
    rintro (⟨c, rfl, ⟨rfl, rfl, rfl⟩ | ⟨d, rfl, rfl⟩⟩ |
      ⟨c, rfl, ⟨rfl, rfl, rfl⟩ | ⟨d, rfl, rfl⟩⟩) <;> simp_all
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

Depends on / 依赖: append_eq_append_iff, cons_eq_append_iff, cons_eq_cons
-/
lemma append_cons_inj_of_notMem {x₁ x₂ z₁ z₂ : List α} {a₁ a₂ : α}
    (notin_x : a₂ ∉ x₁) (notin_z : a₂ ∉ z₁) :
    x₁ ++ a₁ :: z₁ = x₂ ++ a₂ :: z₂ ↔ x₁ = x₂ ∧ a₁ = a₂ ∧ z₁ = z₂ := by
  constructor
  · simp only [append_eq_append_iff, cons_eq_append_iff, cons_eq_cons]
    rintro (⟨c, rfl, ⟨rfl, rfl, rfl⟩ | ⟨d, rfl, rfl⟩⟩ |
      ⟨c, rfl, ⟨rfl, rfl, rfl⟩ | ⟨d, rfl, rfl⟩⟩) <;> simp_all
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

/-! ### foldlM, foldrM, mapM -/

section FoldlMFoldrM

variable {m : Type v -> Type w} [Monad m]

variable [LawfulMonad m]

/--
theorem `foldrM_eq_foldr` / 定理 `foldrM_eq_foldr`

English:
theorem foldrM_eq_foldr
  given: (f : α -> β -> m β) (b l)
  proof: by induction l <;> simp [*]

中文:
定理 foldrM_eq_foldr
  条件: (f : α -> β -> m β) (b l)
  证明: by induction l <;> simp [*]
-/
theorem foldrM_eq_foldr (f : α -> β -> m β) (b l) :
    foldrM f b l = foldr (fun a mb => mb >>= f a) (pure b) l := by induction l <;> simp [*]

/--
theorem `foldlM_eq_foldl` / 定理 `foldlM_eq_foldl`

English:
theorem foldlM_eq_foldl
  given: (f : β -> α -> m β) (b l)
  proof: by
  suffices h :
    forall mb : m β, (mb >>= fun b => List.foldlM f b l) = foldl (fun mb a => mb >>= fun b => f b a) mb l
    by simp [← h (pure b)]
  induction l with
  | nil => simp
  | cons _ _ l_ih => intro; simp only [List.foldlM, foldl, ← l_ih, functor_norm]

中文:
定理 foldlM_eq_foldl
  条件: (f : β -> α -> m β) (b l)
  证明: by
  suffices h :
    forall mb : m β, (mb >>= fun b => List.foldlM f b l) = foldl (fun mb a => mb >>= fun b => f b a) mb l
    by simp [← h (pure b)]
  induction l with
  | nil => simp
  | cons _ _ l_ih => intro; simp only [List.foldlM, foldl, ← l_ih, functor_norm]

Depends on / 依赖: List.foldlM, foldlM, functor_norm, l_ih
-/
theorem foldlM_eq_foldl (f : β -> α -> m β) (b l) :
    List.foldlM f b l = foldl (fun mb a => mb >>= fun b => f b a) (pure b) l := by
  suffices h :
    forall mb : m β, (mb >>= fun b => List.foldlM f b l) = foldl (fun mb a => mb >>= fun b => f b a) mb l
    by simp [← h (pure b)]
  induction l with
  | nil => simp
  | cons _ _ l_ih => intro; simp only [List.foldlM, foldl, ← l_ih, functor_norm]

end FoldlMFoldrM


/--
theorem `length_eq_length_filter_add` / 定理 `length_eq_length_filter_add`

English:
theorem length_eq_length_filter_add
  given: {l : List (α)} (f : α -> Bool)
  proof: by
  simp_rw [← List.countP_eq_length_filter, l.length_eq_countP_add_countP f, Bool.not_eq_true,
    Bool.decide_eq_false]

中文:
定理 length_eq_length_filter_add
  条件: {l : 列表 (α)} (f : α -> 布尔值)
  证明: by
  simp_rw [← List.countP_eq_length_filter, l.length_eq_countP_add_countP f, Bool.not_eq_true,
    Bool.decide_eq_false]

Depends on / 依赖: Bool.decide_eq_false, Bool.not_eq_true, List.countP_eq_length_filter, countP_eq_length_filter, decide_eq_false, l.length_eq_countP_add_countP, length_eq_countP_add_countP, not_eq_true, simp_rw
-/
theorem length_eq_length_filter_add {l : List (α)} (f : α -> Bool) :
    l.length = (l.filter f).length + (l.filter (!f ·)).length := by
  simp_rw [← List.countP_eq_length_filter, l.length_eq_countP_add_countP f, Bool.not_eq_true,
    Bool.decide_eq_false]


/--
theorem `filterMap_eq_flatMap_toList` / 定理 `filterMap_eq_flatMap_toList`

English:
theorem filterMap_eq_flatMap_toList
  given: (f : α -> Option β) (l : List α)
  proof: by
  induction l with | nil => ?_ | cons a l ih => ?_ <;> simp [filterMap_cons]
  rcases f a <;> simp [ih]

@[congr]

中文:
定理 filterMap_eq_flatMap_toList
  条件: (f : α -> 选项类型 β) (l : 列表 α)
  证明: by
  induction l with | nil => ?_ | cons a l ih => ?_ <;> simp [filterMap_cons]
  rcases f a <;> simp [ih]

@[congr]

Depends on / 依赖: filterMap_cons
-/
theorem filterMap_eq_flatMap_toList (f : α -> Option β) (l : List α) :
    l.filterMap f = l.flatMap fun a => (f a).toList := by
  induction l with | nil => ?_ | cons a l ih => ?_ <;> simp [filterMap_cons]
  rcases f a <;> simp [ih]

@[congr]
/--
theorem `filterMap_congr` / 定理 `filterMap_congr`

English:
theorem filterMap_congr
  statement: {f g : α -> Option β} {l : List α}
  proof: by
  induction l <;> simp_all [filterMap_cons]

中文:
定理 filterMap_congr
  结论: {f g : α -> 选项类型 β} {l : 列表 α}
  证明: by
  induction l <;> simp_all [filterMap_cons]

Depends on / 依赖: filterMap_cons
-/
theorem filterMap_congr {f g : α -> Option β} {l : List α}
    (h : forall x in l, f x = g x) : l.filterMap f = l.filterMap g := by
  induction l <;> simp_all [filterMap_cons]

/--
theorem `filterMap_eq_map_iff_forall_eq_some` / 定理 `filterMap_eq_map_iff_forall_eq_some`

English:
theorem filterMap_eq_map_iff_forall_eq_some
  given: {f : α -> Option β} {g : α -> β} {l : List α}
  proof: by
    induction l with | nil => simp | cons a l ih => ?_
    rcases ha : f a with - | b
    · intro h
      have : (filterMap f l).length = l.length + 1 := by grind
      grind
    · simp +contextual [ha, ih]
  mpr h := Eq.trans (filterMap_congr <| by simpa) (congr_fun filterMap_eq_map _)

@[simp]

中文:
定理 filterMap_eq_map_iff_对任意_eq_some
  条件: {f : α -> 选项类型 β} {g : α -> β} {l : 列表 α}
  证明: by
    induction l with | nil => simp | cons a l ih => ?_
    rcases ha : f a with - | b
    · intro h
      have : (filterMap f l).length = l.length + 1 := by grind
      grind
    · simp +contextual [ha, ih]
  mpr h := Eq.trans (filterMap_congr <| by simpa) (congr_fun filterMap_eq_map _)

@[simp]

Depends on / 依赖: Eq.trans, congr_fun, contextual, filterMap, filterMap_congr, filterMap_eq_map, l.length, length
-/
theorem filterMap_eq_map_iff_forall_eq_some {f : α -> Option β} {g : α -> β} {l : List α} :
    l.filterMap f = l.map g ↔ forall x in l, f x = some (g x) where
  mp := by
    induction l with | nil => simp | cons a l ih => ?_
    rcases ha : f a with - | b
    · intro h
      have : (filterMap f l).length = l.length + 1 := by grind
      grind
    · simp +contextual [ha, ih]
  mpr h := Eq.trans (filterMap_congr <| by simpa) (congr_fun filterMap_eq_map _)

@[simp]
/--
lemma `filterMap_none` / 引理 `filterMap_none`

English:
lemma filterMap_none
  given: (l : List α)
  proof: by
  induction l <;> simp [*]

中文:
引理 filterMap_none
  条件: (l : 列表 α)
  证明: by
  induction l <;> simp [*]
-/
lemma filterMap_none (l : List α) :
    l.filterMap (fun _ => @Option.none β) = [] := by
  induction l <;> simp [*]

/-! ### filter -/

section Filter

variable {p : α -> Bool}

/--
theorem `filter_singleton` / 定理 `filter_singleton`

English:
theorem filter_singleton
  given: {a : α}
  statement: [a].filter p = bif p a then [a] else []
  proof: rfl

中文:
定理 filter_singleton
  条件: {a : α}
  结论: [a].filter p = bif p a then [a] else []
  证明: rfl
-/
theorem filter_singleton {a : α} : [a].filter p = bif p a then [a] else [] :=
  rfl

/--
theorem `filter_eq_foldr` / 定理 `filter_eq_foldr`

English:
theorem filter_eq_foldr
  given: (p : α -> Bool) (l : List α)
  proof: by
  induction l <;> simp [*, filter]; rfl

@[simp]

中文:
定理 filter_eq_foldr
  条件: (p : α -> 布尔值) (l : 列表 α)
  证明: by
  induction l <;> simp [*, filter]; rfl

@[simp]

Depends on / 依赖: filter
-/
theorem filter_eq_foldr (p : α -> Bool) (l : List α) :
    filter p l = foldr (fun a out => bif p a then a :: out else out) [] l := by
  induction l <;> simp [*, filter]; rfl

@[simp]
/--
theorem `filter_subset_self` / 定理 `filter_subset_self`

English:
theorem filter_subset_self
  given: (l : List α)
  statement: filter p l subseteq l
  proof: filter_sublist.subset

@[deprecated (since := "2026-04-24")] alias filter_subset' := filter_subset_self

中文:
定理 filter_subset_self
  条件: (l : 列表 α)
  结论: filter p l subseteq l
  证明: filter_sublist.subset

@[deprecated (since := "2026-04-24")] alias filter_subset' := filter_subset_self

Depends on / 依赖: filter_sublist, filter_sublist.subset, subset
-/
theorem filter_subset_self (l : List α) : filter p l subseteq l :=
  filter_sublist.subset

@[deprecated (since := "2026-04-24")] alias filter_subset' := filter_subset_self

/--
theorem `of_mem_filter` / 定理 `of_mem_filter`

English:
theorem of_mem_filter
  given: {a : α} {l} (h : a in filter p l)
  statement: p a
  proof: (mem_filter.1 h).2

中文:
定理 of_mem_filter
  条件: {a : α} {l} (h : a in filter p l)
  结论: p a
  证明: (mem_filter.1 h).2

Depends on / 依赖: mem_filter
-/
theorem of_mem_filter {a : α} {l} (h : a in filter p l) : p a := (mem_filter.1 h).2

/--
theorem `mem_of_mem_filter` / 定理 `mem_of_mem_filter`

English:
theorem mem_of_mem_filter
  given: {a : α} {l} (h : a in filter p l)
  statement: a in l
  proof: filter_subset_self l h

中文:
定理 mem_of_mem_filter
  条件: {a : α} {l} (h : a in filter p l)
  结论: a in l
  证明: filter_subset_self l h

Depends on / 依赖: filter_subset_self
-/
theorem mem_of_mem_filter {a : α} {l} (h : a in filter p l) : a in l :=
  filter_subset_self l h

/--
theorem `mem_filter_of_mem` / 定理 `mem_filter_of_mem`

English:
theorem mem_filter_of_mem
  given: {a : α} {l} (h₁ : a in l) (h₂ : p a)
  statement: a in filter p l
  proof: mem_filter.2 ⟨h₁, h₂⟩

中文:
定理 mem_filter_of_mem
  条件: {a : α} {l} (h₁ : a in l) (h₂ : p a)
  结论: a in filter p l
  证明: mem_filter.2 ⟨h₁, h₂⟩

Depends on / 依赖: mem_filter
-/
theorem mem_filter_of_mem {a : α} {l} (h₁ : a in l) (h₂ : p a) : a in filter p l :=
  mem_filter.2 ⟨h₁, h₂⟩

variable (p)

/--
theorem `monotone_filter_right` / 定理 `monotone_filter_right`

English:
theorem monotone_filter_right
  given: (l : List α) ⦃p q
  statement: α -> Bool⦄
  proof: by
  induction l with grind

中文:
定理 monotone_filter_right
  条件: (l : 列表 α) ⦃p q
  结论: α -> 布尔值⦄
  证明: by
  induction l with grind
-/
theorem monotone_filter_right (l : List α) ⦃p q : α -> Bool⦄
    (h : forall a, p a -> q a) : l.filter p <+ l.filter q := by
  induction l with grind

/--
lemma `map_filter` / 引理 `map_filter`

English:
lemma map_filter
  statement: {f : α -> β} (hf : Injective f) (l : List α)
  proof: by
  simp [comp_def, filter_map, hf.eq_iff]

中文:
引理 map_filter
  结论: {f : α -> β} (hf : 单射 f) (l : 列表 α)
  证明: by
  simp [comp_def, filter_map, hf.eq_iff]

Depends on / 依赖: comp_def, eq_iff, filter_map, hf.eq_iff
-/
lemma map_filter {f : α -> β} (hf : Injective f) (l : List α)
    [DecidablePred fun b => exists a, p a ∧ f a = b] :
    (l.filter p).map f = (l.map f).filter fun b => exists a, p a ∧ f a = b := by
  simp [comp_def, filter_map, hf.eq_iff]

/--
lemma `filter_attach'` / 引理 `filter_attach'`

English:
lemma filter_attach'
  given: (l : List α) (p : {a // a in l} -> Bool) [DecidableEq α]
  proof: by
  classical
  refine map_injective_iff.2 Subtype.coe_injective ?_
  simp [comp_def, map_filter _ Subtype.coe_injective]

中文:
引理 filter_attach'
  条件: (l : 列表 α) (p : {a // a in l} -> 布尔值) [DecidableEq α]
  证明: by
  classical
  refine map_injective_iff.2 Subtype.coe_injective ?_
  simp [comp_def, map_filter _ Subtype.coe_injective]

Depends on / 依赖: Subtype, Subtype.coe_injective, classical, coe_injective, comp_def, map_filter, map_injective_iff
-/
lemma filter_attach' (l : List α) (p : {a // a in l} -> Bool) [DecidableEq α] :
    l.attach.filter p =
      (l.filter fun x => exists h, p ⟨x, h⟩).attach.map (Subtype.map id fun _ => mem_of_mem_filter) := by
  classical
  refine map_injective_iff.2 Subtype.coe_injective ?_
  simp [comp_def, map_filter _ Subtype.coe_injective]

/--
lemma `filter_attach` / 引理 `filter_attach`

English:
lemma filter_attach
  given: (l : List α) (p : α -> Bool)
  proof: map_injective_iff.2 Subtype.coe_injective by
    simp_rw [map_map, comp_def, Subtype.map, id, ← Function.comp_apply (g := Subtype.val),
      ← filter_map, attach_map_subtype_val]

中文:
引理 filter_attach
  条件: (l : 列表 α) (p : α -> 布尔值)
  证明: map_injective_iff.2 Subtype.coe_injective by
    simp_rw [map_map, comp_def, Subtype.map, id, ← Function.comp_apply (g := Subtype.val),
      ← filter_map, attach_map_subtype_val]

Depends on / 依赖: Function, Function.comp_apply, Subtype, Subtype.coe_injective, Subtype.map, Subtype.val, attach_map_subtype_val, coe_injective, comp_apply, comp_def, filter_map, map_injective_iff, map_map, simp_rw
-/
lemma filter_attach (l : List α) (p : α -> Bool) :
    (l.attach.filter fun x => p x : List {x // x in l}) =
      (l.filter p).attach.map (Subtype.map id fun _ => mem_of_mem_filter) :=
map_injective_iff.2 Subtype.coe_injective by
    simp_rw [map_map, comp_def, Subtype.map, id, ← Function.comp_apply (g := Subtype.val),
      ← filter_map, attach_map_subtype_val]

/--
lemma `filter_comm` / 引理 `filter_comm`

English:
lemma filter_comm
  given: (q) (l : List α)
  statement: filter p (filter q l) = filter q (filter p l)
  proof: by
  simp [Bool.and_comm]

@[simp]

中文:
引理 filter_comm
  条件: (q) (l : 列表 α)
  结论: filter p (filter q l) = filter q (filter p l)
  证明: by
  simp [Bool.and_comm]

@[simp]

Depends on / 依赖: Bool.and_comm, and_comm
-/
lemma filter_comm (q) (l : List α) : filter p (filter q l) = filter q (filter p l) := by
  simp [Bool.and_comm]

@[simp]
/--
theorem `filter_true` / 定理 `filter_true`

English:
theorem filter_true
  given: (l : List α)
  proof: by induction l <;> simp [*, filter]

@[simp]

中文:
定理 filter_true
  条件: (l : 列表 α)
  证明: by induction l <;> simp [*, filter]

@[simp]

Depends on / 依赖: filter
-/
theorem filter_true (l : List α) :
    filter (fun _ => true) l = l := by induction l <;> simp [*, filter]

@[simp]
/--
theorem `filter_false` / 定理 `filter_false`

English:
theorem filter_false
  given: (l : List α)
  proof: by induction l <;> simp [*, filter]

中文:
定理 filter_false
  条件: (l : 列表 α)
  证明: by induction l <;> simp [*, filter]

Depends on / 依赖: filter
-/
theorem filter_false (l : List α) :
    filter (fun _ => false) l = [] := by induction l <;> simp [*, filter]

end Filter

/-! ### eraseP -/

section eraseP

variable {p : α -> Bool}

-- Cannot be @[simp] because `a` cannot be inferred by `simp`.
/--
theorem `length_eraseP_add_one` / 定理 `length_eraseP_add_one`

English:
theorem length_eraseP_add_one
  given: {l : List α} {a} (al : a in l) (pa : p a)
  proof: by grind

中文:
定理 length_eraseP_add_one
  条件: {l : 列表 α} {a} (al : a in l) (pa : p a)
  证明: by grind
-/
theorem length_eraseP_add_one {l : List α} {a} (al : a in l) (pa : p a) :
    (l.eraseP p).length + 1 = l.length := by grind

end eraseP

/-! ### erase -/

section Erase

variable [BEq α] [LawfulBEq α]

-- @[simp] -- removed because LHS is not in simp normal form
/--
theorem `length_erase_add_one` / 定理 `length_erase_add_one`

English:
theorem length_erase_add_one
  given: {a : α} {l : List α} (h : a in l)
  proof: by
  rw [erase_eq_eraseP]; rw [length_eraseP_add_one h BEq.rfl]

中文:
定理 length_erase_add_one
  条件: {a : α} {l : 列表 α} (h : a in l)
  证明: by
  rw [erase_eq_eraseP]; rw [length_eraseP_add_one h BEq.rfl]

Depends on / 依赖: BEq.rfl, erase_eq_eraseP, length_eraseP_add_one
-/
theorem length_erase_add_one {a : α} {l : List α} (h : a in l) :
    (l.erase a).length + 1 = l.length := by
  rw [erase_eq_eraseP]; rw [length_eraseP_add_one h BEq.rfl]

/--
theorem `map_erase` / 定理 `map_erase`

English:
theorem map_erase
  given: [BEq β] [LawfulBEq β] {f : α -> β} (finj : Injective f) {a : α} (l : List α)
  proof: by
  have : (a == ·) = (f a == f ·) := by ext b; simp [finj.eq_iff]
  rw [erase_eq_eraseP]; rw [erase_eq_eraseP]; rw [eraseP_map]; rw [this]; rfl

中文:
定理 map_erase
  条件: [BEq β] [LawfulBEq β] {f : α -> β} (finj : 单射 f) {a : α} (l : 列表 α)
  证明: by
  have : (a == ·) = (f a == f ·) := by ext b; simp [finj.eq_iff]
  rw [erase_eq_eraseP]; rw [erase_eq_eraseP]; rw [eraseP_map]; rw [this]; rfl

Depends on / 依赖: eq_iff, eraseP_map, erase_eq_eraseP, finj.eq_iff
-/
theorem map_erase [BEq β] [LawfulBEq β] {f : α -> β} (finj : Injective f) {a : α} (l : List α) :
    map f (l.erase a) = (map f l).erase (f a) := by
  have : (a == ·) = (f a == f ·) := by ext b; simp [finj.eq_iff]
  rw [erase_eq_eraseP]; rw [erase_eq_eraseP]; rw [eraseP_map]; rw [this]; rfl

/--
theorem `map_foldl_erase` / 定理 `map_foldl_erase`

English:
theorem map_foldl_erase
  given: [BEq β] [LawfulBEq β] {f : α -> β} (finj : Injective f) {l₁ l₂ : List α}
  proof: by
  induction l₂ generalizing l₁ <;> [rfl; simp only [foldl_cons, map_erase finj, *]]

中文:
定理 map_foldl_erase
  条件: [BEq β] [LawfulBEq β] {f : α -> β} (finj : 单射 f) {l₁ l₂ : 列表 α}
  证明: by
  induction l₂ generalizing l₁ <;> [rfl; simp only [foldl_cons, map_erase finj, *]]

Depends on / 依赖: foldl_cons, generalizing, map_erase
-/
theorem map_foldl_erase [BEq β] [LawfulBEq β] {f : α -> β} (finj : Injective f) {l₁ l₂ : List α} :
    map f (foldl List.erase l₁ l₂) = foldl (fun l a => l.erase (f a)) (map f l₁) l₂ := by
  induction l₂ generalizing l₁ <;> [rfl; simp only [foldl_cons, map_erase finj, *]]

/--
theorem `erase_getElem` / 定理 `erase_getElem`

English:
theorem erase_getElem
  given: [BEq ι] [LawfulBEq ι] {l : List ι} {i : Nat} (hi : i < l.length)
  proof: by
  induction l generalizing i with
  | nil => simp
  | cons a l IH => cases i with grind

中文:
定理 erase_getElem
  条件: [BEq ι] [LawfulBEq ι] {l : 列表 ι} {i : 自然数} (hi : i < l.length)
  证明: by
  induction l generalizing i with
  | nil => simp
  | cons a l IH => cases i with grind

Depends on / 依赖: generalizing
-/
theorem erase_getElem [BEq ι] [LawfulBEq ι] {l : List ι} {i : Nat} (hi : i < l.length) :
    Perm (l.erase l[i]) (l.eraseIdx i) := by
  induction l generalizing i with
  | nil => simp
  | cons a l IH => cases i with grind

/--
theorem `length_eraseIdx_add_one` / 定理 `length_eraseIdx_add_one`

English:
theorem length_eraseIdx_add_one
  given: {l : List ι} {i : Nat} (h : i < l.length)
  proof: by grind

中文:
定理 length_eraseIdx_add_one
  条件: {l : 列表 ι} {i : 自然数} (h : i < l.length)
  证明: by grind
-/
theorem length_eraseIdx_add_one {l : List ι} {i : Nat} (h : i < l.length) :
    (l.eraseIdx i).length + 1 = l.length := by grind

end Erase

/-! ### diff -/

section Diff

@[simp]
/--
theorem `map_diff` / 定理 `map_diff`

English:
theorem map_diff
  statement: [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] {f : α -> β}
  proof: by
  simp only [diff_eq_foldl, foldl_map, map_foldl_erase finj]

中文:
定理 map_diff
  结论: [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] {f : α -> β}
  证明: by
  simp only [diff_eq_foldl, foldl_map, map_foldl_erase finj]

Depends on / 依赖: diff_eq_foldl, foldl_map, map_foldl_erase
-/
theorem map_diff [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] {f : α -> β}
    (finj : Injective f) {l₁ l₂ : List α} :
    map f (l₁.diff l₂) = (map f l₁).diff (map f l₂) := by
  simp only [diff_eq_foldl, foldl_map, map_foldl_erase finj]

end Diff

section Choose

variable (p : α -> Prop) [DecidablePred p] (l : List α)

/--
theorem `choose_spec` / 定理 `choose_spec`

English:
theorem choose_spec
  given: (hp : exists a, a in l ∧ p a)
  statement: choose p l hp in l ∧ p (choose p l hp)
  proof: (chooseX p l hp).property

中文:
定理 choose_spec
  条件: (hp : 存在 a, a in l ∧ p a)
  结论: choose p l hp in l ∧ p (choose p l hp)
  证明: (chooseX p l hp).property

Depends on / 依赖: chooseX, property
-/
theorem choose_spec (hp : exists a, a in l ∧ p a) : choose p l hp in l ∧ p (choose p l hp) :=
  (chooseX p l hp).property

/--
theorem `choose_mem` / 定理 `choose_mem`

English:
theorem choose_mem
  given: (hp : exists a, a in l ∧ p a)
  statement: choose p l hp in l
  proof: (choose_spec _ _ _).1

中文:
定理 choose_mem
  条件: (hp : 存在 a, a in l ∧ p a)
  结论: choose p l hp in l
  证明: (choose_spec _ _ _).1

Depends on / 依赖: choose_spec
-/
theorem choose_mem (hp : exists a, a in l ∧ p a) : choose p l hp in l :=
  (choose_spec _ _ _).1

/--
theorem `choose_property` / 定理 `choose_property`

English:
theorem choose_property
  given: (hp : exists a, a in l ∧ p a)
  statement: p (choose p l hp)
  proof: (choose_spec _ _ _).2

中文:
定理 choose_property
  条件: (hp : 存在 a, a in l ∧ p a)
  结论: p (choose p l hp)
  证明: (choose_spec _ _ _).2

Depends on / 依赖: choose_spec
-/
theorem choose_property (hp : exists a, a in l ∧ p a) : p (choose p l hp) :=
  (choose_spec _ _ _).2

end Choose

/-! ### Forall -/

section Forall

variable {p q : α -> Prop} {l : List α}

@[simp]
/--
theorem `forall_cons` / 定理 `forall_cons`

English:
theorem forall_cons
  given: (p : α -> Prop) (x : α)
  statement: forall l : List α, Forall p (x :: l) ↔ p x ∧ Forall p l

中文:
定理 对任意_cons
  条件: (p : α -> 命题) (x : α)
  结论: 对任意 l : 列表 α, 任意 p (x :: l) ↔ p x ∧ 任意 p l
-/
theorem forall_cons (p : α -> Prop) (x : α) : forall l : List α, Forall p (x :: l) ↔ p x ∧ Forall p l
  | [] => (and_iff_left_of_imp fun _ => trivial).symm
  | _ :: _ => Iff.rfl

@[simp]
/--
theorem `forall_append` / 定理 `forall_append`

English:
theorem forall_append
  given: {p : α -> Prop}
  statement: forall {xs ys : List α},

中文:
定理 对任意_append
  条件: {p : α -> 命题}
  结论: 对任意 {xs ys : 列表 α},
-/
theorem forall_append {p : α -> Prop} : forall {xs ys : List α},
    Forall p (xs ++ ys) ↔ Forall p xs ∧ Forall p ys
  | [] => by simp
  | _ :: _ => by simp [forall_append, and_assoc]

/--
theorem `forall_iff_forall_mem` / 定理 `forall_iff_forall_mem`

English:
theorem forall_iff_forall_mem
  statement: forall {l : List α}, Forall p l ↔ forall x in l, p x

中文:
定理 对任意_iff_对任意_mem
  结论: 对任意 {l : 列表 α}, 任意 p l ↔ 对任意 x in l, p x
-/
theorem forall_iff_forall_mem : forall {l : List α}, Forall p l ↔ forall x in l, p x
  | [] => (iff_true_intro <| forall_mem_nil _).symm
  | x :: l => by rw [forall_mem_cons, forall_cons, forall_iff_forall_mem]

/--
theorem `Forall.imp` / 定理 `Forall.imp`

English:
theorem Forall.imp
  given: (h : forall x, p x -> q x)
  statement: forall {l : List α}, Forall p l -> Forall q l

中文:
定理 任意.imp
  条件: (h : 对任意 x, p x -> q x)
  结论: 对任意 {l : 列表 α}, 任意 p l -> 任意 q l
-/
theorem Forall.imp (h : forall x, p x -> q x) : forall {l : List α}, Forall p l -> Forall q l
  | [] => id
  | x :: l => by
    simp only [forall_cons, and_imp]
    rw [← and_imp]
    exact And.imp (h x) (Forall.imp h)

@[simp]
/--
theorem `forall_map_iff` / 定理 `forall_map_iff`

English:
theorem forall_map_iff
  given: {p : β -> Prop} (f : α -> β)
  statement: Forall p (l.map f) ↔ Forall (p ∘ f) l
  proof: by
  induction l <;> simp [*]

中文:
定理 对任意_map_iff
  条件: {p : β -> 命题} (f : α -> β)
  结论: 任意 p (l.map f) ↔ 任意 (p ∘ f) l
  证明: by
  induction l <;> simp [*]
-/
theorem forall_map_iff {p : β -> Prop} (f : α -> β) : Forall p (l.map f) ↔ Forall (p ∘ f) l := by
  induction l <;> simp [*]

instance (p : α -> Prop) [DecidablePred p] : DecidablePred (Forall p) := fun _ =>
  decidable_of_iff' _ forall_iff_forall_mem

end Forall


/--
theorem `get_attach` / 定理 `get_attach`

English:
theorem get_attach
  given: (l : List α) (i)
  proof: by simp

中文:
定理 get_attach
  条件: (l : 列表 α) (i)
  证明: by simp
-/
theorem get_attach (l : List α) (i) :
    (l.attach.get i).1 = l.get ⟨i, length_attach (l := l) ▸ i.2⟩ := by simp

section Disjoint

/--
theorem `disjoint_pmap` / 定理 `disjoint_pmap`

English:
theorem disjoint_pmap
  statement: {p : α -> Prop} {f : forall a : α, p a -> β} {s t : List α}
  proof: by
  simp only [Disjoint, mem_pmap]
  rintro b ⟨a, ha, rfl⟩ ⟨a', ha', ha''⟩
  apply h ha
  rwa [hf a a' (hs a ha) (ht a' ha') ha''.symm]

中文:
定理 disjoint_pmap
  结论: {p : α -> 命题} {f : 对任意 a : α, p a -> β} {s t : 列表 α}
  证明: by
  simp only [Disjoint, mem_pmap]
  rintro b ⟨a, ha, rfl⟩ ⟨a', ha', ha''⟩
  apply h ha
  rwa [hf a a' (hs a ha) (ht a' ha') ha''.symm]

Depends on / 依赖: Disjoint, mem_pmap
-/
theorem disjoint_pmap {p : α -> Prop} {f : forall a : α, p a -> β} {s t : List α}
    (hs : forall a in s, p a) (ht : forall a in t, p a)
    (hf : forall (a a' : α) (ha : p a) (ha' : p a'), f a ha = f a' ha' -> a = a')
    (h : Disjoint s t) :
    Disjoint (s.pmap f hs) (t.pmap f ht) := by
  simp only [Disjoint, mem_pmap]
  rintro b ⟨a, ha, rfl⟩ ⟨a', ha', ha''⟩
  apply h ha
  rwa [hf a a' (hs a ha) (ht a' ha') ha''.symm]

/--
theorem `disjoint_map` / 定理 `disjoint_map`

English:
theorem disjoint_map
  statement: {f : α -> β} {s t : List α} (hf : Function.Injective f)
  proof: by
  rw [← pmap_eq_map (fun _ _ => trivial)]; rw [← pmap_eq_map (fun _ _ => trivial)]
  exact disjoint_pmap _ _ (fun _ _ _ _ h' => hf h') h

alias Disjoint.map := disjoint_map

中文:
定理 disjoint_map
  结论: {f : α -> β} {s t : 列表 α} (hf : 函数.单射 f)
  证明: by
  rw [← pmap_eq_map (fun _ _ => trivial)]; rw [← pmap_eq_map (fun _ _ => trivial)]
  exact disjoint_pmap _ _ (fun _ _ _ _ h' => hf h') h

alias Disjoint.map := disjoint_map

Depends on / 依赖: disjoint_pmap, pmap_eq_map
-/
theorem disjoint_map {f : α -> β} {s t : List α} (hf : Function.Injective f)
    (h : Disjoint s t) : Disjoint (s.map f) (t.map f) := by
  rw [← pmap_eq_map (fun _ _ => trivial)]; rw [← pmap_eq_map (fun _ _ => trivial)]
  exact disjoint_pmap _ _ (fun _ _ _ _ h' => hf h') h

alias Disjoint.map := disjoint_map

/--
theorem `Disjoint.of_map` / 定理 `Disjoint.of_map`

English:
theorem Disjoint.of_map
  given: {f : α -> β} {s t : List α} (h : Disjoint (s.map f) (t.map f))
  proof: fun _a has hat =>
  h (mem_map_of_mem has) (mem_map_of_mem hat)

中文:
定理 Disjoint.of_map
  条件: {f : α -> β} {s t : 列表 α} (h : Disjoint (s.map f) (t.map f))
  证明: fun _a has hat =>
  h (mem_map_of_mem has) (mem_map_of_mem hat)
-/
theorem Disjoint.of_map {f : α -> β} {s t : List α} (h : Disjoint (s.map f) (t.map f)) :
    Disjoint s t := fun _a has hat =>
  h (mem_map_of_mem has) (mem_map_of_mem hat)

/--
theorem `Disjoint.map_iff` / 定理 `Disjoint.map_iff`

English:
theorem Disjoint.map_iff
  given: {f : α -> β} {s t : List α} (hf : Function.Injective f)
  proof: ⟨fun h => h.of_map, fun h => h.map hf⟩

中文:
定理 Disjoint.map_iff
  条件: {f : α -> β} {s t : 列表 α} (hf : 函数.单射 f)
  证明: ⟨fun h => h.of_map, fun h => h.map hf⟩

Depends on / 依赖: h.map, h.of_map, of_map
-/
theorem Disjoint.map_iff {f : α -> β} {s t : List α} (hf : Function.Injective f) :
    Disjoint (s.map f) (t.map f) ↔ Disjoint s t :=
  ⟨fun h => h.of_map, fun h => h.map hf⟩

/--
theorem `Perm.disjoint_left` / 定理 `Perm.disjoint_left`

English:
theorem Perm.disjoint_left
  given: {l₁ l₂ l : List α} (p : List.Perm l₁ l₂)
  proof: by
  simp_rw [List.disjoint_left, p.mem_iff]

中文:
定理 置换.disjoint_left
  条件: {l₁ l₂ l : 列表 α} (p : 列表.置换 l₁ l₂)
  证明: by
  simp_rw [List.disjoint_left, p.mem_iff]

Depends on / 依赖: List.disjoint_left, disjoint_left, mem_iff, p.mem_iff, simp_rw
-/
theorem Perm.disjoint_left {l₁ l₂ l : List α} (p : List.Perm l₁ l₂) :
    Disjoint l₁ l ↔ Disjoint l₂ l := by
  simp_rw [List.disjoint_left, p.mem_iff]

/--
theorem `Perm.disjoint_right` / 定理 `Perm.disjoint_right`

English:
theorem Perm.disjoint_right
  given: {l₁ l₂ l : List α} (p : List.Perm l₁ l₂)
  proof: by
  simp_rw [List.disjoint_right, p.mem_iff]

@[simp]

中文:
定理 置换.disjoint_right
  条件: {l₁ l₂ l : 列表 α} (p : 列表.置换 l₁ l₂)
  证明: by
  simp_rw [List.disjoint_right, p.mem_iff]

@[simp]

Depends on / 依赖: List.disjoint_right, disjoint_right, mem_iff, p.mem_iff, simp_rw
-/
theorem Perm.disjoint_right {l₁ l₂ l : List α} (p : List.Perm l₁ l₂) :
    Disjoint l l₁ ↔ Disjoint l l₂ := by
  simp_rw [List.disjoint_right, p.mem_iff]

@[simp]
/--
theorem `disjoint_reverse_left` / 定理 `disjoint_reverse_left`

English:
theorem disjoint_reverse_left
  given: {l₁ l₂ : List α}
  statement: Disjoint l₁.reverse l₂ ↔ Disjoint l₁ l₂
  proof: .disjoint_left reverse_perm _

@[simp]

中文:
定理 disjoint_reverse_left
  条件: {l₁ l₂ : 列表 α}
  结论: Disjoint l₁.reverse l₂ ↔ Disjoint l₁ l₂
  证明: .disjoint_left reverse_perm _

@[simp]

Depends on / 依赖: disjoint_left, reverse_perm
-/
theorem disjoint_reverse_left {l₁ l₂ : List α} : Disjoint l₁.reverse l₂ ↔ Disjoint l₁ l₂ :=
.disjoint_left reverse_perm _

@[simp]
/--
theorem `disjoint_reverse_right` / 定理 `disjoint_reverse_right`

English:
theorem disjoint_reverse_right
  given: {l₁ l₂ : List α}
  statement: Disjoint l₁ l₂.reverse ↔ Disjoint l₁ l₂
  proof: .disjoint_right reverse_perm _

中文:
定理 disjoint_reverse_right
  条件: {l₁ l₂ : 列表 α}
  结论: Disjoint l₁ l₂.reverse ↔ Disjoint l₁ l₂
  证明: .disjoint_right reverse_perm _

Depends on / 依赖: disjoint_right, reverse_perm
-/
theorem disjoint_reverse_right {l₁ l₂ : List α} : Disjoint l₁ l₂.reverse ↔ Disjoint l₁ l₂ :=
.disjoint_right reverse_perm _

end Disjoint

section lookup
variable [BEq α] [LawfulBEq α]

/--
lemma `lookup_graph` / 引理 `lookup_graph`

English:
lemma lookup_graph
  given: (f : α -> β) {a : α} {as : List α} (h : a in as)
  proof: by
  induction as with grind

中文:
引理 lookup_graph
  条件: (f : α -> β) {a : α} {as : 列表 α} (h : a in as)
  证明: by
  induction as with grind
-/
lemma lookup_graph (f : α -> β) {a : α} {as : List α} (h : a in as) :
    lookup a (as.map fun x => (x, f x)) = some (f a) := by
  induction as with grind

end lookup

section range'

@[simp]
/--
lemma `range'_0` / 引理 `range'_0`

English:
lemma range'_0
  given: (a b : Nat)
  statement: range' a b 0 = replicate b a
  proof: by
  induction b with
  | zero => simp
  | succ b ih => simp [range'_succ, ih, replicate_succ]

中文:
引理 range'_0
  条件: (a b : 自然数)
  结论: range' a b 0 = replicate b a
  证明: by
  induction b with
  | zero => simp
  | succ b ih => simp [range'_succ, ih, replicate_succ]

Depends on / 依赖: _succ, replicate_succ
-/
lemma range'_0 (a b : Nat) : range' a b 0 = replicate b a := by
  induction b with
  | zero => simp
  | succ b ih => simp [range'_succ, ih, replicate_succ]

/--
lemma `left_le_of_mem_range'` / 引理 `left_le_of_mem_range'`

English:
lemma left_le_of_mem_range'
  given: {a b s x : Nat} (hx : x in List.range' a b s)
  statement: a <= x
  proof: by
  obtain ⟨i, _, rfl⟩ := List.mem_range'.mp hx
  exact le_add_right a (s * i)

中文:
引理 left_le_of_mem_range'
  条件: {a b s x : 自然数} (hx : x in 列表.range' a b s)
  结论: a <= x
  证明: by
  obtain ⟨i, _, rfl⟩ := List.mem_range'.mp hx
  exact le_add_right a (s * i)

Depends on / 依赖: List.mem_range, le_add_right, mem_range
-/
lemma left_le_of_mem_range' {a b s x : Nat} (hx : x in List.range' a b s) : a <= x := by
  obtain ⟨i, _, rfl⟩ := List.mem_range'.mp hx
  exact le_add_right a (s * i)

end range'

end List
