/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
module

public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Common
public import Mathlib.Util.CompileInductive

/-!
# insertIdx

Proves various lemmas about `List.insertIdx`.
-/

public section

assert_not_exists Set.range Preorder

open Function

open Nat hiding one_pos

namespace List

universe u v

variable {α : Type u} {β : Type v}

section InsertIdx

variable {a : α}

@[simp]
/--
theorem `sublist_insertIdx` / 定理 `sublist_insertIdx`

English:
theorem sublist_insertIdx
  given: (l : List α) (n : Nat) (a : α)
  statement: l <+ (l.insertIdx n a)
  proof: by
  simpa only [eraseIdx_insertIdx_self] using eraseIdx_sublist (l.insertIdx n a) n

@[simp]

中文:
定理 sublist_insertIdx
  条件: (l : List α) (n : 自然数) (a : α)
  结论: l <+ (l.insertIdx n a)
  证明: by
  simpa only [eraseIdx_insertIdx_self] using eraseIdx_sublist (l.insertIdx n a) n

@[simp]

Depends on / 依赖: eraseIdx_insertIdx_self, eraseIdx_sublist, insertIdx, l.insertIdx
-/
theorem sublist_insertIdx (l : List α) (n : Nat) (a : α) : l <+ (l.insertIdx n a) := by
  simpa only [eraseIdx_insertIdx_self] using eraseIdx_sublist (l.insertIdx n a) n

@[simp]
/--
theorem `subset_insertIdx` / 定理 `subset_insertIdx`

English:
theorem subset_insertIdx
  given: (l : List α) (n : Nat) (a : α)
  statement: l subseteq l.insertIdx n a
  proof: (sublist_insertIdx ..).subset

中文:
定理 subset_insertIdx
  条件: (l : List α) (n : 自然数) (a : α)
  结论: l subseteq l.insertIdx n a
  证明: (sublist_insertIdx ..).subset

Depends on / 依赖: sublist_insertIdx, subset
-/
theorem subset_insertIdx (l : List α) (n : Nat) (a : α) : l subseteq l.insertIdx n a :=
  (sublist_insertIdx ..).subset

/-- Erasing `n`th element of a list, then inserting `a` at the same place
is the same as setting `n`th element to `a`.

We assume that `n ≠ length l`, because otherwise LHS equals `l ++ [a]` while RHS equals `l`. -/
@[simp]
/--
theorem `insertIdx_eraseIdx_self` / 定理 `insertIdx_eraseIdx_self`

English:
theorem insertIdx_eraseIdx_self
  given: {l : List α} {n : Nat} (hn : n != length l) (a : α)
  proof: by
  induction n generalizing l <;> cases l <;> simp_all

中文:
定理 insertIdx_eraseIdx_self
  条件: {l : List α} {n : 自然数} (hn : n != length l) (a : α)
  证明: by
  induction n generalizing l <;> cases l <;> simp_all

Depends on / 依赖: generalizing
-/
theorem insertIdx_eraseIdx_self {l : List α} {n : Nat} (hn : n != length l) (a : α) :
    (l.eraseIdx n).insertIdx n a = l.set n a := by
  induction n generalizing l <;> cases l <;> simp_all

/--
theorem `insertIdx_eraseIdx_getElem` / 定理 `insertIdx_eraseIdx_getElem`

English:
theorem insertIdx_eraseIdx_getElem
  given: {l : List α} {n : Nat} (hn : n < length l)
  proof: by
  simp [Nat.ne_of_lt hn]

中文:
定理 insertIdx_eraseIdx_getElem
  条件: {l : List α} {n : 自然数} (hn : n < length l)
  证明: by
  simp [Nat.ne_of_lt hn]

Depends on / 依赖: Nat.ne_of_lt, ne_of_lt
-/
theorem insertIdx_eraseIdx_getElem {l : List α} {n : Nat} (hn : n < length l) :
    (l.eraseIdx n).insertIdx n l[n] = l := by
  simp [Nat.ne_of_lt hn]

/--
theorem `eq_or_mem_of_mem_insertIdx` / 定理 `eq_or_mem_of_mem_insertIdx`

English:
theorem eq_or_mem_of_mem_insertIdx
  given: {l : List α} {n : Nat} {a b : α} (h : a in l.insertIdx n b)
  proof: by
  cases Nat.lt_or_ge (length l) n with
  | inl hn =>
    rw [insertIdx_of_length_lt hn] at h
    exact .inr h
  | inr hn =>
    rwa [mem_insertIdx hn] at h

中文:
定理 eq_or_mem_of_mem_insertIdx
  条件: {l : List α} {n : 自然数} {a b : α} (h : a in l.insertIdx n b)
  证明: by
  cases Nat.lt_or_ge (length l) n with
  | inl hn =>
    rw [insertIdx_of_length_lt hn] at h
    exact .inr h
  | inr hn =>
    rwa [mem_insertIdx hn] at h

Depends on / 依赖: Nat.lt_or_ge, insertIdx_of_length_lt, length, lt_or_ge, mem_insertIdx
-/
theorem eq_or_mem_of_mem_insertIdx {l : List α} {n : Nat} {a b : α} (h : a in l.insertIdx n b) :
    a = b ∨ a in l := by
  cases Nat.lt_or_ge (length l) n with
  | inl hn =>
    rw [insertIdx_of_length_lt hn] at h
    exact .inr h
  | inr hn =>
    rwa [mem_insertIdx hn] at h

/--
theorem `insertIdx_subset_cons` / 定理 `insertIdx_subset_cons`

English:
theorem insertIdx_subset_cons
  given: (n : Nat) (a : α) (l : List α)
  statement: l.insertIdx n a subseteq a :: l
  proof: by
  intro b hb
  simpa using eq_or_mem_of_mem_insertIdx hb

中文:
定理 insertIdx_subset_cons
  条件: (n : 自然数) (a : α) (l : List α)
  结论: l.insertIdx n a subseteq a :: l
  证明: by
  intro b hb
  simpa using eq_or_mem_of_mem_insertIdx hb

Depends on / 依赖: eq_or_mem_of_mem_insertIdx
-/
theorem insertIdx_subset_cons (n : Nat) (a : α) (l : List α) : l.insertIdx n a subseteq a :: l := by
  intro b hb
  simpa using eq_or_mem_of_mem_insertIdx hb

/--
theorem `insertIdx_pmap` / 定理 `insertIdx_pmap`

English:
theorem insertIdx_pmap
  statement: {p : α -> Prop} (f : forall a, p a -> β) {l : List α} {a : α} {n : Nat}
  proof: by
  induction n generalizing l with
  | zero => cases l <;> simp
  | succ n ihn => cases l <;> simp_all

中文:
定理 insertIdx_pmap
  结论: {p : α -> 命题} (f : 对任意 a, p a -> β) {l : List α} {a : α} {n : 自然数}
  证明: by
  induction n generalizing l with
  | zero => cases l <;> simp
  | succ n ihn => cases l <;> simp_all

Depends on / 依赖: generalizing
-/
theorem insertIdx_pmap {p : α -> Prop} (f : forall a, p a -> β) {l : List α} {a : α} {n : Nat}
    (hl : forall x in l, p x) (ha : p a) :
    (l.pmap f hl).insertIdx n (f a ha) = (l.insertIdx n a).pmap f
      (fun _ h => (eq_or_mem_of_mem_insertIdx h).elim (fun heq => heq ▸ ha) (hl _)) := by
  induction n generalizing l with
  | zero => cases l <;> simp
  | succ n ihn => cases l <;> simp_all

/--
theorem `map_insertIdx` / 定理 `map_insertIdx`

English:
theorem map_insertIdx
  given: (f : α -> β) (l : List α) (n : Nat) (a : α)
  proof: by
  simpa only [pmap_eq_map] using (insertIdx_pmap (fun a _ => f a) (fun _ _ => trivial) trivial).symm

中文:
定理 map_insertIdx
  条件: (f : α -> β) (l : List α) (n : 自然数) (a : α)
  证明: by
  simpa only [pmap_eq_map] using (insertIdx_pmap (fun a _ => f a) (fun _ _ => trivial) trivial).symm

Depends on / 依赖: insertIdx_pmap, pmap_eq_map
-/
theorem map_insertIdx (f : α -> β) (l : List α) (n : Nat) (a : α) :
    (l.insertIdx n a).map f = (l.map f).insertIdx n (f a) := by
  simpa only [pmap_eq_map] using (insertIdx_pmap (fun a _ => f a) (fun _ _ => trivial) trivial).symm

/--
theorem `eraseIdx_pmap` / 定理 `eraseIdx_pmap`

English:
theorem eraseIdx_pmap
  given: {p : α -> Prop} (f : forall a, p a -> β) {l : List α} (hl : forall a in l, p a) (n : Nat)
  proof: match l, hl, n with
  | [], _, _ => rfl
  | a :: _, _, 0 => rfl
  | a :: as, h, n + 1 => by rw [forall_mem_cons] at h; simp [eraseIdx_pmap f h.2 n]

中文:
定理 eraseIdx_pmap
  条件: {p : α -> 命题} (f : 对任意 a, p a -> β) {l : List α} (hl : 对任意 a in l, p a) (n : 自然数)
  证明: match l, hl, n with
  | [], _, _ => rfl
  | a :: _, _, 0 => rfl
  | a :: as, h, n + 1 => by rw [forall_mem_cons] at h; simp [eraseIdx_pmap f h.2 n]

Depends on / 依赖: eraseIdx_pmap, forall_mem_cons
-/
theorem eraseIdx_pmap {p : α -> Prop} (f : forall a, p a -> β) {l : List α} (hl : forall a in l, p a) (n : Nat) :
    (pmap f l hl).eraseIdx n = (l.eraseIdx n).pmap f fun a ha => hl a (eraseIdx_subset ha) :=
  match l, hl, n with
  | [], _, _ => rfl
  | a :: _, _, 0 => rfl
  | a :: as, h, n + 1 => by rw [forall_mem_cons] at h; simp [eraseIdx_pmap f h.2 n]

/--
theorem `eraseIdx_map` / 定理 `eraseIdx_map`

English:
theorem eraseIdx_map
  given: (f : α -> β) (l : List α) (n : Nat)
  proof: by
  simpa only [pmap_eq_map] using eraseIdx_pmap (fun a _ => f a) (fun _ _ => trivial) n

中文:
定理 eraseIdx_map
  条件: (f : α -> β) (l : List α) (n : 自然数)
  证明: by
  simpa only [pmap_eq_map] using eraseIdx_pmap (fun a _ => f a) (fun _ _ => trivial) n

Depends on / 依赖: eraseIdx_pmap, pmap_eq_map
-/
theorem eraseIdx_map (f : α -> β) (l : List α) (n : Nat) :
    (map f l).eraseIdx n = (l.eraseIdx n).map f := by
  simpa only [pmap_eq_map] using eraseIdx_pmap (fun a _ => f a) (fun _ _ => trivial) n

/--
theorem `get_insertIdx_of_lt` / 定理 `get_insertIdx_of_lt`

English:
theorem get_insertIdx_of_lt
  statement: (l : List α) (x : α) (n k : Nat) (hn : k < n) (hk : k < l.length)
  proof: by
  simp_all [getElem_insertIdx_of_lt]

中文:
定理 get_insertIdx_of_lt
  结论: (l : List α) (x : α) (n k : 自然数) (hn : k < n) (hk : k < l.length)
  证明: by
  simp_all [getElem_insertIdx_of_lt]

Depends on / 依赖: getElem_insertIdx_of_lt, insertIdx, l.get, l.insertIdx
-/
theorem get_insertIdx_of_lt (l : List α) (x : α) (n k : Nat) (hn : k < n) (hk : k < l.length)
    (hk' : k < (l.insertIdx n x).length := by grind) :
    (l.insertIdx n x).get ⟨k, hk'⟩ = l.get ⟨k, hk⟩ := by
  simp_all [getElem_insertIdx_of_lt]

/--
theorem `get_insertIdx_self` / 定理 `get_insertIdx_self`

English:
theorem get_insertIdx_self
  statement: (l : List α) (x : α) (n : Nat) (hn : n <= l.length)
  proof: by
  simp

中文:
定理 get_insertIdx_self
  结论: (l : List α) (x : α) (n : 自然数) (hn : n <= l.length)
  证明: by
  simp

Depends on / 依赖: Nat.lt_succ_iff, insertIdx, l.insertIdx, length_insertIdx_of_le_length, lt_succ_iff
-/
theorem get_insertIdx_self (l : List α) (x : α) (n : Nat) (hn : n <= l.length)
    (hn' : n < (l.insertIdx n x).length :=
      (by rwa [length_insertIdx_of_le_length hn, Nat.lt_succ_iff])) :
    (l.insertIdx n x).get ⟨n, hn'⟩ = x := by
  simp

/--
theorem `getElem_insertIdx_add_succ` / 定理 `getElem_insertIdx_add_succ`

English:
theorem getElem_insertIdx_add_succ
  statement: (l : List α) (x : α) (n k : Nat) (hk' : n + k < l.length)
  proof: by
  grind

中文:
定理 getElem_insertIdx_add_succ
  结论: (l : List α) (x : α) (n k : 自然数) (hk' : n + k < l.length)
  证明: by
  grind

Depends on / 依赖: Nat.succ_lt_succ_iff, insertIdx, l.insertIdx, length_insertIdx_of_le_length, succ_lt_succ_iff
-/
theorem getElem_insertIdx_add_succ (l : List α) (x : α) (n k : Nat) (hk' : n + k < l.length)
    (hk : n + k + 1 < (l.insertIdx n x).length := (by
      rwa [length_insertIdx_of_le_length (by lia), Nat.succ_lt_succ_iff])) :
    (l.insertIdx n x)[n + k + 1] = l[n + k] := by
  grind

/--
theorem `get_insertIdx_add_succ` / 定理 `get_insertIdx_add_succ`

English:
theorem get_insertIdx_add_succ
  statement: (l : List α) (x : α) (n k : Nat) (hk' : n + k < l.length)
  proof: by
  simp [getElem_insertIdx_add_succ, hk']

中文:
定理 get_insertIdx_add_succ
  结论: (l : List α) (x : α) (n k : 自然数) (hk' : n + k < l.length)
  证明: by
  simp [getElem_insertIdx_add_succ, hk']

Depends on / 依赖: Nat.succ_lt_succ_iff, getElem_insertIdx_add_succ, insertIdx, l.insertIdx, length_insertIdx_of_le_length, succ_lt_succ_iff
-/
theorem get_insertIdx_add_succ (l : List α) (x : α) (n k : Nat) (hk' : n + k < l.length)
    (hk : n + k + 1 < (l.insertIdx n x).length := (by
      rwa [length_insertIdx_of_le_length (by lia), Nat.succ_lt_succ_iff])) :
    (l.insertIdx n x).get ⟨n + k + 1, hk⟩ = get l ⟨n + k, hk'⟩ := by
  simp [getElem_insertIdx_add_succ, hk']

/--
theorem `insertIdx_injective` / 定理 `insertIdx_injective`

English:
theorem insertIdx_injective
  given: (n : Nat) (x : α)
  proof: by
  intro l₁ l₂ hl
  simpa using congr($hl |>.eraseIdx n)

中文:
定理 insertIdx_injective
  条件: (n : 自然数) (x : α)
  证明: by
  intro l₁ l₂ hl
  simpa using congr($hl |>.eraseIdx n)

Depends on / 依赖: eraseIdx
-/
theorem insertIdx_injective (n : Nat) (x : α) :
    Function.Injective (fun l : List α => l.insertIdx n x) := by
  intro l₁ l₂ hl
  simpa using congr($hl |>.eraseIdx n)

/--
theorem `take_insertIdx_eq_take_of_le` / 定理 `take_insertIdx_eq_take_of_le`

English:
theorem take_insertIdx_eq_take_of_le
  given: (l : List α) x i j (h : i <= j)
  proof: ext_getElem (by grind) (by grind)

中文:
定理 take_insertIdx_eq_take_of_le
  条件: (l : List α) x i j (h : i <= j)
  证明: ext_getElem (by grind) (by grind)

Depends on / 依赖: ext_getElem
-/
theorem take_insertIdx_eq_take_of_le (l : List α) x i j (h : i <= j) :
    (l.insertIdx j x).take i = l.take i :=
  ext_getElem (by grind) (by grind)

/--
theorem `take_eraseIdx_eq_take_of_le` / 定理 `take_eraseIdx_eq_take_of_le`

English:
theorem take_eraseIdx_eq_take_of_le
  given: (l : List α) i j (h : i <= j)
  proof: ext_getElem (by grind) (by grind)

中文:
定理 take_eraseIdx_eq_take_of_le
  条件: (l : List α) i j (h : i <= j)
  证明: ext_getElem (by grind) (by grind)

Depends on / 依赖: ext_getElem
-/
theorem take_eraseIdx_eq_take_of_le (l : List α) i j (h : i <= j) :
    (l.eraseIdx j).take i = l.take i :=
  ext_getElem (by grind) (by grind)

end InsertIdx

end List
