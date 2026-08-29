/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Vasilii Nesterov
-/
module

public import Mathlib.Data.Seq.Defs
public import Mathlib.Data.ENat.Basic
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.ApplyFun

/-!
# Basic properties of sequences (possibly infinite lists)

This file provides some basic lemmas about possibly infinite lists represented by the
type `Stream'.Seq`.
-/

@[expose] public section

universe u v w

namespace Stream'

namespace Seq

variable {α : Type u} {β : Type v} {γ : Type w}

section length

/--
theorem `length'_of_terminates` / 定理 `length'_of_terminates`

English:
theorem length'_of_terminates
  given: {s : Seq α} (h : s.Terminates)
  proof: by
  simp [length', h]

中文:
定理 length'_of_terminates
  条件: {s : 序列 α} (h : s.Terminates)
  证明: by
  simp [length', h]

Depends on / 依赖: length
-/
theorem length'_of_terminates {s : Seq α} (h : s.Terminates) :
    s.length' = s.length h := by
  simp [length', h]

/--
theorem `length'_of_not_terminates` / 定理 `length'_of_not_terminates`

English:
theorem length'_of_not_terminates
  given: {s : Seq α} (h : ¬ s.Terminates)
  proof: by
  simp [length', h]

中文:
定理 length'_of_not_terminates
  条件: {s : 序列 α} (h : ¬ s.Terminates)
  证明: by
  simp [length', h]
-/
theorem length'_of_not_terminates {s : Seq α} (h : ¬ s.Terminates) :
    s.length' = ⊤ := by
  simp [length', h]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `length_nil` / 定理 `length_nil`

English:
theorem length_nil
  statement: length (nil : Seq α) terminates_nil = 0
  proof: (Nat.find_eq_zero _).mpr terminatedAt_nil

@[simp]

中文:
定理 length_nil
  结论: length (nil : 序列 α) terminates_nil = 0
  证明: (Nat.find_eq_zero _).mpr terminatedAt_nil

@[simp]

Depends on / 依赖: Nat.find_eq_zero, find_eq_zero, terminatedAt_nil
-/
theorem length_nil : length (nil : Seq α) terminates_nil = 0 :=
  (Nat.find_eq_zero _).mpr terminatedAt_nil

@[simp]
/--
theorem `length'_nil` / 定理 `length'_nil`

English:
theorem length'_nil
  statement: length' (nil : Seq α) = 0
  proof: by
  simp -implicitDefEqProofs [length']

中文:
定理 length'_nil
  结论: length' (nil : 序列 α) = 0
  证明: by
  simp -implicitDefEqProofs [length']
-/
theorem length'_nil : length' (nil : Seq α) = 0 := by
  simp -implicitDefEqProofs [length']

/--
theorem `length_cons` / 定理 `length_cons`

English:
theorem length_cons
  given: {x : α} {s : Seq α} (h : s.Terminates)
  proof: by
  apply Nat.find_comp_succ
  simp

@[simp]

中文:
定理 length_cons
  条件: {x : α} {s : 序列 α} (h : s.Terminates)
  证明: by
  apply Nat.find_comp_succ
  simp

@[simp]

Depends on / 依赖: Nat.find_comp_succ, find_comp_succ
-/
theorem length_cons {x : α} {s : Seq α} (h : s.Terminates) :
    (cons x s).length (terminates_cons_iff.mpr h) = s.length h + 1 := by
  apply Nat.find_comp_succ
  simp

@[simp]
/--
theorem `length'_cons` / 定理 `length'_cons`

English:
theorem length'_cons
  given: (x : α) (s : Seq α)
  proof: by
  by_cases h : (cons x s).Terminates <;> have h' := h <;> rw [terminates_cons_iff] at h'
  · simp [length'_of_terminates h, length'_of_terminates h', length_cons h']
  · simp [length'_of_not_terminates h, length'_of_not_terminates h']

中文:
定理 length'_cons
  条件: (x : α) (s : 序列 α)
  证明: by
  by_cases h : (cons x s).Terminates <;> have h' := h <;> rw [terminates_cons_iff] at h'
  · simp [length'_of_terminates h, length'_of_terminates h', length_cons h']
  · simp [length'_of_not_terminates h, length'_of_not_terminates h']
-/
theorem length'_cons (x : α) (s : Seq α) :
    (cons x s).length' = s.length' + 1 := by
  by_cases h : (cons x s).Terminates <;> have h' := h <;> rw [terminates_cons_iff] at h'
  · simp [length'_of_terminates h, length'_of_terminates h', length_cons h']
  · simp [length'_of_not_terminates h, length'_of_not_terminates h']

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `length_eq_zero` / 定理 `length_eq_zero`

English:
theorem length_eq_zero
  given: {s : Seq α} {h : s.Terminates}
  proof: by
  simp [length, TerminatedAt]

@[simp]

中文:
定理 length_eq_zero
  条件: {s : 序列 α} {h : s.Terminates}
  证明: by
  simp [length, TerminatedAt]

@[simp]

Depends on / 依赖: TerminatedAt, length
-/
theorem length_eq_zero {s : Seq α} {h : s.Terminates} :
    s.length h = 0 ↔ s = nil := by
  simp [length, TerminatedAt]

@[simp]
/--
theorem `length'_eq_zero_iff_nil` / 定理 `length'_eq_zero_iff_nil`

English:
theorem length'_eq_zero_iff_nil
  given: (s : Seq α)
  proof: by
  cases s <;> simp

中文:
定理 length'_eq_zero_iff_nil
  条件: (s : 序列 α)
  证明: by
  cases s <;> simp
-/
theorem length'_eq_zero_iff_nil (s : Seq α) :
    s.length' = 0 ↔ s = nil := by
  cases s <;> simp

/--
theorem `length'_ne_zero_iff_cons` / 定理 `length'_ne_zero_iff_cons`

English:
theorem length'_ne_zero_iff_cons
  given: (s : Seq α)
  proof: by
  cases s <;> simp

中文:
定理 length'_ne_zero_iff_cons
  条件: (s : 序列 α)
  证明: by
  cases s <;> simp
-/
theorem length'_ne_zero_iff_cons (s : Seq α) :
    s.length' != 0 ↔ exists x s', s = cons x s' := by
  cases s <;> simp

set_option backward.isDefEq.respectTransparency false in
/--
theorem `length_le_iff'` / 定理 `length_le_iff'`

English:
theorem length_le_iff'
  given: {s : Seq α} {n : Nat}
  proof: by
  simp only [length, Nat.find_le_iff, TerminatedAt, Terminates, exists_prop]
  refine ⟨?_, ?_⟩
  · rintro ⟨_, k, hkn, hk⟩
    exact le_stable s hkn hk
  · intro hn
    exact ⟨⟨n, hn⟩, ⟨n, le_rfl, hn⟩⟩

中文:
定理 length_le_iff'
  条件: {s : 序列 α} {n : 自然数}
  证明: by
  simp only [length, Nat.find_le_iff, TerminatedAt, Terminates, exists_prop]
  refine ⟨?_, ?_⟩
  · rintro ⟨_, k, hkn, hk⟩
    exact le_stable s hkn hk
  · intro hn
    exact ⟨⟨n, hn⟩, ⟨n, le_rfl, hn⟩⟩

Depends on / 依赖: Nat.find_le_iff, TerminatedAt, Terminates, exists_prop, find_le_iff, le_rfl, le_stable, length
-/
theorem length_le_iff' {s : Seq α} {n : Nat} :
    (exists h, s.length h <= n) ↔ s.TerminatedAt n := by
  simp only [length, Nat.find_le_iff, TerminatedAt, Terminates, exists_prop]
  refine ⟨?_, ?_⟩
  · rintro ⟨_, k, hkn, hk⟩
    exact le_stable s hkn hk
  · intro hn
    exact ⟨⟨n, hn⟩, ⟨n, le_rfl, hn⟩⟩

/--
theorem `length_le_iff` / 定理 `length_le_iff`

English:
theorem length_le_iff
  given: {s : Seq α} {n : Nat} {h : s.Terminates}
  proof: by
  rw [← length_le_iff']; simp [h]

中文:
定理 length_le_iff
  条件: {s : 序列 α} {n : 自然数} {h : s.Terminates}
  证明: by
  rw [← length_le_iff']; simp [h]

Depends on / 依赖: length_le_iff
-/
theorem length_le_iff {s : Seq α} {n : Nat} {h : s.Terminates} :
    s.length h <= n ↔ s.TerminatedAt n := by
  rw [← length_le_iff']; simp [h]

/--
theorem `length'_le_iff` / 定理 `length'_le_iff`

English:
theorem length'_le_iff
  given: {s : Seq α} {n : Nat}
  proof: by
  by_cases h : s.Terminates
  · simpa [length'_of_terminates h] using length_le_iff
  · simpa [length'_of_not_terminates h] using forall_not_of_not_exists h n

中文:
定理 length'_le_iff
  条件: {s : 序列 α} {n : 自然数}
  证明: by
  by_cases h : s.Terminates
  · simpa [length'_of_terminates h] using length_le_iff
  · simpa [length'_of_not_terminates h] using forall_not_of_not_exists h n
-/
theorem length'_le_iff {s : Seq α} {n : Nat} :
    s.length' <= n ↔ s.TerminatedAt n := by
  by_cases h : s.Terminates
  · simpa [length'_of_terminates h] using length_le_iff
  · simpa [length'_of_not_terminates h] using forall_not_of_not_exists h n

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lt_length_iff'` / 定理 `lt_length_iff'`

English:
theorem lt_length_iff'
  given: {s : Seq α} {n : Nat}
  proof: by
  simp only [Terminates, TerminatedAt, length, Nat.lt_find_iff, forall_exists_index, Option.mem_def,
    ← Option.ne_none_iff_exists', ne_eq]
  refine ⟨?_, ?_⟩
  · intro h hn
    exact h n hn n le_rfl hn
  · intro hn _ _ k hkn hk
exact hn le_stable s hkn hk

中文:
定理 lt_length_iff'
  条件: {s : 序列 α} {n : 自然数}
  证明: by
  simp only [Terminates, TerminatedAt, length, Nat.lt_find_iff, forall_exists_index, Option.mem_def,
    ← Option.ne_none_iff_exists', ne_eq]
  refine ⟨?_, ?_⟩
  · intro h hn
    exact h n hn n le_rfl hn
  · intro hn _ _ k hkn hk
exact hn le_stable s hkn hk

Depends on / 依赖: Nat.lt_find_iff, Option.mem_def, Option.ne_none_iff_exists, TerminatedAt, Terminates, forall_exists_index, le_rfl, le_stable, length, lt_find_iff, mem_def, ne_eq, ne_none_iff_exists
-/
theorem lt_length_iff' {s : Seq α} {n : Nat} :
    (forall h : s.Terminates, n < s.length h) ↔ exists a, a in s.get? n := by
  simp only [Terminates, TerminatedAt, length, Nat.lt_find_iff, forall_exists_index, Option.mem_def,
    ← Option.ne_none_iff_exists', ne_eq]
  refine ⟨?_, ?_⟩
  · intro h hn
    exact h n hn n le_rfl hn
  · intro hn _ _ k hkn hk
exact hn le_stable s hkn hk

/--
theorem `lt_length_iff` / 定理 `lt_length_iff`

English:
theorem lt_length_iff
  given: {s : Seq α} {n : Nat} {h : s.Terminates}
  proof: by
  rw [← lt_length_iff']; simp [h]

中文:
定理 lt_length_iff
  条件: {s : 序列 α} {n : 自然数} {h : s.Terminates}
  证明: by
  rw [← lt_length_iff']; simp [h]

Depends on / 依赖: lt_length_iff
-/
theorem lt_length_iff {s : Seq α} {n : Nat} {h : s.Terminates} :
    n < s.length h ↔ exists a, a in s.get? n := by
  rw [← lt_length_iff']; simp [h]

/--
theorem `lt_length'_iff` / 定理 `lt_length'_iff`

English:
theorem lt_length'_iff
  given: {s : Seq α} {n : Nat}
  proof: by
  by_cases h : s.Terminates
  · simpa [length'_of_terminates h] using lt_length_iff
  · simp only [length'_of_not_terminates h, ENat.natCast_lt_top, Option.mem_def, true_iff]
    rw [not_terminates_iff] at h
    rw [← Option.isSome_iff_exists]
    exact h n

中文:
定理 lt_length'_iff
  条件: {s : 序列 α} {n : 自然数}
  证明: by
  by_cases h : s.Terminates
  · simpa [length'_of_terminates h] using lt_length_iff
  · simp only [length'_of_not_terminates h, ENat.natCast_lt_top, Option.mem_def, true_iff]
    rw [not_terminates_iff] at h
    rw [← Option.isSome_iff_exists]
    exact h n

Depends on / 依赖: ENat.natCast_lt_top, Option.isSome_iff_exists, Option.mem_def, Terminates, _of_not_terminates, _of_terminates, isSome_iff_exists, length, lt_length_iff, mem_def, natCast_lt_top, not_terminates_iff, s.Terminates, true_iff
-/
theorem lt_length'_iff {s : Seq α} {n : Nat} :
    n < s.length' ↔ exists a, a in s.get? n := by
  by_cases h : s.Terminates
  · simpa [length'_of_terminates h] using lt_length_iff
  · simp only [length'_of_not_terminates h, ENat.natCast_lt_top, Option.mem_def, true_iff]
    rw [not_terminates_iff] at h
    rw [← Option.isSome_iff_exists]
    exact h n

end length

section OfStream

@[simp]
/--
theorem `ofStream_cons` / 定理 `ofStream_cons`

English:
theorem ofStream_cons
  given: (a : α) (s)
  statement: ofStream (a::s) = cons a (ofStream s)
  proof: by
  apply Subtype.ext; simp only [ofStream, cons]; rw [Stream'.map_cons]

中文:
定理 ofStream_cons
  条件: (a : α) (s)
  结论: ofStream (a::s) = cons a (ofStream s)
  证明: by
  apply Subtype.ext; simp only [ofStream, cons]; rw [Stream'.map_cons]

Depends on / 依赖: Stream, Subtype, Subtype.ext, map_cons, ofStream
-/
theorem ofStream_cons (a : α) (s) : ofStream (a::s) = cons a (ofStream s) := by
  apply Subtype.ext; simp only [ofStream, cons]; rw [Stream'.map_cons]

end OfStream

section OfList

set_option backward.isDefEq.respectTransparency false in
/--
theorem `terminatedAt_ofList` / 定理 `terminatedAt_ofList`

English:
theorem terminatedAt_ofList
  given: (l : List α)
  proof: by
  simp [ofList, TerminatedAt]

中文:
定理 terminatedAt_ofList
  条件: (l : 列表 α)
  证明: by
  simp [ofList, TerminatedAt]

Depends on / 依赖: TerminatedAt, ofList
-/
theorem terminatedAt_ofList (l : List α) :
    (ofList l).TerminatedAt l.length := by
  simp [ofList, TerminatedAt]

/--
theorem `terminates_ofList` / 定理 `terminates_ofList`

English:
theorem terminates_ofList
  given: (l : List α)
  statement: (ofList l).Terminates
  proof: ⟨_, terminatedAt_ofList l⟩

中文:
定理 terminates_ofList
  条件: (l : 列表 α)
  结论: (ofList l).Terminates
  证明: ⟨_, terminatedAt_ofList l⟩

Depends on / 依赖: terminatedAt_ofList
-/
theorem terminates_ofList (l : List α) : (ofList l).Terminates :=
  ⟨_, terminatedAt_ofList l⟩

end OfList

section Take

@[simp]
/--
theorem `take_nil` / 定理 `take_nil`

English:
theorem take_nil
  given: {n : Nat}
  statement: (nil (α := α)).take n = List.nil
  proof: by
  cases n <;> rfl

@[simp]

中文:
定理 take_nil
  条件: {n : 自然数}
  结论: (nil (α := α)).take n = 列表.nil
  证明: by
  cases n <;> rfl

@[simp]

Depends on / 依赖: List.nil
-/
theorem take_nil {n : Nat} : (nil (α := α)).take n = List.nil := by
  cases n <;> rfl

@[simp]
/--
theorem `take_zero` / 定理 `take_zero`

English:
theorem take_zero
  given: {s : Seq α}
  statement: s.take 0 = []
  proof: by
  cases s <;> rfl

@[simp]

中文:
定理 take_zero
  条件: {s : 序列 α}
  结论: s.take 0 = []
  证明: by
  cases s <;> rfl

@[simp]
-/
theorem take_zero {s : Seq α} : s.take 0 = [] := by
  cases s <;> rfl

@[simp]
/--
theorem `take_succ_cons` / 定理 `take_succ_cons`

English:
theorem take_succ_cons
  given: {n : Nat} {x : α} {s : Seq α}
  proof: by
  rfl

@[simp, grind =]

中文:
定理 take_succ_cons
  条件: {n : 自然数} {x : α} {s : 序列 α}
  证明: by
  rfl

@[simp, grind =]
-/
theorem take_succ_cons {n : Nat} {x : α} {s : Seq α} :
    (cons x s).take (n + 1) = x :: s.take n := by
  rfl

@[simp, grind =]
/--
theorem `getElem?_take` / 定理 `getElem?_take`

English:
theorem getElem?_take
  statement: forall (n k : Nat) (s : Seq α),

中文:
定理 getElem?_take
  结论: 对任意 (n k : 自然数) (s : 序列 α),
-/
theorem getElem?_take : forall (n k : Nat) (s : Seq α),
    (s.take k)[n]? = if n < k then s.get? n else none
  | n, 0, s => by simp [take]
  | n, k + 1, s => by
    rw [take]
    cases h : destruct s with
    | none =>
      simp [destruct_eq_none h]
    | some a =>
      match a with
      | (x, r) =>
        rw [destruct_eq_cons h]
        match n with
        | 0 => simp
        | n + 1 => simp [List.getElem?_cons_succ, getElem?_take]

/--
theorem `get?_mem_take` / 定理 `get?_mem_take`

English:
theorem get?_mem_take
  statement: {s : Seq α} {m n : Nat} (h_mn : m < n) {x : α}
  proof: by
  induction m generalizing n s with
  | zero =>
    obtain ⟨l, hl⟩ := Nat.exists_add_one_eq.mpr h_mn
    rw [← hl]; rw [take]; rw [head_eq_some h_get]
    simp
  | succ k ih =>
    obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_lt h_mn
    have : exists y, s.get? 0 = some y := by
      apply ge_stable _

中文:
定理 get?_mem_take
  结论: {s : 序列 α} {m n : 自然数} (h_mn : m < n) {x : α}
  证明: by
  induction m generalizing n s with
  | zero =>
    obtain ⟨l, hl⟩ := Nat.exists_add_one_eq.mpr h_mn
    rw [← hl]; rw [take]; rw [head_eq_some h_get]
    simp
  | succ k ih =>
    obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_lt h_mn
    have : exists y, s.get? 0 = some y := by
      apply ge_stable _

Depends on / 依赖: List.mem_cons, Nat.exists_add_one_eq.mpr, Nat.exists_eq_add_of_lt, _tail, destruct_cons, exists_add_one_eq, exists_eq_add_of_lt, ge_stable, generalizing, h_get, h_mn, head_eq_some, mem_cons, s.get
-/
theorem get?_mem_take {s : Seq α} {m n : Nat} (h_mn : m < n) {x : α}
    (h_get : s.get? m = some x) : x in s.take n := by
  induction m generalizing n s with
  | zero =>
    obtain ⟨l, hl⟩ := Nat.exists_add_one_eq.mpr h_mn
    rw [← hl]; rw [take]; rw [head_eq_some h_get]
    simp
  | succ k ih =>
    obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_lt h_mn
    have : exists y, s.get? 0 = some y := by
      apply ge_stable _ _ h_get
      simp
    obtain ⟨y, hy⟩ := this
    rw [take]; rw [head_eq_some hy]
    simp only [destruct_cons, List.mem_cons]
    right
    apply ih (by lia)
    rwa [get?_tail]

/--
theorem `length_take_le` / 定理 `length_take_le`

English:
theorem length_take_le
  given: {s : Seq α} {n : Nat}
  statement: (s.take n).length <= n
  proof: by
  induction n generalizing s with
  | zero => simp
  | succ m ih =>
    rw [take]
    cases s.destruct with
    | none => simp
    | some v =>
      obtain ⟨x, r⟩ := v
      simpa using ih

中文:
定理 length_take_le
  条件: {s : 序列 α} {n : 自然数}
  结论: (s.take n).length <= n
  证明: by
  induction n generalizing s with
  | zero => simp
  | succ m ih =>
    rw [take]
    cases s.destruct with
    | none => simp
    | some v =>
      obtain ⟨x, r⟩ := v
      simpa using ih

Depends on / 依赖: destruct, generalizing, s.destruct
-/
theorem length_take_le {s : Seq α} {n : Nat} : (s.take n).length <= n := by
  induction n generalizing s with
  | zero => simp
  | succ m ih =>
    rw [take]
    cases s.destruct with
    | none => simp
    | some v =>
      obtain ⟨x, r⟩ := v
      simpa using ih

set_option backward.isDefEq.respectTransparency false in
/--
theorem `length_take_of_le_length` / 定理 `length_take_of_le_length`

English:
theorem length_take_of_le_length
  statement: {s : Seq α} {n : Nat}
  proof: by
  induction n generalizing s with
  | zero => simp [take]
  | succ n ih =>
      rw [take]; rw [destruct]
      let ⟨a, ha⟩ := lt_length_iff'.1 (fun ht => lt_of_lt_of_le (Nat.succ_pos _) (hle ht))
      simp only [Option.mem_def.1 ha, Option.map_eq_map, Option.map_some, List.length_cons,
        

中文:
定理 length_take_of_le_length
  结论: {s : 序列 α} {n : 自然数}
  证明: by
  induction n generalizing s with
  | zero => simp [take]
  | succ n ih =>
      rw [take]; rw [destruct]
      let ⟨a, ha⟩ := lt_length_iff'.1 (fun ht => lt_of_lt_of_le (Nat.succ_pos _) (hle ht))
      simp only [Option.mem_def.1 ha, Option.map_eq_map, Option.map_some, List.length_cons,
        

Depends on / 依赖: List.length_cons, Nat.add_right_cancel_iff, Nat.le_find_iff, Nat.lt_of_succ_le, Nat.succ_le_o, Nat.succ_pos, Option.map_eq_map, Option.map_some, Option.mem_def, Stream, TerminatedAt, add_right_cancel_iff, destruct, generalizing, le_find_iff, le_stable, length, length_cons, lt_length_iff, lt_of_lt_of_le
-/
theorem length_take_of_le_length {s : Seq α} {n : Nat}
    (hle : forall h : s.Terminates, n <= s.length h) : (s.take n).length = n := by
  induction n generalizing s with
  | zero => simp [take]
  | succ n ih =>
      rw [take]; rw [destruct]
      let ⟨a, ha⟩ := lt_length_iff'.1 (fun ht => lt_of_lt_of_le (Nat.succ_pos _) (hle ht))
      simp only [Option.mem_def.1 ha, Option.map_eq_map, Option.map_some, List.length_cons,
        Nat.add_right_cancel_iff]
      rw [ih]
      intro h
      simp only [length, tail, Nat.le_find_iff, TerminatedAt, get?_mk, Stream'.tail]
      intro m hmn hs
      have := lt_length_iff'.1 (fun ht => (Nat.lt_of_succ_le (hle ht)))
      rw [le_stable s (Nat.succ_le_of_lt hmn) hs] at this
      simp at this

end Take

section ToList

@[simp]
/--
theorem `length_toList` / 定理 `length_toList`

English:
theorem length_toList
  given: (s : Seq α) (h : s.Terminates)
  statement: (toList s h).length = length s h
  proof: by
  rw [toList]; rw [length_take_of_le_length]
  intro _
  exact le_rfl

中文:
定理 length_toList
  条件: (s : 序列 α) (h : s.Terminates)
  结论: (toList s h).length = length s h
  证明: by
  rw [toList]; rw [length_take_of_le_length]
  intro _
  exact le_rfl

Depends on / 依赖: le_rfl, length_take_of_le_length, toList
-/
theorem length_toList (s : Seq α) (h : s.Terminates) : (toList s h).length = length s h := by
  rw [toList]; rw [length_take_of_le_length]
  intro _
  exact le_rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `getElem?_toList` / 定理 `getElem?_toList`

English:
theorem getElem?_toList
  given: (s : Seq α) (h : s.Terminates) (n : Nat)
  statement: (toList s h)[n]? = s.get? n
  proof: by
  ext k
  simp only [toList, getElem?_take, Nat.lt_find_iff, length,
    Option.ite_none_right_eq_some, and_iff_right_iff_imp, TerminatedAt]
  intro h m hmn
  let ⟨a, ha⟩ := ge_stable s hmn h
  simp [ha]

中文:
定理 getElem?_toList
  条件: (s : 序列 α) (h : s.Terminates) (n : 自然数)
  结论: (toList s h)[n]? = s.get? n
  证明: by
  ext k
  simp only [toList, getElem?_take, Nat.lt_find_iff, length,
    Option.ite_none_right_eq_some, and_iff_right_iff_imp, TerminatedAt]
  intro h m hmn
  let ⟨a, ha⟩ := ge_stable s hmn h
  simp [ha]

Depends on / 依赖: Nat.lt_find_iff, Option.ite_none_right_eq_some, TerminatedAt, _take, and_iff_right_iff_imp, ge_stable, getElem, ite_none_right_eq_some, length, lt_find_iff, toList
-/
theorem getElem?_toList (s : Seq α) (h : s.Terminates) (n : Nat) : (toList s h)[n]? = s.get? n := by
  ext k
  simp only [toList, getElem?_take, Nat.lt_find_iff, length,
    Option.ite_none_right_eq_some, and_iff_right_iff_imp, TerminatedAt]
  intro h m hmn
  let ⟨a, ha⟩ := ge_stable s hmn h
  simp [ha]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `ofList_toList` / 定理 `ofList_toList`

English:
theorem ofList_toList
  given: (s : Seq α) (h : s.Terminates)
  proof: by
  ext n; simp [ofList]

@[simp]

中文:
定理 ofList_toList
  条件: (s : 序列 α) (h : s.Terminates)
  证明: by
  ext n; simp [ofList]

@[simp]

Depends on / 依赖: ofList
-/
theorem ofList_toList (s : Seq α) (h : s.Terminates) :
    ofList (toList s h) = s := by
  ext n; simp [ofList]

@[simp]
/--
theorem `toList_ofList` / 定理 `toList_ofList`

English:
theorem toList_ofList
  given: (l : List α)
  statement: toList (ofList l) (terminates_ofList l) = l
  proof: ofList_injective (by simp)

中文:
定理 toList_ofList
  条件: (l : 列表 α)
  结论: toList (ofList l) (terminates_ofList l) = l
  证明: ofList_injective (by simp)

Depends on / 依赖: ofList_injective
-/
theorem toList_ofList (l : List α) : toList (ofList l) (terminates_ofList l) = l :=
  ofList_injective (by simp)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `toList_nil` / 定理 `toList_nil`

English:
theorem toList_nil
  statement: toList (nil : Seq α) ⟨0, terminatedAt_zero_iff.2 rfl⟩ = []
  proof: by
  ext; simp [nil, toList, const]

中文:
定理 toList_nil
  结论: toList (nil : 序列 α) ⟨0, terminatedAt_zero_iff.2 rfl⟩ = []
  证明: by
  ext; simp [nil, toList, const]

Depends on / 依赖: toList
-/
theorem toList_nil : toList (nil : Seq α) ⟨0, terminatedAt_zero_iff.2 rfl⟩ = [] := by
  ext; simp [nil, toList, const]

/--
theorem `getLast?_toList` / 定理 `getLast?_toList`

English:
theorem getLast?_toList
  given: (s : Seq α) (h : s.Terminates)
  proof: by
  rw [List.getLast?_eq_getElem?]; rw [getElem?_toList]; rw [length_toList]

中文:
定理 getLast?_toList
  条件: (s : 序列 α) (h : s.Terminates)
  证明: by
  rw [List.getLast?_eq_getElem?]; rw [getElem?_toList]; rw [length_toList]

Depends on / 依赖: List.getLast, _eq_getElem, _toList, getElem, getLast, length_toList
-/
theorem getLast?_toList (s : Seq α) (h : s.Terminates) :
    (toList s h).getLast? = s.get? (s.length h - 1) := by
  rw [List.getLast?_eq_getElem?]; rw [getElem?_toList]; rw [length_toList]

end ToList

section Append

@[simp]
/--
theorem `cons_append` / 定理 `cons_append`

English:
theorem cons_append
  given: (a : α) (s t)
  statement: append (cons a s) t = cons a (append s t)
  proof: destruct_eq_cons by
    dsimp [append]; rw [corec_eq]
    dsimp [append]; rw [destruct_cons]

@[simp]

中文:
定理 cons_append
  条件: (a : α) (s t)
  结论: append (cons a s) t = cons a (append s t)
  证明: destruct_eq_cons by
    dsimp [append]; rw [corec_eq]
    dsimp [append]; rw [destruct_cons]

@[simp]

Depends on / 依赖: append, corec_eq, destruct_cons, destruct_eq_cons
-/
theorem cons_append (a : α) (s t) : append (cons a s) t = cons a (append s t) :=
destruct_eq_cons by
    dsimp [append]; rw [corec_eq]
    dsimp [append]; rw [destruct_cons]

@[simp]
/--
theorem `nil_append` / 定理 `nil_append`

English:
theorem nil_append
  given: (s : Seq α)
  statement: append nil s = s
  proof: by
  apply coinduction2; intro s
  dsimp [append]; rw [corec_eq]
  dsimp [append]
  cases s
  · trivial
  · rw [destruct_cons]
    dsimp
    exact ⟨rfl, _, rfl, rfl⟩

@[simp]

中文:
定理 nil_append
  条件: (s : 序列 α)
  结论: append nil s = s
  证明: by
  apply coinduction2; intro s
  dsimp [append]; rw [corec_eq]
  dsimp [append]
  cases s
  · trivial
  · rw [destruct_cons]
    dsimp
    exact ⟨rfl, _, rfl, rfl⟩

@[simp]

Depends on / 依赖: append, coinduction2, corec_eq, destruct_cons
-/
theorem nil_append (s : Seq α) : append nil s = s := by
  apply coinduction2; intro s
  dsimp [append]; rw [corec_eq]
  dsimp [append]
  cases s
  · trivial
  · rw [destruct_cons]
    dsimp
    exact ⟨rfl, _, rfl, rfl⟩

@[simp]
/--
theorem `append_nil` / 定理 `append_nil`

English:
theorem append_nil
  given: (s : Seq α)
  statement: append s nil = s
  proof: by
  apply coinduction2 s; intro s
  cases s
  · trivial
  · rw [cons_append, destruct_cons, destruct_cons]
    dsimp
    exact ⟨rfl, _, rfl, rfl⟩

@[simp]

中文:
定理 append_nil
  条件: (s : 序列 α)
  结论: append s nil = s
  证明: by
  apply coinduction2 s; intro s
  cases s
  · trivial
  · rw [cons_append, destruct_cons, destruct_cons]
    dsimp
    exact ⟨rfl, _, rfl, rfl⟩

@[simp]

Depends on / 依赖: coinduction2, cons_append, destruct_cons
-/
theorem append_nil (s : Seq α) : append s nil = s := by
  apply coinduction2 s; intro s
  cases s
  · trivial
  · rw [cons_append, destruct_cons, destruct_cons]
    dsimp
    exact ⟨rfl, _, rfl, rfl⟩

@[simp]
/--
theorem `append_assoc` / 定理 `append_assoc`

English:
theorem append_assoc
  given: (s t u : Seq α)
  statement: append (append s t) u = append s (append t u)
  proof: by
  apply eq_of_bisim fun s1 s2 => exists s t u, s1 = append (append s t) u ∧ s2 = append s (append t u)
  · rintro _ _ ⟨s, t, u, rfl, rfl⟩
    cases s with
    | nil =>
      cases t with
      | nil =>
        cases u with
        | nil => simp
        | cons _ u => simpa using ⟨nil, nil, u, by s

中文:
定理 append_assoc
  条件: (s t u : 序列 α)
  结论: append (append s t) u = append s (append t u)
  证明: by
  apply eq_of_bisim fun s1 s2 => exists s t u, s1 = append (append s t) u ∧ s2 = append s (append t u)
  · rintro _ _ ⟨s, t, u, rfl, rfl⟩
    cases s with
    | nil =>
      cases t with
      | nil =>
        cases u with
        | nil => simp
        | cons _ u => simpa using ⟨nil, nil, u, by s

Depends on / 依赖: append, eq_of_bisim
-/
theorem append_assoc (s t u : Seq α) : append (append s t) u = append s (append t u) := by
  apply eq_of_bisim fun s1 s2 => exists s t u, s1 = append (append s t) u ∧ s2 = append s (append t u)
  · rintro _ _ ⟨s, t, u, rfl, rfl⟩
    cases s with
    | nil =>
      cases t with
      | nil =>
        cases u with
        | nil => simp
        | cons _ u => simpa using ⟨nil, nil, u, by simp, by simp⟩
      | cons _ t => simpa using ⟨nil, t, u, by simp, by simp⟩
    | cons _ s => simpa using ⟨s, t, u, rfl, rfl⟩
  · exact ⟨s, t, u, rfl, rfl⟩

/--
theorem `of_mem_append` / 定理 `of_mem_append`

English:
theorem of_mem_append
  given: {s₁ s₂ : Seq α} {a : α} (h : a in append s₁ s₂)
  statement: a in s₁ ∨ a in s₂
  proof: by
  have := h; revert this
  generalize e : append s₁ s₂ = ss; intro h; revert s₁
  apply mem_rec_on h _
  intro b s' o s₁
  cases s₁ with
  | nil =>
    intro m _
    apply Or.inr
    simpa using m
  | cons c t₁ =>
    intro m e
    have := congr_arg destruct e
    rcases show a = c ∨ a in append 

中文:
定理 of_mem_append
  条件: {s₁ s₂ : 序列 α} {a : α} (h : a in append s₁ s₂)
  结论: a in s₁ ∨ a in s₂
  证明: by
  have := h; revert this
  generalize e : append s₁ s₂ = ss; intro h; revert s₁
  apply mem_rec_on h _
  intro b s' o s₁
  cases s₁ with
  | nil =>
    intro m _
    apply Or.inr
    simpa using m
  | cons c t₁ =>
    intro m e
    have := congr_arg destruct e
    rcases show a = c ∨ a in append 

Depends on / 依赖: Or.imp_left, Or.inl, Or.inr, append, congr_arg, destruct, generalize, imp_left, mem_cons, mem_cons_of_mem, mem_rec_on, revert
-/
theorem of_mem_append {s₁ s₂ : Seq α} {a : α} (h : a in append s₁ s₂) : a in s₁ ∨ a in s₂ := by
  have := h; revert this
  generalize e : append s₁ s₂ = ss; intro h; revert s₁
  apply mem_rec_on h _
  intro b s' o s₁
  cases s₁ with
  | nil =>
    intro m _
    apply Or.inr
    simpa using m
  | cons c t₁ =>
    intro m e
    have := congr_arg destruct e
    rcases show a = c ∨ a in append t₁ s₂ by simpa using m with e' | m
    · rw [e']
      exact Or.inl (mem_cons _ _)
    · obtain ⟨i1, i2⟩ := show c = b ∧ append t₁ s₂ = s' by simpa using e
      rcases o with e' | IH
      · simp [i1, e']
      · exact Or.imp_left (mem_cons_of_mem _) (IH m i2)

/--
theorem `mem_append_left` / 定理 `mem_append_left`

English:
theorem mem_append_left
  given: {s₁ s₂ : Seq α} {a : α} (h : a in s₁)
  statement: a in append s₁ s₂
  proof: by
  apply mem_rec_on h; intros; simp [*]

@[simp]

中文:
定理 mem_append_left
  条件: {s₁ s₂ : 序列 α} {a : α} (h : a in s₁)
  结论: a in append s₁ s₂
  证明: by
  apply mem_rec_on h; intros; simp [*]

@[simp]

Depends on / 依赖: intros, mem_rec_on
-/
theorem mem_append_left {s₁ s₂ : Seq α} {a : α} (h : a in s₁) : a in append s₁ s₂ := by
  apply mem_rec_on h; intros; simp [*]

@[simp]
/--
theorem `ofList_append` / 定理 `ofList_append`

English:
theorem ofList_append
  given: (l l' : List α)
  statement: ofList (l ++ l') = append (ofList l) (ofList l')
  proof: by
  induction l <;> simp [*]

@[simp]

中文:
定理 ofList_append
  条件: (l l' : 列表 α)
  结论: ofList (l ++ l') = append (ofList l) (ofList l')
  证明: by
  induction l <;> simp [*]

@[simp]
-/
theorem ofList_append (l l' : List α) : ofList (l ++ l') = append (ofList l) (ofList l') := by
  induction l <;> simp [*]

@[simp]
/--
theorem `ofStream_append` / 定理 `ofStream_append`

English:
theorem ofStream_append
  given: (l : List α) (s : Stream' α)
  proof: by
  induction l <;> simp [*, Stream'.nil_append_stream, Stream'.cons_append_stream]

中文:
定理 ofStream_append
  条件: (l : 列表 α) (s : Stream' α)
  证明: by
  induction l <;> simp [*, Stream'.nil_append_stream, Stream'.cons_append_stream]

Depends on / 依赖: Stream, cons_append_stream, nil_append_stream
-/
theorem ofStream_append (l : List α) (s : Stream' α) :
    ofStream (l ++ₛ s) = append (ofList l) (ofStream s) := by
  induction l <;> simp [*, Stream'.nil_append_stream, Stream'.cons_append_stream]

end Append

section Map

@[simp]
/--
theorem `map_get?` / 定理 `map_get?`

English:
theorem map_get?
  given: (f : α -> β)
  statement: forall s n, get? (map f s) n = (get? s n).map f

中文:
定理 map_get?
  条件: (f : α -> β)
  结论: 对任意 s n, get? (map f s) n = (get? s n).map f
-/
theorem map_get? (f : α -> β) : forall s n, get? (map f s) n = (get? s n).map f
  | ⟨_, _⟩, _ => rfl

@[simp]
/--
theorem `map_nil` / 定理 `map_nil`

English:
theorem map_nil
  given: (f : α -> β)
  statement: map f nil = nil
  proof: rfl

@[simp]

中文:
定理 map_nil
  条件: (f : α -> β)
  结论: map f nil = nil
  证明: rfl

@[simp]
-/
theorem map_nil (f : α -> β) : map f nil = nil :=
  rfl

@[simp]
/--
theorem `map_cons` / 定理 `map_cons`

English:
theorem map_cons
  given: (f : α -> β) (a)
  statement: forall s, map f (cons a s) = cons (f a) (map f s)

中文:
定理 map_cons
  条件: (f : α -> β) (a)
  结论: 对任意 s, map f (cons a s) = cons (f a) (map f s)
-/
theorem map_cons (f : α -> β) (a) : forall s, map f (cons a s) = cons (f a) (map f s)
  | ⟨s, al⟩ => by apply Subtype.ext; dsimp [cons, map]; rw [Stream'.map_cons]; rfl

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  statement: forall s : Seq α, map id s = s

中文:
定理 map_id
  结论: 对任意 s : 序列 α, map id s = s
-/
theorem map_id : forall s : Seq α, map id s = s
  | ⟨s, al⟩ => by
    apply Subtype.ext; dsimp [map]
    rw [Option.map_id]; rw [Stream'.map_id]

@[simp]
/--
theorem `map_tail` / 定理 `map_tail`

English:
theorem map_tail
  given: (f : α -> β)
  statement: forall s, map f (tail s) = tail (map f s)

中文:
定理 map_tail
  条件: (f : α -> β)
  结论: 对任意 s, map f (tail s) = tail (map f s)
-/
theorem map_tail (f : α -> β) : forall s, map f (tail s) = tail (map f s)
  | ⟨s, al⟩ => by apply Subtype.ext; dsimp [tail, map]

/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  given: (f : α -> β) (g : β -> γ)
  statement: forall s : Seq α, map (g ∘ f) s = map g (map f s)

中文:
定理 map_comp
  条件: (f : α -> β) (g : β -> γ)
  结论: 对任意 s : 序列 α, map (g ∘ f) s = map g (map f s)
-/
theorem map_comp (f : α -> β) (g : β -> γ) : forall s : Seq α, map (g ∘ f) s = map g (map f s)
  | ⟨s, al⟩ => by
    apply Subtype.ext; dsimp [map]
    apply congr_arg fun f : _ -> Option γ => Stream'.map f s
    ext ⟨⟩ <;> rfl

@[simp]
/--
theorem `terminatedAt_map_iff` / 定理 `terminatedAt_map_iff`

English:
theorem terminatedAt_map_iff
  given: {f : α -> β} {s : Seq α} {n : Nat}
  proof: by
  simp [TerminatedAt]

@[simp]

中文:
定理 terminatedAt_map_iff
  条件: {f : α -> β} {s : 序列 α} {n : 自然数}
  证明: by
  simp [TerminatedAt]

@[simp]

Depends on / 依赖: TerminatedAt
-/
theorem terminatedAt_map_iff {f : α -> β} {s : Seq α} {n : Nat} :
    (map f s).TerminatedAt n ↔ s.TerminatedAt n := by
  simp [TerminatedAt]

@[simp]
/--
theorem `terminates_map_iff` / 定理 `terminates_map_iff`

English:
theorem terminates_map_iff
  given: {f : α -> β} {s : Seq α}
  proof: by
  simp [Terminates]

@[simp]

中文:
定理 terminates_map_iff
  条件: {f : α -> β} {s : 序列 α}
  证明: by
  simp [Terminates]

@[simp]

Depends on / 依赖: Terminates
-/
theorem terminates_map_iff {f : α -> β} {s : Seq α} :
    (map f s).Terminates ↔ s.Terminates := by
  simp [Terminates]

@[simp]
/--
theorem `length_map` / 定理 `length_map`

English:
theorem length_map
  given: {s : Seq α} {f : α -> β} (h : (s.map f).Terminates)
  proof: by
  rw [length]
  congr
  ext
  simp

@[simp]

中文:
定理 length_map
  条件: {s : 序列 α} {f : α -> β} (h : (s.map f).Terminates)
  证明: by
  rw [length]
  congr
  ext
  simp

@[simp]

Depends on / 依赖: length
-/
theorem length_map {s : Seq α} {f : α -> β} (h : (s.map f).Terminates) :
    (s.map f).length h = s.length (terminates_map_iff.1 h) := by
  rw [length]
  congr
  ext
  simp

@[simp]
/--
theorem `length'_map` / 定理 `length'_map`

English:
theorem length'_map
  given: {s : Seq α} {f : α -> β}
  proof: by
  by_cases h : (s.map f).Terminates <;> have h' := h <;> rw [terminates_map_iff] at h'
  · rw [length'_of_terminates h, length'_of_terminates h', length_map h]
  · rw [length'_of_not_terminates h, length'_of_not_terminates h']

中文:
定理 length'_map
  条件: {s : 序列 α} {f : α -> β}
  证明: by
  by_cases h : (s.map f).Terminates <;> have h' := h <;> rw [terminates_map_iff] at h'
  · rw [length'_of_terminates h, length'_of_terminates h', length_map h]
  · rw [length'_of_not_terminates h, length'_of_not_terminates h']
-/
theorem length'_map {s : Seq α} {f : α -> β} :
    (s.map f).length' = s.length' := by
  by_cases h : (s.map f).Terminates <;> have h' := h <;> rw [terminates_map_iff] at h'
  · rw [length'_of_terminates h, length'_of_terminates h', length_map h]
  · rw [length'_of_not_terminates h, length'_of_not_terminates h']

/--
theorem `mem_map` / 定理 `mem_map`

English:
theorem mem_map
  given: (f : α -> β) {a : α}
  statement: forall {s : Seq α}, a in s -> f a in map f s

中文:
定理 mem_map
  条件: (f : α -> β) {a : α}
  结论: 对任意 {s : 序列 α}, a in s -> f a in map f s
-/
theorem mem_map (f : α -> β) {a : α} : forall {s : Seq α}, a in s -> f a in map f s
  | ⟨_, _⟩ => Stream'.mem_map (Option.map f)

/--
theorem `exists_of_mem_map` / 定理 `exists_of_mem_map`

English:
theorem exists_of_mem_map
  given: {f} {b : β}
  statement: forall {s : Seq α}, b in map f s -> exists a, a in s ∧ f a = b
  proof: fun {s} h => by match s with
  | ⟨g, al⟩ =>
    let ⟨o, om, oe⟩ := @Stream'.exists_of_mem_map _ _ (Option.map f) (some b) g h
    rcases o with - | a
    · injection oe
    · injection oe with h'; exact ⟨a, om, h'⟩

@[simp]

中文:
定理 存在_of_mem_map
  条件: {f} {b : β}
  结论: 对任意 {s : 序列 α}, b in map f s -> 存在 a, a in s ∧ f a = b
  证明: fun {s} h => by match s with
  | ⟨g, al⟩ =>
    let ⟨o, om, oe⟩ := @Stream'.exists_of_mem_map _ _ (Option.map f) (some b) g h
    rcases o with - | a
    · injection oe
    · injection oe with h'; exact ⟨a, om, h'⟩

@[simp]

Depends on / 依赖: Option.map, Stream, exists_of_mem_map, injection
-/
theorem exists_of_mem_map {f} {b : β} : forall {s : Seq α}, b in map f s -> exists a, a in s ∧ f a = b :=
  fun {s} h => by match s with
  | ⟨g, al⟩ =>
    let ⟨o, om, oe⟩ := @Stream'.exists_of_mem_map _ _ (Option.map f) (some b) g h
    rcases o with - | a
    · injection oe
    · injection oe with h'; exact ⟨a, om, h'⟩

@[simp]
/--
theorem `map_append` / 定理 `map_append`

English:
theorem map_append
  given: (f : α -> β) (s t)
  statement: map f (append s t) = append (map f s) (map f t)
  proof: by
  refine eq_of_bisim (fun s1 s2 => exists s t, s1 = map f (append s t) ∧ s2 = append (map f s) (map f t))
    ?_ ⟨s, t, rfl, rfl⟩
  rintro s1 s2 ⟨s, t, rfl, rfl⟩
  cases s with
  | nil =>
    cases t with
    | nil => simp
    | cons _ t => simpa using ⟨nil, t, by simp, by simp⟩
  | cons _ s => s

中文:
定理 map_append
  条件: (f : α -> β) (s t)
  结论: map f (append s t) = append (map f s) (map f t)
  证明: by
  refine eq_of_bisim (fun s1 s2 => exists s t, s1 = map f (append s t) ∧ s2 = append (map f s) (map f t))
    ?_ ⟨s, t, rfl, rfl⟩
  rintro s1 s2 ⟨s, t, rfl, rfl⟩
  cases s with
  | nil =>
    cases t with
    | nil => simp
    | cons _ t => simpa using ⟨nil, t, by simp, by simp⟩
  | cons _ s => s

Depends on / 依赖: append, eq_of_bisim
-/
theorem map_append (f : α -> β) (s t) : map f (append s t) = append (map f s) (map f t) := by
  refine eq_of_bisim (fun s1 s2 => exists s t, s1 = map f (append s t) ∧ s2 = append (map f s) (map f t))
    ?_ ⟨s, t, rfl, rfl⟩
  rintro s1 s2 ⟨s, t, rfl, rfl⟩
  cases s with
  | nil =>
    cases t with
    | nil => simp
    | cons _ t => simpa using ⟨nil, t, by simp, by simp⟩
  | cons _ s => simpa using ⟨s, t, rfl, rfl⟩

end Map

section Join


@[simp]
/--
theorem `join_nil` / 定理 `join_nil`

English:
theorem join_nil
  statement: join nil = (nil : Seq α)
  proof: destruct_eq_none rfl

中文:
定理 join_nil
  结论: join nil = (nil : 序列 α)
  证明: destruct_eq_none rfl

Depends on / 依赖: destruct_eq_none
-/
theorem join_nil : join nil = (nil : Seq α) :=
  destruct_eq_none rfl

set_option backward.isDefEq.respectTransparency false in
-- Not a simp lemmas as `join_cons` is more general
/--
theorem `join_cons_nil` / 定理 `join_cons_nil`

English:
theorem join_cons_nil
  given: (a : α) (S)
  statement: join (cons (a, nil) S) = cons a (join S)
  proof: destruct_eq_cons by simp [join]

中文:
定理 join_cons_nil
  条件: (a : α) (S)
  结论: join (cons (a, nil) S) = cons a (join S)
  证明: destruct_eq_cons by simp [join]

Depends on / 依赖: destruct_eq_cons
-/
theorem join_cons_nil (a : α) (S) : join (cons (a, nil) S) = cons a (join S) :=
destruct_eq_cons by simp [join]

set_option backward.isDefEq.respectTransparency false in
-- Not a simp lemmas as `join_cons` is more general
/--
theorem `join_cons_cons` / 定理 `join_cons_cons`

English:
theorem join_cons_cons
  given: (a b : α) (s S)
  proof: destruct_eq_cons by simp [join]

@[simp]

中文:
定理 join_cons_cons
  条件: (a b : α) (s S)
  证明: destruct_eq_cons by simp [join]

@[simp]

Depends on / 依赖: destruct_eq_cons
-/
theorem join_cons_cons (a b : α) (s S) :
    join (cons (a, cons b s) S) = cons a (join (cons (b, s) S)) :=
destruct_eq_cons by simp [join]

@[simp]
/--
theorem `join_cons` / 定理 `join_cons`

English:
theorem join_cons
  given: (a : α) (s S)
  statement: join (cons (a, s) S) = cons a (append s (join S))
  proof: by
  apply
    eq_of_bisim
      (fun s1 s2 => s1 = s2 ∨ exists a s S, s1 = join (cons (a, s) S) ∧ s2 = cons a (append s (join S)))
      _ (Or.inr ⟨a, s, S, rfl, rfl⟩)
  intro s1 s2 h
  exact
    match s1, s2, h with
| s, _, Or.inl Eq.refl s => by
      cases s; · trivial
      · rw [destruct_cons]

中文:
定理 join_cons
  条件: (a : α) (s S)
  结论: join (cons (a, s) S) = cons a (append s (join S))
  证明: by
  apply
    eq_of_bisim
      (fun s1 s2 => s1 = s2 ∨ exists a s S, s1 = join (cons (a, s) S) ∧ s2 = cons a (append s (join S)))
      _ (Or.inr ⟨a, s, S, rfl, rfl⟩)
  intro s1 s2 h
  exact
    match s1, s2, h with
| s, _, Or.inl Eq.refl s => by
      cases s; · trivial
      · rw [destruct_cons]

Depends on / 依赖: BisimO, Eq.refl, Or.inl, Or.inr, append, cons_append, destruct_cons, eq_of_bisim, join_cons_cons, join_cons_nil, true_and
-/
theorem join_cons (a : α) (s S) : join (cons (a, s) S) = cons a (append s (join S)) := by
  apply
    eq_of_bisim
      (fun s1 s2 => s1 = s2 ∨ exists a s S, s1 = join (cons (a, s) S) ∧ s2 = cons a (append s (join S)))
      _ (Or.inr ⟨a, s, S, rfl, rfl⟩)
  intro s1 s2 h
  exact
    match s1, s2, h with
| s, _, Or.inl Eq.refl s => by
      cases s; · trivial
      · rw [destruct_cons]
        exact ⟨rfl, Or.inl rfl⟩
    | _, _, Or.inr ⟨a, s, S, rfl, rfl⟩ => by
      cases s
      · simp [join_cons_nil]
      · simpa only [BisimO, join_cons_cons, destruct_cons, cons_append, true_and] using
          Or.inr ⟨_, _, S, rfl, rfl⟩

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `join_append` / 定理 `join_append`

English:
theorem join_append
  given: (S T : Seq (Seq1 α))
  statement: join (append S T) = append (join S) (join T)
  proof: by
  apply
    eq_of_bisim fun s1 s2 =>
      exists s S T, s1 = append s (join (append S T)) ∧ s2 = append s (append (join S) (join T))
  · rintro s1 s2 ⟨s, S, T, rfl, rfl⟩
    cases s with
    | nil =>
      cases S with
      | nil =>
        cases T with
        | nil => simp
        | cons s T 

中文:
定理 join_append
  条件: (S T : 序列 (Seq1 α))
  结论: join (append S T) = append (join S) (join T)
  证明: by
  apply
    eq_of_bisim fun s1 s2 =>
      exists s S T, s1 = append s (join (append S T)) ∧ s2 = append s (append (join S) (join T))
  · rintro s1 s2 ⟨s, S, T, rfl, rfl⟩
    cases s with
    | nil =>
      cases S with
      | nil =>
        cases T with
        | nil => simp
        | cons s T 

Depends on / 依赖: append, eq_of_bisim
-/
theorem join_append (S T : Seq (Seq1 α)) : join (append S T) = append (join S) (join T) := by
  apply
    eq_of_bisim fun s1 s2 =>
      exists s S T, s1 = append s (join (append S T)) ∧ s2 = append s (append (join S) (join T))
  · rintro s1 s2 ⟨s, S, T, rfl, rfl⟩
    cases s with
    | nil =>
      cases S with
      | nil =>
        cases T with
        | nil => simp
        | cons s T =>
          obtain ⟨a, s⟩ := s
          simpa using ⟨s, nil, T, by simp, by simp⟩
      | cons s S =>
        obtain ⟨a, s⟩ := s
        simpa using ⟨s, S, T, rfl, rfl⟩
    | cons _ s => simpa using ⟨s, S, T, rfl, rfl⟩
  · exact ⟨nil, S, T, by simp, by simp⟩

end Join

section Drop

@[simp, grind =]
/--
theorem `drop_get?` / 定理 `drop_get?`

English:
theorem drop_get?
  given: {n m : Nat} {s : Seq α}
  statement: (s.drop n).get? m = s.get? (n + m)
  proof: by
  induction n generalizing m with
  | zero => simp [drop]
  | succ k ih =>
    simp only [drop, get?_tail]
    convert! ih using 2
    lia

中文:
定理 drop_get?
  条件: {n m : 自然数} {s : 序列 α}
  结论: (s.drop n).get? m = s.get? (n + m)
  证明: by
  induction n generalizing m with
  | zero => simp [drop]
  | succ k ih =>
    simp only [drop, get?_tail]
    convert! ih using 2
    lia

Depends on / 依赖: _tail, convert, generalizing
-/
theorem drop_get? {n m : Nat} {s : Seq α} : (s.drop n).get? m = s.get? (n + m) := by
  induction n generalizing m with
  | zero => simp [drop]
  | succ k ih =>
    simp only [drop, get?_tail]
    convert! ih using 2
    lia

/--
theorem `dropn_add` / 定理 `dropn_add`

English:
theorem dropn_add
  given: (s : Seq α) (m)
  statement: forall n, drop s (m + n) = drop (drop s m) n

中文:
定理 dropn_add
  条件: (s : 序列 α) (m)
  结论: 对任意 n, drop s (m + n) = drop (drop s m) n
-/
theorem dropn_add (s : Seq α) (m) : forall n, drop s (m + n) = drop (drop s m) n
  | 0 => rfl
  | n + 1 => congr_arg tail (dropn_add s _ n)

/--
theorem `dropn_tail` / 定理 `dropn_tail`

English:
theorem dropn_tail
  given: (s : Seq α) (n)
  statement: drop (tail s) n = drop s (n + 1)
  proof: by
  rw [Nat.add_comm]; symm; apply dropn_add

@[simp]

中文:
定理 dropn_tail
  条件: (s : 序列 α) (n)
  结论: drop (tail s) n = drop s (n + 1)
  证明: by
  rw [Nat.add_comm]; symm; apply dropn_add

@[simp]

Depends on / 依赖: Nat.add_comm, add_comm, dropn_add
-/
theorem dropn_tail (s : Seq α) (n) : drop (tail s) n = drop s (n + 1) := by
  rw [Nat.add_comm]; symm; apply dropn_add

@[simp]
/--
theorem `head_dropn` / 定理 `head_dropn`

English:
theorem head_dropn
  given: (s : Seq α) (n)
  statement: head (drop s n) = get? s n
  proof: by
  induction n generalizing s with
  | zero => rfl
  | succ n IH => rw [← get?_tail, ← dropn_tail]; apply IH

@[simp]

中文:
定理 head_dropn
  条件: (s : 序列 α) (n)
  结论: head (drop s n) = get? s n
  证明: by
  induction n generalizing s with
  | zero => rfl
  | succ n IH => rw [← get?_tail, ← dropn_tail]; apply IH

@[simp]

Depends on / 依赖: _tail, dropn_tail, generalizing
-/
theorem head_dropn (s : Seq α) (n) : head (drop s n) = get? s n := by
  induction n generalizing s with
  | zero => rfl
  | succ n IH => rw [← get?_tail, ← dropn_tail]; apply IH

@[simp]
/--
theorem `drop_zero` / 定理 `drop_zero`

English:
theorem drop_zero
  given: {s : Seq α}
  statement: s.drop 0 = s
  proof: rfl

@[simp]

中文:
定理 drop_zero
  条件: {s : 序列 α}
  结论: s.drop 0 = s
  证明: rfl

@[simp]
-/
theorem drop_zero {s : Seq α} : s.drop 0 = s := rfl

@[simp]
/--
theorem `drop_succ_cons` / 定理 `drop_succ_cons`

English:
theorem drop_succ_cons
  given: {x : α} {s : Seq α} {n : Nat}
  proof: by
  simp [← dropn_tail]

@[simp]

中文:
定理 drop_succ_cons
  条件: {x : α} {s : 序列 α} {n : 自然数}
  证明: by
  simp [← dropn_tail]

@[simp]

Depends on / 依赖: dropn_tail
-/
theorem drop_succ_cons {x : α} {s : Seq α} {n : Nat} :
    (cons x s).drop (n + 1) = s.drop n := by
  simp [← dropn_tail]

@[simp]
/--
theorem `drop_nil` / 定理 `drop_nil`

English:
theorem drop_nil
  given: {n : Nat}
  statement: (@nil α).drop n = nil
  proof: by
  induction n with
  | zero => simp [drop]
  | succ m ih => simp [← dropn_tail, ih]

@[simp]

中文:
定理 drop_nil
  条件: {n : 自然数}
  结论: (@nil α).drop n = nil
  证明: by
  induction n with
  | zero => simp [drop]
  | succ m ih => simp [← dropn_tail, ih]

@[simp]

Depends on / 依赖: dropn_tail
-/
theorem drop_nil {n : Nat} : (@nil α).drop n = nil := by
  induction n with
  | zero => simp [drop]
  | succ m ih => simp [← dropn_tail, ih]

@[simp]
/--
theorem `drop_length'` / 定理 `drop_length'`

English:
theorem drop_length'
  given: {n : Nat} {s : Seq α}
  proof: by
  cases n with
  | zero => simp
  | succ n =>
    cases s with
    | nil => simp
    | cons x s =>
      simp only [drop_succ_cons, length'_cons, Nat.cast_add, Nat.cast_one]
      convert! drop_length' using 1
      generalize s.length' = m
      enat_to_nat
      lia

中文:
定理 drop_length'
  条件: {n : 自然数} {s : 序列 α}
  证明: by
  cases n with
  | zero => simp
  | succ n =>
    cases s with
    | nil => simp
    | cons x s =>
      simp only [drop_succ_cons, length'_cons, Nat.cast_add, Nat.cast_one]
      convert! drop_length' using 1
      generalize s.length' = m
      enat_to_nat
      lia

Depends on / 依赖: Nat.cast_add, Nat.cast_one, _cons, cast_add, cast_one, convert, drop_length, drop_succ_cons, enat_to_nat, generalize, length, s.length
-/
theorem drop_length' {n : Nat} {s : Seq α} :
    (s.drop n).length' = s.length' - n := by
  cases n with
  | zero => simp
  | succ n =>
    cases s with
    | nil => simp
    | cons x s =>
      simp only [drop_succ_cons, length'_cons, Nat.cast_add, Nat.cast_one]
      convert! drop_length' using 1
      generalize s.length' = m
      enat_to_nat
      lia

/--
theorem `take_drop` / 定理 `take_drop`

English:
theorem take_drop
  given: {s : Seq α} {n m : Nat}
  proof: by
  ext
  grind

中文:
定理 take_drop
  条件: {s : 序列 α} {n m : 自然数}
  证明: by
  ext
  grind
-/
theorem take_drop {s : Seq α} {n m : Nat} :
    (s.take n).drop m = (s.drop m).take (n - m) := by
  ext
  grind

end Drop

section ZipWith

@[simp]
/--
theorem `get?_zipWith` / 定理 `get?_zipWith`

English:
theorem get?_zipWith
  given: (f : α -> β -> γ) (s s' n)
  proof: rfl

@[simp]

中文:
定理 get?_zipWith
  条件: (f : α -> β -> γ) (s s' n)
  证明: rfl

@[simp]
-/
theorem get?_zipWith (f : α -> β -> γ) (s s' n) :
    (zipWith f s s').get? n = Option.map₂ f (s.get? n) (s'.get? n) :=
  rfl

@[simp]
/--
theorem `get?_zip` / 定理 `get?_zip`

English:
theorem get?_zip
  given: (s : Seq α) (t : Seq β) (n : Nat)
  proof: get?_zipWith _ _ _ _

@[simp]

中文:
定理 get?_zip
  条件: (s : 序列 α) (t : 序列 β) (n : 自然数)
  证明: get?_zipWith _ _ _ _

@[simp]
-/
theorem get?_zip (s : Seq α) (t : Seq β) (n : Nat) :
    get? (zip s t) n = Option.map₂ Prod.mk (get? s n) (get? t n) :=
  get?_zipWith _ _ _ _

@[simp]
/--
theorem `nats_get?` / 定理 `nats_get?`

English:
theorem nats_get?
  given: (n : Nat)
  statement: nats.get? n = some n
  proof: rfl

@[simp]

中文:
定理 nats_get?
  条件: (n : 自然数)
  结论: nats.get? n = some n
  证明: rfl

@[simp]
-/
theorem nats_get? (n : Nat) : nats.get? n = some n :=
  rfl

@[simp]
/--
theorem `get?_enum` / 定理 `get?_enum`

English:
theorem get?_enum
  given: (s : Seq α) (n : Nat)
  statement: get? (enum s) n = Option.map (Prod.mk n) (get? s n)
  proof: get?_zip _ _ _

@[simp]

中文:
定理 get?_enum
  条件: (s : 序列 α) (n : 自然数)
  结论: get? (enum s) n = 选项类型.map (积类型.mk n) (get? s n)
  证明: get?_zip _ _ _

@[simp]
-/
theorem get?_enum (s : Seq α) (n : Nat) : get? (enum s) n = Option.map (Prod.mk n) (get? s n) :=
  get?_zip _ _ _

@[simp]
/--
theorem `zipWith_nil_left` / 定理 `zipWith_nil_left`

English:
theorem zipWith_nil_left
  given: {f : α -> β -> γ} {s}
  proof: rfl

@[simp]

中文:
定理 zipWith_nil_left
  条件: {f : α -> β -> γ} {s}
  证明: rfl

@[simp]
-/
theorem zipWith_nil_left {f : α -> β -> γ} {s} :
    zipWith f nil s = nil :=
  rfl

@[simp]
/--
theorem `zipWith_nil_right` / 定理 `zipWith_nil_right`

English:
theorem zipWith_nil_right
  given: {f : α -> β -> γ} {s}
  proof: by
  ext1
  simp

@[simp]

中文:
定理 zipWith_nil_right
  条件: {f : α -> β -> γ} {s}
  证明: by
  ext1
  simp

@[simp]
-/
theorem zipWith_nil_right {f : α -> β -> γ} {s} :
    zipWith f s nil = nil := by
  ext1
  simp

@[simp]
/--
theorem `zipWith_cons_cons` / 定理 `zipWith_cons_cons`

English:
theorem zipWith_cons_cons
  given: {f : α -> β -> γ} {x s x' s'}
  proof: by
  ext1 n
  cases n <;> simp

@[simp]

中文:
定理 zipWith_cons_cons
  条件: {f : α -> β -> γ} {x s x' s'}
  证明: by
  ext1 n
  cases n <;> simp

@[simp]
-/
theorem zipWith_cons_cons {f : α -> β -> γ} {x s x' s'} :
    zipWith f (cons x s) (cons x' s') = cons (f x x') (zipWith f s s') := by
  ext1 n
  cases n <;> simp

@[simp]
/--
theorem `zip_nil_left` / 定理 `zip_nil_left`

English:
theorem zip_nil_left
  given: {s : Seq α}
  proof: rfl

@[simp]

中文:
定理 zip_nil_left
  条件: {s : 序列 α}
  证明: rfl

@[simp]
-/
theorem zip_nil_left {s : Seq α} :
    zip (@nil α) s = nil :=
  rfl

@[simp]
/--
theorem `zip_nil_right` / 定理 `zip_nil_right`

English:
theorem zip_nil_right
  given: {s : Seq α}
  proof: zipWith_nil_right

@[simp]

中文:
定理 zip_nil_right
  条件: {s : 序列 α}
  证明: zipWith_nil_right

@[simp]

Depends on / 依赖: zipWith_nil_right
-/
theorem zip_nil_right {s : Seq α} :
    zip s (@nil α) = nil :=
  zipWith_nil_right

@[simp]
/--
theorem `zip_cons_cons` / 定理 `zip_cons_cons`

English:
theorem zip_cons_cons
  given: {s s' : Seq α} {x x'}
  proof: zipWith_cons_cons

@[simp]

中文:
定理 zip_cons_cons
  条件: {s s' : 序列 α} {x x'}
  证明: zipWith_cons_cons

@[simp]

Depends on / 依赖: zipWith_cons_cons
-/
theorem zip_cons_cons {s s' : Seq α} {x x'} :
    zip (cons x s) (cons x' s') = cons (x, x') (zip s s') :=
  zipWith_cons_cons

@[simp]
/--
theorem `enum_nil` / 定理 `enum_nil`

English:
theorem enum_nil
  statement: enum (nil : Seq α) = nil
  proof: rfl

@[simp]

中文:
定理 enum_nil
  结论: enum (nil : 序列 α) = nil
  证明: rfl

@[simp]
-/
theorem enum_nil : enum (nil : Seq α) = nil :=
  rfl

@[simp]
/--
theorem `enum_cons` / 定理 `enum_cons`

English:
theorem enum_cons
  given: (s : Seq α) (x : α)
  proof: by
  ext ⟨n⟩ : 1
  · simp
  · simp only [get?_enum, get?_cons_succ, map_get?, Option.map_map]
    congr

universe u' v'

中文:
定理 enum_cons
  条件: (s : 序列 α) (x : α)
  证明: by
  ext ⟨n⟩ : 1
  · simp
  · simp only [get?_enum, get?_cons_succ, map_get?, Option.map_map]
    congr

universe u' v'

Depends on / 依赖: Option.map_map, _cons_succ, _enum, map_get, map_map
-/
theorem enum_cons (s : Seq α) (x : α) :
    enum (cons x s) = cons (0, x) (map (Prod.map Nat.succ id) (enum s)) := by
  ext ⟨n⟩ : 1
  · simp
  · simp only [get?_enum, get?_cons_succ, map_get?, Option.map_map]
    congr

universe u' v'
variable {α' : Type u'} {β' : Type v'}

/--
theorem `zipWith_map` / 定理 `zipWith_map`

English:
theorem zipWith_map
  given: (s₁ : Seq α) (s₂ : Seq β) (f₁ : α -> α') (f₂ : β -> β') (g : α' -> β' -> γ)
  proof: by
  ext1 n
  simp only [get?_zipWith, map_get?]
  cases s₁.get? n <;> cases s₂.get? n <;> simp

中文:
定理 zipWith_map
  条件: (s₁ : 序列 α) (s₂ : 序列 β) (f₁ : α -> α') (f₂ : β -> β') (g : α' -> β' -> γ)
  证明: by
  ext1 n
  simp only [get?_zipWith, map_get?]
  cases s₁.get? n <;> cases s₂.get? n <;> simp

Depends on / 依赖: _zipWith, map_get
-/
theorem zipWith_map (s₁ : Seq α) (s₂ : Seq β) (f₁ : α -> α') (f₂ : β -> β') (g : α' -> β' -> γ) :
    zipWith g (s₁.map f₁) (s₂.map f₂) = zipWith (fun a b => g (f₁ a) (f₂ b)) s₁ s₂ := by
  ext1 n
  simp only [get?_zipWith, map_get?]
  cases s₁.get? n <;> cases s₂.get? n <;> simp

/--
theorem `zipWith_map_left` / 定理 `zipWith_map_left`

English:
theorem zipWith_map_left
  given: (s₁ : Seq α) (s₂ : Seq β) (f : α -> α') (g : α' -> β -> γ)
  proof: by
  convert! zipWith_map _ _ _ (@id β) _
  simp

中文:
定理 zipWith_map_left
  条件: (s₁ : 序列 α) (s₂ : 序列 β) (f : α -> α') (g : α' -> β -> γ)
  证明: by
  convert! zipWith_map _ _ _ (@id β) _
  simp

Depends on / 依赖: convert, zipWith_map
-/
theorem zipWith_map_left (s₁ : Seq α) (s₂ : Seq β) (f : α -> α') (g : α' -> β -> γ) :
    zipWith g (s₁.map f) s₂ = zipWith (fun a b => g (f a) b) s₁ s₂ := by
  convert! zipWith_map _ _ _ (@id β) _
  simp

/--
theorem `zipWith_map_right` / 定理 `zipWith_map_right`

English:
theorem zipWith_map_right
  given: (s₁ : Seq α) (s₂ : Seq β) (f : β -> β') (g : α -> β' -> γ)
  proof: by
  convert! zipWith_map _ _ (@id α) _ _
  simp

中文:
定理 zipWith_map_right
  条件: (s₁ : 序列 α) (s₂ : 序列 β) (f : β -> β') (g : α -> β' -> γ)
  证明: by
  convert! zipWith_map _ _ (@id α) _ _
  simp

Depends on / 依赖: convert, zipWith_map
-/
theorem zipWith_map_right (s₁ : Seq α) (s₂ : Seq β) (f : β -> β') (g : α -> β' -> γ) :
    zipWith g s₁ (s₂.map f) = zipWith (fun a b => g a (f b)) s₁ s₂ := by
  convert! zipWith_map _ _ (@id α) _ _
  simp

/--
theorem `zip_map` / 定理 `zip_map`

English:
theorem zip_map
  given: (s₁ : Seq α) (s₂ : Seq β) (f₁ : α -> α') (f₂ : β -> β')
  proof: by
  ext1 n
  simp
  cases s₁.get? n <;> cases s₂.get? n <;> simp

中文:
定理 zip_map
  条件: (s₁ : 序列 α) (s₂ : 序列 β) (f₁ : α -> α') (f₂ : β -> β')
  证明: by
  ext1 n
  simp
  cases s₁.get? n <;> cases s₂.get? n <;> simp
-/
theorem zip_map (s₁ : Seq α) (s₂ : Seq β) (f₁ : α -> α') (f₂ : β -> β') :
    (s₁.map f₁).zip (s₂.map f₂) = (s₁.zip s₂).map (Prod.map f₁ f₂) := by
  ext1 n
  simp
  cases s₁.get? n <;> cases s₂.get? n <;> simp

/--
theorem `zip_map_left` / 定理 `zip_map_left`

English:
theorem zip_map_left
  given: (s₁ : Seq α) (s₂ : Seq β) (f : α -> α')
  proof: by
  convert! zip_map _ _ _ _
  simp

中文:
定理 zip_map_left
  条件: (s₁ : 序列 α) (s₂ : 序列 β) (f : α -> α')
  证明: by
  convert! zip_map _ _ _ _
  simp

Depends on / 依赖: convert, zip_map
-/
theorem zip_map_left (s₁ : Seq α) (s₂ : Seq β) (f : α -> α') :
    (s₁.map f).zip s₂ = (s₁.zip s₂).map (Prod.map f id) := by
  convert! zip_map _ _ _ _
  simp

/--
theorem `zip_map_right` / 定理 `zip_map_right`

English:
theorem zip_map_right
  given: (s₁ : Seq α) (s₂ : Seq β) (f : β -> β')
  proof: by
  convert! zip_map _ _ _ _
  simp

中文:
定理 zip_map_right
  条件: (s₁ : 序列 α) (s₂ : 序列 β) (f : β -> β')
  证明: by
  convert! zip_map _ _ _ _
  simp

Depends on / 依赖: convert, zip_map
-/
theorem zip_map_right (s₁ : Seq α) (s₂ : Seq β) (f : β -> β') :
    s₁.zip (s₂.map f) = (s₁.zip s₂).map (Prod.map id f) := by
  convert! zip_map _ _ _ _
  simp

end ZipWith

section Fold

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `fold_nil` / 定理 `fold_nil`

English:
theorem fold_nil
  given: (init : β) (f : β -> α -> β)
  proof: by
  unfold fold
  simp [corec_nil]

@[simp]

中文:
定理 fold_nil
  条件: (init : β) (f : β -> α -> β)
  证明: by
  unfold fold
  simp [corec_nil]

@[simp]

Depends on / 依赖: corec_nil
-/
theorem fold_nil (init : β) (f : β -> α -> β) :
    nil.fold init f = cons init nil := by
  unfold fold
  simp [corec_nil]

@[simp]
/--
theorem `fold_cons` / 定理 `fold_cons`

English:
theorem fold_cons
  given: (init : β) (f : β -> α -> β) (x : α) (s : Seq α)
  proof: by
  unfold fold
  dsimp only
  congr
  rw [corec_cons]
  simp

@[simp]

中文:
定理 fold_cons
  条件: (init : β) (f : β -> α -> β) (x : α) (s : 序列 α)
  证明: by
  unfold fold
  dsimp only
  congr
  rw [corec_cons]
  simp

@[simp]

Depends on / 依赖: corec_cons
-/
theorem fold_cons (init : β) (f : β -> α -> β) (x : α) (s : Seq α) :
    (cons x s).fold init f = cons init (s.fold (f init x) f) := by
  unfold fold
  dsimp only
  congr
  rw [corec_cons]
  simp

@[simp]
/--
theorem `fold_head` / 定理 `fold_head`

English:
theorem fold_head
  given: (init : β) (f : β -> α -> β) (s : Seq α)
  proof: by
  simp [fold]

中文:
定理 fold_head
  条件: (init : β) (f : β -> α -> β) (s : 序列 α)
  证明: by
  simp [fold]
-/
theorem fold_head (init : β) (f : β -> α -> β) (s : Seq α) :
    (s.fold init f).head = init := by
  simp [fold]

end Fold

section Update

variable (hd x : α) (tl : Seq α) (f : α -> α)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `get?_update` / 定理 `get?_update`

English:
theorem get?_update
  given: (s : Seq α) (n : Nat) (m : Nat)
  proof: by
  simp [update, Function.update]
  split_ifs with h_if
  · simp [h_if]
  · rfl

@[simp]

中文:
定理 get?_update
  条件: (s : 序列 α) (n : 自然数) (m : 自然数)
  证明: by
  simp [update, Function.update]
  split_ifs with h_if
  · simp [h_if]
  · rfl

@[simp]
-/
theorem get?_update (s : Seq α) (n : Nat) (m : Nat) :
    (s.update n f).get? m = if m = n then (s.get? m).map f else s.get? m := by
  simp [update, Function.update]
  split_ifs with h_if
  · simp [h_if]
  · rfl

@[simp]
/--
theorem `update_nil` / 定理 `update_nil`

English:
theorem update_nil
  given: (n : Nat)
  statement: update nil n f = nil
  proof: by
  ext1 m
  simp [get?_update]

@[simp]

中文:
定理 update_nil
  条件: (n : 自然数)
  结论: update nil n f = nil
  证明: by
  ext1 m
  simp [get?_update]

@[simp]

Depends on / 依赖: _update
-/
theorem update_nil (n : Nat) : update nil n f = nil := by
  ext1 m
  simp [get?_update]

@[simp]
/--
theorem `set_nil` / 定理 `set_nil`

English:
theorem set_nil
  given: (n : Nat) (x : α)
  statement: set nil n x = nil
  proof: update_nil _ _

@[simp]

中文:
定理 set_nil
  条件: (n : 自然数) (x : α)
  结论: set nil n x = nil
  证明: update_nil _ _

@[simp]

Depends on / 依赖: update_nil
-/
theorem set_nil (n : Nat) (x : α) : set nil n x = nil := update_nil _ _

@[simp]
/--
theorem `update_cons_zero` / 定理 `update_cons_zero`

English:
theorem update_cons_zero
  statement: (cons hd tl).update 0 f = cons (f hd) tl
  proof: by
  ext1 n
  cases n <;> simp [get?_update]

@[simp]

中文:
定理 update_cons_zero
  结论: (cons hd tl).update 0 f = cons (f hd) tl
  证明: by
  ext1 n
  cases n <;> simp [get?_update]

@[simp]

Depends on / 依赖: _update
-/
theorem update_cons_zero : (cons hd tl).update 0 f = cons (f hd) tl := by
  ext1 n
  cases n <;> simp [get?_update]

@[simp]
/--
theorem `set_cons_zero` / 定理 `set_cons_zero`

English:
theorem set_cons_zero
  given: (hd' : α)
  statement: (cons hd tl).set 0 hd' = cons hd' tl
  proof: update_cons_zero _ _ _

@[simp]

中文:
定理 set_cons_zero
  条件: (hd' : α)
  结论: (cons hd tl).set 0 hd' = cons hd' tl
  证明: update_cons_zero _ _ _

@[simp]

Depends on / 依赖: update_cons_zero
-/
theorem set_cons_zero (hd' : α) : (cons hd tl).set 0 hd' = cons hd' tl :=
  update_cons_zero _ _ _

@[simp]
/--
theorem `update_cons_succ` / 定理 `update_cons_succ`

English:
theorem update_cons_succ
  given: (n : Nat)
  statement: (cons hd tl).update (n + 1) f = cons hd (tl.update n f)
  proof: by
  ext1 n
  cases n <;> simp [get?_update]

@[simp]

中文:
定理 update_cons_succ
  条件: (n : 自然数)
  结论: (cons hd tl).update (n + 1) f = cons hd (tl.update n f)
  证明: by
  ext1 n
  cases n <;> simp [get?_update]

@[simp]

Depends on / 依赖: _update
-/
theorem update_cons_succ (n : Nat) : (cons hd tl).update (n + 1) f = cons hd (tl.update n f) := by
  ext1 n
  cases n <;> simp [get?_update]

@[simp]
/--
theorem `set_cons_succ` / 定理 `set_cons_succ`

English:
theorem set_cons_succ
  given: (n : Nat)
  statement: (cons hd tl).set (n + 1) x = cons hd (tl.set n x)
  proof: update_cons_succ _ _ _ _

中文:
定理 set_cons_succ
  条件: (n : 自然数)
  结论: (cons hd tl).set (n + 1) x = cons hd (tl.set n x)
  证明: update_cons_succ _ _ _ _

Depends on / 依赖: update_cons_succ
-/
theorem set_cons_succ (n : Nat) : (cons hd tl).set (n + 1) x = cons hd (tl.set n x) :=
  update_cons_succ _ _ _ _

set_option backward.isDefEq.respectTransparency false in
/--
theorem `get?_set_of_not_terminatedAt` / 定理 `get?_set_of_not_terminatedAt`

English:
theorem get?_set_of_not_terminatedAt
  given: {s : Seq α} {n : Nat} (h_not_terminated : ¬ s.TerminatedAt n)
  proof: by
  simpa [set, update, ← Option.ne_none_iff_exists'] using! h_not_terminated

中文:
定理 get?_set_of_not_terminatedAt
  条件: {s : 序列 α} {n : 自然数} (h_not_terminated : ¬ s.TerminatedAt n)
  证明: by
  simpa [set, update, ← Option.ne_none_iff_exists'] using! h_not_terminated
-/
theorem get?_set_of_not_terminatedAt {s : Seq α} {n : Nat} (h_not_terminated : ¬ s.TerminatedAt n) :
    (s.set n x).get? n = x := by
  simpa [set, update, ← Option.ne_none_iff_exists'] using! h_not_terminated

/--
theorem `get?_set_of_terminatedAt` / 定理 `get?_set_of_terminatedAt`

English:
theorem get?_set_of_terminatedAt
  given: {s : Seq α} {n : Nat} (h_terminated : s.TerminatedAt n)
  proof: by
  simpa [set, get?_update] using! h_terminated

中文:
定理 get?_set_of_terminatedAt
  条件: {s : 序列 α} {n : 自然数} (h_terminated : s.TerminatedAt n)
  证明: by
  simpa [set, get?_update] using! h_terminated
-/
theorem get?_set_of_terminatedAt {s : Seq α} {n : Nat} (h_terminated : s.TerminatedAt n) :
    (s.set n x).get? n = .none := by
  simpa [set, get?_update] using! h_terminated

/--
theorem `get?_set_of_ne` / 定理 `get?_set_of_ne`

English:
theorem get?_set_of_ne
  given: (s : Seq α) {m n : Nat} (h : n != m)
  statement: (s.set m x).get? n = s.get? n
  proof: by
  simp [set, get?_update, h]

中文:
定理 get?_set_of_ne
  条件: (s : 序列 α) {m n : 自然数} (h : n != m)
  结论: (s.set m x).get? n = s.get? n
  证明: by
  simp [set, get?_update, h]
-/
theorem get?_set_of_ne (s : Seq α) {m n : Nat} (h : n != m) : (s.set m x).get? n = s.get? n := by
  simp [set, get?_update, h]

/--
theorem `drop_set_of_lt` / 定理 `drop_set_of_lt`

English:
theorem drop_set_of_lt
  given: (s : Seq α) {m n : Nat} (h : m < n)
  statement: (s.set m x).drop n = s.drop n
  proof: by
  ext1 i
  simp [get?_set_of_ne _ _ (show n + i != m by lia)]

中文:
定理 drop_set_of_lt
  条件: (s : 序列 α) {m n : 自然数} (h : m < n)
  结论: (s.set m x).drop n = s.drop n
  证明: by
  ext1 i
  simp [get?_set_of_ne _ _ (show n + i != m by lia)]

Depends on / 依赖: _set_of_ne
-/
theorem drop_set_of_lt (s : Seq α) {m n : Nat} (h : m < n) : (s.set m x).drop n = s.drop n := by
  ext1 i
  simp [get?_set_of_ne _ _ (show n + i != m by lia)]

end Update

section All

/--
theorem `all_cons` / 定理 `all_cons`

English:
theorem all_cons
  given: {p : α -> Prop} {hd : α} {tl : Seq α} (h_hd : p hd) (h_tl : forall x in tl, p x)
  proof: by
  simp only [mem_cons_iff, forall_eq_or_imp] at *
  exact ⟨h_hd, h_tl⟩

中文:
定理 all_cons
  条件: {p : α -> 命题} {hd : α} {tl : 序列 α} (h_hd : p hd) (h_tl : 对任意 x in tl, p x)
  证明: by
  simp only [mem_cons_iff, forall_eq_or_imp] at *
  exact ⟨h_hd, h_tl⟩

Depends on / 依赖: forall_eq_or_imp, h_hd, h_tl, mem_cons_iff
-/
theorem all_cons {p : α -> Prop} {hd : α} {tl : Seq α} (h_hd : p hd) (h_tl : forall x in tl, p x) :
    (forall x in (cons hd tl), p x) := by
  simp only [mem_cons_iff, forall_eq_or_imp] at *
  exact ⟨h_hd, h_tl⟩

/--
theorem `all_get` / 定理 `all_get`

English:
theorem all_get
  statement: {p : α -> Prop} {s : Seq α} (h : forall x in s, p x) {n : Nat} {x : α}
  proof: by
  exact h _ (get?_mem hx)

中文:
定理 all_get
  结论: {p : α -> 命题} {s : 序列 α} (h : 对任意 x in s, p x) {n : 自然数} {x : α}
  证明: by
  exact h _ (get?_mem hx)

Depends on / 依赖: _mem
-/
theorem all_get {p : α -> Prop} {s : Seq α} (h : forall x in s, p x) {n : Nat} {x : α}
    (hx : s.get? n = .some x) :
    p x := by
  exact h _ (get?_mem hx)

/--
theorem `all_of_get` / 定理 `all_of_get`

English:
theorem all_of_get
  given: {p : α -> Prop} {s : Seq α} (h : forall n x, s.get? n = .some x -> p x)
  proof: by
  simp only [mem_iff_exists_get?]
  grind

中文:
定理 all_of_get
  条件: {p : α -> 命题} {s : 序列 α} (h : 对任意 n x, s.get? n = .some x -> p x)
  证明: by
  simp only [mem_iff_exists_get?]
  grind

Depends on / 依赖: mem_iff_exists_get
-/
theorem all_of_get {p : α -> Prop} {s : Seq α} (h : forall n x, s.get? n = .some x -> p x) :
    forall x in s, p x := by
  simp only [mem_iff_exists_get?]
  grind

/--
lemma `all_coind_drop_motive` / 引理 `all_coind_drop_motive`

English:
lemma all_coind_drop_motive
  statement: {s : Seq α} (motive : Seq α -> Prop) (base : motive s)
  proof: by
  induction n with
  | zero => simpa
  | succ m ih =>
    simp only [drop]
    generalize s.drop m = t at *
    cases t
    · simpa
    · exact step _ _ ih

中文:
引理 all_coind_drop_motive
  结论: {s : 序列 α} (motive : 序列 α -> 命题) (base : motive s)
  证明: by
  induction n with
  | zero => simpa
  | succ m ih =>
    simp only [drop]
    generalize s.drop m = t at *
    cases t
    · simpa
    · exact step _ _ ih

Depends on / 依赖: generalize, s.drop
-/
lemma all_coind_drop_motive {s : Seq α} (motive : Seq α -> Prop) (base : motive s)
    (step : forall hd tl, motive (.cons hd tl) -> motive tl) (n : Nat) :
    motive (s.drop n) := by
  induction n with
  | zero => simpa
  | succ m ih =>
    simp only [drop]
    generalize s.drop m = t at *
    cases t
    · simpa
    · exact step _ _ ih

/--
theorem `all_coind` / 定理 `all_coind`

English:
theorem all_coind
  statement: {s : Seq α} {p : α -> Prop}
  proof: by
  apply all_of_get
  intro n
  have := all_coind_drop_motive motive base (fun hd tl ih => (step hd tl ih).right) n
  rw [← head_dropn]
  generalize s.drop n = s' at this
  cases s' with
  | nil => simp
  | cons hd tl => simp [(step hd tl this).left]

中文:
定理 all_coind
  结论: {s : 序列 α} {p : α -> 命题}
  证明: by
  apply all_of_get
  intro n
  have := all_coind_drop_motive motive base (fun hd tl ih => (step hd tl ih).right) n
  rw [← head_dropn]
  generalize s.drop n = s' at this
  cases s' with
  | nil => simp
  | cons hd tl => simp [(step hd tl this).left]

Depends on / 依赖: all_coind_drop_motive, all_of_get, generalize, head_dropn, motive, s.drop
-/
theorem all_coind {s : Seq α} {p : α -> Prop}
    (motive : Seq α -> Prop) (base : motive s)
    (step : forall hd tl, motive (.cons hd tl) -> p hd ∧ motive tl) :
    forall x in s, p x := by
  apply all_of_get
  intro n
  have := all_coind_drop_motive motive base (fun hd tl ih => (step hd tl ih).right) n
  rw [← head_dropn]
  generalize s.drop n = s' at this
  cases s' with
  | nil => simp
  | cons hd tl => simp [(step hd tl this).left]

/--
theorem `map_all_iff` / 定理 `map_all_iff`

English:
theorem map_all_iff
  given: {β : Type u} {f : α -> β} {p : β -> Prop} {s : Seq α}
  proof: by
  refine ⟨fun _ _ hx => ?_, fun _ _ hx => ?_⟩
  · solve_by_elim [mem_map f hx]
  · obtain ⟨_, _, hx'⟩ := exists_of_mem_map hx
    rw [← hx']
    solve_by_elim

中文:
定理 map_all_iff
  条件: {β : 类型u} {f : α -> β} {p : β -> 命题} {s : 序列 α}
  证明: by
  refine ⟨fun _ _ hx => ?_, fun _ _ hx => ?_⟩
  · solve_by_elim [mem_map f hx]
  · obtain ⟨_, _, hx'⟩ := exists_of_mem_map hx
    rw [← hx']
    solve_by_elim

Depends on / 依赖: exists_of_mem_map, mem_map, solve_by_elim
-/
theorem map_all_iff {β : Type u} {f : α -> β} {p : β -> Prop} {s : Seq α} :
    (forall x in (s.map f), p x) ↔ (forall x in s, (p ∘ f) x) := by
  refine ⟨fun _ _ hx => ?_, fun _ _ hx => ?_⟩
  · solve_by_elim [mem_map f hx]
  · obtain ⟨_, _, hx'⟩ := exists_of_mem_map hx
    rw [← hx']
    solve_by_elim

/--
theorem `take_all` / 定理 `take_all`

English:
theorem take_all
  statement: {s : Seq α} {p : α -> Prop} (h_all : forall x in s, p x) {n : Nat} {x : α}
  proof: by
  induction n generalizing s with
  | zero => simp [take] at hx
  | succ m ih =>
    cases s with
    | nil => simp at hx
    | cons hd tl =>
      simp only [take_succ_cons, List.mem_cons, mem_cons_iff, forall_eq_or_imp] at hx h_all
      rcases hx with (rfl | hx)
      exacts [h_all.left, ih h_

中文:
定理 take_all
  结论: {s : 序列 α} {p : α -> 命题} (h_all : 对任意 x in s, p x) {n : 自然数} {x : α}
  证明: by
  induction n generalizing s with
  | zero => simp [take] at hx
  | succ m ih =>
    cases s with
    | nil => simp at hx
    | cons hd tl =>
      simp only [take_succ_cons, List.mem_cons, mem_cons_iff, forall_eq_or_imp] at hx h_all
      rcases hx with (rfl | hx)
      exacts [h_all.left, ih h_

Depends on / 依赖: List.mem_cons, exacts, forall_eq_or_imp, generalizing, h_all, h_all.left, h_all.right, mem_cons, mem_cons_iff, take_succ_cons
-/
theorem take_all {s : Seq α} {p : α -> Prop} (h_all : forall x in s, p x) {n : Nat} {x : α}
    (hx : x in s.take n) : p x := by
  induction n generalizing s with
  | zero => simp [take] at hx
  | succ m ih =>
    cases s with
    | nil => simp at hx
    | cons hd tl =>
      simp only [take_succ_cons, List.mem_cons, mem_cons_iff, forall_eq_or_imp] at hx h_all
      rcases hx with (rfl | hx)
      exacts [h_all.left, ih h_all.right hx]

/--
theorem `set_all` / 定理 `set_all`

English:
theorem set_all
  statement: {p : α -> Prop} {s : Seq α} (h_all : forall x in s, p x) {n : Nat} {x : α}
  proof: by
  intro y hy
  simp only [mem_iff_exists_get?] at hy
  obtain ⟨m, hy⟩ := hy
  rcases eq_or_ne n m with (rfl | h_nm)
  · by_cases h_term : s.TerminatedAt n
    · simp [get?_set_of_terminatedAt _ h_term] at hy
    · simp_all [get?_set_of_not_terminatedAt _ h_term]
  · rw [get?_set_of_ne _ _ h_nm.sy

中文:
定理 set_all
  结论: {p : α -> 命题} {s : 序列 α} (h_all : 对任意 x in s, p x) {n : 自然数} {x : α}
  证明: by
  intro y hy
  simp only [mem_iff_exists_get?] at hy
  obtain ⟨m, hy⟩ := hy
  rcases eq_or_ne n m with (rfl | h_nm)
  · by_cases h_term : s.TerminatedAt n
    · simp [get?_set_of_terminatedAt _ h_term] at hy
    · simp_all [get?_set_of_not_terminatedAt _ h_term]
  · rw [get?_set_of_ne _ _ h_nm.sy

Depends on / 依赖: TerminatedAt, _mem, _set_of_ne, _set_of_not_terminatedAt, _set_of_terminatedAt, eq_or_ne, h_all, h_nm, h_nm.symm, h_term, hy.symm, mem_iff_exists_get, s.TerminatedAt
-/
theorem set_all {p : α -> Prop} {s : Seq α} (h_all : forall x in s, p x) {n : Nat} {x : α}
    (hx : p x) : forall y in (s.set n x), p y := by
  intro y hy
  simp only [mem_iff_exists_get?] at hy
  obtain ⟨m, hy⟩ := hy
  rcases eq_or_ne n m with (rfl | h_nm)
  · by_cases h_term : s.TerminatedAt n
    · simp [get?_set_of_terminatedAt _ h_term] at hy
    · simp_all [get?_set_of_not_terminatedAt _ h_term]
  · rw [get?_set_of_ne _ _ h_nm.symm] at hy
    apply h_all _ (get?_mem hy.symm)

end All

section Pairwise

@[simp]
/--
theorem `Pairwise.nil` / 定理 `Pairwise.nil`

English:
theorem Pairwise.nil
  given: {R : α -> α -> Prop}
  statement: Pairwise R (@nil α)
  proof: by
  simp [Pairwise]

中文:
定理 两两.nil
  条件: {R : α -> α -> 命题}
  结论: 两两 R (@nil α)
  证明: by
  simp [Pairwise]

Depends on / 依赖: Pairwise
-/
theorem Pairwise.nil {R : α -> α -> Prop} : Pairwise R (@nil α) := by
  simp [Pairwise]

/--
theorem `Pairwise.cons` / 定理 `Pairwise.cons`

English:
theorem Pairwise.cons
  statement: {R : α -> α -> Prop} {hd : α} {tl : Seq α}
  proof: by
  simp only [Pairwise] at *
  intro i j h_ij x hx y hy
  cases j with
  | zero => simp at h_ij
  | succ k =>
    simp only [get?_cons_succ] at hy
    cases i with
    | zero =>
      simp only [get?_cons_zero, Option.mem_def, Option.some.injEq] at hx
      exact hx ▸ all_get h_hd hy
    | succ n 

中文:
定理 两两.cons
  结论: {R : α -> α -> 命题} {hd : α} {tl : 序列 α}
  证明: by
  simp only [Pairwise] at *
  intro i j h_ij x hx y hy
  cases j with
  | zero => simp at h_ij
  | succ k =>
    simp only [get?_cons_succ] at hy
    cases i with
    | zero =>
      simp only [get?_cons_zero, Option.mem_def, Option.some.injEq] at hx
      exact hx ▸ all_get h_hd hy
    | succ n 

Depends on / 依赖: Option.mem_def, Option.some.injEq, Pairwise, _cons_succ, _cons_zero, all_get, h_hd, h_ij, h_tl, mem_def
-/
theorem Pairwise.cons {R : α -> α -> Prop} {hd : α} {tl : Seq α}
    (h_hd : forall x in tl, R hd x)
    (h_tl : Pairwise R tl) : Pairwise R (cons hd tl) := by
  simp only [Pairwise] at *
  intro i j h_ij x hx y hy
  cases j with
  | zero => simp at h_ij
  | succ k =>
    simp only [get?_cons_succ] at hy
    cases i with
    | zero =>
      simp only [get?_cons_zero, Option.mem_def, Option.some.injEq] at hx
      exact hx ▸ all_get h_hd hy
    | succ n => exact h_tl n k (by lia) x hx y hy

/--
theorem `Pairwise.cons_elim` / 定理 `Pairwise.cons_elim`

English:
theorem Pairwise.cons_elim
  statement: {R : α -> α -> Prop} {hd : α} {tl : Seq α}
  proof: by
  simp only [Pairwise] at *
  refine ⟨?_, fun i j h_ij => h (i + 1) (j + 1) (by lia)⟩
  intro x hx
  rw [mem_iff_exists_get?] at hx
  obtain ⟨n, hx⟩ := hx
  simpa [← hx] using h 0 (n + 1) (by lia)

@[simp]

中文:
定理 两两.cons_elim
  结论: {R : α -> α -> 命题} {hd : α} {tl : 序列 α}
  证明: by
  simp only [Pairwise] at *
  refine ⟨?_, fun i j h_ij => h (i + 1) (j + 1) (by lia)⟩
  intro x hx
  rw [mem_iff_exists_get?] at hx
  obtain ⟨n, hx⟩ := hx
  simpa [← hx] using h 0 (n + 1) (by lia)

@[simp]

Depends on / 依赖: Pairwise, h_ij, mem_iff_exists_get
-/
theorem Pairwise.cons_elim {R : α -> α -> Prop} {hd : α} {tl : Seq α}
    (h : Pairwise R (.cons hd tl)) : (forall x in tl, R hd x) ∧ Pairwise R tl := by
  simp only [Pairwise] at *
  refine ⟨?_, fun i j h_ij => h (i + 1) (j + 1) (by lia)⟩
  intro x hx
  rw [mem_iff_exists_get?] at hx
  obtain ⟨n, hx⟩ := hx
  simpa [← hx] using h 0 (n + 1) (by lia)

@[simp]
/--
theorem `Pairwise_cons_nil` / 定理 `Pairwise_cons_nil`

English:
theorem Pairwise_cons_nil
  given: {R : α -> α -> Prop} {hd : α}
  statement: Pairwise R (cons hd nil)
  proof: by
  apply Pairwise.cons <;> simp

中文:
定理 Pairwise_cons_nil
  条件: {R : α -> α -> 命题} {hd : α}
  结论: 两两 R (cons hd nil)
  证明: by
  apply Pairwise.cons <;> simp

Depends on / 依赖: Pairwise, Pairwise.cons
-/
theorem Pairwise_cons_nil {R : α -> α -> Prop} {hd : α} : Pairwise R (cons hd nil) := by
  apply Pairwise.cons <;> simp

/--
theorem `Pairwise_cons_cons_head` / 定理 `Pairwise_cons_cons_head`

English:
theorem Pairwise_cons_cons_head
  statement: {R : α -> α -> Prop} {hd tl_hd : α} {tl_tl : Seq α}
  proof: by
  simp only [Pairwise] at h
  simpa using h 0 1 Nat.one_pos

中文:
定理 Pairwise_cons_cons_head
  结论: {R : α -> α -> 命题} {hd tl_hd : α} {tl_tl : 序列 α}
  证明: by
  simp only [Pairwise] at h
  simpa using h 0 1 Nat.one_pos

Depends on / 依赖: Nat.one_pos, Pairwise, one_pos
-/
theorem Pairwise_cons_cons_head {R : α -> α -> Prop} {hd tl_hd : α} {tl_tl : Seq α}
    (h : Pairwise R (cons hd (cons tl_hd tl_tl))) :
    R hd tl_hd := by
  simp only [Pairwise] at h
  simpa using h 0 1 Nat.one_pos

/--
theorem `Pairwise.cons_cons_of_trans` / 定理 `Pairwise.cons_cons_of_trans`

English:
theorem Pairwise.cons_cons_of_trans
  statement: {R : α -> α -> Prop} [IsTrans _ R] {hd tl_hd : α} {tl_tl : Seq α}
  proof: by
  apply Pairwise.cons _ h_tl
  simp only [mem_cons_iff, forall_eq_or_imp]
  exact ⟨h_hd, fun x hx => Trans.simple h_hd ((cons_elim h_tl).left x hx)⟩

中文:
定理 两两.cons_cons_of_trans
  结论: {R : α -> α -> 命题} [是Trans _ R] {hd tl_hd : α} {tl_tl : 序列 α}
  证明: by
  apply Pairwise.cons _ h_tl
  simp only [mem_cons_iff, forall_eq_or_imp]
  exact ⟨h_hd, fun x hx => Trans.simple h_hd ((cons_elim h_tl).left x hx)⟩
-/
theorem Pairwise.cons_cons_of_trans {R : α -> α -> Prop} [IsTrans _ R] {hd tl_hd : α} {tl_tl : Seq α}
    (h_hd : R hd tl_hd)
    (h_tl : Pairwise R (.cons tl_hd tl_tl)) : Pairwise R (.cons hd (.cons tl_hd tl_tl)) := by
  apply Pairwise.cons _ h_tl
  simp only [mem_cons_iff, forall_eq_or_imp]
  exact ⟨h_hd, fun x hx => Trans.simple h_hd ((cons_elim h_tl).left x hx)⟩


/--
theorem `Pairwise.coind` / 定理 `Pairwise.coind`

English:
theorem Pairwise.coind
  statement: {R : α -> α -> Prop} {s : Seq α}
  proof: by
  simp only [Pairwise]
  intro i j h_ij x hx y hy
  obtain ⟨k, hj⟩ := Nat.exists_eq_add_of_lt h_ij
  rw [← head_dropn] at hx
  rw [hj]; rw [← head_dropn]; rw [Nat.add_assoc]; rw [dropn_add]; rw [head_dropn] at hy
  have := all_coind_drop_motive motive base (fun hd tl ih => (step hd tl ih).right) 

中文:
定理 两两.coind
  结论: {R : α -> α -> 命题} {s : 序列 α}
  证明: by
  simp only [Pairwise]
  intro i j h_ij x hx y hy
  obtain ⟨k, hj⟩ := Nat.exists_eq_add_of_lt h_ij
  rw [← head_dropn] at hx
  rw [hj]; rw [← head_dropn]; rw [Nat.add_assoc]; rw [dropn_add]; rw [head_dropn] at hy
  have := all_coind_drop_motive motive base (fun hd tl ih => (step hd tl ih).right) 

Depends on / 依赖: Nat.add_assoc, Nat.exists_eq_add_of_lt, Option.mem_def, Option.some.injEq, Pairwise, _cons_succ, add_assoc, all_coind_drop_motive, all_get, dropn_add, exists_eq_add_of_lt, generalize, h_ij, head_cons, head_dropn, mem_def, motive, s.drop
-/
theorem Pairwise.coind {R : α -> α -> Prop} {s : Seq α}
    (motive : Seq α -> Prop) (base : motive s)
    (step : forall hd tl, motive (.cons hd tl) -> (forall x in tl, R hd x) ∧ motive tl) : Pairwise R s := by
  simp only [Pairwise]
  intro i j h_ij x hx y hy
  obtain ⟨k, hj⟩ := Nat.exists_eq_add_of_lt h_ij
  rw [← head_dropn] at hx
  rw [hj]; rw [← head_dropn]; rw [Nat.add_assoc]; rw [dropn_add]; rw [head_dropn] at hy
  have := all_coind_drop_motive motive base (fun hd tl ih => (step hd tl ih).right) i
  generalize s.drop i = s' at *
  cases s' with
  | nil => simp at hx
  | cons hd tl =>
    simp only [head_cons, Option.mem_def, Option.some.injEq, get?_cons_succ] at hx hy
    exact hx ▸ all_get (step hd tl this).left hy

/--
theorem `Pairwise.coind_trans` / 定理 `Pairwise.coind_trans`

English:
theorem Pairwise.coind_trans
  statement: {R : α -> α -> Prop} [IsTrans α R] {s : Seq α}
  proof: by
  have h_succ {n} {x y} (hx : s.get? n = some x) (hy : s.get? (n + 1) = some y) : R x y := by
    rw [← head_dropn] at hx
    have := all_coind_drop_motive motive base (fun hd tl ih => (step hd tl ih).right)
    exact (step x (s.drop (n + 1)) (head_eq_some hx ▸ this n)).left _ (by simpa)
  simp o

中文:
定理 两两.coind_trans
  结论: {R : α -> α -> 命题} [是Trans α R] {s : 序列 α}
  证明: by
  have h_succ {n} {x y} (hx : s.get? n = some x) (hy : s.get? (n + 1) = some y) : R x y := by
    rw [← head_dropn] at hx
    have := all_coind_drop_motive motive base (fun hd tl ih => (step hd tl ih).right)
    exact (step x (s.drop (n + 1)) (head_eq_some hx ▸ this n)).left _ (by simpa)
  simp o

Depends on / 依赖: Nat.exists_eq_add_of_lt, Pairwise, all_coind_drop_motive, exists_eq_add_of_lt, ge_stable, generalizing, h_ij, h_succ, head_dropn, head_eq_some, motive, s.drop, s.get
-/
theorem Pairwise.coind_trans {R : α -> α -> Prop} [IsTrans α R] {s : Seq α}
    (motive : Seq α -> Prop) (base : motive s)
    (step : forall hd tl, motive (.cons hd tl) -> (forall x in tl.head, R hd x) ∧ motive tl) :
    Pairwise R s := by
  have h_succ {n} {x y} (hx : s.get? n = some x) (hy : s.get? (n + 1) = some y) : R x y := by
    rw [← head_dropn] at hx
    have := all_coind_drop_motive motive base (fun hd tl ih => (step hd tl ih).right)
    exact (step x (s.drop (n + 1)) (head_eq_some hx ▸ this n)).left _ (by simpa)
  simp only [Pairwise]
  intro i j h_ij x hx y hy
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h_ij
  clear h_ij
  induction k generalizing y with
  | zero => exact h_succ hx hy
  | succ k ih =>
    obtain ⟨z, hz⟩ := ge_stable (m := i + k + 1) _ (by lia) hy
exact _root_.trans (ih z hz) h_succ hz hy

/--
theorem `Pairwise_tail` / 定理 `Pairwise_tail`

English:
theorem Pairwise_tail
  given: {R : α -> α -> Prop} {s : Seq α} (h : s.Pairwise R)
  proof: by
  cases s
  · simp
  · simp [h.cons_elim.right]

中文:
定理 Pairwise_tail
  条件: {R : α -> α -> 命题} {s : 序列 α} (h : s.两两 R)
  证明: by
  cases s
  · simp
  · simp [h.cons_elim.right]

Depends on / 依赖: cons_elim, h.cons_elim.right
-/
theorem Pairwise_tail {R : α -> α -> Prop} {s : Seq α} (h : s.Pairwise R) :
    s.tail.Pairwise R := by
  cases s
  · simp
  · simp [h.cons_elim.right]

/--
theorem `Pairwise_drop` / 定理 `Pairwise_drop`

English:
theorem Pairwise_drop
  given: {R : α -> α -> Prop} {s : Seq α} (h : s.Pairwise R) {n : Nat}
  proof: by
  induction n with
  | zero => simpa
  | succ m ih => simp [drop, Pairwise_tail ih]

中文:
定理 Pairwise_drop
  条件: {R : α -> α -> 命题} {s : 序列 α} (h : s.两两 R) {n : 自然数}
  证明: by
  induction n with
  | zero => simpa
  | succ m ih => simp [drop, Pairwise_tail ih]

Depends on / 依赖: Pairwise_tail
-/
theorem Pairwise_drop {R : α -> α -> Prop} {s : Seq α} (h : s.Pairwise R) {n : Nat} :
    (s.drop n).Pairwise R := by
  induction n with
  | zero => simpa
  | succ m ih => simp [drop, Pairwise_tail ih]

end Pairwise

/--
theorem `at_least_as_long_as_coind` / 定理 `at_least_as_long_as_coind`

English:
theorem at_least_as_long_as_coind
  statement: {a : Seq α} {b : Seq β}
  proof: by
  have (n) (hb : b.drop n != .nil) : motive (a.drop n) (b.drop n) := by
    induction n with
    | zero => simpa
    | succ m ih =>
      simp only [drop] at hb ⊢
      generalize b.drop m = tb at *
      cases tb with
      | nil => simp at hb
      | cons tb_hd tb_tl =>
        simp only [ne_eq

中文:
定理 at_least_as_long_as_coind
  结论: {a : 序列 α} {b : 序列 β}
  证明: by
  have (n) (hb : b.drop n != .nil) : motive (a.drop n) (b.drop n) := by
    induction n with
    | zero => simpa
    | succ m ih =>
      simp only [drop] at hb ⊢
      generalize b.drop m = tb at *
      cases tb with
      | nil => simp at hb
      | cons tb_hd tb_tl =>
        simp only [ne_eq

Depends on / 依赖: Terminates, _of_not_terminates, _of_terminates, a.Terminates, a.drop, a_hd, a_tl, b.drop, cons_ne_nil, forall_const, generalize, h_tail, length, motive, ne_eq, not_false_eq_true, tb_hd, tb_tl
-/
theorem at_least_as_long_as_coind {a : Seq α} {b : Seq β}
    (motive : Seq α -> Seq β -> Prop) (base : motive a b)
    (step : forall a b, motive a b ->
      (forall b_hd b_tl, (b = .cons b_hd b_tl) -> exists a_hd a_tl, a = .cons a_hd a_tl ∧ motive a_tl b_tl)) :
    b.length' <= a.length' := by
  have (n) (hb : b.drop n != .nil) : motive (a.drop n) (b.drop n) := by
    induction n with
    | zero => simpa
    | succ m ih =>
      simp only [drop] at hb ⊢
      generalize b.drop m = tb at *
      cases tb with
      | nil => simp at hb
      | cons tb_hd tb_tl =>
        simp only [ne_eq, cons_ne_nil, not_false_eq_true, forall_const] at ih
        obtain ⟨a_hd, a_tl, ha, h_tail⟩ := step (a.drop m) (.cons tb_hd tb_tl) ih _ _ rfl
        simpa [ha]
  by_cases ha : a.Terminates; swap
  · simp [length'_of_not_terminates ha]
  simp only [length'_of_terminates ha, length'_le_iff]
  by_contra hb
  have hb_cons : b.drop (a.length ha) != .nil := by
    intro hb'
    simp only [← length'_eq_zero_iff_nil, drop_length', tsub_eq_zero_iff_le, length'_le_iff] at hb'
    contradiction
  specialize this (a.length ha) hb_cons
  generalize b.drop (a.length ha) = b' at *
  cases b' with
  | nil =>
    contradiction
  | cons b_hd b_tl =>
    obtain ⟨a_hd, a_tl, ha', _⟩ := step _ _ this _ _ rfl
    apply_fun length' at ha'
    simp only [drop_length', length'_of_terminates ha, tsub_self, length'_cons] at ha'
    generalize a_tl.length' = u at ha'
    enat_to_nat
    lia

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Functor Seq
  body: @map

中文:
实例 :
  签名: 函子 序列
  定义体: @map
-/
instance : Functor Seq where map := @map

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulFunctor Seq
  body: @map_id
  comp_map := @map_comp
  map_const := rfl

中文:
实例 :
  签名: Lawful函子 序列
  定义体: @map_id
  comp_map := @map_comp
  map_const := rfl

Depends on / 依赖: map_id
-/
instance : LawfulFunctor Seq where
  id_map := @map_id
  comp_map := @map_comp
  map_const := rfl

end Seq

namespace Seq1

variable {α : Type u} {β : Type v} {γ : Type w}

open Stream'.Seq

/--
Definition of `toSeq` / `toSeq` 的定义

English:
definition toSeq
  signature: : Seq1 α -> Seq α

中文:
定义 toSeq
  签名: : Seq1 α -> 序列 α
-/
def toSeq : Seq1 α -> Seq α
  | (a, s) => Seq.cons a s

/--
Instance `coeSeq` / 实例 `coeSeq`

English:
instance coeSeq
  signature: : Coe (Seq1 α) (Seq α)
  body: ⟨toSeq⟩

中文:
实例 coeSeq
  签名: : Coe (Seq1 α) (序列 α)
  定义体: ⟨toSeq⟩
-/
instance coeSeq : Coe (Seq1 α) (Seq α) :=
  ⟨toSeq⟩

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : α -> β)

中文:
定义 map
  签名: (f : α -> β)
-/
def map (f : α -> β) : Seq1 α -> Seq1 β
  | (a, s) => (f a, Seq.map f s)

/--
theorem `map_pair` / 定理 `map_pair`

English:
theorem map_pair
  given: {f : α -> β} {a s}
  statement: map f (a, s) = (f a, Seq.map f s)
  proof: rfl

中文:
定理 map_pair
  条件: {f : α -> β} {a s}
  结论: map f (a, s) = (f a, 序列.map f s)
  证明: rfl

Depends on / 依赖: NormedAddCommGroup, Shrink, hf.small
-/
theorem map_pair {f : α -> β} {a s} : map f (a, s) = (f a, Seq.map f s) := rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  statement: forall s : Seq1 α, map id s = s

中文:
定理 map_id
  结论: 对任意 s : Seq1 α, map id s = s

Depends on / 依赖: NormedSpace, Shrink, hf.small
-/
theorem map_id : forall s : Seq1 α, map id s = s
  | ⟨a, s⟩ => by simp [map]

/--
Definition of `join` / `join` 的定义

English:
definition join
  signature: : Seq1 (Seq1 α) -> Seq1 α

中文:
定义 join
  签名: : Seq1 (Seq1 α) -> Seq1 α
-/
def join : Seq1 (Seq1 α) -> Seq1 α
  | ((a, s), S) =>
    match destruct s with
    | none => (a, Seq.join S)
    | some s' => (a, Seq.join (Seq.cons s' S))

@[simp]
/--
theorem `join_nil` / 定理 `join_nil`

English:
theorem join_nil
  given: (a : α) (S)
  statement: join ((a, nil), S) = (a, Seq.join S)
  proof: rfl

@[simp]

中文:
定理 join_nil
  条件: (a : α) (S)
  结论: join ((a, nil), S) = (a, 序列.join S)
  证明: rfl

@[simp]
-/
theorem join_nil (a : α) (S) : join ((a, nil), S) = (a, Seq.join S) :=
  rfl

@[simp]
/--
theorem `join_cons` / 定理 `join_cons`

English:
theorem join_cons
  given: (a b : α) (s S)
  proof: by
  dsimp [join]; rw [destruct_cons]

中文:
定理 join_cons
  条件: (a b : α) (s S)
  证明: by
  dsimp [join]; rw [destruct_cons]

Depends on / 依赖: destruct_cons
-/
theorem join_cons (a b : α) (s S) :
    join ((a, Seq.cons b s), S) = (a, Seq.join (Seq.cons (b, s) S)) := by
  dsimp [join]; rw [destruct_cons]

/--
Definition of `ret` / `ret` 的定义

English:
definition ret
  signature: (a : α)
  body: (a, nil)

中文:
定义 ret
  签名: (a : α)
  定义体: (a, nil)
-/
def ret (a : α) : Seq1 α :=
  (a, nil)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: α] : Inhabited (Seq1 α)
  body: ⟨ret default⟩

中文:
实例 [可居
  签名: α] : 可居 (Seq1 α)
  定义体: ⟨ret default⟩
-/
instance [Inhabited α] : Inhabited (Seq1 α) :=
  ⟨ret default⟩

/--
Definition of `bind` / `bind` 的定义

English:
definition bind
  signature: (s : Seq1 α) (f : α -> Seq1 β)
  body: join (map f s)

@[simp]

中文:
定义 bind
  签名: (s : Seq1 α) (f : α -> Seq1 β)
  定义体: join (map f s)

@[simp]
-/
def bind (s : Seq1 α) (f : α -> Seq1 β) : Seq1 β :=
  join (map f s)

@[simp]
/--
theorem `join_map_ret` / 定理 `join_map_ret`

English:
theorem join_map_ret
  given: (s : Seq α)
  statement: Seq.join (Seq.map ret s) = s
  proof: by
  apply coinduction2 s; intro s; cases s <;> simp [ret]

中文:
定理 join_map_ret
  条件: (s : 序列 α)
  结论: 序列.join (序列.map ret s) = s
  证明: by
  apply coinduction2 s; intro s; cases s <;> simp [ret]

Depends on / 依赖: coinduction2
-/
theorem join_map_ret (s : Seq α) : Seq.join (Seq.map ret s) = s := by
  apply coinduction2 s; intro s; cases s <;> simp [ret]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `bind_ret` / 定理 `bind_ret`

English:
theorem bind_ret
  given: (f : α -> β)
  statement: forall s, bind s (ret ∘ f) = map f s

中文:
定理 bind_ret
  条件: (f : α -> β)
  结论: 对任意 s, bind s (ret ∘ f) = map f s
-/
theorem bind_ret (f : α -> β) : forall s, bind s (ret ∘ f) = map f s
  | ⟨a, s⟩ => by simp [bind, map, map_comp, ret]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `ret_bind` / 定理 `ret_bind`

English:
theorem ret_bind
  given: (a : α) (f : α -> Seq1 β)
  statement: bind (ret a) f = f a
  proof: by
  simp only [bind, map, ret.eq_1, map_nil]
  obtain ⟨a, s⟩ := f a
  cases s <;> simp

中文:
定理 ret_bind
  条件: (a : α) (f : α -> Seq1 β)
  结论: bind (ret a) f = f a
  证明: by
  simp only [bind, map, ret.eq_1, map_nil]
  obtain ⟨a, s⟩ := f a
  cases s <;> simp

Depends on / 依赖: eq_1, map_nil, ret.eq_1
-/
theorem ret_bind (a : α) (f : α -> Seq1 β) : bind (ret a) f = f a := by
  simp only [bind, map, ret.eq_1, map_nil]
  obtain ⟨a, s⟩ := f a
  cases s <;> simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `map_join'` / 定理 `map_join'`

English:
theorem map_join'
  given: (f : α -> β) (S)
  statement: Seq.map f (Seq.join S) = Seq.join (Seq.map (map f) S)
  proof: by
  apply
    Seq.eq_of_bisim fun s1 s2 =>
      exists s S,
        s1 = Seq.append s (Seq.map f (Seq.join S)) ∧ s2 = append s (Seq.join (Seq.map (map f) S))
  · rintro s1 s2 ⟨s, S, rfl, rfl⟩
    cases s with
    | nil =>
      cases S with
      | nil => simp
      | cons x S =>
        obtain ⟨a

中文:
定理 map_join'
  条件: (f : α -> β) (S)
  结论: 序列.map f (序列.join S) = 序列.join (序列.map (map f) S)
  证明: by
  apply
    Seq.eq_of_bisim fun s1 s2 =>
      exists s S,
        s1 = Seq.append s (Seq.map f (Seq.join S)) ∧ s2 = append s (Seq.join (Seq.map (map f) S))
  · rintro s1 s2 ⟨s, S, rfl, rfl⟩
    cases s with
    | nil =>
      cases S with
      | nil => simp
      | cons x S =>
        obtain ⟨a

Depends on / 依赖: Seq.append, Seq.eq_of_bisim, Seq.join, Seq.map, append, eq_of_bisim
-/
theorem map_join' (f : α -> β) (S) : Seq.map f (Seq.join S) = Seq.join (Seq.map (map f) S) := by
  apply
    Seq.eq_of_bisim fun s1 s2 =>
      exists s S,
        s1 = Seq.append s (Seq.map f (Seq.join S)) ∧ s2 = append s (Seq.join (Seq.map (map f) S))
  · rintro s1 s2 ⟨s, S, rfl, rfl⟩
    cases s with
    | nil =>
      cases S with
      | nil => simp
      | cons x S =>
        obtain ⟨a, s⟩ := x
        simpa [map] using ⟨_, _, rfl, rfl⟩
    | cons _ s => simpa using ⟨s, S, rfl, rfl⟩
  · simpa using ⟨nil, S, by simp, by simp⟩

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `map_join` / 定理 `map_join`

English:
theorem map_join
  given: (f : α -> β)
  statement: forall S, map f (join S) = join (map (map f) S)

中文:
定理 map_join
  条件: (f : α -> β)
  结论: 对任意 S, map f (join S) = join (map (map f) S)
-/
theorem map_join (f : α -> β) : forall S, map f (join S) = join (map (map f) S)
  | ((a, s), S) => by cases s <;> simp [map]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `join_join` / 定理 `join_join`

English:
theorem join_join
  given: (SS : Seq (Seq1 (Seq1 α)))
  proof: by
  apply
    Seq.eq_of_bisim fun s1 s2 =>
      exists s SS,
        s1 = Seq.append s (Seq.join (Seq.join SS)) ∧ s2 = Seq.append s (Seq.join (Seq.map join SS))
  · rintro s1 s2 ⟨s, SS, rfl, rfl⟩
    cases s with
    | nil =>
      cases SS with
      | nil => simp
      | cons S SS =>
        obt

中文:
定理 join_join
  条件: (SS : 序列 (Seq1 (Seq1 α)))
  证明: by
  apply
    Seq.eq_of_bisim fun s1 s2 =>
      exists s SS,
        s1 = Seq.append s (Seq.join (Seq.join SS)) ∧ s2 = Seq.append s (Seq.join (Seq.map join SS))
  · rintro s1 s2 ⟨s, SS, rfl, rfl⟩
    cases s with
    | nil =>
      cases SS with
      | nil => simp
      | cons S SS =>
        obt

Depends on / 依赖: Seq.append, Seq.cons, Seq.eq_of_bisim, Seq.join, Seq.map, append, eq_of_bisim
-/
theorem join_join (SS : Seq (Seq1 (Seq1 α))) :
    Seq.join (Seq.join SS) = Seq.join (Seq.map join SS) := by
  apply
    Seq.eq_of_bisim fun s1 s2 =>
      exists s SS,
        s1 = Seq.append s (Seq.join (Seq.join SS)) ∧ s2 = Seq.append s (Seq.join (Seq.map join SS))
  · rintro s1 s2 ⟨s, SS, rfl, rfl⟩
    cases s with
    | nil =>
      cases SS with
      | nil => simp
      | cons S SS =>
        obtain ⟨⟨x, s⟩, S⟩ := S
        cases s with
        | nil => simpa using ⟨_, _, rfl, rfl⟩
        | cons x s => simpa using ⟨Seq.cons x (append s (Seq.join S)), SS, by simp, by simp⟩
    | cons _ s => simpa using ⟨s, SS, rfl, rfl⟩
  · simpa using ⟨nil, SS, by simp, by simp⟩

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `bind_assoc` / 定理 `bind_assoc`

English:
theorem bind_assoc
  given: (s : Seq1 α) (f : α -> Seq1 β) (g : β -> Seq1 γ)
  proof: by
  obtain ⟨a, s⟩ := s
  simp only [bind, map_pair, map_join]
  rw [← map_comp]
  simp only [show (fun x => join (map g (f x))) = join ∘ (map g ∘ f) from rfl]
  rw [map_comp _ join]
  generalize Seq.map (map g ∘ f) s = SS
  rcases map g (f a) with ⟨⟨a, s⟩, S⟩
  induction s using recOn with | nil =>

中文:
定理 bind_assoc
  条件: (s : Seq1 α) (f : α -> Seq1 β) (g : β -> Seq1 γ)
  证明: by
  obtain ⟨a, s⟩ := s
  simp only [bind, map_pair, map_join]
  rw [← map_comp]
  simp only [show (fun x => join (map g (f x))) = join ∘ (map g ∘ f) from rfl]
  rw [map_comp _ join]
  generalize Seq.map (map g ∘ f) s = SS
  rcases map g (f a) with ⟨⟨a, s⟩, S⟩
  induction s using recOn with | nil =>

Depends on / 依赖: Seq.map, generalize, map_comp, map_join, map_pair
-/
theorem bind_assoc (s : Seq1 α) (f : α -> Seq1 β) (g : β -> Seq1 γ) :
    bind (bind s f) g = bind s fun x : α => bind (f x) g := by
  obtain ⟨a, s⟩ := s
  simp only [bind, map_pair, map_join]
  rw [← map_comp]
  simp only [show (fun x => join (map g (f x))) = join ∘ (map g ∘ f) from rfl]
  rw [map_comp _ join]
  generalize Seq.map (map g ∘ f) s = SS
  rcases map g (f a) with ⟨⟨a, s⟩, S⟩
  induction s using recOn with | nil => ?_ | cons x s_1 => ?_ <;>
  induction S using recOn with | nil => simp | cons x_1 s_2 => ?_
  · obtain ⟨x, t⟩ := x_1
    cases t <;> simp
  · obtain ⟨y, t⟩ := x_1; simp

/--
Instance `monad` / 实例 `monad`

English:
instance monad
  signature: : Monad Seq1 where
  body: @map
  pure := @ret
  bind := @bind

中文:
实例 monad
  签名: : 单子 Seq1 where
  定义体: @map
  pure := @ret
  bind := @bind
-/
instance monad : Monad Seq1 where
  map := @map
  pure := @ret
  bind := @bind

/--
Instance `lawfulMonad` / 实例 `lawfulMonad`

English:
instance lawfulMonad
  signature: : LawfulMonad Seq1
  body: LawfulMonad.mk'
  (id_map := @map_id)
  (bind_pure_comp := @bind_ret)
  (pure_bind := @ret_bind)
  (bind_assoc := @bind_assoc)

中文:
实例 lawfulMonad
  签名: : 合法单子 Seq1
  定义体: LawfulMonad.mk'
  (id_map := @map_id)
  (bind_pure_comp := @bind_ret)
  (pure_bind := @ret_bind)
  (bind_assoc := @bind_assoc)

Depends on / 依赖: LawfulMonad, LawfulMonad.mk
-/
instance lawfulMonad : LawfulMonad Seq1 := LawfulMonad.mk'
  (id_map := @map_id)
  (bind_pure_comp := @bind_ret)
  (pure_bind := @ret_bind)
  (bind_assoc := @bind_assoc)

end Seq1

end Stream'
