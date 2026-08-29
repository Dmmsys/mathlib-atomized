/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Data.List.Chain
public import Mathlib.Data.List.Flatten

/-!
# Split a list into contiguous runs of elements which pairwise satisfy a relation.

This file provides the basic API for `List.splitBy` which is defined in Core.
The main results are the following:

- `List.flatten_splitBy`: the lists in `List.splitBy` join to the original list.
- `List.nil_notMem_splitBy`: the empty list is not contained in `List.splitBy`.
- `List.isChain_of_mem_splitBy`: any two adjacent elements in a list in
  `List.splitBy` are related by the specified relation.
- `List.isChain_getLast_head_splitBy`: the last element of each list in `List.splitBy` is not
  related to the first element of the next list.
-/

public section

namespace List

variable {α : Type*} {m : List α}

@[simp]
/--
theorem `splitBy_nil` / 定理 `splitBy_nil`

English:
theorem splitBy_nil
  given: (r : α -> α -> Bool)
  statement: splitBy r [] = []
  proof: rfl

中文:
定理 splitBy_nil
  条件: (r : α -> α -> 布尔)
  结论: splitBy r [] = []
  证明: rfl
-/
theorem splitBy_nil (r : α -> α -> Bool) : splitBy r [] = [] :=
  rfl

/--
theorem `splitByLoop_eq_append` / 定理 `splitByLoop_eq_append`

English:
theorem splitByLoop_eq_append
  statement: {r : α -> α -> Bool} {l : List α} {a : α} {g : List α}
  proof: by
  induction l generalizing a g gs with
  | nil => simp [splitBy.loop]
  | cons b l IH =>
    simp_rw [splitBy.loop]
    split <;> rw [IH]
    conv_rhs => rw [IH]
    simp

中文:
定理 splitByLoop_eq_append
  结论: {r : α -> α -> 布尔} {l : List α} {a : α} {g : List α}
  证明: by
  induction l generalizing a g gs with
  | nil => simp [splitBy.loop]
  | cons b l IH =>
    simp_rw [splitBy.loop]
    split <;> rw [IH]
    conv_rhs => rw [IH]
    simp
-/
private theorem splitByLoop_eq_append {r : α -> α -> Bool} {l : List α} {a : α} {g : List α}
    (gs : List (List α)) : splitBy.loop r l a g gs = gs.reverse ++ splitBy.loop r l a g [] := by
  induction l generalizing a g gs with
  | nil => simp [splitBy.loop]
  | cons b l IH =>
    simp_rw [splitBy.loop]
    split <;> rw [IH]
    conv_rhs => rw [IH]
    simp

/--
theorem `flatten_splitByLoop` / 定理 `flatten_splitByLoop`

English:
theorem flatten_splitByLoop
  given: {r : α -> α -> Bool} {l : List α} {a : α} {g : List α}
  proof: by
  induction l generalizing a g with
  | nil => simp [splitBy.loop]
  | cons b l IH =>
    rw [splitBy.loop]; rw [splitByLoop_eq_append [_]]
    split <;> simp [IH]

@[simp]

中文:
定理 flatten_splitByLoop
  条件: {r : α -> α -> 布尔} {l : List α} {a : α} {g : List α}
  证明: by
  induction l generalizing a g with
  | nil => simp [splitBy.loop]
  | cons b l IH =>
    rw [splitBy.loop]; rw [splitByLoop_eq_append [_]]
    split <;> simp [IH]

@[simp]
-/
private theorem flatten_splitByLoop {r : α -> α -> Bool} {l : List α} {a : α} {g : List α} :
    (splitBy.loop r l a g []).flatten = g.reverse ++ a :: l := by
  induction l generalizing a g with
  | nil => simp [splitBy.loop]
  | cons b l IH =>
    rw [splitBy.loop]; rw [splitByLoop_eq_append [_]]
    split <;> simp [IH]

@[simp]
/--
theorem `flatten_splitBy` / 定理 `flatten_splitBy`

English:
theorem flatten_splitBy
  given: (r : α -> α -> Bool) (l : List α)
  statement: (l.splitBy r).flatten = l
  proof: match l with
  | nil => rfl
  | cons _ _ => flatten_splitByLoop

@[simp]

中文:
定理 flatten_splitBy
  条件: (r : α -> α -> 布尔) (l : List α)
  结论: (l.splitBy r).flatten = l
  证明: match l with
  | nil => rfl
  | cons _ _ => flatten_splitByLoop

@[simp]

Depends on / 依赖: flatten_splitByLoop
-/
theorem flatten_splitBy (r : α -> α -> Bool) (l : List α) : (l.splitBy r).flatten = l :=
  match l with
  | nil => rfl
  | cons _ _ => flatten_splitByLoop

@[simp]
/--
theorem `splitBy_eq_nil` / 定理 `splitBy_eq_nil`

English:
theorem splitBy_eq_nil
  given: {r : α -> α -> Bool} {l : List α}
  statement: l.splitBy r = [] ↔ l = []
  proof: by
  have := flatten_splitBy r l
  refine ⟨fun _ => ?_, ?_⟩ <;> simp_all

中文:
定理 splitBy_eq_nil
  条件: {r : α -> α -> 布尔} {l : List α}
  结论: l.splitBy r = [] ↔ l = []
  证明: by
  have := flatten_splitBy r l
  refine ⟨fun _ => ?_, ?_⟩ <;> simp_all

Depends on / 依赖: flatten_splitBy
-/
theorem splitBy_eq_nil {r : α -> α -> Bool} {l : List α} : l.splitBy r = [] ↔ l = [] := by
  have := flatten_splitBy r l
  refine ⟨fun _ => ?_, ?_⟩ <;> simp_all

/--
theorem `splitBy_ne_nil` / 定理 `splitBy_ne_nil`

English:
theorem splitBy_ne_nil
  given: {r : α -> α -> Bool} {l : List α}
  statement: l.splitBy r != [] ↔ l != []
  proof: splitBy_eq_nil.not

中文:
定理 splitBy_ne_nil
  条件: {r : α -> α -> 布尔} {l : List α}
  结论: l.splitBy r != [] ↔ l != []
  证明: splitBy_eq_nil.not

Depends on / 依赖: splitBy_eq_nil, splitBy_eq_nil.not
-/
theorem splitBy_ne_nil {r : α -> α -> Bool} {l : List α} : l.splitBy r != [] ↔ l != [] :=
  splitBy_eq_nil.not

/--
theorem `nil_notMem_splitByLoop` / 定理 `nil_notMem_splitByLoop`

English:
theorem nil_notMem_splitByLoop
  given: {r : α -> α -> Bool} {l : List α} {a : α} {g : List α}
  proof: by
  induction l generalizing a g with
  | nil => simp [splitBy.loop]
  | cons b l IH =>
    rw [splitBy.loop]
    split
    · exact IH
    · rw [splitByLoop_eq_append, mem_append]
      simpa using IH

@[simp]

中文:
定理 nil_notMem_splitByLoop
  条件: {r : α -> α -> 布尔} {l : List α} {a : α} {g : List α}
  证明: by
  induction l generalizing a g with
  | nil => simp [splitBy.loop]
  | cons b l IH =>
    rw [splitBy.loop]
    split
    · exact IH
    · rw [splitByLoop_eq_append, mem_append]
      simpa using IH

@[simp]
-/
private theorem nil_notMem_splitByLoop {r : α -> α -> Bool} {l : List α} {a : α} {g : List α} :
    [] ∉ splitBy.loop r l a g [] := by
  induction l generalizing a g with
  | nil => simp [splitBy.loop]
  | cons b l IH =>
    rw [splitBy.loop]
    split
    · exact IH
    · rw [splitByLoop_eq_append, mem_append]
      simpa using IH

@[simp]
/--
theorem `nil_notMem_splitBy` / 定理 `nil_notMem_splitBy`

English:
theorem nil_notMem_splitBy
  given: (r : α -> α -> Bool) (l : List α)
  statement: [] ∉ l.splitBy r
  proof: match l with
  | nil => not_mem_nil
  | cons _ _ => nil_notMem_splitByLoop

中文:
定理 nil_notMem_splitBy
  条件: (r : α -> α -> 布尔) (l : List α)
  结论: [] ∉ l.splitBy r
  证明: match l with
  | nil => not_mem_nil
  | cons _ _ => nil_notMem_splitByLoop

Depends on / 依赖: nil_notMem_splitByLoop, not_mem_nil
-/
theorem nil_notMem_splitBy (r : α -> α -> Bool) (l : List α) : [] ∉ l.splitBy r :=
  match l with
  | nil => not_mem_nil
  | cons _ _ => nil_notMem_splitByLoop

/--
theorem `ne_nil_of_mem_splitBy` / 定理 `ne_nil_of_mem_splitBy`

English:
theorem ne_nil_of_mem_splitBy
  given: {r : α -> α -> Bool} {l : List α} (h : m in l.splitBy r)
  statement: m != []
  proof: fun _ => by simp_all

中文:
定理 ne_nil_of_mem_splitBy
  条件: {r : α -> α -> 布尔} {l : List α} (h : m in l.splitBy r)
  结论: m != []
  证明: fun _ => by simp_all
-/
theorem ne_nil_of_mem_splitBy {r : α -> α -> Bool} {l : List α} (h : m in l.splitBy r) : m != [] :=
  fun _ => by simp_all

/--
theorem `head_head_splitBy` / 定理 `head_head_splitBy`

English:
theorem head_head_splitBy
  given: (r : α -> α -> Bool) {l : List α} (hn : l != [])
  proof: by
  simp [head_head_eq_head_flatten]

中文:
定理 head_head_splitBy
  条件: (r : α -> α -> 布尔) {l : List α} (hn : l != [])
  证明: by
  simp [head_head_eq_head_flatten]

Depends on / 依赖: head_head_eq_head_flatten
-/
theorem head_head_splitBy (r : α -> α -> Bool) {l : List α} (hn : l != []) :
    ((l.splitBy r).head (splitBy_ne_nil.2 hn)).head
      (ne_nil_of_mem_splitBy (head_mem _)) = l.head hn := by
  simp [head_head_eq_head_flatten]

/--
theorem `getLast_getLast_splitBy` / 定理 `getLast_getLast_splitBy`

English:
theorem getLast_getLast_splitBy
  given: (r : α -> α -> Bool) {l : List α} (hn : l != [])
  proof: by
  simp [getLast_getLast_eq_getLast_flatten]

中文:
定理 getLast_getLast_splitBy
  条件: (r : α -> α -> 布尔) {l : List α} (hn : l != [])
  证明: by
  simp [getLast_getLast_eq_getLast_flatten]

Depends on / 依赖: getLast_getLast_eq_getLast_flatten
-/
theorem getLast_getLast_splitBy (r : α -> α -> Bool) {l : List α} (hn : l != []) :
    ((l.splitBy r).getLast (splitBy_ne_nil.2 hn)).getLast
      (ne_nil_of_mem_splitBy (getLast_mem _)) = l.getLast hn := by
  simp [getLast_getLast_eq_getLast_flatten]

/--
theorem `isChain_of_mem_splitByLoop` / 定理 `isChain_of_mem_splitByLoop`

English:
theorem isChain_of_mem_splitByLoop
  statement: {r : α -> α -> Bool} {l : List α} {a : α} {g : List α}
  proof: by
  induction l generalizing a g with
  | nil =>
    rw [splitBy.loop]; rw [reverse_cons]; rw [mem_append]; rw [mem_reverse]; rw [mem_singleton] at h
    obtain hm | rfl := h
    · cases not_mem_nil hm
    · apply List.isChain_reverse.1
      rw [reverse_reverse]
      exact isChain_cons.2 ⟨hga, hg

中文:
定理 isChain_of_mem_splitByLoop
  结论: {r : α -> α -> 布尔} {l : List α} {a : α} {g : List α}
  证明: by
  induction l generalizing a g with
  | nil =>
    rw [splitBy.loop]; rw [reverse_cons]; rw [mem_append]; rw [mem_reverse]; rw [mem_singleton] at h
    obtain hm | rfl := h
    · cases not_mem_nil hm
    · apply List.isChain_reverse.1
      rw [reverse_reverse]
      exact isChain_cons.2 ⟨hga, hg
-/
private theorem isChain_of_mem_splitByLoop {r : α -> α -> Bool} {l : List α} {a : α} {g : List α}
    (hga : forall b in g.head?, r b a) (hg : g.IsChain fun y x => r x y)
    (h : m in splitBy.loop r l a g []) : m.IsChain fun x y => r x y := by
  induction l generalizing a g with
  | nil =>
    rw [splitBy.loop]; rw [reverse_cons]; rw [mem_append]; rw [mem_reverse]; rw [mem_singleton] at h
    obtain hm | rfl := h
    · cases not_mem_nil hm
    · apply List.isChain_reverse.1
      rw [reverse_reverse]
      exact isChain_cons.2 ⟨hga, hg⟩
  | cons b l IH =>
    simp only [splitBy.loop, reverse_cons] at h
    split at h
    · apply IH _ (isChain_cons.2 ⟨hga, hg⟩) h
      grind
    · rw [splitByLoop_eq_append, mem_append, reverse_singleton, mem_singleton] at h
      obtain rfl | hm := h
      · apply List.isChain_reverse.1
        rw [reverse_append]; rw [reverse_cons]; rw [reverse_nil]; rw [nil_append]; rw [reverse_reverse]
        exact isChain_cons.2 ⟨hga, hg⟩
      · grind

/--
theorem `isChain_of_mem_splitBy` / 定理 `isChain_of_mem_splitBy`

English:
theorem isChain_of_mem_splitBy
  given: {r : α -> α -> Bool} {l : List α} (h : m in l.splitBy r)
  proof: by
  match l, h with
  | a::l, h => apply isChain_of_mem_splitByLoop _ _ h <;> simp

中文:
定理 isChain_of_mem_splitBy
  条件: {r : α -> α -> 布尔} {l : List α} (h : m in l.splitBy r)
  证明: by
  match l, h with
  | a::l, h => apply isChain_of_mem_splitByLoop _ _ h <;> simp

Depends on / 依赖: isChain_of_mem_splitByLoop
-/
theorem isChain_of_mem_splitBy {r : α -> α -> Bool} {l : List α} (h : m in l.splitBy r) :
    m.IsChain fun x y => r x y := by
  match l, h with
  | a::l, h => apply isChain_of_mem_splitByLoop _ _ h <;> simp

/--
theorem `isChain_getLast_head_splitByLoop` / 定理 `isChain_getLast_head_splitByLoop`

English:
theorem isChain_getLast_head_splitByLoop
  statement: {r : α -> α -> Bool} (l : List α) {a : α}
  proof: by
  induction l generalizing a g gs with
  | nil =>
    rw [splitBy.loop]; rw [reverse_cons]
    apply List.isChain_reverse.1
    simpa using isChain_cons.2 ⟨hga, hgs⟩
  | cons b l IH =>
    rw [splitBy.loop]
    split
    · refine IH hgs' hgs fun m hm => ?_
      obtain ⟨ha, _, H⟩ := hga m hm
    

中文:
定理 isChain_getLast_head_splitByLoop
  结论: {r : α -> α -> 布尔} (l : List α) {a : α}
  证明: by
  induction l generalizing a g gs with
  | nil =>
    rw [splitBy.loop]; rw [reverse_cons]
    apply List.isChain_reverse.1
    simpa using isChain_cons.2 ⟨hga, hgs⟩
  | cons b l IH =>
    rw [splitBy.loop]
    split
    · refine IH hgs' hgs fun m hm => ?_
      obtain ⟨ha, _, H⟩ := hga m hm
    
-/
private theorem isChain_getLast_head_splitByLoop {r : α -> α -> Bool} (l : List α) {a : α}
    {g : List α} {gs : List (List α)} (hgs' : [] ∉ gs)
    (hgs : gs.IsChain fun b a => exists ha hb, r (a.getLast ha) (b.head hb) = false)
    (hga : forall m in gs.head?, exists ha hb, r (m.getLast ha) ((g.reverse ++ [a]).head hb) = false) :
    (splitBy.loop r l a g gs).IsChain fun a b => exists ha hb, r (a.getLast ha) (b.head hb) = false := by
  induction l generalizing a g gs with
  | nil =>
    rw [splitBy.loop]; rw [reverse_cons]
    apply List.isChain_reverse.1
    simpa using isChain_cons.2 ⟨hga, hgs⟩
  | cons b l IH =>
    rw [splitBy.loop]
    split
    · refine IH hgs' hgs fun m hm => ?_
      obtain ⟨ha, _, H⟩ := hga m hm
      refine ⟨ha, append_ne_nil_of_right_ne_nil _ (cons_ne_nil _ _), ?_⟩
      rwa [reverse_cons, head_append_of_ne_nil]
    · apply IH
      · simpa using hgs'
      · rw [reverse_cons]
        apply isChain_cons.2 ⟨hga, hgs⟩
      · simpa

/--
theorem `isChain_getLast_head_splitBy` / 定理 `isChain_getLast_head_splitBy`

English:
theorem isChain_getLast_head_splitBy
  given: (r : α -> α -> Bool) (l : List α)
  proof: by
  cases l with
  | nil => exact isChain_nil
  | cons _ _ =>
    apply isChain_getLast_head_splitByLoop _ not_mem_nil isChain_nil
    rintro _ ⟨⟩

中文:
定理 isChain_getLast_head_splitBy
  条件: (r : α -> α -> 布尔) (l : List α)
  证明: by
  cases l with
  | nil => exact isChain_nil
  | cons _ _ =>
    apply isChain_getLast_head_splitByLoop _ not_mem_nil isChain_nil
    rintro _ ⟨⟩

Depends on / 依赖: isChain_getLast_head_splitByLoop, isChain_nil, not_mem_nil
-/
theorem isChain_getLast_head_splitBy (r : α -> α -> Bool) (l : List α) :
    (l.splitBy r).IsChain fun a b => exists ha hb, r (a.getLast ha) (b.head hb) = false := by
  cases l with
  | nil => exact isChain_nil
  | cons _ _ =>
    apply isChain_getLast_head_splitByLoop _ not_mem_nil isChain_nil
    rintro _ ⟨⟩

/--
theorem `splitByLoop_append` / 定理 `splitByLoop_append`

English:
theorem splitByLoop_append
  statement: {r : α -> α -> Bool} {l g : List α} {a : α}
  proof: by
  induction l generalizing a g with
  | nil =>
    rw [nil_append]
    cases m with
    | nil => simp [splitBy.loop]
    | cons c m => simp_all [splitBy.loop, splitByLoop_eq_append [_], splitBy]
  | cons b l IH => simp_all [splitBy.loop]

中文:
定理 splitByLoop_append
  结论: {r : α -> α -> 布尔} {l g : List α} {a : α}
  证明: by
  induction l generalizing a g with
  | nil =>
    rw [nil_append]
    cases m with
    | nil => simp [splitBy.loop]
    | cons c m => simp_all [splitBy.loop, splitByLoop_eq_append [_], splitBy]
  | cons b l IH => simp_all [splitBy.loop]
-/
private theorem splitByLoop_append {r : α -> α -> Bool} {l g : List α} {a : α}
    (h : (g.reverse ++ a :: l).IsChain fun x y => r x y)
    (ha : forall x in m.head?, r ((a :: l).getLast (cons_ne_nil a l)) x = false) :
    splitBy.loop r (l ++ m) a g [] = (g.reverse ++ a :: l) :: m.splitBy r := by
  induction l generalizing a g with
  | nil =>
    rw [nil_append]
    cases m with
    | nil => simp [splitBy.loop]
    | cons c m => simp_all [splitBy.loop, splitByLoop_eq_append [_], splitBy]
  | cons b l IH => simp_all [splitBy.loop]

/--
theorem `splitBy_of_isChain` / 定理 `splitBy_of_isChain`

English:
theorem splitBy_of_isChain
  statement: {r : α -> α -> Bool} {l : List α} (hn : l != [])
  proof: by
  cases l with
  | nil => contradiction
  | cons a l => rw [splitBy, ← append_nil l, splitByLoop_append] <;> simp [h]

中文:
定理 splitBy_of_isChain
  结论: {r : α -> α -> 布尔} {l : List α} (hn : l != [])
  证明: by
  cases l with
  | nil => contradiction
  | cons a l => rw [splitBy, ← append_nil l, splitByLoop_append] <;> simp [h]

Depends on / 依赖: append_nil, splitBy, splitByLoop_append
-/
theorem splitBy_of_isChain {r : α -> α -> Bool} {l : List α} (hn : l != [])
    (h : l.IsChain fun x y => r x y) : splitBy r l = [l] := by
  cases l with
  | nil => contradiction
  | cons a l => rw [splitBy, ← append_nil l, splitByLoop_append] <;> simp [h]

/--
theorem `splitBy_append_of_isChain` / 定理 `splitBy_append_of_isChain`

English:
theorem splitBy_append_of_isChain
  statement: {r : α -> α -> Bool} {l : List α} (hn : l != [])
  proof: by
  cases l with
  | nil => contradiction
  | cons a l => rw [cons_append, splitBy, splitByLoop_append h ha]; simp

中文:
定理 splitBy_append_of_isChain
  结论: {r : α -> α -> 布尔} {l : List α} (hn : l != [])
  证明: by
  cases l with
  | nil => contradiction
  | cons a l => rw [cons_append, splitBy, splitByLoop_append h ha]; simp
-/
private theorem splitBy_append_of_isChain {r : α -> α -> Bool} {l : List α} (hn : l != [])
    (h : l.IsChain fun x y => r x y) (ha : forall x in m.head?, r (l.getLast hn) x = false) :
    (l ++ m).splitBy r = l :: m.splitBy r := by
  cases l with
  | nil => contradiction
  | cons a l => rw [cons_append, splitBy, splitByLoop_append h ha]; simp

/--
theorem `splitBy_flatten` / 定理 `splitBy_flatten`

English:
theorem splitBy_flatten
  statement: {r : α -> α -> Bool} {l : List (List α)} (hn : [] ∉ l)
  proof: by
  induction l with
  | nil => rfl
  | cons a l IH =>
    rw [mem_cons]; rw [not_or]; rw [eq_comm] at hn
    rw [flatten_cons]; rw [splitBy_append_of_isChain hn.1 (hc _ mem_cons_self)]; rw [IH hn.2 (fun m hm => hc _ (mem_cons_of_mem a hm)) hc'.tail]
    intro y hy
    rw [← head_of_mem_head? hy]
 

中文:
定理 splitBy_flatten
  结论: {r : α -> α -> 布尔} {l : List (List α)} (hn : [] ∉ l)
  证明: by
  induction l with
  | nil => rfl
  | cons a l IH =>
    rw [mem_cons]; rw [not_or]; rw [eq_comm] at hn
    rw [flatten_cons]; rw [splitBy_append_of_isChain hn.1 (hc _ mem_cons_self)]; rw [IH hn.2 (fun m hm => hc _ (mem_cons_of_mem a hm)) hc'.tail]
    intro y hy
    rw [← head_of_mem_head? hy]
 

Depends on / 依赖: eq_comm, flatten_cons, flatten_ne_nil_iff, head_flatten_eq_head_head, head_mem_head, head_of_mem_head, isChain_cons, l.head, mem_cons, mem_cons_of_mem, mem_cons_self, mem_of_mem_head, ne_nil_of_mem, not_or, splitBy_append_of_isChain
-/
theorem splitBy_flatten {r : α -> α -> Bool} {l : List (List α)} (hn : [] ∉ l)
    (hc : forall m in l, m.IsChain fun x y => r x y)
    (hc' : l.IsChain fun a b => exists ha hb, r (a.getLast ha) (b.head hb) = false) :
    l.flatten.splitBy r = l := by
  induction l with
  | nil => rfl
  | cons a l IH =>
    rw [mem_cons]; rw [not_or]; rw [eq_comm] at hn
    rw [flatten_cons]; rw [splitBy_append_of_isChain hn.1 (hc _ mem_cons_self)]; rw [IH hn.2 (fun m hm => hc _ (mem_cons_of_mem a hm)) hc'.tail]
    intro y hy
    rw [← head_of_mem_head? hy]
    rw [isChain_cons] at hc'
    obtain ⟨x, hx, _⟩ := flatten_ne_nil_iff.1 (ne_nil_of_mem (mem_of_mem_head? hy))
    obtain ⟨_, _, H⟩ := hc'.1 (l.head (ne_nil_of_mem hx)) (head_mem_head? _)
    rwa [head_flatten_eq_head_head]

/--
theorem `splitBy_eq_iff` / 定理 `splitBy_eq_iff`

English:
theorem splitBy_eq_iff
  given: {r : α -> α -> Bool} {l : List (List α)}
  proof: by
  constructor
  · rintro rfl
    exact ⟨(flatten_splitBy r m).symm, nil_notMem_splitBy r m, fun _ => isChain_of_mem_splitBy,
      isChain_getLast_head_splitBy r m⟩
  · rintro ⟨rfl, hn, hc, hc'⟩
    exact splitBy_flatten hn hc hc'

中文:
定理 splitBy_eq_iff
  条件: {r : α -> α -> 布尔} {l : List (List α)}
  证明: by
  constructor
  · rintro rfl
    exact ⟨(flatten_splitBy r m).symm, nil_notMem_splitBy r m, fun _ => isChain_of_mem_splitBy,
      isChain_getLast_head_splitBy r m⟩
  · rintro ⟨rfl, hn, hc, hc'⟩
    exact splitBy_flatten hn hc hc'

Depends on / 依赖: flatten_splitBy, isChain_getLast_head_splitBy, isChain_of_mem_splitBy, nil_notMem_splitBy, splitBy_flatten
-/
theorem splitBy_eq_iff {r : α -> α -> Bool} {l : List (List α)} :
    m.splitBy r = l ↔ m = l.flatten ∧ [] ∉ l ∧ (forall m in l, m.IsChain fun x y => r x y) ∧
      l.IsChain fun a b => exists ha hb, r (a.getLast ha) (b.head hb) = false := by
  constructor
  · rintro rfl
    exact ⟨(flatten_splitBy r m).symm, nil_notMem_splitBy r m, fun _ => isChain_of_mem_splitBy,
      isChain_getLast_head_splitBy r m⟩
  · rintro ⟨rfl, hn, hc, hc'⟩
    exact splitBy_flatten hn hc hc'

/--
theorem `splitBy_append` / 定理 `splitBy_append`

English:
theorem splitBy_append
  statement: {r : α -> α -> Bool} {l m : List α}
  proof: by
  obtain rfl | hl := eq_or_ne l []
  · simp
  obtain rfl | hm := eq_or_ne m []
  · simp
  rw [splitBy_eq_iff]
  refine ⟨by simp, by simp, ?_, ?_⟩; · aesop (add apply unsafe isChain_of_mem_splitBy)
  rw [isChain_append]
  refine ⟨isChain_getLast_head_splitBy _ _, isChain_getLast_head_splitBy _ _, 

中文:
定理 splitBy_append
  结论: {r : α -> α -> 布尔} {l m : List α}
  证明: by
  obtain rfl | hl := eq_or_ne l []
  · simp
  obtain rfl | hm := eq_or_ne m []
  · simp
  rw [splitBy_eq_iff]
  refine ⟨by simp, by simp, ?_, ?_⟩; · aesop (add apply unsafe isChain_of_mem_splitBy)
  rw [isChain_append]
  refine ⟨isChain_getLast_head_splitBy _ _, isChain_getLast_head_splitBy _ _, 

Depends on / 依赖: eq_or_ne, getLast_getLast_splitBy, getLast_mem_g, getLast_of_mem_getLast, isChain_append, isChain_getLast_head_splitBy, isChain_of_mem_splitBy, mem_of_mem_getLast, mem_of_mem_head, ne_nil_of_mem_splitBy, simp_rw, splitBy_eq_iff, unsafe
-/
theorem splitBy_append {r : α -> α -> Bool} {l m : List α}
    (ha : forall x in l.getLast?, forall y in m.head?, r x y = false) :
    (l ++ m).splitBy r = l.splitBy r ++ m.splitBy r := by
  obtain rfl | hl := eq_or_ne l []
  · simp
  obtain rfl | hm := eq_or_ne m []
  · simp
  rw [splitBy_eq_iff]
  refine ⟨by simp, by simp, ?_, ?_⟩; · aesop (add apply unsafe isChain_of_mem_splitBy)
  rw [isChain_append]
  refine ⟨isChain_getLast_head_splitBy _ _, isChain_getLast_head_splitBy _ _, fun x hx y hy => ?_⟩
  use ne_nil_of_mem_splitBy (mem_of_mem_getLast? hx), ne_nil_of_mem_splitBy (mem_of_mem_head? hy)
  apply ha
  · simp_rw [← getLast_of_mem_getLast? hx, getLast_getLast_splitBy _ hl]
    exact getLast_mem_getLast? _
  · simp_rw [← head_of_mem_head? hy, head_head_splitBy _ hm]
    exact head_mem_head? _

/--
theorem `splitBy_append_cons` / 定理 `splitBy_append_cons`

English:
theorem splitBy_append_cons
  statement: {r : α -> α -> Bool} {l : List α} {a : α} (m : List α)
  proof: by
  apply splitBy_append
  simpa

中文:
定理 splitBy_append_cons
  结论: {r : α -> α -> 布尔} {l : List α} {a : α} (m : List α)
  证明: by
  apply splitBy_append
  simpa

Depends on / 依赖: splitBy_append
-/
theorem splitBy_append_cons {r : α -> α -> Bool} {l : List α} {a : α} (m : List α)
    (ha : forall x in l.getLast?, r x a = false) :
    (l ++ a :: m).splitBy r = l.splitBy r ++ (a :: m).splitBy r := by
  apply splitBy_append
  simpa

end List
