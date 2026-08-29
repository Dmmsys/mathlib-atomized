/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Daniel Weber
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

/-!
# Traversing walks

Functions that help access different parts of a walk.

## Main definitions

* `SimpleGraph.Walk.getVert`:
  Get the nth vertex encountered in a walk, or the last one if `n` is too large
* `SimpleGraph.Walk.snd`: The second vertex of a walk, or the only vertex in an empty walk
* `SimpleGraph.Walk.penultimate`:
  The penultimate vertex of a walk, or the only vertex in an empty walk
* `SimpleGraph.Walk.firstDart`: The first dart of a non-empty walk
* `SimpleGraph.Walk.lastDart`: The last dart of a non-empty walk

## Tags
walks
-/

@[expose] public section

namespace SimpleGraph

namespace Walk

universe u
variable {V : Type u} {G : SimpleGraph V} {u v w : V}

/--
Definition of `getVert` / `getVert` 的定义

English:
definition getVert
  signature: {u v : V}

中文:
定义 getVert
  签名: {u v : V}
-/
def getVert {u v : V} : G.Walk u v -> Nat -> V
  | nil, _ => u
  | cons _ _, 0 => u
  | cons _ q, n + 1 => q.getVert n

@[simp]
/--
theorem `getVert_zero` / 定理 `getVert_zero`

English:
theorem getVert_zero
  given: {u v} (w : G.Walk u v)
  statement: w.getVert 0 = u
  proof: by cases w <;> rfl

@[simp]

中文:
定理 getVert_zero
  条件: {u v} (w : G.途径 u v)
  结论: w.getVert 0 = u
  证明: by cases w <;> rfl

@[simp]
-/
theorem getVert_zero {u v} (w : G.Walk u v) : w.getVert 0 = u := by cases w <;> rfl

@[simp]
/--
theorem `getVert_nil` / 定理 `getVert_nil`

English:
theorem getVert_nil
  given: (u : V) {i : Nat}
  statement: (@nil _ G u).getVert i = u
  proof: rfl

中文:
定理 getVert_nil
  条件: (u : V) {i : 自然数}
  结论: (@nil _ G u).getVert i = u
  证明: rfl
-/
theorem getVert_nil (u : V) {i : Nat} : (@nil _ G u).getVert i = u := rfl

/--
theorem `getVert_of_length_le` / 定理 `getVert_of_length_le`

English:
theorem getVert_of_length_le
  given: {u v} (w : G.Walk u v) {i : Nat} (hi : w.length <= i)
  proof: by
  induction w generalizing i with
  | nil => rfl
  | cons _ _ ih =>
    cases i
    · cases hi
    · exact ih (Nat.succ_le_succ_iff.1 hi)

@[simp]

中文:
定理 getVert_of_length_le
  条件: {u v} (w : G.途径 u v) {i : 自然数} (hi : w.length <= i)
  证明: by
  induction w generalizing i with
  | nil => rfl
  | cons _ _ ih =>
    cases i
    · cases hi
    · exact ih (Nat.succ_le_succ_iff.1 hi)

@[simp]

Depends on / 依赖: Nat.succ_le_succ_iff, generalizing, succ_le_succ_iff
-/
theorem getVert_of_length_le {u v} (w : G.Walk u v) {i : Nat} (hi : w.length <= i) :
    w.getVert i = v := by
  induction w generalizing i with
  | nil => rfl
  | cons _ _ ih =>
    cases i
    · cases hi
    · exact ih (Nat.succ_le_succ_iff.1 hi)

@[simp]
/--
theorem `getVert_length` / 定理 `getVert_length`

English:
theorem getVert_length
  given: {u v} (w : G.Walk u v)
  statement: w.getVert w.length = v
  proof: w.getVert_of_length_le rfl.le

中文:
定理 getVert_length
  条件: {u v} (w : G.途径 u v)
  结论: w.getVert w.length = v
  证明: w.getVert_of_length_le rfl.le

Depends on / 依赖: getVert_of_length_le, rfl.le, w.getVert_of_length_le
-/
theorem getVert_length {u v} (w : G.Walk u v) : w.getVert w.length = v :=
  w.getVert_of_length_le rfl.le

/--
theorem `adj_getVert_succ` / 定理 `adj_getVert_succ`

English:
theorem adj_getVert_succ
  given: {u v} (w : G.Walk u v) {i : Nat} (hi : i < w.length)
  proof: by
  induction w generalizing i with
  | nil => cases hi
  | cons hxy _ ih =>
    cases i
    · simp [getVert, hxy]
    · exact ih (Nat.succ_lt_succ_iff.1 hi)

@[simp]

中文:
定理 adj_getVert_succ
  条件: {u v} (w : G.途径 u v) {i : 自然数} (hi : i < w.length)
  证明: by
  induction w generalizing i with
  | nil => cases hi
  | cons hxy _ ih =>
    cases i
    · simp [getVert, hxy]
    · exact ih (Nat.succ_lt_succ_iff.1 hi)

@[simp]

Depends on / 依赖: Nat.succ_lt_succ_iff, generalizing, getVert, succ_lt_succ_iff
-/
theorem adj_getVert_succ {u v} (w : G.Walk u v) {i : Nat} (hi : i < w.length) :
    G.Adj (w.getVert i) (w.getVert (i + 1)) := by
  induction w generalizing i with
  | nil => cases hi
  | cons hxy _ ih =>
    cases i
    · simp [getVert, hxy]
    · exact ih (Nat.succ_lt_succ_iff.1 hi)

@[simp]
/--
lemma `getVert_cons_succ` / 引理 `getVert_cons_succ`

English:
lemma getVert_cons_succ
  given: {u v w n} (p : G.Walk v w) (h : G.Adj u v)
  proof: rfl

中文:
引理 getVert_cons_succ
  条件: {u v w n} (p : G.途径 v w) (h : G.伴随 u v)
  证明: rfl
-/
lemma getVert_cons_succ {u v w n} (p : G.Walk v w) (h : G.Adj u v) :
    (p.cons h).getVert (n + 1) = p.getVert n := rfl

/--
lemma `getVert_cons` / 引理 `getVert_cons`

English:
lemma getVert_cons
  given: {u v w n} (p : G.Walk v w) (h : G.Adj u v) (hn : n != 0)
  proof: by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn
  rw [getVert_cons_succ]; rw [Nat.add_sub_cancel]

@[simp]

中文:
引理 getVert_cons
  条件: {u v w n} (p : G.途径 v w) (h : G.伴随 u v) (hn : n != 0)
  证明: by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn
  rw [getVert_cons_succ]; rw [Nat.add_sub_cancel]

@[simp]

Depends on / 依赖: Nat.add_sub_cancel, Nat.exists_eq_add_one_of_ne_zero, add_sub_cancel, exists_eq_add_one_of_ne_zero, getVert_cons_succ
-/
lemma getVert_cons {u v w n} (p : G.Walk v w) (h : G.Adj u v) (hn : n != 0) :
    (p.cons h).getVert n = p.getVert (n - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn
  rw [getVert_cons_succ]; rw [Nat.add_sub_cancel]

@[simp]
/--
theorem `getVert_mem_support` / 定理 `getVert_mem_support`

English:
theorem getVert_mem_support
  given: {u v : V} (p : G.Walk u v) (i : Nat)
  statement: p.getVert i in p.support
  proof: by
  induction p generalizing i <;> cases i <;> simp [*]

中文:
定理 getVert_mem_support
  条件: {u v : V} (p : G.途径 u v) (i : 自然数)
  结论: p.getVert i in p.support
  证明: by
  induction p generalizing i <;> cases i <;> simp [*]

Depends on / 依赖: generalizing
-/
theorem getVert_mem_support {u v : V} (p : G.Walk u v) (i : Nat) : p.getVert i in p.support := by
  induction p generalizing i <;> cases i <;> simp [*]

/--
lemma `getVert_eq_support_getElem` / 引理 `getVert_eq_support_getElem`

English:
lemma getVert_eq_support_getElem
  given: {u v : V} {n : Nat} (p : G.Walk u v) (h : n <= p.length)
  proof: by
  cases p with
  | nil => simp
  | cons => cases n with
    | zero => simp
    | succ n =>
      simp_rw [support_cons, getVert_cons _ _ n.zero_ne_add_one.symm, List.getElem_cons]
      exact getVert_eq_support_getElem _ (Nat.sub_le_of_le_add h)

中文:
引理 getVert_eq_support_getElem
  条件: {u v : V} {n : 自然数} (p : G.途径 u v) (h : n <= p.length)
  证明: by
  cases p with
  | nil => simp
  | cons => cases n with
    | zero => simp
    | succ n =>
      simp_rw [support_cons, getVert_cons _ _ n.zero_ne_add_one.symm, List.getElem_cons]
      exact getVert_eq_support_getElem _ (Nat.sub_le_of_le_add h)

Depends on / 依赖: List.getElem_cons, Nat.sub_le_of_le_add, getElem_cons, getVert_cons, getVert_eq_support_getElem, n.zero_ne_add_one.symm, simp_rw, sub_le_of_le_add, support_cons, zero_ne_add_one
-/
lemma getVert_eq_support_getElem {u v : V} {n : Nat} (p : G.Walk u v) (h : n <= p.length) :
    p.getVert n = p.support[n]'(p.length_support ▸ Nat.lt_add_one_of_le h) := by
  cases p with
  | nil => simp
  | cons => cases n with
    | zero => simp
    | succ n =>
      simp_rw [support_cons, getVert_cons _ _ n.zero_ne_add_one.symm, List.getElem_cons]
      exact getVert_eq_support_getElem _ (Nat.sub_le_of_le_add h)

/--
lemma `support_getElem_eq_getVert` / 引理 `support_getElem_eq_getVert`

English:
lemma support_getElem_eq_getVert
  given: {u v : V} {n : Nat} (p : G.Walk u v) (h)
  proof: (p.getVert_eq_support_getElem <| by grind).symm

中文:
引理 support_getElem_eq_getVert
  条件: {u v : V} {n : 自然数} (p : G.途径 u v) (h)
  证明: (p.getVert_eq_support_getElem <| by grind).symm

Depends on / 依赖: getVert_eq_support_getElem, p.getVert_eq_support_getElem
-/
lemma support_getElem_eq_getVert {u v : V} {n : Nat} (p : G.Walk u v) (h) :
    p.support[n]'h = p.getVert n :=
  (p.getVert_eq_support_getElem <| by grind).symm

/--
lemma `getVert_eq_support_getElem?` / 引理 `getVert_eq_support_getElem?`

English:
lemma getVert_eq_support_getElem?
  given: {u v : V} {n : Nat} (p : G.Walk u v) (h : n <= p.length)
  proof: by
  rw [getVert_eq_support_getElem p h]; rw [← List.getElem?_eq_getElem]

中文:
引理 getVert_eq_support_getElem?
  条件: {u v : V} {n : 自然数} (p : G.途径 u v) (h : n <= p.length)
  证明: by
  rw [getVert_eq_support_getElem p h]; rw [← List.getElem?_eq_getElem]
-/
lemma getVert_eq_support_getElem? {u v : V} {n : Nat} (p : G.Walk u v) (h : n <= p.length) :
    some (p.getVert n) = p.support[n]? := by
  rw [getVert_eq_support_getElem p h]; rw [← List.getElem?_eq_getElem]

/--
lemma `getVert_eq_getD_support` / 引理 `getVert_eq_getD_support`

English:
lemma getVert_eq_getD_support
  given: {u v : V} (p : G.Walk u v) (n : Nat)
  proof: by
  by_cases h : n <= p.length
  · simp [← getVert_eq_support_getElem? p h]
  grind [getVert_of_length_le, length_support]

@[simp]

中文:
引理 getVert_eq_getD_support
  条件: {u v : V} (p : G.途径 u v) (n : 自然数)
  证明: by
  by_cases h : n <= p.length
  · simp [← getVert_eq_support_getElem? p h]
  grind [getVert_of_length_le, length_support]

@[simp]

Depends on / 依赖: getVert_eq_support_getElem, getVert_of_length_le, length, length_support, p.length
-/
lemma getVert_eq_getD_support {u v : V} (p : G.Walk u v) (n : Nat) :
    p.getVert n = p.support.getD n v := by
  by_cases h : n <= p.length
  · simp [← getVert_eq_support_getElem? p h]
  grind [getVert_of_length_le, length_support]

@[simp]
/--
lemma `getVert_support_idxOf` / 引理 `getVert_support_idxOf`

English:
lemma getVert_support_idxOf
  given: [DecidableEq V] (p : G.Walk u v) (h : w in p.support)
  proof: by
  grind [getVert_eq_support_getElem]

中文:
引理 getVert_support_idxOf
  条件: [DecidableEq V] (p : G.途径 u v) (h : w in p.support)
  证明: by
  grind [getVert_eq_support_getElem]

Depends on / 依赖: getVert_eq_support_getElem
-/
lemma getVert_support_idxOf [DecidableEq V] (p : G.Walk u v) (h : w in p.support) :
    p.getVert (p.support.idxOf w) = w := by
  grind [getVert_eq_support_getElem]

/--
theorem `getVert_comp_val_eq_get_support` / 定理 `getVert_comp_val_eq_get_support`

English:
theorem getVert_comp_val_eq_get_support
  given: {u v : V} (p : G.Walk u v)
  proof: by
  grind [getVert_eq_support_getElem, length_support]

中文:
定理 getVert_comp_val_eq_get_support
  条件: {u v : V} (p : G.途径 u v)
  证明: by
  grind [getVert_eq_support_getElem, length_support]

Depends on / 依赖: getVert_eq_support_getElem, length_support
-/
theorem getVert_comp_val_eq_get_support {u v : V} (p : G.Walk u v) :
    p.getVert ∘ Fin.val = p.support.get := by
  grind [getVert_eq_support_getElem, length_support]

/--
theorem `range_getVert_eq_range_support_getElem` / 定理 `range_getVert_eq_range_support_getElem`

English:
theorem range_getVert_eq_range_support_getElem
  given: {u v : V} (p : G.Walk u v)
  proof: Set.ext fun _ => ⟨by grind [Set.range_list_get, getVert_mem_support],
    fun ⟨n, _⟩ => ⟨n, by grind [getVert_eq_support_getElem, length_support]⟩⟩

中文:
定理 range_getVert_eq_range_support_getElem
  条件: {u v : V} (p : G.途径 u v)
  证明: Set.ext fun _ => ⟨by grind [Set.range_list_get, getVert_mem_support],
    fun ⟨n, _⟩ => ⟨n, by grind [getVert_eq_support_getElem, length_support]⟩⟩

Depends on / 依赖: Set.ext, Set.range_list_get, getVert_eq_support_getElem, getVert_mem_support, length_support, range_list_get
-/
theorem range_getVert_eq_range_support_getElem {u v : V} (p : G.Walk u v) :
    Set.range p.getVert = Set.range p.support.get :=
  Set.ext fun _ => ⟨by grind [Set.range_list_get, getVert_mem_support],
    fun ⟨n, _⟩ => ⟨n, by grind [getVert_eq_support_getElem, length_support]⟩⟩

/--
theorem `darts_getElem_eq_getVert` / 定理 `darts_getElem_eq_getVert`

English:
theorem darts_getElem_eq_getVert
  given: {u v : V} {p : G.Walk u v} (n : Nat) (h : n < p.darts.length)
  proof: by
  rw [p.length_darts] at h
  ext <;> simp [p.getVert_eq_support_getElem (le_of_lt h), p.getVert_eq_support_getElem h]

中文:
定理 darts_getElem_eq_getVert
  条件: {u v : V} {p : G.途径 u v} (n : 自然数) (h : n < p.darts.length)
  证明: by
  rw [p.length_darts] at h
  ext <;> simp [p.getVert_eq_support_getElem (le_of_lt h), p.getVert_eq_support_getElem h]

Depends on / 依赖: getVert_eq_support_getElem, le_of_lt, length_darts, p.getVert_eq_support_getElem, p.length_darts
-/
theorem darts_getElem_eq_getVert {u v : V} {p : G.Walk u v} (n : Nat) (h : n < p.darts.length) :
    p.darts[n] = ⟨⟨p.getVert n, p.getVert (n + 1)⟩, p.adj_getVert_succ (p.length_darts ▸ h)⟩ := by
  rw [p.length_darts] at h
  ext <;> simp [p.getVert_eq_support_getElem (le_of_lt h), p.getVert_eq_support_getElem h]

/--
theorem `getElem_edges` / 定理 `getElem_edges`

English:
theorem getElem_edges
  given: {p : G.Walk u v} {i : Nat} (h : i < p.edges.length)
  proof: by
  simp [getElem_edges_eq_edge_getElem_darts, darts_getElem_eq_getVert]

中文:
定理 getElem_edges
  条件: {p : G.途径 u v} {i : 自然数} (h : i < p.edges.length)
  证明: by
  simp [getElem_edges_eq_edge_getElem_darts, darts_getElem_eq_getVert]

Depends on / 依赖: darts_getElem_eq_getVert, getElem_edges_eq_edge_getElem_darts
-/
theorem getElem_edges {p : G.Walk u v} {i : Nat} (h : i < p.edges.length) :
    p.edges[i] = s(p.getVert i, p.getVert (i + 1)) := by
  simp [getElem_edges_eq_edge_getElem_darts, darts_getElem_eq_getVert]

/--
theorem `mk_mem_edges_iff_exists` / 定理 `mk_mem_edges_iff_exists`

English:
theorem mk_mem_edges_iff_exists
  given: {u' v' : V} (p : G.Walk u v)
  proof: by
  constructor <;> grind [getElem_edges, List.mem_iff_getElem]

中文:
定理 mk_mem_edges_iff_存在
  条件: {u' v' : V} (p : G.途径 u v)
  证明: by
  constructor <;> grind [getElem_edges, List.mem_iff_getElem]

Depends on / 依赖: List.mem_iff_getElem, getElem_edges, mem_iff_getElem
-/
theorem mk_mem_edges_iff_exists {u' v' : V} (p : G.Walk u v) :
    s(u', v') in p.edges ↔ exists i < p.length, s(p.getVert i, p.getVert (i + 1)) = s(u', v') := by
  constructor <;> grind [getElem_edges, List.mem_iff_getElem]

/--
theorem `adj_of_infix_support` / 定理 `adj_of_infix_support`

English:
theorem adj_of_infix_support
  given: {u v u' v'} {p : G.Walk u v} (h : [u', v'] <:+: p.support)
  proof: by
  have ⟨k, hk, h⟩ := List.infix_iff_getElem?.mp h
  have h₀ := Nat.zero_add _ ▸ h 0 Nat.zero_lt_two
  have h₁ := Nat.add_comm .. ▸ h 1 Nat.one_lt_two
  rw [← getVert_eq_support_getElem? _ <| by grind]; rw [Option.some.injEq] at h₀ h₁
exact h₀ ▸ h₁ ▸ p.adj_getVert_succ (i := k) by grind

中文:
定理 adj_of_infix_support
  条件: {u v u' v'} {p : G.途径 u v} (h : [u', v'] <:+: p.support)
  证明: by
  have ⟨k, hk, h⟩ := List.infix_iff_getElem?.mp h
  have h₀ := Nat.zero_add _ ▸ h 0 Nat.zero_lt_two
  have h₁ := Nat.add_comm .. ▸ h 1 Nat.one_lt_two
  rw [← getVert_eq_support_getElem? _ <| by grind]; rw [Option.some.injEq] at h₀ h₁
exact h₀ ▸ h₁ ▸ p.adj_getVert_succ (i := k) by grind

Depends on / 依赖: List.infix_iff_getElem, Nat.add_comm, Nat.one_lt_two, Nat.zero_add, Nat.zero_lt_two, Option.some.injEq, add_comm, adj_getVert_succ, getVert_eq_support_getElem, infix_iff_getElem, one_lt_two, p.adj_getVert_succ, zero_add, zero_lt_two
-/
theorem adj_of_infix_support {u v u' v'} {p : G.Walk u v} (h : [u', v'] <:+: p.support) :
    G.Adj u' v' := by
  have ⟨k, hk, h⟩ := List.infix_iff_getElem?.mp h
  have h₀ := Nat.zero_add _ ▸ h 0 Nat.zero_lt_two
  have h₁ := Nat.add_comm .. ▸ h 1 Nat.one_lt_two
  rw [← getVert_eq_support_getElem? _ <| by grind]; rw [Option.some.injEq] at h₀ h₁
exact h₀ ▸ h₁ ▸ p.adj_getVert_succ (i := k) by grind

/--
Definition of `snd` / `snd` 的定义

English:
abbreviation snd
  signature: (p : G.Walk u v)
  body: p.getVert 1

中文:
缩写 snd
  签名: (p : G.途径 u v)
  定义体: p.getVert 1

Depends on / 依赖: getVert, p.getVert
-/
abbrev snd (p : G.Walk u v) : V := p.getVert 1

/--
lemma `adj_snd` / 引理 `adj_snd`

English:
lemma adj_snd
  given: {p : G.Walk v w} (hp : ¬ p.Nil)
  proof: by
  simpa using adj_getVert_succ p (by simpa [not_nil_iff_lt_length] using hp : 0 < p.length)

中文:
引理 adj_snd
  条件: {p : G.途径 v w} (hp : ¬ p.Nil)
  证明: by
  simpa using adj_getVert_succ p (by simpa [not_nil_iff_lt_length] using hp : 0 < p.length)
-/
@[simp] lemma adj_snd {p : G.Walk v w} (hp : ¬ p.Nil) :
    G.Adj v p.snd := by
  simpa using adj_getVert_succ p (by simpa [not_nil_iff_lt_length] using hp : 0 < p.length)

/--
lemma `snd_cons` / 引理 `snd_cons`

English:
lemma snd_cons
  given: {u v w} (q : G.Walk v w) (hadj : G.Adj u v)
  proof: by simp

中文:
引理 snd_cons
  条件: {u v w} (q : G.途径 v w) (hadj : G.伴随 u v)
  证明: by simp
-/
lemma snd_cons {u v w} (q : G.Walk v w) (hadj : G.Adj u v) :
    (q.cons hadj).snd = v := by simp

/--
lemma `snd_mem_tail_support` / 引理 `snd_mem_tail_support`

English:
lemma snd_mem_tail_support
  given: {u v : V} {p : G.Walk u v} (h : ¬p.Nil)
  statement: p.snd in p.support.tail
  proof: p.notNilRec (by simp) h

中文:
引理 snd_mem_tail_support
  条件: {u v : V} {p : G.途径 u v} (h : ¬p.Nil)
  结论: p.snd in p.support.tail
  证明: p.notNilRec (by simp) h

Depends on / 依赖: notNilRec, p.notNilRec
-/
lemma snd_mem_tail_support {u v : V} {p : G.Walk u v} (h : ¬p.Nil) : p.snd in p.support.tail :=
  p.notNilRec (by simp) h

/-- Use `snd_eq_support_getElem_one` to rewrite in the reverse direction. -/
@[simp]
/--
lemma `support_getElem_one` / 引理 `support_getElem_one`

English:
lemma support_getElem_one
  given: {p : G.Walk u v} (hp)
  statement: p.support[1]'hp = p.snd
  proof: by
  grind [getVert_eq_support_getElem]

中文:
引理 support_getElem_one
  条件: {p : G.途径 u v} (hp)
  结论: p.support[1]'hp = p.snd
  证明: by
  grind [getVert_eq_support_getElem]

Depends on / 依赖: getVert_eq_support_getElem
-/
lemma support_getElem_one {p : G.Walk u v} (hp) : p.support[1]'hp = p.snd := by
  grind [getVert_eq_support_getElem]

/--
lemma `snd_eq_support_getElem_one` / 引理 `snd_eq_support_getElem_one`

English:
lemma snd_eq_support_getElem_one
  given: {p : G.Walk u v} (hnil : ¬p.Nil)
  proof: .symm support_getElem_one _

中文:
引理 snd_eq_support_getElem_one
  条件: {p : G.途径 u v} (hnil : ¬p.Nil)
  证明: .symm support_getElem_one _

Depends on / 依赖: support_getElem_one
-/
lemma snd_eq_support_getElem_one {p : G.Walk u v} (hnil : ¬p.Nil) :
    p.snd = p.support[1]'(by grind [not_nil_iff_lt_length]) :=
.symm support_getElem_one _

/--
Definition of `penultimate` / `penultimate` 的定义

English:
abbreviation penultimate
  signature: (p : G.Walk u v)
  body: p.getVert (p.length - 1)

@[simp]

中文:
缩写 penultimate
  签名: (p : G.途径 u v)
  定义体: p.getVert (p.length - 1)

@[simp]

Depends on / 依赖: getVert, length, p.getVert, p.length
-/
abbrev penultimate (p : G.Walk u v) : V := p.getVert (p.length - 1)

@[simp]
/--
lemma `penultimate_nil` / 引理 `penultimate_nil`

English:
lemma penultimate_nil
  statement: (@nil _ G v).penultimate = v
  proof: rfl

@[simp]

中文:
引理 penultimate_nil
  结论: (@nil _ G v).penultimate = v
  证明: rfl

@[simp]
-/
lemma penultimate_nil : (@nil _ G v).penultimate = v := rfl

@[simp]
/--
lemma `penultimate_cons_nil` / 引理 `penultimate_cons_nil`

English:
lemma penultimate_cons_nil
  given: (h : G.Adj u v)
  statement: (cons h nil).penultimate = u
  proof: rfl

@[simp]

中文:
引理 penultimate_cons_nil
  条件: (h : G.伴随 u v)
  结论: (cons h nil).penultimate = u
  证明: rfl

@[simp]
-/
lemma penultimate_cons_nil (h : G.Adj u v) : (cons h nil).penultimate = u := rfl

@[simp]
/--
lemma `penultimate_cons_cons` / 引理 `penultimate_cons_cons`

English:
lemma penultimate_cons_cons
  given: {w'} (h : G.Adj u v) (h₂ : G.Adj v w) (p : G.Walk w w')
  proof: rfl

中文:
引理 penultimate_cons_cons
  条件: {w'} (h : G.伴随 u v) (h₂ : G.伴随 v w) (p : G.途径 w w')
  证明: rfl
-/
lemma penultimate_cons_cons {w'} (h : G.Adj u v) (h₂ : G.Adj v w) (p : G.Walk w w') :
    (cons h (cons h₂ p)).penultimate = (cons h₂ p).penultimate := rfl

/--
lemma `penultimate_cons_of_not_nil` / 引理 `penultimate_cons_of_not_nil`

English:
lemma penultimate_cons_of_not_nil
  given: (h : G.Adj u v) (p : G.Walk v w) (hp : ¬ p.Nil)
  proof: p.notNilRec (by simp) hp h

@[simp]

中文:
引理 penultimate_cons_of_not_nil
  条件: (h : G.伴随 u v) (p : G.途径 v w) (hp : ¬ p.Nil)
  证明: p.notNilRec (by simp) hp h

@[simp]

Depends on / 依赖: notNilRec, p.notNilRec
-/
lemma penultimate_cons_of_not_nil (h : G.Adj u v) (p : G.Walk v w) (hp : ¬ p.Nil) :
    (cons h p).penultimate = p.penultimate :=
  p.notNilRec (by simp) hp h

@[simp]
/--
lemma `adj_penultimate` / 引理 `adj_penultimate`

English:
lemma adj_penultimate
  given: {p : G.Walk v w} (hp : ¬ p.Nil)
  statement: G.Adj p.penultimate w
  proof: by
  grind [getVert_length, adj_getVert_succ]

中文:
引理 adj_penultimate
  条件: {p : G.途径 v w} (hp : ¬ p.Nil)
  结论: G.伴随 p.penultimate w
  证明: by
  grind [getVert_length, adj_getVert_succ]

Depends on / 依赖: adj_getVert_succ, getVert_length
-/
lemma adj_penultimate {p : G.Walk v w} (hp : ¬ p.Nil) : G.Adj p.penultimate w := by
  grind [getVert_length, adj_getVert_succ]

/--
lemma `penultimate_mem_dropLast_support` / 引理 `penultimate_mem_dropLast_support`

English:
lemma penultimate_mem_dropLast_support
  given: {p : G.Walk u v} (h : ¬p.Nil)
  proof: by
.ne have := adj_penultimate h
  grind [getVert_mem_support, List.dropLast_concat_getLast, getLast_support]

@[simp]

中文:
引理 penultimate_mem_dropLast_support
  条件: {p : G.途径 u v} (h : ¬p.Nil)
  证明: by
.ne have := adj_penultimate h
  grind [getVert_mem_support, List.dropLast_concat_getLast, getLast_support]

@[simp]

Depends on / 依赖: List.dropLast_concat_getLast, adj_penultimate, dropLast_concat_getLast, getLast_support, getVert_mem_support
-/
lemma penultimate_mem_dropLast_support {p : G.Walk u v} (h : ¬p.Nil) :
    p.penultimate in p.support.dropLast := by
.ne have := adj_penultimate h
  grind [getVert_mem_support, List.dropLast_concat_getLast, getLast_support]

@[simp]
/--
lemma `support_getElem_length_sub_one_eq_penultimate` / 引理 `support_getElem_length_sub_one_eq_penultimate`

English:
lemma support_getElem_length_sub_one_eq_penultimate
  given: {p : G.Walk u v}
  proof: by
  grind [getVert_eq_support_getElem]

中文:
引理 support_getElem_length_sub_one_eq_penultimate
  条件: {p : G.途径 u v}
  证明: by
  grind [getVert_eq_support_getElem]

Depends on / 依赖: getVert_eq_support_getElem
-/
lemma support_getElem_length_sub_one_eq_penultimate {p : G.Walk u v} :
    p.support[p.length - 1] = p.penultimate := by
  grind [getVert_eq_support_getElem]

/-- The first dart of a walk. -/
@[simps]
/--
Definition of `firstDart` / `firstDart` 的定义

English:
definition firstDart
  signature: (p : G.Walk v w) (hp : ¬ p.Nil)
  body: v
  snd := p.snd
  adj := p.adj_snd hp

中文:
定义 firstDart
  签名: (p : G.途径 v w) (hp : ¬ p.Nil)
  定义体: v
  snd := p.snd
  adj := p.adj_snd hp
-/
def firstDart (p : G.Walk v w) (hp : ¬ p.Nil) : G.Dart where
  fst := v
  snd := p.snd
  adj := p.adj_snd hp

/-- The last dart of a walk. -/
@[simps]
/--
Definition of `lastDart` / `lastDart` 的定义

English:
definition lastDart
  signature: (p : G.Walk v w) (hp : ¬ p.Nil)
  body: p.penultimate
  snd := w
  adj := p.adj_penultimate hp

中文:
定义 lastDart
  签名: (p : G.途径 v w) (hp : ¬ p.Nil)
  定义体: p.penultimate
  snd := w
  adj := p.adj_penultimate hp

Depends on / 依赖: p.penultimate, penultimate
-/
def lastDart (p : G.Walk v w) (hp : ¬ p.Nil) : G.Dart where
  fst := p.penultimate
  snd := w
  adj := p.adj_penultimate hp

/--
lemma `edge_firstDart` / 引理 `edge_firstDart`

English:
lemma edge_firstDart
  given: (p : G.Walk v w) (hp : ¬ p.Nil)
  proof: rfl

中文:
引理 edge_firstDart
  条件: (p : G.途径 v w) (hp : ¬ p.Nil)
  证明: rfl
-/
lemma edge_firstDart (p : G.Walk v w) (hp : ¬ p.Nil) :
    (p.firstDart hp).edge = s(v, p.snd) := rfl

/--
lemma `edge_lastDart` / 引理 `edge_lastDart`

English:
lemma edge_lastDart
  given: (p : G.Walk v w) (hp : ¬ p.Nil)
  proof: rfl

中文:
引理 edge_lastDart
  条件: (p : G.途径 v w) (hp : ¬ p.Nil)
  证明: rfl
-/
lemma edge_lastDart (p : G.Walk v w) (hp : ¬ p.Nil) :
    (p.lastDart hp).edge = s(p.penultimate, w) := rfl

/--
theorem `firstDart_eq` / 定理 `firstDart_eq`

English:
theorem firstDart_eq
  given: {p : G.Walk v w} (h₁ : ¬ p.Nil) (h₂ : 0 < p.darts.length)
  proof: by
  simp [Dart.ext_iff, firstDart_toProd, darts_getElem_eq_getVert]

中文:
定理 firstDart_eq
  条件: {p : G.途径 v w} (h₁ : ¬ p.Nil) (h₂ : 0 < p.darts.length)
  证明: by
  simp [Dart.ext_iff, firstDart_toProd, darts_getElem_eq_getVert]

Depends on / 依赖: Dart.ext_iff, darts_getElem_eq_getVert, ext_iff, firstDart_toProd
-/
theorem firstDart_eq {p : G.Walk v w} (h₁ : ¬ p.Nil) (h₂ : 0 < p.darts.length) :
    p.firstDart h₁ = p.darts[0] := by
  simp [Dart.ext_iff, firstDart_toProd, darts_getElem_eq_getVert]

/--
theorem `lastDart_eq` / 定理 `lastDart_eq`

English:
theorem lastDart_eq
  given: {p : G.Walk v w} (h₁ : ¬ p.Nil) (h₂ : 0 < p.darts.length)
  proof: by
  simp (disch := grind) [Dart.ext_iff, lastDart_toProd, darts_getElem_eq_getVert,
    p.getVert_of_length_le]

中文:
定理 lastDart_eq
  条件: {p : G.途径 v w} (h₁ : ¬ p.Nil) (h₂ : 0 < p.darts.length)
  证明: by
  simp (disch := grind) [Dart.ext_iff, lastDart_toProd, darts_getElem_eq_getVert,
    p.getVert_of_length_le]

Depends on / 依赖: Dart.ext_iff, darts_getElem_eq_getVert, ext_iff, getVert_of_length_le, lastDart_toProd, p.getVert_of_length_le
-/
theorem lastDart_eq {p : G.Walk v w} (h₁ : ¬ p.Nil) (h₂ : 0 < p.darts.length) :
    p.lastDart h₁ = p.darts[p.darts.length - 1] := by
  simp (disch := grind) [Dart.ext_iff, lastDart_toProd, darts_getElem_eq_getVert,
    p.getVert_of_length_le]

/-- Use `firstDart_eq_head_darts` to rewrite in the reverse direction. -/
@[simp]
/--
theorem `head_darts_eq_firstDart` / 定理 `head_darts_eq_firstDart`

English:
theorem head_darts_eq_firstDart
  given: {p : G.Walk v w} (hnil : p.darts != [])
  proof: by
  grind [firstDart_eq]

中文:
定理 head_darts_eq_firstDart
  条件: {p : G.途径 v w} (hnil : p.darts != [])
  证明: by
  grind [firstDart_eq]

Depends on / 依赖: firstDart_eq
-/
theorem head_darts_eq_firstDart {p : G.Walk v w} (hnil : p.darts != []) :
    p.darts.head hnil = p.firstDart (darts_eq_nil.not.mp hnil) := by
  grind [firstDart_eq]

/--
theorem `firstDart_eq_head_darts` / 定理 `firstDart_eq_head_darts`

English:
theorem firstDart_eq_head_darts
  given: {p : G.Walk v w} (hnil : ¬p.Nil)
  proof: .symm head_darts_eq_firstDart _

@[simp]

中文:
定理 firstDart_eq_head_darts
  条件: {p : G.途径 v w} (hnil : ¬p.Nil)
  证明: .symm head_darts_eq_firstDart _

@[simp]

Depends on / 依赖: head_darts_eq_firstDart
-/
theorem firstDart_eq_head_darts {p : G.Walk v w} (hnil : ¬p.Nil) :
    p.firstDart hnil = p.darts.head (darts_eq_nil.not.mpr hnil) :=
.symm head_darts_eq_firstDart _

@[simp]
/--
theorem `firstDart_mem_darts` / 定理 `firstDart_mem_darts`

English:
theorem firstDart_mem_darts
  given: {p : G.Walk v w} (hnil : ¬p.Nil)
  statement: p.firstDart hnil in p.darts
  proof: p.firstDart_eq_head_darts _ ▸ List.head_mem _

@[simp]

中文:
定理 firstDart_mem_darts
  条件: {p : G.途径 v w} (hnil : ¬p.Nil)
  结论: p.firstDart hnil in p.darts
  证明: p.firstDart_eq_head_darts _ ▸ List.head_mem _

@[simp]

Depends on / 依赖: List.head_mem, firstDart_eq_head_darts, head_mem, p.firstDart_eq_head_darts
-/
theorem firstDart_mem_darts {p : G.Walk v w} (hnil : ¬p.Nil) : p.firstDart hnil in p.darts :=
  p.firstDart_eq_head_darts _ ▸ List.head_mem _

@[simp]
/--
theorem `getLast_darts_eq_lastDart` / 定理 `getLast_darts_eq_lastDart`

English:
theorem getLast_darts_eq_lastDart
  given: {p : G.Walk v w} (hnil : p.darts != [])
  proof: by
  grind [lastDart_eq, not_nil_iff_lt_length]

中文:
定理 getLast_darts_eq_lastDart
  条件: {p : G.途径 v w} (hnil : p.darts != [])
  证明: by
  grind [lastDart_eq, not_nil_iff_lt_length]

Depends on / 依赖: lastDart_eq, not_nil_iff_lt_length
-/
theorem getLast_darts_eq_lastDart {p : G.Walk v w} (hnil : p.darts != []) :
    p.darts.getLast hnil = p.lastDart (darts_eq_nil.not.mp hnil) := by
  grind [lastDart_eq, not_nil_iff_lt_length]

/--
theorem `lastDart_eq_getLast_darts` / 定理 `lastDart_eq_getLast_darts`

English:
theorem lastDart_eq_getLast_darts
  given: {p : G.Walk v w} (hnil : ¬p.Nil)
  proof: by
  grind [lastDart_eq, not_nil_iff_lt_length]

@[simp]

中文:
定理 lastDart_eq_getLast_darts
  条件: {p : G.途径 v w} (hnil : ¬p.Nil)
  证明: by
  grind [lastDart_eq, not_nil_iff_lt_length]

@[simp]

Depends on / 依赖: lastDart_eq, not_nil_iff_lt_length
-/
theorem lastDart_eq_getLast_darts {p : G.Walk v w} (hnil : ¬p.Nil) :
    p.lastDart hnil = p.darts.getLast (darts_eq_nil.not.mpr hnil) := by
  grind [lastDart_eq, not_nil_iff_lt_length]

@[simp]
/--
theorem `lastDart_mem_darts` / 定理 `lastDart_mem_darts`

English:
theorem lastDart_mem_darts
  given: {p : G.Walk v w} (hnil : ¬p.Nil)
  statement: p.lastDart hnil in p.darts
  proof: p.lastDart_eq_getLast_darts _ ▸ List.getLast_mem _

中文:
定理 lastDart_mem_darts
  条件: {p : G.途径 v w} (hnil : ¬p.Nil)
  结论: p.lastDart hnil in p.darts
  证明: p.lastDart_eq_getLast_darts _ ▸ List.getLast_mem _

Depends on / 依赖: List.getLast_mem, getLast_mem, lastDart_eq_getLast_darts, p.lastDart_eq_getLast_darts
-/
theorem lastDart_mem_darts {p : G.Walk v w} (hnil : ¬p.Nil) : p.lastDart hnil in p.darts :=
  p.lastDart_eq_getLast_darts _ ▸ List.getLast_mem _

/-- Use `mk_start_snd_eq_head_edges` to rewrite in the reverse direction. -/
@[simp]
/--
theorem `head_edges_eq_mk_start_snd` / 定理 `head_edges_eq_mk_start_snd`

English:
theorem head_edges_eq_mk_start_snd
  given: {p : G.Walk v w} (hp)
  statement: p.edges.head hp = s(v, p.snd)
  proof: by
  simp [p.edge_firstDart, Walk.edges]

中文:
定理 head_edges_eq_mk_start_snd
  条件: {p : G.途径 v w} (hp)
  结论: p.edges.head hp = s(v, p.snd)
  证明: by
  simp [p.edge_firstDart, Walk.edges]

Depends on / 依赖: Walk.edges, edge_firstDart, p.edge_firstDart
-/
theorem head_edges_eq_mk_start_snd {p : G.Walk v w} (hp) : p.edges.head hp = s(v, p.snd) := by
  simp [p.edge_firstDart, Walk.edges]

/--
theorem `mk_start_snd_eq_head_edges` / 定理 `mk_start_snd_eq_head_edges`

English:
theorem mk_start_snd_eq_head_edges
  given: {p : G.Walk v w} (hnil : ¬p.Nil)
  proof: .symm head_edges_eq_mk_start_snd _

中文:
定理 mk_start_snd_eq_head_edges
  条件: {p : G.途径 v w} (hnil : ¬p.Nil)
  证明: .symm head_edges_eq_mk_start_snd _

Depends on / 依赖: head_edges_eq_mk_start_snd
-/
theorem mk_start_snd_eq_head_edges {p : G.Walk v w} (hnil : ¬p.Nil) :
    s(v, p.snd) = p.edges.head (edges_eq_nil.not.mpr hnil) :=
.symm head_edges_eq_mk_start_snd _

/--
theorem `mk_start_snd_mem_edges` / 定理 `mk_start_snd_mem_edges`

English:
theorem mk_start_snd_mem_edges
  given: {p : G.Walk v w} (hnil : ¬p.Nil)
  statement: s(v, p.snd) in p.edges
  proof: p.mk_start_snd_eq_head_edges hnil ▸ List.head_mem _

中文:
定理 mk_start_snd_mem_edges
  条件: {p : G.途径 v w} (hnil : ¬p.Nil)
  结论: s(v, p.snd) in p.edges
  证明: p.mk_start_snd_eq_head_edges hnil ▸ List.head_mem _

Depends on / 依赖: List.head_mem, head_mem, mk_start_snd_eq_head_edges, p.mk_start_snd_eq_head_edges
-/
theorem mk_start_snd_mem_edges {p : G.Walk v w} (hnil : ¬p.Nil) : s(v, p.snd) in p.edges :=
  p.mk_start_snd_eq_head_edges hnil ▸ List.head_mem _

/-- Use `mk_penultimate_end_eq_getLast_edges` to rewrite in the reverse direction. -/
@[simp]
/--
theorem `getLast_edges_eq_mk_penultimate_end` / 定理 `getLast_edges_eq_mk_penultimate_end`

English:
theorem getLast_edges_eq_mk_penultimate_end
  given: {p : G.Walk v w} (hp)
  proof: by
  simp [p.edge_lastDart, Walk.edges]

中文:
定理 getLast_edges_eq_mk_penultimate_end
  条件: {p : G.途径 v w} (hp)
  证明: by
  simp [p.edge_lastDart, Walk.edges]

Depends on / 依赖: Walk.edges, edge_lastDart, p.edge_lastDart
-/
theorem getLast_edges_eq_mk_penultimate_end {p : G.Walk v w} (hp) :
    p.edges.getLast hp = s(p.penultimate, w) := by
  simp [p.edge_lastDart, Walk.edges]

/--
theorem `mk_penultimate_end_eq_getLast_edges` / 定理 `mk_penultimate_end_eq_getLast_edges`

English:
theorem mk_penultimate_end_eq_getLast_edges
  given: {p : G.Walk v w} (hnil : ¬p.Nil)
  proof: .symm getLast_edges_eq_mk_penultimate_end _

中文:
定理 mk_penultimate_end_eq_getLast_edges
  条件: {p : G.途径 v w} (hnil : ¬p.Nil)
  证明: .symm getLast_edges_eq_mk_penultimate_end _

Depends on / 依赖: getLast_edges_eq_mk_penultimate_end
-/
theorem mk_penultimate_end_eq_getLast_edges {p : G.Walk v w} (hnil : ¬p.Nil) :
    s(p.penultimate, w) = p.edges.getLast (edges_eq_nil.not.mpr hnil) :=
.symm getLast_edges_eq_mk_penultimate_end _

/--
theorem `mk_penultimate_end_mem_edges` / 定理 `mk_penultimate_end_mem_edges`

English:
theorem mk_penultimate_end_mem_edges
  given: {p : G.Walk v w} (hnil : ¬p.Nil)
  proof: p.mk_penultimate_end_eq_getLast_edges hnil ▸ List.getLast_mem _

中文:
定理 mk_penultimate_end_mem_edges
  条件: {p : G.途径 v w} (hnil : ¬p.Nil)
  证明: p.mk_penultimate_end_eq_getLast_edges hnil ▸ List.getLast_mem _

Depends on / 依赖: List.getLast_mem, getLast_mem, mk_penultimate_end_eq_getLast_edges, p.mk_penultimate_end_eq_getLast_edges
-/
theorem mk_penultimate_end_mem_edges {p : G.Walk v w} (hnil : ¬p.Nil) :
    s(p.penultimate, w) in p.edges :=
  p.mk_penultimate_end_eq_getLast_edges hnil ▸ List.getLast_mem _

end Walk

end SimpleGraph
