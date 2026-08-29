/-
Copyright (c) 2024 Iván Renison, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iván Renison, Bhavik Mehta
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# Definition of cycle graphs

This file defines and proves several fact about cycle graphs on `n` vertices and the cycle around
the cycle graph when `n ≥ 3`.

## Main declarations

* `SimpleGraph.cycleGraph n`: the cycle graph over `Fin n`.
* `(SimpleGraph.cycleGraph n).cycle`: the cycle around `cycleGraph (n + 3)` starting at 0.
-/

@[expose] public section

namespace SimpleGraph

open Walk

/--
Definition of `cycleGraph` / `cycleGraph` 的定义

English:
definition cycleGraph
  signature: : (n : Nat) -> SimpleGraph (Fin n)

中文:
定义 cycleGraph
  签名: : (n : 自然数) -> 简单图 (有限集 n)
-/
def cycleGraph : (n : Nat) -> SimpleGraph (Fin n)
  | 0 | 1 => ⊥
  | _ + 2 => {
    Adj a b := a - b = 1 ∨ b - a = 1
  }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (n : Nat) -> DecidableRel (cycleGraph n).Adj

中文:
实例 :
  签名: (n : 自然数) -> DecidableRel (cycleGraph n).伴随
-/
instance : (n : Nat) -> DecidableRel (cycleGraph n).Adj
  | 0 | 1 => fun _ _ => inferInstanceAs (Decidable False)
  | _ + 2 => by unfold cycleGraph; infer_instance

/--
theorem `cycleGraph_zero_adj` / 定理 `cycleGraph_zero_adj`

English:
theorem cycleGraph_zero_adj
  given: {u v : Fin 0}
  statement: ¬(cycleGraph 0).Adj u v
  proof: id

中文:
定理 cycleGraph_zero_adj
  条件: {u v : 有限集 0}
  结论: ¬(cycleGraph 0).伴随 u v
  证明: id
-/
theorem cycleGraph_zero_adj {u v : Fin 0} : ¬(cycleGraph 0).Adj u v := id

/--
theorem `cycleGraph_zero_eq_bot` / 定理 `cycleGraph_zero_eq_bot`

English:
theorem cycleGraph_zero_eq_bot
  statement: cycleGraph 0 = ⊥
  proof: Subsingleton.elim _ _

中文:
定理 cycleGraph_zero_eq_bot
  结论: cycleGraph 0 = ⊥
  证明: Subsingleton.elim _ _

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
theorem cycleGraph_zero_eq_bot : cycleGraph 0 = ⊥ := Subsingleton.elim _ _
/--
theorem `cycleGraph_one_eq_bot` / 定理 `cycleGraph_one_eq_bot`

English:
theorem cycleGraph_one_eq_bot
  statement: cycleGraph 1 = ⊥
  proof: Subsingleton.elim _ _

中文:
定理 cycleGraph_one_eq_bot
  结论: cycleGraph 1 = ⊥
  证明: Subsingleton.elim _ _

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
theorem cycleGraph_one_eq_bot : cycleGraph 1 = ⊥ := Subsingleton.elim _ _
/--
theorem `cycleGraph_zero_eq_top` / 定理 `cycleGraph_zero_eq_top`

English:
theorem cycleGraph_zero_eq_top
  statement: cycleGraph 0 = ⊤
  proof: Subsingleton.elim _ _

中文:
定理 cycleGraph_zero_eq_top
  结论: cycleGraph 0 = ⊤
  证明: Subsingleton.elim _ _

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
theorem cycleGraph_zero_eq_top : cycleGraph 0 = ⊤ := Subsingleton.elim _ _
/--
theorem `cycleGraph_one_eq_top` / 定理 `cycleGraph_one_eq_top`

English:
theorem cycleGraph_one_eq_top
  statement: cycleGraph 1 = ⊤
  proof: Subsingleton.elim _ _

中文:
定理 cycleGraph_one_eq_top
  结论: cycleGraph 1 = ⊤
  证明: Subsingleton.elim _ _

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
theorem cycleGraph_one_eq_top : cycleGraph 1 = ⊤ := Subsingleton.elim _ _

/--
theorem `cycleGraph_two_eq_top` / 定理 `cycleGraph_two_eq_top`

English:
theorem cycleGraph_two_eq_top
  statement: cycleGraph 2 = ⊤
  proof: by
  simp only [SimpleGraph.ext_iff, funext_iff]
  decide

中文:
定理 cycleGraph_two_eq_top
  结论: cycleGraph 2 = ⊤
  证明: by
  simp only [SimpleGraph.ext_iff, funext_iff]
  decide

Depends on / 依赖: SimpleGraph, SimpleGraph.ext_iff, ext_iff, funext_iff
-/
theorem cycleGraph_two_eq_top : cycleGraph 2 = ⊤ := by
  simp only [SimpleGraph.ext_iff, funext_iff]
  decide

/--
theorem `cycleGraph_three_eq_top` / 定理 `cycleGraph_three_eq_top`

English:
theorem cycleGraph_three_eq_top
  statement: cycleGraph 3 = ⊤
  proof: by
  simp only [SimpleGraph.ext_iff, funext_iff]
  decide

中文:
定理 cycleGraph_three_eq_top
  结论: cycleGraph 3 = ⊤
  证明: by
  simp only [SimpleGraph.ext_iff, funext_iff]
  decide

Depends on / 依赖: SimpleGraph, SimpleGraph.ext_iff, ext_iff, funext_iff
-/
theorem cycleGraph_three_eq_top : cycleGraph 3 = ⊤ := by
  simp only [SimpleGraph.ext_iff, funext_iff]
  decide

/--
theorem `cycleGraph_one_adj` / 定理 `cycleGraph_one_adj`

English:
theorem cycleGraph_one_adj
  given: {u v : Fin 1}
  statement: ¬(cycleGraph 1).Adj u v
  proof: by
  simp [cycleGraph_one_eq_bot]

中文:
定理 cycleGraph_one_adj
  条件: {u v : 有限集 1}
  结论: ¬(cycleGraph 1).伴随 u v
  证明: by
  simp [cycleGraph_one_eq_bot]

Depends on / 依赖: cycleGraph_one_eq_bot
-/
theorem cycleGraph_one_adj {u v : Fin 1} : ¬(cycleGraph 1).Adj u v := by
  simp [cycleGraph_one_eq_bot]

/--
theorem `cycleGraph_adj` / 定理 `cycleGraph_adj`

English:
theorem cycleGraph_adj
  given: {n : Nat} {u v : Fin (n + 2)}
  proof: Iff.rfl

中文:
定理 cycleGraph_adj
  条件: {n : 自然数} {u v : 有限集 (n + 2)}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem cycleGraph_adj {n : Nat} {u v : Fin (n + 2)} :
    (cycleGraph (n + 2)).Adj u v ↔ u - v = 1 ∨ v - u = 1 := Iff.rfl

/--
theorem `cycleGraph_adj'` / 定理 `cycleGraph_adj'`

English:
theorem cycleGraph_adj'
  given: {n : Nat} {u v : Fin n}
  proof: by
  match n with
  | 0 => exact u.elim0
  | 1 => simp [cycleGraph_one_adj]
  | n + 2 => simp [cycleGraph_adj, Fin.ext_iff]

中文:
定理 cycleGraph_adj'
  条件: {n : 自然数} {u v : 有限集 n}
  证明: by
  match n with
  | 0 => exact u.elim0
  | 1 => simp [cycleGraph_one_adj]
  | n + 2 => simp [cycleGraph_adj, Fin.ext_iff]

Depends on / 依赖: Fin.ext_iff, cycleGraph_adj, cycleGraph_one_adj, ext_iff, u.elim0
-/
theorem cycleGraph_adj' {n : Nat} {u v : Fin n} :
    (cycleGraph n).Adj u v ↔ (u - v).val = 1 ∨ (v - u).val = 1 := by
  match n with
  | 0 => exact u.elim0
  | 1 => simp [cycleGraph_one_adj]
  | n + 2 => simp [cycleGraph_adj, Fin.ext_iff]

/--
theorem `cycleGraph_neighborSet` / 定理 `cycleGraph_neighborSet`

English:
theorem cycleGraph_neighborSet
  given: {n : Nat} {v : Fin (n + 2)}
  proof: by
  ext w
  simp only [mem_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [cycleGraph_adj]; rw [sub_eq_iff_eq_add']; rw [sub_eq_iff_eq_add']; rw [eq_sub_iff_add_eq]; rw [eq_comm]

中文:
定理 cycleGraph_neighborSet
  条件: {n : 自然数} {v : 有限集 (n + 2)}
  证明: by
  ext w
  simp only [mem_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [cycleGraph_adj]; rw [sub_eq_iff_eq_add']; rw [sub_eq_iff_eq_add']; rw [eq_sub_iff_add_eq]; rw [eq_comm]

Depends on / 依赖: Set.mem_insert_iff, Set.mem_singleton_iff, cycleGraph_adj, eq_comm, eq_sub_iff_add_eq, mem_insert_iff, mem_neighborSet, mem_singleton_iff, sub_eq_iff_eq_add
-/
theorem cycleGraph_neighborSet {n : Nat} {v : Fin (n + 2)} :
    (cycleGraph (n + 2)).neighborSet v = {v - 1, v + 1} := by
  ext w
  simp only [mem_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [cycleGraph_adj]; rw [sub_eq_iff_eq_add']; rw [sub_eq_iff_eq_add']; rw [eq_sub_iff_add_eq]; rw [eq_comm]

/--
theorem `cycleGraph_neighborFinset` / 定理 `cycleGraph_neighborFinset`

English:
theorem cycleGraph_neighborFinset
  given: {n : Nat} {v : Fin (n + 2)}
  proof: by
  simp [neighborFinset, cycleGraph_neighborSet]

中文:
定理 cycleGraph_neighborFinset
  条件: {n : 自然数} {v : 有限集 (n + 2)}
  证明: by
  simp [neighborFinset, cycleGraph_neighborSet]

Depends on / 依赖: cycleGraph_neighborSet, neighborFinset
-/
theorem cycleGraph_neighborFinset {n : Nat} {v : Fin (n + 2)} :
    (cycleGraph (n + 2)).neighborFinset v = {v - 1, v + 1} := by
  simp [neighborFinset, cycleGraph_neighborSet]

/--
theorem `cycleGraph_degree_two_le` / 定理 `cycleGraph_degree_two_le`

English:
theorem cycleGraph_degree_two_le
  given: {n : Nat} {v : Fin (n + 2)}
  proof: by
  rw [SimpleGraph.degree]; rw [cycleGraph_neighborFinset]

中文:
定理 cycleGraph_degree_two_le
  条件: {n : 自然数} {v : 有限集 (n + 2)}
  证明: by
  rw [SimpleGraph.degree]; rw [cycleGraph_neighborFinset]

Depends on / 依赖: SimpleGraph, SimpleGraph.degree, cycleGraph_neighborFinset, degree
-/
theorem cycleGraph_degree_two_le {n : Nat} {v : Fin (n + 2)} :
    (cycleGraph (n + 2)).degree v = Finset.card {v - 1, v + 1} := by
  rw [SimpleGraph.degree]; rw [cycleGraph_neighborFinset]

/--
theorem `cycleGraph_degree_three_le` / 定理 `cycleGraph_degree_three_le`

English:
theorem cycleGraph_degree_three_le
  given: {n : Nat} {v : Fin (n + 3)}
  proof: by
  rw [cycleGraph_degree_two_le]; rw [Finset.card_pair]
  simp only [ne_eq, sub_eq_iff_eq_add, add_assoc v, left_eq_add]
  exact ne_of_beq_false rfl

中文:
定理 cycleGraph_degree_three_le
  条件: {n : 自然数} {v : 有限集 (n + 3)}
  证明: by
  rw [cycleGraph_degree_two_le]; rw [Finset.card_pair]
  simp only [ne_eq, sub_eq_iff_eq_add, add_assoc v, left_eq_add]
  exact ne_of_beq_false rfl

Depends on / 依赖: Finset, Finset.card_pair, add_assoc, card_pair, cycleGraph_degree_two_le, left_eq_add, ne_eq, ne_of_beq_false, sub_eq_iff_eq_add
-/
theorem cycleGraph_degree_three_le {n : Nat} {v : Fin (n + 3)} :
    (cycleGraph (n + 3)).degree v = 2 := by
  rw [cycleGraph_degree_two_le]; rw [Finset.card_pair]
  simp only [ne_eq, sub_eq_iff_eq_add, add_assoc v, left_eq_add]
  exact ne_of_beq_false rfl

/--
theorem `pathGraph_le_cycleGraph` / 定理 `pathGraph_le_cycleGraph`

English:
theorem pathGraph_le_cycleGraph
  given: {n : Nat}
  statement: pathGraph n <= cycleGraph n
  proof: by
  match n with
  | 0 | 1 => simp
  | n + 2 =>
    intro u v h
    rw [pathGraph_adj] at h
    rw [cycleGraph_adj']
    cases h with
    | inl h | inr h =>
      simp [Fin.coe_sub_iff_le.mpr (Nat.lt_of_succ_le h.le).le, Nat.eq_sub_of_add_eq' h]

中文:
定理 pathGraph_le_cycleGraph
  条件: {n : 自然数}
  结论: pathGraph n <= cycleGraph n
  证明: by
  match n with
  | 0 | 1 => simp
  | n + 2 =>
    intro u v h
    rw [pathGraph_adj] at h
    rw [cycleGraph_adj']
    cases h with
    | inl h | inr h =>
      simp [Fin.coe_sub_iff_le.mpr (Nat.lt_of_succ_le h.le).le, Nat.eq_sub_of_add_eq' h]

Depends on / 依赖: Fin.coe_sub_iff_le.mpr, Nat.eq_sub_of_add_eq, Nat.lt_of_succ_le, coe_sub_iff_le, cycleGraph_adj, eq_sub_of_add_eq, h.le, lt_of_succ_le, pathGraph_adj
-/
theorem pathGraph_le_cycleGraph {n : Nat} : pathGraph n <= cycleGraph n := by
  match n with
  | 0 | 1 => simp
  | n + 2 =>
    intro u v h
    rw [pathGraph_adj] at h
    rw [cycleGraph_adj']
    cases h with
    | inl h | inr h =>
      simp [Fin.coe_sub_iff_le.mpr (Nat.lt_of_succ_le h.le).le, Nat.eq_sub_of_add_eq' h]

/--
theorem `cycleGraph_preconnected` / 定理 `cycleGraph_preconnected`

English:
theorem cycleGraph_preconnected
  given: {n : Nat}
  statement: (cycleGraph n).Preconnected
  proof: (pathGraph_preconnected n).mono pathGraph_le_cycleGraph

中文:
定理 cycleGraph_preconnected
  条件: {n : 自然数}
  结论: (cycleGraph n).预连通
  证明: (pathGraph_preconnected n).mono pathGraph_le_cycleGraph

Depends on / 依赖: pathGraph_le_cycleGraph, pathGraph_preconnected
-/
theorem cycleGraph_preconnected {n : Nat} : (cycleGraph n).Preconnected :=
  (pathGraph_preconnected n).mono pathGraph_le_cycleGraph

/--
theorem `cycleGraph_connected` / 定理 `cycleGraph_connected`

English:
theorem cycleGraph_connected
  given: {n : Nat}
  statement: (cycleGraph (n + 1)).Connected
  proof: (pathGraph_connected n).mono pathGraph_le_cycleGraph

中文:
定理 cycleGraph_connected
  条件: {n : 自然数}
  结论: (cycleGraph (n + 1)).连通
  证明: (pathGraph_connected n).mono pathGraph_le_cycleGraph

Depends on / 依赖: pathGraph_connected, pathGraph_le_cycleGraph
-/
theorem cycleGraph_connected {n : Nat} : (cycleGraph (n + 1)).Connected :=
  (pathGraph_connected n).mono pathGraph_le_cycleGraph

section cycle

set_option backward.privateInPublic true in
/--
Definition of `cycleGraph.cycleCons` / `cycleGraph.cycleCons` 的定义

English:
definition cycleGraph.cycleCons
  signature: (n : Nat)
  body: by
      simp [cycleGraph_adj, Fin.ext_iff, Fin.sub_val_of_le]
    Walk.cons hadj (cycleGraph.cycleCons n ⟨m, Nat.lt_of_succ_lt h⟩)

中文:
定义 cycleGraph.cycleCons
  签名: (n : 自然数)
  定义体: by
      simp [cycleGraph_adj, Fin.ext_iff, Fin.sub_val_of_le]
    Walk.cons hadj (cycleGraph.cycleCons n ⟨m, Nat.lt_of_succ_lt h⟩)
-/
private def cycleGraph.cycleCons (n : Nat) : forall m : Fin (n + 3), (cycleGraph (n + 3)).Walk m 0
  | ⟨0, h⟩ => Walk.nil
  | ⟨m + 1, h⟩ =>
    have hadj : (cycleGraph (n + 3)).Adj ⟨m + 1, h⟩ ⟨m, Nat.lt_of_succ_lt h⟩ := by
      simp [cycleGraph_adj, Fin.ext_iff, Fin.sub_val_of_le]
    Walk.cons hadj (cycleGraph.cycleCons n ⟨m, Nat.lt_of_succ_lt h⟩)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `cycleGraph.cycle` / `cycleGraph.cycle` 的定义

English:
definition cycleGraph.cycle
  signature: (n : Nat)
  body: have hadj : (cycleGraph (n + 3)).Adj 0 (Fin.last (n + 2)) := by
    simp [cycleGraph_adj]
  Walk.cons hadj (cycleGraph.cycleCons n (Fin.last (n + 2)))

@[deprecated (since := "2026-02-15")]
alias cycleGraph_EulerianCircuit := cycleGraph.cycle

中文:
定义 cycleGraph.cycle
  签名: (n : 自然数)
  定义体: have hadj : (cycleGraph (n + 3)).Adj 0 (Fin.last (n + 2)) := by
    simp [cycleGraph_adj]
  Walk.cons hadj (cycleGraph.cycleCons n (Fin.last (n + 2)))

@[deprecated (since := "2026-02-15")]
alias cycleGraph_EulerianCircuit := cycleGraph.cycle

Depends on / 依赖: Fin.last, Walk.cons, cycleCons, cycleGraph, cycleGraph.cycleCons, cycleGraph_adj
-/
def cycleGraph.cycle (n : Nat) : (cycleGraph (n + 3)).Walk 0 0 :=
  have hadj : (cycleGraph (n + 3)).Adj 0 (Fin.last (n + 2)) := by
    simp [cycleGraph_adj]
  Walk.cons hadj (cycleGraph.cycleCons n (Fin.last (n + 2)))

@[deprecated (since := "2026-02-15")]
alias cycleGraph_EulerianCircuit := cycleGraph.cycle

/--
theorem `cycleGraph.length_cycle_cons` / 定理 `cycleGraph.length_cycle_cons`

English:
theorem cycleGraph.length_cycle_cons
  given: (n : Nat)

中文:
定理 cycleGraph.length_cycle_cons
  条件: (n : 自然数)
-/
private theorem cycleGraph.length_cycle_cons (n : Nat) :
    forall m : Fin (n + 3), (cycleGraph.cycleCons n m).length = m.val
  | ⟨0, h⟩ => by
    unfold cycleGraph.cycleCons
    rfl
  | ⟨m + 1, h⟩ => by
    unfold cycleGraph.cycleCons
    simp only [Walk.length_cons]
    rw [cycleGraph.length_cycle_cons n]

variable {n : Nat}

@[simp, grind =]
/--
theorem `cycleGraph.length_cycle` / 定理 `cycleGraph.length_cycle`

English:
theorem cycleGraph.length_cycle
  statement: (cycleGraph.cycle n).length = n + 3
  proof: by
  unfold cycleGraph.cycle
  simp [cycleGraph.length_cycle_cons]

@[deprecated (since := "2026-02-15")]
alias cycleGraph_EulerianCircuit_length := cycleGraph.length_cycle

中文:
定理 cycleGraph.length_cycle
  结论: (cycleGraph.cycle n).length = n + 3
  证明: by
  unfold cycleGraph.cycle
  simp [cycleGraph.length_cycle_cons]

@[deprecated (since := "2026-02-15")]
alias cycleGraph_EulerianCircuit_length := cycleGraph.length_cycle

Depends on / 依赖: cycleGraph, cycleGraph.cycle, cycleGraph.length_cycle_cons, length_cycle_cons
-/
theorem cycleGraph.length_cycle : (cycleGraph.cycle n).length = n + 3 := by
  unfold cycleGraph.cycle
  simp [cycleGraph.length_cycle_cons]

@[deprecated (since := "2026-02-15")]
alias cycleGraph_EulerianCircuit_length := cycleGraph.length_cycle

/--
theorem `cycleGraph.getVert_cycleCons` / 定理 `cycleGraph.getVert_cycleCons`

English:
theorem cycleGraph.getVert_cycleCons
  given: (m : Fin (n + 3)) (i : Nat) (hi : i <= m.val)
  proof: by
  obtain ⟨m, hm⟩ := m
  induction i generalizing m
  · simp [Nat.mod_eq_of_lt hm]
  · cases m <;> grind +locals [getVert_cons_succ]

中文:
定理 cycleGraph.getVert_cycleCons
  条件: (m : 有限集 (n + 3)) (i : 自然数) (hi : i <= m.val)
  证明: by
  obtain ⟨m, hm⟩ := m
  induction i generalizing m
  · simp [Nat.mod_eq_of_lt hm]
  · cases m <;> grind +locals [getVert_cons_succ]
-/
private theorem cycleGraph.getVert_cycleCons (m : Fin (n + 3)) (i : Nat) (hi : i <= m.val) :
    (cycleGraph.cycleCons n m).getVert i = (m - i) % (n + 3) := by
  obtain ⟨m, hm⟩ := m
  induction i generalizing m
  · simp [Nat.mod_eq_of_lt hm]
  · cases m <;> grind +locals [getVert_cons_succ]

/--
theorem `cycleGraph.getVert_cycle` / 定理 `cycleGraph.getVert_cycle`

English:
theorem cycleGraph.getVert_cycle
  given: {m : Nat} (hm : m <= n + 3)
  proof: by
  cases m
  · simp
  · grind +locals [getVert_cons_succ, cycleGraph.getVert_cycleCons]

中文:
定理 cycleGraph.getVert_cycle
  条件: {m : 自然数} (hm : m <= n + 3)
  证明: by
  cases m
  · simp
  · grind +locals [getVert_cons_succ, cycleGraph.getVert_cycleCons]

Depends on / 依赖: cycleGraph, cycleGraph.getVert_cycleCons, getVert_cons_succ, getVert_cycleCons, locals
-/
theorem cycleGraph.getVert_cycle {m : Nat} (hm : m <= n + 3) :
    (cycleGraph.cycle n).getVert m = ⟨(n + 3 - m) % (n + 3), Nat.mod_lt _ (by lia)⟩ := by
  cases m
  · simp
  · grind +locals [getVert_cons_succ, cycleGraph.getVert_cycleCons]

/--
theorem `cycleGraph.isPath_tail_cycle` / 定理 `cycleGraph.isPath_tail_cycle`

English:
theorem cycleGraph.isPath_tail_cycle
  statement: (cycleGraph.cycle n).tail.IsPath
  proof: by
.mpr fun ⟨i, hi⟩ ⟨j, hj⟩ hij => ?_ refine isPath_iff_injective_get_support _
  rw [support_tail_of_not_nil _ (of_decide_eq_false rfl)] at hi hj
  simp only [List.get_eq_getElem, support_getElem_eq_getVert, getVert_tail] at hij
  grind [← Nat.mod_eq_of_lt, cycleGraph.getVert_cycle]

中文:
定理 cycleGraph.isPath_tail_cycle
  结论: (cycleGraph.cycle n).tail.是道路
  证明: by
.mpr fun ⟨i, hi⟩ ⟨j, hj⟩ hij => ?_ refine isPath_iff_injective_get_support _
  rw [support_tail_of_not_nil _ (of_decide_eq_false rfl)] at hi hj
  simp only [List.get_eq_getElem, support_getElem_eq_getVert, getVert_tail] at hij
  grind [← Nat.mod_eq_of_lt, cycleGraph.getVert_cycle]

Depends on / 依赖: List.get_eq_getElem, Nat.mod_eq_of_lt, cycleGraph, cycleGraph.getVert_cycle, getVert_cycle, getVert_tail, get_eq_getElem, isPath_iff_injective_get_support, mod_eq_of_lt, of_decide_eq_false, support_getElem_eq_getVert, support_tail_of_not_nil
-/
theorem cycleGraph.isPath_tail_cycle : (cycleGraph.cycle n).tail.IsPath := by
.mpr fun ⟨i, hi⟩ ⟨j, hj⟩ hij => ?_ refine isPath_iff_injective_get_support _
  rw [support_tail_of_not_nil _ (of_decide_eq_false rfl)] at hi hj
  simp only [List.get_eq_getElem, support_getElem_eq_getVert, getVert_tail] at hij
  grind [← Nat.mod_eq_of_lt, cycleGraph.getVert_cycle]

/--
theorem `cycleGraph.isCycle_cycle` / 定理 `cycleGraph.isCycle_cycle`

English:
theorem cycleGraph.isCycle_cycle
  statement: (cycleGraph.cycle n).IsCycle
  proof: isCycle_iff_isPath_tail_and_le_length.mpr ⟨cycleGraph.isPath_tail_cycle, by simp⟩

中文:
定理 cycleGraph.isCycle_cycle
  结论: (cycleGraph.cycle n).是环
  证明: isCycle_iff_isPath_tail_and_le_length.mpr ⟨cycleGraph.isPath_tail_cycle, by simp⟩

Depends on / 依赖: cycleGraph, cycleGraph.isPath_tail_cycle, isCycle_iff_isPath_tail_and_le_length, isCycle_iff_isPath_tail_and_le_length.mpr, isPath_tail_cycle
-/
theorem cycleGraph.isCycle_cycle : (cycleGraph.cycle n).IsCycle :=
  isCycle_iff_isPath_tail_and_le_length.mpr ⟨cycleGraph.isPath_tail_cycle, by simp⟩

end cycle

section IsContained

variable {V : Type*} {G : SimpleGraph V}

/--
lemma `cycleGraph_isContained_iff` / 引理 `cycleGraph_isContained_iff`

English:
lemma cycleGraph_isContained_iff
  given: {n : Nat} (hn : 2 < n)
  proof: by
  refine ⟨fun ⟨h⟩ => ?_, fun h' => ?_⟩
  · have : n = n - 3 + 3 := by lia
    rw [this] at h
refine ⟨h.toHom ⟨0, by lia⟩, Walk.map h.toHom cycleGraph.cycle (n - 3), ?_, ?_⟩
    · exact (isCycle_map_iff_of_injective h.injective).mpr cycleGraph.isCycle_cycle
    · simp [cycleGraph.length_cycle, ← this]
  · obtain ⟨a, p, hp₁, hp₂⟩ := h'
    refine ⟨⟨⟨fun n => p.support[n.succ]'(?_), ?_⟩, ?_⟩⟩
    · grind [hp₁.three_le_length, length_tail_add_one, not_nil_iff_lt_length]
    · intro ⟨x, hx⟩ ⟨y, hy⟩ hab
      have hne : x != y := fun _ => by simp_all
      wlog hle : x > y
.symm · exact this hn a p hp₁ hp₂ y hy x hx hab.symm hne.symm (by lia)
      rcases cycleGraph_adj'.mp hab with hab | hab
      · simp_rw [show x = y + 1 by grind [Fin.sub_val_of_le]]
.symm exact p.isChain_adj_support.getElem _ _
      · rw [Fin.coe_sub_iff_lt.mpr hle] at hab
        simp_rw [show x = n - 1 by lia, show y = 0 by lia, Fin.succ_mk, show n - 1 + 1 = n by lia]
        simp [← hp₂, p.adj_snd hp₁.not_nil]
    · have hlen : p.tail.support.length = n := by
        grind [length_tail_add_one, not_nil_iff_lt_length]
      have (m : Fin n) : p.support[m.succ]'(by grind) = p.tail.support[m] := by
        simp [p.support_tail_of_not_nil hp₁.not_nil]
      simp_rw [this]
have := IsPath.mk' (support_tail_of_not_nil _ hp₁.not_nil) ▸ hp₁.support_nodup
      exact hlen ▸ (isPath_iff_injective_get_support _ |>.mp this)

中文:
引理 cycleGraph_isContained_iff
  条件: {n : 自然数} (hn : 2 < n)
  证明: by
  refine ⟨fun ⟨h⟩ => ?_, fun h' => ?_⟩
  · have : n = n - 3 + 3 := by lia
    rw [this] at h
refine ⟨h.toHom ⟨0, by lia⟩, Walk.map h.toHom cycleGraph.cycle (n - 3), ?_, ?_⟩
    · exact (isCycle_map_iff_of_injective h.injective).mpr cycleGraph.isCycle_cycle
    · simp [cycleGraph.length_cycle, ← this]
  · obtain ⟨a, p, hp₁, hp₂⟩ := h'
    refine ⟨⟨⟨fun n => p.support[n.succ]'(?_), ?_⟩, ?_⟩⟩
    · grind [hp₁.three_le_length, length_tail_add_one, not_nil_iff_lt_length]
    · intro ⟨x, hx⟩ ⟨y, hy⟩ hab
      have hne : x != y := fun _ => by simp_all
      wlog hle : x > y
.symm · exact this hn a p hp₁ hp₂ y hy x hx hab.symm hne.symm (by lia)
      rcases cycleGraph_adj'.mp hab with hab | hab
      · simp_rw [show x = y + 1 by grind [Fin.sub_val_of_le]]
.symm exact p.isChain_adj_support.getElem _ _
      · rw [Fin.coe_sub_iff_lt.mpr hle] at hab
        simp_rw [show x = n - 1 by lia, show y = 0 by lia, Fin.succ_mk, show n - 1 + 1 = n by lia]
        simp [← hp₂, p.adj_snd hp₁.not_nil]
    · have hlen : p.tail.support.length = n := by
        grind [length_tail_add_one, not_nil_iff_lt_length]
      have (m : Fin n) : p.support[m.succ]'(by grind) = p.tail.support[m] := by
        simp [p.support_tail_of_not_nil hp₁.not_nil]
      simp_rw [this]
have := IsPath.mk' (support_tail_of_not_nil _ hp₁.not_nil) ▸ hp₁.support_nodup
      exact hlen ▸ (isPath_iff_injective_get_support _ |>.mp this)

Depends on / 依赖: Walk.map, cycleGraph, cycleGraph.cycle, cycleGraph.isCycle_cycle, cycleGraph.length_cycle, h.injective, h.toHom, injective, isCycle_cycle, isCycle_map_iff_of_injective, length_cycle, length_tail_add_one, n.succ, not_nil_iff_lt_length, p.support, support, three_le_length
-/
lemma cycleGraph_isContained_iff {n : Nat} (hn : 2 < n) :
    cycleGraph n ⊑ G ↔ exists (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = n := by
  refine ⟨fun ⟨h⟩ => ?_, fun h' => ?_⟩
  · have : n = n - 3 + 3 := by lia
    rw [this] at h
refine ⟨h.toHom ⟨0, by lia⟩, Walk.map h.toHom cycleGraph.cycle (n - 3), ?_, ?_⟩
    · exact (isCycle_map_iff_of_injective h.injective).mpr cycleGraph.isCycle_cycle
    · simp [cycleGraph.length_cycle, ← this]
  · obtain ⟨a, p, hp₁, hp₂⟩ := h'
    refine ⟨⟨⟨fun n => p.support[n.succ]'(?_), ?_⟩, ?_⟩⟩
    · grind [hp₁.three_le_length, length_tail_add_one, not_nil_iff_lt_length]
    · intro ⟨x, hx⟩ ⟨y, hy⟩ hab
      have hne : x != y := fun _ => by simp_all
      wlog hle : x > y
.symm · exact this hn a p hp₁ hp₂ y hy x hx hab.symm hne.symm (by lia)
      rcases cycleGraph_adj'.mp hab with hab | hab
      · simp_rw [show x = y + 1 by grind [Fin.sub_val_of_le]]
.symm exact p.isChain_adj_support.getElem _ _
      · rw [Fin.coe_sub_iff_lt.mpr hle] at hab
        simp_rw [show x = n - 1 by lia, show y = 0 by lia, Fin.succ_mk, show n - 1 + 1 = n by lia]
        simp [← hp₂, p.adj_snd hp₁.not_nil]
    · have hlen : p.tail.support.length = n := by
        grind [length_tail_add_one, not_nil_iff_lt_length]
      have (m : Fin n) : p.support[m.succ]'(by grind) = p.tail.support[m] := by
        simp [p.support_tail_of_not_nil hp₁.not_nil]
      simp_rw [this]
have := IsPath.mk' (support_tail_of_not_nil _ hp₁.not_nil) ▸ hp₁.support_nodup
      exact hlen ▸ (isPath_iff_injective_get_support _ |>.mp this)

end IsContained

end SimpleGraph
