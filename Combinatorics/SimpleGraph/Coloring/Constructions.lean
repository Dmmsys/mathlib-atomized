/-
Copyright (c) 2023 Iván Renison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iván Renison
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Circulant
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Data.Fin.Parity

/-!
# Concrete colorings of common graphs

This file defines colorings for some common graphs.

## Main declarations

* `SimpleGraph.pathGraph.bicoloring`: Bicoloring of a path graph.

-/

@[expose] public section

assert_not_exists Field

namespace SimpleGraph

/--
Definition of `pathGraph.bicoloring` / `pathGraph.bicoloring` 的定义

English:
definition pathGraph.bicoloring
  signature: (n : Nat)
  body: Coloring.mk (fun u => u.val % 2 = 0) by
    intro u v
    rw [pathGraph_adj]
    rintro (h | h) <;> simp [← h, not_iff, Nat.succ_mod_two_eq_zero_iff]

中文:
定义 pathGraph.bicoloring
  签名: (n : 自然数)
  定义体: Coloring.mk (fun u => u.val % 2 = 0) by
    intro u v
    rw [pathGraph_adj]
    rintro (h | h) <;> simp [← h, not_iff, Nat.succ_mod_two_eq_zero_iff]

Depends on / 依赖: Coloring, Coloring.mk, Nat.succ_mod_two_eq_zero_iff, not_iff, pathGraph_adj, succ_mod_two_eq_zero_iff, u.val
-/
def pathGraph.bicoloring (n : Nat) :
    Coloring (pathGraph n) Bool :=
Coloring.mk (fun u => u.val % 2 = 0) by
    intro u v
    rw [pathGraph_adj]
    rintro (h | h) <;> simp [← h, not_iff, Nat.succ_mod_two_eq_zero_iff]

/--
Definition of `pathGraph_two_embedding` / `pathGraph_two_embedding` 的定义

English:
definition pathGraph_two_embedding
  signature: (n : Nat) (h : 2 <= n)
  body: ⟨v, trans v.2 h⟩
  inj' := by
    rintro v w
    rw [Fin.mk.injEq]
    exact Fin.ext
  map_rel_iff' := by simp [pathGraph]

中文:
定义 pathGraph_two_embedding
  签名: (n : 自然数) (h : 2 <= n)
  定义体: ⟨v, trans v.2 h⟩
  inj' := by
    rintro v w
    rw [Fin.mk.injEq]
    exact Fin.ext
  map_rel_iff' := by simp [pathGraph]
-/
def pathGraph_two_embedding (n : Nat) (h : 2 <= n) : pathGraph 2 ↪g pathGraph n where
  toFun v := ⟨v, trans v.2 h⟩
  inj' := by
    rintro v w
    rw [Fin.mk.injEq]
    exact Fin.ext
  map_rel_iff' := by simp [pathGraph]

/--
theorem `chromaticNumber_pathGraph` / 定理 `chromaticNumber_pathGraph`

English:
theorem chromaticNumber_pathGraph
  given: (n : Nat) (h : 2 <= n)
  proof: by
  have hc := (pathGraph.bicoloring n).colorable
  apply le_antisymm
  · exact hc.chromaticNumber_le
  · have hadj : (pathGraph n).Adj ⟨0, Nat.zero_lt_of_lt h⟩ ⟨1, h⟩ := by simp [pathGraph_adj]
    exact two_le_chromaticNumber_of_adj hadj

中文:
定理 chromaticNumber_pathGraph
  条件: (n : 自然数) (h : 2 <= n)
  证明: by
  have hc := (pathGraph.bicoloring n).colorable
  apply le_antisymm
  · exact hc.chromaticNumber_le
  · have hadj : (pathGraph n).Adj ⟨0, Nat.zero_lt_of_lt h⟩ ⟨1, h⟩ := by simp [pathGraph_adj]
    exact two_le_chromaticNumber_of_adj hadj

Depends on / 依赖: Nat.zero_lt_of_lt, bicoloring, chromaticNumber_le, colorable, hc.chromaticNumber_le, le_antisymm, pathGraph, pathGraph.bicoloring, pathGraph_adj, two_le_chromaticNumber_of_adj, zero_lt_of_lt
-/
theorem chromaticNumber_pathGraph (n : Nat) (h : 2 <= n) :
    (pathGraph n).chromaticNumber = 2 := by
  have hc := (pathGraph.bicoloring n).colorable
  apply le_antisymm
  · exact hc.chromaticNumber_le
  · have hadj : (pathGraph n).Adj ⟨0, Nat.zero_lt_of_lt h⟩ ⟨1, h⟩ := by simp [pathGraph_adj]
    exact two_le_chromaticNumber_of_adj hadj

/--
theorem `Coloring.even_length_iff_congr` / 定理 `Coloring.even_length_iff_congr`

English:
theorem Coloring.even_length_iff_congr
  statement: {α} {G : SimpleGraph α}
  proof: by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
    simp only [Walk.length_cons, Nat.even_add_one]
    have : ¬ c u = true ↔ c v = true := by
      rw [← not_iff]; rw [← Bool.eq_iff_iff]
      exact c.valid h
    tauto

中文:
定理 Coloring.even_length_iff_congr
  结论: {α} {G : SimpleGraph α}
  证明: by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
    simp only [Walk.length_cons, Nat.even_add_one]
    have : ¬ c u = true ↔ c v = true := by
      rw [← not_iff]; rw [← Bool.eq_iff_iff]
      exact c.valid h
    tauto

Depends on / 依赖: Bool.eq_iff_iff, Nat.even_add_one, Walk.length_cons, c.valid, eq_iff_iff, even_add_one, length_cons, not_iff
-/
theorem Coloring.even_length_iff_congr {α} {G : SimpleGraph α}
    (c : G.Coloring Bool) {u v : α} (p : G.Walk u v) :
    Even p.length ↔ (c u ↔ c v) := by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
    simp only [Walk.length_cons, Nat.even_add_one]
    have : ¬ c u = true ↔ c v = true := by
      rw [← not_iff]; rw [← Bool.eq_iff_iff]
      exact c.valid h
    tauto

/--
theorem `Coloring.odd_length_iff_not_congr` / 定理 `Coloring.odd_length_iff_not_congr`

English:
theorem Coloring.odd_length_iff_not_congr
  statement: {α} {G : SimpleGraph α}
  proof: by
  rw [← Nat.not_even_iff_odd]; rw [c.even_length_iff_congr p]
  tauto

中文:
定理 Coloring.odd_length_iff_not_congr
  结论: {α} {G : SimpleGraph α}
  证明: by
  rw [← Nat.not_even_iff_odd]; rw [c.even_length_iff_congr p]
  tauto

Depends on / 依赖: Nat.not_even_iff_odd, c.even_length_iff_congr, even_length_iff_congr, not_even_iff_odd
-/
theorem Coloring.odd_length_iff_not_congr {α} {G : SimpleGraph α}
    (c : G.Coloring Bool) {u v : α} (p : G.Walk u v) :
    Odd p.length ↔ (¬c u ↔ c v) := by
  rw [← Nat.not_even_iff_odd]; rw [c.even_length_iff_congr p]
  tauto

/--
theorem `Walk.three_le_chromaticNumber_of_odd_loop` / 定理 `Walk.three_le_chromaticNumber_of_odd_loop`

English:
theorem Walk.three_le_chromaticNumber_of_odd_loop
  statement: {α} {G : SimpleGraph α} {u : α} (p : G.Walk u u)
  proof: Classical.by_contradiction by
  intro h
have h' : G.chromaticNumber <= 2 := Order.le_of_lt_add_one not_le.mp h
  let c : G.Coloring (Fin 2) := (chromaticNumber_le_iff_colorable.mp h').some
  let c' : G.Coloring Bool := recolorOfEquiv G finTwoEquiv c
  have : ¬c' u ↔ c' u := (c'.odd_length_iff_not_co

中文:
定理 Walk.three_le_chromaticNumber_of_odd_loop
  结论: {α} {G : SimpleGraph α} {u : α} (p : G.Walk u u)
  证明: Classical.by_contradiction by
  intro h
have h' : G.chromaticNumber <= 2 := Order.le_of_lt_add_one not_le.mp h
  let c : G.Coloring (Fin 2) := (chromaticNumber_le_iff_colorable.mp h').some
  let c' : G.Coloring Bool := recolorOfEquiv G finTwoEquiv c
  have : ¬c' u ↔ c' u := (c'.odd_length_iff_not_co

Depends on / 依赖: Classical, Classical.by_contradiction, Coloring, G.Coloring, G.chromaticNumber, Order.le_of_lt_add_one, by_contradiction, chromaticNumber, chromaticNumber_le_iff_colorable, chromaticNumber_le_iff_colorable.mp, finTwoEquiv, le_of_lt_add_one, not_le, not_le.mp, odd_length_iff_not_congr, recolorOfEquiv
-/
theorem Walk.three_le_chromaticNumber_of_odd_loop {α} {G : SimpleGraph α} {u : α} (p : G.Walk u u)
(hOdd : Odd p.length) : 3 <= G.chromaticNumber := Classical.by_contradiction by
  intro h
have h' : G.chromaticNumber <= 2 := Order.le_of_lt_add_one not_le.mp h
  let c : G.Coloring (Fin 2) := (chromaticNumber_le_iff_colorable.mp h').some
  let c' : G.Coloring Bool := recolorOfEquiv G finTwoEquiv c
  have : ¬c' u ↔ c' u := (c'.odd_length_iff_not_congr p).mp hOdd
  simp_all

/--
Definition of `cycleGraph.bicoloring_of_even` / `cycleGraph.bicoloring_of_even` 的定义

English:
definition cycleGraph.bicoloring_of_even
  signature: (n : Nat) (h : Even n)
  body: Coloring.mk (fun u => u.val % 2 = 0) by
    intro u v hadj
    match n with
    | 0 => exact u.elim0
    | 1 => simp at h
    | n + 2 =>
      simp only [ne_eq, decide_eq_decide]
      simp only [cycleGraph_adj] at hadj
      cases hadj with
      | inl huv | inr huv =>
        rw [← add_eq_of_eq_su

中文:
定义 cycleGraph.bicoloring_of_even
  签名: (n : 自然数) (h : Even n)
  定义体: Coloring.mk (fun u => u.val % 2 = 0) by
    intro u v hadj
    match n with
    | 0 => exact u.elim0
    | 1 => simp at h
    | n + 2 =>
      simp only [ne_eq, decide_eq_decide]
      simp only [cycleGraph_adj] at hadj
      cases hadj with
      | inl huv | inr huv =>
        rw [← add_eq_of_eq_su

Depends on / 依赖: Classical, Classical.not_iff.mpr, Coloring, Coloring.mk, Fin.even_add_one_iff_odd, Fin.even_iff_mod_of_even, Fin.not_even_iff_odd_of_even, Fin.not_odd_iff_even_of_even, add_eq_of_eq_sub, cycleGraph_adj, decide_eq_decide, even_add_one_iff_odd, even_iff_mod_of_even, huv.symm, ne_eq, not_even_iff_odd_of_even, not_iff, not_odd_iff_even_of_even, u.elim0, u.val
-/
def cycleGraph.bicoloring_of_even (n : Nat) (h : Even n) : Coloring (cycleGraph n) Bool :=
Coloring.mk (fun u => u.val % 2 = 0) by
    intro u v hadj
    match n with
    | 0 => exact u.elim0
    | 1 => simp at h
    | n + 2 =>
      simp only [ne_eq, decide_eq_decide]
      simp only [cycleGraph_adj] at hadj
      cases hadj with
      | inl huv | inr huv =>
        rw [← add_eq_of_eq_sub' huv.symm]; rw [← Fin.even_iff_mod_of_even h]; rw [← Fin.even_iff_mod_of_even h]; rw [Fin.even_add_one_iff_odd]
        apply Classical.not_iff.mpr
        simp [Fin.not_odd_iff_even_of_even h, Fin.not_even_iff_odd_of_even h]

/--
theorem `chromaticNumber_cycleGraph_of_even` / 定理 `chromaticNumber_cycleGraph_of_even`

English:
theorem chromaticNumber_cycleGraph_of_even
  given: (n : Nat) (h : 2 <= n) (hEven : Even n)
  proof: by
  have hc := (cycleGraph.bicoloring_of_even n hEven).colorable
  apply le_antisymm
  · apply hc.chromaticNumber_le
  · have hadj : (cycleGraph n).Adj ⟨0, Nat.zero_lt_of_lt h⟩ ⟨1, h⟩ := by
      simp [cycleGraph_adj', Fin.sub_val_of_le]
    exact two_le_chromaticNumber_of_adj hadj

中文:
定理 chromaticNumber_cycleGraph_of_even
  条件: (n : 自然数) (h : 2 <= n) (hEven : Even n)
  证明: by
  have hc := (cycleGraph.bicoloring_of_even n hEven).colorable
  apply le_antisymm
  · apply hc.chromaticNumber_le
  · have hadj : (cycleGraph n).Adj ⟨0, Nat.zero_lt_of_lt h⟩ ⟨1, h⟩ := by
      simp [cycleGraph_adj', Fin.sub_val_of_le]
    exact two_le_chromaticNumber_of_adj hadj

Depends on / 依赖: Fin.sub_val_of_le, Nat.zero_lt_of_lt, bicoloring_of_even, chromaticNumber_le, colorable, cycleGraph, cycleGraph.bicoloring_of_even, cycleGraph_adj, hc.chromaticNumber_le, le_antisymm, sub_val_of_le, two_le_chromaticNumber_of_adj, zero_lt_of_lt
-/
theorem chromaticNumber_cycleGraph_of_even (n : Nat) (h : 2 <= n) (hEven : Even n) :
    (cycleGraph n).chromaticNumber = 2 := by
  have hc := (cycleGraph.bicoloring_of_even n hEven).colorable
  apply le_antisymm
  · apply hc.chromaticNumber_le
  · have hadj : (cycleGraph n).Adj ⟨0, Nat.zero_lt_of_lt h⟩ ⟨1, h⟩ := by
      simp [cycleGraph_adj', Fin.sub_val_of_le]
    exact two_le_chromaticNumber_of_adj hadj

/--
Definition of `cycleGraph.tricoloring` / `cycleGraph.tricoloring` 的定义

English:
definition cycleGraph.tricoloring
  signature: (n : Nat) (h : 2 <= n)
  body: Coloring.mk (fun u => if u.val = n - 1 then 2 else ⟨u.val % 2, by lia⟩) by
    intro u v hadj
    match n with
    | 0 => exact u.elim0
    | 1 => simp at h
    | n + 2 =>
      simp only [cycleGraph_adj] at hadj
      split_ifs with hu hv
      · simp [Fin.eq_mk_iff_val_eq.mpr hu, Fin.eq_mk_iff_val

中文:
定义 cycleGraph.tricoloring
  签名: (n : 自然数) (h : 2 <= n)
  定义体: Coloring.mk (fun u => if u.val = n - 1 then 2 else ⟨u.val % 2, by lia⟩) by
    intro u v hadj
    match n with
    | 0 => exact u.elim0
    | 1 => simp at h
    | n + 2 =>
      simp only [cycleGraph_adj] at hadj
      split_ifs with hu hv
      · simp [Fin.eq_mk_iff_val_eq.mpr hu, Fin.eq_mk_iff_val

Depends on / 依赖: Coloring, Coloring.mk, Fin.eq_mk_iff_val_eq.mpr, Fin.ext_iff, Fin.mk_lt_of_lt_val, Fin.ne_of_lt, Nat.zero_lt_two, cycleGraph_adj, eq_mk_iff_val_eq, ext_iff, mk_lt_of_lt_val, mod_lt, ne_eq, ne_of_lt, split_ifs, u.elim0, u.val, u.val.mod_lt, v.val.mod_lt, zero_lt_two
-/
def cycleGraph.tricoloring (n : Nat) (h : 2 <= n) : Coloring (cycleGraph n)
(Fin 3) := Coloring.mk (fun u => if u.val = n - 1 then 2 else ⟨u.val % 2, by lia⟩) by
    intro u v hadj
    match n with
    | 0 => exact u.elim0
    | 1 => simp at h
    | n + 2 =>
      simp only [cycleGraph_adj] at hadj
      split_ifs with hu hv
      · simp [Fin.eq_mk_iff_val_eq.mpr hu, Fin.eq_mk_iff_val_eq.mpr hv] at hadj
      · refine (Fin.ne_of_lt (Fin.mk_lt_of_lt_val (?_))).symm
        exact v.val.mod_lt Nat.zero_lt_two
      · refine (Fin.ne_of_lt (Fin.mk_lt_of_lt_val ?_))
        exact u.val.mod_lt Nat.zero_lt_two
      · simp only [ne_eq, Fin.ext_iff]
        have hu' : u.val + (1 : Fin (n + 2)) < n + 2 := by fin_omega
        have hv' : v.val + (1 : Fin (n + 2)) < n + 2 := by fin_omega
        cases hadj with
        | inl huv | inr huv =>
          rw [← add_eq_of_eq_sub' huv.symm]
          simp only [Fin.val_add_eq_of_add_lt hv', Fin.val_add_eq_of_add_lt hu', Fin.val_one]
          rw [show forall x y : Nat]; rw [x % 2 = y % 2 ↔ (Even x ↔ Even y) by simp [Nat.even_iff]; lia,
            Nat.even_add]
          simp only [Nat.not_even_one, iff_false, not_iff_self, iff_not_self]
          exact id

/--
theorem `chromaticNumber_cycleGraph_of_odd` / 定理 `chromaticNumber_cycleGraph_of_odd`

English:
theorem chromaticNumber_cycleGraph_of_odd
  given: (n : Nat) (h : 2 <= n) (hOdd : Odd n)
  proof: by
  have hc := (cycleGraph.tricoloring n h).colorable
  apply le_antisymm
  · apply hc.chromaticNumber_le
  · have hn3 : n - 3 + 3 = n := by
      refine Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.lt_of_le_of_ne h ?_))
      intro h2
      rw [← h2] at hOdd
      exact (Nat.not_odd_iff.mpr rfl) hOd

中文:
定理 chromaticNumber_cycleGraph_of_odd
  条件: (n : 自然数) (h : 2 <= n) (hOdd : Odd n)
  证明: by
  have hc := (cycleGraph.tricoloring n h).colorable
  apply le_antisymm
  · apply hc.chromaticNumber_le
  · have hn3 : n - 3 + 3 = n := by
      refine Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.lt_of_le_of_ne h ?_))
      intro h2
      rw [← h2] at hOdd
      exact (Nat.not_odd_iff.mpr rfl) hOd

Depends on / 依赖: Nat.lt_of_le_of_ne, Nat.not_odd_iff.mpr, Nat.sub_add_cancel, Nat.succ_le_of_lt, Walk.three_le_chromaticNumber_of_odd_loop, chromaticNumber_le, colorable, cycleGraph, cycleGraph.cycle, cycleGraph.length_cycle, cycleGraph.tricoloring, hc.chromaticNumber_le, le_antisymm, length, length_cycle, lt_of_le_of_ne, not_odd_iff, sub_add_cancel, succ_le_of_lt, three_le_chromaticNumber_of_odd_loop
-/
theorem chromaticNumber_cycleGraph_of_odd (n : Nat) (h : 2 <= n) (hOdd : Odd n) :
    (cycleGraph n).chromaticNumber = 3 := by
  have hc := (cycleGraph.tricoloring n h).colorable
  apply le_antisymm
  · apply hc.chromaticNumber_le
  · have hn3 : n - 3 + 3 = n := by
      refine Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.lt_of_le_of_ne h ?_))
      intro h2
      rw [← h2] at hOdd
      exact (Nat.not_odd_iff.mpr rfl) hOdd
    let w : (cycleGraph (n - 3 + 3)).Walk 0 0 := cycleGraph.cycle (n - 3)
    have hOdd' : Odd w.length := by
      rw [cycleGraph.length_cycle]; rw [hn3]
      exact hOdd
    rw [← hn3]
    exact Walk.three_le_chromaticNumber_of_odd_loop w hOdd'

section CompleteEquipartiteGraph

variable {r t : Nat}

/--
Definition of `Coloring.completeEquipartiteGraph` / `Coloring.completeEquipartiteGraph` 的定义

English:
definition Coloring.completeEquipartiteGraph
  signature: :
  body: ⟨Prod.fst, id⟩

中文:
定义 Coloring.completeEquipartiteGraph
  签名: :
  定义体: ⟨Prod.fst, id⟩

Depends on / 依赖: Prod.fst
-/
def Coloring.completeEquipartiteGraph :
  (completeEquipartiteGraph r t).Coloring (Fin r) := ⟨Prod.fst, id⟩

/--
theorem `completeEquipartiteGraph_colorable` / 定理 `completeEquipartiteGraph_colorable`

English:
theorem completeEquipartiteGraph_colorable
  proof: ⟨Coloring.completeEquipartiteGraph⟩

中文:
定理 completeEquipartiteGraph_colorable
  证明: ⟨Coloring.completeEquipartiteGraph⟩

Depends on / 依赖: Coloring, Coloring.completeEquipartiteGraph, completeEquipartiteGraph
-/
theorem completeEquipartiteGraph_colorable :
  (completeEquipartiteGraph r t).Colorable r := ⟨Coloring.completeEquipartiteGraph⟩

end CompleteEquipartiteGraph

open Walk
/--
lemma `two_colorable_iff_forall_loop_even` / 引理 `two_colorable_iff_forall_loop_even`

English:
lemma two_colorable_iff_forall_loop_even
  given: {α : Type*} {G : SimpleGraph α}
  proof: by
  simp_rw [← Nat.not_odd_iff_even]
  constructor <;> intro h
  · intro _ w ho
    have := (w.three_le_chromaticNumber_of_odd_loop ho).trans h.chromaticNumber_le
    norm_cast
  · apply colorable_iff_forall_connectedComponent.2
    intro c
    obtain ⟨_, hv⟩ := c.nonempty_supp
    use fun a => Fin

中文:
引理 two_colorable_iff_forall_loop_even
  条件: {α : 类型} {G : SimpleGraph α}
  证明: by
  simp_rw [← Nat.not_odd_iff_even]
  constructor <;> intro h
  · intro _ w ho
    have := (w.three_le_chromaticNumber_of_odd_loop ho).trans h.chromaticNumber_le
    norm_cast
  · apply colorable_iff_forall_connectedComponent.2
    intro c
    obtain ⟨_, hv⟩ := c.nonempty_supp
    use fun a => Fin

Depends on / 依赖: Fin.ofNat, Nat.not_odd_iff_even, append, c.connected_toSimpleGraph, c.nonempty_supp, c.toSimpleGraph_hom, chromaticNumber_le, colorable_iff_forall_connectedComponent, concat, connected_toSimpleGraph, h.chromaticNumber_le, length, nonempty_supp, not_odd_iff_even, reverse, simp_rw, some.concat, some.length, some.reverse, three_le_chromaticNumber_of_odd_loop
-/
lemma two_colorable_iff_forall_loop_even {α : Type*} {G : SimpleGraph α} :
    G.Colorable 2 ↔ forall u, forall (w : G.Walk u u), Even w.length := by
  simp_rw [← Nat.not_odd_iff_even]
  constructor <;> intro h
  · intro _ w ho
    have := (w.three_le_chromaticNumber_of_odd_loop ho).trans h.chromaticNumber_le
    norm_cast
  · apply colorable_iff_forall_connectedComponent.2
    intro c
    obtain ⟨_, hv⟩ := c.nonempty_supp
    use fun a => Fin.ofNat 2 (c.connected_toSimpleGraph ⟨_, hv⟩ a).some.length
    intro a b hab he
apply h _ (((c.connected_toSimpleGraph ⟨_, hv⟩ a).some.concat hab).append
                 (c.connected_toSimpleGraph ⟨_, hv⟩ b).some.reverse).map c.toSimpleGraph_hom
    rw [length_map]; rw [length_append]; rw [length_concat]; rw [length_reverse]; rw [add_right_comm]
    have : ((Nonempty.some (c.connected_toSimpleGraph ⟨_, hv⟩ a)).length) % 2 =
        (Nonempty.some (c.connected_toSimpleGraph ⟨_, hv⟩ b)).length % 2 := by
      simp_rw [← Fin.val_natCast, ← Fin.ofNat_eq_cast, he]
    exact (Nat.even_iff.mpr (by lia)).add_one

end SimpleGraph
