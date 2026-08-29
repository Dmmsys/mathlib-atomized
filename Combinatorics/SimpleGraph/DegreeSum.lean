/-
Copyright (c) 2020 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Combinatorics.SimpleGraph.Dart
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.ZMod.Basic

/-!
# Degree-sum formula and handshaking lemma

The degree-sum formula is that the sum of the degrees of the vertices in
a finite graph is equal to twice the number of edges. The handshaking lemma,
a corollary, is that the number of odd-degree vertices is even.

## Main definitions

- `SimpleGraph.sum_degrees_eq_twice_card_edges` is the degree-sum formula.
- `SimpleGraph.even_card_odd_degree_vertices` is the handshaking lemma.
- `SimpleGraph.odd_card_odd_degree_vertices_ne` is that the number of odd-degree
  vertices different from a given odd-degree vertex is odd.
- `SimpleGraph.exists_ne_odd_degree_of_exists_odd_degree` is that the existence of an
  odd-degree vertex implies the existence of another one.

## Implementation notes

We give a combinatorial proof by using the facts that (1) the map from
darts to vertices is such that each fiber has cardinality the degree
of the corresponding vertex and that (2) the map from darts to edges is 2-to-1.

## Tags

simple graphs, sums, degree-sum formula, handshaking lemma
-/

public section

assert_not_exists Field TwoSidedIdeal

open Finset

namespace SimpleGraph

universe u

variable {V : Type u} (G : SimpleGraph V)

section DegreeSum

variable [Fintype V] [DecidableRel G.Adj]

/--
theorem `dart_fst_fiber` / 定理 `dart_fst_fiber`

English:
theorem dart_fst_fiber
  given: [DecidableEq V] (v : V)
  proof: by
  ext d
  simp only [mem_image, true_and, mem_filter, SetCoe.exists, mem_univ]
  constructor
  · rintro rfl
    exact ⟨_, d.adj, by ext <;> rfl⟩
  · rintro ⟨e, he, rfl⟩
    rfl

中文:
定理 dart_fst_fiber
  条件: [DecidableEq V] (v : V)
  证明: by
  ext d
  simp only [mem_image, true_and, mem_filter, SetCoe.exists, mem_univ]
  constructor
  · rintro rfl
    exact ⟨_, d.adj, by ext <;> rfl⟩
  · rintro ⟨e, he, rfl⟩
    rfl

Depends on / 依赖: SetCoe, SetCoe.exists, d.adj, mem_filter, mem_image, mem_univ, true_and
-/
theorem dart_fst_fiber [DecidableEq V] (v : V) :
    ({d : G.Dart | d.fst = v} : Finset _) = univ.image (G.dartOfNeighborSet v) := by
  ext d
  simp only [mem_image, true_and, mem_filter, SetCoe.exists, mem_univ]
  constructor
  · rintro rfl
    exact ⟨_, d.adj, by ext <;> rfl⟩
  · rintro ⟨e, he, rfl⟩
    rfl

/--
theorem `dart_fst_fiber_card_eq_degree` / 定理 `dart_fst_fiber_card_eq_degree`

English:
theorem dart_fst_fiber_card_eq_degree
  given: [DecidableEq V] (v : V)
  proof: by
  simpa only [dart_fst_fiber, Finset.card_univ, card_neighborSet_eq_degree] using
    card_image_of_injective univ (G.dartOfNeighborSet_injective v)

中文:
定理 dart_fst_fiber_card_eq_degree
  条件: [DecidableEq V] (v : V)
  证明: by
  simpa only [dart_fst_fiber, Finset.card_univ, card_neighborSet_eq_degree] using
    card_image_of_injective univ (G.dartOfNeighborSet_injective v)

Depends on / 依赖: Finset, Finset.card_univ, G.dartOfNeighborSet_injective, card_image_of_injective, card_neighborSet_eq_degree, card_univ, dartOfNeighborSet_injective, dart_fst_fiber
-/
theorem dart_fst_fiber_card_eq_degree [DecidableEq V] (v : V) :
    #{d : G.Dart | d.fst = v} = G.degree v := by
  simpa only [dart_fst_fiber, Finset.card_univ, card_neighborSet_eq_degree] using
    card_image_of_injective univ (G.dartOfNeighborSet_injective v)

/--
theorem `dart_card_eq_sum_degrees` / 定理 `dart_card_eq_sum_degrees`

English:
theorem dart_card_eq_sum_degrees
  statement: Fintype.card G.Dart = ∑ v, G.degree v
  proof: by
  have := Classical.decEq V
  simp only [← card_univ, ← dart_fst_fiber_card_eq_degree]
  exact card_eq_sum_card_fiberwise (by simp)

中文:
定理 dart_card_eq_sum_degrees
  结论: 有限类型.card G.Dart = ∑ v, G.degree v
  证明: by
  have := Classical.decEq V
  simp only [← card_univ, ← dart_fst_fiber_card_eq_degree]
  exact card_eq_sum_card_fiberwise (by simp)

Depends on / 依赖: Classical, Classical.decEq, card_eq_sum_card_fiberwise, card_univ, dart_fst_fiber_card_eq_degree
-/
theorem dart_card_eq_sum_degrees : Fintype.card G.Dart = ∑ v, G.degree v := by
  have := Classical.decEq V
  simp only [← card_univ, ← dart_fst_fiber_card_eq_degree]
  exact card_eq_sum_card_fiberwise (by simp)

variable {G} in
/--
theorem `Dart.edge_fiber` / 定理 `Dart.edge_fiber`

English:
theorem Dart.edge_fiber
  given: [DecidableEq V] (d : G.Dart)
  proof: Finset.ext fun d' => by simpa using dart_edge_eq_iff d' d

中文:
定理 Dart.edge_fiber
  条件: [DecidableEq V] (d : G.Dart)
  证明: Finset.ext fun d' => by simpa using dart_edge_eq_iff d' d

Depends on / 依赖: Finset, Finset.ext, dart_edge_eq_iff
-/
theorem Dart.edge_fiber [DecidableEq V] (d : G.Dart) :
    ({d' : G.Dart | d'.edge = d.edge} : Finset _) = {d, d.symm} :=
  Finset.ext fun d' => by simpa using dart_edge_eq_iff d' d

/--
theorem `dart_edge_fiber_card` / 定理 `dart_edge_fiber_card`

English:
theorem dart_edge_fiber_card
  given: [DecidableEq V] (e : Sym2 V) (h : e in G.edgeSet)
  proof: by
  obtain ⟨v, w⟩ := e
  let d : G.Dart := ⟨(v, w), h⟩
  convert! congr_arg card d.edge_fiber
  rw [card_insert_of_notMem]; rw [card_singleton]
  rw [mem_singleton]
  exact d.symm_ne.symm

中文:
定理 dart_edge_fiber_card
  条件: [DecidableEq V] (e : Sym2 V) (h : e in G.edgeSet)
  证明: by
  obtain ⟨v, w⟩ := e
  let d : G.Dart := ⟨(v, w), h⟩
  convert! congr_arg card d.edge_fiber
  rw [card_insert_of_notMem]; rw [card_singleton]
  rw [mem_singleton]
  exact d.symm_ne.symm

Depends on / 依赖: G.Dart, card_insert_of_notMem, card_singleton, congr_arg, convert, d.edge_fiber, d.symm_ne.symm, edge_fiber, mem_singleton, symm_ne
-/
theorem dart_edge_fiber_card [DecidableEq V] (e : Sym2 V) (h : e in G.edgeSet) :
    #{d : G.Dart | d.edge = e} = 2 := by
  obtain ⟨v, w⟩ := e
  let d : G.Dart := ⟨(v, w), h⟩
  convert! congr_arg card d.edge_fiber
  rw [card_insert_of_notMem]; rw [card_singleton]
  rw [mem_singleton]
  exact d.symm_ne.symm

/--
theorem `dart_card_eq_twice_card_edges` / 定理 `dart_card_eq_twice_card_edges`

English:
theorem dart_card_eq_twice_card_edges
  statement: Fintype.card G.Dart = 2 * #G.edgeFinset
  proof: by
  classical
  rw [← card_univ]
  rw [@card_eq_sum_card_fiberwise _ _ _ Dart.edge _ G.edgeFinset fun d _h =>
      by rw [mem_coe]; rw [mem_edgeFinset]; apply Dart.edge_mem]
  rw [← mul_comm]; rw [sum_const_nat]
  intro e h
  apply G.dart_edge_fiber_card e
  rwa [← mem_edgeFinset]

中文:
定理 dart_card_eq_twice_card_edges
  结论: 有限类型.card G.Dart = 2 * #G.edgeFinset
  证明: by
  classical
  rw [← card_univ]
  rw [@card_eq_sum_card_fiberwise _ _ _ Dart.edge _ G.edgeFinset fun d _h =>
      by rw [mem_coe]; rw [mem_edgeFinset]; apply Dart.edge_mem]
  rw [← mul_comm]; rw [sum_const_nat]
  intro e h
  apply G.dart_edge_fiber_card e
  rwa [← mem_edgeFinset]

Depends on / 依赖: Dart.edge, Dart.edge_mem, G.dart_edge_fiber_card, G.edgeFinset, card_eq_sum_card_fiberwise, card_univ, classical, dart_edge_fiber_card, edgeFinset, edge_mem, mem_coe, mem_edgeFinset, mul_comm, sum_const_nat
-/
theorem dart_card_eq_twice_card_edges : Fintype.card G.Dart = 2 * #G.edgeFinset := by
  classical
  rw [← card_univ]
  rw [@card_eq_sum_card_fiberwise _ _ _ Dart.edge _ G.edgeFinset fun d _h =>
      by rw [mem_coe]; rw [mem_edgeFinset]; apply Dart.edge_mem]
  rw [← mul_comm]; rw [sum_const_nat]
  intro e h
  apply G.dart_edge_fiber_card e
  rwa [← mem_edgeFinset]

/--
theorem `sum_degrees_eq_twice_card_edges` / 定理 `sum_degrees_eq_twice_card_edges`

English:
theorem sum_degrees_eq_twice_card_edges
  statement: ∑ v, G.degree v = 2 * #G.edgeFinset
  proof: G.dart_card_eq_sum_degrees.symm.trans G.dart_card_eq_twice_card_edges

中文:
定理 sum_degrees_eq_twice_card_edges
  结论: ∑ v, G.degree v = 2 * #G.edgeFinset
  证明: G.dart_card_eq_sum_degrees.symm.trans G.dart_card_eq_twice_card_edges

Depends on / 依赖: G.dart_card_eq_sum_degrees.symm.trans, G.dart_card_eq_twice_card_edges, dart_card_eq_sum_degrees, dart_card_eq_twice_card_edges
-/
theorem sum_degrees_eq_twice_card_edges : ∑ v, G.degree v = 2 * #G.edgeFinset :=
  G.dart_card_eq_sum_degrees.symm.trans G.dart_card_eq_twice_card_edges

/--
lemma `two_mul_card_edgeFinset` / 引理 `two_mul_card_edgeFinset`

English:
lemma two_mul_card_edgeFinset
  statement: 2 * #G.edgeFinset = #(univ.filter fun (x, y) => G.Adj x y)
  proof: by
  rw [← dart_card_eq_twice_card_edges]; rw [← card_univ]
  refine card_bij' (fun d _ => (d.fst, d.snd)) (fun xy h => ⟨xy, (mem_filter.1 h).2⟩) ?_ ?_ ?_ ?_
    <;> simp

中文:
引理 two_mul_card_edgeFinset
  结论: 2 * #G.edgeFinset = #(univ.filter fun (x, y) => G.伴随 x y)
  证明: by
  rw [← dart_card_eq_twice_card_edges]; rw [← card_univ]
  refine card_bij' (fun d _ => (d.fst, d.snd)) (fun xy h => ⟨xy, (mem_filter.1 h).2⟩) ?_ ?_ ?_ ?_
    <;> simp

Depends on / 依赖: card_bij, card_univ, d.fst, d.snd, dart_card_eq_twice_card_edges, mem_filter
-/
lemma two_mul_card_edgeFinset : 2 * #G.edgeFinset = #(univ.filter fun (x, y) => G.Adj x y) := by
  rw [← dart_card_eq_twice_card_edges]; rw [← card_univ]
  refine card_bij' (fun d _ => (d.fst, d.snd)) (fun xy h => ⟨xy, (mem_filter.1 h).2⟩) ?_ ?_ ?_ ?_
    <;> simp

/--
theorem `sum_degrees_support_eq_twice_card_edges` / 定理 `sum_degrees_support_eq_twice_card_edges`

English:
theorem sum_degrees_support_eq_twice_card_edges
  proof: by
  classical
  simp_rw [← sum_degrees_eq_twice_card_edges,
    ← sum_add_sum_compl G.support.toFinset, left_eq_add]
  apply Finset.sum_eq_zero
  intro v hv
  rw [degree_eq_zero_iff_notMem_support]
  rwa [mem_compl, Set.mem_toFinset] at hv

中文:
定理 sum_degrees_support_eq_twice_card_edges
  证明: by
  classical
  simp_rw [← sum_degrees_eq_twice_card_edges,
    ← sum_add_sum_compl G.support.toFinset, left_eq_add]
  apply Finset.sum_eq_zero
  intro v hv
  rw [degree_eq_zero_iff_notMem_support]
  rwa [mem_compl, Set.mem_toFinset] at hv

Depends on / 依赖: Finset, Finset.sum_eq_zero, G.support.toFinset, Set.mem_toFinset, classical, degree_eq_zero_iff_notMem_support, left_eq_add, mem_compl, mem_toFinset, simp_rw, sum_add_sum_compl, sum_degrees_eq_twice_card_edges, sum_eq_zero, support, toFinset
-/
theorem sum_degrees_support_eq_twice_card_edges :
    ∑ v in G.support, G.degree v = 2 * #G.edgeFinset := by
  classical
  simp_rw [← sum_degrees_eq_twice_card_edges,
    ← sum_add_sum_compl G.support.toFinset, left_eq_add]
  apply Finset.sum_eq_zero
  intro v hv
  rw [degree_eq_zero_iff_notMem_support]
  rwa [mem_compl, Set.mem_toFinset] at hv

end DegreeSum

/--
theorem `even_card_odd_degree_vertices` / 定理 `even_card_odd_degree_vertices`

English:
theorem even_card_odd_degree_vertices
  given: [Fintype V] [DecidableRel G.Adj]
  proof: by
  have h := congr_arg (fun n => ↑n : Nat -> ZMod 2) G.sum_degrees_eq_twice_card_edges
  simp only [ZMod.natCast_self, zero_mul, Nat.cast_mul] at h
  rw [Nat.cast_sum]; rw [← sum_filter_ne_zero] at h
  rw [sum_congr (g := fun _v => (1 : ZMod 2)) rfl] at h
  · simp only [mul_one, nsmul_eq_mul, sum_const, Ne] at h
    rw [← ZMod.natCast_eq_zero_iff_even]
    convert! h
    exact ZMod.natCast_ne_zero_iff_odd.symm
  · intro v
    rw [mem_filter_univ]; rw [Ne]; rw [ZMod.natCast_eq_zero_iff_even]; rw [ZMod.natCast_eq_one_iff_odd]; rw [← Nat.not_even_iff_odd]
    tauto

中文:
定理 even_card_odd_degree_vertices
  条件: [有限类型 V] [DecidableRel G.伴随]
  证明: by
  have h := congr_arg (fun n => ↑n : Nat -> ZMod 2) G.sum_degrees_eq_twice_card_edges
  simp only [ZMod.natCast_self, zero_mul, Nat.cast_mul] at h
  rw [Nat.cast_sum]; rw [← sum_filter_ne_zero] at h
  rw [sum_congr (g := fun _v => (1 : ZMod 2)) rfl] at h
  · simp only [mul_one, nsmul_eq_mul, sum_const, Ne] at h
    rw [← ZMod.natCast_eq_zero_iff_even]
    convert! h
    exact ZMod.natCast_ne_zero_iff_odd.symm
  · intro v
    rw [mem_filter_univ]; rw [Ne]; rw [ZMod.natCast_eq_zero_iff_even]; rw [ZMod.natCast_eq_one_iff_odd]; rw [← Nat.not_even_iff_odd]
    tauto

Depends on / 依赖: G.sum_degrees_eq_twice_card_edges, Nat.cast_mul, Nat.cast_sum, ZMod.natCast_eq_one_iff_o, ZMod.natCast_eq_zero_iff_even, ZMod.natCast_ne_zero_iff_odd.symm, ZMod.natCast_self, cast_mul, cast_sum, congr_arg, convert, mem_filter_univ, mul_one, natCast_eq_one_iff_o, natCast_eq_zero_iff_even, natCast_ne_zero_iff_odd, natCast_self, nsmul_eq_mul, sum_congr, sum_const
-/
theorem even_card_odd_degree_vertices [Fintype V] [DecidableRel G.Adj] :
    Even #{v | Odd (G.degree v)} := by
  have h := congr_arg (fun n => ↑n : Nat -> ZMod 2) G.sum_degrees_eq_twice_card_edges
  simp only [ZMod.natCast_self, zero_mul, Nat.cast_mul] at h
  rw [Nat.cast_sum]; rw [← sum_filter_ne_zero] at h
  rw [sum_congr (g := fun _v => (1 : ZMod 2)) rfl] at h
  · simp only [mul_one, nsmul_eq_mul, sum_const, Ne] at h
    rw [← ZMod.natCast_eq_zero_iff_even]
    convert! h
    exact ZMod.natCast_ne_zero_iff_odd.symm
  · intro v
    rw [mem_filter_univ]; rw [Ne]; rw [ZMod.natCast_eq_zero_iff_even]; rw [ZMod.natCast_eq_one_iff_odd]; rw [← Nat.not_even_iff_odd]
    tauto

/--
theorem `odd_card_odd_degree_vertices_ne` / 定理 `odd_card_odd_degree_vertices_ne`

English:
theorem odd_card_odd_degree_vertices_ne
  statement: [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (v : V)
  proof: by
  rcases G.even_card_odd_degree_vertices with ⟨k, hg⟩
  have hk : 0 < k := by
    have hh : Finset.Nonempty {v : V | Odd (G.degree v)} := by
      use v
      rw [mem_filter_univ]
      exact h
    rwa [← card_pos, hg, ← two_mul, mul_pos_iff_of_pos_left] at hh
    exact zero_lt_two
  have hc : (fun w : V => w != v ∧ Odd (G.degree w)) = fun w : V => Odd (G.degree w) ∧ w != v := by
    ext w
    rw [and_comm]
  simp only [hc]
  rw [← filter_filter]; rw [filter_ne']; rw [card_erase_of_mem]
· refine ⟨k - 1, tsub_eq_of_eq_add hg.trans ?_⟩
    lia
  · rwa [mem_filter_univ]

中文:
定理 odd_card_odd_degree_vertices_ne
  结论: [有限类型 V] [DecidableEq V] [DecidableRel G.伴随] (v : V)
  证明: by
  rcases G.even_card_odd_degree_vertices with ⟨k, hg⟩
  have hk : 0 < k := by
    have hh : Finset.Nonempty {v : V | Odd (G.degree v)} := by
      use v
      rw [mem_filter_univ]
      exact h
    rwa [← card_pos, hg, ← two_mul, mul_pos_iff_of_pos_left] at hh
    exact zero_lt_two
  have hc : (fun w : V => w != v ∧ Odd (G.degree w)) = fun w : V => Odd (G.degree w) ∧ w != v := by
    ext w
    rw [and_comm]
  simp only [hc]
  rw [← filter_filter]; rw [filter_ne']; rw [card_erase_of_mem]
· refine ⟨k - 1, tsub_eq_of_eq_add hg.trans ?_⟩
    lia
  · rwa [mem_filter_univ]

Depends on / 依赖: Finset, Finset.Nonempty, G.degree, G.even_card_odd_degree_vertices, Nonempty, and_comm, card_erase_of_mem, card_pos, degree, even_card_odd_degree_vertices, filter_filter, filter_ne, hg.trans, mem_filter_univ, mul_pos_iff_of_pos_left, tsub_eq_of_eq_add, two_mul, zero_lt_two
-/
theorem odd_card_odd_degree_vertices_ne [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (v : V)
    (h : Odd (G.degree v)) : Odd #{w | w != v ∧ Odd (G.degree w)} := by
  rcases G.even_card_odd_degree_vertices with ⟨k, hg⟩
  have hk : 0 < k := by
    have hh : Finset.Nonempty {v : V | Odd (G.degree v)} := by
      use v
      rw [mem_filter_univ]
      exact h
    rwa [← card_pos, hg, ← two_mul, mul_pos_iff_of_pos_left] at hh
    exact zero_lt_two
  have hc : (fun w : V => w != v ∧ Odd (G.degree w)) = fun w : V => Odd (G.degree w) ∧ w != v := by
    ext w
    rw [and_comm]
  simp only [hc]
  rw [← filter_filter]; rw [filter_ne']; rw [card_erase_of_mem]
· refine ⟨k - 1, tsub_eq_of_eq_add hg.trans ?_⟩
    lia
  · rwa [mem_filter_univ]

/--
theorem `exists_ne_odd_degree_of_exists_odd_degree` / 定理 `exists_ne_odd_degree_of_exists_odd_degree`

English:
theorem exists_ne_odd_degree_of_exists_odd_degree
  statement: [Fintype V] [DecidableRel G.Adj] (v : V)
  proof: by
  have := Classical.decEq V
  rcases G.odd_card_odd_degree_vertices_ne v h with ⟨k, hg⟩
  have hg' : 0 < #{w | w != v ∧ Odd (G.degree w)} := by
    rw [hg]
    apply Nat.succ_pos
  rcases card_pos.mp hg' with ⟨w, hw⟩
  rw [mem_filter_univ] at hw
  exact ⟨w, hw⟩

中文:
定理 存在_ne_odd_degree_of_存在_odd_degree
  结论: [有限类型 V] [DecidableRel G.伴随] (v : V)
  证明: by
  have := Classical.decEq V
  rcases G.odd_card_odd_degree_vertices_ne v h with ⟨k, hg⟩
  have hg' : 0 < #{w | w != v ∧ Odd (G.degree w)} := by
    rw [hg]
    apply Nat.succ_pos
  rcases card_pos.mp hg' with ⟨w, hw⟩
  rw [mem_filter_univ] at hw
  exact ⟨w, hw⟩

Depends on / 依赖: Classical, Classical.decEq, G.degree, G.odd_card_odd_degree_vertices_ne, Nat.succ_pos, card_pos, card_pos.mp, degree, mem_filter_univ, odd_card_odd_degree_vertices_ne, succ_pos
-/
theorem exists_ne_odd_degree_of_exists_odd_degree [Fintype V] [DecidableRel G.Adj] (v : V)
    (h : Odd (G.degree v)) : exists w : V, w != v ∧ Odd (G.degree w) := by
  have := Classical.decEq V
  rcases G.odd_card_odd_degree_vertices_ne v h with ⟨k, hg⟩
  have hg' : 0 < #{w | w != v ∧ Odd (G.degree w)} := by
    rw [hg]
    apply Nat.succ_pos
  rcases card_pos.mp hg' with ⟨w, hw⟩
  rw [mem_filter_univ] at hw
  exact ⟨w, hw⟩

end SimpleGraph
