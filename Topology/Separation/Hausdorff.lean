/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Separation.Basic

/-!
# T₂ and T₂.₅ spaces.

This file defines the T₂ (Hausdorff) condition, which is the most commonly-used among the various
separation axioms, and the related T₂.₅ condition.

## Main definitions

* `T2Space`: A T₂/Hausdorff space is a space where, for every two points `x ≠ y`,
  there is two disjoint open sets, one containing `x`, and the other `y`. T₂ implies T₁ and R₁.
* `T25Space`: A T₂.₅/Urysohn space is a space where, for every two points `x ≠ y`,
  there is two open sets, one containing `x`, and the other `y`, whose closures are disjoint.
  T₂.₅ implies T₂.

See `Mathlib/Topology/Separation/Regular.lean` for regular, T₃, etc. spaces; and
`Mathlib/Topology/Separation/GDelta.lean` for the definitions of `PerfectlyNormalSpace` and
`T6Space`.

Note that `mathlib` adopts the modern convention that `m ≤ n` if and only if `T_m → T_n`, but
occasionally the literature swaps definitions for e.g. T₃ and regular.

## Main results

### T₂ spaces

* `t2_iff_nhds`: A space is T₂ iff the neighbourhoods of distinct points generate the bottom filter.
* `t2_iff_isClosed_diagonal`: A space is T₂ iff the `diagonal` of `X` (that is, the set of all
  points of the form `(a, a) : X × X`) is closed under the product topology.
* `separatedNhds_of_finset_finset`: Any two disjoint finsets are `SeparatedNhds`.
* Most topological constructions preserve Hausdorffness;
  these results are part of the typeclass inference system (e.g. `Topology.IsEmbedding.t2Space`)
* `Set.EqOn.closure`: If two functions are equal on some set `s`, they are equal on its closure.
* `IsCompact.isClosed`: All compact sets are closed.
* `WeaklyLocallyCompactSpace.locallyCompactSpace`: If a topological space is both
  weakly locally compact (i.e., each point has a compact neighbourhood)
  and is T₂, then it is locally compact.
* `totallySeparatedSpace_of_t1_of_basis_clopen`: If `X` has a clopen basis, then
  it is a `TotallySeparatedSpace`.
* `loc_compact_t2_tot_disc_iff_tot_sep`: A locally compact T₂ space is totally disconnected iff
  it is totally separated.
* `T2Quotient`: the largest T2 quotient of a given topological space.

If the space is also compact:

* `normalOfCompactT2`: A compact T₂ space is a `NormalSpace`.
* `connectedComponent_eq_iInter_isClopen`: The connected component of a point
  is the intersection of all its clopen neighbourhoods.
* `compact_t2_tot_disc_iff_tot_sep`: Being a `TotallyDisconnectedSpace`
  is equivalent to being a `TotallySeparatedSpace`.
* `ConnectedComponents.t2`: `ConnectedComponents X` is T₂ for `X` T₂ and compact.

## References

* <https://en.wikipedia.org/wiki/Separation_axiom>
* [Willard's *General Topology*][zbMATH02107988]

-/

@[expose] public section

open Function Set Filter Topology TopologicalSpace

universe u v

variable {X : Type*} {Y : Type*} [TopologicalSpace X]

section Separation

/-- A T₂ space, also known as a Hausdorff space, is one in which for every
  `x ≠ y` there exists disjoint open sets around `x` and `y`. This is
  the most widely used of the separation axioms. -/
@[mk_iff]
/--
Definition of `T2Space` / `T2Space` 的定义

English:
class T2Space
  parameters: (X : Type u) [TopologicalSpace X]
  axioms and operations (1):
    - t2 : Pairwise fun x y => exists u v : Set X, IsOpen u ∧ IsOpen v ∧ x in u ∧ y in v ∧ Disjoint u v

中文:
类 T2空间
  参数: (X : 类型u) [拓扑空间 X]
  公理与运算 (1 个):
    - t2 : 两两 fun x y => 存在 u v : 集合 X, 是开集 u ∧ 是开集 v ∧ x in u ∧ y in v ∧ Disjoint u v
-/
class T2Space (X : Type u) [TopologicalSpace X] : Prop where
  /-- Every two points in a Hausdorff space admit disjoint open neighbourhoods. -/
  t2 : Pairwise fun x y => exists u v : Set X, IsOpen u ∧ IsOpen v ∧ x in u ∧ y in v ∧ Disjoint u v

/--
theorem `t2_separation` / 定理 `t2_separation`

English:
theorem t2_separation
  given: [T2Space X] {x y : X} (h : x != y)
  proof: T2Space.t2 h

中文:
定理 t2_separation
  条件: [T2空间 X] {x y : X} (h : x != y)
  证明: T2Space.t2 h

Depends on / 依赖: T2Space, T2Space.t2
-/
theorem t2_separation [T2Space X] {x y : X} (h : x != y) :
    exists u v : Set X, IsOpen u ∧ IsOpen v ∧ x in u ∧ y in v ∧ Disjoint u v :=
  T2Space.t2 h

-- todo: use this as a definition?
/--
theorem `t2Space_iff_disjoint_nhds` / 定理 `t2Space_iff_disjoint_nhds`

English:
theorem t2Space_iff_disjoint_nhds
  statement: T2Space X ↔ Pairwise fun x y : X => Disjoint (𝓝 x) (𝓝 y)
  proof: by
  refine (t2Space_iff X).trans (forall₃_congr fun x y _ => ?_)
  simp only [(nhds_basis_opens x).disjoint_iff (nhds_basis_opens y), ← exists_and_left,
    and_assoc, and_comm, and_left_comm]

@[simp]

中文:
定理 t2Space_iff_disjoint_nhds
  结论: T2空间 X ↔ 两两 fun x y : X => Disjoint (𝓝 x) (𝓝 y)
  证明: by
  refine (t2Space_iff X).trans (forall₃_congr fun x y _ => ?_)
  simp only [(nhds_basis_opens x).disjoint_iff (nhds_basis_opens y), ← exists_and_left,
    and_assoc, and_comm, and_left_comm]

@[simp]

Depends on / 依赖: and_assoc, and_comm, and_left_comm, disjoint_iff, exists_and_left, nhds_basis_opens, t2Space_iff
-/
theorem t2Space_iff_disjoint_nhds : T2Space X ↔ Pairwise fun x y : X => Disjoint (𝓝 x) (𝓝 y) := by
  refine (t2Space_iff X).trans (forall₃_congr fun x y _ => ?_)
  simp only [(nhds_basis_opens x).disjoint_iff (nhds_basis_opens y), ← exists_and_left,
    and_assoc, and_comm, and_left_comm]

@[simp]
/--
theorem `disjoint_nhds_nhds` / 定理 `disjoint_nhds_nhds`

English:
theorem disjoint_nhds_nhds
  given: [T2Space X] {x y : X}
  statement: Disjoint (𝓝 x) (𝓝 y) ↔ x != y
  proof: ⟨fun hd he => by simp [he, nhds_neBot.ne] at hd, (t2Space_iff_disjoint_nhds.mp ‹_› ·)⟩

中文:
定理 disjoint_nhds_nhds
  条件: [T2空间 X] {x y : X}
  结论: Disjoint (𝓝 x) (𝓝 y) ↔ x != y
  证明: ⟨fun hd he => by simp [he, nhds_neBot.ne] at hd, (t2Space_iff_disjoint_nhds.mp ‹_› ·)⟩

Depends on / 依赖: nhds_neBot, nhds_neBot.ne, t2Space_iff_disjoint_nhds, t2Space_iff_disjoint_nhds.mp
-/
theorem disjoint_nhds_nhds [T2Space X] {x y : X} : Disjoint (𝓝 x) (𝓝 y) ↔ x != y :=
  ⟨fun hd he => by simp [he, nhds_neBot.ne] at hd, (t2Space_iff_disjoint_nhds.mp ‹_› ·)⟩

/--
theorem `pairwise_disjoint_nhds` / 定理 `pairwise_disjoint_nhds`

English:
theorem pairwise_disjoint_nhds
  given: [T2Space X]
  statement: Pairwise (Disjoint on (𝓝 : X -> Filter X))
  proof: fun _ _ =>
  disjoint_nhds_nhds.2

中文:
定理 pairwise_disjoint_nhds
  条件: [T2空间 X]
  结论: 两两 (Disjoint on (𝓝 : X -> 滤子 X))
  证明: fun _ _ =>
  disjoint_nhds_nhds.2
-/
theorem pairwise_disjoint_nhds [T2Space X] : Pairwise (Disjoint on (𝓝 : X -> Filter X)) := fun _ _ =>
  disjoint_nhds_nhds.2

/--
theorem `Set.pairwiseDisjoint_nhds` / 定理 `Set.pairwiseDisjoint_nhds`

English:
theorem Set.pairwiseDisjoint_nhds
  given: [T2Space X] (s : Set X)
  statement: s.PairwiseDisjoint 𝓝
  proof: pairwise_disjoint_nhds.set_pairwise s

中文:
定理 集合.pairwiseDisjoint_nhds
  条件: [T2空间 X] (s : 集合 X)
  结论: s.PairwiseDisjoint 𝓝
  证明: pairwise_disjoint_nhds.set_pairwise s
-/
protected theorem Set.pairwiseDisjoint_nhds [T2Space X] (s : Set X) : s.PairwiseDisjoint 𝓝 :=
  pairwise_disjoint_nhds.set_pairwise s

/--
theorem `Set.Finite.t2_separation` / 定理 `Set.Finite.t2_separation`

English:
theorem Set.Finite.t2_separation
  given: [T2Space X] {s : Set X} (hs : s.Finite)
  proof: s.pairwiseDisjoint_nhds.exists_mem_filter_basis hs nhds_basis_opens

中文:
定理 集合.有限.t2_separation
  条件: [T2空间 X] {s : 集合 X} (hs : s.有限)
  证明: s.pairwiseDisjoint_nhds.exists_mem_filter_basis hs nhds_basis_opens

Depends on / 依赖: exists_mem_filter_basis, nhds_basis_opens, pairwiseDisjoint_nhds, s.pairwiseDisjoint_nhds.exists_mem_filter_basis
-/
theorem Set.Finite.t2_separation [T2Space X] {s : Set X} (hs : s.Finite) :
    exists U : X -> Set X, (forall x, x in U x ∧ IsOpen (U x)) ∧ s.PairwiseDisjoint U :=
  s.pairwiseDisjoint_nhds.exists_mem_filter_basis hs nhds_basis_opens

-- see Note [lower instance priority]
instance (priority := 100) T2Space.t1Space [T2Space X] : T1Space X :=
  t1Space_iff_disjoint_pure_nhds.mpr fun _ _ hne =>
(disjoint_nhds_nhds.2 hne).mono_left pure_le_nhds _

-- see Note [lower instance priority]
instance (priority := 100) T2Space.r1Space [T2Space X] : R1Space X :=
  ⟨fun x y => (eq_or_ne x y).imp specializes_of_eq disjoint_nhds_nhds.2⟩

/--
theorem `SeparationQuotient.t2Space_iff` / 定理 `SeparationQuotient.t2Space_iff`

English:
theorem SeparationQuotient.t2Space_iff
  statement: T2Space (SeparationQuotient X) ↔ R1Space X
  proof: by
  simp only [t2Space_iff_disjoint_nhds, Pairwise, surjective_mk.forall₂, ne_eq, mk_eq_mk,
    r1Space_iff_inseparable_or_disjoint_nhds, ← disjoint_comap_iff surjective_mk, comap_mk_nhds_mk,
    ← or_iff_not_imp_left]

中文:
定理 SeparationQuotient.t2Space_iff
  结论: T2空间 (SeparationQuotient X) ↔ R1空间 X
  证明: by
  simp only [t2Space_iff_disjoint_nhds, Pairwise, surjective_mk.forall₂, ne_eq, mk_eq_mk,
    r1Space_iff_inseparable_or_disjoint_nhds, ← disjoint_comap_iff surjective_mk, comap_mk_nhds_mk,
    ← or_iff_not_imp_left]

Depends on / 依赖: Pairwise, comap_mk_nhds_mk, disjoint_comap_iff, mk_eq_mk, ne_eq, or_iff_not_imp_left, r1Space_iff_inseparable_or_disjoint_nhds, surjective_mk, surjective_mk.forall, t2Space_iff_disjoint_nhds
-/
theorem SeparationQuotient.t2Space_iff : T2Space (SeparationQuotient X) ↔ R1Space X := by
  simp only [t2Space_iff_disjoint_nhds, Pairwise, surjective_mk.forall₂, ne_eq, mk_eq_mk,
    r1Space_iff_inseparable_or_disjoint_nhds, ← disjoint_comap_iff surjective_mk, comap_mk_nhds_mk,
    ← or_iff_not_imp_left]

/--
Instance `SeparationQuotient.t2Space` / 实例 `SeparationQuotient.t2Space`

English:
instance SeparationQuotient.t2Space
  signature: [R1Space X]
  body: t2Space_iff.2 ‹_›

中文:
实例 SeparationQuotient.t2Space
  签名: [R1空间 X]
  定义体: t2Space_iff.2 ‹_›

Depends on / 依赖: t2Space_iff
-/
instance SeparationQuotient.t2Space [R1Space X] : T2Space (SeparationQuotient X) :=
  t2Space_iff.2 ‹_›

instance (priority := 80) [R1Space X] [T0Space X] : T2Space X :=
  t2Space_iff_disjoint_nhds.2 fun _x _y hne => disjoint_nhds_nhds_iff_not_inseparable.2 fun hxy =>
    hne hxy.eq

/--
theorem `R1Space.t2Space_iff_t0Space` / 定理 `R1Space.t2Space_iff_t0Space`

English:
theorem R1Space.t2Space_iff_t0Space
  given: [R1Space X]
  statement: T2Space X ↔ T0Space X
  proof: by
  constructor <;> intro <;> infer_instance

中文:
定理 R1空间.t2Space_iff_t0Space
  条件: [R1空间 X]
  结论: T2空间 X ↔ T0空间 X
  证明: by
  constructor <;> intro <;> infer_instance

Depends on / 依赖: infer_instance
-/
theorem R1Space.t2Space_iff_t0Space [R1Space X] : T2Space X ↔ T0Space X := by
  constructor <;> intro <;> infer_instance

/--
theorem `t2_iff_nhds` / 定理 `t2_iff_nhds`

English:
theorem t2_iff_nhds
  statement: T2Space X ↔ forall {x y : X}, NeBot (𝓝 x ⊓ 𝓝 y) -> x = y
  proof: by
  simp only [t2Space_iff_disjoint_nhds, disjoint_iff, neBot_iff, Ne, not_imp_comm, Pairwise]

中文:
定理 t2_iff_nhds
  结论: T2空间 X ↔ 对任意 {x y : X}, NeBot (𝓝 x ⊓ 𝓝 y) -> x = y
  证明: by
  simp only [t2Space_iff_disjoint_nhds, disjoint_iff, neBot_iff, Ne, not_imp_comm, Pairwise]

Depends on / 依赖: Pairwise, disjoint_iff, neBot_iff, not_imp_comm, t2Space_iff_disjoint_nhds
-/
theorem t2_iff_nhds : T2Space X ↔ forall {x y : X}, NeBot (𝓝 x ⊓ 𝓝 y) -> x = y := by
  simp only [t2Space_iff_disjoint_nhds, disjoint_iff, neBot_iff, Ne, not_imp_comm, Pairwise]

/--
theorem `eq_of_nhds_neBot` / 定理 `eq_of_nhds_neBot`

English:
theorem eq_of_nhds_neBot
  given: [T2Space X] {x y : X} (h : NeBot (𝓝 x ⊓ 𝓝 y))
  statement: x = y
  proof: t2_iff_nhds.mp ‹_› h

中文:
定理 eq_of_nhds_neBot
  条件: [T2空间 X] {x y : X} (h : NeBot (𝓝 x ⊓ 𝓝 y))
  结论: x = y
  证明: t2_iff_nhds.mp ‹_› h

Depends on / 依赖: t2_iff_nhds, t2_iff_nhds.mp
-/
theorem eq_of_nhds_neBot [T2Space X] {x y : X} (h : NeBot (𝓝 x ⊓ 𝓝 y)) : x = y :=
  t2_iff_nhds.mp ‹_› h

/--
theorem `t2Space_iff_nhds` / 定理 `t2Space_iff_nhds`

English:
theorem t2Space_iff_nhds
  proof: by
  simp only [t2Space_iff_disjoint_nhds, Filter.disjoint_iff, Pairwise]

中文:
定理 t2Space_iff_nhds
  证明: by
  simp only [t2Space_iff_disjoint_nhds, Filter.disjoint_iff, Pairwise]

Depends on / 依赖: Filter, Filter.disjoint_iff, Pairwise, disjoint_iff, t2Space_iff_disjoint_nhds
-/
theorem t2Space_iff_nhds :
    T2Space X ↔ Pairwise fun x y : X => exists U in 𝓝 x, exists V in 𝓝 y, Disjoint U V := by
  simp only [t2Space_iff_disjoint_nhds, Filter.disjoint_iff, Pairwise]

/--
theorem `t2_separation_nhds` / 定理 `t2_separation_nhds`

English:
theorem t2_separation_nhds
  given: [T2Space X] {x y : X} (h : x != y)
  proof: let ⟨u, v, open_u, open_v, x_in, y_in, huv⟩ := t2_separation h
  ⟨u, v, open_u.mem_nhds x_in, open_v.mem_nhds y_in, huv⟩

中文:
定理 t2_separation_nhds
  条件: [T2空间 X] {x y : X} (h : x != y)
  证明: let ⟨u, v, open_u, open_v, x_in, y_in, huv⟩ := t2_separation h
  ⟨u, v, open_u.mem_nhds x_in, open_v.mem_nhds y_in, huv⟩

Depends on / 依赖: mem_nhds, open_u, open_u.mem_nhds, open_v, open_v.mem_nhds, t2_separation, x_in, y_in
-/
theorem t2_separation_nhds [T2Space X] {x y : X} (h : x != y) :
    exists u v, u in 𝓝 x ∧ v in 𝓝 y ∧ Disjoint u v :=
  let ⟨u, v, open_u, open_v, x_in, y_in, huv⟩ := t2_separation h
  ⟨u, v, open_u.mem_nhds x_in, open_v.mem_nhds y_in, huv⟩

/--
theorem `t2_separation_compact_nhds` / 定理 `t2_separation_compact_nhds`

English:
theorem t2_separation_compact_nhds
  given: [LocallyCompactSpace X] [T2Space X] {x y : X} (h : x != y)
  proof: by
  simpa only [exists_prop, ← exists_and_left, and_comm, and_assoc, and_left_comm] using
    ((compact_basis_nhds x).disjoint_iff (compact_basis_nhds y)).1 (disjoint_nhds_nhds.2 h)

中文:
定理 t2_separation_compact_nhds
  条件: [局部紧空间 X] [T2空间 X] {x y : X} (h : x != y)
  证明: by
  simpa only [exists_prop, ← exists_and_left, and_comm, and_assoc, and_left_comm] using
    ((compact_basis_nhds x).disjoint_iff (compact_basis_nhds y)).1 (disjoint_nhds_nhds.2 h)

Depends on / 依赖: and_assoc, and_comm, and_left_comm, compact_basis_nhds, disjoint_iff, disjoint_nhds_nhds, exists_and_left, exists_prop
-/
theorem t2_separation_compact_nhds [LocallyCompactSpace X] [T2Space X] {x y : X} (h : x != y) :
    exists u v, u in 𝓝 x ∧ v in 𝓝 y ∧ IsCompact u ∧ IsCompact v ∧ Disjoint u v := by
  simpa only [exists_prop, ← exists_and_left, and_comm, and_assoc, and_left_comm] using
    ((compact_basis_nhds x).disjoint_iff (compact_basis_nhds y)).1 (disjoint_nhds_nhds.2 h)

/--
theorem `t2_iff_ultrafilter` / 定理 `t2_iff_ultrafilter`

English:
theorem t2_iff_ultrafilter
  proof: t2_iff_nhds.trans by simp only [← exists_ultrafilter_iff, and_imp, le_inf_iff, exists_imp]

中文:
定理 t2_iff_ultrafilter
  证明: t2_iff_nhds.trans by simp only [← exists_ultrafilter_iff, and_imp, le_inf_iff, exists_imp]

Depends on / 依赖: and_imp, exists_imp, exists_ultrafilter_iff, le_inf_iff, t2_iff_nhds, t2_iff_nhds.trans
-/
theorem t2_iff_ultrafilter :
    T2Space X ↔ forall {x y : X} (f : Ultrafilter X), ↑f <= 𝓝 x -> ↑f <= 𝓝 y -> x = y :=
t2_iff_nhds.trans by simp only [← exists_ultrafilter_iff, and_imp, le_inf_iff, exists_imp]

/--
theorem `t2_iff_isClosed_diagonal` / 定理 `t2_iff_isClosed_diagonal`

English:
theorem t2_iff_isClosed_diagonal
  statement: T2Space X ↔ IsClosed (diagonal X)
  proof: by
  simp only [t2Space_iff_disjoint_nhds, ← isOpen_compl_iff, isOpen_iff_mem_nhds, Prod.forall,
    nhds_prod_eq, compl_diagonal_mem_prod, mem_compl_iff, mem_diagonal_iff, Pairwise]

@[closedness ., grind .]

中文:
定理 t2_iff_isClosed_diagonal
  结论: T2空间 X ↔ 是闭集 (diagonal X)
  证明: by
  simp only [t2Space_iff_disjoint_nhds, ← isOpen_compl_iff, isOpen_iff_mem_nhds, Prod.forall,
    nhds_prod_eq, compl_diagonal_mem_prod, mem_compl_iff, mem_diagonal_iff, Pairwise]

@[closedness ., grind .]

Depends on / 依赖: Pairwise, Prod.forall, compl_diagonal_mem_prod, isOpen_compl_iff, isOpen_iff_mem_nhds, mem_compl_iff, mem_diagonal_iff, nhds_prod_eq, t2Space_iff_disjoint_nhds
-/
theorem t2_iff_isClosed_diagonal : T2Space X ↔ IsClosed (diagonal X) := by
  simp only [t2Space_iff_disjoint_nhds, ← isOpen_compl_iff, isOpen_iff_mem_nhds, Prod.forall,
    nhds_prod_eq, compl_diagonal_mem_prod, mem_compl_iff, mem_diagonal_iff, Pairwise]

@[closedness ., grind .]
/--
theorem `isClosed_diagonal` / 定理 `isClosed_diagonal`

English:
theorem isClosed_diagonal
  given: [T2Space X]
  statement: IsClosed (diagonal X)
  proof: t2_iff_isClosed_diagonal.mp ‹_›

中文:
定理 isClosed_diagonal
  条件: [T2空间 X]
  结论: 是闭集 (diagonal X)
  证明: t2_iff_isClosed_diagonal.mp ‹_›

Depends on / 依赖: t2_iff_isClosed_diagonal, t2_iff_isClosed_diagonal.mp
-/
theorem isClosed_diagonal [T2Space X] : IsClosed (diagonal X) :=
  t2_iff_isClosed_diagonal.mp ‹_›

/--
theorem `t2Space_iff_of_isOpenQuotientMap` / 定理 `t2Space_iff_of_isOpenQuotientMap`

English:
theorem t2Space_iff_of_isOpenQuotientMap
  statement: [TopologicalSpace Y] {π : X -> Y}
  proof: by
  rw [t2_iff_isClosed_diagonal]
  replace h := IsOpenQuotientMap.prodMap h h
  refine ⟨fun H => H.preimage h.continuous, fun H => ?_⟩
  simp_rw [← isOpen_compl_iff] at H ⊢
  convert! h.isOpenMap _ H
  exact (h.surjective.image_preimage _).symm

中文:
定理 t2Space_iff_of_isOpenQuotientMap
  结论: [拓扑空间 Y] {π : X -> Y}
  证明: by
  rw [t2_iff_isClosed_diagonal]
  replace h := IsOpenQuotientMap.prodMap h h
  refine ⟨fun H => H.preimage h.continuous, fun H => ?_⟩
  simp_rw [← isOpen_compl_iff] at H ⊢
  convert! h.isOpenMap _ H
  exact (h.surjective.image_preimage _).symm

Depends on / 依赖: H.preimage, IsOpenQuotientMap, IsOpenQuotientMap.prodMap, continuous, convert, h.continuous, h.isOpenMap, h.surjective.image_preimage, image_preimage, isOpenMap, isOpen_compl_iff, preimage, prodMap, replace, simp_rw, surjective, t2_iff_isClosed_diagonal
-/
theorem t2Space_iff_of_isOpenQuotientMap [TopologicalSpace Y] {π : X -> Y}
    (h : IsOpenQuotientMap π) : T2Space Y ↔ IsClosed {q : X × X | π q.1 = π q.2} := by
  rw [t2_iff_isClosed_diagonal]
  replace h := IsOpenQuotientMap.prodMap h h
  refine ⟨fun H => H.preimage h.continuous, fun H => ?_⟩
  simp_rw [← isOpen_compl_iff] at H ⊢
  convert! h.isOpenMap _ H
  exact (h.surjective.image_preimage _).symm

/--
theorem `tendsto_nhds_unique` / 定理 `tendsto_nhds_unique`

English:
theorem tendsto_nhds_unique
  statement: [T2Space X] {f : Y -> X} {l : Filter Y} {a b : X} [NeBot l]
  proof: (tendsto_nhds_unique_inseparable ha hb).eq

中文:
定理 tendsto_nhds_unique
  结论: [T2空间 X] {f : Y -> X} {l : 滤子 Y} {a b : X} [NeBot l]
  证明: (tendsto_nhds_unique_inseparable ha hb).eq

Depends on / 依赖: tendsto_nhds_unique_inseparable
-/
theorem tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : Filter Y} {a b : X} [NeBot l]
    (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) : a = b :=
  (tendsto_nhds_unique_inseparable ha hb).eq

/--
theorem `tendsto_nhds_unique'` / 定理 `tendsto_nhds_unique'`

English:
theorem tendsto_nhds_unique'
  statement: [T2Space X] {f : Y -> X} {l : Filter Y} {a b : X} (_ : NeBot l)
  proof: tendsto_nhds_unique ha hb

中文:
定理 tendsto_nhds_unique'
  结论: [T2空间 X] {f : Y -> X} {l : 滤子 Y} {a b : X} (_ : NeBot l)
  证明: tendsto_nhds_unique ha hb

Depends on / 依赖: tendsto_nhds_unique
-/
theorem tendsto_nhds_unique' [T2Space X] {f : Y -> X} {l : Filter Y} {a b : X} (_ : NeBot l)
    (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) : a = b :=
  tendsto_nhds_unique ha hb

/--
theorem `tendsto_nhds_unique_of_eventuallyEq` / 定理 `tendsto_nhds_unique_of_eventuallyEq`

English:
theorem tendsto_nhds_unique_of_eventuallyEq
  statement: [T2Space X] {f g : Y -> X} {l : Filter Y} {a b : X}
  proof: tendsto_nhds_unique (ha.congr' hfg) hb

中文:
定理 tendsto_nhds_unique_of_eventuallyEq
  结论: [T2空间 X] {f g : Y -> X} {l : 滤子 Y} {a b : X}
  证明: tendsto_nhds_unique (ha.congr' hfg) hb

Depends on / 依赖: ha.congr, tendsto_nhds_unique
-/
theorem tendsto_nhds_unique_of_eventuallyEq [T2Space X] {f g : Y -> X} {l : Filter Y} {a b : X}
    [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto g l (𝓝 b)) (hfg : f =ᶠ[l] g) : a = b :=
  tendsto_nhds_unique (ha.congr' hfg) hb

/--
theorem `tendsto_nhds_unique_of_frequently_eq` / 定理 `tendsto_nhds_unique_of_frequently_eq`

English:
theorem tendsto_nhds_unique_of_frequently_eq
  statement: [T2Space X] {f g : Y -> X} {l : Filter Y} {a b : X}
  proof: have : existsᶠ z : X × X in 𝓝 (a, b), z.1 = z.2 := (ha.prodMk_nhds hb).frequently hfg
  not_not.1 fun hne => this (isClosed_diagonal.isOpen_compl.mem_nhds hne)

中文:
定理 tendsto_nhds_unique_of_frequently_eq
  结论: [T2空间 X] {f g : Y -> X} {l : 滤子 Y} {a b : X}
  证明: have : existsᶠ z : X × X in 𝓝 (a, b), z.1 = z.2 := (ha.prodMk_nhds hb).frequently hfg
  not_not.1 fun hne => this (isClosed_diagonal.isOpen_compl.mem_nhds hne)

Depends on / 依赖: frequently, ha.prodMk_nhds, isClosed_diagonal, isClosed_diagonal.isOpen_compl.mem_nhds, isOpen_compl, mem_nhds, not_not, prodMk_nhds
-/
theorem tendsto_nhds_unique_of_frequently_eq [T2Space X] {f g : Y -> X} {l : Filter Y} {a b : X}
    (ha : Tendsto f l (𝓝 a)) (hb : Tendsto g l (𝓝 b)) (hfg : existsᶠ x in l, f x = g x) : a = b :=
  have : existsᶠ z : X × X in 𝓝 (a, b), z.1 = z.2 := (ha.prodMk_nhds hb).frequently hfg
  not_not.1 fun hne => this (isClosed_diagonal.isOpen_compl.mem_nhds hne)

/--
theorem `IsCompact.nhdsSet_inter_eq` / 定理 `IsCompact.nhdsSet_inter_eq`

English:
theorem IsCompact.nhdsSet_inter_eq
  given: [T2Space X] {s t : Set X} (hs : IsCompact s) (ht : IsCompact t)
  proof: by
  refine le_antisymm (nhdsSet_inter_le _ _) ?_
  simp_rw [hs.nhdsSet_inf_eq_biSup, ht.inf_nhdsSet_eq_biSup, nhdsSet, sSup_image]
  refine iSup₂_le fun x hxs => iSup₂_le fun y hyt => ?_
  rcases eq_or_ne x y with (rfl | hne)
  · exact le_iSup₂_of_le x ⟨hxs, hyt⟩ (inf_idem _).le
  · exact (disjoint_nhds_nhds.mpr hne).eq_bot ▸ bot_le

中文:
定理 是紧集.nhdsSet_inter_eq
  条件: [T2空间 X] {s t : 集合 X} (hs : 是紧集 s) (ht : 是紧集 t)
  证明: by
  refine le_antisymm (nhdsSet_inter_le _ _) ?_
  simp_rw [hs.nhdsSet_inf_eq_biSup, ht.inf_nhdsSet_eq_biSup, nhdsSet, sSup_image]
  refine iSup₂_le fun x hxs => iSup₂_le fun y hyt => ?_
  rcases eq_or_ne x y with (rfl | hne)
  · exact le_iSup₂_of_le x ⟨hxs, hyt⟩ (inf_idem _).le
  · exact (disjoint_nhds_nhds.mpr hne).eq_bot ▸ bot_le

Depends on / 依赖: bot_le, disjoint_nhds_nhds, disjoint_nhds_nhds.mpr, eq_bot, eq_or_ne, hs.nhdsSet_inf_eq_biSup, ht.inf_nhdsSet_eq_biSup, inf_idem, inf_nhdsSet_eq_biSup, le_antisymm, nhdsSet, nhdsSet_inf_eq_biSup, nhdsSet_inter_le, sSup_image, simp_rw
-/
theorem IsCompact.nhdsSet_inter_eq [T2Space X] {s t : Set X} (hs : IsCompact s) (ht : IsCompact t) :
    𝓝ˢ (s inter t) = 𝓝ˢ s ⊓ 𝓝ˢ t := by
  refine le_antisymm (nhdsSet_inter_le _ _) ?_
  simp_rw [hs.nhdsSet_inf_eq_biSup, ht.inf_nhdsSet_eq_biSup, nhdsSet, sSup_image]
  refine iSup₂_le fun x hxs => iSup₂_le fun y hyt => ?_
  rcases eq_or_ne x y with (rfl | hne)
  · exact le_iSup₂_of_le x ⟨hxs, hyt⟩ (inf_idem _).le
  · exact (disjoint_nhds_nhds.mpr hne).eq_bot ▸ bot_le

/--
lemma `IsCompact.separation_of_notMem` / 引理 `IsCompact.separation_of_notMem`

English:
lemma IsCompact.separation_of_notMem
  statement: {X : Type u_1} [TopologicalSpace X] [T2Space X] {x : X}
  proof: by
  simpa [SeparatedNhds] using SeparatedNhds.of_isCompact_isCompact_isClosed H1 isCompact_singleton
isClosed_singleton disjoint_singleton_right.mpr H2

中文:
引理 是紧集.separation_of_notMem
  结论: {X : 类型u_1} [拓扑空间 X] [T2空间 X] {x : X}
  证明: by
  simpa [SeparatedNhds] using SeparatedNhds.of_isCompact_isCompact_isClosed H1 isCompact_singleton
isClosed_singleton disjoint_singleton_right.mpr H2

Depends on / 依赖: SeparatedNhds, SeparatedNhds.of_isCompact_isCompact_isClosed, disjoint_singleton_right, disjoint_singleton_right.mpr, isClosed_singleton, isCompact_singleton, of_isCompact_isCompact_isClosed
-/
lemma IsCompact.separation_of_notMem {X : Type u_1} [TopologicalSpace X] [T2Space X] {x : X}
    {t : Set X} (H1 : IsCompact t) (H2 : x ∉ t) :
    exists (U : Set X), exists (V : Set X), IsOpen U ∧ IsOpen V ∧ t subseteq U ∧ x in V ∧ Disjoint U V := by
  simpa [SeparatedNhds] using SeparatedNhds.of_isCompact_isCompact_isClosed H1 isCompact_singleton
isClosed_singleton disjoint_singleton_right.mpr H2

/--
lemma `IsCompact.disjoint_nhdsSet_nhds` / 引理 `IsCompact.disjoint_nhdsSet_nhds`

English:
lemma IsCompact.disjoint_nhdsSet_nhds
  statement: {X : Type u_1} [TopologicalSpace X] [T2Space X] {x : X}
  proof: by
simpa using SeparatedNhds.disjoint_nhdsSet .of_isCompact_isCompact_isClosed H1
isCompact_singleton isClosed_singleton disjoint_singleton_right.mpr H2

中文:
引理 是紧集.disjoint_nhdsSet_nhds
  结论: {X : 类型u_1} [拓扑空间 X] [T2空间 X] {x : X}
  证明: by
simpa using SeparatedNhds.disjoint_nhdsSet .of_isCompact_isCompact_isClosed H1
isCompact_singleton isClosed_singleton disjoint_singleton_right.mpr H2

Depends on / 依赖: SeparatedNhds, SeparatedNhds.disjoint_nhdsSet, disjoint_nhdsSet, disjoint_singleton_right, disjoint_singleton_right.mpr, isClosed_singleton, isCompact_singleton, of_isCompact_isCompact_isClosed
-/
lemma IsCompact.disjoint_nhdsSet_nhds {X : Type u_1} [TopologicalSpace X] [T2Space X] {x : X}
    {t : Set X} (H1 : IsCompact t) (H2 : x ∉ t) :
    Disjoint (𝓝ˢ t) (𝓝 x) := by
simpa using SeparatedNhds.disjoint_nhdsSet .of_isCompact_isCompact_isClosed H1
isCompact_singleton isClosed_singleton disjoint_singleton_right.mpr H2

/--
theorem `Set.InjOn.exists_mem_nhdsSet` / 定理 `Set.InjOn.exists_mem_nhdsSet`

English:
theorem Set.InjOn.exists_mem_nhdsSet
  statement: {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  proof: by
  have : forall x in s ×ˢ s, forallᶠ y in 𝓝 x, f y.1 = f y.2 -> y.1 = y.2 := fun (x, y) ⟨hx, hy⟩ => by
    rcases eq_or_ne x y with rfl | hne
    · rcases loc x hx with ⟨u, hu, hf⟩
exact Filter.mem_of_superset (prod_mem_nhds hu hu) forall_prod_set.2 hf
    · suffices forallᶠ z in 𝓝 (x, y), f z.1 != f z.2 from this.mono fun _ hne h => absurd h hne
refine (fc x hx).prodMap' (fc y hy) isClosed_diagonal.isOpen_compl.mem_nhds ?_
      exact inj.ne hx hy hne
  rw [← eventually_nhdsSet_iff_forall]; rw [sc.nhdsSet_prod_eq sc] at this
  exact eventually_prod_self_iff.1 this

中文:
定理 集合.单射限制.存在_mem_nhdsSet
  结论: {X Y : 类型} [拓扑空间 X] [拓扑空间 Y]
  证明: by
  have : forall x in s ×ˢ s, forallᶠ y in 𝓝 x, f y.1 = f y.2 -> y.1 = y.2 := fun (x, y) ⟨hx, hy⟩ => by
    rcases eq_or_ne x y with rfl | hne
    · rcases loc x hx with ⟨u, hu, hf⟩
exact Filter.mem_of_superset (prod_mem_nhds hu hu) forall_prod_set.2 hf
    · suffices forallᶠ z in 𝓝 (x, y), f z.1 != f z.2 from this.mono fun _ hne h => absurd h hne
refine (fc x hx).prodMap' (fc y hy) isClosed_diagonal.isOpen_compl.mem_nhds ?_
      exact inj.ne hx hy hne
  rw [← eventually_nhdsSet_iff_forall]; rw [sc.nhdsSet_prod_eq sc] at this
  exact eventually_prod_self_iff.1 this

Depends on / 依赖: Filter, Filter.mem_of_superset, absurd, eq_or_ne, eventually_nhdsSet_iff_forall, forall_prod_set, inj.ne, isClosed_diagonal, isClosed_diagonal.isOpen_compl.mem_nhds, isOpen_compl, mem_nhds, mem_of_superset, nhdsSet_prod_eq, prodMap, prod_mem_nhds, sc.nhdsSet_prod_eq, this.mono
-/
theorem Set.InjOn.exists_mem_nhdsSet {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] {f : X -> Y} {s : Set X} (inj : InjOn f s) (sc : IsCompact s)
    (fc : forall x in s, ContinuousAt f x) (loc : forall x in s, exists u in 𝓝 x, InjOn f u) :
    exists t in 𝓝ˢ s, InjOn f t := by
  have : forall x in s ×ˢ s, forallᶠ y in 𝓝 x, f y.1 = f y.2 -> y.1 = y.2 := fun (x, y) ⟨hx, hy⟩ => by
    rcases eq_or_ne x y with rfl | hne
    · rcases loc x hx with ⟨u, hu, hf⟩
exact Filter.mem_of_superset (prod_mem_nhds hu hu) forall_prod_set.2 hf
    · suffices forallᶠ z in 𝓝 (x, y), f z.1 != f z.2 from this.mono fun _ hne h => absurd h hne
refine (fc x hx).prodMap' (fc y hy) isClosed_diagonal.isOpen_compl.mem_nhds ?_
      exact inj.ne hx hy hne
  rw [← eventually_nhdsSet_iff_forall]; rw [sc.nhdsSet_prod_eq sc] at this
  exact eventually_prod_self_iff.1 this

/--
theorem `Set.InjOn.exists_isOpen_superset` / 定理 `Set.InjOn.exists_isOpen_superset`

English:
theorem Set.InjOn.exists_isOpen_superset
  statement: {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  proof: let ⟨_t, hst, ht⟩ := inj.exists_mem_nhdsSet sc fc loc
  let ⟨u, huo, hsu, hut⟩ := mem_nhdsSet_iff_exists.1 hst
  ⟨u, huo, hsu, ht.mono hut⟩

中文:
定理 集合.单射限制.存在_isOpen_superset
  结论: {X Y : 类型} [拓扑空间 X] [拓扑空间 Y]
  证明: let ⟨_t, hst, ht⟩ := inj.exists_mem_nhdsSet sc fc loc
  let ⟨u, huo, hsu, hut⟩ := mem_nhdsSet_iff_exists.1 hst
  ⟨u, huo, hsu, ht.mono hut⟩

Depends on / 依赖: exists_mem_nhdsSet, ht.mono, inj.exists_mem_nhdsSet, mem_nhdsSet_iff_exists
-/
theorem Set.InjOn.exists_isOpen_superset {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] {f : X -> Y} {s : Set X} (inj : InjOn f s) (sc : IsCompact s)
    (fc : forall x in s, ContinuousAt f x) (loc : forall x in s, exists u in 𝓝 x, InjOn f u) :
    exists t, IsOpen t ∧ s subseteq t ∧ InjOn f t :=
  let ⟨_t, hst, ht⟩ := inj.exists_mem_nhdsSet sc fc loc
  let ⟨u, huo, hsu, hut⟩ := mem_nhdsSet_iff_exists.1 hst
  ⟨u, huo, hsu, ht.mono hut⟩

section limUnder

variable [T2Space X] {f : Filter X}



/--
theorem `lim_eq` / 定理 `lim_eq`

English:
theorem lim_eq
  given: {x : X} [NeBot f] (h : f <= 𝓝 x)
  statement: @lim _ _ ⟨x⟩ f = x
  proof: tendsto_nhds_unique (le_nhds_lim ⟨x, h⟩) h

中文:
定理 lim_eq
  条件: {x : X} [NeBot f] (h : f <= 𝓝 x)
  结论: @lim _ _ ⟨x⟩ f = x
  证明: tendsto_nhds_unique (le_nhds_lim ⟨x, h⟩) h

Depends on / 依赖: le_nhds_lim, tendsto_nhds_unique
-/
theorem lim_eq {x : X} [NeBot f] (h : f <= 𝓝 x) : @lim _ _ ⟨x⟩ f = x :=
  tendsto_nhds_unique (le_nhds_lim ⟨x, h⟩) h

/--
theorem `lim_eq_iff` / 定理 `lim_eq_iff`

English:
theorem lim_eq_iff
  given: [NeBot f] (h : exists x : X, f <= 𝓝 x) {x}
  statement: @lim _ _ ⟨x⟩ f = x ↔ f <= 𝓝 x
  proof: ⟨fun c => c ▸ le_nhds_lim h, lim_eq⟩

中文:
定理 lim_eq_iff
  条件: [NeBot f] (h : 存在 x : X, f <= 𝓝 x) {x}
  结论: @lim _ _ ⟨x⟩ f = x ↔ f <= 𝓝 x
  证明: ⟨fun c => c ▸ le_nhds_lim h, lim_eq⟩

Depends on / 依赖: le_nhds_lim, lim_eq
-/
theorem lim_eq_iff [NeBot f] (h : exists x : X, f <= 𝓝 x) {x} : @lim _ _ ⟨x⟩ f = x ↔ f <= 𝓝 x :=
  ⟨fun c => c ▸ le_nhds_lim h, lim_eq⟩

/--
theorem `Ultrafilter.lim_eq_iff_le_nhds` / 定理 `Ultrafilter.lim_eq_iff_le_nhds`

English:
theorem Ultrafilter.lim_eq_iff_le_nhds
  given: [CompactSpace X] {x : X} {F : Ultrafilter X}
  proof: ⟨fun h => h ▸ F.le_nhds_lim, lim_eq⟩

中文:
定理 Ultrafilter.lim_eq_iff_le_nhds
  条件: [紧空间 X] {x : X} {F : Ultrafilter X}
  证明: ⟨fun h => h ▸ F.le_nhds_lim, lim_eq⟩

Depends on / 依赖: F.le_nhds_lim, le_nhds_lim, lim_eq
-/
theorem Ultrafilter.lim_eq_iff_le_nhds [CompactSpace X] {x : X} {F : Ultrafilter X} :
    F.lim = x ↔ ↑F <= 𝓝 x :=
  ⟨fun h => h ▸ F.le_nhds_lim, lim_eq⟩

/--
theorem `isOpen_iff_ultrafilter'` / 定理 `isOpen_iff_ultrafilter'`

English:
theorem isOpen_iff_ultrafilter'
  given: [CompactSpace X] (U : Set X)
  proof: by
  rw [isOpen_iff_ultrafilter]
  refine ⟨fun h F hF => h F.lim hF F F.le_nhds_lim, ?_⟩
  intro cond x hx f h
  rw [← Ultrafilter.lim_eq_iff_le_nhds.2 h] at hx
  exact cond _ hx

中文:
定理 isOpen_iff_ultrafilter'
  条件: [紧空间 X] (U : 集合 X)
  证明: by
  rw [isOpen_iff_ultrafilter]
  refine ⟨fun h F hF => h F.lim hF F F.le_nhds_lim, ?_⟩
  intro cond x hx f h
  rw [← Ultrafilter.lim_eq_iff_le_nhds.2 h] at hx
  exact cond _ hx

Depends on / 依赖: F.le_nhds_lim, F.lim, Ultrafilter, Ultrafilter.lim_eq_iff_le_nhds, isOpen_iff_ultrafilter, le_nhds_lim, lim_eq_iff_le_nhds
-/
theorem isOpen_iff_ultrafilter' [CompactSpace X] (U : Set X) :
    IsOpen U ↔ forall F : Ultrafilter X, F.lim in U -> U in F.1 := by
  rw [isOpen_iff_ultrafilter]
  refine ⟨fun h F hF => h F.lim hF F F.le_nhds_lim, ?_⟩
  intro cond x hx f h
  rw [← Ultrafilter.lim_eq_iff_le_nhds.2 h] at hx
  exact cond _ hx

/--
theorem `Filter.Tendsto.limUnder_eq` / 定理 `Filter.Tendsto.limUnder_eq`

English:
theorem Filter.Tendsto.limUnder_eq
  statement: {x : X} {f : Filter Y} [NeBot f] {g : Y -> X}
  proof: lim_eq h

中文:
定理 滤子.收敛.limUnder_eq
  结论: {x : X} {f : 滤子 Y} [NeBot f] {g : Y -> X}
  证明: lim_eq h

Depends on / 依赖: lim_eq
-/
theorem Filter.Tendsto.limUnder_eq {x : X} {f : Filter Y} [NeBot f] {g : Y -> X}
    (h : Tendsto g f (𝓝 x)) : @limUnder _ _ _ ⟨x⟩ f g = x :=
  lim_eq h

/--
theorem `Filter.limUnder_eq_iff` / 定理 `Filter.limUnder_eq_iff`

English:
theorem Filter.limUnder_eq_iff
  statement: {f : Filter Y} [NeBot f] {g : Y -> X} (h : exists x, Tendsto g f (𝓝 x))
  proof: ⟨fun c => c ▸ tendsto_nhds_limUnder h, Filter.Tendsto.limUnder_eq⟩

中文:
定理 滤子.limUnder_eq_iff
  结论: {f : 滤子 Y} [NeBot f] {g : Y -> X} (h : 存在 x, 收敛 g f (𝓝 x))
  证明: ⟨fun c => c ▸ tendsto_nhds_limUnder h, Filter.Tendsto.limUnder_eq⟩

Depends on / 依赖: Filter, Filter.Tendsto.limUnder_eq, Tendsto, limUnder_eq, tendsto_nhds_limUnder
-/
theorem Filter.limUnder_eq_iff {f : Filter Y} [NeBot f] {g : Y -> X} (h : exists x, Tendsto g f (𝓝 x))
    {x} : @limUnder _ _ _ ⟨x⟩ f g = x ↔ Tendsto g f (𝓝 x) :=
  ⟨fun c => c ▸ tendsto_nhds_limUnder h, Filter.Tendsto.limUnder_eq⟩

/--
theorem `Continuous.limUnder_eq` / 定理 `Continuous.limUnder_eq`

English:
theorem Continuous.limUnder_eq
  given: [TopologicalSpace Y] {f : Y -> X} (h : Continuous f) (y : Y)
  proof: (h.tendsto y).limUnder_eq

@[simp]

中文:
定理 连续.limUnder_eq
  条件: [拓扑空间 Y] {f : Y -> X} (h : 连续 f) (y : Y)
  证明: (h.tendsto y).limUnder_eq

@[simp]

Depends on / 依赖: h.tendsto, limUnder_eq, tendsto
-/
theorem Continuous.limUnder_eq [TopologicalSpace Y] {f : Y -> X} (h : Continuous f) (y : Y) :
    @limUnder _ _ _ ⟨f y⟩ (𝓝 y) f = f y :=
  (h.tendsto y).limUnder_eq

@[simp]
/--
theorem `lim_nhds` / 定理 `lim_nhds`

English:
theorem lim_nhds
  given: (x : X)
  statement: @lim _ _ ⟨x⟩ (𝓝 x) = x
  proof: lim_eq le_rfl

@[simp]

中文:
定理 lim_nhds
  条件: (x : X)
  结论: @lim _ _ ⟨x⟩ (𝓝 x) = x
  证明: lim_eq le_rfl

@[simp]

Depends on / 依赖: le_rfl, lim_eq
-/
theorem lim_nhds (x : X) : @lim _ _ ⟨x⟩ (𝓝 x) = x :=
  lim_eq le_rfl

@[simp]
/--
theorem `limUnder_nhds_id` / 定理 `limUnder_nhds_id`

English:
theorem limUnder_nhds_id
  given: (x : X)
  statement: @limUnder _ _ _ ⟨x⟩ (𝓝 x) id = x
  proof: lim_nhds x

@[simp]

中文:
定理 limUnder_nhds_id
  条件: (x : X)
  结论: @limUnder _ _ _ ⟨x⟩ (𝓝 x) id = x
  证明: lim_nhds x

@[simp]

Depends on / 依赖: lim_nhds
-/
theorem limUnder_nhds_id (x : X) : @limUnder _ _ _ ⟨x⟩ (𝓝 x) id = x :=
  lim_nhds x

@[simp]
/--
theorem `lim_nhdsWithin` / 定理 `lim_nhdsWithin`

English:
theorem lim_nhdsWithin
  given: {x : X} {s : Set X} (h : x in closure s)
  statement: @lim _ _ ⟨x⟩ (𝓝[s] x) = x
  proof: haveI : NeBot (𝓝[s] x) := mem_closure_iff_clusterPt.1 h
  lim_eq inf_le_left

@[simp]

中文:
定理 lim_nhdsWithin
  条件: {x : X} {s : 集合 X} (h : x in closure s)
  结论: @lim _ _ ⟨x⟩ (𝓝[s] x) = x
  证明: haveI : NeBot (𝓝[s] x) := mem_closure_iff_clusterPt.1 h
  lim_eq inf_le_left

@[simp]

Depends on / 依赖: inf_le_left, lim_eq, mem_closure_iff_clusterPt
-/
theorem lim_nhdsWithin {x : X} {s : Set X} (h : x in closure s) : @lim _ _ ⟨x⟩ (𝓝[s] x) = x :=
  haveI : NeBot (𝓝[s] x) := mem_closure_iff_clusterPt.1 h
  lim_eq inf_le_left

@[simp]
/--
theorem `limUnder_nhdsWithin_id` / 定理 `limUnder_nhdsWithin_id`

English:
theorem limUnder_nhdsWithin_id
  given: {x : X} {s : Set X} (h : x in closure s)
  proof: lim_nhdsWithin h

中文:
定理 limUnder_nhdsWithin_id
  条件: {x : X} {s : 集合 X} (h : x in closure s)
  证明: lim_nhdsWithin h

Depends on / 依赖: lim_nhdsWithin
-/
theorem limUnder_nhdsWithin_id {x : X} {s : Set X} (h : x in closure s) :
    @limUnder _ _ _ ⟨x⟩ (𝓝[s] x) id = x :=
  lim_nhdsWithin h

end limUnder

/-!
### `T2Space` constructions

We use two lemmas to prove that various standard constructions generate Hausdorff spaces from
Hausdorff spaces:

* `separated_by_continuous` says that two points `x y : X` can be separated by open neighborhoods
  provided that there exists a continuous map `f : X → Y` with a Hausdorff codomain such that
  `f x ≠ f y`. We use this lemma to prove that topological spaces defined using `induced` are
  Hausdorff spaces.

* `separated_by_isOpenEmbedding` says that for an open embedding `f : X → Y` of a Hausdorff space
  `X`, the images of two distinct points `x y : X`, `x ≠ y` can be separated by open neighborhoods.
  We use this lemma to prove that topological spaces defined using `coinduced` are Hausdorff spaces.
-/

-- see Note [lower instance priority]
instance (priority := 100) DiscreteTopology.toT2Space
    [DiscreteTopology X] : T2Space X :=
  ⟨fun x y h => ⟨{x}, {y}, isOpen_discrete _, isOpen_discrete _, rfl, rfl, disjoint_singleton.2 h⟩⟩

/--
theorem `separated_by_continuous` / 定理 `separated_by_continuous`

English:
theorem separated_by_continuous
  statement: [TopologicalSpace Y] [T2Space Y]
  proof: let ⟨u, v, uo, vo, xu, yv, uv⟩ := t2_separation h
  ⟨f ⁻¹' u, f ⁻¹' v, uo.preimage hf, vo.preimage hf, xu, yv, uv.preimage _⟩

中文:
定理 separated_by_continuous
  结论: [拓扑空间 Y] [T2空间 Y]
  证明: let ⟨u, v, uo, vo, xu, yv, uv⟩ := t2_separation h
  ⟨f ⁻¹' u, f ⁻¹' v, uo.preimage hf, vo.preimage hf, xu, yv, uv.preimage _⟩

Depends on / 依赖: preimage, t2_separation, uo.preimage, uv.preimage, vo.preimage
-/
theorem separated_by_continuous [TopologicalSpace Y] [T2Space Y]
    {f : X -> Y} (hf : Continuous f) {x y : X} (h : f x != f y) :
    exists u v : Set X, IsOpen u ∧ IsOpen v ∧ x in u ∧ y in v ∧ Disjoint u v :=
  let ⟨u, v, uo, vo, xu, yv, uv⟩ := t2_separation h
  ⟨f ⁻¹' u, f ⁻¹' v, uo.preimage hf, vo.preimage hf, xu, yv, uv.preimage _⟩

/--
theorem `separated_by_isOpenEmbedding` / 定理 `separated_by_isOpenEmbedding`

English:
theorem separated_by_isOpenEmbedding
  statement: [TopologicalSpace Y] [T2Space X]
  proof: let ⟨u, v, uo, vo, xu, yv, uv⟩ := t2_separation h
  ⟨f '' u, f '' v, hf.isOpenMap _ uo, hf.isOpenMap _ vo, mem_image_of_mem _ xu,
    mem_image_of_mem _ yv, disjoint_image_of_injective hf.injective uv⟩

中文:
定理 separated_by_isOpenEmbedding
  结论: [拓扑空间 Y] [T2空间 X]
  证明: let ⟨u, v, uo, vo, xu, yv, uv⟩ := t2_separation h
  ⟨f '' u, f '' v, hf.isOpenMap _ uo, hf.isOpenMap _ vo, mem_image_of_mem _ xu,
    mem_image_of_mem _ yv, disjoint_image_of_injective hf.injective uv⟩

Depends on / 依赖: disjoint_image_of_injective, hf.injective, hf.isOpenMap, injective, isOpenMap, mem_image_of_mem, t2_separation
-/
theorem separated_by_isOpenEmbedding [TopologicalSpace Y] [T2Space X]
    {f : X -> Y} (hf : IsOpenEmbedding f) {x y : X} (h : x != y) :
    exists u v : Set Y, IsOpen u ∧ IsOpen v ∧ f x in u ∧ f y in v ∧ Disjoint u v :=
  let ⟨u, v, uo, vo, xu, yv, uv⟩ := t2_separation h
  ⟨f '' u, f '' v, hf.isOpenMap _ uo, hf.isOpenMap _ vo, mem_image_of_mem _ xu,
    mem_image_of_mem _ yv, disjoint_image_of_injective hf.injective uv⟩

instance {p : X -> Prop} [T2Space X] : T2Space (Subtype p) := inferInstance

/--
Instance `Prod.t2Space` / 实例 `Prod.t2Space`

English:
instance Prod.t2Space
  signature: [T2Space X] [TopologicalSpace Y] [T2Space Y]
  body: inferInstance

中文:
实例 积类型.t2Space
  签名: [T2空间 X] [拓扑空间 Y] [T2空间 Y]
  定义体: inferInstance
-/
instance Prod.t2Space [T2Space X] [TopologicalSpace Y] [T2Space Y] : T2Space (X × Y) :=
  inferInstance

/--
theorem `T2Space.of_injective_continuous` / 定理 `T2Space.of_injective_continuous`

English:
theorem T2Space.of_injective_continuous
  statement: [TopologicalSpace Y] [T2Space Y] {f : X -> Y}
  proof: ⟨fun _ _ h => separated_by_continuous hc (hinj.ne h)⟩

中文:
定理 T2空间.of_injective_continuous
  结论: [拓扑空间 Y] [T2空间 Y] {f : X -> Y}
  证明: ⟨fun _ _ h => separated_by_continuous hc (hinj.ne h)⟩

Depends on / 依赖: hinj.ne, separated_by_continuous
-/
theorem T2Space.of_injective_continuous [TopologicalSpace Y] [T2Space Y] {f : X -> Y}
    (hinj : Injective f) (hc : Continuous f) : T2Space X :=
  ⟨fun _ _ h => separated_by_continuous hc (hinj.ne h)⟩

/--
theorem `Topology.IsEmbedding.t2Space` / 定理 `Topology.IsEmbedding.t2Space`

English:
theorem Topology.IsEmbedding.t2Space
  statement: [TopologicalSpace Y] [T2Space Y] {f : X -> Y}
  proof: .of_injective_continuous hf.injective hf.continuous

中文:
定理 拓扑.是嵌入.t2Space
  结论: [拓扑空间 Y] [T2空间 Y] {f : X -> Y}
  证明: .of_injective_continuous hf.injective hf.continuous

Depends on / 依赖: continuous, hf.continuous, hf.injective, injective, of_injective_continuous
-/
theorem Topology.IsEmbedding.t2Space [TopologicalSpace Y] [T2Space Y] {f : X -> Y}
    (hf : IsEmbedding f) : T2Space X :=
  .of_injective_continuous hf.injective hf.continuous

/--
theorem `Homeomorph.t2Space` / 定理 `Homeomorph.t2Space`

English:
theorem Homeomorph.t2Space
  given: [TopologicalSpace Y] [T2Space X] (h : X ≃ₜ Y)
  statement: T2Space Y
  proof: h.symm.isEmbedding.t2Space

中文:
定理 同胚.t2Space
  条件: [拓扑空间 Y] [T2空间 X] (h : X ≃ₜ Y)
  结论: T2空间 Y
  证明: h.symm.isEmbedding.t2Space
-/
protected theorem Homeomorph.t2Space [TopologicalSpace Y] [T2Space X] (h : X ≃ₜ Y) : T2Space Y :=
  h.symm.isEmbedding.t2Space

/--
Instance `ULift.instT2Space` / 实例 `ULift.instT2Space`

English:
instance ULift.instT2Space
  signature: [T2Space X]
  body: IsEmbedding.uliftDown.t2Space

中文:
实例 类型层提升.instT2Space
  签名: [T2空间 X]
  定义体: IsEmbedding.uliftDown.t2Space

Depends on / 依赖: IsEmbedding, IsEmbedding.uliftDown.t2Space, t2Space, uliftDown
-/
instance ULift.instT2Space [T2Space X] : T2Space (ULift X) :=
  IsEmbedding.uliftDown.t2Space

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [T2Space
  signature: X] [TopologicalSpace Y] [T2Space Y] :
  body: by
  constructor
  rintro (x | x) (y | y) h
· exact separated_by_isOpenEmbedding .inl ne_of_apply_ne _ h
· exact separated_by_continuous continuous_isLeft by simp
· exact separated_by_continuous continuous_isLeft by simp
· exact separated_by_isOpenEmbedding .inr ne_of_apply_ne _ h

中文:
实例 [T2空间
  签名: X] [拓扑空间 Y] [T2空间 Y] :
  定义体: by
  constructor
  rintro (x | x) (y | y) h
· exact separated_by_isOpenEmbedding .inl ne_of_apply_ne _ h
· exact separated_by_continuous continuous_isLeft by simp
· exact separated_by_continuous continuous_isLeft by simp
· exact separated_by_isOpenEmbedding .inr ne_of_apply_ne _ h

Depends on / 依赖: continuous_isLeft, ne_of_apply_ne, separated_by_continuous, separated_by_isOpenEmbedding
-/
instance [T2Space X] [TopologicalSpace Y] [T2Space Y] :
    T2Space (X oplus Y) := by
  constructor
  rintro (x | x) (y | y) h
· exact separated_by_isOpenEmbedding .inl ne_of_apply_ne _ h
· exact separated_by_continuous continuous_isLeft by simp
· exact separated_by_continuous continuous_isLeft by simp
· exact separated_by_isOpenEmbedding .inr ne_of_apply_ne _ h

/--
Instance `Pi.t2Space` / 实例 `Pi.t2Space`

English:
instance Pi.t2Space
  signature: {Y : X -> Type v} [forall a, TopologicalSpace (Y a)]
  body: inferInstance

中文:
实例 依赖函数类型.t2Space
  签名: {Y : X -> 类型v} [对任意 a, 拓扑空间 (Y a)]
  定义体: inferInstance
-/
instance Pi.t2Space {Y : X -> Type v} [forall a, TopologicalSpace (Y a)]
    [forall a, T2Space (Y a)] : T2Space (forall a, Y a) :=
  inferInstance

/--
Instance `Sigma.t2Space` / 实例 `Sigma.t2Space`

English:
instance Sigma.t2Space
  signature: {ι} {X : ι -> Type*} [forall i, TopologicalSpace (X i)] [forall a, T2Space (X a)]
  body: by
  constructor
  rintro ⟨i, x⟩ ⟨j, y⟩ ne
  rcases eq_or_ne i j with (rfl | h)
  · replace ne : x != y := ne_of_apply_ne _ ne
    exact separated_by_isOpenEmbedding .sigmaMk ne
  · let _ := (⊥ : TopologicalSpace ι); have : DiscreteTopology ι := ⟨rfl⟩
    exact separated_by_continuous (continuous_def.2 fun u _ => isOpen_sigma_fst_preimage u) h

中文:
实例 依赖和类型.t2Space
  签名: {ι} {X : ι -> 类型} [对任意 i, 拓扑空间 (X i)] [对任意 a, T2空间 (X a)]
  定义体: by
  constructor
  rintro ⟨i, x⟩ ⟨j, y⟩ ne
  rcases eq_or_ne i j with (rfl | h)
  · replace ne : x != y := ne_of_apply_ne _ ne
    exact separated_by_isOpenEmbedding .sigmaMk ne
  · let _ := (⊥ : TopologicalSpace ι); have : DiscreteTopology ι := ⟨rfl⟩
    exact separated_by_continuous (continuous_def.2 fun u _ => isOpen_sigma_fst_preimage u) h

Depends on / 依赖: DiscreteTopology, TopologicalSpace, continuous_def, eq_or_ne, isOpen_sigma_fst_preimage, ne_of_apply_ne, replace, separated_by_continuous, separated_by_isOpenEmbedding, sigmaMk
-/
instance Sigma.t2Space {ι} {X : ι -> Type*} [forall i, TopologicalSpace (X i)] [forall a, T2Space (X a)] :
    T2Space (Σ i, X i) := by
  constructor
  rintro ⟨i, x⟩ ⟨j, y⟩ ne
  rcases eq_or_ne i j with (rfl | h)
  · replace ne : x != y := ne_of_apply_ne _ ne
    exact separated_by_isOpenEmbedding .sigmaMk ne
  · let _ := (⊥ : TopologicalSpace ι); have : DiscreteTopology ι := ⟨rfl⟩
    exact separated_by_continuous (continuous_def.2 fun u _ => isOpen_sigma_fst_preimage u) h

section
variable (X)

/-- The smallest equivalence relation on a topological space giving a T2 quotient. -/
@[instance_reducible]
/--
Definition of `t2Setoid` / `t2Setoid` 的定义

English:
definition t2Setoid
  signature: : Setoid X
  body: sInf {s | T2Space (Quotient s)}

中文:
定义 t2Setoid
  签名: : 集合等价关系 X
  定义体: sInf {s | T2Space (Quotient s)}

Depends on / 依赖: Quotient, T2Space
-/
def t2Setoid : Setoid X := sInf {s | T2Space (Quotient s)}

/--
Definition of `T2Quotient` / `T2Quotient` 的定义

English:
definition T2Quotient
  body: Quotient (t2Setoid X)

中文:
定义 T2Quotient
  定义体: Quotient (t2Setoid X)

Depends on / 依赖: Quotient, t2Setoid
-/
def T2Quotient := Quotient (t2Setoid X)

namespace T2Quotient
variable {X}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: TopologicalSpace (T2Quotient X)
  body: inferInstanceAs TopologicalSpace (Quotient _)

中文:
实例 :
  签名: 拓扑空间 (T2Quotient X)
  定义体: inferInstanceAs TopologicalSpace (Quotient _)

Depends on / 依赖: Quotient, TopologicalSpace
-/
instance : TopologicalSpace (T2Quotient X) :=
inferInstanceAs TopologicalSpace (Quotient _)

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: : X -> T2Quotient X
  body: Quotient.mk (t2Setoid X)

中文:
定义 mk
  签名: : X -> T2Quotient X
  定义体: Quotient.mk (t2Setoid X)

Depends on / 依赖: Quotient, Quotient.mk, t2Setoid
-/
def mk : X -> T2Quotient X := Quotient.mk (t2Setoid X)

/--
lemma `mk_eq` / 引理 `mk_eq`

English:
lemma mk_eq
  given: {x y : X}
  statement: mk x = mk y ↔ forall s : Setoid X, T2Space (Quotient s) -> s x y
  proof: Setoid.quotient_mk_sInf_eq

中文:
引理 mk_eq
  条件: {x y : X}
  结论: mk x = mk y ↔ 对任意 s : 集合等价关系 X, T2空间 (商 s) -> s x y
  证明: Setoid.quotient_mk_sInf_eq

Depends on / 依赖: Setoid, Setoid.quotient_mk_sInf_eq, quotient_mk_sInf_eq
-/
lemma mk_eq {x y : X} : mk x = mk y ↔ forall s : Setoid X, T2Space (Quotient s) -> s x y :=
  Setoid.quotient_mk_sInf_eq

variable (X)

/--
lemma `surjective_mk` / 引理 `surjective_mk`

English:
lemma surjective_mk
  statement: Surjective (mk : X -> T2Quotient X)
  proof: Quotient.mk_surjective

中文:
引理 surjective_mk
  结论: 满射 (mk : X -> T2Quotient X)
  证明: Quotient.mk_surjective

Depends on / 依赖: Quotient, Quotient.mk_surjective, mk_surjective
-/
lemma surjective_mk : Surjective (mk : X -> T2Quotient X) := Quotient.mk_surjective

/--
lemma `continuous_mk` / 引理 `continuous_mk`

English:
lemma continuous_mk
  statement: Continuous (mk : X -> T2Quotient X)
  proof: continuous_quotient_mk'

中文:
引理 continuous_mk
  结论: 连续 (mk : X -> T2Quotient X)
  证明: continuous_quotient_mk'

Depends on / 依赖: continuous_quotient_mk
-/
lemma continuous_mk : Continuous (mk : X -> T2Quotient X) :=
  continuous_quotient_mk'

variable {X}

@[elab_as_elim]
/--
lemma `inductionOn` / 引理 `inductionOn`

English:
lemma inductionOn
  statement: {motive : T2Quotient X -> Prop} (q : T2Quotient X)
  proof: Quotient.inductionOn q h

@[elab_as_elim]

中文:
引理 inductionOn
  结论: {motive : T2Quotient X -> 命题} (q : T2Quotient X)
  证明: Quotient.inductionOn q h

@[elab_as_elim]
-/
protected lemma inductionOn {motive : T2Quotient X -> Prop} (q : T2Quotient X)
    (h : forall x, motive (T2Quotient.mk x)) : motive q := Quotient.inductionOn q h

@[elab_as_elim]
/--
lemma `inductionOn₂` / 引理 `inductionOn₂`

English:
lemma inductionOn₂
  statement: [TopologicalSpace Y] {motive : T2Quotient X -> T2Quotient Y -> Prop}
  proof: Quotient.inductionOn₂ q q' h

中文:
引理 inductionOn₂
  结论: [拓扑空间 Y] {motive : T2Quotient X -> T2Quotient Y -> 命题}
  证明: Quotient.inductionOn₂ q q' h
-/
protected lemma inductionOn₂ [TopologicalSpace Y] {motive : T2Quotient X -> T2Quotient Y -> Prop}
    (q : T2Quotient X) (q' : T2Quotient Y) (h : forall x y, motive (mk x) (mk y)) : motive q q' :=
  Quotient.inductionOn₂ q q' h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: T2Space (T2Quotient X)
  body: by
  rw [t2Space_iff]
  rintro ⟨x⟩ ⟨y⟩ (h : ¬ T2Quotient.mk x = T2Quotient.mk y)
  obtain ⟨s, hs, hsxy⟩ : exists s, T2Space (Quotient s) ∧ Quotient.mk s x != Quotient.mk s y := by
    simpa [T2Quotient.mk_eq, Quotient.eq] using h
  exact separated_by_continuous (continuous_map_sInf (by exact hs)) hsxy

中文:
实例 :
  签名: T2空间 (T2Quotient X)
  定义体: by
  rw [t2Space_iff]
  rintro ⟨x⟩ ⟨y⟩ (h : ¬ T2Quotient.mk x = T2Quotient.mk y)
  obtain ⟨s, hs, hsxy⟩ : exists s, T2Space (Quotient s) ∧ Quotient.mk s x != Quotient.mk s y := by
    simpa [T2Quotient.mk_eq, Quotient.eq] using h
  exact separated_by_continuous (continuous_map_sInf (by exact hs)) hsxy

Depends on / 依赖: Quotient, Quotient.eq, Quotient.mk, T2Quotient, T2Quotient.mk, T2Quotient.mk_eq, T2Space, continuous_map_sInf, mk_eq, separated_by_continuous, t2Space_iff
-/
instance : T2Space (T2Quotient X) := by
  rw [t2Space_iff]
  rintro ⟨x⟩ ⟨y⟩ (h : ¬ T2Quotient.mk x = T2Quotient.mk y)
  obtain ⟨s, hs, hsxy⟩ : exists s, T2Space (Quotient s) ∧ Quotient.mk s x != Quotient.mk s y := by
    simpa [T2Quotient.mk_eq, Quotient.eq] using h
  exact separated_by_continuous (continuous_map_sInf (by exact hs)) hsxy

/--
lemma `compatible` / 引理 `compatible`

English:
lemma compatible
  statement: {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
  proof: t2Setoid X
    forall (a b : X), a ≈ b -> f a = f b := by
  change t2Setoid X <= Setoid.ker f
exact sInf_le .of_injective_continuous
    (Setoid.kerLift_injective _) (hf.quotient_lift fun _ _ => id)

中文:
引理 compatible
  结论: {X Y : 类型} [拓扑空间 X] [拓扑空间 Y] [T2空间 Y]
  证明: t2Setoid X
    forall (a b : X), a ≈ b -> f a = f b := by
  change t2Setoid X <= Setoid.ker f
exact sInf_le .of_injective_continuous
    (Setoid.kerLift_injective _) (hf.quotient_lift fun _ _ => id)

Depends on / 依赖: t2Setoid
-/
lemma compatible {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {f : X -> Y} (hf : Continuous f) : letI _ := t2Setoid X
    forall (a b : X), a ≈ b -> f a = f b := by
  change t2Setoid X <= Setoid.ker f
exact sInf_le .of_injective_continuous
    (Setoid.kerLift_injective _) (hf.quotient_lift fun _ _ => id)

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
  body: Quotient.lift f (T2Quotient.compatible hf)

中文:
定义 lift
  签名: {X Y : 类型} [拓扑空间 X] [拓扑空间 Y] [T2空间 Y]
  定义体: Quotient.lift f (T2Quotient.compatible hf)

Depends on / 依赖: Quotient, Quotient.lift, T2Quotient, T2Quotient.compatible, compatible
-/
def lift {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {f : X -> Y} (hf : Continuous f) : T2Quotient X -> Y :=
  Quotient.lift f (T2Quotient.compatible hf)

/--
lemma `continuous_lift` / 引理 `continuous_lift`

English:
lemma continuous_lift
  statement: {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
  proof: continuous_coinduced_dom.mpr hf

@[simp]

中文:
引理 continuous_lift
  结论: {X Y : 类型} [拓扑空间 X] [拓扑空间 Y] [T2空间 Y]
  证明: continuous_coinduced_dom.mpr hf

@[simp]

Depends on / 依赖: continuous_coinduced_dom, continuous_coinduced_dom.mpr
-/
lemma continuous_lift {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {f : X -> Y} (hf : Continuous f) : Continuous (T2Quotient.lift hf) :=
  continuous_coinduced_dom.mpr hf

@[simp]
/--
lemma `lift_mk` / 引理 `lift_mk`

English:
lemma lift_mk
  statement: {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
  proof: Quotient.lift_mk (s := t2Setoid X) f (T2Quotient.compatible hf) x

中文:
引理 lift_mk
  结论: {X Y : 类型} [拓扑空间 X] [拓扑空间 Y] [T2空间 Y]
  证明: Quotient.lift_mk (s := t2Setoid X) f (T2Quotient.compatible hf) x

Depends on / 依赖: Quotient, Quotient.lift_mk, T2Quotient, T2Quotient.compatible, compatible, lift_mk, t2Setoid
-/
lemma lift_mk {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {f : X -> Y} (hf : Continuous f) (x : X) : lift hf (mk x) = f x :=
  Quotient.lift_mk (s := t2Setoid X) f (T2Quotient.compatible hf) x

/--
lemma `unique_lift` / 引理 `unique_lift`

English:
lemma unique_lift
  statement: {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
  proof: by
.mp funext _ .right_cancellable apply surjective_mk X
  simp [← hfg]

中文:
引理 unique_lift
  结论: {X Y : 类型} [拓扑空间 X] [拓扑空间 Y] [T2空间 Y]
  证明: by
.mp funext _ .right_cancellable apply surjective_mk X
  simp [← hfg]

Depends on / 依赖: right_cancellable, surjective_mk
-/
lemma unique_lift {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {f : X -> Y} (hf : Continuous f) {g : T2Quotient X -> Y} (hfg : g ∘ mk = f) :
    g = lift hf := by
.mp funext _ .right_cancellable apply surjective_mk X
  simp [← hfg]

end T2Quotient
end

variable {Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]

/--
theorem `isClosed_eq` / 定理 `isClosed_eq`

English:
theorem isClosed_eq
  given: [T2Space X] {f g : Y -> X} (hf : Continuous f) (hg : Continuous g)
  proof: continuous_iff_isClosed.mp (hf.prodMk hg) _ isClosed_diagonal

中文:
定理 isClosed_eq
  条件: [T2空间 X] {f g : Y -> X} (hf : 连续 f) (hg : 连续 g)
  证明: continuous_iff_isClosed.mp (hf.prodMk hg) _ isClosed_diagonal

Depends on / 依赖: continuous_iff_isClosed, continuous_iff_isClosed.mp, hf.prodMk, isClosed_diagonal, prodMk
-/
theorem isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) (hg : Continuous g) :
    IsClosed { y : Y | f y = g y } :=
  continuous_iff_isClosed.mp (hf.prodMk hg) _ isClosed_diagonal

/-- If functions `f` and `g` are continuous on a closed set `s`,
then the set of points `x ∈ s` such that `f x = g x` is a closed set. -/
@[closedness .]
/--
theorem `IsClosed.isClosed_eq` / 定理 `IsClosed.isClosed_eq`

English:
theorem IsClosed.isClosed_eq
  statement: [T2Space Y] {f g : X -> Y} {s : Set X} (hs : IsClosed s)
  proof: (hf.prodMk hg).preimage_isClosed_of_isClosed hs isClosed_diagonal

中文:
定理 是闭集.isClosed_eq
  结论: [T2空间 Y] {f g : X -> Y} {s : 集合 X} (hs : 是闭集 s)
  证明: (hf.prodMk hg).preimage_isClosed_of_isClosed hs isClosed_diagonal
-/
protected theorem IsClosed.isClosed_eq [T2Space Y] {f g : X -> Y} {s : Set X} (hs : IsClosed s)
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) : IsClosed {x in s | f x = g x} :=
  (hf.prodMk hg).preimage_isClosed_of_isClosed hs isClosed_diagonal

/--
theorem `isOpen_ne_fun` / 定理 `isOpen_ne_fun`

English:
theorem isOpen_ne_fun
  given: [T2Space X] {f g : Y -> X} (hf : Continuous f) (hg : Continuous g)
  proof: isOpen_compl_iff.mpr isClosed_eq hf hg

中文:
定理 isOpen_ne_fun
  条件: [T2空间 X] {f g : Y -> X} (hf : 连续 f) (hg : 连续 g)
  证明: isOpen_compl_iff.mpr isClosed_eq hf hg

Depends on / 依赖: isClosed_eq, isOpen_compl_iff, isOpen_compl_iff.mpr
-/
theorem isOpen_ne_fun [T2Space X] {f g : Y -> X} (hf : Continuous f) (hg : Continuous g) :
    IsOpen { y : Y | f y != g y } :=
isOpen_compl_iff.mpr isClosed_eq hf hg

/--
theorem `Set.EqOn.closure` / 定理 `Set.EqOn.closure`

English:
theorem Set.EqOn.closure
  statement: [T2Space X] {s : Set Y} {f g : Y -> X} (h : EqOn f g s)
  proof: closure_minimal h (isClosed_eq hf hg)

中文:
定理 集合.EqOn.closure
  结论: [T2空间 X] {s : 集合 Y} {f g : Y -> X} (h : EqOn f g s)
  证明: closure_minimal h (isClosed_eq hf hg)
-/
protected theorem Set.EqOn.closure [T2Space X] {s : Set Y} {f g : Y -> X} (h : EqOn f g s)
    (hf : Continuous f) (hg : Continuous g) : EqOn f g (closure s) :=
  closure_minimal h (isClosed_eq hf hg)

/--
theorem `Continuous.ext_on` / 定理 `Continuous.ext_on`

English:
theorem Continuous.ext_on
  statement: [T2Space X] {s : Set Y} (hs : Dense s) {f g : Y -> X} (hf : Continuous f)
  proof: funext fun x => h.closure hf hg (hs x)

中文:
定理 连续.ext_on
  结论: [T2空间 X] {s : 集合 Y} (hs : 稠密 s) {f g : Y -> X} (hf : 连续 f)
  证明: funext fun x => h.closure hf hg (hs x)

Depends on / 依赖: closure, h.closure
-/
theorem Continuous.ext_on [T2Space X] {s : Set Y} (hs : Dense s) {f g : Y -> X} (hf : Continuous f)
    (hg : Continuous g) (h : EqOn f g s) : f = g :=
  funext fun x => h.closure hf hg (hs x)

/--
theorem `eqOn_closure₂'` / 定理 `eqOn_closure₂'`

English:
theorem eqOn_closure₂'
  statement: [T2Space Z] {s : Set X} {t : Set Y} {f g : X -> Y -> Z}
  proof: suffices closure s subseteq ⋂ y in closure t, { x | f x y = g x y } by simpa only [subset_def, mem_iInter]
(closure_minimal fun x hx => mem_iInter₂.2 <| Set.EqOn.closure (h x hx) (hf₁ _) (hg₁ _))
    isClosed_biInter fun _ _ => isClosed_eq (hf₂ _) (hg₂ _)

中文:
定理 eqOn_closure₂'
  结论: [T2空间 Z] {s : 集合 X} {t : 集合 Y} {f g : X -> Y -> Z}
  证明: suffices closure s subseteq ⋂ y in closure t, { x | f x y = g x y } by simpa only [subset_def, mem_iInter]
(closure_minimal fun x hx => mem_iInter₂.2 <| Set.EqOn.closure (h x hx) (hf₁ _) (hg₁ _))
    isClosed_biInter fun _ _ => isClosed_eq (hf₂ _) (hg₂ _)

Depends on / 依赖: Set.EqOn.closure, closure, closure_minimal, isClosed_biInter, isClosed_eq, mem_iInter, subset_def, subseteq
-/
theorem eqOn_closure₂' [T2Space Z] {s : Set X} {t : Set Y} {f g : X -> Y -> Z}
    (h : forall x in s, forall y in t, f x y = g x y) (hf₁ : forall x, Continuous (f x))
    (hf₂ : forall y, Continuous fun x => f x y) (hg₁ : forall x, Continuous (g x))
    (hg₂ : forall y, Continuous fun x => g x y) : forall x in closure s, forall y in closure t, f x y = g x y :=
  suffices closure s subseteq ⋂ y in closure t, { x | f x y = g x y } by simpa only [subset_def, mem_iInter]
(closure_minimal fun x hx => mem_iInter₂.2 <| Set.EqOn.closure (h x hx) (hf₁ _) (hg₁ _))
    isClosed_biInter fun _ _ => isClosed_eq (hf₂ _) (hg₂ _)

/--
theorem `eqOn_closure₂` / 定理 `eqOn_closure₂`

English:
theorem eqOn_closure₂
  statement: [T2Space Z] {s : Set X} {t : Set Y} {f g : X -> Y -> Z}
  proof: eqOn_closure₂' h hf.uncurry_left hf.uncurry_right hg.uncurry_left hg.uncurry_right

中文:
定理 eqOn_closure₂
  结论: [T2空间 Z] {s : 集合 X} {t : 集合 Y} {f g : X -> Y -> Z}
  证明: eqOn_closure₂' h hf.uncurry_left hf.uncurry_right hg.uncurry_left hg.uncurry_right

Depends on / 依赖: hf.uncurry_left, hf.uncurry_right, hg.uncurry_left, hg.uncurry_right, uncurry_left, uncurry_right
-/
theorem eqOn_closure₂ [T2Space Z] {s : Set X} {t : Set Y} {f g : X -> Y -> Z}
    (h : forall x in s, forall y in t, f x y = g x y) (hf : Continuous (uncurry f))
    (hg : Continuous (uncurry g)) : forall x in closure s, forall y in closure t, f x y = g x y :=
  eqOn_closure₂' h hf.uncurry_left hf.uncurry_right hg.uncurry_left hg.uncurry_right

/--
theorem `Set.EqOn.of_subset_closure` / 定理 `Set.EqOn.of_subset_closure`

English:
theorem Set.EqOn.of_subset_closure
  statement: [T2Space Y] {s t : Set X} {f g : X -> Y} (h : EqOn f g s)
  proof: by
  intro x hx
  have : (𝓝[s] x).NeBot := mem_closure_iff_clusterPt.mp (hts hx)
  exact
    tendsto_nhds_unique_of_eventuallyEq ((hf x hx).mono_left <| nhdsWithin_mono _ hst)
      ((hg x hx).mono_left <| nhdsWithin_mono _ hst) (h.eventuallyEq_of_mem self_mem_nhdsWithin)

中文:
定理 集合.EqOn.of_subset_closure
  结论: [T2空间 Y] {s t : 集合 X} {f g : X -> Y} (h : EqOn f g s)
  证明: by
  intro x hx
  have : (𝓝[s] x).NeBot := mem_closure_iff_clusterPt.mp (hts hx)
  exact
    tendsto_nhds_unique_of_eventuallyEq ((hf x hx).mono_left <| nhdsWithin_mono _ hst)
      ((hg x hx).mono_left <| nhdsWithin_mono _ hst) (h.eventuallyEq_of_mem self_mem_nhdsWithin)

Depends on / 依赖: eventuallyEq_of_mem, h.eventuallyEq_of_mem, mem_closure_iff_clusterPt, mem_closure_iff_clusterPt.mp, mono_left, nhdsWithin_mono, self_mem_nhdsWithin, tendsto_nhds_unique_of_eventuallyEq
-/
theorem Set.EqOn.of_subset_closure [T2Space Y] {s t : Set X} {f g : X -> Y} (h : EqOn f g s)
    (hf : ContinuousOn f t) (hg : ContinuousOn g t) (hst : s subseteq t) (hts : t subseteq closure s) :
    EqOn f g t := by
  intro x hx
  have : (𝓝[s] x).NeBot := mem_closure_iff_clusterPt.mp (hts hx)
  exact
    tendsto_nhds_unique_of_eventuallyEq ((hf x hx).mono_left <| nhdsWithin_mono _ hst)
      ((hg x hx).mono_left <| nhdsWithin_mono _ hst) (h.eventuallyEq_of_mem self_mem_nhdsWithin)

/--
theorem `Function.LeftInverse.isClosed_range` / 定理 `Function.LeftInverse.isClosed_range`

English:
theorem Function.LeftInverse.isClosed_range
  statement: [T2Space X] {f : X -> Y} {g : Y -> X}
  proof: have : EqOn (g ∘ f) id (closure <| range g) :=
    h.rightInvOn_range.eqOn.closure (hg.comp hf) continuous_id
  isClosed_of_closure_subset fun x hx => ⟨f x, this hx⟩

中文:
定理 函数.左逆.isClosed_range
  结论: [T2空间 X] {f : X -> Y} {g : Y -> X}
  证明: have : EqOn (g ∘ f) id (closure <| range g) :=
    h.rightInvOn_range.eqOn.closure (hg.comp hf) continuous_id
  isClosed_of_closure_subset fun x hx => ⟨f x, this hx⟩

Depends on / 依赖: closure, continuous_id, h.rightInvOn_range.eqOn.closure, hg.comp, isClosed_of_closure_subset, rightInvOn_range
-/
theorem Function.LeftInverse.isClosed_range [T2Space X] {f : X -> Y} {g : Y -> X}
    (h : Function.LeftInverse f g) (hf : Continuous f) (hg : Continuous g) : IsClosed (range g) :=
  have : EqOn (g ∘ f) id (closure <| range g) :=
    h.rightInvOn_range.eqOn.closure (hg.comp hf) continuous_id
  isClosed_of_closure_subset fun x hx => ⟨f x, this hx⟩

/--
theorem `Function.LeftInverse.isClosedEmbedding` / 定理 `Function.LeftInverse.isClosedEmbedding`

English:
theorem Function.LeftInverse.isClosedEmbedding
  statement: [T2Space X] {f : X -> Y} {g : Y -> X}
  proof: ⟨.of_leftInverse h hf hg, h.isClosed_range hf hg⟩

中文:
定理 函数.左逆.isClosedEmbedding
  结论: [T2空间 X] {f : X -> Y} {g : Y -> X}
  证明: ⟨.of_leftInverse h hf hg, h.isClosed_range hf hg⟩

Depends on / 依赖: h.isClosed_range, isClosed_range, of_leftInverse
-/
theorem Function.LeftInverse.isClosedEmbedding [T2Space X] {f : X -> Y} {g : Y -> X}
    (h : Function.LeftInverse f g) (hf : Continuous f) (hg : Continuous g) : IsClosedEmbedding g :=
  ⟨.of_leftInverse h hf hg, h.isClosed_range hf hg⟩

/--
theorem `SeparatedNhds.of_isCompact_isCompact` / 定理 `SeparatedNhds.of_isCompact_isCompact`

English:
theorem SeparatedNhds.of_isCompact_isCompact
  statement: [T2Space X] {s t : Set X} (hs : IsCompact s)
  proof: by
  simp only [SeparatedNhds, prod_subset_compl_diagonal_iff_disjoint.symm] at hst ⊢
  exact generalized_tube_lemma hs ht isClosed_diagonal.isOpen_compl hst

中文:
定理 SeparatedNhds.of_isCompact_isCompact
  结论: [T2空间 X] {s t : 集合 X} (hs : 是紧集 s)
  证明: by
  simp only [SeparatedNhds, prod_subset_compl_diagonal_iff_disjoint.symm] at hst ⊢
  exact generalized_tube_lemma hs ht isClosed_diagonal.isOpen_compl hst

Depends on / 依赖: SeparatedNhds, generalized_tube_lemma, isClosed_diagonal, isClosed_diagonal.isOpen_compl, isOpen_compl, prod_subset_compl_diagonal_iff_disjoint, prod_subset_compl_diagonal_iff_disjoint.symm
-/
theorem SeparatedNhds.of_isCompact_isCompact [T2Space X] {s t : Set X} (hs : IsCompact s)
    (ht : IsCompact t) (hst : Disjoint s t) : SeparatedNhds s t := by
  simp only [SeparatedNhds, prod_subset_compl_diagonal_iff_disjoint.symm] at hst ⊢
  exact generalized_tube_lemma hs ht isClosed_diagonal.isOpen_compl hst

/--
lemma `SeparatedNhds.of_isClosed_isCompact_closure_compl_isClosed` / 引理 `SeparatedNhds.of_isClosed_isCompact_closure_compl_isClosed`

English:
lemma SeparatedNhds.of_isClosed_isCompact_closure_compl_isClosed
  statement: [R1Space X] {s : Set X}
  proof: by
  -- Since `t` is a closed subset of the compact set `closure sᶜ`, it is compact.
have ht : IsCompact t := .of_isClosed_subset H2 H3 H4.subset_compl_left.trans subset_closure
  -- we split `s` into its frontier and its interior.
  rw [← sdiff_union_of_subset (interior_subset (s := s))]
  -- since `t ⊆ sᶜ`, which is open, and `interior s` is open, we have
  -- `SeparatedNhds (interior s) t`, which leaves us only with the frontier.
  refine .union_left ?_ ⟨interior s, sᶜ, isOpen_interior, H1.isOpen_compl, le_rfl,
    H4.subset_compl_left, disjoint_compl_right.mono_left interior_subset⟩
  -- Since the frontier of `s` is compact (as it is a subset of `closure sᶜ`), we simply apply
  -- `SeparatedNhds_of_isCompact_isCompact`.
  rw [← H1.frontier_eq]; rw [frontier_eq_closure_inter_closure]; rw [H1.closure_eq]
  refine .of_isCompact_isCompact_isClosed ?_ ht H3 (disjoint_of_subset_left inter_subset_left H4)
  exact H2.of_isClosed_subset (H1.inter isClosed_closure) inter_subset_right

中文:
引理 SeparatedNhds.of_isClosed_isCompact_closure_compl_isClosed
  结论: [R1空间 X] {s : 集合 X}
  证明: by
  -- Since `t` is a closed subset of the compact set `closure sᶜ`, it is compact.
have ht : IsCompact t := .of_isClosed_subset H2 H3 H4.subset_compl_left.trans subset_closure
  -- we split `s` into its frontier and its interior.
  rw [← sdiff_union_of_subset (interior_subset (s := s))]
  -- since `t ⊆ sᶜ`, which is open, and `interior s` is open, we have
  -- `SeparatedNhds (interior s) t`, which leaves us only with the frontier.
  refine .union_left ?_ ⟨interior s, sᶜ, isOpen_interior, H1.isOpen_compl, le_rfl,
    H4.subset_compl_left, disjoint_compl_right.mono_left interior_subset⟩
  -- Since the frontier of `s` is compact (as it is a subset of `closure sᶜ`), we simply apply
  -- `SeparatedNhds_of_isCompact_isCompact`.
  rw [← H1.frontier_eq]; rw [frontier_eq_closure_inter_closure]; rw [H1.closure_eq]
  refine .of_isCompact_isCompact_isClosed ?_ ht H3 (disjoint_of_subset_left inter_subset_left H4)
  exact H2.of_isClosed_subset (H1.inter isClosed_closure) inter_subset_right
-/
lemma SeparatedNhds.of_isClosed_isCompact_closure_compl_isClosed [R1Space X] {s : Set X}
    {t : Set X} (H1 : IsClosed s) (H2 : IsCompact (closure sᶜ)) (H3 : IsClosed t)
    (H4 : Disjoint s t) : SeparatedNhds s t := by
  -- Since `t` is a closed subset of the compact set `closure sᶜ`, it is compact.
have ht : IsCompact t := .of_isClosed_subset H2 H3 H4.subset_compl_left.trans subset_closure
  -- we split `s` into its frontier and its interior.
  rw [← sdiff_union_of_subset (interior_subset (s := s))]
  -- since `t ⊆ sᶜ`, which is open, and `interior s` is open, we have
  -- `SeparatedNhds (interior s) t`, which leaves us only with the frontier.
  refine .union_left ?_ ⟨interior s, sᶜ, isOpen_interior, H1.isOpen_compl, le_rfl,
    H4.subset_compl_left, disjoint_compl_right.mono_left interior_subset⟩
  -- Since the frontier of `s` is compact (as it is a subset of `closure sᶜ`), we simply apply
  -- `SeparatedNhds_of_isCompact_isCompact`.
  rw [← H1.frontier_eq]; rw [frontier_eq_closure_inter_closure]; rw [H1.closure_eq]
  refine .of_isCompact_isCompact_isClosed ?_ ht H3 (disjoint_of_subset_left inter_subset_left H4)
  exact H2.of_isClosed_subset (H1.inter isClosed_closure) inter_subset_right

section SeparatedFinset

/--
theorem `SeparatedNhds.of_finset_finset` / 定理 `SeparatedNhds.of_finset_finset`

English:
theorem SeparatedNhds.of_finset_finset
  given: [T2Space X] (s t : Finset X) (h : Disjoint s t)
  proof: .of_isCompact_isCompact s.finite_toSet.isCompact t.finite_toSet.isCompact mod_cast h

中文:
定理 SeparatedNhds.of_finset_finset
  条件: [T2空间 X] (s t : 有限集 X) (h : Disjoint s t)
  证明: .of_isCompact_isCompact s.finite_toSet.isCompact t.finite_toSet.isCompact mod_cast h

Depends on / 依赖: finite_toSet, isCompact, mod_cast, of_isCompact_isCompact, s.finite_toSet.isCompact, t.finite_toSet.isCompact
-/
theorem SeparatedNhds.of_finset_finset [T2Space X] (s t : Finset X) (h : Disjoint s t) :
    SeparatedNhds (s : Set X) t :=
.of_isCompact_isCompact s.finite_toSet.isCompact t.finite_toSet.isCompact mod_cast h

/--
theorem `SeparatedNhds.of_finite` / 定理 `SeparatedNhds.of_finite`

English:
theorem SeparatedNhds.of_finite
  statement: [T2Space X] {s t : Set X} (hs : s.Finite) (ht : t.Finite)
  proof: by
  rw [← hs.coe_toFinset]; rw [← ht.coe_toFinset]
  exact SeparatedNhds.of_finset_finset _ _ (Finite.disjoint_toFinset.2 h)

中文:
定理 SeparatedNhds.of_finite
  结论: [T2空间 X] {s t : 集合 X} (hs : s.有限) (ht : t.有限)
  证明: by
  rw [← hs.coe_toFinset]; rw [← ht.coe_toFinset]
  exact SeparatedNhds.of_finset_finset _ _ (Finite.disjoint_toFinset.2 h)

Depends on / 依赖: Finite, Finite.disjoint_toFinset, SeparatedNhds, SeparatedNhds.of_finset_finset, coe_toFinset, disjoint_toFinset, hs.coe_toFinset, ht.coe_toFinset, of_finset_finset
-/
theorem SeparatedNhds.of_finite [T2Space X] {s t : Set X} (hs : s.Finite) (ht : t.Finite)
    (h : Disjoint s t) : SeparatedNhds s t := by
  rw [← hs.coe_toFinset]; rw [← ht.coe_toFinset]
  exact SeparatedNhds.of_finset_finset _ _ (Finite.disjoint_toFinset.2 h)

/--
theorem `SeparatedNhds.of_singleton_finset` / 定理 `SeparatedNhds.of_singleton_finset`

English:
theorem SeparatedNhds.of_singleton_finset
  given: [T2Space X] {x : X} {s : Finset X} (h : x ∉ s)
  proof: mod_cast .of_finset_finset {x} s (Finset.disjoint_singleton_left.mpr h)

中文:
定理 SeparatedNhds.of_singleton_finset
  条件: [T2空间 X] {x : X} {s : 有限集 X} (h : x ∉ s)
  证明: mod_cast .of_finset_finset {x} s (Finset.disjoint_singleton_left.mpr h)

Depends on / 依赖: Finset, Finset.disjoint_singleton_left.mpr, disjoint_singleton_left, mod_cast, of_finset_finset
-/
theorem SeparatedNhds.of_singleton_finset [T2Space X] {x : X} {s : Finset X} (h : x ∉ s) :
    SeparatedNhds ({x} : Set X) s :=
  mod_cast .of_finset_finset {x} s (Finset.disjoint_singleton_left.mpr h)

end SeparatedFinset

/-- In a `T2Space`, every compact set is closed. -/
@[aesop 50% apply, grind ←, closedness .]
/--
theorem `IsCompact.isClosed` / 定理 `IsCompact.isClosed`

English:
theorem IsCompact.isClosed
  given: [T2Space X] {s : Set X} (hs : IsCompact s)
  statement: IsClosed s
  proof: isClosed_iff_forall_filter.2 fun _x _f _ hfs hfx =>
    let ⟨_y, hy, hfy⟩ := hs.exists_clusterPt hfs
    mem_of_eq_of_mem (eq_of_nhds_neBot (hfy.mono hfx).neBot).symm hy

@[compactness .]

中文:
定理 是紧集.isClosed
  条件: [T2空间 X] {s : 集合 X} (hs : 是紧集 s)
  结论: 是闭集 s
  证明: isClosed_iff_forall_filter.2 fun _x _f _ hfs hfx =>
    let ⟨_y, hy, hfy⟩ := hs.exists_clusterPt hfs
    mem_of_eq_of_mem (eq_of_nhds_neBot (hfy.mono hfx).neBot).symm hy

@[compactness .]

Depends on / 依赖: eq_of_nhds_neBot, exists_clusterPt, hfy.mono, hs.exists_clusterPt, isClosed_iff_forall_filter, mem_of_eq_of_mem
-/
theorem IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsCompact s) : IsClosed s :=
  isClosed_iff_forall_filter.2 fun _x _f _ hfs hfx =>
    let ⟨_y, hy, hfy⟩ := hs.exists_clusterPt hfs
    mem_of_eq_of_mem (eq_of_nhds_neBot (hfy.mono hfx).neBot).symm hy

@[compactness .]
/--
theorem `IsCompact.preimage_continuous` / 定理 `IsCompact.preimage_continuous`

English:
theorem IsCompact.preimage_continuous
  statement: [CompactSpace X] [T2Space Y] {f : X -> Y} {s : Set Y}
  proof: (hs.isClosed.preimage hf).isCompact

中文:
定理 是紧集.preimage_continuous
  结论: [紧空间 X] [T2空间 Y] {f : X -> Y} {s : 集合 Y}
  证明: (hs.isClosed.preimage hf).isCompact

Depends on / 依赖: hs.isClosed.preimage, isClosed, isCompact, preimage
-/
theorem IsCompact.preimage_continuous [CompactSpace X] [T2Space Y] {f : X -> Y} {s : Set Y}
    (hs : IsCompact s) (hf : Continuous f) : IsCompact (f ⁻¹' s) :=
  (hs.isClosed.preimage hf).isCompact

/--
lemma `Pi.isCompact_iff` / 引理 `Pi.isCompact_iff`

English:
lemma Pi.isCompact_iff
  statement: {ι : Type*} {X : ι -> Type*} [forall i, TopologicalSpace (X i)]
  proof: by
  constructor <;> intro H
· exact ⟨H.isClosed, fun i => H.image continuous_apply i⟩
  · exact IsCompact.of_isClosed_subset (isCompact_univ_pi H.2) H.1 (subset_pi_eval_image univ s)

中文:
引理 依赖函数类型.isCompact_iff
  结论: {ι : 类型} {X : ι -> 类型} [对任意 i, 拓扑空间 (X i)]
  证明: by
  constructor <;> intro H
· exact ⟨H.isClosed, fun i => H.image continuous_apply i⟩
  · exact IsCompact.of_isClosed_subset (isCompact_univ_pi H.2) H.1 (subset_pi_eval_image univ s)

Depends on / 依赖: H.image, H.isClosed, IsCompact, IsCompact.of_isClosed_subset, continuous_apply, isClosed, isCompact_univ_pi, of_isClosed_subset, subset_pi_eval_image
-/
lemma Pi.isCompact_iff {ι : Type*} {X : ι -> Type*} [forall i, TopologicalSpace (X i)]
    [forall i, T2Space (X i)] {s : Set (Π i, X i)} :
    IsCompact s ↔ IsClosed s ∧ forall i, IsCompact (eval i '' s) := by
  constructor <;> intro H
· exact ⟨H.isClosed, fun i => H.image continuous_apply i⟩
  · exact IsCompact.of_isClosed_subset (isCompact_univ_pi H.2) H.1 (subset_pi_eval_image univ s)

/--
lemma `Pi.isCompact_closure_iff` / 引理 `Pi.isCompact_closure_iff`

English:
lemma Pi.isCompact_closure_iff
  statement: {ι : Type*} {X : ι -> Type*} [forall i, TopologicalSpace (X i)]
  proof: by
  simp_rw [← exists_isCompact_superset_iff, Pi.exists_compact_superset_iff, image_subset_iff]

中文:
引理 依赖函数类型.isCompact_closure_iff
  结论: {ι : 类型} {X : ι -> 类型} [对任意 i, 拓扑空间 (X i)]
  证明: by
  simp_rw [← exists_isCompact_superset_iff, Pi.exists_compact_superset_iff, image_subset_iff]

Depends on / 依赖: Pi.exists_compact_superset_iff, exists_compact_superset_iff, exists_isCompact_superset_iff, image_subset_iff, simp_rw
-/
lemma Pi.isCompact_closure_iff {ι : Type*} {X : ι -> Type*} [forall i, TopologicalSpace (X i)]
    [forall i, R1Space (X i)] {s : Set (Π i, X i)} :
    IsCompact (closure s) ↔ forall i, IsCompact (closure <| eval i '' s) := by
  simp_rw [← exists_isCompact_superset_iff, Pi.exists_compact_superset_iff, image_subset_iff]

/--
theorem `exists_subset_nhds_of_isCompact` / 定理 `exists_subset_nhds_of_isCompact`

English:
theorem exists_subset_nhds_of_isCompact
  statement: [T2Space X] {ι : Type*} [Nonempty ι] {V : ι -> Set X}
  proof: exists_subset_nhds_of_isCompact' hV hV_cpct (fun i => (hV_cpct i).isClosed) hU

中文:
定理 存在_subset_nhds_of_isCompact
  结论: [T2空间 X] {ι : 类型} [非空 ι] {V : ι -> 集合 X}
  证明: exists_subset_nhds_of_isCompact' hV hV_cpct (fun i => (hV_cpct i).isClosed) hU

Depends on / 依赖: exists_subset_nhds_of_isCompact, hV_cpct, isClosed
-/
theorem exists_subset_nhds_of_isCompact [T2Space X] {ι : Type*} [Nonempty ι] {V : ι -> Set X}
    (hV : Directed (· ⊇ ·) V) (hV_cpct : forall i, IsCompact (V i)) {U : Set X}
    (hU : forall x in ⋂ i, V i, U in 𝓝 x) : exists i, V i subseteq U :=
  exists_subset_nhds_of_isCompact' hV hV_cpct (fun i => (hV_cpct i).isClosed) hU

/--
theorem `CompactExhaustion.isClosed` / 定理 `CompactExhaustion.isClosed`

English:
theorem CompactExhaustion.isClosed
  given: [T2Space X] (K : CompactExhaustion X) (n : Nat)
  statement: IsClosed (K n)
  proof: (K.isCompact n).isClosed

@[compactness .]

中文:
定理 余mpactExhaustion.isClosed
  条件: [T2空间 X] (K : 余mpactExhaustion X) (n : 自然数)
  结论: 是闭集 (K n)
  证明: (K.isCompact n).isClosed

@[compactness .]

Depends on / 依赖: K.isCompact, isClosed, isCompact
-/
theorem CompactExhaustion.isClosed [T2Space X] (K : CompactExhaustion X) (n : Nat) : IsClosed (K n) :=
  (K.isCompact n).isClosed

@[compactness .]
/--
theorem `IsCompact.inter` / 定理 `IsCompact.inter`

English:
theorem IsCompact.inter
  given: [T2Space X] {s t : Set X} (hs : IsCompact s) (ht : IsCompact t)
  proof: hs.inter_right ht.isClosed

中文:
定理 是紧集.inter
  条件: [T2空间 X] {s t : 集合 X} (hs : 是紧集 s) (ht : 是紧集 t)
  证明: hs.inter_right ht.isClosed

Depends on / 依赖: hs.inter_right, ht.isClosed, inter_right, isClosed
-/
theorem IsCompact.inter [T2Space X] {s t : Set X} (hs : IsCompact s) (ht : IsCompact t) :
    IsCompact (s inter t) :=
hs.inter_right ht.isClosed

/--
theorem `image_closure_of_isCompact` / 定理 `image_closure_of_isCompact`

English:
theorem image_closure_of_isCompact
  statement: [T2Space Y] {s : Set X} (hs : IsCompact (closure s)) {f : X -> Y}
  proof: Subset.antisymm hf.image_closure
    closure_minimal (image_mono subset_closure) (hs.image_of_continuousOn hf).isClosed

中文:
定理 image_closure_of_isCompact
  结论: [T2空间 Y] {s : 集合 X} (hs : 是紧集 (closure s)) {f : X -> Y}
  证明: Subset.antisymm hf.image_closure
    closure_minimal (image_mono subset_closure) (hs.image_of_continuousOn hf).isClosed

Depends on / 依赖: Subset, Subset.antisymm, antisymm, closure_minimal, hf.image_closure, hs.image_of_continuousOn, image_closure, image_mono, image_of_continuousOn, isClosed, subset_closure
-/
theorem image_closure_of_isCompact [T2Space Y] {s : Set X} (hs : IsCompact (closure s)) {f : X -> Y}
    (hf : ContinuousOn f (closure s)) : f '' closure s = closure (f '' s) :=
Subset.antisymm hf.image_closure
    closure_minimal (image_mono subset_closure) (hs.image_of_continuousOn hf).isClosed

/--
theorem `ContinuousAt.ne_iff_eventually_ne` / 定理 `ContinuousAt.ne_iff_eventually_ne`

English:
theorem ContinuousAt.ne_iff_eventually_ne
  statement: [T2Space Y] {x : X} {f g : X -> Y}
  proof: by
  constructor <;> intro hfg
  · obtain ⟨Uf, Ug, h₁U, h₂U, h₃U, h₄U, h₅U⟩ := t2_separation hfg
    rw [Set.disjoint_iff_inter_eq_empty] at h₅U
    filter_upwards [inter_mem
      (hf.preimage_mem_nhds (IsOpen.mem_nhds h₁U h₃U))
      (hg.preimage_mem_nhds (IsOpen.mem_nhds h₂U h₄U))]
    intro x hx
    simp only [Set.mem_inter_iff, Set.mem_preimage] at hx
    by_contra H
    rw [H] at hx
    have : g x in Uf inter Ug := hx
    simp [h₅U] at this
  · obtain ⟨t, h₁t, h₂t, h₃t⟩ := eventually_nhds_iff.1 hfg
    exact h₁t x h₃t

中文:
定理 ContinuousAt.ne_iff_eventually_ne
  结论: [T2空间 Y] {x : X} {f g : X -> Y}
  证明: by
  constructor <;> intro hfg
  · obtain ⟨Uf, Ug, h₁U, h₂U, h₃U, h₄U, h₅U⟩ := t2_separation hfg
    rw [Set.disjoint_iff_inter_eq_empty] at h₅U
    filter_upwards [inter_mem
      (hf.preimage_mem_nhds (IsOpen.mem_nhds h₁U h₃U))
      (hg.preimage_mem_nhds (IsOpen.mem_nhds h₂U h₄U))]
    intro x hx
    simp only [Set.mem_inter_iff, Set.mem_preimage] at hx
    by_contra H
    rw [H] at hx
    have : g x in Uf inter Ug := hx
    simp [h₅U] at this
  · obtain ⟨t, h₁t, h₂t, h₃t⟩ := eventually_nhds_iff.1 hfg
    exact h₁t x h₃t

Depends on / 依赖: IsOpen, IsOpen.mem_nhds, Set.disjoint_iff_inter_eq_empty, Set.mem_inter_iff, Set.mem_preimage, disjoint_iff_inter_eq_empty, eventually_nhds_iff, filter_upwards, hf.preimage_mem_nhds, hg.preimage_mem_nhds, inter_mem, mem_inter_iff, mem_nhds, mem_preimage, preimage_mem_nhds, t2_separation
-/
theorem ContinuousAt.ne_iff_eventually_ne [T2Space Y] {x : X} {f g : X -> Y}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    f x != g x ↔ forallᶠ x in 𝓝 x, f x != g x := by
  constructor <;> intro hfg
  · obtain ⟨Uf, Ug, h₁U, h₂U, h₃U, h₄U, h₅U⟩ := t2_separation hfg
    rw [Set.disjoint_iff_inter_eq_empty] at h₅U
    filter_upwards [inter_mem
      (hf.preimage_mem_nhds (IsOpen.mem_nhds h₁U h₃U))
      (hg.preimage_mem_nhds (IsOpen.mem_nhds h₂U h₄U))]
    intro x hx
    simp only [Set.mem_inter_iff, Set.mem_preimage] at hx
    by_contra H
    rw [H] at hx
    have : g x in Uf inter Ug := hx
    simp [h₅U] at this
  · obtain ⟨t, h₁t, h₂t, h₃t⟩ := eventually_nhds_iff.1 hfg
    exact h₁t x h₃t

/--
theorem `ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE` / 定理 `ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE`

English:
theorem ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
  statement: [T2Space Y] {x : X} {f g : X -> Y}
  proof: by
  constructor <;> intro hfg
  · apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE hfg
    by_contra hCon
    obtain ⟨a, ha⟩ : {x | f x != g x ∧ f x = g x}.Nonempty := by
      have h₁ := (eventually_nhdsWithin_of_eventually_nhds
        ((hf.ne_iff_eventually_ne hg).1 hCon)).and hfg
      have h₂ : ∅ ∉ 𝓝[!=] x := by exact empty_notMem (𝓝[!=] x)
      simp_all
    simp at ha
  · exact hfg.filter_mono nhdsWithin_le_nhds

中文:
定理 ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
  结论: [T2空间 Y] {x : X} {f g : X -> Y}
  证明: by
  constructor <;> intro hfg
  · apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE hfg
    by_contra hCon
    obtain ⟨a, ha⟩ : {x | f x != g x ∧ f x = g x}.Nonempty := by
      have h₁ := (eventually_nhdsWithin_of_eventually_nhds
        ((hf.ne_iff_eventually_ne hg).1 hCon)).and hfg
      have h₂ : ∅ ∉ 𝓝[!=] x := by exact empty_notMem (𝓝[!=] x)
      simp_all
    simp at ha
  · exact hfg.filter_mono nhdsWithin_le_nhds

Depends on / 依赖: Nonempty, empty_notMem, eventuallyEq_nhds_of_eventuallyEq_nhdsNE, eventually_nhdsWithin_of_eventually_nhds, filter_mono, hf.ne_iff_eventually_ne, hfg.filter_mono, ne_iff_eventually_ne, nhdsWithin_le_nhds
-/
theorem ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE [T2Space Y] {x : X} {f g : X -> Y}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) [(𝓝[!=] x).NeBot] :
    f =ᶠ[𝓝[!=] x] g ↔ f =ᶠ[𝓝 x] g := by
  constructor <;> intro hfg
  · apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE hfg
    by_contra hCon
    obtain ⟨a, ha⟩ : {x | f x != g x ∧ f x = g x}.Nonempty := by
      have h₁ := (eventually_nhdsWithin_of_eventually_nhds
        ((hf.ne_iff_eventually_ne hg).1 hCon)).and hfg
      have h₂ : ∅ ∉ 𝓝[!=] x := by exact empty_notMem (𝓝[!=] x)
      simp_all
    simp at ha
  · exact hfg.filter_mono nhdsWithin_le_nhds

/--
theorem `Continuous.isClosedMap` / 定理 `Continuous.isClosedMap`

English:
theorem Continuous.isClosedMap
  statement: [CompactSpace X] [T2Space Y] {f : X -> Y}
  proof: fun _s hs => (hs.isCompact.image h).isClosed

中文:
定理 连续.isClosedMap
  结论: [紧空间 X] [T2空间 Y] {f : X -> Y}
  证明: fun _s hs => (hs.isCompact.image h).isClosed
-/
protected theorem Continuous.isClosedMap [CompactSpace X] [T2Space Y] {f : X -> Y}
    (h : Continuous f) : IsClosedMap f := fun _s hs => (hs.isCompact.image h).isClosed

/--
theorem `Continuous.isClosedEmbedding` / 定理 `Continuous.isClosedEmbedding`

English:
theorem Continuous.isClosedEmbedding
  statement: [CompactSpace X] [T2Space Y] {f : X -> Y} (h : Continuous f)
  proof: .of_continuous_injective_isClosedMap h hf h.isClosedMap

中文:
定理 连续.isClosedEmbedding
  结论: [紧空间 X] [T2空间 Y] {f : X -> Y} (h : 连续 f)
  证明: .of_continuous_injective_isClosedMap h hf h.isClosedMap

Depends on / 依赖: h.isClosedMap, isClosedMap, of_continuous_injective_isClosedMap
-/
theorem Continuous.isClosedEmbedding [CompactSpace X] [T2Space Y] {f : X -> Y} (h : Continuous f)
    (hf : Function.Injective f) : IsClosedEmbedding f :=
  .of_continuous_injective_isClosedMap h hf h.isClosedMap

/--
theorem `Topology.IsQuotientMap.of_surjective_continuous` / 定理 `Topology.IsQuotientMap.of_surjective_continuous`

English:
theorem Topology.IsQuotientMap.of_surjective_continuous
  statement: [CompactSpace X] [T2Space Y] {f : X -> Y}
  proof: hcont.isClosedMap.isQuotientMap hcont hsurj

中文:
定理 拓扑.是商映射.of_surjective_continuous
  结论: [紧空间 X] [T2空间 Y] {f : X -> Y}
  证明: hcont.isClosedMap.isQuotientMap hcont hsurj

Depends on / 依赖: hcont.isClosedMap.isQuotientMap, isClosedMap, isQuotientMap
-/
theorem Topology.IsQuotientMap.of_surjective_continuous [CompactSpace X] [T2Space Y] {f : X -> Y}
    (hsurj : Surjective f) (hcont : Continuous f) : IsQuotientMap f :=
  hcont.isClosedMap.isQuotientMap hcont hsurj

/--
theorem `isPreirreducible_iff_forall_mem_subset_closure_singleton` / 定理 `isPreirreducible_iff_forall_mem_subset_closure_singleton`

English:
theorem isPreirreducible_iff_forall_mem_subset_closure_singleton
  given: [R1Space X] {S : Set X}
  proof: by
  constructor
  · intro h x hx y hy
    by_contra e
    obtain ⟨U, V, hU, hV, hxU, hyV, h'⟩ := r1_separation fun h => e h.specializes.mem_closure
    exact ((h U V hU hV ⟨x, hx, hxU⟩ ⟨y, hy, hyV⟩).mono inter_subset_right).not_disjoint h'
  · intro h u v hu hv ⟨x, hxs, hxu⟩ ⟨y, hys, hyv⟩
    exact ⟨x, hxs, hxu, (specializes_iff_mem_closure.mpr (h x hxs hys)).mem_open hv hyv⟩

中文:
定理 isPreirreducible_iff_对任意_mem_subset_closure_singleton
  条件: [R1空间 X] {S : 集合 X}
  证明: by
  constructor
  · intro h x hx y hy
    by_contra e
    obtain ⟨U, V, hU, hV, hxU, hyV, h'⟩ := r1_separation fun h => e h.specializes.mem_closure
    exact ((h U V hU hV ⟨x, hx, hxU⟩ ⟨y, hy, hyV⟩).mono inter_subset_right).not_disjoint h'
  · intro h u v hu hv ⟨x, hxs, hxu⟩ ⟨y, hys, hyv⟩
    exact ⟨x, hxs, hxu, (specializes_iff_mem_closure.mpr (h x hxs hys)).mem_open hv hyv⟩

Depends on / 依赖: h.specializes.mem_closure, inter_subset_right, mem_closure, mem_open, not_disjoint, r1_separation, specializes, specializes_iff_mem_closure, specializes_iff_mem_closure.mpr
-/
theorem isPreirreducible_iff_forall_mem_subset_closure_singleton [R1Space X] {S : Set X} :
    IsPreirreducible S ↔ forall x in S, S subseteq closure {x} := by
  constructor
  · intro h x hx y hy
    by_contra e
    obtain ⟨U, V, hU, hV, hxU, hyV, h'⟩ := r1_separation fun h => e h.specializes.mem_closure
    exact ((h U V hU hV ⟨x, hx, hxU⟩ ⟨y, hy, hyV⟩).mono inter_subset_right).not_disjoint h'
  · intro h u v hu hv ⟨x, hxs, hxu⟩ ⟨y, hys, hyv⟩
    exact ⟨x, hxs, hxu, (specializes_iff_mem_closure.mpr (h x hxs hys)).mem_open hv hyv⟩

/--
theorem `isPreirreducible_iff_subsingleton` / 定理 `isPreirreducible_iff_subsingleton`

English:
theorem isPreirreducible_iff_subsingleton
  given: [T2Space X] {S : Set X}
  proof: by
  simp [isPreirreducible_iff_forall_mem_subset_closure_singleton, Set.Subsingleton, eq_comm]

中文:
定理 isPreirreducible_iff_subsingleton
  条件: [T2空间 X] {S : 集合 X}
  证明: by
  simp [isPreirreducible_iff_forall_mem_subset_closure_singleton, Set.Subsingleton, eq_comm]

Depends on / 依赖: Set.Subsingleton, Subsingleton, eq_comm, isPreirreducible_iff_forall_mem_subset_closure_singleton
-/
theorem isPreirreducible_iff_subsingleton [T2Space X] {S : Set X} :
    IsPreirreducible S ↔ S.Subsingleton := by
  simp [isPreirreducible_iff_forall_mem_subset_closure_singleton, Set.Subsingleton, eq_comm]

-- todo: use `alias` + `attribute [protected]` once we get `attribute [protected]`
/--
lemma `IsPreirreducible.subsingleton` / 引理 `IsPreirreducible.subsingleton`

English:
lemma IsPreirreducible.subsingleton
  given: [T2Space X] {S : Set X} (h : IsPreirreducible S)
  proof: isPreirreducible_iff_subsingleton.1 h

中文:
引理 IsPreirreducible.subsingleton
  条件: [T2空间 X] {S : 集合 X} (h : IsPreirreducible S)
  证明: isPreirreducible_iff_subsingleton.1 h
-/
protected lemma IsPreirreducible.subsingleton [T2Space X] {S : Set X} (h : IsPreirreducible S) :
    S.Subsingleton :=
  isPreirreducible_iff_subsingleton.1 h

/--
theorem `isIrreducible_iff_singleton` / 定理 `isIrreducible_iff_singleton`

English:
theorem isIrreducible_iff_singleton
  given: [T2Space X] {S : Set X}
  statement: IsIrreducible S ↔ exists x, S = {x}
  proof: by
  rw [IsIrreducible]; rw [isPreirreducible_iff_subsingleton]; rw [exists_eq_singleton_iff_nonempty_subsingleton]

中文:
定理 isIrreducible_iff_singleton
  条件: [T2空间 X] {S : 集合 X}
  结论: 是不可约 S ↔ 存在 x, S = {x}
  证明: by
  rw [IsIrreducible]; rw [isPreirreducible_iff_subsingleton]; rw [exists_eq_singleton_iff_nonempty_subsingleton]

Depends on / 依赖: IsIrreducible, exists_eq_singleton_iff_nonempty_subsingleton, isPreirreducible_iff_subsingleton
-/
theorem isIrreducible_iff_singleton [T2Space X] {S : Set X} : IsIrreducible S ↔ exists x, S = {x} := by
  rw [IsIrreducible]; rw [isPreirreducible_iff_subsingleton]; rw [exists_eq_singleton_iff_nonempty_subsingleton]

/--
theorem `not_preirreducible_nontrivial_t2` / 定理 `not_preirreducible_nontrivial_t2`

English:
theorem not_preirreducible_nontrivial_t2
  statement: (X) [TopologicalSpace X] [PreirreducibleSpace X]
  proof: (PreirreducibleSpace.isPreirreducible_univ (X := X)).subsingleton.not_nontrivial nontrivial_univ

中文:
定理 not_preirreducible_nontrivial_t2
  结论: (X) [拓扑空间 X] [Preirreducible空间 X]
  证明: (PreirreducibleSpace.isPreirreducible_univ (X := X)).subsingleton.not_nontrivial nontrivial_univ

Depends on / 依赖: PreirreducibleSpace, PreirreducibleSpace.isPreirreducible_univ, isPreirreducible_univ, nontrivial_univ, not_nontrivial, subsingleton, subsingleton.not_nontrivial
-/
theorem not_preirreducible_nontrivial_t2 (X) [TopologicalSpace X] [PreirreducibleSpace X]
    [Nontrivial X] [T2Space X] : False :=
  (PreirreducibleSpace.isPreirreducible_univ (X := X)).subsingleton.not_nontrivial nontrivial_univ

/--
theorem `t2Space_antitone` / 定理 `t2Space_antitone`

English:
theorem t2Space_antitone
  given: {X : Type*}
  statement: Antitone (@T2Space X)
  proof: fun inst₁ inst₂ h_top h_t2 => @T2Space.of_injective_continuous _ _ inst₁ inst₂
h_t2 _ Function.injective_id continuous_id_of_le h_top

中文:
定理 t2Space_antitone
  条件: {X : 类型}
  结论: 递减 (@T2空间 X)
  证明: fun inst₁ inst₂ h_top h_t2 => @T2Space.of_injective_continuous _ _ inst₁ inst₂
h_t2 _ Function.injective_id continuous_id_of_le h_top

Depends on / 依赖: Function, Function.injective_id, T2Space, T2Space.of_injective_continuous, continuous_id_of_le, h_t2, h_top, injective_id, of_injective_continuous
-/
theorem t2Space_antitone {X : Type*} : Antitone (@T2Space X) :=
  fun inst₁ inst₂ h_top h_t2 => @T2Space.of_injective_continuous _ _ inst₁ inst₂
h_t2 _ Function.injective_id continuous_id_of_le h_top

end Separation
