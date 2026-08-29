/-
Copyright (c) 2025 Floris van Doorn and Hannah Scholz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Hannah Scholz
-/
module

public import Mathlib.Topology.CWComplex.Classical.Basic

/-!
# Finiteness notions on CW complexes

In this file we define what it means for a CW complex to be finite dimensional, of finite type or
finite. We define constructors with relaxed conditions for CW complexes of finite type and
finite CW complexes.

## Main definitions
* `RelCWComplex.FiniteDimensional`: a CW complex is finite dimensional if it has only finitely many
  nonempty indexing types for the cells.
* `RelCWComplex.FiniteType`: a CW complex is of finite type if it has only finitely many cells in
  each dimension.
* `RelCWComplex.Finite`: a CW complex is finite if it is finite dimensional and of finite type.

## Main statements
* `RelCWComplex.mkFiniteType`: if we want to construct a CW complex of finite type, we can relax the
  condition `mapsTo`.
* `RelCWComplex.mkFinite`: if we want to construct a finite CW complex, we can relax the condition
  `mapsTo` and can leave out the condition `closed'`.
* `RelCWComplex.finite_iff_finite_cells`: a CW complex is finite iff the total number of its cells
  is finite.
-/

@[expose] public section

open Metric Set

namespace Topology

/--
Definition of `RelCWComplex.FiniteDimensional.` / `RelCWComplex.FiniteDimensional.` 的定义

English:
class RelCWComplex.FiniteDimensional.{u}
  parameters: {X : Type u} [TopologicalSpace X] (C : Set X) {D : Set X}
  axioms and operations (1):
    - eventually_isEmpty_cell : forallᶠ n in Filter.atTop, IsEmpty (cell C n)

中文:
类 RelCWComplex.有限维.{u}
  参数: {X : 类型u} [拓扑空间 X] (C : 集合 X) {D : 集合 X}
  公理与运算 (1 个):
    - eventually_isEmpty_cell : 对任意ᶠ n in 滤子.atTop, 是空 (cell C n)

Depends on / 依赖: FiniteDimensional, RelCWComplex, RelCWComplex.FiniteDimensional.eventually_isEmpty_cell, eventually_isEmpty_cell
-/
class RelCWComplex.FiniteDimensional.{u} {X : Type u} [TopologicalSpace X] (C : Set X) {D : Set X}
    [RelCWComplex C D] : Prop where
  /-- For some natural number `n`, the type `cell C m` is empty for all `m ≥ n`. -/
  eventually_isEmpty_cell : forallᶠ n in Filter.atTop, IsEmpty (cell C n)

alias CWComplex.FiniteDimensional.eventually_isEmpty_cell :=
  RelCWComplex.FiniteDimensional.eventually_isEmpty_cell

/--
Definition of `RelCWComplex.FiniteType.` / `RelCWComplex.FiniteType.` 的定义

English:
class RelCWComplex.FiniteType.{u}
  parameters: {X : Type u} [TopologicalSpace X] (C : Set X) {D : Set X}
  axioms and operations (1):
    - finite_cell((n : Nat)) : Finite (cell C n)

中文:
类 RelCWComplex.有限型.{u}
  参数: {X : 类型u} [拓扑空间 X] (C : 集合 X) {D : 集合 X}
  公理与运算 (1 个):
    - finite_cell((n : 自然数)) : 有限 (cell C n)

Depends on / 依赖: FiniteType, RelCWComplex, RelCWComplex.FiniteType.finite_cell, finite_cell
-/
class RelCWComplex.FiniteType.{u} {X : Type u} [TopologicalSpace X] (C : Set X) {D : Set X}
    [RelCWComplex C D] : Prop where
  /-- `cell C n` is finite for every `n`. -/
  finite_cell (n : Nat) : Finite (cell C n)

alias CWComplex.FiniteType.finite_cell := RelCWComplex.FiniteType.finite_cell

/--
Definition of `RelCWComplex.Finite` / `RelCWComplex.Finite` 的定义

English:
class RelCWComplex.Finite
  parameters: {X : Type*} [TopologicalSpace X] (C : Set X) {D : Set X}
  extends: FiniteDimensional C, FiniteType C
  (no additional axioms)

中文:
类 RelCWComplex.有限
  参数: {X : 类型} [拓扑空间 X] (C : 集合 X) {D : 集合 X}
  继承: 有限维 C, 有限型 C
  (无附加公理)
-/
class RelCWComplex.Finite {X : Type*} [TopologicalSpace X] (C : Set X) {D : Set X}
    [RelCWComplex C D] extends FiniteDimensional C, FiniteType C

variable {X : Type*} [TopologicalSpace X] (C : Set X) {D : Set X} [RelCWComplex C D]

@[alias_in CWComplex]
/--
lemma `RelCWComplex.finite_of_finiteDimensional_finiteType` / 引理 `RelCWComplex.finite_of_finiteDimensional_finiteType`

English:
lemma RelCWComplex.finite_of_finiteDimensional_finiteType
  statement: [FiniteDimensional C]
  proof: FiniteDimensional.eventually_isEmpty_cell
  finite_cell n := FiniteType.finite_cell n

中文:
引理 RelCWComplex.finite_of_finiteDimensional_finiteType
  结论: [有限维 C]
  证明: FiniteDimensional.eventually_isEmpty_cell
  finite_cell n := FiniteType.finite_cell n

Depends on / 依赖: FiniteDimensional, FiniteDimensional.eventually_isEmpty_cell, eventually_isEmpty_cell
-/
lemma RelCWComplex.finite_of_finiteDimensional_finiteType [FiniteDimensional C]
    [FiniteType C] : Finite C where
  eventually_isEmpty_cell := FiniteDimensional.eventually_isEmpty_cell
  finite_cell n := FiniteType.finite_cell n

namespace CWComplex

export RelCWComplex (FiniteDimensional FiniteType Finite)

end CWComplex

/-- If we want to construct a relative CW complex of finite type, we can add the condition
`finite_cell` and relax the condition `mapsTo`. -/
@[simps -isSimp, instance_reducible]
/--
Definition of `RelCWComplex.mkFiniteType.` / `RelCWComplex.mkFiniteType.` 的定义

English:
definition RelCWComplex.mkFiniteType.{u}
  signature: {X : Type u} [TopologicalSpace X] (C : Set X)
  body: cell
  map := map
  source_eq := source_eq
  continuousOn := continuousOn
  continuousOn_symm := continuousOn_symm
  pairwiseDisjoint' := pairwiseDisjoint'
  disjointBase' := disjointBase'
  mapsTo n i := by
    use fun m => finite_univ.toFinset (s := (univ : Set (cell m)))
    simp only [Finite.mem_toFinset, mem_univ, iUnion_true]
    exact mapsTo n i
  closed' := closed'
  isClosedBase := isClosedBase
  union' := union'

中文:
定义 RelCWComplex.mkFiniteType.{u}
  签名: {X : 类型u} [拓扑空间 X] (C : 集合 X)
  定义体: cell
  map := map
  source_eq := source_eq
  continuousOn := continuousOn
  continuousOn_symm := continuousOn_symm
  pairwiseDisjoint' := pairwiseDisjoint'
  disjointBase' := disjointBase'
  mapsTo n i := by
    use fun m => finite_univ.toFinset (s := (univ : Set (cell m)))
    simp only [Finite.mem_toFinset, mem_univ, iUnion_true]
    exact mapsTo n i
  closed' := closed'
  isClosedBase := isClosedBase
  union' := union'
-/
def RelCWComplex.mkFiniteType.{u} {X : Type u} [TopologicalSpace X] (C : Set X)
    (D : outParam (Set X))
    (cell : (n : Nat) -> Type u) (map : (n : Nat) -> (i : cell n) -> PartialEquiv (Fin n -> Real) X)
    (finite_cell : forall (n : Nat), _root_.Finite (cell n))
    (source_eq : forall (n : Nat) (i : cell n), (map n i).source = ball 0 1)
    (continuousOn : forall (n : Nat) (i : cell n), ContinuousOn (map n i) (closedBall 0 1))
    (continuousOn_symm : forall (n : Nat) (i : cell n), ContinuousOn (map n i).symm (map n i).target)
    (pairwiseDisjoint' :
      (univ : Set (Σ n, cell n)).PairwiseDisjoint (fun ni => map ni.1 ni.2 '' ball 0 1))
    (disjointBase' : forall (n : Nat) (i : cell n), Disjoint (map n i '' ball 0 1) D)
    (mapsTo : forall (n : Nat) (i : cell n),
      MapsTo (map n i) (sphere 0 1) (D union ⋃ (m < n) (j : cell m), map m j '' closedBall 0 1))
    (closed' : forall (A : Set X) (_ : A subseteq C),
      ((forall n j, IsClosed (A inter map n j '' closedBall 0 1)) ∧ IsClosed (A inter D)) -> IsClosed A)
    (isClosedBase : IsClosed D)
    (union' : D union ⋃ (n : Nat) (j : cell n), map n j '' closedBall 0 1 = C) :
    RelCWComplex C D where
  cell := cell
  map := map
  source_eq := source_eq
  continuousOn := continuousOn
  continuousOn_symm := continuousOn_symm
  pairwiseDisjoint' := pairwiseDisjoint'
  disjointBase' := disjointBase'
  mapsTo n i := by
    use fun m => finite_univ.toFinset (s := (univ : Set (cell m)))
    simp only [Finite.mem_toFinset, mem_univ, iUnion_true]
    exact mapsTo n i
  closed' := closed'
  isClosedBase := isClosedBase
  union' := union'

/--
lemma `RelCWComplex.finiteType_mkFiniteType.` / 引理 `RelCWComplex.finiteType_mkFiniteType.`

English:
lemma RelCWComplex.finiteType_mkFiniteType.{u}
  statement: {X : Type u} [TopologicalSpace X] (C : Set X)
  proof: mkFiniteType C D cell map finite_cell source_eq continuousOn continuousOn_symm
      pairwiseDisjoint' disjointBase' mapsTo closed' isClosedBase union'
    FiniteType C :=
  letI := mkFiniteType C D cell map finite_cell source_eq continuousOn continuousOn_symm
      pairwiseDisjoint' disjointBase' mapsTo closed' isClosedBase union'
  { finite_cell := finite_cell }

中文:
引理 RelCWComplex.finiteType_mkFiniteType.{u}
  结论: {X : 类型u} [拓扑空间 X] (C : 集合 X)
  证明: mkFiniteType C D cell map finite_cell source_eq continuousOn continuousOn_symm
      pairwiseDisjoint' disjointBase' mapsTo closed' isClosedBase union'
    FiniteType C :=
  letI := mkFiniteType C D cell map finite_cell source_eq continuousOn continuousOn_symm
      pairwiseDisjoint' disjointBase' mapsTo closed' isClosedBase union'
  { finite_cell := finite_cell }

Depends on / 依赖: continuousOn, continuousOn_symm, finite_cell, mkFiniteType, source_eq
-/
lemma RelCWComplex.finiteType_mkFiniteType.{u} {X : Type u} [TopologicalSpace X] (C : Set X)
    (D : outParam (Set X))
    (cell : (n : Nat) -> Type u) (map : (n : Nat) -> (i : cell n) -> PartialEquiv (Fin n -> Real) X)
    (finite_cell : forall (n : Nat), _root_.Finite (cell n))
    (source_eq : forall (n : Nat) (i : cell n), (map n i).source = ball 0 1)
    (continuousOn : forall (n : Nat) (i : cell n), ContinuousOn (map n i) (closedBall 0 1))
    (continuousOn_symm : forall (n : Nat) (i : cell n), ContinuousOn (map n i).symm (map n i).target)
    (pairwiseDisjoint' :
      (univ : Set (Σ n, cell n)).PairwiseDisjoint (fun ni => map ni.1 ni.2 '' ball 0 1))
    (disjointBase' : forall (n : Nat) (i : cell n), Disjoint (map n i '' ball 0 1) D)
    (mapsTo : forall (n : Nat) (i : cell n),
      MapsTo (map n i) (sphere 0 1) (D union ⋃ (m < n) (j : cell m), map m j '' closedBall 0 1))
    (closed' : forall (A : Set X) (_ : A subseteq C),
      ((forall n j, IsClosed (A inter map n j '' closedBall 0 1)) ∧ IsClosed (A inter D)) -> IsClosed A)
    (isClosedBase : IsClosed D)
    (union' : D union ⋃ (n : Nat) (j : cell n), map n j '' closedBall 0 1 = C) :
    letI := mkFiniteType C D cell map finite_cell source_eq continuousOn continuousOn_symm
      pairwiseDisjoint' disjointBase' mapsTo closed' isClosedBase union'
    FiniteType C :=
  letI := mkFiniteType C D cell map finite_cell source_eq continuousOn continuousOn_symm
      pairwiseDisjoint' disjointBase' mapsTo closed' isClosedBase union'
  { finite_cell := finite_cell }

/-- If we want to construct a CW complex of finite type, we can add the condition `finite_cell` and
relax the condition `mapsTo`. -/
@[simps -isSimp, instance_reducible]
/--
Definition of `CWComplex.mkFiniteType.` / `CWComplex.mkFiniteType.` 的定义

English:
definition CWComplex.mkFiniteType.{u}
  signature: {X : Type u} [TopologicalSpace X] (C : Set X)
  body: cell
  map := map
  source_eq := source_eq
  continuousOn := continuousOn
  continuousOn_symm := continuousOn_symm
  pairwiseDisjoint' := pairwiseDisjoint'
  mapsTo' n i := by
    use fun m => finite_univ.toFinset (s := (univ : Set (cell m)))
    simp only [Finite.mem_toFinset, mem_univ, iUnion_true]
    exact mapsTo n i
  closed' := closed'
  union' := union'

中文:
定义 CWComplex.mkFiniteType.{u}
  签名: {X : 类型u} [拓扑空间 X] (C : 集合 X)
  定义体: cell
  map := map
  source_eq := source_eq
  continuousOn := continuousOn
  continuousOn_symm := continuousOn_symm
  pairwiseDisjoint' := pairwiseDisjoint'
  mapsTo' n i := by
    use fun m => finite_univ.toFinset (s := (univ : Set (cell m)))
    simp only [Finite.mem_toFinset, mem_univ, iUnion_true]
    exact mapsTo n i
  closed' := closed'
  union' := union'
-/
def CWComplex.mkFiniteType.{u} {X : Type u} [TopologicalSpace X] (C : Set X)
    (cell : (n : Nat) -> Type u) (map : (n : Nat) -> (i : cell n) -> PartialEquiv (Fin n -> Real) X)
    (finite_cell : forall (n : Nat), _root_.Finite (cell n))
    (source_eq : forall (n : Nat) (i : cell n), (map n i).source = ball 0 1)
    (continuousOn : forall (n : Nat) (i : cell n), ContinuousOn (map n i) (closedBall 0 1))
    (continuousOn_symm : forall (n : Nat) (i : cell n), ContinuousOn (map n i).symm (map n i).target)
    (pairwiseDisjoint' :
      (univ : Set (Σ n, cell n)).PairwiseDisjoint (fun ni => map ni.1 ni.2 '' ball 0 1))
    (mapsTo : forall (n : Nat) (i : cell n),
      MapsTo (map n i) (sphere 0 1) (⋃ (m < n) (j : cell m), map m j '' closedBall 0 1))
    (closed' : forall (A : Set X) (_ : A subseteq C),
    (forall n j, IsClosed (A inter map n j '' closedBall 0 1)) -> IsClosed A)
    (union' : ⋃ (n : Nat) (j : cell n), map n j '' closedBall 0 1 = C) :
    CWComplex C where
  cell := cell
  map := map
  source_eq := source_eq
  continuousOn := continuousOn
  continuousOn_symm := continuousOn_symm
  pairwiseDisjoint' := pairwiseDisjoint'
  mapsTo' n i := by
    use fun m => finite_univ.toFinset (s := (univ : Set (cell m)))
    simp only [Finite.mem_toFinset, mem_univ, iUnion_true]
    exact mapsTo n i
  closed' := closed'
  union' := union'

/--
lemma `CWComplex.finiteType_mkFiniteType.` / 引理 `CWComplex.finiteType_mkFiniteType.`

English:
lemma CWComplex.finiteType_mkFiniteType.{u}
  statement: {X : Type u} [TopologicalSpace X] (C : Set X)
  proof: mkFiniteType C cell map finite_cell source_eq continuousOn continuousOn_symm
      pairwiseDisjoint' mapsTo closed' union'
    FiniteType C :=
  letI := mkFiniteType C cell map finite_cell source_eq continuousOn continuousOn_symm
      pairwiseDisjoint' mapsTo closed' union'
  { finite_cell := finite_cell }

中文:
引理 CWComplex.finiteType_mkFiniteType.{u}
  结论: {X : 类型u} [拓扑空间 X] (C : 集合 X)
  证明: mkFiniteType C cell map finite_cell source_eq continuousOn continuousOn_symm
      pairwiseDisjoint' mapsTo closed' union'
    FiniteType C :=
  letI := mkFiniteType C cell map finite_cell source_eq continuousOn continuousOn_symm
      pairwiseDisjoint' mapsTo closed' union'
  { finite_cell := finite_cell }

Depends on / 依赖: continuousOn, continuousOn_symm, finite_cell, mkFiniteType, source_eq
-/
lemma CWComplex.finiteType_mkFiniteType.{u} {X : Type u} [TopologicalSpace X] (C : Set X)
    (cell : (n : Nat) -> Type u) (map : (n : Nat) -> (i : cell n) -> PartialEquiv (Fin n -> Real) X)
    (finite_cell : forall (n : Nat), _root_.Finite (cell n))
    (source_eq : forall (n : Nat) (i : cell n), (map n i).source = ball 0 1)
    (continuousOn : forall (n : Nat) (i : cell n), ContinuousOn (map n i) (closedBall 0 1))
    (continuousOn_symm : forall (n : Nat) (i : cell n), ContinuousOn (map n i).symm (map n i).target)
    (pairwiseDisjoint' :
      (univ : Set (Σ n, cell n)).PairwiseDisjoint (fun ni => map ni.1 ni.2 '' ball 0 1))
    (mapsTo : forall (n : Nat) (i : cell n),
      MapsTo (map n i) (sphere 0 1) (⋃ (m < n) (j : cell m), map m j '' closedBall 0 1))
    (closed' : forall (A : Set X) (_ : A subseteq C),
      (forall n j, IsClosed (A inter map n j '' closedBall 0 1)) -> IsClosed A)
    (union' : ⋃ (n : Nat) (j : cell n), map n j '' closedBall 0 1 = C) :
    letI := mkFiniteType C cell map finite_cell source_eq continuousOn continuousOn_symm
      pairwiseDisjoint' mapsTo closed' union'
    FiniteType C :=
  letI := mkFiniteType C cell map finite_cell source_eq continuousOn continuousOn_symm
      pairwiseDisjoint' mapsTo closed' union'
  { finite_cell := finite_cell }

/-- If we want to construct a finite relative CW complex we can add the conditions
`eventually_isEmpty_cell` and `finite_cell`, relax the condition `mapsTo` and remove the condition
`closed'`. -/
@[simps -isSimp, instance_reducible]
/--
Definition of `RelCWComplex.mkFinite.` / `RelCWComplex.mkFinite.` 的定义

English:
definition RelCWComplex.mkFinite.{u}
  signature: {X : Type u} [TopologicalSpace X] (C : Set X)
  body: cell
  map := map
  source_eq := source_eq
  continuousOn := continuousOn
  continuousOn_symm := continuousOn_symm
  pairwiseDisjoint' := pairwiseDisjoint'
  disjointBase' := disjointBase'
  mapsTo n i := by
    use fun m => finite_univ.toFinset (s := (univ : Set (cell m)))
    simp only [Finite.mem_toFinset, mem_univ, iUnion_true]
    exact mapsTo n i
  closed' A asubc := by
    intro h
    -- `A = A ∩ C = A ∩ (D ∪ ⋃ n, ⋃ j, closedCell n j)` is closed by assumption since `C` has only
    -- finitely many cells.
    rw [← inter_eq_left.2 asubc]
    simp_rw [Filter.eventually_atTop] at eventually_isEmpty_cell
    obtain ⟨N, hN⟩ := eventually_isEmpty_cell
    suffices IsClosed (A inter (D union ⋃ (n : {n : Nat // n < N}), ⋃ j, ↑(map n j) '' closedBall 0 1)) by
      convert! this using 2
      rw [← union']; rw [iUnion_subtype]
      congrm D union ⋃ n, ?_
      refine subset_antisymm ?_ (iUnion_subset (fun i => by rfl))
      apply iUnion_subset
      intro i
      have : n < N := Decidable.byContradiction fun h => (hN n (Nat.ge_of_not_lt h)).false i
      exact subset_iUnion₂ (s := fun _ i => (map n i) '' closedBall 0 1) this i
    simp_rw [inter_union_distrib_left, inter_iUnion]
    exact h.2.union (isClosed_iUnion_of_finite (fun n => isClosed_iUnion_of_finite (h.1 n.1)))
  isClosedBase := isClosedBase
  union' := union'

中文:
定义 RelCWComplex.mkFinite.{u}
  签名: {X : 类型u} [拓扑空间 X] (C : 集合 X)
  定义体: cell
  map := map
  source_eq := source_eq
  continuousOn := continuousOn
  continuousOn_symm := continuousOn_symm
  pairwiseDisjoint' := pairwiseDisjoint'
  disjointBase' := disjointBase'
  mapsTo n i := by
    use fun m => finite_univ.toFinset (s := (univ : Set (cell m)))
    simp only [Finite.mem_toFinset, mem_univ, iUnion_true]
    exact mapsTo n i
  closed' A asubc := by
    intro h
    -- `A = A ∩ C = A ∩ (D ∪ ⋃ n, ⋃ j, closedCell n j)` is closed by assumption since `C` has only
    -- finitely many cells.
    rw [← inter_eq_left.2 asubc]
    simp_rw [Filter.eventually_atTop] at eventually_isEmpty_cell
    obtain ⟨N, hN⟩ := eventually_isEmpty_cell
    suffices IsClosed (A inter (D union ⋃ (n : {n : Nat // n < N}), ⋃ j, ↑(map n j) '' closedBall 0 1)) by
      convert! this using 2
      rw [← union']; rw [iUnion_subtype]
      congrm D union ⋃ n, ?_
      refine subset_antisymm ?_ (iUnion_subset (fun i => by rfl))
      apply iUnion_subset
      intro i
      have : n < N := Decidable.byContradiction fun h => (hN n (Nat.ge_of_not_lt h)).false i
      exact subset_iUnion₂ (s := fun _ i => (map n i) '' closedBall 0 1) this i
    simp_rw [inter_union_distrib_left, inter_iUnion]
    exact h.2.union (isClosed_iUnion_of_finite (fun n => isClosed_iUnion_of_finite (h.1 n.1)))
  isClosedBase := isClosedBase
  union' := union'
-/
def RelCWComplex.mkFinite.{u} {X : Type u} [TopologicalSpace X] (C : Set X)
    (D : outParam (Set X)) (cell : (n : Nat) -> Type u)
    (map : (n : Nat) -> (i : cell n) -> PartialEquiv (Fin n -> Real) X)
    (eventually_isEmpty_cell : forallᶠ n in Filter.atTop, IsEmpty (cell n))
    (finite_cell : forall (n : Nat), _root_.Finite (cell n))
    (source_eq : forall (n : Nat) (i : cell n), (map n i).source = ball 0 1)
    (continuousOn : forall (n : Nat) (i : cell n), ContinuousOn (map n i) (closedBall 0 1))
    (continuousOn_symm : forall (n : Nat) (i : cell n), ContinuousOn (map n i).symm (map n i).target)
    (pairwiseDisjoint' :
      (univ : Set (Σ n, cell n)).PairwiseDisjoint (fun ni => map ni.1 ni.2 '' ball 0 1))
    (disjointBase' : forall (n : Nat) (i : cell n), Disjoint (map n i '' ball 0 1) D)
    (mapsTo : forall (n : Nat) (i : cell n),
      MapsTo (map n i) (sphere 0 1) (D union ⋃ (m < n) (j : cell m), map m j '' closedBall 0 1))
    (isClosedBase : IsClosed D)
    (union' : D union ⋃ (n : Nat) (j : cell n), map n j '' closedBall 0 1 = C) :
    RelCWComplex C D where
  cell := cell
  map := map
  source_eq := source_eq
  continuousOn := continuousOn
  continuousOn_symm := continuousOn_symm
  pairwiseDisjoint' := pairwiseDisjoint'
  disjointBase' := disjointBase'
  mapsTo n i := by
    use fun m => finite_univ.toFinset (s := (univ : Set (cell m)))
    simp only [Finite.mem_toFinset, mem_univ, iUnion_true]
    exact mapsTo n i
  closed' A asubc := by
    intro h
    -- `A = A ∩ C = A ∩ (D ∪ ⋃ n, ⋃ j, closedCell n j)` is closed by assumption since `C` has only
    -- finitely many cells.
    rw [← inter_eq_left.2 asubc]
    simp_rw [Filter.eventually_atTop] at eventually_isEmpty_cell
    obtain ⟨N, hN⟩ := eventually_isEmpty_cell
    suffices IsClosed (A inter (D union ⋃ (n : {n : Nat // n < N}), ⋃ j, ↑(map n j) '' closedBall 0 1)) by
      convert! this using 2
      rw [← union']; rw [iUnion_subtype]
      congrm D union ⋃ n, ?_
      refine subset_antisymm ?_ (iUnion_subset (fun i => by rfl))
      apply iUnion_subset
      intro i
      have : n < N := Decidable.byContradiction fun h => (hN n (Nat.ge_of_not_lt h)).false i
      exact subset_iUnion₂ (s := fun _ i => (map n i) '' closedBall 0 1) this i
    simp_rw [inter_union_distrib_left, inter_iUnion]
    exact h.2.union (isClosed_iUnion_of_finite (fun n => isClosed_iUnion_of_finite (h.1 n.1)))
  isClosedBase := isClosedBase
  union' := union'

/--
lemma `RelCWComplex.finite_mkFinite.` / 引理 `RelCWComplex.finite_mkFinite.`

English:
lemma RelCWComplex.finite_mkFinite.{u}
  statement: {X : Type u} [TopologicalSpace X] (C : Set X)
  proof: mkFinite C D cell map eventually_isEmpty_cell finite_cell source_eq continuousOn
      continuousOn_symm pairwiseDisjoint' disjointBase' mapsTo isClosedBase union'
    Finite C :=
  letI := mkFinite C D cell map eventually_isEmpty_cell finite_cell source_eq continuousOn
      continuousOn_symm pairwiseDisjoint' disjointBase' mapsTo isClosedBase union'
  { eventually_isEmpty_cell := eventually_isEmpty_cell
    finite_cell := finite_cell }

中文:
引理 RelCWComplex.finite_mkFinite.{u}
  结论: {X : 类型u} [拓扑空间 X] (C : 集合 X)
  证明: mkFinite C D cell map eventually_isEmpty_cell finite_cell source_eq continuousOn
      continuousOn_symm pairwiseDisjoint' disjointBase' mapsTo isClosedBase union'
    Finite C :=
  letI := mkFinite C D cell map eventually_isEmpty_cell finite_cell source_eq continuousOn
      continuousOn_symm pairwiseDisjoint' disjointBase' mapsTo isClosedBase union'
  { eventually_isEmpty_cell := eventually_isEmpty_cell
    finite_cell := finite_cell }

Depends on / 依赖: continuousOn, eventually_isEmpty_cell, finite_cell, mkFinite, source_eq
-/
lemma RelCWComplex.finite_mkFinite.{u} {X : Type u} [TopologicalSpace X] (C : Set X)
    (D : outParam (Set X)) (cell : (n : Nat) -> Type u)
    (map : (n : Nat) -> (i : cell n) -> PartialEquiv (Fin n -> Real) X)
    (eventually_isEmpty_cell : forallᶠ n in Filter.atTop, IsEmpty (cell n))
    (finite_cell : forall (n : Nat), _root_.Finite (cell n))
    (source_eq : forall (n : Nat) (i : cell n), (map n i).source = ball 0 1)
    (continuousOn : forall (n : Nat) (i : cell n), ContinuousOn (map n i) (closedBall 0 1))
    (continuousOn_symm : forall (n : Nat) (i : cell n), ContinuousOn (map n i).symm (map n i).target)
    (pairwiseDisjoint' :
      (univ : Set (Σ n, cell n)).PairwiseDisjoint (fun ni => map ni.1 ni.2 '' ball 0 1))
    (disjointBase' : forall (n : Nat) (i : cell n), Disjoint (map n i '' ball 0 1) D)
    (mapsTo : forall (n : Nat) (i : cell n),
      MapsTo (map n i) (sphere 0 1) (D union ⋃ (m < n) (j : cell m), map m j '' closedBall 0 1))
    (isClosedBase : IsClosed D)
    (union' : D union ⋃ (n : Nat) (j : cell n), map n j '' closedBall 0 1 = C) :
    letI := mkFinite C D cell map eventually_isEmpty_cell finite_cell source_eq continuousOn
      continuousOn_symm pairwiseDisjoint' disjointBase' mapsTo isClosedBase union'
    Finite C :=
  letI := mkFinite C D cell map eventually_isEmpty_cell finite_cell source_eq continuousOn
      continuousOn_symm pairwiseDisjoint' disjointBase' mapsTo isClosedBase union'
  { eventually_isEmpty_cell := eventually_isEmpty_cell
    finite_cell := finite_cell }

/-- If we want to construct a finite CW complex we can add the conditions `eventually_isEmpty_cell`
and `finite_cell`, relax the condition `mapsTo` and remove the condition `closed'`. -/
@[simps! -isSimp, instance_reducible]
/--
Definition of `CWComplex.mkFinite.` / `CWComplex.mkFinite.` 的定义

English:
definition CWComplex.mkFinite.{u}
  signature: {X : Type u} [TopologicalSpace X] (C : Set X)
  body: (RelCWComplex.mkFinite C ∅
  (cell := cell)
  (map := map)
  (eventually_isEmpty_cell := eventually_isEmpty_cell)
  (finite_cell := finite_cell)
  (source_eq := source_eq)
  (continuousOn := continuousOn)
  (continuousOn_symm := continuousOn_symm)
  (pairwiseDisjoint' := pairwiseDisjoint')
  (disjointBase' := by simp only [disjoint_empty, implies_true])
  (mapsTo := by simpa only [empty_union])
  (isClosedBase := isClosed_empty)
  (union' := by simpa only [empty_union])).toCWComplex

中文:
定义 CWComplex.mkFinite.{u}
  签名: {X : 类型u} [拓扑空间 X] (C : 集合 X)
  定义体: (RelCWComplex.mkFinite C ∅
  (cell := cell)
  (map := map)
  (eventually_isEmpty_cell := eventually_isEmpty_cell)
  (finite_cell := finite_cell)
  (source_eq := source_eq)
  (continuousOn := continuousOn)
  (continuousOn_symm := continuousOn_symm)
  (pairwiseDisjoint' := pairwiseDisjoint')
  (disjointBase' := by simp only [disjoint_empty, implies_true])
  (mapsTo := by simpa only [empty_union])
  (isClosedBase := isClosed_empty)
  (union' := by simpa only [empty_union])).toCWComplex

Depends on / 依赖: RelCWComplex, RelCWComplex.mkFinite, mkFinite
-/
def CWComplex.mkFinite.{u} {X : Type u} [TopologicalSpace X] (C : Set X)
    (cell : (n : Nat) -> Type u) (map : (n : Nat) -> (i : cell n) -> PartialEquiv (Fin n -> Real) X)
    (eventually_isEmpty_cell : forallᶠ n in Filter.atTop, IsEmpty (cell n))
    (finite_cell : forall (n : Nat), _root_.Finite (cell n))
    (source_eq : forall (n : Nat) (i : cell n), (map n i).source = ball 0 1)
    (continuousOn : forall (n : Nat) (i : cell n), ContinuousOn (map n i) (closedBall 0 1))
    (continuousOn_symm : forall (n : Nat) (i : cell n), ContinuousOn (map n i).symm (map n i).target)
    (pairwiseDisjoint' :
      (univ : Set (Σ n, cell n)).PairwiseDisjoint (fun ni => map ni.1 ni.2 '' ball 0 1))
    (mapsTo_iff_image_subset : forall (n : Nat) (i : cell n),
      MapsTo (map n i) (sphere 0 1) (⋃ (m < n) (j : cell m), map m j '' closedBall 0 1))
    (union' : ⋃ (n : Nat) (j : cell n), map n j '' closedBall 0 1 = C) :
    CWComplex C := (RelCWComplex.mkFinite C ∅
  (cell := cell)
  (map := map)
  (eventually_isEmpty_cell := eventually_isEmpty_cell)
  (finite_cell := finite_cell)
  (source_eq := source_eq)
  (continuousOn := continuousOn)
  (continuousOn_symm := continuousOn_symm)
  (pairwiseDisjoint' := pairwiseDisjoint')
  (disjointBase' := by simp only [disjoint_empty, implies_true])
  (mapsTo := by simpa only [empty_union])
  (isClosedBase := isClosed_empty)
  (union' := by simpa only [empty_union])).toCWComplex

/--
lemma `CWComplex.finite_mkFinite.` / 引理 `CWComplex.finite_mkFinite.`

English:
lemma CWComplex.finite_mkFinite.{u}
  statement: {X : Type u} [TopologicalSpace X] (C : Set X)
  proof: mkFinite C cell map eventually_isEmpty_cell finite_cell source_eq continuousOn
      continuousOn_symm pairwiseDisjoint' mapsTo union'
    Finite C :=
  letI := mkFinite C cell map eventually_isEmpty_cell finite_cell source_eq continuousOn
      continuousOn_symm pairwiseDisjoint' mapsTo union'
  { eventually_isEmpty_cell := eventually_isEmpty_cell
    finite_cell := finite_cell }

中文:
引理 CWComplex.finite_mkFinite.{u}
  结论: {X : 类型u} [拓扑空间 X] (C : 集合 X)
  证明: mkFinite C cell map eventually_isEmpty_cell finite_cell source_eq continuousOn
      continuousOn_symm pairwiseDisjoint' mapsTo union'
    Finite C :=
  letI := mkFinite C cell map eventually_isEmpty_cell finite_cell source_eq continuousOn
      continuousOn_symm pairwiseDisjoint' mapsTo union'
  { eventually_isEmpty_cell := eventually_isEmpty_cell
    finite_cell := finite_cell }

Depends on / 依赖: continuousOn, eventually_isEmpty_cell, finite_cell, mkFinite, source_eq
-/
lemma CWComplex.finite_mkFinite.{u} {X : Type u} [TopologicalSpace X] (C : Set X)
    (cell : (n : Nat) -> Type u) (map : (n : Nat) -> (i : cell n) -> PartialEquiv (Fin n -> Real) X)
    (eventually_isEmpty_cell : forallᶠ n in Filter.atTop, IsEmpty (cell n))
    (finite_cell : forall (n : Nat), _root_.Finite (cell n))
    (source_eq : forall (n : Nat) (i : cell n), (map n i).source = ball 0 1)
    (continuousOn : forall (n : Nat) (i : cell n), ContinuousOn (map n i) (closedBall 0 1))
    (continuousOn_symm : forall (n : Nat) (i : cell n), ContinuousOn (map n i).symm (map n i).target)
    (pairwiseDisjoint' :
      (univ : Set (Σ n, cell n)).PairwiseDisjoint (fun ni => map ni.1 ni.2 '' ball 0 1))
    (mapsTo : forall (n : Nat) (i : cell n),
      MapsTo (map n i) (sphere 0 1) (⋃ (m < n) (j : cell m), map m j '' closedBall 0 1))
    (union' : ⋃ (n : Nat) (j : cell n), map n j '' closedBall 0 1 = C) :
    letI := mkFinite C cell map eventually_isEmpty_cell finite_cell source_eq continuousOn
      continuousOn_symm pairwiseDisjoint' mapsTo union'
    Finite C :=
  letI := mkFinite C cell map eventually_isEmpty_cell finite_cell source_eq continuousOn
      continuousOn_symm pairwiseDisjoint' mapsTo union'
  { eventually_isEmpty_cell := eventually_isEmpty_cell
    finite_cell := finite_cell }

variable {X : Type*} [TopologicalSpace X] {C D : Set X} [RelCWComplex C D]

/-- If the collection of all cells (of any dimension) of a relative CW complex `C` is finite, then
`C` is finite as a CW complex. -/
@[alias_in CWComplex]
/--
lemma `RelCWComplex.finite_of_finite_cells` / 引理 `RelCWComplex.finite_of_finite_cells`

English:
lemma RelCWComplex.finite_of_finite_cells
  given: (finite : _root_.Finite (Σ n, cell C n))
  statement: Finite C where
  proof: by
    simp only [Filter.eventually_atTop]
    cases isEmpty_or_nonempty (Σ n, cell C n)
    · exact ⟨0, by simp_all⟩
    -- We take the greatest `n` such that there is a `j : cell C n` and show that this fulfills
    -- the necessary conditions.
    have _ := Fintype.ofFinite (Σ n, cell C n)
    let A := (Finset.univ : Finset (Σ n, cell C n)).image Sigma.fst
    use A.max' (Finset.image_nonempty.2 Finset.univ_nonempty) + 1
    intro m _
    by_contra! h'
    have hmA : m in A := by
      simp only [Finset.mem_image, Finset.mem_univ, true_and, A]
      simp only [← exists_true_iff_nonempty] at h'
      obtain ⟨j, _⟩ := h'
      use ⟨m, j⟩
    linarith [A.le_max' m hmA]
  finite_cell _ := Finite.of_injective (Sigma.mk _) sigma_mk_injective

中文:
引理 RelCWComplex.finite_of_finite_cells
  条件: (finite : _root_.有限 (Σ n, cell C n))
  结论: 有限 C where
  证明: by
    simp only [Filter.eventually_atTop]
    cases isEmpty_or_nonempty (Σ n, cell C n)
    · exact ⟨0, by simp_all⟩
    -- We take the greatest `n` such that there is a `j : cell C n` and show that this fulfills
    -- the necessary conditions.
    have _ := Fintype.ofFinite (Σ n, cell C n)
    let A := (Finset.univ : Finset (Σ n, cell C n)).image Sigma.fst
    use A.max' (Finset.image_nonempty.2 Finset.univ_nonempty) + 1
    intro m _
    by_contra! h'
    have hmA : m in A := by
      simp only [Finset.mem_image, Finset.mem_univ, true_and, A]
      simp only [← exists_true_iff_nonempty] at h'
      obtain ⟨j, _⟩ := h'
      use ⟨m, j⟩
    linarith [A.le_max' m hmA]
  finite_cell _ := Finite.of_injective (Sigma.mk _) sigma_mk_injective

Depends on / 依赖: Filter, Filter.eventually_atTop, eventually_atTop, isEmpty_or_nonempty
-/
lemma RelCWComplex.finite_of_finite_cells (finite : _root_.Finite (Σ n, cell C n)) : Finite C where
  eventually_isEmpty_cell := by
    simp only [Filter.eventually_atTop]
    cases isEmpty_or_nonempty (Σ n, cell C n)
    · exact ⟨0, by simp_all⟩
    -- We take the greatest `n` such that there is a `j : cell C n` and show that this fulfills
    -- the necessary conditions.
    have _ := Fintype.ofFinite (Σ n, cell C n)
    let A := (Finset.univ : Finset (Σ n, cell C n)).image Sigma.fst
    use A.max' (Finset.image_nonempty.2 Finset.univ_nonempty) + 1
    intro m _
    by_contra! h'
    have hmA : m in A := by
      simp only [Finset.mem_image, Finset.mem_univ, true_and, A]
      simp only [← exists_true_iff_nonempty] at h'
      obtain ⟨j, _⟩ := h'
      use ⟨m, j⟩
    linarith [A.le_max' m hmA]
  finite_cell _ := Finite.of_injective (Sigma.mk _) sigma_mk_injective

/-- If `C` is finite as a CW complex then the collection of all cells (of any dimension) is
finite. -/
@[alias_in CWComplex]
/--
lemma `RelCWComplex.finite_cells_of_finite` / 引理 `RelCWComplex.finite_cells_of_finite`

English:
lemma RelCWComplex.finite_cells_of_finite
  given: [finite : Finite C]
  statement: _root_.Finite (Σ n, cell C n)
  proof: by
  -- We show that there is a bijection between `Σ n, cell C n` and
  -- `Σ (m : {m : ℕ // m < n}), cell C m`.
  have h := finite.eventually_isEmpty_cell
  have _ := finite.finite_cell
  simp only [Filter.eventually_atTop] at h
  rcases h with ⟨n, hn⟩
  have (m) (j : cell C m) : m < n := by
    by_contra h
    exact (hn m (not_lt.1 h)).false j
  let f : (Σ (m : {m : Nat // m < n}), cell C m) ≃ Σ m, cell C m := {
    toFun := fun ⟨m, j⟩ => ⟨m, j⟩
    invFun := fun ⟨m, j⟩ => ⟨⟨m, this m j⟩, j⟩
    left_inv := by simp [Function.LeftInverse]
    right_inv := by simp [Function.RightInverse, Function.LeftInverse] }
  rw [← Equiv.finite_iff f]
  exact Finite.instSigma

中文:
引理 RelCWComplex.finite_cells_of_finite
  条件: [finite : 有限 C]
  结论: _root_.有限 (Σ n, cell C n)
  证明: by
  -- We show that there is a bijection between `Σ n, cell C n` and
  -- `Σ (m : {m : ℕ // m < n}), cell C m`.
  have h := finite.eventually_isEmpty_cell
  have _ := finite.finite_cell
  simp only [Filter.eventually_atTop] at h
  rcases h with ⟨n, hn⟩
  have (m) (j : cell C m) : m < n := by
    by_contra h
    exact (hn m (not_lt.1 h)).false j
  let f : (Σ (m : {m : Nat // m < n}), cell C m) ≃ Σ m, cell C m := {
    toFun := fun ⟨m, j⟩ => ⟨m, j⟩
    invFun := fun ⟨m, j⟩ => ⟨⟨m, this m j⟩, j⟩
    left_inv := by simp [Function.LeftInverse]
    right_inv := by simp [Function.RightInverse, Function.LeftInverse] }
  rw [← Equiv.finite_iff f]
  exact Finite.instSigma
-/
lemma RelCWComplex.finite_cells_of_finite [finite : Finite C] : _root_.Finite (Σ n, cell C n) := by
  -- We show that there is a bijection between `Σ n, cell C n` and
  -- `Σ (m : {m : ℕ // m < n}), cell C m`.
  have h := finite.eventually_isEmpty_cell
  have _ := finite.finite_cell
  simp only [Filter.eventually_atTop] at h
  rcases h with ⟨n, hn⟩
  have (m) (j : cell C m) : m < n := by
    by_contra h
    exact (hn m (not_lt.1 h)).false j
  let f : (Σ (m : {m : Nat // m < n}), cell C m) ≃ Σ m, cell C m := {
    toFun := fun ⟨m, j⟩ => ⟨m, j⟩
    invFun := fun ⟨m, j⟩ => ⟨⟨m, this m j⟩, j⟩
    left_inv := by simp [Function.LeftInverse]
    right_inv := by simp [Function.RightInverse, Function.LeftInverse] }
  rw [← Equiv.finite_iff f]
  exact Finite.instSigma

/-- A CW complex is finite iff the total number of its cells is finite. -/
@[alias_in CWComplex]
/--
lemma `RelCWComplex.finite_iff_finite_cells` / 引理 `RelCWComplex.finite_iff_finite_cells`

English:
lemma RelCWComplex.finite_iff_finite_cells
  statement: Finite C ↔ _root_.Finite (Σ n, cell C n)
  proof: ⟨fun h => finite_cells_of_finite (finite := h), finite_of_finite_cells⟩

中文:
引理 RelCWComplex.finite_iff_finite_cells
  结论: 有限 C ↔ _root_.有限 (Σ n, cell C n)
  证明: ⟨fun h => finite_cells_of_finite (finite := h), finite_of_finite_cells⟩

Depends on / 依赖: finite, finite_cells_of_finite, finite_of_finite_cells
-/
lemma RelCWComplex.finite_iff_finite_cells : Finite C ↔ _root_.Finite (Σ n, cell C n) :=
  ⟨fun h => finite_cells_of_finite (finite := h), finite_of_finite_cells⟩

end Topology
