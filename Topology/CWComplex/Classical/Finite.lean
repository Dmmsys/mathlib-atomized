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

/-- A CW complex is finite dimensional if `cell C n` is empty for all but finitely many `n`. -/
/-
**Topology.RelCWComplex.FiniteDimensional.** 是 Mathlib 中的一个类，位于命名空间 `Topology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A CW complex is finite dimensional if `cell C n` is empty for all but finitely m
any `n`.
-/
class RelCWComplex.FiniteDimensional.{u} {X : Type u} [TopologicalSpace X] (C : Set X) {D : Set X}
    [RelCWComplex C D] : Prop where
  /-- For some natural number `n`, the type `cell C m` is empty for all `m ≥ n`. -/
  eventually_isEmpty_cell : ∀ᶠ n in Filter.atTop, IsEmpty (cell C n)

alias CWComplex.FiniteDimensional.eventually_isEmpty_cell :=
  RelCWComplex.FiniteDimensional.eventually_isEmpty_cell

/-- A CW complex is of finite type if `cell C n` is finite for every `n`. -/
/-
**Topology.RelCWComplex.FiniteType.** 是 Mathlib 中的一个类，位于命名空间 `Topology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A CW complex is of finite type if `cell C n` is finite for every `n`.
-/
class RelCWComplex.FiniteType.{u} {X : Type u} [TopologicalSpace X] (C : Set X) {D : Set X}
    [RelCWComplex C D] : Prop where
  /-- `cell C n` is finite for every `n`. -/
  finite_cell (n : ℕ) : Finite (cell C n)

alias CWComplex.FiniteType.finite_cell := RelCWComplex.FiniteType.finite_cell

/-- A CW complex is finite if it is finite dimensional and of finite type. -/
/-
**Topology.RelCWComplex.Finite** 是 Mathlib 中的一个归纳类型，位于命名空间 `Topology.RelCWComple
x`。
形式化陈述：{X : Type u_1} → [inst : TopologicalSpace X] → (C : Set X) → {D : Set X} →
 [Topology.RelCWComplex C D] → Prop
参数：C : Set X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A CW complex is finite if it is finite dimensional and of finite type.
-/
class RelCWComplex.Finite {X : Type*} [TopologicalSpace X] (C : Set X) {D : Set X}
    [RelCWComplex C D] extends FiniteDimensional C, FiniteType C

variable {X : Type*} [TopologicalSpace X] (C : Set X) {D : Set X} [RelCWComplex C D]

@[alias_in CWComplex]
/-
**Topology.RelCWComplex.finite_of_finiteDimensional_finiteType** 是 Mathlib 中的一个定
理，位于命名空间 `Topology.RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] (C : Set X) {D : Set X} [inst
_1 : Topology.RelCWComplex C D]   [Topology.RelCWComplex.FiniteDimensional C] [T
opology.RelCWComplex.FiniteType C], Topology.RelCWComplex.Finite C
参数：C : Set X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.RelCWComplex.FiniteType.finite_cell`：∀ {X : Type u} {inst : Top
ologicalSpace X} {C D : Set X} {inst_1 : Topology.RelCWComplex C D}   [self : To
pology.RelCWComplex.FiniteType C] …
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
/-
**Topology.RelCWComplex.mkFiniteType.** 是 Mathlib 中的一个定义，位于命名空间 `Topology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If we want to construct a relative CW complex of finite type, we can add the con
dition
`finite_cell` and relax the condition `mapsTo`.
-/
def RelCWComplex.mkFiniteType.{u} {X : Type u} [TopologicalSpace X] (C : Set X)
    (D : outParam (Set X))
    (cell : (n : ℕ) → Type u) (map : (n : ℕ) → (i : cell n) → PartialEquiv (Fin n → ℝ) X)
    (finite_cell : ∀ (n : ℕ), _root_.Finite (cell n))
    (source_eq : ∀ (n : ℕ) (i : cell n), (map n i).source = ball 0 1)
    (continuousOn : ∀ (n : ℕ) (i : cell n), ContinuousOn (map n i) (closedBall 0 1))
    (continuousOn_symm : ∀ (n : ℕ) (i : cell n), ContinuousOn (map n i).symm (map n i).target)
    (pairwiseDisjoint' :
      (univ : Set (Σ n, cell n)).PairwiseDisjoint (fun ni ↦ map ni.1 ni.2 '' ball 0 1))
    (disjointBase' : ∀ (n : ℕ) (i : cell n), Disjoint (map n i '' ball 0 1) D)
    (mapsTo : ∀ (n : ℕ) (i : cell n),
      MapsTo (map n i) (sphere 0 1) (D ∪ ⋃ (m < n) (j : cell m), map m j '' closedBall 0 1))
    (closed' : ∀ (A : Set X) (_ : A ⊆ C),
      ((∀ n j, IsClosed (A ∩ map n j '' closedBall 0 1)) ∧ IsClosed (A ∩ D)) → IsClosed A)
    (isClosedBase : IsClosed D)
    (union' : D ∪ ⋃ (n : ℕ) (j : cell n), map n j '' closedBall 0 1 = C) :
    RelCWComplex C D where
  cell := cell
  map := map
  source_eq := source_eq
  continuousOn := continuousOn
  continuousOn_symm := continuousOn_symm
  pairwiseDisjoint' := pairwiseDisjoint'
  disjointBase' := disjointBase'
  mapsTo n i := by
    use fun m ↦ finite_univ.toFinset (s := (univ : Set (cell m)))
    simp only [Finite.mem_toFinset, mem_univ, iUnion_true]
    exact mapsTo n i
  closed' := closed'
  isClosedBase := isClosedBase
  union' := union'

/-- A CW complex that was constructed using `RelCWComplex.mkFiniteType` is of finite type. -/
/-
**Topology.RelCWComplex.finiteType_mkFiniteType.** 是 Mathlib 中的一个引理，位于命名空间 `Topo
logy`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A CW complex that was constructed using `RelCWComplex.mkFiniteType` is of finite
 type.
-/
lemma RelCWComplex.finiteType_mkFiniteType.{u} {X : Type u} [TopologicalSpace X] (C : Set X)
    (D : outParam (Set X))
    (cell : (n : ℕ) → Type u) (map : (n : ℕ) → (i : cell n) → PartialEquiv (Fin n → ℝ) X)
    (finite_cell : ∀ (n : ℕ), _root_.Finite (cell n))
    (source_eq : ∀ (n : ℕ) (i : cell n), (map n i).source = ball 0 1)
    (continuousOn : ∀ (n : ℕ) (i : cell n), ContinuousOn (map n i) (closedBall 0 1))
    (continuousOn_symm : ∀ (n : ℕ) (i : cell n), ContinuousOn (map n i).symm (map n i).target)
    (pairwiseDisjoint' :
      (univ : Set (Σ n, cell n)).PairwiseDisjoint (fun ni ↦ map ni.1 ni.2 '' ball 0 1))
    (disjointBase' : ∀ (n : ℕ) (i : cell n), Disjoint (map n i '' ball 0 1) D)
    (mapsTo : ∀ (n : ℕ) (i : cell n),
      MapsTo (map n i) (sphere 0 1) (D ∪ ⋃ (m < n) (j : cell m), map m j '' closedBall 0 1))
    (closed' : ∀ (A : Set X) (_ : A ⊆ C),
      ((∀ n j, IsClosed (A ∩ map n j '' closedBall 0 1)) ∧ IsClosed (A ∩ D)) → IsClosed A)
    (isClosedBase : IsClosed D)
    (union' : D ∪ ⋃ (n : ℕ) (j : cell n), map n j '' closedBall 0 1 = C) :
    letI := mkFiniteType C D cell map finite_cell source_eq continuousOn continuousOn_symm
      pairwiseDisjoint' disjointBase' mapsTo closed' isClosedBase union'
    FiniteType C :=
  letI := mkFiniteType C D cell map finite_cell source_eq continuousOn continuousOn_symm
      pairwiseDisjoint' disjointBase' mapsTo closed' isClosedBase union'
  { finite_cell := finite_cell }

/-- If we want to construct a CW complex of finite type, we can add the condition `finite_cell` and
relax the condition `mapsTo`. -/
@[simps -isSimp, instance_reducible]
/-
**Topology.CWComplex.mkFiniteType.** 是 Mathlib 中的一个定义，位于命名空间 `Topology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If we want to construct a CW complex of finite type, we can add the condition `f
inite_cell` and
relax the condition `mapsTo`.
-/
def CWComplex.mkFiniteType.{u} {X : Type u} [TopologicalSpace X] (C : Set X)
    (cell : (n : ℕ) → Type u) (map : (n : ℕ) → (i : cell n) → PartialEquiv (Fin n → ℝ) X)
    (finite_cell : ∀ (n : ℕ), _root_.Finite (cell n))
    (source_eq : ∀ (n : ℕ) (i : cell n), (map n i).source = ball 0 1)
    (continuousOn : ∀ (n : ℕ) (i : cell n), ContinuousOn (map n i) (closedBall 0 1))
    (continuousOn_symm : ∀ (n : ℕ) (i : cell n), ContinuousOn (map n i).symm (map n i).target)
    (pairwiseDisjoint' :
      (univ : Set (Σ n, cell n)).PairwiseDisjoint (fun ni ↦ map ni.1 ni.2 '' ball 0 1))
    (mapsTo : ∀ (n : ℕ) (i : cell n),
      MapsTo (map n i) (sphere 0 1) (⋃ (m < n) (j : cell m), map m j '' closedBall 0 1))
    (closed' : ∀ (A : Set X) (_ : A ⊆ C),
    (∀ n j, IsClosed (A ∩ map n j '' closedBall 0 1)) → IsClosed A)
    (union' : ⋃ (n : ℕ) (j : cell n), map n j '' closedBall 0 1 = C) :
    CWComplex C where
  cell := cell
  map := map
  source_eq := source_eq
  continuousOn := continuousOn
  continuousOn_symm := continuousOn_symm
  pairwiseDisjoint' := pairwiseDisjoint'
  mapsTo' n i := by
    use fun m ↦ finite_univ.toFinset (s := (univ : Set (cell m)))
    simp only [Finite.mem_toFinset, mem_univ, iUnion_true]
    exact mapsTo n i
  closed' := closed'
  union' := union'

/-- A CW complex that was constructed using `CWComplex.mkFiniteType` is of finite type. -/
/-
**Topology.CWComplex.finiteType_mkFiniteType.** 是 Mathlib 中的一个引理，位于命名空间 `Topolog
y`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A CW complex that was constructed using `CWComplex.mkFiniteType` is of finite ty
pe.
-/
lemma CWComplex.finiteType_mkFiniteType.{u} {X : Type u} [TopologicalSpace X] (C : Set X)
    (cell : (n : ℕ) → Type u) (map : (n : ℕ) → (i : cell n) → PartialEquiv (Fin n → ℝ) X)
    (finite_cell : ∀ (n : ℕ), _root_.Finite (cell n))
    (source_eq : ∀ (n : ℕ) (i : cell n), (map n i).source = ball 0 1)
    (continuousOn : ∀ (n : ℕ) (i : cell n), ContinuousOn (map n i) (closedBall 0 1))
    (continuousOn_symm : ∀ (n : ℕ) (i : cell n), ContinuousOn (map n i).symm (map n i).target)
    (pairwiseDisjoint' :
      (univ : Set (Σ n, cell n)).PairwiseDisjoint (fun ni ↦ map ni.1 ni.2 '' ball 0 1))
    (mapsTo : ∀ (n : ℕ) (i : cell n),
      MapsTo (map n i) (sphere 0 1) (⋃ (m < n) (j : cell m), map m j '' closedBall 0 1))
    (closed' : ∀ (A : Set X) (_ : A ⊆ C),
      (∀ n j, IsClosed (A ∩ map n j '' closedBall 0 1)) → IsClosed A)
    (union' : ⋃ (n : ℕ) (j : cell n), map n j '' closedBall 0 1 = C) :
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
/-
**Topology.RelCWComplex.mkFinite.** 是 Mathlib 中的一个定义，位于命名空间 `Topology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If we want to construct a finite relative CW complex we can add the conditions
`eventually_isEmpty_cell` and `finite_cell`, relax the condition `mapsTo` and re
move the condition
`closed'`.
-/
def RelCWComplex.mkFinite.{u} {X : Type u} [TopologicalSpace X] (C : Set X)
    (D : outParam (Set X)) (cell : (n : ℕ) → Type u)
    (map : (n : ℕ) → (i : cell n) → PartialEquiv (Fin n → ℝ) X)
    (eventually_isEmpty_cell : ∀ᶠ n in Filter.atTop, IsEmpty (cell n))
    (finite_cell : ∀ (n : ℕ), _root_.Finite (cell n))
    (source_eq : ∀ (n : ℕ) (i : cell n), (map n i).source = ball 0 1)
    (continuousOn : ∀ (n : ℕ) (i : cell n), ContinuousOn (map n i) (closedBall 0 1))
    (continuousOn_symm : ∀ (n : ℕ) (i : cell n), ContinuousOn (map n i).symm (map n i).target)
    (pairwiseDisjoint' :
      (univ : Set (Σ n, cell n)).PairwiseDisjoint (fun ni ↦ map ni.1 ni.2 '' ball 0 1))
    (disjointBase' : ∀ (n : ℕ) (i : cell n), Disjoint (map n i '' ball 0 1) D)
    (mapsTo : ∀ (n : ℕ) (i : cell n),
      MapsTo (map n i) (sphere 0 1) (D ∪ ⋃ (m < n) (j : cell m), map m j '' closedBall 0 1))
    (isClosedBase : IsClosed D)
    (union' : D ∪ ⋃ (n : ℕ) (j : cell n), map n j '' closedBall 0 1 = C) :
    RelCWComplex C D where
  cell := cell
  map := map
  source_eq := source_eq
  continuousOn := continuousOn
  continuousOn_symm := continuousOn_symm
  pairwiseDisjoint' := pairwiseDisjoint'
  disjointBase' := disjointBase'
  mapsTo n i := by
    use fun m ↦ finite_univ.toFinset (s := (univ : Set (cell m)))
    simp only [Finite.mem_toFinset, mem_univ, iUnion_true]
    exact mapsTo n i
  closed' A asubc := by
    intro h
    -- `A = A ∩ C = A ∩ (D ∪ ⋃ n, ⋃ j, closedCell n j)` is closed by assumption since `C` has only
    -- finitely many cells.
    rw [← inter_eq_left.2 asubc]
    simp_rw [Filter.eventually_atTop] at eventually_isEmpty_cell
    obtain ⟨N, hN⟩ := eventually_isEmpty_cell
    suffices IsClosed (A ∩ (D ∪ ⋃ (n : {n : ℕ // n < N}), ⋃ j, ↑(map n j) '' closedBall 0 1)) by
      convert! this using 2
      rw [← union', iUnion_subtype]
      congrm D ∪ ⋃ n, ?_
      refine subset_antisymm ?_ (iUnion_subset (fun i ↦ by rfl))
      apply iUnion_subset
      intro i
      have : n < N := Decidable.byContradiction fun h ↦ (hN n (Nat.ge_of_not_lt h)).false i
      exact subset_iUnion₂ (s := fun _ i ↦ (map n i) '' closedBall 0 1) this i
    simp_rw [inter_union_distrib_left, inter_iUnion]
    exact h.2.union (isClosed_iUnion_of_finite (fun n ↦ isClosed_iUnion_of_finite (h.1 n.1)))
  isClosedBase := isClosedBase
  union' := union'

/-- A CW complex that was constructed using `RelCWComplex.mkFinite` is finite. -/
/-
**Topology.RelCWComplex.finite_mkFinite.** 是 Mathlib 中的一个引理，位于命名空间 `Topology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A CW complex that was constructed using `RelCWComplex.mkFinite` is finite.
-/
lemma RelCWComplex.finite_mkFinite.{u} {X : Type u} [TopologicalSpace X] (C : Set X)
    (D : outParam (Set X)) (cell : (n : ℕ) → Type u)
    (map : (n : ℕ) → (i : cell n) → PartialEquiv (Fin n → ℝ) X)
    (eventually_isEmpty_cell : ∀ᶠ n in Filter.atTop, IsEmpty (cell n))
    (finite_cell : ∀ (n : ℕ), _root_.Finite (cell n))
    (source_eq : ∀ (n : ℕ) (i : cell n), (map n i).source = ball 0 1)
    (continuousOn : ∀ (n : ℕ) (i : cell n), ContinuousOn (map n i) (closedBall 0 1))
    (continuousOn_symm : ∀ (n : ℕ) (i : cell n), ContinuousOn (map n i).symm (map n i).target)
    (pairwiseDisjoint' :
      (univ : Set (Σ n, cell n)).PairwiseDisjoint (fun ni ↦ map ni.1 ni.2 '' ball 0 1))
    (disjointBase' : ∀ (n : ℕ) (i : cell n), Disjoint (map n i '' ball 0 1) D)
    (mapsTo : ∀ (n : ℕ) (i : cell n),
      MapsTo (map n i) (sphere 0 1) (D ∪ ⋃ (m < n) (j : cell m), map m j '' closedBall 0 1))
    (isClosedBase : IsClosed D)
    (union' : D ∪ ⋃ (n : ℕ) (j : cell n), map n j '' closedBall 0 1 = C) :
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
/-
**Topology.CWComplex.mkFinite.** 是 Mathlib 中的一个定义，位于命名空间 `Topology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If we want to construct a finite CW complex we can add the conditions `eventuall
y_isEmpty_cell`
and `finite_cell`, relax the condition `mapsTo` and remove the condition `closed
'`.
-/
def CWComplex.mkFinite.{u} {X : Type u} [TopologicalSpace X] (C : Set X)
    (cell : (n : ℕ) → Type u) (map : (n : ℕ) → (i : cell n) → PartialEquiv (Fin n → ℝ) X)
    (eventually_isEmpty_cell : ∀ᶠ n in Filter.atTop, IsEmpty (cell n))
    (finite_cell : ∀ (n : ℕ), _root_.Finite (cell n))
    (source_eq : ∀ (n : ℕ) (i : cell n), (map n i).source = ball 0 1)
    (continuousOn : ∀ (n : ℕ) (i : cell n), ContinuousOn (map n i) (closedBall 0 1))
    (continuousOn_symm : ∀ (n : ℕ) (i : cell n), ContinuousOn (map n i).symm (map n i).target)
    (pairwiseDisjoint' :
      (univ : Set (Σ n, cell n)).PairwiseDisjoint (fun ni ↦ map ni.1 ni.2 '' ball 0 1))
    (mapsTo_iff_image_subset : ∀ (n : ℕ) (i : cell n),
      MapsTo (map n i) (sphere 0 1) (⋃ (m < n) (j : cell m), map m j '' closedBall 0 1))
    (union' : ⋃ (n : ℕ) (j : cell n), map n j '' closedBall 0 1 = C) :
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

/-- A CW complex that was constructed using `CWComplex.mkFinite` is finite. -/
/-
**Topology.CWComplex.finite_mkFinite.** 是 Mathlib 中的一个引理，位于命名空间 `Topology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A CW complex that was constructed using `CWComplex.mkFinite` is finite.
-/
lemma CWComplex.finite_mkFinite.{u} {X : Type u} [TopologicalSpace X] (C : Set X)
    (cell : (n : ℕ) → Type u) (map : (n : ℕ) → (i : cell n) → PartialEquiv (Fin n → ℝ) X)
    (eventually_isEmpty_cell : ∀ᶠ n in Filter.atTop, IsEmpty (cell n))
    (finite_cell : ∀ (n : ℕ), _root_.Finite (cell n))
    (source_eq : ∀ (n : ℕ) (i : cell n), (map n i).source = ball 0 1)
    (continuousOn : ∀ (n : ℕ) (i : cell n), ContinuousOn (map n i) (closedBall 0 1))
    (continuousOn_symm : ∀ (n : ℕ) (i : cell n), ContinuousOn (map n i).symm (map n i).target)
    (pairwiseDisjoint' :
      (univ : Set (Σ n, cell n)).PairwiseDisjoint (fun ni ↦ map ni.1 ni.2 '' ball 0 1))
    (mapsTo : ∀ (n : ℕ) (i : cell n),
      MapsTo (map n i) (sphere 0 1) (⋃ (m < n) (j : cell m), map m j '' closedBall 0 1))
    (union' : ⋃ (n : ℕ) (j : cell n), map n j '' closedBall 0 1 = C) :
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
/-
**Topology.RelCWComplex.finite_of_finite_cells** 是 Mathlib 中的一个定理，位于命名空间 `Topolo
gy.RelCWComplex`。
形式化陈述：∀ {X : Type u_2} [inst : TopologicalSpace X] {C D : Set X} [inst_1 : Topol
ogy.RelCWComplex C D],   Finite ((n : ℕ) × Topology.RelCWComplex.cell C n) → Top
ology.RelCWComplex.Finite C
参数：(n : ℕ) × Topology.RelCWComplex.cell C n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finset.image_nonempty`：image_nonempty : (s.image f).Nonempty ↔ s.Nonempt
y
· 使用定理 `Finset.univ_nonempty`：univ_nonempty [Nonempty α] : (univ : Finset α).Non
empty
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
（共 57 条，此处仅展示前 30 条）

--- 原说明 ---
If the collection of all cells (of any dimension) of a relative CW complex `C` i
s finite, then
`C` is finite as a CW complex.
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
    have hmA : m ∈ A := by
      simp only [Finset.mem_image, Finset.mem_univ, true_and, A]
      simp only [← exists_true_iff_nonempty] at h'
      obtain ⟨j, _⟩ := h'
      use ⟨m, j⟩
    linarith [A.le_max' m hmA]
  finite_cell _ := Finite.of_injective (Sigma.mk _) sigma_mk_injective

/-- If `C` is finite as a CW complex then the collection of all cells (of any dimension) is
finite. -/
@[alias_in CWComplex]
/-
**Topology.RelCWComplex.finite_cells_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `Topolo
gy.RelCWComplex`。
形式化陈述：∀ {X : Type u_2} [inst : TopologicalSpace X] {C D : Set X} [inst_1 : Topol
ogy.RelCWComplex C D]   [finite : Topology.RelCWComplex.Finite C], Finite ((n : 
ℕ) × Topology.RelCWComplex.cell C n)
参数：(n : ℕ) × Topology.RelCWComplex.cell C n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.RelCWComplex.FiniteDimensional.eventually_isEmpty_cell`：∀ {X : 
Type u} {inst : TopologicalSpace X} {C D : Set X} {inst_1 : Topology.RelCWComple
x C D}   [self : Topology.RelCWComplex.FiniteDimensio…
· 使用定理 `Topology.RelCWComplex.Finite.toFiniteDimensional`：∀ {X : Type u_1} {inst
 : TopologicalSpace X} {C D : Set X} {inst_1 : Topology.RelCWComplex C D}   [sel
f : Topology.RelCWComplex.Finite C], T…
· 使用定理 `Topology.RelCWComplex.FiniteType.finite_cell`：∀ {X : Type u} {inst : Top
ologicalSpace X} {C D : Set X} {inst_1 : Topology.RelCWComplex C D}   [self : To
pology.RelCWComplex.FiniteType C] …
· 使用定理 `Topology.RelCWComplex.Finite.toFiniteType`：∀ {X : Type u_1} {inst : Topo
logicalSpace X} {C D : Set X} {inst_1 : Topology.RelCWComplex C D}   [self : Top
ology.RelCWComplex.Finite C], T…
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `IsEmpty.false`：∀ {α : Sort u} [self : IsEmpty α] (a : α), False
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sigma.eta`：∀ {α : Type u_1} {β : α → Type u_4} (x : (a : α) × β a), ⟨x.f
st, x.snd⟩ = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.finite_iff`：Equiv.finite_iff (f : α ≃ β) : Finite α ↔ Finite β
· 使用定理 `Finite.instSigma`：∀ {α : Type u_1} {β : α → Type u_2} [Finite α] [∀ (a :
 α), Finite (β a)], Finite ((a : α) × β a)
· 使用定理 `instFiniteSubtypeLtOfLocallyFiniteOrderBot`：∀ {α : Type u_1} [inst : Pre
order α] {y : α} [LocallyFiniteOrderBot α], Finite { x // x < y }

--- 原说明 ---
If `C` is finite as a CW complex then the collection of all cells (of any dimens
ion) is
finite.
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
  let f : (Σ (m : {m : ℕ // m < n}), cell C m) ≃ Σ m, cell C m := {
    toFun := fun ⟨m, j⟩ ↦ ⟨m, j⟩
    invFun := fun ⟨m, j⟩ ↦ ⟨⟨m, this m j⟩, j⟩
    left_inv := by simp [Function.LeftInverse]
    right_inv := by simp [Function.RightInverse, Function.LeftInverse] }
  rw [← Equiv.finite_iff f]
  exact Finite.instSigma

/-- A CW complex is finite iff the total number of its cells is finite. -/
@[alias_in CWComplex]
/-
**Topology.RelCWComplex.finite_iff_finite_cells** 是 Mathlib 中的一个定理，位于命名空间 `Topol
ogy.RelCWComplex`。
形式化陈述：∀ {X : Type u_2} [inst : TopologicalSpace X] {C D : Set X} [inst_1 : Topol
ogy.RelCWComplex C D],   Topology.RelCWComplex.Finite C ↔ Finite ((n : ℕ) × Topo
logy.RelCWComplex.cell C n)
参数：(n : ℕ) × Topology.RelCWComplex.cell C n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.RelCWComplex.finite_cells_of_finite`：∀ {X : Type u_2} [inst : T
opologicalSpace X] {C D : Set X} [inst_1 : Topology.RelCWComplex C D]   [finite 
: Topology.RelCWComplex.Finite C],…
· 使用定理 `Topology.RelCWComplex.finite_of_finite_cells`：∀ {X : Type u_2} [inst : T
opologicalSpace X] {C D : Set X} [inst_1 : Topology.RelCWComplex C D],   Finite 
((n : ℕ) × Topology.RelCWComplex.c…

--- 原说明 ---
A CW complex is finite iff the total number of its cells is finite.
-/
lemma RelCWComplex.finite_iff_finite_cells : Finite C ↔ _root_.Finite (Σ n, cell C n) :=
  ⟨fun h ↦ finite_cells_of_finite (finite := h), finite_of_finite_cells⟩

end Topology

