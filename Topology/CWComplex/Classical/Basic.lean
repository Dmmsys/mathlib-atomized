/-
Copyright (c) 2024 Floris van Doorn and Hannah Scholz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Hannah Scholz
-/
module

public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Data.ENat.Basic
public import Mathlib.Logic.Equiv.PartialEquiv
public import Mathlib.Util.AliasIn

/-!
# CW complexes

This file defines (relative) CW complexes and proves basic properties about them using the classical
approach of Whitehead.

A CW complex is a topological space that is made by gluing closed disks of different dimensions
together.

## Main definitions
* `RelCWComplex C D`: the class of CW structures on a subspace `C` relative to a base set
  `D` of a topological space `X`.
* `CWComplex C`: an abbreviation for `RelCWComplex C ∅`. The class of CW structures on a
  subspace `C` of the topological space `X`.
* `openCell n`: indexed family of all open cells of dimension `n`.
* `closedCell n`: indexed family of all closed cells of dimension `n`.
* `cellFrontier n`: indexed family of the boundaries of cells of dimension `n`.
* `skeleton C n`: the `n`-skeleton of the (relative) CW complex `C`.

## Main statements
* `iUnion_openCell_eq_skeleton`: the skeletons can also be seen as a union of open cells.
* `cellFrontier_subset_finite_openCell`: the edge of a cell is contained in a finite union of
  open cells of a lower dimension.

## Implementation notes
* We use the historical definition of CW complexes, due to Whitehead: a CW complex is a collection
  of cells with attaching maps - all cells are subspaces of one ambient topological space.
  This way, we avoid having to work with a lot of different topological spaces.
  On the other hand, it requires the union of all cells to be closed.
  If that is not the case, you need to consider that union as a subspace of itself.
* For a categorical approach that defines CW complexes via colimits and transfinite compositions,
  see `Mathlib/Topology/CWComplex/Abstract/Basic.lean`.
  The two approaches are equivalent but serve different purposes:
  * This approach is more convenient for concrete geometric arguments
  * The categorical approach is more suitable for abstract arguments and generalizations
* The definition `RelCWComplex` does not require `X` to be a Hausdorff space.
  A lot of the lemmas will however require this property.
* This definition is a class to ease working with different constructions and their properties.
  Overall this means that being a CW complex is treated more like a property than data.
* The natural number is explicit in `openCell`, `closedCell` and `cellFrontier` because `cell n` and
  `cell m` might be the same type in an explicit CW complex even when `n` and `m` are different.
* `CWComplex` is a separate class from `RelCWComplex`. This not only gives absolute CW complexes a
  better constructor but also aids typeclass inference: a construction on relative CW complexes may
  yield a base that for the special case of CW complexes is provably equal to the empty set but not
  definitionally so. In that case we define an instance specifically for absolute CW complexes and
  want this to be inferred over the relative version. Since the base is an `outParam` this is
  especially necessary since you cannot provide typeclass inference with a specified base.
  But having the type `CWComplex` be separate from `RelCWComplex` makes this specification possible.
* For a similar reason to the previous bullet point we make the instance
  `CWComplex.instRelCWComplex` have high priority. For example, when talking about the type of
  cells `cell C` of an absolute CW complex `C`, this actually refers to `RelCWComplex.cell C`
  through this instance. Again, we want typeclass inference to first consider absolute CW
  structures.
* The namespaces `CWComplex` and `RelCWComplex` generally should not be opened at the same time
  as they contain many declarations with identical names. Still, we want working with absolute
  CW complexes to be as convenient as possible. Thus every declaration about relative CW complexes
  that doesn't have a modified version for absolute CW complexes should receive an alias in the
  `CWComplex` namespace. It is recommended to use the `alias_in` attribute for this here. See
  below for a restriction on when we want to create aliases.
* For types and definitions relevant to CW complexes like `cell`, `openCell`, `closedCell`,
  `cellFrontier`, `skeletonLT` and similar, we want there to exist only one actually used version,
  namely the version in the `RelCWComplex` namespace (and thus no separate definition in the
  `CWComplex` namespace.) This is to avoid unnecessary duplication of lemmas. To achieve this,
  definitions from the `RelCWComplex` namespace should be added to the `CWComplex` namespace with
  `export` instead of `alias_in`/`alias`. These will then apply to the absolute CW complex through
  the instance `CWComplex.instRelCWComplex`.
* For statements, the auxiliary construction `skeletonLT` is preferred over `skeleton` as it makes
  the base case of inductions easier. The statement about `skeleton` should then be derived from the
  one about `skeletonLT`.

## References
* [A. Hatcher, *Algebraic Topology*][hatcher02]
-/

@[expose] public section

noncomputable section

open Metric Set Function

namespace Topology

/--
Definition of `RelCWComplex.` / `RelCWComplex.` 的定义

English:
class RelCWComplex.{u}
  parameters: {X : Type u} [TopologicalSpace X] (C : Set X) (D : outParam (Set X))
  axioms and operations (11):
    - cell((n : Nat)) : Type u
    - map((n : Nat) (i : cell n)) : PartialEquiv (Fin n -> Real) X
    - source_eq((n : Nat) (i : cell n)) : (map n i).source = ball 0 1
    - continuousOn((n : Nat) (i : cell n)) : ContinuousOn (map n i) (closedBall 0 1)
    - continuousOn_symm((n : Nat) (i : cell n)) : ContinuousOn (map n i).symm (map n i).target
    - pairwiseDisjoint' : (univ : Set (Σ n, cell n)).PairwiseDisjoint (fun ni => map ni.1 ni.2 '' ball 0 1)
    - disjointBase'((n : Nat) (i : cell n)) : Disjoint (map n i '' ball 0 1) D
    - mapsTo((n : Nat) (i : cell n)) : exists I : Π m, Finset (cell m), MapsTo (map n i) (sphere 0 1) (D union ⋃ (m < n) (j in I m), map m j '' closedBall 0 1)
    - closed'((A : Set X) (hAC : A subseteq C)) : ((forall n j, IsClosed (A inter map n j '' closedBall 0 1)) ∧ IsClosed (A inter D)) -> IsClosed A
    - isClosedBase : IsClosed D
    - union' : D union ⋃ (n : Nat) (j : cell n), map n j '' closedBall 0 1 = C

中文:
类 RelCWComplex.{u}
  参数: {X : 类型u} [拓扑空间 X] (C : 集合 X) (D : outParam (集合 X))
  公理与运算 (11 个):
    - cell((n : 自然数)) : 类型u
    - map((n : 自然数) (i : cell n)) : 部分等价 (有限集 n -> 实数) X
    - source_eq((n : 自然数) (i : cell n)) : (map n i).source = ball 0 1
    - continuousOn((n : 自然数) (i : cell n)) : ContinuousOn (map n i) (closedBall 0 1)
    - continuousOn_symm((n : 自然数) (i : cell n)) : ContinuousOn (map n i).symm (map n i).target
    - pairwiseDisjoint' : (univ : 集合 (Σ n, cell n)).PairwiseDisjoint (fun ni => map ni.1 ni.2 '' ball 0 1)
    - disjointBase'((n : 自然数) (i : cell n)) : Disjoint (map n i '' ball 0 1) D
    - mapsTo((n : 自然数) (i : cell n)) : 存在 I : Π m, 有限集 (cell m), 映射到 (map n i) (sphere 0 1) (D union ⋃ (m < n) (j in I m), map m j '' closedBall 0 1)
    - closed'((A : 集合 X) (hAC : A subseteq C)) : ((对任意 n j, 是闭集 (A inter map n j '' closedBall 0 1)) ∧ 是闭集 (A inter D)) -> 是闭集 A
    - isClosedBase : 是闭集 D
    - union' : D union ⋃ (n : 自然数) (j : cell n), map n j '' closedBall 0 1 = C
-/
class RelCWComplex.{u} {X : Type u} [TopologicalSpace X] (C : Set X) (D : outParam (Set X)) where
  /-- The indexing type of the cells of dimension `n`. -/
  cell (n : Nat) : Type u
  /-- The characteristic map of the `n`-cell given by the index `i`.
  This map is a bijection when restricting to `ball 0 1`, where we consider `(Fin n → ℝ)`
  endowed with the maximum metric. -/
  map (n : Nat) (i : cell n) : PartialEquiv (Fin n -> Real) X
  /-- The source of every characteristic map of dimension `n` is
  `(ball 0 1 : Set (Fin n → ℝ))`. -/
  source_eq (n : Nat) (i : cell n) : (map n i).source = ball 0 1
  /-- The characteristic maps are continuous when restricting to `closedBall 0 1`. -/
  continuousOn (n : Nat) (i : cell n) : ContinuousOn (map n i) (closedBall 0 1)
  /-- The inverse of the restriction to `ball 0 1` is continuous on the image. -/
  continuousOn_symm (n : Nat) (i : cell n) : ContinuousOn (map n i).symm (map n i).target
  /-- The open cells are pairwise disjoint. Use `RelCWComplex.pairwiseDisjoint` or
  `RelCWComplex.disjoint_openCell_of_ne` instead. -/
  pairwiseDisjoint' :
    (univ : Set (Σ n, cell n)).PairwiseDisjoint (fun ni => map ni.1 ni.2 '' ball 0 1)
  /-- All open cells are disjoint with the base. Use `RelCWComplex.disjointBase` instead. -/
  disjointBase' (n : Nat) (i : cell n) : Disjoint (map n i '' ball 0 1) D
  /-- The boundary of a cell is contained in the union of the base with a finite union of closed
  cells of a lower dimension. Use `RelCWComplex.cellFrontier_subset_base_union_finite_closedCell`
  instead. -/
  mapsTo (n : Nat) (i : cell n) : exists I : Π m, Finset (cell m),
    MapsTo (map n i) (sphere 0 1) (D union ⋃ (m < n) (j in I m), map m j '' closedBall 0 1)
  /-- A CW complex has weak topology, i.e. a set `A` in `X` is closed iff its intersection with
  every closed cell and `D` is closed. Use `RelCWComplex.closed` instead. -/
  closed' (A : Set X) (hAC : A subseteq C) :
    ((forall n j, IsClosed (A inter map n j '' closedBall 0 1)) ∧ IsClosed (A inter D)) -> IsClosed A
  /-- The base `D` is closed. -/
  isClosedBase : IsClosed D
  /-- The union of all closed cells equals `C`. Use `RelCWComplex.union` instead. -/
  union' : D union ⋃ (n : Nat) (j : cell n), map n j '' closedBall 0 1 = C

/--
Definition of `CWComplex.` / `CWComplex.` 的定义

English:
class CWComplex.{u}
  parameters: {X : Type u} [TopologicalSpace X] (C : Set X)
  axioms and operations (9):
    - cell((n : Nat)) : Type u
    - map((n : Nat) (i : cell n)) : PartialEquiv (Fin n -> Real) X
    - source_eq((n : Nat) (i : cell n)) : (map n i).source = ball 0 1
    - continuousOn((n : Nat) (i : cell n)) : ContinuousOn (map n i) (closedBall 0 1)
    - continuousOn_symm((n : Nat) (i : cell n)) : ContinuousOn (map n i).symm (map n i).target
    - pairwiseDisjoint' : (univ : Set (Σ n, cell n)).PairwiseDisjoint (fun ni => map ni.1 ni.2 '' ball 0 1)
    - mapsTo'((n : Nat) (i : cell n)) : exists I : Π m, Finset (cell m), MapsTo (map n i) (sphere 0 1) (⋃ (m < n) (j in I m), map m j '' closedBall 0 1)
    - closed'((A : Set X) (hAC : A subseteq C)) : (forall n j, IsClosed (A inter map n j '' closedBall 0 1)) -> IsClosed A
    - union' : ⋃ (n : Nat) (j : cell n), map n j '' closedBall 0 1 = C

中文:
类 CWComplex.{u}
  参数: {X : 类型u} [拓扑空间 X] (C : 集合 X)
  公理与运算 (9 个):
    - cell((n : 自然数)) : 类型u
    - map((n : 自然数) (i : cell n)) : 部分等价 (有限集 n -> 实数) X
    - source_eq((n : 自然数) (i : cell n)) : (map n i).source = ball 0 1
    - continuousOn((n : 自然数) (i : cell n)) : ContinuousOn (map n i) (closedBall 0 1)
    - continuousOn_symm((n : 自然数) (i : cell n)) : ContinuousOn (map n i).symm (map n i).target
    - pairwiseDisjoint' : (univ : 集合 (Σ n, cell n)).PairwiseDisjoint (fun ni => map ni.1 ni.2 '' ball 0 1)
    - mapsTo'((n : 自然数) (i : cell n)) : 存在 I : Π m, 有限集 (cell m), 映射到 (map n i) (sphere 0 1) (⋃ (m < n) (j in I m), map m j '' closedBall 0 1)
    - closed'((A : 集合 X) (hAC : A subseteq C)) : (对任意 n j, 是闭集 (A inter map n j '' closedBall 0 1)) -> 是闭集 A
    - union' : ⋃ (n : 自然数) (j : cell n), map n j '' closedBall 0 1 = C
-/
class CWComplex.{u} {X : Type u} [TopologicalSpace X] (C : Set X) where
  /-- The indexing type of the cells of dimension `n`. -/
  protected cell (n : Nat) : Type u
  /-- The characteristic map of the `n`-cell given by the index `i`.
  This map is a bijection when restricting to `ball 0 1`, where we consider `(Fin n → ℝ)`
  endowed with the maximum metric. -/
  protected map (n : Nat) (i : cell n) : PartialEquiv (Fin n -> Real) X
  /-- The source of every characteristic map of dimension `n` is
  `(ball 0 1 : Set (Fin n → ℝ))`. -/
  protected source_eq (n : Nat) (i : cell n) : (map n i).source = ball 0 1
  /-- The characteristic maps are continuous when restricting to `closedBall 0 1`. -/
  protected continuousOn (n : Nat) (i : cell n) : ContinuousOn (map n i) (closedBall 0 1)
  /-- The inverse of the restriction to `ball 0 1` is continuous on the image. -/
  protected continuousOn_symm (n : Nat) (i : cell n) : ContinuousOn (map n i).symm (map n i).target
  /-- The open cells are pairwise disjoint. Use `CWComplex.pairwiseDisjoint` or
  `CWComplex.disjoint_openCell_of_ne` instead. -/
  protected pairwiseDisjoint' :
    (univ : Set (Σ n, cell n)).PairwiseDisjoint (fun ni => map ni.1 ni.2 '' ball 0 1)
  /-- The boundary of a cell is contained in a finite union of closed cells of a lower dimension.
  Use `CWComplex.mapsTo` or `CWComplex.cellFrontier_subset_finite_closedCell` instead. -/
  protected mapsTo' (n : Nat) (i : cell n) : exists I : Π m, Finset (cell m),
    MapsTo (map n i) (sphere 0 1) (⋃ (m < n) (j in I m), map m j '' closedBall 0 1)
  /-- A CW complex has weak topology, i.e. a set `A` in `X` is closed iff its intersection with
  every closed cell is closed. Use `CWComplex.closed` instead. -/
  protected closed' (A : Set X) (hAC : A subseteq C) :
    (forall n j, IsClosed (A inter map n j '' closedBall 0 1)) -> IsClosed A
  /-- The union of all closed cells equals `C`. Use `CWComplex.union` instead. -/
  protected union' : ⋃ (n : Nat) (j : cell n), map n j '' closedBall 0 1 = C

@[simps -isSimp]
instance (priority := high) CWComplex.instRelCWComplex {X : Type*} [TopologicalSpace X] (C : Set X)
    [CWComplex C] : RelCWComplex C ∅ where
  cell := CWComplex.cell C
  map := CWComplex.map
  source_eq := CWComplex.source_eq
  continuousOn := CWComplex.continuousOn
  continuousOn_symm := CWComplex.continuousOn_symm
  pairwiseDisjoint' := CWComplex.pairwiseDisjoint'
  disjointBase' := by simp [disjoint_empty]
  mapsTo := by simpa only [empty_union] using CWComplex.mapsTo'
  closed' := by simpa only [inter_empty, isClosed_empty, and_true] using CWComplex.closed'
  isClosedBase := isClosed_empty
  union' := by simpa only [empty_union] using CWComplex.union'

/-- A relative CW complex with an empty base is an absolute CW complex. -/
@[simps -isSimp, instance_reducible]
/--
Definition of `RelCWComplex.toCWComplex` / `RelCWComplex.toCWComplex` 的定义

English:
definition RelCWComplex.toCWComplex
  signature: {X : Type*} [TopologicalSpace X] (C : Set X) [RelCWComplex C ∅]
  body: cell C
  map := map
  source_eq := source_eq
  continuousOn := continuousOn
  continuousOn_symm := continuousOn_symm
  pairwiseDisjoint' := pairwiseDisjoint'
  mapsTo' := by simpa using mapsTo (C := C)
  closed' := by simpa using closed' (C := C)
  union' := by simpa using union' (C := C)

中文:
定义 RelCWComplex.toCWComplex
  签名: {X : 类型} [拓扑空间 X] (C : 集合 X) [RelCWComplex C ∅]
  定义体: cell C
  map := map
  source_eq := source_eq
  continuousOn := continuousOn
  continuousOn_symm := continuousOn_symm
  pairwiseDisjoint' := pairwiseDisjoint'
  mapsTo' := by simpa using mapsTo (C := C)
  closed' := by simpa using closed' (C := C)
  union' := by simpa using union' (C := C)
-/
def RelCWComplex.toCWComplex {X : Type*} [TopologicalSpace X] (C : Set X) [RelCWComplex C ∅] :
    CWComplex C where
  cell := cell C
  map := map
  source_eq := source_eq
  continuousOn := continuousOn
  continuousOn_symm := continuousOn_symm
  pairwiseDisjoint' := pairwiseDisjoint'
  mapsTo' := by simpa using mapsTo (C := C)
  closed' := by simpa using closed' (C := C)
  union' := by simpa using union' (C := C)

/--
lemma `RelCWComplex.toCWComplex_eq` / 引理 `RelCWComplex.toCWComplex_eq`

English:
lemma RelCWComplex.toCWComplex_eq
  statement: {X : Type*} [TopologicalSpace X] (C : Set X)
  proof: rfl

中文:
引理 RelCWComplex.toCWComplex_eq
  结论: {X : 类型} [拓扑空间 X] (C : 集合 X)
  证明: rfl
-/
lemma RelCWComplex.toCWComplex_eq {X : Type*} [TopologicalSpace X] (C : Set X)
    [h : RelCWComplex C ∅] : (toCWComplex C).instRelCWComplex = h :=
  rfl

variable {X : Type*} [t : TopologicalSpace X] {C D : Set X}

/--
Definition of `RelCWComplex.openCell` / `RelCWComplex.openCell` 的定义

English:
definition RelCWComplex.openCell
  signature: [RelCWComplex C D] (n : Nat) (i : cell C n)
  body: map n i '' ball 0 1

中文:
定义 RelCWComplex.openCell
  签名: [RelCWComplex C D] (n : 自然数) (i : cell C n)
  定义体: map n i '' ball 0 1
-/
def RelCWComplex.openCell [RelCWComplex C D] (n : Nat) (i : cell C n) : Set X := map n i '' ball 0 1

/--
Definition of `RelCWComplex.closedCell` / `RelCWComplex.closedCell` 的定义

English:
definition RelCWComplex.closedCell
  signature: [RelCWComplex C D] (n : Nat) (i : cell C n)
  body: map n i '' closedBall 0 1

中文:
定义 RelCWComplex.closedCell
  签名: [RelCWComplex C D] (n : 自然数) (i : cell C n)
  定义体: map n i '' closedBall 0 1

Depends on / 依赖: closedBall
-/
def RelCWComplex.closedCell [RelCWComplex C D] (n : Nat) (i : cell C n) : Set X :=
  map n i '' closedBall 0 1

/--
Definition of `RelCWComplex.cellFrontier` / `RelCWComplex.cellFrontier` 的定义

English:
definition RelCWComplex.cellFrontier
  signature: [RelCWComplex C D] (n : Nat) (i : cell C n)
  body: map n i '' sphere 0 1

中文:
定义 RelCWComplex.cellFrontier
  签名: [RelCWComplex C D] (n : 自然数) (i : cell C n)
  定义体: map n i '' sphere 0 1

Depends on / 依赖: sphere
-/
def RelCWComplex.cellFrontier [RelCWComplex C D] (n : Nat) (i : cell C n) : Set X :=
  map n i '' sphere 0 1

namespace CWComplex

export RelCWComplex (cell map source_eq continuousOn continuousOn_symm isClosedBase openCell
  closedCell cellFrontier)

end CWComplex

/--
lemma `CWComplex.mapsTo` / 引理 `CWComplex.mapsTo`

English:
lemma CWComplex.mapsTo
  given: [CWComplex C] (n : Nat) (i : cell C n)
  statement: exists I : Π m, Finset (cell C m),
  proof: by
  have := RelCWComplex.mapsTo n i
  simp_rw [empty_union] at this
  exact this

@[alias_in CWComplex]

中文:
引理 CWComplex.mapsTo
  条件: [CWComplex C] (n : 自然数) (i : cell C n)
  结论: 存在 I : Π m, 有限集 (cell C m),
  证明: by
  have := RelCWComplex.mapsTo n i
  simp_rw [empty_union] at this
  exact this

@[alias_in CWComplex]

Depends on / 依赖: RelCWComplex, RelCWComplex.mapsTo, empty_union, mapsTo, simp_rw
-/
lemma CWComplex.mapsTo [CWComplex C] (n : Nat) (i : cell C n) : exists I : Π m, Finset (cell C m),
    MapsTo (map n i) (sphere 0 1) (⋃ (m < n) (j in I m), map m j '' closedBall 0 1) := by
  have := RelCWComplex.mapsTo n i
  simp_rw [empty_union] at this
  exact this

@[alias_in CWComplex]
/--
lemma `RelCWComplex.pairwiseDisjoint` / 引理 `RelCWComplex.pairwiseDisjoint`

English:
lemma RelCWComplex.pairwiseDisjoint
  given: [RelCWComplex C D]
  proof: RelCWComplex.pairwiseDisjoint'

@[alias_in CWComplex]

中文:
引理 RelCWComplex.pairwiseDisjoint
  条件: [RelCWComplex C D]
  证明: RelCWComplex.pairwiseDisjoint'

@[alias_in CWComplex]

Depends on / 依赖: RelCWComplex, RelCWComplex.pairwiseDisjoint, pairwiseDisjoint
-/
lemma RelCWComplex.pairwiseDisjoint [RelCWComplex C D] :
    (univ : Set (Σ n, cell C n)).PairwiseDisjoint (fun ni => openCell ni.1 ni.2) :=
  RelCWComplex.pairwiseDisjoint'

@[alias_in CWComplex]
/--
lemma `RelCWComplex.disjointBase` / 引理 `RelCWComplex.disjointBase`

English:
lemma RelCWComplex.disjointBase
  given: [RelCWComplex C D] (n : Nat) (i : cell C n)
  proof: RelCWComplex.disjointBase' n i

@[alias_in CWComplex]

中文:
引理 RelCWComplex.disjointBase
  条件: [RelCWComplex C D] (n : 自然数) (i : cell C n)
  证明: RelCWComplex.disjointBase' n i

@[alias_in CWComplex]

Depends on / 依赖: RelCWComplex, RelCWComplex.disjointBase, disjointBase
-/
lemma RelCWComplex.disjointBase [RelCWComplex C D] (n : Nat) (i : cell C n) :
    Disjoint (openCell n i) D :=
  RelCWComplex.disjointBase' n i

@[alias_in CWComplex]
/--
lemma `RelCWComplex.disjoint_openCell_of_ne` / 引理 `RelCWComplex.disjoint_openCell_of_ne`

English:
lemma RelCWComplex.disjoint_openCell_of_ne
  statement: [RelCWComplex C D] {n m : Nat} {i : cell C n}
  proof: pairwiseDisjoint (mem_univ _) (mem_univ _) ne

中文:
引理 RelCWComplex.disjoint_openCell_of_ne
  结论: [RelCWComplex C D] {n m : 自然数} {i : cell C n}
  证明: pairwiseDisjoint (mem_univ _) (mem_univ _) ne

Depends on / 依赖: mem_univ, pairwiseDisjoint
-/
lemma RelCWComplex.disjoint_openCell_of_ne [RelCWComplex C D] {n m : Nat} {i : cell C n}
    {j : cell C m} (ne : (⟨n, i⟩ : Σ n, cell C n) != ⟨m, j⟩) :
    Disjoint (openCell n i) (openCell m j) :=
  pairwiseDisjoint (mem_univ _) (mem_univ _) ne

/--
lemma `RelCWComplex.cellFrontier_subset_base_union_finite_closedCell` / 引理 `RelCWComplex.cellFrontier_subset_base_union_finite_closedCell`

English:
lemma RelCWComplex.cellFrontier_subset_base_union_finite_closedCell
  statement: [RelCWComplex C D]
  proof: by
  rcases mapsTo n i with ⟨I, hI⟩
  use I
  rw [mapsTo_iff_image_subset] at hI
  exact hI

中文:
引理 RelCWComplex.cellFrontier_subset_base_union_finite_closedCell
  结论: [RelCWComplex C D]
  证明: by
  rcases mapsTo n i with ⟨I, hI⟩
  use I
  rw [mapsTo_iff_image_subset] at hI
  exact hI

Depends on / 依赖: mapsTo, mapsTo_iff_image_subset
-/
lemma RelCWComplex.cellFrontier_subset_base_union_finite_closedCell [RelCWComplex C D]
    (n : Nat) (i : cell C n) : exists I : Π m, Finset (cell C m), cellFrontier n i subseteq
    D union ⋃ (m < n) (j in I m), closedCell m j := by
  rcases mapsTo n i with ⟨I, hI⟩
  use I
  rw [mapsTo_iff_image_subset] at hI
  exact hI

/--
lemma `CWComplex.cellFrontier_subset_finite_closedCell` / 引理 `CWComplex.cellFrontier_subset_finite_closedCell`

English:
lemma CWComplex.cellFrontier_subset_finite_closedCell
  given: [CWComplex C] (n : Nat) (i : cell C n)
  proof: by
  rcases RelCWComplex.mapsTo n i with ⟨I, hI⟩
  use I
  rw [mapsTo_iff_image_subset]; rw [empty_union] at hI
  exact hI

中文:
引理 CWComplex.cellFrontier_subset_finite_closedCell
  条件: [CWComplex C] (n : 自然数) (i : cell C n)
  证明: by
  rcases RelCWComplex.mapsTo n i with ⟨I, hI⟩
  use I
  rw [mapsTo_iff_image_subset]; rw [empty_union] at hI
  exact hI

Depends on / 依赖: RelCWComplex, RelCWComplex.mapsTo, empty_union, mapsTo, mapsTo_iff_image_subset
-/
lemma CWComplex.cellFrontier_subset_finite_closedCell [CWComplex C] (n : Nat) (i : cell C n) :
    exists I : Π m, Finset (cell C m), cellFrontier n i subseteq ⋃ (m < n) (j in I m), closedCell m j := by
  rcases RelCWComplex.mapsTo n i with ⟨I, hI⟩
  use I
  rw [mapsTo_iff_image_subset]; rw [empty_union] at hI
  exact hI

/--
lemma `RelCWComplex.union` / 引理 `RelCWComplex.union`

English:
lemma RelCWComplex.union
  given: [RelCWComplex C D]
  statement: D union ⋃ (n : Nat) (j : cell C n), closedCell n j = C
  proof: RelCWComplex.union'

中文:
引理 RelCWComplex.union
  条件: [RelCWComplex C D]
  结论: D union ⋃ (n : 自然数) (j : cell C n), closedCell n j = C
  证明: RelCWComplex.union'

Depends on / 依赖: RelCWComplex, RelCWComplex.union
-/
lemma RelCWComplex.union [RelCWComplex C D] : D union ⋃ (n : Nat) (j : cell C n), closedCell n j = C :=
  RelCWComplex.union'

/--
lemma `CWComplex.union` / 引理 `CWComplex.union`

English:
lemma CWComplex.union
  given: [CWComplex C]
  statement: ⋃ (n : Nat) (j : cell C n), closedCell n j = C
  proof: by
  have := RelCWComplex.union' (C := C)
  rw [empty_union] at this
  exact this

@[alias_in CWComplex]

中文:
引理 CWComplex.union
  条件: [CWComplex C]
  结论: ⋃ (n : 自然数) (j : cell C n), closedCell n j = C
  证明: by
  have := RelCWComplex.union' (C := C)
  rw [empty_union] at this
  exact this

@[alias_in CWComplex]

Depends on / 依赖: RelCWComplex, RelCWComplex.union, empty_union
-/
lemma CWComplex.union [CWComplex C] : ⋃ (n : Nat) (j : cell C n), closedCell n j = C := by
  have := RelCWComplex.union' (C := C)
  rw [empty_union] at this
  exact this

@[alias_in CWComplex]
/--
lemma `RelCWComplex.openCell_subset_closedCell` / 引理 `RelCWComplex.openCell_subset_closedCell`

English:
lemma RelCWComplex.openCell_subset_closedCell
  given: [RelCWComplex C D] (n : Nat) (i : cell C n)
  proof: image_mono Metric.ball_subset_closedBall

@[alias_in CWComplex]

中文:
引理 RelCWComplex.openCell_subset_closedCell
  条件: [RelCWComplex C D] (n : 自然数) (i : cell C n)
  证明: image_mono Metric.ball_subset_closedBall

@[alias_in CWComplex]

Depends on / 依赖: Metric, Metric.ball_subset_closedBall, ball_subset_closedBall, image_mono
-/
lemma RelCWComplex.openCell_subset_closedCell [RelCWComplex C D] (n : Nat) (i : cell C n) :
    openCell n i subseteq closedCell n i := image_mono Metric.ball_subset_closedBall

@[alias_in CWComplex]
/--
lemma `RelCWComplex.cellFrontier_subset_closedCell` / 引理 `RelCWComplex.cellFrontier_subset_closedCell`

English:
lemma RelCWComplex.cellFrontier_subset_closedCell
  given: [RelCWComplex C D] (n : Nat) (i : cell C n)
  proof: image_mono Metric.sphere_subset_closedBall

@[alias_in CWComplex]

中文:
引理 RelCWComplex.cellFrontier_subset_closedCell
  条件: [RelCWComplex C D] (n : 自然数) (i : cell C n)
  证明: image_mono Metric.sphere_subset_closedBall

@[alias_in CWComplex]

Depends on / 依赖: Metric, Metric.sphere_subset_closedBall, image_mono, sphere_subset_closedBall
-/
lemma RelCWComplex.cellFrontier_subset_closedCell [RelCWComplex C D] (n : Nat) (i : cell C n) :
    cellFrontier n i subseteq closedCell n i := image_mono Metric.sphere_subset_closedBall

@[alias_in CWComplex]
/--
lemma `RelCWComplex.cellFrontier_union_openCell_eq_closedCell` / 引理 `RelCWComplex.cellFrontier_union_openCell_eq_closedCell`

English:
lemma RelCWComplex.cellFrontier_union_openCell_eq_closedCell
  statement: [RelCWComplex C D] (n : Nat)
  proof: by
  rw [cellFrontier]; rw [openCell]; rw [closedCell]; rw [← image_union]
  congrm map n i '' ?_
  exact sphere_union_ball

@[alias_in CWComplex]

中文:
引理 RelCWComplex.cellFrontier_union_openCell_eq_closedCell
  结论: [RelCWComplex C D] (n : 自然数)
  证明: by
  rw [cellFrontier]; rw [openCell]; rw [closedCell]; rw [← image_union]
  congrm map n i '' ?_
  exact sphere_union_ball

@[alias_in CWComplex]

Depends on / 依赖: cellFrontier, closedCell, congrm, image_union, openCell, sphere_union_ball
-/
lemma RelCWComplex.cellFrontier_union_openCell_eq_closedCell [RelCWComplex C D] (n : Nat)
    (i : cell C n) : cellFrontier n i union openCell n i = closedCell n i := by
  rw [cellFrontier]; rw [openCell]; rw [closedCell]; rw [← image_union]
  congrm map n i '' ?_
  exact sphere_union_ball

@[alias_in CWComplex]
/--
lemma `RelCWComplex.map_zero_mem_openCell` / 引理 `RelCWComplex.map_zero_mem_openCell`

English:
lemma RelCWComplex.map_zero_mem_openCell
  given: [RelCWComplex C D] (n : Nat) (i : cell C n)
  proof: by
  apply mem_image_of_mem
  simp only [mem_ball, dist_self, zero_lt_one]

@[alias_in CWComplex]

中文:
引理 RelCWComplex.map_zero_mem_openCell
  条件: [RelCWComplex C D] (n : 自然数) (i : cell C n)
  证明: by
  apply mem_image_of_mem
  simp only [mem_ball, dist_self, zero_lt_one]

@[alias_in CWComplex]

Depends on / 依赖: dist_self, mem_ball, mem_image_of_mem, zero_lt_one
-/
lemma RelCWComplex.map_zero_mem_openCell [RelCWComplex C D] (n : Nat) (i : cell C n) :
    map n i 0 in openCell n i := by
  apply mem_image_of_mem
  simp only [mem_ball, dist_self, zero_lt_one]

@[alias_in CWComplex]
/--
lemma `RelCWComplex.map_zero_mem_closedCell` / 引理 `RelCWComplex.map_zero_mem_closedCell`

English:
lemma RelCWComplex.map_zero_mem_closedCell
  given: [RelCWComplex C D] (n : Nat) (i : cell C n)
  proof: openCell_subset_closedCell _ _ (map_zero_mem_openCell _ _)

中文:
引理 RelCWComplex.map_zero_mem_closedCell
  条件: [RelCWComplex C D] (n : 自然数) (i : cell C n)
  证明: openCell_subset_closedCell _ _ (map_zero_mem_openCell _ _)

Depends on / 依赖: map_zero_mem_openCell, openCell_subset_closedCell
-/
lemma RelCWComplex.map_zero_mem_closedCell [RelCWComplex C D] (n : Nat) (i : cell C n) :
    map n i 0 in closedCell n i :=
  openCell_subset_closedCell _ _ (map_zero_mem_openCell _ _)

/--
lemma `RelCWComplex.openCell_nonempty` / 引理 `RelCWComplex.openCell_nonempty`

English:
lemma RelCWComplex.openCell_nonempty
  given: [RelCWComplex C D] (n : Nat) (j : cell C n)
  proof: ⟨(map n j) 0, map_zero_mem_openCell n j⟩

中文:
引理 RelCWComplex.openCell_nonempty
  条件: [RelCWComplex C D] (n : 自然数) (j : cell C n)
  证明: ⟨(map n j) 0, map_zero_mem_openCell n j⟩

Depends on / 依赖: map_zero_mem_openCell
-/
lemma RelCWComplex.openCell_nonempty [RelCWComplex C D] (n : Nat) (j : cell C n) :
    (openCell n j).Nonempty :=
  ⟨(map n j) 0, map_zero_mem_openCell n j⟩

/--
lemma `RelCWComplex.closedCell_nonempty` / 引理 `RelCWComplex.closedCell_nonempty`

English:
lemma RelCWComplex.closedCell_nonempty
  given: [RelCWComplex C D] (n : Nat) (j : cell C n)
  proof: ⟨(map n j) 0, map_zero_mem_closedCell n j⟩

中文:
引理 RelCWComplex.closedCell_nonempty
  条件: [RelCWComplex C D] (n : 自然数) (j : cell C n)
  证明: ⟨(map n j) 0, map_zero_mem_closedCell n j⟩

Depends on / 依赖: map_zero_mem_closedCell
-/
lemma RelCWComplex.closedCell_nonempty [RelCWComplex C D] (n : Nat) (j : cell C n) :
    (closedCell n j).Nonempty :=
  ⟨(map n j) 0, map_zero_mem_closedCell n j⟩

/--
lemma `RelCWComplex.openCell_congr` / 引理 `RelCWComplex.openCell_congr`

English:
lemma RelCWComplex.openCell_congr
  statement: [RelCWComplex C D] (n : Nat) {s t : cell C n}
  proof: by
  contrapose! st
  exact (disjoint_openCell_of_ne (by simpa)).ne (openCell_nonempty n s).ne_empty

中文:
引理 RelCWComplex.openCell_congr
  结论: [RelCWComplex C D] (n : 自然数) {s t : cell C n}
  证明: by
  contrapose! st
  exact (disjoint_openCell_of_ne (by simpa)).ne (openCell_nonempty n s).ne_empty

Depends on / 依赖: contrapose, disjoint_openCell_of_ne, ne_empty, openCell_nonempty
-/
lemma RelCWComplex.openCell_congr [RelCWComplex C D] (n : Nat) {s t : cell C n}
    (st : openCell n s = openCell n t) : s = t := by
  contrapose! st
  exact (disjoint_openCell_of_ne (by simpa)).ne (openCell_nonempty n s).ne_empty

/--
lemma `RelCWComplex.subset_of_eq_union_iUnion` / 引理 `RelCWComplex.subset_of_eq_union_iUnion`

English:
lemma RelCWComplex.subset_of_eq_union_iUnion
  statement: [RelCWComplex C D] (I J : Π n, Set (cell C n))
  proof: by
  intro i hi
  by_contra hJ
  have h : openCell n i subseteq D union ⋃ n, ⋃ (j : J n), openCell (C := C) n j :=
    hIJ.symm ▸ subset_union_of_subset_right
      (subset_iUnion_of_subset n (subset_iUnion_of_subset ⟨i, hi⟩ (subset_refl (openCell n i)))) D
  have h' : Disjoint (openCell n i) (D union ⋃ n, ⋃ (j : J n), openCell (C := C) n j) := by
    simp_rw [disjoint_union_right, disjoint_iUnion_right]
    exact ⟨disjointBase n i, fun m j => disjoint_openCell_of_ne (by lia)⟩
  rw [disjoint_of_subset_iff_left_eq_empty h] at h'
  exact notMem_empty _ (h' ▸ map_zero_mem_openCell n i)

中文:
引理 RelCWComplex.subset_of_eq_union_iUnion
  结论: [RelCWComplex C D] (I J : Π n, 集合 (cell C n))
  证明: by
  intro i hi
  by_contra hJ
  have h : openCell n i subseteq D union ⋃ n, ⋃ (j : J n), openCell (C := C) n j :=
    hIJ.symm ▸ subset_union_of_subset_right
      (subset_iUnion_of_subset n (subset_iUnion_of_subset ⟨i, hi⟩ (subset_refl (openCell n i)))) D
  have h' : Disjoint (openCell n i) (D union ⋃ n, ⋃ (j : J n), openCell (C := C) n j) := by
    simp_rw [disjoint_union_right, disjoint_iUnion_right]
    exact ⟨disjointBase n i, fun m j => disjoint_openCell_of_ne (by lia)⟩
  rw [disjoint_of_subset_iff_left_eq_empty h] at h'
  exact notMem_empty _ (h' ▸ map_zero_mem_openCell n i)
-/
private lemma RelCWComplex.subset_of_eq_union_iUnion [RelCWComplex C D] (I J : Π n, Set (cell C n))
    (hIJ : D union ⋃ (n : Nat) (j : I n), openCell (C := C) n j =
      D union ⋃ (n : Nat) (j : J n), openCell (C := C) n j) (n : Nat) :
    I n subseteq J n := by
  intro i hi
  by_contra hJ
  have h : openCell n i subseteq D union ⋃ n, ⋃ (j : J n), openCell (C := C) n j :=
    hIJ.symm ▸ subset_union_of_subset_right
      (subset_iUnion_of_subset n (subset_iUnion_of_subset ⟨i, hi⟩ (subset_refl (openCell n i)))) D
  have h' : Disjoint (openCell n i) (D union ⋃ n, ⋃ (j : J n), openCell (C := C) n j) := by
    simp_rw [disjoint_union_right, disjoint_iUnion_right]
    exact ⟨disjointBase n i, fun m j => disjoint_openCell_of_ne (by lia)⟩
  rw [disjoint_of_subset_iff_left_eq_empty h] at h'
  exact notMem_empty _ (h' ▸ map_zero_mem_openCell n i)

/--
lemma `RelCWComplex.eq_of_eq_union_iUnion` / 引理 `RelCWComplex.eq_of_eq_union_iUnion`

English:
lemma RelCWComplex.eq_of_eq_union_iUnion
  statement: [RelCWComplex C D] (I J : Π n, Set (cell C n))
  proof: by
  ext n x
  exact ⟨fun h => subset_of_eq_union_iUnion I J hIJ n h,
    fun h => subset_of_eq_union_iUnion J I hIJ.symm n h⟩

中文:
引理 RelCWComplex.eq_of_eq_union_iUnion
  结论: [RelCWComplex C D] (I J : Π n, 集合 (cell C n))
  证明: by
  ext n x
  exact ⟨fun h => subset_of_eq_union_iUnion I J hIJ n h,
    fun h => subset_of_eq_union_iUnion J I hIJ.symm n h⟩
-/
lemma RelCWComplex.eq_of_eq_union_iUnion [RelCWComplex C D] (I J : Π n, Set (cell C n))
    (hIJ : D union ⋃ (n : Nat) (j : I n), openCell (C := C) n j =
      D union ⋃ (n : Nat) (j : J n), openCell (C := C) n j) :
    I = J := by
  ext n x
  exact ⟨fun h => subset_of_eq_union_iUnion I J hIJ n h,
    fun h => subset_of_eq_union_iUnion J I hIJ.symm n h⟩

/--
lemma `CWComplex.eq_of_eq_union_iUnion` / 引理 `CWComplex.eq_of_eq_union_iUnion`

English:
lemma CWComplex.eq_of_eq_union_iUnion
  statement: [CWComplex C] (I J : Π n, Set (cell C n))
  proof: by
  apply RelCWComplex.eq_of_eq_union_iUnion
  simp_rw [empty_union, hIJ]

@[alias_in CWComplex]

中文:
引理 CWComplex.eq_of_eq_union_iUnion
  结论: [CWComplex C] (I J : Π n, 集合 (cell C n))
  证明: by
  apply RelCWComplex.eq_of_eq_union_iUnion
  simp_rw [empty_union, hIJ]

@[alias_in CWComplex]
-/
lemma CWComplex.eq_of_eq_union_iUnion [CWComplex C] (I J : Π n, Set (cell C n))
    (hIJ : ⋃ (n : Nat) (j : I n), openCell (C := C) n j =
      ⋃ (n : Nat) (j : J n), openCell (C := C) n j) :
    I = J := by
  apply RelCWComplex.eq_of_eq_union_iUnion
  simp_rw [empty_union, hIJ]

@[alias_in CWComplex]
/--
lemma `RelCWComplex.isCompact_closedCell` / 引理 `RelCWComplex.isCompact_closedCell`

English:
lemma RelCWComplex.isCompact_closedCell
  given: [RelCWComplex C D] {n : Nat} {i : cell C n}
  proof: (isCompact_closedBall _ _).image_of_continuousOn (continuousOn n i)

@[alias_in CWComplex]

中文:
引理 RelCWComplex.isCompact_closedCell
  条件: [RelCWComplex C D] {n : 自然数} {i : cell C n}
  证明: (isCompact_closedBall _ _).image_of_continuousOn (continuousOn n i)

@[alias_in CWComplex]

Depends on / 依赖: continuousOn, image_of_continuousOn, isCompact_closedBall
-/
lemma RelCWComplex.isCompact_closedCell [RelCWComplex C D] {n : Nat} {i : cell C n} :
    IsCompact (closedCell n i) :=
  (isCompact_closedBall _ _).image_of_continuousOn (continuousOn n i)

@[alias_in CWComplex]
/--
lemma `RelCWComplex.isClosed_closedCell` / 引理 `RelCWComplex.isClosed_closedCell`

English:
lemma RelCWComplex.isClosed_closedCell
  given: [RelCWComplex C D] [T2Space X] {n : Nat} {i : cell C n}
  proof: isCompact_closedCell.isClosed

@[alias_in CWComplex]

中文:
引理 RelCWComplex.isClosed_closedCell
  条件: [RelCWComplex C D] [T2空间 X] {n : 自然数} {i : cell C n}
  证明: isCompact_closedCell.isClosed

@[alias_in CWComplex]

Depends on / 依赖: isClosed, isCompact_closedCell, isCompact_closedCell.isClosed
-/
lemma RelCWComplex.isClosed_closedCell [RelCWComplex C D] [T2Space X] {n : Nat} {i : cell C n} :
    IsClosed (closedCell n i) := isCompact_closedCell.isClosed

@[alias_in CWComplex]
/--
lemma `RelCWComplex.isCompact_cellFrontier` / 引理 `RelCWComplex.isCompact_cellFrontier`

English:
lemma RelCWComplex.isCompact_cellFrontier
  given: [RelCWComplex C D] {n : Nat} {i : cell C n}
  proof: (isCompact_sphere _ _).image_of_continuousOn ((continuousOn n i).mono sphere_subset_closedBall)

@[alias_in CWComplex]

中文:
引理 RelCWComplex.isCompact_cellFrontier
  条件: [RelCWComplex C D] {n : 自然数} {i : cell C n}
  证明: (isCompact_sphere _ _).image_of_continuousOn ((continuousOn n i).mono sphere_subset_closedBall)

@[alias_in CWComplex]

Depends on / 依赖: continuousOn, image_of_continuousOn, isCompact_sphere, sphere_subset_closedBall
-/
lemma RelCWComplex.isCompact_cellFrontier [RelCWComplex C D] {n : Nat} {i : cell C n} :
    IsCompact (cellFrontier n i) :=
  (isCompact_sphere _ _).image_of_continuousOn ((continuousOn n i).mono sphere_subset_closedBall)

@[alias_in CWComplex]
/--
lemma `RelCWComplex.isClosed_cellFrontier` / 引理 `RelCWComplex.isClosed_cellFrontier`

English:
lemma RelCWComplex.isClosed_cellFrontier
  given: [RelCWComplex C D] [T2Space X] {n : Nat} {i : cell C n}
  proof: isCompact_cellFrontier.isClosed

@[alias_in CWComplex]

中文:
引理 RelCWComplex.isClosed_cellFrontier
  条件: [RelCWComplex C D] [T2空间 X] {n : 自然数} {i : cell C n}
  证明: isCompact_cellFrontier.isClosed

@[alias_in CWComplex]

Depends on / 依赖: isClosed, isCompact_cellFrontier, isCompact_cellFrontier.isClosed
-/
lemma RelCWComplex.isClosed_cellFrontier [RelCWComplex C D] [T2Space X] {n : Nat} {i : cell C n} :
    IsClosed (cellFrontier n i) :=
  isCompact_cellFrontier.isClosed

@[alias_in CWComplex]
/--
lemma `RelCWComplex.closure_openCell_eq_closedCell` / 引理 `RelCWComplex.closure_openCell_eq_closedCell`

English:
lemma RelCWComplex.closure_openCell_eq_closedCell
  statement: [RelCWComplex C D] [T2Space X] {n : Nat}
  proof: by
  apply subset_antisymm (isClosed_closedCell.closure_subset_iff.2 (openCell_subset_closedCell n j))
  rw [closedCell]; rw [← closure_ball 0 (by exact one_ne_zero)]
  apply ContinuousOn.image_closure
  rw [closure_ball 0 (by exact one_ne_zero)]
  exact continuousOn n j

中文:
引理 RelCWComplex.closure_openCell_eq_closedCell
  结论: [RelCWComplex C D] [T2空间 X] {n : 自然数}
  证明: by
  apply subset_antisymm (isClosed_closedCell.closure_subset_iff.2 (openCell_subset_closedCell n j))
  rw [closedCell]; rw [← closure_ball 0 (by exact one_ne_zero)]
  apply ContinuousOn.image_closure
  rw [closure_ball 0 (by exact one_ne_zero)]
  exact continuousOn n j

Depends on / 依赖: ContinuousOn, ContinuousOn.image_closure, closedCell, closure_ball, closure_subset_iff, continuousOn, image_closure, isClosed_closedCell, isClosed_closedCell.closure_subset_iff, one_ne_zero, openCell_subset_closedCell, subset_antisymm
-/
lemma RelCWComplex.closure_openCell_eq_closedCell [RelCWComplex C D] [T2Space X] {n : Nat}
    {j : cell C n} : closure (openCell n j) = closedCell n j := by
  apply subset_antisymm (isClosed_closedCell.closure_subset_iff.2 (openCell_subset_closedCell n j))
  rw [closedCell]; rw [← closure_ball 0 (by exact one_ne_zero)]
  apply ContinuousOn.image_closure
  rw [closure_ball 0 (by exact one_ne_zero)]
  exact continuousOn n j

/--
lemma `RelCWComplex.closed` / 引理 `RelCWComplex.closed`

English:
lemma RelCWComplex.closed
  statement: (C : Set X) {D : Set X} [RelCWComplex C D] [T2Space X] (A : Set X)
  proof: by
  refine ⟨?_, closed' A asubc⟩
  exact fun closedA => ⟨fun _ _ => closedA.inter isClosed_closedCell, closedA.inter (isClosedBase C)⟩

中文:
引理 RelCWComplex.closed
  结论: (C : 集合 X) {D : 集合 X} [RelCWComplex C D] [T2空间 X] (A : 集合 X)
  证明: by
  refine ⟨?_, closed' A asubc⟩
  exact fun closedA => ⟨fun _ _ => closedA.inter isClosed_closedCell, closedA.inter (isClosedBase C)⟩

Depends on / 依赖: closed, closedA, closedA.inter, isClosedBase, isClosed_closedCell
-/
lemma RelCWComplex.closed (C : Set X) {D : Set X} [RelCWComplex C D] [T2Space X] (A : Set X)
    (asubc : A subseteq C) :
    IsClosed A ↔ (forall n (j : cell C n), IsClosed (A inter closedCell n j)) ∧ IsClosed (A inter D) := by
  refine ⟨?_, closed' A asubc⟩
  exact fun closedA => ⟨fun _ _ => closedA.inter isClosed_closedCell, closedA.inter (isClosedBase C)⟩

/--
lemma `CWComplex.closed` / 引理 `CWComplex.closed`

English:
lemma CWComplex.closed
  given: (C : Set X) [CWComplex C] [T2Space X] (A : Set X) (asubc : A subseteq C)
  proof: by
  have := RelCWComplex.closed C A asubc
  simp_all

@[alias_in CWComplex]

中文:
引理 CWComplex.closed
  条件: (C : 集合 X) [CWComplex C] [T2空间 X] (A : 集合 X) (asubc : A subseteq C)
  证明: by
  have := RelCWComplex.closed C A asubc
  simp_all

@[alias_in CWComplex]

Depends on / 依赖: RelCWComplex, RelCWComplex.closed, closed
-/
lemma CWComplex.closed (C : Set X) [CWComplex C] [T2Space X] (A : Set X) (asubc : A subseteq C) :
    IsClosed A ↔ forall n (j : cell C n), IsClosed (A inter closedCell n j) := by
  have := RelCWComplex.closed C A asubc
  simp_all

@[alias_in CWComplex]
/--
lemma `RelCWComplex.closedCell_subset_complex` / 引理 `RelCWComplex.closedCell_subset_complex`

English:
lemma RelCWComplex.closedCell_subset_complex
  given: [RelCWComplex C D] (n : Nat) (j : cell C n)
  proof: by
  simp_rw [← union]
  exact subset_union_of_subset_right (subset_iUnion₂ _ _) _

@[alias_in CWComplex]

中文:
引理 RelCWComplex.closedCell_subset_complex
  条件: [RelCWComplex C D] (n : 自然数) (j : cell C n)
  证明: by
  simp_rw [← union]
  exact subset_union_of_subset_right (subset_iUnion₂ _ _) _

@[alias_in CWComplex]

Depends on / 依赖: simp_rw, subset_union_of_subset_right
-/
lemma RelCWComplex.closedCell_subset_complex [RelCWComplex C D] (n : Nat) (j : cell C n) :
    closedCell n j subseteq C := by
  simp_rw [← union]
  exact subset_union_of_subset_right (subset_iUnion₂ _ _) _

@[alias_in CWComplex]
/--
lemma `RelCWComplex.openCell_subset_complex` / 引理 `RelCWComplex.openCell_subset_complex`

English:
lemma RelCWComplex.openCell_subset_complex
  given: [RelCWComplex C D] (n : Nat) (j : cell C n)
  proof: (openCell_subset_closedCell _ _).trans (closedCell_subset_complex _ _)

@[alias_in CWComplex]

中文:
引理 RelCWComplex.openCell_subset_complex
  条件: [RelCWComplex C D] (n : 自然数) (j : cell C n)
  证明: (openCell_subset_closedCell _ _).trans (closedCell_subset_complex _ _)

@[alias_in CWComplex]

Depends on / 依赖: closedCell_subset_complex, openCell_subset_closedCell
-/
lemma RelCWComplex.openCell_subset_complex [RelCWComplex C D] (n : Nat) (j : cell C n) :
    openCell n j subseteq C :=
  (openCell_subset_closedCell _ _).trans (closedCell_subset_complex _ _)

@[alias_in CWComplex]
/--
lemma `RelCWComplex.cellFrontier_subset_complex` / 引理 `RelCWComplex.cellFrontier_subset_complex`

English:
lemma RelCWComplex.cellFrontier_subset_complex
  given: [RelCWComplex C D] (n : Nat) (j : cell C n)
  proof: (cellFrontier_subset_closedCell n j).trans (closedCell_subset_complex n j)

@[alias_in CWComplex]

中文:
引理 RelCWComplex.cellFrontier_subset_complex
  条件: [RelCWComplex C D] (n : 自然数) (j : cell C n)
  证明: (cellFrontier_subset_closedCell n j).trans (closedCell_subset_complex n j)

@[alias_in CWComplex]

Depends on / 依赖: cellFrontier_subset_closedCell, closedCell_subset_complex
-/
lemma RelCWComplex.cellFrontier_subset_complex [RelCWComplex C D] (n : Nat) (j : cell C n) :
    cellFrontier n j subseteq C :=
  (cellFrontier_subset_closedCell n j).trans (closedCell_subset_complex n j)

@[alias_in CWComplex]
/--
lemma `RelCWComplex.closedCell_zero_eq_singleton` / 引理 `RelCWComplex.closedCell_zero_eq_singleton`

English:
lemma RelCWComplex.closedCell_zero_eq_singleton
  given: [RelCWComplex C D] {j : cell C 0}
  proof: by
  simp [closedCell, Matrix.empty_eq]

@[alias_in CWComplex]

中文:
引理 RelCWComplex.closedCell_zero_eq_singleton
  条件: [RelCWComplex C D] {j : cell C 0}
  证明: by
  simp [closedCell, Matrix.empty_eq]

@[alias_in CWComplex]

Depends on / 依赖: Matrix, Matrix.empty_eq, closedCell, empty_eq
-/
lemma RelCWComplex.closedCell_zero_eq_singleton [RelCWComplex C D] {j : cell C 0} :
    closedCell 0 j = {map 0 j ![]} := by
  simp [closedCell, Matrix.empty_eq]

@[alias_in CWComplex]
/--
lemma `RelCWComplex.openCell_zero_eq_singleton` / 引理 `RelCWComplex.openCell_zero_eq_singleton`

English:
lemma RelCWComplex.openCell_zero_eq_singleton
  given: [RelCWComplex C D] {j : cell C 0}
  proof: by
  simp [openCell, Matrix.empty_eq]

@[alias_in CWComplex]

中文:
引理 RelCWComplex.openCell_zero_eq_singleton
  条件: [RelCWComplex C D] {j : cell C 0}
  证明: by
  simp [openCell, Matrix.empty_eq]

@[alias_in CWComplex]

Depends on / 依赖: Matrix, Matrix.empty_eq, empty_eq, openCell
-/
lemma RelCWComplex.openCell_zero_eq_singleton [RelCWComplex C D] {j : cell C 0} :
    openCell 0 j = {map 0 j ![]} := by
  simp [openCell, Matrix.empty_eq]

@[alias_in CWComplex]
/--
lemma `RelCWComplex.cellFrontier_zero_eq_empty` / 引理 `RelCWComplex.cellFrontier_zero_eq_empty`

English:
lemma RelCWComplex.cellFrontier_zero_eq_empty
  given: [RelCWComplex C D] {j : cell C 0}
  proof: by
  simp [cellFrontier, sphere_eq_empty_of_subsingleton]

@[alias_in CWComplex]

中文:
引理 RelCWComplex.cellFrontier_zero_eq_empty
  条件: [RelCWComplex C D] {j : cell C 0}
  证明: by
  simp [cellFrontier, sphere_eq_empty_of_subsingleton]

@[alias_in CWComplex]

Depends on / 依赖: cellFrontier, sphere_eq_empty_of_subsingleton
-/
lemma RelCWComplex.cellFrontier_zero_eq_empty [RelCWComplex C D] {j : cell C 0} :
    cellFrontier 0 j = ∅ := by
  simp [cellFrontier, sphere_eq_empty_of_subsingleton]

@[alias_in CWComplex]
/--
lemma `RelCWComplex.nonempty_cellFrontier` / 引理 `RelCWComplex.nonempty_cellFrontier`

English:
lemma RelCWComplex.nonempty_cellFrontier
  given: [CWComplex C] {n : Nat} (hn : n != 0) (j : cell C n)
  proof: by
  let : NeZero n := ⟨hn⟩
  use map n j (Pi.single 0 1)
  simp only [cellFrontier, mem_image, mem_sphere_iff_norm, sub_zero]
  use Pi.single 0 1, by simp [Pi.norm_single]

中文:
引理 RelCWComplex.nonempty_cellFrontier
  条件: [CWComplex C] {n : 自然数} (hn : n != 0) (j : cell C n)
  证明: by
  let : NeZero n := ⟨hn⟩
  use map n j (Pi.single 0 1)
  simp only [cellFrontier, mem_image, mem_sphere_iff_norm, sub_zero]
  use Pi.single 0 1, by simp [Pi.norm_single]

Depends on / 依赖: NeZero, Pi.norm_single, Pi.single, cellFrontier, mem_image, mem_sphere_iff_norm, norm_single, single, sub_zero
-/
lemma RelCWComplex.nonempty_cellFrontier [CWComplex C] {n : Nat} (hn : n != 0) (j : cell C n) :
    (cellFrontier n j).Nonempty := by
  let : NeZero n := ⟨hn⟩
  use map n j (Pi.single 0 1)
  simp only [cellFrontier, mem_image, mem_sphere_iff_norm, sub_zero]
  use Pi.single 0 1, by simp [Pi.norm_single]

/-- If two 0-cells have the same characteristic image point, they are equal. -/
@[alias_in CWComplex]
/--
lemma `RelCWComplex.injective_map_zero` / 引理 `RelCWComplex.injective_map_zero`

English:
lemma RelCWComplex.injective_map_zero
  given: (C : Set X) [RelCWComplex C D]
  proof: by
  rintro x z h
  by_contra hne
  exact not_disjoint_iff.mpr ⟨map 0 x ![], by simp [openCell_zero_eq_singleton, h]⟩
 disjoint_openCell_of_ne (by grind : (⟨0, x⟩ : Σ n, cell C n) != ⟨0, z⟩)

@[simp, alias_in CWComplex]

中文:
引理 RelCWComplex.injective_map_zero
  条件: (C : 集合 X) [RelCWComplex C D]
  证明: by
  rintro x z h
  by_contra hne
  exact not_disjoint_iff.mpr ⟨map 0 x ![], by simp [openCell_zero_eq_singleton, h]⟩
 disjoint_openCell_of_ne (by grind : (⟨0, x⟩ : Σ n, cell C n) != ⟨0, z⟩)

@[simp, alias_in CWComplex]

Depends on / 依赖: disjoint_openCell_of_ne, not_disjoint_iff, not_disjoint_iff.mpr, openCell_zero_eq_singleton
-/
lemma RelCWComplex.injective_map_zero (C : Set X) [RelCWComplex C D] :
    Injective ((map 0 · ![]) : cell C 0 -> X) := by
  rintro x z h
  by_contra hne
  exact not_disjoint_iff.mpr ⟨map 0 x ![], by simp [openCell_zero_eq_singleton, h]⟩
 disjoint_openCell_of_ne (by grind : (⟨0, x⟩ : Σ n, cell C n) != ⟨0, z⟩)

@[simp, alias_in CWComplex]
/--
lemma `RelCWComplex.map_zero_eq_self_iff` / 引理 `RelCWComplex.map_zero_eq_self_iff`

English:
lemma RelCWComplex.map_zero_eq_self_iff
  given: (C : Set X) [RelCWComplex C D] {x z : cell C 0}
  proof: ⟨fun h => injective_map_zero C h, fun h => h ▸ rfl⟩

@[alias_in CWComplex]

中文:
引理 RelCWComplex.map_zero_eq_self_iff
  条件: (C : 集合 X) [RelCWComplex C D] {x z : cell C 0}
  证明: ⟨fun h => injective_map_zero C h, fun h => h ▸ rfl⟩

@[alias_in CWComplex]

Depends on / 依赖: injective_map_zero
-/
lemma RelCWComplex.map_zero_eq_self_iff (C : Set X) [RelCWComplex C D] {x z : cell C 0} :
    map 0 x ![] = map 0 z ![] ↔ x = z :=
  ⟨fun h => injective_map_zero C h, fun h => h ▸ rfl⟩

@[alias_in CWComplex]
/--
lemma `RelCWComplex.closedCell_zero_injective` / 引理 `RelCWComplex.closedCell_zero_injective`

English:
lemma RelCWComplex.closedCell_zero_injective
  given: (C : Set X) [RelCWComplex C D]
  proof: by
  intro x y h
  rw [closedCell_zero_eq_singleton]; rw [closedCell_zero_eq_singleton]; rw [singleton_eq_singleton_iff] at h
  exact injective_map_zero C h

@[alias_in CWComplex]

中文:
引理 RelCWComplex.closedCell_zero_injective
  条件: (C : 集合 X) [RelCWComplex C D]
  证明: by
  intro x y h
  rw [closedCell_zero_eq_singleton]; rw [closedCell_zero_eq_singleton]; rw [singleton_eq_singleton_iff] at h
  exact injective_map_zero C h

@[alias_in CWComplex]

Depends on / 依赖: closedCell_zero_eq_singleton, injective_map_zero, singleton_eq_singleton_iff
-/
lemma RelCWComplex.closedCell_zero_injective (C : Set X) [RelCWComplex C D] :
    Injective (closedCell 0 : cell C 0 -> _) := by
  intro x y h
  rw [closedCell_zero_eq_singleton]; rw [closedCell_zero_eq_singleton]; rw [singleton_eq_singleton_iff] at h
  exact injective_map_zero C h

@[alias_in CWComplex]
/--
lemma `RelCWComplex.openCell_zero_injective` / 引理 `RelCWComplex.openCell_zero_injective`

English:
lemma RelCWComplex.openCell_zero_injective
  given: (C : Set X) [RelCWComplex C D]
  proof: by
  intro x y h
  rw [openCell_zero_eq_singleton]; rw [openCell_zero_eq_singleton]; rw [singleton_eq_singleton_iff] at h
  exact injective_map_zero C h

@[alias_in CWComplex]

中文:
引理 RelCWComplex.openCell_zero_injective
  条件: (C : 集合 X) [RelCWComplex C D]
  证明: by
  intro x y h
  rw [openCell_zero_eq_singleton]; rw [openCell_zero_eq_singleton]; rw [singleton_eq_singleton_iff] at h
  exact injective_map_zero C h

@[alias_in CWComplex]

Depends on / 依赖: injective_map_zero, openCell_zero_eq_singleton, singleton_eq_singleton_iff
-/
lemma RelCWComplex.openCell_zero_injective (C : Set X) [RelCWComplex C D] :
    Injective (openCell 0 : cell C 0 -> _) := by
  intro x y h
  rw [openCell_zero_eq_singleton]; rw [openCell_zero_eq_singleton]; rw [singleton_eq_singleton_iff] at h
  exact injective_map_zero C h

@[alias_in CWComplex]
/--
lemma `RelCWComplex.cellFrontier_one_eq` / 引理 `RelCWComplex.cellFrontier_one_eq`

English:
lemma RelCWComplex.cellFrontier_one_eq
  given: [RelCWComplex C D] (e : cell C 1)
  proof: by
  rw [cellFrontier]
  congr 1
  ext f
  simp only [mem_sphere_iff_norm, sub_zero, Pi.norm_def, Finset.univ_unique, Fin.default_eq_zero,
    Fin.isValue, Finset.sup_singleton, coe_nnnorm, Real.norm_eq_abs, abs_eq (zero_le_one' Real),
    mem_insert_iff, mem_singleton_iff]
  rw [eq_const_of_unique (f := f)]; rw [← funext_iff_of_subsingleton (x := 0) (y := 0)]
  simp [const_apply, or_comm]

中文:
引理 RelCWComplex.cellFrontier_one_eq
  条件: [RelCWComplex C D] (e : cell C 1)
  证明: by
  rw [cellFrontier]
  congr 1
  ext f
  simp only [mem_sphere_iff_norm, sub_zero, Pi.norm_def, Finset.univ_unique, Fin.default_eq_zero,
    Fin.isValue, Finset.sup_singleton, coe_nnnorm, Real.norm_eq_abs, abs_eq (zero_le_one' Real),
    mem_insert_iff, mem_singleton_iff]
  rw [eq_const_of_unique (f := f)]; rw [← funext_iff_of_subsingleton (x := 0) (y := 0)]
  simp [const_apply, or_comm]

Depends on / 依赖: Fin.default_eq_zero, Fin.isValue, Finset, Finset.sup_singleton, Finset.univ_unique, Pi.norm_def, Real.norm_eq_abs, abs_eq, cellFrontier, coe_nnnorm, const_apply, default_eq_zero, eq_const_of_unique, funext_iff_of_subsingleton, isValue, mem_insert_iff, mem_singleton_iff, mem_sphere_iff_norm, norm_def, norm_eq_abs
-/
lemma RelCWComplex.cellFrontier_one_eq [RelCWComplex C D] (e : cell C 1) :
    cellFrontier 1 e = map 1 e '' {-1, 1} := by
  rw [cellFrontier]
  congr 1
  ext f
  simp only [mem_sphere_iff_norm, sub_zero, Pi.norm_def, Finset.univ_unique, Fin.default_eq_zero,
    Fin.isValue, Finset.sup_singleton, coe_nnnorm, Real.norm_eq_abs, abs_eq (zero_le_one' Real),
    mem_insert_iff, mem_singleton_iff]
  rw [eq_const_of_unique (f := f)]; rw [← funext_iff_of_subsingleton (x := 0) (y := 0)]
  simp [const_apply, or_comm]

/--
lemma `CWComplex.exists_cellFrontier_one_eq` / 引理 `CWComplex.exists_cellFrontier_one_eq`

English:
lemma CWComplex.exists_cellFrontier_one_eq
  given: [CWComplex C] (e : cell C 1)
  proof: by
  obtain ⟨f, h⟩ := cellFrontier_subset_finite_closedCell 1 e
  simp only [RelCWComplex.cellFrontier_one_eq, image_pair, Order.lt_one_iff, iUnion_iUnion_eq_left,
    RelCWComplex.closedCell_zero_eq_singleton, pair_subset_iff, mem_iUnion, mem_singleton_iff,
    exists_prop] at h
  obtain ⟨⟨u, hu, hun1⟩, v, hv, hv1⟩ := h
  use u, v
  simp [RelCWComplex.cellFrontier_one_eq, image_pair, RelCWComplex.closedCell_zero_eq_singleton,
    hun1, hv1, pair_comm]

@[alias_in CWComplex]

中文:
引理 CWComplex.存在_cellFrontier_one_eq
  条件: [CWComplex C] (e : cell C 1)
  证明: by
  obtain ⟨f, h⟩ := cellFrontier_subset_finite_closedCell 1 e
  simp only [RelCWComplex.cellFrontier_one_eq, image_pair, Order.lt_one_iff, iUnion_iUnion_eq_left,
    RelCWComplex.closedCell_zero_eq_singleton, pair_subset_iff, mem_iUnion, mem_singleton_iff,
    exists_prop] at h
  obtain ⟨⟨u, hu, hun1⟩, v, hv, hv1⟩ := h
  use u, v
  simp [RelCWComplex.cellFrontier_one_eq, image_pair, RelCWComplex.closedCell_zero_eq_singleton,
    hun1, hv1, pair_comm]

@[alias_in CWComplex]

Depends on / 依赖: Order.lt_one_iff, RelCWComplex, RelCWComplex.cellFrontier_one_eq, RelCWComplex.closedCell_zero_eq_singleton, cellFrontier_one_eq, cellFrontier_subset_finite_closedCell, closedCell_zero_eq_singleton, exists_prop, iUnion_iUnion_eq_left, image_pair, lt_one_iff, mem_iUnion, mem_singleton_iff, pair_comm, pair_subset_iff
-/
lemma CWComplex.exists_cellFrontier_one_eq [CWComplex C] (e : cell C 1) :
    exists x y : cell C 0, cellFrontier 1 e = closedCell 0 x union closedCell 0 y := by
  obtain ⟨f, h⟩ := cellFrontier_subset_finite_closedCell 1 e
  simp only [RelCWComplex.cellFrontier_one_eq, image_pair, Order.lt_one_iff, iUnion_iUnion_eq_left,
    RelCWComplex.closedCell_zero_eq_singleton, pair_subset_iff, mem_iUnion, mem_singleton_iff,
    exists_prop] at h
  obtain ⟨⟨u, hu, hun1⟩, v, hv, hv1⟩ := h
  use u, v
  simp [RelCWComplex.cellFrontier_one_eq, image_pair, RelCWComplex.closedCell_zero_eq_singleton,
    hun1, hv1, pair_comm]

@[alias_in CWComplex]
/--
lemma `RelCWComplex.base_subset_complex` / 引理 `RelCWComplex.base_subset_complex`

English:
lemma RelCWComplex.base_subset_complex
  given: [RelCWComplex C D]
  statement: D subseteq C
  proof: by
  simp_rw [← union]
  exact subset_union_left

@[alias_in CWComplex]

中文:
引理 RelCWComplex.base_subset_complex
  条件: [RelCWComplex C D]
  结论: D subseteq C
  证明: by
  simp_rw [← union]
  exact subset_union_left

@[alias_in CWComplex]

Depends on / 依赖: simp_rw, subset_union_left
-/
lemma RelCWComplex.base_subset_complex [RelCWComplex C D] : D subseteq C := by
  simp_rw [← union]
  exact subset_union_left

@[alias_in CWComplex]
/--
lemma `RelCWComplex.isClosed` / 引理 `RelCWComplex.isClosed`

English:
lemma RelCWComplex.isClosed
  given: [T2Space X] [RelCWComplex C D]
  statement: IsClosed C
  proof: by
  rw [closed C C (by rfl)]
  constructor
  · intros
    rw [inter_eq_right.2 (closedCell_subset_complex _ _)]
    exact isClosed_closedCell
  · rw [inter_eq_right.2 base_subset_complex]
    exact isClosedBase C

中文:
引理 RelCWComplex.isClosed
  条件: [T2空间 X] [RelCWComplex C D]
  结论: 是闭集 C
  证明: by
  rw [closed C C (by rfl)]
  constructor
  · intros
    rw [inter_eq_right.2 (closedCell_subset_complex _ _)]
    exact isClosed_closedCell
  · rw [inter_eq_right.2 base_subset_complex]
    exact isClosedBase C

Depends on / 依赖: base_subset_complex, closed, closedCell_subset_complex, inter_eq_right, intros, isClosedBase, isClosed_closedCell
-/
lemma RelCWComplex.isClosed [T2Space X] [RelCWComplex C D] : IsClosed C := by
  rw [closed C C (by rfl)]
  constructor
  · intros
    rw [inter_eq_right.2 (closedCell_subset_complex _ _)]
    exact isClosed_closedCell
  · rw [inter_eq_right.2 base_subset_complex]
    exact isClosedBase C

/--
lemma `RelCWComplex.iUnion_openCell_eq_iUnion_closedCell` / 引理 `RelCWComplex.iUnion_openCell_eq_iUnion_closedCell`

English:
lemma RelCWComplex.iUnion_openCell_eq_iUnion_closedCell
  given: [RelCWComplex C D] (n : Nat∞)
  proof: by
  apply subset_antisymm
  · apply union_subset
    · exact subset_union_left
    · apply iUnion₂_subset fun m hm => iUnion_subset fun j => ?_
      apply subset_union_of_subset_right
      apply subset_iUnion₂_of_subset m hm
      apply subset_iUnion_of_subset j
      exact openCell_subset_closedCell m j
  · apply union_subset subset_union_left
    refine iUnion₂_subset fun m hm => iUnion_subset fun j => ?_
    rw [← cellFrontier_union_openCell_eq_closedCell]
    apply union_subset
    · induction m using Nat.case_strong_induction_on with
      | hz => simp [cellFrontier_zero_eq_empty]
      | hi m hm' =>
        obtain ⟨I, hI⟩ := cellFrontier_subset_base_union_finite_closedCell (m + 1) j
        apply hI.trans
        apply union_subset subset_union_left
        apply iUnion₂_subset fun l hl => iUnion₂_subset fun i _ => ?_
        rw [← cellFrontier_union_openCell_eq_closedCell]
        apply union_subset
        · exact (hm' l (Nat.le_of_lt_succ hl) ((ENat.natCast_lt_natCast.2 hl).trans hm) i)
        · apply subset_union_of_subset_right
exact subset_iUnion₂_of_subset l ((ENat.natCast_lt_natCast.2 hl).trans hm)
            subset_iUnion _ i
    · exact subset_union_of_subset_right (subset_iUnion₂_of_subset m hm (subset_iUnion _ j)) _

中文:
引理 RelCWComplex.iUnion_openCell_eq_iUnion_closedCell
  条件: [RelCWComplex C D] (n : 自然数∞)
  证明: by
  apply subset_antisymm
  · apply union_subset
    · exact subset_union_left
    · apply iUnion₂_subset fun m hm => iUnion_subset fun j => ?_
      apply subset_union_of_subset_right
      apply subset_iUnion₂_of_subset m hm
      apply subset_iUnion_of_subset j
      exact openCell_subset_closedCell m j
  · apply union_subset subset_union_left
    refine iUnion₂_subset fun m hm => iUnion_subset fun j => ?_
    rw [← cellFrontier_union_openCell_eq_closedCell]
    apply union_subset
    · induction m using Nat.case_strong_induction_on with
      | hz => simp [cellFrontier_zero_eq_empty]
      | hi m hm' =>
        obtain ⟨I, hI⟩ := cellFrontier_subset_base_union_finite_closedCell (m + 1) j
        apply hI.trans
        apply union_subset subset_union_left
        apply iUnion₂_subset fun l hl => iUnion₂_subset fun i _ => ?_
        rw [← cellFrontier_union_openCell_eq_closedCell]
        apply union_subset
        · exact (hm' l (Nat.le_of_lt_succ hl) ((ENat.natCast_lt_natCast.2 hl).trans hm) i)
        · apply subset_union_of_subset_right
exact subset_iUnion₂_of_subset l ((ENat.natCast_lt_natCast.2 hl).trans hm)
            subset_iUnion _ i
    · exact subset_union_of_subset_right (subset_iUnion₂_of_subset m hm (subset_iUnion _ j)) _
-/
private lemma RelCWComplex.iUnion_openCell_eq_iUnion_closedCell [RelCWComplex C D] (n : Nat∞) :
    D union ⋃ (m : Nat) (_ : m < n) (j : cell C m), openCell m j =
      D union ⋃ (m : Nat) (_ : m < n) (j : cell C m), closedCell m j := by
  apply subset_antisymm
  · apply union_subset
    · exact subset_union_left
    · apply iUnion₂_subset fun m hm => iUnion_subset fun j => ?_
      apply subset_union_of_subset_right
      apply subset_iUnion₂_of_subset m hm
      apply subset_iUnion_of_subset j
      exact openCell_subset_closedCell m j
  · apply union_subset subset_union_left
    refine iUnion₂_subset fun m hm => iUnion_subset fun j => ?_
    rw [← cellFrontier_union_openCell_eq_closedCell]
    apply union_subset
    · induction m using Nat.case_strong_induction_on with
      | hz => simp [cellFrontier_zero_eq_empty]
      | hi m hm' =>
        obtain ⟨I, hI⟩ := cellFrontier_subset_base_union_finite_closedCell (m + 1) j
        apply hI.trans
        apply union_subset subset_union_left
        apply iUnion₂_subset fun l hl => iUnion₂_subset fun i _ => ?_
        rw [← cellFrontier_union_openCell_eq_closedCell]
        apply union_subset
        · exact (hm' l (Nat.le_of_lt_succ hl) ((ENat.natCast_lt_natCast.2 hl).trans hm) i)
        · apply subset_union_of_subset_right
exact subset_iUnion₂_of_subset l ((ENat.natCast_lt_natCast.2 hl).trans hm)
            subset_iUnion _ i
    · exact subset_union_of_subset_right (subset_iUnion₂_of_subset m hm (subset_iUnion _ j)) _

/--
lemma `RelCWComplex.union_iUnion_openCell_eq_complex` / 引理 `RelCWComplex.union_iUnion_openCell_eq_complex`

English:
lemma RelCWComplex.union_iUnion_openCell_eq_complex
  given: [RelCWComplex C D]
  proof: by
  suffices D union ⋃ n, ⋃ (j : cell C n), openCell n j =
      D union ⋃ (m : Nat) (_ : m < (⊤ : Nat∞)) (j : cell C m), closedCell m j by
    simpa [union] using this
  simp_rw [← RelCWComplex.iUnion_openCell_eq_iUnion_closedCell, ENat.natCast_lt_top, iUnion_true]

中文:
引理 RelCWComplex.union_iUnion_openCell_eq_complex
  条件: [RelCWComplex C D]
  证明: by
  suffices D union ⋃ n, ⋃ (j : cell C n), openCell n j =
      D union ⋃ (m : Nat) (_ : m < (⊤ : Nat∞)) (j : cell C m), closedCell m j by
    simpa [union] using this
  simp_rw [← RelCWComplex.iUnion_openCell_eq_iUnion_closedCell, ENat.natCast_lt_top, iUnion_true]

Depends on / 依赖: ENat.natCast_lt_top, RelCWComplex, RelCWComplex.iUnion_openCell_eq_iUnion_closedCell, closedCell, iUnion_openCell_eq_iUnion_closedCell, iUnion_true, natCast_lt_top, openCell, simp_rw
-/
lemma RelCWComplex.union_iUnion_openCell_eq_complex [RelCWComplex C D] :
    D union ⋃ (n : Nat) (j : cell C n), openCell n j = C := by
  suffices D union ⋃ n, ⋃ (j : cell C n), openCell n j =
      D union ⋃ (m : Nat) (_ : m < (⊤ : Nat∞)) (j : cell C m), closedCell m j by
    simpa [union] using this
  simp_rw [← RelCWComplex.iUnion_openCell_eq_iUnion_closedCell, ENat.natCast_lt_top, iUnion_true]

/--
lemma `CWComplex.iUnion_openCell_eq_complex` / 引理 `CWComplex.iUnion_openCell_eq_complex`

English:
lemma CWComplex.iUnion_openCell_eq_complex
  given: [CWComplex C]
  proof: by
  simpa using RelCWComplex.union_iUnion_openCell_eq_complex (C := C)

中文:
引理 CWComplex.iUnion_openCell_eq_complex
  条件: [CWComplex C]
  证明: by
  simpa using RelCWComplex.union_iUnion_openCell_eq_complex (C := C)

Depends on / 依赖: RelCWComplex, RelCWComplex.union_iUnion_openCell_eq_complex, union_iUnion_openCell_eq_complex
-/
lemma CWComplex.iUnion_openCell_eq_complex [CWComplex C] :
    ⋃ (n : Nat) (j : cell C n), openCell n j = C := by
  simpa using RelCWComplex.union_iUnion_openCell_eq_complex (C := C)

/-- The contrapositive of `disjoint_openCell_of_ne`. -/
@[alias_in CWComplex]
/--
lemma `RelCWComplex.eq_of_not_disjoint_openCell` / 引理 `RelCWComplex.eq_of_not_disjoint_openCell`

English:
lemma RelCWComplex.eq_of_not_disjoint_openCell
  statement: [RelCWComplex C D] {n : Nat} {j : cell C n} {m : Nat}
  proof: by
  contrapose! h
  exact disjoint_openCell_of_ne h

中文:
引理 RelCWComplex.eq_of_not_disjoint_openCell
  结论: [RelCWComplex C D] {n : 自然数} {j : cell C n} {m : 自然数}
  证明: by
  contrapose! h
  exact disjoint_openCell_of_ne h

Depends on / 依赖: contrapose, disjoint_openCell_of_ne
-/
lemma RelCWComplex.eq_of_not_disjoint_openCell [RelCWComplex C D] {n : Nat} {j : cell C n} {m : Nat}
    {i : cell C m} (h : ¬ Disjoint (openCell n j) (openCell m i)) :
    (⟨n, j⟩ : (Σ n, cell C n)) = ⟨m, i⟩ := by
  contrapose! h
  exact disjoint_openCell_of_ne h

/--
lemma `RelCWComplex.disjoint_base_iUnion_openCell` / 引理 `RelCWComplex.disjoint_base_iUnion_openCell`

English:
lemma RelCWComplex.disjoint_base_iUnion_openCell
  given: [RelCWComplex C D]
  proof: by
  simp_rw [disjoint_iff_inter_eq_empty, inter_iUnion, iUnion_eq_empty]
  intro n i
  rw [inter_comm]; rw [(disjointBase n i).inter_eq]

中文:
引理 RelCWComplex.disjoint_base_iUnion_openCell
  条件: [RelCWComplex C D]
  证明: by
  simp_rw [disjoint_iff_inter_eq_empty, inter_iUnion, iUnion_eq_empty]
  intro n i
  rw [inter_comm]; rw [(disjointBase n i).inter_eq]

Depends on / 依赖: disjointBase, disjoint_iff_inter_eq_empty, iUnion_eq_empty, inter_comm, inter_eq, inter_iUnion, simp_rw
-/
lemma RelCWComplex.disjoint_base_iUnion_openCell [RelCWComplex C D] :
    Disjoint D (⋃ (n : Nat) (j : cell C n), openCell n j) := by
  simp_rw [disjoint_iff_inter_eq_empty, inter_iUnion, iUnion_eq_empty]
  intro n i
  rw [inter_comm]; rw [(disjointBase n i).inter_eq]

/--
lemma `RelCWComplex.isClosed_inter_cellFrontier_succ_of_le_isClosed_inter_closedCell` / 引理 `RelCWComplex.isClosed_inter_cellFrontier_succ_of_le_isClosed_inter_closedCell`

English:
lemma RelCWComplex.isClosed_inter_cellFrontier_succ_of_le_isClosed_inter_closedCell
  proof: by
  -- this is a consequence of `cellFrontier_subset_base_union_finite_closedCell`
  obtain ⟨I, hI⟩ := cellFrontier_subset_base_union_finite_closedCell (n + 1) j
  rw [← inter_eq_right.2 hI]; rw [← inter_assoc]
  refine IsClosed.inter ?_ isClosed_cellFrontier
  simp_rw [inter_union_distrib_left, inter_iUnion,
    ← iUnion_subtype (fun m => m < n + 1) (fun m => ⋃ i in I m, A inter closedCell m i)]
  apply hD.union
  apply isClosed_iUnion_of_finite
  intro ⟨m, mlt⟩
  rw [← iUnion_subtype (fun i => i in I m) (fun i => A inter closedCell m i.1)]
  exact isClosed_iUnion_of_finite (fun ⟨j, _⟩ => hn m (Nat.le_of_lt_succ mlt) j)

中文:
引理 RelCWComplex.isClosed_inter_cellFrontier_succ_of_le_isClosed_inter_closedCell
  证明: by
  -- this is a consequence of `cellFrontier_subset_base_union_finite_closedCell`
  obtain ⟨I, hI⟩ := cellFrontier_subset_base_union_finite_closedCell (n + 1) j
  rw [← inter_eq_right.2 hI]; rw [← inter_assoc]
  refine IsClosed.inter ?_ isClosed_cellFrontier
  simp_rw [inter_union_distrib_left, inter_iUnion,
    ← iUnion_subtype (fun m => m < n + 1) (fun m => ⋃ i in I m, A inter closedCell m i)]
  apply hD.union
  apply isClosed_iUnion_of_finite
  intro ⟨m, mlt⟩
  rw [← iUnion_subtype (fun i => i in I m) (fun i => A inter closedCell m i.1)]
  exact isClosed_iUnion_of_finite (fun ⟨j, _⟩ => hn m (Nat.le_of_lt_succ mlt) j)
-/
lemma RelCWComplex.isClosed_inter_cellFrontier_succ_of_le_isClosed_inter_closedCell
    [RelCWComplex C D] [T2Space X] {A : Set X} {n : Nat} (hn : forall m <= n, forall (j : cell C m),
    IsClosed (A inter closedCell m j)) (j : cell C (n + 1)) (hD : IsClosed (A inter D)) :
    IsClosed (A inter cellFrontier (n + 1) j) := by
  -- this is a consequence of `cellFrontier_subset_base_union_finite_closedCell`
  obtain ⟨I, hI⟩ := cellFrontier_subset_base_union_finite_closedCell (n + 1) j
  rw [← inter_eq_right.2 hI]; rw [← inter_assoc]
  refine IsClosed.inter ?_ isClosed_cellFrontier
  simp_rw [inter_union_distrib_left, inter_iUnion,
    ← iUnion_subtype (fun m => m < n + 1) (fun m => ⋃ i in I m, A inter closedCell m i)]
  apply hD.union
  apply isClosed_iUnion_of_finite
  intro ⟨m, mlt⟩
  rw [← iUnion_subtype (fun i => i in I m) (fun i => A inter closedCell m i.1)]
  exact isClosed_iUnion_of_finite (fun ⟨j, _⟩ => hn m (Nat.le_of_lt_succ mlt) j)

/--
lemma `CWComplex.isClosed_inter_cellFrontier_succ_of_le_isClosed_inter_closedCell` / 引理 `CWComplex.isClosed_inter_cellFrontier_succ_of_le_isClosed_inter_closedCell`

English:
lemma CWComplex.isClosed_inter_cellFrontier_succ_of_le_isClosed_inter_closedCell
  proof: RelCWComplex.isClosed_inter_cellFrontier_succ_of_le_isClosed_inter_closedCell hn j
    (by simp only [inter_empty, isClosed_empty])

中文:
引理 CWComplex.isClosed_inter_cellFrontier_succ_of_le_isClosed_inter_closedCell
  证明: RelCWComplex.isClosed_inter_cellFrontier_succ_of_le_isClosed_inter_closedCell hn j
    (by simp only [inter_empty, isClosed_empty])

Depends on / 依赖: RelCWComplex, RelCWComplex.isClosed_inter_cellFrontier_succ_of_le_isClosed_inter_closedCell, inter_empty, isClosed_empty, isClosed_inter_cellFrontier_succ_of_le_isClosed_inter_closedCell
-/
lemma CWComplex.isClosed_inter_cellFrontier_succ_of_le_isClosed_inter_closedCell
    [CWComplex C] [T2Space X] {A : Set X} {n : Nat} (hn : forall m <= n, forall (j : cell C m),
    IsClosed (A inter closedCell m j)) (j : cell C (n + 1)) :
    IsClosed (A inter cellFrontier (n + 1) j) :=
  RelCWComplex.isClosed_inter_cellFrontier_succ_of_le_isClosed_inter_closedCell hn j
    (by simp only [inter_empty, isClosed_empty])

/--
lemma `RelCWComplex.isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell` / 引理 `RelCWComplex.isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell`

English:
lemma RelCWComplex.isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell
  proof: by
  rw [closed C A hAC]
  refine ⟨?_, hDA⟩
  intro n j
  induction n using Nat.case_strong_induction_on with
  | hz =>
    rw [closedCell_zero_eq_singleton]
    exact isClosed_inter_singleton
  | hi n hn =>
    specialize h n.succ n.zero_lt_succ j
    rcases h with h1 | h2
    · rw [← cellFrontier_union_openCell_eq_closedCell, inter_union_distrib_left]
      exact (isClosed_inter_cellFrontier_succ_of_le_isClosed_inter_closedCell hn j hDA).union h1
    · exact h2

中文:
引理 RelCWComplex.isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell
  证明: by
  rw [closed C A hAC]
  refine ⟨?_, hDA⟩
  intro n j
  induction n using Nat.case_strong_induction_on with
  | hz =>
    rw [closedCell_zero_eq_singleton]
    exact isClosed_inter_singleton
  | hi n hn =>
    specialize h n.succ n.zero_lt_succ j
    rcases h with h1 | h2
    · rw [← cellFrontier_union_openCell_eq_closedCell, inter_union_distrib_left]
      exact (isClosed_inter_cellFrontier_succ_of_le_isClosed_inter_closedCell hn j hDA).union h1
    · exact h2

Depends on / 依赖: Nat.case_strong_induction_on, case_strong_induction_on, cellFrontier_union_openCell_eq_closedCell, closed, closedCell_zero_eq_singleton, inter_union_distrib_left, isClosed_inter_cellFrontier_succ_of_le_isClosed_inter_closedCell, isClosed_inter_singleton, n.succ, n.zero_lt_succ, specialize, zero_lt_succ
-/
lemma RelCWComplex.isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell
    [RelCWComplex C D] [T2Space X] {A : Set X} (hAC : A subseteq C) (hDA : IsClosed (A inter D))
    (h : forall n (_ : 0 < n), forall (j : cell C n),
    IsClosed (A inter openCell n j) ∨ IsClosed (A inter closedCell n j)) : IsClosed A := by
  rw [closed C A hAC]
  refine ⟨?_, hDA⟩
  intro n j
  induction n using Nat.case_strong_induction_on with
  | hz =>
    rw [closedCell_zero_eq_singleton]
    exact isClosed_inter_singleton
  | hi n hn =>
    specialize h n.succ n.zero_lt_succ j
    rcases h with h1 | h2
    · rw [← cellFrontier_union_openCell_eq_closedCell, inter_union_distrib_left]
      exact (isClosed_inter_cellFrontier_succ_of_le_isClosed_inter_closedCell hn j hDA).union h1
    · exact h2

/--
lemma `RelCWComplex.isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell` / 引理 `RelCWComplex.isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell`

English:
lemma RelCWComplex.isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell
  proof: by
  apply isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell hAC hDA
  intro n hn j
  rcases h n hn j with h | h
  · left
    rw [disjoint_iff_inter_eq_empty.1 h]
    exact isClosed_empty
  · exact Or.inr h

中文:
引理 RelCWComplex.isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell
  证明: by
  apply isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell hAC hDA
  intro n hn j
  rcases h n hn j with h | h
  · left
    rw [disjoint_iff_inter_eq_empty.1 h]
    exact isClosed_empty
  · exact Or.inr h

Depends on / 依赖: Or.inr, disjoint_iff_inter_eq_empty, isClosed_empty, isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell
-/
lemma RelCWComplex.isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell
    [RelCWComplex C D] [T2Space X] {A : Set X} (hAC : A subseteq C) (hDA : IsClosed (A inter D))
    (h : forall n (_ : 0 < n), forall (j : cell C n),
    Disjoint A (openCell n j) ∨ IsClosed (A inter closedCell n j)) : IsClosed A := by
  apply isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell hAC hDA
  intro n hn j
  rcases h n hn j with h | h
  · left
    rw [disjoint_iff_inter_eq_empty.1 h]
    exact isClosed_empty
  · exact Or.inr h

/--
lemma `CWComplex.isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell` / 引理 `CWComplex.isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell`

English:
lemma CWComplex.isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell
  proof: RelCWComplex.isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell hAC (by simp) h

中文:
引理 CWComplex.isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell
  证明: RelCWComplex.isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell hAC (by simp) h

Depends on / 依赖: RelCWComplex, RelCWComplex.isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell, isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell
-/
lemma CWComplex.isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell
    [CWComplex C] [T2Space X] {A : Set X} (hAC : A subseteq C) (h : forall n (_ : 0 < n), forall (j : cell C n),
    IsClosed (A inter openCell n j) ∨ IsClosed (A inter closedCell n j)) : IsClosed A :=
  RelCWComplex.isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell hAC (by simp) h

/--
lemma `CWComplex.isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell` / 引理 `CWComplex.isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell`

English:
lemma CWComplex.isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell
  proof: RelCWComplex.isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell hAC (by simp) h

中文:
引理 CWComplex.isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell
  证明: RelCWComplex.isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell hAC (by simp) h

Depends on / 依赖: RelCWComplex, RelCWComplex.isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell, isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell
-/
lemma CWComplex.isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell
    [CWComplex C] [T2Space X] {A : Set X} (hAC : A subseteq C) (h : forall n (_ : 0 < n), forall (j : cell C n),
    Disjoint A (openCell n j) ∨ IsClosed (A inter closedCell n j)) : IsClosed A :=
  RelCWComplex.isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell hAC (by simp) h

/--
lemma `RelCWComplex.cellFrontier_subset_finite_openCell` / 引理 `RelCWComplex.cellFrontier_subset_finite_openCell`

English:
lemma RelCWComplex.cellFrontier_subset_finite_openCell
  given: [RelCWComplex C D] (n : Nat) (i : cell C n)
  proof: by
  induction n using Nat.case_strong_induction_on with
  | hz => simp [cellFrontier_zero_eq_empty]
  | hi n hn =>
    -- We apply `cellFrontier_subset_base_union_finite_closedCell` once and then apply
    -- the induction hypothesis to the finitely many cells that
    -- `cellFrontier_subset_base_union_finite_closedCell` gives us.
    classical
    obtain ⟨J, hJ⟩ := cellFrontier_subset_base_union_finite_closedCell n.succ i
    choose p hp using hn
    let I m := J m union ((Finset.range n.succ).biUnion
      (fun l => (J l).biUnion (fun y => if h : l <= n then p l h y m else ∅)))
    use I
    intro x hx
    specialize hJ hx
    simp only [mem_union, mem_iUnion, exists_prop] at hJ ⊢
    rcases hJ with hJ | hJ
    · exact .inl hJ
    obtain ⟨l, hln, j, hj, hxj⟩ := hJ
    rw [← cellFrontier_union_openCell_eq_closedCell] at hxj
    rcases hxj with hxj | hxj
    · specialize hp l (Nat.le_of_lt_succ hln) j hxj
      simp_rw [mem_union, mem_iUnion, exists_prop] at hp
      refine .imp_right (fun ⟨k, hkl, i, hi, hxi⟩ => ⟨k, lt_trans hkl hln, i, ?_, hxi⟩) hp
      simp only [Nat.succ_eq_add_one, Finset.mem_union, Finset.mem_biUnion, Finset.mem_range, I]
      exact .inr ⟨l, hln, j, hj, by simp [Nat.le_of_lt_succ hln, hi]⟩
    · right
      use l, hln, j
      simp only [Nat.succ_eq_add_one, Finset.mem_union, I]
      exact ⟨Or.intro_left _ hj, hxj⟩

中文:
引理 RelCWComplex.cellFrontier_subset_finite_openCell
  条件: [RelCWComplex C D] (n : 自然数) (i : cell C n)
  证明: by
  induction n using Nat.case_strong_induction_on with
  | hz => simp [cellFrontier_zero_eq_empty]
  | hi n hn =>
    -- We apply `cellFrontier_subset_base_union_finite_closedCell` once and then apply
    -- the induction hypothesis to the finitely many cells that
    -- `cellFrontier_subset_base_union_finite_closedCell` gives us.
    classical
    obtain ⟨J, hJ⟩ := cellFrontier_subset_base_union_finite_closedCell n.succ i
    choose p hp using hn
    let I m := J m union ((Finset.range n.succ).biUnion
      (fun l => (J l).biUnion (fun y => if h : l <= n then p l h y m else ∅)))
    use I
    intro x hx
    specialize hJ hx
    simp only [mem_union, mem_iUnion, exists_prop] at hJ ⊢
    rcases hJ with hJ | hJ
    · exact .inl hJ
    obtain ⟨l, hln, j, hj, hxj⟩ := hJ
    rw [← cellFrontier_union_openCell_eq_closedCell] at hxj
    rcases hxj with hxj | hxj
    · specialize hp l (Nat.le_of_lt_succ hln) j hxj
      simp_rw [mem_union, mem_iUnion, exists_prop] at hp
      refine .imp_right (fun ⟨k, hkl, i, hi, hxi⟩ => ⟨k, lt_trans hkl hln, i, ?_, hxi⟩) hp
      simp only [Nat.succ_eq_add_one, Finset.mem_union, Finset.mem_biUnion, Finset.mem_range, I]
      exact .inr ⟨l, hln, j, hj, by simp [Nat.le_of_lt_succ hln, hi]⟩
    · right
      use l, hln, j
      simp only [Nat.succ_eq_add_one, Finset.mem_union, I]
      exact ⟨Or.intro_left _ hj, hxj⟩

Depends on / 依赖: Nat.case_strong_induction_on, case_strong_induction_on, cellFrontier_zero_eq_empty
-/
lemma RelCWComplex.cellFrontier_subset_finite_openCell [RelCWComplex C D] (n : Nat) (i : cell C n) :
    exists I : Π m, Finset (cell C m),
    cellFrontier n i subseteq D union (⋃ (m < n) (j in I m), openCell m j) := by
  induction n using Nat.case_strong_induction_on with
  | hz => simp [cellFrontier_zero_eq_empty]
  | hi n hn =>
    -- We apply `cellFrontier_subset_base_union_finite_closedCell` once and then apply
    -- the induction hypothesis to the finitely many cells that
    -- `cellFrontier_subset_base_union_finite_closedCell` gives us.
    classical
    obtain ⟨J, hJ⟩ := cellFrontier_subset_base_union_finite_closedCell n.succ i
    choose p hp using hn
    let I m := J m union ((Finset.range n.succ).biUnion
      (fun l => (J l).biUnion (fun y => if h : l <= n then p l h y m else ∅)))
    use I
    intro x hx
    specialize hJ hx
    simp only [mem_union, mem_iUnion, exists_prop] at hJ ⊢
    rcases hJ with hJ | hJ
    · exact .inl hJ
    obtain ⟨l, hln, j, hj, hxj⟩ := hJ
    rw [← cellFrontier_union_openCell_eq_closedCell] at hxj
    rcases hxj with hxj | hxj
    · specialize hp l (Nat.le_of_lt_succ hln) j hxj
      simp_rw [mem_union, mem_iUnion, exists_prop] at hp
      refine .imp_right (fun ⟨k, hkl, i, hi, hxi⟩ => ⟨k, lt_trans hkl hln, i, ?_, hxi⟩) hp
      simp only [Nat.succ_eq_add_one, Finset.mem_union, Finset.mem_biUnion, Finset.mem_range, I]
      exact .inr ⟨l, hln, j, hj, by simp [Nat.le_of_lt_succ hln, hi]⟩
    · right
      use l, hln, j
      simp only [Nat.succ_eq_add_one, Finset.mem_union, I]
      exact ⟨Or.intro_left _ hj, hxj⟩

/--
lemma `CWComplex.cellFrontier_subset_finite_openCell` / 引理 `CWComplex.cellFrontier_subset_finite_openCell`

English:
lemma CWComplex.cellFrontier_subset_finite_openCell
  given: [CWComplex C] (n : Nat) (i : cell C n)
  proof: by
  simpa using RelCWComplex.cellFrontier_subset_finite_openCell n i

中文:
引理 CWComplex.cellFrontier_subset_finite_openCell
  条件: [CWComplex C] (n : 自然数) (i : cell C n)
  证明: by
  simpa using RelCWComplex.cellFrontier_subset_finite_openCell n i

Depends on / 依赖: RelCWComplex, RelCWComplex.cellFrontier_subset_finite_openCell, cellFrontier_subset_finite_openCell
-/
lemma CWComplex.cellFrontier_subset_finite_openCell [CWComplex C] (n : Nat) (i : cell C n) :
    exists I : Π m, Finset (cell C m),
    cellFrontier n i subseteq ⋃ (m < n) (j in I m), openCell m j := by
  simpa using RelCWComplex.cellFrontier_subset_finite_openCell n i

section Subcomplex

namespace RelCWComplex

/--
Definition of `Subcomplex` / `Subcomplex` 的定义

English:
structure Subcomplex
  parameters: (C : Set X) {D : Set X} [RelCWComplex C D]
  axioms and operations (4):
    - carrier : Set X
    - I : Π n, Set (cell C n)
    - closed' : IsClosed carrier
    - union' : D union ⋃ (n : Nat) (j : I n), openCell (C := C) n j = carrier

中文:
结构 子复形
  参数: (C : 集合 X) {D : 集合 X} [RelCWComplex C D]
  公理与运算 (4 个):
    - carrier : 集合 X
    - I : Π n, 集合 (cell C n)
    - closed' : 是闭集 carrier
    - union' : D union ⋃ (n : 自然数) (j : I n), openCell (C := C) n j = carrier

Depends on / 依赖: carrier
-/
structure Subcomplex (C : Set X) {D : Set X} [RelCWComplex C D] where
  /-- The underlying set of the subcomplex. -/
  carrier : Set X
  /-- The indexing set of cells of the subcomplex. -/
  I : Π n, Set (cell C n)
  /-- A subcomplex is closed. -/
  closed' : IsClosed carrier
  /-- The union of all open cells of the subcomplex equals the subcomplex. -/
  union' : D union ⋃ (n : Nat) (j : I n), openCell (C := C) n j = carrier

namespace Subcomplex

variable [RelCWComplex C D]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (Subcomplex C) X
  body: E.carrier
  coe_injective E F h := by
    obtain ⟨E, _, _, hE⟩ := E
    obtain ⟨F, _, _, hF⟩ := F
    congr
    apply eq_of_eq_union_iUnion
    rw [hE]; rw [hF]
    simpa using h

中文:
实例 :
  签名: 集合状 (子复形 C) X
  定义体: E.carrier
  coe_injective E F h := by
    obtain ⟨E, _, _, hE⟩ := E
    obtain ⟨F, _, _, hF⟩ := F
    congr
    apply eq_of_eq_union_iUnion
    rw [hE]; rw [hF]
    simpa using h

Depends on / 依赖: E.carrier, carrier
-/
instance : SetLike (Subcomplex C) X where
  coe E := E.carrier
  coe_injective E F h := by
    obtain ⟨E, _, _, hE⟩ := E
    obtain ⟨F, _, _, hF⟩ := F
    congr
    apply eq_of_eq_union_iUnion
    rw [hE]; rw [hF]
    simpa using h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (Subcomplex C)
  body: .ofSetLike (Subcomplex C) X

initialize_simps_projections Subcomplex (carrier -> coe, as_prefix coe)

@[alias_in CWComplex.Subcomplex]

中文:
实例 :
  签名: 偏序 (子复形 C)
  定义体: .ofSetLike (Subcomplex C) X

initialize_simps_projections Subcomplex (carrier -> coe, as_prefix coe)

@[alias_in CWComplex.Subcomplex]

Depends on / 依赖: Subcomplex, ofSetLike
-/
instance : PartialOrder (Subcomplex C) := .ofSetLike (Subcomplex C) X

initialize_simps_projections Subcomplex (carrier -> coe, as_prefix coe)

@[alias_in CWComplex.Subcomplex]
/--
lemma `mem_carrier` / 引理 `mem_carrier`

English:
lemma mem_carrier
  given: {E : Subcomplex C} {x : X}
  statement: x in E.carrier ↔ x in (E : Set X)
  proof: Iff.rfl

@[alias_in CWComplex.Subcomplex]

中文:
引理 mem_carrier
  条件: {E : 子复形 C} {x : X}
  结论: x in E.carrier ↔ x in (E : 集合 X)
  证明: Iff.rfl

@[alias_in CWComplex.Subcomplex]

Depends on / 依赖: Iff.rfl
-/
lemma mem_carrier {E : Subcomplex C} {x : X} : x in E.carrier ↔ x in (E : Set X) := Iff.rfl

@[alias_in CWComplex.Subcomplex]
/--
lemma `coe_eq_carrier` / 引理 `coe_eq_carrier`

English:
lemma coe_eq_carrier
  given: {E : Subcomplex C}
  statement: (E : Set X) = E.carrier
  proof: rfl

@[ext, alias_in CWComplex.Subcomplex]

中文:
引理 coe_eq_carrier
  条件: {E : 子复形 C}
  结论: (E : 集合 X) = E.carrier
  证明: rfl

@[ext, alias_in CWComplex.Subcomplex]
-/
lemma coe_eq_carrier {E : Subcomplex C} : (E : Set X) = E.carrier := rfl

@[ext, alias_in CWComplex.Subcomplex]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {E F : Subcomplex C} (h : forall x, x in E ↔ x in F)
  statement: E = F
  proof: SetLike.ext h

@[alias_in CWComplex.Subcomplex]

中文:
引理 ext
  条件: {E F : 子复形 C} (h : 对任意 x, x in E ↔ x in F)
  结论: E = F
  证明: SetLike.ext h

@[alias_in CWComplex.Subcomplex]

Depends on / 依赖: SetLike, SetLike.ext
-/
lemma ext {E F : Subcomplex C} (h : forall x, x in E ↔ x in F) : E = F :=
  SetLike.ext h

@[alias_in CWComplex.Subcomplex]
/--
lemma `eq_iff` / 引理 `eq_iff`

English:
lemma eq_iff
  given: (E F : Subcomplex C)
  statement: E = F ↔ (E : Set X) = F
  proof: SetLike.coe_injective.eq_iff.symm

中文:
引理 eq_iff
  条件: (E F : 子复形 C)
  结论: E = F ↔ (E : 集合 X) = F
  证明: SetLike.coe_injective.eq_iff.symm

Depends on / 依赖: SetLike, SetLike.coe_injective.eq_iff.symm, coe_injective, eq_iff
-/
lemma eq_iff (E F : Subcomplex C) : E = F ↔ (E : Set X) = F :=
  SetLike.coe_injective.eq_iff.symm

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (E : Subcomplex C) (F : Set X) (hF : F = E) (J : (n : Nat) -> Set (cell C n))
  body: { carrier := F
    I := J
    closed' := hF.symm ▸ E.closed'
    union' := hF.symm ▸ hJ ▸ E.union' }

@[simp, alias_in CWComplex.Subcomplex]

中文:
定义 copy
  签名: (E : 子复形 C) (F : 集合 X) (hF : F = E) (J : (n : 自然数) -> 集合 (cell C n))
  定义体: { carrier := F
    I := J
    closed' := hF.symm ▸ E.closed'
    union' := hF.symm ▸ hJ ▸ E.union' }

@[simp, alias_in CWComplex.Subcomplex]
-/
protected def copy (E : Subcomplex C) (F : Set X) (hF : F = E) (J : (n : Nat) -> Set (cell C n))
    (hJ : J = E.I) : Subcomplex C :=
  { carrier := F
    I := J
    closed' := hF.symm ▸ E.closed'
    union' := hF.symm ▸ hJ ▸ E.union' }

@[simp, alias_in CWComplex.Subcomplex]
/--
lemma `coe_copy` / 引理 `coe_copy`

English:
lemma coe_copy
  statement: (E : Subcomplex C) (F : Set X) (hF : F = E) (J : (n : Nat) -> Set (cell C n))
  proof: rfl

@[alias_in CWComplex.Subcomplex]

中文:
引理 coe_copy
  结论: (E : 子复形 C) (F : 集合 X) (hF : F = E) (J : (n : 自然数) -> 集合 (cell C n))
  证明: rfl

@[alias_in CWComplex.Subcomplex]
-/
lemma coe_copy (E : Subcomplex C) (F : Set X) (hF : F = E) (J : (n : Nat) -> Set (cell C n))
    (hJ : J = E.I) : (E.copy F hF J hJ : Set X) = F :=
  rfl

@[alias_in CWComplex.Subcomplex]
/--
lemma `copy_eq` / 引理 `copy_eq`

English:
lemma copy_eq
  statement: (E : Subcomplex C) (F : Set X) (hF : F = E) (J : (n : Nat) -> Set (cell C n))
  proof: SetLike.coe_injective hF

中文:
引理 copy_eq
  结论: (E : 子复形 C) (F : 集合 X) (hF : F = E) (J : (n : 自然数) -> 集合 (cell C n))
  证明: SetLike.coe_injective hF

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
lemma copy_eq (E : Subcomplex C) (F : Set X) (hF : F = E) (J : (n : Nat) -> Set (cell C n))
    (hJ : J = E.I) : E.copy F hF J hJ = E :=
  SetLike.coe_injective hF

/--
lemma `union` / 引理 `union`

English:
lemma union
  given: (E : Subcomplex C)
  proof: by
  rw [E.union']
  rfl

@[alias_in CWComplex.Subcomplex]

中文:
引理 union
  条件: (E : 子复形 C)
  证明: by
  rw [E.union']
  rfl

@[alias_in CWComplex.Subcomplex]

Depends on / 依赖: E.union
-/
lemma union (E : Subcomplex C) :
    D union ⋃ (n : Nat) (j : E.I n), openCell (C := C) n j.1 = E := by
  rw [E.union']
  rfl

@[alias_in CWComplex.Subcomplex]
/--
lemma `closed` / 引理 `closed`

English:
lemma closed
  given: (E : Subcomplex C)
  statement: IsClosed (E : Set X)
  proof: E.closed'

中文:
引理 closed
  条件: (E : 子复形 C)
  结论: 是闭集 (E : 集合 X)
  证明: E.closed'

Depends on / 依赖: E.closed, closed
-/
lemma closed (E : Subcomplex C) : IsClosed (E : Set X) := E.closed'

end Subcomplex

end RelCWComplex

namespace CWComplex

export RelCWComplex (Subcomplex Subcomplex.I Subcomplex.copy)

end CWComplex

/--
lemma `CWComplex.Subcomplex.union` / 引理 `CWComplex.Subcomplex.union`

English:
lemma CWComplex.Subcomplex.union
  given: {C : Set X} [CWComplex C] {E : Subcomplex C}
  proof: by
  have := RelCWComplex.Subcomplex.union E (C := C)
  rw [empty_union] at this
  exact this

中文:
引理 CWComplex.子复形.union
  条件: {C : 集合 X} [CWComplex C] {E : 子复形 C}
  证明: by
  have := RelCWComplex.Subcomplex.union E (C := C)
  rw [empty_union] at this
  exact this

Depends on / 依赖: RelCWComplex, RelCWComplex.Subcomplex.union, Subcomplex, empty_union
-/
lemma CWComplex.Subcomplex.union {C : Set X} [CWComplex C] {E : Subcomplex C} :
    ⋃ (n : Nat) (j : E.I n), openCell (C := C) n j = E := by
  have := RelCWComplex.Subcomplex.union E (C := C)
  rw [empty_union] at this
  exact this

/-- An alternative version of `Subcomplex.mk`: Instead of requiring that `E` is closed it requires
that for every cell of the subcomplex the corresponding closed cell is a subset of `E`. -/
@[simps -isSimp]
/--
Definition of `RelCWComplex.Subcomplex.mk'` / `RelCWComplex.Subcomplex.mk'` 的定义

English:
definition RelCWComplex.Subcomplex.mk'
  signature: [T2Space X] (C : Set X) {D : Set X} [RelCWComplex C D]
  body: E
  I := I
  closed' := by
    have hEC : (E : Set X) subseteq C := by
      simp_rw [← union, ← union_iUnion_openCell_eq_complex (C := C)]
      exact union_subset_union_right D
        (iUnion_mono fun n => iUnion_subset fun i => subset_iUnion _ (i : cell C n))
    apply isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell hEC
    · have : D subseteq E := by
        rw [← union]
        exact subset_union_left
      rw [inter_eq_right.2 this]
      exact isClosedBase C
    intro n _ j
    by_cases h : j in I n
    · right
      suffices closedCell n j subseteq E by
        rw [inter_eq_right.2 this]
        exact isClosed_closedCell
      exact closedCell_subset n ⟨j, h⟩
    · left
      simp_rw [← union, disjoint_union_left, disjoint_iUnion_left]
.symm, fun _ _ => disjoint_openCell_of_ne (by aesop)⟩ exact ⟨disjointBase n j
  union' := union

中文:
定义 RelCWComplex.子复形.mk'
  签名: [T2空间 X] (C : 集合 X) {D : 集合 X} [RelCWComplex C D]
  定义体: E
  I := I
  closed' := by
    have hEC : (E : Set X) subseteq C := by
      simp_rw [← union, ← union_iUnion_openCell_eq_complex (C := C)]
      exact union_subset_union_right D
        (iUnion_mono fun n => iUnion_subset fun i => subset_iUnion _ (i : cell C n))
    apply isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell hEC
    · have : D subseteq E := by
        rw [← union]
        exact subset_union_left
      rw [inter_eq_right.2 this]
      exact isClosedBase C
    intro n _ j
    by_cases h : j in I n
    · right
      suffices closedCell n j subseteq E by
        rw [inter_eq_right.2 this]
        exact isClosed_closedCell
      exact closedCell_subset n ⟨j, h⟩
    · left
      simp_rw [← union, disjoint_union_left, disjoint_iUnion_left]
.symm, fun _ _ => disjoint_openCell_of_ne (by aesop)⟩ exact ⟨disjointBase n j
  union' := union

Depends on / 依赖: subseteq
-/
def RelCWComplex.Subcomplex.mk' [T2Space X] (C : Set X) {D : Set X} [RelCWComplex C D]
    (E : Set X) (I : Π n, Set (cell C n))
    (closedCell_subset : forall (n : Nat) (i : I n), closedCell (C := C) n i subseteq E)
    (union : D union ⋃ (n : Nat) (j : I n), openCell (C := C) n j = E) : Subcomplex C where
  carrier := E
  I := I
  closed' := by
    have hEC : (E : Set X) subseteq C := by
      simp_rw [← union, ← union_iUnion_openCell_eq_complex (C := C)]
      exact union_subset_union_right D
        (iUnion_mono fun n => iUnion_subset fun i => subset_iUnion _ (i : cell C n))
    apply isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell hEC
    · have : D subseteq E := by
        rw [← union]
        exact subset_union_left
      rw [inter_eq_right.2 this]
      exact isClosedBase C
    intro n _ j
    by_cases h : j in I n
    · right
      suffices closedCell n j subseteq E by
        rw [inter_eq_right.2 this]
        exact isClosed_closedCell
      exact closedCell_subset n ⟨j, h⟩
    · left
      simp_rw [← union, disjoint_union_left, disjoint_iUnion_left]
.symm, fun _ _ => disjoint_openCell_of_ne (by aesop)⟩ exact ⟨disjointBase n j
  union' := union

/-- An alternative version of `Subcomplex.mk`: Instead of requiring that `E` is closed it requires
that for every cell of the subcomplex the corresponding closed cell is a subset of `E`. -/
@[simps! -isSimp]
/--
Definition of `CWComplex.Subcomplex.mk'` / `CWComplex.Subcomplex.mk'` 的定义

English:
definition CWComplex.Subcomplex.mk'
  signature: [T2Space X] (C : Set X) [CWComplex C] (E : Set X)
  body: RelCWComplex.Subcomplex.mk' C E I closedCell_subset (by rw [empty_union]; exact union)

中文:
定义 CWComplex.子复形.mk'
  签名: [T2空间 X] (C : 集合 X) [CWComplex C] (E : 集合 X)
  定义体: RelCWComplex.Subcomplex.mk' C E I closedCell_subset (by rw [empty_union]; exact union)

Depends on / 依赖: subseteq
-/
def CWComplex.Subcomplex.mk' [T2Space X] (C : Set X) [CWComplex C] (E : Set X)
    (I : Π n, Set (cell C n))
    (closedCell_subset : forall (n : Nat) (i : I n), closedCell (C := C) n i subseteq E)
    (union : ⋃ (n : Nat) (j : I n), openCell (C := C) n j = E) : Subcomplex C :=
  RelCWComplex.Subcomplex.mk' C E I closedCell_subset (by rw [empty_union]; exact union)

/-- An alternative version of `Subcomplex.mk`: Instead of requiring that `E` is closed it requires
that `E` is a CW-complex. -/
@[simps -isSimp]
/--
Definition of `RelCWComplex.Subcomplex.mk''` / `RelCWComplex.Subcomplex.mk''` 的定义

English:
definition RelCWComplex.Subcomplex.mk''
  signature: [T2Space X] (C : Set X) {D : Set X} [RelCWComplex C D] (E : Set X)
  body: E
  I := I
  closed' := isClosed
  union' := union

中文:
定义 RelCWComplex.子复形.mk''
  签名: [T2空间 X] (C : 集合 X) {D : 集合 X} [RelCWComplex C D] (E : 集合 X)
  定义体: E
  I := I
  closed' := isClosed
  union' := union

Depends on / 依赖: Subcomplex
-/
def RelCWComplex.Subcomplex.mk'' [T2Space X] (C : Set X) {D : Set X} [RelCWComplex C D] (E : Set X)
    (I : Π n, Set (cell C n)) [RelCWComplex E D]
    (union : D union ⋃ (n : Nat) (j : I n), openCell (C := C) n j = E) : Subcomplex C where
  carrier := E
  I := I
  closed' := isClosed
  union' := union

/-- An alternative version of `Subcomplex.mk`: Instead of requiring that `E` is closed it requires
that `E` is a CW-complex. -/
@[simps -isSimp]
/--
Definition of `CWComplex.Subcomplex.mk''` / `CWComplex.Subcomplex.mk''` 的定义

English:
definition CWComplex.Subcomplex.mk''
  signature: [T2Space X] (C : Set X) [h : CWComplex C] (E : Set X)
  body: E
  I := I
  closed' := RelCWComplex.isClosed
  union' := by
    rw [empty_union]
    exact union

@[alias_in CWComplex.Subcomplex]

中文:
定义 CWComplex.子复形.mk''
  签名: [T2空间 X] (C : 集合 X) [h : CWComplex C] (E : 集合 X)
  定义体: E
  I := I
  closed' := RelCWComplex.isClosed
  union' := by
    rw [empty_union]
    exact union

@[alias_in CWComplex.Subcomplex]
-/
def CWComplex.Subcomplex.mk'' [T2Space X] (C : Set X) [h : CWComplex C] (E : Set X)
    (I : Π n, Set (cell C n)) [CWComplex E]
    (union : ⋃ (n : Nat) (j : I n), openCell (C := C) n j = E) :
    Subcomplex C where
  carrier := E
  I := I
  closed' := RelCWComplex.isClosed
  union' := by
    rw [empty_union]
    exact union

@[alias_in CWComplex.Subcomplex]
/--
lemma `RelCWComplex.Subcomplex.subset_complex` / 引理 `RelCWComplex.Subcomplex.subset_complex`

English:
lemma RelCWComplex.Subcomplex.subset_complex
  given: {C D : Set X} [RelCWComplex C D] (E : Subcomplex C)
  proof: by
  simp_rw [← union, ← RelCWComplex.union_iUnion_openCell_eq_complex]
  exact union_subset_union_right _ (iUnion_mono fun _ => iUnion_mono' fun j => ⟨j, subset_rfl⟩)

@[alias_in CWComplex.Subcomplex]

中文:
引理 RelCWComplex.子复形.subset_complex
  条件: {C D : 集合 X} [RelCWComplex C D] (E : 子复形 C)
  证明: by
  simp_rw [← union, ← RelCWComplex.union_iUnion_openCell_eq_complex]
  exact union_subset_union_right _ (iUnion_mono fun _ => iUnion_mono' fun j => ⟨j, subset_rfl⟩)

@[alias_in CWComplex.Subcomplex]

Depends on / 依赖: RelCWComplex, RelCWComplex.union_iUnion_openCell_eq_complex, iUnion_mono, simp_rw, subset_rfl, union_iUnion_openCell_eq_complex, union_subset_union_right
-/
lemma RelCWComplex.Subcomplex.subset_complex {C D : Set X} [RelCWComplex C D] (E : Subcomplex C) :
    ↑E subseteq C := by
  simp_rw [← union, ← RelCWComplex.union_iUnion_openCell_eq_complex]
  exact union_subset_union_right _ (iUnion_mono fun _ => iUnion_mono' fun j => ⟨j, subset_rfl⟩)

@[alias_in CWComplex.Subcomplex]
/--
lemma `RelCWComplex.Subcomplex.base_subset` / 引理 `RelCWComplex.Subcomplex.base_subset`

English:
lemma RelCWComplex.Subcomplex.base_subset
  given: {C D : Set X} [RelCWComplex C D] (E : Subcomplex C)
  proof: by
  simp_rw [← union]
  exact subset_union_left

中文:
引理 RelCWComplex.子复形.base_subset
  条件: {C D : 集合 X} [RelCWComplex C D] (E : 子复形 C)
  证明: by
  simp_rw [← union]
  exact subset_union_left

Depends on / 依赖: simp_rw, subset_union_left
-/
lemma RelCWComplex.Subcomplex.base_subset {C D : Set X} [RelCWComplex C D] (E : Subcomplex C) :
    D subseteq E := by
  simp_rw [← union]
  exact subset_union_left

end Subcomplex

section skeleton

variable [T2Space X]

namespace RelCWComplex

/-- A non-standard definition of the `n`-skeleton of a CW complex for `n ∈ ℕ ∪ {∞}`.
This allows the base case of induction to be about the base instead of being about the union of
the base and some points.
The standard `skeleton` is defined in terms of `skeletonLT`. `skeletonLT` is preferred
in statements. You should then derive the statement about `skeleton`. -/
@[simps! (attr := alias_in CWComplex) -isSimp, irreducible]
/--
Definition of `skeletonLT` / `skeletonLT` 的定义

English:
definition skeletonLT
  signature: (C : Set X) {D : Set X} [RelCWComplex C D] (n : Nat∞)
  body: Subcomplex.mk' _ (D union ⋃ (m : Nat) (_ : m < n) (j : cell C m), closedCell m j)
    (fun l => {x : cell C l | l < n})
    (by
      intro l ⟨i, hi⟩
      apply subset_union_of_subset_right
      apply subset_iUnion₂_of_subset l hi
      exact subset_iUnion _ _)
    (by
      rw [← RelCWComplex.iUnion_openCell_eq_iUnion_closedCell]
      congrm D union ?_
      apply iUnion_congr fun m => ?_
      rw [iUnion_subtype]; rw [iUnion_comm]
      rfl)

中文:
定义 skeletonLT
  签名: (C : 集合 X) {D : 集合 X} [RelCWComplex C D] (n : 自然数∞)
  定义体: Subcomplex.mk' _ (D union ⋃ (m : Nat) (_ : m < n) (j : cell C m), closedCell m j)
    (fun l => {x : cell C l | l < n})
    (by
      intro l ⟨i, hi⟩
      apply subset_union_of_subset_right
      apply subset_iUnion₂_of_subset l hi
      exact subset_iUnion _ _)
    (by
      rw [← RelCWComplex.iUnion_openCell_eq_iUnion_closedCell]
      congrm D union ?_
      apply iUnion_congr fun m => ?_
      rw [iUnion_subtype]; rw [iUnion_comm]
      rfl)

Depends on / 依赖: RelCWComplex, RelCWComplex.iUnion_openCell_eq_iUnion_closedCell, Subcomplex, Subcomplex.mk, closedCell, congrm, iUnion_comm, iUnion_congr, iUnion_openCell_eq_iUnion_closedCell, iUnion_subtype, subset_iUnion, subset_union_of_subset_right
-/
def skeletonLT (C : Set X) {D : Set X} [RelCWComplex C D] (n : Nat∞) : Subcomplex C :=
    Subcomplex.mk' _ (D union ⋃ (m : Nat) (_ : m < n) (j : cell C m), closedCell m j)
    (fun l => {x : cell C l | l < n})
    (by
      intro l ⟨i, hi⟩
      apply subset_union_of_subset_right
      apply subset_iUnion₂_of_subset l hi
      exact subset_iUnion _ _)
    (by
      rw [← RelCWComplex.iUnion_openCell_eq_iUnion_closedCell]
      congrm D union ?_
      apply iUnion_congr fun m => ?_
      rw [iUnion_subtype]; rw [iUnion_comm]
      rfl)

/--
Definition of `skeleton` / `skeleton` 的定义

English:
abbreviation skeleton
  signature: (C : Set X) {D : Set X} [RelCWComplex C D] (n : Nat∞)
  body: skeletonLT C (n + 1)

中文:
缩写 skeleton
  签名: (C : 集合 X) {D : 集合 X} [RelCWComplex C D] (n : 自然数∞)
  定义体: skeletonLT C (n + 1)

Depends on / 依赖: skeletonLT
-/
abbrev skeleton (C : Set X) {D : Set X} [RelCWComplex C D] (n : Nat∞) : Subcomplex C :=
  skeletonLT C (n + 1)

end RelCWComplex

namespace CWComplex

export RelCWComplex (skeletonLT skeleton)

end CWComplex

/--
lemma `RelCWComplex.skeletonLT_zero_eq_base` / 引理 `RelCWComplex.skeletonLT_zero_eq_base`

English:
lemma RelCWComplex.skeletonLT_zero_eq_base
  given: [RelCWComplex C D]
  statement: skeletonLT C 0 = D
  proof: by
  simp [coe_skeletonLT]

中文:
引理 RelCWComplex.skeletonLT_zero_eq_base
  条件: [RelCWComplex C D]
  结论: skeletonLT C 0 = D
  证明: by
  simp [coe_skeletonLT]

Depends on / 依赖: coe_skeletonLT
-/
lemma RelCWComplex.skeletonLT_zero_eq_base [RelCWComplex C D] : skeletonLT C 0 = D := by
  simp [coe_skeletonLT]

/--
lemma `CWComplex.skeletonLT_zero_eq_empty` / 引理 `CWComplex.skeletonLT_zero_eq_empty`

English:
lemma CWComplex.skeletonLT_zero_eq_empty
  given: [CWComplex C]
  statement: (skeletonLT C 0 : Set X) = ∅
  proof: RelCWComplex.skeletonLT_zero_eq_base

中文:
引理 CWComplex.skeletonLT_zero_eq_empty
  条件: [CWComplex C]
  结论: (skeletonLT C 0 : 集合 X) = ∅
  证明: RelCWComplex.skeletonLT_zero_eq_base

Depends on / 依赖: RelCWComplex, RelCWComplex.skeletonLT_zero_eq_base, skeletonLT_zero_eq_base
-/
lemma CWComplex.skeletonLT_zero_eq_empty [CWComplex C] : (skeletonLT C 0 : Set X) = ∅ :=
    RelCWComplex.skeletonLT_zero_eq_base

/--
lemma `RelCWComplex.skeletonLT_top` / 引理 `RelCWComplex.skeletonLT_top`

English:
lemma RelCWComplex.skeletonLT_top
  given: [RelCWComplex C D]
  proof: by
  simp [coe_skeletonLT, union]

中文:
引理 RelCWComplex.skeletonLT_top
  条件: [RelCWComplex C D]
  证明: by
  simp [coe_skeletonLT, union]
-/
@[simp, alias_in CWComplex] lemma RelCWComplex.skeletonLT_top [RelCWComplex C D] :
    skeletonLT C ⊤ = C := by
  simp [coe_skeletonLT, union]

/--
lemma `RelCWComplex.skeleton_top` / 引理 `RelCWComplex.skeleton_top`

English:
lemma RelCWComplex.skeleton_top
  given: [RelCWComplex C D]
  statement: skeleton C ⊤ = C
  proof: skeletonLT_top

@[alias_in CWComplex]

中文:
引理 RelCWComplex.skeleton_top
  条件: [RelCWComplex C D]
  结论: skeleton C ⊤ = C
  证明: skeletonLT_top

@[alias_in CWComplex]
-/
@[simp, alias_in CWComplex] lemma RelCWComplex.skeleton_top [RelCWComplex C D] : skeleton C ⊤ = C :=
  skeletonLT_top

@[alias_in CWComplex]
/--
lemma `RelCWComplex.skeletonLT_mono` / 引理 `RelCWComplex.skeletonLT_mono`

English:
lemma RelCWComplex.skeletonLT_mono
  given: [RelCWComplex C D] {n m : Nat∞} (h : m <= n)
  proof: by
  simp_rw [coe_skeletonLT]
  apply union_subset_union_right
  intro x xmem
  simp_rw [mem_iUnion, exists_prop] at xmem ⊢
  obtain ⟨l, lltm, xmeml⟩ := xmem
  exact ⟨l, lt_of_lt_of_le lltm h, xmeml⟩

@[alias_in CWComplex]

中文:
引理 RelCWComplex.skeletonLT_mono
  条件: [RelCWComplex C D] {n m : 自然数∞} (h : m <= n)
  证明: by
  simp_rw [coe_skeletonLT]
  apply union_subset_union_right
  intro x xmem
  simp_rw [mem_iUnion, exists_prop] at xmem ⊢
  obtain ⟨l, lltm, xmeml⟩ := xmem
  exact ⟨l, lt_of_lt_of_le lltm h, xmeml⟩

@[alias_in CWComplex]

Depends on / 依赖: coe_skeletonLT, exists_prop, lt_of_lt_of_le, mem_iUnion, simp_rw, union_subset_union_right
-/
lemma RelCWComplex.skeletonLT_mono [RelCWComplex C D] {n m : Nat∞} (h : m <= n) :
    (skeletonLT C m : Set X) subseteq skeletonLT C n := by
  simp_rw [coe_skeletonLT]
  apply union_subset_union_right
  intro x xmem
  simp_rw [mem_iUnion, exists_prop] at xmem ⊢
  obtain ⟨l, lltm, xmeml⟩ := xmem
  exact ⟨l, lt_of_lt_of_le lltm h, xmeml⟩

@[alias_in CWComplex]
/--
lemma `RelCWComplex.skeletonLT_monotone` / 引理 `RelCWComplex.skeletonLT_monotone`

English:
lemma RelCWComplex.skeletonLT_monotone
  given: [RelCWComplex C D]
  statement: Monotone (skeletonLT C)
  proof: fun _ _ h => skeletonLT_mono h

@[alias_in CWComplex]

中文:
引理 RelCWComplex.skeletonLT_monotone
  条件: [RelCWComplex C D]
  结论: 递增 (skeletonLT C)
  证明: fun _ _ h => skeletonLT_mono h

@[alias_in CWComplex]

Depends on / 依赖: skeletonLT_mono
-/
lemma RelCWComplex.skeletonLT_monotone [RelCWComplex C D] : Monotone (skeletonLT C) :=
  fun _ _ h => skeletonLT_mono h

@[alias_in CWComplex]
/--
lemma `RelCWComplex.skeleton_mono` / 引理 `RelCWComplex.skeleton_mono`

English:
lemma RelCWComplex.skeleton_mono
  given: [RelCWComplex C D] {n m : Nat∞} (h : m <= n)
  proof: skeletonLT_mono (by gcongr)

@[alias_in CWComplex]

中文:
引理 RelCWComplex.skeleton_mono
  条件: [RelCWComplex C D] {n m : 自然数∞} (h : m <= n)
  证明: skeletonLT_mono (by gcongr)

@[alias_in CWComplex]

Depends on / 依赖: skeletonLT_mono
-/
lemma RelCWComplex.skeleton_mono [RelCWComplex C D] {n m : Nat∞} (h : m <= n) :
    (skeleton C m : Set X) subseteq skeleton C n :=
  skeletonLT_mono (by gcongr)

@[alias_in CWComplex]
/--
lemma `RelCWComplex.skeleton_monotone` / 引理 `RelCWComplex.skeleton_monotone`

English:
lemma RelCWComplex.skeleton_monotone
  given: [RelCWComplex C D]
  statement: Monotone (skeleton C)
  proof: fun _ _ h => skeleton_mono h

@[alias_in CWComplex]

中文:
引理 RelCWComplex.skeleton_monotone
  条件: [RelCWComplex C D]
  结论: 递增 (skeleton C)
  证明: fun _ _ h => skeleton_mono h

@[alias_in CWComplex]

Depends on / 依赖: skeleton_mono
-/
lemma RelCWComplex.skeleton_monotone [RelCWComplex C D] : Monotone (skeleton C) :=
  fun _ _ h => skeleton_mono h

@[alias_in CWComplex]
/--
lemma `RelCWComplex.closedCell_subset_skeletonLT` / 引理 `RelCWComplex.closedCell_subset_skeletonLT`

English:
lemma RelCWComplex.closedCell_subset_skeletonLT
  given: [RelCWComplex C D] (n : Nat) (j : cell C n)
  proof: by
  intro x xmem
  rw [coe_skeletonLT]
  right
  simp_rw [mem_iUnion, exists_prop]
  refine ⟨n, (by norm_cast; exact lt_add_one n), ⟨j,xmem⟩⟩

@[alias_in CWComplex]

中文:
引理 RelCWComplex.closedCell_subset_skeletonLT
  条件: [RelCWComplex C D] (n : 自然数) (j : cell C n)
  证明: by
  intro x xmem
  rw [coe_skeletonLT]
  right
  simp_rw [mem_iUnion, exists_prop]
  refine ⟨n, (by norm_cast; exact lt_add_one n), ⟨j,xmem⟩⟩

@[alias_in CWComplex]

Depends on / 依赖: coe_skeletonLT, exists_prop, lt_add_one, mem_iUnion, simp_rw
-/
lemma RelCWComplex.closedCell_subset_skeletonLT [RelCWComplex C D] (n : Nat) (j : cell C n) :
    closedCell n j subseteq skeletonLT C (n + 1) := by
  intro x xmem
  rw [coe_skeletonLT]
  right
  simp_rw [mem_iUnion, exists_prop]
  refine ⟨n, (by norm_cast; exact lt_add_one n), ⟨j,xmem⟩⟩

@[alias_in CWComplex]
/--
lemma `RelCWComplex.closedCell_subset_skeleton` / 引理 `RelCWComplex.closedCell_subset_skeleton`

English:
lemma RelCWComplex.closedCell_subset_skeleton
  given: [RelCWComplex C D] (n : Nat) (j : cell C n)
  proof: closedCell_subset_skeletonLT n j

@[alias_in CWComplex]

中文:
引理 RelCWComplex.closedCell_subset_skeleton
  条件: [RelCWComplex C D] (n : 自然数) (j : cell C n)
  证明: closedCell_subset_skeletonLT n j

@[alias_in CWComplex]

Depends on / 依赖: closedCell_subset_skeletonLT
-/
lemma RelCWComplex.closedCell_subset_skeleton [RelCWComplex C D] (n : Nat) (j : cell C n) :
    closedCell n j subseteq skeleton C n :=
  closedCell_subset_skeletonLT n j

@[alias_in CWComplex]
/--
lemma `RelCWComplex.openCell_subset_skeletonLT` / 引理 `RelCWComplex.openCell_subset_skeletonLT`

English:
lemma RelCWComplex.openCell_subset_skeletonLT
  given: [RelCWComplex C D] (n : Nat) (j : cell C n)
  proof: (openCell_subset_closedCell _ _).trans (closedCell_subset_skeletonLT _ _)

@[alias_in CWComplex]

中文:
引理 RelCWComplex.openCell_subset_skeletonLT
  条件: [RelCWComplex C D] (n : 自然数) (j : cell C n)
  证明: (openCell_subset_closedCell _ _).trans (closedCell_subset_skeletonLT _ _)

@[alias_in CWComplex]

Depends on / 依赖: closedCell_subset_skeletonLT, openCell_subset_closedCell
-/
lemma RelCWComplex.openCell_subset_skeletonLT [RelCWComplex C D] (n : Nat) (j : cell C n) :
    openCell n j subseteq skeletonLT C (n + 1) :=
  (openCell_subset_closedCell _ _).trans (closedCell_subset_skeletonLT _ _)

@[alias_in CWComplex]
/--
lemma `RelCWComplex.openCell_subset_skeleton` / 引理 `RelCWComplex.openCell_subset_skeleton`

English:
lemma RelCWComplex.openCell_subset_skeleton
  given: [RelCWComplex C D] (n : Nat) (j : cell C n)
  proof: (openCell_subset_closedCell _ _).trans (closedCell_subset_skeleton _ _)

@[alias_in CWComplex]

中文:
引理 RelCWComplex.openCell_subset_skeleton
  条件: [RelCWComplex C D] (n : 自然数) (j : cell C n)
  证明: (openCell_subset_closedCell _ _).trans (closedCell_subset_skeleton _ _)

@[alias_in CWComplex]

Depends on / 依赖: closedCell_subset_skeleton, openCell_subset_closedCell
-/
lemma RelCWComplex.openCell_subset_skeleton [RelCWComplex C D] (n : Nat) (j : cell C n) :
    openCell n j subseteq skeleton C n :=
  (openCell_subset_closedCell _ _).trans (closedCell_subset_skeleton _ _)

@[alias_in CWComplex]
/--
lemma `RelCWComplex.cellFrontier_subset_skeletonLT` / 引理 `RelCWComplex.cellFrontier_subset_skeletonLT`

English:
lemma RelCWComplex.cellFrontier_subset_skeletonLT
  given: [RelCWComplex C D] (n : Nat) (j : cell C n)
  proof: by
  obtain ⟨I, hI⟩ := cellFrontier_subset_base_union_finite_closedCell n j
  apply subset_trans hI
  rw [coe_skeletonLT]
  apply union_subset_union_right
  intro x xmem
  simp only [mem_iUnion, exists_prop] at xmem ⊢
  obtain ⟨i, iltn, j, _, xmem⟩ := xmem
  exact ⟨i, by norm_cast, j, xmem⟩

@[alias_in CWComplex]

中文:
引理 RelCWComplex.cellFrontier_subset_skeletonLT
  条件: [RelCWComplex C D] (n : 自然数) (j : cell C n)
  证明: by
  obtain ⟨I, hI⟩ := cellFrontier_subset_base_union_finite_closedCell n j
  apply subset_trans hI
  rw [coe_skeletonLT]
  apply union_subset_union_right
  intro x xmem
  simp only [mem_iUnion, exists_prop] at xmem ⊢
  obtain ⟨i, iltn, j, _, xmem⟩ := xmem
  exact ⟨i, by norm_cast, j, xmem⟩

@[alias_in CWComplex]

Depends on / 依赖: cellFrontier_subset_base_union_finite_closedCell, coe_skeletonLT, exists_prop, mem_iUnion, subset_trans, union_subset_union_right
-/
lemma RelCWComplex.cellFrontier_subset_skeletonLT [RelCWComplex C D] (n : Nat) (j : cell C n) :
    cellFrontier n j subseteq skeletonLT C n := by
  obtain ⟨I, hI⟩ := cellFrontier_subset_base_union_finite_closedCell n j
  apply subset_trans hI
  rw [coe_skeletonLT]
  apply union_subset_union_right
  intro x xmem
  simp only [mem_iUnion, exists_prop] at xmem ⊢
  obtain ⟨i, iltn, j, _, xmem⟩ := xmem
  exact ⟨i, by norm_cast, j, xmem⟩

@[alias_in CWComplex]
/--
lemma `RelCWComplex.cellFrontier_subset_skeleton` / 引理 `RelCWComplex.cellFrontier_subset_skeleton`

English:
lemma RelCWComplex.cellFrontier_subset_skeleton
  given: [RelCWComplex C D] (n : Nat) (j : cell C (n + 1))
  proof: cellFrontier_subset_skeletonLT _ _

@[alias_in CWComplex]

中文:
引理 RelCWComplex.cellFrontier_subset_skeleton
  条件: [RelCWComplex C D] (n : 自然数) (j : cell C (n + 1))
  证明: cellFrontier_subset_skeletonLT _ _

@[alias_in CWComplex]

Depends on / 依赖: cellFrontier_subset_skeletonLT
-/
lemma RelCWComplex.cellFrontier_subset_skeleton [RelCWComplex C D] (n : Nat) (j : cell C (n + 1)) :
    cellFrontier (n + 1) j subseteq skeleton C n :=
  cellFrontier_subset_skeletonLT _ _

@[alias_in CWComplex]
/--
lemma `RelCWComplex.iUnion_cellFrontier_subset_skeletonLT` / 引理 `RelCWComplex.iUnion_cellFrontier_subset_skeletonLT`

English:
lemma RelCWComplex.iUnion_cellFrontier_subset_skeletonLT
  given: [RelCWComplex C D] (l : Nat)
  proof: iUnion_subset (fun _ => cellFrontier_subset_skeletonLT _ _)

@[alias_in CWComplex]

中文:
引理 RelCWComplex.iUnion_cellFrontier_subset_skeletonLT
  条件: [RelCWComplex C D] (l : 自然数)
  证明: iUnion_subset (fun _ => cellFrontier_subset_skeletonLT _ _)

@[alias_in CWComplex]

Depends on / 依赖: cellFrontier_subset_skeletonLT, iUnion_subset
-/
lemma RelCWComplex.iUnion_cellFrontier_subset_skeletonLT [RelCWComplex C D] (l : Nat) :
    ⋃ (j : cell C l), cellFrontier l j subseteq skeletonLT C l :=
  iUnion_subset (fun _ => cellFrontier_subset_skeletonLT _ _)

@[alias_in CWComplex]
/--
lemma `RelCWComplex.iUnion_cellFrontier_subset_skeleton` / 引理 `RelCWComplex.iUnion_cellFrontier_subset_skeleton`

English:
lemma RelCWComplex.iUnion_cellFrontier_subset_skeleton
  given: [RelCWComplex C D] (l : Nat)
  proof: (iUnion_cellFrontier_subset_skeletonLT l).trans (skeletonLT_mono le_self_add)

@[alias_in CWComplex]

中文:
引理 RelCWComplex.iUnion_cellFrontier_subset_skeleton
  条件: [RelCWComplex C D] (l : 自然数)
  证明: (iUnion_cellFrontier_subset_skeletonLT l).trans (skeletonLT_mono le_self_add)

@[alias_in CWComplex]

Depends on / 依赖: iUnion_cellFrontier_subset_skeletonLT, le_self_add, skeletonLT_mono
-/
lemma RelCWComplex.iUnion_cellFrontier_subset_skeleton [RelCWComplex C D] (l : Nat) :
    ⋃ (j : cell C l), cellFrontier l j subseteq skeleton C l :=
  (iUnion_cellFrontier_subset_skeletonLT l).trans (skeletonLT_mono le_self_add)

@[alias_in CWComplex]
/--
lemma `RelCWComplex.skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ` / 引理 `RelCWComplex.skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ`

English:
lemma RelCWComplex.skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ
  statement: [RelCWComplex C D]
  proof: by
  rw [coe_skeletonLT]; rw [coe_skeletonLT]; rw [union_assoc]
  congr
  norm_cast
  exact (biUnion_lt_succ _ _).symm

@[alias_in CWComplex]

中文:
引理 RelCWComplex.skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ
  结论: [RelCWComplex C D]
  证明: by
  rw [coe_skeletonLT]; rw [coe_skeletonLT]; rw [union_assoc]
  congr
  norm_cast
  exact (biUnion_lt_succ _ _).symm

@[alias_in CWComplex]

Depends on / 依赖: biUnion_lt_succ, coe_skeletonLT, union_assoc
-/
lemma RelCWComplex.skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ [RelCWComplex C D]
    (n : Nat) :
    (skeletonLT C n : Set X) union ⋃ (j : cell C n), closedCell n j = skeletonLT C (n + 1) := by
  rw [coe_skeletonLT]; rw [coe_skeletonLT]; rw [union_assoc]
  congr
  norm_cast
  exact (biUnion_lt_succ _ _).symm

@[alias_in CWComplex]
/--
lemma `RelCWComplex.skeleton_union_iUnion_closedCell_eq_skeleton_succ` / 引理 `RelCWComplex.skeleton_union_iUnion_closedCell_eq_skeleton_succ`

English:
lemma RelCWComplex.skeleton_union_iUnion_closedCell_eq_skeleton_succ
  given: [RelCWComplex C D] (n : Nat)
  proof: skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ _

中文:
引理 RelCWComplex.skeleton_union_iUnion_closedCell_eq_skeleton_succ
  条件: [RelCWComplex C D] (n : 自然数)
  证明: skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ _

Depends on / 依赖: skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ
-/
lemma RelCWComplex.skeleton_union_iUnion_closedCell_eq_skeleton_succ [RelCWComplex C D] (n : Nat) :
    (skeleton C n : Set X) union ⋃ (j : cell C (n + 1)), closedCell (n + 1) j = skeleton C (n + 1) :=
  skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ _

/--
lemma `RelCWComplex.iUnion_openCell_eq_skeletonLT` / 引理 `RelCWComplex.iUnion_openCell_eq_skeletonLT`

English:
lemma RelCWComplex.iUnion_openCell_eq_skeletonLT
  given: [RelCWComplex C D] (n : Nat∞)
  proof: (coe_skeletonLT C _).symm ▸ RelCWComplex.iUnion_openCell_eq_iUnion_closedCell n

中文:
引理 RelCWComplex.iUnion_openCell_eq_skeletonLT
  条件: [RelCWComplex C D] (n : 自然数∞)
  证明: (coe_skeletonLT C _).symm ▸ RelCWComplex.iUnion_openCell_eq_iUnion_closedCell n

Depends on / 依赖: RelCWComplex, RelCWComplex.iUnion_openCell_eq_iUnion_closedCell, coe_skeletonLT, iUnion_openCell_eq_iUnion_closedCell
-/
lemma RelCWComplex.iUnion_openCell_eq_skeletonLT [RelCWComplex C D] (n : Nat∞) :
    D union ⋃ (m : Nat) (_ : m < n) (j : cell C m), openCell m j = skeletonLT C n :=
  (coe_skeletonLT C _).symm ▸ RelCWComplex.iUnion_openCell_eq_iUnion_closedCell n

/--
lemma `CWComplex.iUnion_openCell_eq_skeletonLT` / 引理 `CWComplex.iUnion_openCell_eq_skeletonLT`

English:
lemma CWComplex.iUnion_openCell_eq_skeletonLT
  given: [CWComplex C] (n : Nat∞)
  proof: by
  rw [← RelCWComplex.iUnion_openCell_eq_skeletonLT]; rw [empty_union]

中文:
引理 CWComplex.iUnion_openCell_eq_skeletonLT
  条件: [CWComplex C] (n : 自然数∞)
  证明: by
  rw [← RelCWComplex.iUnion_openCell_eq_skeletonLT]; rw [empty_union]

Depends on / 依赖: RelCWComplex, RelCWComplex.iUnion_openCell_eq_skeletonLT, empty_union, iUnion_openCell_eq_skeletonLT
-/
lemma CWComplex.iUnion_openCell_eq_skeletonLT [CWComplex C] (n : Nat∞) :
    ⋃ (m : Nat) (_ : m < n) (j : cell C m), openCell m j = skeletonLT C n := by
  rw [← RelCWComplex.iUnion_openCell_eq_skeletonLT]; rw [empty_union]

/--
lemma `RelCWComplex.iUnion_openCell_eq_skeleton` / 引理 `RelCWComplex.iUnion_openCell_eq_skeleton`

English:
lemma RelCWComplex.iUnion_openCell_eq_skeleton
  given: [RelCWComplex C D] (n : Nat∞)
  proof: iUnion_openCell_eq_skeletonLT _

中文:
引理 RelCWComplex.iUnion_openCell_eq_skeleton
  条件: [RelCWComplex C D] (n : 自然数∞)
  证明: iUnion_openCell_eq_skeletonLT _

Depends on / 依赖: iUnion_openCell_eq_skeletonLT
-/
lemma RelCWComplex.iUnion_openCell_eq_skeleton [RelCWComplex C D] (n : Nat∞) :
    D union ⋃ (m : Nat) (_ : m < n + 1) (j : cell C m), openCell m j = skeleton C n :=
  iUnion_openCell_eq_skeletonLT _

/--
lemma `CWComplex.iUnion_openCell_eq_skeleton` / 引理 `CWComplex.iUnion_openCell_eq_skeleton`

English:
lemma CWComplex.iUnion_openCell_eq_skeleton
  given: [CWComplex C] (n : Nat∞)
  proof: iUnion_openCell_eq_skeletonLT _

@[alias_in CWComplex]

中文:
引理 CWComplex.iUnion_openCell_eq_skeleton
  条件: [CWComplex C] (n : 自然数∞)
  证明: iUnion_openCell_eq_skeletonLT _

@[alias_in CWComplex]

Depends on / 依赖: iUnion_openCell_eq_skeletonLT
-/
lemma CWComplex.iUnion_openCell_eq_skeleton [CWComplex C] (n : Nat∞) :
    ⋃ (m : Nat) (_ : m < n + 1) (j : cell C m), openCell m j = skeleton C n :=
  iUnion_openCell_eq_skeletonLT _

@[alias_in CWComplex]
/--
lemma `RelCWComplex.iUnion_skeletonLT_eq_complex` / 引理 `RelCWComplex.iUnion_skeletonLT_eq_complex`

English:
lemma RelCWComplex.iUnion_skeletonLT_eq_complex
  given: [RelCWComplex C D]
  proof: by
  apply subset_antisymm (iUnion_subset_iff.2 fun _ => (skeletonLT C _).subset_complex)
  simp_rw [← union_iUnion_openCell_eq_complex, union_subset_iff, iUnion₂_subset_iff]
  exact ⟨subset_iUnion_of_subset 0 (skeletonLT C 0).base_subset,
    fun n i => subset_iUnion_of_subset _ (openCell_subset_skeletonLT n i)⟩

@[alias_in CWComplex]

中文:
引理 RelCWComplex.iUnion_skeletonLT_eq_complex
  条件: [RelCWComplex C D]
  证明: by
  apply subset_antisymm (iUnion_subset_iff.2 fun _ => (skeletonLT C _).subset_complex)
  simp_rw [← union_iUnion_openCell_eq_complex, union_subset_iff, iUnion₂_subset_iff]
  exact ⟨subset_iUnion_of_subset 0 (skeletonLT C 0).base_subset,
    fun n i => subset_iUnion_of_subset _ (openCell_subset_skeletonLT n i)⟩

@[alias_in CWComplex]

Depends on / 依赖: base_subset, iUnion_subset_iff, openCell_subset_skeletonLT, simp_rw, skeletonLT, subset_antisymm, subset_complex, subset_iUnion_of_subset, union_iUnion_openCell_eq_complex, union_subset_iff
-/
lemma RelCWComplex.iUnion_skeletonLT_eq_complex [RelCWComplex C D] :
    ⋃ (n : Nat), skeletonLT C n = C := by
  apply subset_antisymm (iUnion_subset_iff.2 fun _ => (skeletonLT C _).subset_complex)
  simp_rw [← union_iUnion_openCell_eq_complex, union_subset_iff, iUnion₂_subset_iff]
  exact ⟨subset_iUnion_of_subset 0 (skeletonLT C 0).base_subset,
    fun n i => subset_iUnion_of_subset _ (openCell_subset_skeletonLT n i)⟩

@[alias_in CWComplex]
/--
lemma `RelCWComplex.iUnion_skeleton_eq_complex` / 引理 `RelCWComplex.iUnion_skeleton_eq_complex`

English:
lemma RelCWComplex.iUnion_skeleton_eq_complex
  given: [RelCWComplex C D]
  proof: by
  apply subset_antisymm (iUnion_subset_iff.2 fun _ => (skeleton C _).subset_complex)
  simp_rw [← union_iUnion_openCell_eq_complex, union_subset_iff, iUnion₂_subset_iff]
  exact ⟨subset_iUnion_of_subset 0 (skeleton C 0).base_subset,
    fun n i => subset_iUnion_of_subset _ (openCell_subset_skeleton n i)⟩

中文:
引理 RelCWComplex.iUnion_skeleton_eq_complex
  条件: [RelCWComplex C D]
  证明: by
  apply subset_antisymm (iUnion_subset_iff.2 fun _ => (skeleton C _).subset_complex)
  simp_rw [← union_iUnion_openCell_eq_complex, union_subset_iff, iUnion₂_subset_iff]
  exact ⟨subset_iUnion_of_subset 0 (skeleton C 0).base_subset,
    fun n i => subset_iUnion_of_subset _ (openCell_subset_skeleton n i)⟩

Depends on / 依赖: base_subset, iUnion_subset_iff, openCell_subset_skeleton, simp_rw, skeleton, subset_antisymm, subset_complex, subset_iUnion_of_subset, union_iUnion_openCell_eq_complex, union_subset_iff
-/
lemma RelCWComplex.iUnion_skeleton_eq_complex [RelCWComplex C D] :
    ⋃ (n : Nat), skeleton C n = C := by
  apply subset_antisymm (iUnion_subset_iff.2 fun _ => (skeleton C _).subset_complex)
  simp_rw [← union_iUnion_openCell_eq_complex, union_subset_iff, iUnion₂_subset_iff]
  exact ⟨subset_iUnion_of_subset 0 (skeleton C 0).base_subset,
    fun n i => subset_iUnion_of_subset _ (openCell_subset_skeleton n i)⟩

/--
lemma `RelCWComplex.mem_skeletonLT_iff` / 引理 `RelCWComplex.mem_skeletonLT_iff`

English:
lemma RelCWComplex.mem_skeletonLT_iff
  given: [RelCWComplex C D] {n : Nat∞} {x : X}
  proof: by
  simp [← SetLike.mem_coe, ← iUnion_openCell_eq_skeletonLT]

中文:
引理 RelCWComplex.mem_skeletonLT_iff
  条件: [RelCWComplex C D] {n : 自然数∞} {x : X}
  证明: by
  simp [← SetLike.mem_coe, ← iUnion_openCell_eq_skeletonLT]

Depends on / 依赖: SetLike, SetLike.mem_coe, iUnion_openCell_eq_skeletonLT, mem_coe
-/
lemma RelCWComplex.mem_skeletonLT_iff [RelCWComplex C D] {n : Nat∞} {x : X} :
    x in skeletonLT C n ↔ x in D ∨ exists (m : Nat) (_ : m < n) (j : cell C m), x in openCell m j := by
  simp [← SetLike.mem_coe, ← iUnion_openCell_eq_skeletonLT]

/--
lemma `CWComplex.mem_skeletonLT_iff` / 引理 `CWComplex.mem_skeletonLT_iff`

English:
lemma CWComplex.mem_skeletonLT_iff
  given: [CWComplex C] {n : Nat∞} {x : X}
  proof: by
  simp [← SetLike.mem_coe, ← iUnion_openCell_eq_skeletonLT]

中文:
引理 CWComplex.mem_skeletonLT_iff
  条件: [CWComplex C] {n : 自然数∞} {x : X}
  证明: by
  simp [← SetLike.mem_coe, ← iUnion_openCell_eq_skeletonLT]

Depends on / 依赖: SetLike, SetLike.mem_coe, iUnion_openCell_eq_skeletonLT, mem_coe
-/
lemma CWComplex.mem_skeletonLT_iff [CWComplex C] {n : Nat∞} {x : X} :
    x in skeletonLT C n ↔ exists (m : Nat) (_ : m < n) (j : cell C m), x in openCell m j := by
  simp [← SetLike.mem_coe, ← iUnion_openCell_eq_skeletonLT]

/--
lemma `RelCWComplex.mem_skeleton_iff` / 引理 `RelCWComplex.mem_skeleton_iff`

English:
lemma RelCWComplex.mem_skeleton_iff
  given: [RelCWComplex C D] {n : Nat∞} {x : X}
  proof: by
  rw [skeleton]; rw [mem_skeletonLT_iff]
  suffices forall (m : Nat), m < n + 1 ↔ m <= n by simp_rw [this]
  intro m
  cases n
  · simp
  · rw [← Nat.cast_one, ← Nat.cast_add, Nat.cast_lt, Nat.cast_le, Order.lt_add_one_iff]

中文:
引理 RelCWComplex.mem_skeleton_iff
  条件: [RelCWComplex C D] {n : 自然数∞} {x : X}
  证明: by
  rw [skeleton]; rw [mem_skeletonLT_iff]
  suffices forall (m : Nat), m < n + 1 ↔ m <= n by simp_rw [this]
  intro m
  cases n
  · simp
  · rw [← Nat.cast_one, ← Nat.cast_add, Nat.cast_lt, Nat.cast_le, Order.lt_add_one_iff]

Depends on / 依赖: Nat.cast_add, Nat.cast_le, Nat.cast_lt, Nat.cast_one, Order.lt_add_one_iff, cast_add, cast_le, cast_lt, cast_one, lt_add_one_iff, mem_skeletonLT_iff, simp_rw, skeleton
-/
lemma RelCWComplex.mem_skeleton_iff [RelCWComplex C D] {n : Nat∞} {x : X} :
    x in skeleton C n ↔ x in D ∨ exists (m : Nat) (_ : m <= n) (j : cell C m), x in openCell m j := by
  rw [skeleton]; rw [mem_skeletonLT_iff]
  suffices forall (m : Nat), m < n + 1 ↔ m <= n by simp_rw [this]
  intro m
  cases n
  · simp
  · rw [← Nat.cast_one, ← Nat.cast_add, Nat.cast_lt, Nat.cast_le, Order.lt_add_one_iff]

/--
lemma `CWComplex.mem_skeleton_iff` / 引理 `CWComplex.mem_skeleton_iff`

English:
lemma CWComplex.mem_skeleton_iff
  given: [CWComplex C] {n : Nat∞} {x : X}
  proof: by
  rw [RelCWComplex.mem_skeleton_iff]; rw [mem_empty_iff_false]; rw [false_or]

@[deprecated (since := "2026-04-30")] alias CWComplex.exists_mem_openCell_of_mem_skeleton :=
  CWComplex.mem_skeleton_iff

中文:
引理 CWComplex.mem_skeleton_iff
  条件: [CWComplex C] {n : 自然数∞} {x : X}
  证明: by
  rw [RelCWComplex.mem_skeleton_iff]; rw [mem_empty_iff_false]; rw [false_or]

@[deprecated (since := "2026-04-30")] alias CWComplex.exists_mem_openCell_of_mem_skeleton :=
  CWComplex.mem_skeleton_iff

Depends on / 依赖: RelCWComplex, RelCWComplex.mem_skeleton_iff, false_or, mem_empty_iff_false, mem_skeleton_iff
-/
lemma CWComplex.mem_skeleton_iff [CWComplex C] {n : Nat∞} {x : X} :
    x in skeleton C n ↔ exists (m : Nat) (_ : m <= n) (j : cell C m), x in openCell m j := by
  rw [RelCWComplex.mem_skeleton_iff]; rw [mem_empty_iff_false]; rw [false_or]

@[deprecated (since := "2026-04-30")] alias CWComplex.exists_mem_openCell_of_mem_skeleton :=
  CWComplex.mem_skeleton_iff

/-- A skeleton and an open cell of a higher dimension are disjoint. -/
@[alias_in CWComplex]
/--
lemma `RelCWComplex.disjoint_skeletonLT_openCell` / 引理 `RelCWComplex.disjoint_skeletonLT_openCell`

English:
lemma RelCWComplex.disjoint_skeletonLT_openCell
  statement: [RelCWComplex C D] {n : Nat∞} {m : Nat}
  proof: by
  -- This is a consequence of `iUnion_openCell_eq_skeletonLT` and `disjoint_openCell_of_ne`
  simp_rw [← iUnion_openCell_eq_skeletonLT, disjoint_union_left, disjoint_iUnion_left]
  refine ⟨(disjointBase m j).symm, ?_⟩
  intro l hln i
  apply disjoint_openCell_of_ne
  intro
  simp_all only [Sigma.mk.inj_iff]
  exact (lt_self_iff_false m).mp (ENat.natCast_lt_natCast.1 (hln.trans_le hnm))

中文:
引理 RelCWComplex.disjoint_skeletonLT_openCell
  结论: [RelCWComplex C D] {n : 自然数∞} {m : 自然数}
  证明: by
  -- This is a consequence of `iUnion_openCell_eq_skeletonLT` and `disjoint_openCell_of_ne`
  simp_rw [← iUnion_openCell_eq_skeletonLT, disjoint_union_left, disjoint_iUnion_left]
  refine ⟨(disjointBase m j).symm, ?_⟩
  intro l hln i
  apply disjoint_openCell_of_ne
  intro
  simp_all only [Sigma.mk.inj_iff]
  exact (lt_self_iff_false m).mp (ENat.natCast_lt_natCast.1 (hln.trans_le hnm))
-/
lemma RelCWComplex.disjoint_skeletonLT_openCell [RelCWComplex C D] {n : Nat∞} {m : Nat}
    {j : cell C m} (hnm : n <= m) : Disjoint (skeletonLT C n : Set X) (openCell m j) := by
  -- This is a consequence of `iUnion_openCell_eq_skeletonLT` and `disjoint_openCell_of_ne`
  simp_rw [← iUnion_openCell_eq_skeletonLT, disjoint_union_left, disjoint_iUnion_left]
  refine ⟨(disjointBase m j).symm, ?_⟩
  intro l hln i
  apply disjoint_openCell_of_ne
  intro
  simp_all only [Sigma.mk.inj_iff]
  exact (lt_self_iff_false m).mp (ENat.natCast_lt_natCast.1 (hln.trans_le hnm))

/-- A skeleton and an open cell of a higher dimension are disjoint. -/
@[alias_in CWComplex]
/--
lemma `RelCWComplex.disjoint_skeleton_openCell` / 引理 `RelCWComplex.disjoint_skeleton_openCell`

English:
lemma RelCWComplex.disjoint_skeleton_openCell
  statement: [RelCWComplex C D] {n : Nat∞} {m : Nat}
  proof: disjoint_skeletonLT_openCell (Order.add_one_le_of_lt nlem)

中文:
引理 RelCWComplex.disjoint_skeleton_openCell
  结论: [RelCWComplex C D] {n : 自然数∞} {m : 自然数}
  证明: disjoint_skeletonLT_openCell (Order.add_one_le_of_lt nlem)

Depends on / 依赖: Order.add_one_le_of_lt, add_one_le_of_lt, disjoint_skeletonLT_openCell
-/
lemma RelCWComplex.disjoint_skeleton_openCell [RelCWComplex C D] {n : Nat∞} {m : Nat}
    {j : cell C m} (nlem : n < m) : Disjoint (skeleton C n : Set X) (openCell m j) :=
  disjoint_skeletonLT_openCell (Order.add_one_le_of_lt nlem)

/-- A skeleton intersected with a closed cell of a higher dimension is the skeleton intersected with
the boundary of the cell. -/
@[alias_in CWComplex]
/--
lemma `RelCWComplex.skeletonLT_inter_closedCell_eq_skeletonLT_inter_cellFrontier` / 引理 `RelCWComplex.skeletonLT_inter_closedCell_eq_skeletonLT_inter_cellFrontier`

English:
lemma RelCWComplex.skeletonLT_inter_closedCell_eq_skeletonLT_inter_cellFrontier
  statement: [RelCWComplex C D]
  proof: by
  refine subset_antisymm ?_ (inter_subset_inter_right _ (cellFrontier_subset_closedCell _ _))
  rw [← cellFrontier_union_openCell_eq_closedCell]; rw [inter_union_distrib_left]
  apply union_subset (by rfl)
  rw [(disjoint_skeletonLT_openCell hnm).inter_eq]
  exact empty_subset _

中文:
引理 RelCWComplex.skeletonLT_inter_closedCell_eq_skeletonLT_inter_cellFrontier
  结论: [RelCWComplex C D]
  证明: by
  refine subset_antisymm ?_ (inter_subset_inter_right _ (cellFrontier_subset_closedCell _ _))
  rw [← cellFrontier_union_openCell_eq_closedCell]; rw [inter_union_distrib_left]
  apply union_subset (by rfl)
  rw [(disjoint_skeletonLT_openCell hnm).inter_eq]
  exact empty_subset _

Depends on / 依赖: cellFrontier_subset_closedCell, cellFrontier_union_openCell_eq_closedCell, disjoint_skeletonLT_openCell, empty_subset, inter_eq, inter_subset_inter_right, inter_union_distrib_left, subset_antisymm, union_subset
-/
lemma RelCWComplex.skeletonLT_inter_closedCell_eq_skeletonLT_inter_cellFrontier [RelCWComplex C D]
    {n : Nat∞} {m : Nat} {j : cell C m} (hnm : n <= m) :
    (skeletonLT C n : Set X) inter closedCell m j = (skeletonLT C n : Set X) inter cellFrontier m j := by
  refine subset_antisymm ?_ (inter_subset_inter_right _ (cellFrontier_subset_closedCell _ _))
  rw [← cellFrontier_union_openCell_eq_closedCell]; rw [inter_union_distrib_left]
  apply union_subset (by rfl)
  rw [(disjoint_skeletonLT_openCell hnm).inter_eq]
  exact empty_subset _

/-- Version of `skeletonLT_inter_closedCell_eq_skeletonLT_inter_cellFrontier` using `skeleton`. -/
@[alias_in CWComplex]
/--
lemma `RelCWComplex.skeleton_inter_closedCell_eq_skeleton_inter_cellFrontier` / 引理 `RelCWComplex.skeleton_inter_closedCell_eq_skeleton_inter_cellFrontier`

English:
lemma RelCWComplex.skeleton_inter_closedCell_eq_skeleton_inter_cellFrontier
  statement: [RelCWComplex C D]
  proof: skeletonLT_inter_closedCell_eq_skeletonLT_inter_cellFrontier (Order.add_one_le_of_lt hnm)

中文:
引理 RelCWComplex.skeleton_inter_closedCell_eq_skeleton_inter_cellFrontier
  结论: [RelCWComplex C D]
  证明: skeletonLT_inter_closedCell_eq_skeletonLT_inter_cellFrontier (Order.add_one_le_of_lt hnm)

Depends on / 依赖: Order.add_one_le_of_lt, add_one_le_of_lt, skeletonLT_inter_closedCell_eq_skeletonLT_inter_cellFrontier
-/
lemma RelCWComplex.skeleton_inter_closedCell_eq_skeleton_inter_cellFrontier [RelCWComplex C D]
    {n : Nat∞} {m : Nat} {j : cell C m} (hnm : n < m) :
    (skeleton C n : Set X) inter closedCell m j = (skeleton C n : Set X) inter cellFrontier m j :=
  skeletonLT_inter_closedCell_eq_skeletonLT_inter_cellFrontier (Order.add_one_le_of_lt hnm)

end skeleton

/--
lemma `RelCWComplex.disjoint_interior_base_closedCell` / 引理 `RelCWComplex.disjoint_interior_base_closedCell`

English:
lemma RelCWComplex.disjoint_interior_base_closedCell
  statement: [T2Space X] [RelCWComplex C D] {n : Nat}
  proof: by
  rw [disjoint_iff_inter_eq_empty]
  by_contra! h
  rw [← closure_openCell_eq_closedCell]; rw [inter_comm]; rw [closure_inter_open_nonempty_iff isOpen_interior] at h
  rcases h with ⟨x, xmemcell, xmemD⟩
  suffices x in (skeletonLT C 0 : Set X) inter openCell n j by
    rwa [(disjoint_skeletonLT_openCell n.cast_nonneg').inter_eq] at this
  exact ⟨(skeletonLT C 0).base_subset (interior_subset xmemD), xmemcell⟩

中文:
引理 RelCWComplex.disjoint_interior_base_closedCell
  结论: [T2空间 X] [RelCWComplex C D] {n : 自然数}
  证明: by
  rw [disjoint_iff_inter_eq_empty]
  by_contra! h
  rw [← closure_openCell_eq_closedCell]; rw [inter_comm]; rw [closure_inter_open_nonempty_iff isOpen_interior] at h
  rcases h with ⟨x, xmemcell, xmemD⟩
  suffices x in (skeletonLT C 0 : Set X) inter openCell n j by
    rwa [(disjoint_skeletonLT_openCell n.cast_nonneg').inter_eq] at this
  exact ⟨(skeletonLT C 0).base_subset (interior_subset xmemD), xmemcell⟩

Depends on / 依赖: base_subset, cast_nonneg, closure_inter_open_nonempty_iff, closure_openCell_eq_closedCell, disjoint_iff_inter_eq_empty, disjoint_skeletonLT_openCell, inter_comm, inter_eq, interior_subset, isOpen_interior, n.cast_nonneg, openCell, skeletonLT, xmemcell
-/
lemma RelCWComplex.disjoint_interior_base_closedCell [T2Space X] [RelCWComplex C D] {n : Nat}
    {j : cell C n} : Disjoint (interior D) (closedCell n j) := by
  rw [disjoint_iff_inter_eq_empty]
  by_contra! h
  rw [← closure_openCell_eq_closedCell]; rw [inter_comm]; rw [closure_inter_open_nonempty_iff isOpen_interior] at h
  rcases h with ⟨x, xmemcell, xmemD⟩
  suffices x in (skeletonLT C 0 : Set X) inter openCell n j by
    rwa [(disjoint_skeletonLT_openCell n.cast_nonneg').inter_eq] at this
  exact ⟨(skeletonLT C 0).base_subset (interior_subset xmemD), xmemcell⟩

/--
lemma `RelCWComplex.disjoint_interior_base_iUnion_closedCell` / 引理 `RelCWComplex.disjoint_interior_base_iUnion_closedCell`

English:
lemma RelCWComplex.disjoint_interior_base_iUnion_closedCell
  given: [T2Space X] [RelCWComplex C D]
  proof: by
  simp_rw [disjoint_iff_inter_eq_empty, inter_iUnion, disjoint_interior_base_closedCell.inter_eq,
    iUnion_empty]

中文:
引理 RelCWComplex.disjoint_interior_base_iUnion_closedCell
  条件: [T2空间 X] [RelCWComplex C D]
  证明: by
  simp_rw [disjoint_iff_inter_eq_empty, inter_iUnion, disjoint_interior_base_closedCell.inter_eq,
    iUnion_empty]

Depends on / 依赖: disjoint_iff_inter_eq_empty, disjoint_interior_base_closedCell, disjoint_interior_base_closedCell.inter_eq, iUnion_empty, inter_eq, inter_iUnion, simp_rw
-/
lemma RelCWComplex.disjoint_interior_base_iUnion_closedCell [T2Space X] [RelCWComplex C D] :
    Disjoint (interior D) (⋃ (n : Nat) (j : cell C n), closedCell n j) := by
  simp_rw [disjoint_iff_inter_eq_empty, inter_iUnion, disjoint_interior_base_closedCell.inter_eq,
    iUnion_empty]

set_option backward.isDefEq.respectTransparency.types false in
/-- A closed discrete subset of a space is a CW complex. -/
@[reducible, simps -isSimp]
/--
Definition of `CWComplex.OfDiscreteClosed` / `CWComplex.OfDiscreteClosed` 的定义

English:
definition CWComplex.OfDiscreteClosed
  signature: (hD : IsDiscrete D) (Dc : IsClosed D)
  body: match n with
    | 0 => D
    | (_ + 1) => PEmpty
  map n i := match n with
    | 0 => PartialEquiv.single ![] i
    | (_ + 1) => i.elim
  source_eq n i := match n with
    | 0 => by simp [ball, Matrix.empty_eq, eq_univ_iff_forall]
    | (_ + 1) => i.elim
  continuousOn n i := match n with
    | 0 => continuousOn_const
    | (_ + 1) => i.elim
  continuousOn_symm n i := match n with
    | 0 => continuousOn_const
    | (_ + 1) => i.elim
  pairwiseDisjoint' := by
    simp_rw [PairwiseDisjoint, Set.Pairwise, Function.onFun]
    rintro ⟨_|n, j⟩ _ ⟨_|m, i⟩ _ ne
    · simp_all [Subtype.coe_injective.ne]
    · exact i.elim
    · tauto
    · exact i.elim
  mapsTo' n i := match n with
    | 0 => by simp [Matrix.zero_empty, sphere_eq_empty_of_subsingleton]
    | (_ + 1) => i.elim
  closed' A AD _ := isClosed_of_subset_discrete_closed AD hD Dc
  union' := by
    apply subset_antisymm (iUnion₂_subset_iff.mpr fun n => by cases n <;> simp)
    intro x xD
    simp only [mem_iUnion, mem_image, mem_closedBall, dist_zero_right]
    refine ⟨0, ?_⟩
    simpa [-Matrix.zero_empty]

中文:
定义 CWComplex.OfDiscreteClosed
  签名: (hD : 是离散 D) (Dc : 是闭集 D)
  定义体: match n with
    | 0 => D
    | (_ + 1) => PEmpty
  map n i := match n with
    | 0 => PartialEquiv.single ![] i
    | (_ + 1) => i.elim
  source_eq n i := match n with
    | 0 => by simp [ball, Matrix.empty_eq, eq_univ_iff_forall]
    | (_ + 1) => i.elim
  continuousOn n i := match n with
    | 0 => continuousOn_const
    | (_ + 1) => i.elim
  continuousOn_symm n i := match n with
    | 0 => continuousOn_const
    | (_ + 1) => i.elim
  pairwiseDisjoint' := by
    simp_rw [PairwiseDisjoint, Set.Pairwise, Function.onFun]
    rintro ⟨_|n, j⟩ _ ⟨_|m, i⟩ _ ne
    · simp_all [Subtype.coe_injective.ne]
    · exact i.elim
    · tauto
    · exact i.elim
  mapsTo' n i := match n with
    | 0 => by simp [Matrix.zero_empty, sphere_eq_empty_of_subsingleton]
    | (_ + 1) => i.elim
  closed' A AD _ := isClosed_of_subset_discrete_closed AD hD Dc
  union' := by
    apply subset_antisymm (iUnion₂_subset_iff.mpr fun n => by cases n <;> simp)
    intro x xD
    simp only [mem_iUnion, mem_image, mem_closedBall, dist_zero_right]
    refine ⟨0, ?_⟩
    simpa [-Matrix.zero_empty]
-/
def CWComplex.OfDiscreteClosed (hD : IsDiscrete D) (Dc : IsClosed D) : CWComplex D where
  cell n := match n with
    | 0 => D
    | (_ + 1) => PEmpty
  map n i := match n with
    | 0 => PartialEquiv.single ![] i
    | (_ + 1) => i.elim
  source_eq n i := match n with
    | 0 => by simp [ball, Matrix.empty_eq, eq_univ_iff_forall]
    | (_ + 1) => i.elim
  continuousOn n i := match n with
    | 0 => continuousOn_const
    | (_ + 1) => i.elim
  continuousOn_symm n i := match n with
    | 0 => continuousOn_const
    | (_ + 1) => i.elim
  pairwiseDisjoint' := by
    simp_rw [PairwiseDisjoint, Set.Pairwise, Function.onFun]
    rintro ⟨_|n, j⟩ _ ⟨_|m, i⟩ _ ne
    · simp_all [Subtype.coe_injective.ne]
    · exact i.elim
    · tauto
    · exact i.elim
  mapsTo' n i := match n with
    | 0 => by simp [Matrix.zero_empty, sphere_eq_empty_of_subsingleton]
    | (_ + 1) => i.elim
  closed' A AD _ := isClosed_of_subset_discrete_closed AD hD Dc
  union' := by
    apply subset_antisymm (iUnion₂_subset_iff.mpr fun n => by cases n <;> simp)
    intro x xD
    simp only [mem_iUnion, mem_image, mem_closedBall, dist_zero_right]
    refine ⟨0, ?_⟩
    simpa [-Matrix.zero_empty]

/--
Instance `CWComplex.ofDiscreteTopology` / 实例 `CWComplex.ofDiscreteTopology`

English:
instance CWComplex.ofDiscreteTopology
  signature: {X : Type*} [TopologicalSpace X] [DiscreteTopology X]
  body: CWComplex.OfDiscreteClosed IsDiscrete.univ isClosed_univ

中文:
实例 CWComplex.ofDiscreteTopology
  签名: {X : 类型} [拓扑空间 X] [离散拓扑 X]
  定义体: CWComplex.OfDiscreteClosed IsDiscrete.univ isClosed_univ

Depends on / 依赖: CWComplex, CWComplex.OfDiscreteClosed, IsDiscrete, IsDiscrete.univ, OfDiscreteClosed, isClosed_univ
-/
instance CWComplex.ofDiscreteTopology {X : Type*} [TopologicalSpace X] [DiscreteTopology X] :
    CWComplex (univ : Set X) :=
  CWComplex.OfDiscreteClosed IsDiscrete.univ isClosed_univ

end Topology
