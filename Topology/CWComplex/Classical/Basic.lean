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
  CW complexes to be  as convenient as possible. Thus every declaration about relative CW complexes
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

/-- A CW complex of a topological space `X` relative to another subspace `D` is the data of its
*`n`-cells* `cell n i` for each `n : ℕ` along with *attaching maps* that satisfy a number of
properties with the most important being closure-finiteness (`mapsTo`) and weak topology
(`closed'`). Note that this definition requires `C` and `D` to be closed subspaces.
If `C` is not closed choose `X` to be `C`. -/
/-
**Topology.RelCWComplex.** 是 Mathlib 中的一个类，位于命名空间 `Topology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A CW complex of a topological space `X` relative to another subspace `D` is the 
data of its
*`n`-cells* `cell n i` for each `n : ℕ` along with *attaching maps* that satisfy
 a number of
properties with the most important being closure-finiteness (`mapsTo`) and weak 
topology
(`closed'`). Note that this definition requires `C` and `D` to be closed subspac
es.
If `C` is not closed choose `X` to be `C`.
-/
class RelCWComplex.{u} {X : Type u} [TopologicalSpace X] (C : Set X) (D : outParam (Set X)) where
  /-- The indexing type of the cells of dimension `n`. -/
  cell (n : ℕ) : Type u
  /-- The characteristic map of the `n`-cell given by the index `i`.
  This map is a bijection when restricting to `ball 0 1`, where we consider `(Fin n → ℝ)`
  endowed with the maximum metric. -/
  map (n : ℕ) (i : cell n) : PartialEquiv (Fin n → ℝ) X
  /-- The source of every characteristic map of dimension `n` is
  `(ball 0 1 : Set (Fin n → ℝ))`. -/
  source_eq (n : ℕ) (i : cell n) : (map n i).source = ball 0 1
  /-- The characteristic maps are continuous when restricting to `closedBall 0 1`. -/
  continuousOn (n : ℕ) (i : cell n) : ContinuousOn (map n i) (closedBall 0 1)
  /-- The inverse of the restriction to `ball 0 1` is continuous on the image. -/
  continuousOn_symm (n : ℕ) (i : cell n) : ContinuousOn (map n i).symm (map n i).target
  /-- The open cells are pairwise disjoint. Use `RelCWComplex.pairwiseDisjoint` or
  `RelCWComplex.disjoint_openCell_of_ne` instead. -/
  pairwiseDisjoint' :
    (univ : Set (Σ n, cell n)).PairwiseDisjoint (fun ni ↦ map ni.1 ni.2 '' ball 0 1)
  /-- All open cells are disjoint with the base. Use `RelCWComplex.disjointBase` instead. -/
  disjointBase' (n : ℕ) (i : cell n) : Disjoint (map n i '' ball 0 1) D
  /-- The boundary of a cell is contained in the union of the base with a finite union of closed
  cells of a lower dimension. Use `RelCWComplex.cellFrontier_subset_base_union_finite_closedCell`
  instead. -/
  mapsTo (n : ℕ) (i : cell n) : ∃ I : Π m, Finset (cell m),
    MapsTo (map n i) (sphere 0 1) (D ∪ ⋃ (m < n) (j ∈ I m), map m j '' closedBall 0 1)
  /-- A CW complex has weak topology, i.e. a set `A` in `X` is closed iff its intersection with
  every closed cell and `D` is closed. Use `RelCWComplex.closed` instead. -/
  closed' (A : Set X) (hAC : A ⊆ C) :
    ((∀ n j, IsClosed (A ∩ map n j '' closedBall 0 1)) ∧ IsClosed (A ∩ D)) → IsClosed A
  /-- The base `D` is closed. -/
  isClosedBase : IsClosed D
  /-- The union of all closed cells equals `C`. Use `RelCWComplex.union` instead. -/
  union' : D ∪ ⋃ (n : ℕ) (j : cell n), map n j '' closedBall 0 1 = C

/-- Characterizing when a subspace `C` of a topological space `X` is a CW complex. Note that this
requires `C` to be closed. If `C` is not closed choose `X` to be `C`. -/
/-
**Topology.CWComplex.** 是 Mathlib 中的一个类，位于命名空间 `Topology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Characterizing when a subspace `C` of a topological space `X` is a CW complex. N
ote that this
requires `C` to be closed. If `C` is not closed choose `X` to be `C`.
-/
class CWComplex.{u} {X : Type u} [TopologicalSpace X] (C : Set X) where
  /-- The indexing type of the cells of dimension `n`. -/
  protected cell (n : ℕ) : Type u
  /-- The characteristic map of the `n`-cell given by the index `i`.
  This map is a bijection when restricting to `ball 0 1`, where we consider `(Fin n → ℝ)`
  endowed with the maximum metric. -/
  protected map (n : ℕ) (i : cell n) : PartialEquiv (Fin n → ℝ) X
  /-- The source of every characteristic map of dimension `n` is
  `(ball 0 1 : Set (Fin n → ℝ))`. -/
  protected source_eq (n : ℕ) (i : cell n) : (map n i).source = ball 0 1
  /-- The characteristic maps are continuous when restricting to `closedBall 0 1`. -/
  protected continuousOn (n : ℕ) (i : cell n) : ContinuousOn (map n i) (closedBall 0 1)
  /-- The inverse of the restriction to `ball 0 1` is continuous on the image. -/
  protected continuousOn_symm (n : ℕ) (i : cell n) : ContinuousOn (map n i).symm (map n i).target
  /-- The open cells are pairwise disjoint. Use `CWComplex.pairwiseDisjoint` or
  `CWComplex.disjoint_openCell_of_ne` instead. -/
  protected pairwiseDisjoint' :
    (univ : Set (Σ n, cell n)).PairwiseDisjoint (fun ni ↦ map ni.1 ni.2 '' ball 0 1)
  /-- The boundary of a cell is contained in a finite union of closed cells of a lower dimension.
  Use `CWComplex.mapsTo` or `CWComplex.cellFrontier_subset_finite_closedCell` instead. -/
  protected mapsTo' (n : ℕ) (i : cell n) : ∃ I : Π m, Finset (cell m),
    MapsTo (map n i) (sphere 0 1) (⋃ (m < n) (j ∈ I m), map m j '' closedBall 0 1)
  /-- A CW complex has weak topology, i.e. a set `A` in `X` is closed iff its intersection with
  every closed cell is closed. Use `CWComplex.closed` instead. -/
  protected closed' (A : Set X) (hAC : A ⊆ C) :
    (∀ n j, IsClosed (A ∩ map n j '' closedBall 0 1)) → IsClosed A
  /-- The union of all closed cells equals `C`. Use `CWComplex.union` instead. -/
  protected union' : ⋃ (n : ℕ) (j : cell n), map n j '' closedBall 0 1 = C

@[simps -isSimp]
/-
**Topology.** 是 Mathlib 中的一个实例，位于命名空间 `Topology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
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
/-
**Topology.RelCWComplex.toCWComplex** 是 Mathlib 中的一个定义，位于命名空间 `Topology.RelCWCom
plex`。
形式化陈述：{X : Type u_1} → [inst : TopologicalSpace X] → (C : Set X) → [Topology.Rel
CWComplex C ∅] → Topology.CWComplex C
参数：C : Set X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A relative CW complex with an empty base is an absolute CW complex.
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
/-
**Topology.RelCWComplex.toCWComplex_eq** 是 Mathlib 中的一个定理，位于命名空间 `Topology.RelCW
Complex`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] (C : Set X) [h : Topology.Rel
CWComplex C ∅],   Topology.CWComplex.instRelCWComplex C = h
参数：C : Set X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma RelCWComplex.toCWComplex_eq {X : Type*} [TopologicalSpace X] (C : Set X)
    [h : RelCWComplex C ∅] : (toCWComplex C).instRelCWComplex = h :=
  rfl

variable {X : Type*} [t : TopologicalSpace X] {C D : Set X}

/-- The open `n`-cell given by the index `i`. Use this instead of `map n i '' ball 0 1` whenever
possible. -/
/-
**Topology.RelCWComplex.openCell** 是 Mathlib 中的一个定义，位于命名空间 `Topology.RelCWComple
x`。
形式化陈述：{X : Type u_1} →   [t : TopologicalSpace X] →     {C D : Set X} → [inst : 
Topology.RelCWComplex C D] → (n : ℕ) → Topology.RelCWComplex.cell C n → Set X
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The open `n`-cell given by the index `i`. Use this instead of `map n i '' ball 0
 1` whenever
possible.
-/
def RelCWComplex.openCell [RelCWComplex C D] (n : ℕ) (i : cell C n) : Set X := map n i '' ball 0 1

/-- The closed `n`-cell given by the index `i`. Use this instead of `map n i '' closedBall 0 1`
whenever possible. -/
/-
**Topology.RelCWComplex.closedCell** 是 Mathlib 中的一个定义，位于命名空间 `Topology.RelCWComp
lex`。
形式化陈述：{X : Type u_1} →   [t : TopologicalSpace X] →     {C D : Set X} → [inst : 
Topology.RelCWComplex C D] → (n : ℕ) → Topology.RelCWComplex.cell C n → Set X
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The closed `n`-cell given by the index `i`. Use this instead of `map n i '' clos
edBall 0 1`
whenever possible.
-/
def RelCWComplex.closedCell [RelCWComplex C D] (n : ℕ) (i : cell C n) : Set X :=
  map n i '' closedBall 0 1

/-- The boundary of the `n`-cell given by the index `i`. Use this instead of `map n i '' sphere 0 1`
whenever possible. -/
/-
**Topology.RelCWComplex.cellFrontier** 是 Mathlib 中的一个定义，位于命名空间 `Topology.RelCWCo
mplex`。
形式化陈述：{X : Type u_1} →   [t : TopologicalSpace X] →     {C D : Set X} → [inst : 
Topology.RelCWComplex C D] → (n : ℕ) → Topology.RelCWComplex.cell C n → Set X
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The boundary of the `n`-cell given by the index `i`. Use this instead of `map n 
i '' sphere 0 1`
whenever possible.
-/
def RelCWComplex.cellFrontier [RelCWComplex C D] (n : ℕ) (i : cell C n) : Set X :=
  map n i '' sphere 0 1

namespace CWComplex

export RelCWComplex (cell map source_eq continuousOn continuousOn_symm isClosedBase openCell
  closedCell cellFrontier)

end CWComplex

/-
**Topology.CWComplex.mapsTo** 是 Mathlib 中的一个定理，位于命名空间 `Topology.CWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C : Set X} [inst : Topology.CWC
omplex C] (n : ℕ)   (i : Topology.RelCWComplex.cell C n),   ∃ I,     Set.MapsTo 
(↑(Topology.RelCWComplex.map n i)) (Metric.sphere 0 1)       (⋃ m, ⋃ (_ : m < n)
, ⋃ j ∈ I m, ↑(Topology.RelCWComplex.map m j) '' Metric.closedBall 0 1)
参数：n : ℕ；i : Topology.RelCWComplex.cell C n；↑(Topology.RelCWComplex.map n i)；Met
ric.sphere 0 1；⋃ m, ⋃ (_ : m < n), ⋃ j ∈ I m, ↑(Topology.RelCWComplex.map m j) '
' Metric.closedBall 0 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.RelCWComplex.mapsTo`：∀ {X : Type u} {inst : TopologicalSpace X}
 {C : Set X} {D : outParam (Set X)} [self : Topology.RelCWComplex C D] (n : ℕ)  
 (i : Topology.Rel…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.empty_union`：empty_union (a : Set α) : ∅ union a = a
-/
lemma CWComplex.mapsTo [CWComplex C] (n : ℕ) (i : cell C n) : ∃ I : Π m, Finset (cell C m),
    MapsTo (map n i) (sphere 0 1) (⋃ (m < n) (j ∈ I m), map m j '' closedBall 0 1) := by
  have := RelCWComplex.mapsTo n i
  simp_rw [empty_union] at this
  exact this

@[alias_in CWComplex]
/-
**Topology.RelCWComplex.pairwiseDisjoint** 是 Mathlib 中的一个定理，位于命名空间 `Topology.Rel
CWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : Topology.R
elCWComplex C D],   Set.univ.PairwiseDisjoint fun ni => Topology.RelCWComplex.op
enCell ni.fst ni.snd
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.RelCWComplex.pairwiseDisjoint'`：∀ {X : Type u} {inst : Topologi
calSpace X} {C : Set X} {D : outParam (Set X)} [self : Topology.RelCWComplex C D
],   Set.univ.PairwiseDisjoin…
-/
lemma RelCWComplex.pairwiseDisjoint [RelCWComplex C D] :
    (univ : Set (Σ n, cell C n)).PairwiseDisjoint (fun ni ↦ openCell ni.1 ni.2) :=
  RelCWComplex.pairwiseDisjoint'

@[alias_in CWComplex]
/-
**Topology.RelCWComplex.disjointBase** 是 Mathlib 中的一个定理，位于命名空间 `Topology.RelCWCo
mplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : Topology.R
elCWComplex C D] (n : ℕ)   (i : Topology.RelCWComplex.cell C n), Disjoint (Topol
ogy.RelCWComplex.openCell n i) D
参数：n : ℕ；i : Topology.RelCWComplex.cell C n；Topology.RelCWComplex.openCell n i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.RelCWComplex.disjointBase'`：∀ {X : Type u} {inst : TopologicalS
pace X} {C : Set X} {D : outParam (Set X)} [self : Topology.RelCWComplex C D] (n
 : ℕ)   (i : Topology.Rel…
-/
lemma RelCWComplex.disjointBase [RelCWComplex C D] (n : ℕ) (i : cell C n) :
    Disjoint (openCell n i) D :=
  RelCWComplex.disjointBase' n i

@[alias_in CWComplex]
/-
**Topology.RelCWComplex.disjoint_openCell_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Topol
ogy.RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : Topology.R
elCWComplex C D] {n m : ℕ}   {i : Topology.RelCWComplex.cell C n} {j : Topology.
RelCWComplex.cell C m},   ⟨n, i⟩ ≠ ⟨m, j⟩ → Disjoint (Topology.RelCWComplex.open
Cell n i) (Topology.RelCWComplex.openCell m j)
参数：Topology.RelCWComplex.openCell n i；Topology.RelCWComplex.openCell m j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.RelCWComplex.pairwiseDisjoint`：∀ {X : Type u_1} [t : Topologica
lSpace X] {C D : Set X} [inst : Topology.RelCWComplex C D],   Set.univ.PairwiseD
isjoint fun ni => Topology.R…
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
lemma RelCWComplex.disjoint_openCell_of_ne [RelCWComplex C D] {n m : ℕ} {i : cell C n}
    {j : cell C m} (ne : (⟨n, i⟩ : Σ n, cell C n) ≠ ⟨m, j⟩) :
    Disjoint (openCell n i) (openCell m j) :=
  pairwiseDisjoint (mem_univ _) (mem_univ _) ne
/-
**Topology.RelCWComplex.cellFrontier_subset_base_union_finite_closedCell** 是 Mat
hlib 中的一个定理，位于命名空间 `Topology.RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : Topology.R
elCWComplex C D] (n : ℕ)   (i : Topology.RelCWComplex.cell C n),   ∃ I, Topology
.RelCWComplex.cellFrontier n i ⊆ D ∪ ⋃ m, ⋃ (_ : m < n), ⋃ j ∈ I m, Topology.Rel
CWComplex.closedCell m j
参数：n : ℕ；i : Topology.RelCWComplex.cell C n；_ : m < n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.RelCWComplex.mapsTo`：∀ {X : Type u} {inst : TopologicalSpace X}
 {C : Set X} {D : outParam (Set X)} [self : Topology.RelCWComplex C D] (n : ℕ)  
 (i : Topology.Rel…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mapsTo_iff_image_subset`：mapsTo_iff_image_subset : MapsTo f s t ↔ f 
'' s subseteq t
-/
lemma RelCWComplex.cellFrontier_subset_base_union_finite_closedCell [RelCWComplex C D]
    (n : ℕ) (i : cell C n) : ∃ I : Π m, Finset (cell C m), cellFrontier n i ⊆
    D ∪ ⋃ (m < n) (j ∈ I m), closedCell m j := by
  rcases mapsTo n i with ⟨I, hI⟩
  use I
  rw [mapsTo_iff_image_subset] at hI
  exact hI
/-
**Topology.CWComplex.cellFrontier_subset_finite_closedCell** 是 Mathlib 中的一个定理，位于
命名空间 `Topology.CWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C : Set X} [inst : Topology.CWC
omplex C] (n : ℕ)   (i : Topology.RelCWComplex.cell C n),   ∃ I, Topology.RelCWC
omplex.cellFrontier n i ⊆ ⋃ m, ⋃ (_ : m < n), ⋃ j ∈ I m, Topology.RelCWComplex.c
losedCell m j
参数：n : ℕ；i : Topology.RelCWComplex.cell C n；_ : m < n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.RelCWComplex.mapsTo`：∀ {X : Type u} {inst : TopologicalSpace X}
 {C : Set X} {D : outParam (Set X)} [self : Topology.RelCWComplex C D] (n : ℕ)  
 (i : Topology.Rel…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.empty_union`：empty_union (a : Set α) : ∅ union a = a
· 使用定理 `Set.mapsTo_iff_image_subset`：mapsTo_iff_image_subset : MapsTo f s t ↔ f 
'' s subseteq t
-/
lemma CWComplex.cellFrontier_subset_finite_closedCell [CWComplex C] (n : ℕ) (i : cell C n) :
    ∃ I : Π m, Finset (cell C m), cellFrontier n i ⊆ ⋃ (m < n) (j ∈ I m), closedCell m j := by
  rcases RelCWComplex.mapsTo n i with ⟨I, hI⟩
  use I
  rw [mapsTo_iff_image_subset, empty_union] at hI
  exact hI
/-
**Topology.RelCWComplex.union** 是 Mathlib 中的一个定理，位于命名空间 `Topology.RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : Topology.R
elCWComplex C D],   D ∪ ⋃ n, ⋃ j, Topology.RelCWComplex.closedCell n j = C
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.RelCWComplex.union'`：∀ {X : Type u} {inst : TopologicalSpace X}
 {C : Set X} {D : outParam (Set X)} [self : Topology.RelCWComplex C D],   D ∪ ⋃ 
n, ⋃ j, ↑(Topology…
-/
lemma RelCWComplex.union [RelCWComplex C D] : D ∪ ⋃ (n : ℕ) (j : cell C n), closedCell n j = C :=
  RelCWComplex.union'
/-
**Topology.CWComplex.union** 是 Mathlib 中的一个定理，位于命名空间 `Topology.CWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C : Set X} [inst : Topology.CWC
omplex C],   ⋃ n, ⋃ j, Topology.RelCWComplex.closedCell n j = C
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.RelCWComplex.union'`：∀ {X : Type u} {inst : TopologicalSpace X}
 {C : Set X} {D : outParam (Set X)} [self : Topology.RelCWComplex C D],   D ∪ ⋃ 
n, ⋃ j, ↑(Topology…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.empty_union`：empty_union (a : Set α) : ∅ union a = a
-/
lemma CWComplex.union [CWComplex C] : ⋃ (n : ℕ) (j : cell C n), closedCell n j = C := by
  have := RelCWComplex.union' (C := C)
  rw [empty_union] at this
  exact this

@[alias_in CWComplex]
/-
**Topology.RelCWComplex.openCell_subset_closedCell** 是 Mathlib 中的一个定理，位于命名空间 `To
pology.RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : Topology.R
elCWComplex C D] (n : ℕ)   (i : Topology.RelCWComplex.cell C n), Topology.RelCWC
omplex.openCell n i ⊆ Topology.RelCWComplex.closedCell n i
参数：n : ℕ；i : Topology.RelCWComplex.cell C n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Metric.ball_subset_closedBall`：ball_subset_closedBall : ball x ε subsete
q closedBall x ε
-/
lemma RelCWComplex.openCell_subset_closedCell [RelCWComplex C D] (n : ℕ) (i : cell C n) :
    openCell n i ⊆ closedCell n i := image_mono Metric.ball_subset_closedBall

@[alias_in CWComplex]
/-
**Topology.RelCWComplex.cellFrontier_subset_closedCell** 是 Mathlib 中的一个定理，位于命名空间
 `Topology.RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : Topology.R
elCWComplex C D] (n : ℕ)   (i : Topology.RelCWComplex.cell C n), Topology.RelCWC
omplex.cellFrontier n i ⊆ Topology.RelCWComplex.closedCell n i
参数：n : ℕ；i : Topology.RelCWComplex.cell C n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Metric.sphere_subset_closedBall`：sphere_subset_closedBall : sphere x ε s
ubseteq closedBall x ε
-/
lemma RelCWComplex.cellFrontier_subset_closedCell [RelCWComplex C D] (n : ℕ) (i : cell C n) :
    cellFrontier n i ⊆ closedCell n i := image_mono Metric.sphere_subset_closedBall

@[alias_in CWComplex]
/-
**Topology.RelCWComplex.cellFrontier_union_openCell_eq_closedCell** 是 Mathlib 中的
一个定理，位于命名空间 `Topology.RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : Topology.R
elCWComplex C D] (n : ℕ)   (i : Topology.RelCWComplex.cell C n),   Topology.RelC
WComplex.cellFrontier n i ∪ Topology.RelCWComplex.openCell n i = Topology.RelCWC
omplex.closedCell n i
参数：n : ℕ；i : Topology.RelCWComplex.cell C n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.RelCWComplex.cellFrontier.eq_1`：∀ {X : Type u_1} [t : Topologic
alSpace X] {C D : Set X} [inst : Topology.RelCWComplex C D] (n : ℕ)   (i : Topol
ogy.RelCWComplex.cell C n),  …
· 使用定理 `Topology.RelCWComplex.openCell.eq_1`：∀ {X : Type u_1} [t : TopologicalSp
ace X] {C D : Set X} [inst : Topology.RelCWComplex C D] (n : ℕ)   (i : Topology.
RelCWComplex.cell C n),  …
· 使用定理 `Topology.RelCWComplex.closedCell.eq_1`：∀ {X : Type u_1} [t : Topological
Space X] {C D : Set X} [inst : Topology.RelCWComplex C D] (n : ℕ)   (i : Topolog
y.RelCWComplex.cell C n),  …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_union`：image_union (f : α -> β) (s t : Set α) : f '' (s union 
t) = f '' s union f '' t
· 使用定理 `Metric.sphere_union_ball`：sphere_union_ball : sphere x ε union ball x ε 
= closedBall x ε
-/
lemma RelCWComplex.cellFrontier_union_openCell_eq_closedCell [RelCWComplex C D] (n : ℕ)
    (i : cell C n) : cellFrontier n i ∪ openCell n i = closedCell n i := by
  rw [cellFrontier, openCell, closedCell, ← image_union]
  congrm map n i '' ?_
  exact sphere_union_ball

@[alias_in CWComplex]
/-
**Topology.RelCWComplex.map_zero_mem_openCell** 是 Mathlib 中的一个定理，位于命名空间 `Topolog
y.RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : Topology.R
elCWComplex C D] (n : ℕ)   (i : Topology.RelCWComplex.cell C n), ↑(Topology.RelC
WComplex.map n i) 0 ∈ Topology.RelCWComplex.openCell n i
参数：n : ℕ；i : Topology.RelCWComplex.cell C n；Topology.RelCWComplex.map n i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
lemma RelCWComplex.map_zero_mem_openCell [RelCWComplex C D] (n : ℕ) (i : cell C n) :
    map n i 0 ∈ openCell n i := by
  apply mem_image_of_mem
  simp only [mem_ball, dist_self, zero_lt_one]

@[alias_in CWComplex]
/-
**Topology.RelCWComplex.map_zero_mem_closedCell** 是 Mathlib 中的一个定理，位于命名空间 `Topol
ogy.RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : Topology.R
elCWComplex C D] (n : ℕ)   (i : Topology.RelCWComplex.cell C n), ↑(Topology.RelC
WComplex.map n i) 0 ∈ Topology.RelCWComplex.closedCell n i
参数：n : ℕ；i : Topology.RelCWComplex.cell C n；Topology.RelCWComplex.map n i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.RelCWComplex.openCell_subset_closedCell`：∀ {X : Type u_1} [t : 
TopologicalSpace X] {C D : Set X} [inst : Topology.RelCWComplex C D] (n : ℕ)   (
i : Topology.RelCWComplex.cell C n), T…
· 使用定理 `Topology.RelCWComplex.map_zero_mem_openCell`：∀ {X : Type u_1} [t : Topol
ogicalSpace X] {C D : Set X} [inst : Topology.RelCWComplex C D] (n : ℕ)   (i : T
opology.RelCWComplex.cell C n), ↑…
-/
lemma RelCWComplex.map_zero_mem_closedCell [RelCWComplex C D] (n : ℕ) (i : cell C n) :
    map n i 0 ∈ closedCell n i :=
  openCell_subset_closedCell _ _ (map_zero_mem_openCell _ _)
/-
**Topology.RelCWComplex.openCell_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Topology.Re
lCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : Topology.R
elCWComplex C D] (n : ℕ)   (j : Topology.RelCWComplex.cell C n), (Topology.RelCW
Complex.openCell n j).Nonempty
参数：n : ℕ；j : Topology.RelCWComplex.cell C n；Topology.RelCWComplex.openCell n j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.RelCWComplex.map_zero_mem_openCell`：∀ {X : Type u_1} [t : Topol
ogicalSpace X] {C D : Set X} [inst : Topology.RelCWComplex C D] (n : ℕ)   (i : T
opology.RelCWComplex.cell C n), ↑…
-/
lemma RelCWComplex.openCell_nonempty [RelCWComplex C D] (n : ℕ) (j : cell C n) :
    (openCell n j).Nonempty :=
  ⟨(map n j) 0, map_zero_mem_openCell n j⟩
/-
**Topology.RelCWComplex.closedCell_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Topology.
RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : Topology.R
elCWComplex C D] (n : ℕ)   (j : Topology.RelCWComplex.cell C n), (Topology.RelCW
Complex.closedCell n j).Nonempty
参数：n : ℕ；j : Topology.RelCWComplex.cell C n；Topology.RelCWComplex.closedCell n j
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.RelCWComplex.map_zero_mem_closedCell`：∀ {X : Type u_1} [t : Top
ologicalSpace X] {C D : Set X} [inst : Topology.RelCWComplex C D] (n : ℕ)   (i :
 Topology.RelCWComplex.cell C n), ↑…
-/
lemma RelCWComplex.closedCell_nonempty [RelCWComplex C D] (n : ℕ) (j : cell C n) :
    (closedCell n j).Nonempty :=
  ⟨(map n j) 0, map_zero_mem_closedCell n j⟩

/-- If two open cells are equal, so are the underlying cells. -/
/-
**Topology.RelCWComplex.openCell_congr** 是 Mathlib 中的一个定理，位于命名空间 `Topology.RelCW
Complex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : Topology.R
elCWComplex C D] (n : ℕ)   {s t_1 : Topology.RelCWComplex.cell C n},   Topology.
RelCWComplex.openCell n s = Topology.RelCWComplex.openCell n t_1 → s = t_1
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `Disjoint.ne`：Disjoint.ne (ha : a != ⊥) (hab : Disjoint a b) : a != b
· 使用定理 `Set.Nonempty.ne_empty`：∀ {α : Type u} {s : Set α}, s.Nonempty → s ≠ ∅
· 使用定理 `Topology.RelCWComplex.openCell_nonempty`：∀ {X : Type u_1} [t : Topologic
alSpace X] {C D : Set X} [inst : Topology.RelCWComplex C D] (n : ℕ)   (j : Topol
ogy.RelCWComplex.cell C n), (…
· 使用定理 `Topology.RelCWComplex.disjoint_openCell_of_ne`：∀ {X : Type u_1} [t : Top
ologicalSpace X] {C D : Set X} [inst : Topology.RelCWComplex C D] {n m : ℕ}   {i
 : Topology.RelCWComplex.cell C n} …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Sigma.mk.injEq`：∀ {α : Type u} {β : α → Type v} (fst : α) (snd : β fst) 
(fst_1 : α) (snd_1 : β fst_1),   (⟨fst, snd⟩ = ⟨fst_1, snd_1⟩) = (fst = fst_1 ∧ 
snd …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p

--- 原说明 ---
If two open cells are equal, so are the underlying cells.
-/
lemma RelCWComplex.openCell_congr [RelCWComplex C D] (n : ℕ) {s t : cell C n}
    (st : openCell n s = openCell n t) : s = t := by
  contrapose! st
  exact (disjoint_openCell_of_ne (by simpa)).ne (openCell_nonempty n s).ne_empty

/-- This is an auxiliary lemma used to prove `RelCWComplex.eq_of_eq_union_iUnion`. -/
/-
**Topology.RelCWComplex.subset_of_eq_union_iUnion** 是 Mathlib 中的一个引理，位于命名空间 `Top
ology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is an auxiliary lemma used to prove `RelCWComplex.eq_of_eq_union_iUnion`.
-/
private lemma RelCWComplex.subset_of_eq_union_iUnion [RelCWComplex C D] (I J : Π n, Set (cell C n))
    (hIJ : D ∪ ⋃ (n : ℕ) (j : I n), openCell (C := C) n j =
      D ∪ ⋃ (n : ℕ) (j : J n), openCell (C := C) n j) (n : ℕ) :
    I n ⊆ J n := by
  intro i hi
  by_contra hJ
  have h : openCell n i ⊆ D ∪ ⋃ n, ⋃ (j : J n), openCell (C := C) n j :=
    hIJ.symm ▸ subset_union_of_subset_right
      (subset_iUnion_of_subset n (subset_iUnion_of_subset ⟨i, hi⟩ (subset_refl (openCell n i)))) D
  have h' : Disjoint (openCell n i) (D ∪ ⋃ n, ⋃ (j : J n), openCell (C := C) n j) := by
    simp_rw [disjoint_union_right, disjoint_iUnion_right]
    exact ⟨disjointBase n i, fun m j ↦ disjoint_openCell_of_ne (by lia)⟩
  rw [disjoint_of_subset_iff_left_eq_empty h] at h'
  exact notMem_empty _ (h' ▸ map_zero_mem_openCell n i)
/-
**Topology.RelCWComplex.eq_of_eq_union_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Topolog
y.RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : Topology.R
elCWComplex C D]   (I J : (n : ℕ) → Set (Topology.RelCWComplex.cell C n)),   D ∪
 ⋃ n, ⋃ j, Topology.RelCWComplex.openCell n ↑j = D ∪ ⋃ n, ⋃ j, Topology.RelCWCom
plex.openCell n ↑j → I = J
参数：I J : (n : ℕ) → Set (Topology.RelCWComplex.cell C n)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `_private.Mathlib.Topology.CWComplex.Classical.Basic.0.Topology.RelCWComp
lex.subset_of_eq_union_iUnion`：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : 
Set X} [inst : Topology.RelCWComplex C D]   (I J : (n : ℕ) → Set (Topology.RelCW
Complex.cel…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma RelCWComplex.eq_of_eq_union_iUnion [RelCWComplex C D] (I J : Π n, Set (cell C n))
    (hIJ : D ∪ ⋃ (n : ℕ) (j : I n), openCell (C := C) n j =
      D ∪ ⋃ (n : ℕ) (j : J n), openCell (C := C) n j) :
    I = J := by
  ext n x
  exact ⟨fun h ↦ subset_of_eq_union_iUnion I J hIJ n h,
    fun h ↦ subset_of_eq_union_iUnion J I hIJ.symm n h⟩
/-
**Topology.CWComplex.eq_of_eq_union_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Topology.C
WComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C : Set X} [inst : Topology.CWC
omplex C]   (I J : (n : ℕ) → Set (Topology.RelCWComplex.cell C n)),   ⋃ n, ⋃ j, 
Topology.RelCWComplex.openCell n ↑j = ⋃ n, ⋃ j, Topology.RelCWComplex.openCell n
 ↑j → I = J
参数：I J : (n : ℕ) → Set (Topology.RelCWComplex.cell C n)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.RelCWComplex.eq_of_eq_union_iUnion`：∀ {X : Type u_1} [t : Topol
ogicalSpace X] {C D : Set X} [inst : Topology.RelCWComplex C D]   (I J : (n : ℕ)
 → Set (Topology.RelCWComplex.cel…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.empty_union`：empty_union (a : Set α) : ∅ union a = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma CWComplex.eq_of_eq_union_iUnion [CWComplex C] (I J : Π n, Set (cell C n))
    (hIJ : ⋃ (n : ℕ) (j : I n), openCell (C := C) n j =
      ⋃ (n : ℕ) (j : J n), openCell (C := C) n j) :
    I = J := by
  apply RelCWComplex.eq_of_eq_union_iUnion
  simp_rw [empty_union, hIJ]

@[alias_in CWComplex]
/-
**Topology.RelCWComplex.isCompact_closedCell** 是 Mathlib 中的一个定理，位于命名空间 `Topology
.RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : Topology.R
elCWComplex C D] {n : ℕ}   {i : Topology.RelCWComplex.cell C n}, IsCompact (Topo
logy.RelCWComplex.closedCell n i)
参数：Topology.RelCWComplex.closedCell n i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.image_of_continuousOn`：IsCompact.image_of_continuousOn {f : X 
-> Y} (hs : IsCompact s) (hf : ContinuousOn f s) : IsCompact (f '' s)
· 使用定理 `ProperSpace.isCompact_closedBall`：∀ {α : Type u} {inst : PseudoMetricSpa
ce α} [self : ProperSpace α] (x : α) (r : ℝ), IsCompact (Metric.closedBall x r)
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `Topology.RelCWComplex.continuousOn`：∀ {X : Type u} {inst : TopologicalSp
ace X} {C : Set X} {D : outParam (Set X)} [self : Topology.RelCWComplex C D] (n 
: ℕ)   (i : Topology.Rel…
-/
lemma RelCWComplex.isCompact_closedCell [RelCWComplex C D] {n : ℕ} {i : cell C n} :
    IsCompact (closedCell n i) :=
  (isCompact_closedBall _ _).image_of_continuousOn (continuousOn n i)

@[alias_in CWComplex]
/-
**Topology.RelCWComplex.isClosed_closedCell** 是 Mathlib 中的一个定理，位于命名空间 `Topology.
RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : Topology.R
elCWComplex C D] [T2Space X] {n : ℕ}   {i : Topology.RelCWComplex.cell C n}, IsC
losed (Topology.RelCWComplex.closedCell n i)
参数：Topology.RelCWComplex.closedCell n i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `Topology.RelCWComplex.isCompact_closedCell`：∀ {X : Type u_1} [t : Topolo
gicalSpace X] {C D : Set X} [inst : Topology.RelCWComplex C D] {n : ℕ}   {i : To
pology.RelCWComplex.cell C n}, I…
-/
lemma RelCWComplex.isClosed_closedCell [RelCWComplex C D] [T2Space X] {n : ℕ} {i : cell C n} :
    IsClosed (closedCell n i) := isCompact_closedCell.isClosed

@[alias_in CWComplex]
/-
**Topology.RelCWComplex.isCompact_cellFrontier** 是 Mathlib 中的一个定理，位于命名空间 `Topolo
gy.RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : Topology.R
elCWComplex C D] {n : ℕ}   {i : Topology.RelCWComplex.cell C n}, IsCompact (Topo
logy.RelCWComplex.cellFrontier n i)
参数：Topology.RelCWComplex.cellFrontier n i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.image_of_continuousOn`：IsCompact.image_of_continuousOn {f : X 
-> Y} (hs : IsCompact s) (hf : ContinuousOn f s) : IsCompact (f '' s)
· 使用定理 `isCompact_sphere`：isCompact_sphere {α : Type*} [PseudoMetricSpace α] [Pr
operSpace α] (x : α) (r : Real) : IsCompact (sphere x r)
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `Topology.RelCWComplex.continuousOn`：∀ {X : Type u} {inst : TopologicalSp
ace X} {C : Set X} {D : outParam (Set X)} [self : Topology.RelCWComplex C D] (n 
: ℕ)   (i : Topology.Rel…
· 使用定理 `Metric.sphere_subset_closedBall`：sphere_subset_closedBall : sphere x ε s
ubseteq closedBall x ε
-/
lemma RelCWComplex.isCompact_cellFrontier [RelCWComplex C D] {n : ℕ} {i : cell C n} :
    IsCompact (cellFrontier n i) :=
  (isCompact_sphere _ _).image_of_continuousOn ((continuousOn n i).mono sphere_subset_closedBall)

@[alias_in CWComplex]
/-
**Topology.RelCWComplex.isClosed_cellFrontier** 是 Mathlib 中的一个定理，位于命名空间 `Topolog
y.RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : Topology.R
elCWComplex C D] [T2Space X] {n : ℕ}   {i : Topology.RelCWComplex.cell C n}, IsC
losed (Topology.RelCWComplex.cellFrontier n i)
参数：Topology.RelCWComplex.cellFrontier n i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `Topology.RelCWComplex.isCompact_cellFrontier`：∀ {X : Type u_1} [t : Topo
logicalSpace X] {C D : Set X} [inst : Topology.RelCWComplex C D] {n : ℕ}   {i : 
Topology.RelCWComplex.cell C n}, I…
-/
lemma RelCWComplex.isClosed_cellFrontier [RelCWComplex C D] [T2Space X] {n : ℕ} {i : cell C n} :
    IsClosed (cellFrontier n i) :=
  isCompact_cellFrontier.isClosed

@[alias_in CWComplex]
/-
**Topology.RelCWComplex.closure_openCell_eq_closedCell** 是 Mathlib 中的一个定理，位于命名空间
 `Topology.RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : Topology.R
elCWComplex C D] [T2Space X] {n : ℕ}   {j : Topology.RelCWComplex.cell C n},   c
losure (Topology.RelCWComplex.openCell n j) = Topology.RelCWComplex.closedCell n
 j
参数：Topology.RelCWComplex.openCell n j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsClosed.closure_subset_iff`：IsClosed.closure_subset_iff (h₁ : IsClosed 
t) : closure s subseteq t ↔ s subseteq t
· 使用定理 `Topology.RelCWComplex.isClosed_closedCell`：∀ {X : Type u_1} [t : Topolog
icalSpace X] {C D : Set X} [inst : Topology.RelCWComplex C D] [T2Space X] {n : ℕ
}   {i : Topology.RelCWComplex.…
· 使用定理 `Topology.RelCWComplex.openCell_subset_closedCell`：∀ {X : Type u_1} [t : 
TopologicalSpace X] {C D : Set X} [inst : Topology.RelCWComplex C D] (n : ℕ)   (
i : Topology.RelCWComplex.cell C n), T…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.RelCWComplex.closedCell.eq_1`：∀ {X : Type u_1} [t : Topological
Space X] {C D : Set X} [inst : Topology.RelCWComplex C D] (n : ℕ)   (i : Topolog
y.RelCWComplex.cell C n),  …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `closure_ball`：closure_ball (x : E) {r : Real} (hr : r != 0) : closure (b
all x r) = closedBall x r
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `ContinuousOn.image_closure`：ContinuousOn.image_closure (hf : ContinuousO
n f (closure s)) : f '' closure s subseteq closure (f '' s)
· 使用定理 `Topology.RelCWComplex.continuousOn`：∀ {X : Type u} {inst : TopologicalSp
ace X} {C : Set X} {D : outParam (Set X)} [self : Topology.RelCWComplex C D] (n 
: ℕ)   (i : Topology.Rel…
-/
lemma RelCWComplex.closure_openCell_eq_closedCell [RelCWComplex C D] [T2Space X] {n : ℕ}
    {j : cell C n} : closure (openCell n j) = closedCell n j := by
  apply subset_antisymm (isClosed_closedCell.closure_subset_iff.2 (openCell_subset_closedCell n j))
  rw [closedCell, ← closure_ball 0 (by exact one_ne_zero)]
  apply ContinuousOn.image_closure
  rw [closure_ball 0 (by exact one_ne_zero)]
  exact continuousOn n j
/-
**Topology.RelCWComplex.closed** 是 Mathlib 中的一个定理，位于命名空间 `Topology.RelCWComplex`
。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] (C : Set X) {D : Set X} [inst : 
Topology.RelCWComplex C D] [T2Space X],   ∀ A ⊆ C,     IsClosed A ↔       (∀ (n 
: ℕ) (j : Topology.RelCWComplex.cell C n), IsClosed (A ∩ Topology.RelCWComplex.c
losedCell n j)) ∧         IsClosed (A ∩ D)
参数：C : Set X；∀ (n : ℕ) (j : Topology.RelCWComplex.cell C n), IsClosed (A ∩ Topol
ogy.RelCWComplex.closedCell n j)；A ∩ D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.inter`：IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : I
sClosed (s₁ inter s₂)
· 使用定理 `Topology.RelCWComplex.isClosed_closedCell`：∀ {X : Type u_1} [t : Topolog
icalSpace X] {C D : Set X} [inst : Topology.RelCWComplex C D] [T2Space X] {n : ℕ
}   {i : Topology.RelCWComplex.…
· 使用定理 `Topology.RelCWComplex.isClosedBase`：∀ {X : Type u} {inst : TopologicalSp
ace X} (C : Set X) {D : outParam (Set X)} [self : Topology.RelCWComplex C D],   
IsClosed D
· 使用定理 `Topology.RelCWComplex.closed'`：∀ {X : Type u} {inst : TopologicalSpace X
} {C : Set X} {D : outParam (Set X)} [self : Topology.RelCWComplex C D],   ∀ A ⊆
 C,     (∀ (n : ℕ) …
-/
lemma RelCWComplex.closed (C : Set X) {D : Set X} [RelCWComplex C D] [T2Space X] (A : Set X)
    (asubc : A ⊆ C) :
    IsClosed A ↔ (∀ n (j : cell C n), IsClosed (A ∩ closedCell n j)) ∧ IsClosed (A ∩ D) := by
  refine ⟨?_, closed' A asubc⟩
  exact fun closedA ↦ ⟨fun _ _ ↦ closedA.inter isClosed_closedCell, closedA.inter (isClosedBase C)⟩
/-
**Topology.CWComplex.closed** 是 Mathlib 中的一个定理，位于命名空间 `Topology.CWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] (C : Set X) [inst : Topology.CWC
omplex C] [T2Space X],   ∀ A ⊆ C,     IsClosed A ↔ ∀ (n : ℕ) (j : Topology.RelCW
Complex.cell C n), IsClosed (A ∩ Topology.RelCWComplex.closedCell n j)
参数：C : Set X；n : ℕ；j : Topology.RelCWComplex.cell C n；A ∩ Topology.RelCWComplex.
closedCell n j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.RelCWComplex.closed`：∀ {X : Type u_1} [t : TopologicalSpace X] 
(C : Set X) {D : Set X} [inst : Topology.RelCWComplex C D] [T2Space X],   ∀ A ⊆ 
C,     IsClosed A …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_empty`：inter_empty (a : Set α) : a inter ∅ = ∅
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma CWComplex.closed (C : Set X) [CWComplex C] [T2Space X] (A : Set X) (asubc : A ⊆ C) :
    IsClosed A ↔ ∀ n (j : cell C n), IsClosed (A ∩ closedCell n j) := by
  have := RelCWComplex.closed C A asubc
  simp_all

@[alias_in CWComplex]
/-
**Topology.RelCWComplex.closedCell_subset_complex** 是 Mathlib 中的一个定理，位于命名空间 `Top
ology.RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : Topology.R
elCWComplex C D] (n : ℕ)   (j : Topology.RelCWComplex.cell C n), Topology.RelCWC
omplex.closedCell n j ⊆ C
参数：n : ℕ；j : Topology.RelCWComplex.cell C n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.subset_union_of_subset_right`：subset_union_of_subset_right {s u : Se
t α} (h : s subseteq u) (t : Set α) : s subseteq t union u
· 使用定理 `Set.subset_iUnion₂`：subset_iUnion₂ {s : forall i, κ i -> Set α} (i : ι) 
(j : κ i) : s i j subseteq ⋃ (i') (j'), s i' j'
-/
lemma RelCWComplex.closedCell_subset_complex [RelCWComplex C D] (n : ℕ) (j : cell C n) :
    closedCell n j ⊆ C := by
  simp_rw [← union]
  exact subset_union_of_subset_right (subset_iUnion₂ _ _) _

@[alias_in CWComplex]
/-
**Topology.RelCWComplex.openCell_subset_complex** 是 Mathlib 中的一个定理，位于命名空间 `Topol
ogy.RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : Topology.R
elCWComplex C D] (n : ℕ)   (j : Topology.RelCWComplex.cell C n), Topology.RelCWC
omplex.openCell n j ⊆ C
参数：n : ℕ；j : Topology.RelCWComplex.cell C n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Topology.RelCWComplex.openCell_subset_closedCell`：∀ {X : Type u_1} [t : 
TopologicalSpace X] {C D : Set X} [inst : Topology.RelCWComplex C D] (n : ℕ)   (
i : Topology.RelCWComplex.cell C n), T…
· 使用定理 `Topology.RelCWComplex.closedCell_subset_complex`：∀ {X : Type u_1} [t : T
opologicalSpace X] {C D : Set X} [inst : Topology.RelCWComplex C D] (n : ℕ)   (j
 : Topology.RelCWComplex.cell C n), T…
-/
lemma RelCWComplex.openCell_subset_complex [RelCWComplex C D] (n : ℕ) (j : cell C n) :
    openCell n j ⊆ C :=
  (openCell_subset_closedCell _ _).trans (closedCell_subset_complex _ _)

@[alias_in CWComplex]
/-
**Topology.RelCWComplex.cellFrontier_subset_complex** 是 Mathlib 中的一个定理，位于命名空间 `T
opology.RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : Topology.R
elCWComplex C D] (n : ℕ)   (j : Topology.RelCWComplex.cell C n), Topology.RelCWC
omplex.cellFrontier n j ⊆ C
参数：n : ℕ；j : Topology.RelCWComplex.cell C n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Topology.RelCWComplex.cellFrontier_subset_closedCell`：∀ {X : Type u_1} [
t : TopologicalSpace X] {C D : Set X} [inst : Topology.RelCWComplex C D] (n : ℕ)
   (i : Topology.RelCWComplex.cell C n), T…
· 使用定理 `Topology.RelCWComplex.closedCell_subset_complex`：∀ {X : Type u_1} [t : T
opologicalSpace X] {C D : Set X} [inst : Topology.RelCWComplex C D] (n : ℕ)   (j
 : Topology.RelCWComplex.cell C n), T…
-/
lemma RelCWComplex.cellFrontier_subset_complex [RelCWComplex C D] (n : ℕ) (j : cell C n) :
    cellFrontier n j ⊆ C :=
  (cellFrontier_subset_closedCell n j).trans (closedCell_subset_complex n j)

@[alias_in CWComplex]
/-
**Topology.RelCWComplex.closedCell_zero_eq_singleton** 是 Mathlib 中的一个定理，位于命名空间 `
Topology.RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : Topology.R
elCWComplex C D]   {j : Topology.RelCWComplex.cell C 0}, Topology.RelCWComplex.c
losedCell 0 j = {↑(Topology.RelCWComplex.map 0 j) ![]}
参数：Topology.RelCWComplex.map 0 j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Matrix.empty_eq`：empty_eq (v : Fin 0 -> α) : v = ![]
· 使用定理 `Set.Nonempty.image_const`：∀ {α : Type u_1} {β : Type u_2} {s : Set α}, s
.Nonempty → ∀ (a : β), (fun x => a) '' s = {a}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma RelCWComplex.closedCell_zero_eq_singleton [RelCWComplex C D] {j : cell C 0} :
    closedCell 0 j = {map 0 j ![]} := by
  simp [closedCell, Matrix.empty_eq]

@[alias_in CWComplex]
/-
**Topology.RelCWComplex.openCell_zero_eq_singleton** 是 Mathlib 中的一个定理，位于命名空间 `To
pology.RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : Topology.R
elCWComplex C D]   {j : Topology.RelCWComplex.cell C 0}, Topology.RelCWComplex.o
penCell 0 j = {↑(Topology.RelCWComplex.map 0 j) ![]}
参数：Topology.RelCWComplex.map 0 j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Matrix.empty_eq`：empty_eq (v : Fin 0 -> α) : v = ![]
· 使用定理 `Set.Nonempty.image_const`：∀ {α : Type u_1} {β : Type u_2} {s : Set α}, s
.Nonempty → ∀ (a : β), (fun x => a) '' s = {a}
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma RelCWComplex.openCell_zero_eq_singleton [RelCWComplex C D] {j : cell C 0} :
    openCell 0 j = {map 0 j ![]} := by
  simp [openCell, Matrix.empty_eq]

@[alias_in CWComplex]
/-
**Topology.RelCWComplex.cellFrontier_zero_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `To
pology.RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : Topology.R
elCWComplex C D]   {j : Topology.RelCWComplex.cell C 0}, Topology.RelCWComplex.c
ellFrontier 0 j = ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.zero_empty`：∀ {α : Type u_1} [inst : Zero α], 0 = ![]
· 使用定理 `Metric.sphere_eq_empty_of_subsingleton`：sphere_eq_empty_of_subsingleton 
[Subsingleton α] (hε : ε != 0) : sphere x ε = ∅
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma RelCWComplex.cellFrontier_zero_eq_empty [RelCWComplex C D] {j : cell C 0} :
    cellFrontier 0 j = ∅ := by
  simp [cellFrontier, sphere_eq_empty_of_subsingleton]

@[alias_in CWComplex]
/-
**Topology.RelCWComplex.nonempty_cellFrontier** 是 Mathlib 中的一个定理，位于命名空间 `Topolog
y.RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C : Set X} [inst : Topology.CWC
omplex C] {n : ℕ},   n ≠ 0 → ∀ (j : Topology.RelCWComplex.cell C n), (Topology.R
elCWComplex.cellFrontier n j).Nonempty
参数：j : Topology.RelCWComplex.cell C n；Topology.RelCWComplex.cellFrontier n j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Pi.norm_single`：Pi.norm_single [DecidableEq ι] [forall i, NormedAddCommG
roup (G i)] {i : ι} (y : G i) : ‖Pi.single i y‖ = ‖y‖
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma RelCWComplex.nonempty_cellFrontier [CWComplex C] {n : ℕ} (hn : n ≠ 0) (j : cell C n) :
    (cellFrontier n j).Nonempty := by
  let : NeZero n := ⟨hn⟩
  use map n j (Pi.single 0 1)
  simp only [cellFrontier, mem_image, mem_sphere_iff_norm, sub_zero]
  use Pi.single 0 1, by simp [Pi.norm_single]

/-- If two 0-cells have the same characteristic image point, they are equal. -/
@[alias_in CWComplex]
/-
**Topology.RelCWComplex.injective_map_zero** 是 Mathlib 中的一个定理，位于命名空间 `Topology.R
elCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {D : Set X} (C : Set X) [inst : 
Topology.RelCWComplex C D],   Function.Injective fun x => ↑(Topology.RelCWComple
x.map 0 x) ![]
参数：C : Set X；Topology.RelCWComplex.map 0 x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.not_disjoint_iff`：not_disjoint_iff : ¬Disjoint s t ↔ exists x, x in 
s ∧ x in t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.RelCWComplex.openCell_zero_eq_singleton`：∀ {X : Type u_1} [t : 
TopologicalSpace X] {C D : Set X} [inst : Topology.RelCWComplex C D]   {j : Topo
logy.RelCWComplex.cell C 0}, Topology.…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Topology.RelCWComplex.disjoint_openCell_of_ne`：∀ {X : Type u_1} [t : Top
ologicalSpace X] {C D : Set X} [inst : Topology.RelCWComplex C D] {n m : ℕ}   {i
 : Topology.RelCWComplex.cell C n} …

--- 原说明 ---
If two 0-cells have the same characteristic image point, they are equal.
-/
lemma RelCWComplex.injective_map_zero (C : Set X) [RelCWComplex C D] :
    Injective ((map 0 · ![]) : cell C 0 → X) := by
  rintro x z h
  by_contra hne
  exact not_disjoint_iff.mpr ⟨map 0 x ![], by simp [openCell_zero_eq_singleton, h]⟩
    <| disjoint_openCell_of_ne (by grind : (⟨0, x⟩ : Σ n, cell C n) ≠ ⟨0, z⟩)

@[simp, alias_in CWComplex]
/-
**Topology.RelCWComplex.map_zero_eq_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Topology
.RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {D : Set X} (C : Set X) [inst : 
Topology.RelCWComplex C D]   {x z : Topology.RelCWComplex.cell C 0},   ↑(Topolog
y.RelCWComplex.map 0 x) ![] = ↑(Topology.RelCWComplex.map 0 z) ![] ↔ x = z
参数：C : Set X；Topology.RelCWComplex.map 0 x；Topology.RelCWComplex.map 0 z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.RelCWComplex.injective_map_zero`：∀ {X : Type u_1} [t : Topologi
calSpace X] {D : Set X} (C : Set X) [inst : Topology.RelCWComplex C D],   Functi
on.Injective fun x => ↑(Topolo…
-/
lemma RelCWComplex.map_zero_eq_self_iff (C : Set X) [RelCWComplex C D] {x z : cell C 0} :
    map 0 x ![] = map 0 z ![] ↔ x = z :=
  ⟨fun h ↦ injective_map_zero C h, fun h ↦ h ▸ rfl⟩

@[alias_in CWComplex]
/-
**Topology.RelCWComplex.closedCell_zero_injective** 是 Mathlib 中的一个定理，位于命名空间 `Top
ology.RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {D : Set X} (C : Set X) [inst : 
Topology.RelCWComplex C D],   Function.Injective (Topology.RelCWComplex.closedCe
ll 0)
参数：C : Set X；Topology.RelCWComplex.closedCell 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.RelCWComplex.injective_map_zero`：∀ {X : Type u_1} [t : Topologi
calSpace X] {D : Set X} (C : Set X) [inst : Topology.RelCWComplex C D],   Functi
on.Injective fun x => ↑(Topolo…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.singleton_eq_singleton_iff`：singleton_eq_singleton_iff {x y : α} : {
x} = ({y} : Set α) ↔ x = y
· 使用定理 `Topology.RelCWComplex.closedCell_zero_eq_singleton`：∀ {X : Type u_1} [t 
: TopologicalSpace X] {C D : Set X} [inst : Topology.RelCWComplex C D]   {j : To
pology.RelCWComplex.cell C 0}, Topology.…
-/
lemma RelCWComplex.closedCell_zero_injective (C : Set X) [RelCWComplex C D] :
    Injective (closedCell 0 : cell C 0 → _) := by
  intro x y h
  rw [closedCell_zero_eq_singleton, closedCell_zero_eq_singleton, singleton_eq_singleton_iff] at h
  exact injective_map_zero C h

@[alias_in CWComplex]
/-
**Topology.RelCWComplex.openCell_zero_injective** 是 Mathlib 中的一个定理，位于命名空间 `Topol
ogy.RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {D : Set X} (C : Set X) [inst : 
Topology.RelCWComplex C D],   Function.Injective (Topology.RelCWComplex.openCell
 0)
参数：C : Set X；Topology.RelCWComplex.openCell 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.RelCWComplex.injective_map_zero`：∀ {X : Type u_1} [t : Topologi
calSpace X] {D : Set X} (C : Set X) [inst : Topology.RelCWComplex C D],   Functi
on.Injective fun x => ↑(Topolo…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.singleton_eq_singleton_iff`：singleton_eq_singleton_iff {x y : α} : {
x} = ({y} : Set α) ↔ x = y
· 使用定理 `Topology.RelCWComplex.openCell_zero_eq_singleton`：∀ {X : Type u_1} [t : 
TopologicalSpace X] {C D : Set X} [inst : Topology.RelCWComplex C D]   {j : Topo
logy.RelCWComplex.cell C 0}, Topology.…
-/
lemma RelCWComplex.openCell_zero_injective (C : Set X) [RelCWComplex C D] :
    Injective (openCell 0 : cell C 0 → _) := by
  intro x y h
  rw [openCell_zero_eq_singleton, openCell_zero_eq_singleton, singleton_eq_singleton_iff] at h
  exact injective_map_zero C h

@[alias_in CWComplex]
/-
**Topology.RelCWComplex.cellFrontier_one_eq** 是 Mathlib 中的一个定理，位于命名空间 `Topology.
RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : Topology.R
elCWComplex C D]   (e : Topology.RelCWComplex.cell C 1),   Topology.RelCWComplex
.cellFrontier 1 e = ↑(Topology.RelCWComplex.map 1 e) '' {-1, 1}
参数：e : Topology.RelCWComplex.cell C 1；Topology.RelCWComplex.map 1 e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.RelCWComplex.cellFrontier.eq_1`：∀ {X : Type u_1} [t : Topologic
alSpace X] {C D : Set X} [inst : Topology.RelCWComplex C D] (n : ℕ)   (i : Topol
ogy.RelCWComplex.cell C n),  …
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `Finset.sup_singleton`：sup_singleton {b : β} : ({b} : Finset β).sup f = f
 b
· 使用定理 `abs_eq`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrder G
] [IsOrderedAddMonoid G] {a b : G},   0 ≤ b → (|a| = b ↔ a = b ∨ a = -b)
· 使用引理 `zero_le_one'`：zero_le_one' (α) [Zero α] [One α] [LE α] [ZeroLEOneClass α
] : (0 : α) <= 1
· 使用定理 `eq_const_of_unique`：eq_const_of_unique {β : Sort*} [Unique α] (f : α -> 
β) : f = Function.const α (f default)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Function.funext_iff_of_subsingleton`：funext_iff_of_subsingleton [Subsing
leton α] {g : α -> β} (x y : α) : f x = g y ↔ f = g
· 使用定理 `Fin.subsingleton_one`：Subsingleton (Fin 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma RelCWComplex.cellFrontier_one_eq [RelCWComplex C D] (e : cell C 1) :
    cellFrontier 1 e = map 1 e '' {-1, 1} := by
  rw [cellFrontier]
  congr 1
  ext f
  simp only [mem_sphere_iff_norm, sub_zero, Pi.norm_def, Finset.univ_unique, Fin.default_eq_zero,
    Fin.isValue, Finset.sup_singleton, coe_nnnorm, Real.norm_eq_abs, abs_eq (zero_le_one' ℝ),
    mem_insert_iff, mem_singleton_iff]
  rw [eq_const_of_unique (f := f), ← funext_iff_of_subsingleton (x := 0) (y := 0)]
  simp [const_apply, or_comm]
/-
**Topology.CWComplex.exists_cellFrontier_one_eq** 是 Mathlib 中的一个定理，位于命名空间 `Topol
ogy.CWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C : Set X} [inst : Topology.CWC
omplex C]   (e : Topology.RelCWComplex.cell C 1),   ∃ x y,     Topology.RelCWCom
plex.cellFrontier 1 e = Topology.RelCWComplex.closedCell 0 x ∪ Topology.RelCWCom
plex.closedCell 0 y
参数：e : Topology.RelCWComplex.cell C 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.CWComplex.cellFrontier_subset_finite_closedCell`：∀ {X : Type u_
1} [t : TopologicalSpace X] {C : Set X} [inst : Topology.CWComplex C] (n : ℕ)   
(i : Topology.RelCWComplex.cell C n),   ∃ I, T…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.RelCWComplex.cellFrontier_one_eq`：∀ {X : Type u_1} [t : Topolog
icalSpace X] {C D : Set X} [inst : Topology.RelCWComplex C D]   (e : Topology.Re
lCWComplex.cell C 1),   Topolog…
· 使用定理 `Set.image_pair`：image_pair (f : α -> β) (a b : α) : f '' {a, b} = {f a, 
f b}
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Set.iUnion_iUnion_eq_left`：iUnion_iUnion_eq_left {b : β} {s : forall x :
 β, x = b -> Set α} : ⋃ (x) (h : x = b), s x h = s b rfl
· 使用定理 `Topology.RelCWComplex.closedCell_zero_eq_singleton`：∀ {X : Type u_1} [t 
: TopologicalSpace X] {C D : Set X} [inst : Topology.RelCWComplex C D]   {j : To
pology.RelCWComplex.cell C 0}, Topology.…
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.pair_comm`：pair_comm (a b : α) : ({a, b} : Set α) = {b, a}
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma CWComplex.exists_cellFrontier_one_eq [CWComplex C] (e : cell C 1) :
    ∃ x y : cell C 0, cellFrontier 1 e = closedCell 0 x ∪ closedCell 0 y := by
  obtain ⟨f, h⟩ := cellFrontier_subset_finite_closedCell 1 e
  simp only [RelCWComplex.cellFrontier_one_eq, image_pair, Order.lt_one_iff, iUnion_iUnion_eq_left,
    RelCWComplex.closedCell_zero_eq_singleton, pair_subset_iff, mem_iUnion, mem_singleton_iff,
    exists_prop] at h
  obtain ⟨⟨u, hu, hun1⟩, v, hv, hv1⟩ := h
  use u, v
  simp [RelCWComplex.cellFrontier_one_eq, image_pair, RelCWComplex.closedCell_zero_eq_singleton,
    hun1, hv1, pair_comm]

@[alias_in CWComplex]
/-
**Topology.RelCWComplex.base_subset_complex** 是 Mathlib 中的一个定理，位于命名空间 `Topology.
RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [Topology.RelCWCom
plex C D], D ⊆ C
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
-/
lemma RelCWComplex.base_subset_complex [RelCWComplex C D] : D ⊆ C := by
  simp_rw [← union]
  exact subset_union_left

@[alias_in CWComplex]
/-
**Topology.RelCWComplex.isClosed** 是 Mathlib 中的一个定理，位于命名空间 `Topology.RelCWComple
x`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [T2Space X] [Topol
ogy.RelCWComplex C D], IsClosed C
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.RelCWComplex.closed`：∀ {X : Type u_1} [t : TopologicalSpace X] 
(C : Set X) {D : Set X} [inst : Topology.RelCWComplex C D] [T2Space X],   ∀ A ⊆ 
C,     IsClosed A …
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_eq_right`：∀ {α : Type u} {s t : Set α}, s ∩ t = t ↔ t ⊆ s
· 使用定理 `Topology.RelCWComplex.closedCell_subset_complex`：∀ {X : Type u_1} [t : T
opologicalSpace X] {C D : Set X} [inst : Topology.RelCWComplex C D] (n : ℕ)   (j
 : Topology.RelCWComplex.cell C n), T…
· 使用定理 `Topology.RelCWComplex.isClosed_closedCell`：∀ {X : Type u_1} [t : Topolog
icalSpace X] {C D : Set X} [inst : Topology.RelCWComplex C D] [T2Space X] {n : ℕ
}   {i : Topology.RelCWComplex.…
· 使用定理 `Topology.RelCWComplex.base_subset_complex`：∀ {X : Type u_1} [t : Topolog
icalSpace X] {C D : Set X} [Topology.RelCWComplex C D], D ⊆ C
· 使用定理 `Topology.RelCWComplex.isClosedBase`：∀ {X : Type u} {inst : TopologicalSp
ace X} (C : Set X) {D : outParam (Set X)} [self : Topology.RelCWComplex C D],   
IsClosed D
-/
lemma RelCWComplex.isClosed [T2Space X] [RelCWComplex C D] : IsClosed C := by
  rw [closed C C (by rfl)]
  constructor
  · intros
    rw [inter_eq_right.2 (closedCell_subset_complex _ _)]
    exact isClosed_closedCell
  · rw [inter_eq_right.2 base_subset_complex]
    exact isClosedBase C

/-- A helper lemma that is essentially the same as `RelCWComplex.iUnion_openCell_eq_skeletonLT`.
Use that lemma instead. -/
/-
**Topology.RelCWComplex.iUnion_openCell_eq_iUnion_closedCell** 是 Mathlib 中的一个引理，
位于命名空间 `Topology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A helper lemma that is essentially the same as `RelCWComplex.iUnion_openCell_eq_
skeletonLT`.
Use that lemma instead.
-/
private lemma RelCWComplex.iUnion_openCell_eq_iUnion_closedCell [RelCWComplex C D] (n : ℕ∞) :
    D ∪ ⋃ (m : ℕ) (_ : m < n) (j : cell C m), openCell m j =
      D ∪ ⋃ (m : ℕ) (_ : m < n) (j : cell C m), closedCell m j := by
  apply subset_antisymm
  · apply union_subset
    · exact subset_union_left
    · apply iUnion₂_subset fun m hm ↦ iUnion_subset fun j ↦ ?_
      apply subset_union_of_subset_right
      apply subset_iUnion₂_of_subset m hm
      apply subset_iUnion_of_subset j
      exact openCell_subset_closedCell m j
  · apply union_subset subset_union_left
    refine iUnion₂_subset fun m hm ↦ iUnion_subset fun j ↦ ?_
    rw [← cellFrontier_union_openCell_eq_closedCell]
    apply union_subset
    · induction m using Nat.case_strong_induction_on with
      | hz => simp [cellFrontier_zero_eq_empty]
      | hi m hm' =>
        obtain ⟨I, hI⟩ := cellFrontier_subset_base_union_finite_closedCell (m + 1) j
        apply hI.trans
        apply union_subset subset_union_left
        apply iUnion₂_subset fun l hl ↦ iUnion₂_subset fun i _ ↦ ?_
        rw [← cellFrontier_union_openCell_eq_closedCell]
        apply union_subset
        · exact (hm' l (Nat.le_of_lt_succ hl) ((ENat.natCast_lt_natCast.2 hl).trans hm) i)
        · apply subset_union_of_subset_right
          exact subset_iUnion₂_of_subset l ((ENat.natCast_lt_natCast.2 hl).trans hm) <|
            subset_iUnion _ i
    · exact subset_union_of_subset_right (subset_iUnion₂_of_subset m hm (subset_iUnion _ j)) _
/-
**Topology.RelCWComplex.union_iUnion_openCell_eq_complex** 是 Mathlib 中的一个定理，位于命名
空间 `Topology.RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : Topology.R
elCWComplex C D],   D ∪ ⋃ n, ⋃ j, Topology.RelCWComplex.openCell n j = C
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.iUnion_true`：iUnion_true {s : True -> Set α} : iUnion s = s trivial
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Topology.RelCWComplex.union`：∀ {X : Type u_1} [t : TopologicalSpace X] {
C D : Set X} [inst : Topology.RelCWComplex C D],   D ∪ ⋃ n, ⋃ j, Topology.RelCWC
omplex.closedCell…
-/
lemma RelCWComplex.union_iUnion_openCell_eq_complex [RelCWComplex C D] :
    D ∪ ⋃ (n : ℕ) (j : cell C n), openCell n j = C := by
  suffices D ∪ ⋃ n, ⋃ (j : cell C n), openCell n j =
      D ∪ ⋃ (m : ℕ) (_ : m < (⊤ : ℕ∞)) (j : cell C m), closedCell m j by
    simpa [union] using this
  simp_rw [← RelCWComplex.iUnion_openCell_eq_iUnion_closedCell, ENat.natCast_lt_top, iUnion_true]
/-
**Topology.CWComplex.iUnion_openCell_eq_complex** 是 Mathlib 中的一个定理，位于命名空间 `Topol
ogy.CWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C : Set X} [inst : Topology.CWC
omplex C],   ⋃ n, ⋃ j, Topology.RelCWComplex.openCell n j = C
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.empty_union`：empty_union (a : Set α) : ∅ union a = a
· 使用定理 `Topology.RelCWComplex.union_iUnion_openCell_eq_complex`：∀ {X : Type u_1}
 [t : TopologicalSpace X] {C D : Set X} [inst : Topology.RelCWComplex C D],   D 
∪ ⋃ n, ⋃ j, Topology.RelCWComplex.openCell n…
-/
lemma CWComplex.iUnion_openCell_eq_complex [CWComplex C] :
    ⋃ (n : ℕ) (j : cell C n), openCell n j = C := by
  simpa using RelCWComplex.union_iUnion_openCell_eq_complex (C := C)

/-- The contrapositive of `disjoint_openCell_of_ne`. -/
@[alias_in CWComplex]
/-
**Topology.RelCWComplex.eq_of_not_disjoint_openCell** 是 Mathlib 中的一个定理，位于命名空间 `T
opology.RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : Topology.R
elCWComplex C D] {n : ℕ}   {j : Topology.RelCWComplex.cell C n} {m : ℕ} {i : Top
ology.RelCWComplex.cell C m},   ¬Disjoint (Topology.RelCWComplex.openCell n j) (
Topology.RelCWComplex.openCell m i) → ⟨n, j⟩ = ⟨m, i⟩
参数：Topology.RelCWComplex.openCell n j；Topology.RelCWComplex.openCell m i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `Topology.RelCWComplex.disjoint_openCell_of_ne`：∀ {X : Type u_1} [t : Top
ologicalSpace X] {C D : Set X} [inst : Topology.RelCWComplex C D] {n m : ℕ}   {i
 : Topology.RelCWComplex.cell C n} …

--- 原说明 ---
The contrapositive of `disjoint_openCell_of_ne`.
-/
lemma RelCWComplex.eq_of_not_disjoint_openCell [RelCWComplex C D] {n : ℕ} {j : cell C n} {m : ℕ}
    {i : cell C m} (h : ¬ Disjoint (openCell n j) (openCell m i)) :
    (⟨n, j⟩ : (Σ n, cell C n)) = ⟨m, i⟩ := by
  contrapose! h
  exact disjoint_openCell_of_ne h
/-
**Topology.RelCWComplex.disjoint_base_iUnion_openCell** 是 Mathlib 中的一个定理，位于命名空间 
`Topology.RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : Topology.R
elCWComplex C D],   Disjoint D (⋃ n, ⋃ j, Topology.RelCWComplex.openCell n j)
参数：⋃ n, ⋃ j, Topology.RelCWComplex.openCell n j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.inter_iUnion`：inter_iUnion (s : Set β) (t : ι -> Set β) : (s inter ⋃
 i, t i) = ⋃ i, s inter t i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Disjoint.inter_eq`：∀ {α : Type u} {s t : Set α}, Disjoint s t → s ∩ t = 
∅
· 使用定理 `Topology.RelCWComplex.disjointBase`：∀ {X : Type u_1} [t : TopologicalSpa
ce X] {C D : Set X} [inst : Topology.RelCWComplex C D] (n : ℕ)   (i : Topology.R
elCWComplex.cell C n), D…
-/
lemma RelCWComplex.disjoint_base_iUnion_openCell [RelCWComplex C D] :
    Disjoint D (⋃ (n : ℕ) (j : cell C n), openCell n j) := by
  simp_rw [disjoint_iff_inter_eq_empty, inter_iUnion, iUnion_eq_empty]
  intro n i
  rw [inter_comm, (disjointBase n i).inter_eq]

/-- If for all `m ≤ n` and every `i : cell C m` the intersection `A ∩ closedCell m j` is closed
and `A ∩ D` is closed then `A ∩ cellFrontier (n + 1) j` is closed for every
`j : cell C (n + 1)`. -/
/-
**Topology.RelCWComplex.isClosed_inter_cellFrontier_succ_of_le_isClosed_inter_cl
osedCell** 是 Mathlib 中的一个定理，位于命名空间 `Topology.RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : Topology.R
elCWComplex C D] [T2Space X] {A : Set X}   {n : ℕ},   (∀ m ≤ n, ∀ (j : Topology.
RelCWComplex.cell C m), IsClosed (A ∩ Topology.RelCWComplex.closedCell m j)) →  
   ∀ (j : Topology.RelCWComplex.cell C (n + 1)),       IsClosed (A ∩ D) → IsClos
ed (A ∩ Topology.RelCWComplex.cellFrontier (n + 1) j)
参数：∀ m ≤ n, ∀ (j : Topology.RelCWComplex.cell C m), IsClosed (A ∩ Topology.RelCW
Complex.closedCell m j)；j : Topology.RelCWComplex.cell C (n + 1)；A ∩ D；A ∩ Topol
ogy.RelCWComplex.cellFrontier (n + 1) j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.RelCWComplex.cellFrontier_subset_base_union_finite_closedCell`：
∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : Topology.RelCWCo
mplex C D] (n : ℕ)   (i : Topology.RelCWComplex.cell C n),  …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_eq_right`：∀ {α : Type u} {s t : Set α}, s ∩ t = t ↔ t ⊆ s
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
· 使用定理 `IsClosed.inter`：IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : I
sClosed (s₁ inter s₂)
· 使用定理 `Set.inter_union_distrib_left`：inter_union_distrib_left (s t u : Set α) :
 s inter (t union u) = s inter t union s inter u
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.inter_iUnion`：inter_iUnion (s : Set β) (t : ι -> Set β) : (s inter ⋃
 i, t i) = ⋃ i, s inter t i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_subtype`：iUnion_subtype (p : α -> Prop) (s : { x // p x } -> 
Set β) : ⋃ x : { x // p x }, s x = ⋃ (x) (hx : p x), s ⟨x, hx⟩
· 使用定理 `IsClosed.union`：IsClosed.union : IsClosed s₁ -> IsClosed s₂ -> IsClosed 
(s₁ union s₂)
· 使用定理 `isClosed_iUnion_of_finite`：isClosed_iUnion_of_finite [Finite ι] {s : ι -
> Set X} (h : forall i, IsClosed (s i)) : IsClosed (⋃ i, s i)
· 使用定理 `instFiniteSubtypeLtOfLocallyFiniteOrderBot`：∀ {α : Type u_1} [inst : Pre
order α] {y : α} [LocallyFiniteOrderBot α], Finite { x // x < y }
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Nat.le_of_lt_succ`：∀ {m n : ℕ}, m < n.succ → m ≤ n
· 使用定理 `Topology.RelCWComplex.isClosed_cellFrontier`：∀ {X : Type u_1} [t : Topol
ogicalSpace X] {C D : Set X} [inst : Topology.RelCWComplex C D] [T2Space X] {n :
 ℕ}   {i : Topology.RelCWComplex.…

--- 原说明 ---
If for all `m ≤ n` and every `i : cell C m` the intersection `A ∩ closedCell m j
` is closed
and `A ∩ D` is closed then `A ∩ cellFrontier (n + 1) j` is closed for every
`j : cell C (n + 1)`.
-/
lemma RelCWComplex.isClosed_inter_cellFrontier_succ_of_le_isClosed_inter_closedCell
    [RelCWComplex C D] [T2Space X] {A : Set X} {n : ℕ} (hn : ∀ m ≤ n, ∀ (j : cell C m),
    IsClosed (A ∩ closedCell m j)) (j : cell C (n + 1)) (hD : IsClosed (A ∩ D)) :
    IsClosed (A ∩ cellFrontier (n + 1) j) := by
  -- this is a consequence of `cellFrontier_subset_base_union_finite_closedCell`
  obtain ⟨I, hI⟩ := cellFrontier_subset_base_union_finite_closedCell (n + 1) j
  rw [← inter_eq_right.2 hI, ← inter_assoc]
  refine IsClosed.inter ?_ isClosed_cellFrontier
  simp_rw [inter_union_distrib_left, inter_iUnion,
    ← iUnion_subtype (fun m ↦ m < n + 1) (fun m ↦ ⋃ i ∈ I m, A ∩ closedCell m i)]
  apply hD.union
  apply isClosed_iUnion_of_finite
  intro ⟨m, mlt⟩
  rw [← iUnion_subtype (fun i ↦ i ∈ I m) (fun i ↦ A ∩ closedCell m i.1)]
  exact isClosed_iUnion_of_finite (fun ⟨j, _⟩ ↦ hn m (Nat.le_of_lt_succ mlt) j)
/-
**Topology.CWComplex.isClosed_inter_cellFrontier_succ_of_le_isClosed_inter_close
dCell** 是 Mathlib 中的一个定理，位于命名空间 `Topology.CWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C : Set X} [inst : Topology.CWC
omplex C] [T2Space X] {A : Set X} {n : ℕ},   (∀ m ≤ n, ∀ (j : Topology.RelCWComp
lex.cell C m), IsClosed (A ∩ Topology.RelCWComplex.closedCell m j)) →     ∀ (j :
 Topology.RelCWComplex.cell C (n + 1)), IsClosed (A ∩ Topology.RelCWComplex.cell
Frontier (n + 1) j)
参数：∀ m ≤ n, ∀ (j : Topology.RelCWComplex.cell C m), IsClosed (A ∩ Topology.RelCW
Complex.closedCell m j)；j : Topology.RelCWComplex.cell C (n + 1)；A ∩ Topology.Re
lCWComplex.cellFrontier (n + 1) j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.RelCWComplex.isClosed_inter_cellFrontier_succ_of_le_isClosed_in
ter_closedCell`：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : 
Topology.RelCWComplex C D] [T2Space X] {A : Set X}   {n : ℕ},   (∀ m ≤ n, ∀ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_empty`：inter_empty (a : Set α) : a inter ∅ = ∅
-/
lemma CWComplex.isClosed_inter_cellFrontier_succ_of_le_isClosed_inter_closedCell
    [CWComplex C] [T2Space X] {A : Set X} {n : ℕ} (hn : ∀ m ≤ n, ∀ (j : cell C m),
    IsClosed (A ∩ closedCell m j)) (j : cell C (n + 1)) :
    IsClosed (A ∩ cellFrontier (n + 1) j) :=
  RelCWComplex.isClosed_inter_cellFrontier_succ_of_le_isClosed_inter_closedCell hn j
    (by simp only [inter_empty, isClosed_empty])

/-- If for every cell either `A ∩ openCell n j` or `A ∩ closedCell n j` is closed then
`A` is closed. -/
/-
**Topology.RelCWComplex.isClosed_of_isClosed_inter_openCell_or_isClosed_inter_cl
osedCell** 是 Mathlib 中的一个定理，位于命名空间 `Topology.RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : Topology.R
elCWComplex C D] [T2Space X] {A : Set X},   A ⊆ C →     IsClosed (A ∩ D) →      
 (∀ (n : ℕ),           0 < n →             ∀ (j : Topology.RelCWComplex.cell C n
),               IsClosed (A ∩ Topology.RelCWComplex.openCell n j) ∨ IsClosed (A
 ∩ Topology.RelCWComplex.closedCell n j)) →         IsClosed A
参数：A ∩ D；∀ (n : ℕ),           0 < n →             ∀ (j : Topology.RelCWComplex.c
ell C n),               IsClosed (A ∩ Topology.RelCWComplex.openCell n j) ∨ IsCl
osed (A ∩ Topology.RelCWComplex.closedCell n j)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.RelCWComplex.closed`：∀ {X : Type u_1} [t : TopologicalSpace X] 
(C : Set X) {D : Set X} [inst : Topology.RelCWComplex C D] [T2Space X],   ∀ A ⊆ 
C,     IsClosed A …
· 使用定理 `Nat.case_strong_induction_on`：∀ {p : ℕ → Prop} (a : ℕ), p 0 → (∀ (n : ℕ)
, (∀ m ≤ n, p m) → p (n + 1)) → p a
· 使用定理 `Topology.RelCWComplex.closedCell_zero_eq_singleton`：∀ {X : Type u_1} [t 
: TopologicalSpace X] {C D : Set X} [inst : Topology.RelCWComplex C D]   {j : To
pology.RelCWComplex.cell C 0}, Topology.…
· 使用引理 `isClosed_inter_singleton`：isClosed_inter_singleton [T1Space X] {A : Set 
X} {a : X} : IsClosed (A inter {a})
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `Nat.zero_lt_succ`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.RelCWComplex.cellFrontier_union_openCell_eq_closedCell`：∀ {X : 
Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : Topology.RelCWComplex C
 D] (n : ℕ)   (i : Topology.RelCWComplex.cell C n),  …
· 使用定理 `Set.inter_union_distrib_left`：inter_union_distrib_left (s t u : Set α) :
 s inter (t union u) = s inter t union s inter u
· 使用定理 `IsClosed.union`：IsClosed.union : IsClosed s₁ -> IsClosed s₂ -> IsClosed 
(s₁ union s₂)
· 使用定理 `Topology.RelCWComplex.isClosed_inter_cellFrontier_succ_of_le_isClosed_in
ter_closedCell`：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : 
Topology.RelCWComplex C D] [T2Space X] {A : Set X}   {n : ℕ},   (∀ m ≤ n, ∀ …

--- 原说明 ---
If for every cell either `A ∩ openCell n j` or `A ∩ closedCell n j` is closed th
en
`A` is closed.
-/
lemma RelCWComplex.isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell
    [RelCWComplex C D] [T2Space X] {A : Set X} (hAC : A ⊆ C) (hDA : IsClosed (A ∩ D))
    (h : ∀ n (_ : 0 < n), ∀ (j : cell C n),
    IsClosed (A ∩ openCell n j) ∨ IsClosed (A ∩ closedCell n j)) : IsClosed A := by
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

/-- If for every cell either `A ∩ openCell n j` is empty or `A ∩ closedCell n j` is closed then
`A` is closed. -/
/-
**Topology.RelCWComplex.isClosed_of_disjoint_openCell_or_isClosed_inter_closedCe
ll** 是 Mathlib 中的一个定理，位于命名空间 `Topology.RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : Topology.R
elCWComplex C D] [T2Space X] {A : Set X},   A ⊆ C →     IsClosed (A ∩ D) →      
 (∀ (n : ℕ),           0 < n →             ∀ (j : Topology.RelCWComplex.cell C n
),               Disjoint A (Topology.RelCWComplex.openCell n j) ∨ IsClosed (A ∩
 Topology.RelCWComplex.closedCell n j)) →         IsClosed A
参数：A ∩ D；∀ (n : ℕ),           0 < n →             ∀ (j : Topology.RelCWComplex.c
ell C n),               Disjoint A (Topology.RelCWComplex.openCell n j) ∨ IsClos
ed (A ∩ Topology.RelCWComplex.closedCell n j)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.RelCWComplex.isClosed_of_isClosed_inter_openCell_or_isClosed_in
ter_closedCell`：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : 
Topology.RelCWComplex C D] [T2Space X] {A : Set X},   A ⊆ C →     IsClosed (…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.disjoint_iff_inter_eq_empty`：disjoint_iff_inter_eq_empty : Disjoint 
s t ↔ s inter t = ∅
· 使用定理 `isClosed_empty`：isClosed_empty : IsClosed (∅ : Set X)

--- 原说明 ---
If for every cell either `A ∩ openCell n j` is empty or `A ∩ closedCell n j` is 
closed then
`A` is closed.
-/
lemma RelCWComplex.isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell
    [RelCWComplex C D] [T2Space X] {A : Set X} (hAC : A ⊆ C) (hDA : IsClosed (A ∩ D))
    (h : ∀ n (_ : 0 < n), ∀ (j : cell C n),
    Disjoint A (openCell n j) ∨ IsClosed (A ∩ closedCell n j)) : IsClosed A := by
  apply isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell hAC hDA
  intro n hn j
  rcases h n hn j with h | h
  · left
    rw [disjoint_iff_inter_eq_empty.1 h]
    exact isClosed_empty
  · exact Or.inr h

/-- If for every cell either `A ∩ openCell n j` or `A ∩ closedCell n j` is closed then
`A` is closed. -/
/-
**Topology.CWComplex.isClosed_of_isClosed_inter_openCell_or_isClosed_inter_close
dCell** 是 Mathlib 中的一个定理，位于命名空间 `Topology.CWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C : Set X} [inst : Topology.CWC
omplex C] [T2Space X] {A : Set X},   A ⊆ C →     (∀ (n : ℕ),         0 < n →    
       ∀ (j : Topology.RelCWComplex.cell C n),             IsClosed (A ∩ Topolog
y.RelCWComplex.openCell n j) ∨ IsClosed (A ∩ Topology.RelCWComplex.closedCell n 
j)) →       IsClosed A
参数：∀ (n : ℕ),         0 < n →           ∀ (j : Topology.RelCWComplex.cell C n), 
            IsClosed (A ∩ Topology.RelCWComplex.openCell n j) ∨ IsClosed (A ∩ To
pology.RelCWComplex.closedCell n j)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.RelCWComplex.isClosed_of_isClosed_inter_openCell_or_isClosed_in
ter_closedCell`：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : 
Topology.RelCWComplex C D] [T2Space X] {A : Set X},   A ⊆ C →     IsClosed (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_empty`：inter_empty (a : Set α) : a inter ∅ = ∅
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X

--- 原说明 ---
If for every cell either `A ∩ openCell n j` or `A ∩ closedCell n j` is closed th
en
`A` is closed.
-/
lemma CWComplex.isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell
    [CWComplex C] [T2Space X] {A : Set X} (hAC : A ⊆ C) (h : ∀ n (_ : 0 < n), ∀ (j : cell C n),
    IsClosed (A ∩ openCell n j) ∨ IsClosed (A ∩ closedCell n j)) : IsClosed A :=
  RelCWComplex.isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell hAC (by simp) h

/-- If for every cell either `A ∩ openCell n j` is empty or `A ∩ closedCell n j` is closed then
`A` is closed. -/
/-
**Topology.CWComplex.isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell*
* 是 Mathlib 中的一个定理，位于命名空间 `Topology.CWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C : Set X} [inst : Topology.CWC
omplex C] [T2Space X] {A : Set X},   A ⊆ C →     (∀ (n : ℕ),         0 < n →    
       ∀ (j : Topology.RelCWComplex.cell C n),             Disjoint A (Topology.
RelCWComplex.openCell n j) ∨ IsClosed (A ∩ Topology.RelCWComplex.closedCell n j)
) →       IsClosed A
参数：∀ (n : ℕ),         0 < n →           ∀ (j : Topology.RelCWComplex.cell C n), 
            Disjoint A (Topology.RelCWComplex.openCell n j) ∨ IsClosed (A ∩ Topo
logy.RelCWComplex.closedCell n j)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.RelCWComplex.isClosed_of_disjoint_openCell_or_isClosed_inter_cl
osedCell`：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : Topolo
gy.RelCWComplex C D] [T2Space X] {A : Set X},   A ⊆ C →     IsClosed (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_empty`：inter_empty (a : Set α) : a inter ∅ = ∅
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X

--- 原说明 ---
If for every cell either `A ∩ openCell n j` is empty or `A ∩ closedCell n j` is 
closed then
`A` is closed.
-/
lemma CWComplex.isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell
    [CWComplex C] [T2Space X] {A : Set X} (hAC : A ⊆ C) (h : ∀ n (_ : 0 < n), ∀ (j : cell C n),
    Disjoint A (openCell n j) ∨ IsClosed (A ∩ closedCell n j)) : IsClosed A :=
  RelCWComplex.isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell hAC (by simp) h

/-- A version of `cellFrontier_subset_base_union_finite_closedCell` using open cells:
The boundary of a cell is contained in a finite union of open cells of a lower dimension. -/
/-
**Topology.RelCWComplex.cellFrontier_subset_finite_openCell** 是 Mathlib 中的一个定理，位
于命名空间 `Topology.RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : Topology.R
elCWComplex C D] (n : ℕ)   (i : Topology.RelCWComplex.cell C n),   ∃ I, Topology
.RelCWComplex.cellFrontier n i ⊆ D ∪ ⋃ m, ⋃ (_ : m < n), ⋃ j ∈ I m, Topology.Rel
CWComplex.openCell m j
参数：n : ℕ；i : Topology.RelCWComplex.cell C n；_ : m < n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.case_strong_induction_on`：∀ {p : ℕ → Prop} (a : ℕ), p 0 → (∀ (n : ℕ)
, (∀ m ≤ n, p m) → p (n + 1)) → p a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Topology.RelCWComplex.cellFrontier_zero_eq_empty`：∀ {X : Type u_1} [t : 
TopologicalSpace X] {C D : Set X} [inst : Topology.RelCWComplex C D]   {j : Topo
logy.RelCWComplex.cell C 0}, Topology.…
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Set.iUnion_of_empty`：iUnion_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋃ i,
 s i = ∅
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Set.iUnion_empty`：iUnion_empty : (⋃ _ : ι, ∅ : Set α) = ∅
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
· 使用定理 `Pi.instNonempty`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Nonempty (β
 a)], Nonempty ((a : α) → β a)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Topology.RelCWComplex.cellFrontier_subset_base_union_finite_closedCell`：
∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : Topology.RelCWCo
mplex C D] (n : ℕ)   (i : Topology.RelCWComplex.cell C n),  …
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.RelCWComplex.cellFrontier_union_openCell_eq_closedCell`：∀ {X : 
Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : Topology.RelCWComplex C
 D] (n : ℕ)   (i : Topology.RelCWComplex.cell C n),  …
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `Nat.le_of_lt_succ`：∀ {m n : ℕ}, m < n.succ → m ≤ n
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Or.intro_left`：∀ {a : Prop} (b : Prop), a → a ∨ b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
A version of `cellFrontier_subset_base_union_finite_closedCell` using open cells
:
The boundary of a cell is contained in a finite union of open cells of a lower d
imension.
-/
lemma RelCWComplex.cellFrontier_subset_finite_openCell [RelCWComplex C D] (n : ℕ) (i : cell C n) :
    ∃ I : Π m, Finset (cell C m),
    cellFrontier n i ⊆ D ∪ (⋃ (m < n) (j ∈ I m), openCell m j) := by
  induction n using Nat.case_strong_induction_on with
  | hz => simp [cellFrontier_zero_eq_empty]
  | hi n hn =>
    -- We apply `cellFrontier_subset_base_union_finite_closedCell` once and then apply
    -- the induction hypothesis to the finitely many cells that
    -- `cellFrontier_subset_base_union_finite_closedCell` gives us.
    classical
    obtain ⟨J, hJ⟩ := cellFrontier_subset_base_union_finite_closedCell n.succ i
    choose p hp using hn
    let I m := J m ∪ ((Finset.range n.succ).biUnion
      (fun l ↦ (J l).biUnion (fun y ↦ if h : l ≤ n then p l h y m else ∅)))
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
      refine .imp_right (fun ⟨k, hkl, i, hi, hxi⟩ ↦ ⟨k, lt_trans hkl hln, i, ?_, hxi⟩) hp
      simp only [Nat.succ_eq_add_one, Finset.mem_union, Finset.mem_biUnion, Finset.mem_range, I]
      exact .inr ⟨l, hln, j, hj, by simp [Nat.le_of_lt_succ hln, hi]⟩
    · right
      use l, hln, j
      simp only [Nat.succ_eq_add_one, Finset.mem_union, I]
      exact ⟨Or.intro_left _ hj, hxj⟩

/-- A version of `cellFrontier_subset_finite_closedCell` using open cells: The boundary of a cell is
contained in a finite union of open cells of a lower dimension. -/
/-
**Topology.CWComplex.cellFrontier_subset_finite_openCell** 是 Mathlib 中的一个定理，位于命名
空间 `Topology.CWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C : Set X} [inst : Topology.CWC
omplex C] (n : ℕ)   (i : Topology.RelCWComplex.cell C n),   ∃ I, Topology.RelCWC
omplex.cellFrontier n i ⊆ ⋃ m, ⋃ (_ : m < n), ⋃ j ∈ I m, Topology.RelCWComplex.o
penCell m j
参数：n : ℕ；i : Topology.RelCWComplex.cell C n；_ : m < n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.empty_union`：empty_union (a : Set α) : ∅ union a = a
· 使用定理 `Topology.RelCWComplex.cellFrontier_subset_finite_openCell`：∀ {X : Type u
_1} [t : TopologicalSpace X] {C D : Set X} [inst : Topology.RelCWComplex C D] (n
 : ℕ)   (i : Topology.RelCWComplex.cell C n),  …

--- 原说明 ---
A version of `cellFrontier_subset_finite_closedCell` using open cells: The bound
ary of a cell is
contained in a finite union of open cells of a lower dimension.
-/
lemma CWComplex.cellFrontier_subset_finite_openCell [CWComplex C] (n : ℕ) (i : cell C n) :
    ∃ I : Π m, Finset (cell C m),
    cellFrontier n i ⊆ ⋃ (m < n) (j ∈ I m), openCell m j := by
  simpa using RelCWComplex.cellFrontier_subset_finite_openCell n i

section Subcomplex

namespace RelCWComplex

/-- A subcomplex is a closed subspace of a CW complex that is the union of open cells of the
  CW complex. -/
/-
**Topology.RelCWComplex.Subcomplex** 是 Mathlib 中的一个结构，位于命名空间 `Topology.RelCWComp
lex`。
形式化陈述：Subcomplex (C : Set X) {D : Set X} [RelCWComplex C D] where /-- The underl
ying set of the subcomplex. -/ carrier : Set X /-- The indexing set of cells of 
the subcomplex. -/ I : Π n, Set (cell C n) /-- A subcomplex is closed. -/ closed
' : IsClosed carrier /-- The union of all open cells of the subcomplex equals th
e subcomplex. -/ union' : D union ⋃ (n : Nat) (j : I n), openCell (C
参数：C : Set X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subcomplex is a closed subspace of a CW complex that is the union of open cell
s of the
  CW complex.
-/
structure Subcomplex (C : Set X) {D : Set X} [RelCWComplex C D] where
  /-- The underlying set of the subcomplex. -/
  carrier : Set X
  /-- The indexing set of cells of the subcomplex. -/
  I : Π n, Set (cell C n)
  /-- A subcomplex is closed. -/
  closed' : IsClosed carrier
  /-- The union of all open cells of the subcomplex equals the subcomplex. -/
  union' : D ∪ ⋃ (n : ℕ) (j : I n), openCell (C := C) n j = carrier

namespace Subcomplex

variable [RelCWComplex C D]

/-
**Topology.RelCWComplex.Subcomplex.** 是 Mathlib 中的一个实例，位于命名空间 `Topology.RelCWCom
plex.Subcomplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetLike (Subcomplex C) X where
  coe E := E.carrier
  coe_injective E F h := by
    obtain ⟨E, _, _, hE⟩ := E
    obtain ⟨F, _, _, hF⟩ := F
    congr
    apply eq_of_eq_union_iUnion
    rw [hE, hF]
    simpa using h
/-
**Topology.RelCWComplex.Subcomplex.** 是 Mathlib 中的一个实例，位于命名空间 `Topology.RelCWCom
plex.Subcomplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (Subcomplex C) := .ofSetLike (Subcomplex C) X

initialize_simps_projections Subcomplex (carrier → coe, as_prefix coe)

@[alias_in CWComplex.Subcomplex]
/-
**Topology.RelCWComplex.Subcomplex.mem_carrier** 是 Mathlib 中的一个引理，位于命名空间 `Topolo
gy.RelCWComplex.Subcomplex`。
形式化陈述：mem_carrier {E : Subcomplex C} {x : X} : x in E.carrier ↔ x in (E : Set X)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_carrier {E : Subcomplex C} {x : X} : x ∈ E.carrier ↔ x ∈ (E : Set X) := Iff.rfl

@[alias_in CWComplex.Subcomplex]
/-
**Topology.RelCWComplex.Subcomplex.coe_eq_carrier** 是 Mathlib 中的一个引理，位于命名空间 `Top
ology.RelCWComplex.Subcomplex`。
形式化陈述：coe_eq_carrier {E : Subcomplex C} : (E : Set X) = E.carrier
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_eq_carrier {E : Subcomplex C} : (E : Set X) = E.carrier := rfl

@[ext, alias_in CWComplex.Subcomplex]
/-
**Topology.RelCWComplex.Subcomplex.ext** 是 Mathlib 中的一个引理，位于命名空间 `Topology.RelCW
Complex.Subcomplex`。
形式化陈述：ext {E F : Subcomplex C} (h : forall x, x in E ↔ x in F) : E = F
参数：h : forall x, x in E ↔ x in F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
-/
lemma ext {E F : Subcomplex C} (h : ∀ x, x ∈ E ↔ x ∈ F) : E = F :=
  SetLike.ext h

@[alias_in CWComplex.Subcomplex]
/-
**Topology.RelCWComplex.Subcomplex.eq_iff** 是 Mathlib 中的一个引理，位于命名空间 `Topology.Re
lCWComplex.Subcomplex`。
形式化陈述：eq_iff (E F : Subcomplex C) : E = F ↔ (E : Set X) = F
参数：E F : Subcomplex C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
lemma eq_iff (E F : Subcomplex C) : E = F ↔ (E : Set X) = F :=
  SetLike.coe_injective.eq_iff.symm

/-- Copy of a `Subcomplex` with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
/-
**Topology.RelCWComplex.Subcomplex.copy** 是 Mathlib 中的一个定义，位于命名空间 `Topology.RelC
WComplex.Subcomplex`。
形式化陈述：{X : Type u_1} →   [t : TopologicalSpace X] →     {C D : Set X} →       [i
nst : Topology.RelCWComplex C D] →         (E : Topology.RelCWComplex.Subcomplex
 C) →           (F : Set X) →             F = ↑E → (J : (n : ℕ) → Set (Topology.
RelCWComplex.cell C n)) → J = E.I → Topology.RelCWComplex.Subcomplex C
参数：E : Topology.RelCWComplex.Subcomplex C；F : Set X；J : (n : ℕ) → Set (Topology.
RelCWComplex.cell C n)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a `Subcomplex` with a new `carrier` equal to the old one. Useful to fix 
definitional
equalities.
-/
protected def copy (E : Subcomplex C) (F : Set X) (hF : F = E) (J : (n : ℕ) → Set (cell C n))
    (hJ : J = E.I) : Subcomplex C :=
  { carrier := F
    I := J
    closed' := hF.symm ▸ E.closed'
    union' := hF.symm ▸ hJ ▸ E.union' }

@[simp, alias_in CWComplex.Subcomplex]
/-
**Topology.RelCWComplex.Subcomplex.coe_copy** 是 Mathlib 中的一个引理，位于命名空间 `Topology.
RelCWComplex.Subcomplex`。
形式化陈述：coe_copy (E : Subcomplex C) (F : Set X) (hF : F = E) (J : (n : Nat) -> Set
 (cell C n)) (hJ : J = E.I) : (E.copy F hF J hJ : Set X) = F
参数：E : Subcomplex C；F : Set X；hF : F = E；J : (n : Nat) -> Set (cell C n)；hJ : J 
= E.I。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_copy (E : Subcomplex C) (F : Set X) (hF : F = E) (J : (n : ℕ) → Set (cell C n))
    (hJ : J = E.I) : (E.copy F hF J hJ : Set X) = F :=
  rfl

@[alias_in CWComplex.Subcomplex]
/-
**Topology.RelCWComplex.Subcomplex.copy_eq** 是 Mathlib 中的一个引理，位于命名空间 `Topology.R
elCWComplex.Subcomplex`。
形式化陈述：copy_eq (E : Subcomplex C) (F : Set X) (hF : F = E) (J : (n : Nat) -> Set 
(cell C n)) (hJ : J = E.I) : E.copy F hF J hJ = E
参数：E : Subcomplex C；F : Set X；hF : F = E；J : (n : Nat) -> Set (cell C n)；hJ : J 
= E.I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
lemma copy_eq (E : Subcomplex C) (F : Set X) (hF : F = E) (J : (n : ℕ) → Set (cell C n))
    (hJ : J = E.I) : E.copy F hF J hJ = E :=
  SetLike.coe_injective hF
/-
**Topology.RelCWComplex.Subcomplex.union** 是 Mathlib 中的一个引理，位于命名空间 `Topology.Rel
CWComplex.Subcomplex`。
形式化陈述：union (E : Subcomplex C) : D union ⋃ (n : Nat) (j : E.I n), openCell (C
参数：E : Subcomplex C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.RelCWComplex.Subcomplex.union'`：∀ {X : Type u_1} [t : Topologic
alSpace X] {C D : Set X} [inst : Topology.RelCWComplex C D]   (self : Topology.R
elCWComplex.Subcomplex C), D …
-/
lemma union (E : Subcomplex C) :
    D ∪ ⋃ (n : ℕ) (j : E.I n), openCell (C := C) n j.1 = E := by
  rw [E.union']
  rfl

@[alias_in CWComplex.Subcomplex]
/-
**Topology.RelCWComplex.Subcomplex.closed** 是 Mathlib 中的一个引理，位于命名空间 `Topology.Re
lCWComplex.Subcomplex`。
形式化陈述：closed (E : Subcomplex C) : IsClosed (E : Set X)
参数：E : Subcomplex C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.RelCWComplex.Subcomplex.closed'`：∀ {X : Type u_1} [t : Topologi
calSpace X] {C D : Set X} [inst : Topology.RelCWComplex C D]   (self : Topology.
RelCWComplex.Subcomplex C), Is…
-/
lemma closed (E : Subcomplex C) : IsClosed (E : Set X) := E.closed'

end Subcomplex

end RelCWComplex

namespace CWComplex

export RelCWComplex (Subcomplex Subcomplex.I Subcomplex.copy)

end CWComplex

/-
**Topology.CWComplex.Subcomplex.union** 是 Mathlib 中的一个定理，位于命名空间 `Topology.CWComp
lex.Subcomplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C : Set X} [inst : Topology.CWC
omplex C]   {E : Topology.RelCWComplex.Subcomplex C}, ⋃ n, ⋃ j, Topology.RelCWCo
mplex.openCell n ↑j = ↑E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.RelCWComplex.Subcomplex.union`：union (E : Subcomplex C) : D uni
on ⋃ (n : Nat) (j : E.I n), openCell (C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.empty_union`：empty_union (a : Set α) : ∅ union a = a
-/
lemma CWComplex.Subcomplex.union {C : Set X} [CWComplex C] {E : Subcomplex C} :
    ⋃ (n : ℕ) (j : E.I n), openCell (C := C) n j = E := by
  have := RelCWComplex.Subcomplex.union E (C := C)
  rw [empty_union] at this
  exact this

/-- An alternative version of `Subcomplex.mk`: Instead of requiring that `E` is closed it requires
that for every cell of the subcomplex the corresponding closed cell is a subset of `E`. -/
@[simps -isSimp]
/-
**Topology.RelCWComplex.Subcomplex.mk'** 是 Mathlib 中的一个定义，位于命名空间 `Topology.RelCW
Complex.Subcomplex`。
形式化陈述：{X : Type u_1} →   [t : TopologicalSpace X] →     [T2Space X] →       (C :
 Set X) →         {D : Set X} →           [inst : Topology.RelCWComplex C D] →  
           (E : Set X) →               (I : (n : ℕ) → Set (Topology.RelCWComplex
.cell C n)) →                 (∀ (n : ℕ) (i : ↑(I n)), Topology.RelCWComplex.clo
sedCell n ↑i ⊆ E) →                   D ∪ ⋃ n, ⋃ j, Topology.RelCWComplex.openCe
ll n ↑j = E → Topology.RelCWComplex.Subcomplex C
参数：C : Set X；E : Set X；I : (n : ℕ) → Set (Topology.RelCWComplex.cell C n)；∀ (n :
 ℕ) (i : ↑(I n)), Topology.RelCWComplex.closedCell n ↑i ⊆ E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An alternative version of `Subcomplex.mk`: Instead of requiring that `E` is clos
ed it requires
that for every cell of the subcomplex the corresponding closed cell is a subset 
of `E`.
-/
def RelCWComplex.Subcomplex.mk' [T2Space X] (C : Set X) {D : Set X} [RelCWComplex C D]
    (E : Set X) (I : Π n, Set (cell C n))
    (closedCell_subset : ∀ (n : ℕ) (i : I n), closedCell (C := C) n i ⊆ E)
    (union : D ∪ ⋃ (n : ℕ) (j : I n), openCell (C := C) n j = E) : Subcomplex C where
  carrier := E
  I := I
  closed' := by
    have hEC : (E : Set X) ⊆ C := by
      simp_rw [← union, ← union_iUnion_openCell_eq_complex (C := C)]
      exact union_subset_union_right D
        (iUnion_mono fun n ↦ iUnion_subset fun i ↦ subset_iUnion _ (i : cell C n))
    apply isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell hEC
    · have : D ⊆ E := by
        rw [← union]
        exact subset_union_left
      rw [inter_eq_right.2 this]
      exact isClosedBase C
    intro n _ j
    by_cases h : j ∈ I n
    · right
      suffices closedCell n j ⊆ E by
        rw [inter_eq_right.2 this]
        exact isClosed_closedCell
      exact closedCell_subset n ⟨j, h⟩
    · left
      simp_rw [← union, disjoint_union_left, disjoint_iUnion_left]
      exact ⟨disjointBase n j |>.symm, fun _ _ ↦ disjoint_openCell_of_ne (by aesop)⟩
  union' := union

/-- An alternative version of `Subcomplex.mk`: Instead of requiring that `E` is closed it requires
that for every cell of the subcomplex the corresponding closed cell is a subset of `E`. -/
@[simps! -isSimp]
/-
**Topology.CWComplex.Subcomplex.mk'** 是 Mathlib 中的一个定义，位于命名空间 `Topology.CWComple
x.Subcomplex`。
形式化陈述：{X : Type u_1} →   [t : TopologicalSpace X] →     [T2Space X] →       (C :
 Set X) →         [inst : Topology.CWComplex C] →           (E : Set X) →       
      (I : (n : ℕ) → Set (Topology.RelCWComplex.cell C n)) →               (∀ (n
 : ℕ) (i : ↑(I n)), Topology.RelCWComplex.closedCell n ↑i ⊆ E) →                
 ⋃ n, ⋃ j, Topology.RelCWComplex.openCell n ↑j = E → Topology.RelCWComplex.Subco
mplex C
参数：C : Set X；E : Set X；I : (n : ℕ) → Set (Topology.RelCWComplex.cell C n)；∀ (n :
 ℕ) (i : ↑(I n)), Topology.RelCWComplex.closedCell n ↑i ⊆ E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An alternative version of `Subcomplex.mk`: Instead of requiring that `E` is clos
ed it requires
that for every cell of the subcomplex the corresponding closed cell is a subset 
of `E`.
-/
def CWComplex.Subcomplex.mk' [T2Space X] (C : Set X) [CWComplex C] (E : Set X)
    (I : Π n, Set (cell C n))
    (closedCell_subset : ∀ (n : ℕ) (i : I n), closedCell (C := C) n i ⊆ E)
    (union : ⋃ (n : ℕ) (j : I n), openCell (C := C) n j = E) : Subcomplex C :=
  RelCWComplex.Subcomplex.mk' C E I closedCell_subset (by rw [empty_union]; exact union)

/-- An alternative version of `Subcomplex.mk`: Instead of requiring that `E` is closed it requires
that `E` is a CW-complex. -/
@[simps -isSimp]
/-
**Topology.RelCWComplex.Subcomplex.mk''** 是 Mathlib 中的一个定义，位于命名空间 `Topology.RelC
WComplex.Subcomplex`。
形式化陈述：{X : Type u_1} →   [t : TopologicalSpace X] →     [T2Space X] →       (C :
 Set X) →         {D : Set X} →           [inst : Topology.RelCWComplex C D] →  
           (E : Set X) →               (I : (n : ℕ) → Set (Topology.RelCWComplex
.cell C n)) →                 [Topology.RelCWComplex E D] →                   D 
∪ ⋃ n, ⋃ j, Topology.RelCWComplex.openCell n ↑j = E → Topology.RelCWComplex.Subc
omplex C
参数：C : Set X；E : Set X；I : (n : ℕ) → Set (Topology.RelCWComplex.cell C n)。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.RelCWComplex.isClosed`：∀ {X : Type u_1} [t : TopologicalSpace X
] {C D : Set X} [T2Space X] [Topology.RelCWComplex C D], IsClosed C

--- 原说明 ---
An alternative version of `Subcomplex.mk`: Instead of requiring that `E` is clos
ed it requires
that `E` is a CW-complex.
-/
def RelCWComplex.Subcomplex.mk'' [T2Space X] (C : Set X) {D : Set X} [RelCWComplex C D] (E : Set X)
    (I : Π n, Set (cell C n)) [RelCWComplex E D]
    (union : D ∪ ⋃ (n : ℕ) (j : I n), openCell (C := C) n j = E) : Subcomplex C where
  carrier := E
  I := I
  closed' := isClosed
  union' := union

/-- An alternative version of `Subcomplex.mk`: Instead of requiring that `E` is closed it requires
that `E` is a CW-complex. -/
@[simps -isSimp]
/-
**Topology.CWComplex.Subcomplex.mk''** 是 Mathlib 中的一个定义，位于命名空间 `Topology.CWCompl
ex.Subcomplex`。
形式化陈述：{X : Type u_1} →   [t : TopologicalSpace X] →     [T2Space X] →       (C :
 Set X) →         [h : Topology.CWComplex C] →           (E : Set X) →          
   (I : (n : ℕ) → Set (Topology.RelCWComplex.cell C n)) →               [Topolog
y.CWComplex E] →                 ⋃ n, ⋃ j, Topology.RelCWComplex.openCell n ↑j =
 E → Topology.RelCWComplex.Subcomplex C
参数：C : Set X；E : Set X；I : (n : ℕ) → Set (Topology.RelCWComplex.cell C n)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An alternative version of `Subcomplex.mk`: Instead of requiring that `E` is clos
ed it requires
that `E` is a CW-complex.
-/
def CWComplex.Subcomplex.mk'' [T2Space X] (C : Set X) [h : CWComplex C] (E : Set X)
    (I : Π n, Set (cell C n)) [CWComplex E]
    (union : ⋃ (n : ℕ) (j : I n), openCell (C := C) n j = E) :
    Subcomplex C where
  carrier := E
  I := I
  closed' := RelCWComplex.isClosed
  union' := by
    rw [empty_union]
    exact union

@[alias_in CWComplex.Subcomplex]
/-
**Topology.RelCWComplex.Subcomplex.subset_complex** 是 Mathlib 中的一个定理，位于命名空间 `Top
ology.RelCWComplex.Subcomplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : Topology.R
elCWComplex C D]   (E : Topology.RelCWComplex.Subcomplex C), ↑E ⊆ C
参数：E : Topology.RelCWComplex.Subcomplex C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_subset_union_right`：union_subset_union_right (s) {t₁ t₂ : Set 
α} (h : t₁ subseteq t₂) : s union t₁ subseteq s union t₂
· 使用定理 `Set.iUnion_mono`：iUnion_mono {s t : ι -> Set α} (h : forall i, s i subse
teq t i) : ⋃ i, s i subseteq ⋃ i, t i
· 使用定理 `Set.iUnion_mono'`：iUnion_mono' {s : ι -> Set α} {t : ι₂ -> Set α} (h : f
orall i, exists j, s i subseteq t j) : ⋃ i, s i subseteq ⋃ i, t i
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a
-/
lemma RelCWComplex.Subcomplex.subset_complex {C D : Set X} [RelCWComplex C D] (E : Subcomplex C) :
    ↑E ⊆ C := by
  simp_rw [← union, ← RelCWComplex.union_iUnion_openCell_eq_complex]
  exact union_subset_union_right _ (iUnion_mono fun _ ↦ iUnion_mono' fun j ↦ ⟨j, subset_rfl⟩)

@[alias_in CWComplex.Subcomplex]
/-
**Topology.RelCWComplex.Subcomplex.base_subset** 是 Mathlib 中的一个定理，位于命名空间 `Topolo
gy.RelCWComplex.Subcomplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : Topology.R
elCWComplex C D]   (E : Topology.RelCWComplex.Subcomplex C), D ⊆ ↑E
参数：E : Topology.RelCWComplex.Subcomplex C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
-/
lemma RelCWComplex.Subcomplex.base_subset {C D : Set X} [RelCWComplex C D] (E : Subcomplex C) :
    D ⊆ E := by
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
/-
**Topology.RelCWComplex.skeletonLT** 是 Mathlib 中的一个定义，位于命名空间 `Topology.RelCWComp
lex`。
形式化陈述：skeletonLT (C : Set X) {D : Set X} [RelCWComplex C D] (n : Nat∞) : Subcomp
lex C
参数：C : Set X；n : Nat∞。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-standard definition of the `n`-skeleton of a CW complex for `n ∈ ℕ ∪ {∞}`.
This allows the base case of induction to be about the base instead of being abo
ut the union of
the base and some points.
The standard `skeleton` is defined in terms of `skeletonLT`. `skeletonLT` is pre
ferred
in statements. You should then derive the statement about `skeleton`.
-/
def skeletonLT (C : Set X) {D : Set X} [RelCWComplex C D] (n : ℕ∞) : Subcomplex C :=
    Subcomplex.mk' _ (D ∪ ⋃ (m : ℕ) (_ : m < n) (j : cell C m), closedCell m j)
    (fun l ↦ {x : cell C l | l < n})
    (by
      intro l ⟨i, hi⟩
      apply subset_union_of_subset_right
      apply subset_iUnion₂_of_subset l hi
      exact subset_iUnion _ _)
    (by
      rw [← RelCWComplex.iUnion_openCell_eq_iUnion_closedCell]
      congrm D ∪ ?_
      apply iUnion_congr fun m ↦ ?_
      rw [iUnion_subtype, iUnion_comm]
      rfl)

/-- The `n`-skeleton of a CW complex, for `n ∈ ℕ ∪ {∞}`. For statements use `skeletonLT` instead
and then derive the statement about `skeleton`. -/
/-
**Topology.RelCWComplex.skeleton** 是 Mathlib 中的一个缩写定义，位于命名空间 `Topology.RelCWComp
lex`。
形式化陈述：skeleton (C : Set X) {D : Set X} [RelCWComplex C D] (n : Nat∞) : Subcomple
x C
参数：C : Set X；n : Nat∞。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `n`-skeleton of a CW complex, for `n ∈ ℕ ∪ {∞}`. For statements use `skeleto
nLT` instead
and then derive the statement about `skeleton`.
-/
abbrev skeleton (C : Set X) {D : Set X} [RelCWComplex C D] (n : ℕ∞) : Subcomplex C :=
  skeletonLT C (n + 1)

end RelCWComplex

namespace CWComplex

export RelCWComplex (skeletonLT skeleton)

end CWComplex

/-
**Topology.RelCWComplex.skeletonLT_zero_eq_base** 是 Mathlib 中的一个定理，位于命名空间 `Topol
ogy.RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : T2Space X]
 [inst_1 : Topology.RelCWComplex C D],   ↑(Topology.RelCWComplex.skeletonLT C 0)
 = D
参数：Topology.RelCWComplex.skeletonLT C 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.RelCWComplex.coe_skeletonLT`：∀ {X : Type u_1} [t : TopologicalS
pace X] [inst : T2Space X] (C : Set X) {D : Set X}   [inst_1 : Topology.RelCWCom
plex C D] (n : ℕ∞),   ↑(To…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `Set.iUnion_of_empty`：iUnion_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋃ i,
 s i = ∅
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Set.iUnion_empty`：iUnion_empty : (⋃ _ : ι, ∅ : Set α) = ∅
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma RelCWComplex.skeletonLT_zero_eq_base [RelCWComplex C D] : skeletonLT C 0 = D := by
  simp [coe_skeletonLT]
/-
**Topology.CWComplex.skeletonLT_zero_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Topolog
y.CWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C : Set X} [inst : T2Space X] [
inst_1 : Topology.CWComplex C],   ↑(Topology.RelCWComplex.skeletonLT C 0) = ∅
参数：Topology.RelCWComplex.skeletonLT C 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.RelCWComplex.skeletonLT_zero_eq_base`：∀ {X : Type u_1} [t : Top
ologicalSpace X] {C D : Set X} [inst : T2Space X] [inst_1 : Topology.RelCWComple
x C D],   ↑(Topology.RelCWComplex.s…
-/
lemma CWComplex.skeletonLT_zero_eq_empty [CWComplex C] : (skeletonLT C 0 : Set X) = ∅ :=
    RelCWComplex.skeletonLT_zero_eq_base
/-
**Topology.RelCWComplex.skeletonLT_top** 是 Mathlib 中的一个定理，位于命名空间 `Topology.RelCW
Complex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : T2Space X]
 [inst_1 : Topology.RelCWComplex C D],   ↑(Topology.RelCWComplex.skeletonLT C ⊤)
 = C
参数：Topology.RelCWComplex.skeletonLT C ⊤。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.RelCWComplex.coe_skeletonLT`：∀ {X : Type u_1} [t : TopologicalS
pace X] [inst : T2Space X] (C : Set X) {D : Set X}   [inst_1 : Topology.RelCWCom
plex C D] (n : ℕ∞),   ↑(To…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_true`：iUnion_true {s : True -> Set α} : iUnion s = s trivial
· 使用定理 `Topology.RelCWComplex.union`：∀ {X : Type u_1} [t : TopologicalSpace X] {
C D : Set X} [inst : Topology.RelCWComplex C D],   D ∪ ⋃ n, ⋃ j, Topology.RelCWC
omplex.closedCell…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp, alias_in CWComplex] lemma RelCWComplex.skeletonLT_top [RelCWComplex C D] :
    skeletonLT C ⊤ = C := by
  simp [coe_skeletonLT, union]
/-
**Topology.RelCWComplex.skeleton_top** 是 Mathlib 中的一个定理，位于命名空间 `Topology.RelCWCo
mplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : T2Space X]
 [inst_1 : Topology.RelCWComplex C D],   ↑(Topology.RelCWComplex.skeleton C ⊤) =
 C
参数：Topology.RelCWComplex.skeleton C ⊤。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.RelCWComplex.skeletonLT_top`：∀ {X : Type u_1} [t : TopologicalS
pace X] {C D : Set X} [inst : T2Space X] [inst_1 : Topology.RelCWComplex C D],  
 ↑(Topology.RelCWComplex.s…
-/
@[simp, alias_in CWComplex] lemma RelCWComplex.skeleton_top [RelCWComplex C D] : skeleton C ⊤ = C :=
  skeletonLT_top

@[alias_in CWComplex]
/-
**Topology.RelCWComplex.skeletonLT_mono** 是 Mathlib 中的一个定理，位于命名空间 `Topology.RelC
WComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : T2Space X]
 [inst_1 : Topology.RelCWComplex C D]   {n m : ℕ∞}, m ≤ n → ↑(Topology.RelCWComp
lex.skeletonLT C m) ⊆ ↑(Topology.RelCWComplex.skeletonLT C n)
参数：Topology.RelCWComplex.skeletonLT C m；Topology.RelCWComplex.skeletonLT C n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.RelCWComplex.coe_skeletonLT`：∀ {X : Type u_1} [t : TopologicalS
pace X] [inst : T2Space X] (C : Set X) {D : Set X}   [inst_1 : Topology.RelCWCom
plex C D] (n : ℕ∞),   ↑(To…
· 使用定理 `Set.union_subset_union_right`：union_subset_union_right (s) {t₁ t₂ : Set 
α} (h : t₁ subseteq t₂) : s union t₁ subseteq s union t₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
-/
lemma RelCWComplex.skeletonLT_mono [RelCWComplex C D] {n m : ℕ∞} (h : m ≤ n) :
    (skeletonLT C m : Set X) ⊆ skeletonLT C n := by
  simp_rw [coe_skeletonLT]
  apply union_subset_union_right
  intro x xmem
  simp_rw [mem_iUnion, exists_prop] at xmem ⊢
  obtain ⟨l, lltm, xmeml⟩ := xmem
  exact ⟨l, lt_of_lt_of_le lltm h, xmeml⟩

@[alias_in CWComplex]
/-
**Topology.RelCWComplex.skeletonLT_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Topology.
RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : T2Space X]
 [inst_1 : Topology.RelCWComplex C D],   Monotone (Topology.RelCWComplex.skeleto
nLT C)
参数：Topology.RelCWComplex.skeletonLT C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.RelCWComplex.skeletonLT_mono`：∀ {X : Type u_1} [t : Topological
Space X] {C D : Set X} [inst : T2Space X] [inst_1 : Topology.RelCWComplex C D]  
 {n m : ℕ∞}, m ≤ n → ↑(Topo…
-/
lemma RelCWComplex.skeletonLT_monotone [RelCWComplex C D] : Monotone (skeletonLT C) :=
  fun _ _ h ↦ skeletonLT_mono h

@[alias_in CWComplex]
/-
**Topology.RelCWComplex.skeleton_mono** 是 Mathlib 中的一个定理，位于命名空间 `Topology.RelCWC
omplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : T2Space X]
 [inst_1 : Topology.RelCWComplex C D]   {n m : ℕ∞}, m ≤ n → ↑(Topology.RelCWComp
lex.skeleton C m) ⊆ ↑(Topology.RelCWComplex.skeleton C n)
参数：Topology.RelCWComplex.skeleton C m；Topology.RelCWComplex.skeleton C n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.RelCWComplex.skeletonLT_mono`：∀ {X : Type u_1} [t : Topological
Space X] {C D : Set X} [inst : T2Space X] [inst_1 : Topology.RelCWComplex C D]  
 {n m : ℕ∞}, m ≤ n → ↑(Topo…
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma RelCWComplex.skeleton_mono [RelCWComplex C D] {n m : ℕ∞} (h : m ≤ n) :
    (skeleton C m : Set X) ⊆ skeleton C n :=
  skeletonLT_mono (by gcongr)

@[alias_in CWComplex]
/-
**Topology.RelCWComplex.skeleton_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Topology.Re
lCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : T2Space X]
 [inst_1 : Topology.RelCWComplex C D],   Monotone (Topology.RelCWComplex.skeleto
n C)
参数：Topology.RelCWComplex.skeleton C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.RelCWComplex.skeleton_mono`：∀ {X : Type u_1} [t : TopologicalSp
ace X] {C D : Set X} [inst : T2Space X] [inst_1 : Topology.RelCWComplex C D]   {
n m : ℕ∞}, m ≤ n → ↑(Topo…
-/
lemma RelCWComplex.skeleton_monotone [RelCWComplex C D] : Monotone (skeleton C) :=
  fun _ _ h ↦ skeleton_mono h

@[alias_in CWComplex]
/-
**Topology.RelCWComplex.closedCell_subset_skeletonLT** 是 Mathlib 中的一个定理，位于命名空间 `
Topology.RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : T2Space X]
 [inst_1 : Topology.RelCWComplex C D] (n : ℕ)   (j : Topology.RelCWComplex.cell 
C n),   Topology.RelCWComplex.closedCell n j ⊆ ↑(Topology.RelCWComplex.skeletonL
T C (↑n + 1))
参数：n : ℕ；j : Topology.RelCWComplex.cell C n；Topology.RelCWComplex.skeletonLT C (
↑n + 1)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.RelCWComplex.coe_skeletonLT`：∀ {X : Type u_1} [t : TopologicalS
pace X] [inst : T2Space X] (C : Set X) {D : Set X}   [inst_1 : Topology.RelCWCom
plex C D] (n : ℕ∞),   ↑(To…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
-/
lemma RelCWComplex.closedCell_subset_skeletonLT [RelCWComplex C D] (n : ℕ) (j : cell C n) :
    closedCell n j ⊆ skeletonLT C (n + 1) := by
  intro x xmem
  rw [coe_skeletonLT]
  right
  simp_rw [mem_iUnion, exists_prop]
  refine ⟨n, (by norm_cast; exact lt_add_one n), ⟨j,xmem⟩⟩

@[alias_in CWComplex]
/-
**Topology.RelCWComplex.closedCell_subset_skeleton** 是 Mathlib 中的一个定理，位于命名空间 `To
pology.RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : T2Space X]
 [inst_1 : Topology.RelCWComplex C D] (n : ℕ)   (j : Topology.RelCWComplex.cell 
C n), Topology.RelCWComplex.closedCell n j ⊆ ↑(Topology.RelCWComplex.skeleton C 
↑n)
参数：n : ℕ；j : Topology.RelCWComplex.cell C n；Topology.RelCWComplex.skeleton C ↑n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.RelCWComplex.closedCell_subset_skeletonLT`：∀ {X : Type u_1} [t 
: TopologicalSpace X] {C D : Set X} [inst : T2Space X] [inst_1 : Topology.RelCWC
omplex C D] (n : ℕ)   (j : Topology.RelC…
-/
lemma RelCWComplex.closedCell_subset_skeleton [RelCWComplex C D] (n : ℕ) (j : cell C n) :
    closedCell n j ⊆ skeleton C n :=
  closedCell_subset_skeletonLT n j

@[alias_in CWComplex]
/-
**Topology.RelCWComplex.openCell_subset_skeletonLT** 是 Mathlib 中的一个定理，位于命名空间 `To
pology.RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : T2Space X]
 [inst_1 : Topology.RelCWComplex C D] (n : ℕ)   (j : Topology.RelCWComplex.cell 
C n),   Topology.RelCWComplex.openCell n j ⊆ ↑(Topology.RelCWComplex.skeletonLT 
C (↑n + 1))
参数：n : ℕ；j : Topology.RelCWComplex.cell C n；Topology.RelCWComplex.skeletonLT C (
↑n + 1)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Topology.RelCWComplex.openCell_subset_closedCell`：∀ {X : Type u_1} [t : 
TopologicalSpace X] {C D : Set X} [inst : Topology.RelCWComplex C D] (n : ℕ)   (
i : Topology.RelCWComplex.cell C n), T…
· 使用定理 `Topology.RelCWComplex.closedCell_subset_skeletonLT`：∀ {X : Type u_1} [t 
: TopologicalSpace X] {C D : Set X} [inst : T2Space X] [inst_1 : Topology.RelCWC
omplex C D] (n : ℕ)   (j : Topology.RelC…
-/
lemma RelCWComplex.openCell_subset_skeletonLT [RelCWComplex C D] (n : ℕ) (j : cell C n) :
    openCell n j ⊆ skeletonLT C (n + 1) :=
  (openCell_subset_closedCell _ _).trans (closedCell_subset_skeletonLT _ _)

@[alias_in CWComplex]
/-
**Topology.RelCWComplex.openCell_subset_skeleton** 是 Mathlib 中的一个定理，位于命名空间 `Topo
logy.RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : T2Space X]
 [inst_1 : Topology.RelCWComplex C D] (n : ℕ)   (j : Topology.RelCWComplex.cell 
C n), Topology.RelCWComplex.openCell n j ⊆ ↑(Topology.RelCWComplex.skeleton C ↑n
)
参数：n : ℕ；j : Topology.RelCWComplex.cell C n；Topology.RelCWComplex.skeleton C ↑n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Topology.RelCWComplex.openCell_subset_closedCell`：∀ {X : Type u_1} [t : 
TopologicalSpace X] {C D : Set X} [inst : Topology.RelCWComplex C D] (n : ℕ)   (
i : Topology.RelCWComplex.cell C n), T…
· 使用定理 `Topology.RelCWComplex.closedCell_subset_skeleton`：∀ {X : Type u_1} [t : 
TopologicalSpace X] {C D : Set X} [inst : T2Space X] [inst_1 : Topology.RelCWCom
plex C D] (n : ℕ)   (j : Topology.RelC…
-/
lemma RelCWComplex.openCell_subset_skeleton [RelCWComplex C D] (n : ℕ) (j : cell C n) :
    openCell n j ⊆ skeleton C n :=
  (openCell_subset_closedCell _ _).trans (closedCell_subset_skeleton _ _)

@[alias_in CWComplex]
/-
**Topology.RelCWComplex.cellFrontier_subset_skeletonLT** 是 Mathlib 中的一个定理，位于命名空间
 `Topology.RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : T2Space X]
 [inst_1 : Topology.RelCWComplex C D] (n : ℕ)   (j : Topology.RelCWComplex.cell 
C n),   Topology.RelCWComplex.cellFrontier n j ⊆ ↑(Topology.RelCWComplex.skeleto
nLT C ↑n)
参数：n : ℕ；j : Topology.RelCWComplex.cell C n；Topology.RelCWComplex.skeletonLT C ↑
n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.RelCWComplex.cellFrontier_subset_base_union_finite_closedCell`：
∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : Topology.RelCWCo
mplex C D] (n : ℕ)   (i : Topology.RelCWComplex.cell C n),  …
· 使用定理 `subset_trans`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b c : α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.RelCWComplex.coe_skeletonLT`：∀ {X : Type u_1} [t : TopologicalS
pace X] [inst : T2Space X] (C : Set X) {D : Set X}   [inst_1 : Topology.RelCWCom
plex C D] (n : ℕ∞),   ↑(To…
· 使用定理 `Set.union_subset_union_right`：union_subset_union_right (s) {t₁ t₂ : Set 
α} (h : t₁ subseteq t₂) : s union t₁ subseteq s union t₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
lemma RelCWComplex.cellFrontier_subset_skeletonLT [RelCWComplex C D] (n : ℕ) (j : cell C n) :
    cellFrontier n j ⊆ skeletonLT C n := by
  obtain ⟨I, hI⟩ := cellFrontier_subset_base_union_finite_closedCell n j
  apply subset_trans hI
  rw [coe_skeletonLT]
  apply union_subset_union_right
  intro x xmem
  simp only [mem_iUnion, exists_prop] at xmem ⊢
  obtain ⟨i, iltn, j, _, xmem⟩ := xmem
  exact ⟨i, by norm_cast, j, xmem⟩

@[alias_in CWComplex]
/-
**Topology.RelCWComplex.cellFrontier_subset_skeleton** 是 Mathlib 中的一个定理，位于命名空间 `
Topology.RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : T2Space X]
 [inst_1 : Topology.RelCWComplex C D] (n : ℕ)   (j : Topology.RelCWComplex.cell 
C (n + 1)),   Topology.RelCWComplex.cellFrontier (n + 1) j ⊆ ↑(Topology.RelCWCom
plex.skeleton C ↑n)
参数：n : ℕ；j : Topology.RelCWComplex.cell C (n + 1)；n + 1；Topology.RelCWComplex.sk
eleton C ↑n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.RelCWComplex.cellFrontier_subset_skeletonLT`：∀ {X : Type u_1} [
t : TopologicalSpace X] {C D : Set X} [inst : T2Space X] [inst_1 : Topology.RelC
WComplex C D] (n : ℕ)   (j : Topology.RelC…
-/
lemma RelCWComplex.cellFrontier_subset_skeleton [RelCWComplex C D] (n : ℕ) (j : cell C (n + 1)) :
    cellFrontier (n + 1) j ⊆ skeleton C n :=
  cellFrontier_subset_skeletonLT _ _

@[alias_in CWComplex]
/-
**Topology.RelCWComplex.iUnion_cellFrontier_subset_skeletonLT** 是 Mathlib 中的一个定理
，位于命名空间 `Topology.RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : T2Space X]
 [inst_1 : Topology.RelCWComplex C D] (l : ℕ),   ⋃ j, Topology.RelCWComplex.cell
Frontier l j ⊆ ↑(Topology.RelCWComplex.skeletonLT C ↑l)
参数：l : ℕ；Topology.RelCWComplex.skeletonLT C ↑l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.iUnion_subset`：iUnion_subset {s : ι -> Set α} {t : Set α} (h : foral
l i, s i subseteq t) : ⋃ i, s i subseteq t
· 使用定理 `Topology.RelCWComplex.cellFrontier_subset_skeletonLT`：∀ {X : Type u_1} [
t : TopologicalSpace X] {C D : Set X} [inst : T2Space X] [inst_1 : Topology.RelC
WComplex C D] (n : ℕ)   (j : Topology.RelC…
-/
lemma RelCWComplex.iUnion_cellFrontier_subset_skeletonLT [RelCWComplex C D] (l : ℕ) :
    ⋃ (j : cell C l), cellFrontier l j ⊆ skeletonLT C l :=
  iUnion_subset (fun _ ↦ cellFrontier_subset_skeletonLT _ _)

@[alias_in CWComplex]
/-
**Topology.RelCWComplex.iUnion_cellFrontier_subset_skeleton** 是 Mathlib 中的一个定理，位
于命名空间 `Topology.RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : T2Space X]
 [inst_1 : Topology.RelCWComplex C D] (l : ℕ),   ⋃ j, Topology.RelCWComplex.cell
Frontier l j ⊆ ↑(Topology.RelCWComplex.skeleton C ↑l)
参数：l : ℕ；Topology.RelCWComplex.skeleton C ↑l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Topology.RelCWComplex.iUnion_cellFrontier_subset_skeletonLT`：∀ {X : Type
 u_1} [t : TopologicalSpace X] {C D : Set X} [inst : T2Space X] [inst_1 : Topolo
gy.RelCWComplex C D] (l : ℕ),   ⋃ j, Topology.Rel…
· 使用定理 `Topology.RelCWComplex.skeletonLT_mono`：∀ {X : Type u_1} [t : Topological
Space X] {C D : Set X} [inst : T2Space X] [inst_1 : Topology.RelCWComplex C D]  
 {n m : ℕ∞}, m ≤ n → ↑(Topo…
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
-/
lemma RelCWComplex.iUnion_cellFrontier_subset_skeleton [RelCWComplex C D] (l : ℕ) :
    ⋃ (j : cell C l), cellFrontier l j ⊆ skeleton C l :=
  (iUnion_cellFrontier_subset_skeletonLT l).trans (skeletonLT_mono le_self_add)

@[alias_in CWComplex]
/-
**Topology.RelCWComplex.skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ** 
是 Mathlib 中的一个定理，位于命名空间 `Topology.RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : T2Space X]
 [inst_1 : Topology.RelCWComplex C D] (n : ℕ),   ↑(Topology.RelCWComplex.skeleto
nLT C ↑n) ∪ ⋃ j, Topology.RelCWComplex.closedCell n j =     ↑(Topology.RelCWComp
lex.skeletonLT C (↑n + 1))
参数：n : ℕ；Topology.RelCWComplex.skeletonLT C ↑n；Topology.RelCWComplex.skeletonLT 
C (↑n + 1)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.RelCWComplex.coe_skeletonLT`：∀ {X : Type u_1} [t : TopologicalS
pace X] [inst : T2Space X] (C : Set X) {D : Set X}   [inst_1 : Topology.RelCWCom
plex C D] (n : ℕ∞),   ↑(To…
· 使用定理 `Set.union_assoc`：union_assoc (a b c : Set α) : a union b union c = a uni
on (b union c)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Set.biUnion_lt_succ`：biUnion_lt_succ (u : Nat -> Set α) (n : Nat) : ⋃ k 
< n + 1, u k = (⋃ k < n, u k) union u n
-/
lemma RelCWComplex.skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ [RelCWComplex C D]
    (n : ℕ) :
    (skeletonLT C n : Set X) ∪ ⋃ (j : cell C n), closedCell n j = skeletonLT C (n + 1) := by
  rw [coe_skeletonLT, coe_skeletonLT, union_assoc]
  congr
  norm_cast
  exact (biUnion_lt_succ _ _).symm

@[alias_in CWComplex]
/-
**Topology.RelCWComplex.skeleton_union_iUnion_closedCell_eq_skeleton_succ** 是 Ma
thlib 中的一个定理，位于命名空间 `Topology.RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : T2Space X]
 [inst_1 : Topology.RelCWComplex C D] (n : ℕ),   ↑(Topology.RelCWComplex.skeleto
n C ↑n) ∪ ⋃ j, Topology.RelCWComplex.closedCell (n + 1) j =     ↑(Topology.RelCW
Complex.skeleton C (↑n + 1))
参数：n : ℕ；Topology.RelCWComplex.skeleton C ↑n；n + 1；Topology.RelCWComplex.skeleto
n C (↑n + 1)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.RelCWComplex.skeletonLT_union_iUnion_closedCell_eq_skeletonLT_s
ucc`：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : T2Space X] 
[inst_1 : Topology.RelCWComplex C D] (n : ℕ),   ↑(Topology.RelCWC…
-/
lemma RelCWComplex.skeleton_union_iUnion_closedCell_eq_skeleton_succ [RelCWComplex C D] (n : ℕ) :
    (skeleton C n : Set X) ∪ ⋃ (j : cell C (n + 1)), closedCell (n + 1) j = skeleton C (n + 1) :=
  skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ _

/-- A version of the definition of `skeletonLT` with open cells. -/
/-
**Topology.RelCWComplex.iUnion_openCell_eq_skeletonLT** 是 Mathlib 中的一个定理，位于命名空间 
`Topology.RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : T2Space X]
 [inst_1 : Topology.RelCWComplex C D]   (n : ℕ∞), D ∪ ⋃ m, ⋃ (_ : ↑m < n), ⋃ j, 
Topology.RelCWComplex.openCell m j = ↑(Topology.RelCWComplex.skeletonLT C n)
参数：n : ℕ∞；_ : ↑m < n；Topology.RelCWComplex.skeletonLT C n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Topology.CWComplex.Classical.Basic.0.Topology.RelCWComp
lex.iUnion_openCell_eq_iUnion_closedCell`：∀ {X : Type u_1} [t : TopologicalSpace
 X] {C D : Set X} [inst : Topology.RelCWComplex C D] (n : ℕ∞),   D ∪ ⋃ m, ⋃ (_ :
 ↑m < n), ⋃ j, Topolog…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.RelCWComplex.coe_skeletonLT`：∀ {X : Type u_1} [t : TopologicalS
pace X] [inst : T2Space X] (C : Set X) {D : Set X}   [inst_1 : Topology.RelCWCom
plex C D] (n : ℕ∞),   ↑(To…

--- 原说明 ---
A version of the definition of `skeletonLT` with open cells.
-/
lemma RelCWComplex.iUnion_openCell_eq_skeletonLT [RelCWComplex C D] (n : ℕ∞) :
    D ∪ ⋃ (m : ℕ) (_ : m < n) (j : cell C m), openCell m j = skeletonLT C n :=
  (coe_skeletonLT C _).symm ▸ RelCWComplex.iUnion_openCell_eq_iUnion_closedCell n
/-
**Topology.CWComplex.iUnion_openCell_eq_skeletonLT** 是 Mathlib 中的一个定理，位于命名空间 `To
pology.CWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C : Set X} [inst : T2Space X] [
inst_1 : Topology.CWComplex C] (n : ℕ∞),   ⋃ m, ⋃ (_ : ↑m < n), ⋃ j, Topology.Re
lCWComplex.openCell m j = ↑(Topology.RelCWComplex.skeletonLT C n)
参数：n : ℕ∞；_ : ↑m < n；Topology.RelCWComplex.skeletonLT C n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.RelCWComplex.iUnion_openCell_eq_skeletonLT`：∀ {X : Type u_1} [t
 : TopologicalSpace X] {C D : Set X} [inst : T2Space X] [inst_1 : Topology.RelCW
Complex C D]   (n : ℕ∞), D ∪ ⋃ m, ⋃ (_ : …
· 使用定理 `Set.empty_union`：empty_union (a : Set α) : ∅ union a = a
-/
lemma CWComplex.iUnion_openCell_eq_skeletonLT [CWComplex C] (n : ℕ∞) :
    ⋃ (m : ℕ) (_ : m < n) (j : cell C m), openCell m j = skeletonLT C n := by
  rw [← RelCWComplex.iUnion_openCell_eq_skeletonLT, empty_union]
/-
**Topology.RelCWComplex.iUnion_openCell_eq_skeleton** 是 Mathlib 中的一个定理，位于命名空间 `T
opology.RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : T2Space X]
 [inst_1 : Topology.RelCWComplex C D]   (n : ℕ∞), D ∪ ⋃ m, ⋃ (_ : ↑m < n + 1), ⋃
 j, Topology.RelCWComplex.openCell m j = ↑(Topology.RelCWComplex.skeleton C n)
参数：n : ℕ∞；_ : ↑m < n + 1；Topology.RelCWComplex.skeleton C n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.RelCWComplex.iUnion_openCell_eq_skeletonLT`：∀ {X : Type u_1} [t
 : TopologicalSpace X] {C D : Set X} [inst : T2Space X] [inst_1 : Topology.RelCW
Complex C D]   (n : ℕ∞), D ∪ ⋃ m, ⋃ (_ : …
-/
lemma RelCWComplex.iUnion_openCell_eq_skeleton [RelCWComplex C D] (n : ℕ∞) :
    D ∪ ⋃ (m : ℕ) (_ : m < n + 1) (j : cell C m), openCell m j = skeleton C n :=
  iUnion_openCell_eq_skeletonLT _
/-
**Topology.CWComplex.iUnion_openCell_eq_skeleton** 是 Mathlib 中的一个定理，位于命名空间 `Topo
logy.CWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C : Set X} [inst : T2Space X] [
inst_1 : Topology.CWComplex C] (n : ℕ∞),   ⋃ m, ⋃ (_ : ↑m < n + 1), ⋃ j, Topolog
y.RelCWComplex.openCell m j = ↑(Topology.RelCWComplex.skeleton C n)
参数：n : ℕ∞；_ : ↑m < n + 1；Topology.RelCWComplex.skeleton C n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.CWComplex.iUnion_openCell_eq_skeletonLT`：∀ {X : Type u_1} [t : 
TopologicalSpace X] {C : Set X} [inst : T2Space X] [inst_1 : Topology.CWComplex 
C] (n : ℕ∞),   ⋃ m, ⋃ (_ : ↑m < n), ⋃ …
-/
lemma CWComplex.iUnion_openCell_eq_skeleton [CWComplex C] (n : ℕ∞) :
    ⋃ (m : ℕ) (_ : m < n + 1) (j : cell C m), openCell m j = skeleton C n :=
  iUnion_openCell_eq_skeletonLT _

@[alias_in CWComplex]
/-
**Topology.RelCWComplex.iUnion_skeletonLT_eq_complex** 是 Mathlib 中的一个定理，位于命名空间 `
Topology.RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : T2Space X]
 [inst_1 : Topology.RelCWComplex C D],   ⋃ n, ↑(Topology.RelCWComplex.skeletonLT
 C ↑n) = C
参数：Topology.RelCWComplex.skeletonLT C ↑n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.iUnion_subset_iff`：iUnion_subset_iff {s : ι -> Set α} {t : Set α} : 
⋃ i, s i subseteq t ↔ forall i, s i subseteq t
· 使用定理 `Topology.RelCWComplex.Subcomplex.subset_complex`：∀ {X : Type u_1} [t : T
opologicalSpace X] {C D : Set X} [inst : Topology.RelCWComplex C D]   (E : Topol
ogy.RelCWComplex.Subcomplex C), ↑E ⊆ …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.subset_iUnion_of_subset`：subset_iUnion_of_subset {s : Set α} {t : ι 
-> Set α} (i : ι) (h : s subseteq t i) : s subseteq ⋃ i, t i
· 使用定理 `Topology.RelCWComplex.Subcomplex.base_subset`：∀ {X : Type u_1} [t : Topo
logicalSpace X] {C D : Set X} [inst : Topology.RelCWComplex C D]   (E : Topology
.RelCWComplex.Subcomplex C), D ⊆ ↑…
· 使用定理 `Topology.RelCWComplex.openCell_subset_skeletonLT`：∀ {X : Type u_1} [t : 
TopologicalSpace X] {C D : Set X} [inst : T2Space X] [inst_1 : Topology.RelCWCom
plex C D] (n : ℕ)   (j : Topology.RelC…
-/
lemma RelCWComplex.iUnion_skeletonLT_eq_complex [RelCWComplex C D] :
    ⋃ (n : ℕ), skeletonLT C n = C := by
  apply subset_antisymm (iUnion_subset_iff.2 fun _ ↦ (skeletonLT C _).subset_complex)
  simp_rw [← union_iUnion_openCell_eq_complex, union_subset_iff, iUnion₂_subset_iff]
  exact ⟨subset_iUnion_of_subset 0 (skeletonLT C 0).base_subset,
    fun n i ↦ subset_iUnion_of_subset _ (openCell_subset_skeletonLT n i)⟩

@[alias_in CWComplex]
/-
**Topology.RelCWComplex.iUnion_skeleton_eq_complex** 是 Mathlib 中的一个定理，位于命名空间 `To
pology.RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : T2Space X]
 [inst_1 : Topology.RelCWComplex C D],   ⋃ n, ↑(Topology.RelCWComplex.skeleton C
 ↑n) = C
参数：Topology.RelCWComplex.skeleton C ↑n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.iUnion_subset_iff`：iUnion_subset_iff {s : ι -> Set α} {t : Set α} : 
⋃ i, s i subseteq t ↔ forall i, s i subseteq t
· 使用定理 `Topology.RelCWComplex.Subcomplex.subset_complex`：∀ {X : Type u_1} [t : T
opologicalSpace X] {C D : Set X} [inst : Topology.RelCWComplex C D]   (E : Topol
ogy.RelCWComplex.Subcomplex C), ↑E ⊆ …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.subset_iUnion_of_subset`：subset_iUnion_of_subset {s : Set α} {t : ι 
-> Set α} (i : ι) (h : s subseteq t i) : s subseteq ⋃ i, t i
· 使用定理 `Topology.RelCWComplex.Subcomplex.base_subset`：∀ {X : Type u_1} [t : Topo
logicalSpace X] {C D : Set X} [inst : Topology.RelCWComplex C D]   (E : Topology
.RelCWComplex.Subcomplex C), D ⊆ ↑…
· 使用定理 `Topology.RelCWComplex.openCell_subset_skeleton`：∀ {X : Type u_1} [t : To
pologicalSpace X] {C D : Set X} [inst : T2Space X] [inst_1 : Topology.RelCWCompl
ex C D] (n : ℕ)   (j : Topology.RelC…
-/
lemma RelCWComplex.iUnion_skeleton_eq_complex [RelCWComplex C D] :
    ⋃ (n : ℕ), skeleton C n = C := by
  apply subset_antisymm (iUnion_subset_iff.2 fun _ ↦ (skeleton C _).subset_complex)
  simp_rw [← union_iUnion_openCell_eq_complex, union_subset_iff, iUnion₂_subset_iff]
  exact ⟨subset_iUnion_of_subset 0 (skeleton C 0).base_subset,
    fun n i ↦ subset_iUnion_of_subset _ (openCell_subset_skeleton n i)⟩
/-
**Topology.RelCWComplex.mem_skeletonLT_iff** 是 Mathlib 中的一个定理，位于命名空间 `Topology.R
elCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : T2Space X]
 [inst_1 : Topology.RelCWComplex C D] {n : ℕ∞}   {x : X},   x ∈ Topology.RelCWCo
mplex.skeletonLT C n ↔ x ∈ D ∨ ∃ m, ∃ (_ : ↑m < n), ∃ j, x ∈ Topology.RelCWCompl
ex.openCell m j
参数：_ : ↑m < n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma RelCWComplex.mem_skeletonLT_iff [RelCWComplex C D] {n : ℕ∞} {x : X} :
    x ∈ skeletonLT C n ↔ x ∈ D ∨ ∃ (m : ℕ) (_ : m < n) (j : cell C m), x ∈ openCell m j := by
  simp [← SetLike.mem_coe, ← iUnion_openCell_eq_skeletonLT]
/-
**Topology.CWComplex.mem_skeletonLT_iff** 是 Mathlib 中的一个定理，位于命名空间 `Topology.CWCo
mplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C : Set X} [inst : T2Space X] [
inst_1 : Topology.CWComplex C] {n : ℕ∞}   {x : X}, x ∈ Topology.RelCWComplex.ske
letonLT C n ↔ ∃ m, ∃ (_ : ↑m < n), ∃ j, x ∈ Topology.RelCWComplex.openCell m j
参数：_ : ↑m < n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma CWComplex.mem_skeletonLT_iff [CWComplex C] {n : ℕ∞} {x : X} :
    x ∈ skeletonLT C n ↔ ∃ (m : ℕ) (_ : m < n) (j : cell C m), x ∈ openCell m j := by
  simp [← SetLike.mem_coe, ← iUnion_openCell_eq_skeletonLT]
/-
**Topology.RelCWComplex.mem_skeleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `Topology.Rel
CWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : T2Space X]
 [inst_1 : Topology.RelCWComplex C D] {n : ℕ∞}   {x : X},   x ∈ Topology.RelCWCo
mplex.skeleton C n ↔ x ∈ D ∨ ∃ m, ∃ (_ : ↑m ≤ n), ∃ j, x ∈ Topology.RelCWComplex
.openCell m j
参数：_ : ↑m ≤ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.RelCWComplex.skeleton.eq_1`：∀ {X : Type u_1} [t : TopologicalSp
ace X] [inst : T2Space X] (C : Set X) {D : Set X}   [inst_1 : Topology.RelCWComp
lex C D] (n : ℕ∞),   Topo…
· 使用定理 `Topology.RelCWComplex.mem_skeletonLT_iff`：∀ {X : Type u_1} [t : Topologi
calSpace X] {C D : Set X} [inst : T2Space X] [inst_1 : Topology.RelCWComplex C D
] {n : ℕ∞}   {x : X},   x ∈ To…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `top_add`：top_add (a : α) : ⊤ + a = ⊤
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `Order.lt_add_one_iff`：lt_add_one_iff [NoMaxOrder α] : x < y + 1 ↔ x <= y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
-/
lemma RelCWComplex.mem_skeleton_iff [RelCWComplex C D] {n : ℕ∞} {x : X} :
    x ∈ skeleton C n ↔ x ∈ D ∨ ∃ (m : ℕ) (_ : m ≤ n) (j : cell C m), x ∈ openCell m j := by
  rw [skeleton, mem_skeletonLT_iff]
  suffices ∀ (m : ℕ), m < n + 1 ↔ m ≤ n by simp_rw [this]
  intro m
  cases n
  · simp
  · rw [← Nat.cast_one, ← Nat.cast_add, Nat.cast_lt, Nat.cast_le, Order.lt_add_one_iff]
/-
**Topology.CWComplex.mem_skeleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `Topology.CWComp
lex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C : Set X} [inst : T2Space X] [
inst_1 : Topology.CWComplex C] {n : ℕ∞}   {x : X}, x ∈ Topology.RelCWComplex.ske
leton C n ↔ ∃ m, ∃ (_ : ↑m ≤ n), ∃ j, x ∈ Topology.RelCWComplex.openCell m j
参数：_ : ↑m ≤ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.RelCWComplex.mem_skeleton_iff`：∀ {X : Type u_1} [t : Topologica
lSpace X] {C D : Set X} [inst : T2Space X] [inst_1 : Topology.RelCWComplex C D] 
{n : ℕ∞}   {x : X},   x ∈ To…
· 使用定理 `Set.mem_empty_iff_false`：mem_empty_iff_false (x : α) : x in (∅ : Set α) 
↔ False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma CWComplex.mem_skeleton_iff [CWComplex C] {n : ℕ∞} {x : X} :
    x ∈ skeleton C n ↔ ∃ (m : ℕ) (_ : m ≤ n) (j : cell C m), x ∈ openCell m j := by
  rw [RelCWComplex.mem_skeleton_iff, mem_empty_iff_false, false_or]

@[deprecated (since := "2026-04-30")] alias CWComplex.exists_mem_openCell_of_mem_skeleton :=
  CWComplex.mem_skeleton_iff

/-- A skeleton and an open cell of a higher dimension are disjoint. -/
@[alias_in CWComplex]
/-
**Topology.RelCWComplex.disjoint_skeletonLT_openCell** 是 Mathlib 中的一个定理，位于命名空间 `
Topology.RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : T2Space X]
 [inst_1 : Topology.RelCWComplex C D] {n : ℕ∞}   {m : ℕ} {j : Topology.RelCWComp
lex.cell C m},   n ≤ ↑m → Disjoint (↑(Topology.RelCWComplex.skeletonLT C n)) (To
pology.RelCWComplex.openCell m j)
参数：↑(Topology.RelCWComplex.skeletonLT C n)；Topology.RelCWComplex.openCell m j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `Topology.RelCWComplex.disjointBase`：∀ {X : Type u_1} [t : TopologicalSpa
ce X] {C D : Set X} [inst : Topology.RelCWComplex C D] (n : ℕ)   (i : Topology.R
elCWComplex.cell C n), D…
· 使用定理 `Topology.RelCWComplex.disjoint_openCell_of_ne`：∀ {X : Type u_1} [t : Top
ologicalSpace X] {C D : Set X} [inst : Topology.RelCWComplex C D] {n m : ℕ}   {i
 : Topology.RelCWComplex.cell C n} …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `lt_self_iff_false`：lt_self_iff_false (x : α) : x < x ↔ False
· 使用引理 `ENat.natCast_lt_natCast`：natCast_lt_natCast {n m : Nat} : (n : Nat∞) < (
m : Nat∞) ↔ n < m
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c

--- 原说明 ---
A skeleton and an open cell of a higher dimension are disjoint.
-/
lemma RelCWComplex.disjoint_skeletonLT_openCell [RelCWComplex C D] {n : ℕ∞} {m : ℕ}
    {j : cell C m} (hnm : n ≤ m) : Disjoint (skeletonLT C n : Set X) (openCell m j) := by
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
/-
**Topology.RelCWComplex.disjoint_skeleton_openCell** 是 Mathlib 中的一个定理，位于命名空间 `To
pology.RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : T2Space X]
 [inst_1 : Topology.RelCWComplex C D] {n : ℕ∞}   {m : ℕ} {j : Topology.RelCWComp
lex.cell C m},   n < ↑m → Disjoint (↑(Topology.RelCWComplex.skeleton C n)) (Topo
logy.RelCWComplex.openCell m j)
参数：↑(Topology.RelCWComplex.skeleton C n)；Topology.RelCWComplex.openCell m j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.RelCWComplex.disjoint_skeletonLT_openCell`：∀ {X : Type u_1} [t 
: TopologicalSpace X] {C D : Set X} [inst : T2Space X] [inst_1 : Topology.RelCWC
omplex C D] {n : ℕ∞}   {m : ℕ} {j : Topo…
· 使用定理 `Order.add_one_le_of_lt`：add_one_le_of_lt (h : x < y) : x + 1 <= y

--- 原说明 ---
A skeleton and an open cell of a higher dimension are disjoint.
-/
lemma RelCWComplex.disjoint_skeleton_openCell [RelCWComplex C D] {n : ℕ∞} {m : ℕ}
    {j : cell C m} (nlem : n < m) : Disjoint (skeleton C n : Set X) (openCell m j) :=
  disjoint_skeletonLT_openCell (Order.add_one_le_of_lt nlem)

/-- A skeleton intersected with a closed cell of a higher dimension is the skeleton intersected with
the boundary of the cell. -/
@[alias_in CWComplex]
/-
**Topology.RelCWComplex.skeletonLT_inter_closedCell_eq_skeletonLT_inter_cellFron
tier** 是 Mathlib 中的一个定理，位于命名空间 `Topology.RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : T2Space X]
 [inst_1 : Topology.RelCWComplex C D] {n : ℕ∞}   {m : ℕ} {j : Topology.RelCWComp
lex.cell C m},   n ≤ ↑m →     ↑(Topology.RelCWComplex.skeletonLT C n) ∩ Topology
.RelCWComplex.closedCell m j =       ↑(Topology.RelCWComplex.skeletonLT C n) ∩ T
opology.RelCWComplex.cellFrontier m j
参数：Topology.RelCWComplex.skeletonLT C n；Topology.RelCWComplex.skeletonLT C n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.RelCWComplex.cellFrontier_union_openCell_eq_closedCell`：∀ {X : 
Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : Topology.RelCWComplex C
 D] (n : ℕ)   (i : Topology.RelCWComplex.cell C n),  …
· 使用定理 `Set.inter_union_distrib_left`：inter_union_distrib_left (s t u : Set α) :
 s inter (t union u) = s inter t union s inter u
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Disjoint.inter_eq`：∀ {α : Type u} {s t : Set α}, Disjoint s t → s ∩ t = 
∅
· 使用定理 `Topology.RelCWComplex.disjoint_skeletonLT_openCell`：∀ {X : Type u_1} [t 
: TopologicalSpace X] {C D : Set X} [inst : T2Space X] [inst_1 : Topology.RelCWC
omplex C D] {n : ℕ∞}   {m : ℕ} {j : Topo…
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
· 使用定理 `Set.inter_subset_inter_right`：inter_subset_inter_right {s t : Set α} (u 
: Set α) (H : s subseteq t) : u inter s subseteq u inter t
· 使用定理 `Topology.RelCWComplex.cellFrontier_subset_closedCell`：∀ {X : Type u_1} [
t : TopologicalSpace X] {C D : Set X} [inst : Topology.RelCWComplex C D] (n : ℕ)
   (i : Topology.RelCWComplex.cell C n), T…

--- 原说明 ---
A skeleton intersected with a closed cell of a higher dimension is the skeleton 
intersected with
the boundary of the cell.
-/
lemma RelCWComplex.skeletonLT_inter_closedCell_eq_skeletonLT_inter_cellFrontier [RelCWComplex C D]
    {n : ℕ∞} {m : ℕ} {j : cell C m} (hnm : n ≤ m) :
    (skeletonLT C n : Set X) ∩ closedCell m j = (skeletonLT C n : Set X) ∩ cellFrontier m j := by
  refine subset_antisymm ?_ (inter_subset_inter_right _ (cellFrontier_subset_closedCell _ _))
  rw [← cellFrontier_union_openCell_eq_closedCell, inter_union_distrib_left]
  apply union_subset (by rfl)
  rw [(disjoint_skeletonLT_openCell hnm).inter_eq]
  exact empty_subset _

/-- Version of `skeletonLT_inter_closedCell_eq_skeletonLT_inter_cellFrontier` using `skeleton`. -/
@[alias_in CWComplex]
/-
**Topology.RelCWComplex.skeleton_inter_closedCell_eq_skeleton_inter_cellFrontier
** 是 Mathlib 中的一个定理，位于命名空间 `Topology.RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : T2Space X]
 [inst_1 : Topology.RelCWComplex C D] {n : ℕ∞}   {m : ℕ} {j : Topology.RelCWComp
lex.cell C m},   n < ↑m →     ↑(Topology.RelCWComplex.skeleton C n) ∩ Topology.R
elCWComplex.closedCell m j =       ↑(Topology.RelCWComplex.skeleton C n) ∩ Topol
ogy.RelCWComplex.cellFrontier m j
参数：Topology.RelCWComplex.skeleton C n；Topology.RelCWComplex.skeleton C n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.RelCWComplex.skeletonLT_inter_closedCell_eq_skeletonLT_inter_ce
llFrontier`：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [inst : T2Sp
ace X] [inst_1 : Topology.RelCWComplex C D] {n : ℕ∞}   {m : ℕ} {j : Topo…
· 使用定理 `Order.add_one_le_of_lt`：add_one_le_of_lt (h : x < y) : x + 1 <= y

--- 原说明 ---
Version of `skeletonLT_inter_closedCell_eq_skeletonLT_inter_cellFrontier` using 
`skeleton`.
-/
lemma RelCWComplex.skeleton_inter_closedCell_eq_skeleton_inter_cellFrontier [RelCWComplex C D]
    {n : ℕ∞} {m : ℕ} {j : cell C m} (hnm : n < m) :
    (skeleton C n : Set X) ∩ closedCell m j = (skeleton C n : Set X) ∩ cellFrontier m j :=
  skeletonLT_inter_closedCell_eq_skeletonLT_inter_cellFrontier (Order.add_one_le_of_lt hnm)

end skeleton

/-
**Topology.RelCWComplex.disjoint_interior_base_closedCell** 是 Mathlib 中的一个定理，位于命
名空间 `Topology.RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [T2Space X] [inst 
: Topology.RelCWComplex C D] {n : ℕ}   {j : Topology.RelCWComplex.cell C n}, Dis
joint (interior D) (Topology.RelCWComplex.closedCell n j)
参数：interior D；Topology.RelCWComplex.closedCell n j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.disjoint_iff_inter_eq_empty`：disjoint_iff_inter_eq_empty : Disjoint 
s t ↔ s inter t = ∅
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `closure_inter_open_nonempty_iff`：closure_inter_open_nonempty_iff (h : Is
Open t) : (closure s inter t).Nonempty ↔ (s inter t).Nonempty
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.RelCWComplex.closure_openCell_eq_closedCell`：∀ {X : Type u_1} [
t : TopologicalSpace X] {C D : Set X} [inst : Topology.RelCWComplex C D] [T2Spac
e X] {n : ℕ}   {j : Topology.RelCWComplex.…
· 使用定理 `Topology.RelCWComplex.Subcomplex.base_subset`：∀ {X : Type u_1} [t : Topo
logicalSpace X] {C D : Set X} [inst : Topology.RelCWComplex C D]   (E : Topology
.RelCWComplex.Subcomplex C), D ⊆ ↑…
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `Disjoint.inter_eq`：∀ {α : Type u} {s t : Set α}, Disjoint s t → s ∩ t = 
∅
· 使用定理 `Topology.RelCWComplex.disjoint_skeletonLT_openCell`：∀ {X : Type u_1} [t 
: TopologicalSpace X] {C D : Set X} [inst : T2Space X] [inst_1 : Topology.RelCWC
omplex C D] {n : ℕ∞}   {m : ℕ} {j : Topo…
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
-/
lemma RelCWComplex.disjoint_interior_base_closedCell [T2Space X] [RelCWComplex C D] {n : ℕ}
    {j : cell C n} : Disjoint (interior D) (closedCell n j) := by
  rw [disjoint_iff_inter_eq_empty]
  by_contra! h
  rw [← closure_openCell_eq_closedCell, inter_comm,
    closure_inter_open_nonempty_iff isOpen_interior] at h
  rcases h with ⟨x, xmemcell, xmemD⟩
  suffices x ∈ (skeletonLT C 0 : Set X) ∩ openCell n j by
    rwa [(disjoint_skeletonLT_openCell n.cast_nonneg').inter_eq] at this
  exact ⟨(skeletonLT C 0).base_subset (interior_subset xmemD), xmemcell⟩
/-
**Topology.RelCWComplex.disjoint_interior_base_iUnion_closedCell** 是 Mathlib 中的一
个定理，位于命名空间 `Topology.RelCWComplex`。
形式化陈述：∀ {X : Type u_1} [t : TopologicalSpace X] {C D : Set X} [T2Space X] [inst 
: Topology.RelCWComplex C D],   Disjoint (interior D) (⋃ n, ⋃ j, Topology.RelCWC
omplex.closedCell n j)
参数：interior D；⋃ n, ⋃ j, Topology.RelCWComplex.closedCell n j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.inter_iUnion`：inter_iUnion (s : Set β) (t : ι -> Set β) : (s inter ⋃
 i, t i) = ⋃ i, s inter t i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Disjoint.inter_eq`：∀ {α : Type u} {s t : Set α}, Disjoint s t → s ∩ t = 
∅
· 使用定理 `Topology.RelCWComplex.disjoint_interior_base_closedCell`：∀ {X : Type u_1
} [t : TopologicalSpace X] {C D : Set X} [T2Space X] [inst : Topology.RelCWCompl
ex C D] {n : ℕ}   {j : Topology.RelCWComplex.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.iUnion_empty`：iUnion_empty : (⋃ _ : ι, ∅ : Set α) = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma RelCWComplex.disjoint_interior_base_iUnion_closedCell [T2Space X] [RelCWComplex C D] :
    Disjoint (interior D) (⋃ (n : ℕ) (j : cell C n), closedCell n j) := by
  simp_rw [disjoint_iff_inter_eq_empty, inter_iUnion, disjoint_interior_base_closedCell.inter_eq,
    iUnion_empty]

set_option backward.isDefEq.respectTransparency.types false in
/-- A closed discrete subset of a space is a CW complex. -/
@[reducible, simps -isSimp]
/-
**Topology.CWComplex.OfDiscreteClosed** 是 Mathlib 中的一个定义，位于命名空间 `Topology.CWComp
lex`。
形式化陈述：{X : Type u_1} → [t : TopologicalSpace X] → {D : Set X} → IsDiscrete D → I
sClosed D → Topology.CWComplex D
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_of_subset_discrete_closed`：isClosed_of_subset_discrete_closed {
s t : Set X} (sd : s subseteq t) (ht : IsDiscrete t) (tc : IsClosed t) : IsClose
d s

--- 原说明 ---
A closed discrete subset of a space is a CW complex.
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
    apply subset_antisymm (iUnion₂_subset_iff.mpr fun n ↦ by cases n <;> simp)
    intro x xD
    simp only [mem_iUnion, mem_image, mem_closedBall, dist_zero_right]
    refine ⟨0, ?_⟩
    simpa [-Matrix.zero_empty]

/-- A discrete space is a CW complex. -/
/-
**Topology.CWComplex.ofDiscreteTopology** 是 Mathlib 中的一个定义，位于命名空间 `Topology.CWCo
mplex`。
形式化陈述：{X : Type u_2} → [inst : TopologicalSpace X] → [DiscreteTopology X] → Topo
logy.CWComplex Set.univ
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `IsDiscrete.univ`：IsDiscrete.univ [DiscreteTopology X] : IsDiscrete (Set.
univ : Set X)
· 使用定理 `isClosed_univ`：isClosed_univ : IsClosed (univ : Set X)

--- 原说明 ---
A discrete space is a CW complex.
-/
instance CWComplex.ofDiscreteTopology {X : Type*} [TopologicalSpace X] [DiscreteTopology X] :
    CWComplex (univ : Set X) :=
  CWComplex.OfDiscreteClosed IsDiscrete.univ isClosed_univ

end Topology

