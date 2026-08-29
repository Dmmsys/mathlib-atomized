/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
module

public import Mathlib.Data.ENNReal.Real
public import Mathlib.Tactic.Bound.Attribute
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Bornology.Basic
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.UniformSpace.Basic

/-!
## Pseudo-metric spaces

This file defines pseudo-metric spaces: these differ from metric spaces by not imposing the
condition `dist x y = 0 → x = y`.
Many definitions and theorems expected on (pseudo-)metric spaces are already introduced on uniform
spaces and topological spaces. For example: open and closed sets, compactness, completeness,
continuity and uniform continuity.

## Main definitions

* `Dist α`: Endows a space `α` with a function `dist a b`.
* `PseudoMetricSpace α`: A space endowed with a distance function, which can
  be zero even if the two elements are non-equal.
* `PseudoMetricSpace.ofDistTopology`: Construct a pseudometric space from a compatible topology
  and distance.
* `Metric.ball x ε`: The set of all points `y` with `dist y x < ε`.
* `Metric.closedBall x ε`: The set of all points `y` with `dist y x ≤ ε`.
* `Metric.sphere x ε`: The set of all points `y` with `dist y x = ε`.
* `nndist a b`: `dist` as a function to the non-negative reals.
* `Metric.Bounded s`: Whether a subset of a `PseudoMetricSpace` is bounded.
* `PseudoMetricSpace.replaceUniformity`, `PseudoMetricSpace.replaceTopology`,
  `PseudoMetricSpace.replaceBornology`: Tools to construct a pseudometric space on a type with a
  pre-existing uniformity, topology, or bornology in such a way that the definitional equalities
  for these structures are preserved; these are essential to avoid type class synthesis issues.
* `Real.pseudoMetricSpace`: The pseudometric space structure on `ℝ` with
  `dist x y = |x - y|`.
* `MetricSpace α`: A `PseudoMetricSpace` with the guarantee `dist x y = 0 → x = y`.

## Main results

* `PseudoMetricSpace.ext`: extensionality for pseudometric space structures.
* `dist_triangle`, `dist_nonneg`, `nndist_triangle`: core distance inequalities.
* `Metric.mk_uniformity_basis`, `Metric.mk_uniformity_basis_le`: tools for constructing bases for
  the uniformity, with `Metric.nhds_basis_ball` and `Metric.nhds_basis_closedBall` as basic
  neighborhood-basis corollaries.
* `Metric.tendsto_nhds_nhds`, `Metric.continuous_iff`: epsilon-delta characterizations of
  convergence and continuity.
* `Metric.mem_closure_iff`, `Metric.dense_iff`: characterizations of closure and dense sets.

## Tags

pseudometric space, dist
-/

@[expose] public section

assert_not_exists compactSpace_uniformity

open Set Filter TopologicalSpace Bornology
open scoped ENNReal NNReal Uniformity Topology

universe u v w

variable {α : Type u} {β : Type v} {X ι : Type*}

/--
theorem `UniformSpace.ofDist_aux` / 定理 `UniformSpace.ofDist_aux`

English:
theorem UniformSpace.ofDist_aux
  given: (ε : Real) (hε : 0 < ε)
  statement: exists δ > (0 : Real), forall x < δ, forall y < δ, x + y < ε
  proof: ⟨ε / 2, half_pos hε, fun _x hx _y hy => add_halves ε ▸ add_lt_add hx hy⟩

中文:
定理 UniformSpace.ofDist_aux
  条件: (ε : 实数) (hε : 0 < ε)
  结论: 存在 δ > (0 : 实数), 对任意 x < δ, 对任意 y < δ, x + y < ε
  证明: ⟨ε / 2, half_pos hε, fun _x hx _y hy => add_halves ε ▸ add_lt_add hx hy⟩

Depends on / 依赖: add_halves, add_lt_add, half_pos
-/
theorem UniformSpace.ofDist_aux (ε : Real) (hε : 0 < ε) : exists δ > (0 : Real), forall x < δ, forall y < δ, x + y < ε :=
  ⟨ε / 2, half_pos hε, fun _x hx _y hy => add_halves ε ▸ add_lt_add hx hy⟩

/-- Construct a uniform structure from a distance function and metric space axioms -/
@[instance_reducible]
/--
Definition of `UniformSpace.ofDist` / `UniformSpace.ofDist` 的定义

English:
definition UniformSpace.ofDist
  signature: (dist : α -> α -> Real) (dist_self : forall x : α, dist x x = 0)
  body: .ofFun dist dist_self dist_comm dist_triangle ofDist_aux

中文:
定义 UniformSpace.ofDist
  签名: (dist : α -> α -> 实数) (dist_self : 对任意 x : α, dist x x = 0)
  定义体: .ofFun dist dist_self dist_comm dist_triangle ofDist_aux

Depends on / 依赖: dist_comm, dist_self, dist_triangle, ofDist_aux
-/
def UniformSpace.ofDist (dist : α -> α -> Real) (dist_self : forall x : α, dist x x = 0)
    (dist_comm : forall x y : α, dist x y = dist y x)
    (dist_triangle : forall x y z : α, dist x z <= dist x y + dist y z) : UniformSpace α :=
  .ofFun dist dist_self dist_comm dist_triangle ofDist_aux

/--
Definition of `Bornology.ofDist` / `Bornology.ofDist` 的定义

English:
abbreviation Bornology.ofDist
  signature: {α : Type*} (dist : α -> α -> Real) (dist_comm : forall x y, dist x y = dist y x)
  body: Bornology.ofBounded { s : Set α | exists C, forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> dist x y <= C }
    ⟨0, fun _ hx _ => hx.elim⟩ (fun _ ⟨c, hc⟩ _ h => ⟨c, fun _ hx _ hy => hc (h hx) (h hy)⟩)
    (fun s hs t ht => by
      rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
      · rwa [empty_unio

中文:
缩写 Bornology.ofDist
  签名: {α : 类型} (dist : α -> α -> 实数) (dist_comm : 对任意 x y, dist x y = dist y x)
  定义体: Bornology.ofBounded { s : Set α | exists C, forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> dist x y <= C }
    ⟨0, fun _ hx _ => hx.elim⟩ (fun _ ⟨c, hc⟩ _ h => ⟨c, fun _ hx _ hy => hc (h hx) (h hy)⟩)
    (fun s hs t ht => by
      rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
      · rwa [empty_unio

Depends on / 依赖: Bornology, Bornology.ofBounded, dist_triangle, empty_union, eq_empty_or_nonempty, hx.elim, ofBounded, rsuffices, s.eq_empty_or_nonempty, t.eq_empty_or_nonempty, union_empty
-/
abbrev Bornology.ofDist {α : Type*} (dist : α -> α -> Real) (dist_comm : forall x y, dist x y = dist y x)
    (dist_triangle : forall x y z, dist x z <= dist x y + dist y z) : Bornology α :=
  Bornology.ofBounded { s : Set α | exists C, forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> dist x y <= C }
    ⟨0, fun _ hx _ => hx.elim⟩ (fun _ ⟨c, hc⟩ _ h => ⟨c, fun _ hx _ hy => hc (h hx) (h hy)⟩)
    (fun s hs t ht => by
      rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
      · rwa [empty_union]
      rcases t.eq_empty_or_nonempty with rfl | ⟨y, hy⟩
      · rwa [union_empty]
      rsuffices ⟨C, hC⟩ : exists C, forall z in s union t, dist x z <= C
      · refine ⟨C + C, fun a ha b hb => (dist_triangle a x b).trans ?_⟩
        simpa only [dist_comm] using add_le_add (hC _ ha) (hC _ hb)
      rcases hs with ⟨Cs, hs⟩; rcases ht with ⟨Ct, ht⟩
      refine ⟨max Cs (dist x y + Ct), fun z hz => hz.elim
        (fun hz => (hs hx hz).trans (le_max_left _ _))
        (fun hz => (dist_triangle x y z).trans <|
          (add_le_add le_rfl (ht hy hz)).trans (le_max_right _ _))⟩)
fun z => ⟨dist z z, forall_eq.2 forall_eq.2 le_rfl⟩

/-- The distance function (given an ambient metric space on `α`), which returns
  a nonnegative real number `dist x y` given `x y : α`. -/
@[ext]
/--
Definition of `Dist` / `Dist` 的定义

English:
class Dist
  parameters: (α : Type*)
  axioms and operations (1):
    - dist : α -> α -> Real

中文:
类 Dist
  参数: (α : 类型)
  公理与运算 (1 个):
    - dist : α -> α -> 实数

Depends on / 依赖: dist_comm, dist_self, dist_triangle, nonneg_of_mul_nonneg_right, two_mul, two_pos
-/
class Dist (α : Type*) where
  /-- Distance between two points -/
  dist : α -> α -> Real

export Dist (dist)

-- the uniform structure and the emetric space structure are embedded in the metric space structure
-- to avoid instance diamond issues. See Note [forgetful inheritance].
set_option backward.privateInPublic true in
/--
theorem `dist_nonneg'` / 定理 `dist_nonneg'`

English:
theorem dist_nonneg'
  statement: {α} {x y : α} (dist : α -> α -> Real)
  proof: have : 0 <= 2 * dist x y :=
    calc 0 = dist x x := (dist_self _).symm
    _ <= dist x y + dist y x := dist_triangle _ _ _
    _ = 2 * dist x y := by rw [two_mul, dist_comm]
  nonneg_of_mul_nonneg_right this two_pos

中文:
定理 dist_nonneg'
  结论: {α} {x y : α} (dist : α -> α -> 实数)
  证明: have : 0 <= 2 * dist x y :=
    calc 0 = dist x x := (dist_self _).symm
    _ <= dist x y + dist y x := dist_triangle _ _ _
    _ = 2 * dist x y := by rw [two_mul, dist_comm]
  nonneg_of_mul_nonneg_right this two_pos
-/
private theorem dist_nonneg' {α} {x y : α} (dist : α -> α -> Real)
    (dist_self : forall x : α, dist x x = 0) (dist_comm : forall x y : α, dist x y = dist y x)
    (dist_triangle : forall x y z : α, dist x z <= dist x y + dist y z) : 0 <= dist x y :=
  have : 0 <= 2 * dist x y :=
    calc 0 = dist x x := (dist_self _).symm
    _ <= dist x y + dist y x := dist_triangle _ _ _
    _ = 2 * dist x y := by rw [two_mul, dist_comm]
  nonneg_of_mul_nonneg_right this two_pos

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `PseudoMetricSpace` / `PseudoMetricSpace` 的定义

English:
class PseudoMetricSpace
  parameters: (α : Type u)
  extends: Dist α
  axioms and operations (9):
    - dist_self : forall x : α, dist x x = 0
    - dist_comm : forall x y : α, dist x y = dist y x
    - dist_triangle : forall x y z : α, dist x z <= dist x y + dist y z
    - edist : α -> α -> Real>=0∞  [default: fun x y => ENNReal.ofNNReal (.mk (dist x y) (dist_nonneg' _ ]
    - edist_dist : forall x y : α, edist x y = ENNReal.ofReal (dist x y)  [default: by intro x y; exact ENNReal.coe_nnreal_eq _]
    - toUniformSpace : UniformSpace α  [default: .ofDist dist dist_self dist_comm dist_triangle]
    - uniformity_dist : 𝓤 α = ⨅ ε > 0, 𝓟 { p : α × α | dist p.1 p.2 < ε }  [default: by intros; rfl]
    - toBornology : Bornology α  [default: Bornology.ofDist dist dist_comm dist_triangle]
    - cobounded_sets : (Bornology.cobounded α).sets = { s | exists C : Real, forall x in sᶜ, forall y in sᶜ, dist x y <= C }  [default: by intros; rfl]

中文:
类 PseudoMetricSpace
  参数: (α : 类型u)
  继承: Dist α
  公理与运算 (9 个):
    - dist_self : 对任意 x : α, dist x x = 0
    - dist_comm : 对任意 x y : α, dist x y = dist y x
    - dist_triangle : 对任意 x y z : α, dist x z <= dist x y + dist y z
    - edist : α -> α -> 实数>=0∞  [默认: fun x y => ENNReal.ofNNReal (.mk (dist x y) (dist_nonneg' _ ]
    - edist_dist : 对任意 x y : α, edist x y = ENN实数.of实数 (dist x y)  [默认: by intro x y; exact ENNReal.coe_nnreal_eq _]
    - toUniformSpace : UniformSpace α  [默认: .ofDist dist dist_self dist_comm dist_triangle]
    - uniformity_dist : 𝓤 α = ⨅ ε > 0, 𝓟 { p : α × α | dist p.1 p.2 < ε }  [默认: by intros; rfl]
    - toBornology : Bornology α  [默认: Bornology.ofDist dist dist_comm dist_triangle]
    - cobounded_sets : (Bornology.cobounded α).sets = { s | 存在 C : 实数, 对任意 x in sᶜ, 对任意 y in sᶜ, dist x y <= C }  [默认: by intros; rfl]

Depends on / 依赖: ENNReal, ENNReal.ofNNReal, dist_nonneg, ofNNReal
-/
class PseudoMetricSpace (α : Type u) : Type u extends Dist α where
  dist_self : forall x : α, dist x x = 0
  dist_comm : forall x y : α, dist x y = dist y x
  dist_triangle : forall x y z : α, dist x z <= dist x y + dist y z
  /-- Extended distance between two points -/
  edist : α -> α -> Real>=0∞ := fun x y => ENNReal.ofNNReal (.mk (dist x y) (dist_nonneg' _ ‹_› ‹_› ‹_›))
  edist_dist : forall x y : α, edist x y = ENNReal.ofReal (dist x y) := by
    intro x y; exact ENNReal.coe_nnreal_eq _
  toUniformSpace : UniformSpace α := .ofDist dist dist_self dist_comm dist_triangle
  uniformity_dist : 𝓤 α = ⨅ ε > 0, 𝓟 { p : α × α | dist p.1 p.2 < ε } := by intros; rfl
  toBornology : Bornology α := Bornology.ofDist dist dist_comm dist_triangle
  cobounded_sets : (Bornology.cobounded α).sets =
    { s | exists C : Real, forall x in sᶜ, forall y in sᶜ, dist x y <= C } := by intros; rfl

/-- Two pseudometric space structures with the same distance function coincide. -/
@[ext]
/--
theorem `PseudoMetricSpace.ext` / 定理 `PseudoMetricSpace.ext`

English:
theorem PseudoMetricSpace.ext
  statement: {α : Type*} {m m' : PseudoMetricSpace α}
  proof: by
  let d := m.toDist
  obtain ⟨_, _, _, _, hed, _, hU, _, hB⟩ := m
  let d' := m'.toDist
  obtain ⟨_, _, _, _, hed', _, hU', _, hB'⟩ := m'
  obtain rfl : d = d' := h
  congr
  · ext x y : 2
    rw [hed]; rw [hed']
  · exact UniformSpace.ext (hU.trans hU'.symm)
  · ext : 2
    rw [← Filter.mem_sets

中文:
定理 PseudoMetricSpace.ext
  结论: {α : 类型} {m m' : PseudoMetricSpace α}
  证明: by
  let d := m.toDist
  obtain ⟨_, _, _, _, hed, _, hU, _, hB⟩ := m
  let d' := m'.toDist
  obtain ⟨_, _, _, _, hed', _, hU', _, hB'⟩ := m'
  obtain rfl : d = d' := h
  congr
  · ext x y : 2
    rw [hed]; rw [hed']
  · exact UniformSpace.ext (hU.trans hU'.symm)
  · ext : 2
    rw [← Filter.mem_sets

Depends on / 依赖: Filter, Filter.mem_sets, UniformSpace, UniformSpace.ext, hU.trans, m.toDist, mem_sets, toDist
-/
theorem PseudoMetricSpace.ext {α : Type*} {m m' : PseudoMetricSpace α}
    (h : m.toDist = m'.toDist) : m = m' := by
  let d := m.toDist
  obtain ⟨_, _, _, _, hed, _, hU, _, hB⟩ := m
  let d' := m'.toDist
  obtain ⟨_, _, _, _, hed', _, hU', _, hB'⟩ := m'
  obtain rfl : d = d' := h
  congr
  · ext x y : 2
    rw [hed]; rw [hed']
  · exact UniformSpace.ext (hU.trans hU'.symm)
  · ext : 2
    rw [← Filter.mem_sets]; rw [← Filter.mem_sets]; rw [hB]; rw [hB']

variable [PseudoMetricSpace α]

attribute [instance_reducible, instance]
  PseudoMetricSpace.toUniformSpace PseudoMetricSpace.toBornology

-- see Note [lower instance priority]
instance (priority := 200) PseudoMetricSpace.toEDist : EDist α :=
  ⟨PseudoMetricSpace.edist⟩

/-- Construct a pseudo-metric space structure whose underlying topological space structure
(definitionally) agrees which a pre-existing topology which is compatible with a given distance
function. -/
@[instance_reducible]
/--
Definition of `PseudoMetricSpace.ofDistTopology` / `PseudoMetricSpace.ofDistTopology` 的定义

English:
definition PseudoMetricSpace.ofDistTopology
  signature: {α : Type u} [TopologicalSpace α] (dist : α -> α -> Real)
  body: { dist := dist
    dist_self := dist_self
    dist_comm := dist_comm
    dist_triangle := dist_triangle
    toUniformSpace :=
(UniformSpace.ofDist dist dist_self dist_comm dist_triangle).replaceTopology
TopologicalSpace.ext_iff.2 fun s => (H s).trans forall₂_congr fun x _ =>
          ((UniformSpace

中文:
定义 PseudoMetricSpace.ofDistTopology
  签名: {α : 类型u} [TopologicalSpace α] (dist : α -> α -> 实数)
  定义体: { dist := dist
    dist_self := dist_self
    dist_comm := dist_comm
    dist_triangle := dist_triangle
    toUniformSpace :=
(UniformSpace.ofDist dist dist_self dist_comm dist_triangle).replaceTopology
TopologicalSpace.ext_iff.2 fun s => (H s).trans forall₂_congr fun x _ =>
          ((UniformSpace

Depends on / 依赖: Bornology, Bornology.ofDist, Prod.mk, TopologicalSpace, TopologicalSpace.ext_iff, UniformSpace, UniformSpace.hasBasis_ofFun, UniformSpace.ofDist, UniformSpace.ofDist_aux, cobound, dist_comm, dist_self, dist_triangle, exists_gt, ext_iff, hasBasis_ofFun, mem_iff, mem_iff.symm, ofDist, ofDist_aux
-/
def PseudoMetricSpace.ofDistTopology {α : Type u} [TopologicalSpace α] (dist : α -> α -> Real)
    (dist_self : forall x : α, dist x x = 0) (dist_comm : forall x y : α, dist x y = dist y x)
    (dist_triangle : forall x y z : α, dist x z <= dist x y + dist y z)
    (H : forall s : Set α, IsOpen s ↔ forall x in s, exists ε > 0, forall y, dist x y < ε -> y in s) :
    PseudoMetricSpace α :=
  { dist := dist
    dist_self := dist_self
    dist_comm := dist_comm
    dist_triangle := dist_triangle
    toUniformSpace :=
(UniformSpace.ofDist dist dist_self dist_comm dist_triangle).replaceTopology
TopologicalSpace.ext_iff.2 fun s => (H s).trans forall₂_congr fun x _ =>
          ((UniformSpace.hasBasis_ofFun (exists_gt (0 : Real)) dist dist_self dist_comm dist_triangle
            UniformSpace.ofDist_aux).comap (Prod.mk x)).mem_iff.symm
    uniformity_dist := rfl
    toBornology := Bornology.ofDist dist dist_comm dist_triangle
    cobounded_sets := rfl }

@[simp]
/--
theorem `dist_self` / 定理 `dist_self`

English:
theorem dist_self
  given: (x : α)
  statement: dist x x = 0
  proof: PseudoMetricSpace.dist_self x

中文:
定理 dist_self
  条件: (x : α)
  结论: dist x x = 0
  证明: PseudoMetricSpace.dist_self x

Depends on / 依赖: PseudoMetricSpace, PseudoMetricSpace.dist_self, dist_self
-/
theorem dist_self (x : α) : dist x x = 0 :=
  PseudoMetricSpace.dist_self x

/--
theorem `dist_comm` / 定理 `dist_comm`

English:
theorem dist_comm
  given: (x y : α)
  statement: dist x y = dist y x
  proof: PseudoMetricSpace.dist_comm x y

中文:
定理 dist_comm
  条件: (x y : α)
  结论: dist x y = dist y x
  证明: PseudoMetricSpace.dist_comm x y

Depends on / 依赖: PseudoMetricSpace, PseudoMetricSpace.dist_comm, dist_comm
-/
theorem dist_comm (x y : α) : dist x y = dist y x :=
  PseudoMetricSpace.dist_comm x y

/--
theorem `edist_dist` / 定理 `edist_dist`

English:
theorem edist_dist
  given: (x y : α)
  statement: edist x y = ENNReal.ofReal (dist x y)
  proof: PseudoMetricSpace.edist_dist x y

@[bound]

中文:
定理 edist_dist
  条件: (x y : α)
  结论: edist x y = ENN实数.of实数 (dist x y)
  证明: PseudoMetricSpace.edist_dist x y

@[bound]

Depends on / 依赖: PseudoMetricSpace, PseudoMetricSpace.edist_dist, edist_dist
-/
theorem edist_dist (x y : α) : edist x y = ENNReal.ofReal (dist x y) :=
  PseudoMetricSpace.edist_dist x y

@[bound]
/--
theorem `dist_triangle` / 定理 `dist_triangle`

English:
theorem dist_triangle
  given: (x y z : α)
  statement: dist x z <= dist x y + dist y z
  proof: PseudoMetricSpace.dist_triangle x y z

中文:
定理 dist_triangle
  条件: (x y z : α)
  结论: dist x z <= dist x y + dist y z
  证明: PseudoMetricSpace.dist_triangle x y z

Depends on / 依赖: PseudoMetricSpace, PseudoMetricSpace.dist_triangle, dist_triangle
-/
theorem dist_triangle (x y z : α) : dist x z <= dist x y + dist y z :=
  PseudoMetricSpace.dist_triangle x y z

/--
theorem `dist_triangle_left` / 定理 `dist_triangle_left`

English:
theorem dist_triangle_left
  given: (x y z : α)
  statement: dist x y <= dist z x + dist z y
  proof: by
  rw [dist_comm z]; apply dist_triangle

中文:
定理 dist_triangle_left
  条件: (x y z : α)
  结论: dist x y <= dist z x + dist z y
  证明: by
  rw [dist_comm z]; apply dist_triangle

Depends on / 依赖: dist_comm, dist_triangle
-/
theorem dist_triangle_left (x y z : α) : dist x y <= dist z x + dist z y := by
  rw [dist_comm z]; apply dist_triangle

/--
theorem `dist_triangle_right` / 定理 `dist_triangle_right`

English:
theorem dist_triangle_right
  given: (x y z : α)
  statement: dist x y <= dist x z + dist y z
  proof: by
  rw [dist_comm y]; apply dist_triangle

中文:
定理 dist_triangle_right
  条件: (x y z : α)
  结论: dist x y <= dist x z + dist y z
  证明: by
  rw [dist_comm y]; apply dist_triangle

Depends on / 依赖: dist_comm, dist_triangle
-/
theorem dist_triangle_right (x y z : α) : dist x y <= dist x z + dist y z := by
  rw [dist_comm y]; apply dist_triangle

/--
theorem `dist_triangle4` / 定理 `dist_triangle4`

English:
theorem dist_triangle4
  given: (x y z w : α)
  statement: dist x w <= dist x y + dist y z + dist z w
  proof: calc
    dist x w <= dist x z + dist z w := dist_triangle x z w
    _ <= dist x y + dist y z + dist z w := by gcongr; apply dist_triangle x y z

中文:
定理 dist_triangle4
  条件: (x y z w : α)
  结论: dist x w <= dist x y + dist y z + dist z w
  证明: calc
    dist x w <= dist x z + dist z w := dist_triangle x z w
    _ <= dist x y + dist y z + dist z w := by gcongr; apply dist_triangle x y z

Depends on / 依赖: dist_triangle
-/
theorem dist_triangle4 (x y z w : α) : dist x w <= dist x y + dist y z + dist z w :=
  calc
    dist x w <= dist x z + dist z w := dist_triangle x z w
    _ <= dist x y + dist y z + dist z w := by gcongr; apply dist_triangle x y z

/--
theorem `dist_triangle4_left` / 定理 `dist_triangle4_left`

English:
theorem dist_triangle4_left
  given: (x₁ y₁ x₂ y₂ : α)
  proof: by
  rw [add_left_comm]; rw [dist_comm x₁]; rw [← add_assoc]
  apply dist_triangle4

中文:
定理 dist_triangle4_left
  条件: (x₁ y₁ x₂ y₂ : α)
  证明: by
  rw [add_left_comm]; rw [dist_comm x₁]; rw [← add_assoc]
  apply dist_triangle4

Depends on / 依赖: add_assoc, add_left_comm, dist_comm, dist_triangle4
-/
theorem dist_triangle4_left (x₁ y₁ x₂ y₂ : α) :
    dist x₂ y₂ <= dist x₁ y₁ + (dist x₁ x₂ + dist y₁ y₂) := by
  rw [add_left_comm]; rw [dist_comm x₁]; rw [← add_assoc]
  apply dist_triangle4

/--
theorem `dist_triangle4_right` / 定理 `dist_triangle4_right`

English:
theorem dist_triangle4_right
  given: (x₁ y₁ x₂ y₂ : α)
  proof: by
  rw [add_right_comm]; rw [dist_comm y₁]
  apply dist_triangle4

中文:
定理 dist_triangle4_right
  条件: (x₁ y₁ x₂ y₂ : α)
  证明: by
  rw [add_right_comm]; rw [dist_comm y₁]
  apply dist_triangle4

Depends on / 依赖: add_right_comm, dist_comm, dist_triangle4
-/
theorem dist_triangle4_right (x₁ y₁ x₂ y₂ : α) :
    dist x₁ y₁ <= dist x₁ x₂ + dist y₁ y₂ + dist x₂ y₂ := by
  rw [add_right_comm]; rw [dist_comm y₁]
  apply dist_triangle4

/--
theorem `dist_triangle8` / 定理 `dist_triangle8`

English:
theorem dist_triangle8
  given: (a b c d e f g h : α)
  statement: dist a h <= dist a b + dist b c + dist c d
  proof: by
  apply le_trans (dist_triangle4 a f g h)
  gcongr
  apply le_trans (dist_triangle4 a d e f)
  gcongr
  exact dist_triangle4 a b c d

中文:
定理 dist_triangle8
  条件: (a b c d e f g h : α)
  结论: dist a h <= dist a b + dist b c + dist c d
  证明: by
  apply le_trans (dist_triangle4 a f g h)
  gcongr
  apply le_trans (dist_triangle4 a d e f)
  gcongr
  exact dist_triangle4 a b c d

Depends on / 依赖: dist_triangle4, le_trans
-/
theorem dist_triangle8 (a b c d e f g h : α) : dist a h <= dist a b + dist b c + dist c d
    + dist d e + dist e f + dist f g + dist g h := by
  apply le_trans (dist_triangle4 a f g h)
  gcongr
  apply le_trans (dist_triangle4 a d e f)
  gcongr
  exact dist_triangle4 a b c d

/--
theorem `swap_dist` / 定理 `swap_dist`

English:
theorem swap_dist
  statement: Function.swap (@dist α _) = dist
  proof: by funext x y; exact dist_comm _ _

中文:
定理 swap_dist
  结论: Function.swap (@dist α _) = dist
  证明: by funext x y; exact dist_comm _ _

Depends on / 依赖: dist_comm
-/
theorem swap_dist : Function.swap (@dist α _) = dist := by funext x y; exact dist_comm _ _

/--
theorem `abs_dist_sub_le` / 定理 `abs_dist_sub_le`

English:
theorem abs_dist_sub_le
  given: (x y z : α)
  statement: |dist x z - dist y z| <= dist x y
  proof: abs_sub_le_iff.2
    ⟨sub_le_iff_le_add.2 (dist_triangle _ _ _), sub_le_iff_le_add.2 (dist_triangle_left _ _ _)⟩

@[simp, bound]

中文:
定理 abs_dist_sub_le
  条件: (x y z : α)
  结论: |dist x z - dist y z| <= dist x y
  证明: abs_sub_le_iff.2
    ⟨sub_le_iff_le_add.2 (dist_triangle _ _ _), sub_le_iff_le_add.2 (dist_triangle_left _ _ _)⟩

@[simp, bound]

Depends on / 依赖: abs_sub_le_iff, dist_triangle, dist_triangle_left, sub_le_iff_le_add
-/
theorem abs_dist_sub_le (x y z : α) : |dist x z - dist y z| <= dist x y :=
  abs_sub_le_iff.2
    ⟨sub_le_iff_le_add.2 (dist_triangle _ _ _), sub_le_iff_le_add.2 (dist_triangle_left _ _ _)⟩

@[simp, bound]
/--
theorem `dist_nonneg` / 定理 `dist_nonneg`

English:
theorem dist_nonneg
  given: {x y : α}
  statement: 0 <= dist x y
  proof: dist_nonneg' dist dist_self dist_comm dist_triangle

中文:
定理 dist_nonneg
  条件: {x y : α}
  结论: 0 <= dist x y
  证明: dist_nonneg' dist dist_self dist_comm dist_triangle

Depends on / 依赖: dist_comm, dist_nonneg, dist_self, dist_triangle
-/
theorem dist_nonneg {x y : α} : 0 <= dist x y :=
  dist_nonneg' dist dist_self dist_comm dist_triangle

namespace Mathlib.Meta.Positivity

open Lean Meta Qq Function

/-- Extension for the `positivity` tactic: distances are nonnegative. -/
@[positivity Dist.dist _ _]
meta def evalDist : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(Real), ~q(@Dist.dist $β $inst $a $b) =>
    let _inst ← synthInstanceQ q(PseudoMetricSpace $β)
    assertInstancesCommute
    pure (.nonnegative q(dist_nonneg))
  | _, _, _ => throwError "not dist"

end Mathlib.Meta.Positivity

example {x y : α} : 0 <= dist x y := by positivity

/--
theorem `abs_dist` / 定理 `abs_dist`

English:
theorem abs_dist
  given: {a b : α}
  statement: |dist a b| = dist a b
  proof: abs_of_nonneg dist_nonneg

中文:
定理 abs_dist
  条件: {a b : α}
  结论: |dist a b| = dist a b
  证明: abs_of_nonneg dist_nonneg
-/
@[simp] theorem abs_dist {a b : α} : |dist a b| = dist a b := abs_of_nonneg dist_nonneg

/--
Definition of `NNDist` / `NNDist` 的定义

English:
class NNDist
  parameters: (α : Type*)
  axioms and operations (1):
    - nndist : α -> α -> Real>=0

中文:
类 NNDist
  参数: (α : 类型)
  公理与运算 (1 个):
    - nndist : α -> α -> 实数>=0
-/
class NNDist (α : Type*) where
  /-- Nonnegative distance between two points -/
  nndist : α -> α -> Real>=0

export NNDist (nndist)

-- see Note [lower instance priority]
/-- Distance as a nonnegative real number. -/
instance (priority := 100) PseudoMetricSpace.toNNDist : NNDist α :=
  ⟨fun a b => ⟨dist a b, dist_nonneg⟩⟩

/--
theorem `dist_nndist` / 定理 `dist_nndist`

English:
theorem dist_nndist
  given: (x y : α)
  statement: dist x y = nndist x y
  proof: rfl

@[simp, norm_cast]

中文:
定理 dist_nndist
  条件: (x y : α)
  结论: dist x y = nndist x y
  证明: rfl

@[simp, norm_cast]
-/
theorem dist_nndist (x y : α) : dist x y = nndist x y := rfl

@[simp, norm_cast]
/--
theorem `coe_nndist` / 定理 `coe_nndist`

English:
theorem coe_nndist
  given: (x y : α)
  statement: ↑(nndist x y) = dist x y
  proof: rfl

中文:
定理 coe_nndist
  条件: (x y : α)
  结论: ↑(nndist x y) = dist x y
  证明: rfl
-/
theorem coe_nndist (x y : α) : ↑(nndist x y) = dist x y := rfl

/--
theorem `edist_nndist` / 定理 `edist_nndist`

English:
theorem edist_nndist
  given: (x y : α)
  statement: edist x y = nndist x y
  proof: by
  rw [edist_dist]; rw [dist_nndist]; rw [ENNReal.ofReal_coe_nnreal]

中文:
定理 edist_nndist
  条件: (x y : α)
  结论: edist x y = nndist x y
  证明: by
  rw [edist_dist]; rw [dist_nndist]; rw [ENNReal.ofReal_coe_nnreal]

Depends on / 依赖: ENNReal, ENNReal.ofReal_coe_nnreal, dist_nndist, edist_dist, ofReal_coe_nnreal
-/
theorem edist_nndist (x y : α) : edist x y = nndist x y := by
  rw [edist_dist]; rw [dist_nndist]; rw [ENNReal.ofReal_coe_nnreal]

/--
theorem `nndist_edist` / 定理 `nndist_edist`

English:
theorem nndist_edist
  given: (x y : α)
  statement: nndist x y = (edist x y).toNNReal
  proof: by
  simp [edist_nndist]

@[simp, norm_cast]

中文:
定理 nndist_edist
  条件: (x y : α)
  结论: nndist x y = (edist x y).toNN实数
  证明: by
  simp [edist_nndist]

@[simp, norm_cast]

Depends on / 依赖: edist_nndist
-/
theorem nndist_edist (x y : α) : nndist x y = (edist x y).toNNReal := by
  simp [edist_nndist]

@[simp, norm_cast]
/--
theorem `coe_nnreal_ennreal_nndist` / 定理 `coe_nnreal_ennreal_nndist`

English:
theorem coe_nnreal_ennreal_nndist
  given: (x y : α)
  statement: ↑(nndist x y) = edist x y
  proof: (edist_nndist x y).symm

@[simp, norm_cast]

中文:
定理 coe_nnreal_ennreal_nndist
  条件: (x y : α)
  结论: ↑(nndist x y) = edist x y
  证明: (edist_nndist x y).symm

@[simp, norm_cast]

Depends on / 依赖: edist_nndist
-/
theorem coe_nnreal_ennreal_nndist (x y : α) : ↑(nndist x y) = edist x y :=
  (edist_nndist x y).symm

@[simp, norm_cast]
/--
theorem `edist_lt_coe` / 定理 `edist_lt_coe`

English:
theorem edist_lt_coe
  given: {x y : α} {c : Real>=0}
  statement: edist x y < c ↔ nndist x y < c
  proof: by
  rw [edist_nndist]; rw [ENNReal.coe_lt_coe]

@[simp, norm_cast]

中文:
定理 edist_lt_coe
  条件: {x y : α} {c : 实数>=0}
  结论: edist x y < c ↔ nndist x y < c
  证明: by
  rw [edist_nndist]; rw [ENNReal.coe_lt_coe]

@[simp, norm_cast]

Depends on / 依赖: ENNReal, ENNReal.coe_lt_coe, coe_lt_coe, edist_nndist
-/
theorem edist_lt_coe {x y : α} {c : Real>=0} : edist x y < c ↔ nndist x y < c := by
  rw [edist_nndist]; rw [ENNReal.coe_lt_coe]

@[simp, norm_cast]
/--
theorem `edist_le_coe` / 定理 `edist_le_coe`

English:
theorem edist_le_coe
  given: {x y : α} {c : Real>=0}
  statement: edist x y <= c ↔ nndist x y <= c
  proof: by
  rw [edist_nndist]; rw [ENNReal.coe_le_coe]

中文:
定理 edist_le_coe
  条件: {x y : α} {c : 实数>=0}
  结论: edist x y <= c ↔ nndist x y <= c
  证明: by
  rw [edist_nndist]; rw [ENNReal.coe_le_coe]

Depends on / 依赖: ENNReal, ENNReal.coe_le_coe, coe_le_coe, edist_nndist
-/
theorem edist_le_coe {x y : α} {c : Real>=0} : edist x y <= c ↔ nndist x y <= c := by
  rw [edist_nndist]; rw [ENNReal.coe_le_coe]

/--
theorem `edist_lt_top` / 定理 `edist_lt_top`

English:
theorem edist_lt_top
  given: {α : Type*} [PseudoMetricSpace α] (x y : α)
  statement: edist x y < ⊤
  proof: (edist_dist x y).symm ▸ ENNReal.ofReal_lt_top

中文:
定理 edist_lt_top
  条件: {α : 类型} [PseudoMetricSpace α] (x y : α)
  结论: edist x y < ⊤
  证明: (edist_dist x y).symm ▸ ENNReal.ofReal_lt_top

Depends on / 依赖: ENNReal, ENNReal.ofReal_lt_top, edist_dist, ofReal_lt_top
-/
theorem edist_lt_top {α : Type*} [PseudoMetricSpace α] (x y : α) : edist x y < ⊤ :=
  (edist_dist x y).symm ▸ ENNReal.ofReal_lt_top

/-- In a pseudometric space, the extended distance is always finite -/
@[aesop (rule_sets := [finiteness]) safe apply, simp]
/--
theorem `edist_ne_top` / 定理 `edist_ne_top`

English:
theorem edist_ne_top
  given: (x y : α)
  statement: edist x y != ⊤
  proof: (edist_lt_top x y).ne

中文:
定理 edist_ne_top
  条件: (x y : α)
  结论: edist x y != ⊤
  证明: (edist_lt_top x y).ne

Depends on / 依赖: edist_lt_top
-/
theorem edist_ne_top (x y : α) : edist x y != ⊤ :=
  (edist_lt_top x y).ne

/--
theorem `nndist_self` / 定理 `nndist_self`

English:
theorem nndist_self
  given: (a : α)
  statement: nndist a a = 0
  proof: NNReal.coe_eq_zero.1 (dist_self a)

@[simp, norm_cast]

中文:
定理 nndist_self
  条件: (a : α)
  结论: nndist a a = 0
  证明: NNReal.coe_eq_zero.1 (dist_self a)

@[simp, norm_cast]
-/
@[simp] theorem nndist_self (a : α) : nndist a a = 0 := NNReal.coe_eq_zero.1 (dist_self a)

@[simp, norm_cast]
/--
theorem `dist_lt_coe` / 定理 `dist_lt_coe`

English:
theorem dist_lt_coe
  given: {x y : α} {c : Real>=0}
  statement: dist x y < c ↔ nndist x y < c
  proof: Iff.rfl

@[simp, norm_cast]

中文:
定理 dist_lt_coe
  条件: {x y : α} {c : 实数>=0}
  结论: dist x y < c ↔ nndist x y < c
  证明: Iff.rfl

@[simp, norm_cast]

Depends on / 依赖: Iff.rfl
-/
theorem dist_lt_coe {x y : α} {c : Real>=0} : dist x y < c ↔ nndist x y < c :=
  Iff.rfl

@[simp, norm_cast]
/--
theorem `dist_le_coe` / 定理 `dist_le_coe`

English:
theorem dist_le_coe
  given: {x y : α} {c : Real>=0}
  statement: dist x y <= c ↔ nndist x y <= c
  proof: Iff.rfl

@[simp]

中文:
定理 dist_le_coe
  条件: {x y : α} {c : 实数>=0}
  结论: dist x y <= c ↔ nndist x y <= c
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem dist_le_coe {x y : α} {c : Real>=0} : dist x y <= c ↔ nndist x y <= c :=
  Iff.rfl

@[simp]
/--
theorem `edist_lt_ofReal` / 定理 `edist_lt_ofReal`

English:
theorem edist_lt_ofReal
  given: {x y : α} {r : Real}
  statement: edist x y < ENNReal.ofReal r ↔ dist x y < r
  proof: by
  rw [edist_dist]; rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg]

@[simp]

中文:
定理 edist_lt_ofReal
  条件: {x y : α} {r : 实数}
  结论: edist x y < ENN实数.of实数 r ↔ dist x y < r
  证明: by
  rw [edist_dist]; rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg]

@[simp]

Depends on / 依赖: ENNReal, ENNReal.ofReal_lt_ofReal_iff_of_nonneg, dist_nonneg, edist_dist, ofReal_lt_ofReal_iff_of_nonneg
-/
theorem edist_lt_ofReal {x y : α} {r : Real} : edist x y < ENNReal.ofReal r ↔ dist x y < r := by
  rw [edist_dist]; rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg]

@[simp]
/--
theorem `edist_le_ofReal` / 定理 `edist_le_ofReal`

English:
theorem edist_le_ofReal
  given: {x y : α} {r : Real} (hr : 0 <= r)
  proof: by
  rw [edist_dist]; rw [ENNReal.ofReal_le_ofReal_iff hr]

中文:
定理 edist_le_ofReal
  条件: {x y : α} {r : 实数} (hr : 0 <= r)
  证明: by
  rw [edist_dist]; rw [ENNReal.ofReal_le_ofReal_iff hr]

Depends on / 依赖: ENNReal, ENNReal.ofReal_le_ofReal_iff, edist_dist, ofReal_le_ofReal_iff
-/
theorem edist_le_ofReal {x y : α} {r : Real} (hr : 0 <= r) :
    edist x y <= ENNReal.ofReal r ↔ dist x y <= r := by
  rw [edist_dist]; rw [ENNReal.ofReal_le_ofReal_iff hr]

/--
theorem `nndist_dist` / 定理 `nndist_dist`

English:
theorem nndist_dist
  given: (x y : α)
  statement: nndist x y = Real.toNNReal (dist x y)
  proof: by
  rw [dist_nndist]; rw [Real.toNNReal_coe]

中文:
定理 nndist_dist
  条件: (x y : α)
  结论: nndist x y = 实数.toNN实数 (dist x y)
  证明: by
  rw [dist_nndist]; rw [Real.toNNReal_coe]

Depends on / 依赖: Real.toNNReal_coe, dist_nndist, toNNReal_coe
-/
theorem nndist_dist (x y : α) : nndist x y = Real.toNNReal (dist x y) := by
  rw [dist_nndist]; rw [Real.toNNReal_coe]

/--
theorem `nndist_comm` / 定理 `nndist_comm`

English:
theorem nndist_comm
  given: (x y : α)
  statement: nndist x y = nndist y x
  proof: NNReal.eq dist_comm x y

中文:
定理 nndist_comm
  条件: (x y : α)
  结论: nndist x y = nndist y x
  证明: NNReal.eq dist_comm x y

Depends on / 依赖: NNReal, NNReal.eq, dist_comm
-/
theorem nndist_comm (x y : α) : nndist x y = nndist y x := NNReal.eq dist_comm x y

/--
theorem `nndist_triangle` / 定理 `nndist_triangle`

English:
theorem nndist_triangle
  given: (x y z : α)
  statement: nndist x z <= nndist x y + nndist y z
  proof: dist_triangle _ _ _

中文:
定理 nndist_triangle
  条件: (x y z : α)
  结论: nndist x z <= nndist x y + nndist y z
  证明: dist_triangle _ _ _

Depends on / 依赖: dist_triangle
-/
theorem nndist_triangle (x y z : α) : nndist x z <= nndist x y + nndist y z :=
  dist_triangle _ _ _

/--
theorem `nndist_triangle_left` / 定理 `nndist_triangle_left`

English:
theorem nndist_triangle_left
  given: (x y z : α)
  statement: nndist x y <= nndist z x + nndist z y
  proof: dist_triangle_left _ _ _

中文:
定理 nndist_triangle_left
  条件: (x y z : α)
  结论: nndist x y <= nndist z x + nndist z y
  证明: dist_triangle_left _ _ _

Depends on / 依赖: dist_triangle_left
-/
theorem nndist_triangle_left (x y z : α) : nndist x y <= nndist z x + nndist z y :=
  dist_triangle_left _ _ _

/--
theorem `nndist_triangle_right` / 定理 `nndist_triangle_right`

English:
theorem nndist_triangle_right
  given: (x y z : α)
  statement: nndist x y <= nndist x z + nndist y z
  proof: dist_triangle_right _ _ _

中文:
定理 nndist_triangle_right
  条件: (x y z : α)
  结论: nndist x y <= nndist x z + nndist y z
  证明: dist_triangle_right _ _ _

Depends on / 依赖: dist_triangle_right
-/
theorem nndist_triangle_right (x y z : α) : nndist x y <= nndist x z + nndist y z :=
  dist_triangle_right _ _ _

/--
theorem `dist_edist` / 定理 `dist_edist`

English:
theorem dist_edist
  given: (x y : α)
  statement: dist x y = (edist x y).toReal
  proof: by
  rw [edist_dist]; rw [ENNReal.toReal_ofReal dist_nonneg]

中文:
定理 dist_edist
  条件: (x y : α)
  结论: dist x y = (edist x y).to实数
  证明: by
  rw [edist_dist]; rw [ENNReal.toReal_ofReal dist_nonneg]

Depends on / 依赖: ENNReal, ENNReal.toReal_ofReal, dist_nonneg, edist_dist, toReal_ofReal
-/
theorem dist_edist (x y : α) : dist x y = (edist x y).toReal := by
  rw [edist_dist]; rw [ENNReal.toReal_ofReal dist_nonneg]

namespace Metric

-- instantiate pseudometric space as a topology
variable {x y z : α} {δ ε ε₁ ε₂ : Real} {s : Set α}

/-- `ball x ε` is the set of all points `y` with `dist y x < ε` -/
@[wikidata Q838611]
/--
Definition of `ball` / `ball` 的定义

English:
definition ball
  signature: (x : α) (ε : Real)
  body: { y | dist y x < ε }

@[simp]

中文:
定义 ball
  签名: (x : α) (ε : 实数)
  定义体: { y | dist y x < ε }

@[simp]
-/
def ball (x : α) (ε : Real) : Set α :=
  { y | dist y x < ε }

@[simp]
/--
theorem `mem_ball` / 定理 `mem_ball`

English:
theorem mem_ball
  statement: y in ball x ε ↔ dist y x < ε
  proof: Iff.rfl

中文:
定理 mem_ball
  结论: y in ball x ε ↔ dist y x < ε
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_ball : y in ball x ε ↔ dist y x < ε :=
  Iff.rfl

/--
theorem `mem_ball'` / 定理 `mem_ball'`

English:
theorem mem_ball'
  statement: y in ball x ε ↔ dist x y < ε
  proof: by rw [dist_comm, mem_ball]

中文:
定理 mem_ball'
  结论: y in ball x ε ↔ dist x y < ε
  证明: by rw [dist_comm, mem_ball]

Depends on / 依赖: dist_comm, mem_ball
-/
theorem mem_ball' : y in ball x ε ↔ dist x y < ε := by rw [dist_comm, mem_ball]

/--
theorem `pos_of_mem_ball` / 定理 `pos_of_mem_ball`

English:
theorem pos_of_mem_ball
  given: (hy : y in ball x ε)
  statement: 0 < ε
  proof: dist_nonneg.trans_lt hy

中文:
定理 pos_of_mem_ball
  条件: (hy : y in ball x ε)
  结论: 0 < ε
  证明: dist_nonneg.trans_lt hy

Depends on / 依赖: dist_nonneg, dist_nonneg.trans_lt, trans_lt
-/
theorem pos_of_mem_ball (hy : y in ball x ε) : 0 < ε :=
  dist_nonneg.trans_lt hy

/--
theorem `mem_ball_self` / 定理 `mem_ball_self`

English:
theorem mem_ball_self
  given: (h : 0 < ε)
  statement: x in ball x ε
  proof: by
  rwa [mem_ball, dist_self]

@[simp]

中文:
定理 mem_ball_self
  条件: (h : 0 < ε)
  结论: x in ball x ε
  证明: by
  rwa [mem_ball, dist_self]

@[simp]

Depends on / 依赖: dist_self, mem_ball
-/
theorem mem_ball_self (h : 0 < ε) : x in ball x ε := by
  rwa [mem_ball, dist_self]

@[simp]
/--
theorem `nonempty_ball` / 定理 `nonempty_ball`

English:
theorem nonempty_ball
  statement: (ball x ε).Nonempty ↔ 0 < ε
  proof: ⟨fun ⟨_x, hx⟩ => pos_of_mem_ball hx, fun h => ⟨x, mem_ball_self h⟩⟩

@[simp]

中文:
定理 nonempty_ball
  结论: (ball x ε).Nonempty ↔ 0 < ε
  证明: ⟨fun ⟨_x, hx⟩ => pos_of_mem_ball hx, fun h => ⟨x, mem_ball_self h⟩⟩

@[simp]

Depends on / 依赖: mem_ball_self, pos_of_mem_ball
-/
theorem nonempty_ball : (ball x ε).Nonempty ↔ 0 < ε :=
  ⟨fun ⟨_x, hx⟩ => pos_of_mem_ball hx, fun h => ⟨x, mem_ball_self h⟩⟩

@[simp]
/--
theorem `ball_eq_empty` / 定理 `ball_eq_empty`

English:
theorem ball_eq_empty
  statement: ball x ε = ∅ ↔ ε <= 0
  proof: by
  rw [← not_nonempty_iff_eq_empty]; rw [nonempty_ball]; rw [not_lt]

@[simp]

中文:
定理 ball_eq_empty
  结论: ball x ε = ∅ ↔ ε <= 0
  证明: by
  rw [← not_nonempty_iff_eq_empty]; rw [nonempty_ball]; rw [not_lt]

@[simp]

Depends on / 依赖: nonempty_ball, not_lt, not_nonempty_iff_eq_empty
-/
theorem ball_eq_empty : ball x ε = ∅ ↔ ε <= 0 := by
  rw [← not_nonempty_iff_eq_empty]; rw [nonempty_ball]; rw [not_lt]

@[simp]
/--
theorem `ball_zero` / 定理 `ball_zero`

English:
theorem ball_zero
  statement: ball x 0 = ∅
  proof: by rw [ball_eq_empty]

中文:
定理 ball_zero
  结论: ball x 0 = ∅
  证明: by rw [ball_eq_empty]

Depends on / 依赖: ball_eq_empty
-/
theorem ball_zero : ball x 0 = ∅ := by rw [ball_eq_empty]

/--
theorem `exists_lt_mem_ball_of_mem_ball` / 定理 `exists_lt_mem_ball_of_mem_ball`

English:
theorem exists_lt_mem_ball_of_mem_ball
  given: (h : x in ball y ε)
  statement: exists ε' < ε, x in ball y ε'
  proof: by
  simpa [mem_ball] using exists_between' h

中文:
定理 exists_lt_mem_ball_of_mem_ball
  条件: (h : x in ball y ε)
  结论: 存在 ε' < ε, x in ball y ε'
  证明: by
  simpa [mem_ball] using exists_between' h

Depends on / 依赖: exists_between, mem_ball
-/
theorem exists_lt_mem_ball_of_mem_ball (h : x in ball y ε) : exists ε' < ε, x in ball y ε' := by
  simpa [mem_ball] using exists_between' h

/--
theorem `ball_eq_ball` / 定理 `ball_eq_ball`

English:
theorem ball_eq_ball
  given: (ε : Real) (x : α)
  proof: rfl

中文:
定理 ball_eq_ball
  条件: (ε : 实数) (x : α)
  证明: rfl
-/
theorem ball_eq_ball (ε : Real) (x : α) :
    UniformSpace.ball x { p | dist p.2 p.1 < ε } = Metric.ball x ε :=
  rfl

/--
theorem `ball_eq_ball'` / 定理 `ball_eq_ball'`

English:
theorem ball_eq_ball'
  given: (ε : Real) (x : α)
  proof: by
  ext
  simp [dist_comm, UniformSpace.ball]

@[simp]

中文:
定理 ball_eq_ball'
  条件: (ε : 实数) (x : α)
  证明: by
  ext
  simp [dist_comm, UniformSpace.ball]

@[simp]

Depends on / 依赖: UniformSpace, UniformSpace.ball, dist_comm
-/
theorem ball_eq_ball' (ε : Real) (x : α) :
    UniformSpace.ball x { p | dist p.1 p.2 < ε } = Metric.ball x ε := by
  ext
  simp [dist_comm, UniformSpace.ball]

@[simp]
/--
theorem `iUnion_ball_nat` / 定理 `iUnion_ball_nat`

English:
theorem iUnion_ball_nat
  given: (x : α)
  statement: ⋃ n : Nat, ball x n = univ
  proof: iUnion_eq_univ_iff.2 fun y => exists_nat_gt (dist y x)

@[simp]

中文:
定理 iUnion_ball_nat
  条件: (x : α)
  结论: ⋃ n : 自然数, ball x n = univ
  证明: iUnion_eq_univ_iff.2 fun y => exists_nat_gt (dist y x)

@[simp]

Depends on / 依赖: exists_nat_gt, iUnion_eq_univ_iff
-/
theorem iUnion_ball_nat (x : α) : ⋃ n : Nat, ball x n = univ :=
  iUnion_eq_univ_iff.2 fun y => exists_nat_gt (dist y x)

@[simp]
/--
theorem `iUnion_ball_nat_succ` / 定理 `iUnion_ball_nat_succ`

English:
theorem iUnion_ball_nat_succ
  given: (x : α)
  statement: ⋃ n : Nat, ball x (n + 1) = univ
  proof: iUnion_eq_univ_iff.2 fun y => (exists_nat_gt (dist y x)).imp fun _ h => h.trans (lt_add_one _)

中文:
定理 iUnion_ball_nat_succ
  条件: (x : α)
  结论: ⋃ n : 自然数, ball x (n + 1) = univ
  证明: iUnion_eq_univ_iff.2 fun y => (exists_nat_gt (dist y x)).imp fun _ h => h.trans (lt_add_one _)

Depends on / 依赖: exists_nat_gt, h.trans, iUnion_eq_univ_iff, lt_add_one
-/
theorem iUnion_ball_nat_succ (x : α) : ⋃ n : Nat, ball x (n + 1) = univ :=
  iUnion_eq_univ_iff.2 fun y => (exists_nat_gt (dist y x)).imp fun _ h => h.trans (lt_add_one _)

/--
Definition of `closedBall` / `closedBall` 的定义

English:
definition closedBall
  signature: (x : α) (ε : Real)
  body: { y | dist y x <= ε }

中文:
定义 closedBall
  签名: (x : α) (ε : 实数)
  定义体: { y | dist y x <= ε }
-/
def closedBall (x : α) (ε : Real) :=
  { y | dist y x <= ε }

/--
theorem `mem_closedBall` / 定理 `mem_closedBall`

English:
theorem mem_closedBall
  statement: y in closedBall x ε ↔ dist y x <= ε
  proof: Iff.rfl

中文:
定理 mem_closedBall
  结论: y in closedBall x ε ↔ dist y x <= ε
  证明: Iff.rfl
-/
@[simp] theorem mem_closedBall : y in closedBall x ε ↔ dist y x <= ε := Iff.rfl

/--
theorem `mem_closedBall'` / 定理 `mem_closedBall'`

English:
theorem mem_closedBall'
  statement: y in closedBall x ε ↔ dist x y <= ε
  proof: by rw [dist_comm, mem_closedBall]

中文:
定理 mem_closedBall'
  结论: y in closedBall x ε ↔ dist x y <= ε
  证明: by rw [dist_comm, mem_closedBall]

Depends on / 依赖: dist_comm, mem_closedBall
-/
theorem mem_closedBall' : y in closedBall x ε ↔ dist x y <= ε := by rw [dist_comm, mem_closedBall]

/--
theorem `nonneg_of_mem_closedBall` / 定理 `nonneg_of_mem_closedBall`

English:
theorem nonneg_of_mem_closedBall
  given: (hy : y in closedBall x ε)
  statement: 0 <= ε
  proof: dist_nonneg.trans hy

中文:
定理 nonneg_of_mem_closedBall
  条件: (hy : y in closedBall x ε)
  结论: 0 <= ε
  证明: dist_nonneg.trans hy

Depends on / 依赖: dist_nonneg, dist_nonneg.trans
-/
theorem nonneg_of_mem_closedBall (hy : y in closedBall x ε) : 0 <= ε :=
  dist_nonneg.trans hy

/--
Definition of `sphere` / `sphere` 的定义

English:
definition sphere
  signature: (x : α) (ε : Real)
  body: { y | dist y x = ε }

中文:
定义 sphere
  签名: (x : α) (ε : 实数)
  定义体: { y | dist y x = ε }
-/
def sphere (x : α) (ε : Real) := { y | dist y x = ε }

/--
theorem `mem_sphere` / 定理 `mem_sphere`

English:
theorem mem_sphere
  statement: y in sphere x ε ↔ dist y x = ε
  proof: Iff.rfl

中文:
定理 mem_sphere
  结论: y in sphere x ε ↔ dist y x = ε
  证明: Iff.rfl
-/
@[simp] theorem mem_sphere : y in sphere x ε ↔ dist y x = ε := Iff.rfl

/--
theorem `mem_sphere'` / 定理 `mem_sphere'`

English:
theorem mem_sphere'
  statement: y in sphere x ε ↔ dist x y = ε
  proof: by rw [dist_comm, mem_sphere]

中文:
定理 mem_sphere'
  结论: y in sphere x ε ↔ dist x y = ε
  证明: by rw [dist_comm, mem_sphere]

Depends on / 依赖: dist_comm, mem_sphere
-/
theorem mem_sphere' : y in sphere x ε ↔ dist x y = ε := by rw [dist_comm, mem_sphere]

/--
theorem `ne_of_mem_sphere` / 定理 `ne_of_mem_sphere`

English:
theorem ne_of_mem_sphere
  given: (h : y in sphere x ε) (hε : ε != 0)
  statement: y != x
  proof: ne_of_mem_of_not_mem h by simpa using hε.symm

中文:
定理 ne_of_mem_sphere
  条件: (h : y in sphere x ε) (hε : ε != 0)
  结论: y != x
  证明: ne_of_mem_of_not_mem h by simpa using hε.symm

Depends on / 依赖: ne_of_mem_of_not_mem
-/
theorem ne_of_mem_sphere (h : y in sphere x ε) (hε : ε != 0) : y != x :=
ne_of_mem_of_not_mem h by simpa using hε.symm

/--
theorem `nonneg_of_mem_sphere` / 定理 `nonneg_of_mem_sphere`

English:
theorem nonneg_of_mem_sphere
  given: (hy : y in sphere x ε)
  statement: 0 <= ε
  proof: dist_nonneg.trans_eq hy

@[simp]

中文:
定理 nonneg_of_mem_sphere
  条件: (hy : y in sphere x ε)
  结论: 0 <= ε
  证明: dist_nonneg.trans_eq hy

@[simp]

Depends on / 依赖: dist_nonneg, dist_nonneg.trans_eq, trans_eq
-/
theorem nonneg_of_mem_sphere (hy : y in sphere x ε) : 0 <= ε :=
  dist_nonneg.trans_eq hy

@[simp]
/--
theorem `sphere_eq_empty_of_neg` / 定理 `sphere_eq_empty_of_neg`

English:
theorem sphere_eq_empty_of_neg
  given: (hε : ε < 0)
  statement: sphere x ε = ∅
  proof: Set.eq_empty_iff_forall_notMem.mpr fun _y hy => (nonneg_of_mem_sphere hy).not_gt hε

中文:
定理 sphere_eq_empty_of_neg
  条件: (hε : ε < 0)
  结论: sphere x ε = ∅
  证明: Set.eq_empty_iff_forall_notMem.mpr fun _y hy => (nonneg_of_mem_sphere hy).not_gt hε

Depends on / 依赖: Set.eq_empty_iff_forall_notMem.mpr, eq_empty_iff_forall_notMem, nonneg_of_mem_sphere, not_gt
-/
theorem sphere_eq_empty_of_neg (hε : ε < 0) : sphere x ε = ∅ :=
  Set.eq_empty_iff_forall_notMem.mpr fun _y hy => (nonneg_of_mem_sphere hy).not_gt hε

/--
theorem `sphere_eq_empty_of_subsingleton` / 定理 `sphere_eq_empty_of_subsingleton`

English:
theorem sphere_eq_empty_of_subsingleton
  given: [Subsingleton α] (hε : ε != 0)
  statement: sphere x ε = ∅
  proof: Set.eq_empty_iff_forall_notMem.mpr fun _ h => ne_of_mem_sphere h hε (Subsingleton.elim _ _)

中文:
定理 sphere_eq_empty_of_subsingleton
  条件: [Subsingleton α] (hε : ε != 0)
  结论: sphere x ε = ∅
  证明: Set.eq_empty_iff_forall_notMem.mpr fun _ h => ne_of_mem_sphere h hε (Subsingleton.elim _ _)

Depends on / 依赖: Set.eq_empty_iff_forall_notMem.mpr, Subsingleton, Subsingleton.elim, eq_empty_iff_forall_notMem, ne_of_mem_sphere
-/
theorem sphere_eq_empty_of_subsingleton [Subsingleton α] (hε : ε != 0) : sphere x ε = ∅ :=
  Set.eq_empty_iff_forall_notMem.mpr fun _ h => ne_of_mem_sphere h hε (Subsingleton.elim _ _)

/--
Instance `sphere_isEmpty_of_subsingleton` / 实例 `sphere_isEmpty_of_subsingleton`

English:
instance sphere_isEmpty_of_subsingleton
  signature: [Subsingleton α] [NeZero ε]
  body: by
  rw [sphere_eq_empty_of_subsingleton (NeZero.ne ε)]; infer_instance

中文:
实例 sphere_isEmpty_of_subsingleton
  签名: [Subsingleton α] [NeZero ε]
  定义体: by
  rw [sphere_eq_empty_of_subsingleton (NeZero.ne ε)]; infer_instance

Depends on / 依赖: NeZero, NeZero.ne, infer_instance, sphere_eq_empty_of_subsingleton
-/
instance sphere_isEmpty_of_subsingleton [Subsingleton α] [NeZero ε] : IsEmpty (sphere x ε) := by
  rw [sphere_eq_empty_of_subsingleton (NeZero.ne ε)]; infer_instance

/--
theorem `closedBall_eq_singleton_of_subsingleton` / 定理 `closedBall_eq_singleton_of_subsingleton`

English:
theorem closedBall_eq_singleton_of_subsingleton
  given: [Subsingleton α] (h : 0 <= ε)
  proof: by
  ext x'
  simpa [Subsingleton.allEq x x']

中文:
定理 closedBall_eq_singleton_of_subsingleton
  条件: [Subsingleton α] (h : 0 <= ε)
  证明: by
  ext x'
  simpa [Subsingleton.allEq x x']

Depends on / 依赖: Subsingleton, Subsingleton.allEq
-/
theorem closedBall_eq_singleton_of_subsingleton [Subsingleton α] (h : 0 <= ε) :
    closedBall x ε = {x} := by
  ext x'
  simpa [Subsingleton.allEq x x']

/--
theorem `ball_eq_singleton_of_subsingleton` / 定理 `ball_eq_singleton_of_subsingleton`

English:
theorem ball_eq_singleton_of_subsingleton
  given: [Subsingleton α] (h : 0 < ε)
  statement: ball x ε = {x}
  proof: by
  ext x'
  simpa [Subsingleton.allEq x x']

中文:
定理 ball_eq_singleton_of_subsingleton
  条件: [Subsingleton α] (h : 0 < ε)
  结论: ball x ε = {x}
  证明: by
  ext x'
  simpa [Subsingleton.allEq x x']

Depends on / 依赖: Subsingleton, Subsingleton.allEq
-/
theorem ball_eq_singleton_of_subsingleton [Subsingleton α] (h : 0 < ε) : ball x ε = {x} := by
  ext x'
  simpa [Subsingleton.allEq x x']

/--
theorem `mem_closedBall_self` / 定理 `mem_closedBall_self`

English:
theorem mem_closedBall_self
  given: (h : 0 <= ε)
  statement: x in closedBall x ε
  proof: by
  rwa [mem_closedBall, dist_self]

@[simp]

中文:
定理 mem_closedBall_self
  条件: (h : 0 <= ε)
  结论: x in closedBall x ε
  证明: by
  rwa [mem_closedBall, dist_self]

@[simp]

Depends on / 依赖: dist_self, mem_closedBall
-/
theorem mem_closedBall_self (h : 0 <= ε) : x in closedBall x ε := by
  rwa [mem_closedBall, dist_self]

@[simp]
/--
theorem `nonempty_closedBall` / 定理 `nonempty_closedBall`

English:
theorem nonempty_closedBall
  statement: (closedBall x ε).Nonempty ↔ 0 <= ε
  proof: ⟨fun ⟨_x, hx⟩ => dist_nonneg.trans hx, fun h => ⟨x, mem_closedBall_self h⟩⟩

@[simp]

中文:
定理 nonempty_closedBall
  结论: (closedBall x ε).Nonempty ↔ 0 <= ε
  证明: ⟨fun ⟨_x, hx⟩ => dist_nonneg.trans hx, fun h => ⟨x, mem_closedBall_self h⟩⟩

@[simp]

Depends on / 依赖: dist_nonneg, dist_nonneg.trans, mem_closedBall_self
-/
theorem nonempty_closedBall : (closedBall x ε).Nonempty ↔ 0 <= ε :=
  ⟨fun ⟨_x, hx⟩ => dist_nonneg.trans hx, fun h => ⟨x, mem_closedBall_self h⟩⟩

@[simp]
/--
theorem `closedBall_eq_empty` / 定理 `closedBall_eq_empty`

English:
theorem closedBall_eq_empty
  statement: closedBall x ε = ∅ ↔ ε < 0
  proof: by
  rw [← not_nonempty_iff_eq_empty]; rw [nonempty_closedBall]; rw [not_le]

@[simp] alias ⟨_, closedBall_of_neg⟩ := closedBall_eq_empty

中文:
定理 closedBall_eq_empty
  结论: closedBall x ε = ∅ ↔ ε < 0
  证明: by
  rw [← not_nonempty_iff_eq_empty]; rw [nonempty_closedBall]; rw [not_le]

@[simp] alias ⟨_, closedBall_of_neg⟩ := closedBall_eq_empty

Depends on / 依赖: nonempty_closedBall, not_le, not_nonempty_iff_eq_empty
-/
theorem closedBall_eq_empty : closedBall x ε = ∅ ↔ ε < 0 := by
  rw [← not_nonempty_iff_eq_empty]; rw [nonempty_closedBall]; rw [not_le]

@[simp] alias ⟨_, closedBall_of_neg⟩ := closedBall_eq_empty

/--
theorem `closedBall_eq_sphere_of_nonpos` / 定理 `closedBall_eq_sphere_of_nonpos`

English:
theorem closedBall_eq_sphere_of_nonpos
  given: (hε : ε <= 0)
  statement: closedBall x ε = sphere x ε
  proof: Set.ext fun _ => (hε.trans dist_nonneg).ge_iff_eq'

中文:
定理 closedBall_eq_sphere_of_nonpos
  条件: (hε : ε <= 0)
  结论: closedBall x ε = sphere x ε
  证明: Set.ext fun _ => (hε.trans dist_nonneg).ge_iff_eq'

Depends on / 依赖: Set.ext, dist_nonneg, ge_iff_eq
-/
theorem closedBall_eq_sphere_of_nonpos (hε : ε <= 0) : closedBall x ε = sphere x ε :=
  Set.ext fun _ => (hε.trans dist_nonneg).ge_iff_eq'

/--
theorem `ball_subset_closedBall` / 定理 `ball_subset_closedBall`

English:
theorem ball_subset_closedBall
  statement: ball x ε subseteq closedBall x ε
  proof: fun _y hy =>
  mem_closedBall.2 (le_of_lt hy)

中文:
定理 ball_subset_closedBall
  结论: ball x ε subseteq closedBall x ε
  证明: fun _y hy =>
  mem_closedBall.2 (le_of_lt hy)
-/
theorem ball_subset_closedBall : ball x ε subseteq closedBall x ε := fun _y hy =>
  mem_closedBall.2 (le_of_lt hy)

/--
theorem `sphere_subset_closedBall` / 定理 `sphere_subset_closedBall`

English:
theorem sphere_subset_closedBall
  statement: sphere x ε subseteq closedBall x ε
  proof: fun _ => le_of_eq

中文:
定理 sphere_subset_closedBall
  结论: sphere x ε subseteq closedBall x ε
  证明: fun _ => le_of_eq

Depends on / 依赖: le_of_eq
-/
theorem sphere_subset_closedBall : sphere x ε subseteq closedBall x ε := fun _ => le_of_eq

/--
lemma `sphere_subset_ball` / 引理 `sphere_subset_ball`

English:
lemma sphere_subset_ball
  given: {r R : Real} (h : r < R)
  statement: sphere x r subseteq ball x R
  proof: fun _x hx =>
  (mem_sphere.1 hx).trans_lt h

中文:
引理 sphere_subset_ball
  条件: {r R : 实数} (h : r < R)
  结论: sphere x r subseteq ball x R
  证明: fun _x hx =>
  (mem_sphere.1 hx).trans_lt h
-/
lemma sphere_subset_ball {r R : Real} (h : r < R) : sphere x r subseteq ball x R := fun _x hx =>
  (mem_sphere.1 hx).trans_lt h

/--
theorem `closedBall_disjoint_ball` / 定理 `closedBall_disjoint_ball`

English:
theorem closedBall_disjoint_ball
  given: (h : δ + ε <= dist x y)
  statement: Disjoint (closedBall x δ) (ball y ε)
  proof: Set.disjoint_left.mpr fun _a ha1 ha2 =>
(h.trans <| dist_triangle_left _ _ _).not_gt add_lt_add_of_le_of_lt ha1 ha2

中文:
定理 closedBall_disjoint_ball
  条件: (h : δ + ε <= dist x y)
  结论: Disjoint (closedBall x δ) (ball y ε)
  证明: Set.disjoint_left.mpr fun _a ha1 ha2 =>
(h.trans <| dist_triangle_left _ _ _).not_gt add_lt_add_of_le_of_lt ha1 ha2

Depends on / 依赖: Set.disjoint_left.mpr, add_lt_add_of_le_of_lt, disjoint_left, dist_triangle_left, h.trans, not_gt
-/
theorem closedBall_disjoint_ball (h : δ + ε <= dist x y) : Disjoint (closedBall x δ) (ball y ε) :=
  Set.disjoint_left.mpr fun _a ha1 ha2 =>
(h.trans <| dist_triangle_left _ _ _).not_gt add_lt_add_of_le_of_lt ha1 ha2

/--
theorem `ball_disjoint_closedBall` / 定理 `ball_disjoint_closedBall`

English:
theorem ball_disjoint_closedBall
  given: (h : δ + ε <= dist x y)
  statement: Disjoint (ball x δ) (closedBall y ε)
  proof: (closedBall_disjoint_ball <| by rwa [add_comm, dist_comm]).symm

中文:
定理 ball_disjoint_closedBall
  条件: (h : δ + ε <= dist x y)
  结论: Disjoint (ball x δ) (closedBall y ε)
  证明: (closedBall_disjoint_ball <| by rwa [add_comm, dist_comm]).symm

Depends on / 依赖: add_comm, closedBall_disjoint_ball, dist_comm
-/
theorem ball_disjoint_closedBall (h : δ + ε <= dist x y) : Disjoint (ball x δ) (closedBall y ε) :=
  (closedBall_disjoint_ball <| by rwa [add_comm, dist_comm]).symm

/--
theorem `ball_disjoint_ball` / 定理 `ball_disjoint_ball`

English:
theorem ball_disjoint_ball
  given: (h : δ + ε <= dist x y)
  statement: Disjoint (ball x δ) (ball y ε)
  proof: (closedBall_disjoint_ball h).mono_left ball_subset_closedBall

中文:
定理 ball_disjoint_ball
  条件: (h : δ + ε <= dist x y)
  结论: Disjoint (ball x δ) (ball y ε)
  证明: (closedBall_disjoint_ball h).mono_left ball_subset_closedBall

Depends on / 依赖: ball_subset_closedBall, closedBall_disjoint_ball, mono_left
-/
theorem ball_disjoint_ball (h : δ + ε <= dist x y) : Disjoint (ball x δ) (ball y ε) :=
  (closedBall_disjoint_ball h).mono_left ball_subset_closedBall

/--
theorem `closedBall_disjoint_closedBall` / 定理 `closedBall_disjoint_closedBall`

English:
theorem closedBall_disjoint_closedBall
  given: (h : δ + ε < dist x y)
  proof: Set.disjoint_left.mpr fun _a ha1 ha2 =>
h.not_ge (dist_triangle_left _ _ _).trans add_le_add ha1 ha2

中文:
定理 closedBall_disjoint_closedBall
  条件: (h : δ + ε < dist x y)
  证明: Set.disjoint_left.mpr fun _a ha1 ha2 =>
h.not_ge (dist_triangle_left _ _ _).trans add_le_add ha1 ha2

Depends on / 依赖: Set.disjoint_left.mpr, add_le_add, disjoint_left, dist_triangle_left, h.not_ge, not_ge
-/
theorem closedBall_disjoint_closedBall (h : δ + ε < dist x y) :
    Disjoint (closedBall x δ) (closedBall y ε) :=
  Set.disjoint_left.mpr fun _a ha1 ha2 =>
h.not_ge (dist_triangle_left _ _ _).trans add_le_add ha1 ha2

/--
theorem `sphere_disjoint_ball` / 定理 `sphere_disjoint_ball`

English:
theorem sphere_disjoint_ball
  statement: Disjoint (sphere x ε) (ball x ε)
  proof: Set.disjoint_left.mpr fun _y hy₁ hy₂ => absurd hy₁ ne_of_lt hy₂

@[simp]

中文:
定理 sphere_disjoint_ball
  结论: Disjoint (sphere x ε) (ball x ε)
  证明: Set.disjoint_left.mpr fun _y hy₁ hy₂ => absurd hy₁ ne_of_lt hy₂

@[simp]

Depends on / 依赖: Set.disjoint_left.mpr, absurd, disjoint_left, ne_of_lt
-/
theorem sphere_disjoint_ball : Disjoint (sphere x ε) (ball x ε) :=
Set.disjoint_left.mpr fun _y hy₁ hy₂ => absurd hy₁ ne_of_lt hy₂

@[simp]
/--
theorem `ball_union_sphere` / 定理 `ball_union_sphere`

English:
theorem ball_union_sphere
  statement: ball x ε union sphere x ε = closedBall x ε
  proof: Set.ext fun _y => (@le_iff_lt_or_eq Real _ _ _).symm

@[simp]

中文:
定理 ball_union_sphere
  结论: ball x ε union sphere x ε = closedBall x ε
  证明: Set.ext fun _y => (@le_iff_lt_or_eq Real _ _ _).symm

@[simp]

Depends on / 依赖: Set.ext, le_iff_lt_or_eq
-/
theorem ball_union_sphere : ball x ε union sphere x ε = closedBall x ε :=
  Set.ext fun _y => (@le_iff_lt_or_eq Real _ _ _).symm

@[simp]
/--
theorem `sphere_union_ball` / 定理 `sphere_union_ball`

English:
theorem sphere_union_ball
  statement: sphere x ε union ball x ε = closedBall x ε
  proof: by
  rw [union_comm]; rw [ball_union_sphere]

@[simp]

中文:
定理 sphere_union_ball
  结论: sphere x ε union ball x ε = closedBall x ε
  证明: by
  rw [union_comm]; rw [ball_union_sphere]

@[simp]

Depends on / 依赖: ball_union_sphere, union_comm
-/
theorem sphere_union_ball : sphere x ε union ball x ε = closedBall x ε := by
  rw [union_comm]; rw [ball_union_sphere]

@[simp]
/--
theorem `closedBall_sdiff_sphere` / 定理 `closedBall_sdiff_sphere`

English:
theorem closedBall_sdiff_sphere
  statement: closedBall x ε \ sphere x ε = ball x ε
  proof: by
  rw [← ball_union_sphere]; rw [Set.union_sdiff_cancel_right sphere_disjoint_ball.symm.le_bot]

@[deprecated (since := "2026-06-03")] alias closedBall_diff_sphere := closedBall_sdiff_sphere

@[simp]

中文:
定理 closedBall_sdiff_sphere
  结论: closedBall x ε \ sphere x ε = ball x ε
  证明: by
  rw [← ball_union_sphere]; rw [Set.union_sdiff_cancel_right sphere_disjoint_ball.symm.le_bot]

@[deprecated (since := "2026-06-03")] alias closedBall_diff_sphere := closedBall_sdiff_sphere

@[simp]

Depends on / 依赖: Set.union_sdiff_cancel_right, ball_union_sphere, le_bot, sphere_disjoint_ball, sphere_disjoint_ball.symm.le_bot, union_sdiff_cancel_right
-/
theorem closedBall_sdiff_sphere : closedBall x ε \ sphere x ε = ball x ε := by
  rw [← ball_union_sphere]; rw [Set.union_sdiff_cancel_right sphere_disjoint_ball.symm.le_bot]

@[deprecated (since := "2026-06-03")] alias closedBall_diff_sphere := closedBall_sdiff_sphere

@[simp]
/--
theorem `closedBall_sdiff_ball` / 定理 `closedBall_sdiff_ball`

English:
theorem closedBall_sdiff_ball
  statement: closedBall x ε \ ball x ε = sphere x ε
  proof: by
  rw [← ball_union_sphere]; rw [Set.union_sdiff_cancel_left sphere_disjoint_ball.symm.le_bot]

@[deprecated (since := "2026-06-03")] alias closedBall_diff_ball := closedBall_sdiff_ball

中文:
定理 closedBall_sdiff_ball
  结论: closedBall x ε \ ball x ε = sphere x ε
  证明: by
  rw [← ball_union_sphere]; rw [Set.union_sdiff_cancel_left sphere_disjoint_ball.symm.le_bot]

@[deprecated (since := "2026-06-03")] alias closedBall_diff_ball := closedBall_sdiff_ball

Depends on / 依赖: Set.union_sdiff_cancel_left, ball_union_sphere, le_bot, sphere_disjoint_ball, sphere_disjoint_ball.symm.le_bot, union_sdiff_cancel_left
-/
theorem closedBall_sdiff_ball : closedBall x ε \ ball x ε = sphere x ε := by
  rw [← ball_union_sphere]; rw [Set.union_sdiff_cancel_left sphere_disjoint_ball.symm.le_bot]

@[deprecated (since := "2026-06-03")] alias closedBall_diff_ball := closedBall_sdiff_ball

/--
theorem `mem_ball_comm` / 定理 `mem_ball_comm`

English:
theorem mem_ball_comm
  statement: x in ball y ε ↔ y in ball x ε
  proof: by rw [mem_ball', mem_ball]

中文:
定理 mem_ball_comm
  结论: x in ball y ε ↔ y in ball x ε
  证明: by rw [mem_ball', mem_ball]

Depends on / 依赖: mem_ball
-/
theorem mem_ball_comm : x in ball y ε ↔ y in ball x ε := by rw [mem_ball', mem_ball]

/--
theorem `mem_closedBall_comm` / 定理 `mem_closedBall_comm`

English:
theorem mem_closedBall_comm
  statement: x in closedBall y ε ↔ y in closedBall x ε
  proof: by
  rw [mem_closedBall']; rw [mem_closedBall]

中文:
定理 mem_closedBall_comm
  结论: x in closedBall y ε ↔ y in closedBall x ε
  证明: by
  rw [mem_closedBall']; rw [mem_closedBall]

Depends on / 依赖: mem_closedBall
-/
theorem mem_closedBall_comm : x in closedBall y ε ↔ y in closedBall x ε := by
  rw [mem_closedBall']; rw [mem_closedBall]

/--
theorem `mem_sphere_comm` / 定理 `mem_sphere_comm`

English:
theorem mem_sphere_comm
  statement: x in sphere y ε ↔ y in sphere x ε
  proof: by rw [mem_sphere', mem_sphere]

@[gcongr]

中文:
定理 mem_sphere_comm
  结论: x in sphere y ε ↔ y in sphere x ε
  证明: by rw [mem_sphere', mem_sphere]

@[gcongr]

Depends on / 依赖: mem_sphere
-/
theorem mem_sphere_comm : x in sphere y ε ↔ y in sphere x ε := by rw [mem_sphere', mem_sphere]

@[gcongr]
/--
theorem `ball_subset_ball` / 定理 `ball_subset_ball`

English:
theorem ball_subset_ball
  given: (h : ε₁ <= ε₂)
  statement: ball x ε₁ subseteq ball x ε₂
  proof: fun _y yx =>
  lt_of_lt_of_le (mem_ball.1 yx) h

中文:
定理 ball_subset_ball
  条件: (h : ε₁ <= ε₂)
  结论: ball x ε₁ subseteq ball x ε₂
  证明: fun _y yx =>
  lt_of_lt_of_le (mem_ball.1 yx) h
-/
theorem ball_subset_ball (h : ε₁ <= ε₂) : ball x ε₁ subseteq ball x ε₂ := fun _y yx =>
  lt_of_lt_of_le (mem_ball.1 yx) h

/--
theorem `closedBall_eq_bInter_ball` / 定理 `closedBall_eq_bInter_ball`

English:
theorem closedBall_eq_bInter_ball
  statement: closedBall x ε = ⋂ δ > ε, ball x δ
  proof: by
  ext y; rw [mem_closedBall, ← forall_gt_iff_le, mem_iInter₂]; rfl

中文:
定理 closedBall_eq_bInter_ball
  结论: closedBall x ε = ⋂ δ > ε, ball x δ
  证明: by
  ext y; rw [mem_closedBall, ← forall_gt_iff_le, mem_iInter₂]; rfl

Depends on / 依赖: forall_gt_iff_le, mem_closedBall
-/
theorem closedBall_eq_bInter_ball : closedBall x ε = ⋂ δ > ε, ball x δ := by
  ext y; rw [mem_closedBall, ← forall_gt_iff_le, mem_iInter₂]; rfl

/--
theorem `ball_subset_ball'` / 定理 `ball_subset_ball'`

English:
theorem ball_subset_ball'
  given: (h : ε₁ + dist x y <= ε₂)
  statement: ball x ε₁ subseteq ball y ε₂
  proof: fun z hz =>
  calc
    dist z y <= dist z x + dist x y := dist_triangle _ _ _
    _ < ε₁ + dist x y := by gcongr; exact hz
    _ <= ε₂ := h

@[gcongr]

中文:
定理 ball_subset_ball'
  条件: (h : ε₁ + dist x y <= ε₂)
  结论: ball x ε₁ subseteq ball y ε₂
  证明: fun z hz =>
  calc
    dist z y <= dist z x + dist x y := dist_triangle _ _ _
    _ < ε₁ + dist x y := by gcongr; exact hz
    _ <= ε₂ := h

@[gcongr]
-/
theorem ball_subset_ball' (h : ε₁ + dist x y <= ε₂) : ball x ε₁ subseteq ball y ε₂ := fun z hz =>
  calc
    dist z y <= dist z x + dist x y := dist_triangle _ _ _
    _ < ε₁ + dist x y := by gcongr; exact hz
    _ <= ε₂ := h

@[gcongr]
/--
theorem `closedBall_subset_closedBall` / 定理 `closedBall_subset_closedBall`

English:
theorem closedBall_subset_closedBall
  given: (h : ε₁ <= ε₂)
  statement: closedBall x ε₁ subseteq closedBall x ε₂
  proof: fun _y (yx : _ <= ε₁) => le_trans yx h

中文:
定理 closedBall_subset_closedBall
  条件: (h : ε₁ <= ε₂)
  结论: closedBall x ε₁ subseteq closedBall x ε₂
  证明: fun _y (yx : _ <= ε₁) => le_trans yx h

Depends on / 依赖: le_trans
-/
theorem closedBall_subset_closedBall (h : ε₁ <= ε₂) : closedBall x ε₁ subseteq closedBall x ε₂ :=
  fun _y (yx : _ <= ε₁) => le_trans yx h

/--
theorem `closedBall_subset_closedBall'` / 定理 `closedBall_subset_closedBall'`

English:
theorem closedBall_subset_closedBall'
  given: (h : ε₁ + dist x y <= ε₂)
  proof: fun z hz =>
  calc
    dist z y <= dist z x + dist x y := dist_triangle _ _ _
    _ <= ε₁ + dist x y := by gcongr; exact hz
    _ <= ε₂ := h

中文:
定理 closedBall_subset_closedBall'
  条件: (h : ε₁ + dist x y <= ε₂)
  证明: fun z hz =>
  calc
    dist z y <= dist z x + dist x y := dist_triangle _ _ _
    _ <= ε₁ + dist x y := by gcongr; exact hz
    _ <= ε₂ := h
-/
theorem closedBall_subset_closedBall' (h : ε₁ + dist x y <= ε₂) :
    closedBall x ε₁ subseteq closedBall y ε₂ := fun z hz =>
  calc
    dist z y <= dist z x + dist x y := dist_triangle _ _ _
    _ <= ε₁ + dist x y := by gcongr; exact hz
    _ <= ε₂ := h

/--
theorem `closedBall_subset_ball` / 定理 `closedBall_subset_ball`

English:
theorem closedBall_subset_ball
  given: (h : ε₁ < ε₂)
  statement: closedBall x ε₁ subseteq ball x ε₂
  proof: fun y (yh : dist y x <= ε₁) => lt_of_le_of_lt yh h

中文:
定理 closedBall_subset_ball
  条件: (h : ε₁ < ε₂)
  结论: closedBall x ε₁ subseteq ball x ε₂
  证明: fun y (yh : dist y x <= ε₁) => lt_of_le_of_lt yh h

Depends on / 依赖: lt_of_le_of_lt
-/
theorem closedBall_subset_ball (h : ε₁ < ε₂) : closedBall x ε₁ subseteq ball x ε₂ :=
  fun y (yh : dist y x <= ε₁) => lt_of_le_of_lt yh h

/--
theorem `closedBall_subset_ball'` / 定理 `closedBall_subset_ball'`

English:
theorem closedBall_subset_ball'
  given: (h : ε₁ + dist x y < ε₂)
  proof: fun z hz =>
  calc
    dist z y <= dist z x + dist x y := dist_triangle _ _ _
    _ <= ε₁ + dist x y := by gcongr; exact hz
    _ < ε₂ := h

中文:
定理 closedBall_subset_ball'
  条件: (h : ε₁ + dist x y < ε₂)
  证明: fun z hz =>
  calc
    dist z y <= dist z x + dist x y := dist_triangle _ _ _
    _ <= ε₁ + dist x y := by gcongr; exact hz
    _ < ε₂ := h
-/
theorem closedBall_subset_ball' (h : ε₁ + dist x y < ε₂) :
    closedBall x ε₁ subseteq ball y ε₂ := fun z hz =>
  calc
    dist z y <= dist z x + dist x y := dist_triangle _ _ _
    _ <= ε₁ + dist x y := by gcongr; exact hz
    _ < ε₂ := h

/--
theorem `dist_le_add_of_nonempty_closedBall_inter_closedBall` / 定理 `dist_le_add_of_nonempty_closedBall_inter_closedBall`

English:
theorem dist_le_add_of_nonempty_closedBall_inter_closedBall
  proof: let ⟨z, hz⟩ := h
  calc
    dist x y <= dist z x + dist z y := dist_triangle_left _ _ _
    _ <= ε₁ + ε₂ := add_le_add hz.1 hz.2

中文:
定理 dist_le_add_of_nonempty_closedBall_inter_closedBall
  证明: let ⟨z, hz⟩ := h
  calc
    dist x y <= dist z x + dist z y := dist_triangle_left _ _ _
    _ <= ε₁ + ε₂ := add_le_add hz.1 hz.2

Depends on / 依赖: add_le_add, dist_triangle_left
-/
theorem dist_le_add_of_nonempty_closedBall_inter_closedBall
    (h : (closedBall x ε₁ inter closedBall y ε₂).Nonempty) : dist x y <= ε₁ + ε₂ :=
  let ⟨z, hz⟩ := h
  calc
    dist x y <= dist z x + dist z y := dist_triangle_left _ _ _
    _ <= ε₁ + ε₂ := add_le_add hz.1 hz.2

/--
theorem `dist_lt_add_of_nonempty_closedBall_inter_ball` / 定理 `dist_lt_add_of_nonempty_closedBall_inter_ball`

English:
theorem dist_lt_add_of_nonempty_closedBall_inter_ball
  given: (h : (closedBall x ε₁ inter ball y ε₂).Nonempty)
  proof: let ⟨z, hz⟩ := h
  calc
    dist x y <= dist z x + dist z y := dist_triangle_left _ _ _
    _ < ε₁ + ε₂ := add_lt_add_of_le_of_lt hz.1 hz.2

中文:
定理 dist_lt_add_of_nonempty_closedBall_inter_ball
  条件: (h : (closedBall x ε₁ inter ball y ε₂).Nonempty)
  证明: let ⟨z, hz⟩ := h
  calc
    dist x y <= dist z x + dist z y := dist_triangle_left _ _ _
    _ < ε₁ + ε₂ := add_lt_add_of_le_of_lt hz.1 hz.2

Depends on / 依赖: add_lt_add_of_le_of_lt, dist_triangle_left
-/
theorem dist_lt_add_of_nonempty_closedBall_inter_ball (h : (closedBall x ε₁ inter ball y ε₂).Nonempty) :
    dist x y < ε₁ + ε₂ :=
  let ⟨z, hz⟩ := h
  calc
    dist x y <= dist z x + dist z y := dist_triangle_left _ _ _
    _ < ε₁ + ε₂ := add_lt_add_of_le_of_lt hz.1 hz.2

/--
theorem `dist_lt_add_of_nonempty_ball_inter_closedBall` / 定理 `dist_lt_add_of_nonempty_ball_inter_closedBall`

English:
theorem dist_lt_add_of_nonempty_ball_inter_closedBall
  given: (h : (ball x ε₁ inter closedBall y ε₂).Nonempty)
  proof: by
  rw [inter_comm] at h
  rw [add_comm]; rw [dist_comm]
  exact dist_lt_add_of_nonempty_closedBall_inter_ball h

中文:
定理 dist_lt_add_of_nonempty_ball_inter_closedBall
  条件: (h : (ball x ε₁ inter closedBall y ε₂).Nonempty)
  证明: by
  rw [inter_comm] at h
  rw [add_comm]; rw [dist_comm]
  exact dist_lt_add_of_nonempty_closedBall_inter_ball h

Depends on / 依赖: add_comm, dist_comm, dist_lt_add_of_nonempty_closedBall_inter_ball, inter_comm
-/
theorem dist_lt_add_of_nonempty_ball_inter_closedBall (h : (ball x ε₁ inter closedBall y ε₂).Nonempty) :
    dist x y < ε₁ + ε₂ := by
  rw [inter_comm] at h
  rw [add_comm]; rw [dist_comm]
  exact dist_lt_add_of_nonempty_closedBall_inter_ball h

/--
theorem `dist_lt_add_of_nonempty_ball_inter_ball` / 定理 `dist_lt_add_of_nonempty_ball_inter_ball`

English:
theorem dist_lt_add_of_nonempty_ball_inter_ball
  given: (h : (ball x ε₁ inter ball y ε₂).Nonempty)
  proof: dist_lt_add_of_nonempty_closedBall_inter_ball
    h.mono (inter_subset_inter ball_subset_closedBall Subset.rfl)

@[simp]

中文:
定理 dist_lt_add_of_nonempty_ball_inter_ball
  条件: (h : (ball x ε₁ inter ball y ε₂).Nonempty)
  证明: dist_lt_add_of_nonempty_closedBall_inter_ball
    h.mono (inter_subset_inter ball_subset_closedBall Subset.rfl)

@[simp]

Depends on / 依赖: Subset, Subset.rfl, ball_subset_closedBall, dist_lt_add_of_nonempty_closedBall_inter_ball, h.mono, inter_subset_inter
-/
theorem dist_lt_add_of_nonempty_ball_inter_ball (h : (ball x ε₁ inter ball y ε₂).Nonempty) :
    dist x y < ε₁ + ε₂ :=
dist_lt_add_of_nonempty_closedBall_inter_ball
    h.mono (inter_subset_inter ball_subset_closedBall Subset.rfl)

@[simp]
/--
theorem `iUnion_closedBall_nat` / 定理 `iUnion_closedBall_nat`

English:
theorem iUnion_closedBall_nat
  given: (x : α)
  statement: ⋃ n : Nat, closedBall x n = univ
  proof: iUnion_eq_univ_iff.2 fun y => exists_nat_ge (dist y x)

中文:
定理 iUnion_closedBall_nat
  条件: (x : α)
  结论: ⋃ n : 自然数, closedBall x n = univ
  证明: iUnion_eq_univ_iff.2 fun y => exists_nat_ge (dist y x)

Depends on / 依赖: exists_nat_ge, iUnion_eq_univ_iff
-/
theorem iUnion_closedBall_nat (x : α) : ⋃ n : Nat, closedBall x n = univ :=
  iUnion_eq_univ_iff.2 fun y => exists_nat_ge (dist y x)

/--
theorem `iUnion_inter_closedBall_nat` / 定理 `iUnion_inter_closedBall_nat`

English:
theorem iUnion_inter_closedBall_nat
  given: (s : Set α) (x : α)
  statement: ⋃ n : Nat, s inter closedBall x n = s
  proof: by
  rw [← inter_iUnion]; rw [iUnion_closedBall_nat]; rw [inter_univ]

中文:
定理 iUnion_inter_closedBall_nat
  条件: (s : Set α) (x : α)
  结论: ⋃ n : 自然数, s inter closedBall x n = s
  证明: by
  rw [← inter_iUnion]; rw [iUnion_closedBall_nat]; rw [inter_univ]

Depends on / 依赖: iUnion_closedBall_nat, inter_iUnion, inter_univ
-/
theorem iUnion_inter_closedBall_nat (s : Set α) (x : α) : ⋃ n : Nat, s inter closedBall x n = s := by
  rw [← inter_iUnion]; rw [iUnion_closedBall_nat]; rw [inter_univ]

/--
theorem `ball_subset` / 定理 `ball_subset`

English:
theorem ball_subset
  given: (h : dist x y <= ε₂ - ε₁)
  statement: ball x ε₁ subseteq ball y ε₂
  proof: fun z zx => by
  rw [← add_sub_cancel ε₁ ε₂]
  exact lt_of_le_of_lt (dist_triangle z x y) (add_lt_add_of_lt_of_le zx h)

中文:
定理 ball_subset
  条件: (h : dist x y <= ε₂ - ε₁)
  结论: ball x ε₁ subseteq ball y ε₂
  证明: fun z zx => by
  rw [← add_sub_cancel ε₁ ε₂]
  exact lt_of_le_of_lt (dist_triangle z x y) (add_lt_add_of_lt_of_le zx h)

Depends on / 依赖: add_lt_add_of_lt_of_le, add_sub_cancel, dist_triangle, lt_of_le_of_lt
-/
theorem ball_subset (h : dist x y <= ε₂ - ε₁) : ball x ε₁ subseteq ball y ε₂ := fun z zx => by
  rw [← add_sub_cancel ε₁ ε₂]
  exact lt_of_le_of_lt (dist_triangle z x y) (add_lt_add_of_lt_of_le zx h)

/--
theorem `ball_half_subset` / 定理 `ball_half_subset`

English:
theorem ball_half_subset
  given: (y) (h : y in ball x (ε / 2))
  statement: ball y (ε / 2) subseteq ball x ε
  proof: ball_subset by rw [sub_self_div_two]; exact le_of_lt h

中文:
定理 ball_half_subset
  条件: (y) (h : y in ball x (ε / 2))
  结论: ball y (ε / 2) subseteq ball x ε
  证明: ball_subset by rw [sub_self_div_two]; exact le_of_lt h

Depends on / 依赖: ball_subset, le_of_lt, sub_self_div_two
-/
theorem ball_half_subset (y) (h : y in ball x (ε / 2)) : ball y (ε / 2) subseteq ball x ε :=
ball_subset by rw [sub_self_div_two]; exact le_of_lt h

/--
theorem `exists_ball_subset_ball` / 定理 `exists_ball_subset_ball`

English:
theorem exists_ball_subset_ball
  given: (h : y in ball x ε)
  statement: exists ε' > 0, ball y ε' subseteq ball x ε
  proof: ⟨_, sub_pos.2 h, ball_subset by rw [sub_sub_self]⟩

中文:
定理 exists_ball_subset_ball
  条件: (h : y in ball x ε)
  结论: 存在 ε' > 0, ball y ε' subseteq ball x ε
  证明: ⟨_, sub_pos.2 h, ball_subset by rw [sub_sub_self]⟩

Depends on / 依赖: ball_subset, sub_pos, sub_sub_self
-/
theorem exists_ball_subset_ball (h : y in ball x ε) : exists ε' > 0, ball y ε' subseteq ball x ε :=
⟨_, sub_pos.2 h, ball_subset by rw [sub_sub_self]⟩

/--
theorem `forall_of_forall_mem_closedBall` / 定理 `forall_of_forall_mem_closedBall`

English:
theorem forall_of_forall_mem_closedBall
  statement: (p : α -> Prop) (x : α)
  proof: by
  obtain ⟨R, hR, h⟩ : exists R >= dist y x, forall z : α, z in closedBall x R -> p z :=
    frequently_iff.1 H (Ici_mem_atTop (dist y x))
  exact h _ hR

中文:
定理 forall_of_forall_mem_closedBall
  结论: (p : α -> 命题) (x : α)
  证明: by
  obtain ⟨R, hR, h⟩ : exists R >= dist y x, forall z : α, z in closedBall x R -> p z :=
    frequently_iff.1 H (Ici_mem_atTop (dist y x))
  exact h _ hR

Depends on / 依赖: Ici_mem_atTop, closedBall, frequently_iff
-/
theorem forall_of_forall_mem_closedBall (p : α -> Prop) (x : α)
    (H : existsᶠ R : Real in atTop, forall y in closedBall x R, p y) (y : α) : p y := by
  obtain ⟨R, hR, h⟩ : exists R >= dist y x, forall z : α, z in closedBall x R -> p z :=
    frequently_iff.1 H (Ici_mem_atTop (dist y x))
  exact h _ hR

/--
theorem `forall_of_forall_mem_ball` / 定理 `forall_of_forall_mem_ball`

English:
theorem forall_of_forall_mem_ball
  statement: (p : α -> Prop) (x : α)
  proof: by
  obtain ⟨R, hR, h⟩ : exists R > dist y x, forall z : α, z in ball x R -> p z :=
    frequently_iff.1 H (Ioi_mem_atTop (dist y x))
  exact h _ hR

中文:
定理 forall_of_forall_mem_ball
  结论: (p : α -> 命题) (x : α)
  证明: by
  obtain ⟨R, hR, h⟩ : exists R > dist y x, forall z : α, z in ball x R -> p z :=
    frequently_iff.1 H (Ioi_mem_atTop (dist y x))
  exact h _ hR

Depends on / 依赖: Ioi_mem_atTop, frequently_iff
-/
theorem forall_of_forall_mem_ball (p : α -> Prop) (x : α)
    (H : existsᶠ R : Real in atTop, forall y in ball x R, p y) (y : α) : p y := by
  obtain ⟨R, hR, h⟩ : exists R > dist y x, forall z : α, z in ball x R -> p z :=
    frequently_iff.1 H (Ioi_mem_atTop (dist y x))
  exact h _ hR

/--
theorem `isBounded_iff` / 定理 `isBounded_iff`

English:
theorem isBounded_iff
  given: {s : Set α}
  proof: by
  rw [isBounded_def]; rw [← Filter.mem_sets]; rw [@PseudoMetricSpace.cobounded_sets α]; rw [mem_ofPred_eq]; rw [compl_compl]

中文:
定理 isBounded_iff
  条件: {s : Set α}
  证明: by
  rw [isBounded_def]; rw [← Filter.mem_sets]; rw [@PseudoMetricSpace.cobounded_sets α]; rw [mem_ofPred_eq]; rw [compl_compl]

Depends on / 依赖: Filter, Filter.mem_sets, PseudoMetricSpace, PseudoMetricSpace.cobounded_sets, cobounded_sets, compl_compl, isBounded_def, mem_ofPred_eq, mem_sets
-/
theorem isBounded_iff {s : Set α} :
    IsBounded s ↔ exists C : Real, forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> dist x y <= C := by
  rw [isBounded_def]; rw [← Filter.mem_sets]; rw [@PseudoMetricSpace.cobounded_sets α]; rw [mem_ofPred_eq]; rw [compl_compl]

/--
lemma `boundedSpace_iff` / 引理 `boundedSpace_iff`

English:
lemma boundedSpace_iff
  statement: BoundedSpace α ↔ exists C, forall a b : α, dist a b <= C
  proof: by
  rw [← isBounded_univ]; rw [Metric.isBounded_iff]
  simp

中文:
引理 boundedSpace_iff
  结论: BoundedSpace α ↔ 存在 C, 对任意 a b : α, dist a b <= C
  证明: by
  rw [← isBounded_univ]; rw [Metric.isBounded_iff]
  simp

Depends on / 依赖: Metric, Metric.isBounded_iff, isBounded_iff, isBounded_univ
-/
lemma boundedSpace_iff : BoundedSpace α ↔ exists C, forall a b : α, dist a b <= C := by
  rw [← isBounded_univ]; rw [Metric.isBounded_iff]
  simp

/--
theorem `isBounded_iff_eventually` / 定理 `isBounded_iff_eventually`

English:
theorem isBounded_iff_eventually
  given: {s : Set α}
  proof: isBounded_iff.trans
    ⟨fun ⟨C, h⟩ => eventually_atTop.2 ⟨C, fun _C' hC' _x hx _y hy => (h hx hy).trans hC'⟩,
      Eventually.exists⟩

中文:
定理 isBounded_iff_eventually
  条件: {s : Set α}
  证明: isBounded_iff.trans
    ⟨fun ⟨C, h⟩ => eventually_atTop.2 ⟨C, fun _C' hC' _x hx _y hy => (h hx hy).trans hC'⟩,
      Eventually.exists⟩

Depends on / 依赖: Eventually, Eventually.exists, eventually_atTop, isBounded_iff, isBounded_iff.trans
-/
theorem isBounded_iff_eventually {s : Set α} :
    IsBounded s ↔ forallᶠ C in atTop, forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> dist x y <= C :=
  isBounded_iff.trans
    ⟨fun ⟨C, h⟩ => eventually_atTop.2 ⟨C, fun _C' hC' _x hx _y hy => (h hx hy).trans hC'⟩,
      Eventually.exists⟩

/--
theorem `isBounded_iff_exists_ge` / 定理 `isBounded_iff_exists_ge`

English:
theorem isBounded_iff_exists_ge
  given: {s : Set α} (c : Real)
  proof: ⟨fun h => ((eventually_ge_atTop c).and (isBounded_iff_eventually.1 h)).exists, fun h =>
isBounded_iff.2 h.imp fun _ => And.right⟩

中文:
定理 isBounded_iff_exists_ge
  条件: {s : Set α} (c : 实数)
  证明: ⟨fun h => ((eventually_ge_atTop c).and (isBounded_iff_eventually.1 h)).exists, fun h =>
isBounded_iff.2 h.imp fun _ => And.right⟩

Depends on / 依赖: And.right, eventually_ge_atTop, h.imp, isBounded_iff, isBounded_iff_eventually
-/
theorem isBounded_iff_exists_ge {s : Set α} (c : Real) :
    IsBounded s ↔ exists C, c <= C ∧ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> dist x y <= C :=
  ⟨fun h => ((eventually_ge_atTop c).and (isBounded_iff_eventually.1 h)).exists, fun h =>
isBounded_iff.2 h.imp fun _ => And.right⟩

/--
theorem `isBounded_iff_nndist` / 定理 `isBounded_iff_nndist`

English:
theorem isBounded_iff_nndist
  given: {s : Set α}
  proof: by
  simp only [isBounded_iff_exists_ge 0, NNReal.exists, ← NNReal.coe_le_coe, ← dist_nndist,
    NNReal.coe_mk, exists_prop]

中文:
定理 isBounded_iff_nndist
  条件: {s : Set α}
  证明: by
  simp only [isBounded_iff_exists_ge 0, NNReal.exists, ← NNReal.coe_le_coe, ← dist_nndist,
    NNReal.coe_mk, exists_prop]

Depends on / 依赖: NNReal, NNReal.coe_le_coe, NNReal.coe_mk, NNReal.exists, coe_le_coe, coe_mk, dist_nndist, exists_prop, isBounded_iff_exists_ge
-/
theorem isBounded_iff_nndist {s : Set α} :
    IsBounded s ↔ exists C : Real>=0, forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> nndist x y <= C := by
  simp only [isBounded_iff_exists_ge 0, NNReal.exists, ← NNReal.coe_le_coe, ← dist_nndist,
    NNReal.coe_mk, exists_prop]

/--
lemma `boundedSpace_iff_nndist` / 引理 `boundedSpace_iff_nndist`

English:
lemma boundedSpace_iff_nndist
  statement: BoundedSpace α ↔ exists C, forall a b : α, nndist a b <= C
  proof: by
  rw [← isBounded_univ]; rw [Metric.isBounded_iff_nndist]
  simp

中文:
引理 boundedSpace_iff_nndist
  结论: BoundedSpace α ↔ 存在 C, 对任意 a b : α, nndist a b <= C
  证明: by
  rw [← isBounded_univ]; rw [Metric.isBounded_iff_nndist]
  simp

Depends on / 依赖: Metric, Metric.isBounded_iff_nndist, isBounded_iff_nndist, isBounded_univ
-/
lemma boundedSpace_iff_nndist : BoundedSpace α ↔ exists C, forall a b : α, nndist a b <= C := by
  rw [← isBounded_univ]; rw [Metric.isBounded_iff_nndist]
  simp

/--
lemma `boundedSpace_iff_edist` / 引理 `boundedSpace_iff_edist`

English:
lemma boundedSpace_iff_edist
  statement: BoundedSpace α ↔ exists C : Real>=0, forall a b : α, edist a b <= C
  proof: by
  simp [Metric.boundedSpace_iff_nndist]

中文:
引理 boundedSpace_iff_edist
  结论: BoundedSpace α ↔ 存在 C : 实数>=0, 对任意 a b : α, edist a b <= C
  证明: by
  simp [Metric.boundedSpace_iff_nndist]

Depends on / 依赖: Metric, Metric.boundedSpace_iff_nndist, boundedSpace_iff_nndist
-/
lemma boundedSpace_iff_edist : BoundedSpace α ↔ exists C : Real>=0, forall a b : α, edist a b <= C := by
  simp [Metric.boundedSpace_iff_nndist]

/--
theorem `toUniformSpace_eq` / 定理 `toUniformSpace_eq`

English:
theorem toUniformSpace_eq
  proof: UniformSpace.ext PseudoMetricSpace.uniformity_dist

中文:
定理 toUniformSpace_eq
  证明: UniformSpace.ext PseudoMetricSpace.uniformity_dist

Depends on / 依赖: PseudoMetricSpace, PseudoMetricSpace.uniformity_dist, UniformSpace, UniformSpace.ext, uniformity_dist
-/
theorem toUniformSpace_eq :
    ‹PseudoMetricSpace α›.toUniformSpace = .ofDist dist dist_self dist_comm dist_triangle :=
  UniformSpace.ext PseudoMetricSpace.uniformity_dist

/--
theorem `uniformity_basis_dist` / 定理 `uniformity_basis_dist`

English:
theorem uniformity_basis_dist
  proof: by
  rw [toUniformSpace_eq]
  exact UniformSpace.hasBasis_ofFun (exists_gt _) _ _ _ _ _

中文:
定理 uniformity_basis_dist
  证明: by
  rw [toUniformSpace_eq]
  exact UniformSpace.hasBasis_ofFun (exists_gt _) _ _ _ _ _

Depends on / 依赖: UniformSpace, UniformSpace.hasBasis_ofFun, exists_gt, hasBasis_ofFun, toUniformSpace_eq
-/
theorem uniformity_basis_dist :
    (𝓤 α).HasBasis (fun ε : Real => 0 < ε) fun ε => { p : α × α | dist p.1 p.2 < ε } := by
  rw [toUniformSpace_eq]
  exact UniformSpace.hasBasis_ofFun (exists_gt _) _ _ _ _ _

/--
theorem `mk_uniformity_basis` / 定理 `mk_uniformity_basis`

English:
theorem mk_uniformity_basis
  statement: {β : Type*} {p : β -> Prop} {f : β -> Real}
  proof: by
  refine ⟨fun s => uniformity_basis_dist.mem_iff.trans ?_⟩
  constructor
  · rintro ⟨ε, ε₀, hε⟩
    rcases hf ε₀ with ⟨i, hi, H⟩
exact ⟨i, hi, fun x (hx : _ < _) => hε lt_of_lt_of_le hx H⟩
  · exact fun ⟨i, hi, H⟩ => ⟨f i, hf₀ i hi, H⟩

中文:
定理 mk_uniformity_basis
  结论: {β : 类型} {p : β -> 命题} {f : β -> 实数}
  证明: by
  refine ⟨fun s => uniformity_basis_dist.mem_iff.trans ?_⟩
  constructor
  · rintro ⟨ε, ε₀, hε⟩
    rcases hf ε₀ with ⟨i, hi, H⟩
exact ⟨i, hi, fun x (hx : _ < _) => hε lt_of_lt_of_le hx H⟩
  · exact fun ⟨i, hi, H⟩ => ⟨f i, hf₀ i hi, H⟩
-/
protected theorem mk_uniformity_basis {β : Type*} {p : β -> Prop} {f : β -> Real}
    (hf₀ : forall i, p i -> 0 < f i) (hf : forall ⦃ε⦄, 0 < ε -> exists i, p i ∧ f i <= ε) :
    (𝓤 α).HasBasis p fun i => { p : α × α | dist p.1 p.2 < f i } := by
  refine ⟨fun s => uniformity_basis_dist.mem_iff.trans ?_⟩
  constructor
  · rintro ⟨ε, ε₀, hε⟩
    rcases hf ε₀ with ⟨i, hi, H⟩
exact ⟨i, hi, fun x (hx : _ < _) => hε lt_of_lt_of_le hx H⟩
  · exact fun ⟨i, hi, H⟩ => ⟨f i, hf₀ i hi, H⟩

/--
theorem `uniformity_basis_dist_rat` / 定理 `uniformity_basis_dist_rat`

English:
theorem uniformity_basis_dist_rat
  proof: Metric.mk_uniformity_basis (fun _ => Rat.cast_pos.2) fun _ε hε =>
    let ⟨r, hr0, hrε⟩ := exists_rat_btwn hε
    ⟨r, Rat.cast_pos.1 hr0, hrε.le⟩

中文:
定理 uniformity_basis_dist_rat
  证明: Metric.mk_uniformity_basis (fun _ => Rat.cast_pos.2) fun _ε hε =>
    let ⟨r, hr0, hrε⟩ := exists_rat_btwn hε
    ⟨r, Rat.cast_pos.1 hr0, hrε.le⟩

Depends on / 依赖: Metric, Metric.mk_uniformity_basis, Rat.cast_pos, cast_pos, exists_rat_btwn, mk_uniformity_basis
-/
theorem uniformity_basis_dist_rat :
    (𝓤 α).HasBasis (fun r : Rat => 0 < r) fun r => { p : α × α | dist p.1 p.2 < r } :=
  Metric.mk_uniformity_basis (fun _ => Rat.cast_pos.2) fun _ε hε =>
    let ⟨r, hr0, hrε⟩ := exists_rat_btwn hε
    ⟨r, Rat.cast_pos.1 hr0, hrε.le⟩

/--
theorem `uniformity_basis_dist_inv_nat_succ` / 定理 `uniformity_basis_dist_inv_nat_succ`

English:
theorem uniformity_basis_dist_inv_nat_succ
  proof: Metric.mk_uniformity_basis (fun n _ => div_pos zero_lt_one <| Nat.cast_add_one_pos n) fun _ε ε0 =>
    (exists_nat_one_div_lt ε0).imp fun _n hn => ⟨trivial, le_of_lt hn⟩

中文:
定理 uniformity_basis_dist_inv_nat_succ
  证明: Metric.mk_uniformity_basis (fun n _ => div_pos zero_lt_one <| Nat.cast_add_one_pos n) fun _ε ε0 =>
    (exists_nat_one_div_lt ε0).imp fun _n hn => ⟨trivial, le_of_lt hn⟩

Depends on / 依赖: Metric, Metric.mk_uniformity_basis, Nat.cast_add_one_pos, cast_add_one_pos, div_pos, exists_nat_one_div_lt, le_of_lt, mk_uniformity_basis, zero_lt_one
-/
theorem uniformity_basis_dist_inv_nat_succ :
    (𝓤 α).HasBasis (fun _ => True) fun n : Nat => { p : α × α | dist p.1 p.2 < 1 / (↑n + 1) } :=
  Metric.mk_uniformity_basis (fun n _ => div_pos zero_lt_one <| Nat.cast_add_one_pos n) fun _ε ε0 =>
    (exists_nat_one_div_lt ε0).imp fun _n hn => ⟨trivial, le_of_lt hn⟩

/--
theorem `uniformity_basis_dist_inv_nat_pos` / 定理 `uniformity_basis_dist_inv_nat_pos`

English:
theorem uniformity_basis_dist_inv_nat_pos
  proof: Metric.mk_uniformity_basis (fun _ hn => div_pos zero_lt_one <| Nat.cast_pos.2 hn) fun _ ε0 =>
    let ⟨n, hn⟩ := exists_nat_one_div_lt ε0
    ⟨n + 1, Nat.succ_pos n, mod_cast hn.le⟩

中文:
定理 uniformity_basis_dist_inv_nat_pos
  证明: Metric.mk_uniformity_basis (fun _ hn => div_pos zero_lt_one <| Nat.cast_pos.2 hn) fun _ ε0 =>
    let ⟨n, hn⟩ := exists_nat_one_div_lt ε0
    ⟨n + 1, Nat.succ_pos n, mod_cast hn.le⟩

Depends on / 依赖: Metric, Metric.mk_uniformity_basis, Nat.cast_pos, Nat.succ_pos, cast_pos, div_pos, exists_nat_one_div_lt, hn.le, mk_uniformity_basis, mod_cast, succ_pos, zero_lt_one
-/
theorem uniformity_basis_dist_inv_nat_pos :
    (𝓤 α).HasBasis (fun n : Nat => 0 < n) fun n : Nat => { p : α × α | dist p.1 p.2 < 1 / ↑n } :=
  Metric.mk_uniformity_basis (fun _ hn => div_pos zero_lt_one <| Nat.cast_pos.2 hn) fun _ ε0 =>
    let ⟨n, hn⟩ := exists_nat_one_div_lt ε0
    ⟨n + 1, Nat.succ_pos n, mod_cast hn.le⟩

/--
theorem `uniformity_basis_dist_pow` / 定理 `uniformity_basis_dist_pow`

English:
theorem uniformity_basis_dist_pow
  given: {r : Real} (h0 : 0 < r) (h1 : r < 1)
  proof: Metric.mk_uniformity_basis (fun _ _ => pow_pos h0 _) fun _ε ε0 =>
    let ⟨n, hn⟩ := exists_pow_lt_of_lt_one ε0 h1
    ⟨n, trivial, hn.le⟩

中文:
定理 uniformity_basis_dist_pow
  条件: {r : 实数} (h0 : 0 < r) (h1 : r < 1)
  证明: Metric.mk_uniformity_basis (fun _ _ => pow_pos h0 _) fun _ε ε0 =>
    let ⟨n, hn⟩ := exists_pow_lt_of_lt_one ε0 h1
    ⟨n, trivial, hn.le⟩

Depends on / 依赖: Metric, Metric.mk_uniformity_basis, exists_pow_lt_of_lt_one, hn.le, mk_uniformity_basis, pow_pos
-/
theorem uniformity_basis_dist_pow {r : Real} (h0 : 0 < r) (h1 : r < 1) :
    (𝓤 α).HasBasis (fun _ : Nat => True) fun n : Nat => { p : α × α | dist p.1 p.2 < r ^ n } :=
  Metric.mk_uniformity_basis (fun _ _ => pow_pos h0 _) fun _ε ε0 =>
    let ⟨n, hn⟩ := exists_pow_lt_of_lt_one ε0 h1
    ⟨n, trivial, hn.le⟩

/--
theorem `uniformity_basis_dist_lt` / 定理 `uniformity_basis_dist_lt`

English:
theorem uniformity_basis_dist_lt
  given: {R : Real} (hR : 0 < R)
  proof: Metric.mk_uniformity_basis (fun _ => And.left) fun r hr =>
⟨min r (R / 2), ⟨lt_min hr (half_pos hR), min_lt_iff.2 Or.inr (half_lt_self hR)⟩,
      min_le_left _ _⟩

中文:
定理 uniformity_basis_dist_lt
  条件: {R : 实数} (hR : 0 < R)
  证明: Metric.mk_uniformity_basis (fun _ => And.left) fun r hr =>
⟨min r (R / 2), ⟨lt_min hr (half_pos hR), min_lt_iff.2 Or.inr (half_lt_self hR)⟩,
      min_le_left _ _⟩

Depends on / 依赖: And.left, Metric, Metric.mk_uniformity_basis, Or.inr, half_lt_self, half_pos, lt_min, min_le_left, min_lt_iff, mk_uniformity_basis
-/
theorem uniformity_basis_dist_lt {R : Real} (hR : 0 < R) :
    (𝓤 α).HasBasis (fun r : Real => 0 < r ∧ r < R) fun r => { p : α × α | dist p.1 p.2 < r } :=
  Metric.mk_uniformity_basis (fun _ => And.left) fun r hr =>
⟨min r (R / 2), ⟨lt_min hr (half_pos hR), min_lt_iff.2 Or.inr (half_lt_self hR)⟩,
      min_le_left _ _⟩

/--
theorem `mk_uniformity_basis_le` / 定理 `mk_uniformity_basis_le`

English:
theorem mk_uniformity_basis_le
  statement: {β : Type*} {p : β -> Prop} {f : β -> Real}
  proof: by
  refine ⟨fun s => uniformity_basis_dist.mem_iff.trans ?_⟩
  constructor
  · rintro ⟨ε, ε₀, hε⟩
    rcases exists_between ε₀ with ⟨ε', hε'⟩
    rcases hf ε' hε'.1 with ⟨i, hi, H⟩
exact ⟨i, hi, fun x (hx : _ <= _) => hε lt_of_le_of_lt (le_trans hx H) hε'.2⟩
  · exact fun ⟨i, hi, H⟩ => ⟨f i, hf₀ i 

中文:
定理 mk_uniformity_basis_le
  结论: {β : 类型} {p : β -> 命题} {f : β -> 实数}
  证明: by
  refine ⟨fun s => uniformity_basis_dist.mem_iff.trans ?_⟩
  constructor
  · rintro ⟨ε, ε₀, hε⟩
    rcases exists_between ε₀ with ⟨ε', hε'⟩
    rcases hf ε' hε'.1 with ⟨i, hi, H⟩
exact ⟨i, hi, fun x (hx : _ <= _) => hε lt_of_le_of_lt (le_trans hx H) hε'.2⟩
  · exact fun ⟨i, hi, H⟩ => ⟨f i, hf₀ i 
-/
protected theorem mk_uniformity_basis_le {β : Type*} {p : β -> Prop} {f : β -> Real}
    (hf₀ : forall x, p x -> 0 < f x) (hf : forall ε, 0 < ε -> exists x, p x ∧ f x <= ε) :
    (𝓤 α).HasBasis p fun x => { p : α × α | dist p.1 p.2 <= f x } := by
  refine ⟨fun s => uniformity_basis_dist.mem_iff.trans ?_⟩
  constructor
  · rintro ⟨ε, ε₀, hε⟩
    rcases exists_between ε₀ with ⟨ε', hε'⟩
    rcases hf ε' hε'.1 with ⟨i, hi, H⟩
exact ⟨i, hi, fun x (hx : _ <= _) => hε lt_of_le_of_lt (le_trans hx H) hε'.2⟩
  · exact fun ⟨i, hi, H⟩ => ⟨f i, hf₀ i hi, fun x (hx : _ < _) => H (mem_ofPred.2 hx.le)⟩

/--
theorem `uniformity_basis_dist_le` / 定理 `uniformity_basis_dist_le`

English:
theorem uniformity_basis_dist_le
  proof: Metric.mk_uniformity_basis_le (fun _ => id) fun ε ε₀ => ⟨ε, ε₀, le_refl ε⟩

中文:
定理 uniformity_basis_dist_le
  证明: Metric.mk_uniformity_basis_le (fun _ => id) fun ε ε₀ => ⟨ε, ε₀, le_refl ε⟩

Depends on / 依赖: Metric, Metric.mk_uniformity_basis_le, le_refl, mk_uniformity_basis_le
-/
theorem uniformity_basis_dist_le :
    (𝓤 α).HasBasis ((0 : Real) < ·) fun ε => { p : α × α | dist p.1 p.2 <= ε } :=
  Metric.mk_uniformity_basis_le (fun _ => id) fun ε ε₀ => ⟨ε, ε₀, le_refl ε⟩

/--
theorem `uniformity_basis_dist_le_inv_nat_succ` / 定理 `uniformity_basis_dist_le_inv_nat_succ`

English:
theorem uniformity_basis_dist_le_inv_nat_succ
  proof: Metric.mk_uniformity_basis_le (fun n _ => div_pos zero_lt_one <| Nat.cast_add_one_pos n)
    fun _ε ε0 => (exists_nat_one_div_lt ε0).imp fun _n hn => ⟨trivial, hn.le⟩

中文:
定理 uniformity_basis_dist_le_inv_nat_succ
  证明: Metric.mk_uniformity_basis_le (fun n _ => div_pos zero_lt_one <| Nat.cast_add_one_pos n)
    fun _ε ε0 => (exists_nat_one_div_lt ε0).imp fun _n hn => ⟨trivial, hn.le⟩

Depends on / 依赖: Metric, Metric.mk_uniformity_basis_le, Nat.cast_add_one_pos, cast_add_one_pos, div_pos, exists_nat_one_div_lt, hn.le, mk_uniformity_basis_le, zero_lt_one
-/
theorem uniformity_basis_dist_le_inv_nat_succ :
    (𝓤 α).HasBasis (fun _ => True) fun n : Nat => { p : α × α | dist p.1 p.2 <= 1 / (↑n + 1) } :=
  Metric.mk_uniformity_basis_le (fun n _ => div_pos zero_lt_one <| Nat.cast_add_one_pos n)
    fun _ε ε0 => (exists_nat_one_div_lt ε0).imp fun _n hn => ⟨trivial, hn.le⟩

/--
theorem `uniformity_basis_dist_le_inv_nat_pos` / 定理 `uniformity_basis_dist_le_inv_nat_pos`

English:
theorem uniformity_basis_dist_le_inv_nat_pos
  proof: Metric.mk_uniformity_basis_le (fun n hn => div_pos zero_lt_one <| Nat.cast_pos.2 hn) fun _ε ε0 =>
    let ⟨n, hn⟩ := exists_nat_one_div_lt ε0
    ⟨n + 1, n.succ_pos, by simpa using hn.le⟩

中文:
定理 uniformity_basis_dist_le_inv_nat_pos
  证明: Metric.mk_uniformity_basis_le (fun n hn => div_pos zero_lt_one <| Nat.cast_pos.2 hn) fun _ε ε0 =>
    let ⟨n, hn⟩ := exists_nat_one_div_lt ε0
    ⟨n + 1, n.succ_pos, by simpa using hn.le⟩

Depends on / 依赖: Metric, Metric.mk_uniformity_basis_le, Nat.cast_pos, cast_pos, div_pos, exists_nat_one_div_lt, hn.le, mk_uniformity_basis_le, n.succ_pos, succ_pos, zero_lt_one
-/
theorem uniformity_basis_dist_le_inv_nat_pos :
    (𝓤 α).HasBasis (fun n : Nat => 0 < n) fun n : Nat => { p : α × α | dist p.1 p.2 <= 1 / ↑n } :=
  Metric.mk_uniformity_basis_le (fun n hn => div_pos zero_lt_one <| Nat.cast_pos.2 hn) fun _ε ε0 =>
    let ⟨n, hn⟩ := exists_nat_one_div_lt ε0
    ⟨n + 1, n.succ_pos, by simpa using hn.le⟩

/--
theorem `uniformity_basis_dist_le_pow` / 定理 `uniformity_basis_dist_le_pow`

English:
theorem uniformity_basis_dist_le_pow
  given: {r : Real} (h0 : 0 < r) (h1 : r < 1)
  proof: Metric.mk_uniformity_basis_le (fun _ _ => pow_pos h0 _) fun _ε ε0 =>
    let ⟨n, hn⟩ := exists_pow_lt_of_lt_one ε0 h1
    ⟨n, trivial, hn.le⟩

中文:
定理 uniformity_basis_dist_le_pow
  条件: {r : 实数} (h0 : 0 < r) (h1 : r < 1)
  证明: Metric.mk_uniformity_basis_le (fun _ _ => pow_pos h0 _) fun _ε ε0 =>
    let ⟨n, hn⟩ := exists_pow_lt_of_lt_one ε0 h1
    ⟨n, trivial, hn.le⟩

Depends on / 依赖: Metric, Metric.mk_uniformity_basis_le, exists_pow_lt_of_lt_one, hn.le, mk_uniformity_basis_le, pow_pos
-/
theorem uniformity_basis_dist_le_pow {r : Real} (h0 : 0 < r) (h1 : r < 1) :
    (𝓤 α).HasBasis (fun _ : Nat => True) fun n : Nat => { p : α × α | dist p.1 p.2 <= r ^ n } :=
  Metric.mk_uniformity_basis_le (fun _ _ => pow_pos h0 _) fun _ε ε0 =>
    let ⟨n, hn⟩ := exists_pow_lt_of_lt_one ε0 h1
    ⟨n, trivial, hn.le⟩

/--
theorem `mem_uniformity_dist` / 定理 `mem_uniformity_dist`

English:
theorem mem_uniformity_dist
  given: {s : Set (α × α)}
  proof: uniformity_basis_dist.mem_uniformity_iff

中文:
定理 mem_uniformity_dist
  条件: {s : Set (α × α)}
  证明: uniformity_basis_dist.mem_uniformity_iff

Depends on / 依赖: mem_uniformity_iff, uniformity_basis_dist, uniformity_basis_dist.mem_uniformity_iff
-/
theorem mem_uniformity_dist {s : Set (α × α)} :
    s in 𝓤 α ↔ exists ε > 0, forall ⦃a b : α⦄, dist a b < ε -> (a, b) in s :=
  uniformity_basis_dist.mem_uniformity_iff

/--
theorem `dist_mem_uniformity` / 定理 `dist_mem_uniformity`

English:
theorem dist_mem_uniformity
  given: {ε : Real} (ε0 : 0 < ε)
  statement: { p : α × α | dist p.1 p.2 < ε } in 𝓤 α
  proof: mem_uniformity_dist.2 ⟨ε, ε0, fun _ _ => id⟩

中文:
定理 dist_mem_uniformity
  条件: {ε : 实数} (ε0 : 0 < ε)
  结论: { p : α × α | dist p.1 p.2 < ε } in 𝓤 α
  证明: mem_uniformity_dist.2 ⟨ε, ε0, fun _ _ => id⟩

Depends on / 依赖: mem_uniformity_dist
-/
theorem dist_mem_uniformity {ε : Real} (ε0 : 0 < ε) : { p : α × α | dist p.1 p.2 < ε } in 𝓤 α :=
  mem_uniformity_dist.2 ⟨ε, ε0, fun _ _ => id⟩

/--
theorem `uniformContinuous_iff` / 定理 `uniformContinuous_iff`

English:
theorem uniformContinuous_iff
  given: [PseudoMetricSpace β] {f : α -> β}
  proof: uniformity_basis_dist.uniformContinuous_iff uniformity_basis_dist

中文:
定理 uniformContinuous_iff
  条件: [PseudoMetricSpace β] {f : α -> β}
  证明: uniformity_basis_dist.uniformContinuous_iff uniformity_basis_dist

Depends on / 依赖: uniformContinuous_iff, uniformity_basis_dist, uniformity_basis_dist.uniformContinuous_iff
-/
theorem uniformContinuous_iff [PseudoMetricSpace β] {f : α -> β} :
    UniformContinuous f ↔ forall ε > 0, exists δ > 0, forall ⦃a b : α⦄, dist a b < δ -> dist (f a) (f b) < ε :=
  uniformity_basis_dist.uniformContinuous_iff uniformity_basis_dist

/--
theorem `uniformContinuousOn_iff` / 定理 `uniformContinuousOn_iff`

English:
theorem uniformContinuousOn_iff
  given: [PseudoMetricSpace β] {f : α -> β} {s : Set α}
  proof: uniformity_basis_dist.uniformContinuousOn_iff uniformity_basis_dist

中文:
定理 uniformContinuousOn_iff
  条件: [PseudoMetricSpace β] {f : α -> β} {s : Set α}
  证明: uniformity_basis_dist.uniformContinuousOn_iff uniformity_basis_dist

Depends on / 依赖: uniformContinuousOn_iff, uniformity_basis_dist, uniformity_basis_dist.uniformContinuousOn_iff
-/
theorem uniformContinuousOn_iff [PseudoMetricSpace β] {f : α -> β} {s : Set α} :
    UniformContinuousOn f s ↔
      forall ε > 0, exists δ > 0, forall x in s, forall y in s, dist x y < δ -> dist (f x) (f y) < ε :=
  uniformity_basis_dist.uniformContinuousOn_iff uniformity_basis_dist

/--
theorem `uniformContinuous_iff_le` / 定理 `uniformContinuous_iff_le`

English:
theorem uniformContinuous_iff_le
  given: [PseudoMetricSpace β] {f : α -> β}
  proof: uniformity_basis_dist_le.uniformContinuous_iff uniformity_basis_dist_le

中文:
定理 uniformContinuous_iff_le
  条件: [PseudoMetricSpace β] {f : α -> β}
  证明: uniformity_basis_dist_le.uniformContinuous_iff uniformity_basis_dist_le

Depends on / 依赖: uniformContinuous_iff, uniformity_basis_dist_le, uniformity_basis_dist_le.uniformContinuous_iff
-/
theorem uniformContinuous_iff_le [PseudoMetricSpace β] {f : α -> β} :
    UniformContinuous f ↔ forall ε > 0, exists δ > 0, forall ⦃a b : α⦄, dist a b <= δ -> dist (f a) (f b) <= ε :=
  uniformity_basis_dist_le.uniformContinuous_iff uniformity_basis_dist_le

/--
theorem `uniformContinuousOn_iff_le` / 定理 `uniformContinuousOn_iff_le`

English:
theorem uniformContinuousOn_iff_le
  given: [PseudoMetricSpace β] {f : α -> β} {s : Set α}
  proof: uniformity_basis_dist_le.uniformContinuousOn_iff uniformity_basis_dist_le

中文:
定理 uniformContinuousOn_iff_le
  条件: [PseudoMetricSpace β] {f : α -> β} {s : Set α}
  证明: uniformity_basis_dist_le.uniformContinuousOn_iff uniformity_basis_dist_le

Depends on / 依赖: uniformContinuousOn_iff, uniformity_basis_dist_le, uniformity_basis_dist_le.uniformContinuousOn_iff
-/
theorem uniformContinuousOn_iff_le [PseudoMetricSpace β] {f : α -> β} {s : Set α} :
    UniformContinuousOn f s ↔
      forall ε > 0, exists δ > 0, forall x in s, forall y in s, dist x y <= δ -> dist (f x) (f y) <= ε :=
  uniformity_basis_dist_le.uniformContinuousOn_iff uniformity_basis_dist_le

/--
theorem `nhds_basis_ball` / 定理 `nhds_basis_ball`

English:
theorem nhds_basis_ball
  statement: (𝓝 x).HasBasis (0 < ·) (ball x)
  proof: nhds_basis_uniformity uniformity_basis_dist

中文:
定理 nhds_basis_ball
  结论: (𝓝 x).HasBasis (0 < ·) (ball x)
  证明: nhds_basis_uniformity uniformity_basis_dist

Depends on / 依赖: nhds_basis_uniformity, uniformity_basis_dist
-/
theorem nhds_basis_ball : (𝓝 x).HasBasis (0 < ·) (ball x) :=
  nhds_basis_uniformity uniformity_basis_dist

/--
theorem `mem_nhds_iff` / 定理 `mem_nhds_iff`

English:
theorem mem_nhds_iff
  statement: s in 𝓝 x ↔ exists ε > 0, ball x ε subseteq s
  proof: nhds_basis_ball.mem_iff

中文:
定理 mem_nhds_iff
  结论: s in 𝓝 x ↔ 存在 ε > 0, ball x ε subseteq s
  证明: nhds_basis_ball.mem_iff

Depends on / 依赖: mem_iff, nhds_basis_ball, nhds_basis_ball.mem_iff
-/
theorem mem_nhds_iff : s in 𝓝 x ↔ exists ε > 0, ball x ε subseteq s :=
  nhds_basis_ball.mem_iff

/--
theorem `eventually_nhds_iff` / 定理 `eventually_nhds_iff`

English:
theorem eventually_nhds_iff
  given: {p : α -> Prop}
  proof: mem_nhds_iff

中文:
定理 eventually_nhds_iff
  条件: {p : α -> 命题}
  证明: mem_nhds_iff

Depends on / 依赖: mem_nhds_iff
-/
theorem eventually_nhds_iff {p : α -> Prop} :
    (forallᶠ y in 𝓝 x, p y) ↔ exists ε > 0, forall ⦃y⦄, dist y x < ε -> p y :=
  mem_nhds_iff

/--
theorem `eventually_nhds_iff_ball` / 定理 `eventually_nhds_iff_ball`

English:
theorem eventually_nhds_iff_ball
  given: {p : α -> Prop}
  proof: mem_nhds_iff

中文:
定理 eventually_nhds_iff_ball
  条件: {p : α -> 命题}
  证明: mem_nhds_iff

Depends on / 依赖: mem_nhds_iff
-/
theorem eventually_nhds_iff_ball {p : α -> Prop} :
    (forallᶠ y in 𝓝 x, p y) ↔ exists ε > 0, forall y in ball x ε, p y :=
  mem_nhds_iff

/--
theorem `eventually_nhds_prod_iff` / 定理 `eventually_nhds_prod_iff`

English:
theorem eventually_nhds_prod_iff
  given: {f : Filter ι} {x₀ : α} {p : α × ι -> Prop}
  proof: by
  refine (nhds_basis_ball.prod f.basis_sets).eventually_iff.trans ?_
  simp only [Prod.exists, forall_prod_set, id, mem_ball, and_assoc, exists_and_left,
    Set.mem_surjective.exists, eventually_mem_set]

中文:
定理 eventually_nhds_prod_iff
  条件: {f : Filter ι} {x₀ : α} {p : α × ι -> 命题}
  证明: by
  refine (nhds_basis_ball.prod f.basis_sets).eventually_iff.trans ?_
  simp only [Prod.exists, forall_prod_set, id, mem_ball, and_assoc, exists_and_left,
    Set.mem_surjective.exists, eventually_mem_set]

Depends on / 依赖: Prod.exists, Set.mem_surjective.exists, and_assoc, basis_sets, eventually_iff, eventually_iff.trans, eventually_mem_set, exists_and_left, f.basis_sets, forall_prod_set, mem_ball, mem_surjective, nhds_basis_ball, nhds_basis_ball.prod
-/
theorem eventually_nhds_prod_iff {f : Filter ι} {x₀ : α} {p : α × ι -> Prop} :
    (forallᶠ x in 𝓝 x₀ ×ˢ f, p x) ↔ exists ε > (0 : Real), exists pa : ι -> Prop, (forallᶠ i in f, pa i) ∧
      forall ⦃x⦄, dist x x₀ < ε -> forall ⦃i⦄, pa i -> p (x, i) := by
  refine (nhds_basis_ball.prod f.basis_sets).eventually_iff.trans ?_
  simp only [Prod.exists, forall_prod_set, id, mem_ball, and_assoc, exists_and_left,
    Set.mem_surjective.exists, eventually_mem_set]

/--
theorem `eventually_prod_nhds_iff` / 定理 `eventually_prod_nhds_iff`

English:
theorem eventually_prod_nhds_iff
  given: {f : Filter ι} {x₀ : α} {p : ι × α -> Prop}
  proof: by
  rw [eventually_swap_iff]; rw [Metric.eventually_nhds_prod_iff]
  constructor <;>
    · rintro ⟨a1, a2, a3, a4, a5⟩
      exact ⟨a3, a4, a1, a2, fun _ b1 b2 b3 => a5 b3 b1⟩

中文:
定理 eventually_prod_nhds_iff
  条件: {f : Filter ι} {x₀ : α} {p : ι × α -> 命题}
  证明: by
  rw [eventually_swap_iff]; rw [Metric.eventually_nhds_prod_iff]
  constructor <;>
    · rintro ⟨a1, a2, a3, a4, a5⟩
      exact ⟨a3, a4, a1, a2, fun _ b1 b2 b3 => a5 b3 b1⟩

Depends on / 依赖: Metric, Metric.eventually_nhds_prod_iff, eventually_nhds_prod_iff, eventually_swap_iff
-/
theorem eventually_prod_nhds_iff {f : Filter ι} {x₀ : α} {p : ι × α -> Prop} :
    (forallᶠ x in f ×ˢ 𝓝 x₀, p x) ↔ exists pa : ι -> Prop, (forallᶠ i in f, pa i) ∧
      exists ε > 0, forall ⦃i⦄, pa i -> forall ⦃x⦄, dist x x₀ < ε -> p (i, x) := by
  rw [eventually_swap_iff]; rw [Metric.eventually_nhds_prod_iff]
  constructor <;>
    · rintro ⟨a1, a2, a3, a4, a5⟩
      exact ⟨a3, a4, a1, a2, fun _ b1 b2 b3 => a5 b3 b1⟩

/--
theorem `nhds_basis_closedBall` / 定理 `nhds_basis_closedBall`

English:
theorem nhds_basis_closedBall
  statement: (𝓝 x).HasBasis (fun ε : Real => 0 < ε) (closedBall x)
  proof: nhds_basis_uniformity uniformity_basis_dist_le

中文:
定理 nhds_basis_closedBall
  结论: (𝓝 x).HasBasis (fun ε : 实数 => 0 < ε) (closedBall x)
  证明: nhds_basis_uniformity uniformity_basis_dist_le

Depends on / 依赖: nhds_basis_uniformity, uniformity_basis_dist_le
-/
theorem nhds_basis_closedBall : (𝓝 x).HasBasis (fun ε : Real => 0 < ε) (closedBall x) :=
  nhds_basis_uniformity uniformity_basis_dist_le

/--
theorem `nhds_basis_ball_inv_nat_succ` / 定理 `nhds_basis_ball_inv_nat_succ`

English:
theorem nhds_basis_ball_inv_nat_succ
  proof: nhds_basis_uniformity uniformity_basis_dist_inv_nat_succ

中文:
定理 nhds_basis_ball_inv_nat_succ
  证明: nhds_basis_uniformity uniformity_basis_dist_inv_nat_succ

Depends on / 依赖: nhds_basis_uniformity, uniformity_basis_dist_inv_nat_succ
-/
theorem nhds_basis_ball_inv_nat_succ :
    (𝓝 x).HasBasis (fun _ => True) fun n : Nat => ball x (1 / (↑n + 1)) :=
  nhds_basis_uniformity uniformity_basis_dist_inv_nat_succ

/--
theorem `nhds_basis_ball_inv_nat_pos` / 定理 `nhds_basis_ball_inv_nat_pos`

English:
theorem nhds_basis_ball_inv_nat_pos
  proof: nhds_basis_uniformity uniformity_basis_dist_inv_nat_pos

中文:
定理 nhds_basis_ball_inv_nat_pos
  证明: nhds_basis_uniformity uniformity_basis_dist_inv_nat_pos

Depends on / 依赖: nhds_basis_uniformity, uniformity_basis_dist_inv_nat_pos
-/
theorem nhds_basis_ball_inv_nat_pos :
    (𝓝 x).HasBasis (fun n => 0 < n) fun n : Nat => ball x (1 / ↑n) :=
  nhds_basis_uniformity uniformity_basis_dist_inv_nat_pos

/--
theorem `nhds_basis_closedBall_inv_nat_succ` / 定理 `nhds_basis_closedBall_inv_nat_succ`

English:
theorem nhds_basis_closedBall_inv_nat_succ
  proof: nhds_basis_uniformity uniformity_basis_dist_le_inv_nat_succ

中文:
定理 nhds_basis_closedBall_inv_nat_succ
  证明: nhds_basis_uniformity uniformity_basis_dist_le_inv_nat_succ

Depends on / 依赖: nhds_basis_uniformity, uniformity_basis_dist_le_inv_nat_succ
-/
theorem nhds_basis_closedBall_inv_nat_succ :
    (𝓝 x).HasBasis (fun _ => True) fun n : Nat => closedBall x (1 / (↑n + 1)) :=
  nhds_basis_uniformity uniformity_basis_dist_le_inv_nat_succ

/--
theorem `nhds_basis_closedBall_inv_nat_pos` / 定理 `nhds_basis_closedBall_inv_nat_pos`

English:
theorem nhds_basis_closedBall_inv_nat_pos
  proof: nhds_basis_uniformity uniformity_basis_dist_le_inv_nat_pos

中文:
定理 nhds_basis_closedBall_inv_nat_pos
  证明: nhds_basis_uniformity uniformity_basis_dist_le_inv_nat_pos

Depends on / 依赖: nhds_basis_uniformity, uniformity_basis_dist_le_inv_nat_pos
-/
theorem nhds_basis_closedBall_inv_nat_pos :
    (𝓝 x).HasBasis (fun n => 0 < n) fun n : Nat => closedBall x (1 / ↑n) :=
  nhds_basis_uniformity uniformity_basis_dist_le_inv_nat_pos

/--
theorem `nhds_basis_ball_pow` / 定理 `nhds_basis_ball_pow`

English:
theorem nhds_basis_ball_pow
  given: {r : Real} (h0 : 0 < r) (h1 : r < 1)
  proof: nhds_basis_uniformity (uniformity_basis_dist_pow h0 h1)

中文:
定理 nhds_basis_ball_pow
  条件: {r : 实数} (h0 : 0 < r) (h1 : r < 1)
  证明: nhds_basis_uniformity (uniformity_basis_dist_pow h0 h1)

Depends on / 依赖: nhds_basis_uniformity, uniformity_basis_dist_pow
-/
theorem nhds_basis_ball_pow {r : Real} (h0 : 0 < r) (h1 : r < 1) :
    (𝓝 x).HasBasis (fun _ => True) fun n : Nat => ball x (r ^ n) :=
  nhds_basis_uniformity (uniformity_basis_dist_pow h0 h1)

/--
theorem `nhds_basis_closedBall_pow` / 定理 `nhds_basis_closedBall_pow`

English:
theorem nhds_basis_closedBall_pow
  given: {r : Real} (h0 : 0 < r) (h1 : r < 1)
  proof: nhds_basis_uniformity (uniformity_basis_dist_le_pow h0 h1)

中文:
定理 nhds_basis_closedBall_pow
  条件: {r : 实数} (h0 : 0 < r) (h1 : r < 1)
  证明: nhds_basis_uniformity (uniformity_basis_dist_le_pow h0 h1)

Depends on / 依赖: nhds_basis_uniformity, uniformity_basis_dist_le_pow
-/
theorem nhds_basis_closedBall_pow {r : Real} (h0 : 0 < r) (h1 : r < 1) :
    (𝓝 x).HasBasis (fun _ => True) fun n : Nat => closedBall x (r ^ n) :=
  nhds_basis_uniformity (uniformity_basis_dist_le_pow h0 h1)

/--
theorem `isOpen_iff` / 定理 `isOpen_iff`

English:
theorem isOpen_iff
  statement: IsOpen s ↔ forall x in s, exists ε > 0, ball x ε subseteq s
  proof: by
  simp only [isOpen_iff_mem_nhds, mem_nhds_iff]

中文:
定理 isOpen_iff
  结论: IsOpen s ↔ 对任意 x in s, 存在 ε > 0, ball x ε subseteq s
  证明: by
  simp only [isOpen_iff_mem_nhds, mem_nhds_iff]

Depends on / 依赖: isOpen_iff_mem_nhds, mem_nhds_iff
-/
theorem isOpen_iff : IsOpen s ↔ forall x in s, exists ε > 0, ball x ε subseteq s := by
  simp only [isOpen_iff_mem_nhds, mem_nhds_iff]

/--
theorem `isOpen_ball` / 定理 `isOpen_ball`

English:
theorem isOpen_ball
  statement: IsOpen (ball x ε)
  proof: isOpen_iff.2 fun _ => exists_ball_subset_ball

中文:
定理 isOpen_ball
  结论: IsOpen (ball x ε)
  证明: isOpen_iff.2 fun _ => exists_ball_subset_ball
-/
@[simp] theorem isOpen_ball : IsOpen (ball x ε) :=
  isOpen_iff.2 fun _ => exists_ball_subset_ball

/--
theorem `ball_mem_nhds` / 定理 `ball_mem_nhds`

English:
theorem ball_mem_nhds
  given: (x : α) {ε : Real} (ε0 : 0 < ε)
  statement: ball x ε in 𝓝 x
  proof: isOpen_ball.mem_nhds (mem_ball_self ε0)

中文:
定理 ball_mem_nhds
  条件: (x : α) {ε : 实数} (ε0 : 0 < ε)
  结论: ball x ε in 𝓝 x
  证明: isOpen_ball.mem_nhds (mem_ball_self ε0)

Depends on / 依赖: isOpen_ball, isOpen_ball.mem_nhds, mem_ball_self, mem_nhds
-/
theorem ball_mem_nhds (x : α) {ε : Real} (ε0 : 0 < ε) : ball x ε in 𝓝 x :=
  isOpen_ball.mem_nhds (mem_ball_self ε0)

/--
theorem `closedBall_mem_nhds` / 定理 `closedBall_mem_nhds`

English:
theorem closedBall_mem_nhds
  given: (x : α) {ε : Real} (ε0 : 0 < ε)
  statement: closedBall x ε in 𝓝 x
  proof: mem_of_superset (ball_mem_nhds x ε0) ball_subset_closedBall

中文:
定理 closedBall_mem_nhds
  条件: (x : α) {ε : 实数} (ε0 : 0 < ε)
  结论: closedBall x ε in 𝓝 x
  证明: mem_of_superset (ball_mem_nhds x ε0) ball_subset_closedBall

Depends on / 依赖: ball_mem_nhds, ball_subset_closedBall, mem_of_superset
-/
theorem closedBall_mem_nhds (x : α) {ε : Real} (ε0 : 0 < ε) : closedBall x ε in 𝓝 x :=
  mem_of_superset (ball_mem_nhds x ε0) ball_subset_closedBall

/--
theorem `closedBall_mem_nhds_of_mem` / 定理 `closedBall_mem_nhds_of_mem`

English:
theorem closedBall_mem_nhds_of_mem
  given: {x c : α} {ε : Real} (h : x in ball c ε)
  statement: closedBall c ε in 𝓝 x
  proof: mem_of_superset (isOpen_ball.mem_nhds h) ball_subset_closedBall

中文:
定理 closedBall_mem_nhds_of_mem
  条件: {x c : α} {ε : 实数} (h : x in ball c ε)
  结论: closedBall c ε in 𝓝 x
  证明: mem_of_superset (isOpen_ball.mem_nhds h) ball_subset_closedBall

Depends on / 依赖: ball_subset_closedBall, isOpen_ball, isOpen_ball.mem_nhds, mem_nhds, mem_of_superset
-/
theorem closedBall_mem_nhds_of_mem {x c : α} {ε : Real} (h : x in ball c ε) : closedBall c ε in 𝓝 x :=
  mem_of_superset (isOpen_ball.mem_nhds h) ball_subset_closedBall

/--
theorem `nhdsWithin_basis_ball` / 定理 `nhdsWithin_basis_ball`

English:
theorem nhdsWithin_basis_ball
  given: {s : Set α}
  proof: nhdsWithin_hasBasis nhds_basis_ball s

中文:
定理 nhdsWithin_basis_ball
  条件: {s : Set α}
  证明: nhdsWithin_hasBasis nhds_basis_ball s

Depends on / 依赖: nhdsWithin_hasBasis, nhds_basis_ball
-/
theorem nhdsWithin_basis_ball {s : Set α} :
    (𝓝[s] x).HasBasis (fun ε : Real => 0 < ε) fun ε => ball x ε inter s :=
  nhdsWithin_hasBasis nhds_basis_ball s

/--
theorem `mem_nhdsWithin_iff` / 定理 `mem_nhdsWithin_iff`

English:
theorem mem_nhdsWithin_iff
  given: {t : Set α}
  statement: s in 𝓝[t] x ↔ exists ε > 0, ball x ε inter t subseteq s
  proof: nhdsWithin_basis_ball.mem_iff

中文:
定理 mem_nhdsWithin_iff
  条件: {t : Set α}
  结论: s in 𝓝[t] x ↔ 存在 ε > 0, ball x ε inter t subseteq s
  证明: nhdsWithin_basis_ball.mem_iff

Depends on / 依赖: mem_iff, nhdsWithin_basis_ball, nhdsWithin_basis_ball.mem_iff
-/
theorem mem_nhdsWithin_iff {t : Set α} : s in 𝓝[t] x ↔ exists ε > 0, ball x ε inter t subseteq s :=
  nhdsWithin_basis_ball.mem_iff

/--
theorem `tendsto_nhdsWithin_nhdsWithin` / 定理 `tendsto_nhdsWithin_nhdsWithin`

English:
theorem tendsto_nhdsWithin_nhdsWithin
  given: [PseudoMetricSpace β] {t : Set β} {f : α -> β} {a b}
  proof: (nhdsWithin_basis_ball.tendsto_iff nhdsWithin_basis_ball).trans by
    simp only [inter_comm _ s, inter_comm _ t, mem_inter_iff, and_imp, gt_iff_lt, mem_ball]

中文:
定理 tendsto_nhdsWithin_nhdsWithin
  条件: [PseudoMetricSpace β] {t : Set β} {f : α -> β} {a b}
  证明: (nhdsWithin_basis_ball.tendsto_iff nhdsWithin_basis_ball).trans by
    simp only [inter_comm _ s, inter_comm _ t, mem_inter_iff, and_imp, gt_iff_lt, mem_ball]

Depends on / 依赖: and_imp, gt_iff_lt, inter_comm, mem_ball, mem_inter_iff, nhdsWithin_basis_ball, nhdsWithin_basis_ball.tendsto_iff, tendsto_iff
-/
theorem tendsto_nhdsWithin_nhdsWithin [PseudoMetricSpace β] {t : Set β} {f : α -> β} {a b} :
    Tendsto f (𝓝[s] a) (𝓝[t] b) ↔
      forall ε > 0, exists δ > 0, forall ⦃x : α⦄, x in s -> dist x a < δ -> f x in t ∧ dist (f x) b < ε :=
(nhdsWithin_basis_ball.tendsto_iff nhdsWithin_basis_ball).trans by
    simp only [inter_comm _ s, inter_comm _ t, mem_inter_iff, and_imp, gt_iff_lt, mem_ball]

/--
theorem `tendsto_nhdsWithin_nhds` / 定理 `tendsto_nhdsWithin_nhds`

English:
theorem tendsto_nhdsWithin_nhds
  given: [PseudoMetricSpace β] {f : α -> β} {a b}
  proof: by
  rw [← nhdsWithin_univ b]; rw [tendsto_nhdsWithin_nhdsWithin]
  simp only [mem_univ, true_and]

中文:
定理 tendsto_nhdsWithin_nhds
  条件: [PseudoMetricSpace β] {f : α -> β} {a b}
  证明: by
  rw [← nhdsWithin_univ b]; rw [tendsto_nhdsWithin_nhdsWithin]
  simp only [mem_univ, true_and]

Depends on / 依赖: mem_univ, nhdsWithin_univ, tendsto_nhdsWithin_nhdsWithin, true_and
-/
theorem tendsto_nhdsWithin_nhds [PseudoMetricSpace β] {f : α -> β} {a b} :
    Tendsto f (𝓝[s] a) (𝓝 b) ↔
      forall ε > 0, exists δ > 0, forall ⦃x : α⦄, x in s -> dist x a < δ -> dist (f x) b < ε := by
  rw [← nhdsWithin_univ b]; rw [tendsto_nhdsWithin_nhdsWithin]
  simp only [mem_univ, true_and]

/--
theorem `tendsto_nhds_nhds` / 定理 `tendsto_nhds_nhds`

English:
theorem tendsto_nhds_nhds
  given: [PseudoMetricSpace β] {f : α -> β} {a b}
  proof: nhds_basis_ball.tendsto_iff nhds_basis_ball

中文:
定理 tendsto_nhds_nhds
  条件: [PseudoMetricSpace β] {f : α -> β} {a b}
  证明: nhds_basis_ball.tendsto_iff nhds_basis_ball

Depends on / 依赖: nhds_basis_ball, nhds_basis_ball.tendsto_iff, tendsto_iff
-/
theorem tendsto_nhds_nhds [PseudoMetricSpace β] {f : α -> β} {a b} :
    Tendsto f (𝓝 a) (𝓝 b) ↔ forall ε > 0, exists δ > 0, forall ⦃x : α⦄, dist x a < δ -> dist (f x) b < ε :=
  nhds_basis_ball.tendsto_iff nhds_basis_ball

/--
theorem `continuousAt_iff` / 定理 `continuousAt_iff`

English:
theorem continuousAt_iff
  given: [PseudoMetricSpace β] {f : α -> β} {a : α}
  proof: by
  rw [ContinuousAt]; rw [tendsto_nhds_nhds]

中文:
定理 continuousAt_iff
  条件: [PseudoMetricSpace β] {f : α -> β} {a : α}
  证明: by
  rw [ContinuousAt]; rw [tendsto_nhds_nhds]

Depends on / 依赖: ContinuousAt, tendsto_nhds_nhds
-/
theorem continuousAt_iff [PseudoMetricSpace β] {f : α -> β} {a : α} :
    ContinuousAt f a ↔ forall ε > 0, exists δ > 0, forall ⦃x : α⦄, dist x a < δ -> dist (f x) (f a) < ε := by
  rw [ContinuousAt]; rw [tendsto_nhds_nhds]

/--
theorem `continuousWithinAt_iff` / 定理 `continuousWithinAt_iff`

English:
theorem continuousWithinAt_iff
  given: [PseudoMetricSpace β] {f : α -> β} {a : α} {s : Set α}
  proof: by
  rw [ContinuousWithinAt]; rw [tendsto_nhdsWithin_nhds]

中文:
定理 continuousWithinAt_iff
  条件: [PseudoMetricSpace β] {f : α -> β} {a : α} {s : Set α}
  证明: by
  rw [ContinuousWithinAt]; rw [tendsto_nhdsWithin_nhds]

Depends on / 依赖: ContinuousWithinAt, tendsto_nhdsWithin_nhds
-/
theorem continuousWithinAt_iff [PseudoMetricSpace β] {f : α -> β} {a : α} {s : Set α} :
    ContinuousWithinAt f s a ↔
      forall ε > 0, exists δ > 0, forall ⦃x : α⦄, x in s -> dist x a < δ -> dist (f x) (f a) < ε := by
  rw [ContinuousWithinAt]; rw [tendsto_nhdsWithin_nhds]

/--
theorem `continuousOn_iff` / 定理 `continuousOn_iff`

English:
theorem continuousOn_iff
  given: [PseudoMetricSpace β] {f : α -> β} {s : Set α}
  proof: by
  simp [ContinuousOn, continuousWithinAt_iff]

中文:
定理 continuousOn_iff
  条件: [PseudoMetricSpace β] {f : α -> β} {s : Set α}
  证明: by
  simp [ContinuousOn, continuousWithinAt_iff]

Depends on / 依赖: ContinuousOn, continuousWithinAt_iff
-/
theorem continuousOn_iff [PseudoMetricSpace β] {f : α -> β} {s : Set α} :
    ContinuousOn f s ↔ forall b in s, forall ε > 0, exists δ > 0, forall a in s, dist a b < δ -> dist (f a) (f b) < ε := by
  simp [ContinuousOn, continuousWithinAt_iff]

/--
theorem `continuous_iff` / 定理 `continuous_iff`

English:
theorem continuous_iff
  given: [PseudoMetricSpace β] {f : α -> β}
  proof: continuous_iff_continuousAt.trans forall_congr' fun _ => tendsto_nhds_nhds

中文:
定理 continuous_iff
  条件: [PseudoMetricSpace β] {f : α -> β}
  证明: continuous_iff_continuousAt.trans forall_congr' fun _ => tendsto_nhds_nhds

Depends on / 依赖: continuous_iff_continuousAt, continuous_iff_continuousAt.trans, forall_congr, tendsto_nhds_nhds
-/
theorem continuous_iff [PseudoMetricSpace β] {f : α -> β} :
    Continuous f ↔ forall b, forall ε > 0, exists δ > 0, forall a, dist a b < δ -> dist (f a) (f b) < ε :=
continuous_iff_continuousAt.trans forall_congr' fun _ => tendsto_nhds_nhds

/--
theorem `tendsto_nhds` / 定理 `tendsto_nhds`

English:
theorem tendsto_nhds
  given: {f : Filter β} {u : β -> α} {a : α}
  proof: nhds_basis_ball.tendsto_right_iff

中文:
定理 tendsto_nhds
  条件: {f : Filter β} {u : β -> α} {a : α}
  证明: nhds_basis_ball.tendsto_right_iff

Depends on / 依赖: nhds_basis_ball, nhds_basis_ball.tendsto_right_iff, tendsto_right_iff
-/
theorem tendsto_nhds {f : Filter β} {u : β -> α} {a : α} :
    Tendsto u f (𝓝 a) ↔ forall ε > 0, forallᶠ x in f, dist (u x) a < ε :=
  nhds_basis_ball.tendsto_right_iff

/--
theorem `continuousAt_iff'` / 定理 `continuousAt_iff'`

English:
theorem continuousAt_iff'
  given: [TopologicalSpace β] {f : β -> α} {b : β}
  proof: by
  rw [ContinuousAt]; rw [tendsto_nhds]

中文:
定理 continuousAt_iff'
  条件: [TopologicalSpace β] {f : β -> α} {b : β}
  证明: by
  rw [ContinuousAt]; rw [tendsto_nhds]

Depends on / 依赖: ContinuousAt, tendsto_nhds
-/
theorem continuousAt_iff' [TopologicalSpace β] {f : β -> α} {b : β} :
    ContinuousAt f b ↔ forall ε > 0, forallᶠ x in 𝓝 b, dist (f x) (f b) < ε := by
  rw [ContinuousAt]; rw [tendsto_nhds]

/--
theorem `continuousWithinAt_iff'` / 定理 `continuousWithinAt_iff'`

English:
theorem continuousWithinAt_iff'
  given: [TopologicalSpace β] {f : β -> α} {b : β} {s : Set β}
  proof: by
  rw [ContinuousWithinAt]; rw [tendsto_nhds]

中文:
定理 continuousWithinAt_iff'
  条件: [TopologicalSpace β] {f : β -> α} {b : β} {s : Set β}
  证明: by
  rw [ContinuousWithinAt]; rw [tendsto_nhds]

Depends on / 依赖: ContinuousWithinAt, tendsto_nhds
-/
theorem continuousWithinAt_iff' [TopologicalSpace β] {f : β -> α} {b : β} {s : Set β} :
    ContinuousWithinAt f s b ↔ forall ε > 0, forallᶠ x in 𝓝[s] b, dist (f x) (f b) < ε := by
  rw [ContinuousWithinAt]; rw [tendsto_nhds]

/--
theorem `continuousOn_iff'` / 定理 `continuousOn_iff'`

English:
theorem continuousOn_iff'
  given: [TopologicalSpace β] {f : β -> α} {s : Set β}
  proof: by
  simp [ContinuousOn, continuousWithinAt_iff']

中文:
定理 continuousOn_iff'
  条件: [TopologicalSpace β] {f : β -> α} {s : Set β}
  证明: by
  simp [ContinuousOn, continuousWithinAt_iff']

Depends on / 依赖: ContinuousOn, continuousWithinAt_iff
-/
theorem continuousOn_iff' [TopologicalSpace β] {f : β -> α} {s : Set β} :
    ContinuousOn f s ↔ forall b in s, forall ε > 0, forallᶠ x in 𝓝[s] b, dist (f x) (f b) < ε := by
  simp [ContinuousOn, continuousWithinAt_iff']

/--
theorem `continuous_iff'` / 定理 `continuous_iff'`

English:
theorem continuous_iff'
  given: [TopologicalSpace β] {f : β -> α}
  proof: continuous_iff_continuousAt.trans forall_congr' fun _ => tendsto_nhds

中文:
定理 continuous_iff'
  条件: [TopologicalSpace β] {f : β -> α}
  证明: continuous_iff_continuousAt.trans forall_congr' fun _ => tendsto_nhds

Depends on / 依赖: continuous_iff_continuousAt, continuous_iff_continuousAt.trans, forall_congr, tendsto_nhds
-/
theorem continuous_iff' [TopologicalSpace β] {f : β -> α} :
    Continuous f ↔ forall (a), forall ε > 0, forallᶠ x in 𝓝 a, dist (f x) (f a) < ε :=
continuous_iff_continuousAt.trans forall_congr' fun _ => tendsto_nhds

/--
theorem `tendsto_atTop` / 定理 `tendsto_atTop`

English:
theorem tendsto_atTop
  given: [Nonempty β] [SemilatticeSup β] {u : β -> α} {a : α}
  proof: (atTop_basis.tendsto_iff nhds_basis_ball).trans by
    simp only [true_and, mem_ball, mem_Ici]

中文:
定理 tendsto_atTop
  条件: [Nonempty β] [SemilatticeSup β] {u : β -> α} {a : α}
  证明: (atTop_basis.tendsto_iff nhds_basis_ball).trans by
    simp only [true_and, mem_ball, mem_Ici]

Depends on / 依赖: atTop_basis, atTop_basis.tendsto_iff, mem_Ici, mem_ball, nhds_basis_ball, tendsto_iff, true_and
-/
theorem tendsto_atTop [Nonempty β] [SemilatticeSup β] {u : β -> α} {a : α} :
    Tendsto u atTop (𝓝 a) ↔ forall ε > 0, exists N, forall n >= N, dist (u n) a < ε :=
(atTop_basis.tendsto_iff nhds_basis_ball).trans by
    simp only [true_and, mem_ball, mem_Ici]

/--
theorem `tendsto_atTop'` / 定理 `tendsto_atTop'`

English:
theorem tendsto_atTop'
  given: [Nonempty β] [SemilatticeSup β] [NoMaxOrder β] {u : β -> α} {a : α}
  proof: (atTop_basis_Ioi.tendsto_iff nhds_basis_ball).trans by
    simp only [true_and, gt_iff_lt, mem_Ioi, mem_ball]

中文:
定理 tendsto_atTop'
  条件: [Nonempty β] [SemilatticeSup β] [NoMaxOrder β] {u : β -> α} {a : α}
  证明: (atTop_basis_Ioi.tendsto_iff nhds_basis_ball).trans by
    simp only [true_and, gt_iff_lt, mem_Ioi, mem_ball]

Depends on / 依赖: atTop_basis_Ioi, atTop_basis_Ioi.tendsto_iff, gt_iff_lt, mem_Ioi, mem_ball, nhds_basis_ball, tendsto_iff, true_and
-/
theorem tendsto_atTop' [Nonempty β] [SemilatticeSup β] [NoMaxOrder β] {u : β -> α} {a : α} :
    Tendsto u atTop (𝓝 a) ↔ forall ε > 0, exists N, forall n > N, dist (u n) a < ε :=
(atTop_basis_Ioi.tendsto_iff nhds_basis_ball).trans by
    simp only [true_and, gt_iff_lt, mem_Ioi, mem_ball]

/--
theorem `isOpen_singleton_iff` / 定理 `isOpen_singleton_iff`

English:
theorem isOpen_singleton_iff
  given: {α : Type*} [PseudoMetricSpace α] {x : α}
  proof: by
  simp [isOpen_iff, subset_singleton_iff, mem_ball]

中文:
定理 isOpen_singleton_iff
  条件: {α : 类型} [PseudoMetricSpace α] {x : α}
  证明: by
  simp [isOpen_iff, subset_singleton_iff, mem_ball]

Depends on / 依赖: isOpen_iff, mem_ball, subset_singleton_iff
-/
theorem isOpen_singleton_iff {α : Type*} [PseudoMetricSpace α] {x : α} :
    IsOpen ({x} : Set α) ↔ exists ε > 0, forall y, dist y x < ε -> y = x := by
  simp [isOpen_iff, subset_singleton_iff, mem_ball]

/--
theorem `_root_.Dense.exists_dist_lt` / 定理 `_root_.Dense.exists_dist_lt`

English:
theorem _root_.Dense.exists_dist_lt
  given: {s : Set α} (hs : Dense s) (x : α) {ε : Real} (hε : 0 < ε)
  proof: by
  have : (ball x ε).Nonempty := by simp [hε]
  simpa only [mem_ball'] using hs.exists_mem_open isOpen_ball this

nonrec theorem _root_.DenseRange.exists_dist_lt {β : Type*} {f : β -> α} (hf : DenseRange f) (x : α)
    {ε : Real} (hε : 0 < ε) : exists y, dist x (f y) < ε :=
  exists_range_iff.1 (h

中文:
定理 _root_.Dense.exists_dist_lt
  条件: {s : Set α} (hs : Dense s) (x : α) {ε : 实数} (hε : 0 < ε)
  证明: by
  have : (ball x ε).Nonempty := by simp [hε]
  simpa only [mem_ball'] using hs.exists_mem_open isOpen_ball this

nonrec theorem _root_.DenseRange.exists_dist_lt {β : Type*} {f : β -> α} (hf : DenseRange f) (x : α)
    {ε : Real} (hε : 0 < ε) : exists y, dist x (f y) < ε :=
  exists_range_iff.1 (h

Depends on / 依赖: Nonempty, exists_mem_open, hs.exists_mem_open, isOpen_ball, mem_ball
-/
theorem _root_.Dense.exists_dist_lt {s : Set α} (hs : Dense s) (x : α) {ε : Real} (hε : 0 < ε) :
    exists y in s, dist x y < ε := by
  have : (ball x ε).Nonempty := by simp [hε]
  simpa only [mem_ball'] using hs.exists_mem_open isOpen_ball this

nonrec theorem _root_.DenseRange.exists_dist_lt {β : Type*} {f : β -> α} (hf : DenseRange f) (x : α)
    {ε : Real} (hε : 0 < ε) : exists y, dist x (f y) < ε :=
  exists_range_iff.1 (hf.exists_dist_lt x hε)

/--
lemma `uniformSpace_eq_bot` / 引理 `uniformSpace_eq_bot`

English:
lemma uniformSpace_eq_bot
  proof: by
  simp only [uniformity_basis_dist.uniformSpace_eq_bot, mem_ofPred_eq, not_lt]

中文:
引理 uniformSpace_eq_bot
  证明: by
  simp only [uniformity_basis_dist.uniformSpace_eq_bot, mem_ofPred_eq, not_lt]
-/
protected lemma uniformSpace_eq_bot :
    ‹PseudoMetricSpace α›.toUniformSpace = ⊥ ↔
      exists r : Real, 0 < r ∧ Pairwise (r <= dist · · : α -> α -> Prop) := by
  simp only [uniformity_basis_dist.uniformSpace_eq_bot, mem_ofPred_eq, not_lt]

end Metric

open Metric

/--
lemma `DiscreteTopology.of_forall_le_dist` / 引理 `DiscreteTopology.of_forall_le_dist`

English:
lemma DiscreteTopology.of_forall_le_dist
  statement: {α} [PseudoMetricSpace α] {r : Real} (hpos : 0 < r)
  proof: ⟨by rw [Metric.uniformSpace_eq_bot.2 ⟨r, hpos, hr⟩, UniformSpace.toTopologicalSpace_bot]⟩

中文:
引理 DiscreteTopology.of_forall_le_dist
  结论: {α} [PseudoMetricSpace α] {r : 实数} (hpos : 0 < r)
  证明: ⟨by rw [Metric.uniformSpace_eq_bot.2 ⟨r, hpos, hr⟩, UniformSpace.toTopologicalSpace_bot]⟩

Depends on / 依赖: Metric, Metric.uniformSpace_eq_bot, UniformSpace, UniformSpace.toTopologicalSpace_bot, toTopologicalSpace_bot, uniformSpace_eq_bot
-/
lemma DiscreteTopology.of_forall_le_dist {α} [PseudoMetricSpace α] {r : Real} (hpos : 0 < r)
    (hr : Pairwise (r <= dist · · : α -> α -> Prop)) : DiscreteTopology α :=
  ⟨by rw [Metric.uniformSpace_eq_bot.2 ⟨r, hpos, hr⟩, UniformSpace.toTopologicalSpace_bot]⟩


/--
theorem `Metric.uniformity_edist_aux` / 定理 `Metric.uniformity_edist_aux`

English:
theorem Metric.uniformity_edist_aux
  given: {α} (d : α -> α -> Real>=0)
  proof: by
  simp only [le_antisymm_iff, le_iInf_iff, le_principal_iff]
  refine ⟨fun ε hε => ?_, fun ε hε => ?_⟩
  · rcases ENNReal.lt_iff_exists_nnreal_btwn.1 hε with ⟨ε', ε'0, ε'ε⟩
    refine mem_iInf_of_mem (ε' : Real) (mem_iInf_of_mem (ENNReal.coe_pos.1 ε'0) ?_)
    exact fun x hx => lt_trans (ENNReal.

中文:
定理 Metric.uniformity_edist_aux
  条件: {α} (d : α -> α -> 实数>=0)
  证明: by
  simp only [le_antisymm_iff, le_iInf_iff, le_principal_iff]
  refine ⟨fun ε hε => ?_, fun ε hε => ?_⟩
  · rcases ENNReal.lt_iff_exists_nnreal_btwn.1 hε with ⟨ε', ε'0, ε'ε⟩
    refine mem_iInf_of_mem (ε' : Real) (mem_iInf_of_mem (ENNReal.coe_pos.1 ε'0) ?_)
    exact fun x hx => lt_trans (ENNReal.

Depends on / 依赖: ENNReal, ENNReal.coe_lt_coe, ENNReal.coe_pos, ENNReal.lt_iff_exists_nnreal_btwn, coe_lt_coe, coe_pos, le_antisymm_iff, le_iInf_iff, le_of_lt, le_principal_iff, lt_iff_exists_nnreal_btwn, lt_trans, mem_iInf_of_mem
-/
theorem Metric.uniformity_edist_aux {α} (d : α -> α -> Real>=0) :
    ⨅ ε > (0 : Real), 𝓟 { p : α × α | ↑(d p.1 p.2) < ε } =
      ⨅ ε > (0 : Real>=0∞), 𝓟 { p : α × α | ↑(d p.1 p.2) < ε } := by
  simp only [le_antisymm_iff, le_iInf_iff, le_principal_iff]
  refine ⟨fun ε hε => ?_, fun ε hε => ?_⟩
  · rcases ENNReal.lt_iff_exists_nnreal_btwn.1 hε with ⟨ε', ε'0, ε'ε⟩
    refine mem_iInf_of_mem (ε' : Real) (mem_iInf_of_mem (ENNReal.coe_pos.1 ε'0) ?_)
    exact fun x hx => lt_trans (ENNReal.coe_lt_coe.2 hx) ε'ε
  · lift ε to Real>=0 using le_of_lt hε
    refine mem_iInf_of_mem (ε : Real>=0∞) (mem_iInf_of_mem (ENNReal.coe_pos.2 hε) ?_)
    exact fun _ => ENNReal.coe_lt_coe.1

/--
theorem `Metric.uniformity_edist` / 定理 `Metric.uniformity_edist`

English:
theorem Metric.uniformity_edist
  statement: 𝓤 α = ⨅ ε > 0, 𝓟 { p : α × α | edist p.1 p.2 < ε }
  proof: by
  simp only [PseudoMetricSpace.uniformity_dist, dist_nndist, edist_nndist,
    Metric.uniformity_edist_aux]

中文:
定理 Metric.uniformity_edist
  结论: 𝓤 α = ⨅ ε > 0, 𝓟 { p : α × α | edist p.1 p.2 < ε }
  证明: by
  simp only [PseudoMetricSpace.uniformity_dist, dist_nndist, edist_nndist,
    Metric.uniformity_edist_aux]

Depends on / 依赖: Metric, Metric.uniformity_edist_aux, PseudoMetricSpace, PseudoMetricSpace.uniformity_dist, dist_nndist, edist_nndist, uniformity_dist, uniformity_edist_aux
-/
theorem Metric.uniformity_edist : 𝓤 α = ⨅ ε > 0, 𝓟 { p : α × α | edist p.1 p.2 < ε } := by
  simp only [PseudoMetricSpace.uniformity_dist, dist_nndist, edist_nndist,
    Metric.uniformity_edist_aux]

-- see Note [lower instance priority]
/-- A pseudometric space induces a pseudoemetric space -/
instance (priority := 100) PseudoMetricSpace.toPseudoEMetricSpace : PseudoEMetricSpace α :=
  { ‹PseudoMetricSpace α› with
    edist_self := by simp [edist_dist]
    edist_comm := fun _ _ => by simp only [edist_dist, dist_comm]
    edist_triangle := fun x y z => by
      simp only [edist_dist, ← ENNReal.ofReal_add, dist_nonneg]
      rw [ENNReal.ofReal_le_ofReal_iff _]
      · exact dist_triangle _ _ _
      · simpa using add_le_add (dist_nonneg : 0 <= dist x y) dist_nonneg
    uniformity_edist := Metric.uniformity_edist }

/--
theorem `Metric.eball_top_eq_univ` / 定理 `Metric.eball_top_eq_univ`

English:
theorem Metric.eball_top_eq_univ
  given: (x : α)
  statement: eball x ∞ = Set.univ
  proof: Set.eq_univ_iff_forall.mpr fun y => edist_lt_top y x

中文:
定理 Metric.eball_top_eq_univ
  条件: (x : α)
  结论: eball x ∞ = Set.univ
  证明: Set.eq_univ_iff_forall.mpr fun y => edist_lt_top y x

Depends on / 依赖: Set.eq_univ_iff_forall.mpr, edist_lt_top, eq_univ_iff_forall
-/
theorem Metric.eball_top_eq_univ (x : α) : eball x ∞ = Set.univ :=
  Set.eq_univ_iff_forall.mpr fun y => edist_lt_top y x

/-- Balls defined using the distance or the edistance coincide -/
@[simp]
/--
theorem `Metric.eball_ofReal` / 定理 `Metric.eball_ofReal`

English:
theorem Metric.eball_ofReal
  given: {x : α} {ε : Real}
  statement: eball x (.ofReal ε) = ball x ε
  proof: by
  ext y
  simp only [mem_eball, mem_ball, edist_dist]
  exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg

@[deprecated (since := "2026-01-24")]
alias Metric.emetric_ball := Metric.eball_ofReal

中文:
定理 Metric.eball_ofReal
  条件: {x : α} {ε : 实数}
  结论: eball x (.of实数 ε) = ball x ε
  证明: by
  ext y
  simp only [mem_eball, mem_ball, edist_dist]
  exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg

@[deprecated (since := "2026-01-24")]
alias Metric.emetric_ball := Metric.eball_ofReal

Depends on / 依赖: ENNReal, ENNReal.ofReal_lt_ofReal_iff_of_nonneg, dist_nonneg, edist_dist, mem_ball, mem_eball, ofReal_lt_ofReal_iff_of_nonneg
-/
theorem Metric.eball_ofReal {x : α} {ε : Real} : eball x (.ofReal ε) = ball x ε := by
  ext y
  simp only [mem_eball, mem_ball, edist_dist]
  exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg

@[deprecated (since := "2026-01-24")]
alias Metric.emetric_ball := Metric.eball_ofReal

/-- Balls defined using the distance or the edistance coincide -/
@[simp]
/--
theorem `Metric.eball_coe` / 定理 `Metric.eball_coe`

English:
theorem Metric.eball_coe
  given: {x : α} {ε : Real>=0}
  statement: eball x ε = ball x ε
  proof: by
  rw [← eball_ofReal]
  simp

@[deprecated (since := "2026-01-24")]
alias Metric.emetric_ball_nnreal := Metric.eball_coe

中文:
定理 Metric.eball_coe
  条件: {x : α} {ε : 实数>=0}
  结论: eball x ε = ball x ε
  证明: by
  rw [← eball_ofReal]
  simp

@[deprecated (since := "2026-01-24")]
alias Metric.emetric_ball_nnreal := Metric.eball_coe

Depends on / 依赖: eball_ofReal
-/
theorem Metric.eball_coe {x : α} {ε : Real>=0} : eball x ε = ball x ε := by
  rw [← eball_ofReal]
  simp

@[deprecated (since := "2026-01-24")]
alias Metric.emetric_ball_nnreal := Metric.eball_coe

/--
theorem `Metric.closedEBall_ofReal` / 定理 `Metric.closedEBall_ofReal`

English:
theorem Metric.closedEBall_ofReal
  given: {x : α} {ε : Real} (h : 0 <= ε)
  proof: by
  ext y; simp [edist_le_ofReal h]

@[deprecated (since := "2026-01-24")]
alias Metric.emetric_closedBall := Metric.closedEBall_ofReal

中文:
定理 Metric.closedEBall_ofReal
  条件: {x : α} {ε : 实数} (h : 0 <= ε)
  证明: by
  ext y; simp [edist_le_ofReal h]

@[deprecated (since := "2026-01-24")]
alias Metric.emetric_closedBall := Metric.closedEBall_ofReal

Depends on / 依赖: edist_le_ofReal
-/
theorem Metric.closedEBall_ofReal {x : α} {ε : Real} (h : 0 <= ε) :
    closedEBall x (.ofReal ε) = closedBall x ε := by
  ext y; simp [edist_le_ofReal h]

@[deprecated (since := "2026-01-24")]
alias Metric.emetric_closedBall := Metric.closedEBall_ofReal

/-- Closed balls defined using the distance or the edistance coincide -/
@[simp]
/--
theorem `Metric.closedEBall_coe` / 定理 `Metric.closedEBall_coe`

English:
theorem Metric.closedEBall_coe
  given: {x : α} {ε : Real>=0}
  proof: by
  rw [← closedEBall_ofReal ε.coe_nonneg]; rw [ENNReal.ofReal_coe_nnreal]

@[deprecated (since := "2026-01-24")]
alias Metric.emetric_closedBall_nnreal := Metric.closedEBall_coe

@[simp]

中文:
定理 Metric.closedEBall_coe
  条件: {x : α} {ε : 实数>=0}
  证明: by
  rw [← closedEBall_ofReal ε.coe_nonneg]; rw [ENNReal.ofReal_coe_nnreal]

@[deprecated (since := "2026-01-24")]
alias Metric.emetric_closedBall_nnreal := Metric.closedEBall_coe

@[simp]

Depends on / 依赖: ENNReal, ENNReal.ofReal_coe_nnreal, closedEBall_ofReal, coe_nonneg, ofReal_coe_nnreal
-/
theorem Metric.closedEBall_coe {x : α} {ε : Real>=0} :
    closedEBall x ε = closedBall x ε := by
  rw [← closedEBall_ofReal ε.coe_nonneg]; rw [ENNReal.ofReal_coe_nnreal]

@[deprecated (since := "2026-01-24")]
alias Metric.emetric_closedBall_nnreal := Metric.closedEBall_coe

@[simp]
/--
theorem `Metric.eball_top` / 定理 `Metric.eball_top`

English:
theorem Metric.eball_top
  given: (x : α)
  statement: eball x ⊤ = univ
  proof: eq_univ_of_forall fun _ => edist_lt_top _ _

@[deprecated (since := "2026-01-24")]
alias Metric.emetric_ball_top := Metric.eball_top

中文:
定理 Metric.eball_top
  条件: (x : α)
  结论: eball x ⊤ = univ
  证明: eq_univ_of_forall fun _ => edist_lt_top _ _

@[deprecated (since := "2026-01-24")]
alias Metric.emetric_ball_top := Metric.eball_top

Depends on / 依赖: edist_lt_top, eq_univ_of_forall
-/
theorem Metric.eball_top (x : α) : eball x ⊤ = univ :=
  eq_univ_of_forall fun _ => edist_lt_top _ _

@[deprecated (since := "2026-01-24")]
alias Metric.emetric_ball_top := Metric.eball_top

/--
Definition of `PseudoMetricSpace.replaceUniformity` / `PseudoMetricSpace.replaceUniformity` 的定义

English:
abbreviation PseudoMetricSpace.replaceUniformity
  signature: {α} [U : UniformSpace α] (m : PseudoMetricSpace α)
  body: { m with
    toUniformSpace := U
    uniformity_dist := H.trans PseudoMetricSpace.uniformity_dist }

中文:
缩写 PseudoMetricSpace.replaceUniformity
  签名: {α} [U : UniformSpace α] (m : PseudoMetricSpace α)
  定义体: { m with
    toUniformSpace := U
    uniformity_dist := H.trans PseudoMetricSpace.uniformity_dist }

Depends on / 依赖: H.trans, PseudoMetricSpace, PseudoMetricSpace.uniformity_dist, toUniformSpace, uniformity_dist
-/
abbrev PseudoMetricSpace.replaceUniformity {α} [U : UniformSpace α] (m : PseudoMetricSpace α)
    (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace]) : PseudoMetricSpace α :=
  { m with
    toUniformSpace := U
    uniformity_dist := H.trans PseudoMetricSpace.uniformity_dist }

/--
theorem `PseudoMetricSpace.replaceUniformity_eq` / 定理 `PseudoMetricSpace.replaceUniformity_eq`

English:
theorem PseudoMetricSpace.replaceUniformity_eq
  statement: {α} [U : UniformSpace α] (m : PseudoMetricSpace α)
  proof: by
  ext
  rfl

中文:
定理 PseudoMetricSpace.replaceUniformity_eq
  结论: {α} [U : UniformSpace α] (m : PseudoMetricSpace α)
  证明: by
  ext
  rfl
-/
theorem PseudoMetricSpace.replaceUniformity_eq {α} [U : UniformSpace α] (m : PseudoMetricSpace α)
    (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace]) : m.replaceUniformity H = m := by
  ext
  rfl

-- ensure that the bornology is unchanged when replacing the uniformity.
example {α} [U : UniformSpace α] (m : PseudoMetricSpace α)
    (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace]) :
    (PseudoMetricSpace.replaceUniformity m H).toBornology = m.toBornology := by
  with_reducible_and_instances rfl

/--
Definition of `PseudoMetricSpace.replaceTopology` / `PseudoMetricSpace.replaceTopology` 的定义

English:
abbreviation PseudoMetricSpace.replaceTopology
  signature: {γ} [U : TopologicalSpace γ] (m : PseudoMetricSpace γ)
  body: @PseudoMetricSpace.replaceUniformity γ (m.toUniformSpace.replaceTopology H) m rfl

中文:
缩写 PseudoMetricSpace.replaceTopology
  签名: {γ} [U : TopologicalSpace γ] (m : PseudoMetricSpace γ)
  定义体: @PseudoMetricSpace.replaceUniformity γ (m.toUniformSpace.replaceTopology H) m rfl

Depends on / 依赖: PseudoMetricSpace, PseudoMetricSpace.replaceUniformity, m.toUniformSpace.replaceTopology, replaceTopology, replaceUniformity, toUniformSpace
-/
abbrev PseudoMetricSpace.replaceTopology {γ} [U : TopologicalSpace γ] (m : PseudoMetricSpace γ)
    (H : U = m.toUniformSpace.toTopologicalSpace) : PseudoMetricSpace γ :=
  @PseudoMetricSpace.replaceUniformity γ (m.toUniformSpace.replaceTopology H) m rfl

/--
theorem `PseudoMetricSpace.replaceTopology_eq` / 定理 `PseudoMetricSpace.replaceTopology_eq`

English:
theorem PseudoMetricSpace.replaceTopology_eq
  statement: {γ} [U : TopologicalSpace γ] (m : PseudoMetricSpace γ)
  proof: by
  ext
  rfl

中文:
定理 PseudoMetricSpace.replaceTopology_eq
  结论: {γ} [U : TopologicalSpace γ] (m : PseudoMetricSpace γ)
  证明: by
  ext
  rfl
-/
theorem PseudoMetricSpace.replaceTopology_eq {γ} [U : TopologicalSpace γ] (m : PseudoMetricSpace γ)
    (H : U = m.toUniformSpace.toTopologicalSpace) : m.replaceTopology H = m := by
  ext
  rfl

/--
Definition of `PseudoEMetricSpace.toPseudoMetricSpaceOfDist` / `PseudoEMetricSpace.toPseudoMetricSpaceOfDist` 的定义

English:
abbreviation PseudoEMetricSpace.toPseudoMetricSpaceOfDist
  signature: {X : Type*} [e : PseudoEMetricSpace X]
  body: dist
  dist_self x := by simpa [h, (dist_nonneg _ _).ge_iff_eq', -edist_self] using edist_self x
  dist_comm x y := by simpa [h, dist_nonneg] using edist_comm x y
  dist_triangle x y z := by
    simpa [h, dist_nonneg, add_nonneg, ← ENNReal.ofReal_add] using edist_triangle x y z
  edist := edist
  ed

中文:
缩写 PseudoEMetricSpace.toPseudoMetricSpaceOfDist
  签名: {X : 类型} [e : PseudoEMetricSpace X]
  定义体: dist
  dist_self x := by simpa [h, (dist_nonneg _ _).ge_iff_eq', -edist_self] using edist_self x
  dist_comm x y := by simpa [h, dist_nonneg] using edist_comm x y
  dist_triangle x y z := by
    simpa [h, dist_nonneg, add_nonneg, ← ENNReal.ofReal_add] using edist_triangle x y z
  edist := edist
  ed
-/
abbrev PseudoEMetricSpace.toPseudoMetricSpaceOfDist {X : Type*} [e : PseudoEMetricSpace X]
    (dist : X -> X -> Real) (dist_nonneg : forall x y, 0 <= dist x y)
    (h : forall x y, edist x y = .ofReal (dist x y)) : PseudoMetricSpace X where
  dist := dist
  dist_self x := by simpa [h, (dist_nonneg _ _).ge_iff_eq', -edist_self] using edist_self x
  dist_comm x y := by simpa [h, dist_nonneg] using edist_comm x y
  dist_triangle x y z := by
    simpa [h, dist_nonneg, add_nonneg, ← ENNReal.ofReal_add] using edist_triangle x y z
  edist := edist
  edist_dist _ _ := by simp only [h]
  toUniformSpace := PseudoEMetricSpace.toUniformSpace
uniformity_dist := e.uniformity_edist.trans by
    simpa [h, dist_nonneg, ENNReal.coe_toNNReal_eq_toReal]
      using (Metric.uniformity_edist_aux fun x y : X => (edist x y).toNNReal).symm

/--
Definition of `PseudoEMetricSpace.toPseudoMetricSpace` / `PseudoEMetricSpace.toPseudoMetricSpace` 的定义

English:
abbreviation PseudoEMetricSpace.toPseudoMetricSpace
  signature: {α : Type u} [PseudoEMetricSpace α]
  body: PseudoEMetricSpace.toPseudoMetricSpaceOfDist (ENNReal.toReal <| edist · ·) (by simp) (by simp [h])

中文:
缩写 PseudoEMetricSpace.toPseudoMetricSpace
  签名: {α : 类型u} [PseudoEMetricSpace α]
  定义体: PseudoEMetricSpace.toPseudoMetricSpaceOfDist (ENNReal.toReal <| edist · ·) (by simp) (by simp [h])

Depends on / 依赖: ENNReal, ENNReal.toReal, PseudoEMetricSpace, PseudoEMetricSpace.toPseudoMetricSpaceOfDist, toPseudoMetricSpaceOfDist, toReal
-/
abbrev PseudoEMetricSpace.toPseudoMetricSpace {α : Type u} [PseudoEMetricSpace α]
    (h : forall x y : α, edist x y != ⊤) : PseudoMetricSpace α :=
  PseudoEMetricSpace.toPseudoMetricSpaceOfDist (ENNReal.toReal <| edist · ·) (by simp) (by simp [h])

/--
Definition of `PseudoMetricSpace.replaceBornology` / `PseudoMetricSpace.replaceBornology` 的定义

English:
abbreviation PseudoMetricSpace.replaceBornology
  signature: {α} [B : Bornology α] (m : PseudoMetricSpace α)
  body: { m with
    toBornology := B
cobounded_sets := Set.ext compl_surjective.forall.2 fun s =>
(H s).trans by rw [isBounded_iff, mem_ofPred_eq, compl_compl] }

中文:
缩写 PseudoMetricSpace.replaceBornology
  签名: {α} [B : Bornology α] (m : PseudoMetricSpace α)
  定义体: { m with
    toBornology := B
cobounded_sets := Set.ext compl_surjective.forall.2 fun s =>
(H s).trans by rw [isBounded_iff, mem_ofPred_eq, compl_compl] }

Depends on / 依赖: Set.ext, cobounded_sets, compl_compl, compl_surjective, compl_surjective.forall, isBounded_iff, mem_ofPred_eq, toBornology
-/
abbrev PseudoMetricSpace.replaceBornology {α} [B : Bornology α] (m : PseudoMetricSpace α)
    (H : forall s, @IsBounded _ B s ↔ @IsBounded _ PseudoMetricSpace.toBornology s) :
    PseudoMetricSpace α :=
  { m with
    toBornology := B
cobounded_sets := Set.ext compl_surjective.forall.2 fun s =>
(H s).trans by rw [isBounded_iff, mem_ofPred_eq, compl_compl] }

/--
theorem `PseudoMetricSpace.replaceBornology_eq` / 定理 `PseudoMetricSpace.replaceBornology_eq`

English:
theorem PseudoMetricSpace.replaceBornology_eq
  statement: {α} [m : PseudoMetricSpace α] [B : Bornology α]
  proof: by
  ext
  rfl

中文:
定理 PseudoMetricSpace.replaceBornology_eq
  结论: {α} [m : PseudoMetricSpace α] [B : Bornology α]
  证明: by
  ext
  rfl
-/
theorem PseudoMetricSpace.replaceBornology_eq {α} [m : PseudoMetricSpace α] [B : Bornology α]
    (H : forall s, @IsBounded _ B s ↔ @IsBounded _ PseudoMetricSpace.toBornology s) :
    PseudoMetricSpace.replaceBornology _ H = m := by
  ext
  rfl

-- ensure that the uniformity is unchanged when replacing the bornology.
example {α} [B : Bornology α] (m : PseudoMetricSpace α)
    (H : forall s, @IsBounded _ B s ↔ @IsBounded _ PseudoMetricSpace.toBornology s) :
    (PseudoMetricSpace.replaceBornology m H).toUniformSpace = m.toUniformSpace := by
  with_reducible_and_instances rfl

section Real

/--
Instance `Real.pseudoMetricSpace` / 实例 `Real.pseudoMetricSpace`

English:
instance Real.pseudoMetricSpace
  signature: : PseudoMetricSpace Real where
  body: |x - y|
  dist_self := by simp [abs_zero]
  dist_comm _ _ := abs_sub_comm _ _
  dist_triangle _ _ _ := abs_sub_le _ _ _

中文:
实例 Real.pseudoMetricSpace
  签名: : PseudoMetricSpace 实数 where
  定义体: |x - y|
  dist_self := by simp [abs_zero]
  dist_comm _ _ := abs_sub_comm _ _
  dist_triangle _ _ _ := abs_sub_le _ _ _
-/
instance Real.pseudoMetricSpace : PseudoMetricSpace Real where
  dist x y := |x - y|
  dist_self := by simp [abs_zero]
  dist_comm _ _ := abs_sub_comm _ _
  dist_triangle _ _ _ := abs_sub_le _ _ _

/--
theorem `Real.dist_eq` / 定理 `Real.dist_eq`

English:
theorem Real.dist_eq
  given: (x y : Real)
  statement: dist x y = |x - y|
  proof: rfl

中文:
定理 Real.dist_eq
  条件: (x y : 实数)
  结论: dist x y = |x - y|
  证明: rfl
-/
theorem Real.dist_eq (x y : Real) : dist x y = |x - y| := rfl

/--
theorem `Real.nndist_eq` / 定理 `Real.nndist_eq`

English:
theorem Real.nndist_eq
  given: (x y : Real)
  statement: nndist x y = Real.nnabs (x - y)
  proof: rfl

中文:
定理 Real.nndist_eq
  条件: (x y : 实数)
  结论: nndist x y = 实数.nnabs (x - y)
  证明: rfl
-/
theorem Real.nndist_eq (x y : Real) : nndist x y = Real.nnabs (x - y) := rfl

/--
theorem `Real.nndist_eq'` / 定理 `Real.nndist_eq'`

English:
theorem Real.nndist_eq'
  given: (x y : Real)
  statement: nndist x y = Real.nnabs (y - x)
  proof: nndist_comm _ _

中文:
定理 Real.nndist_eq'
  条件: (x y : 实数)
  结论: nndist x y = 实数.nnabs (y - x)
  证明: nndist_comm _ _

Depends on / 依赖: nndist_comm
-/
theorem Real.nndist_eq' (x y : Real) : nndist x y = Real.nnabs (y - x) :=
  nndist_comm _ _

/--
theorem `Real.dist_0_eq_abs` / 定理 `Real.dist_0_eq_abs`

English:
theorem Real.dist_0_eq_abs
  given: (x : Real)
  statement: dist x 0 = |x|
  proof: by simp [Real.dist_eq]

中文:
定理 Real.dist_0_eq_abs
  条件: (x : 实数)
  结论: dist x 0 = |x|
  证明: by simp [Real.dist_eq]

Depends on / 依赖: Real.dist_eq, dist_eq
-/
theorem Real.dist_0_eq_abs (x : Real) : dist x 0 = |x| := by simp [Real.dist_eq]

/--
theorem `Real.sub_le_dist` / 定理 `Real.sub_le_dist`

English:
theorem Real.sub_le_dist
  given: (x y : Real)
  statement: x - y <= dist x y
  proof: by
  rw [Real.dist_eq]; rw [le_abs]
  exact Or.inl (le_refl _)

中文:
定理 Real.sub_le_dist
  条件: (x y : 实数)
  结论: x - y <= dist x y
  证明: by
  rw [Real.dist_eq]; rw [le_abs]
  exact Or.inl (le_refl _)

Depends on / 依赖: Or.inl, Real.dist_eq, dist_eq, le_abs, le_refl
-/
theorem Real.sub_le_dist (x y : Real) : x - y <= dist x y := by
  rw [Real.dist_eq]; rw [le_abs]
  exact Or.inl (le_refl _)

/--
theorem `Real.ball_eq_Ioo` / 定理 `Real.ball_eq_Ioo`

English:
theorem Real.ball_eq_Ioo
  given: (x r : Real)
  statement: ball x r = Ioo (x - r) (x + r)
  proof: Set.ext fun y => by
    rw [mem_ball]; rw [dist_comm]; rw [Real.dist_eq]; rw [abs_sub_lt_iff]; rw [mem_Ioo]; rw [← sub_lt_iff_lt_add']; rw [sub_lt_comm]

中文:
定理 Real.ball_eq_Ioo
  条件: (x r : 实数)
  结论: ball x r = Ioo (x - r) (x + r)
  证明: Set.ext fun y => by
    rw [mem_ball]; rw [dist_comm]; rw [Real.dist_eq]; rw [abs_sub_lt_iff]; rw [mem_Ioo]; rw [← sub_lt_iff_lt_add']; rw [sub_lt_comm]

Depends on / 依赖: Real.dist_eq, Set.ext, abs_sub_lt_iff, dist_comm, dist_eq, mem_Ioo, mem_ball, sub_lt_comm, sub_lt_iff_lt_add
-/
theorem Real.ball_eq_Ioo (x r : Real) : ball x r = Ioo (x - r) (x + r) :=
  Set.ext fun y => by
    rw [mem_ball]; rw [dist_comm]; rw [Real.dist_eq]; rw [abs_sub_lt_iff]; rw [mem_Ioo]; rw [← sub_lt_iff_lt_add']; rw [sub_lt_comm]

/--
theorem `Real.ball_zero_eq_Ioo` / 定理 `Real.ball_zero_eq_Ioo`

English:
theorem Real.ball_zero_eq_Ioo
  given: (r : Real)
  statement: ball 0 r = Ioo (-r) r
  proof: by
  simp [Real.ball_eq_Ioo]

中文:
定理 Real.ball_zero_eq_Ioo
  条件: (r : 实数)
  结论: ball 0 r = Ioo (-r) r
  证明: by
  simp [Real.ball_eq_Ioo]

Depends on / 依赖: Real.ball_eq_Ioo, ball_eq_Ioo
-/
theorem Real.ball_zero_eq_Ioo (r : Real) : ball 0 r = Ioo (-r) r := by
  simp [Real.ball_eq_Ioo]

/--
theorem `Real.closedBall_eq_Icc` / 定理 `Real.closedBall_eq_Icc`

English:
theorem Real.closedBall_eq_Icc
  given: {x r : Real}
  statement: closedBall x r = Icc (x - r) (x + r)
  proof: by
  ext y
  rw [mem_closedBall]; rw [dist_comm]; rw [Real.dist_eq]; rw [abs_sub_le_iff]; rw [mem_Icc]; rw [← sub_le_iff_le_add']; rw [sub_le_comm]

中文:
定理 Real.closedBall_eq_Icc
  条件: {x r : 实数}
  结论: closedBall x r = Icc (x - r) (x + r)
  证明: by
  ext y
  rw [mem_closedBall]; rw [dist_comm]; rw [Real.dist_eq]; rw [abs_sub_le_iff]; rw [mem_Icc]; rw [← sub_le_iff_le_add']; rw [sub_le_comm]

Depends on / 依赖: Real.dist_eq, abs_sub_le_iff, dist_comm, dist_eq, mem_Icc, mem_closedBall, sub_le_comm, sub_le_iff_le_add
-/
theorem Real.closedBall_eq_Icc {x r : Real} : closedBall x r = Icc (x - r) (x + r) := by
  ext y
  rw [mem_closedBall]; rw [dist_comm]; rw [Real.dist_eq]; rw [abs_sub_le_iff]; rw [mem_Icc]; rw [← sub_le_iff_le_add']; rw [sub_le_comm]

/--
theorem `Real.closedBall_zero_eq_Icc` / 定理 `Real.closedBall_zero_eq_Icc`

English:
theorem Real.closedBall_zero_eq_Icc
  given: (r : Real)
  statement: closedBall 0 r = Icc (-r) r
  proof: by
  simp [Real.closedBall_eq_Icc]

中文:
定理 Real.closedBall_zero_eq_Icc
  条件: (r : 实数)
  结论: closedBall 0 r = Icc (-r) r
  证明: by
  simp [Real.closedBall_eq_Icc]

Depends on / 依赖: Real.closedBall_eq_Icc, closedBall_eq_Icc
-/
theorem Real.closedBall_zero_eq_Icc (r : Real) : closedBall 0 r = Icc (-r) r := by
  simp [Real.closedBall_eq_Icc]

/--
theorem `Real.Ioo_eq_ball` / 定理 `Real.Ioo_eq_ball`

English:
theorem Real.Ioo_eq_ball
  given: (x y : Real)
  statement: Ioo x y = ball ((x + y) / 2) ((y - x) / 2)
  proof: by
  rw [Real.ball_eq_Ioo]; rw [← sub_div]; rw [add_comm]; rw [← sub_add]; rw [add_sub_cancel_left]; rw [add_self_div_two]; rw [← add_div]; rw [add_assoc]; rw [add_sub_cancel]; rw [add_self_div_two]

中文:
定理 Real.Ioo_eq_ball
  条件: (x y : 实数)
  结论: Ioo x y = ball ((x + y) / 2) ((y - x) / 2)
  证明: by
  rw [Real.ball_eq_Ioo]; rw [← sub_div]; rw [add_comm]; rw [← sub_add]; rw [add_sub_cancel_left]; rw [add_self_div_two]; rw [← add_div]; rw [add_assoc]; rw [add_sub_cancel]; rw [add_self_div_two]

Depends on / 依赖: Real.ball_eq_Ioo, add_assoc, add_comm, add_div, add_self_div_two, add_sub_cancel, add_sub_cancel_left, ball_eq_Ioo, sub_add, sub_div
-/
theorem Real.Ioo_eq_ball (x y : Real) : Ioo x y = ball ((x + y) / 2) ((y - x) / 2) := by
  rw [Real.ball_eq_Ioo]; rw [← sub_div]; rw [add_comm]; rw [← sub_add]; rw [add_sub_cancel_left]; rw [add_self_div_two]; rw [← add_div]; rw [add_assoc]; rw [add_sub_cancel]; rw [add_self_div_two]

/--
theorem `Real.Icc_eq_closedBall` / 定理 `Real.Icc_eq_closedBall`

English:
theorem Real.Icc_eq_closedBall
  given: (x y : Real)
  statement: Icc x y = closedBall ((x + y) / 2) ((y - x) / 2)
  proof: by
  rw [Real.closedBall_eq_Icc]; rw [← sub_div]; rw [add_comm]; rw [← sub_add]; rw [add_sub_cancel_left]; rw [add_self_div_two]; rw [← add_div]; rw [add_assoc]; rw [add_sub_cancel]; rw [add_self_div_two]

中文:
定理 Real.Icc_eq_closedBall
  条件: (x y : 实数)
  结论: Icc x y = closedBall ((x + y) / 2) ((y - x) / 2)
  证明: by
  rw [Real.closedBall_eq_Icc]; rw [← sub_div]; rw [add_comm]; rw [← sub_add]; rw [add_sub_cancel_left]; rw [add_self_div_two]; rw [← add_div]; rw [add_assoc]; rw [add_sub_cancel]; rw [add_self_div_two]

Depends on / 依赖: Real.closedBall_eq_Icc, add_assoc, add_comm, add_div, add_self_div_two, add_sub_cancel, add_sub_cancel_left, closedBall_eq_Icc, sub_add, sub_div
-/
theorem Real.Icc_eq_closedBall (x y : Real) : Icc x y = closedBall ((x + y) / 2) ((y - x) / 2) := by
  rw [Real.closedBall_eq_Icc]; rw [← sub_div]; rw [add_comm]; rw [← sub_add]; rw [add_sub_cancel_left]; rw [add_self_div_two]; rw [← add_div]; rw [add_assoc]; rw [add_sub_cancel]; rw [add_self_div_two]

/--
lemma `Real.sphere_eq_pair` / 引理 `Real.sphere_eq_pair`

English:
lemma Real.sphere_eq_pair
  given: (x : Real) {r : Real} (hr : 0 <= r)
  statement: sphere x r = {x - r, x + r}
  proof: by
  ext; simp [dist_eq]; grind

中文:
引理 Real.sphere_eq_pair
  条件: (x : 实数) {r : 实数} (hr : 0 <= r)
  结论: sphere x r = {x - r, x + r}
  证明: by
  ext; simp [dist_eq]; grind

Depends on / 依赖: dist_eq
-/
lemma Real.sphere_eq_pair (x : Real) {r : Real} (hr : 0 <= r) : sphere x r = {x - r, x + r} := by
  ext; simp [dist_eq]; grind

/--
theorem `Metric.uniformity_eq_comap_nhds_zero` / 定理 `Metric.uniformity_eq_comap_nhds_zero`

English:
theorem Metric.uniformity_eq_comap_nhds_zero
  proof: by
  ext s
  simp only [mem_uniformity_dist, (nhds_basis_ball.comap _).mem_iff]
  simp [subset_def, Real.dist_0_eq_abs]

中文:
定理 Metric.uniformity_eq_comap_nhds_zero
  证明: by
  ext s
  simp only [mem_uniformity_dist, (nhds_basis_ball.comap _).mem_iff]
  simp [subset_def, Real.dist_0_eq_abs]

Depends on / 依赖: Real.dist_0_eq_abs, dist_0_eq_abs, mem_iff, mem_uniformity_dist, nhds_basis_ball, nhds_basis_ball.comap, subset_def
-/
theorem Metric.uniformity_eq_comap_nhds_zero :
    𝓤 α = comap (fun p : α × α => dist p.1 p.2) (𝓝 (0 : Real)) := by
  ext s
  simp only [mem_uniformity_dist, (nhds_basis_ball.comap _).mem_iff]
  simp [subset_def, Real.dist_0_eq_abs]

/--
theorem `tendsto_uniformity_iff_dist_tendsto_zero` / 定理 `tendsto_uniformity_iff_dist_tendsto_zero`

English:
theorem tendsto_uniformity_iff_dist_tendsto_zero
  given: {f : ι -> α × α} {p : Filter ι}
  proof: by
  rw [Metric.uniformity_eq_comap_nhds_zero]; rw [tendsto_comap_iff]; rw [Function.comp_def]

中文:
定理 tendsto_uniformity_iff_dist_tendsto_zero
  条件: {f : ι -> α × α} {p : Filter ι}
  证明: by
  rw [Metric.uniformity_eq_comap_nhds_zero]; rw [tendsto_comap_iff]; rw [Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, Metric, Metric.uniformity_eq_comap_nhds_zero, comp_def, tendsto_comap_iff, uniformity_eq_comap_nhds_zero
-/
theorem tendsto_uniformity_iff_dist_tendsto_zero {f : ι -> α × α} {p : Filter ι} :
    Tendsto f p (𝓤 α) ↔ Tendsto (fun x => dist (f x).1 (f x).2) p (𝓝 0) := by
  rw [Metric.uniformity_eq_comap_nhds_zero]; rw [tendsto_comap_iff]; rw [Function.comp_def]

/--
theorem `Filter.Tendsto.congr_dist` / 定理 `Filter.Tendsto.congr_dist`

English:
theorem Filter.Tendsto.congr_dist
  statement: {f₁ f₂ : ι -> α} {p : Filter ι} {a : α}
  proof: h₁.congr_uniformity tendsto_uniformity_iff_dist_tendsto_zero.2 h

alias tendsto_of_tendsto_of_dist := Filter.Tendsto.congr_dist

中文:
定理 Filter.Tendsto.congr_dist
  结论: {f₁ f₂ : ι -> α} {p : Filter ι} {a : α}
  证明: h₁.congr_uniformity tendsto_uniformity_iff_dist_tendsto_zero.2 h

alias tendsto_of_tendsto_of_dist := Filter.Tendsto.congr_dist

Depends on / 依赖: congr_uniformity, tendsto_uniformity_iff_dist_tendsto_zero
-/
theorem Filter.Tendsto.congr_dist {f₁ f₂ : ι -> α} {p : Filter ι} {a : α}
    (h₁ : Tendsto f₁ p (𝓝 a)) (h : Tendsto (fun x => dist (f₁ x) (f₂ x)) p (𝓝 0)) :
    Tendsto f₂ p (𝓝 a) :=
h₁.congr_uniformity tendsto_uniformity_iff_dist_tendsto_zero.2 h

alias tendsto_of_tendsto_of_dist := Filter.Tendsto.congr_dist

/--
theorem `tendsto_iff_of_dist` / 定理 `tendsto_iff_of_dist`

English:
theorem tendsto_iff_of_dist
  statement: {f₁ f₂ : ι -> α} {p : Filter ι} {a : α}
  proof: Uniform.tendsto_congr tendsto_uniformity_iff_dist_tendsto_zero.2 h

中文:
定理 tendsto_iff_of_dist
  结论: {f₁ f₂ : ι -> α} {p : Filter ι} {a : α}
  证明: Uniform.tendsto_congr tendsto_uniformity_iff_dist_tendsto_zero.2 h

Depends on / 依赖: Uniform, Uniform.tendsto_congr, tendsto_congr, tendsto_uniformity_iff_dist_tendsto_zero
-/
theorem tendsto_iff_of_dist {f₁ f₂ : ι -> α} {p : Filter ι} {a : α}
    (h : Tendsto (fun x => dist (f₁ x) (f₂ x)) p (𝓝 0)) : Tendsto f₁ p (𝓝 a) ↔ Tendsto f₂ p (𝓝 a) :=
Uniform.tendsto_congr tendsto_uniformity_iff_dist_tendsto_zero.2 h

end Real

/--
theorem `PseudoMetricSpace.dist_eq_of_dist_zero` / 定理 `PseudoMetricSpace.dist_eq_of_dist_zero`

English:
theorem PseudoMetricSpace.dist_eq_of_dist_zero
  given: (x : α) {y z : α} (h : dist y z = 0)
  proof: dist_comm y x ▸ dist_comm z x ▸ sub_eq_zero.1 (abs_nonpos_iff.1 (h ▸ abs_dist_sub_le y z x))

中文:
定理 PseudoMetricSpace.dist_eq_of_dist_zero
  条件: (x : α) {y z : α} (h : dist y z = 0)
  证明: dist_comm y x ▸ dist_comm z x ▸ sub_eq_zero.1 (abs_nonpos_iff.1 (h ▸ abs_dist_sub_le y z x))

Depends on / 依赖: abs_dist_sub_le, abs_nonpos_iff, dist_comm, sub_eq_zero
-/
theorem PseudoMetricSpace.dist_eq_of_dist_zero (x : α) {y z : α} (h : dist y z = 0) :
    dist x y = dist x z :=
  dist_comm y x ▸ dist_comm z x ▸ sub_eq_zero.1 (abs_nonpos_iff.1 (h ▸ abs_dist_sub_le y z x))

/--
theorem `dist_dist_dist_le_left` / 定理 `dist_dist_dist_le_left`

English:
theorem dist_dist_dist_le_left
  given: (x y z : α)
  statement: dist (dist x z) (dist y z) <= dist x y
  proof: abs_dist_sub_le ..

中文:
定理 dist_dist_dist_le_left
  条件: (x y z : α)
  结论: dist (dist x z) (dist y z) <= dist x y
  证明: abs_dist_sub_le ..

Depends on / 依赖: abs_dist_sub_le
-/
theorem dist_dist_dist_le_left (x y z : α) : dist (dist x z) (dist y z) <= dist x y :=
  abs_dist_sub_le ..

/--
theorem `dist_dist_dist_le_right` / 定理 `dist_dist_dist_le_right`

English:
theorem dist_dist_dist_le_right
  given: (x y z : α)
  statement: dist (dist x y) (dist x z) <= dist y z
  proof: by
  simpa only [dist_comm x] using dist_dist_dist_le_left y z x

中文:
定理 dist_dist_dist_le_right
  条件: (x y z : α)
  结论: dist (dist x y) (dist x z) <= dist y z
  证明: by
  simpa only [dist_comm x] using dist_dist_dist_le_left y z x

Depends on / 依赖: dist_comm, dist_dist_dist_le_left
-/
theorem dist_dist_dist_le_right (x y z : α) : dist (dist x y) (dist x z) <= dist y z := by
  simpa only [dist_comm x] using dist_dist_dist_le_left y z x

/--
theorem `dist_dist_dist_le` / 定理 `dist_dist_dist_le`

English:
theorem dist_dist_dist_le
  given: (x y x' y' : α)
  statement: dist (dist x y) (dist x' y') <= dist x x' + dist y y'
  proof: (dist_triangle _ _ _).trans
    add_le_add (dist_dist_dist_le_left _ _ _) (dist_dist_dist_le_right _ _ _)

中文:
定理 dist_dist_dist_le
  条件: (x y x' y' : α)
  结论: dist (dist x y) (dist x' y') <= dist x x' + dist y y'
  证明: (dist_triangle _ _ _).trans
    add_le_add (dist_dist_dist_le_left _ _ _) (dist_dist_dist_le_right _ _ _)

Depends on / 依赖: add_le_add, dist_dist_dist_le_left, dist_dist_dist_le_right, dist_triangle
-/
theorem dist_dist_dist_le (x y x' y' : α) : dist (dist x y) (dist x' y') <= dist x x' + dist y y' :=
(dist_triangle _ _ _).trans
    add_le_add (dist_dist_dist_le_left _ _ _) (dist_dist_dist_le_right _ _ _)

/--
theorem `nhds_comap_dist` / 定理 `nhds_comap_dist`

English:
theorem nhds_comap_dist
  given: (a : α)
  statement: ((𝓝 (0 : Real)).comap (dist · a)) = 𝓝 a
  proof: by
  simp only [@nhds_eq_comap_uniformity α, Metric.uniformity_eq_comap_nhds_zero, comap_comap,
    Function.comp_def, dist_comm]

中文:
定理 nhds_comap_dist
  条件: (a : α)
  结论: ((𝓝 (0 : 实数)).comap (dist · a)) = 𝓝 a
  证明: by
  simp only [@nhds_eq_comap_uniformity α, Metric.uniformity_eq_comap_nhds_zero, comap_comap,
    Function.comp_def, dist_comm]

Depends on / 依赖: Function, Function.comp_def, Metric, Metric.uniformity_eq_comap_nhds_zero, comap_comap, comp_def, dist_comm, nhds_eq_comap_uniformity, uniformity_eq_comap_nhds_zero
-/
theorem nhds_comap_dist (a : α) : ((𝓝 (0 : Real)).comap (dist · a)) = 𝓝 a := by
  simp only [@nhds_eq_comap_uniformity α, Metric.uniformity_eq_comap_nhds_zero, comap_comap,
    Function.comp_def, dist_comm]

/--
theorem `tendsto_iff_dist_tendsto_zero` / 定理 `tendsto_iff_dist_tendsto_zero`

English:
theorem tendsto_iff_dist_tendsto_zero
  given: {f : β -> α} {x : Filter β} {a : α}
  proof: by
  rw [← nhds_comap_dist a]; rw [tendsto_comap_iff]; rw [Function.comp_def]

中文:
定理 tendsto_iff_dist_tendsto_zero
  条件: {f : β -> α} {x : Filter β} {a : α}
  证明: by
  rw [← nhds_comap_dist a]; rw [tendsto_comap_iff]; rw [Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, comp_def, nhds_comap_dist, tendsto_comap_iff
-/
theorem tendsto_iff_dist_tendsto_zero {f : β -> α} {x : Filter β} {a : α} :
    Tendsto f x (𝓝 a) ↔ Tendsto (fun b => dist (f b) a) x (𝓝 0) := by
  rw [← nhds_comap_dist a]; rw [tendsto_comap_iff]; rw [Function.comp_def]

namespace Metric

variable {x y z : α} {ε ε₁ ε₂ : Real} {s : Set α}

/--
lemma `mk_uniformity_basis_of_tendsto` / 引理 `mk_uniformity_basis_of_tendsto`

English:
lemma mk_uniformity_basis_of_tendsto
  statement: {β : Type*} {p : β -> Prop} {f : β -> Real}
  proof: by
  apply Metric.mk_uniformity_basis hf₀
  rw [nhds_basis_closedBall.tendsto_right_iff] at hf
.exists.imp fun i => and_imp.mpr fun hp hi => ?_ refine fun ε hε => hf₁.and (hf ε hε)
  exact ⟨hp, by
    simpa [Metric.mem_closedBall, Real.dist_eq, abs_of_nonneg (hf₀ i hp).le] using hi⟩

中文:
引理 mk_uniformity_basis_of_tendsto
  结论: {β : 类型} {p : β -> 命题} {f : β -> 实数}
  证明: by
  apply Metric.mk_uniformity_basis hf₀
  rw [nhds_basis_closedBall.tendsto_right_iff] at hf
.exists.imp fun i => and_imp.mpr fun hp hi => ?_ refine fun ε hε => hf₁.and (hf ε hε)
  exact ⟨hp, by
    simpa [Metric.mem_closedBall, Real.dist_eq, abs_of_nonneg (hf₀ i hp).le] using hi⟩

Depends on / 依赖: Metric, Metric.mem_closedBall, Metric.mk_uniformity_basis, Real.dist_eq, abs_of_nonneg, and_imp, and_imp.mpr, dist_eq, exists.imp, mem_closedBall, mk_uniformity_basis, nhds_basis_closedBall, nhds_basis_closedBall.tendsto_right_iff, tendsto_right_iff
-/
lemma mk_uniformity_basis_of_tendsto {β : Type*} {p : β -> Prop} {f : β -> Real}
    {l : Filter β} [l.NeBot] (hf₀ : forall i, p i -> 0 < f i) (hf₁ : forallᶠ i in l, p i)
    (hf : Tendsto f l (𝓝 0)) :
    (𝓤 α).HasBasis p fun i => {x | dist x.1 x.2 < f i} := by
  apply Metric.mk_uniformity_basis hf₀
  rw [nhds_basis_closedBall.tendsto_right_iff] at hf
.exists.imp fun i => and_imp.mpr fun hp hi => ?_ refine fun ε hε => hf₁.and (hf ε hε)
  exact ⟨hp, by
    simpa [Metric.mem_closedBall, Real.dist_eq, abs_of_nonneg (hf₀ i hp).le] using hi⟩

/--
theorem `ball_subset_interior_closedBall` / 定理 `ball_subset_interior_closedBall`

English:
theorem ball_subset_interior_closedBall
  statement: ball x ε subseteq interior (closedBall x ε)
  proof: interior_maximal ball_subset_closedBall isOpen_ball

中文:
定理 ball_subset_interior_closedBall
  结论: ball x ε subseteq interior (closedBall x ε)
  证明: interior_maximal ball_subset_closedBall isOpen_ball

Depends on / 依赖: ball_subset_closedBall, interior_maximal, isOpen_ball
-/
theorem ball_subset_interior_closedBall : ball x ε subseteq interior (closedBall x ε) :=
  interior_maximal ball_subset_closedBall isOpen_ball

/--
theorem `mem_closure_iff` / 定理 `mem_closure_iff`

English:
theorem mem_closure_iff
  given: {s : Set α} {a : α}
  statement: a in closure s ↔ forall ε > 0, exists b in s, dist a b < ε
  proof: (mem_closure_iff_nhds_basis nhds_basis_ball).trans by simp only [mem_ball, dist_comm]

中文:
定理 mem_closure_iff
  条件: {s : Set α} {a : α}
  结论: a in closure s ↔ 对任意 ε > 0, 存在 b in s, dist a b < ε
  证明: (mem_closure_iff_nhds_basis nhds_basis_ball).trans by simp only [mem_ball, dist_comm]

Depends on / 依赖: dist_comm, mem_ball, mem_closure_iff_nhds_basis, nhds_basis_ball
-/
theorem mem_closure_iff {s : Set α} {a : α} : a in closure s ↔ forall ε > 0, exists b in s, dist a b < ε :=
(mem_closure_iff_nhds_basis nhds_basis_ball).trans by simp only [mem_ball, dist_comm]

/--
theorem `mem_closure_range_iff` / 定理 `mem_closure_range_iff`

English:
theorem mem_closure_range_iff
  given: {e : β -> α} {a : α}
  proof: by
  simp only [mem_closure_iff, exists_range_iff]

中文:
定理 mem_closure_range_iff
  条件: {e : β -> α} {a : α}
  证明: by
  simp only [mem_closure_iff, exists_range_iff]

Depends on / 依赖: exists_range_iff, mem_closure_iff
-/
theorem mem_closure_range_iff {e : β -> α} {a : α} :
    a in closure (range e) ↔ forall ε > 0, exists k : β, dist a (e k) < ε := by
  simp only [mem_closure_iff, exists_range_iff]

/--
theorem `mem_closure_range_iff_nat` / 定理 `mem_closure_range_iff_nat`

English:
theorem mem_closure_range_iff_nat
  given: {e : β -> α} {a : α}
  proof: (mem_closure_iff_nhds_basis nhds_basis_ball_inv_nat_succ).trans by
    simp only [mem_ball, dist_comm, exists_range_iff, forall_const]

中文:
定理 mem_closure_range_iff_nat
  条件: {e : β -> α} {a : α}
  证明: (mem_closure_iff_nhds_basis nhds_basis_ball_inv_nat_succ).trans by
    simp only [mem_ball, dist_comm, exists_range_iff, forall_const]

Depends on / 依赖: dist_comm, exists_range_iff, forall_const, mem_ball, mem_closure_iff_nhds_basis, nhds_basis_ball_inv_nat_succ
-/
theorem mem_closure_range_iff_nat {e : β -> α} {a : α} :
    a in closure (range e) ↔ forall n : Nat, exists k : β, dist a (e k) < 1 / ((n : Real) + 1) :=
(mem_closure_iff_nhds_basis nhds_basis_ball_inv_nat_succ).trans by
    simp only [mem_ball, dist_comm, exists_range_iff, forall_const]

/--
theorem `mem_of_closed'` / 定理 `mem_of_closed'`

English:
theorem mem_of_closed'
  given: {s : Set α} (hs : IsClosed s) {a : α}
  proof: by
  simpa only [hs.closure_eq] using @mem_closure_iff _ _ s a

中文:
定理 mem_of_closed'
  条件: {s : Set α} (hs : IsClosed s) {a : α}
  证明: by
  simpa only [hs.closure_eq] using @mem_closure_iff _ _ s a

Depends on / 依赖: closure_eq, hs.closure_eq, mem_closure_iff
-/
theorem mem_of_closed' {s : Set α} (hs : IsClosed s) {a : α} :
    a in s ↔ forall ε > 0, exists b in s, dist a b < ε := by
  simpa only [hs.closure_eq] using @mem_closure_iff _ _ s a

/--
theorem `dense_iff` / 定理 `dense_iff`

English:
theorem dense_iff
  given: {s : Set α}
  statement: Dense s ↔ forall x, forall r > 0, (ball x r inter s).Nonempty
  proof: forall_congr' fun x => by
    simp only [mem_closure_iff, Set.Nonempty, mem_inter_iff, mem_ball', and_comm]

中文:
定理 dense_iff
  条件: {s : Set α}
  结论: Dense s ↔ 对任意 x, 对任意 r > 0, (ball x r inter s).Nonempty
  证明: forall_congr' fun x => by
    simp only [mem_closure_iff, Set.Nonempty, mem_inter_iff, mem_ball', and_comm]

Depends on / 依赖: Nonempty, Set.Nonempty, and_comm, forall_congr, mem_ball, mem_closure_iff, mem_inter_iff
-/
theorem dense_iff {s : Set α} : Dense s ↔ forall x, forall r > 0, (ball x r inter s).Nonempty :=
  forall_congr' fun x => by
    simp only [mem_closure_iff, Set.Nonempty, mem_inter_iff, mem_ball', and_comm]

/--
theorem `dense_iff_iUnion_ball` / 定理 `dense_iff_iUnion_ball`

English:
theorem dense_iff_iUnion_ball
  given: (s : Set α)
  statement: Dense s ↔ forall r > 0, ⋃ c in s, ball c r = univ
  proof: by
  simp_rw [eq_univ_iff_forall, mem_iUnion, exists_prop, mem_ball, Dense, mem_closure_iff,
    forall_comm (α := α)]

中文:
定理 dense_iff_iUnion_ball
  条件: (s : Set α)
  结论: Dense s ↔ 对任意 r > 0, ⋃ c in s, ball c r = univ
  证明: by
  simp_rw [eq_univ_iff_forall, mem_iUnion, exists_prop, mem_ball, Dense, mem_closure_iff,
    forall_comm (α := α)]

Depends on / 依赖: eq_univ_iff_forall, exists_prop, forall_comm, mem_ball, mem_closure_iff, mem_iUnion, simp_rw
-/
theorem dense_iff_iUnion_ball (s : Set α) : Dense s ↔ forall r > 0, ⋃ c in s, ball c r = univ := by
  simp_rw [eq_univ_iff_forall, mem_iUnion, exists_prop, mem_ball, Dense, mem_closure_iff,
    forall_comm (α := α)]

/--
theorem `denseRange_iff` / 定理 `denseRange_iff`

English:
theorem denseRange_iff
  given: {f : β -> α}
  statement: DenseRange f ↔ forall x, forall r > 0, exists y, dist x (f y) < r
  proof: forall_congr' fun x => by simp only [mem_closure_iff, exists_range_iff]

中文:
定理 denseRange_iff
  条件: {f : β -> α}
  结论: DenseRange f ↔ 对任意 x, 对任意 r > 0, 存在 y, dist x (f y) < r
  证明: forall_congr' fun x => by simp only [mem_closure_iff, exists_range_iff]

Depends on / 依赖: exists_range_iff, forall_congr, mem_closure_iff
-/
theorem denseRange_iff {f : β -> α} : DenseRange f ↔ forall x, forall r > 0, exists y, dist x (f y) < r :=
  forall_congr' fun x => by simp only [mem_closure_iff, exists_range_iff]

end Metric

open Additive Multiplicative

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PseudoMetricSpace (Additive α)
  body: ‹_›

中文:
实例 :
  签名: PseudoMetricSpace (Additive α)
  定义体: ‹_›
-/
instance : PseudoMetricSpace (Additive α) := ‹_›
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PseudoMetricSpace (Multiplicative α)
  body: ‹_›

中文:
实例 :
  签名: PseudoMetricSpace (Multiplicative α)
  定义体: ‹_›
-/
instance : PseudoMetricSpace (Multiplicative α) := ‹_›

section

variable [PseudoMetricSpace X]

/--
theorem `nndist_ofMul` / 定理 `nndist_ofMul`

English:
theorem nndist_ofMul
  given: (a b : X)
  statement: nndist (ofMul a) (ofMul b) = nndist a b
  proof: rfl

中文:
定理 nndist_ofMul
  条件: (a b : X)
  结论: nndist (ofMul a) (ofMul b) = nndist a b
  证明: rfl
-/
@[simp] theorem nndist_ofMul (a b : X) : nndist (ofMul a) (ofMul b) = nndist a b := rfl

/--
theorem `nndist_ofAdd` / 定理 `nndist_ofAdd`

English:
theorem nndist_ofAdd
  given: (a b : X)
  statement: nndist (ofAdd a) (ofAdd b) = nndist a b
  proof: rfl

中文:
定理 nndist_ofAdd
  条件: (a b : X)
  结论: nndist (ofAdd a) (ofAdd b) = nndist a b
  证明: rfl
-/
@[simp] theorem nndist_ofAdd (a b : X) : nndist (ofAdd a) (ofAdd b) = nndist a b := rfl

/--
theorem `nndist_toMul` / 定理 `nndist_toMul`

English:
theorem nndist_toMul
  given: (a b : Additive X)
  statement: nndist a.toMul b.toMul = nndist a b
  proof: rfl

@[simp]

中文:
定理 nndist_toMul
  条件: (a b : Additive X)
  结论: nndist a.toMul b.toMul = nndist a b
  证明: rfl

@[simp]
-/
@[simp] theorem nndist_toMul (a b : Additive X) : nndist a.toMul b.toMul = nndist a b := rfl

@[simp]
/--
theorem `nndist_toAdd` / 定理 `nndist_toAdd`

English:
theorem nndist_toAdd
  given: (a b : Multiplicative X)
  statement: nndist a.toAdd b.toAdd = nndist a b
  proof: rfl

中文:
定理 nndist_toAdd
  条件: (a b : Multiplicative X)
  结论: nndist a.toAdd b.toAdd = nndist a b
  证明: rfl
-/
theorem nndist_toAdd (a b : Multiplicative X) : nndist a.toAdd b.toAdd = nndist a b := rfl

end

open OrderDual

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PseudoMetricSpace αᵒᵈ
  body: ‹_›

中文:
实例 :
  签名: PseudoMetricSpace αᵒᵈ
  定义体: ‹_›
-/
instance : PseudoMetricSpace αᵒᵈ := ‹_›

section

variable [PseudoMetricSpace X]

/--
theorem `nndist_toDual` / 定理 `nndist_toDual`

English:
theorem nndist_toDual
  given: (a b : X)
  statement: nndist (toDual a) (toDual b) = nndist a b
  proof: rfl

中文:
定理 nndist_toDual
  条件: (a b : X)
  结论: nndist (toDual a) (toDual b) = nndist a b
  证明: rfl
-/
@[simp] theorem nndist_toDual (a b : X) : nndist (toDual a) (toDual b) = nndist a b := rfl

/--
theorem `nndist_ofDual` / 定理 `nndist_ofDual`

English:
theorem nndist_ofDual
  given: (a b : Xᵒᵈ)
  statement: nndist (ofDual a) (ofDual b) = nndist a b
  proof: rfl

中文:
定理 nndist_ofDual
  条件: (a b : Xᵒᵈ)
  结论: nndist (ofDual a) (ofDual b) = nndist a b
  证明: rfl
-/
@[simp] theorem nndist_ofDual (a b : Xᵒᵈ) : nndist (ofDual a) (ofDual b) = nndist a b := rfl

end
