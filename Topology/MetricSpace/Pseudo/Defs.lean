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

/-
**UniformSpace.ofDist_aux** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformSpace.ofDist_aux (ε : Real) (hε : 0 < ε) : exists δ > (0 : Real), f
orall x < δ, forall y < δ, x + y < ε
参数：ε : Real；hε : 0 < ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `add_lt_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftStrictMono α] [AddRightStrictMono α] {a b c d : α},   a < b → c < d → a + c < 
…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `add_halves`：∀ {K : Type u_1} [inst : DivisionSemiring K] [NeZero 2] (a :
 K), a / 2 + a / 2 = a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem UniformSpace.ofDist_aux (ε : ℝ) (hε : 0 < ε) : ∃ δ > (0 : ℝ), ∀ x < δ, ∀ y < δ, x + y < ε :=
  ⟨ε / 2, half_pos hε, fun _x hx _y hy => add_halves ε ▸ add_lt_add hx hy⟩

/-- Construct a uniform structure from a distance function and metric space axioms -/
@[instance_reducible]
/-
**UniformSpace.ofDist** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：UniformSpace.ofDist (dist : α -> α -> Real) (dist_self : forall x : α, dis
t x x = 0) (dist_comm : forall x y : α, dist x y = dist y x) (dist_triangle : fo
rall x y z : α, dist x z <= dist x y + dist y z) : UniformSpace α
参数：dist : α -> α -> Real；dist_self : forall x : α, dist x x = 0；dist_comm : fora
ll x y : α, dist x y = dist y x；dist_triangle : forall x y z : α, dist x z <= di
st x y + dist y z。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.ofDist_aux`：UniformSpace.ofDist_aux (ε : Real) (hε : 0 < ε)
 : exists δ > (0 : Real), forall x < δ, forall y < δ, x + y < ε

--- 原说明 ---
Construct a uniform structure from a distance function and metric space axioms
-/
def UniformSpace.ofDist (dist : α → α → ℝ) (dist_self : ∀ x : α, dist x x = 0)
    (dist_comm : ∀ x y : α, dist x y = dist y x)
    (dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z) : UniformSpace α :=
  .ofFun dist dist_self dist_comm dist_triangle ofDist_aux

/-- Construct a bornology from a distance function and metric space axioms. -/
/-
**Bornology.ofDist** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Bornology.ofDist {α : Type*} (dist : α -> α -> Real) (dist_comm : forall x
 y, dist x y = dist y x) (dist_triangle : forall x y z, dist x z <= dist x y + d
ist y z) : Bornology α
参数：dist : α -> α -> Real；dist_comm : forall x y, dist x y = dist y x；dist_triang
le : forall x y z, dist x z <= dist x y + dist y z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a bornology from a distance function and metric space axioms.
-/
abbrev Bornology.ofDist {α : Type*} (dist : α → α → ℝ) (dist_comm : ∀ x y, dist x y = dist y x)
    (dist_triangle : ∀ x y z, dist x z ≤ dist x y + dist y z) : Bornology α :=
  Bornology.ofBounded { s : Set α | ∃ C, ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → dist x y ≤ C }
    ⟨0, fun _ hx _ => hx.elim⟩ (fun _ ⟨c, hc⟩ _ h => ⟨c, fun _ hx _ hy => hc (h hx) (h hy)⟩)
    (fun s hs t ht => by
      rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
      · rwa [empty_union]
      rcases t.eq_empty_or_nonempty with rfl | ⟨y, hy⟩
      · rwa [union_empty]
      rsuffices ⟨C, hC⟩ : ∃ C, ∀ z ∈ s ∪ t, dist x z ≤ C
      · refine ⟨C + C, fun a ha b hb => (dist_triangle a x b).trans ?_⟩
        simpa only [dist_comm] using add_le_add (hC _ ha) (hC _ hb)
      rcases hs with ⟨Cs, hs⟩; rcases ht with ⟨Ct, ht⟩
      refine ⟨max Cs (dist x y + Ct), fun z hz => hz.elim
        (fun hz => (hs hx hz).trans (le_max_left _ _))
        (fun hz => (dist_triangle x y z).trans <|
          (add_le_add le_rfl (ht hy hz)).trans (le_max_right _ _))⟩)
    fun z => ⟨dist z z, forall_eq.2 <| forall_eq.2 le_rfl⟩

/-- The distance function (given an ambient metric space on `α`), which returns
  a nonnegative real number `dist x y` given `x y : α`. -/
@[ext]
/-
**Dist** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：Dist (α : Type*) where /-- Distance between two points -/ dist : α -> α ->
 Real  export Dist (dist)  -- the uniform structure and the emetric space struct
ure are embedded in the metric space structure -- to avoid instance diamond issu
es. See Note [forgetful inheritance]. set_option backward.privateInPublic true i
n /-- This is an internal lemma used inside the default of `PseudoMetricSpace.ed
ist`. -/ private theorem dist_nonneg' {α} {x y : α} (dist : α -> α -> Real) (dis
t_self : forall x : α, dis
参数：α : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The distance function (given an ambient metric space on `α`), which returns
  a nonnegative real number `dist x y` given `x y : α`.
-/
class Dist (α : Type*) where
  /-- Distance between two points -/
  dist : α → α → ℝ

export Dist (dist)

-- the uniform structure and the emetric space structure are embedded in the metric space structure
-- to avoid instance diamond issues. See Note [forgetful inheritance].
set_option backward.privateInPublic true in
/-- This is an internal lemma used inside the default of `PseudoMetricSpace.edist`. -/
/-
**dist_nonneg'** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is an internal lemma used inside the default of `PseudoMetricSpace.edist`.
-/
private theorem dist_nonneg' {α} {x y : α} (dist : α → α → ℝ)
    (dist_self : ∀ x : α, dist x x = 0) (dist_comm : ∀ x y : α, dist x y = dist y x)
    (dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z) : 0 ≤ dist x y :=
  have : 0 ≤ 2 * dist x y :=
    calc 0 = dist x x := (dist_self _).symm
    _ ≤ dist x y + dist y x := dist_triangle _ _ _
    _ = 2 * dist x y := by rw [two_mul, dist_comm]
  nonneg_of_mul_nonneg_right this two_pos

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- A pseudometric space is a type endowed with a `ℝ`-valued distance `dist` satisfying
reflexivity `dist x x = 0`, commutativity `dist x y = dist y x`, and the triangle inequality
`dist x z ≤ dist x y + dist y z`.

Note that we do not require `dist x y = 0 → x = y`. See metric spaces (`MetricSpace`) for the
similar class with that stronger assumption.

Any pseudometric space is a topological space and a uniform space (see `TopologicalSpace`,
`UniformSpace`), where the topology and uniformity come from the metric.
Note that a T1 pseudometric space is just a metric space.

We make the uniformity/topology part of the data instead of deriving it from the metric. This e.g.
ensures that we do not get a diamond when doing
`[PseudoMetricSpace α] [PseudoMetricSpace β] : TopologicalSpace (α × β)`:
The product metric and product topology agree, but not definitionally so.
See Note [forgetful inheritance]. -/
/-
**PseudoMetricSpace** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：PseudoMetricSpace (α : Type u) : Type u extends Dist α where dist_self : f
orall x : α, dist x x = 0 dist_comm : forall x y : α, dist x y = dist y x dist_t
riangle : forall x y z : α, dist x z <= dist x y + dist y z /-- Extended distanc
e between two points -/ edist : α -> α -> Real>=0∞
参数：α : Type u。
继承自：Dist α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pseudometric space is a type endowed with a `ℝ`-valued distance `dist` satisfy
ing
reflexivity `dist x x = 0`, commutativity `dist x y = dist y x`, and the triangl
e inequality
`dist x z ≤ dist x y + dist y z`.

Note that we do not require `dist x y = 0 → x = y`. See metric spaces (`MetricSp
ace`) for the
similar class with that stronger assumption.

Any pseudometric space is a topological space and a uniform space (see `Topologi
calSpace`,
`UniformSpace`), where the topology and uniformity come from the metric.
Note that a T1 pseudometric space is just a metric space.

We make the uniformity/topology part of the data instead of deriving it from the
 metric. This e.g.
ensures that we do not get a diamond when doing
`[PseudoMetricSpace α] [PseudoMetricSpace β] : TopologicalSpace (α × β)`:
The product metric and product topology agree, but not definitionally so.
See Note [forgetful inheritance].
-/
class PseudoMetricSpace (α : Type u) : Type u extends Dist α where
  dist_self : ∀ x : α, dist x x = 0
  dist_comm : ∀ x y : α, dist x y = dist y x
  dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z
  /-- Extended distance between two points -/
  edist : α → α → ℝ≥0∞ := fun x y => ENNReal.ofNNReal (.mk (dist x y) (dist_nonneg' _ ‹_› ‹_› ‹_›))
  edist_dist : ∀ x y : α, edist x y = ENNReal.ofReal (dist x y) := by
    intro x y; exact ENNReal.coe_nnreal_eq _
  toUniformSpace : UniformSpace α := .ofDist dist dist_self dist_comm dist_triangle
  uniformity_dist : 𝓤 α = ⨅ ε > 0, 𝓟 { p : α × α | dist p.1 p.2 < ε } := by intros; rfl
  toBornology : Bornology α := Bornology.ofDist dist dist_comm dist_triangle
  cobounded_sets : (Bornology.cobounded α).sets =
    { s | ∃ C : ℝ, ∀ x ∈ sᶜ, ∀ y ∈ sᶜ, dist x y ≤ C } := by intros; rfl

/-- Two pseudometric space structures with the same distance function coincide. -/
@[ext]
/-
**PseudoMetricSpace.ext** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PseudoMetricSpace.ext {α : Type*} {m m' : PseudoMetricSpace α} (h : m.toDi
st = m'.toDist) : m = m'
参数：h : m.toDist = m'.toDist。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniformSpace.ext`：∀ {α : Type ua} {u₁ u₂ : UniformSpace α}, uniformity α
 = uniformity α → u₁ = u₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Bornology.ext`：Bornology.ext (t t' : Bornology α) (h_cobounded : @Bornol
ogy.cobounded α t = @Bornology.cobounded α t') : t = t'
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `Filter.mem_sets`：∀ {α : Type u_1} {f : Filter α} {s : Set α}, s ∈ f.sets
 ↔ s ∈ f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Two pseudometric space structures with the same distance function coincide.
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
    rw [hed, hed']
  · exact UniformSpace.ext (hU.trans hU'.symm)
  · ext : 2
    rw [← Filter.mem_sets, ← Filter.mem_sets, hB, hB']

variable [PseudoMetricSpace α]

attribute [instance_reducible, instance]
  PseudoMetricSpace.toUniformSpace PseudoMetricSpace.toBornology

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 200) PseudoMetricSpace.toEDist : EDist α :=
  ⟨PseudoMetricSpace.edist⟩

/-- Construct a pseudo-metric space structure whose underlying topological space structure
(definitionally) agrees which a pre-existing topology which is compatible with a given distance
function. -/
@[instance_reducible]
/-
**PseudoMetricSpace.ofDistTopology** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：PseudoMetricSpace.ofDistTopology {α : Type u} [TopologicalSpace α] (dist :
 α -> α -> Real) (dist_self : forall x : α, dist x x = 0) (dist_comm : forall x 
y : α, dist x y = dist y x) (dist_triangle : forall x y z : α, dist x z <= dist 
x y + dist y z) (H : forall s : Set α, IsOpen s ↔ forall x in s, exists ε > 0, f
orall y, dist x y < ε -> y in s) : PseudoMetricSpace α
参数：dist : α -> α -> Real；dist_self : forall x : α, dist x x = 0；dist_comm : fora
ll x y : α, dist x y = dist y x；dist_triangle : forall x y z : α, dist x z <= di
st x y + dist y z；H : forall s : Set α, IsOpen s ↔ forall x in s, exists ε > 0, 
forall y, dist x y < ε -> y in s。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Topology.MetricSpace.Pseudo.Defs.0.dist_nonneg'`：∀ {α :
 Sort u_3} {x y : α} (dist : α → α → ℝ),   (∀ (x : α), dist x x = 0) →     (∀ (x
 y : α), dist x y = dist y x) → (∀ (x y z : α), dist x…

--- 原说明 ---
Construct a pseudo-metric space structure whose underlying topological space str
ucture
(definitionally) agrees which a pre-existing topology which is compatible with a
 given distance
function.
-/
def PseudoMetricSpace.ofDistTopology {α : Type u} [TopologicalSpace α] (dist : α → α → ℝ)
    (dist_self : ∀ x : α, dist x x = 0) (dist_comm : ∀ x y : α, dist x y = dist y x)
    (dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z)
    (H : ∀ s : Set α, IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ∀ y, dist x y < ε → y ∈ s) :
    PseudoMetricSpace α :=
  { dist := dist
    dist_self := dist_self
    dist_comm := dist_comm
    dist_triangle := dist_triangle
    toUniformSpace :=
      (UniformSpace.ofDist dist dist_self dist_comm dist_triangle).replaceTopology <|
        TopologicalSpace.ext_iff.2 fun s ↦ (H s).trans <| forall₂_congr fun x _ ↦
          ((UniformSpace.hasBasis_ofFun (exists_gt (0 : ℝ)) dist dist_self dist_comm dist_triangle
            UniformSpace.ofDist_aux).comap (Prod.mk x)).mem_iff.symm
    uniformity_dist := rfl
    toBornology := Bornology.ofDist dist dist_comm dist_triangle
    cobounded_sets := rfl }

@[simp]
/-
**dist_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_self (x : α) : dist x x = 0
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PseudoMetricSpace.dist_self`：∀ {α : Type u} [self : PseudoMetricSpace α]
 (x : α), dist x x = 0
-/
theorem dist_self (x : α) : dist x x = 0 :=
  PseudoMetricSpace.dist_self x
/-
**dist_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_comm (x y : α) : dist x y = dist y x
参数：x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PseudoMetricSpace.dist_comm`：∀ {α : Type u} [self : PseudoMetricSpace α]
 (x y : α), dist x y = dist y x
-/
theorem dist_comm (x y : α) : dist x y = dist y x :=
  PseudoMetricSpace.dist_comm x y
/-
**edist_dist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_dist (x y : α) : edist x y = ENNReal.ofReal (dist x y)
参数：x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PseudoMetricSpace.edist_dist`：∀ {α : Type u} [self : PseudoMetricSpace α
] (x y : α), PseudoMetricSpace.edist x y = ENNReal.ofReal (dist x y)
-/
theorem edist_dist (x y : α) : edist x y = ENNReal.ofReal (dist x y) :=
  PseudoMetricSpace.edist_dist x y

@[bound]
/-
**dist_triangle** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_triangle (x y z : α) : dist x z <= dist x y + dist y z
参数：x y z : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PseudoMetricSpace.dist_triangle`：∀ {α : Type u} [self : PseudoMetricSpac
e α] (x y z : α), dist x z ≤ dist x y + dist y z
-/
theorem dist_triangle (x y z : α) : dist x z ≤ dist x y + dist y z :=
  PseudoMetricSpace.dist_triangle x y z
/-
**dist_triangle_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_triangle_left (x y z : α) : dist x y <= dist z x + dist z y
参数：x y z : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `dist_triangle`：dist_triangle (x y z : α) : dist x z <= dist x y + dist y
 z
-/
theorem dist_triangle_left (x y z : α) : dist x y ≤ dist z x + dist z y := by
  rw [dist_comm z]; apply dist_triangle
/-
**dist_triangle_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_triangle_right (x y z : α) : dist x y <= dist x z + dist y z
参数：x y z : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `dist_triangle`：dist_triangle (x y z : α) : dist x z <= dist x y + dist y
 z
-/
theorem dist_triangle_right (x y z : α) : dist x y ≤ dist x z + dist y z := by
  rw [dist_comm y]; apply dist_triangle
/-
**dist_triangle4** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_triangle4 (x y z w : α) : dist x w <= dist x y + dist y z + dist z w
参数：x y z w : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dist_triangle`：dist_triangle (x y z : α) : dist x z <= dist x y + dist y
 z
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem dist_triangle4 (x y z w : α) : dist x w ≤ dist x y + dist y z + dist z w :=
  calc
    dist x w ≤ dist x z + dist z w := dist_triangle x z w
    _ ≤ dist x y + dist y z + dist z w := by gcongr; apply dist_triangle x y z
/-
**dist_triangle4_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_triangle4_left (x₁ y₁ x₂ y₂ : α) : dist x₂ y₂ <= dist x₁ y₁ + (dist x
₁ x₂ + dist y₁ y₂)
参数：x₁ y₁ x₂ y₂ : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_left_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G),
 a + (b + c) = b + (a + c)
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `dist_triangle4`：dist_triangle4 (x y z w : α) : dist x w <= dist x y + di
st y z + dist z w
-/
theorem dist_triangle4_left (x₁ y₁ x₂ y₂ : α) :
    dist x₂ y₂ ≤ dist x₁ y₁ + (dist x₁ x₂ + dist y₁ y₂) := by
  rw [add_left_comm, dist_comm x₁, ← add_assoc]
  apply dist_triangle4
/-
**dist_triangle4_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_triangle4_right (x₁ y₁ x₂ y₂ : α) : dist x₁ y₁ <= dist x₁ x₂ + dist y
₁ y₂ + dist x₂ y₂
参数：x₁ y₁ x₂ y₂ : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_right_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G)
, a + b + c = a + c + b
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `dist_triangle4`：dist_triangle4 (x y z w : α) : dist x w <= dist x y + di
st y z + dist z w
-/
theorem dist_triangle4_right (x₁ y₁ x₂ y₂ : α) :
    dist x₁ y₁ ≤ dist x₁ x₂ + dist y₁ y₂ + dist x₂ y₂ := by
  rw [add_right_comm, dist_comm y₁]
  apply dist_triangle4
/-
**dist_triangle8** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_triangle8 (a b c d e f g h : α) : dist a h <= dist a b + dist b c + d
ist c d + dist d e + dist e f + dist f g + dist g h
参数：a b c d e f g h : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `dist_triangle4`：dist_triangle4 (x y z w : α) : dist x w <= dist x y + di
st y z + dist z w
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem dist_triangle8 (a b c d e f g h : α) : dist a h ≤ dist a b + dist b c + dist c d
    + dist d e + dist e f + dist f g + dist g h := by
  apply le_trans (dist_triangle4 a f g h)
  gcongr
  apply le_trans (dist_triangle4 a d e f)
  gcongr
  exact dist_triangle4 a b c d
/-
**swap_dist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：swap_dist : Function.swap (@dist α _) = dist
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
-/
theorem swap_dist : Function.swap (@dist α _) = dist := by funext x y; exact dist_comm _ _
/-
**abs_dist_sub_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：abs_dist_sub_le (x y z : α) : |dist x z - dist y z| <= dist x y
参数：x y z : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_sub_le_iff`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : Linea
rOrder G] [IsOrderedAddMonoid G] {a b c : G},   |a - b| ≤ c ↔ a - b ≤ c ∧ b - a 
≤ c
· 使用定理 `sub_le_iff_le_add`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [A
ddRightMono α] {a b c : α}, a - c ≤ b ↔ a ≤ b + c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `dist_triangle`：dist_triangle (x y z : α) : dist x z <= dist x y + dist y
 z
· 使用定理 `dist_triangle_left`：dist_triangle_left (x y z : α) : dist x y <= dist z 
x + dist z y
-/
theorem abs_dist_sub_le (x y z : α) : |dist x z - dist y z| ≤ dist x y :=
  abs_sub_le_iff.2
    ⟨sub_le_iff_le_add.2 (dist_triangle _ _ _), sub_le_iff_le_add.2 (dist_triangle_left _ _ _)⟩

@[simp, bound]
/-
**dist_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_nonneg {x y : α} : 0 <= dist x y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Topology.MetricSpace.Pseudo.Defs.0.dist_nonneg'`：∀ {α :
 Sort u_3} {x y : α} (dist : α → α → ℝ),   (∀ (x : α), dist x x = 0) →     (∀ (x
 y : α), dist x y = dist y x) → (∀ (x y z : α), dist x…
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `dist_triangle`：dist_triangle (x y z : α) : dist x z <= dist x y + dist y
 z
-/
theorem dist_nonneg {x y : α} : 0 ≤ dist x y :=
  dist_nonneg' dist dist_self dist_comm dist_triangle

namespace Mathlib.Meta.Positivity

open Lean Meta Qq Function

/-- Extension for the `positivity` tactic: distances are nonnegative. -/
@[positivity Dist.dist _ _]
meta def evalDist : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@Dist.dist $β $inst $a $b) =>
    let _inst ← synthInstanceQ q(PseudoMetricSpace $β)
    assertInstancesCommute
    pure (.nonnegative q(dist_nonneg))
  | _, _, _ => throwError "not dist"

end Mathlib.Meta.Positivity

/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example {x y : α} : 0 ≤ dist x y := by positivity
/-
**abs_dist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} [inst : PseudoMetricSpace α] {a b : α}, |dist a b| = dist a
 b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
-/
@[simp] theorem abs_dist {a b : α} : |dist a b| = dist a b := abs_of_nonneg dist_nonneg

/-- A version of `Dist` that takes value in `ℝ≥0`. -/
/-
**NNDist** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_3 → Type u_3
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `Dist` that takes value in `ℝ≥0`.
-/
class NNDist (α : Type*) where
  /-- Nonnegative distance between two points -/
  nndist : α → α → ℝ≥0

export NNDist (nndist)

-- see Note [lower instance priority]
/-- Distance as a nonnegative real number. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Distance as a nonnegative real number.
-/
instance (priority := 100) PseudoMetricSpace.toNNDist : NNDist α :=
  ⟨fun a b => ⟨dist a b, dist_nonneg⟩⟩

/-- Express `dist` in terms of `nndist` -/
/-
**dist_nndist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_nndist (x y : α) : dist x y = nndist x y
参数：x y : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Express `dist` in terms of `nndist`
-/
theorem dist_nndist (x y : α) : dist x y = nndist x y := rfl

@[simp, norm_cast]
/-
**coe_nndist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coe_nndist (x y : α) : ↑(nndist x y) = dist x y
参数：x y : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_nndist (x y : α) : ↑(nndist x y) = dist x y := rfl

/-- Express `edist` in terms of `nndist` -/
/-
**edist_nndist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_nndist (x y : α) : edist x y = nndist x y
参数：x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `edist_dist`：edist_dist (x y : α) : edist x y = ENNReal.ofReal (dist x y)
· 使用定理 `dist_nndist`：dist_nndist (x y : α) : dist x y = nndist x y
· 使用定理 `ENNReal.ofReal_coe_nnreal`：∀ {p : NNReal}, ENNReal.ofReal ↑p = ↑p

--- 原说明 ---
Express `edist` in terms of `nndist`
-/
theorem edist_nndist (x y : α) : edist x y = nndist x y := by
  rw [edist_dist, dist_nndist, ENNReal.ofReal_coe_nnreal]

/-- Express `nndist` in terms of `edist` -/
/-
**nndist_edist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nndist_edist (x y : α) : nndist x y = (edist x y).toNNReal
参数：x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `edist_nndist`：edist_nndist (x y : α) : edist x y = nndist x y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Express `nndist` in terms of `edist`
-/
theorem nndist_edist (x y : α) : nndist x y = (edist x y).toNNReal := by
  simp [edist_nndist]

@[simp, norm_cast]
/-
**coe_nnreal_ennreal_nndist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coe_nnreal_ennreal_nndist (x y : α) : ↑(nndist x y) = edist x y
参数：x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `edist_nndist`：edist_nndist (x y : α) : edist x y = nndist x y
-/
theorem coe_nnreal_ennreal_nndist (x y : α) : ↑(nndist x y) = edist x y :=
  (edist_nndist x y).symm

@[simp, norm_cast]
/-
**edist_lt_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_lt_coe {x y : α} {c : Real>=0} : edist x y < c ↔ nndist x y < c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `edist_nndist`：edist_nndist (x y : α) : edist x y = nndist x y
· 使用定理 `ENNReal.coe_lt_coe`：∀ {r q : NNReal}, ↑r < ↑q ↔ r < q
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem edist_lt_coe {x y : α} {c : ℝ≥0} : edist x y < c ↔ nndist x y < c := by
  rw [edist_nndist, ENNReal.coe_lt_coe]

@[simp, norm_cast]
/-
**edist_le_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_le_coe {x y : α} {c : Real>=0} : edist x y <= c ↔ nndist x y <= c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `edist_nndist`：edist_nndist (x y : α) : edist x y = nndist x y
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem edist_le_coe {x y : α} {c : ℝ≥0} : edist x y ≤ c ↔ nndist x y ≤ c := by
  rw [edist_nndist, ENNReal.coe_le_coe]

/-- In a pseudometric space, the extended distance is always finite -/
/-
**edist_lt_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_lt_top {α : Type*} [PseudoMetricSpace α] (x y : α) : edist x y < ⊤
参数：x y : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.ofReal_lt_top`：∀ {r : ℝ}, ENNReal.ofReal r < ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `edist_dist`：edist_dist (x y : α) : edist x y = ENNReal.ofReal (dist x y)

--- 原说明 ---
In a pseudometric space, the extended distance is always finite
-/
theorem edist_lt_top {α : Type*} [PseudoMetricSpace α] (x y : α) : edist x y < ⊤ :=
  (edist_dist x y).symm ▸ ENNReal.ofReal_lt_top

/-- In a pseudometric space, the extended distance is always finite -/
@[aesop (rule_sets := [finiteness]) safe apply, simp]
/-
**edist_ne_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_ne_top (x y : α) : edist x y != ⊤
参数：x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `edist_lt_top`：edist_lt_top {α : Type*} [PseudoMetricSpace α] (x y : α) :
 edist x y < ⊤

--- 原说明 ---
In a pseudometric space, the extended distance is always finite
-/
theorem edist_ne_top (x y : α) : edist x y ≠ ⊤ :=
  (edist_lt_top x y).ne

/-- `nndist x x` vanishes -/
/-
**nndist_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} [inst : PseudoMetricSpace α] (a : α), nndist a a = 0
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NNReal.coe_eq_zero`：∀ {r : NNReal}, ↑r = 0 ↔ r = 0
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0

--- 原说明 ---
`nndist x x` vanishes
-/
@[simp] theorem nndist_self (a : α) : nndist a a = 0 := NNReal.coe_eq_zero.1 (dist_self a)

@[simp, norm_cast]
/-
**dist_lt_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_lt_coe {x y : α} {c : Real>=0} : dist x y < c ↔ nndist x y < c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
`nndist x x` vanishes
-/
theorem dist_lt_coe {x y : α} {c : ℝ≥0} : dist x y < c ↔ nndist x y < c :=
  Iff.rfl

@[simp, norm_cast]
/-
**dist_le_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_le_coe {x y : α} {c : Real>=0} : dist x y <= c ↔ nndist x y <= c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem dist_le_coe {x y : α} {c : ℝ≥0} : dist x y ≤ c ↔ nndist x y ≤ c :=
  Iff.rfl

@[simp]
/-
**edist_lt_ofReal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_lt_ofReal {x y : α} {r : Real} : edist x y < ENNReal.ofReal r ↔ dist
 x y < r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `edist_dist`：edist_dist (x y : α) : edist x y = ENNReal.ofReal (dist x y)
· 使用定理 `ENNReal.ofReal_lt_ofReal_iff_of_nonneg`：ofReal_lt_ofReal_iff_of_nonneg {
p q : Real} (hp : 0 <= p) : ENNReal.ofReal p < ENNReal.ofReal q ↔ p < q
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem edist_lt_ofReal {x y : α} {r : ℝ} : edist x y < ENNReal.ofReal r ↔ dist x y < r := by
  rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg]

@[simp]
/-
**edist_le_ofReal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_le_ofReal {x y : α} {r : Real} (hr : 0 <= r) : edist x y <= ENNReal.
ofReal r ↔ dist x y <= r
参数：hr : 0 <= r。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `edist_dist`：edist_dist (x y : α) : edist x y = ENNReal.ofReal (dist x y)
· 使用定理 `ENNReal.ofReal_le_ofReal_iff`：ofReal_le_ofReal_iff {p q : Real} (h : 0 <
= q) : ENNReal.ofReal p <= ENNReal.ofReal q ↔ p <= q
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem edist_le_ofReal {x y : α} {r : ℝ} (hr : 0 ≤ r) :
    edist x y ≤ ENNReal.ofReal r ↔ dist x y ≤ r := by
  rw [edist_dist, ENNReal.ofReal_le_ofReal_iff hr]

/-- Express `nndist` in terms of `dist` -/
/-
**nndist_dist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nndist_dist (x y : α) : nndist x y = Real.toNNReal (dist x y)
参数：x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_nndist`：dist_nndist (x y : α) : dist x y = nndist x y
· 使用定理 `Real.toNNReal_coe`：∀ {r : NNReal}, (↑r).toNNReal = r

--- 原说明 ---
Express `nndist` in terms of `dist`
-/
theorem nndist_dist (x y : α) : nndist x y = Real.toNNReal (dist x y) := by
  rw [dist_nndist, Real.toNNReal_coe]
/-
**nndist_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nndist_comm (x y : α) : nndist x y = nndist y x
参数：x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
-/
theorem nndist_comm (x y : α) : nndist x y = nndist y x := NNReal.eq <| dist_comm x y

/-- Triangle inequality for the nonnegative distance -/
/-
**nndist_triangle** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nndist_triangle (x y z : α) : nndist x z <= nndist x y + nndist y z
参数：x y z : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dist_triangle`：dist_triangle (x y z : α) : dist x z <= dist x y + dist y
 z

--- 原说明 ---
Triangle inequality for the nonnegative distance
-/
theorem nndist_triangle (x y z : α) : nndist x z ≤ nndist x y + nndist y z :=
  dist_triangle _ _ _
/-
**nndist_triangle_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nndist_triangle_left (x y z : α) : nndist x y <= nndist z x + nndist z y
参数：x y z : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dist_triangle_left`：dist_triangle_left (x y z : α) : dist x y <= dist z 
x + dist z y
-/
theorem nndist_triangle_left (x y z : α) : nndist x y ≤ nndist z x + nndist z y :=
  dist_triangle_left _ _ _
/-
**nndist_triangle_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nndist_triangle_right (x y z : α) : nndist x y <= nndist x z + nndist y z
参数：x y z : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dist_triangle_right`：dist_triangle_right (x y z : α) : dist x y <= dist 
x z + dist y z
-/
theorem nndist_triangle_right (x y z : α) : nndist x y ≤ nndist x z + nndist y z :=
  dist_triangle_right _ _ _

/-- Express `dist` in terms of `edist` -/
/-
**dist_edist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_edist (x y : α) : dist x y = (edist x y).toReal
参数：x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `edist_dist`：edist_dist (x y : α) : edist x y = ENNReal.ofReal (dist x y)
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y

--- 原说明 ---
Express `dist` in terms of `edist`
-/
theorem dist_edist (x y : α) : dist x y = (edist x y).toReal := by
  rw [edist_dist, ENNReal.toReal_ofReal dist_nonneg]

namespace Metric

-- instantiate pseudometric space as a topology
variable {x y z : α} {δ ε ε₁ ε₂ : ℝ} {s : Set α}

/-- `ball x ε` is the set of all points `y` with `dist y x < ε` -/
@[wikidata Q838611]
/-
**Metric.ball** 是 Mathlib 中的一个定义，位于命名空间 `Metric`。
形式化陈述：ball (x : α) (ε : Real) : Set α
参数：x : α；ε : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ball x ε` is the set of all points `y` with `dist y x < ε`
-/
def ball (x : α) (ε : ℝ) : Set α :=
  { y | dist y x < ε }

@[simp]
/-
**Metric.mem_ball** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：mem_ball : y in ball x ε ↔ dist y x < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_ball : y ∈ ball x ε ↔ dist y x < ε :=
  Iff.rfl
/-
**Metric.mem_ball'** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：mem_ball' : y in ball x ε ↔ dist x y < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `Metric.mem_ball`：mem_ball : y in ball x ε ↔ dist y x < ε
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_ball' : y ∈ ball x ε ↔ dist x y < ε := by rw [dist_comm, mem_ball]
/-
**Metric.pos_of_mem_ball** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：pos_of_mem_ball (hy : y in ball x ε) : 0 < ε
参数：hy : y in ball x ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
-/
theorem pos_of_mem_ball (hy : y ∈ ball x ε) : 0 < ε :=
  dist_nonneg.trans_lt hy
/-
**Metric.mem_ball_self** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：mem_ball_self (h : 0 < ε) : x in ball x ε
参数：h : 0 < ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.mem_ball`：mem_ball : y in ball x ε ↔ dist y x < ε
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
-/
theorem mem_ball_self (h : 0 < ε) : x ∈ ball x ε := by
  rwa [mem_ball, dist_self]

@[simp]
/-
**Metric.nonempty_ball** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：nonempty_ball : (ball x ε).Nonempty ↔ 0 < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.pos_of_mem_ball`：pos_of_mem_ball (hy : y in ball x ε) : 0 < ε
· 使用定理 `Metric.mem_ball_self`：mem_ball_self (h : 0 < ε) : x in ball x ε
-/
theorem nonempty_ball : (ball x ε).Nonempty ↔ 0 < ε :=
  ⟨fun ⟨_x, hx⟩ => pos_of_mem_ball hx, fun h => ⟨x, mem_ball_self h⟩⟩

@[simp]
/-
**Metric.ball_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：ball_eq_empty : ball x ε = ∅ ↔ ε <= 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.not_nonempty_iff_eq_empty`：not_nonempty_iff_eq_empty : ¬s.Nonempty ↔
 s = ∅
· 使用定理 `Metric.nonempty_ball`：nonempty_ball : (ball x ε).Nonempty ↔ 0 < ε
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ball_eq_empty : ball x ε = ∅ ↔ ε ≤ 0 := by
  rw [← not_nonempty_iff_eq_empty, nonempty_ball, not_lt]

@[simp]
/-
**Metric.ball_zero** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：ball_zero : ball x 0 = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.ball_eq_empty`：ball_eq_empty : ball x ε = ∅ ↔ ε <= 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem ball_zero : ball x 0 = ∅ := by rw [ball_eq_empty]

/-- If a point belongs to an open ball, then there is a strictly smaller radius whose ball also
contains it.

See also `exists_lt_subset_ball`. -/
/-
**Metric.exists_lt_mem_ball_of_mem_ball** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：exists_lt_mem_ball_of_mem_ball (h : x in ball y ε) : exists ε' < ε, x in b
all y ε'
参数：h : x in ball y ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_between'`：∀ {α : Type u_2} [inst : LT α] [DenselyOrdered α] {a₁ a
₂ : α}, a₂ < a₁ → ∃ a < a₁, a₂ < a
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R

--- 原说明 ---
If a point belongs to an open ball, then there is a strictly smaller radius whos
e ball also
contains it.

See also `exists_lt_subset_ball`.
-/
theorem exists_lt_mem_ball_of_mem_ball (h : x ∈ ball y ε) : ∃ ε' < ε, x ∈ ball y ε' := by
  simpa [mem_ball] using exists_between' h
/-
**Metric.ball_eq_ball** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：ball_eq_ball (ε : Real) (x : α) : UniformSpace.ball x { p | dist p.2 p.1 <
 ε } = Metric.ball x ε
参数：ε : Real；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ball_eq_ball (ε : ℝ) (x : α) :
    UniformSpace.ball x { p | dist p.2 p.1 < ε } = Metric.ball x ε :=
  rfl
/-
**Metric.ball_eq_ball'** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：ball_eq_ball' (ε : Real) (x : α) : UniformSpace.ball x { p | dist p.1 p.2 
< ε } = Metric.ball x ε
参数：ε : Real；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ball_eq_ball' (ε : ℝ) (x : α) :
    UniformSpace.ball x { p | dist p.1 p.2 < ε } = Metric.ball x ε := by
  ext
  simp [dist_comm, UniformSpace.ball]

@[simp]
/-
**Metric.iUnion_ball_nat** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：iUnion_ball_nat (x : α) : ⋃ n : Nat, ball x n = univ
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.iUnion_eq_univ_iff`：iUnion_eq_univ_iff {f : ι -> Set α} : ⋃ i, f i =
 univ ↔ forall x, exists i, x in f i
· 使用定理 `exists_nat_gt`：exists_nat_gt (x : R) : exists n : Nat, x < n
-/
theorem iUnion_ball_nat (x : α) : ⋃ n : ℕ, ball x n = univ :=
  iUnion_eq_univ_iff.2 fun y => exists_nat_gt (dist y x)

@[simp]
/-
**Metric.iUnion_ball_nat_succ** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：iUnion_ball_nat_succ (x : α) : ⋃ n : Nat, ball x (n + 1) = univ
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.iUnion_eq_univ_iff`：iUnion_eq_univ_iff {f : ι -> Set α} : ⋃ i, f i =
 univ ↔ forall x, exists i, x in f i
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `exists_nat_gt`：exists_nat_gt (x : R) : exists n : Nat, x < n
-/
theorem iUnion_ball_nat_succ (x : α) : ⋃ n : ℕ, ball x (n + 1) = univ :=
  iUnion_eq_univ_iff.2 fun y => (exists_nat_gt (dist y x)).imp fun _ h => h.trans (lt_add_one _)

/-- `closedBall x ε` is the set of all points `y` with `dist y x ≤ ε` -/
/-
**Metric.closedBall** 是 Mathlib 中的一个定义，位于命名空间 `Metric`。
形式化陈述：closedBall (x : α) (ε : Real)
参数：x : α；ε : Real。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`closedBall x ε` is the set of all points `y` with `dist y x ≤ ε`
-/
def closedBall (x : α) (ε : ℝ) :=
  { y | dist y x ≤ ε }
/-
**Metric.mem_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：∀ {α : Type u} [inst : PseudoMetricSpace α] {x y : α} {ε : ℝ}, y ∈ Metric.
closedBall x ε ↔ dist y x ≤ ε
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem mem_closedBall : y ∈ closedBall x ε ↔ dist y x ≤ ε := Iff.rfl
/-
**Metric.mem_closedBall'** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：mem_closedBall' : y in closedBall x ε ↔ dist x y <= ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `Metric.mem_closedBall`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x y 
: α} {ε : ℝ}, y ∈ Metric.closedBall x ε ↔ dist y x ≤ ε
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_closedBall' : y ∈ closedBall x ε ↔ dist x y ≤ ε := by rw [dist_comm, mem_closedBall]
/-
**Metric.nonneg_of_mem_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：nonneg_of_mem_closedBall (hy : y in closedBall x ε) : 0 <= ε
参数：hy : y in closedBall x ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
-/
theorem nonneg_of_mem_closedBall (hy : y ∈ closedBall x ε) : 0 ≤ ε :=
  dist_nonneg.trans hy

/-- `sphere x ε` is the set of all points `y` with `dist y x = ε` -/
/-
**Metric.sphere** 是 Mathlib 中的一个定义，位于命名空间 `Metric`。
形式化陈述：sphere (x : α) (ε : Real)
参数：x : α；ε : Real。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`sphere x ε` is the set of all points `y` with `dist y x = ε`
-/
def sphere (x : α) (ε : ℝ) := { y | dist y x = ε }
/-
**Metric.mem_sphere** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：∀ {α : Type u} [inst : PseudoMetricSpace α] {x y : α} {ε : ℝ}, y ∈ Metric.
sphere x ε ↔ dist y x = ε
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem mem_sphere : y ∈ sphere x ε ↔ dist y x = ε := Iff.rfl
/-
**Metric.mem_sphere'** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：mem_sphere' : y in sphere x ε ↔ dist x y = ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `Metric.mem_sphere`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x y : α}
 {ε : ℝ}, y ∈ Metric.sphere x ε ↔ dist y x = ε
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_sphere' : y ∈ sphere x ε ↔ dist x y = ε := by rw [dist_comm, mem_sphere]
/-
**Metric.ne_of_mem_sphere** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：ne_of_mem_sphere (h : y in sphere x ε) (hε : ε != 0) : y != x
参数：h : y in sphere x ε；hε : ε != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem ne_of_mem_sphere (h : y ∈ sphere x ε) (hε : ε ≠ 0) : y ≠ x :=
  ne_of_mem_of_not_mem h <| by simpa using hε.symm
/-
**Metric.nonneg_of_mem_sphere** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：nonneg_of_mem_sphere (hy : y in sphere x ε) : 0 <= ε
参数：hy : y in sphere x ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
-/
theorem nonneg_of_mem_sphere (hy : y ∈ sphere x ε) : 0 ≤ ε :=
  dist_nonneg.trans_eq hy

@[simp]
/-
**Metric.sphere_eq_empty_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：sphere_eq_empty_of_neg (hε : ε < 0) : sphere x ε = ∅
参数：hε : ε < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.eq_empty_iff_forall_notMem`：eq_empty_iff_forall_notMem {s : Set α} :
 s = ∅ ↔ forall x, x ∉ s
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Metric.nonneg_of_mem_sphere`：nonneg_of_mem_sphere (hy : y in sphere x ε)
 : 0 <= ε
-/
theorem sphere_eq_empty_of_neg (hε : ε < 0) : sphere x ε = ∅ :=
  Set.eq_empty_iff_forall_notMem.mpr fun _y hy => (nonneg_of_mem_sphere hy).not_gt hε
/-
**Metric.sphere_eq_empty_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：sphere_eq_empty_of_subsingleton [Subsingleton α] (hε : ε != 0) : sphere x 
ε = ∅
参数：hε : ε != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.eq_empty_iff_forall_notMem`：eq_empty_iff_forall_notMem {s : Set α} :
 s = ∅ ↔ forall x, x ∉ s
· 使用定理 `Metric.ne_of_mem_sphere`：ne_of_mem_sphere (h : y in sphere x ε) (hε : ε 
!= 0) : y != x
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem sphere_eq_empty_of_subsingleton [Subsingleton α] (hε : ε ≠ 0) : sphere x ε = ∅ :=
  Set.eq_empty_iff_forall_notMem.mpr fun _ h => ne_of_mem_sphere h hε (Subsingleton.elim _ _)
/-
**Metric.sphere_isEmpty_of_subsingleton** 是 Mathlib 中的一个实例，位于命名空间 `Metric`。
形式化陈述：sphere_isEmpty_of_subsingleton [Subsingleton α] [NeZero ε] : IsEmpty (sphe
re x ε)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.sphere_eq_empty_of_subsingleton`：sphere_eq_empty_of_subsingleton 
[Subsingleton α] (hε : ε != 0) : sphere x ε = ∅
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `Set.instIsEmptyElemEmptyCollection`：∀ (α : Type u), IsEmpty ↑∅
-/
instance sphere_isEmpty_of_subsingleton [Subsingleton α] [NeZero ε] : IsEmpty (sphere x ε) := by
  rw [sphere_eq_empty_of_subsingleton (NeZero.ne ε)]; infer_instance
/-
**Metric.closedBall_eq_singleton_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Metr
ic`。
形式化陈述：closedBall_eq_singleton_of_subsingleton [Subsingleton α] (h : 0 <= ε) : cl
osedBall x ε = {x}
参数：h : 0 <= ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subsingleton.allEq`：∀ {α : Sort u} [self : Subsingleton α] (a b : α), a 
= b
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
-/
theorem closedBall_eq_singleton_of_subsingleton [Subsingleton α] (h : 0 ≤ ε) :
    closedBall x ε = {x} := by
  ext x'
  simpa [Subsingleton.allEq x x']
/-
**Metric.ball_eq_singleton_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：ball_eq_singleton_of_subsingleton [Subsingleton α] (h : 0 < ε) : ball x ε 
= {x}
参数：h : 0 < ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subsingleton.allEq`：∀ {α : Sort u} [self : Subsingleton α] (a b : α), a 
= b
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
-/
theorem ball_eq_singleton_of_subsingleton [Subsingleton α] (h : 0 < ε) : ball x ε = {x} := by
  ext x'
  simpa [Subsingleton.allEq x x']
/-
**Metric.mem_closedBall_self** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：mem_closedBall_self (h : 0 <= ε) : x in closedBall x ε
参数：h : 0 <= ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.mem_closedBall`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x y 
: α} {ε : ℝ}, y ∈ Metric.closedBall x ε ↔ dist y x ≤ ε
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
-/
theorem mem_closedBall_self (h : 0 ≤ ε) : x ∈ closedBall x ε := by
  rwa [mem_closedBall, dist_self]

@[simp]
/-
**Metric.nonempty_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：nonempty_closedBall : (closedBall x ε).Nonempty ↔ 0 <= ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `Metric.mem_closedBall_self`：mem_closedBall_self (h : 0 <= ε) : x in clos
edBall x ε
-/
theorem nonempty_closedBall : (closedBall x ε).Nonempty ↔ 0 ≤ ε :=
  ⟨fun ⟨_x, hx⟩ => dist_nonneg.trans hx, fun h => ⟨x, mem_closedBall_self h⟩⟩

@[simp]
/-
**Metric.closedBall_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：closedBall_eq_empty : closedBall x ε = ∅ ↔ ε < 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.not_nonempty_iff_eq_empty`：not_nonempty_iff_eq_empty : ¬s.Nonempty ↔
 s = ∅
· 使用定理 `Metric.nonempty_closedBall`：nonempty_closedBall : (closedBall x ε).Nonem
pty ↔ 0 <= ε
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem closedBall_eq_empty : closedBall x ε = ∅ ↔ ε < 0 := by
  rw [← not_nonempty_iff_eq_empty, nonempty_closedBall, not_le]

@[simp] alias ⟨_, closedBall_of_neg⟩ := closedBall_eq_empty

/-- Closed balls and spheres coincide when the radius is non-positive -/
/-
**Metric.closedBall_eq_sphere_of_nonpos** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：closedBall_eq_sphere_of_nonpos (hε : ε <= 0) : closedBall x ε = sphere x ε
参数：hε : ε <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `LE.le.ge_iff_eq'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b 
≤ a → (a ≤ b ↔ a = b)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y

--- 原说明 ---
Closed balls and spheres coincide when the radius is non-positive
-/
theorem closedBall_eq_sphere_of_nonpos (hε : ε ≤ 0) : closedBall x ε = sphere x ε :=
  Set.ext fun _ => (hε.trans dist_nonneg).ge_iff_eq'
/-
**Metric.ball_subset_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：ball_subset_closedBall : ball x ε subseteq closedBall x ε
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.mem_closedBall`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x y 
: α} {ε : ℝ}, y ∈ Metric.closedBall x ε ↔ dist y x ≤ ε
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem ball_subset_closedBall : ball x ε ⊆ closedBall x ε := fun _y hy =>
  mem_closedBall.2 (le_of_lt hy)
/-
**Metric.sphere_subset_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：sphere_subset_closedBall : sphere x ε subseteq closedBall x ε
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
theorem sphere_subset_closedBall : sphere x ε ⊆ closedBall x ε := fun _ => le_of_eq
/-
**Metric.sphere_subset_ball** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：sphere_subset_ball {r R : Real} (h : r < R) : sphere x r subseteq ball x R
参数：h : r < R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans_lt`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a = b → b < c →
 a < c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.mem_sphere`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x y : α}
 {ε : ℝ}, y ∈ Metric.sphere x ε ↔ dist y x = ε
-/
lemma sphere_subset_ball {r R : ℝ} (h : r < R) : sphere x r ⊆ ball x R := fun _x hx ↦
  (mem_sphere.1 hx).trans_lt h
/-
**Metric.closedBall_disjoint_ball** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：closedBall_disjoint_ball (h : δ + ε <= dist x y) : Disjoint (closedBall x 
δ) (ball y ε)
参数：h : δ + ε <= dist x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `dist_triangle_left`：dist_triangle_left (x y z : α) : dist x y <= dist z 
x + dist z y
· 使用定理 `add_lt_add_of_le_of_lt`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preord
er α] [AddLeftStrictMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c < d → a 
+ c < b + d
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem closedBall_disjoint_ball (h : δ + ε ≤ dist x y) : Disjoint (closedBall x δ) (ball y ε) :=
  Set.disjoint_left.mpr fun _a ha1 ha2 =>
    (h.trans <| dist_triangle_left _ _ _).not_gt <| add_lt_add_of_le_of_lt ha1 ha2
/-
**Metric.ball_disjoint_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：ball_disjoint_closedBall (h : δ + ε <= dist x y) : Disjoint (ball x δ) (cl
osedBall y ε)
参数：h : δ + ε <= dist x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `Metric.closedBall_disjoint_ball`：closedBall_disjoint_ball (h : δ + ε <= 
dist x y) : Disjoint (closedBall x δ) (ball y ε)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
-/
theorem ball_disjoint_closedBall (h : δ + ε ≤ dist x y) : Disjoint (ball x δ) (closedBall y ε) :=
  (closedBall_disjoint_ball <| by rwa [add_comm, dist_comm]).symm
/-
**Metric.ball_disjoint_ball** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：ball_disjoint_ball (h : δ + ε <= dist x y) : Disjoint (ball x δ) (ball y ε
)
参数：h : δ + ε <= dist x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.mono_left`：Disjoint.mono_left (h : a <= b) : Disjoint b c -> Di
sjoint a c
· 使用定理 `Metric.ball_subset_closedBall`：ball_subset_closedBall : ball x ε subsete
q closedBall x ε
· 使用定理 `Metric.closedBall_disjoint_ball`：closedBall_disjoint_ball (h : δ + ε <= 
dist x y) : Disjoint (closedBall x δ) (ball y ε)
-/
theorem ball_disjoint_ball (h : δ + ε ≤ dist x y) : Disjoint (ball x δ) (ball y ε) :=
  (closedBall_disjoint_ball h).mono_left ball_subset_closedBall
/-
**Metric.closedBall_disjoint_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：closedBall_disjoint_closedBall (h : δ + ε < dist x y) : Disjoint (closedBa
ll x δ) (closedBall y ε)
参数：h : δ + ε < dist x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `dist_triangle_left`：dist_triangle_left (x y z : α) : dist x y <= dist z 
x + dist z y
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem closedBall_disjoint_closedBall (h : δ + ε < dist x y) :
    Disjoint (closedBall x δ) (closedBall y ε) :=
  Set.disjoint_left.mpr fun _a ha1 ha2 =>
    h.not_ge <| (dist_triangle_left _ _ _).trans <| add_le_add ha1 ha2
/-
**Metric.sphere_disjoint_ball** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：sphere_disjoint_ball : Disjoint (sphere x ε) (ball x ε)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
-/
theorem sphere_disjoint_ball : Disjoint (sphere x ε) (ball x ε) :=
  Set.disjoint_left.mpr fun _y hy₁ hy₂ => absurd hy₁ <| ne_of_lt hy₂

@[simp]
/-
**Metric.ball_union_sphere** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：ball_union_sphere : ball x ε union sphere x ε = closedBall x ε
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `le_iff_lt_or_eq`：le_iff_lt_or_eq : a <= b ↔ a < b ∨ a = b
-/
theorem ball_union_sphere : ball x ε ∪ sphere x ε = closedBall x ε :=
  Set.ext fun _y => (@le_iff_lt_or_eq ℝ _ _ _).symm

@[simp]
/-
**Metric.sphere_union_ball** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：sphere_union_ball : sphere x ε union ball x ε = closedBall x ε
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `Metric.ball_union_sphere`：ball_union_sphere : ball x ε union sphere x ε 
= closedBall x ε
-/
theorem sphere_union_ball : sphere x ε ∪ ball x ε = closedBall x ε := by
  rw [union_comm, ball_union_sphere]

@[simp]
/-
**Metric.closedBall_sdiff_sphere** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：closedBall_sdiff_sphere : closedBall x ε \ sphere x ε = ball x ε
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Metric.ball_union_sphere`：ball_union_sphere : ball x ε union sphere x ε 
= closedBall x ε
· 使用定理 `Set.union_sdiff_cancel_right`：union_sdiff_cancel_right {s t : Set α} (h 
: s inter t subseteq ∅) : (s union t) \ t = s
· 使用定理 `Disjoint.le_bot`：Disjoint.le_bot : Disjoint a b -> a ⊓ b <= ⊥
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `Metric.sphere_disjoint_ball`：sphere_disjoint_ball : Disjoint (sphere x ε
) (ball x ε)
-/
theorem closedBall_sdiff_sphere : closedBall x ε \ sphere x ε = ball x ε := by
  rw [← ball_union_sphere, Set.union_sdiff_cancel_right sphere_disjoint_ball.symm.le_bot]

@[deprecated (since := "2026-06-03")] alias closedBall_diff_sphere := closedBall_sdiff_sphere

@[simp]
/-
**Metric.closedBall_sdiff_ball** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：closedBall_sdiff_ball : closedBall x ε \ ball x ε = sphere x ε
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Metric.ball_union_sphere`：ball_union_sphere : ball x ε union sphere x ε 
= closedBall x ε
· 使用定理 `Set.union_sdiff_cancel_left`：union_sdiff_cancel_left {s t : Set α} (h : 
s inter t subseteq ∅) : (s union t) \ s = t
· 使用定理 `Disjoint.le_bot`：Disjoint.le_bot : Disjoint a b -> a ⊓ b <= ⊥
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `Metric.sphere_disjoint_ball`：sphere_disjoint_ball : Disjoint (sphere x ε
) (ball x ε)
-/
theorem closedBall_sdiff_ball : closedBall x ε \ ball x ε = sphere x ε := by
  rw [← ball_union_sphere, Set.union_sdiff_cancel_left sphere_disjoint_ball.symm.le_bot]

@[deprecated (since := "2026-06-03")] alias closedBall_diff_ball := closedBall_sdiff_ball
/-
**Metric.mem_ball_comm** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：mem_ball_comm : x in ball y ε ↔ y in ball x ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.mem_ball'`：mem_ball' : y in ball x ε ↔ dist x y < ε
· 使用定理 `Metric.mem_ball`：mem_ball : y in ball x ε ↔ dist y x < ε
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_ball_comm : x ∈ ball y ε ↔ y ∈ ball x ε := by rw [mem_ball', mem_ball]
/-
**Metric.mem_closedBall_comm** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：mem_closedBall_comm : x in closedBall y ε ↔ y in closedBall x ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.mem_closedBall'`：mem_closedBall' : y in closedBall x ε ↔ dist x y
 <= ε
· 使用定理 `Metric.mem_closedBall`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x y 
: α} {ε : ℝ}, y ∈ Metric.closedBall x ε ↔ dist y x ≤ ε
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_closedBall_comm : x ∈ closedBall y ε ↔ y ∈ closedBall x ε := by
  rw [mem_closedBall', mem_closedBall]
/-
**Metric.mem_sphere_comm** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：mem_sphere_comm : x in sphere y ε ↔ y in sphere x ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.mem_sphere'`：mem_sphere' : y in sphere x ε ↔ dist x y = ε
· 使用定理 `Metric.mem_sphere`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x y : α}
 {ε : ℝ}, y ∈ Metric.sphere x ε ↔ dist y x = ε
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_sphere_comm : x ∈ sphere y ε ↔ y ∈ sphere x ε := by rw [mem_sphere', mem_sphere]

@[gcongr]
/-
**Metric.ball_subset_ball** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：ball_subset_ball (h : ε₁ <= ε₂) : ball x ε₁ subseteq ball x ε₂
参数：h : ε₁ <= ε₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.mem_ball`：mem_ball : y in ball x ε ↔ dist y x < ε
-/
theorem ball_subset_ball (h : ε₁ ≤ ε₂) : ball x ε₁ ⊆ ball x ε₂ := fun _y yx =>
  lt_of_lt_of_le (mem_ball.1 yx) h
/-
**Metric.closedBall_eq_bInter_ball** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：closedBall_eq_bInter_ball : closedBall x ε = ⋂ δ > ε, ball x δ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.mem_closedBall`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x y 
: α} {ε : ℝ}, y ∈ Metric.closedBall x ε ↔ dist y x ≤ ε
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `forall_gt_iff_le`：∀ {α : Type u_2} [inst : LinearOrder α] {a b : α}, (∀ 
⦃c : α⦄, a < c → b < c) ↔ b ≤ a
· 使用定理 `Set.mem_iInter₂`：mem_iInter₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋂ (i) (j), s i j) ↔ forall i j, x in s i j
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem closedBall_eq_bInter_ball : closedBall x ε = ⋂ δ > ε, ball x δ := by
  ext y; rw [mem_closedBall, ← forall_gt_iff_le, mem_iInter₂]; rfl
/-
**Metric.ball_subset_ball'** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：ball_subset_ball' (h : ε₁ + dist x y <= ε₂) : ball x ε₁ subseteq ball y ε₂
参数：h : ε₁ + dist x y <= ε₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dist_triangle`：dist_triangle (x y z : α) : dist x z <= dist x y + dist y
 z
· 使用定理 `add_lt_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [i : Ad
dRightStrictMono α] {b c : α}, b < c → ∀ (a : α), b + a < c + a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem ball_subset_ball' (h : ε₁ + dist x y ≤ ε₂) : ball x ε₁ ⊆ ball y ε₂ := fun z hz =>
  calc
    dist z y ≤ dist z x + dist x y := dist_triangle _ _ _
    _ < ε₁ + dist x y := by gcongr; exact hz
    _ ≤ ε₂ := h

@[gcongr]
/-
**Metric.closedBall_subset_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：closedBall_subset_closedBall (h : ε₁ <= ε₂) : closedBall x ε₁ subseteq clo
sedBall x ε₂
参数：h : ε₁ <= ε₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
-/
theorem closedBall_subset_closedBall (h : ε₁ ≤ ε₂) : closedBall x ε₁ ⊆ closedBall x ε₂ :=
  fun _y (yx : _ ≤ ε₁) => le_trans yx h
/-
**Metric.closedBall_subset_closedBall'** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：closedBall_subset_closedBall' (h : ε₁ + dist x y <= ε₂) : closedBall x ε₁ 
subseteq closedBall y ε₂
参数：h : ε₁ + dist x y <= ε₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dist_triangle`：dist_triangle (x y z : α) : dist x z <= dist x y + dist y
 z
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem closedBall_subset_closedBall' (h : ε₁ + dist x y ≤ ε₂) :
    closedBall x ε₁ ⊆ closedBall y ε₂ := fun z hz =>
  calc
    dist z y ≤ dist z x + dist x y := dist_triangle _ _ _
    _ ≤ ε₁ + dist x y := by gcongr; exact hz
    _ ≤ ε₂ := h
/-
**Metric.closedBall_subset_ball** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：closedBall_subset_ball (h : ε₁ < ε₂) : closedBall x ε₁ subseteq ball x ε₂
参数：h : ε₁ < ε₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
-/
theorem closedBall_subset_ball (h : ε₁ < ε₂) : closedBall x ε₁ ⊆ ball x ε₂ :=
  fun y (yh : dist y x ≤ ε₁) => lt_of_le_of_lt yh h
/-
**Metric.closedBall_subset_ball'** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：closedBall_subset_ball' (h : ε₁ + dist x y < ε₂) : closedBall x ε₁ subsete
q ball y ε₂
参数：h : ε₁ + dist x y < ε₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dist_triangle`：dist_triangle (x y z : α) : dist x z <= dist x y + dist y
 z
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem closedBall_subset_ball' (h : ε₁ + dist x y < ε₂) :
    closedBall x ε₁ ⊆ ball y ε₂ := fun z hz =>
  calc
    dist z y ≤ dist z x + dist x y := dist_triangle _ _ _
    _ ≤ ε₁ + dist x y := by gcongr; exact hz
    _ < ε₂ := h
/-
**Metric.dist_le_add_of_nonempty_closedBall_inter_closedBall** 是 Mathlib 中的一个定理，
位于命名空间 `Metric`。
形式化陈述：dist_le_add_of_nonempty_closedBall_inter_closedBall (h : (closedBall x ε₁ 
inter closedBall y ε₂).Nonempty) : dist x y <= ε₁ + ε₂
参数：h : (closedBall x ε₁ inter closedBall y ε₂).Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dist_triangle_left`：dist_triangle_left (x y z : α) : dist x y <= dist z 
x + dist z y
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem dist_le_add_of_nonempty_closedBall_inter_closedBall
    (h : (closedBall x ε₁ ∩ closedBall y ε₂).Nonempty) : dist x y ≤ ε₁ + ε₂ :=
  let ⟨z, hz⟩ := h
  calc
    dist x y ≤ dist z x + dist z y := dist_triangle_left _ _ _
    _ ≤ ε₁ + ε₂ := add_le_add hz.1 hz.2
/-
**Metric.dist_lt_add_of_nonempty_closedBall_inter_ball** 是 Mathlib 中的一个定理，位于命名空间
 `Metric`。
形式化陈述：dist_lt_add_of_nonempty_closedBall_inter_ball (h : (closedBall x ε₁ inter 
ball y ε₂).Nonempty) : dist x y < ε₁ + ε₂
参数：h : (closedBall x ε₁ inter ball y ε₂).Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dist_triangle_left`：dist_triangle_left (x y z : α) : dist x y <= dist z 
x + dist z y
· 使用定理 `add_lt_add_of_le_of_lt`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preord
er α] [AddLeftStrictMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c < d → a 
+ c < b + d
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem dist_lt_add_of_nonempty_closedBall_inter_ball (h : (closedBall x ε₁ ∩ ball y ε₂).Nonempty) :
    dist x y < ε₁ + ε₂ :=
  let ⟨z, hz⟩ := h
  calc
    dist x y ≤ dist z x + dist z y := dist_triangle_left _ _ _
    _ < ε₁ + ε₂ := add_lt_add_of_le_of_lt hz.1 hz.2
/-
**Metric.dist_lt_add_of_nonempty_ball_inter_closedBall** 是 Mathlib 中的一个定理，位于命名空间
 `Metric`。
形式化陈述：dist_lt_add_of_nonempty_ball_inter_closedBall (h : (ball x ε₁ inter closed
Ball y ε₂).Nonempty) : dist x y < ε₁ + ε₂
参数：h : (ball x ε₁ inter closedBall y ε₂).Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `Metric.dist_lt_add_of_nonempty_closedBall_inter_ball`：dist_lt_add_of_non
empty_closedBall_inter_ball (h : (closedBall x ε₁ inter ball y ε₂).Nonempty) : d
ist x y < ε₁ + ε₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
-/
theorem dist_lt_add_of_nonempty_ball_inter_closedBall (h : (ball x ε₁ ∩ closedBall y ε₂).Nonempty) :
    dist x y < ε₁ + ε₂ := by
  rw [inter_comm] at h
  rw [add_comm, dist_comm]
  exact dist_lt_add_of_nonempty_closedBall_inter_ball h
/-
**Metric.dist_lt_add_of_nonempty_ball_inter_ball** 是 Mathlib 中的一个定理，位于命名空间 `Metr
ic`。
形式化陈述：dist_lt_add_of_nonempty_ball_inter_ball (h : (ball x ε₁ inter ball y ε₂).N
onempty) : dist x y < ε₁ + ε₂
参数：h : (ball x ε₁ inter ball y ε₂).Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.dist_lt_add_of_nonempty_closedBall_inter_ball`：dist_lt_add_of_non
empty_closedBall_inter_ball (h : (closedBall x ε₁ inter ball y ε₂).Nonempty) : d
ist x y < ε₁ + ε₂
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
· 使用定理 `Set.inter_subset_inter`：inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq t₁) (h₂ : s₂ subseteq t₂) : s₁ inter s₂ subseteq t₁ inter t₂
· 使用定理 `Metric.ball_subset_closedBall`：ball_subset_closedBall : ball x ε subsete
q closedBall x ε
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem dist_lt_add_of_nonempty_ball_inter_ball (h : (ball x ε₁ ∩ ball y ε₂).Nonempty) :
    dist x y < ε₁ + ε₂ :=
  dist_lt_add_of_nonempty_closedBall_inter_ball <|
    h.mono (inter_subset_inter ball_subset_closedBall Subset.rfl)

@[simp]
/-
**Metric.iUnion_closedBall_nat** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：iUnion_closedBall_nat (x : α) : ⋃ n : Nat, closedBall x n = univ
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.iUnion_eq_univ_iff`：iUnion_eq_univ_iff {f : ι -> Set α} : ⋃ i, f i =
 univ ↔ forall x, exists i, x in f i
· 使用定理 `exists_nat_ge`：exists_nat_ge (x : R) : exists n : Nat, x <= n
-/
theorem iUnion_closedBall_nat (x : α) : ⋃ n : ℕ, closedBall x n = univ :=
  iUnion_eq_univ_iff.2 fun y => exists_nat_ge (dist y x)
/-
**Metric.iUnion_inter_closedBall_nat** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：iUnion_inter_closedBall_nat (s : Set α) (x : α) : ⋃ n : Nat, s inter close
dBall x n = s
参数：s : Set α；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_iUnion`：inter_iUnion (s : Set β) (t : ι -> Set β) : (s inter ⋃
 i, t i) = ⋃ i, s inter t i
· 使用定理 `Metric.iUnion_closedBall_nat`：iUnion_closedBall_nat (x : α) : ⋃ n : Nat,
 closedBall x n = univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
-/
theorem iUnion_inter_closedBall_nat (s : Set α) (x : α) : ⋃ n : ℕ, s ∩ closedBall x n = s := by
  rw [← inter_iUnion, iUnion_closedBall_nat, inter_univ]
/-
**Metric.ball_subset** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：ball_subset (h : dist x y <= ε₂ - ε₁) : ball x ε₁ subseteq ball y ε₂
参数：h : dist x y <= ε₂ - ε₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `dist_triangle`：dist_triangle (x y z : α) : dist x z <= dist x y + dist y
 z
· 使用定理 `add_lt_add_of_lt_of_le`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preord
er α] [AddLeftMono α] [AddRightStrictMono α] {a b c d : α},   a < b → c ≤ d → a 
+ c < b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem ball_subset (h : dist x y ≤ ε₂ - ε₁) : ball x ε₁ ⊆ ball y ε₂ := fun z zx => by
  rw [← add_sub_cancel ε₁ ε₂]
  exact lt_of_le_of_lt (dist_triangle z x y) (add_lt_add_of_lt_of_le zx h)
/-
**Metric.ball_half_subset** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：ball_half_subset (y) (h : y in ball x (ε / 2)) : ball y (ε / 2) subseteq b
all x ε
参数：y；h : y in ball x (ε / 2)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Metric.ball_subset`：ball_subset (h : dist x y <= ε₂ - ε₁) : ball x ε₁ su
bseteq ball y ε₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_self_div_two`：sub_self_div_two (a : α) : a - a / 2 = a / 2
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem ball_half_subset (y) (h : y ∈ ball x (ε / 2)) : ball y (ε / 2) ⊆ ball x ε :=
  ball_subset <| by rw [sub_self_div_two]; exact le_of_lt h
/-
**Metric.exists_ball_subset_ball** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：exists_ball_subset_ball (h : y in ball x ε) : exists ε' > 0, ball y ε' sub
seteq ball x ε
参数：h : y in ball x ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Metric.ball_subset`：ball_subset (h : dist x y <= ε₂ - ε₁) : ball x ε₁ su
bseteq ball y ε₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_sub_self`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - (a
 - b) = b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem exists_ball_subset_ball (h : y ∈ ball x ε) : ∃ ε' > 0, ball y ε' ⊆ ball x ε :=
  ⟨_, sub_pos.2 h, ball_subset <| by rw [sub_sub_self]⟩

/-- If a property holds for all points in closed balls of arbitrarily large radii, then it holds for
all points. -/
/-
**Metric.forall_of_forall_mem_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：forall_of_forall_mem_closedBall (p : α -> Prop) (x : α) (H : existsᶠ R : R
eal in atTop, forall y in closedBall x R, p y) (y : α) : p y
参数：p : α -> Prop；x : α；H : existsᶠ R : Real in atTop, forall y in closedBall x R
, p y；y : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.frequently_iff`：frequently_iff {f : Filter α} {P : α -> Prop} : (
existsᶠ x in f, P x) ↔ forall {U}, U in f -> exists x in U, P x
· 使用定理 `Filter.Ici_mem_atTop`：Ici_mem_atTop [Preorder α] (a : α) : Ici a in (atT
op : Filter α)

--- 原说明 ---
If a property holds for all points in closed balls of arbitrarily large radii, t
hen it holds for
all points.
-/
theorem forall_of_forall_mem_closedBall (p : α → Prop) (x : α)
    (H : ∃ᶠ R : ℝ in atTop, ∀ y ∈ closedBall x R, p y) (y : α) : p y := by
  obtain ⟨R, hR, h⟩ : ∃ R ≥ dist y x, ∀ z : α, z ∈ closedBall x R → p z :=
    frequently_iff.1 H (Ici_mem_atTop (dist y x))
  exact h _ hR

/-- If a property holds for all points in balls of arbitrarily large radii, then it holds for all
points. -/
/-
**Metric.forall_of_forall_mem_ball** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：forall_of_forall_mem_ball (p : α -> Prop) (x : α) (H : existsᶠ R : Real in
 atTop, forall y in ball x R, p y) (y : α) : p y
参数：p : α -> Prop；x : α；H : existsᶠ R : Real in atTop, forall y in ball x R, p y；
y : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.frequently_iff`：frequently_iff {f : Filter α} {P : α -> Prop} : (
existsᶠ x in f, P x) ↔ forall {U}, U in f -> exists x in U, P x
· 使用定理 `Filter.Ioi_mem_atTop`：Ioi_mem_atTop [Preorder α] [NoTopOrder α] (x : α) 
: Ioi x in (atTop : Filter α)
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R

--- 原说明 ---
If a property holds for all points in balls of arbitrarily large radii, then it 
holds for all
points.
-/
theorem forall_of_forall_mem_ball (p : α → Prop) (x : α)
    (H : ∃ᶠ R : ℝ in atTop, ∀ y ∈ ball x R, p y) (y : α) : p y := by
  obtain ⟨R, hR, h⟩ : ∃ R > dist y x, ∀ z : α, z ∈ ball x R → p z :=
    frequently_iff.1 H (Ioi_mem_atTop (dist y x))
  exact h _ hR
/-
**Metric.isBounded_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：isBounded_iff {s : Set α} : IsBounded s ↔ exists C : Real, forall ⦃x⦄, x i
n s -> forall ⦃y⦄, y in s -> dist x y <= C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bornology.isBounded_def`：isBounded_def {s : Set α} : IsBounded s ↔ sᶜ in
 cobounded α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.mem_sets`：∀ {α : Type u_1} {f : Filter α} {s : Set α}, s ∈ f.sets
 ↔ s ∈ f
· 使用定理 `PseudoMetricSpace.cobounded_sets`：∀ {α : Type u} [self : PseudoMetricSpa
ce α], (Bornology.cobounded α).sets = {s | ∃ C, ∀ x ∈ sᶜ, ∀ y ∈ sᶜ, dist x y ≤ C
}
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isBounded_iff {s : Set α} :
    IsBounded s ↔ ∃ C : ℝ, ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → dist x y ≤ C := by
  rw [isBounded_def, ← Filter.mem_sets, @PseudoMetricSpace.cobounded_sets α, mem_ofPred_eq,
    compl_compl]
/-
**Metric.boundedSpace_iff** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：boundedSpace_iff : BoundedSpace α ↔ exists C, forall a b : α, dist a b <= 
C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Bornology.isBounded_univ`：isBounded_univ : IsBounded (univ : Set α) ↔ Bo
undedSpace α
· 使用定理 `Metric.isBounded_iff`：isBounded_iff {s : Set α} : IsBounded s ↔ exists C
 : Real, forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> dist x y <= C
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma boundedSpace_iff : BoundedSpace α ↔ ∃ C, ∀ a b : α, dist a b ≤ C := by
  rw [← isBounded_univ, Metric.isBounded_iff]
  simp
/-
**Metric.isBounded_iff_eventually** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：isBounded_iff_eventually {s : Set α} : IsBounded s ↔ forallᶠ C in atTop, f
orall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> dist x y <= C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Metric.isBounded_iff`：isBounded_iff {s : Set α} : IsBounded s ↔ exists C
 : Real, forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> dist x y <= C
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
-/
theorem isBounded_iff_eventually {s : Set α} :
    IsBounded s ↔ ∀ᶠ C in atTop, ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → dist x y ≤ C :=
  isBounded_iff.trans
    ⟨fun ⟨C, h⟩ => eventually_atTop.2 ⟨C, fun _C' hC' _x hx _y hy => (h hx hy).trans hC'⟩,
      Eventually.exists⟩
/-
**Metric.isBounded_iff_exists_ge** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：isBounded_iff_exists_ge {s : Set α} (c : Real) : IsBounded s ↔ exists C, c
 <= C ∧ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> dist x y <= C
参数：c : Real。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.isBounded_iff_eventually`：isBounded_iff_eventually {s : Set α} : 
IsBounded s ↔ forallᶠ C in atTop, forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> di
st x y <= C
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.isBounded_iff`：isBounded_iff {s : Set α} : IsBounded s ↔ exists C
 : Real, forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> dist x y <= C
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem isBounded_iff_exists_ge {s : Set α} (c : ℝ) :
    IsBounded s ↔ ∃ C, c ≤ C ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → dist x y ≤ C :=
  ⟨fun h => ((eventually_ge_atTop c).and (isBounded_iff_eventually.1 h)).exists, fun h =>
    isBounded_iff.2 <| h.imp fun _ => And.right⟩
/-
**Metric.isBounded_iff_nndist** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：isBounded_iff_nndist {s : Set α} : IsBounded s ↔ exists C : Real>=0, foral
l ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> nndist x y <= C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.isBounded_iff_exists_ge`：isBounded_iff_exists_ge {s : Set α} (c :
 Real) : IsBounded s ↔ exists C, c <= C ∧ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in
 s -> dist x y <= C
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isBounded_iff_nndist {s : Set α} :
    IsBounded s ↔ ∃ C : ℝ≥0, ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → nndist x y ≤ C := by
  simp only [isBounded_iff_exists_ge 0, NNReal.exists, ← NNReal.coe_le_coe, ← dist_nndist,
    NNReal.coe_mk, exists_prop]
/-
**Metric.boundedSpace_iff_nndist** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：boundedSpace_iff_nndist : BoundedSpace α ↔ exists C, forall a b : α, nndis
t a b <= C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Bornology.isBounded_univ`：isBounded_univ : IsBounded (univ : Set α) ↔ Bo
undedSpace α
· 使用定理 `Metric.isBounded_iff_nndist`：isBounded_iff_nndist {s : Set α} : IsBounde
d s ↔ exists C : Real>=0, forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> nndist x y
 <= C
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma boundedSpace_iff_nndist : BoundedSpace α ↔ ∃ C, ∀ a b : α, nndist a b ≤ C := by
  rw [← isBounded_univ, Metric.isBounded_iff_nndist]
  simp
/-
**Metric.boundedSpace_iff_edist** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：boundedSpace_iff_edist : BoundedSpace α ↔ exists C : Real>=0, forall a b :
 α, edist a b <= C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma boundedSpace_iff_edist : BoundedSpace α ↔ ∃ C : ℝ≥0, ∀ a b : α, edist a b ≤ C := by
  simp [Metric.boundedSpace_iff_nndist]
/-
**Metric.toUniformSpace_eq** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：toUniformSpace_eq : ‹PseudoMetricSpace α›.toUniformSpace = .ofDist dist di
st_self dist_comm dist_triangle
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.ext`：∀ {α : Type ua} {u₁ u₂ : UniformSpace α}, uniformity α
 = uniformity α → u₁ = u₂
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `dist_triangle`：dist_triangle (x y z : α) : dist x z <= dist x y + dist y
 z
· 使用定理 `PseudoMetricSpace.uniformity_dist`：∀ {α : Type u} [self : PseudoMetricSp
ace α], uniformity α = ⨅ ε, ⨅ (_ : ε > 0), Filter.principal {p | dist p.1 p.2 < 
ε}
-/
theorem toUniformSpace_eq :
    ‹PseudoMetricSpace α›.toUniformSpace = .ofDist dist dist_self dist_comm dist_triangle :=
  UniformSpace.ext PseudoMetricSpace.uniformity_dist
/-
**Metric.uniformity_basis_dist** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：uniformity_basis_dist : (𝓤 α).HasBasis (fun ε : Real => 0 < ε) fun ε => { 
p : α × α | dist p.1 p.2 < ε }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `dist_triangle`：dist_triangle (x y z : α) : dist x z <= dist x y + dist y
 z
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.toUniformSpace_eq`：toUniformSpace_eq : ‹PseudoMetricSpace α›.toUn
iformSpace = .ofDist dist dist_self dist_comm dist_triangle
· 使用定理 `UniformSpace.hasBasis_ofFun`：hasBasis_ofFun [AddCommMonoid M] [LinearOrd
er M] (h₀ : exists x : M, 0 < x) (d : X -> X -> M) (refl : forall x, d x x = 0) 
(symm : forall x …
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `UniformSpace.ofDist_aux`：UniformSpace.ofDist_aux (ε : Real) (hε : 0 < ε)
 : exists δ > (0 : Real), forall x < δ, forall y < δ, x + y < ε
-/
theorem uniformity_basis_dist :
    (𝓤 α).HasBasis (fun ε : ℝ => 0 < ε) fun ε => { p : α × α | dist p.1 p.2 < ε } := by
  rw [toUniformSpace_eq]
  exact UniformSpace.hasBasis_ofFun (exists_gt _) _ _ _ _ _

/-- Given `f : β → ℝ`, if `f` sends `{i | p i}` to a set of positive numbers
accumulating to zero, then `f i`-neighborhoods of the diagonal form a basis of `𝓤 α`.

For specific bases see `uniformity_basis_dist`, `uniformity_basis_dist_inv_nat_succ`,
and `uniformity_basis_dist_inv_nat_pos`. -/
/-
**Metric.mk_uniformity_basis** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：∀ {α : Type u} [inst : PseudoMetricSpace α] {β : Type u_3} {p : β → Prop} 
{f : β → ℝ},   (∀ (i : β), p i → 0 < f i) →     (∀ ⦃ε : ℝ⦄, 0 < ε → ∃ i, p i ∧ f
 i ≤ ε) → (uniformity α).HasBasis p fun i => {p | dist p.1 p.2 < f i}
参数：∀ (i : β), p i → 0 < f i；∀ ⦃ε : ℝ⦄, 0 < ε → ∃ i, p i ∧ f i ≤ ε；uniformity α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Metric.uniformity_basis_dist`：uniformity_basis_dist : (𝓤 α).HasBasis (fu
n ε : Real => 0 < ε) fun ε => { p : α × α | dist p.1 p.2 < ε }
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c

--- 原说明 ---
Given `f : β → ℝ`, if `f` sends `{i | p i}` to a set of positive numbers
accumulating to zero, then `f i`-neighborhoods of the diagonal form a basis of `
𝓤 α`.

For specific bases see `uniformity_basis_dist`, `uniformity_basis_dist_inv_nat_s
ucc`,
and `uniformity_basis_dist_inv_nat_pos`.
-/
protected theorem mk_uniformity_basis {β : Type*} {p : β → Prop} {f : β → ℝ}
    (hf₀ : ∀ i, p i → 0 < f i) (hf : ∀ ⦃ε⦄, 0 < ε → ∃ i, p i ∧ f i ≤ ε) :
    (𝓤 α).HasBasis p fun i => { p : α × α | dist p.1 p.2 < f i } := by
  refine ⟨fun s => uniformity_basis_dist.mem_iff.trans ?_⟩
  constructor
  · rintro ⟨ε, ε₀, hε⟩
    rcases hf ε₀ with ⟨i, hi, H⟩
    exact ⟨i, hi, fun x (hx : _ < _) => hε <| lt_of_lt_of_le hx H⟩
  · exact fun ⟨i, hi, H⟩ => ⟨f i, hf₀ i hi, H⟩
/-
**Metric.uniformity_basis_dist_rat** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：uniformity_basis_dist_rat : (𝓤 α).HasBasis (fun r : Rat => 0 < r) fun r =>
 { p : α × α | dist p.1 p.2 < r }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.mk_uniformity_basis`：∀ {α : Type u} [inst : PseudoMetricSpace α] 
{β : Type u_3} {p : β → Prop} {f : β → ℝ},   (∀ (i : β), p i → 0 < f i) →     (∀
 ⦃ε : ℝ⦄, 0 < ε …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Rat.cast_pos`：∀ {q : ℚ} {K : Type u_5} [inst : Field K] [inst_1 : Linear
Order K] [IsStrictOrderedRing K], 0 < ↑q ↔ 0 < q
· 使用定理 `exists_rat_btwn`：exists_rat_btwn {x y : K} (h : x < y) : exists q : Rat,
 x < q ∧ q < y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem uniformity_basis_dist_rat :
    (𝓤 α).HasBasis (fun r : ℚ => 0 < r) fun r => { p : α × α | dist p.1 p.2 < r } :=
  Metric.mk_uniformity_basis (fun _ => Rat.cast_pos.2) fun _ε hε =>
    let ⟨r, hr0, hrε⟩ := exists_rat_btwn hε
    ⟨r, Rat.cast_pos.1 hr0, hrε.le⟩
/-
**Metric.uniformity_basis_dist_inv_nat_succ** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：uniformity_basis_dist_inv_nat_succ : (𝓤 α).HasBasis (fun _ => True) fun n 
: Nat => { p : α × α | dist p.1 p.2 < 1 / (↑n + 1) }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.mk_uniformity_basis`：∀ {α : Type u} [inst : PseudoMetricSpace α] 
{β : Type u_3} {p : β → Prop} {f : β → ℝ},   (∀ (i : β), p i → 0 < f i) →     (∀
 ⦃ε : ℝ⦄, 0 < ε …
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.cast_add_one_pos`：cast_add_one_pos (n : Nat) : 0 < (n : α) + 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `trivial`：True
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `exists_nat_one_div_lt`：exists_nat_one_div_lt (hε : 0 < ε) : exists n : N
at, 1 / (n + 1 : K) < ε
-/
theorem uniformity_basis_dist_inv_nat_succ :
    (𝓤 α).HasBasis (fun _ => True) fun n : ℕ => { p : α × α | dist p.1 p.2 < 1 / (↑n + 1) } :=
  Metric.mk_uniformity_basis (fun n _ => div_pos zero_lt_one <| Nat.cast_add_one_pos n) fun _ε ε0 =>
    (exists_nat_one_div_lt ε0).imp fun _n hn => ⟨trivial, le_of_lt hn⟩
/-
**Metric.uniformity_basis_dist_inv_nat_pos** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：uniformity_basis_dist_inv_nat_pos : (𝓤 α).HasBasis (fun n : Nat => 0 < n) 
fun n : Nat => { p : α × α | dist p.1 p.2 < 1 / ↑n }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.mk_uniformity_basis`：∀ {α : Type u} [inst : PseudoMetricSpace α] 
{β : Type u_3} {p : β → Prop} {f : β → ℝ},   (∀ (i : β), p i → 0 < f i) →     (∀
 ⦃ε : ℝ⦄, 0 < ε …
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用引理 `exists_nat_one_div_lt`：exists_nat_one_div_lt (hε : 0 < ε) : exists n : N
at, 1 / (n + 1 : K) < ε
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem uniformity_basis_dist_inv_nat_pos :
    (𝓤 α).HasBasis (fun n : ℕ => 0 < n) fun n : ℕ => { p : α × α | dist p.1 p.2 < 1 / ↑n } :=
  Metric.mk_uniformity_basis (fun _ hn => div_pos zero_lt_one <| Nat.cast_pos.2 hn) fun _ ε0 =>
    let ⟨n, hn⟩ := exists_nat_one_div_lt ε0
    ⟨n + 1, Nat.succ_pos n, mod_cast hn.le⟩
/-
**Metric.uniformity_basis_dist_pow** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：uniformity_basis_dist_pow {r : Real} (h0 : 0 < r) (h1 : r < 1) : (𝓤 α).Has
Basis (fun _ : Nat => True) fun n : Nat => { p : α × α | dist p.1 p.2 < r ^ n }
参数：h0 : 0 < r；h1 : r < 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.mk_uniformity_basis`：∀ {α : Type u} [inst : PseudoMetricSpace α] 
{β : Type u_3} {p : β → Prop} {f : β → ℝ},   (∀ (i : β), p i → 0 < f i) →     (∀
 ⦃ε : ℝ⦄, 0 < ε …
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `exists_pow_lt_of_lt_one`：exists_pow_lt_of_lt_one (hx : 0 < x) (hy : y < 
1) : exists n : Nat, y ^ n < x
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `trivial`：True
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem uniformity_basis_dist_pow {r : ℝ} (h0 : 0 < r) (h1 : r < 1) :
    (𝓤 α).HasBasis (fun _ : ℕ => True) fun n : ℕ => { p : α × α | dist p.1 p.2 < r ^ n } :=
  Metric.mk_uniformity_basis (fun _ _ => pow_pos h0 _) fun _ε ε0 =>
    let ⟨n, hn⟩ := exists_pow_lt_of_lt_one ε0 h1
    ⟨n, trivial, hn.le⟩
/-
**Metric.uniformity_basis_dist_lt** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：uniformity_basis_dist_lt {R : Real} (hR : 0 < R) : (𝓤 α).HasBasis (fun r :
 Real => 0 < r ∧ r < R) fun r => { p : α × α | dist p.1 p.2 < r }
参数：hR : 0 < R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.mk_uniformity_basis`：∀ {α : Type u} [inst : PseudoMetricSpace α] 
{β : Type u_3} {p : β → Prop} {f : β → ℝ},   (∀ (i : β), p i → 0 < f i) →     (∀
 ⦃ε : ℝ⦄, 0 < ε …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `lt_min`：lt_min (h₁ : a < b) (h₂ : a < c) : a < min b c
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `min_lt_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, min b c <
 a ↔ b < a ∨ c < a
· 使用定理 `half_lt_self`：∀ {α : Type u_2} [inst : Semifield α] [inst_1 : PartialOrd
er α] [PosMulReflectLT α] {a : α} [IsStrictOrderedRing α],   0 < a → a / 2 < a
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
-/
theorem uniformity_basis_dist_lt {R : ℝ} (hR : 0 < R) :
    (𝓤 α).HasBasis (fun r : ℝ => 0 < r ∧ r < R) fun r => { p : α × α | dist p.1 p.2 < r } :=
  Metric.mk_uniformity_basis (fun _ => And.left) fun r hr =>
    ⟨min r (R / 2), ⟨lt_min hr (half_pos hR), min_lt_iff.2 <| Or.inr (half_lt_self hR)⟩,
      min_le_left _ _⟩

/-- Given `f : β → ℝ`, if `f` sends `{i | p i}` to a set of positive numbers
accumulating to zero, then closed neighborhoods of the diagonal of sizes `{f i | p i}`
form a basis of `𝓤 α`.

Currently we have only one specific basis `uniformity_basis_dist_le` based on this constructor.
More can be easily added if needed in the future. -/
/-
**Metric.mk_uniformity_basis_le** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：∀ {α : Type u} [inst : PseudoMetricSpace α] {β : Type u_3} {p : β → Prop} 
{f : β → ℝ},   (∀ (x : β), p x → 0 < f x) →     (∀ (ε : ℝ), 0 < ε → ∃ x, p x ∧ f
 x ≤ ε) → (uniformity α).HasBasis p fun x => {p | dist p.1 p.2 ≤ f x}
参数：∀ (x : β), p x → 0 < f x；∀ (ε : ℝ), 0 < ε → ∃ x, p x ∧ f x ≤ ε；uniformity α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Metric.uniformity_basis_dist`：uniformity_basis_dist : (𝓤 α).HasBasis (fu
n ε : Real => 0 < ε) fun ε => { p : α × α | dist p.1 p.2 < ε }
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
Given `f : β → ℝ`, if `f` sends `{i | p i}` to a set of positive numbers
accumulating to zero, then closed neighborhoods of the diagonal of sizes `{f i |
 p i}`
form a basis of `𝓤 α`.

Currently we have only one specific basis `uniformity_basis_dist_le` based on th
is constructor.
More can be easily added if needed in the future.
-/
protected theorem mk_uniformity_basis_le {β : Type*} {p : β → Prop} {f : β → ℝ}
    (hf₀ : ∀ x, p x → 0 < f x) (hf : ∀ ε, 0 < ε → ∃ x, p x ∧ f x ≤ ε) :
    (𝓤 α).HasBasis p fun x => { p : α × α | dist p.1 p.2 ≤ f x } := by
  refine ⟨fun s => uniformity_basis_dist.mem_iff.trans ?_⟩
  constructor
  · rintro ⟨ε, ε₀, hε⟩
    rcases exists_between ε₀ with ⟨ε', hε'⟩
    rcases hf ε' hε'.1 with ⟨i, hi, H⟩
    exact ⟨i, hi, fun x (hx : _ ≤ _) => hε <| lt_of_le_of_lt (le_trans hx H) hε'.2⟩
  · exact fun ⟨i, hi, H⟩ => ⟨f i, hf₀ i hi, fun x (hx : _ < _) => H (mem_ofPred.2 hx.le)⟩

/-- Constant size closed neighborhoods of the diagonal form a basis
of the uniformity filter. -/
/-
**Metric.uniformity_basis_dist_le** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：uniformity_basis_dist_le : (𝓤 α).HasBasis ((0 : Real) < ·) fun ε => { p : 
α × α | dist p.1 p.2 <= ε }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.mk_uniformity_basis_le`：∀ {α : Type u} [inst : PseudoMetricSpace 
α] {β : Type u_3} {p : β → Prop} {f : β → ℝ},   (∀ (x : β), p x → 0 < f x) →    
 (∀ (ε : ℝ), 0 < ε …
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
Constant size closed neighborhoods of the diagonal form a basis
of the uniformity filter.
-/
theorem uniformity_basis_dist_le :
    (𝓤 α).HasBasis ((0 : ℝ) < ·) fun ε => { p : α × α | dist p.1 p.2 ≤ ε } :=
  Metric.mk_uniformity_basis_le (fun _ => id) fun ε ε₀ => ⟨ε, ε₀, le_refl ε⟩
/-
**Metric.uniformity_basis_dist_le_inv_nat_succ** 是 Mathlib 中的一个定理，位于命名空间 `Metric
`。
形式化陈述：uniformity_basis_dist_le_inv_nat_succ : (𝓤 α).HasBasis (fun _ => True) fun
 n : Nat => { p : α × α | dist p.1 p.2 <= 1 / (↑n + 1) }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.mk_uniformity_basis_le`：∀ {α : Type u} [inst : PseudoMetricSpace 
α] {β : Type u_3} {p : β → Prop} {f : β → ℝ},   (∀ (x : β), p x → 0 < f x) →    
 (∀ (ε : ℝ), 0 < ε …
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.cast_add_one_pos`：cast_add_one_pos (n : Nat) : 0 < (n : α) + 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `trivial`：True
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `exists_nat_one_div_lt`：exists_nat_one_div_lt (hε : 0 < ε) : exists n : N
at, 1 / (n + 1 : K) < ε
-/
theorem uniformity_basis_dist_le_inv_nat_succ :
    (𝓤 α).HasBasis (fun _ => True) fun n : ℕ => { p : α × α | dist p.1 p.2 ≤ 1 / (↑n + 1) } :=
  Metric.mk_uniformity_basis_le (fun n _ => div_pos zero_lt_one <| Nat.cast_add_one_pos n)
    fun _ε ε0 => (exists_nat_one_div_lt ε0).imp fun _n hn => ⟨trivial, hn.le⟩
/-
**Metric.uniformity_basis_dist_le_inv_nat_pos** 是 Mathlib 中的一个定理，位于命名空间 `Metric`
。
形式化陈述：uniformity_basis_dist_le_inv_nat_pos : (𝓤 α).HasBasis (fun n : Nat => 0 < 
n) fun n : Nat => { p : α × α | dist p.1 p.2 <= 1 / ↑n }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.mk_uniformity_basis_le`：∀ {α : Type u} [inst : PseudoMetricSpace 
α] {β : Type u_3} {p : β → Prop} {f : β → ℝ},   (∀ (x : β), p x → 0 < f x) →    
 (∀ (ε : ℝ), 0 < ε …
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用引理 `exists_nat_one_div_lt`：exists_nat_one_div_lt (hε : 0 < ε) : exists n : N
at, 1 / (n + 1 : K) < ε
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem uniformity_basis_dist_le_inv_nat_pos :
    (𝓤 α).HasBasis (fun n : ℕ => 0 < n) fun n : ℕ => { p : α × α | dist p.1 p.2 ≤ 1 / ↑n } :=
  Metric.mk_uniformity_basis_le (fun n hn => div_pos zero_lt_one <| Nat.cast_pos.2 hn) fun _ε ε0 =>
    let ⟨n, hn⟩ := exists_nat_one_div_lt ε0
    ⟨n + 1, n.succ_pos, by simpa using hn.le⟩
/-
**Metric.uniformity_basis_dist_le_pow** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：uniformity_basis_dist_le_pow {r : Real} (h0 : 0 < r) (h1 : r < 1) : (𝓤 α).
HasBasis (fun _ : Nat => True) fun n : Nat => { p : α × α | dist p.1 p.2 <= r ^ 
n }
参数：h0 : 0 < r；h1 : r < 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.mk_uniformity_basis_le`：∀ {α : Type u} [inst : PseudoMetricSpace 
α] {β : Type u_3} {p : β → Prop} {f : β → ℝ},   (∀ (x : β), p x → 0 < f x) →    
 (∀ (ε : ℝ), 0 < ε …
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `exists_pow_lt_of_lt_one`：exists_pow_lt_of_lt_one (hx : 0 < x) (hy : y < 
1) : exists n : Nat, y ^ n < x
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `trivial`：True
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem uniformity_basis_dist_le_pow {r : ℝ} (h0 : 0 < r) (h1 : r < 1) :
    (𝓤 α).HasBasis (fun _ : ℕ => True) fun n : ℕ => { p : α × α | dist p.1 p.2 ≤ r ^ n } :=
  Metric.mk_uniformity_basis_le (fun _ _ => pow_pos h0 _) fun _ε ε0 =>
    let ⟨n, hn⟩ := exists_pow_lt_of_lt_one ε0 h1
    ⟨n, trivial, hn.le⟩
/-
**Metric.mem_uniformity_dist** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：mem_uniformity_dist {s : Set (α × α)} : s in 𝓤 α ↔ exists ε > 0, forall ⦃a
 b : α⦄, dist a b < ε -> (a, b) in s
参数：α × α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.mem_uniformity_iff`：Filter.HasBasis.mem_uniformity_iff {
p : β -> Prop} {s : β -> SetRel α α} (h : (𝓤 α).HasBasis p s) {t : SetRel α α} :
 t in 𝓤 α ↔ exists i, p …
· 使用定理 `Metric.uniformity_basis_dist`：uniformity_basis_dist : (𝓤 α).HasBasis (fu
n ε : Real => 0 < ε) fun ε => { p : α × α | dist p.1 p.2 < ε }
-/
theorem mem_uniformity_dist {s : Set (α × α)} :
    s ∈ 𝓤 α ↔ ∃ ε > 0, ∀ ⦃a b : α⦄, dist a b < ε → (a, b) ∈ s :=
  uniformity_basis_dist.mem_uniformity_iff

/-- A constant size neighborhood of the diagonal is an entourage. -/
/-
**Metric.dist_mem_uniformity** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：dist_mem_uniformity {ε : Real} (ε0 : 0 < ε) : { p : α × α | dist p.1 p.2 <
 ε } in 𝓤 α
参数：ε0 : 0 < ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.mem_uniformity_dist`：mem_uniformity_dist {s : Set (α × α)} : s in
 𝓤 α ↔ exists ε > 0, forall ⦃a b : α⦄, dist a b < ε -> (a, b) in s

--- 原说明 ---
A constant size neighborhood of the diagonal is an entourage.
-/
theorem dist_mem_uniformity {ε : ℝ} (ε0 : 0 < ε) : { p : α × α | dist p.1 p.2 < ε } ∈ 𝓤 α :=
  mem_uniformity_dist.2 ⟨ε, ε0, fun _ _ ↦ id⟩
/-
**Metric.uniformContinuous_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：uniformContinuous_iff [PseudoMetricSpace β] {f : α -> β} : UniformContinuo
us f ↔ forall ε > 0, exists δ > 0, forall ⦃a b : α⦄, dist a b < δ -> dist (f a) 
(f b) < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.uniformContinuous_iff`：Filter.HasBasis.uniformContinuous
_iff {ι'} {p : ι -> Prop} {s : ι -> SetRel α α} (ha : (𝓤 α).HasBasis p s) {q : ι
' -> Prop} {t : ι' -> Set (…
· 使用定理 `Metric.uniformity_basis_dist`：uniformity_basis_dist : (𝓤 α).HasBasis (fu
n ε : Real => 0 < ε) fun ε => { p : α × α | dist p.1 p.2 < ε }
-/
theorem uniformContinuous_iff [PseudoMetricSpace β] {f : α → β} :
    UniformContinuous f ↔ ∀ ε > 0, ∃ δ > 0, ∀ ⦃a b : α⦄, dist a b < δ → dist (f a) (f b) < ε :=
  uniformity_basis_dist.uniformContinuous_iff uniformity_basis_dist
/-
**Metric.uniformContinuousOn_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：uniformContinuousOn_iff [PseudoMetricSpace β] {f : α -> β} {s : Set α} : U
niformContinuousOn f s ↔ forall ε > 0, exists δ > 0, forall x in s, forall y in 
s, dist x y < δ -> dist (f x) (f y) < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.uniformContinuousOn_iff`：Filter.HasBasis.uniformContinuo
usOn_iff {ι'} {p : ι -> Prop} {s : ι -> SetRel α α} (ha : (𝓤 α).HasBasis p s) {q
 : ι' -> Prop} {t : ι' -> Set…
· 使用定理 `Metric.uniformity_basis_dist`：uniformity_basis_dist : (𝓤 α).HasBasis (fu
n ε : Real => 0 < ε) fun ε => { p : α × α | dist p.1 p.2 < ε }
-/
theorem uniformContinuousOn_iff [PseudoMetricSpace β] {f : α → β} {s : Set α} :
    UniformContinuousOn f s ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x ∈ s, ∀ y ∈ s, dist x y < δ → dist (f x) (f y) < ε :=
  uniformity_basis_dist.uniformContinuousOn_iff uniformity_basis_dist
/-
**Metric.uniformContinuous_iff_le** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：uniformContinuous_iff_le [PseudoMetricSpace β] {f : α -> β} : UniformConti
nuous f ↔ forall ε > 0, exists δ > 0, forall ⦃a b : α⦄, dist a b <= δ -> dist (f
 a) (f b) <= ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.uniformContinuous_iff`：Filter.HasBasis.uniformContinuous
_iff {ι'} {p : ι -> Prop} {s : ι -> SetRel α α} (ha : (𝓤 α).HasBasis p s) {q : ι
' -> Prop} {t : ι' -> Set (…
· 使用定理 `Metric.uniformity_basis_dist_le`：uniformity_basis_dist_le : (𝓤 α).HasBas
is ((0 : Real) < ·) fun ε => { p : α × α | dist p.1 p.2 <= ε }
-/
theorem uniformContinuous_iff_le [PseudoMetricSpace β] {f : α → β} :
    UniformContinuous f ↔ ∀ ε > 0, ∃ δ > 0, ∀ ⦃a b : α⦄, dist a b ≤ δ → dist (f a) (f b) ≤ ε :=
  uniformity_basis_dist_le.uniformContinuous_iff uniformity_basis_dist_le
/-
**Metric.uniformContinuousOn_iff_le** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：uniformContinuousOn_iff_le [PseudoMetricSpace β] {f : α -> β} {s : Set α} 
: UniformContinuousOn f s ↔ forall ε > 0, exists δ > 0, forall x in s, forall y 
in s, dist x y <= δ -> dist (f x) (f y) <= ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.uniformContinuousOn_iff`：Filter.HasBasis.uniformContinuo
usOn_iff {ι'} {p : ι -> Prop} {s : ι -> SetRel α α} (ha : (𝓤 α).HasBasis p s) {q
 : ι' -> Prop} {t : ι' -> Set…
· 使用定理 `Metric.uniformity_basis_dist_le`：uniformity_basis_dist_le : (𝓤 α).HasBas
is ((0 : Real) < ·) fun ε => { p : α × α | dist p.1 p.2 <= ε }
-/
theorem uniformContinuousOn_iff_le [PseudoMetricSpace β] {f : α → β} {s : Set α} :
    UniformContinuousOn f s ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ δ → dist (f x) (f y) ≤ ε :=
  uniformity_basis_dist_le.uniformContinuousOn_iff uniformity_basis_dist_le
/-
**Metric.nhds_basis_ball** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：nhds_basis_ball : (𝓝 x).HasBasis (0 < ·) (ball x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhds_basis_uniformity`：nhds_basis_uniformity {p : ι -> Prop} {s : ι -> S
etRel α α} (h : (𝓤 α).HasBasis p s) {x : α} : (𝓝 x).HasBasis p fun i => { y | (y
, x) in s i…
· 使用定理 `Metric.uniformity_basis_dist`：uniformity_basis_dist : (𝓤 α).HasBasis (fu
n ε : Real => 0 < ε) fun ε => { p : α × α | dist p.1 p.2 < ε }
-/
theorem nhds_basis_ball : (𝓝 x).HasBasis (0 < ·) (ball x) :=
  nhds_basis_uniformity uniformity_basis_dist
/-
**Metric.mem_nhds_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：mem_nhds_iff : s in 𝓝 x ↔ exists ε > 0, ball x ε subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Metric.nhds_basis_ball`：nhds_basis_ball : (𝓝 x).HasBasis (0 < ·) (ball x
)
-/
theorem mem_nhds_iff : s ∈ 𝓝 x ↔ ∃ ε > 0, ball x ε ⊆ s :=
  nhds_basis_ball.mem_iff
/-
**Metric.eventually_nhds_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：eventually_nhds_iff {p : α -> Prop} : (forallᶠ y in 𝓝 x, p y) ↔ exists ε >
 0, forall ⦃y⦄, dist y x < ε -> p y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists ε > 0, ball x ε su
bseteq s
-/
theorem eventually_nhds_iff {p : α → Prop} :
    (∀ᶠ y in 𝓝 x, p y) ↔ ∃ ε > 0, ∀ ⦃y⦄, dist y x < ε → p y :=
  mem_nhds_iff
/-
**Metric.eventually_nhds_iff_ball** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：eventually_nhds_iff_ball {p : α -> Prop} : (forallᶠ y in 𝓝 x, p y) ↔ exist
s ε > 0, forall y in ball x ε, p y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists ε > 0, ball x ε su
bseteq s
-/
theorem eventually_nhds_iff_ball {p : α → Prop} :
    (∀ᶠ y in 𝓝 x, p y) ↔ ∃ ε > 0, ∀ y ∈ ball x ε, p y :=
  mem_nhds_iff

/-- A version of `Filter.eventually_prod_iff` where the first filter consists of neighborhoods
in a pseudo-metric space. -/
/-
**Metric.eventually_nhds_prod_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：eventually_nhds_prod_iff {f : Filter ι} {x₀ : α} {p : α × ι -> Prop} : (fo
rallᶠ x in 𝓝 x₀ ×ˢ f, p x) ↔ exists ε > (0 : Real), exists pa : ι -> Prop, (fora
llᶠ i in f, pa i) ∧ forall ⦃x⦄, dist x x₀ < ε -> forall ⦃i⦄, pa i -> p (x, i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.HasBasis.eventually_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Fil
ter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {q : α → Prop}, (∀ᶠ 
(x : α) in l, q x) ↔…
· 使用定理 `Filter.HasBasis.prod`：∀ {α : Type u_1} {β : Type u_2} {la : Filter α} {l
b : Filter β} {ι : Type u_6} {ι' : Type u_7} {pa : ι → Prop}   {sa : ι → Set α} 
{pb : ι' →…
· 使用定理 `Metric.nhds_basis_ball`：nhds_basis_ball : (𝓝 x).HasBasis (0 < ·) (ball x
)
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Function.Surjective.exists`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Surjective f → ∀ {p : β → Prop}, (∃ y, p y) ↔ ∃ x, p (f x)
· 使用定理 `Set.mem_surjective`：∀ {α : Type u}, Function.Surjective Membership.mem
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A version of `Filter.eventually_prod_iff` where the first filter consists of nei
ghborhoods
in a pseudo-metric space.
-/
theorem eventually_nhds_prod_iff {f : Filter ι} {x₀ : α} {p : α × ι → Prop} :
    (∀ᶠ x in 𝓝 x₀ ×ˢ f, p x) ↔ ∃ ε > (0 : ℝ), ∃ pa : ι → Prop, (∀ᶠ i in f, pa i) ∧
      ∀ ⦃x⦄, dist x x₀ < ε → ∀ ⦃i⦄, pa i → p (x, i) := by
  refine (nhds_basis_ball.prod f.basis_sets).eventually_iff.trans ?_
  simp only [Prod.exists, forall_prod_set, id, mem_ball, and_assoc, exists_and_left,
    Set.mem_surjective.exists, eventually_mem_set]

/-- A version of `Filter.eventually_prod_iff` where the second filter consists of neighborhoods
in a pseudo-metric space. -/
/-
**Metric.eventually_prod_nhds_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：eventually_prod_nhds_iff {f : Filter ι} {x₀ : α} {p : ι × α -> Prop} : (fo
rallᶠ x in f ×ˢ 𝓝 x₀, p x) ↔ exists pa : ι -> Prop, (forallᶠ i in f, pa i) ∧ exi
sts ε > 0, forall ⦃i⦄, pa i -> forall ⦃x⦄, dist x x₀ < ε -> p (i, x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventually_swap_iff`：eventually_swap_iff {p : α × β -> Prop} : (f
orallᶠ x : α × β in f ×ˢ g, p x) ↔ forallᶠ y : β × α in g ×ˢ f, p y.swap
· 使用定理 `Metric.eventually_nhds_prod_iff`：eventually_nhds_prod_iff {f : Filter ι}
 {x₀ : α} {p : α × ι -> Prop} : (forallᶠ x in 𝓝 x₀ ×ˢ f, p x) ↔ exists ε > (0 : 
Real), exists pa : ι …

--- 原说明 ---
A version of `Filter.eventually_prod_iff` where the second filter consists of ne
ighborhoods
in a pseudo-metric space.
-/
theorem eventually_prod_nhds_iff {f : Filter ι} {x₀ : α} {p : ι × α → Prop} :
    (∀ᶠ x in f ×ˢ 𝓝 x₀, p x) ↔ ∃ pa : ι → Prop, (∀ᶠ i in f, pa i) ∧
      ∃ ε > 0, ∀ ⦃i⦄, pa i → ∀ ⦃x⦄, dist x x₀ < ε → p (i, x) := by
  rw [eventually_swap_iff, Metric.eventually_nhds_prod_iff]
  constructor <;>
    · rintro ⟨a1, a2, a3, a4, a5⟩
      exact ⟨a3, a4, a1, a2, fun _ b1 b2 b3 => a5 b3 b1⟩
/-
**Metric.nhds_basis_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：nhds_basis_closedBall : (𝓝 x).HasBasis (fun ε : Real => 0 < ε) (closedBall
 x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhds_basis_uniformity`：nhds_basis_uniformity {p : ι -> Prop} {s : ι -> S
etRel α α} (h : (𝓤 α).HasBasis p s) {x : α} : (𝓝 x).HasBasis p fun i => { y | (y
, x) in s i…
· 使用定理 `Metric.uniformity_basis_dist_le`：uniformity_basis_dist_le : (𝓤 α).HasBas
is ((0 : Real) < ·) fun ε => { p : α × α | dist p.1 p.2 <= ε }
-/
theorem nhds_basis_closedBall : (𝓝 x).HasBasis (fun ε : ℝ => 0 < ε) (closedBall x) :=
  nhds_basis_uniformity uniformity_basis_dist_le
/-
**Metric.nhds_basis_ball_inv_nat_succ** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：nhds_basis_ball_inv_nat_succ : (𝓝 x).HasBasis (fun _ => True) fun n : Nat 
=> ball x (1 / (↑n + 1))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhds_basis_uniformity`：nhds_basis_uniformity {p : ι -> Prop} {s : ι -> S
etRel α α} (h : (𝓤 α).HasBasis p s) {x : α} : (𝓝 x).HasBasis p fun i => { y | (y
, x) in s i…
· 使用定理 `Metric.uniformity_basis_dist_inv_nat_succ`：uniformity_basis_dist_inv_nat
_succ : (𝓤 α).HasBasis (fun _ => True) fun n : Nat => { p : α × α | dist p.1 p.2
 < 1 / (↑n + 1) }
-/
theorem nhds_basis_ball_inv_nat_succ :
    (𝓝 x).HasBasis (fun _ => True) fun n : ℕ => ball x (1 / (↑n + 1)) :=
  nhds_basis_uniformity uniformity_basis_dist_inv_nat_succ
/-
**Metric.nhds_basis_ball_inv_nat_pos** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：nhds_basis_ball_inv_nat_pos : (𝓝 x).HasBasis (fun n => 0 < n) fun n : Nat 
=> ball x (1 / ↑n)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhds_basis_uniformity`：nhds_basis_uniformity {p : ι -> Prop} {s : ι -> S
etRel α α} (h : (𝓤 α).HasBasis p s) {x : α} : (𝓝 x).HasBasis p fun i => { y | (y
, x) in s i…
· 使用定理 `Metric.uniformity_basis_dist_inv_nat_pos`：uniformity_basis_dist_inv_nat_
pos : (𝓤 α).HasBasis (fun n : Nat => 0 < n) fun n : Nat => { p : α × α | dist p.
1 p.2 < 1 / ↑n }
-/
theorem nhds_basis_ball_inv_nat_pos :
    (𝓝 x).HasBasis (fun n => 0 < n) fun n : ℕ => ball x (1 / ↑n) :=
  nhds_basis_uniformity uniformity_basis_dist_inv_nat_pos
/-
**Metric.nhds_basis_closedBall_inv_nat_succ** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：nhds_basis_closedBall_inv_nat_succ : (𝓝 x).HasBasis (fun _ => True) fun n 
: Nat => closedBall x (1 / (↑n + 1))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhds_basis_uniformity`：nhds_basis_uniformity {p : ι -> Prop} {s : ι -> S
etRel α α} (h : (𝓤 α).HasBasis p s) {x : α} : (𝓝 x).HasBasis p fun i => { y | (y
, x) in s i…
· 使用定理 `Metric.uniformity_basis_dist_le_inv_nat_succ`：uniformity_basis_dist_le_i
nv_nat_succ : (𝓤 α).HasBasis (fun _ => True) fun n : Nat => { p : α × α | dist p
.1 p.2 <= 1 / (↑n + 1) }
-/
theorem nhds_basis_closedBall_inv_nat_succ :
    (𝓝 x).HasBasis (fun _ => True) fun n : ℕ => closedBall x (1 / (↑n + 1)) :=
  nhds_basis_uniformity uniformity_basis_dist_le_inv_nat_succ
/-
**Metric.nhds_basis_closedBall_inv_nat_pos** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：nhds_basis_closedBall_inv_nat_pos : (𝓝 x).HasBasis (fun n => 0 < n) fun n 
: Nat => closedBall x (1 / ↑n)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhds_basis_uniformity`：nhds_basis_uniformity {p : ι -> Prop} {s : ι -> S
etRel α α} (h : (𝓤 α).HasBasis p s) {x : α} : (𝓝 x).HasBasis p fun i => { y | (y
, x) in s i…
· 使用定理 `Metric.uniformity_basis_dist_le_inv_nat_pos`：uniformity_basis_dist_le_in
v_nat_pos : (𝓤 α).HasBasis (fun n : Nat => 0 < n) fun n : Nat => { p : α × α | d
ist p.1 p.2 <= 1 / ↑n }
-/
theorem nhds_basis_closedBall_inv_nat_pos :
    (𝓝 x).HasBasis (fun n => 0 < n) fun n : ℕ => closedBall x (1 / ↑n) :=
  nhds_basis_uniformity uniformity_basis_dist_le_inv_nat_pos
/-
**Metric.nhds_basis_ball_pow** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：nhds_basis_ball_pow {r : Real} (h0 : 0 < r) (h1 : r < 1) : (𝓝 x).HasBasis 
(fun _ => True) fun n : Nat => ball x (r ^ n)
参数：h0 : 0 < r；h1 : r < 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhds_basis_uniformity`：nhds_basis_uniformity {p : ι -> Prop} {s : ι -> S
etRel α α} (h : (𝓤 α).HasBasis p s) {x : α} : (𝓝 x).HasBasis p fun i => { y | (y
, x) in s i…
· 使用定理 `Metric.uniformity_basis_dist_pow`：uniformity_basis_dist_pow {r : Real} (
h0 : 0 < r) (h1 : r < 1) : (𝓤 α).HasBasis (fun _ : Nat => True) fun n : Nat => {
 p : α × α | dist p.1 …
-/
theorem nhds_basis_ball_pow {r : ℝ} (h0 : 0 < r) (h1 : r < 1) :
    (𝓝 x).HasBasis (fun _ => True) fun n : ℕ => ball x (r ^ n) :=
  nhds_basis_uniformity (uniformity_basis_dist_pow h0 h1)
/-
**Metric.nhds_basis_closedBall_pow** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：nhds_basis_closedBall_pow {r : Real} (h0 : 0 < r) (h1 : r < 1) : (𝓝 x).Has
Basis (fun _ => True) fun n : Nat => closedBall x (r ^ n)
参数：h0 : 0 < r；h1 : r < 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhds_basis_uniformity`：nhds_basis_uniformity {p : ι -> Prop} {s : ι -> S
etRel α α} (h : (𝓤 α).HasBasis p s) {x : α} : (𝓝 x).HasBasis p fun i => { y | (y
, x) in s i…
· 使用定理 `Metric.uniformity_basis_dist_le_pow`：uniformity_basis_dist_le_pow {r : R
eal} (h0 : 0 < r) (h1 : r < 1) : (𝓤 α).HasBasis (fun _ : Nat => True) fun n : Na
t => { p : α × α | dist p…
-/
theorem nhds_basis_closedBall_pow {r : ℝ} (h0 : 0 < r) (h1 : r < 1) :
    (𝓝 x).HasBasis (fun _ => True) fun n : ℕ => closedBall x (r ^ n) :=
  nhds_basis_uniformity (uniformity_basis_dist_le_pow h0 h1)
/-
**Metric.isOpen_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：isOpen_iff : IsOpen s ↔ forall x in s, exists ε > 0, ball x ε subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isOpen_iff : IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ball x ε ⊆ s := by
  simp only [isOpen_iff_mem_nhds, mem_nhds_iff]
/-
**Metric.isOpen_ball** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：∀ {α : Type u} [inst : PseudoMetricSpace α] {x : α} {ε : ℝ}, IsOpen (Metri
c.ball x ε)
参数：Metric.ball x ε。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.isOpen_iff`：isOpen_iff : IsOpen s ↔ forall x in s, exists ε > 0, 
ball x ε subseteq s
· 使用定理 `Metric.exists_ball_subset_ball`：exists_ball_subset_ball (h : y in ball x
 ε) : exists ε' > 0, ball y ε' subseteq ball x ε
-/
@[simp] theorem isOpen_ball : IsOpen (ball x ε) :=
  isOpen_iff.2 fun _ => exists_ball_subset_ball
/-
**Metric.ball_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：ball_mem_nhds (x : α) {ε : Real} (ε0 : 0 < ε) : ball x ε in 𝓝 x
参数：x : α；ε0 : 0 < ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Metric.isOpen_ball`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x : α} 
{ε : ℝ}, IsOpen (Metric.ball x ε)
· 使用定理 `Metric.mem_ball_self`：mem_ball_self (h : 0 < ε) : x in ball x ε
-/
theorem ball_mem_nhds (x : α) {ε : ℝ} (ε0 : 0 < ε) : ball x ε ∈ 𝓝 x :=
  isOpen_ball.mem_nhds (mem_ball_self ε0)
/-
**Metric.closedBall_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：closedBall_mem_nhds (x : α) {ε : Real} (ε0 : 0 < ε) : closedBall x ε in 𝓝 
x
参数：x : α；ε0 : 0 < ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Metric.ball_mem_nhds`：ball_mem_nhds (x : α) {ε : Real} (ε0 : 0 < ε) : ba
ll x ε in 𝓝 x
· 使用定理 `Metric.ball_subset_closedBall`：ball_subset_closedBall : ball x ε subsete
q closedBall x ε
-/
theorem closedBall_mem_nhds (x : α) {ε : ℝ} (ε0 : 0 < ε) : closedBall x ε ∈ 𝓝 x :=
  mem_of_superset (ball_mem_nhds x ε0) ball_subset_closedBall
/-
**Metric.closedBall_mem_nhds_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：closedBall_mem_nhds_of_mem {x c : α} {ε : Real} (h : x in ball c ε) : clos
edBall c ε in 𝓝 x
参数：h : x in ball c ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Metric.isOpen_ball`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x : α} 
{ε : ℝ}, IsOpen (Metric.ball x ε)
· 使用定理 `Metric.ball_subset_closedBall`：ball_subset_closedBall : ball x ε subsete
q closedBall x ε
-/
theorem closedBall_mem_nhds_of_mem {x c : α} {ε : ℝ} (h : x ∈ ball c ε) : closedBall c ε ∈ 𝓝 x :=
  mem_of_superset (isOpen_ball.mem_nhds h) ball_subset_closedBall
/-
**Metric.nhdsWithin_basis_ball** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：nhdsWithin_basis_ball {s : Set α} : (𝓝[s] x).HasBasis (fun ε : Real => 0 <
 ε) fun ε => ball x ε inter s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhdsWithin_hasBasis`：nhdsWithin_hasBasis {ι : Sort*} {p : ι -> Prop} {s 
: ι -> Set α} {a : α} (h : (𝓝 a).HasBasis p s) (t : Set α) : (𝓝[t] a).HasBasis p
 fun i =>…
· 使用定理 `Metric.nhds_basis_ball`：nhds_basis_ball : (𝓝 x).HasBasis (0 < ·) (ball x
)
-/
theorem nhdsWithin_basis_ball {s : Set α} :
    (𝓝[s] x).HasBasis (fun ε : ℝ => 0 < ε) fun ε => ball x ε ∩ s :=
  nhdsWithin_hasBasis nhds_basis_ball s
/-
**Metric.mem_nhdsWithin_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：mem_nhdsWithin_iff {t : Set α} : s in 𝓝[t] x ↔ exists ε > 0, ball x ε inte
r t subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Metric.nhdsWithin_basis_ball`：nhdsWithin_basis_ball {s : Set α} : (𝓝[s] 
x).HasBasis (fun ε : Real => 0 < ε) fun ε => ball x ε inter s
-/
theorem mem_nhdsWithin_iff {t : Set α} : s ∈ 𝓝[t] x ↔ ∃ ε > 0, ball x ε ∩ t ⊆ s :=
  nhdsWithin_basis_ball.mem_iff
/-
**Metric.tendsto_nhdsWithin_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：tendsto_nhdsWithin_nhdsWithin [PseudoMetricSpace β] {t : Set β} {f : α -> 
β} {a b} : Tendsto f (𝓝[s] a) (𝓝[t] b) ↔ forall ε > 0, exists δ > 0, forall ⦃x :
 α⦄, x in s -> dist x a < δ -> f x in t ∧ dist (f x) b < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.HasBasis.tendsto_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Fil
ter β} {pb : ι' →…
· 使用定理 `Metric.nhdsWithin_basis_ball`：nhdsWithin_basis_ball {s : Set α} : (𝓝[s] 
x).HasBasis (fun ε : Real => 0 < ε) fun ε => ball x ε inter s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_nhdsWithin_nhdsWithin [PseudoMetricSpace β] {t : Set β} {f : α → β} {a b} :
    Tendsto f (𝓝[s] a) (𝓝[t] b) ↔
      ∀ ε > 0, ∃ δ > 0, ∀ ⦃x : α⦄, x ∈ s → dist x a < δ → f x ∈ t ∧ dist (f x) b < ε :=
  (nhdsWithin_basis_ball.tendsto_iff nhdsWithin_basis_ball).trans <| by
    simp only [inter_comm _ s, inter_comm _ t, mem_inter_iff, and_imp, gt_iff_lt, mem_ball]
/-
**Metric.tendsto_nhdsWithin_nhds** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：tendsto_nhdsWithin_nhds [PseudoMetricSpace β] {f : α -> β} {a b} : Tendsto
 f (𝓝[s] a) (𝓝 b) ↔ forall ε > 0, exists δ > 0, forall ⦃x : α⦄, x in s -> dist x
 a < δ -> dist (f x) b < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `Metric.tendsto_nhdsWithin_nhdsWithin`：tendsto_nhdsWithin_nhdsWithin [Pse
udoMetricSpace β] {t : Set β} {f : α -> β} {a b} : Tendsto f (𝓝[s] a) (𝓝[t] b) ↔
 forall ε > 0, exists δ > …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_nhdsWithin_nhds [PseudoMetricSpace β] {f : α → β} {a b} :
    Tendsto f (𝓝[s] a) (𝓝 b) ↔
      ∀ ε > 0, ∃ δ > 0, ∀ ⦃x : α⦄, x ∈ s → dist x a < δ → dist (f x) b < ε := by
  rw [← nhdsWithin_univ b, tendsto_nhdsWithin_nhdsWithin]
  simp only [mem_univ, true_and]
/-
**Metric.tendsto_nhds_nhds** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：tendsto_nhds_nhds [PseudoMetricSpace β] {f : α -> β} {a b} : Tendsto f (𝓝 
a) (𝓝 b) ↔ forall ε > 0, exists δ > 0, forall ⦃x : α⦄, dist x a < δ -> dist (f x
) b < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.tendsto_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Fil
ter β} {pb : ι' →…
· 使用定理 `Metric.nhds_basis_ball`：nhds_basis_ball : (𝓝 x).HasBasis (0 < ·) (ball x
)
-/
theorem tendsto_nhds_nhds [PseudoMetricSpace β] {f : α → β} {a b} :
    Tendsto f (𝓝 a) (𝓝 b) ↔ ∀ ε > 0, ∃ δ > 0, ∀ ⦃x : α⦄, dist x a < δ → dist (f x) b < ε :=
  nhds_basis_ball.tendsto_iff nhds_basis_ball
/-
**Metric.continuousAt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：continuousAt_iff [PseudoMetricSpace β] {f : α -> β} {a : α} : ContinuousAt
 f a ↔ forall ε > 0, exists δ > 0, forall ⦃x : α⦄, dist x a < δ -> dist (f x) (f
 a) < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSp
ace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (x : X),   ContinuousAt f x = F
ilter.T…
· 使用定理 `Metric.tendsto_nhds_nhds`：tendsto_nhds_nhds [PseudoMetricSpace β] {f : α
 -> β} {a b} : Tendsto f (𝓝 a) (𝓝 b) ↔ forall ε > 0, exists δ > 0, forall ⦃x : α
⦄, dist x a < …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem continuousAt_iff [PseudoMetricSpace β] {f : α → β} {a : α} :
    ContinuousAt f a ↔ ∀ ε > 0, ∃ δ > 0, ∀ ⦃x : α⦄, dist x a < δ → dist (f x) (f a) < ε := by
  rw [ContinuousAt, tendsto_nhds_nhds]
/-
**Metric.continuousWithinAt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：continuousWithinAt_iff [PseudoMetricSpace β] {f : α -> β} {a : α} {s : Set
 α} : ContinuousWithinAt f s a ↔ forall ε > 0, exists δ > 0, forall ⦃x : α⦄, x i
n s -> dist x a < δ -> dist (f x) (f a) < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousWithinAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (s : Set X)   (x : X), Co
ntinuousWithi…
· 使用定理 `Metric.tendsto_nhdsWithin_nhds`：tendsto_nhdsWithin_nhds [PseudoMetricSpa
ce β] {f : α -> β} {a b} : Tendsto f (𝓝[s] a) (𝓝 b) ↔ forall ε > 0, exists δ > 0
, forall ⦃x : α⦄, x …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem continuousWithinAt_iff [PseudoMetricSpace β] {f : α → β} {a : α} {s : Set α} :
    ContinuousWithinAt f s a ↔
      ∀ ε > 0, ∃ δ > 0, ∀ ⦃x : α⦄, x ∈ s → dist x a < δ → dist (f x) (f a) < ε := by
  rw [ContinuousWithinAt, tendsto_nhdsWithin_nhds]
/-
**Metric.continuousOn_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：continuousOn_iff [PseudoMetricSpace β] {f : α -> β} {s : Set α} : Continuo
usOn f s ↔ forall b in s, forall ε > 0, exists δ > 0, forall a in s, dist a b < 
δ -> dist (f a) (f b) < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem continuousOn_iff [PseudoMetricSpace β] {f : α → β} {s : Set α} :
    ContinuousOn f s ↔ ∀ b ∈ s, ∀ ε > 0, ∃ δ > 0, ∀ a ∈ s, dist a b < δ → dist (f a) (f b) < ε := by
  simp [ContinuousOn, continuousWithinAt_iff]
/-
**Metric.continuous_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：continuous_iff [PseudoMetricSpace β] {f : α -> β} : Continuous f ↔ forall 
b, forall ε > 0, exists δ > 0, forall a, dist a b < δ -> dist (f a) (f b) < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Metric.tendsto_nhds_nhds`：tendsto_nhds_nhds [PseudoMetricSpace β] {f : α
 -> β} {a b} : Tendsto f (𝓝 a) (𝓝 b) ↔ forall ε > 0, exists δ > 0, forall ⦃x : α
⦄, dist x a < …
-/
theorem continuous_iff [PseudoMetricSpace β] {f : α → β} :
    Continuous f ↔ ∀ b, ∀ ε > 0, ∃ δ > 0, ∀ a, dist a b < δ → dist (f a) (f b) < ε :=
  continuous_iff_continuousAt.trans <| forall_congr' fun _ => tendsto_nhds_nhds
/-
**Metric.tendsto_nhds** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：tendsto_nhds {f : Filter β} {u : β -> α} {a : α} : Tendsto u f (𝓝 a) ↔ for
all ε > 0, forallᶠ x in f, dist (u x) a < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `Metric.nhds_basis_ball`：nhds_basis_ball : (𝓝 x).HasBasis (0 < ·) (ball x
)
-/
theorem tendsto_nhds {f : Filter β} {u : β → α} {a : α} :
    Tendsto u f (𝓝 a) ↔ ∀ ε > 0, ∀ᶠ x in f, dist (u x) a < ε :=
  nhds_basis_ball.tendsto_right_iff
/-
**Metric.continuousAt_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：continuousAt_iff' [TopologicalSpace β] {f : β -> α} {b : β} : ContinuousAt
 f b ↔ forall ε > 0, forallᶠ x in 𝓝 b, dist (f x) (f b) < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSp
ace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (x : X),   ContinuousAt f x = F
ilter.T…
· 使用定理 `Metric.tendsto_nhds`：tendsto_nhds {f : Filter β} {u : β -> α} {a : α} : 
Tendsto u f (𝓝 a) ↔ forall ε > 0, forallᶠ x in f, dist (u x) a < ε
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem continuousAt_iff' [TopologicalSpace β] {f : β → α} {b : β} :
    ContinuousAt f b ↔ ∀ ε > 0, ∀ᶠ x in 𝓝 b, dist (f x) (f b) < ε := by
  rw [ContinuousAt, tendsto_nhds]
/-
**Metric.continuousWithinAt_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：continuousWithinAt_iff' [TopologicalSpace β] {f : β -> α} {b : β} {s : Set
 β} : ContinuousWithinAt f s b ↔ forall ε > 0, forallᶠ x in 𝓝[s] b, dist (f x) (
f b) < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousWithinAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (s : Set X)   (x : X), Co
ntinuousWithi…
· 使用定理 `Metric.tendsto_nhds`：tendsto_nhds {f : Filter β} {u : β -> α} {a : α} : 
Tendsto u f (𝓝 a) ↔ forall ε > 0, forallᶠ x in f, dist (u x) a < ε
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem continuousWithinAt_iff' [TopologicalSpace β] {f : β → α} {b : β} {s : Set β} :
    ContinuousWithinAt f s b ↔ ∀ ε > 0, ∀ᶠ x in 𝓝[s] b, dist (f x) (f b) < ε := by
  rw [ContinuousWithinAt, tendsto_nhds]
/-
**Metric.continuousOn_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：continuousOn_iff' [TopologicalSpace β] {f : β -> α} {s : Set β} : Continuo
usOn f s ↔ forall b in s, forall ε > 0, forallᶠ x in 𝓝[s] b, dist (f x) (f b) < 
ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem continuousOn_iff' [TopologicalSpace β] {f : β → α} {s : Set β} :
    ContinuousOn f s ↔ ∀ b ∈ s, ∀ ε > 0, ∀ᶠ x in 𝓝[s] b, dist (f x) (f b) < ε := by
  simp [ContinuousOn, continuousWithinAt_iff']
/-
**Metric.continuous_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：continuous_iff' [TopologicalSpace β] {f : β -> α} : Continuous f ↔ forall 
(a), forall ε > 0, forallᶠ x in 𝓝 a, dist (f x) (f a) < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Metric.tendsto_nhds`：tendsto_nhds {f : Filter β} {u : β -> α} {a : α} : 
Tendsto u f (𝓝 a) ↔ forall ε > 0, forallᶠ x in f, dist (u x) a < ε
-/
theorem continuous_iff' [TopologicalSpace β] {f : β → α} :
    Continuous f ↔ ∀ (a), ∀ ε > 0, ∀ᶠ x in 𝓝 a, dist (f x) (f a) < ε :=
  continuous_iff_continuousAt.trans <| forall_congr' fun _ => tendsto_nhds
/-
**Metric.tendsto_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：tendsto_atTop [Nonempty β] [SemilatticeSup β] {u : β -> α} {a : α} : Tends
to u atTop (𝓝 a) ↔ forall ε > 0, exists N, forall n >= N, dist (u n) a < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.HasBasis.tendsto_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Fil
ter β} {pb : ι' →…
· 使用定理 `Filter.atTop_basis`：atTop_basis [Nonempty α] : (@atTop α _).HasBasis (fu
n _ => True) Ici
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Metric.nhds_basis_ball`：nhds_basis_ball : (𝓝 x).HasBasis (0 < ·) (ball x
)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_atTop [Nonempty β] [SemilatticeSup β] {u : β → α} {a : α} :
    Tendsto u atTop (𝓝 a) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (u n) a < ε :=
  (atTop_basis.tendsto_iff nhds_basis_ball).trans <| by
    simp only [true_and, mem_ball, mem_Ici]

/-- A variant of `tendsto_atTop` that
uses `∃ N, ∀ n > N, ...` rather than `∃ N, ∀ n ≥ N, ...`
-/
/-
**Metric.tendsto_atTop'** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：tendsto_atTop' [Nonempty β] [SemilatticeSup β] [NoMaxOrder β] {u : β -> α}
 {a : α} : Tendsto u atTop (𝓝 a) ↔ forall ε > 0, exists N, forall n > N, dist (u
 n) a < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.HasBasis.tendsto_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Fil
ter β} {pb : ι' →…
· 使用引理 `Filter.atTop_basis_Ioi`：atTop_basis_Ioi [Nonempty α] [NoMaxOrder α] : (@
atTop α _).HasBasis (fun _ => True) Ioi
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Metric.nhds_basis_ball`：nhds_basis_ball : (𝓝 x).HasBasis (0 < ·) (ball x
)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A variant of `tendsto_atTop` that
uses `∃ N, ∀ n > N, ...` rather than `∃ N, ∀ n ≥ N, ...`
-/
theorem tendsto_atTop' [Nonempty β] [SemilatticeSup β] [NoMaxOrder β] {u : β → α} {a : α} :
    Tendsto u atTop (𝓝 a) ↔ ∀ ε > 0, ∃ N, ∀ n > N, dist (u n) a < ε :=
  (atTop_basis_Ioi.tendsto_iff nhds_basis_ball).trans <| by
    simp only [true_and, gt_iff_lt, mem_Ioi, mem_ball]
/-
**Metric.isOpen_singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：isOpen_singleton_iff {α : Type*} [PseudoMetricSpace α] {x : α} : IsOpen ({
x} : Set α) ↔ exists ε > 0, forall y, dist y x < ε -> y = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isOpen_singleton_iff {α : Type*} [PseudoMetricSpace α] {x : α} :
    IsOpen ({x} : Set α) ↔ ∃ ε > 0, ∀ y, dist y x < ε → y = x := by
  simp [isOpen_iff, subset_singleton_iff, mem_ball]
/-
**Metric._root_.Dense.exists_dist_lt** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Dense.exists_dist_lt {s : Set α} (hs : Dense s) (x : α) {ε : ℝ} (hε : 0 < ε) :
    ∃ y ∈ s, dist x y < ε := by
  have : (ball x ε).Nonempty := by simp [hε]
  simpa only [mem_ball'] using hs.exists_mem_open isOpen_ball this

nonrec theorem _root_.DenseRange.exists_dist_lt {β : Type*} {f : β → α} (hf : DenseRange f) (x : α)
    {ε : ℝ} (hε : 0 < ε) : ∃ y, dist x (f y) < ε :=
  exists_range_iff.1 (hf.exists_dist_lt x hε)

/-- (Pseudo) metric space has discrete `UniformSpace` structure
iff the distances between distinct points are uniformly bounded away from zero. -/
/-
**Metric.uniformSpace_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：∀ {α : Type u} [inst : PseudoMetricSpace α],   PseudoMetricSpace.toUniform
Space = ⊥ ↔ ∃ r, 0 < r ∧ Pairwise fun x1 x2 => r ≤ dist x1 x2
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.uniformSpace_eq_bot`：∀ {α : Type ua} {ι : Sort u_2} {p :
 ι → Prop} {s : ι → SetRel α α} {u : UniformSpace α},   (uniformity α).HasBasis 
p s → (u = ⊥ ↔ ∃ i, p i ∧…
· 使用定理 `Metric.uniformity_basis_dist`：uniformity_basis_dist : (𝓤 α).HasBasis (fu
n ε : Real => 0 < ε) fun ε => { p : α × α | dist p.1 p.2 < ε }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
(Pseudo) metric space has discrete `UniformSpace` structure
iff the distances between distinct points are uniformly bounded away from zero.
-/
protected lemma uniformSpace_eq_bot :
    ‹PseudoMetricSpace α›.toUniformSpace = ⊥ ↔
      ∃ r : ℝ, 0 < r ∧ Pairwise (r ≤ dist · · : α → α → Prop) := by
  simp only [uniformity_basis_dist.uniformSpace_eq_bot, mem_ofPred_eq, not_lt]

end Metric

open Metric

/-- If the distances between distinct points in a (pseudo) metric space
are uniformly bounded away from zero, then the space has discrete topology. -/
/-
**DiscreteTopology.of_forall_le_dist** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：DiscreteTopology.of_forall_le_dist {α} [PseudoMetricSpace α] {r : Real} (h
pos : 0 < r) (hr : Pairwise (r <= dist · · : α -> α -> Prop)) : DiscreteTopology
 α
参数：hpos : 0 < r；hr : Pairwise (r <= dist · · : α -> α -> Prop)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.uniformSpace_eq_bot`：∀ {α : Type u} [inst : PseudoMetricSpace α],
   PseudoMetricSpace.toUniformSpace = ⊥ ↔ ∃ r, 0 < r ∧ Pairwise fun x1 x2 => r ≤
 dist x1 x2
· 使用定理 `UniformSpace.toTopologicalSpace_bot`：toTopologicalSpace_bot : @UniformSp
ace.toTopologicalSpace α ⊥ = ⊥

--- 原说明 ---
If the distances between distinct points in a (pseudo) metric space
are uniformly bounded away from zero, then the space has discrete topology.
-/
lemma DiscreteTopology.of_forall_le_dist {α} [PseudoMetricSpace α] {r : ℝ} (hpos : 0 < r)
    (hr : Pairwise (r ≤ dist · · : α → α → Prop)) : DiscreteTopology α :=
  ⟨by rw [Metric.uniformSpace_eq_bot.2 ⟨r, hpos, hr⟩, UniformSpace.toTopologicalSpace_bot]⟩

/-! Instantiate a pseudometric space as a pseudoemetric space. Before we can state the instance,
we need to show that the uniform structure coming from the edistance and the
distance coincide. -/

/-
**Metric.uniformity_edist_aux** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Metric.uniformity_edist_aux {α} (d : α -> α -> Real>=0) : ⨅ ε > (0 : Real)
, 𝓟 { p : α × α | ↑(d p.1 p.2) < ε } = ⨅ ε > (0 : Real>=0∞), 𝓟 { p : α × α | ↑(d
 p.1 p.2) < ε }
参数：d : α -> α -> Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.lt_iff_exists_nnreal_btwn`：lt_iff_exists_nnreal_btwn : a < b ↔ e
xists r : Real>=0, a < r ∧ (r : Real>=0∞) < b
· 使用定理 `Filter.mem_iInf_of_mem`：mem_iInf_of_mem {f : ι -> Filter α} (i : ι) {s} 
(hs : s in f i) : s in ⨅ i, f i
· 使用定理 `ENNReal.coe_pos`：∀ {r : NNReal}, 0 < ↑r ↔ 0 < r
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_lt_coe`：∀ {r q : NNReal}, ↑r < ↑q ↔ r < q
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
Instantiate a pseudometric space as a pseudoemetric space. Before we can state t
he instance,
we need to show that the uniform structure coming from the edistance and the
distance coincide.
-/
theorem Metric.uniformity_edist_aux {α} (d : α → α → ℝ≥0) :
    ⨅ ε > (0 : ℝ), 𝓟 { p : α × α | ↑(d p.1 p.2) < ε } =
      ⨅ ε > (0 : ℝ≥0∞), 𝓟 { p : α × α | ↑(d p.1 p.2) < ε } := by
  simp only [le_antisymm_iff, le_iInf_iff, le_principal_iff]
  refine ⟨fun ε hε => ?_, fun ε hε => ?_⟩
  · rcases ENNReal.lt_iff_exists_nnreal_btwn.1 hε with ⟨ε', ε'0, ε'ε⟩
    refine mem_iInf_of_mem (ε' : ℝ) (mem_iInf_of_mem (ENNReal.coe_pos.1 ε'0) ?_)
    exact fun x hx => lt_trans (ENNReal.coe_lt_coe.2 hx) ε'ε
  · lift ε to ℝ≥0 using le_of_lt hε
    refine mem_iInf_of_mem (ε : ℝ≥0∞) (mem_iInf_of_mem (ENNReal.coe_pos.2 hε) ?_)
    exact fun _ => ENNReal.coe_lt_coe.1
/-
**Metric.uniformity_edist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Metric.uniformity_edist : 𝓤 α = ⨅ ε > 0, 𝓟 { p : α × α | edist p.1 p.2 < ε
 }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PseudoMetricSpace.uniformity_dist`：∀ {α : Type u} [self : PseudoMetricSp
ace α], uniformity α = ⨅ ε, ⨅ (_ : ε > 0), Filter.principal {p | dist p.1 p.2 < 
ε}
· 使用定理 `Metric.uniformity_edist_aux`：Metric.uniformity_edist_aux {α} (d : α -> α
 -> Real>=0) : ⨅ ε > (0 : Real), 𝓟 { p : α × α | ↑(d p.1 p.2) < ε } = ⨅ ε > (0 :
 Real>=0∞), 𝓟 { p…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `edist_nndist`：edist_nndist (x y : α) : edist x y = nndist x y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Metric.uniformity_edist : 𝓤 α = ⨅ ε > 0, 𝓟 { p : α × α | edist p.1 p.2 < ε } := by
  simp only [PseudoMetricSpace.uniformity_dist, dist_nndist, edist_nndist,
    Metric.uniformity_edist_aux]

-- see Note [lower instance priority]
/-- A pseudometric space induces a pseudoemetric space -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pseudometric space induces a pseudoemetric space
-/
instance (priority := 100) PseudoMetricSpace.toPseudoEMetricSpace : PseudoEMetricSpace α :=
  { ‹PseudoMetricSpace α› with
    edist_self := by simp [edist_dist]
    edist_comm := fun _ _ => by simp only [edist_dist, dist_comm]
    edist_triangle := fun x y z => by
      simp only [edist_dist, ← ENNReal.ofReal_add, dist_nonneg]
      rw [ENNReal.ofReal_le_ofReal_iff _]
      · exact dist_triangle _ _ _
      · simpa using add_le_add (dist_nonneg : 0 ≤ dist x y) dist_nonneg
    uniformity_edist := Metric.uniformity_edist }

/-- In a pseudometric space, an open ball of infinite radius is the whole space -/
/-
**Metric.eball_top_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Metric.eball_top_eq_univ (x : α) : eball x ∞ = Set.univ
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用定理 `edist_lt_top`：edist_lt_top {α : Type*} [PseudoMetricSpace α] (x y : α) :
 edist x y < ⊤

--- 原说明 ---
In a pseudometric space, an open ball of infinite radius is the whole space
-/
theorem Metric.eball_top_eq_univ (x : α) : eball x ∞ = Set.univ :=
  Set.eq_univ_iff_forall.mpr fun y => edist_lt_top y x

/-- Balls defined using the distance or the edistance coincide -/
@[simp]
/-
**Metric.eball_ofReal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Metric.eball_ofReal {x : α} {ε : Real} : eball x (.ofReal ε) = ball x ε
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `edist_dist`：edist_dist (x y : α) : edist x y = ENNReal.ofReal (dist x y)
· 使用定理 `ENNReal.ofReal_lt_ofReal_iff_of_nonneg`：ofReal_lt_ofReal_iff_of_nonneg {
p q : Real} (hp : 0 <= p) : ENNReal.ofReal p < ENNReal.ofReal q ↔ p < q
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y

--- 原说明 ---
Balls defined using the distance or the edistance coincide
-/
theorem Metric.eball_ofReal {x : α} {ε : ℝ} : eball x (.ofReal ε) = ball x ε := by
  ext y
  simp only [mem_eball, mem_ball, edist_dist]
  exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg

@[deprecated (since := "2026-01-24")]
alias Metric.emetric_ball := Metric.eball_ofReal

/-- Balls defined using the distance or the edistance coincide -/
@[simp]
/-
**Metric.eball_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Metric.eball_coe {x : α} {ε : Real>=0} : eball x ε = ball x ε
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Metric.eball_ofReal`：Metric.eball_ofReal {x : α} {ε : Real} : eball x (.
ofReal ε) = ball x ε
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ENNReal.ofReal_coe_nnreal`：∀ {p : NNReal}, ENNReal.ofReal ↑p = ↑p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Balls defined using the distance or the edistance coincide
-/
theorem Metric.eball_coe {x : α} {ε : ℝ≥0} : eball x ε = ball x ε := by
  rw [← eball_ofReal]
  simp

@[deprecated (since := "2026-01-24")]
alias Metric.emetric_ball_nnreal := Metric.eball_coe

/-- Closed balls defined using the distance or the edistance coincide -/
/-
**Metric.closedEBall_ofReal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Metric.closedEBall_ofReal {x : α} {ε : Real} (h : 0 <= ε) : closedEBall x 
(.ofReal ε) = closedBall x ε
参数：h : 0 <= ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `edist_le_ofReal`：edist_le_ofReal {x y : α} {r : Real} (hr : 0 <= r) : ed
ist x y <= ENNReal.ofReal r ↔ dist x y <= r
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Closed balls defined using the distance or the edistance coincide
-/
theorem Metric.closedEBall_ofReal {x : α} {ε : ℝ} (h : 0 ≤ ε) :
    closedEBall x (.ofReal ε) = closedBall x ε := by
  ext y; simp [edist_le_ofReal h]

@[deprecated (since := "2026-01-24")]
alias Metric.emetric_closedBall := Metric.closedEBall_ofReal

/-- Closed balls defined using the distance or the edistance coincide -/
@[simp]
/-
**Metric.closedEBall_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Metric.closedEBall_coe {x : α} {ε : Real>=0} : closedEBall x ε = closedBal
l x ε
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Metric.closedEBall_ofReal`：Metric.closedEBall_ofReal {x : α} {ε : Real} 
(h : 0 <= ε) : closedEBall x (.ofReal ε) = closedBall x ε
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `ENNReal.ofReal_coe_nnreal`：∀ {p : NNReal}, ENNReal.ofReal ↑p = ↑p

--- 原说明 ---
Closed balls defined using the distance or the edistance coincide
-/
theorem Metric.closedEBall_coe {x : α} {ε : ℝ≥0} :
    closedEBall x ε = closedBall x ε := by
  rw [← closedEBall_ofReal ε.coe_nonneg, ENNReal.ofReal_coe_nnreal]

@[deprecated (since := "2026-01-24")]
alias Metric.emetric_closedBall_nnreal := Metric.closedEBall_coe

@[simp]
/-
**Metric.eball_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Metric.eball_top (x : α) : eball x ⊤ = univ
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_univ_of_forall`：eq_univ_of_forall {s : Set α} : (forall x, x in s
) -> s = univ
· 使用定理 `edist_lt_top`：edist_lt_top {α : Type*} [PseudoMetricSpace α] (x y : α) :
 edist x y < ⊤
-/
theorem Metric.eball_top (x : α) : eball x ⊤ = univ :=
  eq_univ_of_forall fun _ => edist_lt_top _ _

@[deprecated (since := "2026-01-24")]
alias Metric.emetric_ball_top := Metric.eball_top

/-- Build a new pseudometric space from an old one where the bundled uniform structure is provably
(but typically non-definitionaly) equal to some given uniform structure.
See Note [forgetful inheritance].
See Note [reducible non-instances].
-/
/-
**PseudoMetricSpace.replaceUniformity** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：PseudoMetricSpace.replaceUniformity {α} [U : UniformSpace α] (m : PseudoMe
tricSpace α) (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace]) : PseudoMetricSpa
ce α
参数：m : PseudoMetricSpace α；H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace]。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PseudoMetricSpace.dist_self`：∀ {α : Type u} [self : PseudoMetricSpace α]
 (x : α), dist x x = 0
· 使用定理 `PseudoMetricSpace.dist_comm`：∀ {α : Type u} [self : PseudoMetricSpace α]
 (x y : α), dist x y = dist y x
· 使用定理 `PseudoMetricSpace.dist_triangle`：∀ {α : Type u} [self : PseudoMetricSpac
e α] (x y z : α), dist x z ≤ dist x y + dist y z
· 使用定理 `PseudoMetricSpace.edist_dist`：∀ {α : Type u} [self : PseudoMetricSpace α
] (x y : α), PseudoMetricSpace.edist x y = ENNReal.ofReal (dist x y)
· 使用定理 `PseudoMetricSpace.cobounded_sets`：∀ {α : Type u} [self : PseudoMetricSpa
ce α], (Bornology.cobounded α).sets = {s | ∃ C, ∀ x ∈ sᶜ, ∀ y ∈ sᶜ, dist x y ≤ C
}

--- 原说明 ---
Build a new pseudometric space from an old one where the bundled uniform structu
re is provably
(but typically non-definitionaly) equal to some given uniform structure.
See Note [forgetful inheritance].
See Note [reducible non-instances].
-/
abbrev PseudoMetricSpace.replaceUniformity {α} [U : UniformSpace α] (m : PseudoMetricSpace α)
    (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace]) : PseudoMetricSpace α :=
  { m with
    toUniformSpace := U
    uniformity_dist := H.trans PseudoMetricSpace.uniformity_dist }
/-
**PseudoMetricSpace.replaceUniformity_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PseudoMetricSpace.replaceUniformity_eq {α} [U : UniformSpace α] (m : Pseud
oMetricSpace α) (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace]) : m.replaceUni
formity H = m
参数：m : PseudoMetricSpace α；H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PseudoMetricSpace.ext`：PseudoMetricSpace.ext {α : Type*} {m m' : PseudoM
etricSpace α} (h : m.toDist = m'.toDist) : m = m'
· 使用定理 `Dist.ext`：∀ {α : Type u_3} {x y : Dist α}, dist = dist → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem PseudoMetricSpace.replaceUniformity_eq {α} [U : UniformSpace α] (m : PseudoMetricSpace α)
    (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace]) : m.replaceUniformity H = m := by
  ext
  rfl

-- ensure that the bornology is unchanged when replacing the uniformity.
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example {α} [U : UniformSpace α] (m : PseudoMetricSpace α)
    (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace]) :
    (PseudoMetricSpace.replaceUniformity m H).toBornology = m.toBornology := by
  with_reducible_and_instances rfl

/-- Build a new pseudometric space from an old one where the bundled topological structure is
provably (but typically non-definitionaly) equal to some given topological structure.
See Note [forgetful inheritance].
See Note [reducible non-instances].
-/
/-
**PseudoMetricSpace.replaceTopology** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：PseudoMetricSpace.replaceTopology {γ} [U : TopologicalSpace γ] (m : Pseudo
MetricSpace γ) (H : U = m.toUniformSpace.toTopologicalSpace) : PseudoMetricSpace
 γ
参数：m : PseudoMetricSpace γ；H : U = m.toUniformSpace.toTopologicalSpace。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Build a new pseudometric space from an old one where the bundled topological str
ucture is
provably (but typically non-definitionaly) equal to some given topological struc
ture.
See Note [forgetful inheritance].
See Note [reducible non-instances].
-/
abbrev PseudoMetricSpace.replaceTopology {γ} [U : TopologicalSpace γ] (m : PseudoMetricSpace γ)
    (H : U = m.toUniformSpace.toTopologicalSpace) : PseudoMetricSpace γ :=
  @PseudoMetricSpace.replaceUniformity γ (m.toUniformSpace.replaceTopology H) m rfl
/-
**PseudoMetricSpace.replaceTopology_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PseudoMetricSpace.replaceTopology_eq {γ} [U : TopologicalSpace γ] (m : Pse
udoMetricSpace γ) (H : U = m.toUniformSpace.toTopologicalSpace) : m.replaceTopol
ogy H = m
参数：m : PseudoMetricSpace γ；H : U = m.toUniformSpace.toTopologicalSpace。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PseudoMetricSpace.ext`：PseudoMetricSpace.ext {α : Type*} {m m' : PseudoM
etricSpace α} (h : m.toDist = m'.toDist) : m = m'
· 使用定理 `Dist.ext`：∀ {α : Type u_3} {x y : Dist α}, dist = dist → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem PseudoMetricSpace.replaceTopology_eq {γ} [U : TopologicalSpace γ] (m : PseudoMetricSpace γ)
    (H : U = m.toUniformSpace.toTopologicalSpace) : m.replaceTopology H = m := by
  ext
  rfl

/-- One gets a pseudometric space from an emetric space if the edistance
is everywhere finite, by pushing the edistance to reals. We set it up so that the edist and the
uniformity are defeq in the pseudometric space and the pseudoemetric space. In this definition, the
distance is given separately, to be able to prescribe some expression which is not defeq to the
push-forward of the edistance to reals. See note [reducible non-instances]. -/
/-
**PseudoEMetricSpace.toPseudoMetricSpaceOfDist** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：PseudoEMetricSpace.toPseudoMetricSpaceOfDist {X : Type*} [e : PseudoEMetri
cSpace X] (dist : X -> X -> Real) (dist_nonneg : forall x y, 0 <= dist x y) (h :
 forall x y, edist x y = .ofReal (dist x y)) : PseudoMetricSpace X where dist
参数：dist : X -> X -> Real；dist_nonneg : forall x y, 0 <= dist x y；h : forall x y,
 edist x y = .ofReal (dist x y)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
One gets a pseudometric space from an emetric space if the edistance
is everywhere finite, by pushing the edistance to reals. We set it up so that th
e edist and the
uniformity are defeq in the pseudometric space and the pseudoemetric space. In t
his definition, the
distance is given separately, to be able to prescribe some expression which is n
ot defeq to the
push-forward of the edistance to reals. See note [reducible non-instances].
-/
abbrev PseudoEMetricSpace.toPseudoMetricSpaceOfDist {X : Type*} [e : PseudoEMetricSpace X]
    (dist : X → X → ℝ) (dist_nonneg : ∀ x y, 0 ≤ dist x y)
    (h : ∀ x y, edist x y = .ofReal (dist x y)) : PseudoMetricSpace X where
  dist := dist
  dist_self x := by simpa [h, (dist_nonneg _ _).ge_iff_eq', -edist_self] using edist_self x
  dist_comm x y := by simpa [h, dist_nonneg] using edist_comm x y
  dist_triangle x y z := by
    simpa [h, dist_nonneg, add_nonneg, ← ENNReal.ofReal_add] using edist_triangle x y z
  edist := edist
  edist_dist _ _ := by simp only [h]
  toUniformSpace := PseudoEMetricSpace.toUniformSpace
  uniformity_dist := e.uniformity_edist.trans <| by
    simpa [h, dist_nonneg, ENNReal.coe_toNNReal_eq_toReal]
      using (Metric.uniformity_edist_aux fun x y : X => (edist x y).toNNReal).symm

/-- One gets a pseudometric space from an emetric space if the edistance
is everywhere finite, by pushing the edistance to reals. We set it up so that the edist and the
uniformity are defeq in the pseudometric space and the emetric space. -/
/-
**PseudoEMetricSpace.toPseudoMetricSpace** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：PseudoEMetricSpace.toPseudoMetricSpace {α : Type u} [PseudoEMetricSpace α]
 (h : forall x y : α, edist x y != ⊤) : PseudoMetricSpace α
参数：h : forall x y : α, edist x y != ⊤。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
One gets a pseudometric space from an emetric space if the edistance
is everywhere finite, by pushing the edistance to reals. We set it up so that th
e edist and the
uniformity are defeq in the pseudometric space and the emetric space.
-/
abbrev PseudoEMetricSpace.toPseudoMetricSpace {α : Type u} [PseudoEMetricSpace α]
    (h : ∀ x y : α, edist x y ≠ ⊤) : PseudoMetricSpace α :=
  PseudoEMetricSpace.toPseudoMetricSpaceOfDist (ENNReal.toReal <| edist · ·) (by simp) (by simp [h])

/-- Build a new pseudometric space from an old one where the bundled bornology structure is provably
(but typically non-definitionaly) equal to some given bornology structure.
See Note [forgetful inheritance].
See Note [reducible non-instances].
-/
/-
**PseudoMetricSpace.replaceBornology** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：PseudoMetricSpace.replaceBornology {α} [B : Bornology α] (m : PseudoMetric
Space α) (H : forall s, @IsBounded _ B s ↔ @IsBounded _ PseudoMetricSpace.toBorn
ology s) : PseudoMetricSpace α
参数：m : PseudoMetricSpace α；H : forall s, @IsBounded _ B s ↔ @IsBounded _ PseudoM
etricSpace.toBornology s。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PseudoMetricSpace.dist_self`：∀ {α : Type u} [self : PseudoMetricSpace α]
 (x : α), dist x x = 0
· 使用定理 `PseudoMetricSpace.dist_comm`：∀ {α : Type u} [self : PseudoMetricSpace α]
 (x y : α), dist x y = dist y x
· 使用定理 `PseudoMetricSpace.dist_triangle`：∀ {α : Type u} [self : PseudoMetricSpac
e α] (x y z : α), dist x z ≤ dist x y + dist y z
· 使用定理 `PseudoMetricSpace.edist_dist`：∀ {α : Type u} [self : PseudoMetricSpace α
] (x y : α), PseudoMetricSpace.edist x y = ENNReal.ofReal (dist x y)
· 使用定理 `PseudoMetricSpace.uniformity_dist`：∀ {α : Type u} [self : PseudoMetricSp
ace α], uniformity α = ⨅ ε, ⨅ (_ : ε > 0), Filter.principal {p | dist p.1 p.2 < 
ε}

--- 原说明 ---
Build a new pseudometric space from an old one where the bundled bornology struc
ture is provably
(but typically non-definitionaly) equal to some given bornology structure.
See Note [forgetful inheritance].
See Note [reducible non-instances].
-/
abbrev PseudoMetricSpace.replaceBornology {α} [B : Bornology α] (m : PseudoMetricSpace α)
    (H : ∀ s, @IsBounded _ B s ↔ @IsBounded _ PseudoMetricSpace.toBornology s) :
    PseudoMetricSpace α :=
  { m with
    toBornology := B
    cobounded_sets := Set.ext <| compl_surjective.forall.2 fun s =>
        (H s).trans <| by rw [isBounded_iff, mem_ofPred_eq, compl_compl] }
/-
**PseudoMetricSpace.replaceBornology_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PseudoMetricSpace.replaceBornology_eq {α} [m : PseudoMetricSpace α] [B : B
ornology α] (H : forall s, @IsBounded _ B s ↔ @IsBounded _ PseudoMetricSpace.toB
ornology s) : PseudoMetricSpace.replaceBornology _ H = m
参数：H : forall s, @IsBounded _ B s ↔ @IsBounded _ PseudoMetricSpace.toBornology s
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PseudoMetricSpace.ext`：PseudoMetricSpace.ext {α : Type*} {m m' : PseudoM
etricSpace α} (h : m.toDist = m'.toDist) : m = m'
· 使用定理 `Dist.ext`：∀ {α : Type u_3} {x y : Dist α}, dist = dist → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem PseudoMetricSpace.replaceBornology_eq {α} [m : PseudoMetricSpace α] [B : Bornology α]
    (H : ∀ s, @IsBounded _ B s ↔ @IsBounded _ PseudoMetricSpace.toBornology s) :
    PseudoMetricSpace.replaceBornology _ H = m := by
  ext
  rfl

-- ensure that the uniformity is unchanged when replacing the bornology.
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example {α} [B : Bornology α] (m : PseudoMetricSpace α)
    (H : ∀ s, @IsBounded _ B s ↔ @IsBounded _ PseudoMetricSpace.toBornology s) :
    (PseudoMetricSpace.replaceBornology m H).toUniformSpace = m.toUniformSpace := by
  with_reducible_and_instances rfl

section Real

/-- Instantiate the reals as a pseudometric space. -/
/-
**Real.pseudoMetricSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Real.pseudoMetricSpace : PseudoMetricSpace Real where dist x y
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `abs_sub_comm`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] 
(a b : α), |a - b| = |b - a|
· 使用定理 `abs_sub_le`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrd
er G] [IsOrderedAddMonoid G] (a b c : G),   |a - c| ≤ |a - b| + |b - c|

--- 原说明 ---
Instantiate the reals as a pseudometric space.
-/
instance Real.pseudoMetricSpace : PseudoMetricSpace ℝ where
  dist x y := |x - y|
  dist_self := by simp [abs_zero]
  dist_comm _ _ := abs_sub_comm _ _
  dist_triangle _ _ _ := abs_sub_le _ _ _
/-
**Real.dist_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.dist_eq (x y : Real) : dist x y = |x - y|
参数：x y : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Real.dist_eq (x y : ℝ) : dist x y = |x - y| := rfl
/-
**Real.nndist_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.nndist_eq (x y : Real) : nndist x y = Real.nnabs (x - y)
参数：x y : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Real.nndist_eq (x y : ℝ) : nndist x y = Real.nnabs (x - y) := rfl
/-
**Real.nndist_eq'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.nndist_eq' (x y : Real) : nndist x y = Real.nnabs (y - x)
参数：x y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nndist_comm`：nndist_comm (x y : α) : nndist x y = nndist y x
-/
theorem Real.nndist_eq' (x y : ℝ) : nndist x y = Real.nnabs (y - x) :=
  nndist_comm _ _
/-
**Real.dist_0_eq_abs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.dist_0_eq_abs (x : Real) : dist x 0 = |x|
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Real.dist_0_eq_abs (x : ℝ) : dist x 0 = |x| := by simp [Real.dist_eq]
/-
**Real.sub_le_dist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.sub_le_dist (x y : Real) : x - y <= dist x y
参数：x y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.dist_eq`：Real.dist_eq (x y : Real) : dist x y = |x - y|
· 使用定理 `le_abs`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] {a
 b : α}, a ≤ |b| ↔ a ≤ b ∨ a ≤ -b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem Real.sub_le_dist (x y : ℝ) : x - y ≤ dist x y := by
  rw [Real.dist_eq, le_abs]
  exact Or.inl (le_refl _)
/-
**Real.ball_eq_Ioo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.ball_eq_Ioo (x r : Real) : ball x r = Ioo (x - r) (x + r)
参数：x r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.mem_ball`：mem_ball : y in ball x ε ↔ dist y x < ε
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `Real.dist_eq`：Real.dist_eq (x y : Real) : dist x y = |x - y|
· 使用定理 `abs_sub_lt_iff`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : Linea
rOrder G] [IsOrderedAddMonoid G] {a b c : G},   |a - b| < c ↔ a - b < c ∧ b - a 
< c
· 使用定理 `Set.mem_Ioo`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
oo a b ↔ a < x ∧ x < b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_lt_iff_lt_add'`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : LT 
α] [AddLeftStrictMono α] {a b c : α}, a - b < c ↔ a < b + c
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `sub_lt_comm`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : LT α] [Add
LeftStrictMono α] {a b c : α}, a - b < c ↔ a - c < b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Real.ball_eq_Ioo (x r : ℝ) : ball x r = Ioo (x - r) (x + r) :=
  Set.ext fun y => by
    rw [mem_ball, dist_comm, Real.dist_eq, abs_sub_lt_iff, mem_Ioo, ← sub_lt_iff_lt_add',
      sub_lt_comm]
/-
**Real.ball_zero_eq_Ioo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.ball_zero_eq_Ioo (r : Real) : ball 0 r = Ioo (-r) r
参数：r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.ball_eq_Ioo`：Real.ball_eq_Ioo (x r : Real) : ball x r = Ioo (x - r)
 (x + r)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Real.ball_zero_eq_Ioo (r : ℝ) : ball 0 r = Ioo (-r) r := by
  simp [Real.ball_eq_Ioo]
/-
**Real.closedBall_eq_Icc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.closedBall_eq_Icc {x r : Real} : closedBall x r = Icc (x - r) (x + r)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.mem_closedBall`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x y 
: α} {ε : ℝ}, y ∈ Metric.closedBall x ε ↔ dist y x ≤ ε
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `Real.dist_eq`：Real.dist_eq (x y : Real) : dist x y = |x - y|
· 使用定理 `abs_sub_le_iff`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : Linea
rOrder G] [IsOrderedAddMonoid G] {a b c : G},   |a - b| ≤ c ↔ a - b ≤ c ∧ b - a 
≤ c
· 使用定理 `Set.mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
cc a b ↔ a ≤ x ∧ x ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_le_iff_le_add'`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : LE 
α] [AddLeftMono α] {a b c : α}, a - b ≤ c ↔ a ≤ b + c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `sub_le_comm`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : LE α] [Add
LeftMono α] {a b c : α}, a - b ≤ c ↔ a - c ≤ b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Real.closedBall_eq_Icc {x r : ℝ} : closedBall x r = Icc (x - r) (x + r) := by
  ext y
  rw [mem_closedBall, dist_comm, Real.dist_eq, abs_sub_le_iff, mem_Icc, ← sub_le_iff_le_add',
    sub_le_comm]
/-
**Real.closedBall_zero_eq_Icc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.closedBall_zero_eq_Icc (r : Real) : closedBall 0 r = Icc (-r) r
参数：r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.closedBall_eq_Icc`：Real.closedBall_eq_Icc {x r : Real} : closedBall
 x r = Icc (x - r) (x + r)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Real.closedBall_zero_eq_Icc (r : ℝ) : closedBall 0 r = Icc (-r) r := by
  simp [Real.closedBall_eq_Icc]
/-
**Real.Ioo_eq_ball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.Ioo_eq_ball (x y : Real) : Ioo x y = ball ((x + y) / 2) ((y - x) / 2)
参数：x y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.ball_eq_Ioo`：Real.ball_eq_Ioo (x r : Real) : ball x r = Ioo (x - r)
 (x + r)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_div`：sub_div (a b c : K) : (a - b) / c = a / c - b / c
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `sub_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b + c = a - (b - c)
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `add_self_div_two`：∀ {K : Type u_1} [inst : DivisionSemiring K] [NeZero 2
] (a : K), (a + a) / 2 = a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
-/
theorem Real.Ioo_eq_ball (x y : ℝ) : Ioo x y = ball ((x + y) / 2) ((y - x) / 2) := by
  rw [Real.ball_eq_Ioo, ← sub_div, add_comm, ← sub_add, add_sub_cancel_left, add_self_div_two,
    ← add_div, add_assoc, add_sub_cancel, add_self_div_two]
/-
**Real.Icc_eq_closedBall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.Icc_eq_closedBall (x y : Real) : Icc x y = closedBall ((x + y) / 2) (
(y - x) / 2)
参数：x y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.closedBall_eq_Icc`：Real.closedBall_eq_Icc {x r : Real} : closedBall
 x r = Icc (x - r) (x + r)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_div`：sub_div (a b c : K) : (a - b) / c = a / c - b / c
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `sub_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b + c = a - (b - c)
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `add_self_div_two`：∀ {K : Type u_1} [inst : DivisionSemiring K] [NeZero 2
] (a : K), (a + a) / 2 = a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
-/
theorem Real.Icc_eq_closedBall (x y : ℝ) : Icc x y = closedBall ((x + y) / 2) ((y - x) / 2) := by
  rw [Real.closedBall_eq_Icc, ← sub_div, add_comm, ← sub_add, add_sub_cancel_left, add_self_div_two,
    ← add_div, add_assoc, add_sub_cancel, add_self_div_two]
/-
**Real.sphere_eq_pair** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Real.sphere_eq_pair (x : Real) {r : Real} (hr : 0 <= r) : sphere x r = {x 
- r, x + r}
参数：x : Real；hr : 0 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma Real.sphere_eq_pair (x : ℝ) {r : ℝ} (hr : 0 ≤ r) : sphere x r = {x - r, x + r} := by
  ext; simp [dist_eq]; grind
/-
**Metric.uniformity_eq_comap_nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Metric.uniformity_eq_comap_nhds_zero : 𝓤 α = comap (fun p : α × α => dist 
p.1 p.2) (𝓝 (0 : Real))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
· 使用定理 `Metric.nhds_basis_ball`：nhds_basis_ball : (𝓝 x).HasBasis (0 < ·) (ball x
)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Real.dist_0_eq_abs`：Real.dist_0_eq_abs (x : Real) : dist x 0 = |x|
· 使用定理 `abs_dist`：∀ {α : Type u} [inst : PseudoMetricSpace α] {a b : α}, |dist a
 b| = dist a b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Metric.uniformity_eq_comap_nhds_zero :
    𝓤 α = comap (fun p : α × α => dist p.1 p.2) (𝓝 (0 : ℝ)) := by
  ext s
  simp only [mem_uniformity_dist, (nhds_basis_ball.comap _).mem_iff]
  simp [subset_def, Real.dist_0_eq_abs]
/-
**tendsto_uniformity_iff_dist_tendsto_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_uniformity_iff_dist_tendsto_zero {f : ι -> α × α} {p : Filter ι} :
 Tendsto f p (𝓤 α) ↔ Tendsto (fun x => dist (f x).1 (f x).2) p (𝓝 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.uniformity_eq_comap_nhds_zero`：Metric.uniformity_eq_comap_nhds_ze
ro : 𝓤 α = comap (fun p : α × α => dist p.1 p.2) (𝓝 (0 : Real))
· 使用定理 `Filter.tendsto_comap_iff`：tendsto_comap_iff {f : α -> β} {g : β -> γ} {a
 : Filter α} {c : Filter γ} : Tendsto f a (c.comap g) ↔ Tendsto (g ∘ f) a c
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tendsto_uniformity_iff_dist_tendsto_zero {f : ι → α × α} {p : Filter ι} :
    Tendsto f p (𝓤 α) ↔ Tendsto (fun x => dist (f x).1 (f x).2) p (𝓝 0) := by
  rw [Metric.uniformity_eq_comap_nhds_zero, tendsto_comap_iff, Function.comp_def]
/-
**Filter.Tendsto.congr_dist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.congr_dist {f₁ f₂ : ι -> α} {p : Filter ι} {a : α} (h₁ : Te
ndsto f₁ p (𝓝 a)) (h : Tendsto (fun x => dist (f₁ x) (f₂ x)) p (𝓝 0)) : Tendsto 
f₂ p (𝓝 a)
参数：h₁ : Tendsto f₁ p (𝓝 a)；h : Tendsto (fun x => dist (f₁ x) (f₂ x)) p (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.congr_uniformity`：Filter.Tendsto.congr_uniformity {α β} [
UniformSpace β] {f g : α -> β} {l : Filter α} {b : β} (hf : Tendsto f l (𝓝 b)) (
hg : Tendsto (fun x =…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_uniformity_iff_dist_tendsto_zero`：tendsto_uniformity_iff_dist_te
ndsto_zero {f : ι -> α × α} {p : Filter ι} : Tendsto f p (𝓤 α) ↔ Tendsto (fun x 
=> dist (f x).1 (f x).2) p (𝓝 …
-/
theorem Filter.Tendsto.congr_dist {f₁ f₂ : ι → α} {p : Filter ι} {a : α}
    (h₁ : Tendsto f₁ p (𝓝 a)) (h : Tendsto (fun x => dist (f₁ x) (f₂ x)) p (𝓝 0)) :
    Tendsto f₂ p (𝓝 a) :=
  h₁.congr_uniformity <| tendsto_uniformity_iff_dist_tendsto_zero.2 h

alias tendsto_of_tendsto_of_dist := Filter.Tendsto.congr_dist
/-
**tendsto_iff_of_dist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_iff_of_dist {f₁ f₂ : ι -> α} {p : Filter ι} {a : α} (h : Tendsto (
fun x => dist (f₁ x) (f₂ x)) p (𝓝 0)) : Tendsto f₁ p (𝓝 a) ↔ Tendsto f₂ p (𝓝 a)
参数：h : Tendsto (fun x => dist (f₁ x) (f₂ x)) p (𝓝 0)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Uniform.tendsto_congr`：Uniform.tendsto_congr {α β} [UniformSpace β] {f g
 : α -> β} {l : Filter α} {b : β} (hfg : Tendsto (fun x => (f x, g x)) l (𝓤 β)) 
: Tendsto f…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_uniformity_iff_dist_tendsto_zero`：tendsto_uniformity_iff_dist_te
ndsto_zero {f : ι -> α × α} {p : Filter ι} : Tendsto f p (𝓤 α) ↔ Tendsto (fun x 
=> dist (f x).1 (f x).2) p (𝓝 …
-/
theorem tendsto_iff_of_dist {f₁ f₂ : ι → α} {p : Filter ι} {a : α}
    (h : Tendsto (fun x => dist (f₁ x) (f₂ x)) p (𝓝 0)) : Tendsto f₁ p (𝓝 a) ↔ Tendsto f₂ p (𝓝 a) :=
  Uniform.tendsto_congr <| tendsto_uniformity_iff_dist_tendsto_zero.2 h

end Real

/-
**PseudoMetricSpace.dist_eq_of_dist_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PseudoMetricSpace.dist_eq_of_dist_zero (x : α) {y z : α} (h : dist y z = 0
) : dist x y = dist x z
参数：x : α；h : dist y z = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `abs_nonpos_iff`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrd
er α] [AddLeftMono α] {a : α} [AddRightMono α], |a| ≤ 0 ↔ a = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `abs_dist_sub_le`：abs_dist_sub_le (x y z : α) : |dist x z - dist y z| <= 
dist x y
· 使用定理 `PseudoMetricSpace.dist_comm`：∀ {α : Type u} [self : PseudoMetricSpace α]
 (x y : α), dist x y = dist y x
-/
theorem PseudoMetricSpace.dist_eq_of_dist_zero (x : α) {y z : α} (h : dist y z = 0) :
    dist x y = dist x z :=
  dist_comm y x ▸ dist_comm z x ▸ sub_eq_zero.1 (abs_nonpos_iff.1 (h ▸ abs_dist_sub_le y z x))
/-
**dist_dist_dist_le_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_dist_dist_le_left (x y z : α) : dist (dist x z) (dist y z) <= dist x 
y
参数：x y z : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `abs_dist_sub_le`：abs_dist_sub_le (x y z : α) : |dist x z - dist y z| <= 
dist x y
-/
theorem dist_dist_dist_le_left (x y z : α) : dist (dist x z) (dist y z) ≤ dist x y :=
  abs_dist_sub_le ..
/-
**dist_dist_dist_le_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_dist_dist_le_right (x y z : α) : dist (dist x y) (dist x z) <= dist y
 z
参数：x y z : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `dist_dist_dist_le_left`：dist_dist_dist_le_left (x y z : α) : dist (dist 
x z) (dist y z) <= dist x y
-/
theorem dist_dist_dist_le_right (x y z : α) : dist (dist x y) (dist x z) ≤ dist y z := by
  simpa only [dist_comm x] using dist_dist_dist_le_left y z x
/-
**dist_dist_dist_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_dist_dist_le (x y x' y' : α) : dist (dist x y) (dist x' y') <= dist x
 x' + dist y y'
参数：x y x' y' : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `dist_triangle`：dist_triangle (x y z : α) : dist x z <= dist x y + dist y
 z
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `dist_dist_dist_le_left`：dist_dist_dist_le_left (x y z : α) : dist (dist 
x z) (dist y z) <= dist x y
· 使用定理 `dist_dist_dist_le_right`：dist_dist_dist_le_right (x y z : α) : dist (dis
t x y) (dist x z) <= dist y z
-/
theorem dist_dist_dist_le (x y x' y' : α) : dist (dist x y) (dist x' y') ≤ dist x x' + dist y y' :=
  (dist_triangle _ _ _).trans <|
    add_le_add (dist_dist_dist_le_left _ _ _) (dist_dist_dist_le_right _ _ _)
/-
**nhds_comap_dist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_comap_dist (a : α) : ((𝓝 (0 : Real)).comap (dist · a)) = 𝓝 a
参数：a : α。
该定理/引理给出了一组等式。
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
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `nhds_eq_comap_uniformity`：nhds_eq_comap_uniformity {x : α} : 𝓝 x = (𝓤 α)
.comap (Prod.mk x)
· 使用定理 `Metric.uniformity_eq_comap_nhds_zero`：Metric.uniformity_eq_comap_nhds_ze
ro : 𝓤 α = comap (fun p : α × α => dist p.1 p.2) (𝓝 (0 : Real))
· 使用定理 `Filter.comap_comap`：comap_comap {m : γ -> β} {n : β -> α} : comap m (com
ap n f) = comap (n ∘ m) f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nhds_comap_dist (a : α) : ((𝓝 (0 : ℝ)).comap (dist · a)) = 𝓝 a := by
  simp only [@nhds_eq_comap_uniformity α, Metric.uniformity_eq_comap_nhds_zero, comap_comap,
    Function.comp_def, dist_comm]
/-
**tendsto_iff_dist_tendsto_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_iff_dist_tendsto_zero {f : β -> α} {x : Filter β} {a : α} : Tendst
o f x (𝓝 a) ↔ Tendsto (fun b => dist (f b) a) x (𝓝 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhds_comap_dist`：nhds_comap_dist (a : α) : ((𝓝 (0 : Real)).comap (dist ·
 a)) = 𝓝 a
· 使用定理 `Filter.tendsto_comap_iff`：tendsto_comap_iff {f : α -> β} {g : β -> γ} {a
 : Filter α} {c : Filter γ} : Tendsto f a (c.comap g) ↔ Tendsto (g ∘ f) a c
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tendsto_iff_dist_tendsto_zero {f : β → α} {x : Filter β} {a : α} :
    Tendsto f x (𝓝 a) ↔ Tendsto (fun b => dist (f b) a) x (𝓝 0) := by
  rw [← nhds_comap_dist a, tendsto_comap_iff, Function.comp_def]

namespace Metric

variable {x y z : α} {ε ε₁ ε₂ : ℝ} {s : Set α}

/-- If `f` is a positive radius tending to zero, then the sets of pairs with distance less than
`f i` form a basis of the uniformity. -/
/-
**Metric.mk_uniformity_basis_of_tendsto** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：mk_uniformity_basis_of_tendsto {β : Type*} {p : β -> Prop} {f : β -> Real}
 {l : Filter β} [l.NeBot] (hf₀ : forall i, p i -> 0 < f i) (hf₁ : forallᶠ i in l
, p i) (hf : Tendsto f l (𝓝 0)) : (𝓤 α).HasBasis p fun i => {x | dist x.1 x.2 < 
f i}
参数：hf₀ : forall i, p i -> 0 < f i；hf₁ : forallᶠ i in l, p i；hf : Tendsto f l (𝓝 
0)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.mk_uniformity_basis`：∀ {α : Type u} [inst : PseudoMetricSpace α] 
{β : Type u_3} {p : β → Prop} {f : β → ℝ},   (∀ (i : β), p i → 0 < f i) →     (∀
 ⦃ε : ℝ⦄, 0 < ε …
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `and_imp`：∀ {a b c : Prop}, a ∧ b → c ↔ a → b → c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `Metric.nhds_basis_closedBall`：nhds_basis_closedBall : (𝓝 x).HasBasis (fu
n ε : Real => 0 < ε) (closedBall x)

--- 原说明 ---
If `f` is a positive radius tending to zero, then the sets of pairs with distanc
e less than
`f i` form a basis of the uniformity.
-/
lemma mk_uniformity_basis_of_tendsto {β : Type*} {p : β → Prop} {f : β → ℝ}
    {l : Filter β} [l.NeBot] (hf₀ : ∀ i, p i → 0 < f i) (hf₁ : ∀ᶠ i in l, p i)
    (hf : Tendsto f l (𝓝 0)) :
    (𝓤 α).HasBasis p fun i ↦ {x | dist x.1 x.2 < f i} := by
  apply Metric.mk_uniformity_basis hf₀
  rw [nhds_basis_closedBall.tendsto_right_iff] at hf
  refine fun ε hε ↦ hf₁.and (hf ε hε) |>.exists.imp fun i ↦ and_imp.mpr fun hp hi ↦ ?_
  exact ⟨hp, by
    simpa [Metric.mem_closedBall, Real.dist_eq, abs_of_nonneg (hf₀ i hp).le] using hi⟩
/-
**Metric.ball_subset_interior_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：ball_subset_interior_closedBall : ball x ε subseteq interior (closedBall x
 ε)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `interior_maximal`：interior_maximal (h₁ : t subseteq s) (h₂ : IsOpen t) :
 t subseteq interior s
· 使用定理 `Metric.ball_subset_closedBall`：ball_subset_closedBall : ball x ε subsete
q closedBall x ε
· 使用定理 `Metric.isOpen_ball`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x : α} 
{ε : ℝ}, IsOpen (Metric.ball x ε)
-/
theorem ball_subset_interior_closedBall : ball x ε ⊆ interior (closedBall x ε) :=
  interior_maximal ball_subset_closedBall isOpen_ball

/-- ε-characterization of the closure in pseudometric spaces -/
/-
**Metric.mem_closure_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：mem_closure_iff {s : Set α} {a : α} : a in closure s ↔ forall ε > 0, exist
s b in s, dist a b < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `mem_closure_iff_nhds_basis`：mem_closure_iff_nhds_basis {p : ι -> Prop} {
s : ι -> Set X} (h : (𝓝 x).HasBasis p s) : x in closure t ↔ forall i, p i -> exi
sts y in t, y in…
· 使用定理 `Metric.nhds_basis_ball`：nhds_basis_ball : (𝓝 x).HasBasis (0 < ·) (ball x
)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
ε-characterization of the closure in pseudometric spaces
-/
theorem mem_closure_iff {s : Set α} {a : α} : a ∈ closure s ↔ ∀ ε > 0, ∃ b ∈ s, dist a b < ε :=
  (mem_closure_iff_nhds_basis nhds_basis_ball).trans <| by simp only [mem_ball, dist_comm]
/-
**Metric.mem_closure_range_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：mem_closure_range_iff {e : β -> α} {a : α} : a in closure (range e) ↔ fora
ll ε > 0, exists k : β, dist a (e k) < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_closure_range_iff {e : β → α} {a : α} :
    a ∈ closure (range e) ↔ ∀ ε > 0, ∃ k : β, dist a (e k) < ε := by
  simp only [mem_closure_iff, exists_range_iff]
/-
**Metric.mem_closure_range_iff_nat** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：mem_closure_range_iff_nat {e : β -> α} {a : α} : a in closure (range e) ↔ 
forall n : Nat, exists k : β, dist a (e k) < 1 / ((n : Real) + 1)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `mem_closure_iff_nhds_basis`：mem_closure_iff_nhds_basis {p : ι -> Prop} {
s : ι -> Set X} (h : (𝓝 x).HasBasis p s) : x in closure t ↔ forall i, p i -> exi
sts y in t, y in…
· 使用定理 `Metric.nhds_basis_ball_inv_nat_succ`：nhds_basis_ball_inv_nat_succ : (𝓝 x
).HasBasis (fun _ => True) fun n : Nat => ball x (1 / (↑n + 1))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_closure_range_iff_nat {e : β → α} {a : α} :
    a ∈ closure (range e) ↔ ∀ n : ℕ, ∃ k : β, dist a (e k) < 1 / ((n : ℝ) + 1) :=
  (mem_closure_iff_nhds_basis nhds_basis_ball_inv_nat_succ).trans <| by
    simp only [mem_ball, dist_comm, exists_range_iff, forall_const]
/-
**Metric.mem_of_closed'** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：mem_of_closed' {s : Set α} (hs : IsClosed s) {a : α} : a in s ↔ forall ε >
 0, exists b in s, dist a b < ε
参数：hs : IsClosed s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `Metric.mem_closure_iff`：mem_closure_iff {s : Set α} {a : α} : a in closu
re s ↔ forall ε > 0, exists b in s, dist a b < ε
-/
theorem mem_of_closed' {s : Set α} (hs : IsClosed s) {a : α} :
    a ∈ s ↔ ∀ ε > 0, ∃ b ∈ s, dist a b < ε := by
  simpa only [hs.closure_eq] using @mem_closure_iff _ _ s a
/-
**Metric.dense_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：dense_iff {s : Set α} : Dense s ↔ forall x, forall r > 0, (ball x r inter 
s).Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem dense_iff {s : Set α} : Dense s ↔ ∀ x, ∀ r > 0, (ball x r ∩ s).Nonempty :=
  forall_congr' fun x => by
    simp only [mem_closure_iff, Set.Nonempty, mem_inter_iff, mem_ball', and_comm]
/-
**Metric.dense_iff_iUnion_ball** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：dense_iff_iUnion_ball (s : Set α) : Dense s ↔ forall r > 0, ⋃ c in s, ball
 c r = univ
参数：s : Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem dense_iff_iUnion_ball (s : Set α) : Dense s ↔ ∀ r > 0, ⋃ c ∈ s, ball c r = univ := by
  simp_rw [eq_univ_iff_forall, mem_iUnion, exists_prop, mem_ball, Dense, mem_closure_iff,
    forall_comm (α := α)]
/-
**Metric.denseRange_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：denseRange_iff {f : β -> α} : DenseRange f ↔ forall x, forall r > 0, exist
s y, dist x (f y) < r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem denseRange_iff {f : β → α} : DenseRange f ↔ ∀ x, ∀ r > 0, ∃ y, dist x (f y) < r :=
  forall_congr' fun x => by simp only [mem_closure_iff, exists_range_iff]

end Metric

open Additive Multiplicative

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PseudoMetricSpace (Additive α) := ‹_›
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PseudoMetricSpace (Multiplicative α) := ‹_›

section

variable [PseudoMetricSpace X]

/-
**nndist_ofMul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : Type u_1} [inst : PseudoMetricSpace X] (a b : X), nndist (Additive.
ofMul a) (Additive.ofMul b) = nndist a b
参数：a b : X；Additive.ofMul a；Additive.ofMul b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem nndist_ofMul (a b : X) : nndist (ofMul a) (ofMul b) = nndist a b := rfl
/-
**nndist_ofAdd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : Type u_1} [inst : PseudoMetricSpace X] (a b : X),   nndist (Multipl
icative.ofAdd a) (Multiplicative.ofAdd b) = nndist a b
参数：a b : X；Multiplicative.ofAdd a；Multiplicative.ofAdd b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem nndist_ofAdd (a b : X) : nndist (ofAdd a) (ofAdd b) = nndist a b := rfl
/-
**nndist_toMul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : Type u_1} [inst : PseudoMetricSpace X] (a b : Additive X),   nndist
 (Additive.toMul a) (Additive.toMul b) = nndist a b
参数：a b : Additive X；Additive.toMul a；Additive.toMul b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem nndist_toMul (a b : Additive X) : nndist a.toMul b.toMul = nndist a b := rfl

@[simp]
/-
**nndist_toAdd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nndist_toAdd (a b : Multiplicative X) : nndist a.toAdd b.toAdd = nndist a 
b
参数：a b : Multiplicative X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nndist_toAdd (a b : Multiplicative X) : nndist a.toAdd b.toAdd = nndist a b := rfl

end

open OrderDual

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PseudoMetricSpace αᵒᵈ := ‹_›

section

variable [PseudoMetricSpace X]

/-
**nndist_toDual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : Type u_1} [inst : PseudoMetricSpace X] (a b : X), nndist (OrderDual
.toDual a) (OrderDual.toDual b) = nndist a b
参数：a b : X；OrderDual.toDual a；OrderDual.toDual b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem nndist_toDual (a b : X) : nndist (toDual a) (toDual b) = nndist a b := rfl
/-
**nndist_ofDual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : Type u_1} [inst : PseudoMetricSpace X] (a b : Xᵒᵈ), nndist (OrderDu
al.ofDual a) (OrderDual.ofDual b) = nndist a b
参数：a b : Xᵒᵈ；OrderDual.ofDual a；OrderDual.ofDual b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem nndist_ofDual (a b : Xᵒᵈ) : nndist (ofDual a) (ofDual b) = nndist a b := rfl

end

