/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Metric spaces

This file defines metric spaces and shows some of their basic properties.

Many definitions and theorems expected on metric spaces are already introduced on uniform spaces and
topological spaces. This includes open and closed sets, compactness, completeness, continuity
and uniform continuity.

## Main definitions

* `MetricSpace α`: A pseudometric space with the guarantee `dist x y = 0 → x = y`.
* `MetricSpace.ofDistTopology`: Construct a metric space from a compatible topology and distance.
* `MetricSpace.replaceUniformity`, `MetricSpace.replaceTopology`,
  `MetricSpace.replaceBornology`: Tools to construct a metric space on a type with a pre-existing
  uniformity, topology, or bornology in such a way that the definitional equalities for these
  structures are preserved; these are essential to avoid type class synthesis issues.

## Main results

* `dist_eq_zero`, `dist_pos`, `eq_of_forall_dist_le`, `eq_of_nndist_eq_zero`: core
  characterizations of equality via distance.

## Implementation notes
A lot of elementary properties don't require `eq_of_dist_eq_zero`, hence are stated and proven
for `PseudoMetricSpace`s in `Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`.

## Tags

metric, pseudometric space, dist
-/

@[expose] public section

assert_not_exists Finset.sum

open Set Filter Bornology
open scoped NNReal Uniformity

universe u v w

variable {α : Type u} {β : Type v} {X ι : Type*}
variable [PseudoMetricSpace α]

/-- A metric space is a type endowed with a `ℝ`-valued distance `dist` satisfying
`dist x y = 0 ↔ x = y`, commutativity `dist x y = dist y x`, and the triangle inequality
`dist x z ≤ dist x y + dist y z`.

See pseudometric spaces (`PseudoMetricSpace`) for the similar class with the `dist x y = 0 ↔ x = y`
assumption weakened to `dist x x = 0`.

Any metric space is a T1 topological space and a uniform space (see `TopologicalSpace`, `T1Space`,
`UniformSpace`), where the topology and uniformity come from the metric.

We make the uniformity/topology part of the data instead of deriving it from the metric.
This e.g. ensures that we do not get a diamond when doing
`[MetricSpace α] [MetricSpace β] : TopologicalSpace (α × β)`:
The product metric and product topology agree, but not definitionally so.
See Note [forgetful inheritance]. -/
@[wikidata Q180953]
/--
Definition of `MetricSpace` / `MetricSpace` 的定义

English:
class MetricSpace
  parameters: (α : Type u)
  extends: PseudoMetricSpace α
  axioms and operations (1):
    - eq_of_dist_eq_zero : forall {x y : α}, dist x y = 0 -> x = y

中文:
类 MetricSpace
  参数: (α : 类型u)
  继承: PseudoMetricSpace α
  公理与运算 (1 个):
    - eq_of_dist_eq_zero : 对任意 {x y : α}, dist x y = 0 -> x = y
-/
class MetricSpace (α : Type u) : Type u extends PseudoMetricSpace α where
  eq_of_dist_eq_zero : forall {x y : α}, dist x y = 0 -> x = y

/-- Two metric space structures with the same distance coincide. -/
@[ext]
/--
theorem `MetricSpace.ext` / 定理 `MetricSpace.ext`

English:
theorem MetricSpace.ext
  given: {α : Type*} {m m' : MetricSpace α} (h : m.toDist = m'.toDist)
  proof: by
  cases m; cases m'; congr; ext1; assumption

中文:
定理 MetricSpace.ext
  条件: {α : 类型} {m m' : MetricSpace α} (h : m.toDist = m'.toDist)
  证明: by
  cases m; cases m'; congr; ext1; assumption
-/
theorem MetricSpace.ext {α : Type*} {m m' : MetricSpace α} (h : m.toDist = m'.toDist) :
    m = m' := by
  cases m; cases m'; congr; ext1; assumption

/-- Construct a metric space structure whose underlying topological space structure
(definitionally) agrees which a pre-existing topology which is compatible with a given distance
function. -/
@[instance_reducible]
/--
Definition of `MetricSpace.ofDistTopology` / `MetricSpace.ofDistTopology` 的定义

English:
definition MetricSpace.ofDistTopology
  signature: {α : Type u} [TopologicalSpace α] (dist : α -> α -> Real)
  body: { PseudoMetricSpace.ofDistTopology dist dist_self dist_comm dist_triangle H with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero _ _ }

中文:
定义 MetricSpace.ofDistTopology
  签名: {α : 类型u} [TopologicalSpace α] (dist : α -> α -> 实数)
  定义体: { PseudoMetricSpace.ofDistTopology dist dist_self dist_comm dist_triangle H with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero _ _ }

Depends on / 依赖: PseudoMetricSpace, PseudoMetricSpace.ofDistTopology, dist_comm, dist_self, dist_triangle, eq_of_dist_eq_zero, ofDistTopology
-/
def MetricSpace.ofDistTopology {α : Type u} [TopologicalSpace α] (dist : α -> α -> Real)
    (dist_self : forall x : α, dist x x = 0) (dist_comm : forall x y : α, dist x y = dist y x)
    (dist_triangle : forall x y z : α, dist x z <= dist x y + dist y z)
    (H : forall s : Set α, IsOpen s ↔ forall x in s, exists ε > 0, forall y, dist x y < ε -> y in s)
    (eq_of_dist_eq_zero : forall x y : α, dist x y = 0 -> x = y) : MetricSpace α :=
  { PseudoMetricSpace.ofDistTopology dist dist_self dist_comm dist_triangle H with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero _ _ }

variable {γ : Type w} [MetricSpace γ]

/--
theorem `eq_of_dist_eq_zero` / 定理 `eq_of_dist_eq_zero`

English:
theorem eq_of_dist_eq_zero
  given: {x y : γ}
  statement: dist x y = 0 -> x = y
  proof: MetricSpace.eq_of_dist_eq_zero

@[simp]

中文:
定理 eq_of_dist_eq_zero
  条件: {x y : γ}
  结论: dist x y = 0 -> x = y
  证明: MetricSpace.eq_of_dist_eq_zero

@[simp]

Depends on / 依赖: MetricSpace, MetricSpace.eq_of_dist_eq_zero, eq_of_dist_eq_zero
-/
theorem eq_of_dist_eq_zero {x y : γ} : dist x y = 0 -> x = y :=
  MetricSpace.eq_of_dist_eq_zero

@[simp]
/--
theorem `dist_eq_zero` / 定理 `dist_eq_zero`

English:
theorem dist_eq_zero
  given: {x y : γ}
  statement: dist x y = 0 ↔ x = y
  proof: Iff.intro eq_of_dist_eq_zero fun this => this ▸ dist_self _

@[simp]

中文:
定理 dist_eq_zero
  条件: {x y : γ}
  结论: dist x y = 0 ↔ x = y
  证明: Iff.intro eq_of_dist_eq_zero fun this => this ▸ dist_self _

@[simp]

Depends on / 依赖: Iff.intro, dist_self, eq_of_dist_eq_zero
-/
theorem dist_eq_zero {x y : γ} : dist x y = 0 ↔ x = y :=
  Iff.intro eq_of_dist_eq_zero fun this => this ▸ dist_self _

@[simp]
/--
theorem `zero_eq_dist` / 定理 `zero_eq_dist`

English:
theorem zero_eq_dist
  given: {x y : γ}
  statement: 0 = dist x y ↔ x = y
  proof: by rw [eq_comm, dist_eq_zero]

中文:
定理 zero_eq_dist
  条件: {x y : γ}
  结论: 0 = dist x y ↔ x = y
  证明: by rw [eq_comm, dist_eq_zero]

Depends on / 依赖: dist_eq_zero, eq_comm
-/
theorem zero_eq_dist {x y : γ} : 0 = dist x y ↔ x = y := by rw [eq_comm, dist_eq_zero]

/--
theorem `dist_ne_zero` / 定理 `dist_ne_zero`

English:
theorem dist_ne_zero
  given: {x y : γ}
  statement: dist x y != 0 ↔ x != y
  proof: by
  simpa only [not_iff_not] using dist_eq_zero

@[simp]

中文:
定理 dist_ne_zero
  条件: {x y : γ}
  结论: dist x y != 0 ↔ x != y
  证明: by
  simpa only [not_iff_not] using dist_eq_zero

@[simp]

Depends on / 依赖: dist_eq_zero, not_iff_not
-/
theorem dist_ne_zero {x y : γ} : dist x y != 0 ↔ x != y := by
  simpa only [not_iff_not] using dist_eq_zero

@[simp]
/--
theorem `dist_le_zero` / 定理 `dist_le_zero`

English:
theorem dist_le_zero
  given: {x y : γ}
  statement: dist x y <= 0 ↔ x = y
  proof: by
  simpa [le_antisymm_iff, dist_nonneg] using @dist_eq_zero _ _ x y

@[simp]

中文:
定理 dist_le_zero
  条件: {x y : γ}
  结论: dist x y <= 0 ↔ x = y
  证明: by
  simpa [le_antisymm_iff, dist_nonneg] using @dist_eq_zero _ _ x y

@[simp]

Depends on / 依赖: dist_eq_zero, dist_nonneg, le_antisymm_iff
-/
theorem dist_le_zero {x y : γ} : dist x y <= 0 ↔ x = y := by
  simpa [le_antisymm_iff, dist_nonneg] using @dist_eq_zero _ _ x y

@[simp]
/--
theorem `dist_pos` / 定理 `dist_pos`

English:
theorem dist_pos
  given: {x y : γ}
  statement: 0 < dist x y ↔ x != y
  proof: by
  simpa only [not_le] using not_congr dist_le_zero

中文:
定理 dist_pos
  条件: {x y : γ}
  结论: 0 < dist x y ↔ x != y
  证明: by
  simpa only [not_le] using not_congr dist_le_zero

Depends on / 依赖: dist_le_zero, not_congr, not_le
-/
theorem dist_pos {x y : γ} : 0 < dist x y ↔ x != y := by
  simpa only [not_le] using not_congr dist_le_zero

/--
theorem `eq_of_forall_dist_le` / 定理 `eq_of_forall_dist_le`

English:
theorem eq_of_forall_dist_le
  given: {x y : γ} (h : forall ε > 0, dist x y <= ε)
  statement: x = y
  proof: eq_of_dist_eq_zero (eq_of_le_of_forall_lt_imp_le_of_dense dist_nonneg h)

中文:
定理 eq_of_forall_dist_le
  条件: {x y : γ} (h : 对任意 ε > 0, dist x y <= ε)
  结论: x = y
  证明: eq_of_dist_eq_zero (eq_of_le_of_forall_lt_imp_le_of_dense dist_nonneg h)

Depends on / 依赖: dist_nonneg, eq_of_dist_eq_zero, eq_of_le_of_forall_lt_imp_le_of_dense
-/
theorem eq_of_forall_dist_le {x y : γ} (h : forall ε > 0, dist x y <= ε) : x = y :=
  eq_of_dist_eq_zero (eq_of_le_of_forall_lt_imp_le_of_dense dist_nonneg h)

/--
theorem `eq_of_nndist_eq_zero` / 定理 `eq_of_nndist_eq_zero`

English:
theorem eq_of_nndist_eq_zero
  given: {x y : γ}
  statement: nndist x y = 0 -> x = y
  proof: by
  simp only [NNReal.eq_iff, ← dist_nndist, imp_self, NNReal.coe_zero, dist_eq_zero]

中文:
定理 eq_of_nndist_eq_zero
  条件: {x y : γ}
  结论: nndist x y = 0 -> x = y
  证明: by
  simp only [NNReal.eq_iff, ← dist_nndist, imp_self, NNReal.coe_zero, dist_eq_zero]

Depends on / 依赖: NNReal, NNReal.coe_zero, NNReal.eq_iff, coe_zero, dist_eq_zero, dist_nndist, eq_iff, imp_self
-/
theorem eq_of_nndist_eq_zero {x y : γ} : nndist x y = 0 -> x = y := by
  simp only [NNReal.eq_iff, ← dist_nndist, imp_self, NNReal.coe_zero, dist_eq_zero]

/-- Characterize the equality of points as the vanishing of the nonnegative distance -/
@[simp]
/--
theorem `nndist_eq_zero` / 定理 `nndist_eq_zero`

English:
theorem nndist_eq_zero
  given: {x y : γ}
  statement: nndist x y = 0 ↔ x = y
  proof: by
  simp only [NNReal.eq_iff, ← dist_nndist, NNReal.coe_zero, dist_eq_zero]

@[simp]

中文:
定理 nndist_eq_zero
  条件: {x y : γ}
  结论: nndist x y = 0 ↔ x = y
  证明: by
  simp only [NNReal.eq_iff, ← dist_nndist, NNReal.coe_zero, dist_eq_zero]

@[simp]

Depends on / 依赖: NNReal, NNReal.coe_zero, NNReal.eq_iff, coe_zero, dist_eq_zero, dist_nndist, eq_iff
-/
theorem nndist_eq_zero {x y : γ} : nndist x y = 0 ↔ x = y := by
  simp only [NNReal.eq_iff, ← dist_nndist, NNReal.coe_zero, dist_eq_zero]

@[simp]
/--
theorem `zero_eq_nndist` / 定理 `zero_eq_nndist`

English:
theorem zero_eq_nndist
  given: {x y : γ}
  statement: 0 = nndist x y ↔ x = y
  proof: by
  simp only [NNReal.eq_iff, ← dist_nndist, NNReal.coe_zero, zero_eq_dist]

中文:
定理 zero_eq_nndist
  条件: {x y : γ}
  结论: 0 = nndist x y ↔ x = y
  证明: by
  simp only [NNReal.eq_iff, ← dist_nndist, NNReal.coe_zero, zero_eq_dist]

Depends on / 依赖: NNReal, NNReal.coe_zero, NNReal.eq_iff, coe_zero, dist_nndist, eq_iff, zero_eq_dist
-/
theorem zero_eq_nndist {x y : γ} : 0 = nndist x y ↔ x = y := by
  simp only [NNReal.eq_iff, ← dist_nndist, NNReal.coe_zero, zero_eq_dist]

namespace Metric

variable {x : γ} {s : Set γ}

/--
theorem `closedBall_zero` / 定理 `closedBall_zero`

English:
theorem closedBall_zero
  statement: closedBall x 0 = {x}
  proof: Set.ext fun _ => dist_le_zero

中文:
定理 closedBall_zero
  结论: closedBall x 0 = {x}
  证明: Set.ext fun _ => dist_le_zero
-/
@[simp] theorem closedBall_zero : closedBall x 0 = {x} := Set.ext fun _ => dist_le_zero

/--
theorem `sphere_zero` / 定理 `sphere_zero`

English:
theorem sphere_zero
  statement: sphere x 0 = {x}
  proof: Set.ext fun _ => dist_eq_zero

中文:
定理 sphere_zero
  结论: sphere x 0 = {x}
  证明: Set.ext fun _ => dist_eq_zero
-/
@[simp] theorem sphere_zero : sphere x 0 = {x} := Set.ext fun _ => dist_eq_zero

/--
theorem `subsingleton_closedBall` / 定理 `subsingleton_closedBall`

English:
theorem subsingleton_closedBall
  given: (x : γ) {r : Real} (hr : r <= 0)
  statement: (closedBall x r).Subsingleton
  proof: by
  rcases hr.lt_or_eq with (hr | rfl)
  · rw [closedBall_eq_empty.2 hr]
    exact subsingleton_empty
  · rw [closedBall_zero]
    exact subsingleton_singleton

中文:
定理 subsingleton_closedBall
  条件: (x : γ) {r : 实数} (hr : r <= 0)
  结论: (closedBall x r).Subsingleton
  证明: by
  rcases hr.lt_or_eq with (hr | rfl)
  · rw [closedBall_eq_empty.2 hr]
    exact subsingleton_empty
  · rw [closedBall_zero]
    exact subsingleton_singleton

Depends on / 依赖: closedBall_eq_empty, closedBall_zero, hr.lt_or_eq, lt_or_eq, subsingleton_empty, subsingleton_singleton
-/
theorem subsingleton_closedBall (x : γ) {r : Real} (hr : r <= 0) : (closedBall x r).Subsingleton := by
  rcases hr.lt_or_eq with (hr | rfl)
  · rw [closedBall_eq_empty.2 hr]
    exact subsingleton_empty
  · rw [closedBall_zero]
    exact subsingleton_singleton

/--
theorem `subsingleton_sphere` / 定理 `subsingleton_sphere`

English:
theorem subsingleton_sphere
  given: (x : γ) {r : Real} (hr : r <= 0)
  statement: (sphere x r).Subsingleton
  proof: (subsingleton_closedBall x hr).anti sphere_subset_closedBall

中文:
定理 subsingleton_sphere
  条件: (x : γ) {r : 实数} (hr : r <= 0)
  结论: (sphere x r).Subsingleton
  证明: (subsingleton_closedBall x hr).anti sphere_subset_closedBall

Depends on / 依赖: sphere_subset_closedBall, subsingleton_closedBall
-/
theorem subsingleton_sphere (x : γ) {r : Real} (hr : r <= 0) : (sphere x r).Subsingleton :=
  (subsingleton_closedBall x hr).anti sphere_subset_closedBall

end Metric

/--
Definition of `MetricSpace.replaceUniformity` / `MetricSpace.replaceUniformity` 的定义

English:
abbreviation MetricSpace.replaceUniformity
  signature: {γ} [U : UniformSpace γ] (m : MetricSpace γ)
  body: PseudoMetricSpace.replaceUniformity m.toPseudoMetricSpace H
  eq_of_dist_eq_zero := @eq_of_dist_eq_zero _ _

中文:
缩写 MetricSpace.replaceUniformity
  签名: {γ} [U : UniformSpace γ] (m : MetricSpace γ)
  定义体: PseudoMetricSpace.replaceUniformity m.toPseudoMetricSpace H
  eq_of_dist_eq_zero := @eq_of_dist_eq_zero _ _

Depends on / 依赖: PseudoMetricSpace, PseudoMetricSpace.replaceUniformity, m.toPseudoMetricSpace, replaceUniformity, toPseudoMetricSpace
-/
abbrev MetricSpace.replaceUniformity {γ} [U : UniformSpace γ] (m : MetricSpace γ)
    (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace]) : MetricSpace γ where
  toPseudoMetricSpace := PseudoMetricSpace.replaceUniformity m.toPseudoMetricSpace H
  eq_of_dist_eq_zero := @eq_of_dist_eq_zero _ _

/--
theorem `MetricSpace.replaceUniformity_eq` / 定理 `MetricSpace.replaceUniformity_eq`

English:
theorem MetricSpace.replaceUniformity_eq
  statement: {γ} [U : UniformSpace γ] (m : MetricSpace γ)
  proof: by
  ext; rfl

中文:
定理 MetricSpace.replaceUniformity_eq
  结论: {γ} [U : UniformSpace γ] (m : MetricSpace γ)
  证明: by
  ext; rfl
-/
theorem MetricSpace.replaceUniformity_eq {γ} [U : UniformSpace γ] (m : MetricSpace γ)
    (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace]) : m.replaceUniformity H = m := by
  ext; rfl

/--
Definition of `MetricSpace.replaceTopology` / `MetricSpace.replaceTopology` 的定义

English:
abbreviation MetricSpace.replaceTopology
  signature: {γ} [U : TopologicalSpace γ] (m : MetricSpace γ)
  body: @MetricSpace.replaceUniformity γ (m.toUniformSpace.replaceTopology H) m rfl

中文:
缩写 MetricSpace.replaceTopology
  签名: {γ} [U : TopologicalSpace γ] (m : MetricSpace γ)
  定义体: @MetricSpace.replaceUniformity γ (m.toUniformSpace.replaceTopology H) m rfl

Depends on / 依赖: MetricSpace, MetricSpace.replaceUniformity, m.toUniformSpace.replaceTopology, replaceTopology, replaceUniformity, toUniformSpace
-/
abbrev MetricSpace.replaceTopology {γ} [U : TopologicalSpace γ] (m : MetricSpace γ)
    (H : U = m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace) : MetricSpace γ :=
  @MetricSpace.replaceUniformity γ (m.toUniformSpace.replaceTopology H) m rfl

/--
theorem `MetricSpace.replaceTopology_eq` / 定理 `MetricSpace.replaceTopology_eq`

English:
theorem MetricSpace.replaceTopology_eq
  statement: {γ} [U : TopologicalSpace γ] (m : MetricSpace γ)
  proof: by
  ext; rfl

中文:
定理 MetricSpace.replaceTopology_eq
  结论: {γ} [U : TopologicalSpace γ] (m : MetricSpace γ)
  证明: by
  ext; rfl
-/
theorem MetricSpace.replaceTopology_eq {γ} [U : TopologicalSpace γ] (m : MetricSpace γ)
    (H : U = m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace) :
    m.replaceTopology H = m := by
  ext; rfl

/--
Definition of `MetricSpace.replaceBornology` / `MetricSpace.replaceBornology` 的定义

English:
abbreviation MetricSpace.replaceBornology
  signature: {α} [B : Bornology α] (m : MetricSpace α)
  body: { PseudoMetricSpace.replaceBornology _ H, m with toBornology := B }

中文:
缩写 MetricSpace.replaceBornology
  签名: {α} [B : Bornology α] (m : MetricSpace α)
  定义体: { PseudoMetricSpace.replaceBornology _ H, m with toBornology := B }

Depends on / 依赖: PseudoMetricSpace, PseudoMetricSpace.replaceBornology, replaceBornology, toBornology
-/
abbrev MetricSpace.replaceBornology {α} [B : Bornology α] (m : MetricSpace α)
    (H : forall s, @IsBounded _ B s ↔ @IsBounded _ PseudoMetricSpace.toBornology s) : MetricSpace α :=
  { PseudoMetricSpace.replaceBornology _ H, m with toBornology := B }

/--
theorem `MetricSpace.replaceBornology_eq` / 定理 `MetricSpace.replaceBornology_eq`

English:
theorem MetricSpace.replaceBornology_eq
  statement: {α} [m : MetricSpace α] [B : Bornology α]
  proof: by
  ext
  rfl

中文:
定理 MetricSpace.replaceBornology_eq
  结论: {α} [m : MetricSpace α] [B : Bornology α]
  证明: by
  ext
  rfl
-/
theorem MetricSpace.replaceBornology_eq {α} [m : MetricSpace α] [B : Bornology α]
    (H : forall s, @IsBounded _ B s ↔ @IsBounded _ PseudoMetricSpace.toBornology s) :
    MetricSpace.replaceBornology _ H = m := by
  ext
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MetricSpace Empty
  body: 0
  dist_self _ := rfl
  dist_comm _ _ := rfl
  edist _ _ := 0
  eq_of_dist_eq_zero _ := Subsingleton.elim _ _
  dist_triangle _ _ _ := show (0 : Real) <= 0 + 0 by rw [add_zero]
  toUniformSpace := inferInstance
  uniformity_dist := Subsingleton.elim _ _

中文:
实例 :
  签名: MetricSpace Empty
  定义体: 0
  dist_self _ := rfl
  dist_comm _ _ := rfl
  edist _ _ := 0
  eq_of_dist_eq_zero _ := Subsingleton.elim _ _
  dist_triangle _ _ _ := show (0 : Real) <= 0 + 0 by rw [add_zero]
  toUniformSpace := inferInstance
  uniformity_dist := Subsingleton.elim _ _
-/
instance : MetricSpace Empty where
  dist _ _ := 0
  dist_self _ := rfl
  dist_comm _ _ := rfl
  edist _ _ := 0
  eq_of_dist_eq_zero _ := Subsingleton.elim _ _
  dist_triangle _ _ _ := show (0 : Real) <= 0 + 0 by rw [add_zero]
  toUniformSpace := inferInstance
  uniformity_dist := Subsingleton.elim _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MetricSpace PUnit.{u + 1}
  body: 0
  dist_self _ := rfl
  dist_comm _ _ := rfl
  edist _ _ := 0
  eq_of_dist_eq_zero _ := Subsingleton.elim _ _
  dist_triangle _ _ _ := show (0 : Real) <= 0 + 0 by rw [add_zero]
  toUniformSpace := inferInstance
  uniformity_dist := by
    simp +contextual [principal_univ, eq_top_of_neBot (𝓤 PUnit)]

中文:
实例 :
  签名: MetricSpace PUnit.{u + 1}
  定义体: 0
  dist_self _ := rfl
  dist_comm _ _ := rfl
  edist _ _ := 0
  eq_of_dist_eq_zero _ := Subsingleton.elim _ _
  dist_triangle _ _ _ := show (0 : Real) <= 0 + 0 by rw [add_zero]
  toUniformSpace := inferInstance
  uniformity_dist := by
    simp +contextual [principal_univ, eq_top_of_neBot (𝓤 PUnit)]
-/
instance : MetricSpace PUnit.{u + 1} where
  dist _ _ := 0
  dist_self _ := rfl
  dist_comm _ _ := rfl
  edist _ _ := 0
  eq_of_dist_eq_zero _ := Subsingleton.elim _ _
  dist_triangle _ _ _ := show (0 : Real) <= 0 + 0 by rw [add_zero]
  toUniformSpace := inferInstance
  uniformity_dist := by
    simp +contextual [principal_univ, eq_top_of_neBot (𝓤 PUnit)]

/-!
### `Additive`, `Multiplicative`

The distance on those type synonyms is inherited without change.
-/


open Additive Multiplicative

section

variable [Dist X]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Dist (Additive X)
  body: ‹Dist X›

中文:
实例 :
  签名: Dist (Additive X)
  定义体: ‹Dist X›
-/
instance : Dist (Additive X) := ‹Dist X›
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Dist (Multiplicative X)
  body: ‹Dist X›

中文:
实例 :
  签名: Dist (Multiplicative X)
  定义体: ‹Dist X›
-/
instance : Dist (Multiplicative X) := ‹Dist X›

/--
theorem `dist_ofMul` / 定理 `dist_ofMul`

English:
theorem dist_ofMul
  given: (a b : X)
  statement: dist (ofMul a) (ofMul b) = dist a b
  proof: rfl

中文:
定理 dist_ofMul
  条件: (a b : X)
  结论: dist (ofMul a) (ofMul b) = dist a b
  证明: rfl
-/
@[simp] theorem dist_ofMul (a b : X) : dist (ofMul a) (ofMul b) = dist a b := rfl

/--
theorem `dist_ofAdd` / 定理 `dist_ofAdd`

English:
theorem dist_ofAdd
  given: (a b : X)
  statement: dist (ofAdd a) (ofAdd b) = dist a b
  proof: rfl

中文:
定理 dist_ofAdd
  条件: (a b : X)
  结论: dist (ofAdd a) (ofAdd b) = dist a b
  证明: rfl
-/
@[simp] theorem dist_ofAdd (a b : X) : dist (ofAdd a) (ofAdd b) = dist a b := rfl

/--
theorem `dist_toMul` / 定理 `dist_toMul`

English:
theorem dist_toMul
  given: (a b : Additive X)
  statement: dist a.toMul b.toMul = dist a b
  proof: rfl

中文:
定理 dist_toMul
  条件: (a b : Additive X)
  结论: dist a.toMul b.toMul = dist a b
  证明: rfl
-/
@[simp] theorem dist_toMul (a b : Additive X) : dist a.toMul b.toMul = dist a b := rfl

/--
theorem `dist_toAdd` / 定理 `dist_toAdd`

English:
theorem dist_toAdd
  given: (a b : Multiplicative X)
  statement: dist a.toAdd b.toAdd = dist a b
  proof: rfl

中文:
定理 dist_toAdd
  条件: (a b : Multiplicative X)
  结论: dist a.toAdd b.toAdd = dist a b
  证明: rfl
-/
@[simp] theorem dist_toAdd (a b : Multiplicative X) : dist a.toAdd b.toAdd = dist a b := rfl

end

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MetricSpace
  signature: X] : MetricSpace (Additive X)
  body: ‹MetricSpace X›

中文:
实例 [MetricSpace
  签名: X] : MetricSpace (Additive X)
  定义体: ‹MetricSpace X›
-/
instance [MetricSpace X] : MetricSpace (Additive X) := ‹MetricSpace X›
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MetricSpace
  signature: X] : MetricSpace (Multiplicative X)
  body: ‹MetricSpace X›

中文:
实例 [MetricSpace
  签名: X] : MetricSpace (Multiplicative X)
  定义体: ‹MetricSpace X›

Depends on / 依赖: MetricSpace
-/
instance [MetricSpace X] : MetricSpace (Multiplicative X) := ‹MetricSpace X›

/-!
### Order dual

The distance on this type synonym is inherited without change.
-/

open OrderDual

section

variable [Dist X]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Dist Xᵒᵈ
  body: ‹Dist X›

中文:
实例 :
  签名: Dist Xᵒᵈ
  定义体: ‹Dist X›
-/
instance : Dist Xᵒᵈ := ‹Dist X›

/--
theorem `dist_toDual` / 定理 `dist_toDual`

English:
theorem dist_toDual
  given: (a b : X)
  statement: dist (toDual a) (toDual b) = dist a b
  proof: rfl

中文:
定理 dist_toDual
  条件: (a b : X)
  结论: dist (toDual a) (toDual b) = dist a b
  证明: rfl
-/
@[simp] theorem dist_toDual (a b : X) : dist (toDual a) (toDual b) = dist a b := rfl

/--
theorem `dist_ofDual` / 定理 `dist_ofDual`

English:
theorem dist_ofDual
  given: (a b : Xᵒᵈ)
  statement: dist (ofDual a) (ofDual b) = dist a b
  proof: rfl

中文:
定理 dist_ofDual
  条件: (a b : Xᵒᵈ)
  结论: dist (ofDual a) (ofDual b) = dist a b
  证明: rfl
-/
@[simp] theorem dist_ofDual (a b : Xᵒᵈ) : dist (ofDual a) (ofDual b) = dist a b := rfl

end

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MetricSpace
  signature: X] : MetricSpace Xᵒᵈ
  body: ‹MetricSpace X›

中文:
实例 [MetricSpace
  签名: X] : MetricSpace Xᵒᵈ
  定义体: ‹MetricSpace X›

Depends on / 依赖: MetricSpace
-/
instance [MetricSpace X] : MetricSpace Xᵒᵈ := ‹MetricSpace X›
