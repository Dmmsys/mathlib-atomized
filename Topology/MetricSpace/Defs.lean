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
/-
**MetricSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A metric space is a type endowed with a `ℝ`-valued distance `dist` satisfying
`dist x y = 0 ↔ x = y`, commutativity `dist x y = dist y x`, and the triangle in
equality
`dist x z ≤ dist x y + dist y z`.

See pseudometric spaces (`PseudoMetricSpace`) for the similar class with the `di
st x y = 0 ↔ x = y`
assumption weakened to `dist x x = 0`.

Any metric space is a T1 topological space and a uniform space (see `Topological
Space`, `T1Space`,
`UniformSpace`), where the topology and uniformity come from the metric.

We make the uniformity/topology part of the data instead of deriving it from the
 metric.
This e.g. ensures that we do not get a diamond when doing
`[MetricSpace α] [MetricSpace β] : TopologicalSpace (α × β)`:
The product metric and product topology agree, but not definitionally so.
See Note [forgetful inheritance].
-/
class MetricSpace (α : Type u) : Type u extends PseudoMetricSpace α where
  eq_of_dist_eq_zero : ∀ {x y : α}, dist x y = 0 → x = y

/-- Two metric space structures with the same distance coincide. -/
@[ext]
/-
**MetricSpace.ext** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MetricSpace.ext {α : Type*} {m m' : MetricSpace α} (h : m.toDist = m'.toDi
st) : m = m'
参数：h : m.toDist = m'.toDist。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PseudoMetricSpace.ext`：PseudoMetricSpace.ext {α : Type*} {m m' : PseudoM
etricSpace α} (h : m.toDist = m'.toDist) : m = m'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Two metric space structures with the same distance coincide.
-/
theorem MetricSpace.ext {α : Type*} {m m' : MetricSpace α} (h : m.toDist = m'.toDist) :
    m = m' := by
  cases m; cases m'; congr; ext1; assumption

/-- Construct a metric space structure whose underlying topological space structure
(definitionally) agrees which a pre-existing topology which is compatible with a given distance
function. -/
@[instance_reducible]
/-
**MetricSpace.ofDistTopology** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MetricSpace.ofDistTopology {α : Type u} [TopologicalSpace α] (dist : α -> 
α -> Real) (dist_self : forall x : α, dist x x = 0) (dist_comm : forall x y : α,
 dist x y = dist y x) (dist_triangle : forall x y z : α, dist x z <= dist x y + 
dist y z) (H : forall s : Set α, IsOpen s ↔ forall x in s, exists ε > 0, forall 
y, dist x y < ε -> y in s) (eq_of_dist_eq_zero : forall x y : α, dist x y = 0 ->
 x = y) : MetricSpace α
参数：dist : α -> α -> Real；dist_self : forall x : α, dist x x = 0；dist_comm : fora
ll x y : α, dist x y = dist y x；dist_triangle : forall x y z : α, dist x z <= di
st x y + dist y z；H : forall s : Set α, IsOpen s ↔ forall x in s, exists ε > 0, 
forall y, dist x y < ε -> y in s；eq_of_dist_eq_zero : forall x y : α, dist x y =
 0 -> x = y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a metric space structure whose underlying topological space structure
(definitionally) agrees which a pre-existing topology which is compatible with a
 given distance
function.
-/
def MetricSpace.ofDistTopology {α : Type u} [TopologicalSpace α] (dist : α → α → ℝ)
    (dist_self : ∀ x : α, dist x x = 0) (dist_comm : ∀ x y : α, dist x y = dist y x)
    (dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z)
    (H : ∀ s : Set α, IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ∀ y, dist x y < ε → y ∈ s)
    (eq_of_dist_eq_zero : ∀ x y : α, dist x y = 0 → x = y) : MetricSpace α :=
  { PseudoMetricSpace.ofDistTopology dist dist_self dist_comm dist_triangle H with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero _ _ }

variable {γ : Type w} [MetricSpace γ]
/-
**eq_of_dist_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_of_dist_eq_zero {x y : γ} : dist x y = 0 -> x = y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MetricSpace.eq_of_dist_eq_zero`：∀ {α : Type u} [self : MetricSpace α] {x
 y : α}, dist x y = 0 → x = y
-/
theorem eq_of_dist_eq_zero {x y : γ} : dist x y = 0 → x = y :=
  MetricSpace.eq_of_dist_eq_zero

@[simp]
/-
**dist_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_eq_zero {x y : γ} : dist x y = 0 ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_dist_eq_zero`：eq_of_dist_eq_zero {x y : γ} : dist x y = 0 -> x = y
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
-/
theorem dist_eq_zero {x y : γ} : dist x y = 0 ↔ x = y :=
  Iff.intro eq_of_dist_eq_zero fun this => this ▸ dist_self _

@[simp]
/-
**zero_eq_dist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zero_eq_dist {x y : γ} : 0 = dist x y ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `dist_eq_zero`：dist_eq_zero {x y : γ} : dist x y = 0 ↔ x = y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem zero_eq_dist {x y : γ} : 0 = dist x y ↔ x = y := by rw [eq_comm, dist_eq_zero]
/-
**dist_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_ne_zero {x y : γ} : dist x y != 0 ↔ x != y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dist_eq_zero`：dist_eq_zero {x y : γ} : dist x y = 0 ↔ x = y
-/
theorem dist_ne_zero {x y : γ} : dist x y ≠ 0 ↔ x ≠ y := by
  simpa only [not_iff_not] using dist_eq_zero

@[simp]
/-
**dist_le_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_le_zero {x y : γ} : dist x y <= 0 ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `dist_eq_zero`：dist_eq_zero {x y : γ} : dist x y = 0 ↔ x = y
-/
theorem dist_le_zero {x y : γ} : dist x y ≤ 0 ↔ x = y := by
  simpa [le_antisymm_iff, dist_nonneg] using @dist_eq_zero _ _ x y

@[simp]
/-
**dist_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_pos {x y : γ} : 0 < dist x y ↔ x != y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `dist_le_zero`：dist_le_zero {x y : γ} : dist x y <= 0 ↔ x = y
-/
theorem dist_pos {x y : γ} : 0 < dist x y ↔ x ≠ y := by
  simpa only [not_le] using not_congr dist_le_zero
/-
**eq_of_forall_dist_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_of_forall_dist_le {x y : γ} (h : forall ε > 0, dist x y <= ε) : x = y
参数：h : forall ε > 0, dist x y <= ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_dist_eq_zero`：eq_of_dist_eq_zero {x y : γ} : dist x y = 0 -> x = y
· 使用引理 `eq_of_le_of_forall_lt_imp_le_of_dense`：eq_of_le_of_forall_lt_imp_le_of_d
ense (h₁ : a₂ <= a₁) (h₂ : forall a, a₂ < a -> a₁ <= a) : a₁ = a₂
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
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
-/
theorem eq_of_forall_dist_le {x y : γ} (h : ∀ ε > 0, dist x y ≤ ε) : x = y :=
  eq_of_dist_eq_zero (eq_of_le_of_forall_lt_imp_le_of_dense dist_nonneg h)

/-- Deduce the equality of points from the vanishing of the nonnegative distance -/
/-
**eq_of_nndist_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_of_nndist_eq_zero {x y : γ} : nndist x y = 0 -> x = y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)

--- 原说明 ---
Deduce the equality of points from the vanishing of the nonnegative distance
-/
theorem eq_of_nndist_eq_zero {x y : γ} : nndist x y = 0 → x = y := by
  simp only [NNReal.eq_iff, ← dist_nndist, imp_self, NNReal.coe_zero, dist_eq_zero]

/-- Characterize the equality of points as the vanishing of the nonnegative distance -/
@[simp]
/-
**nndist_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nndist_eq_zero {x y : γ} : nndist x y = 0 ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Characterize the equality of points as the vanishing of the nonnegative distance
-/
theorem nndist_eq_zero {x y : γ} : nndist x y = 0 ↔ x = y := by
  simp only [NNReal.eq_iff, ← dist_nndist, NNReal.coe_zero, dist_eq_zero]

@[simp]
/-
**zero_eq_nndist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zero_eq_nndist {x y : γ} : 0 = nndist x y ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem zero_eq_nndist {x y : γ} : 0 = nndist x y ↔ x = y := by
  simp only [NNReal.eq_iff, ← dist_nndist, NNReal.coe_zero, zero_eq_dist]

namespace Metric

variable {x : γ} {s : Set γ}

/-
**Metric.closedBall_zero** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：∀ {γ : Type w} [inst : MetricSpace γ] {x : γ}, Metric.closedBall x 0 = {x}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `dist_le_zero`：dist_le_zero {x y : γ} : dist x y <= 0 ↔ x = y
-/
@[simp] theorem closedBall_zero : closedBall x 0 = {x} := Set.ext fun _ => dist_le_zero
/-
**Metric.sphere_zero** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：∀ {γ : Type w} [inst : MetricSpace γ] {x : γ}, Metric.sphere x 0 = {x}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `dist_eq_zero`：dist_eq_zero {x y : γ} : dist x y = 0 ↔ x = y
-/
@[simp] theorem sphere_zero : sphere x 0 = {x} := Set.ext fun _ => dist_eq_zero
/-
**Metric.subsingleton_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：subsingleton_closedBall (x : γ) {r : Real} (hr : r <= 0) : (closedBall x r
).Subsingleton
参数：x : γ；hr : r <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.lt_or_eq`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a < b ∨ a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.closedBall_eq_empty`：closedBall_eq_empty : closedBall x ε = ∅ ↔ ε
 < 0
· 使用定理 `Set.subsingleton_empty`：subsingleton_empty : (∅ : Set α).Subsingleton
· 使用定理 `Metric.closedBall_zero`：∀ {γ : Type w} [inst : MetricSpace γ] {x : γ}, M
etric.closedBall x 0 = {x}
· 使用定理 `Set.subsingleton_singleton`：subsingleton_singleton {a} : ({a} : Set α).S
ubsingleton
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem subsingleton_closedBall (x : γ) {r : ℝ} (hr : r ≤ 0) : (closedBall x r).Subsingleton := by
  rcases hr.lt_or_eq with (hr | rfl)
  · rw [closedBall_eq_empty.2 hr]
    exact subsingleton_empty
  · rw [closedBall_zero]
    exact subsingleton_singleton
/-
**Metric.subsingleton_sphere** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：subsingleton_sphere (x : γ) {r : Real} (hr : r <= 0) : (sphere x r).Subsin
gleton
参数：x : γ；hr : r <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.anti`：∀ {α : Type u} {s t : Set α}, t.Subsingleton → s 
⊆ t → s.Subsingleton
· 使用定理 `Metric.subsingleton_closedBall`：subsingleton_closedBall (x : γ) {r : Rea
l} (hr : r <= 0) : (closedBall x r).Subsingleton
· 使用定理 `Metric.sphere_subset_closedBall`：sphere_subset_closedBall : sphere x ε s
ubseteq closedBall x ε
-/
theorem subsingleton_sphere (x : γ) {r : ℝ} (hr : r ≤ 0) : (sphere x r).Subsingleton :=
  (subsingleton_closedBall x hr).anti sphere_subset_closedBall

end Metric

/-- Build a new metric space from an old one where the bundled uniform structure is provably
(but typically non-definitionaly) equal to some given uniform structure.
See Note [forgetful inheritance].
See Note [reducible non-instances].
-/
/-
**MetricSpace.replaceUniformity** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：MetricSpace.replaceUniformity {γ} [U : UniformSpace γ] (m : MetricSpace γ)
 (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace]) : MetricSpace γ where toPseud
oMetricSpace
参数：m : MetricSpace γ；H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace]。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MetricSpace.eq_of_dist_eq_zero`：∀ {α : Type u} [self : MetricSpace α] {x
 y : α}, dist x y = 0 → x = y

--- 原说明 ---
Build a new metric space from an old one where the bundled uniform structure is 
provably
(but typically non-definitionaly) equal to some given uniform structure.
See Note [forgetful inheritance].
See Note [reducible non-instances].
-/
abbrev MetricSpace.replaceUniformity {γ} [U : UniformSpace γ] (m : MetricSpace γ)
    (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace]) : MetricSpace γ where
  toPseudoMetricSpace := PseudoMetricSpace.replaceUniformity m.toPseudoMetricSpace H
  eq_of_dist_eq_zero := @eq_of_dist_eq_zero _ _
/-
**MetricSpace.replaceUniformity_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MetricSpace.replaceUniformity_eq {γ} [U : UniformSpace γ] (m : MetricSpace
 γ) (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace]) : m.replaceUniformity H = 
m
参数：m : MetricSpace γ；H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MetricSpace.ext`：MetricSpace.ext {α : Type*} {m m' : MetricSpace α} (h :
 m.toDist = m'.toDist) : m = m'
· 使用定理 `Dist.ext`：∀ {α : Type u_3} {x y : Dist α}, dist = dist → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem MetricSpace.replaceUniformity_eq {γ} [U : UniformSpace γ] (m : MetricSpace γ)
    (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace]) : m.replaceUniformity H = m := by
  ext; rfl

/-- Build a new metric space from an old one where the bundled topological structure is provably
(but typically non-definitionaly) equal to some given topological structure.
See Note [forgetful inheritance].
See Note [reducible non-instances].
-/
/-
**MetricSpace.replaceTopology** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：MetricSpace.replaceTopology {γ} [U : TopologicalSpace γ] (m : MetricSpace 
γ) (H : U = m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace) : MetricSpa
ce γ
参数：m : MetricSpace γ；H : U = m.toPseudoMetricSpace.toUniformSpace.toTopologicalS
pace。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Build a new metric space from an old one where the bundled topological structure
 is provably
(but typically non-definitionaly) equal to some given topological structure.
See Note [forgetful inheritance].
See Note [reducible non-instances].
-/
abbrev MetricSpace.replaceTopology {γ} [U : TopologicalSpace γ] (m : MetricSpace γ)
    (H : U = m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace) : MetricSpace γ :=
  @MetricSpace.replaceUniformity γ (m.toUniformSpace.replaceTopology H) m rfl
/-
**MetricSpace.replaceTopology_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MetricSpace.replaceTopology_eq {γ} [U : TopologicalSpace γ] (m : MetricSpa
ce γ) (H : U = m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace) : m.repl
aceTopology H = m
参数：m : MetricSpace γ；H : U = m.toPseudoMetricSpace.toUniformSpace.toTopologicalS
pace。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MetricSpace.ext`：MetricSpace.ext {α : Type*} {m m' : MetricSpace α} (h :
 m.toDist = m'.toDist) : m = m'
· 使用定理 `Dist.ext`：∀ {α : Type u_3} {x y : Dist α}, dist = dist → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem MetricSpace.replaceTopology_eq {γ} [U : TopologicalSpace γ] (m : MetricSpace γ)
    (H : U = m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace) :
    m.replaceTopology H = m := by
  ext; rfl

/-- Build a new metric space from an old one where the bundled bornology structure is provably
(but typically non-definitionaly) equal to some given bornology structure.
See Note [forgetful inheritance].
See Note [reducible non-instances].
-/
/-
**MetricSpace.replaceBornology** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：MetricSpace.replaceBornology {α} [B : Bornology α] (m : MetricSpace α) (H 
: forall s, @IsBounded _ B s ↔ @IsBounded _ PseudoMetricSpace.toBornology s) : M
etricSpace α
参数：m : MetricSpace α；H : forall s, @IsBounded _ B s ↔ @IsBounded _ PseudoMetricS
pace.toBornology s。
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
· 使用定理 `PseudoMetricSpace.cobounded_sets`：∀ {α : Type u} [self : PseudoMetricSpa
ce α], (Bornology.cobounded α).sets = {s | ∃ C, ∀ x ∈ sᶜ, ∀ y ∈ sᶜ, dist x y ≤ C
}
· 使用定理 `MetricSpace.eq_of_dist_eq_zero`：∀ {α : Type u} [self : MetricSpace α] {x
 y : α}, dist x y = 0 → x = y

--- 原说明 ---
Build a new metric space from an old one where the bundled bornology structure i
s provably
(but typically non-definitionaly) equal to some given bornology structure.
See Note [forgetful inheritance].
See Note [reducible non-instances].
-/
abbrev MetricSpace.replaceBornology {α} [B : Bornology α] (m : MetricSpace α)
    (H : ∀ s, @IsBounded _ B s ↔ @IsBounded _ PseudoMetricSpace.toBornology s) : MetricSpace α :=
  { PseudoMetricSpace.replaceBornology _ H, m with toBornology := B }
/-
**MetricSpace.replaceBornology_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MetricSpace.replaceBornology_eq {α} [m : MetricSpace α] [B : Bornology α] 
(H : forall s, @IsBounded _ B s ↔ @IsBounded _ PseudoMetricSpace.toBornology s) 
: MetricSpace.replaceBornology _ H = m
参数：H : forall s, @IsBounded _ B s ↔ @IsBounded _ PseudoMetricSpace.toBornology s
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MetricSpace.ext`：MetricSpace.ext {α : Type*} {m m' : MetricSpace α} (h :
 m.toDist = m'.toDist) : m = m'
· 使用定理 `Dist.ext`：∀ {α : Type u_3} {x y : Dist α}, dist = dist → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem MetricSpace.replaceBornology_eq {α} [m : MetricSpace α] [B : Bornology α]
    (H : ∀ s, @IsBounded _ B s ↔ @IsBounded _ PseudoMetricSpace.toBornology s) :
    MetricSpace.replaceBornology _ H = m := by
  ext
  rfl
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MetricSpace Empty where
  dist _ _ := 0
  dist_self _ := rfl
  dist_comm _ _ := rfl
  edist _ _ := 0
  eq_of_dist_eq_zero _ := Subsingleton.elim _ _
  dist_triangle _ _ _ := show (0 : ℝ) ≤ 0 + 0 by rw [add_zero]
  toUniformSpace := inferInstance
  uniformity_dist := Subsingleton.elim _ _
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MetricSpace PUnit.{u + 1} where
  dist _ _ := 0
  dist_self _ := rfl
  dist_comm _ _ := rfl
  edist _ _ := 0
  eq_of_dist_eq_zero _ := Subsingleton.elim _ _
  dist_triangle _ _ _ := show (0 : ℝ) ≤ 0 + 0 by rw [add_zero]
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

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Dist (Additive X) := ‹Dist X›
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Dist (Multiplicative X) := ‹Dist X›
/-
**dist_ofMul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : Type u_1} [inst : Dist X] (a b : X), dist (Additive.ofMul a) (Addit
ive.ofMul b) = dist a b
参数：a b : X；Additive.ofMul a；Additive.ofMul b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem dist_ofMul (a b : X) : dist (ofMul a) (ofMul b) = dist a b := rfl
/-
**dist_ofAdd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : Type u_1} [inst : Dist X] (a b : X), dist (Multiplicative.ofAdd a) 
(Multiplicative.ofAdd b) = dist a b
参数：a b : X；Multiplicative.ofAdd a；Multiplicative.ofAdd b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem dist_ofAdd (a b : X) : dist (ofAdd a) (ofAdd b) = dist a b := rfl
/-
**dist_toMul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : Type u_1} [inst : Dist X] (a b : Additive X), dist (Additive.toMul 
a) (Additive.toMul b) = dist a b
参数：a b : Additive X；Additive.toMul a；Additive.toMul b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem dist_toMul (a b : Additive X) : dist a.toMul b.toMul = dist a b := rfl
/-
**dist_toAdd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : Type u_1} [inst : Dist X] (a b : Multiplicative X),   dist (Multipl
icative.toAdd a) (Multiplicative.toAdd b) = dist a b
参数：a b : Multiplicative X；Multiplicative.toAdd a；Multiplicative.toAdd b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem dist_toAdd (a b : Multiplicative X) : dist a.toAdd b.toAdd = dist a b := rfl

end

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MetricSpace X] : MetricSpace (Additive X) := ‹MetricSpace X›
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MetricSpace X] : MetricSpace (Multiplicative X) := ‹MetricSpace X›

/-!
### Order dual

The distance on this type synonym is inherited without change.
-/

open OrderDual

section

variable [Dist X]

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Dist Xᵒᵈ := ‹Dist X›
/-
**dist_toDual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : Type u_1} [inst : Dist X] (a b : X), dist (OrderDual.toDual a) (Ord
erDual.toDual b) = dist a b
参数：a b : X；OrderDual.toDual a；OrderDual.toDual b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem dist_toDual (a b : X) : dist (toDual a) (toDual b) = dist a b := rfl
/-
**dist_ofDual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : Type u_1} [inst : Dist X] (a b : Xᵒᵈ), dist (OrderDual.ofDual a) (O
rderDual.ofDual b) = dist a b
参数：a b : Xᵒᵈ；OrderDual.ofDual a；OrderDual.ofDual b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem dist_ofDual (a b : Xᵒᵈ) : dist (ofDual a) (ofDual b) = dist a b := rfl

end

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MetricSpace X] : MetricSpace Xᵒᵈ := ‹MetricSpace X›
