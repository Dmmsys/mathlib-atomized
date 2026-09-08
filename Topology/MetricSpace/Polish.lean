/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.MetricSpace.PiNat
public import Mathlib.Topology.Metrizable.CompletelyMetrizable
public import Mathlib.Topology.Sets.Opens

/-!
# Polish spaces

A topological space is Polish if its topology is second-countable and there exists a compatible
complete metric. This is the class of spaces that is well-behaved with respect to measure theory.
In this file, we establish the basic properties of Polish spaces.

## Main definitions and results

* `PolishSpace α` is a mixin typeclass on a topological space, requiring that the topology is
  second-countable and compatible with a complete metric. To endow the space with such a metric,
  use in a proof `letI := upgradeIsCompletelyMetrizable α`.
* `IsClosed.polishSpace`: a closed subset of a Polish space is Polish.
* `IsOpen.polishSpace`: an open subset of a Polish space is Polish.
* `exists_nat_nat_continuous_surjective`: any nonempty Polish space is the continuous image
  of the fundamental Polish space `ℕ → ℕ`.

A fundamental property of Polish spaces is that one can put finer topologies, still Polish,
with additional properties:

* `exists_polishSpace_forall_le`: on a topological space, consider countably many topologies
  `t n`, all Polish and finer than the original topology. Then there exists another Polish
  topology which is finer than all the `t n`.
* `IsClopenable s` is a property of a subset `s` of a topological space, requiring that there
  exists a finer topology, which is Polish, for which `s` becomes open and closed. We show that
  this property is satisfied for open sets, closed sets, for complements, and for countable unions.
  Once Borel-measurable sets are defined in later files, it will follow that any Borel-measurable
  set is clopenable. Once the Lusin-Souslin theorem is proved using analytic sets, we will even
  show that a set is clopenable if and only if it is Borel-measurable, see
  `isClopenable_iff_measurableSet`.
-/

@[expose] public section

noncomputable section

open Filter Function Metric TopologicalSpace Set Topology
open scoped Uniformity

variable {α : Type*} {β : Type*}

/-! ### Basic properties of Polish spaces -/


/-- A Polish space is a topological space with second countable topology, that can be endowed
with a metric for which it is complete.

To endow a Polish space with a complete metric space structure, do
`letI := upgradeIsCompletelyMetrizable α`.
-/
/-
**PolishSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_3) → [h : TopologicalSpace α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Polish space is a topological space with second countable topology, that can b
e endowed
with a metric for which it is complete.

To endow a Polish space with a complete metric space structure, do
`letI := upgradeIsCompletelyMetrizable α`.
-/
class PolishSpace (α : Type*) [h : TopologicalSpace α] : Prop
    extends SecondCountableTopology α, IsCompletelyMetrizableSpace α
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [TopologicalSpace α] [SeparableSpace α] [IsCompletelyMetrizableSpace α] :
    PolishSpace α := by
  let := upgradeIsCompletelyMetrizable α
  have := UniformSpace.secondCountable_of_separable α
  constructor

namespace PolishSpace

/-- Any nonempty Polish space is the continuous image of the fundamental space `ℕ → ℕ`. -/
/-
**PolishSpace.exists_nat_nat_continuous_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Po
lishSpace`。
形式化陈述：exists_nat_nat_continuous_surjective (α : Type*) [TopologicalSpace α] [Pol
ishSpace α] [Nonempty α] : exists f : (Nat -> Nat) -> α, Continuous f ∧ Surjecti
ve f
参数：α : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_nat_nat_continuous_surjective_of_completeSpace`：exists_nat_nat_co
ntinuous_surjective_of_completeSpace (α : Type*) [MetricSpace α] [CompleteSpace 
α] [SecondCountableTopology α] [Nonempty α]…
· 使用定理 `PolishSpace.toIsCompletelyMetrizableSpace`：∀ {α : Type u_3} {h : Topolog
icalSpace α} [self : PolishSpace α], TopologicalSpace.IsCompletelyMetrizableSpac
e α
· 使用定理 `TopologicalSpace.UpgradedIsCompletelyMetrizableSpace.toCompleteSpace`：∀ 
{X : Type u_3} [self : TopologicalSpace.UpgradedIsCompletelyMetrizableSpace X], 
CompleteSpace X
· 使用定理 `PolishSpace.toSecondCountableTopology`：∀ {α : Type u_3} {h : Topological
Space α} [self : PolishSpace α], SecondCountableTopology α

--- 原说明 ---
Any nonempty Polish space is the continuous image of the fundamental space `ℕ → 
ℕ`.
-/
theorem exists_nat_nat_continuous_surjective (α : Type*) [TopologicalSpace α] [PolishSpace α]
    [Nonempty α] : ∃ f : (ℕ → ℕ) → α, Continuous f ∧ Surjective f :=
  letI := upgradeIsCompletelyMetrizable α
  exists_nat_nat_continuous_surjective_of_completeSpace α

/-- Given a closed embedding into a Polish space, the source space is also Polish. -/
/-
**PolishSpace._root_.Topology.IsClosedEmbedding.polishSpace** 是 Mathlib 中的一个定理，位
于命名空间 `PolishSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a closed embedding into a Polish space, the source space is also Polish.
-/
theorem _root_.Topology.IsClosedEmbedding.polishSpace [TopologicalSpace α] [TopologicalSpace β]
    [PolishSpace β] {f : α → β} (hf : IsClosedEmbedding f) : PolishSpace α := by
  let := upgradeIsCompletelyMetrizable β
  let : MetricSpace α := hf.isEmbedding.comapMetricSpace f
  have : SecondCountableTopology α := hf.isEmbedding.secondCountableTopology
  have : CompleteSpace α := by
    rw [completeSpace_iff_isComplete_range hf.isEmbedding.to_isometry.isUniformInducing]
    exact hf.isClosed_range.isComplete
  infer_instance

/-- Pulling back a Polish topology under an equiv gives again a Polish topology. -/
/-
**PolishSpace._root_.Equiv.polishSpace_induced** 是 Mathlib 中的一个定理，位于命名空间 `Polish
Space`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pulling back a Polish topology under an equiv gives again a Polish topology.
-/
theorem _root_.Equiv.polishSpace_induced [t : TopologicalSpace β] [PolishSpace β] (f : α ≃ β) :
    @PolishSpace α (t.induced f) :=
  letI : TopologicalSpace α := t.induced f
  (f.toHomeomorphOfIsInducing ⟨rfl⟩).isClosedEmbedding.polishSpace

/-- A closed subset of a Polish space is also Polish. -/
/-
**PolishSpace._root_.IsClosed.polishSpace** 是 Mathlib 中的一个定理，位于命名空间 `PolishSpace
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A closed subset of a Polish space is also Polish.
-/
theorem _root_.IsClosed.polishSpace [TopologicalSpace α] [PolishSpace α] {s : Set α}
    (hs : IsClosed s) : PolishSpace s :=
  hs.isClosedEmbedding_subtypeVal.polishSpace
/-
**PolishSpace._root_.CompletePseudometrizable.iInf** 是 Mathlib 中的一个定理，位于命名空间 `Po
lishSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.CompletePseudometrizable.iInf {ι : Type*} [Countable ι]
    {t : ι → TopologicalSpace α} (ht₀ : ∃ t₀, @T2Space α t₀ ∧ ∀ i, t i ≤ t₀)
    (ht : ∀ i, ∃ u : UniformSpace α, CompleteSpace α ∧ 𝓤[u].IsCountablyGenerated ∧
      u.toTopologicalSpace = t i) :
    ∃ u : UniformSpace α, CompleteSpace α ∧
      𝓤[u].IsCountablyGenerated ∧ u.toTopologicalSpace = ⨅ i, t i := by
  choose u hcomp hcount hut using ht
  obtain rfl : t = fun i ↦ (u i).toTopologicalSpace := (funext hut).symm
  refine ⟨⨅ i, u i, .iInf hcomp ht₀, ?_, UniformSpace.toTopologicalSpace_iInf⟩
  rw [iInf_uniformity]
  infer_instance
/-
**PolishSpace.iInf** 是 Mathlib 中的一个定理，位于命名空间 `PolishSpace`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_3} [Countable ι] {t : ι → TopologicalSpace α}
,   (∃ i₀, ∀ (i : ι), t i ≤ t i₀) → (∀ (i : ι), PolishSpace α) → PolishSpace α
参数：∃ i₀, ∀ (i : ι), t i ≤ t i₀；∀ (i : ι), PolishSpace α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompletePseudometrizable.iInf`：∀ {α : Type u_1} {ι : Type u_3} [Countabl
e ι] {t : ι → TopologicalSpace α},   (∃ t₀, T2Space α ∧ ∀ (i : ι), t i ≤ t₀) →  
   (∀ (i : ι), ∃ u,…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.MetrizableSpace`：∀ {X : Typ
e u_1} [inst : TopologicalSpace X] [TopologicalSpace.IsCompletelyMetrizableSpace
 X],   TopologicalSpace.MetrizableSpace X
· 使用定理 `PolishSpace.toIsCompletelyMetrizableSpace`：∀ {α : Type u_3} {h : Topolog
icalSpace α} [self : PolishSpace α], TopologicalSpace.IsCompletelyMetrizableSpac
e α
· 使用定理 `TopologicalSpace.UpgradedIsCompletelyMetrizableSpace.toCompleteSpace`：∀ 
{X : Type u_3} [self : TopologicalSpace.UpgradedIsCompletelyMetrizableSpace X], 
CompleteSpace X
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `TopologicalSpace.secondCountableTopology_iInf`：secondCountableTopology_i
Inf {α ι} [Countable ι] {t : ι -> TopologicalSpace α} (ht : forall i, @SecondCou
ntableTopology α (t i)) : @SecondCo…
· 使用定理 `PolishSpace.toSecondCountableTopology`：∀ {α : Type u_3} {h : Topological
Space α} [self : PolishSpace α], SecondCountableTopology α
· 使用定理 `t1Space_antitone`：t1Space_antitone {X} : Antitone (@T1Space X)
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `T3Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T3
Space X], T0Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `instT4SpaceOfT1SpaceOfNormalSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [T1Space X] [NormalSpace X], T4Space X
· 使用定理 `CompletelyNormalSpace.toNormalSpace`：∀ {X : Type u_1} [inst : Topologica
lSpace X] [CompletelyNormalSpace X], NormalSpace X
· 使用定理 `UniformSpace.completelyNormalSpace_of_isCountablyGenerated_uniformity`：∀
 {α : Type u} [inst : UniformSpace α] [(uniformity α).IsCountablyGenerated], Com
pletelyNormalSpace α
-/
protected theorem iInf {ι : Type*} [Countable ι] {t : ι → TopologicalSpace α}
    (ht₀ : ∃ i₀, ∀ i, t i ≤ t i₀) (ht : ∀ i, @PolishSpace α (t i)) : @PolishSpace α (⨅ i, t i) := by
  rcases ht₀ with ⟨i₀, hi₀⟩
  rcases CompletePseudometrizable.iInf ⟨t i₀, letI := t i₀; haveI := ht i₀; inferInstance, hi₀⟩
    fun i ↦
      letI := t i; haveI := ht i; letI := upgradeIsCompletelyMetrizable α
      ⟨inferInstance, inferInstance, inferInstance, rfl⟩
    with ⟨u, hcomp, hcount, htop⟩
  rw [← htop]
  have : @SecondCountableTopology α u.toTopologicalSpace :=
    htop.symm ▸ secondCountableTopology_iInf fun i ↦ letI := t i; (ht i).toSecondCountableTopology
  have : @T1Space α u.toTopologicalSpace :=
    htop.symm ▸ t1Space_antitone (iInf_le _ i₀) (by let := t i₀; have := ht i₀; infer_instance)
  infer_instance

/-- Given a Polish space, and countably many finer Polish topologies, there exists another Polish
topology which is finer than all of them. -/
/-
**PolishSpace.exists_polishSpace_forall_le** 是 Mathlib 中的一个定理，位于命名空间 `PolishSpac
e`。
形式化陈述：exists_polishSpace_forall_le {ι : Type*} [Countable ι] [t : TopologicalSpa
ce α] [p : PolishSpace α] (m : ι -> TopologicalSpace α) (hm : forall n, m n <= t
) (h'm : forall n, @PolishSpace α (m n)) : exists t' : TopologicalSpace α, (fora
ll n, t' <= m n) ∧ t' <= t ∧ @PolishSpace α t'
参数：m : ι -> TopologicalSpace α；hm : forall n, m n <= t；h'm : forall n, @PolishSp
ace α (m n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
· 使用定理 `PolishSpace.iInf`：∀ {α : Type u_1} {ι : Type u_3} [Countable ι] {t : ι →
 TopologicalSpace α},   (∃ i₀, ∀ (i : ι), t i ≤ t i₀) → (∀ (i : ι), PolishSpace 
α) → P…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Option.forall`：∀ {α : Type u_1} {p : Option α → Prop}, (∀ (x : Option α)
, p x) ↔ p none ∧ ∀ (x : α), p (some x)
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
Given a Polish space, and countably many finer Polish topologies, there exists a
nother Polish
topology which is finer than all of them.
-/
theorem exists_polishSpace_forall_le {ι : Type*} [Countable ι] [t : TopologicalSpace α]
    [p : PolishSpace α] (m : ι → TopologicalSpace α) (hm : ∀ n, m n ≤ t)
    (h'm : ∀ n, @PolishSpace α (m n)) :
    ∃ t' : TopologicalSpace α, (∀ n, t' ≤ m n) ∧ t' ≤ t ∧ @PolishSpace α t' :=
  ⟨⨅ i : Option ι, i.elim t m, fun i ↦ iInf_le _ (some i), iInf_le _ none,
    .iInf ⟨none, Option.forall.2 ⟨le_rfl, hm⟩⟩ <| Option.forall.2 ⟨p, h'm⟩⟩
/-
**PolishSpace.** 是 Mathlib 中的一个实例，位于命名空间 `PolishSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PolishSpace ENNReal :=
  ENNReal.orderIsoUnitIntervalBirational.toHomeomorph.isClosedEmbedding.polishSpace

end PolishSpace

/-!
### An open subset of a Polish space is Polish

To prove this fact, one needs to construct another metric, giving rise to the same topology,
for which the open subset is complete. This is not obvious, as for instance `(0,1) ⊆ ℝ` is not
complete for the usual metric of `ℝ`: one should build a new metric that blows up close to the
boundary.
-/

namespace TopologicalSpace.Opens

variable [MetricSpace α] {s : Opens α}

/-- A type synonym for a subset `s` of a metric space, on which we will construct another metric
for which it will be complete. -/
/-
**TopologicalSpace.Opens.CompleteCopy** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpac
e.Opens`。
形式化陈述：CompleteCopy {α : Type*} [MetricSpace α] (s : Opens α) : Type _
参数：s : Opens α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type synonym for a subset `s` of a metric space, on which we will construct an
other metric
for which it will be complete.
-/
def CompleteCopy {α : Type*} [MetricSpace α] (s : Opens α) : Type _ := s

namespace CompleteCopy

/-- A distance on an open subset `s` of a metric space, designed to make it complete.  It is given
by `dist' x y = dist x y + |1 / dist x sᶜ - 1 / dist y sᶜ|`, where the second term blows up close to
the boundary to ensure that Cauchy sequences for `dist'` remain well inside `s`. -/
/-
**TopologicalSpace.Opens.CompleteCopy.instDist** 是 Mathlib 中的一个实例，位于命名空间 `Topolo
gicalSpace.Opens.CompleteCopy`。
形式化陈述：instDist : Dist (CompleteCopy s) where dist x y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A distance on an open subset `s` of a metric space, designed to make it complete
.  It is given
by `dist' x y = dist x y + |1 / dist x sᶜ - 1 / dist y sᶜ|`, where the second te
rm blows up close to
the boundary to ensure that Cauchy sequences for `dist'` remain well inside `s`.
-/
instance instDist : Dist (CompleteCopy s) where
  dist x y := dist x.1 y.1 + abs (1 / infDist x.1 sᶜ - 1 / infDist y.1 sᶜ)
/-
**TopologicalSpace.Opens.CompleteCopy.dist_eq** 是 Mathlib 中的一个定理，位于命名空间 `Topolog
icalSpace.Opens.CompleteCopy`。
形式化陈述：dist_eq (x y : CompleteCopy s) : dist x y = dist x.1 y.1 + abs (1 / infDis
t x.1 sᶜ - 1 / infDist y.1 sᶜ)
参数：x y : CompleteCopy s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dist_eq (x y : CompleteCopy s) :
    dist x y = dist x.1 y.1 + abs (1 / infDist x.1 sᶜ - 1 / infDist y.1 sᶜ) :=
  rfl
/-
**TopologicalSpace.Opens.CompleteCopy.dist_val_le_dist** 是 Mathlib 中的一个定理，位于命名空间
 `TopologicalSpace.Opens.CompleteCopy`。
形式化陈述：dist_val_le_dist (x y : CompleteCopy s) : dist x.1 y.1 <= dist x y
参数：x y : CompleteCopy s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_add_of_nonneg_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1
 : LE α] [AddLeftMono α] {a b : α}, 0 ≤ b → a ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem dist_val_le_dist (x y : CompleteCopy s) : dist x.1 y.1 ≤ dist x y :=
  le_add_of_nonneg_right (abs_nonneg _)
/-
**TopologicalSpace.Opens.CompleteCopy.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpa
ce.Opens.CompleteCopy`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : TopologicalSpace (CompleteCopy s) := inferInstanceAs (TopologicalSpace s)
/-
**TopologicalSpace.Opens.CompleteCopy.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpa
ce.Opens.CompleteCopy`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SecondCountableTopology α] : SecondCountableTopology (CompleteCopy s) :=
  inferInstanceAs (SecondCountableTopology s)
/-
**TopologicalSpace.Opens.CompleteCopy.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpa
ce.Opens.CompleteCopy`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : T0Space (CompleteCopy s) := inferInstanceAs (T0Space s)

/--
A metric space structure on a subset `s` of a metric space, designed to make it complete
if `s` is open. It is given by `dist' x y = dist x y + |1 / dist x sᶜ - 1 / dist y sᶜ|`, where the
second term blows up close to the boundary to ensure that Cauchy sequences for `dist'` remain well
inside `s`.

This definition ensures the `TopologicalSpace` structure on
`TopologicalSpace.Opens.CompleteCopy s` is definitionally equal to the original one.
-/
/-
**TopologicalSpace.Opens.CompleteCopy.instMetricSpace** 是 Mathlib 中的一个实例，位于命名空间 
`TopologicalSpace.Opens.CompleteCopy`。
形式化陈述：instMetricSpace : MetricSpace (CompleteCopy s)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.CompleteCopy.instT0Space`：∀ {α : Type u_1} [inst 
: MetricSpace α] {s : TopologicalSpace.Opens α}, T0Space s.CompleteCopy

--- 原说明 ---
A metric space structure on a subset `s` of a metric space, designed to make it 
complete
if `s` is open. It is given by `dist' x y = dist x y + |1 / dist x sᶜ - 1 / dist
 y sᶜ|`, where the
second term blows up close to the boundary to ensure that Cauchy sequences for `
dist'` remain well
inside `s`.

This definition ensures the `TopologicalSpace` structure on
`TopologicalSpace.Opens.CompleteCopy s` is definitionally equal to the original 
one.
-/
instance instMetricSpace : MetricSpace (CompleteCopy s) := by
  refine @MetricSpace.ofT0PseudoMetricSpace (CompleteCopy s)
    (.ofDistTopology dist (fun _ ↦ ?_) (fun _ _ ↦ ?_) (fun x y z ↦ ?_) fun t ↦ ?_) _
  · simp only [dist_eq, dist_self, one_div, sub_self, abs_zero, add_zero]
  · simp only [dist_eq, dist_comm, abs_sub_comm]
  · calc
      dist x z = dist x.1 z.1 + |1 / infDist x.1 sᶜ - 1 / infDist z.1 sᶜ| := rfl
      _ ≤ dist x.1 y.1 + dist y.1 z.1 + (|1 / infDist x.1 sᶜ - 1 / infDist y.1 sᶜ| +
            |1 / infDist y.1 sᶜ - 1 / infDist z.1 sᶜ|) :=
        add_le_add (dist_triangle _ _ _) (dist_triangle (1 / infDist _ _) _ _)
      _ = dist x y + dist y z := add_add_add_comm ..
  · refine ⟨fun h x hx ↦ ?_, fun h ↦ isOpen_iff_mem_nhds.2 fun x hx ↦ ?_⟩
    · rcases (Metric.isOpen_iff (α := s)).1 h x hx with ⟨ε, ε0, hε⟩
      exact ⟨ε, ε0, fun y hy ↦ hε <| (dist_comm _ _).trans_lt <| (dist_val_le_dist _ _).trans_lt hy⟩
    · rcases h x hx with ⟨ε, ε0, hε⟩
      simp only [dist_eq, one_div] at hε
      have : Tendsto (fun y : s ↦ dist x.1 y.1 + |(infDist x.1 sᶜ)⁻¹ - (infDist y.1 sᶜ)⁻¹|)
          (𝓝 x) (𝓝 (dist x.1 x.1 + |(infDist x.1 sᶜ)⁻¹ - (infDist x.1 sᶜ)⁻¹|)) := by
        refine (tendsto_const_nhds.dist continuous_subtype_val.continuousAt).add
          (tendsto_const_nhds.sub <| ?_).abs
        refine (continuousAt_inv_infDist_pt ?_).comp continuous_subtype_val.continuousAt
        rw [s.isOpen.isClosed_compl.closure_eq, mem_compl_iff, not_not]
        exact x.2
      simp only [dist_self, sub_self, abs_zero, zero_add] at this
      exact mem_of_superset (this <| gt_mem_nhds ε0) hε
/-
**TopologicalSpace.Opens.CompleteCopy.instCompleteSpace** 是 Mathlib 中的一个实例，位于命名空
间 `TopologicalSpace.Opens.CompleteCopy`。
形式化陈述：instCompleteSpace [CompleteSpace α] : CompleteSpace (CompleteCopy s)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.complete_of_convergent_controlled_sequences`：Metric.complete_of_c
onvergent_controlled_sequences (B : Nat -> Real) (hB : forall n, 0 < B n) (H : f
orall u : Nat -> α, (forall N n m : Nat,…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `cauchySeq_of_le_tendsto_0`：cauchySeq_of_le_tendsto_0 {s : β -> α} (b : β
 -> Real) (h : forall n m N : β, N <= n -> N <= m -> dist (s n) (s m) <= b N) (h
₀ : Tendsto b a…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `TopologicalSpace.Opens.CompleteCopy.dist_val_le_dist`：dist_val_le_dist (
x y : CompleteCopy s) : dist x.1 y.1 <= dist x y
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `tendsto_pow_atTop_nhds_zero_of_lt_one`：tendsto_pow_atTop_nhds_zero_of_lt
_one {𝕜 : Type*} [Semifield 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [ExistsAd
dOfLE 𝕜] [Archimedean 𝕜] [T…
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_lt_true`：isNNRat_lt_true [Semiring α] [Line
arOrder α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Nat} -> {da db : Nat}
 -> IsNNRat a na da -> IsN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
（共 77 条，此处仅展示前 30 条）
-/
instance instCompleteSpace [CompleteSpace α] : CompleteSpace (CompleteCopy s) := by
  refine Metric.complete_of_convergent_controlled_sequences ((1 / 2) ^ ·) (by simp) fun u hu ↦ ?_
  have A : CauchySeq fun n => (u n).1 := by
    refine cauchySeq_of_le_tendsto_0 (fun n : ℕ => (1 / 2) ^ n) (fun n m N hNn hNm => ?_) ?_
    · exact (dist_val_le_dist (u n) (u m)).trans (hu N n m hNn hNm).le
    · exact tendsto_pow_atTop_nhds_zero_of_lt_one (by simp) (by norm_num)
  obtain ⟨x, xlim⟩ : ∃ x, Tendsto (fun n => (u n).1) atTop (𝓝 x) := cauchySeq_tendsto_of_complete A
  by_cases xs : x ∈ s
  · exact ⟨⟨x, xs⟩, tendsto_subtype_rng.2 xlim⟩
  obtain ⟨C, hC⟩ : ∃ C, ∀ n, 1 / infDist (u n).1 sᶜ < C := by
    refine ⟨(1 / 2) ^ 0 + 1 / infDist (u 0).1 sᶜ, fun n ↦ ?_⟩
    rw [← sub_lt_iff_lt_add]
    calc
      _ ≤ |1 / infDist (u n).1 sᶜ - 1 / infDist (u 0).1 sᶜ| := le_abs_self _
      _ = |1 / infDist (u 0).1 sᶜ - 1 / infDist (u n).1 sᶜ| := abs_sub_comm _ _
      _ ≤ dist (u 0) (u n) := le_add_of_nonneg_left dist_nonneg
      _ < (1 / 2) ^ 0 := hu 0 0 n le_rfl n.zero_le
  have Cpos : 0 < C := lt_of_le_of_lt (div_nonneg zero_le_one infDist_nonneg) (hC 0)
  have Hmem : ∀ {y}, y ∈ s ↔ 0 < infDist y sᶜ := fun {y} ↦ by
    rw [← s.isOpen.isClosed_compl.notMem_iff_infDist_pos ⟨x, xs⟩]; exact not_not.symm
  have I : ∀ n, 1 / C ≤ infDist (u n).1 sᶜ := fun n ↦ by
    have : 0 < infDist (u n).1 sᶜ := Hmem.1 (u n).2
    rw [div_le_iff₀' Cpos]
    exact (div_le_iff₀ this).1 (hC n).le
  have I' : 1 / C ≤ infDist x sᶜ :=
    have : Tendsto (fun n => infDist (u n).1 sᶜ) atTop (𝓝 (infDist x sᶜ)) :=
      ((continuous_infDist_pt (sᶜ : Set α)).tendsto x).comp xlim
    ge_of_tendsto' this I
  exact absurd (Hmem.2 <| lt_of_lt_of_le (div_pos one_pos Cpos) I') xs

/-- An open subset of a Polish space is also Polish. -/
/-
**TopologicalSpace.Opens.CompleteCopy._root_.IsOpen.polishSpace** 是 Mathlib 中的一个
定理，位于命名空间 `TopologicalSpace.Opens.CompleteCopy`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An open subset of a Polish space is also Polish.
-/
theorem _root_.IsOpen.polishSpace {α : Type*} [TopologicalSpace α] [PolishSpace α] {s : Set α}
    (hs : IsOpen s) : PolishSpace s := by
  let := upgradeIsCompletelyMetrizable α
  lift s to Opens α using hs
  exact inferInstanceAs (PolishSpace s.CompleteCopy)

end CompleteCopy

end TopologicalSpace.Opens

namespace PolishSpace

/-! ### Clopenable sets in Polish spaces -/

/-- A set in a topological space is clopenable if there exists a finer Polish topology for which
this set is open and closed. It turns out that this notion is equivalent to being Borel-measurable,
but this is nontrivial (see `isClopenable_iff_measurableSet`). -/
/-
**PolishSpace.IsClopenable** 是 Mathlib 中的一个定义，位于命名空间 `PolishSpace`。
形式化陈述：IsClopenable [t : TopologicalSpace α] (s : Set α) : Prop
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set in a topological space is clopenable if there exists a finer Polish topolo
gy for which
this set is open and closed. It turns out that this notion is equivalent to bein
g Borel-measurable,
but this is nontrivial (see `isClopenable_iff_measurableSet`).
-/
def IsClopenable [t : TopologicalSpace α] (s : Set α) : Prop :=
  ∃ t' : TopologicalSpace α, t' ≤ t ∧ @PolishSpace α t' ∧ IsClosed[t'] s ∧ IsOpen[t'] s

/-- Given a closed set `s` in a Polish space, one can construct a finer Polish topology for
which `s` is both open and closed. -/
/-
**PolishSpace._root_.IsClosed.isClopenable** 是 Mathlib 中的一个定理，位于命名空间 `PolishSpac
e`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a closed set `s` in a Polish space, one can construct a finer Polish topol
ogy for
which `s` is both open and closed.
-/
theorem _root_.IsClosed.isClopenable [TopologicalSpace α] [PolishSpace α] {s : Set α}
    (hs : IsClosed s) : IsClopenable s := by
  /- Both sets `s` and `sᶜ` admit a Polish topology. So does their disjoint union `s ⊕ sᶜ`.
    Pulling back this topology by the canonical bijection with `α` gives the desired Polish
    topology in which `s` is both open and closed. -/
  classical
  have : PolishSpace s := hs.polishSpace
  let t : Set α := sᶜ
  have : PolishSpace t := hs.isOpen_compl.polishSpace
  let f : s ⊕ t ≃ α := Equiv.Set.sumCompl s
  have hle : TopologicalSpace.coinduced f instTopologicalSpaceSum ≤ ‹_› := by
    simp only [instTopologicalSpaceSum, coinduced_sup, coinduced_compose, sup_le_iff,
      ← continuous_iff_coinduced_le]
    exact ⟨continuous_subtype_val, continuous_subtype_val⟩
  refine ⟨.coinduced f instTopologicalSpaceSum, hle, ?_, hs.mono hle, ?_⟩
  · rw [← f.induced_symm]
    exact f.symm.polishSpace_induced
  · rw [isOpen_coinduced, isOpen_sum_iff]
    simp [preimage_preimage, f, t]
/-
**PolishSpace.IsClopenable.compl** 是 Mathlib 中的一个定理，位于命名空间 `PolishSpace.IsClopen
able`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] {s : Set α}, PolishSpace.IsCl
openable s → PolishSpace.IsClopenable sᶜ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.isClosed_compl`：∀ {X : Type u} [inst : TopologicalSpace X] {s : S
et X}, IsOpen s → IsClosed sᶜ
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
-/
theorem IsClopenable.compl [TopologicalSpace α] {s : Set α} (hs : IsClopenable s) :
    IsClopenable sᶜ := by
  rcases hs with ⟨t, t_le, t_polish, h, h'⟩
  exact ⟨t, t_le, t_polish, @IsOpen.isClosed_compl α t s h', @IsClosed.isOpen_compl α t s h⟩
/-
**PolishSpace._root_.IsOpen.isClopenable** 是 Mathlib 中的一个定理，位于命名空间 `PolishSpace`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsOpen.isClopenable [TopologicalSpace α] [PolishSpace α] {s : Set α}
    (hs : IsOpen s) : IsClopenable s := by
  simpa using hs.isClosed_compl.isClopenable.compl

-- TODO: generalize for free to `[Countable ι] {s : ι → Set α}`
/-
**PolishSpace.IsClopenable.iUnion** 是 Mathlib 中的一个定理，位于命名空间 `PolishSpace.IsClope
nable`。
形式化陈述：∀ {α : Type u_1} [t : TopologicalSpace α] [PolishSpace α] {s : ℕ → Set α},
   (∀ (n : ℕ), PolishSpace.IsClopenable (s n)) → PolishSpace.IsClopenable (⋃ n, 
s n)
参数：∀ (n : ℕ), PolishSpace.IsClopenable (s n)；⋃ n, s n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PolishSpace.exists_polishSpace_forall_le`：exists_polishSpace_forall_le {
ι : Type*} [Countable ι] [t : TopologicalSpace α] [p : PolishSpace α] (m : ι -> 
TopologicalSpace α) (hm : fora…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `IsOpen.isClopenable`：∀ {α : Type u_1} [inst : TopologicalSpace α] [Polis
hSpace α] {s : Set α}, IsOpen s → PolishSpace.IsClopenable s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem IsClopenable.iUnion [t : TopologicalSpace α] [PolishSpace α] {s : ℕ → Set α}
    (hs : ∀ n, IsClopenable (s n)) : IsClopenable (⋃ n, s n) := by
  choose m mt m_polish _ m_open using hs
  obtain ⟨t', t'm, -, t'_polish⟩ :
      ∃ t' : TopologicalSpace α, (∀ n : ℕ, t' ≤ m n) ∧ t' ≤ t ∧ @PolishSpace α t' :=
    exists_polishSpace_forall_le m mt m_polish
  have A : IsOpen[t'] (⋃ n, s n) := by
    apply isOpen_iUnion
    intro n
    apply t'm n
    exact m_open n
  obtain ⟨t'', t''_le, t''_polish, h1, h2⟩ : ∃ t'' : TopologicalSpace α,
      t'' ≤ t' ∧ @PolishSpace α t'' ∧ IsClosed[t''] (⋃ n, s n) ∧ IsOpen[t''] (⋃ n, s n) :=
    @IsOpen.isClopenable α t' t'_polish _ A
  exact ⟨t'', t''_le.trans ((t'm 0).trans (mt 0)), t''_polish, h1, h2⟩

end PolishSpace

