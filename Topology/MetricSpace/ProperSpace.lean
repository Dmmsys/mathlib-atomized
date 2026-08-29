/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Topology.Order.IsLUB

/-! ## Proper spaces

## Main definitions and results
* `ProperSpace α`: a `PseudoMetricSpace` where all closed balls are compact

* `isCompact_sphere`: any sphere in a proper space is compact.
* `proper_of_compact`: compact spaces are proper.
* `secondCountable_of_proper`: proper spaces are sigma-compact, hence second countable.
* `locallyCompact_of_proper`: proper spaces are locally compact.
* `pi_properSpace`: finite products of proper spaces are proper.

-/

public section

open Set Filter

universe u v w

variable {α : Type u} {β : Type v} {X ι : Type*}

section ProperSpace

open Metric

/--
Definition of `ProperSpace` / `ProperSpace` 的定义

English:
class ProperSpace
  parameters: (α : Type u) [PseudoMetricSpace α]
  axioms and operations (1):
    - isCompact_closedBall : forall x : α, forall r, IsCompact (closedBall x r)

中文:
类 ProperSpace
  参数: (α : 类型u) [PseudoMetricSpace α]
  公理与运算 (1 个):
    - isCompact_closedBall : 对任意 x : α, 对任意 r, IsCompact (closedBall x r)
-/
class ProperSpace (α : Type u) [PseudoMetricSpace α] : Prop where
  isCompact_closedBall : forall x : α, forall r, IsCompact (closedBall x r)

export ProperSpace (isCompact_closedBall)
attribute [compactness .] isCompact_closedBall

/-- In a proper pseudometric space, all spheres are compact. -/
@[compactness .]
/--
theorem `isCompact_sphere` / 定理 `isCompact_sphere`

English:
theorem isCompact_sphere
  given: {α : Type*} [PseudoMetricSpace α] [ProperSpace α] (x : α) (r : Real)
  proof: (isCompact_closedBall x r).of_isClosed_subset isClosed_sphere sphere_subset_closedBall

中文:
定理 isCompact_sphere
  条件: {α : 类型} [PseudoMetricSpace α] [命题erSpace α] (x : α) (r : 实数)
  证明: (isCompact_closedBall x r).of_isClosed_subset isClosed_sphere sphere_subset_closedBall

Depends on / 依赖: isClosed_sphere, isCompact_closedBall, of_isClosed_subset, sphere_subset_closedBall
-/
theorem isCompact_sphere {α : Type*} [PseudoMetricSpace α] [ProperSpace α] (x : α) (r : Real) :
    IsCompact (sphere x r) :=
  (isCompact_closedBall x r).of_isClosed_subset isClosed_sphere sphere_subset_closedBall

/-- In a proper pseudometric space, any closed ball is a `CompactSpace` when considered as a
subtype. -/
instance {α : Type*} [PseudoMetricSpace α] [ProperSpace α] (x : α) (r : Real) :
    CompactSpace (closedBall x r) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)

/--
Instance `Metric.sphere.compactSpace` / 实例 `Metric.sphere.compactSpace`

English:
instance Metric.sphere.compactSpace
  signature: {α : Type*} [PseudoMetricSpace α] [ProperSpace α]
  body: isCompact_iff_compactSpace.mp (isCompact_sphere _ _)

中文:
实例 Metric.sphere.compactSpace
  签名: {α : 类型} [PseudoMetricSpace α] [命题erSpace α]
  定义体: isCompact_iff_compactSpace.mp (isCompact_sphere _ _)

Depends on / 依赖: isCompact_iff_compactSpace, isCompact_iff_compactSpace.mp, isCompact_sphere
-/
instance Metric.sphere.compactSpace {α : Type*} [PseudoMetricSpace α] [ProperSpace α]
    (x : α) (r : Real) : CompactSpace (sphere x r) :=
  isCompact_iff_compactSpace.mp (isCompact_sphere _ _)

variable [PseudoMetricSpace α]

-- see Note [lower instance priority]
/-- A proper pseudometric space is sigma compact, and therefore second countable. -/
instance (priority := 100) secondCountable_of_proper [ProperSpace α] :
    SecondCountableTopology α := by
  -- We already have `sigmaCompactSpace_of_locallyCompact_secondCountable`, so we don't
  -- add an instance for `SigmaCompactSpace`.
  suffices SigmaCompactSpace α from EMetric.secondCountable_of_sigmaCompact α
  rcases em (Nonempty α) with (⟨⟨x⟩⟩ | hn)
  · exact ⟨⟨fun n => closedBall x n, fun n => isCompact_closedBall _ _, iUnion_closedBall_nat _⟩⟩
  · exact ⟨⟨fun _ => ∅, fun _ => isCompact_empty, iUnion_eq_univ_iff.2 fun x => (hn ⟨x⟩).elim⟩⟩

/--
theorem `ProperSpace.of_isCompact_closedBall_of_le` / 定理 `ProperSpace.of_isCompact_closedBall_of_le`

English:
theorem ProperSpace.of_isCompact_closedBall_of_le
  statement: (R : Real)
  proof: ⟨fun x r => IsCompact.of_isClosed_subset (h x (max r R) (le_max_right _ _)) isClosed_closedBall
    (closedBall_subset_closedBall <| le_max_left _ _)⟩

中文:
定理 ProperSpace.of_isCompact_closedBall_of_le
  结论: (R : 实数)
  证明: ⟨fun x r => IsCompact.of_isClosed_subset (h x (max r R) (le_max_right _ _)) isClosed_closedBall
    (closedBall_subset_closedBall <| le_max_left _ _)⟩

Depends on / 依赖: IsCompact, IsCompact.of_isClosed_subset, closedBall_subset_closedBall, isClosed_closedBall, le_max_left, le_max_right, of_isClosed_subset
-/
theorem ProperSpace.of_isCompact_closedBall_of_le (R : Real)
    (h : forall x : α, forall r, R <= r -> IsCompact (closedBall x r)) : ProperSpace α :=
  ⟨fun x r => IsCompact.of_isClosed_subset (h x (max r R) (le_max_right _ _)) isClosed_closedBall
    (closedBall_subset_closedBall <| le_max_left _ _)⟩

/--
theorem `ProperSpace.of_seq_closedBall` / 定理 `ProperSpace.of_seq_closedBall`

English:
theorem ProperSpace.of_seq_closedBall
  statement: {β : Type*} {l : Filter β} [NeBot l] {x : α} {r : β -> Real}
  proof: let ⟨_i, hci, hir⟩ := (hc.and <| hr.eventually_ge_atTop <| r + dist a x).exists
hci.of_isClosed_subset isClosed_closedBall closedBall_subset_closedBall' hir

中文:
定理 ProperSpace.of_seq_closedBall
  结论: {β : 类型} {l : Filter β} [NeBot l] {x : α} {r : β -> 实数}
  证明: let ⟨_i, hci, hir⟩ := (hc.and <| hr.eventually_ge_atTop <| r + dist a x).exists
hci.of_isClosed_subset isClosed_closedBall closedBall_subset_closedBall' hir

Depends on / 依赖: closedBall_subset_closedBall, eventually_ge_atTop, hc.and, hci.of_isClosed_subset, hr.eventually_ge_atTop, isClosed_closedBall, of_isClosed_subset
-/
theorem ProperSpace.of_seq_closedBall {β : Type*} {l : Filter β} [NeBot l] {x : α} {r : β -> Real}
    (hr : Tendsto r l atTop) (hc : forallᶠ i in l, IsCompact (closedBall x (r i))) :
    ProperSpace α where
  isCompact_closedBall a r :=
    let ⟨_i, hci, hir⟩ := (hc.and <| hr.eventually_ge_atTop <| r + dist a x).exists
hci.of_isClosed_subset isClosed_closedBall closedBall_subset_closedBall' hir

-- A compact pseudometric space is proper
-- see Note [lower instance priority]
instance (priority := 100) proper_of_compact [CompactSpace α] : ProperSpace α :=
  ⟨fun _ _ => isClosed_closedBall.isCompact⟩

-- see Note [lower instance priority]
/-- A proper space is locally compact -/
instance (priority := 100) locallyCompact_of_proper [ProperSpace α] : LocallyCompactSpace α :=
  .of_hasBasis (fun _ => nhds_basis_closedBall) fun _ _ _ =>
    isCompact_closedBall _ _

-- see Note [lower instance priority]
/-- A proper space is complete -/
instance (priority := 100) complete_of_proper [ProperSpace α] : CompleteSpace α :=
  ⟨fun {f} hf => by
    /- We want to show that the Cauchy filter `f` is converging. It suffices to find a closed
      ball (therefore compact by properness) where it is nontrivial. -/
    obtain ⟨t, t_fset, ht⟩ : exists t in f, forall x in t, forall y in t, dist x y < 1 :=
      (Metric.cauchy_iff.1 hf).2 1 zero_lt_one
    rcases hf.1.nonempty_of_mem t_fset with ⟨x, xt⟩
    have : closedBall x 1 in f := mem_of_superset t_fset fun y yt => (ht y yt x xt).le
    rcases (isCompact_iff_totallyBounded_isComplete.1 (isCompact_closedBall x 1)).2 f hf
        (le_principal_iff.2 this) with
      ⟨y, -, hy⟩
    exact ⟨y, hy⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ProperSpace Real
  body: Real.closedBall_eq_Icc ▸ ConditionallyCompleteLinearOrder.isCompact_Icc _ _

中文:
实例 :
  签名: 命题erSpace 实数
  定义体: Real.closedBall_eq_Icc ▸ ConditionallyCompleteLinearOrder.isCompact_Icc _ _

Depends on / 依赖: ConditionallyCompleteLinearOrder, ConditionallyCompleteLinearOrder.isCompact_Icc, Real.closedBall_eq_Icc, closedBall_eq_Icc, isCompact_Icc
-/
instance : ProperSpace Real where isCompact_closedBall _ _ :=
  Real.closedBall_eq_Icc ▸ ConditionallyCompleteLinearOrder.isCompact_Icc _ _

-- shortcut instance for performance reasons
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SecondCountableTopology Real
  body: inferInstance

中文:
实例 :
  签名: SecondCountableTopology 实数
  定义体: inferInstance
-/
instance : SecondCountableTopology Real := inferInstance

/--
Instance `prod_properSpace` / 实例 `prod_properSpace`

English:
instance prod_properSpace
  signature: {α : Type*} {β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
  body: by
    rintro ⟨x, y⟩ r
    rw [← closedBall_prod_same x y]
    exact (isCompact_closedBall x r).prod (isCompact_closedBall y r)

中文:
实例 prod_properSpace
  签名: {α : 类型} {β : 类型} [PseudoMetricSpace α] [PseudoMetricSpace β]
  定义体: by
    rintro ⟨x, y⟩ r
    rw [← closedBall_prod_same x y]
    exact (isCompact_closedBall x r).prod (isCompact_closedBall y r)

Depends on / 依赖: closedBall_prod_same, isCompact_closedBall
-/
instance prod_properSpace {α : Type*} {β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    [ProperSpace α] [ProperSpace β] : ProperSpace (α × β) where
  isCompact_closedBall := by
    rintro ⟨x, y⟩ r
    rw [← closedBall_prod_same x y]
    exact (isCompact_closedBall x r).prod (isCompact_closedBall y r)

/--
Instance `pi_properSpace` / 实例 `pi_properSpace`

English:
instance pi_properSpace
  signature: {X : β -> Type*} [Fintype β] [forall b, PseudoMetricSpace (X b)]
  body: by
  refine .of_isCompact_closedBall_of_le 0 fun x r hr => ?_
  rw [closedBall_pi _ hr]
  exact isCompact_univ_pi fun _ => isCompact_closedBall _ _

中文:
实例 pi_properSpace
  签名: {X : β -> 类型} [Fintype β] [对任意 b, PseudoMetricSpace (X b)]
  定义体: by
  refine .of_isCompact_closedBall_of_le 0 fun x r hr => ?_
  rw [closedBall_pi _ hr]
  exact isCompact_univ_pi fun _ => isCompact_closedBall _ _

Depends on / 依赖: closedBall_pi, isCompact_closedBall, isCompact_univ_pi, of_isCompact_closedBall_of_le
-/
instance pi_properSpace {X : β -> Type*} [Fintype β] [forall b, PseudoMetricSpace (X b)]
    [h : forall b, ProperSpace (X b)] : ProperSpace (forall b, X b) := by
  refine .of_isCompact_closedBall_of_le 0 fun x r hr => ?_
  rw [closedBall_pi _ hr]
  exact isCompact_univ_pi fun _ => isCompact_closedBall _ _

/--
lemma `ProperSpace.of_isClosed` / 引理 `ProperSpace.of_isClosed`

English:
lemma ProperSpace.of_isClosed
  statement: {X : Type*} [PseudoMetricSpace X] [ProperSpace X]
  proof: ⟨fun x r => Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
    ((isCompact_closedBall x.1 r).of_isClosed_subset
    (hs.isClosedMap_subtype_val _ isClosed_closedBall) (Set.image_subset_iff.mpr subset_rfl))⟩

中文:
引理 ProperSpace.of_isClosed
  结论: {X : 类型} [PseudoMetricSpace X] [命题erSpace X]
  证明: ⟨fun x r => Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
    ((isCompact_closedBall x.1 r).of_isClosed_subset
    (hs.isClosedMap_subtype_val _ isClosed_closedBall) (Set.image_subset_iff.mpr subset_rfl))⟩

Depends on / 依赖: IsEmbedding, Set.image_subset_iff.mpr, Topology, Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr, hs.isClosedMap_subtype_val, image_subset_iff, isClosedMap_subtype_val, isClosed_closedBall, isCompact_closedBall, isCompact_iff, of_isClosed_subset, subset_rfl, subtypeVal
-/
lemma ProperSpace.of_isClosed {X : Type*} [PseudoMetricSpace X] [ProperSpace X]
    {s : Set X} (hs : IsClosed s) :
    ProperSpace s :=
  ⟨fun x r => Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
    ((isCompact_closedBall x.1 r).of_isClosed_subset
    (hs.isClosedMap_subtype_val _ isClosed_closedBall) (Set.image_subset_iff.mpr subset_rfl))⟩

end ProperSpace

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [PseudoMetricSpace
  signature: X] [ProperSpace X] : ProperSpace (Additive X)
  body: ‹ProperSpace X›

中文:
实例 [PseudoMetricSpace
  签名: X] [命题erSpace X] : 命题erSpace (Additive X)
  定义体: ‹ProperSpace X›

Depends on / 依赖: ProperSpace
-/
instance [PseudoMetricSpace X] [ProperSpace X] : ProperSpace (Additive X) := ‹ProperSpace X›
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [PseudoMetricSpace
  signature: X] [ProperSpace X] : ProperSpace (Multiplicative X)
  body: ‹ProperSpace X›

中文:
实例 [PseudoMetricSpace
  签名: X] [命题erSpace X] : 命题erSpace (Multiplicative X)
  定义体: ‹ProperSpace X›

Depends on / 依赖: ProperSpace
-/
instance [PseudoMetricSpace X] [ProperSpace X] : ProperSpace (Multiplicative X) := ‹ProperSpace X›
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [PseudoMetricSpace
  signature: X] [ProperSpace X] : ProperSpace Xᵒᵈ
  body: ‹ProperSpace X›

中文:
实例 [PseudoMetricSpace
  签名: X] [命题erSpace X] : 命题erSpace Xᵒᵈ
  定义体: ‹ProperSpace X›

Depends on / 依赖: ProperSpace
-/
instance [PseudoMetricSpace X] [ProperSpace X] : ProperSpace Xᵒᵈ := ‹ProperSpace X›
