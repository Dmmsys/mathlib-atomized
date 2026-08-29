/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
module

public import Mathlib.Topology.Order.Bornology
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.EMetricSpace.Diam

/-!
## Boundedness in (pseudo)-metric spaces

This file contains one definition, and various results on boundedness in pseudo-metric spaces.
* `Metric.diam s` : The `iSup` of the distances of members of `s`.
  Defined in terms of `ediam`, for better handling of the case when it should be infinite.

* `isBounded_iff_subset_closedBall`: a non-empty set is bounded if and only if
  it is included in some closed ball
* describing the cobounded filter, relating to the cocompact filter
* `IsCompact.isBounded`: compact sets are bounded
* `TotallyBounded.isBounded`: totally bounded sets are bounded
* `isCompact_iff_isClosed_bounded`, the **Heine–Borel theorem**:
  in a proper space, a set is compact if and only if it is closed and bounded.
* `cobounded_eq_cocompact`: in a proper space, cobounded and compact sets are the same
  diameter of a subset, and its relation to boundedness

## Tags

metric, pseudometric space, bounded, diameter, Heine-Borel theorem
-/

@[expose] public section

assert_not_exists Module.Basis

open Set Filter Bornology
open scoped ENNReal Uniformity Topology Pointwise

universe u v w

variable {α : Type u} {β : Type v} {X ι : Type*}

section UniformSpace
variable [UniformSpace α] [Preorder α] [CompactIccSpace α]

/--
lemma `totallyBounded_Icc` / 引理 `totallyBounded_Icc`

English:
lemma totallyBounded_Icc
  given: (a b : α)
  statement: TotallyBounded (Icc a b)
  proof: isCompact_Icc.totallyBounded

中文:
引理 totallyBounded_Icc
  条件: (a b : α)
  结论: TotallyBounded (Icc a b)
  证明: isCompact_Icc.totallyBounded

Depends on / 依赖: isCompact_Icc, isCompact_Icc.totallyBounded, totallyBounded
-/
lemma totallyBounded_Icc (a b : α) : TotallyBounded (Icc a b) :=
  isCompact_Icc.totallyBounded

/--
lemma `totallyBounded_Ico` / 引理 `totallyBounded_Ico`

English:
lemma totallyBounded_Ico
  given: (a b : α)
  statement: TotallyBounded (Ico a b)
  proof: (totallyBounded_Icc a b).subset Ico_subset_Icc_self

中文:
引理 totallyBounded_Ico
  条件: (a b : α)
  结论: TotallyBounded (Ico a b)
  证明: (totallyBounded_Icc a b).subset Ico_subset_Icc_self

Depends on / 依赖: Ico_subset_Icc_self, subset, totallyBounded_Icc
-/
lemma totallyBounded_Ico (a b : α) : TotallyBounded (Ico a b) :=
  (totallyBounded_Icc a b).subset Ico_subset_Icc_self

/--
lemma `totallyBounded_Ioc` / 引理 `totallyBounded_Ioc`

English:
lemma totallyBounded_Ioc
  given: (a b : α)
  statement: TotallyBounded (Ioc a b)
  proof: (totallyBounded_Icc a b).subset Ioc_subset_Icc_self

中文:
引理 totallyBounded_Ioc
  条件: (a b : α)
  结论: TotallyBounded (Ioc a b)
  证明: (totallyBounded_Icc a b).subset Ioc_subset_Icc_self

Depends on / 依赖: Ioc_subset_Icc_self, subset, totallyBounded_Icc
-/
lemma totallyBounded_Ioc (a b : α) : TotallyBounded (Ioc a b) :=
  (totallyBounded_Icc a b).subset Ioc_subset_Icc_self

/--
lemma `totallyBounded_Ioo` / 引理 `totallyBounded_Ioo`

English:
lemma totallyBounded_Ioo
  given: (a b : α)
  statement: TotallyBounded (Ioo a b)
  proof: (totallyBounded_Icc a b).subset Ioo_subset_Icc_self

中文:
引理 totallyBounded_Ioo
  条件: (a b : α)
  结论: TotallyBounded (Ioo a b)
  证明: (totallyBounded_Icc a b).subset Ioo_subset_Icc_self

Depends on / 依赖: Ioo_subset_Icc_self, subset, totallyBounded_Icc
-/
lemma totallyBounded_Ioo (a b : α) : TotallyBounded (Ioo a b) :=
  (totallyBounded_Icc a b).subset Ioo_subset_Icc_self

end UniformSpace

namespace Metric

section Bounded

variable {x : α} {s t : Set α} {r : Real}
variable [PseudoMetricSpace α]

/--
theorem `isBounded_closedBall` / 定理 `isBounded_closedBall`

English:
theorem isBounded_closedBall
  statement: IsBounded (closedBall x r)
  proof: isBounded_iff.2 ⟨r + r, fun y hy z hz =>
    calc dist y z <= dist y x + dist z x := dist_triangle_right _ _ _
    _ <= r + r := add_le_add hy hz⟩

中文:
定理 isBounded_closedBall
  结论: IsBounded (closedBall x r)
  证明: isBounded_iff.2 ⟨r + r, fun y hy z hz =>
    calc dist y z <= dist y x + dist z x := dist_triangle_right _ _ _
    _ <= r + r := add_le_add hy hz⟩

Depends on / 依赖: add_le_add, dist_triangle_right, isBounded_iff
-/
theorem isBounded_closedBall : IsBounded (closedBall x r) :=
  isBounded_iff.2 ⟨r + r, fun y hy z hz =>
    calc dist y z <= dist y x + dist z x := dist_triangle_right _ _ _
    _ <= r + r := add_le_add hy hz⟩

/--
theorem `isBounded_ball` / 定理 `isBounded_ball`

English:
theorem isBounded_ball
  statement: IsBounded (ball x r)
  proof: isBounded_closedBall.subset ball_subset_closedBall

中文:
定理 isBounded_ball
  结论: IsBounded (ball x r)
  证明: isBounded_closedBall.subset ball_subset_closedBall

Depends on / 依赖: ball_subset_closedBall, isBounded_closedBall, isBounded_closedBall.subset, subset
-/
theorem isBounded_ball : IsBounded (ball x r) :=
  isBounded_closedBall.subset ball_subset_closedBall

/--
theorem `eq_countable_union_of_isBounded_of_isOpen` / 定理 `eq_countable_union_of_isBounded_of_isOpen`

English:
theorem eq_countable_union_of_isBounded_of_isOpen
  given: {U : Set α} (hU : IsOpen U)
  proof: by
  obtain rfl | ⟨x, -⟩ := U.eq_empty_or_nonempty
  · exact ⟨fun i => ∅, monotone_const, by simp_all⟩
  refine ⟨fun i => U inter ball x i, fun i j hij => ?_, ?_, fun i => ⟨?_, hU.inter isOpen_ball⟩⟩
  · exact inter_subset_inter_right _ (ball_subset_ball (Nat.cast_le.2 hij))
  · simp [← inter_iUnion

中文:
定理 eq_countable_union_of_isBounded_of_isOpen
  条件: {U : Set α} (hU : IsOpen U)
  证明: by
  obtain rfl | ⟨x, -⟩ := U.eq_empty_or_nonempty
  · exact ⟨fun i => ∅, monotone_const, by simp_all⟩
  refine ⟨fun i => U inter ball x i, fun i j hij => ?_, ?_, fun i => ⟨?_, hU.inter isOpen_ball⟩⟩
  · exact inter_subset_inter_right _ (ball_subset_ball (Nat.cast_le.2 hij))
  · simp [← inter_iUnion

Depends on / 依赖: Nat.cast_le, U.eq_empty_or_nonempty, ball_subset_ball, cast_le, eq_empty_or_nonempty, hU.inter, inter_iUnion, inter_subset_inter_right, inter_subset_right, isBounded_ball, isBounded_ball.subset, isOpen_ball, monotone_const, subset
-/
theorem eq_countable_union_of_isBounded_of_isOpen {U : Set α} (hU : IsOpen U) :
    exists f : Nat -> Set α, Monotone f ∧ ⋃ i, f i = U ∧ forall i, IsBounded (f i) ∧ IsOpen (f i) := by
  obtain rfl | ⟨x, -⟩ := U.eq_empty_or_nonempty
  · exact ⟨fun i => ∅, monotone_const, by simp_all⟩
  refine ⟨fun i => U inter ball x i, fun i j hij => ?_, ?_, fun i => ⟨?_, hU.inter isOpen_ball⟩⟩
  · exact inter_subset_inter_right _ (ball_subset_ball (Nat.cast_le.2 hij))
  · simp [← inter_iUnion]
  · exact isBounded_ball.subset inter_subset_right

/--
theorem `isBounded_sphere` / 定理 `isBounded_sphere`

English:
theorem isBounded_sphere
  statement: IsBounded (sphere x r)
  proof: isBounded_closedBall.subset sphere_subset_closedBall

中文:
定理 isBounded_sphere
  结论: IsBounded (sphere x r)
  证明: isBounded_closedBall.subset sphere_subset_closedBall

Depends on / 依赖: isBounded_closedBall, isBounded_closedBall.subset, sphere_subset_closedBall, subset
-/
theorem isBounded_sphere : IsBounded (sphere x r) :=
  isBounded_closedBall.subset sphere_subset_closedBall

/--
theorem `isBounded_iff_subset_closedBall` / 定理 `isBounded_iff_subset_closedBall`

English:
theorem isBounded_iff_subset_closedBall
  given: (c : α)
  statement: IsBounded s ↔ exists r, s subseteq closedBall c r
  proof: ⟨fun h => (isBounded_iff.1 (h.insert c)).imp fun _r hr _x hx => hr (.inr hx) (mem_insert _ _),
    fun ⟨_r, hr⟩ => isBounded_closedBall.subset hr⟩

中文:
定理 isBounded_iff_subset_closedBall
  条件: (c : α)
  结论: IsBounded s ↔ 存在 r, s subseteq closedBall c r
  证明: ⟨fun h => (isBounded_iff.1 (h.insert c)).imp fun _r hr _x hx => hr (.inr hx) (mem_insert _ _),
    fun ⟨_r, hr⟩ => isBounded_closedBall.subset hr⟩

Depends on / 依赖: h.insert, insert, isBounded_closedBall, isBounded_closedBall.subset, isBounded_iff, mem_insert, subset
-/
theorem isBounded_iff_subset_closedBall (c : α) : IsBounded s ↔ exists r, s subseteq closedBall c r :=
  ⟨fun h => (isBounded_iff.1 (h.insert c)).imp fun _r hr _x hx => hr (.inr hx) (mem_insert _ _),
    fun ⟨_r, hr⟩ => isBounded_closedBall.subset hr⟩

/--
theorem `_root_.Bornology.IsBounded.subset_closedBall` / 定理 `_root_.Bornology.IsBounded.subset_closedBall`

English:
theorem _root_.Bornology.IsBounded.subset_closedBall
  given: (h : IsBounded s) (c : α)
  proof: (isBounded_iff_subset_closedBall c).1 h

中文:
定理 _root_.Bornology.IsBounded.subset_closedBall
  条件: (h : IsBounded s) (c : α)
  证明: (isBounded_iff_subset_closedBall c).1 h

Depends on / 依赖: isBounded_iff_subset_closedBall
-/
theorem _root_.Bornology.IsBounded.subset_closedBall (h : IsBounded s) (c : α) :
    exists r, s subseteq closedBall c r :=
  (isBounded_iff_subset_closedBall c).1 h

/--
theorem `_root_.Bornology.IsBounded.subset_ball_lt` / 定理 `_root_.Bornology.IsBounded.subset_ball_lt`

English:
theorem _root_.Bornology.IsBounded.subset_ball_lt
  given: (h : IsBounded s) (a : Real) (c : α)
  proof: let ⟨r, hr⟩ := h.subset_closedBall c
⟨max r a + 1, (le_max_right _ _).trans_lt (lt_add_one _), hr.trans closedBall_subset_ball
    (le_max_left _ _).trans_lt (lt_add_one _)⟩

中文:
定理 _root_.Bornology.IsBounded.subset_ball_lt
  条件: (h : IsBounded s) (a : 实数) (c : α)
  证明: let ⟨r, hr⟩ := h.subset_closedBall c
⟨max r a + 1, (le_max_right _ _).trans_lt (lt_add_one _), hr.trans closedBall_subset_ball
    (le_max_left _ _).trans_lt (lt_add_one _)⟩

Depends on / 依赖: closedBall_subset_ball, h.subset_closedBall, hr.trans, le_max_left, le_max_right, lt_add_one, subset_closedBall, trans_lt
-/
theorem _root_.Bornology.IsBounded.subset_ball_lt (h : IsBounded s) (a : Real) (c : α) :
    exists r, a < r ∧ s subseteq ball c r :=
  let ⟨r, hr⟩ := h.subset_closedBall c
⟨max r a + 1, (le_max_right _ _).trans_lt (lt_add_one _), hr.trans closedBall_subset_ball
    (le_max_left _ _).trans_lt (lt_add_one _)⟩

/--
theorem `_root_.Bornology.IsBounded.subset_ball` / 定理 `_root_.Bornology.IsBounded.subset_ball`

English:
theorem _root_.Bornology.IsBounded.subset_ball
  given: (h : IsBounded s) (c : α)
  statement: exists r, s subseteq ball c r
  proof: (h.subset_ball_lt 0 c).imp fun _ => And.right

中文:
定理 _root_.Bornology.IsBounded.subset_ball
  条件: (h : IsBounded s) (c : α)
  结论: 存在 r, s subseteq ball c r
  证明: (h.subset_ball_lt 0 c).imp fun _ => And.right

Depends on / 依赖: And.right, h.subset_ball_lt, subset_ball_lt
-/
theorem _root_.Bornology.IsBounded.subset_ball (h : IsBounded s) (c : α) : exists r, s subseteq ball c r :=
  (h.subset_ball_lt 0 c).imp fun _ => And.right

/--
theorem `isBounded_iff_subset_ball` / 定理 `isBounded_iff_subset_ball`

English:
theorem isBounded_iff_subset_ball
  given: (c : α)
  statement: IsBounded s ↔ exists r, s subseteq ball c r
  proof: ⟨(IsBounded.subset_ball · c), fun ⟨_r, hr⟩ => isBounded_ball.subset hr⟩

中文:
定理 isBounded_iff_subset_ball
  条件: (c : α)
  结论: IsBounded s ↔ 存在 r, s subseteq ball c r
  证明: ⟨(IsBounded.subset_ball · c), fun ⟨_r, hr⟩ => isBounded_ball.subset hr⟩

Depends on / 依赖: IsBounded, IsBounded.subset_ball, isBounded_ball, isBounded_ball.subset, subset, subset_ball
-/
theorem isBounded_iff_subset_ball (c : α) : IsBounded s ↔ exists r, s subseteq ball c r :=
  ⟨(IsBounded.subset_ball · c), fun ⟨_r, hr⟩ => isBounded_ball.subset hr⟩

/--
theorem `_root_.Bornology.IsBounded.subset_closedBall_lt` / 定理 `_root_.Bornology.IsBounded.subset_closedBall_lt`

English:
theorem _root_.Bornology.IsBounded.subset_closedBall_lt
  given: (h : IsBounded s) (a : Real) (c : α)
  proof: let ⟨r, har, hr⟩ := h.subset_ball_lt a c
  ⟨r, har, hr.trans ball_subset_closedBall⟩

中文:
定理 _root_.Bornology.IsBounded.subset_closedBall_lt
  条件: (h : IsBounded s) (a : 实数) (c : α)
  证明: let ⟨r, har, hr⟩ := h.subset_ball_lt a c
  ⟨r, har, hr.trans ball_subset_closedBall⟩

Depends on / 依赖: ball_subset_closedBall, h.subset_ball_lt, hr.trans, subset_ball_lt
-/
theorem _root_.Bornology.IsBounded.subset_closedBall_lt (h : IsBounded s) (a : Real) (c : α) :
    exists r, a < r ∧ s subseteq closedBall c r :=
  let ⟨r, har, hr⟩ := h.subset_ball_lt a c
  ⟨r, har, hr.trans ball_subset_closedBall⟩

/--
theorem `isBounded_closure_of_isBounded` / 定理 `isBounded_closure_of_isBounded`

English:
theorem isBounded_closure_of_isBounded
  given: (h : IsBounded s)
  statement: IsBounded (closure s)
  proof: let ⟨C, h⟩ := isBounded_iff.1 h
isBounded_iff.2 ⟨C, fun _a ha _b hb => isClosed_Iic.closure_subset
    map_mem_closure₂ continuous_dist ha hb h⟩

中文:
定理 isBounded_closure_of_isBounded
  条件: (h : IsBounded s)
  结论: IsBounded (closure s)
  证明: let ⟨C, h⟩ := isBounded_iff.1 h
isBounded_iff.2 ⟨C, fun _a ha _b hb => isClosed_Iic.closure_subset
    map_mem_closure₂ continuous_dist ha hb h⟩

Depends on / 依赖: closure_subset, continuous_dist, isBounded_iff, isClosed_Iic, isClosed_Iic.closure_subset
-/
theorem isBounded_closure_of_isBounded (h : IsBounded s) : IsBounded (closure s) :=
  let ⟨C, h⟩ := isBounded_iff.1 h
isBounded_iff.2 ⟨C, fun _a ha _b hb => isClosed_Iic.closure_subset
    map_mem_closure₂ continuous_dist ha hb h⟩

/--
theorem `_root_.Bornology.IsBounded.closure` / 定理 `_root_.Bornology.IsBounded.closure`

English:
theorem _root_.Bornology.IsBounded.closure
  given: (h : IsBounded s)
  statement: IsBounded (closure s)
  proof: isBounded_closure_of_isBounded h

@[simp]

中文:
定理 _root_.Bornology.IsBounded.closure
  条件: (h : IsBounded s)
  结论: IsBounded (closure s)
  证明: isBounded_closure_of_isBounded h

@[simp]
-/
protected theorem _root_.Bornology.IsBounded.closure (h : IsBounded s) : IsBounded (closure s) :=
  isBounded_closure_of_isBounded h

@[simp]
/--
theorem `isBounded_closure_iff` / 定理 `isBounded_closure_iff`

English:
theorem isBounded_closure_iff
  statement: IsBounded (closure s) ↔ IsBounded s
  proof: ⟨fun h => h.subset subset_closure, fun h => h.closure⟩

中文:
定理 isBounded_closure_iff
  结论: IsBounded (closure s) ↔ IsBounded s
  证明: ⟨fun h => h.subset subset_closure, fun h => h.closure⟩

Depends on / 依赖: closure, h.closure, h.subset, subset, subset_closure
-/
theorem isBounded_closure_iff : IsBounded (closure s) ↔ IsBounded s :=
  ⟨fun h => h.subset subset_closure, fun h => h.closure⟩

/--
theorem `hasBasis_nhds_isOpen_isBounded` / 定理 `hasBasis_nhds_isOpen_isBounded`

English:
theorem hasBasis_nhds_isOpen_isBounded
  given: (x : α)
  proof: by
  simp_rw [← and_assoc]
  apply (nhds_basis_opens x).restrict fun s hs => ?_
  exact ⟨s inter Metric.ball x 1,
    by aesop (add safe apply IsOpen.inter),
    by simpa using Metric.isBounded_ball.subset Set.inter_subset_right⟩

中文:
定理 hasBasis_nhds_isOpen_isBounded
  条件: (x : α)
  证明: by
  simp_rw [← and_assoc]
  apply (nhds_basis_opens x).restrict fun s hs => ?_
  exact ⟨s inter Metric.ball x 1,
    by aesop (add safe apply IsOpen.inter),
    by simpa using Metric.isBounded_ball.subset Set.inter_subset_right⟩

Depends on / 依赖: IsOpen, IsOpen.inter, Metric, Metric.ball, Metric.isBounded_ball.subset, Set.inter_subset_right, and_assoc, inter_subset_right, isBounded_ball, nhds_basis_opens, restrict, simp_rw, subset
-/
theorem hasBasis_nhds_isOpen_isBounded (x : α) :
    (𝓝 x).HasBasis (fun a => x in a ∧ IsOpen a ∧ Bornology.IsBounded a) id := by
  simp_rw [← and_assoc]
  apply (nhds_basis_opens x).restrict fun s hs => ?_
  exact ⟨s inter Metric.ball x 1,
    by aesop (add safe apply IsOpen.inter),
    by simpa using Metric.isBounded_ball.subset Set.inter_subset_right⟩

/--
theorem `hasBasis_cobounded_compl_closedBall` / 定理 `hasBasis_cobounded_compl_closedBall`

English:
theorem hasBasis_cobounded_compl_closedBall
  given: (c : α)
  proof: ⟨compl_surjective.forall.2 fun _ => (isBounded_iff_subset_closedBall c).trans by simp⟩

中文:
定理 hasBasis_cobounded_compl_closedBall
  条件: (c : α)
  证明: ⟨compl_surjective.forall.2 fun _ => (isBounded_iff_subset_closedBall c).trans by simp⟩

Depends on / 依赖: compl_surjective, compl_surjective.forall, isBounded_iff_subset_closedBall
-/
theorem hasBasis_cobounded_compl_closedBall (c : α) :
    (cobounded α).HasBasis (fun _ => True) (fun r => (closedBall c r)ᶜ) :=
⟨compl_surjective.forall.2 fun _ => (isBounded_iff_subset_closedBall c).trans by simp⟩

/--
theorem `hasAntitoneBasis_cobounded_compl_closedBall` / 定理 `hasAntitoneBasis_cobounded_compl_closedBall`

English:
theorem hasAntitoneBasis_cobounded_compl_closedBall
  given: (c : α)
  proof: ⟨Metric.hasBasis_cobounded_compl_closedBall _, fun _ _ hr _ => by simpa using hr.trans_lt⟩

中文:
定理 hasAntitoneBasis_cobounded_compl_closedBall
  条件: (c : α)
  证明: ⟨Metric.hasBasis_cobounded_compl_closedBall _, fun _ _ hr _ => by simpa using hr.trans_lt⟩

Depends on / 依赖: Metric, Metric.hasBasis_cobounded_compl_closedBall, hasBasis_cobounded_compl_closedBall, hr.trans_lt, trans_lt
-/
theorem hasAntitoneBasis_cobounded_compl_closedBall (c : α) :
    (cobounded α).HasAntitoneBasis (fun r => (closedBall c r)ᶜ) :=
  ⟨Metric.hasBasis_cobounded_compl_closedBall _, fun _ _ hr _ => by simpa using hr.trans_lt⟩

/--
theorem `hasBasis_cobounded_compl_ball` / 定理 `hasBasis_cobounded_compl_ball`

English:
theorem hasBasis_cobounded_compl_ball
  given: (c : α)
  proof: ⟨compl_surjective.forall.2 fun _ => (isBounded_iff_subset_ball c).trans by simp⟩

中文:
定理 hasBasis_cobounded_compl_ball
  条件: (c : α)
  证明: ⟨compl_surjective.forall.2 fun _ => (isBounded_iff_subset_ball c).trans by simp⟩

Depends on / 依赖: compl_surjective, compl_surjective.forall, isBounded_iff_subset_ball
-/
theorem hasBasis_cobounded_compl_ball (c : α) :
    (cobounded α).HasBasis (fun _ => True) (fun r => (ball c r)ᶜ) :=
⟨compl_surjective.forall.2 fun _ => (isBounded_iff_subset_ball c).trans by simp⟩

/--
theorem `hasAntitoneBasis_cobounded_compl_ball` / 定理 `hasAntitoneBasis_cobounded_compl_ball`

English:
theorem hasAntitoneBasis_cobounded_compl_ball
  given: (c : α)
  proof: ⟨Metric.hasBasis_cobounded_compl_ball _, fun _ _ hr _ => by simpa using hr.trans⟩

@[simp]

中文:
定理 hasAntitoneBasis_cobounded_compl_ball
  条件: (c : α)
  证明: ⟨Metric.hasBasis_cobounded_compl_ball _, fun _ _ hr _ => by simpa using hr.trans⟩

@[simp]

Depends on / 依赖: Metric, Metric.hasBasis_cobounded_compl_ball, hasBasis_cobounded_compl_ball, hr.trans
-/
theorem hasAntitoneBasis_cobounded_compl_ball (c : α) :
    (cobounded α).HasAntitoneBasis (fun r => (ball c r)ᶜ) :=
  ⟨Metric.hasBasis_cobounded_compl_ball _, fun _ _ hr _ => by simpa using hr.trans⟩

@[simp]
/--
theorem `comap_dist_right_atTop` / 定理 `comap_dist_right_atTop`

English:
theorem comap_dist_right_atTop
  given: (c : α)
  statement: comap (dist · c) atTop = cobounded α
  proof: (atTop_basis.comap _).eq_of_same_basis by
    simpa only [compl_def, mem_ball, not_lt] using! hasBasis_cobounded_compl_ball c

@[simp]

中文:
定理 comap_dist_right_atTop
  条件: (c : α)
  结论: comap (dist · c) atTop = cobounded α
  证明: (atTop_basis.comap _).eq_of_same_basis by
    simpa only [compl_def, mem_ball, not_lt] using! hasBasis_cobounded_compl_ball c

@[simp]

Depends on / 依赖: atTop_basis, atTop_basis.comap, compl_def, eq_of_same_basis, hasBasis_cobounded_compl_ball, mem_ball, not_lt
-/
theorem comap_dist_right_atTop (c : α) : comap (dist · c) atTop = cobounded α :=
(atTop_basis.comap _).eq_of_same_basis by
    simpa only [compl_def, mem_ball, not_lt] using! hasBasis_cobounded_compl_ball c

@[simp]
/--
theorem `comap_dist_left_atTop` / 定理 `comap_dist_left_atTop`

English:
theorem comap_dist_left_atTop
  given: (c : α)
  statement: comap (dist c) atTop = cobounded α
  proof: by
  simpa only [dist_comm _ c] using comap_dist_right_atTop c

@[simp]

中文:
定理 comap_dist_left_atTop
  条件: (c : α)
  结论: comap (dist c) atTop = cobounded α
  证明: by
  simpa only [dist_comm _ c] using comap_dist_right_atTop c

@[simp]

Depends on / 依赖: comap_dist_right_atTop, dist_comm
-/
theorem comap_dist_left_atTop (c : α) : comap (dist c) atTop = cobounded α := by
  simpa only [dist_comm _ c] using comap_dist_right_atTop c

@[simp]
/--
theorem `tendsto_dist_right_atTop_iff` / 定理 `tendsto_dist_right_atTop_iff`

English:
theorem tendsto_dist_right_atTop_iff
  given: (c : α) {f : β -> α} {l : Filter β}
  proof: by
  rw [← comap_dist_right_atTop c]; rw [tendsto_comap_iff]; rw [Function.comp_def]

@[simp]

中文:
定理 tendsto_dist_right_atTop_iff
  条件: (c : α) {f : β -> α} {l : Filter β}
  证明: by
  rw [← comap_dist_right_atTop c]; rw [tendsto_comap_iff]; rw [Function.comp_def]

@[simp]

Depends on / 依赖: Function, Function.comp_def, comap_dist_right_atTop, comp_def, tendsto_comap_iff
-/
theorem tendsto_dist_right_atTop_iff (c : α) {f : β -> α} {l : Filter β} :
    Tendsto (fun x => dist (f x) c) l atTop ↔ Tendsto f l (cobounded α) := by
  rw [← comap_dist_right_atTop c]; rw [tendsto_comap_iff]; rw [Function.comp_def]

@[simp]
/--
theorem `tendsto_dist_left_atTop_iff` / 定理 `tendsto_dist_left_atTop_iff`

English:
theorem tendsto_dist_left_atTop_iff
  given: (c : α) {f : β -> α} {l : Filter β}
  proof: by
  simp only [dist_comm c, tendsto_dist_right_atTop_iff]

中文:
定理 tendsto_dist_left_atTop_iff
  条件: (c : α) {f : β -> α} {l : Filter β}
  证明: by
  simp only [dist_comm c, tendsto_dist_right_atTop_iff]

Depends on / 依赖: dist_comm, tendsto_dist_right_atTop_iff
-/
theorem tendsto_dist_left_atTop_iff (c : α) {f : β -> α} {l : Filter β} :
    Tendsto (fun x => dist c (f x)) l atTop ↔ Tendsto f l (cobounded α) := by
  simp only [dist_comm c, tendsto_dist_right_atTop_iff]

/--
theorem `tendsto_dist_right_cobounded_atTop` / 定理 `tendsto_dist_right_cobounded_atTop`

English:
theorem tendsto_dist_right_cobounded_atTop
  given: (c : α)
  statement: Tendsto (dist · c) (cobounded α) atTop
  proof: tendsto_iff_comap.2 (comap_dist_right_atTop c).ge

中文:
定理 tendsto_dist_right_cobounded_atTop
  条件: (c : α)
  结论: Tendsto (dist · c) (cobounded α) atTop
  证明: tendsto_iff_comap.2 (comap_dist_right_atTop c).ge

Depends on / 依赖: comap_dist_right_atTop, tendsto_iff_comap
-/
theorem tendsto_dist_right_cobounded_atTop (c : α) : Tendsto (dist · c) (cobounded α) atTop :=
  tendsto_iff_comap.2 (comap_dist_right_atTop c).ge

/--
theorem `tendsto_dist_left_cobounded_atTop` / 定理 `tendsto_dist_left_cobounded_atTop`

English:
theorem tendsto_dist_left_cobounded_atTop
  given: (c : α)
  statement: Tendsto (dist c) (cobounded α) atTop
  proof: tendsto_iff_comap.2 (comap_dist_left_atTop c).ge

中文:
定理 tendsto_dist_left_cobounded_atTop
  条件: (c : α)
  结论: Tendsto (dist c) (cobounded α) atTop
  证明: tendsto_iff_comap.2 (comap_dist_left_atTop c).ge

Depends on / 依赖: comap_dist_left_atTop, tendsto_iff_comap
-/
theorem tendsto_dist_left_cobounded_atTop (c : α) : Tendsto (dist c) (cobounded α) atTop :=
  tendsto_iff_comap.2 (comap_dist_left_atTop c).ge

/--
theorem `_root_.TotallyBounded.isBounded` / 定理 `_root_.TotallyBounded.isBounded`

English:
theorem _root_.TotallyBounded.isBounded
  given: {s : Set α} (h : TotallyBounded s)
  statement: IsBounded s
  proof: -- We cover the totally bounded set by finitely many balls of radius 1,
  -- and then argue that a finite union of bounded sets is bounded
  let ⟨_t, fint, subs⟩ := (totallyBounded_iff.mp h) 1 zero_lt_one
  ((isBounded_biUnion fint).2 fun _ _ => isBounded_ball).subset subs

中文:
定理 _root_.TotallyBounded.isBounded
  条件: {s : Set α} (h : TotallyBounded s)
  结论: IsBounded s
  证明: -- We cover the totally bounded set by finitely many balls of radius 1,
  -- and then argue that a finite union of bounded sets is bounded
  let ⟨_t, fint, subs⟩ := (totallyBounded_iff.mp h) 1 zero_lt_one
  ((isBounded_biUnion fint).2 fun _ _ => isBounded_ball).subset subs
-/
theorem _root_.TotallyBounded.isBounded {s : Set α} (h : TotallyBounded s) : IsBounded s :=
  -- We cover the totally bounded set by finitely many balls of radius 1,
  -- and then argue that a finite union of bounded sets is bounded
  let ⟨_t, fint, subs⟩ := (totallyBounded_iff.mp h) 1 zero_lt_one
  ((isBounded_biUnion fint).2 fun _ _ => isBounded_ball).subset subs

/-- A compact set is bounded -/
@[aesop 50% apply, grind ←]
/--
theorem `_root_.IsCompact.isBounded` / 定理 `_root_.IsCompact.isBounded`

English:
theorem _root_.IsCompact.isBounded
  given: {s : Set α} (h : IsCompact s)
  statement: IsBounded s
  proof: -- A compact set is totally bounded, thus bounded
  h.totallyBounded.isBounded

中文:
定理 _root_.IsCompact.isBounded
  条件: {s : Set α} (h : IsCompact s)
  结论: IsBounded s
  证明: -- A compact set is totally bounded, thus bounded
  h.totallyBounded.isBounded
-/
theorem _root_.IsCompact.isBounded {s : Set α} (h : IsCompact s) : IsBounded s :=
  -- A compact set is totally bounded, thus bounded
  h.totallyBounded.isBounded

instance (priority := low) [CompactSpace α] : BoundedSpace α := ⟨isCompact_univ.isBounded⟩

/--
theorem `cobounded_le_cocompact` / 定理 `cobounded_le_cocompact`

English:
theorem cobounded_le_cocompact
  statement: cobounded α <= cocompact α
  proof: hasBasis_cocompact.ge_iff.2 fun _s hs => hs.isBounded

中文:
定理 cobounded_le_cocompact
  结论: cobounded α <= cocompact α
  证明: hasBasis_cocompact.ge_iff.2 fun _s hs => hs.isBounded

Depends on / 依赖: ge_iff, hasBasis_cocompact, hasBasis_cocompact.ge_iff, hs.isBounded, isBounded
-/
theorem cobounded_le_cocompact : cobounded α <= cocompact α :=
  hasBasis_cocompact.ge_iff.2 fun _s hs => hs.isBounded

/--
theorem `isCobounded_iff_closedBall_compl_subset` / 定理 `isCobounded_iff_closedBall_compl_subset`

English:
theorem isCobounded_iff_closedBall_compl_subset
  given: {s : Set α} (c : α)
  proof: by
  rw [← isBounded_compl_iff]; rw [isBounded_iff_subset_closedBall c]
  apply exists_congr
  intro r
  rw [compl_subset_comm]

中文:
定理 isCobounded_iff_closedBall_compl_subset
  条件: {s : Set α} (c : α)
  证明: by
  rw [← isBounded_compl_iff]; rw [isBounded_iff_subset_closedBall c]
  apply exists_congr
  intro r
  rw [compl_subset_comm]

Depends on / 依赖: compl_subset_comm, exists_congr, isBounded_compl_iff, isBounded_iff_subset_closedBall
-/
theorem isCobounded_iff_closedBall_compl_subset {s : Set α} (c : α) :
    IsCobounded s ↔ exists (r : Real), (Metric.closedBall c r)ᶜ subseteq s := by
  rw [← isBounded_compl_iff]; rw [isBounded_iff_subset_closedBall c]
  apply exists_congr
  intro r
  rw [compl_subset_comm]

/--
theorem `_root_.Bornology.IsCobounded.closedBall_compl_subset` / 定理 `_root_.Bornology.IsCobounded.closedBall_compl_subset`

English:
theorem _root_.Bornology.IsCobounded.closedBall_compl_subset
  statement: {s : Set α} (hs : IsCobounded s)
  proof: (isCobounded_iff_closedBall_compl_subset c).mp hs

中文:
定理 _root_.Bornology.IsCobounded.closedBall_compl_subset
  结论: {s : Set α} (hs : IsCobounded s)
  证明: (isCobounded_iff_closedBall_compl_subset c).mp hs

Depends on / 依赖: isCobounded_iff_closedBall_compl_subset
-/
theorem _root_.Bornology.IsCobounded.closedBall_compl_subset {s : Set α} (hs : IsCobounded s)
    (c : α) : exists (r : Real), (Metric.closedBall c r)ᶜ subseteq s :=
  (isCobounded_iff_closedBall_compl_subset c).mp hs

/--
theorem `closedBall_compl_subset_of_mem_cocompact` / 定理 `closedBall_compl_subset_of_mem_cocompact`

English:
theorem closedBall_compl_subset_of_mem_cocompact
  given: {s : Set α} (hs : s in cocompact α) (c : α)
  proof: IsCobounded.closedBall_compl_subset (cobounded_le_cocompact hs) c

中文:
定理 closedBall_compl_subset_of_mem_cocompact
  条件: {s : Set α} (hs : s in cocompact α) (c : α)
  证明: IsCobounded.closedBall_compl_subset (cobounded_le_cocompact hs) c

Depends on / 依赖: IsCobounded, IsCobounded.closedBall_compl_subset, closedBall_compl_subset, cobounded_le_cocompact
-/
theorem closedBall_compl_subset_of_mem_cocompact {s : Set α} (hs : s in cocompact α) (c : α) :
    exists (r : Real), (Metric.closedBall c r)ᶜ subseteq s :=
  IsCobounded.closedBall_compl_subset (cobounded_le_cocompact hs) c

/--
theorem `mem_cocompact_of_closedBall_compl_subset` / 定理 `mem_cocompact_of_closedBall_compl_subset`

English:
theorem mem_cocompact_of_closedBall_compl_subset
  statement: [ProperSpace α] (c : α)
  proof: by
  rcases h with ⟨r, h⟩
  rw [Filter.mem_cocompact]
  exact ⟨closedBall c r, isCompact_closedBall c r, h⟩

中文:
定理 mem_cocompact_of_closedBall_compl_subset
  结论: [命题erSpace α] (c : α)
  证明: by
  rcases h with ⟨r, h⟩
  rw [Filter.mem_cocompact]
  exact ⟨closedBall c r, isCompact_closedBall c r, h⟩

Depends on / 依赖: Filter, Filter.mem_cocompact, closedBall, isCompact_closedBall, mem_cocompact
-/
theorem mem_cocompact_of_closedBall_compl_subset [ProperSpace α] (c : α)
    (h : exists r, (closedBall c r)ᶜ subseteq s) : s in cocompact α := by
  rcases h with ⟨r, h⟩
  rw [Filter.mem_cocompact]
  exact ⟨closedBall c r, isCompact_closedBall c r, h⟩

/--
theorem `mem_cocompact_iff_closedBall_compl_subset` / 定理 `mem_cocompact_iff_closedBall_compl_subset`

English:
theorem mem_cocompact_iff_closedBall_compl_subset
  given: [ProperSpace α] (c : α)
  proof: ⟨(closedBall_compl_subset_of_mem_cocompact · _), mem_cocompact_of_closedBall_compl_subset _⟩

中文:
定理 mem_cocompact_iff_closedBall_compl_subset
  条件: [命题erSpace α] (c : α)
  证明: ⟨(closedBall_compl_subset_of_mem_cocompact · _), mem_cocompact_of_closedBall_compl_subset _⟩

Depends on / 依赖: closedBall_compl_subset_of_mem_cocompact, mem_cocompact_of_closedBall_compl_subset
-/
theorem mem_cocompact_iff_closedBall_compl_subset [ProperSpace α] (c : α) :
    s in cocompact α ↔ exists r, (closedBall c r)ᶜ subseteq s :=
  ⟨(closedBall_compl_subset_of_mem_cocompact · _), mem_cocompact_of_closedBall_compl_subset _⟩

/--
theorem `isBounded_range_iff` / 定理 `isBounded_range_iff`

English:
theorem isBounded_range_iff
  given: {f : β -> α}
  statement: IsBounded (range f) ↔ exists C, forall x y, dist (f x) (f y) <= C
  proof: isBounded_iff.trans by simp only [forall_mem_range]

中文:
定理 isBounded_range_iff
  条件: {f : β -> α}
  结论: IsBounded (range f) ↔ 存在 C, 对任意 x y, dist (f x) (f y) <= C
  证明: isBounded_iff.trans by simp only [forall_mem_range]

Depends on / 依赖: forall_mem_range, isBounded_iff, isBounded_iff.trans
-/
theorem isBounded_range_iff {f : β -> α} : IsBounded (range f) ↔ exists C, forall x y, dist (f x) (f y) <= C :=
isBounded_iff.trans by simp only [forall_mem_range]

/--
theorem `isBounded_image_iff` / 定理 `isBounded_image_iff`

English:
theorem isBounded_image_iff
  given: {f : β -> α} {s : Set β}
  proof: isBounded_iff.trans by simp only [forall_mem_image]

中文:
定理 isBounded_image_iff
  条件: {f : β -> α} {s : Set β}
  证明: isBounded_iff.trans by simp only [forall_mem_image]

Depends on / 依赖: forall_mem_image, isBounded_iff, isBounded_iff.trans
-/
theorem isBounded_image_iff {f : β -> α} {s : Set β} :
    IsBounded (f '' s) ↔ exists C, forall x in s, forall y in s, dist (f x) (f y) <= C :=
isBounded_iff.trans by simp only [forall_mem_image]

/--
theorem `isBounded_range_of_tendsto_cofinite_uniformity` / 定理 `isBounded_range_of_tendsto_cofinite_uniformity`

English:
theorem isBounded_range_of_tendsto_cofinite_uniformity
  statement: {f : β -> α}
  proof: by
  rcases (hasBasis_cofinite.prod_self.tendsto_iff uniformity_basis_dist).1 hf 1 zero_lt_one with
    ⟨s, hsf, hs1⟩
  rw [← image_union_image_compl_eq_range]
  refine (hsf.image f).isBounded.union (isBounded_image_iff.2 ⟨1, fun x hx y hy => ?_⟩)
  exact le_of_lt (hs1 (x, y) ⟨hx, hy⟩)

中文:
定理 isBounded_range_of_tendsto_cofinite_uniformity
  结论: {f : β -> α}
  证明: by
  rcases (hasBasis_cofinite.prod_self.tendsto_iff uniformity_basis_dist).1 hf 1 zero_lt_one with
    ⟨s, hsf, hs1⟩
  rw [← image_union_image_compl_eq_range]
  refine (hsf.image f).isBounded.union (isBounded_image_iff.2 ⟨1, fun x hx y hy => ?_⟩)
  exact le_of_lt (hs1 (x, y) ⟨hx, hy⟩)

Depends on / 依赖: hasBasis_cofinite, hasBasis_cofinite.prod_self.tendsto_iff, hsf.image, image_union_image_compl_eq_range, isBounded, isBounded.union, isBounded_image_iff, le_of_lt, prod_self, tendsto_iff, uniformity_basis_dist, zero_lt_one
-/
theorem isBounded_range_of_tendsto_cofinite_uniformity {f : β -> α}
    (hf : Tendsto (Prod.map f f) (.cofinite ×ˢ .cofinite) (𝓤 α)) : IsBounded (range f) := by
  rcases (hasBasis_cofinite.prod_self.tendsto_iff uniformity_basis_dist).1 hf 1 zero_lt_one with
    ⟨s, hsf, hs1⟩
  rw [← image_union_image_compl_eq_range]
  refine (hsf.image f).isBounded.union (isBounded_image_iff.2 ⟨1, fun x hx y hy => ?_⟩)
  exact le_of_lt (hs1 (x, y) ⟨hx, hy⟩)

/--
theorem `isBounded_range_of_cauchy_map_cofinite` / 定理 `isBounded_range_of_cauchy_map_cofinite`

English:
theorem isBounded_range_of_cauchy_map_cofinite
  given: {f : β -> α} (hf : Cauchy (map f cofinite))
  proof: isBounded_range_of_tendsto_cofinite_uniformity (cauchy_map_iff.1 hf).2

中文:
定理 isBounded_range_of_cauchy_map_cofinite
  条件: {f : β -> α} (hf : Cauchy (map f cofinite))
  证明: isBounded_range_of_tendsto_cofinite_uniformity (cauchy_map_iff.1 hf).2

Depends on / 依赖: cauchy_map_iff, isBounded_range_of_tendsto_cofinite_uniformity
-/
theorem isBounded_range_of_cauchy_map_cofinite {f : β -> α} (hf : Cauchy (map f cofinite)) :
    IsBounded (range f) :=
isBounded_range_of_tendsto_cofinite_uniformity (cauchy_map_iff.1 hf).2

/--
theorem `_root_.CauchySeq.isBounded_range` / 定理 `_root_.CauchySeq.isBounded_range`

English:
theorem _root_.CauchySeq.isBounded_range
  given: {f : Nat -> α} (hf : CauchySeq f)
  statement: IsBounded (range f)
  proof: isBounded_range_of_cauchy_map_cofinite by rwa [Nat.cofinite_eq_atTop]

中文:
定理 _root_.CauchySeq.isBounded_range
  条件: {f : 自然数 -> α} (hf : CauchySeq f)
  结论: IsBounded (range f)
  证明: isBounded_range_of_cauchy_map_cofinite by rwa [Nat.cofinite_eq_atTop]

Depends on / 依赖: Nat.cofinite_eq_atTop, cofinite_eq_atTop, isBounded_range_of_cauchy_map_cofinite
-/
theorem _root_.CauchySeq.isBounded_range {f : Nat -> α} (hf : CauchySeq f) : IsBounded (range f) :=
isBounded_range_of_cauchy_map_cofinite by rwa [Nat.cofinite_eq_atTop]

/--
theorem `isBounded_range_of_tendsto_cofinite` / 定理 `isBounded_range_of_tendsto_cofinite`

English:
theorem isBounded_range_of_tendsto_cofinite
  given: {f : β -> α} {a : α} (hf : Tendsto f cofinite (𝓝 a))
  proof: isBounded_range_of_tendsto_cofinite_uniformity
(hf.prodMap hf).mono_right nhds_prod_eq.symm.trans_le (nhds_le_uniformity a)

中文:
定理 isBounded_range_of_tendsto_cofinite
  条件: {f : β -> α} {a : α} (hf : Tendsto f cofinite (𝓝 a))
  证明: isBounded_range_of_tendsto_cofinite_uniformity
(hf.prodMap hf).mono_right nhds_prod_eq.symm.trans_le (nhds_le_uniformity a)

Depends on / 依赖: hf.prodMap, isBounded_range_of_tendsto_cofinite_uniformity, mono_right, nhds_le_uniformity, nhds_prod_eq, nhds_prod_eq.symm.trans_le, prodMap, trans_le
-/
theorem isBounded_range_of_tendsto_cofinite {f : β -> α} {a : α} (hf : Tendsto f cofinite (𝓝 a)) :
    IsBounded (range f) :=
isBounded_range_of_tendsto_cofinite_uniformity
(hf.prodMap hf).mono_right nhds_prod_eq.symm.trans_le (nhds_le_uniformity a)

/--
theorem `isBounded_of_compactSpace` / 定理 `isBounded_of_compactSpace`

English:
theorem isBounded_of_compactSpace
  given: [CompactSpace α]
  statement: IsBounded s
  proof: isCompact_univ.isBounded.subset (subset_univ _)

中文:
定理 isBounded_of_compactSpace
  条件: [CompactSpace α]
  结论: IsBounded s
  证明: isCompact_univ.isBounded.subset (subset_univ _)

Depends on / 依赖: isBounded, isCompact_univ, isCompact_univ.isBounded.subset, subset, subset_univ
-/
theorem isBounded_of_compactSpace [CompactSpace α] : IsBounded s :=
  isCompact_univ.isBounded.subset (subset_univ _)

/--
theorem `isBounded_range_of_tendsto` / 定理 `isBounded_range_of_tendsto`

English:
theorem isBounded_range_of_tendsto
  given: (u : Nat -> α) {x : α} (hu : Tendsto u atTop (𝓝 x))
  proof: hu.cauchySeq.isBounded_range

中文:
定理 isBounded_range_of_tendsto
  条件: (u : 自然数 -> α) {x : α} (hu : Tendsto u atTop (𝓝 x))
  证明: hu.cauchySeq.isBounded_range

Depends on / 依赖: cauchySeq, hu.cauchySeq.isBounded_range, isBounded_range
-/
theorem isBounded_range_of_tendsto (u : Nat -> α) {x : α} (hu : Tendsto u atTop (𝓝 x)) :
    IsBounded (range u) :=
  hu.cauchySeq.isBounded_range

/--
theorem `disjoint_nhds_cobounded` / 定理 `disjoint_nhds_cobounded`

English:
theorem disjoint_nhds_cobounded
  given: (x : α)
  statement: Disjoint (𝓝 x) (cobounded α)
  proof: disjoint_of_disjoint_of_mem disjoint_compl_right (ball_mem_nhds _ one_pos) isBounded_ball

中文:
定理 disjoint_nhds_cobounded
  条件: (x : α)
  结论: Disjoint (𝓝 x) (cobounded α)
  证明: disjoint_of_disjoint_of_mem disjoint_compl_right (ball_mem_nhds _ one_pos) isBounded_ball

Depends on / 依赖: ball_mem_nhds, disjoint_compl_right, disjoint_of_disjoint_of_mem, isBounded_ball, one_pos
-/
theorem disjoint_nhds_cobounded (x : α) : Disjoint (𝓝 x) (cobounded α) :=
  disjoint_of_disjoint_of_mem disjoint_compl_right (ball_mem_nhds _ one_pos) isBounded_ball

/--
theorem `disjoint_cobounded_nhds` / 定理 `disjoint_cobounded_nhds`

English:
theorem disjoint_cobounded_nhds
  given: (x : α)
  statement: Disjoint (cobounded α) (𝓝 x)
  proof: (disjoint_nhds_cobounded x).symm

中文:
定理 disjoint_cobounded_nhds
  条件: (x : α)
  结论: Disjoint (cobounded α) (𝓝 x)
  证明: (disjoint_nhds_cobounded x).symm

Depends on / 依赖: disjoint_nhds_cobounded
-/
theorem disjoint_cobounded_nhds (x : α) : Disjoint (cobounded α) (𝓝 x) :=
  (disjoint_nhds_cobounded x).symm

/--
theorem `disjoint_nhdsSet_cobounded` / 定理 `disjoint_nhdsSet_cobounded`

English:
theorem disjoint_nhdsSet_cobounded
  given: {s : Set α} (hs : IsCompact s)
  statement: Disjoint (𝓝ˢ s) (cobounded α)
  proof: hs.disjoint_nhdsSet_left.2 fun _ _ => disjoint_nhds_cobounded _

中文:
定理 disjoint_nhdsSet_cobounded
  条件: {s : Set α} (hs : IsCompact s)
  结论: Disjoint (𝓝ˢ s) (cobounded α)
  证明: hs.disjoint_nhdsSet_left.2 fun _ _ => disjoint_nhds_cobounded _

Depends on / 依赖: disjoint_nhdsSet_left, disjoint_nhds_cobounded, hs.disjoint_nhdsSet_left
-/
theorem disjoint_nhdsSet_cobounded {s : Set α} (hs : IsCompact s) : Disjoint (𝓝ˢ s) (cobounded α) :=
  hs.disjoint_nhdsSet_left.2 fun _ _ => disjoint_nhds_cobounded _

/--
theorem `disjoint_cobounded_nhdsSet` / 定理 `disjoint_cobounded_nhdsSet`

English:
theorem disjoint_cobounded_nhdsSet
  given: {s : Set α} (hs : IsCompact s)
  statement: Disjoint (cobounded α) (𝓝ˢ s)
  proof: (disjoint_nhdsSet_cobounded hs).symm

中文:
定理 disjoint_cobounded_nhdsSet
  条件: {s : Set α} (hs : IsCompact s)
  结论: Disjoint (cobounded α) (𝓝ˢ s)
  证明: (disjoint_nhdsSet_cobounded hs).symm

Depends on / 依赖: disjoint_nhdsSet_cobounded
-/
theorem disjoint_cobounded_nhdsSet {s : Set α} (hs : IsCompact s) : Disjoint (cobounded α) (𝓝ˢ s) :=
  (disjoint_nhdsSet_cobounded hs).symm

/--
theorem `exists_isBounded_image_of_tendsto` / 定理 `exists_isBounded_image_of_tendsto`

English:
theorem exists_isBounded_image_of_tendsto
  statement: {α β : Type*} [PseudoMetricSpace β]
  proof: (l.basis_sets.map f).disjoint_iff_left.mp (disjoint_nhds_cobounded x).mono_left hf

中文:
定理 exists_isBounded_image_of_tendsto
  结论: {α β : 类型} [PseudoMetricSpace β]
  证明: (l.basis_sets.map f).disjoint_iff_left.mp (disjoint_nhds_cobounded x).mono_left hf

Depends on / 依赖: basis_sets, disjoint_iff_left, disjoint_iff_left.mp, disjoint_nhds_cobounded, l.basis_sets.map, mono_left
-/
theorem exists_isBounded_image_of_tendsto {α β : Type*} [PseudoMetricSpace β]
    {l : Filter α} {f : α -> β} {x : β} (hf : Tendsto f l (𝓝 x)) :
    exists s in l, IsBounded (f '' s) :=
(l.basis_sets.map f).disjoint_iff_left.mp (disjoint_nhds_cobounded x).mono_left hf

/--
theorem `exists_isOpen_isBounded_image_inter_of_isCompact_of_forall_continuousWithinAt` / 定理 `exists_isOpen_isBounded_image_inter_of_isCompact_of_forall_continuousWithinAt`

English:
theorem exists_isOpen_isBounded_image_inter_of_isCompact_of_forall_continuousWithinAt
  proof: by
  have : Disjoint (𝓝ˢ k ⊓ 𝓟 s) (comap f (cobounded α)) := by
    rw [disjoint_assoc]; rw [inf_comm]; rw [hk.disjoint_nhdsSet_left]
exact fun x hx => disjoint_left_comm.2
      tendsto_comap.disjoint (disjoint_cobounded_nhds _) (hf x hx)
  rcases ((((hasBasis_nhdsSet _).inf_principal _)).disjoint_

中文:
定理 exists_isOpen_isBounded_image_inter_of_isCompact_of_forall_continuousWithinAt
  证明: by
  have : Disjoint (𝓝ˢ k ⊓ 𝓟 s) (comap f (cobounded α)) := by
    rw [disjoint_assoc]; rw [inf_comm]; rw [hk.disjoint_nhdsSet_left]
exact fun x hx => disjoint_left_comm.2
      tendsto_comap.disjoint (disjoint_cobounded_nhds _) (hf x hx)
  rcases ((((hasBasis_nhdsSet _).inf_principal _)).disjoint_

Depends on / 依赖: Disjoint, basis_sets, cobounded, disjoint, disjoint_assoc, disjoint_cobounded_nhds, disjoint_iff, disjoint_left_comm, disjoint_nhdsSet_left, hasBasis_nhdsSet, hk.disjoint_nhdsSet_left, image_subset_iff, inf_comm, inf_principal, isBounded_compl_iff, preimage_compl, subset, subset_compl_iff_disjoint_right, tendsto_comap, tendsto_comap.disjoint
-/
theorem exists_isOpen_isBounded_image_inter_of_isCompact_of_forall_continuousWithinAt
    [TopologicalSpace β] {k s : Set β} {f : β -> α} (hk : IsCompact k)
    (hf : forall x in k, ContinuousWithinAt f s x) :
    exists t, k subseteq t ∧ IsOpen t ∧ IsBounded (f '' (t inter s)) := by
  have : Disjoint (𝓝ˢ k ⊓ 𝓟 s) (comap f (cobounded α)) := by
    rw [disjoint_assoc]; rw [inf_comm]; rw [hk.disjoint_nhdsSet_left]
exact fun x hx => disjoint_left_comm.2
      tendsto_comap.disjoint (disjoint_cobounded_nhds _) (hf x hx)
  rcases ((((hasBasis_nhdsSet _).inf_principal _)).disjoint_iff ((basis_sets _).comap _)).1 this
    with ⟨U, ⟨hUo, hkU⟩, t, ht, hd⟩
  refine ⟨U, hkU, hUo, (isBounded_compl_iff.2 ht).subset ?_⟩
  rwa [image_subset_iff, preimage_compl, subset_compl_iff_disjoint_right]

/--
theorem `exists_isOpen_isBounded_image_of_isCompact_of_forall_continuousAt` / 定理 `exists_isOpen_isBounded_image_of_isCompact_of_forall_continuousAt`

English:
theorem exists_isOpen_isBounded_image_of_isCompact_of_forall_continuousAt
  statement: [TopologicalSpace β]
  proof: by
  simp_rw [← continuousWithinAt_univ] at hf
  simpa only [inter_univ] using
    exists_isOpen_isBounded_image_inter_of_isCompact_of_forall_continuousWithinAt hk hf

中文:
定理 exists_isOpen_isBounded_image_of_isCompact_of_forall_continuousAt
  结论: [TopologicalSpace β]
  证明: by
  simp_rw [← continuousWithinAt_univ] at hf
  simpa only [inter_univ] using
    exists_isOpen_isBounded_image_inter_of_isCompact_of_forall_continuousWithinAt hk hf

Depends on / 依赖: continuousWithinAt_univ, exists_isOpen_isBounded_image_inter_of_isCompact_of_forall_continuousWithinAt, inter_univ, simp_rw
-/
theorem exists_isOpen_isBounded_image_of_isCompact_of_forall_continuousAt [TopologicalSpace β]
    {k : Set β} {f : β -> α} (hk : IsCompact k) (hf : forall x in k, ContinuousAt f x) :
    exists t, k subseteq t ∧ IsOpen t ∧ IsBounded (f '' t) := by
  simp_rw [← continuousWithinAt_univ] at hf
  simpa only [inter_univ] using
    exists_isOpen_isBounded_image_inter_of_isCompact_of_forall_continuousWithinAt hk hf

/--
theorem `exists_isOpen_isBounded_image_inter_of_isCompact_of_continuousOn` / 定理 `exists_isOpen_isBounded_image_inter_of_isCompact_of_continuousOn`

English:
theorem exists_isOpen_isBounded_image_inter_of_isCompact_of_continuousOn
  statement: [TopologicalSpace β]
  proof: exists_isOpen_isBounded_image_inter_of_isCompact_of_forall_continuousWithinAt hk fun x hx =>
    hf x (hks hx)

中文:
定理 exists_isOpen_isBounded_image_inter_of_isCompact_of_continuousOn
  结论: [TopologicalSpace β]
  证明: exists_isOpen_isBounded_image_inter_of_isCompact_of_forall_continuousWithinAt hk fun x hx =>
    hf x (hks hx)

Depends on / 依赖: exists_isOpen_isBounded_image_inter_of_isCompact_of_forall_continuousWithinAt
-/
theorem exists_isOpen_isBounded_image_inter_of_isCompact_of_continuousOn [TopologicalSpace β]
    {k s : Set β} {f : β -> α} (hk : IsCompact k) (hks : k subseteq s) (hf : ContinuousOn f s) :
    exists t, k subseteq t ∧ IsOpen t ∧ IsBounded (f '' (t inter s)) :=
  exists_isOpen_isBounded_image_inter_of_isCompact_of_forall_continuousWithinAt hk fun x hx =>
    hf x (hks hx)

/--
theorem `exists_isOpen_isBounded_image_of_isCompact_of_continuousOn` / 定理 `exists_isOpen_isBounded_image_of_isCompact_of_continuousOn`

English:
theorem exists_isOpen_isBounded_image_of_isCompact_of_continuousOn
  statement: [TopologicalSpace β]
  proof: exists_isOpen_isBounded_image_of_isCompact_of_forall_continuousAt hk fun _x hx =>
    hf.continuousAt (hs.mem_nhds (hks hx))

中文:
定理 exists_isOpen_isBounded_image_of_isCompact_of_continuousOn
  结论: [TopologicalSpace β]
  证明: exists_isOpen_isBounded_image_of_isCompact_of_forall_continuousAt hk fun _x hx =>
    hf.continuousAt (hs.mem_nhds (hks hx))

Depends on / 依赖: continuousAt, exists_isOpen_isBounded_image_of_isCompact_of_forall_continuousAt, hf.continuousAt, hs.mem_nhds, mem_nhds
-/
theorem exists_isOpen_isBounded_image_of_isCompact_of_continuousOn [TopologicalSpace β]
    {k s : Set β} {f : β -> α} (hk : IsCompact k) (hs : IsOpen s) (hks : k subseteq s)
    (hf : ContinuousOn f s) : exists t, k subseteq t ∧ IsOpen t ∧ IsBounded (f '' t) :=
  exists_isOpen_isBounded_image_of_isCompact_of_forall_continuousAt hk fun _x hx =>
    hf.continuousAt (hs.mem_nhds (hks hx))

/--
theorem `isCompact_of_isClosed_isBounded` / 定理 `isCompact_of_isClosed_isBounded`

English:
theorem isCompact_of_isClosed_isBounded
  given: [ProperSpace α] (hc : IsClosed s) (hb : IsBounded s)
  proof: by
  rcases eq_empty_or_nonempty s with (rfl | ⟨x, -⟩)
  · exact isCompact_empty
  · rcases hb.subset_closedBall x with ⟨r, hr⟩
    exact (isCompact_closedBall x r).of_isClosed_subset hc hr

中文:
定理 isCompact_of_isClosed_isBounded
  条件: [命题erSpace α] (hc : IsClosed s) (hb : IsBounded s)
  证明: by
  rcases eq_empty_or_nonempty s with (rfl | ⟨x, -⟩)
  · exact isCompact_empty
  · rcases hb.subset_closedBall x with ⟨r, hr⟩
    exact (isCompact_closedBall x r).of_isClosed_subset hc hr

Depends on / 依赖: eq_empty_or_nonempty, hb.subset_closedBall, isCompact_closedBall, isCompact_empty, of_isClosed_subset, subset_closedBall
-/
theorem isCompact_of_isClosed_isBounded [ProperSpace α] (hc : IsClosed s) (hb : IsBounded s) :
    IsCompact s := by
  rcases eq_empty_or_nonempty s with (rfl | ⟨x, -⟩)
  · exact isCompact_empty
  · rcases hb.subset_closedBall x with ⟨r, hr⟩
    exact (isCompact_closedBall x r).of_isClosed_subset hc hr

/--
theorem `_root_.Bornology.IsBounded.isCompact_closure` / 定理 `_root_.Bornology.IsBounded.isCompact_closure`

English:
theorem _root_.Bornology.IsBounded.isCompact_closure
  given: [ProperSpace α] (h : IsBounded s)
  proof: isCompact_of_isClosed_isBounded isClosed_closure h.closure

中文:
定理 _root_.Bornology.IsBounded.isCompact_closure
  条件: [命题erSpace α] (h : IsBounded s)
  证明: isCompact_of_isClosed_isBounded isClosed_closure h.closure

Depends on / 依赖: closure, h.closure, isClosed_closure, isCompact_of_isClosed_isBounded
-/
theorem _root_.Bornology.IsBounded.isCompact_closure [ProperSpace α] (h : IsBounded s) :
    IsCompact (closure s) :=
  isCompact_of_isClosed_isBounded isClosed_closure h.closure

/-- The **Heine–Borel theorem**:
In a proper metric space, a set is compact if and only if it is closed and bounded. -/
@[wikidata Q253214]
/--
theorem `isCompact_iff_isClosed_bounded` / 定理 `isCompact_iff_isClosed_bounded`

English:
theorem isCompact_iff_isClosed_bounded
  given: {α : Type*} {s : Set α} [MetricSpace α] [ProperSpace α]
  proof: ⟨fun h => ⟨h.isClosed, h.isBounded⟩, fun h => isCompact_of_isClosed_isBounded h.1 h.2⟩

中文:
定理 isCompact_iff_isClosed_bounded
  条件: {α : 类型} {s : Set α} [MetricSpace α] [命题erSpace α]
  证明: ⟨fun h => ⟨h.isClosed, h.isBounded⟩, fun h => isCompact_of_isClosed_isBounded h.1 h.2⟩

Depends on / 依赖: h.isBounded, h.isClosed, isBounded, isClosed, isCompact_of_isClosed_isBounded
-/
theorem isCompact_iff_isClosed_bounded {α : Type*} {s : Set α} [MetricSpace α] [ProperSpace α] :
    IsCompact s ↔ IsClosed s ∧ IsBounded s :=
  ⟨fun h => ⟨h.isClosed, h.isBounded⟩, fun h => isCompact_of_isClosed_isBounded h.1 h.2⟩

/--
theorem `compactSpace_iff_isBounded_univ` / 定理 `compactSpace_iff_isBounded_univ`

English:
theorem compactSpace_iff_isBounded_univ
  given: [ProperSpace α]
  proof: ⟨@isBounded_of_compactSpace α _ _, fun hb => ⟨isCompact_of_isClosed_isBounded isClosed_univ hb⟩⟩

中文:
定理 compactSpace_iff_isBounded_univ
  条件: [命题erSpace α]
  证明: ⟨@isBounded_of_compactSpace α _ _, fun hb => ⟨isCompact_of_isClosed_isBounded isClosed_univ hb⟩⟩

Depends on / 依赖: isBounded_of_compactSpace, isClosed_univ, isCompact_of_isClosed_isBounded
-/
theorem compactSpace_iff_isBounded_univ [ProperSpace α] :
    CompactSpace α ↔ IsBounded (univ : Set α) :=
  ⟨@isBounded_of_compactSpace α _ _, fun hb => ⟨isCompact_of_isClosed_isBounded isClosed_univ hb⟩⟩

section CompactIccSpace

variable [Preorder α] [CompactIccSpace α]

/--
theorem `isBounded_Icc` / 定理 `isBounded_Icc`

English:
theorem isBounded_Icc
  given: (a b : α)
  statement: IsBounded (Icc a b)
  proof: (totallyBounded_Icc a b).isBounded

中文:
定理 isBounded_Icc
  条件: (a b : α)
  结论: IsBounded (Icc a b)
  证明: (totallyBounded_Icc a b).isBounded

Depends on / 依赖: isBounded, totallyBounded_Icc
-/
theorem isBounded_Icc (a b : α) : IsBounded (Icc a b) :=
  (totallyBounded_Icc a b).isBounded

/--
theorem `isBounded_Ico` / 定理 `isBounded_Ico`

English:
theorem isBounded_Ico
  given: (a b : α)
  statement: IsBounded (Ico a b)
  proof: (totallyBounded_Ico a b).isBounded

中文:
定理 isBounded_Ico
  条件: (a b : α)
  结论: IsBounded (Ico a b)
  证明: (totallyBounded_Ico a b).isBounded

Depends on / 依赖: isBounded, totallyBounded_Ico
-/
theorem isBounded_Ico (a b : α) : IsBounded (Ico a b) :=
  (totallyBounded_Ico a b).isBounded

/--
theorem `isBounded_Ioc` / 定理 `isBounded_Ioc`

English:
theorem isBounded_Ioc
  given: (a b : α)
  statement: IsBounded (Ioc a b)
  proof: (totallyBounded_Ioc a b).isBounded

中文:
定理 isBounded_Ioc
  条件: (a b : α)
  结论: IsBounded (Ioc a b)
  证明: (totallyBounded_Ioc a b).isBounded

Depends on / 依赖: isBounded, totallyBounded_Ioc
-/
theorem isBounded_Ioc (a b : α) : IsBounded (Ioc a b) :=
  (totallyBounded_Ioc a b).isBounded

/--
theorem `isBounded_Ioo` / 定理 `isBounded_Ioo`

English:
theorem isBounded_Ioo
  given: (a b : α)
  statement: IsBounded (Ioo a b)
  proof: (totallyBounded_Ioo a b).isBounded

中文:
定理 isBounded_Ioo
  条件: (a b : α)
  结论: IsBounded (Ioo a b)
  证明: (totallyBounded_Ioo a b).isBounded

Depends on / 依赖: isBounded, totallyBounded_Ioo
-/
theorem isBounded_Ioo (a b : α) : IsBounded (Ioo a b) :=
  (totallyBounded_Ioo a b).isBounded

/--
theorem `isBounded_of_bddAbove_of_bddBelow` / 定理 `isBounded_of_bddAbove_of_bddBelow`

English:
theorem isBounded_of_bddAbove_of_bddBelow
  given: {s : Set α} (h₁ : BddAbove s) (h₂ : BddBelow s)
  proof: let ⟨u, hu⟩ := h₁
  let ⟨l, hl⟩ := h₂
  (isBounded_Icc l u).subset (fun _x hx => mem_Icc.mpr ⟨hl hx, hu hx⟩)

中文:
定理 isBounded_of_bddAbove_of_bddBelow
  条件: {s : Set α} (h₁ : BddAbove s) (h₂ : BddBelow s)
  证明: let ⟨u, hu⟩ := h₁
  let ⟨l, hl⟩ := h₂
  (isBounded_Icc l u).subset (fun _x hx => mem_Icc.mpr ⟨hl hx, hu hx⟩)

Depends on / 依赖: isBounded_Icc, mem_Icc, mem_Icc.mpr, subset
-/
theorem isBounded_of_bddAbove_of_bddBelow {s : Set α} (h₁ : BddAbove s) (h₂ : BddBelow s) :
    IsBounded s :=
  let ⟨u, hu⟩ := h₁
  let ⟨l, hl⟩ := h₂
  (isBounded_Icc l u).subset (fun _x hx => mem_Icc.mpr ⟨hl hx, hu hx⟩)

open Metric in
/--
lemma `_root_.IsOrderBornology.of_isCompactIcc` / 引理 `_root_.IsOrderBornology.of_isCompactIcc`

English:
lemma _root_.IsOrderBornology.of_isCompactIcc
  statement: (x : α)
  proof: by
    refine ⟨?_, fun hs => Metric.isBounded_of_bddAbove_of_bddBelow hs.2 hs.1⟩
    rw [Metric.isBounded_iff_subset_closedBall x]
    rintro ⟨r, hr⟩
    exact ⟨(bddBelow_ball _).mono hr, (bddAbove_ball _).mono hr⟩

中文:
引理 _root_.IsOrderBornology.of_isCompactIcc
  结论: (x : α)
  证明: by
    refine ⟨?_, fun hs => Metric.isBounded_of_bddAbove_of_bddBelow hs.2 hs.1⟩
    rw [Metric.isBounded_iff_subset_closedBall x]
    rintro ⟨r, hr⟩
    exact ⟨(bddBelow_ball _).mono hr, (bddAbove_ball _).mono hr⟩

Depends on / 依赖: Metric, Metric.isBounded_iff_subset_closedBall, Metric.isBounded_of_bddAbove_of_bddBelow, bddAbove_ball, bddBelow_ball, isBounded_iff_subset_closedBall, isBounded_of_bddAbove_of_bddBelow
-/
lemma _root_.IsOrderBornology.of_isCompactIcc (x : α)
    (bddBelow_ball : forall r, BddBelow (closedBall x r))
    (bddAbove_ball : forall r, BddAbove (closedBall x r)) : IsOrderBornology α where
  isBounded_iff_bddBelow_bddAbove s := by
    refine ⟨?_, fun hs => Metric.isBounded_of_bddAbove_of_bddBelow hs.2 hs.1⟩
    rw [Metric.isBounded_iff_subset_closedBall x]
    rintro ⟨r, hr⟩
    exact ⟨(bddBelow_ball _).mono hr, (bddAbove_ball _).mono hr⟩

end CompactIccSpace

section CompactIccSpace_abs

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [PseudoMetricSpace α]
  [CompactIccSpace α]

/--
lemma `isBounded_of_abs_le` / 引理 `isBounded_of_abs_le`

English:
lemma isBounded_of_abs_le
  given: (C : α)
  statement: Bornology.IsBounded {x : α | |x| <= C}
  proof: by
  convert! Metric.isBounded_Icc (-C) C
  ext1 x
  simp [abs_le]

中文:
引理 isBounded_of_abs_le
  条件: (C : α)
  结论: Bornology.IsBounded {x : α | |x| <= C}
  证明: by
  convert! Metric.isBounded_Icc (-C) C
  ext1 x
  simp [abs_le]

Depends on / 依赖: Metric, Metric.isBounded_Icc, abs_le, convert, isBounded_Icc
-/
lemma isBounded_of_abs_le (C : α) : Bornology.IsBounded {x : α | |x| <= C} := by
  convert! Metric.isBounded_Icc (-C) C
  ext1 x
  simp [abs_le]

/--
lemma `isBounded_of_abs_lt` / 引理 `isBounded_of_abs_lt`

English:
lemma isBounded_of_abs_lt
  given: (C : α)
  statement: Bornology.IsBounded {x : α | |x| < C}
  proof: by
  convert! Metric.isBounded_Ioo (-C) C
  ext1 x
  simp [abs_lt]

中文:
引理 isBounded_of_abs_lt
  条件: (C : α)
  结论: Bornology.IsBounded {x : α | |x| < C}
  证明: by
  convert! Metric.isBounded_Ioo (-C) C
  ext1 x
  simp [abs_lt]

Depends on / 依赖: Metric, Metric.isBounded_Ioo, abs_lt, convert, isBounded_Ioo
-/
lemma isBounded_of_abs_lt (C : α) : Bornology.IsBounded {x : α | |x| < C} := by
  convert! Metric.isBounded_Ioo (-C) C
  ext1 x
  simp [abs_lt]

end CompactIccSpace_abs

end Bounded

section Diam

variable {s : Set α} {x y z : α}

section PseudoMetricSpace
variable [PseudoMetricSpace α]

/--
Definition of `diam` / `diam` 的定义

English:
definition diam
  signature: (s : Set α)
  body: ENNReal.toReal (ediam s)

中文:
定义 diam
  签名: (s : Set α)
  定义体: ENNReal.toReal (ediam s)

Depends on / 依赖: ENNReal, ENNReal.toReal, toReal
-/
noncomputable def diam (s : Set α) : Real :=
  ENNReal.toReal (ediam s)

/--
theorem `diam_nonneg` / 定理 `diam_nonneg`

English:
theorem diam_nonneg
  statement: 0 <= diam s
  proof: ENNReal.toReal_nonneg

中文:
定理 diam_nonneg
  结论: 0 <= diam s
  证明: ENNReal.toReal_nonneg

Depends on / 依赖: ENNReal, ENNReal.toReal_nonneg, toReal_nonneg
-/
theorem diam_nonneg : 0 <= diam s :=
  ENNReal.toReal_nonneg

/--
theorem `diam_subsingleton` / 定理 `diam_subsingleton`

English:
theorem diam_subsingleton
  given: (hs : s.Subsingleton)
  statement: diam s = 0
  proof: by
  simp [diam, ediam_subsingleton hs]

中文:
定理 diam_subsingleton
  条件: (hs : s.Subsingleton)
  结论: diam s = 0
  证明: by
  simp [diam, ediam_subsingleton hs]

Depends on / 依赖: ediam_subsingleton
-/
theorem diam_subsingleton (hs : s.Subsingleton) : diam s = 0 := by
  simp [diam, ediam_subsingleton hs]

/-- The empty set has zero diameter -/
@[simp]
/--
theorem `diam_empty` / 定理 `diam_empty`

English:
theorem diam_empty
  statement: diam (∅ : Set α) = 0
  proof: diam_subsingleton subsingleton_empty

中文:
定理 diam_empty
  结论: diam (∅ : Set α) = 0
  证明: diam_subsingleton subsingleton_empty

Depends on / 依赖: diam_subsingleton, subsingleton_empty
-/
theorem diam_empty : diam (∅ : Set α) = 0 :=
  diam_subsingleton subsingleton_empty

/-- A singleton has zero diameter -/
@[simp]
/--
theorem `diam_singleton` / 定理 `diam_singleton`

English:
theorem diam_singleton
  statement: diam ({x} : Set α) = 0
  proof: diam_subsingleton subsingleton_singleton

@[to_additive (attr := simp)]

中文:
定理 diam_singleton
  结论: diam ({x} : Set α) = 0
  证明: diam_subsingleton subsingleton_singleton

@[to_additive (attr := simp)]

Depends on / 依赖: diam_subsingleton, subsingleton_singleton
-/
theorem diam_singleton : diam ({x} : Set α) = 0 :=
  diam_subsingleton subsingleton_singleton

@[to_additive (attr := simp)]
/--
theorem `diam_one` / 定理 `diam_one`

English:
theorem diam_one
  given: [One α]
  statement: diam (1 : Set α) = 0
  proof: diam_singleton

中文:
定理 diam_one
  条件: [One α]
  结论: diam (1 : Set α) = 0
  证明: diam_singleton

Depends on / 依赖: diam_singleton
-/
theorem diam_one [One α] : diam (1 : Set α) = 0 :=
  diam_singleton

-- Does not work as a simp-lemma, since {x, y} reduces to (insert y {x})
/--
theorem `diam_pair` / 定理 `diam_pair`

English:
theorem diam_pair
  statement: diam ({x, y} : Set α) = dist x y
  proof: by
  simp only [diam, ediam_pair, dist_edist]

中文:
定理 diam_pair
  结论: diam ({x, y} : Set α) = dist x y
  证明: by
  simp only [diam, ediam_pair, dist_edist]

Depends on / 依赖: dist_edist, ediam_pair
-/
theorem diam_pair : diam ({x, y} : Set α) = dist x y := by
  simp only [diam, ediam_pair, dist_edist]

-- Does not work as a simp-lemma, since {x, y, z} reduces to (insert z (insert y {x}))
/--
theorem `diam_triple` / 定理 `diam_triple`

English:
theorem diam_triple
  proof: by
  simp only [diam, ediam_triple, dist_edist]
  rw [ENNReal.toReal_max]; rw [ENNReal.toReal_max] <;> apply_rules [ne_of_lt, edist_lt_top, max_lt]

中文:
定理 diam_triple
  证明: by
  simp only [diam, ediam_triple, dist_edist]
  rw [ENNReal.toReal_max]; rw [ENNReal.toReal_max] <;> apply_rules [ne_of_lt, edist_lt_top, max_lt]

Depends on / 依赖: ENNReal, ENNReal.toReal_max, apply_rules, dist_edist, ediam_triple, edist_lt_top, max_lt, ne_of_lt, toReal_max
-/
theorem diam_triple :
    diam ({x, y, z} : Set α) = max (max (dist x y) (dist x z)) (dist y z) := by
  simp only [diam, ediam_triple, dist_edist]
  rw [ENNReal.toReal_max]; rw [ENNReal.toReal_max] <;> apply_rules [ne_of_lt, edist_lt_top, max_lt]

/--
theorem `ediam_le_of_forall_dist_le` / 定理 `ediam_le_of_forall_dist_le`

English:
theorem ediam_le_of_forall_dist_le
  given: {C : Real} (h : forall x in s, forall y in s, dist x y <= C)
  proof: ediam_le fun x hx y hy => (edist_dist x y).symm ▸ ENNReal.ofReal_le_ofReal (h x hx y hy)

中文:
定理 ediam_le_of_forall_dist_le
  条件: {C : 实数} (h : 对任意 x in s, 对任意 y in s, dist x y <= C)
  证明: ediam_le fun x hx y hy => (edist_dist x y).symm ▸ ENNReal.ofReal_le_ofReal (h x hx y hy)

Depends on / 依赖: ENNReal, ENNReal.ofReal_le_ofReal, ediam_le, edist_dist, ofReal_le_ofReal
-/
theorem ediam_le_of_forall_dist_le {C : Real} (h : forall x in s, forall y in s, dist x y <= C) :
    ediam s <= ENNReal.ofReal C :=
  ediam_le fun x hx y hy => (edist_dist x y).symm ▸ ENNReal.ofReal_le_ofReal (h x hx y hy)

/--
theorem `diam_le_of_forall_dist_le` / 定理 `diam_le_of_forall_dist_le`

English:
theorem diam_le_of_forall_dist_le
  given: {C : Real} (h₀ : 0 <= C) (h : forall x in s, forall y in s, dist x y <= C)
  proof: ENNReal.toReal_le_of_le_ofReal h₀ (ediam_le_of_forall_dist_le h)

中文:
定理 diam_le_of_forall_dist_le
  条件: {C : 实数} (h₀ : 0 <= C) (h : 对任意 x in s, 对任意 y in s, dist x y <= C)
  证明: ENNReal.toReal_le_of_le_ofReal h₀ (ediam_le_of_forall_dist_le h)

Depends on / 依赖: ENNReal, ENNReal.toReal_le_of_le_ofReal, ediam_le_of_forall_dist_le, toReal_le_of_le_ofReal
-/
theorem diam_le_of_forall_dist_le {C : Real} (h₀ : 0 <= C) (h : forall x in s, forall y in s, dist x y <= C) :
    diam s <= C :=
  ENNReal.toReal_le_of_le_ofReal h₀ (ediam_le_of_forall_dist_le h)

/--
theorem `diam_le_of_forall_dist_le_of_nonempty` / 定理 `diam_le_of_forall_dist_le_of_nonempty`

English:
theorem diam_le_of_forall_dist_le_of_nonempty
  statement: (hs : s.Nonempty) {C : Real}
  proof: have h₀ : 0 <= C :=
    let ⟨x, hx⟩ := hs
    le_trans dist_nonneg (h x hx x hx)
  diam_le_of_forall_dist_le h₀ h

中文:
定理 diam_le_of_forall_dist_le_of_nonempty
  结论: (hs : s.Nonempty) {C : 实数}
  证明: have h₀ : 0 <= C :=
    let ⟨x, hx⟩ := hs
    le_trans dist_nonneg (h x hx x hx)
  diam_le_of_forall_dist_le h₀ h

Depends on / 依赖: diam_le_of_forall_dist_le, dist_nonneg, le_trans
-/
theorem diam_le_of_forall_dist_le_of_nonempty (hs : s.Nonempty) {C : Real}
    (h : forall x in s, forall y in s, dist x y <= C) : diam s <= C :=
  have h₀ : 0 <= C :=
    let ⟨x, hx⟩ := hs
    le_trans dist_nonneg (h x hx x hx)
  diam_le_of_forall_dist_le h₀ h

/--
theorem `dist_le_diam_of_mem'` / 定理 `dist_le_diam_of_mem'`

English:
theorem dist_le_diam_of_mem'
  given: (h : ediam s != ⊤) (hx : x in s) (hy : y in s)
  proof: by
  rw [diam]; rw [dist_edist]
exact ENNReal.toReal_mono h edist_le_ediam_of_mem hx hy

中文:
定理 dist_le_diam_of_mem'
  条件: (h : ediam s != ⊤) (hx : x in s) (hy : y in s)
  证明: by
  rw [diam]; rw [dist_edist]
exact ENNReal.toReal_mono h edist_le_ediam_of_mem hx hy

Depends on / 依赖: ENNReal, ENNReal.toReal_mono, dist_edist, edist_le_ediam_of_mem, toReal_mono
-/
theorem dist_le_diam_of_mem' (h : ediam s != ⊤) (hx : x in s) (hy : y in s) :
    dist x y <= diam s := by
  rw [diam]; rw [dist_edist]
exact ENNReal.toReal_mono h edist_le_ediam_of_mem hx hy

/--
theorem `isBounded_iff_ediam_ne_top` / 定理 `isBounded_iff_ediam_ne_top`

English:
theorem isBounded_iff_ediam_ne_top
  statement: IsBounded s ↔ ediam s != ⊤
  proof: isBounded_iff.trans Iff.intro
    (fun ⟨_C, hC⟩ => ne_top_of_le_ne_top ENNReal.ofReal_ne_top <| ediam_le_of_forall_dist_le hC)
    fun h => ⟨diam s, fun _x hx _y hy => dist_le_diam_of_mem' h hx hy⟩

alias ⟨_root_.Bornology.IsBounded.ediam_ne_top, _⟩ := isBounded_iff_ediam_ne_top

中文:
定理 isBounded_iff_ediam_ne_top
  结论: IsBounded s ↔ ediam s != ⊤
  证明: isBounded_iff.trans Iff.intro
    (fun ⟨_C, hC⟩ => ne_top_of_le_ne_top ENNReal.ofReal_ne_top <| ediam_le_of_forall_dist_le hC)
    fun h => ⟨diam s, fun _x hx _y hy => dist_le_diam_of_mem' h hx hy⟩

alias ⟨_root_.Bornology.IsBounded.ediam_ne_top, _⟩ := isBounded_iff_ediam_ne_top

Depends on / 依赖: ENNReal, ENNReal.ofReal_ne_top, Iff.intro, dist_le_diam_of_mem, ediam_le_of_forall_dist_le, isBounded_iff, isBounded_iff.trans, ne_top_of_le_ne_top, ofReal_ne_top
-/
theorem isBounded_iff_ediam_ne_top : IsBounded s ↔ ediam s != ⊤ :=
isBounded_iff.trans Iff.intro
    (fun ⟨_C, hC⟩ => ne_top_of_le_ne_top ENNReal.ofReal_ne_top <| ediam_le_of_forall_dist_le hC)
    fun h => ⟨diam s, fun _x hx _y hy => dist_le_diam_of_mem' h hx hy⟩

alias ⟨_root_.Bornology.IsBounded.ediam_ne_top, _⟩ := isBounded_iff_ediam_ne_top

/--
theorem `ediam_eq_top_iff_unbounded` / 定理 `ediam_eq_top_iff_unbounded`

English:
theorem ediam_eq_top_iff_unbounded
  statement: ediam s = ⊤ ↔ ¬IsBounded s
  proof: isBounded_iff_ediam_ne_top.not_left.symm

中文:
定理 ediam_eq_top_iff_unbounded
  结论: ediam s = ⊤ ↔ ¬IsBounded s
  证明: isBounded_iff_ediam_ne_top.not_left.symm

Depends on / 依赖: isBounded_iff_ediam_ne_top, isBounded_iff_ediam_ne_top.not_left.symm, not_left
-/
theorem ediam_eq_top_iff_unbounded : ediam s = ⊤ ↔ ¬IsBounded s :=
  isBounded_iff_ediam_ne_top.not_left.symm

/--
theorem `ediam_univ_eq_top_iff_noncompact` / 定理 `ediam_univ_eq_top_iff_noncompact`

English:
theorem ediam_univ_eq_top_iff_noncompact
  given: [ProperSpace α]
  proof: by
  rw [← not_compactSpace_iff]; rw [compactSpace_iff_isBounded_univ]; rw [isBounded_iff_ediam_ne_top]; rw [Classical.not_not]

@[simp]

中文:
定理 ediam_univ_eq_top_iff_noncompact
  条件: [命题erSpace α]
  证明: by
  rw [← not_compactSpace_iff]; rw [compactSpace_iff_isBounded_univ]; rw [isBounded_iff_ediam_ne_top]; rw [Classical.not_not]

@[simp]

Depends on / 依赖: Classical, Classical.not_not, compactSpace_iff_isBounded_univ, isBounded_iff_ediam_ne_top, not_compactSpace_iff, not_not
-/
theorem ediam_univ_eq_top_iff_noncompact [ProperSpace α] :
    ediam (univ : Set α) = ∞ ↔ NoncompactSpace α := by
  rw [← not_compactSpace_iff]; rw [compactSpace_iff_isBounded_univ]; rw [isBounded_iff_ediam_ne_top]; rw [Classical.not_not]

@[simp]
/--
theorem `ediam_univ_of_noncompact` / 定理 `ediam_univ_of_noncompact`

English:
theorem ediam_univ_of_noncompact
  given: [ProperSpace α] [NoncompactSpace α]
  proof: ediam_univ_eq_top_iff_noncompact.mpr ‹_›

@[simp]

中文:
定理 ediam_univ_of_noncompact
  条件: [命题erSpace α] [NoncompactSpace α]
  证明: ediam_univ_eq_top_iff_noncompact.mpr ‹_›

@[simp]

Depends on / 依赖: ediam_univ_eq_top_iff_noncompact, ediam_univ_eq_top_iff_noncompact.mpr
-/
theorem ediam_univ_of_noncompact [ProperSpace α] [NoncompactSpace α] :
    ediam (univ : Set α) = ∞ :=
  ediam_univ_eq_top_iff_noncompact.mpr ‹_›

@[simp]
/--
theorem `diam_univ_of_noncompact` / 定理 `diam_univ_of_noncompact`

English:
theorem diam_univ_of_noncompact
  given: [ProperSpace α] [NoncompactSpace α]
  statement: diam (univ : Set α) = 0
  proof: by
  simp [diam]

中文:
定理 diam_univ_of_noncompact
  条件: [命题erSpace α] [NoncompactSpace α]
  结论: diam (univ : Set α) = 0
  证明: by
  simp [diam]
-/
theorem diam_univ_of_noncompact [ProperSpace α] [NoncompactSpace α] : diam (univ : Set α) = 0 := by
  simp [diam]

/--
theorem `dist_le_diam_of_mem` / 定理 `dist_le_diam_of_mem`

English:
theorem dist_le_diam_of_mem
  given: (h : IsBounded s) (hx : x in s) (hy : y in s)
  statement: dist x y <= diam s
  proof: dist_le_diam_of_mem' h.ediam_ne_top hx hy

中文:
定理 dist_le_diam_of_mem
  条件: (h : IsBounded s) (hx : x in s) (hy : y in s)
  结论: dist x y <= diam s
  证明: dist_le_diam_of_mem' h.ediam_ne_top hx hy

Depends on / 依赖: dist_le_diam_of_mem, ediam_ne_top, h.ediam_ne_top
-/
theorem dist_le_diam_of_mem (h : IsBounded s) (hx : x in s) (hy : y in s) : dist x y <= diam s :=
  dist_le_diam_of_mem' h.ediam_ne_top hx hy

/--
theorem `ediam_of_unbounded` / 定理 `ediam_of_unbounded`

English:
theorem ediam_of_unbounded
  given: (h : ¬IsBounded s)
  statement: ediam s = ∞
  proof: ediam_eq_top_iff_unbounded.2 h

中文:
定理 ediam_of_unbounded
  条件: (h : ¬IsBounded s)
  结论: ediam s = ∞
  证明: ediam_eq_top_iff_unbounded.2 h

Depends on / 依赖: ediam_eq_top_iff_unbounded
-/
theorem ediam_of_unbounded (h : ¬IsBounded s) : ediam s = ∞ := ediam_eq_top_iff_unbounded.2 h

/--
theorem `diam_eq_zero_of_unbounded` / 定理 `diam_eq_zero_of_unbounded`

English:
theorem diam_eq_zero_of_unbounded
  given: (h : ¬IsBounded s)
  statement: diam s = 0
  proof: by
  rw [diam]; rw [ediam_of_unbounded h]; rw [ENNReal.toReal_top]

中文:
定理 diam_eq_zero_of_unbounded
  条件: (h : ¬IsBounded s)
  结论: diam s = 0
  证明: by
  rw [diam]; rw [ediam_of_unbounded h]; rw [ENNReal.toReal_top]

Depends on / 依赖: ENNReal, ENNReal.toReal_top, ediam_of_unbounded, toReal_top
-/
theorem diam_eq_zero_of_unbounded (h : ¬IsBounded s) : diam s = 0 := by
  rw [diam]; rw [ediam_of_unbounded h]; rw [ENNReal.toReal_top]

/--
theorem `diam_mono` / 定理 `diam_mono`

English:
theorem diam_mono
  given: {s t : Set α} (h : s subseteq t) (ht : IsBounded t)
  statement: diam s <= diam t
  proof: ENNReal.toReal_mono ht.ediam_ne_top ediam_mono h

中文:
定理 diam_mono
  条件: {s t : Set α} (h : s subseteq t) (ht : IsBounded t)
  结论: diam s <= diam t
  证明: ENNReal.toReal_mono ht.ediam_ne_top ediam_mono h

Depends on / 依赖: ENNReal, ENNReal.toReal_mono, ediam_mono, ediam_ne_top, ht.ediam_ne_top, toReal_mono
-/
theorem diam_mono {s t : Set α} (h : s subseteq t) (ht : IsBounded t) : diam s <= diam t :=
ENNReal.toReal_mono ht.ediam_ne_top ediam_mono h

/--
theorem `diam_union` / 定理 `diam_union`

English:
theorem diam_union
  given: {t : Set α} (xs : x in s) (yt : y in t)
  proof: by
  simp only [diam, dist_edist]
  grw [ENNReal.toReal_le_add' (ediam_union_le_add_edist xs yt), ENNReal.toReal_add_le]
  · simp only [ENNReal.add_eq_top, edist_ne_top, or_false]
exact fun h => top_unique h ▸ ediam_mono subset_union_left
· exact fun h => top_unique h ▸ ediam_mono subset_union_right

中文:
定理 diam_union
  条件: {t : Set α} (xs : x in s) (yt : y in t)
  证明: by
  simp only [diam, dist_edist]
  grw [ENNReal.toReal_le_add' (ediam_union_le_add_edist xs yt), ENNReal.toReal_add_le]
  · simp only [ENNReal.add_eq_top, edist_ne_top, or_false]
exact fun h => top_unique h ▸ ediam_mono subset_union_left
· exact fun h => top_unique h ▸ ediam_mono subset_union_right

Depends on / 依赖: ENNReal, ENNReal.add_eq_top, ENNReal.toReal_add_le, ENNReal.toReal_le_add, add_eq_top, dist_edist, ediam_mono, ediam_union_le_add_edist, edist_ne_top, or_false, subset_union_left, subset_union_right, toReal_add_le, toReal_le_add, top_unique
-/
theorem diam_union {t : Set α} (xs : x in s) (yt : y in t) :
    diam (s union t) <= diam s + dist x y + diam t := by
  simp only [diam, dist_edist]
  grw [ENNReal.toReal_le_add' (ediam_union_le_add_edist xs yt), ENNReal.toReal_add_le]
  · simp only [ENNReal.add_eq_top, edist_ne_top, or_false]
exact fun h => top_unique h ▸ ediam_mono subset_union_left
· exact fun h => top_unique h ▸ ediam_mono subset_union_right

/--
theorem `diam_union'` / 定理 `diam_union'`

English:
theorem diam_union'
  given: {t : Set α} (h : (s inter t).Nonempty)
  statement: diam (s union t) <= diam s + diam t
  proof: by
  rcases h with ⟨x, ⟨xs, xt⟩⟩
  simpa using diam_union xs xt

中文:
定理 diam_union'
  条件: {t : Set α} (h : (s inter t).Nonempty)
  结论: diam (s union t) <= diam s + diam t
  证明: by
  rcases h with ⟨x, ⟨xs, xt⟩⟩
  simpa using diam_union xs xt

Depends on / 依赖: diam_union
-/
theorem diam_union' {t : Set α} (h : (s inter t).Nonempty) : diam (s union t) <= diam s + diam t := by
  rcases h with ⟨x, ⟨xs, xt⟩⟩
  simpa using diam_union xs xt

/--
theorem `diam_le_of_subset_closedBall` / 定理 `diam_le_of_subset_closedBall`

English:
theorem diam_le_of_subset_closedBall
  given: {r : Real} (hr : 0 <= r) (h : s subseteq closedBall x r)
  proof: diam_le_of_forall_dist_le (mul_nonneg zero_le_two hr) fun a ha b hb =>
    calc
      dist a b <= dist a x + dist b x := dist_triangle_right _ _ _
      _ <= r + r := add_le_add (h ha) (h hb)
      _ = 2 * r := by simp [mul_two, mul_comm]

中文:
定理 diam_le_of_subset_closedBall
  条件: {r : 实数} (hr : 0 <= r) (h : s subseteq closedBall x r)
  证明: diam_le_of_forall_dist_le (mul_nonneg zero_le_two hr) fun a ha b hb =>
    calc
      dist a b <= dist a x + dist b x := dist_triangle_right _ _ _
      _ <= r + r := add_le_add (h ha) (h hb)
      _ = 2 * r := by simp [mul_two, mul_comm]

Depends on / 依赖: add_le_add, diam_le_of_forall_dist_le, dist_triangle_right, mul_comm, mul_nonneg, mul_two, zero_le_two
-/
theorem diam_le_of_subset_closedBall {r : Real} (hr : 0 <= r) (h : s subseteq closedBall x r) :
    diam s <= 2 * r :=
  diam_le_of_forall_dist_le (mul_nonneg zero_le_two hr) fun a ha b hb =>
    calc
      dist a b <= dist a x + dist b x := dist_triangle_right _ _ _
      _ <= r + r := add_le_add (h ha) (h hb)
      _ = 2 * r := by simp [mul_two, mul_comm]

/--
theorem `diam_closedBall` / 定理 `diam_closedBall`

English:
theorem diam_closedBall
  given: {r : Real} (h : 0 <= r)
  statement: diam (closedBall x r) <= 2 * r
  proof: diam_le_of_subset_closedBall h Subset.rfl

中文:
定理 diam_closedBall
  条件: {r : 实数} (h : 0 <= r)
  结论: diam (closedBall x r) <= 2 * r
  证明: diam_le_of_subset_closedBall h Subset.rfl

Depends on / 依赖: Subset, Subset.rfl, diam_le_of_subset_closedBall
-/
theorem diam_closedBall {r : Real} (h : 0 <= r) : diam (closedBall x r) <= 2 * r :=
  diam_le_of_subset_closedBall h Subset.rfl

/--
theorem `diam_ball` / 定理 `diam_ball`

English:
theorem diam_ball
  given: {r : Real} (h : 0 <= r)
  statement: diam (ball x r) <= 2 * r
  proof: diam_le_of_subset_closedBall h ball_subset_closedBall

中文:
定理 diam_ball
  条件: {r : 实数} (h : 0 <= r)
  结论: diam (ball x r) <= 2 * r
  证明: diam_le_of_subset_closedBall h ball_subset_closedBall

Depends on / 依赖: ball_subset_closedBall, diam_le_of_subset_closedBall
-/
theorem diam_ball {r : Real} (h : 0 <= r) : diam (ball x r) <= 2 * r :=
  diam_le_of_subset_closedBall h ball_subset_closedBall

/--
theorem `_root_.IsComplete.nonempty_iInter_of_nonempty_biInter` / 定理 `_root_.IsComplete.nonempty_iInter_of_nonempty_biInter`

English:
theorem _root_.IsComplete.nonempty_iInter_of_nonempty_biInter
  statement: {s : Nat -> Set α}
  proof: by
  let u N := (h N).some
  have I : forall n N, n <= N -> u N in s n := by
    intro n N hn
    apply mem_of_subset_of_mem _ (h N).choose_spec
    intro x hx
    simp only [mem_iInter] at hx
    exact hx n hn
  have : CauchySeq u := by
    apply cauchySeq_of_le_tendsto_0 _ _ h'
    intro m n N hm 

中文:
定理 _root_.IsComplete.nonempty_iInter_of_nonempty_biInter
  结论: {s : 自然数 -> Set α}
  证明: by
  let u N := (h N).some
  have I : forall n N, n <= N -> u N in s n := by
    intro n N hn
    apply mem_of_subset_of_mem _ (h N).choose_spec
    intro x hx
    simp only [mem_iInter] at hx
    exact hx n hn
  have : CauchySeq u := by
    apply cauchySeq_of_le_tendsto_0 _ _ h'
    intro m n N hm 

Depends on / 依赖: CauchySeq, Tendsto, cauchySeq_of_le_tendsto_0, cauchySeq_tendsto_of_isComplete, choose_spec, dist_le_diam_of_mem, mem_iInter, mem_of_subset_of_mem, zero_le
-/
theorem _root_.IsComplete.nonempty_iInter_of_nonempty_biInter {s : Nat -> Set α}
    (h0 : IsComplete (s 0)) (hs : forall n, IsClosed (s n)) (h's : forall n, IsBounded (s n))
    (h : forall N, (⋂ n <= N, s n).Nonempty) (h' : Tendsto (fun n => diam (s n)) atTop (𝓝 0)) :
    (⋂ n, s n).Nonempty := by
  let u N := (h N).some
  have I : forall n N, n <= N -> u N in s n := by
    intro n N hn
    apply mem_of_subset_of_mem _ (h N).choose_spec
    intro x hx
    simp only [mem_iInter] at hx
    exact hx n hn
  have : CauchySeq u := by
    apply cauchySeq_of_le_tendsto_0 _ _ h'
    intro m n N hm hn
    exact dist_le_diam_of_mem (h's N) (I _ _ hm) (I _ _ hn)
  obtain ⟨x, -, xlim⟩ : exists x in s 0, Tendsto (fun n : Nat => u n) atTop (𝓝 x) :=
    cauchySeq_tendsto_of_isComplete h0 (fun n => I 0 n zero_le) this
  refine ⟨x, mem_iInter.2 fun n => ?_⟩
  apply (hs n).mem_of_tendsto xlim
  filter_upwards [Ici_mem_atTop n] with p hp
  exact I n p hp

/--
theorem `nonempty_iInter_of_nonempty_biInter` / 定理 `nonempty_iInter_of_nonempty_biInter`

English:
theorem nonempty_iInter_of_nonempty_biInter
  statement: [CompleteSpace α] {s : Nat -> Set α}
  proof: (hs 0).isComplete.nonempty_iInter_of_nonempty_biInter hs h's h h'

中文:
定理 nonempty_iInter_of_nonempty_biInter
  结论: [CompleteSpace α] {s : 自然数 -> Set α}
  证明: (hs 0).isComplete.nonempty_iInter_of_nonempty_biInter hs h's h h'

Depends on / 依赖: isComplete, isComplete.nonempty_iInter_of_nonempty_biInter, nonempty_iInter_of_nonempty_biInter
-/
theorem nonempty_iInter_of_nonempty_biInter [CompleteSpace α] {s : Nat -> Set α}
    (hs : forall n, IsClosed (s n)) (h's : forall n, IsBounded (s n)) (h : forall N, (⋂ n <= N, s n).Nonempty)
    (h' : Tendsto (fun n => diam (s n)) atTop (𝓝 0)) : (⋂ n, s n).Nonempty :=
  (hs 0).isComplete.nonempty_iInter_of_nonempty_biInter hs h's h h'

end PseudoMetricSpace

section MetricSpace

/--
theorem `diam_pos` / 定理 `diam_pos`

English:
theorem diam_pos
  given: [MetricSpace α] (hs1 : s.Nontrivial) (hs2 : IsBounded s)
  statement: 0 < diam s
  proof: by
  rcases hs1 with ⟨x, hx, y, hy, hxy⟩
exact (dist_pos.mpr hxy).trans_le Metric.dist_le_diam_of_mem hs2 hx hy

中文:
定理 diam_pos
  条件: [MetricSpace α] (hs1 : s.Nontrivial) (hs2 : IsBounded s)
  结论: 0 < diam s
  证明: by
  rcases hs1 with ⟨x, hx, y, hy, hxy⟩
exact (dist_pos.mpr hxy).trans_le Metric.dist_le_diam_of_mem hs2 hx hy

Depends on / 依赖: Metric, Metric.dist_le_diam_of_mem, dist_le_diam_of_mem, dist_pos, dist_pos.mpr, trans_le
-/
theorem diam_pos [MetricSpace α] (hs1 : s.Nontrivial) (hs2 : IsBounded s) : 0 < diam s := by
  rcases hs1 with ⟨x, hx, y, hy, hxy⟩
exact (dist_pos.mpr hxy).trans_le Metric.dist_le_diam_of_mem hs2 hx hy

end MetricSpace

end Diam

end Metric

namespace Mathlib.Meta.Positivity

open Lean Meta Qq Function

/-- Extension for the `positivity` tactic: the diameter of a set is always nonnegative. -/
@[positivity Metric.diam _]
meta def evalDiam : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(Real), ~q(@Metric.diam _ $inst $s) =>
    assertInstancesCommute
    pure (.nonnegative q(Metric.diam_nonneg))
  | _, _, _ => throwError "not ‖ · ‖"

end Mathlib.Meta.Positivity

section

open Metric

variable [PseudoMetricSpace α]

/--
theorem `Metric.cobounded_eq_cocompact` / 定理 `Metric.cobounded_eq_cocompact`

English:
theorem Metric.cobounded_eq_cocompact
  given: [ProperSpace α]
  statement: cobounded α = cocompact α
  proof: by
  nontriviality α; inhabit α
exact cobounded_le_cocompact.antisymm (hasBasis_cobounded_compl_closedBall default).ge_iff.2
    fun _ _ => (isCompact_closedBall _ _).compl_mem_cocompact

中文:
定理 Metric.cobounded_eq_cocompact
  条件: [命题erSpace α]
  结论: cobounded α = cocompact α
  证明: by
  nontriviality α; inhabit α
exact cobounded_le_cocompact.antisymm (hasBasis_cobounded_compl_closedBall default).ge_iff.2
    fun _ _ => (isCompact_closedBall _ _).compl_mem_cocompact

Depends on / 依赖: antisymm, cobounded_le_cocompact, cobounded_le_cocompact.antisymm, compl_mem_cocompact, ge_iff, hasBasis_cobounded_compl_closedBall, inhabit, isCompact_closedBall, nontriviality
-/
theorem Metric.cobounded_eq_cocompact [ProperSpace α] : cobounded α = cocompact α := by
  nontriviality α; inhabit α
exact cobounded_le_cocompact.antisymm (hasBasis_cobounded_compl_closedBall default).ge_iff.2
    fun _ _ => (isCompact_closedBall _ _).compl_mem_cocompact

/--
theorem `tendsto_dist_right_cocompact_atTop` / 定理 `tendsto_dist_right_cocompact_atTop`

English:
theorem tendsto_dist_right_cocompact_atTop
  given: [ProperSpace α] (x : α)
  proof: (tendsto_dist_right_cobounded_atTop x).mono_left cobounded_eq_cocompact.ge

中文:
定理 tendsto_dist_right_cocompact_atTop
  条件: [命题erSpace α] (x : α)
  证明: (tendsto_dist_right_cobounded_atTop x).mono_left cobounded_eq_cocompact.ge

Depends on / 依赖: cobounded_eq_cocompact, cobounded_eq_cocompact.ge, mono_left, tendsto_dist_right_cobounded_atTop
-/
theorem tendsto_dist_right_cocompact_atTop [ProperSpace α] (x : α) :
    Tendsto (dist · x) (cocompact α) atTop :=
  (tendsto_dist_right_cobounded_atTop x).mono_left cobounded_eq_cocompact.ge

/--
theorem `tendsto_dist_left_cocompact_atTop` / 定理 `tendsto_dist_left_cocompact_atTop`

English:
theorem tendsto_dist_left_cocompact_atTop
  given: [ProperSpace α] (x : α)
  proof: (tendsto_dist_left_cobounded_atTop x).mono_left cobounded_eq_cocompact.ge

中文:
定理 tendsto_dist_left_cocompact_atTop
  条件: [命题erSpace α] (x : α)
  证明: (tendsto_dist_left_cobounded_atTop x).mono_left cobounded_eq_cocompact.ge

Depends on / 依赖: cobounded_eq_cocompact, cobounded_eq_cocompact.ge, mono_left, tendsto_dist_left_cobounded_atTop
-/
theorem tendsto_dist_left_cocompact_atTop [ProperSpace α] (x : α) :
    Tendsto (dist x) (cocompact α) atTop :=
  (tendsto_dist_left_cobounded_atTop x).mono_left cobounded_eq_cocompact.ge

/--
theorem `comap_dist_left_atTop_eq_cocompact` / 定理 `comap_dist_left_atTop_eq_cocompact`

English:
theorem comap_dist_left_atTop_eq_cocompact
  given: [ProperSpace α] (x : α)
  proof: by simp [cobounded_eq_cocompact]

中文:
定理 comap_dist_left_atTop_eq_cocompact
  条件: [命题erSpace α] (x : α)
  证明: by simp [cobounded_eq_cocompact]

Depends on / 依赖: cobounded_eq_cocompact
-/
theorem comap_dist_left_atTop_eq_cocompact [ProperSpace α] (x : α) :
    comap (dist x) atTop = cocompact α := by simp [cobounded_eq_cocompact]

/--
theorem `tendsto_cocompact_of_tendsto_dist_comp_atTop` / 定理 `tendsto_cocompact_of_tendsto_dist_comp_atTop`

English:
theorem tendsto_cocompact_of_tendsto_dist_comp_atTop
  statement: {f : β -> α} {l : Filter β} (x : α)
  proof: ((tendsto_dist_right_atTop_iff _).1 h).mono_right cobounded_le_cocompact

中文:
定理 tendsto_cocompact_of_tendsto_dist_comp_atTop
  结论: {f : β -> α} {l : Filter β} (x : α)
  证明: ((tendsto_dist_right_atTop_iff _).1 h).mono_right cobounded_le_cocompact

Depends on / 依赖: cobounded_le_cocompact, mono_right, tendsto_dist_right_atTop_iff
-/
theorem tendsto_cocompact_of_tendsto_dist_comp_atTop {f : β -> α} {l : Filter β} (x : α)
    (h : Tendsto (fun y => dist (f y) x) l atTop) : Tendsto f l (cocompact α) :=
  ((tendsto_dist_right_atTop_iff _).1 h).mono_right cobounded_le_cocompact

/--
theorem `Metric.finite_isBounded_inter_isClosed` / 定理 `Metric.finite_isBounded_inter_isClosed`

English:
theorem Metric.finite_isBounded_inter_isClosed
  statement: [ProperSpace α] {K s : Set α} (hsd : IsDiscrete s)
  proof: by
  refine (IsCompact.finite ?_ ?_).subset (Set.inter_subset_inter_left s subset_closure)
  · exact hK.isCompact_closure.inter_right hs
  · exact hsd.mono Set.inter_subset_right

中文:
定理 Metric.finite_isBounded_inter_isClosed
  结论: [命题erSpace α] {K s : Set α} (hsd : IsDiscrete s)
  证明: by
  refine (IsCompact.finite ?_ ?_).subset (Set.inter_subset_inter_left s subset_closure)
  · exact hK.isCompact_closure.inter_right hs
  · exact hsd.mono Set.inter_subset_right

Depends on / 依赖: IsCompact, IsCompact.finite, Set.inter_subset_inter_left, Set.inter_subset_right, finite, hK.isCompact_closure.inter_right, hsd.mono, inter_right, inter_subset_inter_left, inter_subset_right, isCompact_closure, subset, subset_closure
-/
theorem Metric.finite_isBounded_inter_isClosed [ProperSpace α] {K s : Set α} (hsd : IsDiscrete s)
    (hK : IsBounded K) (hs : IsClosed s) : Set.Finite (K inter s) := by
  refine (IsCompact.finite ?_ ?_).subset (Set.inter_subset_inter_left s subset_closure)
  · exact hK.isCompact_closure.inter_right hs
  · exact hsd.mono Set.inter_subset_right

end

namespace Continuous

variable {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderClosedTopology α]
  [PseudoMetricSpace β] [ProperSpace β]

/--
theorem `exists_forall_le_of_isBounded` / 定理 `exists_forall_le_of_isBounded`

English:
theorem exists_forall_le_of_isBounded
  statement: {f : β -> α} (hf : Continuous f) (x₀ : β)
  proof: by
  refine hf.exists_forall_le' (x₀ := x₀) ?_
  have hU : {x : β | f x₀ < f x} in Filter.cocompact β := by
    refine Filter.mem_cocompact'.mpr ⟨_, ?_, fun ⦃_⦄ a => a⟩
    simp only [Set.compl_ofPred, not_lt]
    exact Metric.isCompact_of_isClosed_isBounded (isClosed_le (by fun_prop) (by fun_prop))

中文:
定理 exists_forall_le_of_isBounded
  结论: {f : β -> α} (hf : Continuous f) (x₀ : β)
  证明: by
  refine hf.exists_forall_le' (x₀ := x₀) ?_
  have hU : {x : β | f x₀ < f x} in Filter.cocompact β := by
    refine Filter.mem_cocompact'.mpr ⟨_, ?_, fun ⦃_⦄ a => a⟩
    simp only [Set.compl_ofPred, not_lt]
    exact Metric.isCompact_of_isClosed_isBounded (isClosed_le (by fun_prop) (by fun_prop))

Depends on / 依赖: Filter, Filter.cocompact, Filter.mem_cocompact, Metric, Metric.isCompact_of_isClosed_isBounded, Set.compl_ofPred, cocompact, compl_ofPred, exists_forall_le, filter_upwards, fun_prop, hf.exists_forall_le, hx.le, isClosed_le, isCompact_of_isClosed_isBounded, mem_cocompact, not_lt
-/
theorem exists_forall_le_of_isBounded {f : β -> α} (hf : Continuous f) (x₀ : β)
    (h : Bornology.IsBounded {x : β | f x <= f x₀}) :
    exists x, forall y, f x <= f y := by
  refine hf.exists_forall_le' (x₀ := x₀) ?_
  have hU : {x : β | f x₀ < f x} in Filter.cocompact β := by
    refine Filter.mem_cocompact'.mpr ⟨_, ?_, fun ⦃_⦄ a => a⟩
    simp only [Set.compl_ofPred, not_lt]
    exact Metric.isCompact_of_isClosed_isBounded (isClosed_le (by fun_prop) (by fun_prop)) h
  filter_upwards [hU] with x hx using hx.le

/--
theorem `exists_forall_ge_of_isBounded` / 定理 `exists_forall_ge_of_isBounded`

English:
theorem exists_forall_ge_of_isBounded
  statement: {f : β -> α} (hf : Continuous f) (x₀ : β)
  proof: hf.exists_forall_le_of_isBounded (α := αᵒᵈ) x₀ h

中文:
定理 exists_forall_ge_of_isBounded
  结论: {f : β -> α} (hf : Continuous f) (x₀ : β)
  证明: hf.exists_forall_le_of_isBounded (α := αᵒᵈ) x₀ h

Depends on / 依赖: exists_forall_le_of_isBounded, hf.exists_forall_le_of_isBounded
-/
theorem exists_forall_ge_of_isBounded {f : β -> α} (hf : Continuous f) (x₀ : β)
    (h : Bornology.IsBounded {x : β | f x₀ <= f x}) :
    exists x, forall y, f y <= f x :=
  hf.exists_forall_le_of_isBounded (α := αᵒᵈ) x₀ h

end Continuous
