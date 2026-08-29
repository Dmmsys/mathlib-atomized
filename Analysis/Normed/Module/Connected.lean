/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Connectedness of subsets of vector spaces

We show several results related to the (path)-connectedness of subsets of real vector spaces:
* `Set.Countable.isPathConnected_compl_of_one_lt_rank` asserts that the complement of a countable
  set is path-connected in a space of dimension `> 1`.
* `isPathConnected_compl_singleton_of_one_lt_rank` is the special case of the complement of a
  singleton.
* `isPathConnected_sphere` shows that any sphere is path-connected in dimension `> 1`.
* `isPathConnected_compl_of_one_lt_codim` shows that the complement of a subspace
  of codimension `> 1` is path-connected.

Statements with connectedness instead of path-connectedness are also given.
-/

public section

assert_not_exists Subgroup.index Nat.divisors
-- TODO assert_not_exists Cardinal

open Set Metric
open scoped Convex ENNReal

section TopologicalVectorSpace

variable {E : Type*} [AddCommGroup E] [Module Real E]
  [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul Real E]

/--
theorem `Set.Countable.isPathConnected_compl_of_one_lt_rank` / 定理 `Set.Countable.isPathConnected_compl_of_one_lt_rank`

English:
theorem Set.Countable.isPathConnected_compl_of_one_lt_rank
  proof: by
  have : Nontrivial E := (rank_pos_iff_nontrivial (R := Real)).1 (zero_lt_one.trans h)
  -- the set `sᶜ` is dense, therefore nonempty. Pick `a ∈ sᶜ`. We have to show that any
  -- `b ∈ sᶜ` can be joined to `a`.
  obtain ⟨a, ha⟩ : sᶜ.Nonempty := (hs.dense_compl Real).nonempty
  refine ⟨a, ha, ?_⟩


中文:
定理 集合.可数.isPathConnected_compl_of_one_lt_rank
  证明: by
  have : Nontrivial E := (rank_pos_iff_nontrivial (R := Real)).1 (zero_lt_one.trans h)
  -- the set `sᶜ` is dense, therefore nonempty. Pick `a ∈ sᶜ`. We have to show that any
  -- `b ∈ sᶜ` can be joined to `a`.
  obtain ⟨a, ha⟩ : sᶜ.Nonempty := (hs.dense_compl Real).nonempty
  refine ⟨a, ha, ?_⟩


Depends on / 依赖: Nontrivial, rank_pos_iff_nontrivial, zero_lt_one, zero_lt_one.trans
-/
theorem Set.Countable.isPathConnected_compl_of_one_lt_rank
    (h : 1 < Module.rank Real E) {s : Set E} (hs : s.Countable) :
    IsPathConnected sᶜ := by
  have : Nontrivial E := (rank_pos_iff_nontrivial (R := Real)).1 (zero_lt_one.trans h)
  -- the set `sᶜ` is dense, therefore nonempty. Pick `a ∈ sᶜ`. We have to show that any
  -- `b ∈ sᶜ` can be joined to `a`.
  obtain ⟨a, ha⟩ : sᶜ.Nonempty := (hs.dense_compl Real).nonempty
  refine ⟨a, ha, ?_⟩
  intro b hb
  rcases eq_or_ne a b with rfl | hab
  · exact JoinedIn.refl ha
  /- Assume `b ≠ a`. Write `a = c - x` and `b = c + x` for some nonzero `x`. Choose `y` which
  is linearly independent from `x`. Then the segments joining `a = c - x` to `c + ty` are pairwise
  disjoint for varying `t` (except for the endpoint `a`) so only countably many of them can
  intersect `s`. In the same way, there are countably many `t`s for which the segment
  from `b = c + x` to `c + ty` intersects `s`. Choosing `t` outside of these countable exceptions,
  one gets a path in the complement of `s` from `a` to `z = c + ty` and then to `b`.
  -/
  let c := (2 : Real)⁻¹ • (a + b)
  let x := (2 : Real)⁻¹ • (b - a)
  have Ia : c - x = a := by
    simp only [c, x]
    module
  have Ib : c + x = b := by
    simp only [c, x]
    module
  have x_ne_zero : x != 0 := by simpa [x] using sub_ne_zero.2 hab.symm
  obtain ⟨y, hy⟩ : exists y, LinearIndependent Real ![x, y] :=
    exists_linearIndependent_pair_of_one_lt_rank h x_ne_zero
  have A : Set.Countable {t : Real | ([c + x -[Real] c + t • y] inter s).Nonempty} := by
    apply countable_ofPred_nonempty_of_disjoint _ (fun t => inter_subset_right) hs
    intro t t' htt'
    apply disjoint_iff_inter_eq_empty.2
    have N : {c + x} inter s = ∅ := by
      simpa only [singleton_inter_eq_empty, mem_compl_iff, Ib] using hb
    rw [inter_assoc]; rw [inter_comm s]; rw [inter_assoc]; rw [inter_self]; rw [← inter_assoc]; rw [← subset_empty_iff]; rw [← N]
    apply inter_subset_inter_left
    apply Eq.subset
    apply segment_inter_eq_endpoint_of_linearIndependent_of_ne hy htt'.symm
  have B : Set.Countable {t : Real | ([c - x -[Real] c + t • y] inter s).Nonempty} := by
    apply countable_ofPred_nonempty_of_disjoint _ (fun t => inter_subset_right) hs
    intro t t' htt'
    apply disjoint_iff_inter_eq_empty.2
    have N : {c - x} inter s = ∅ := by
      simpa only [singleton_inter_eq_empty, mem_compl_iff, Ia] using ha
    rw [inter_assoc]; rw [inter_comm s]; rw [inter_assoc]; rw [inter_self]; rw [← inter_assoc]; rw [← subset_empty_iff]; rw [← N]
    apply inter_subset_inter_left
    rw [sub_eq_add_neg _ x]
    apply Eq.subset
    apply segment_inter_eq_endpoint_of_linearIndependent_of_ne _ htt'.symm
    convert! hy.units_smul ![-1, 1]
    simp [← List.ofFn_inj]
  obtain ⟨t, ht⟩ : Set.Nonempty ({t : Real | ([c + x -[Real] c + t • y] inter s).Nonempty}
      union {t : Real | ([c - x -[Real] c + t • y] inter s).Nonempty})ᶜ := ((A.union B).dense_compl Real).nonempty
  let z := c + t • y
  simp only [compl_union, mem_inter_iff, mem_compl_iff, mem_ofPred_eq, not_nonempty_iff_eq_empty]
    at ht
  have JA : JoinedIn sᶜ a z := by
    apply JoinedIn.of_segment_subset
    rw [subset_compl_iff_disjoint_right]; rw [disjoint_iff_inter_eq_empty]
    convert! ht.2
    exact Ia.symm
  have JB : JoinedIn sᶜ b z := by
    apply JoinedIn.of_segment_subset
    rw [subset_compl_iff_disjoint_right]; rw [disjoint_iff_inter_eq_empty]
    convert! ht.1
    exact Ib.symm
  exact JA.trans JB.symm

/--
theorem `Set.Countable.isConnected_compl_of_one_lt_rank` / 定理 `Set.Countable.isConnected_compl_of_one_lt_rank`

English:
theorem Set.Countable.isConnected_compl_of_one_lt_rank
  statement: (h : 1 < Module.rank Real E) {s : Set E}
  proof: (hs.isPathConnected_compl_of_one_lt_rank h).isConnected

中文:
定理 集合.可数.isConnected_compl_of_one_lt_rank
  结论: (h : 1 < 模.rank 实数 E) {s : 集合 E}
  证明: (hs.isPathConnected_compl_of_one_lt_rank h).isConnected

Depends on / 依赖: hs.isPathConnected_compl_of_one_lt_rank, isConnected, isPathConnected_compl_of_one_lt_rank
-/
theorem Set.Countable.isConnected_compl_of_one_lt_rank (h : 1 < Module.rank Real E) {s : Set E}
    (hs : s.Countable) : IsConnected sᶜ :=
  (hs.isPathConnected_compl_of_one_lt_rank h).isConnected

/--
theorem `isPathConnected_compl_singleton_of_one_lt_rank` / 定理 `isPathConnected_compl_singleton_of_one_lt_rank`

English:
theorem isPathConnected_compl_singleton_of_one_lt_rank
  given: (h : 1 < Module.rank Real E) (x : E)
  proof: Set.Countable.isPathConnected_compl_of_one_lt_rank h (countable_singleton x)

中文:
定理 isPathConnected_compl_singleton_of_one_lt_rank
  条件: (h : 1 < 模.rank 实数 E) (x : E)
  证明: Set.Countable.isPathConnected_compl_of_one_lt_rank h (countable_singleton x)

Depends on / 依赖: Countable, Set.Countable.isPathConnected_compl_of_one_lt_rank, countable_singleton, isPathConnected_compl_of_one_lt_rank
-/
theorem isPathConnected_compl_singleton_of_one_lt_rank (h : 1 < Module.rank Real E) (x : E) :
    IsPathConnected {x}ᶜ :=
  Set.Countable.isPathConnected_compl_of_one_lt_rank h (countable_singleton x)

/--
theorem `isConnected_compl_singleton_of_one_lt_rank` / 定理 `isConnected_compl_singleton_of_one_lt_rank`

English:
theorem isConnected_compl_singleton_of_one_lt_rank
  given: (h : 1 < Module.rank Real E) (x : E)
  proof: (isPathConnected_compl_singleton_of_one_lt_rank h x).isConnected

中文:
定理 isConnected_compl_singleton_of_one_lt_rank
  条件: (h : 1 < 模.rank 实数 E) (x : E)
  证明: (isPathConnected_compl_singleton_of_one_lt_rank h x).isConnected

Depends on / 依赖: isConnected, isPathConnected_compl_singleton_of_one_lt_rank
-/
theorem isConnected_compl_singleton_of_one_lt_rank (h : 1 < Module.rank Real E) (x : E) :
    IsConnected {x}ᶜ :=
  (isPathConnected_compl_singleton_of_one_lt_rank h x).isConnected

end TopologicalVectorSpace

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]

section Ball

namespace Metric

/--
theorem `contractibleSpace_ball` / 定理 `contractibleSpace_ball`

English:
theorem contractibleSpace_ball
  given: {x : E} {r : Real} (hr : 0 < r)
  proof: (convex_ball _ _).contractibleSpace (by simpa)

@[deprecated (since := "2026-02-02")]
alias ball_contractible := contractibleSpace_ball

中文:
定理 contractibleSpace_ball
  条件: {x : E} {r : 实数} (hr : 0 < r)
  证明: (convex_ball _ _).contractibleSpace (by simpa)

@[deprecated (since := "2026-02-02")]
alias ball_contractible := contractibleSpace_ball

Depends on / 依赖: contractibleSpace, convex_ball
-/
theorem contractibleSpace_ball {x : E} {r : Real} (hr : 0 < r) :
    ContractibleSpace (ball x r) :=
  (convex_ball _ _).contractibleSpace (by simpa)

@[deprecated (since := "2026-02-02")]
alias ball_contractible := contractibleSpace_ball

/--
theorem `contractibleSpace_eball` / 定理 `contractibleSpace_eball`

English:
theorem contractibleSpace_eball
  given: {x : E} {r : Real>=0∞} (hr : 0 < r)
  proof: (convex_eball _ _).contractibleSpace ⟨x, by simpa⟩

@[deprecated (since := "2026-02-02")]
alias eball_contractible := contractibleSpace_eball

中文:
定理 contractibleSpace_eball
  条件: {x : E} {r : 实数>=0∞} (hr : 0 < r)
  证明: (convex_eball _ _).contractibleSpace ⟨x, by simpa⟩

@[deprecated (since := "2026-02-02")]
alias eball_contractible := contractibleSpace_eball

Depends on / 依赖: contractibleSpace, convex_eball
-/
theorem contractibleSpace_eball {x : E} {r : Real>=0∞} (hr : 0 < r) :
    ContractibleSpace (eball x r) :=
  (convex_eball _ _).contractibleSpace ⟨x, by simpa⟩

@[deprecated (since := "2026-02-02")]
alias eball_contractible := contractibleSpace_eball

/--
theorem `contractibleSpace_closedBall` / 定理 `contractibleSpace_closedBall`

English:
theorem contractibleSpace_closedBall
  given: {x : E} {r : Real} (hr : 0 <= r)
  proof: (convex_closedBall _ _).contractibleSpace (by simpa)

中文:
定理 contractibleSpace_closedBall
  条件: {x : E} {r : 实数} (hr : 0 <= r)
  证明: (convex_closedBall _ _).contractibleSpace (by simpa)

Depends on / 依赖: contractibleSpace, convex_closedBall
-/
theorem contractibleSpace_closedBall {x : E} {r : Real} (hr : 0 <= r) :
    ContractibleSpace (closedBall x r) :=
  (convex_closedBall _ _).contractibleSpace (by simpa)

/--
Instance `contractibleSpace_closedEBall` / 实例 `contractibleSpace_closedEBall`

English:
instance contractibleSpace_closedEBall
  signature: {x : E} {r : Real>=0∞}
  body: (convex_closedEBall _ _).contractibleSpace ⟨x, by simp⟩

中文:
实例 contractibleSpace_closedEBall
  签名: {x : E} {r : 实数>=0∞}
  定义体: (convex_closedEBall _ _).contractibleSpace ⟨x, by simp⟩

Depends on / 依赖: contractibleSpace, convex_closedEBall
-/
instance contractibleSpace_closedEBall {x : E} {r : Real>=0∞} :
    ContractibleSpace (closedEBall x r) :=
  (convex_closedEBall _ _).contractibleSpace ⟨x, by simp⟩

/--
theorem `isPathConnected_ball` / 定理 `isPathConnected_ball`

English:
theorem isPathConnected_ball
  given: {x : E} {r : Real} (hr : 0 < r)
  proof: .isPathConnected by simpa convex_ball _ _

中文:
定理 isPathConnected_ball
  条件: {x : E} {r : 实数} (hr : 0 < r)
  证明: .isPathConnected by simpa convex_ball _ _

Depends on / 依赖: convex_ball, isPathConnected
-/
theorem isPathConnected_ball {x : E} {r : Real} (hr : 0 < r) :
    IsPathConnected (ball x r) :=
.isPathConnected by simpa convex_ball _ _

/--
theorem `isPathConnected_eball` / 定理 `isPathConnected_eball`

English:
theorem isPathConnected_eball
  given: {x : E} {r : Real>=0∞} (hr : 0 < r)
  proof: .isPathConnected ⟨x, by simpa⟩ convex_eball _ _

中文:
定理 isPathConnected_eball
  条件: {x : E} {r : 实数>=0∞} (hr : 0 < r)
  证明: .isPathConnected ⟨x, by simpa⟩ convex_eball _ _

Depends on / 依赖: convex_eball, isPathConnected
-/
theorem isPathConnected_eball {x : E} {r : Real>=0∞} (hr : 0 < r) :
    IsPathConnected (eball x r) :=
.isPathConnected ⟨x, by simpa⟩ convex_eball _ _

/--
theorem `isPathConnected_closedBall` / 定理 `isPathConnected_closedBall`

English:
theorem isPathConnected_closedBall
  given: {x : E} {r : Real} (hr : 0 <= r)
  proof: .isPathConnected ⟨x, by simpa⟩ convex_closedBall _ _

中文:
定理 isPathConnected_closedBall
  条件: {x : E} {r : 实数} (hr : 0 <= r)
  证明: .isPathConnected ⟨x, by simpa⟩ convex_closedBall _ _

Depends on / 依赖: convex_closedBall, isPathConnected
-/
theorem isPathConnected_closedBall {x : E} {r : Real} (hr : 0 <= r) :
    IsPathConnected (closedBall x r) :=
.isPathConnected ⟨x, by simpa⟩ convex_closedBall _ _

/--
theorem `isPathConnected_closedEBall` / 定理 `isPathConnected_closedEBall`

English:
theorem isPathConnected_closedEBall
  given: {x : E} {r : Real>=0∞}
  proof: isPathConnected_iff_pathConnectedSpace.mpr inferInstance

中文:
定理 isPathConnected_closedEBall
  条件: {x : E} {r : 实数>=0∞}
  证明: isPathConnected_iff_pathConnectedSpace.mpr inferInstance

Depends on / 依赖: isPathConnected_iff_pathConnectedSpace, isPathConnected_iff_pathConnectedSpace.mpr
-/
theorem isPathConnected_closedEBall {x : E} {r : Real>=0∞} :
    IsPathConnected (closedEBall x r) :=
  isPathConnected_iff_pathConnectedSpace.mpr inferInstance

/--
theorem `isPreconnected_ball` / 定理 `isPreconnected_ball`

English:
theorem isPreconnected_ball
  given: {x : E} {r : Real}
  statement: IsPreconnected (ball x r)
  proof: (convex_ball _ _).isPreconnected

中文:
定理 isPreconnected_ball
  条件: {x : E} {r : 实数}
  结论: 是预连通 (ball x r)
  证明: (convex_ball _ _).isPreconnected

Depends on / 依赖: convex_ball, isPreconnected
-/
theorem isPreconnected_ball {x : E} {r : Real} : IsPreconnected (ball x r) :=
  (convex_ball _ _).isPreconnected

/--
theorem `isPreconnected_eball` / 定理 `isPreconnected_eball`

English:
theorem isPreconnected_eball
  given: {x : E} {r : Real>=0∞}
  statement: IsPreconnected (eball x r)
  proof: (convex_eball _ _).isPreconnected

中文:
定理 isPreconnected_eball
  条件: {x : E} {r : 实数>=0∞}
  结论: 是预连通 (eball x r)
  证明: (convex_eball _ _).isPreconnected

Depends on / 依赖: convex_eball, isPreconnected
-/
theorem isPreconnected_eball {x : E} {r : Real>=0∞} : IsPreconnected (eball x r) :=
  (convex_eball _ _).isPreconnected

/--
theorem `isPreconnected_closedBall` / 定理 `isPreconnected_closedBall`

English:
theorem isPreconnected_closedBall
  given: {x : E} {r : Real}
  statement: IsPreconnected (closedBall x r)
  proof: (convex_closedBall _ _).isPreconnected

中文:
定理 isPreconnected_closedBall
  条件: {x : E} {r : 实数}
  结论: 是预连通 (closedBall x r)
  证明: (convex_closedBall _ _).isPreconnected

Depends on / 依赖: convex_closedBall, isPreconnected
-/
theorem isPreconnected_closedBall {x : E} {r : Real} : IsPreconnected (closedBall x r) :=
  (convex_closedBall _ _).isPreconnected

/--
theorem `isPreconnected_closedEBall` / 定理 `isPreconnected_closedEBall`

English:
theorem isPreconnected_closedEBall
  given: {x : E} {r : Real>=0∞}
  statement: IsPreconnected (closedEBall x r)
  proof: (convex_closedEBall _ _).isPreconnected

中文:
定理 isPreconnected_closedEBall
  条件: {x : E} {r : 实数>=0∞}
  结论: 是预连通 (closedEBall x r)
  证明: (convex_closedEBall _ _).isPreconnected

Depends on / 依赖: convex_closedEBall, isPreconnected
-/
theorem isPreconnected_closedEBall {x : E} {r : Real>=0∞} : IsPreconnected (closedEBall x r) :=
  (convex_closedEBall _ _).isPreconnected

/--
theorem `isConnected_ball` / 定理 `isConnected_ball`

English:
theorem isConnected_ball
  given: {x : E} {r : Real} (hr : 0 < r)
  proof: (isPathConnected_ball hr).isConnected

中文:
定理 isConnected_ball
  条件: {x : E} {r : 实数} (hr : 0 < r)
  证明: (isPathConnected_ball hr).isConnected

Depends on / 依赖: isConnected, isPathConnected_ball
-/
theorem isConnected_ball {x : E} {r : Real} (hr : 0 < r) :
    IsConnected (ball x r) :=
  (isPathConnected_ball hr).isConnected

/--
theorem `isConnected_eball` / 定理 `isConnected_eball`

English:
theorem isConnected_eball
  given: {x : E} {r : Real>=0∞} (hr : 0 < r)
  proof: (isPathConnected_eball hr).isConnected

中文:
定理 isConnected_eball
  条件: {x : E} {r : 实数>=0∞} (hr : 0 < r)
  证明: (isPathConnected_eball hr).isConnected

Depends on / 依赖: isConnected, isPathConnected_eball
-/
theorem isConnected_eball {x : E} {r : Real>=0∞} (hr : 0 < r) :
    IsConnected (eball x r) :=
  (isPathConnected_eball hr).isConnected

/--
theorem `isConnected_closedBall` / 定理 `isConnected_closedBall`

English:
theorem isConnected_closedBall
  given: {x : E} {r : Real} (hr : 0 <= r)
  statement: IsConnected (closedBall x r)
  proof: ⟨⟨x, by simpa⟩, isPreconnected_closedBall⟩

中文:
定理 isConnected_closedBall
  条件: {x : E} {r : 实数} (hr : 0 <= r)
  结论: 是连通 (closedBall x r)
  证明: ⟨⟨x, by simpa⟩, isPreconnected_closedBall⟩

Depends on / 依赖: isPreconnected_closedBall
-/
theorem isConnected_closedBall {x : E} {r : Real} (hr : 0 <= r) : IsConnected (closedBall x r) :=
  ⟨⟨x, by simpa⟩, isPreconnected_closedBall⟩

/--
theorem `isConnected_closedEBall` / 定理 `isConnected_closedEBall`

English:
theorem isConnected_closedEBall
  given: {x : E} {r : Real>=0∞}
  statement: IsConnected (closedEBall x r)
  proof: ⟨⟨x, mem_closedEBall_self⟩, isPreconnected_closedEBall⟩

中文:
定理 isConnected_closedEBall
  条件: {x : E} {r : 实数>=0∞}
  结论: 是连通 (closedEBall x r)
  证明: ⟨⟨x, mem_closedEBall_self⟩, isPreconnected_closedEBall⟩

Depends on / 依赖: isPreconnected_closedEBall, mem_closedEBall_self
-/
theorem isConnected_closedEBall {x : E} {r : Real>=0∞} : IsConnected (closedEBall x r) :=
  ⟨⟨x, mem_closedEBall_self⟩, isPreconnected_closedEBall⟩

end Metric

end Ball

/--
theorem `isPathConnected_sphere` / 定理 `isPathConnected_sphere`

English:
theorem isPathConnected_sphere
  given: (h : 1 < Module.rank Real E) (x : E) {r : Real} (hr : 0 <= r)
  proof: by
  /- when `r > 0`, we write the sphere as the image of `{0}ᶜ` under the map
  `y ↦ x + (r * ‖y‖⁻¹) • y`. Since the image under a continuous map of a path connected set
  is path connected, this concludes the proof. -/
  rcases hr.eq_or_lt with rfl | rpos
  · simpa using isPathConnected_singleton 

中文:
定理 isPathConnected_sphere
  条件: (h : 1 < 模.rank 实数 E) (x : E) {r : 实数} (hr : 0 <= r)
  证明: by
  /- when `r > 0`, we write the sphere as the image of `{0}ᶜ` under the map
  `y ↦ x + (r * ‖y‖⁻¹) • y`. Since the image under a continuous map of a path connected set
  is path connected, this concludes the proof. -/
  rcases hr.eq_or_lt with rfl | rpos
  · simpa using isPathConnected_singleton 
-/
theorem isPathConnected_sphere (h : 1 < Module.rank Real E) (x : E) {r : Real} (hr : 0 <= r) :
    IsPathConnected (sphere x r) := by
  /- when `r > 0`, we write the sphere as the image of `{0}ᶜ` under the map
  `y ↦ x + (r * ‖y‖⁻¹) • y`. Since the image under a continuous map of a path connected set
  is path connected, this concludes the proof. -/
  rcases hr.eq_or_lt with rfl | rpos
  · simpa using isPathConnected_singleton x
  let f : E -> E := fun y => x + (r * ‖y‖⁻¹) • y
  have A : ContinuousOn f {0}ᶜ := by
    intro y hy
    apply (continuousAt_const.add _).continuousWithinAt
    apply (continuousAt_const.mul (ContinuousAt.inv₀ continuousAt_id.norm ?_)).smul continuousAt_id
    simpa using hy
  have B : IsPathConnected ({0}ᶜ : Set E) := isPathConnected_compl_singleton_of_one_lt_rank h 0
  have C : IsPathConnected (f '' {0}ᶜ) := B.image' A
  have : f '' {0}ᶜ = sphere x r := by
    apply Subset.antisymm
    · rintro - ⟨y, hy, rfl⟩
      have : ‖y‖ != 0 := by simpa using hy
      simp [f, norm_smul, abs_of_nonneg hr, mul_assoc, inv_mul_cancel₀ this]
    · intro y hy
      refine ⟨y - x, ?_, ?_⟩
      · intro H
        simp only [mem_singleton_iff, sub_eq_zero] at H
        simp only [H, mem_sphere_iff_norm, sub_self, norm_zero] at hy
        exact rpos.ne hy
      · simp [f, mem_sphere_iff_norm.1 hy, mul_inv_cancel₀ rpos.ne']
  rwa [this] at C

/--
theorem `isConnected_sphere` / 定理 `isConnected_sphere`

English:
theorem isConnected_sphere
  given: (h : 1 < Module.rank Real E) (x : E) {r : Real} (hr : 0 <= r)
  proof: (isPathConnected_sphere h x hr).isConnected

中文:
定理 isConnected_sphere
  条件: (h : 1 < 模.rank 实数 E) (x : E) {r : 实数} (hr : 0 <= r)
  证明: (isPathConnected_sphere h x hr).isConnected

Depends on / 依赖: isConnected, isPathConnected_sphere
-/
theorem isConnected_sphere (h : 1 < Module.rank Real E) (x : E) {r : Real} (hr : 0 <= r) :
    IsConnected (sphere x r) :=
  (isPathConnected_sphere h x hr).isConnected

/--
theorem `isPreconnected_sphere` / 定理 `isPreconnected_sphere`

English:
theorem isPreconnected_sphere
  given: (h : 1 < Module.rank Real E) (x : E) (r : Real)
  proof: by
  rcases le_or_gt 0 r with hr | hr
  · exact (isConnected_sphere h x hr).isPreconnected
  · simpa [hr] using isPreconnected_empty

中文:
定理 isPreconnected_sphere
  条件: (h : 1 < 模.rank 实数 E) (x : E) (r : 实数)
  证明: by
  rcases le_or_gt 0 r with hr | hr
  · exact (isConnected_sphere h x hr).isPreconnected
  · simpa [hr] using isPreconnected_empty

Depends on / 依赖: isConnected_sphere, isPreconnected, isPreconnected_empty, le_or_gt
-/
theorem isPreconnected_sphere (h : 1 < Module.rank Real E) (x : E) (r : Real) :
    IsPreconnected (sphere x r) := by
  rcases le_or_gt 0 r with hr | hr
  · exact (isConnected_sphere h x hr).isPreconnected
  · simpa [hr] using isPreconnected_empty

end NormedSpace

section

variable {F : Type*} [AddCommGroup F] [Module Real F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul Real F]

/--
theorem `isPathConnected_compl_of_one_lt_codim` / 定理 `isPathConnected_compl_of_one_lt_codim`

English:
theorem isPathConnected_compl_of_one_lt_codim
  statement: {E : Submodule Real F}
  proof: by
  rcases E.exists_isCompl with ⟨E', hE'⟩
  refine isPathConnected_compl_of_isPathConnected_compl_zero hE'.symm
    (isPathConnected_compl_singleton_of_one_lt_rank ?_ 0)
  rwa [← (E.quotientEquivOfIsCompl E' hE').rank_eq]

中文:
定理 isPathConnected_compl_of_one_lt_codim
  结论: {E : 子模 实数 F}
  证明: by
  rcases E.exists_isCompl with ⟨E', hE'⟩
  refine isPathConnected_compl_of_isPathConnected_compl_zero hE'.symm
    (isPathConnected_compl_singleton_of_one_lt_rank ?_ 0)
  rwa [← (E.quotientEquivOfIsCompl E' hE').rank_eq]

Depends on / 依赖: E.exists_isCompl, E.quotientEquivOfIsCompl, exists_isCompl, isPathConnected_compl_of_isPathConnected_compl_zero, isPathConnected_compl_singleton_of_one_lt_rank, quotientEquivOfIsCompl, rank_eq
-/
theorem isPathConnected_compl_of_one_lt_codim {E : Submodule Real F}
    (hcodim : 1 < Module.rank Real (F ⧸ E)) : IsPathConnected (Eᶜ : Set F) := by
  rcases E.exists_isCompl with ⟨E', hE'⟩
  refine isPathConnected_compl_of_isPathConnected_compl_zero hE'.symm
    (isPathConnected_compl_singleton_of_one_lt_rank ?_ 0)
  rwa [← (E.quotientEquivOfIsCompl E' hE').rank_eq]

/--
theorem `isConnected_compl_of_one_lt_codim` / 定理 `isConnected_compl_of_one_lt_codim`

English:
theorem isConnected_compl_of_one_lt_codim
  given: {E : Submodule Real F} (hcodim : 1 < Module.rank Real (F ⧸ E))
  proof: (isPathConnected_compl_of_one_lt_codim hcodim).isConnected

中文:
定理 isConnected_compl_of_one_lt_codim
  条件: {E : 子模 实数 F} (hcodim : 1 < 模.rank 实数 (F ⧸ E))
  证明: (isPathConnected_compl_of_one_lt_codim hcodim).isConnected

Depends on / 依赖: hcodim, isConnected, isPathConnected_compl_of_one_lt_codim
-/
theorem isConnected_compl_of_one_lt_codim {E : Submodule Real F} (hcodim : 1 < Module.rank Real (F ⧸ E)) :
    IsConnected (Eᶜ : Set F) :=
  (isPathConnected_compl_of_one_lt_codim hcodim).isConnected

/--
theorem `Submodule.connectedComponentIn_eq_self_of_one_lt_codim` / 定理 `Submodule.connectedComponentIn_eq_self_of_one_lt_codim`

English:
theorem Submodule.connectedComponentIn_eq_self_of_one_lt_codim
  statement: (E : Submodule Real F)
  proof: (isConnected_compl_of_one_lt_codim hcodim).2.connectedComponentIn hx

中文:
定理 子模.connectedComponentIn_eq_self_of_one_lt_codim
  结论: (E : 子模 实数 F)
  证明: (isConnected_compl_of_one_lt_codim hcodim).2.connectedComponentIn hx

Depends on / 依赖: connectedComponentIn, hcodim, isConnected_compl_of_one_lt_codim
-/
theorem Submodule.connectedComponentIn_eq_self_of_one_lt_codim (E : Submodule Real F)
    (hcodim : 1 < Module.rank Real (F ⧸ E)) {x : F} (hx : x ∉ E) :
    connectedComponentIn ((E : Set F)ᶜ) x = (E : Set F)ᶜ :=
  (isConnected_compl_of_one_lt_codim hcodim).2.connectedComponentIn hx

end
