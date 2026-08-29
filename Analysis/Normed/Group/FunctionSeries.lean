/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Continuity of series of functions

We show that series of functions are continuous when each individual function in the series is and
additionally suitable uniform summable bounds are satisfied, in `continuous_tsum`.

For smoothness of series of functions, see the file `Mathlib/Analysis/Calculus/SmoothSeries.lean`.

TODO: update this to use `SummableUniformlyOn`.

-/

public section

open Set Metric TopologicalSpace Function Filter

open scoped Topology NNReal

variable {α β F : Type*} [NormedAddCommGroup F] [CompleteSpace F] {u : α -> Real}

/--
theorem `tendstoUniformlyOn_tsum` / 定理 `tendstoUniformlyOn_tsum`

English:
theorem tendstoUniformlyOn_tsum
  statement: {f : α -> β -> F} (hu : Summable u) {s : Set β}
  proof: by
  refine tendstoUniformlyOn_iff.2 fun ε εpos => ?_
  filter_upwards [(tendsto_order.1 (tendsto_tsum_compl_atTop_zero u)).2 _ εpos] with t ht x hx
  have A : Summable fun n => ‖f n x‖ :=
    .of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => hfu n x hx) hu
  rw [dist_eq_norm]; rw [← A.of_norm.sum

中文:
定理 tendstoUniformlyOn_tsum
  结论: {f : α -> β -> F} (hu : Summable u) {s : 集合 β}
  证明: by
  refine tendstoUniformlyOn_iff.2 fun ε εpos => ?_
  filter_upwards [(tendsto_order.1 (tendsto_tsum_compl_atTop_zero u)).2 _ εpos] with t ht x hx
  have A : Summable fun n => ‖f n x‖ :=
    .of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => hfu n x hx) hu
  rw [dist_eq_norm]; rw [← A.of_norm.sum

Depends on / 依赖: A.of_norm.sum_add_tsum_subtype_compl, A.subtype, Summable, add_sub_cancel_left, dist_eq_norm, filter_upwards, hu.subtype, lt_of_le_of_lt, norm_nonneg, norm_tsum_le_tsum_norm, of_nonneg_of_le, of_norm, subtype, sum_add_tsum_subtype_compl, tendstoUniformlyOn_iff, tendsto_order, tendsto_tsum_compl_atTop_zero, tsum_le_tsum
-/
theorem tendstoUniformlyOn_tsum {f : α -> β -> F} (hu : Summable u) {s : Set β}
    (hfu : forall n x, x in s -> ‖f n x‖ <= u n) :
    TendstoUniformlyOn (fun t : Finset α => fun x => ∑ n in t, f n x) (fun x => ∑' n, f n x) atTop
      s := by
  refine tendstoUniformlyOn_iff.2 fun ε εpos => ?_
  filter_upwards [(tendsto_order.1 (tendsto_tsum_compl_atTop_zero u)).2 _ εpos] with t ht x hx
  have A : Summable fun n => ‖f n x‖ :=
    .of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => hfu n x hx) hu
  rw [dist_eq_norm]; rw [← A.of_norm.sum_add_tsum_subtype_compl t]; rw [add_sub_cancel_left]
  apply lt_of_le_of_lt _ ht
  apply (norm_tsum_le_tsum_norm (A.subtype _)).trans
  exact (A.subtype _).tsum_le_tsum (fun n => hfu _ _ hx) (hu.subtype _)

/--
theorem `tendstoUniformlyOn_tsum_nat` / 定理 `tendstoUniformlyOn_tsum_nat`

English:
theorem tendstoUniformlyOn_tsum_nat
  statement: {f : Nat -> β -> F} {u : Nat -> Real} (hu : Summable u) {s : Set β}
  proof: fun v hv => tendsto_finset_range.eventually (tendstoUniformlyOn_tsum hu hfu v hv)

中文:
定理 tendstoUniformlyOn_tsum_nat
  结论: {f : 自然数 -> β -> F} {u : 自然数 -> 实数} (hu : Summable u) {s : 集合 β}
  证明: fun v hv => tendsto_finset_range.eventually (tendstoUniformlyOn_tsum hu hfu v hv)

Depends on / 依赖: eventually, tendstoUniformlyOn_tsum, tendsto_finset_range, tendsto_finset_range.eventually
-/
theorem tendstoUniformlyOn_tsum_nat {f : Nat -> β -> F} {u : Nat -> Real} (hu : Summable u) {s : Set β}
    (hfu : forall n x, x in s -> ‖f n x‖ <= u n) :
    TendstoUniformlyOn (fun N x => ∑ n in Finset.range N, f n x) (fun x => ∑' n, f n x) atTop
      s :=
  fun v hv => tendsto_finset_range.eventually (tendstoUniformlyOn_tsum hu hfu v hv)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `tendstoUniformlyOn_tsum_of_cofinite_eventually` / 定理 `tendstoUniformlyOn_tsum_of_cofinite_eventually`

English:
theorem tendstoUniformlyOn_tsum_of_cofinite_eventually
  statement: {ι : Type*} {f : ι -> β -> F} {u : ι -> Real}
  proof: by
  classical
  refine tendstoUniformlyOn_iff.2 fun ε εpos => ?_
  have := (tendsto_order.1 (tendsto_tsum_compl_atTop_zero u)).2 _ εpos
  simp only [eventually_atTop] at *
  obtain ⟨t, ht⟩ := this
  rw [eventually_iff_exists_mem] at hfu
  obtain ⟨N, hN, HN⟩ := hfu
  refine ⟨hN.toFinset union t, fun

中文:
定理 tendstoUniformlyOn_tsum_of_cofinite_eventually
  结论: {ι : 类型} {f : ι -> β -> F} {u : ι -> 实数}
  证明: by
  classical
  refine tendstoUniformlyOn_iff.2 fun ε εpos => ?_
  have := (tendsto_order.1 (tendsto_tsum_compl_atTop_zero u)).2 _ εpos
  simp only [eventually_atTop] at *
  obtain ⟨t, ht⟩ := this
  rw [eventually_iff_exists_mem] at hfu
  obtain ⟨N, hN, HN⟩ := hfu
  refine ⟨hN.toFinset union t, fun

Depends on / 依赖: Summable, Summable.add_compl, Summable.of_finite, Summable.of_nonneg_of_le, add_compl, classical, comp_apply, eventually_atTop, eventually_iff_exists_mem, hN.toFinset, hu.subtype, norm_nonneg, of_finite, of_nonneg_of_le, subtype, tendstoUniformlyOn_iff, tendsto_order, tendsto_tsum_compl_atTop_zero, toFinset
-/
theorem tendstoUniformlyOn_tsum_of_cofinite_eventually {ι : Type*} {f : ι -> β -> F} {u : ι -> Real}
    (hu : Summable u) {s : Set β} (hfu : forallᶠ n in cofinite, forall x in s, ‖f n x‖ <= u n) :
    TendstoUniformlyOn (fun t x => ∑ n in t, f n x) (fun x => ∑' n, f n x) atTop s := by
  classical
  refine tendstoUniformlyOn_iff.2 fun ε εpos => ?_
  have := (tendsto_order.1 (tendsto_tsum_compl_atTop_zero u)).2 _ εpos
  simp only [eventually_atTop] at *
  obtain ⟨t, ht⟩ := this
  rw [eventually_iff_exists_mem] at hfu
  obtain ⟨N, hN, HN⟩ := hfu
  refine ⟨hN.toFinset union t, fun n hn x hx => ?_⟩
  have A : Summable fun n => ‖f n x‖ := by
    apply Summable.add_compl (s := hN.toFinset) Summable.of_finite
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (hu.subtype _)
    simp only [comp_apply, Subtype.forall, Set.mem_compl_iff, Finset.mem_coe]
    aesop
  rw [dist_eq_norm]; rw [← A.of_norm.sum_add_tsum_subtype_compl n]; rw [add_sub_cancel_left]
  apply lt_of_le_of_lt _ (ht n (Finset.union_subset_right hn))
  apply (norm_tsum_le_tsum_norm (A.subtype _)).trans
  apply (A.subtype _).tsum_le_tsum _ (hu.subtype _)
  simp only [comp_apply, Subtype.forall]
  apply fun i hi => HN i ?_ x hx
  have : i ∉ hN.toFinset := fun hg => hi (Finset.union_subset_left hn hg)
  simp_all

/--
theorem `tendstoUniformlyOn_tsum_nat_eventually` / 定理 `tendstoUniformlyOn_tsum_nat_eventually`

English:
theorem tendstoUniformlyOn_tsum_nat_eventually
  statement: {α F : Type*} [NormedAddCommGroup F]
  proof: fun v hv => tendsto_finset_range.eventually
    tendstoUniformlyOn_tsum_of_cofinite_eventually hu (Nat.cofinite_eq_atTop ▸ hfu) v hv

中文:
定理 tendstoUniformlyOn_tsum_nat_eventually
  结论: {α F : 类型} [赋范交换加群 F]
  证明: fun v hv => tendsto_finset_range.eventually
    tendstoUniformlyOn_tsum_of_cofinite_eventually hu (Nat.cofinite_eq_atTop ▸ hfu) v hv

Depends on / 依赖: Nat.cofinite_eq_atTop, cofinite_eq_atTop, eventually, tendstoUniformlyOn_tsum_of_cofinite_eventually, tendsto_finset_range, tendsto_finset_range.eventually
-/
theorem tendstoUniformlyOn_tsum_nat_eventually {α F : Type*} [NormedAddCommGroup F]
    [CompleteSpace F] {f : Nat -> α -> F} {u : Nat -> Real} (hu : Summable u) {s : Set α}
    (hfu : forallᶠ n in atTop, forall x in s, ‖f n x‖ <= u n) :
    TendstoUniformlyOn (fun N x => ∑ n in Finset.range N, f n x)
       (fun x => ∑' n, f n x) atTop s :=
fun v hv => tendsto_finset_range.eventually
    tendstoUniformlyOn_tsum_of_cofinite_eventually hu (Nat.cofinite_eq_atTop ▸ hfu) v hv

/--
theorem `tendstoUniformly_tsum` / 定理 `tendstoUniformly_tsum`

English:
theorem tendstoUniformly_tsum
  given: {f : α -> β -> F} (hu : Summable u) (hfu : forall n x, ‖f n x‖ <= u n)
  proof: by
  rw [← tendstoUniformlyOn_univ]; exact tendstoUniformlyOn_tsum hu fun n x _ => hfu n x

中文:
定理 tendstoUniformly_tsum
  条件: {f : α -> β -> F} (hu : Summable u) (hfu : 对任意 n x, ‖f n x‖ <= u n)
  证明: by
  rw [← tendstoUniformlyOn_univ]; exact tendstoUniformlyOn_tsum hu fun n x _ => hfu n x

Depends on / 依赖: tendstoUniformlyOn_tsum, tendstoUniformlyOn_univ
-/
theorem tendstoUniformly_tsum {f : α -> β -> F} (hu : Summable u) (hfu : forall n x, ‖f n x‖ <= u n) :
    TendstoUniformly (fun t : Finset α => fun x => ∑ n in t, f n x)
      (fun x => ∑' n, f n x) atTop := by
  rw [← tendstoUniformlyOn_univ]; exact tendstoUniformlyOn_tsum hu fun n x _ => hfu n x

/--
theorem `tendstoUniformly_tsum_nat` / 定理 `tendstoUniformly_tsum_nat`

English:
theorem tendstoUniformly_tsum_nat
  statement: {f : Nat -> β -> F} {u : Nat -> Real} (hu : Summable u)
  proof: fun v hv => tendsto_finset_range.eventually (tendstoUniformly_tsum hu hfu v hv)

中文:
定理 tendstoUniformly_tsum_nat
  结论: {f : 自然数 -> β -> F} {u : 自然数 -> 实数} (hu : Summable u)
  证明: fun v hv => tendsto_finset_range.eventually (tendstoUniformly_tsum hu hfu v hv)

Depends on / 依赖: eventually, tendstoUniformly_tsum, tendsto_finset_range, tendsto_finset_range.eventually
-/
theorem tendstoUniformly_tsum_nat {f : Nat -> β -> F} {u : Nat -> Real} (hu : Summable u)
    (hfu : forall n x, ‖f n x‖ <= u n) :
    TendstoUniformly (fun N x => ∑ n in Finset.range N, f n x) (fun x => ∑' n, f n x)
      atTop :=
  fun v hv => tendsto_finset_range.eventually (tendstoUniformly_tsum hu hfu v hv)

/--
theorem `tendstoUniformly_tsum_of_cofinite_eventually` / 定理 `tendstoUniformly_tsum_of_cofinite_eventually`

English:
theorem tendstoUniformly_tsum_of_cofinite_eventually
  statement: {ι : Type*} {f : ι -> β -> F} {u : ι -> Real}
  proof: by
  rw [← tendstoUniformlyOn_univ]
  apply tendstoUniformlyOn_tsum_of_cofinite_eventually hu
  simpa using hfu

中文:
定理 tendstoUniformly_tsum_of_cofinite_eventually
  结论: {ι : 类型} {f : ι -> β -> F} {u : ι -> 实数}
  证明: by
  rw [← tendstoUniformlyOn_univ]
  apply tendstoUniformlyOn_tsum_of_cofinite_eventually hu
  simpa using hfu

Depends on / 依赖: tendstoUniformlyOn_tsum_of_cofinite_eventually, tendstoUniformlyOn_univ
-/
theorem tendstoUniformly_tsum_of_cofinite_eventually {ι : Type*} {f : ι -> β -> F} {u : ι -> Real}
    (hu : Summable u) (hfu : forallᶠ (n : ι) in cofinite, forall x : β, ‖f n x‖ <= u n) :
    TendstoUniformly (fun t x => ∑ n in t, f n x) (fun x => ∑' n, f n x) atTop := by
  rw [← tendstoUniformlyOn_univ]
  apply tendstoUniformlyOn_tsum_of_cofinite_eventually hu
  simpa using hfu

/--
theorem `continuousOn_tsum` / 定理 `continuousOn_tsum`

English:
theorem continuousOn_tsum
  statement: [TopologicalSpace β] {f : α -> β -> F} {s : Set β}
  proof: by
  refine (tendstoUniformlyOn_tsum hu hfu).continuousOn (Frequently.of_forall ?_)
  intro t
  exact continuousOn_finsetSum _ fun i _ => hf i

中文:
定理 continuousOn_tsum
  结论: [拓扑空间 β] {f : α -> β -> F} {s : 集合 β}
  证明: by
  refine (tendstoUniformlyOn_tsum hu hfu).continuousOn (Frequently.of_forall ?_)
  intro t
  exact continuousOn_finsetSum _ fun i _ => hf i

Depends on / 依赖: Frequently, Frequently.of_forall, continuousOn, continuousOn_finsetSum, of_forall, tendstoUniformlyOn_tsum
-/
theorem continuousOn_tsum [TopologicalSpace β] {f : α -> β -> F} {s : Set β}
    (hf : forall i, ContinuousOn (f i) s) (hu : Summable u) (hfu : forall n x, x in s -> ‖f n x‖ <= u n) :
    ContinuousOn (fun x => ∑' n, f n x) s := by
  refine (tendstoUniformlyOn_tsum hu hfu).continuousOn (Frequently.of_forall ?_)
  intro t
  exact continuousOn_finsetSum _ fun i _ => hf i

/--
theorem `continuous_tsum` / 定理 `continuous_tsum`

English:
theorem continuous_tsum
  statement: [TopologicalSpace β] {f : α -> β -> F} (hf : forall i, Continuous (f i))
  proof: by
  simp_rw [← continuousOn_univ] at hf ⊢
  exact continuousOn_tsum hf hu fun n x _ => hfu n x

中文:
定理 continuous_tsum
  结论: [拓扑空间 β] {f : α -> β -> F} (hf : 对任意 i, 连续 (f i))
  证明: by
  simp_rw [← continuousOn_univ] at hf ⊢
  exact continuousOn_tsum hf hu fun n x _ => hfu n x

Depends on / 依赖: continuousOn_tsum, continuousOn_univ, simp_rw
-/
theorem continuous_tsum [TopologicalSpace β] {f : α -> β -> F} (hf : forall i, Continuous (f i))
    (hu : Summable u) (hfu : forall n x, ‖f n x‖ <= u n) : Continuous fun x => ∑' n, f n x := by
  simp_rw [← continuousOn_univ] at hf ⊢
  exact continuousOn_tsum hf hu fun n x _ => hfu n x
