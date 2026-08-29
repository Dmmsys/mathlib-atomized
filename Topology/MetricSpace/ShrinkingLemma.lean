/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
public import Mathlib.Topology.ShrinkingLemma

/-!
# Shrinking lemma in a proper metric space

In this file we prove a few versions of the shrinking lemma for coverings by balls in a proper
(pseudo) metric space.

## Tags

shrinking lemma, metric space
-/

public section


universe u v

open Set Metric

open Topology

variable {α : Type u} {ι : Type v} [MetricSpace α] [ProperSpace α] {c : ι -> α}
variable {s : Set α}

/--
theorem `exists_subset_iUnion_ball_radius_lt` / 定理 `exists_subset_iUnion_ball_radius_lt`

English:
theorem exists_subset_iUnion_ball_radius_lt
  statement: {r : ι -> Real} (hs : IsClosed s)
  proof: by
  rcases exists_subset_iUnion_closed_subset hs (fun i => @isOpen_ball _ _ (c i) (r i)) uf us with
    ⟨v, hsv, hvc, hcv⟩
  have := fun i => exists_lt_subset_ball (hvc i) (hcv i)
  choose r' hlt hsub using this
exact ⟨r', hsv.trans iUnion_mono hsub, hlt⟩

中文:
定理 存在_subset_iUnion_ball_radius_lt
  结论: {r : ι -> 实数} (hs : 是闭集 s)
  证明: by
  rcases exists_subset_iUnion_closed_subset hs (fun i => @isOpen_ball _ _ (c i) (r i)) uf us with
    ⟨v, hsv, hvc, hcv⟩
  have := fun i => exists_lt_subset_ball (hvc i) (hcv i)
  choose r' hlt hsub using this
exact ⟨r', hsv.trans iUnion_mono hsub, hlt⟩

Depends on / 依赖: exists_lt_subset_ball, exists_subset_iUnion_closed_subset, hsv.trans, iUnion_mono, isOpen_ball
-/
theorem exists_subset_iUnion_ball_radius_lt {r : ι -> Real} (hs : IsClosed s)
    (uf : forall x in s, { i | x in ball (c i) (r i) }.Finite) (us : s subseteq ⋃ i, ball (c i) (r i)) :
    exists r' : ι -> Real, (s subseteq ⋃ i, ball (c i) (r' i)) ∧ forall i, r' i < r i := by
  rcases exists_subset_iUnion_closed_subset hs (fun i => @isOpen_ball _ _ (c i) (r i)) uf us with
    ⟨v, hsv, hvc, hcv⟩
  have := fun i => exists_lt_subset_ball (hvc i) (hcv i)
  choose r' hlt hsub using this
exact ⟨r', hsv.trans iUnion_mono hsub, hlt⟩

/--
theorem `exists_iUnion_ball_eq_radius_lt` / 定理 `exists_iUnion_ball_eq_radius_lt`

English:
theorem exists_iUnion_ball_eq_radius_lt
  statement: {r : ι -> Real} (uf : forall x, { i | x in ball (c i) (r i) }.Finite)
  proof: let ⟨r', hU, hv⟩ := exists_subset_iUnion_ball_radius_lt isClosed_univ (fun x _ => uf x) uU.ge
  ⟨r', univ_subset_iff.1 hU, hv⟩

中文:
定理 存在_iUnion_ball_eq_radius_lt
  结论: {r : ι -> 实数} (uf : 对任意 x, { i | x in ball (c i) (r i) }.有限)
  证明: let ⟨r', hU, hv⟩ := exists_subset_iUnion_ball_radius_lt isClosed_univ (fun x _ => uf x) uU.ge
  ⟨r', univ_subset_iff.1 hU, hv⟩

Depends on / 依赖: exists_subset_iUnion_ball_radius_lt, isClosed_univ, uU.ge, univ_subset_iff
-/
theorem exists_iUnion_ball_eq_radius_lt {r : ι -> Real} (uf : forall x, { i | x in ball (c i) (r i) }.Finite)
    (uU : ⋃ i, ball (c i) (r i) = univ) :
    exists r' : ι -> Real, ⋃ i, ball (c i) (r' i) = univ ∧ forall i, r' i < r i :=
  let ⟨r', hU, hv⟩ := exists_subset_iUnion_ball_radius_lt isClosed_univ (fun x _ => uf x) uU.ge
  ⟨r', univ_subset_iff.1 hU, hv⟩

/--
theorem `exists_subset_iUnion_ball_radius_pos_lt` / 定理 `exists_subset_iUnion_ball_radius_pos_lt`

English:
theorem exists_subset_iUnion_ball_radius_pos_lt
  statement: {r : ι -> Real} (hr : forall i, 0 < r i) (hs : IsClosed s)
  proof: by
  rcases exists_subset_iUnion_closed_subset hs (fun i => @isOpen_ball _ _ (c i) (r i)) uf us with
    ⟨v, hsv, hvc, hcv⟩
  have := fun i => exists_pos_lt_subset_ball (hr i) (hvc i) (hcv i)
  choose r' hlt hsub using this
exact ⟨r', hsv.trans iUnion_mono hsub, hlt⟩

中文:
定理 存在_subset_iUnion_ball_radius_pos_lt
  结论: {r : ι -> 实数} (hr : 对任意 i, 0 < r i) (hs : 是闭集 s)
  证明: by
  rcases exists_subset_iUnion_closed_subset hs (fun i => @isOpen_ball _ _ (c i) (r i)) uf us with
    ⟨v, hsv, hvc, hcv⟩
  have := fun i => exists_pos_lt_subset_ball (hr i) (hvc i) (hcv i)
  choose r' hlt hsub using this
exact ⟨r', hsv.trans iUnion_mono hsub, hlt⟩

Depends on / 依赖: exists_pos_lt_subset_ball, exists_subset_iUnion_closed_subset, hsv.trans, iUnion_mono, isOpen_ball
-/
theorem exists_subset_iUnion_ball_radius_pos_lt {r : ι -> Real} (hr : forall i, 0 < r i) (hs : IsClosed s)
    (uf : forall x in s, { i | x in ball (c i) (r i) }.Finite) (us : s subseteq ⋃ i, ball (c i) (r i)) :
    exists r' : ι -> Real, (s subseteq ⋃ i, ball (c i) (r' i)) ∧ forall i, r' i in Ioo 0 (r i) := by
  rcases exists_subset_iUnion_closed_subset hs (fun i => @isOpen_ball _ _ (c i) (r i)) uf us with
    ⟨v, hsv, hvc, hcv⟩
  have := fun i => exists_pos_lt_subset_ball (hr i) (hvc i) (hcv i)
  choose r' hlt hsub using this
exact ⟨r', hsv.trans iUnion_mono hsub, hlt⟩

/--
theorem `exists_iUnion_ball_eq_radius_pos_lt` / 定理 `exists_iUnion_ball_eq_radius_pos_lt`

English:
theorem exists_iUnion_ball_eq_radius_pos_lt
  statement: {r : ι -> Real} (hr : forall i, 0 < r i)
  proof: let ⟨r', hU, hv⟩ :=
    exists_subset_iUnion_ball_radius_pos_lt hr isClosed_univ (fun x _ => uf x) uU.ge
  ⟨r', univ_subset_iff.1 hU, hv⟩

中文:
定理 存在_iUnion_ball_eq_radius_pos_lt
  结论: {r : ι -> 实数} (hr : 对任意 i, 0 < r i)
  证明: let ⟨r', hU, hv⟩ :=
    exists_subset_iUnion_ball_radius_pos_lt hr isClosed_univ (fun x _ => uf x) uU.ge
  ⟨r', univ_subset_iff.1 hU, hv⟩

Depends on / 依赖: exists_subset_iUnion_ball_radius_pos_lt, isClosed_univ, uU.ge, univ_subset_iff
-/
theorem exists_iUnion_ball_eq_radius_pos_lt {r : ι -> Real} (hr : forall i, 0 < r i)
    (uf : forall x, { i | x in ball (c i) (r i) }.Finite) (uU : ⋃ i, ball (c i) (r i) = univ) :
    exists r' : ι -> Real, ⋃ i, ball (c i) (r' i) = univ ∧ forall i, r' i in Ioo 0 (r i) :=
  let ⟨r', hU, hv⟩ :=
    exists_subset_iUnion_ball_radius_pos_lt hr isClosed_univ (fun x _ => uf x) uU.ge
  ⟨r', univ_subset_iff.1 hU, hv⟩

/--
theorem `exists_locallyFinite_subset_iUnion_ball_radius_lt` / 定理 `exists_locallyFinite_subset_iUnion_ball_radius_lt`

English:
theorem exists_locallyFinite_subset_iUnion_ball_radius_lt
  statement: (hs : IsClosed s) {R : α -> Real}
  proof: by
  have : forall x in s, (𝓝 x).HasBasis (fun r : Real => 0 < r ∧ r < R x) fun r => ball x r := fun x hx =>
    nhds_basis_uniformity (uniformity_basis_dist_lt (hR x hx))
  rcases refinement_of_locallyCompact_sigmaCompact_of_nhds_basis_set hs this with
    ⟨ι, c, r', hr', hsub', hfin⟩
  rcases exists_subset_iUnion_ball_radius_pos_lt (fun i => (hr' i).2.1) hs
      (fun x _ => hfin.point_finite x) hsub' with
    ⟨r, hsub, hlt⟩
  exact ⟨ι, c, r, r', fun i => ⟨(hr' i).1, (hlt i).1, (hlt i).2, (hr' i).2.2⟩, hfin, hsub⟩

中文:
定理 存在_locallyFinite_subset_iUnion_ball_radius_lt
  结论: (hs : 是闭集 s) {R : α -> 实数}
  证明: by
  have : forall x in s, (𝓝 x).HasBasis (fun r : Real => 0 < r ∧ r < R x) fun r => ball x r := fun x hx =>
    nhds_basis_uniformity (uniformity_basis_dist_lt (hR x hx))
  rcases refinement_of_locallyCompact_sigmaCompact_of_nhds_basis_set hs this with
    ⟨ι, c, r', hr', hsub', hfin⟩
  rcases exists_subset_iUnion_ball_radius_pos_lt (fun i => (hr' i).2.1) hs
      (fun x _ => hfin.point_finite x) hsub' with
    ⟨r, hsub, hlt⟩
  exact ⟨ι, c, r, r', fun i => ⟨(hr' i).1, (hlt i).1, (hlt i).2, (hr' i).2.2⟩, hfin, hsub⟩

Depends on / 依赖: HasBasis, exists_subset_iUnion_ball_radius_pos_lt, hfin.point_finite, nhds_basis_uniformity, point_finite, refinement_of_locallyCompact_sigmaCompact_of_nhds_basis_set, uniformity_basis_dist_lt
-/
theorem exists_locallyFinite_subset_iUnion_ball_radius_lt (hs : IsClosed s) {R : α -> Real}
    (hR : forall x in s, 0 < R x) :
    exists (ι : Type u) (c : ι -> α) (r r' : ι -> Real),
      (forall i, c i in s ∧ 0 < r i ∧ r i < r' i ∧ r' i < R (c i)) ∧
        (LocallyFinite fun i => ball (c i) (r' i)) ∧ s subseteq ⋃ i, ball (c i) (r i) := by
  have : forall x in s, (𝓝 x).HasBasis (fun r : Real => 0 < r ∧ r < R x) fun r => ball x r := fun x hx =>
    nhds_basis_uniformity (uniformity_basis_dist_lt (hR x hx))
  rcases refinement_of_locallyCompact_sigmaCompact_of_nhds_basis_set hs this with
    ⟨ι, c, r', hr', hsub', hfin⟩
  rcases exists_subset_iUnion_ball_radius_pos_lt (fun i => (hr' i).2.1) hs
      (fun x _ => hfin.point_finite x) hsub' with
    ⟨r, hsub, hlt⟩
  exact ⟨ι, c, r, r', fun i => ⟨(hr' i).1, (hlt i).1, (hlt i).2, (hr' i).2.2⟩, hfin, hsub⟩

/--
theorem `exists_locallyFinite_iUnion_eq_ball_radius_lt` / 定理 `exists_locallyFinite_iUnion_eq_ball_radius_lt`

English:
theorem exists_locallyFinite_iUnion_eq_ball_radius_lt
  given: {R : α -> Real} (hR : forall x, 0 < R x)
  proof: let ⟨ι, c, r, r', hlt, hfin, hsub⟩ :=
    exists_locallyFinite_subset_iUnion_ball_radius_lt isClosed_univ fun x _ => hR x
  ⟨ι, c, r, r', fun i => (hlt i).2, hfin, univ_subset_iff.1 hsub⟩

中文:
定理 存在_locallyFinite_iUnion_eq_ball_radius_lt
  条件: {R : α -> 实数} (hR : 对任意 x, 0 < R x)
  证明: let ⟨ι, c, r, r', hlt, hfin, hsub⟩ :=
    exists_locallyFinite_subset_iUnion_ball_radius_lt isClosed_univ fun x _ => hR x
  ⟨ι, c, r, r', fun i => (hlt i).2, hfin, univ_subset_iff.1 hsub⟩

Depends on / 依赖: exists_locallyFinite_subset_iUnion_ball_radius_lt, isClosed_univ, univ_subset_iff
-/
theorem exists_locallyFinite_iUnion_eq_ball_radius_lt {R : α -> Real} (hR : forall x, 0 < R x) :
    exists (ι : Type u) (c : ι -> α) (r r' : ι -> Real),
      (forall i, 0 < r i ∧ r i < r' i ∧ r' i < R (c i)) ∧
        (LocallyFinite fun i => ball (c i) (r' i)) ∧ ⋃ i, ball (c i) (r i) = univ :=
  let ⟨ι, c, r, r', hlt, hfin, hsub⟩ :=
    exists_locallyFinite_subset_iUnion_ball_radius_lt isClosed_univ fun x _ => hR x
  ⟨ι, c, r, r', fun i => (hlt i).2, hfin, univ_subset_iff.1 hsub⟩
