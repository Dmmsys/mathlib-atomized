/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
module

public import Mathlib.Data.ENNReal.Lemmas
public import Mathlib.Topology.Bornology.Constructions
public import Mathlib.Topology.EMetricSpace.Pi
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Product of pseudometric spaces

This file constructs the infinity distance on finite products of pseudometric spaces.
-/

@[expose] public section

open Bornology Filter Metric Set
open scoped NNReal Topology

variable {α β : Type*} [PseudoMetricSpace α]

open Finset

variable {X : β -> Type*} [Fintype β] [forall b, PseudoMetricSpace (X b)]

/--
Instance `pseudoMetricSpacePi` / 实例 `pseudoMetricSpacePi`

English:
instance pseudoMetricSpacePi
  signature: : PseudoMetricSpace (forall b, X b)
  body: by
  /- we construct the instance from the pseudoemetric space instance to avoid checking again that
    the uniformity is the same as the product uniformity, but we register nevertheless a nice
    formula for the distance -/
  let i := PseudoEMetricSpace.toPseudoMetricSpaceOfDist
    (fun f g : forall b, X b => ((sup univ fun b => nndist (f b) (g b) : Real>=0) : Real))
    (fun f g => NNReal.zero_le_coe)
    (fun f g => by simp [edist_pi_def])
  refine i.replaceBornology fun s => ?_
  simp only [isBounded_iff_eventually, ← forall_isBounded_image_eval_iff,
    forall_mem_image, ← Filter.eventually_all, @dist_nndist (X _)]
  refine eventually_congr ((eventually_ge_atTop 0).mono fun C hC => ?_)
  lift C to Real>=0 using hC
refine ⟨fun H x hx y hy => NNReal.coe_le_coe.2 Finset.sup_le fun b _ => H b hx hy,
    fun H b x hx y hy => NNReal.coe_le_coe.2 ?_⟩
  exact Finset.sup_le_iff.1 (NNReal.coe_le_coe.1 <| H hx hy) b (Finset.mem_univ b)

中文:
实例 pseudoMetricSpacePi
  签名: : 伪度量空间 (对任意 b, X b)
  定义体: by
  /- we construct the instance from the pseudoemetric space instance to avoid checking again that
    the uniformity is the same as the product uniformity, but we register nevertheless a nice
    formula for the distance -/
  let i := PseudoEMetricSpace.toPseudoMetricSpaceOfDist
    (fun f g : forall b, X b => ((sup univ fun b => nndist (f b) (g b) : Real>=0) : Real))
    (fun f g => NNReal.zero_le_coe)
    (fun f g => by simp [edist_pi_def])
  refine i.replaceBornology fun s => ?_
  simp only [isBounded_iff_eventually, ← forall_isBounded_image_eval_iff,
    forall_mem_image, ← Filter.eventually_all, @dist_nndist (X _)]
  refine eventually_congr ((eventually_ge_atTop 0).mono fun C hC => ?_)
  lift C to Real>=0 using hC
refine ⟨fun H x hx y hy => NNReal.coe_le_coe.2 Finset.sup_le fun b _ => H b hx hy,
    fun H b x hx y hy => NNReal.coe_le_coe.2 ?_⟩
  exact Finset.sup_le_iff.1 (NNReal.coe_le_coe.1 <| H hx hy) b (Finset.mem_univ b)
-/
instance pseudoMetricSpacePi : PseudoMetricSpace (forall b, X b) := by
  /- we construct the instance from the pseudoemetric space instance to avoid checking again that
    the uniformity is the same as the product uniformity, but we register nevertheless a nice
    formula for the distance -/
  let i := PseudoEMetricSpace.toPseudoMetricSpaceOfDist
    (fun f g : forall b, X b => ((sup univ fun b => nndist (f b) (g b) : Real>=0) : Real))
    (fun f g => NNReal.zero_le_coe)
    (fun f g => by simp [edist_pi_def])
  refine i.replaceBornology fun s => ?_
  simp only [isBounded_iff_eventually, ← forall_isBounded_image_eval_iff,
    forall_mem_image, ← Filter.eventually_all, @dist_nndist (X _)]
  refine eventually_congr ((eventually_ge_atTop 0).mono fun C hC => ?_)
  lift C to Real>=0 using hC
refine ⟨fun H x hx y hy => NNReal.coe_le_coe.2 Finset.sup_le fun b _ => H b hx hy,
    fun H b x hx y hy => NNReal.coe_le_coe.2 ?_⟩
  exact Finset.sup_le_iff.1 (NNReal.coe_le_coe.1 <| H hx hy) b (Finset.mem_univ b)

/--
lemma `nndist_pi_def` / 引理 `nndist_pi_def`

English:
lemma nndist_pi_def
  given: (f g : forall b, X b)
  statement: nndist f g = sup univ fun b => nndist (f b) (g b)
  proof: rfl

中文:
引理 nndist_pi_def
  条件: (f g : 对任意 b, X b)
  结论: nndist f g = 上确界 univ fun b => nndist (f b) (g b)
  证明: rfl
-/
lemma nndist_pi_def (f g : forall b, X b) : nndist f g = sup univ fun b => nndist (f b) (g b) := rfl

/--
lemma `dist_pi_def` / 引理 `dist_pi_def`

English:
lemma dist_pi_def
  given: (f g : forall b, X b)
  statement: dist f g = (sup univ fun b => nndist (f b) (g b) : Real>=0)
  proof: rfl

中文:
引理 dist_pi_def
  条件: (f g : 对任意 b, X b)
  结论: dist f g = (上确界 univ fun b => nndist (f b) (g b) : 实数>=0)
  证明: rfl
-/
lemma dist_pi_def (f g : forall b, X b) : dist f g = (sup univ fun b => nndist (f b) (g b) : Real>=0) := rfl

/--
lemma `nndist_pi_le_iff` / 引理 `nndist_pi_le_iff`

English:
lemma nndist_pi_le_iff
  given: {f g : forall b, X b} {r : Real>=0}
  proof: by simp [nndist_pi_def]

中文:
引理 nndist_pi_le_iff
  条件: {f g : 对任意 b, X b} {r : 实数>=0}
  证明: by simp [nndist_pi_def]

Depends on / 依赖: nndist_pi_def
-/
lemma nndist_pi_le_iff {f g : forall b, X b} {r : Real>=0} :
    nndist f g <= r ↔ forall b, nndist (f b) (g b) <= r := by simp [nndist_pi_def]

/--
lemma `nndist_pi_lt_iff` / 引理 `nndist_pi_lt_iff`

English:
lemma nndist_pi_lt_iff
  given: {f g : forall b, X b} {r : Real>=0} (hr : 0 < r)
  proof: by
  simp [nndist_pi_def, Finset.sup_lt_iff hr]

中文:
引理 nndist_pi_lt_iff
  条件: {f g : 对任意 b, X b} {r : 实数>=0} (hr : 0 < r)
  证明: by
  simp [nndist_pi_def, Finset.sup_lt_iff hr]

Depends on / 依赖: Finset, Finset.sup_lt_iff, nndist_pi_def, sup_lt_iff
-/
lemma nndist_pi_lt_iff {f g : forall b, X b} {r : Real>=0} (hr : 0 < r) :
    nndist f g < r ↔ forall b, nndist (f b) (g b) < r := by
  simp [nndist_pi_def, Finset.sup_lt_iff hr]

/--
lemma `nndist_pi_eq_iff` / 引理 `nndist_pi_eq_iff`

English:
lemma nndist_pi_eq_iff
  given: {f g : forall b, X b} {r : Real>=0} (hr : 0 < r)
  proof: by
  rw [eq_iff_le_not_lt]; rw [nndist_pi_lt_iff hr]; rw [nndist_pi_le_iff]; rw [not_forall]; rw [and_comm]
  simp_rw [not_lt, and_congr_left_iff, le_antisymm_iff]
  intro h
  refine exists_congr fun b => ?_
  apply (and_iff_right <| h _).symm

中文:
引理 nndist_pi_eq_iff
  条件: {f g : 对任意 b, X b} {r : 实数>=0} (hr : 0 < r)
  证明: by
  rw [eq_iff_le_not_lt]; rw [nndist_pi_lt_iff hr]; rw [nndist_pi_le_iff]; rw [not_forall]; rw [and_comm]
  simp_rw [not_lt, and_congr_left_iff, le_antisymm_iff]
  intro h
  refine exists_congr fun b => ?_
  apply (and_iff_right <| h _).symm

Depends on / 依赖: and_comm, and_congr_left_iff, and_iff_right, eq_iff_le_not_lt, exists_congr, le_antisymm_iff, nndist_pi_le_iff, nndist_pi_lt_iff, not_forall, not_lt, simp_rw
-/
lemma nndist_pi_eq_iff {f g : forall b, X b} {r : Real>=0} (hr : 0 < r) :
    nndist f g = r ↔ (exists i, nndist (f i) (g i) = r) ∧ forall b, nndist (f b) (g b) <= r := by
  rw [eq_iff_le_not_lt]; rw [nndist_pi_lt_iff hr]; rw [nndist_pi_le_iff]; rw [not_forall]; rw [and_comm]
  simp_rw [not_lt, and_congr_left_iff, le_antisymm_iff]
  intro h
  refine exists_congr fun b => ?_
  apply (and_iff_right <| h _).symm

/--
lemma `dist_pi_lt_iff` / 引理 `dist_pi_lt_iff`

English:
lemma dist_pi_lt_iff
  given: {f g : forall b, X b} {r : Real} (hr : 0 < r)
  proof: by
  lift r to Real>=0 using hr.le
  exact nndist_pi_lt_iff hr

中文:
引理 dist_pi_lt_iff
  条件: {f g : 对任意 b, X b} {r : 实数} (hr : 0 < r)
  证明: by
  lift r to Real>=0 using hr.le
  exact nndist_pi_lt_iff hr

Depends on / 依赖: hr.le, nndist_pi_lt_iff
-/
lemma dist_pi_lt_iff {f g : forall b, X b} {r : Real} (hr : 0 < r) :
    dist f g < r ↔ forall b, dist (f b) (g b) < r := by
  lift r to Real>=0 using hr.le
  exact nndist_pi_lt_iff hr

/--
lemma `dist_pi_le_iff` / 引理 `dist_pi_le_iff`

English:
lemma dist_pi_le_iff
  given: {f g : forall b, X b} {r : Real} (hr : 0 <= r)
  proof: by
  lift r to Real>=0 using hr
  exact nndist_pi_le_iff

中文:
引理 dist_pi_le_iff
  条件: {f g : 对任意 b, X b} {r : 实数} (hr : 0 <= r)
  证明: by
  lift r to Real>=0 using hr
  exact nndist_pi_le_iff

Depends on / 依赖: nndist_pi_le_iff
-/
lemma dist_pi_le_iff {f g : forall b, X b} {r : Real} (hr : 0 <= r) :
    dist f g <= r ↔ forall b, dist (f b) (g b) <= r := by
  lift r to Real>=0 using hr
  exact nndist_pi_le_iff

/--
lemma `dist_pi_eq_iff` / 引理 `dist_pi_eq_iff`

English:
lemma dist_pi_eq_iff
  given: {f g : forall b, X b} {r : Real} (hr : 0 < r)
  proof: by
  lift r to Real>=0 using hr.le
  simp_rw [← coe_nndist, NNReal.coe_inj, nndist_pi_eq_iff hr, NNReal.coe_le_coe]

中文:
引理 dist_pi_eq_iff
  条件: {f g : 对任意 b, X b} {r : 实数} (hr : 0 < r)
  证明: by
  lift r to Real>=0 using hr.le
  simp_rw [← coe_nndist, NNReal.coe_inj, nndist_pi_eq_iff hr, NNReal.coe_le_coe]

Depends on / 依赖: NNReal, NNReal.coe_inj, NNReal.coe_le_coe, coe_inj, coe_le_coe, coe_nndist, hr.le, nndist_pi_eq_iff, simp_rw
-/
lemma dist_pi_eq_iff {f g : forall b, X b} {r : Real} (hr : 0 < r) :
    dist f g = r ↔ (exists i, dist (f i) (g i) = r) ∧ forall b, dist (f b) (g b) <= r := by
  lift r to Real>=0 using hr.le
  simp_rw [← coe_nndist, NNReal.coe_inj, nndist_pi_eq_iff hr, NNReal.coe_le_coe]

/--
lemma `dist_pi_le_iff'` / 引理 `dist_pi_le_iff'`

English:
lemma dist_pi_le_iff'
  given: [Nonempty β] {f g : forall b, X b} {r : Real}
  proof: by
  by_cases hr : 0 <= r
  · exact dist_pi_le_iff hr
  · exact iff_of_false (fun h => hr <| dist_nonneg.trans h) fun h =>
hr dist_nonneg.trans h Classical.arbitrary _

中文:
引理 dist_pi_le_iff'
  条件: [非空 β] {f g : 对任意 b, X b} {r : 实数}
  证明: by
  by_cases hr : 0 <= r
  · exact dist_pi_le_iff hr
  · exact iff_of_false (fun h => hr <| dist_nonneg.trans h) fun h =>
hr dist_nonneg.trans h Classical.arbitrary _

Depends on / 依赖: Classical, Classical.arbitrary, arbitrary, dist_nonneg, dist_nonneg.trans, dist_pi_le_iff, iff_of_false
-/
lemma dist_pi_le_iff' [Nonempty β] {f g : forall b, X b} {r : Real} :
    dist f g <= r ↔ forall b, dist (f b) (g b) <= r := by
  by_cases hr : 0 <= r
  · exact dist_pi_le_iff hr
  · exact iff_of_false (fun h => hr <| dist_nonneg.trans h) fun h =>
hr dist_nonneg.trans h Classical.arbitrary _

/--
lemma `dist_pi_const_le` / 引理 `dist_pi_const_le`

English:
lemma dist_pi_const_le
  given: (a b : α)
  statement: (dist (fun _ : β => a) fun _ => b) <= dist a b
  proof: (dist_pi_le_iff dist_nonneg).2 fun _ => le_rfl

中文:
引理 dist_pi_const_le
  条件: (a b : α)
  结论: (dist (fun _ : β => a) fun _ => b) <= dist a b
  证明: (dist_pi_le_iff dist_nonneg).2 fun _ => le_rfl

Depends on / 依赖: dist_nonneg, dist_pi_le_iff, le_rfl
-/
lemma dist_pi_const_le (a b : α) : (dist (fun _ : β => a) fun _ => b) <= dist a b :=
  (dist_pi_le_iff dist_nonneg).2 fun _ => le_rfl

/--
lemma `nndist_pi_const_le` / 引理 `nndist_pi_const_le`

English:
lemma nndist_pi_const_le
  given: (a b : α)
  statement: (nndist (fun _ : β => a) fun _ => b) <= nndist a b
  proof: nndist_pi_le_iff.2 fun _ => le_rfl

@[simp]

中文:
引理 nndist_pi_const_le
  条件: (a b : α)
  结论: (nndist (fun _ : β => a) fun _ => b) <= nndist a b
  证明: nndist_pi_le_iff.2 fun _ => le_rfl

@[simp]

Depends on / 依赖: le_rfl, nndist_pi_le_iff
-/
lemma nndist_pi_const_le (a b : α) : (nndist (fun _ : β => a) fun _ => b) <= nndist a b :=
  nndist_pi_le_iff.2 fun _ => le_rfl

@[simp]
/--
lemma `dist_pi_const` / 引理 `dist_pi_const`

English:
lemma dist_pi_const
  given: [Nonempty β] (a b : α)
  statement: (dist (fun _ : β => a) fun _ => b) = dist a b
  proof: by
  simpa only [dist_edist] using congr_arg ENNReal.toReal (edist_pi_const a b)

@[simp]

中文:
引理 dist_pi_const
  条件: [非空 β] (a b : α)
  结论: (dist (fun _ : β => a) fun _ => b) = dist a b
  证明: by
  simpa only [dist_edist] using congr_arg ENNReal.toReal (edist_pi_const a b)

@[simp]

Depends on / 依赖: ENNReal, ENNReal.toReal, congr_arg, dist_edist, edist_pi_const, toReal
-/
lemma dist_pi_const [Nonempty β] (a b : α) : (dist (fun _ : β => a) fun _ => b) = dist a b := by
  simpa only [dist_edist] using congr_arg ENNReal.toReal (edist_pi_const a b)

@[simp]
/--
lemma `nndist_pi_const` / 引理 `nndist_pi_const`

English:
lemma nndist_pi_const
  given: [Nonempty β] (a b : α)
  statement: (nndist (fun _ : β => a) fun _ => b) = nndist a b
  proof: NNReal.eq dist_pi_const a b

中文:
引理 nndist_pi_const
  条件: [非空 β] (a b : α)
  结论: (nndist (fun _ : β => a) fun _ => b) = nndist a b
  证明: NNReal.eq dist_pi_const a b

Depends on / 依赖: NNReal, NNReal.eq, dist_pi_const
-/
lemma nndist_pi_const [Nonempty β] (a b : α) : (nndist (fun _ : β => a) fun _ => b) = nndist a b :=
NNReal.eq dist_pi_const a b

/--
lemma `nndist_le_pi_nndist` / 引理 `nndist_le_pi_nndist`

English:
lemma nndist_le_pi_nndist
  given: (f g : forall b, X b) (b : β)
  statement: nndist (f b) (g b) <= nndist f g
  proof: by
  rw [← ENNReal.coe_le_coe]; rw [← edist_nndist]; rw [← edist_nndist]
  exact edist_le_pi_edist f g b

中文:
引理 nndist_le_pi_nndist
  条件: (f g : 对任意 b, X b) (b : β)
  结论: nndist (f b) (g b) <= nndist f g
  证明: by
  rw [← ENNReal.coe_le_coe]; rw [← edist_nndist]; rw [← edist_nndist]
  exact edist_le_pi_edist f g b

Depends on / 依赖: ENNReal, ENNReal.coe_le_coe, coe_le_coe, edist_le_pi_edist, edist_nndist
-/
lemma nndist_le_pi_nndist (f g : forall b, X b) (b : β) : nndist (f b) (g b) <= nndist f g := by
  rw [← ENNReal.coe_le_coe]; rw [← edist_nndist]; rw [← edist_nndist]
  exact edist_le_pi_edist f g b

/--
lemma `dist_le_pi_dist` / 引理 `dist_le_pi_dist`

English:
lemma dist_le_pi_dist
  given: (f g : forall b, X b) (b : β)
  statement: dist (f b) (g b) <= dist f g
  proof: by
  simp only [dist_nndist, NNReal.coe_le_coe, nndist_le_pi_nndist f g b]

中文:
引理 dist_le_pi_dist
  条件: (f g : 对任意 b, X b) (b : β)
  结论: dist (f b) (g b) <= dist f g
  证明: by
  simp only [dist_nndist, NNReal.coe_le_coe, nndist_le_pi_nndist f g b]

Depends on / 依赖: NNReal, NNReal.coe_le_coe, coe_le_coe, dist_nndist, nndist_le_pi_nndist
-/
lemma dist_le_pi_dist (f g : forall b, X b) (b : β) : dist (f b) (g b) <= dist f g := by
  simp only [dist_nndist, NNReal.coe_le_coe, nndist_le_pi_nndist f g b]

/--
lemma `ball_pi` / 引理 `ball_pi`

English:
lemma ball_pi
  given: (x : forall b, X b) {r : Real} (hr : 0 < r)
  proof: by
  ext p
  simp [dist_pi_lt_iff hr]

中文:
引理 ball_pi
  条件: (x : 对任意 b, X b) {r : 实数} (hr : 0 < r)
  证明: by
  ext p
  simp [dist_pi_lt_iff hr]

Depends on / 依赖: dist_pi_lt_iff
-/
lemma ball_pi (x : forall b, X b) {r : Real} (hr : 0 < r) :
    ball x r = Set.pi univ fun b => ball (x b) r := by
  ext p
  simp [dist_pi_lt_iff hr]

/--
lemma `ball_pi'` / 引理 `ball_pi'`

English:
lemma ball_pi'
  given: [Nonempty β] (x : forall b, X b) (r : Real)
  proof: (lt_or_ge 0 r).elim (ball_pi x) fun hr => by simp [ball_eq_empty.2 hr]

中文:
引理 ball_pi'
  条件: [非空 β] (x : 对任意 b, X b) (r : 实数)
  证明: (lt_or_ge 0 r).elim (ball_pi x) fun hr => by simp [ball_eq_empty.2 hr]

Depends on / 依赖: ball_eq_empty, ball_pi, lt_or_ge
-/
lemma ball_pi' [Nonempty β] (x : forall b, X b) (r : Real) :
    ball x r = Set.pi univ fun b => ball (x b) r :=
  (lt_or_ge 0 r).elim (ball_pi x) fun hr => by simp [ball_eq_empty.2 hr]

/--
lemma `closedBall_pi` / 引理 `closedBall_pi`

English:
lemma closedBall_pi
  given: (x : forall b, X b) {r : Real} (hr : 0 <= r)
  proof: by
  ext p
  simp [dist_pi_le_iff hr]

中文:
引理 closedBall_pi
  条件: (x : 对任意 b, X b) {r : 实数} (hr : 0 <= r)
  证明: by
  ext p
  simp [dist_pi_le_iff hr]

Depends on / 依赖: dist_pi_le_iff
-/
lemma closedBall_pi (x : forall b, X b) {r : Real} (hr : 0 <= r) :
    closedBall x r = Set.pi univ fun b => closedBall (x b) r := by
  ext p
  simp [dist_pi_le_iff hr]

/--
lemma `closedBall_pi'` / 引理 `closedBall_pi'`

English:
lemma closedBall_pi'
  given: [Nonempty β] (x : forall b, X b) (r : Real)
  proof: (le_or_gt 0 r).elim (closedBall_pi x) fun hr => by simp [closedBall_eq_empty.2 hr]

中文:
引理 closedBall_pi'
  条件: [非空 β] (x : 对任意 b, X b) (r : 实数)
  证明: (le_or_gt 0 r).elim (closedBall_pi x) fun hr => by simp [closedBall_eq_empty.2 hr]

Depends on / 依赖: closedBall_eq_empty, closedBall_pi, le_or_gt
-/
lemma closedBall_pi' [Nonempty β] (x : forall b, X b) (r : Real) :
    closedBall x r = Set.pi univ fun b => closedBall (x b) r :=
  (le_or_gt 0 r).elim (closedBall_pi x) fun hr => by simp [closedBall_eq_empty.2 hr]

/--
lemma `sphere_pi` / 引理 `sphere_pi`

English:
lemma sphere_pi
  given: (x : forall b, X b) {r : Real} (h : 0 < r ∨ Nonempty β)
  proof: by
  obtain hr | rfl | hr := lt_trichotomy r 0
  · simp [hr]
  · rw [closedBall_eq_sphere_of_nonpos le_rfl, eq_comm, Set.inter_eq_right]
    let := h.resolve_left (lt_irrefl _)
    inhabit β
    refine subset_iUnion_of_subset default ?_
    intro x hx
    replace hx := hx.le
    rw [dist_pi_le_iff le_rfl] at hx
    exact le_antisymm (hx default) dist_nonneg
  · ext
    simp [dist_pi_eq_iff hr, dist_pi_le_iff hr.le]

@[simp]

中文:
引理 sphere_pi
  条件: (x : 对任意 b, X b) {r : 实数} (h : 0 < r ∨ 非空 β)
  证明: by
  obtain hr | rfl | hr := lt_trichotomy r 0
  · simp [hr]
  · rw [closedBall_eq_sphere_of_nonpos le_rfl, eq_comm, Set.inter_eq_right]
    let := h.resolve_left (lt_irrefl _)
    inhabit β
    refine subset_iUnion_of_subset default ?_
    intro x hx
    replace hx := hx.le
    rw [dist_pi_le_iff le_rfl] at hx
    exact le_antisymm (hx default) dist_nonneg
  · ext
    simp [dist_pi_eq_iff hr, dist_pi_le_iff hr.le]

@[simp]

Depends on / 依赖: Set.inter_eq_right, closedBall_eq_sphere_of_nonpos, dist_nonneg, dist_pi_eq_iff, dist_pi_le_iff, eq_comm, h.resolve_left, hr.le, hx.le, inhabit, inter_eq_right, le_antisymm, le_rfl, lt_irrefl, lt_trichotomy, replace, resolve_left, subset_iUnion_of_subset
-/
lemma sphere_pi (x : forall b, X b) {r : Real} (h : 0 < r ∨ Nonempty β) :
    sphere x r = (⋃ i : β, Function.eval i ⁻¹' sphere (x i) r) inter closedBall x r := by
  obtain hr | rfl | hr := lt_trichotomy r 0
  · simp [hr]
  · rw [closedBall_eq_sphere_of_nonpos le_rfl, eq_comm, Set.inter_eq_right]
    let := h.resolve_left (lt_irrefl _)
    inhabit β
    refine subset_iUnion_of_subset default ?_
    intro x hx
    replace hx := hx.le
    rw [dist_pi_le_iff le_rfl] at hx
    exact le_antisymm (hx default) dist_nonneg
  · ext
    simp [dist_pi_eq_iff hr, dist_pi_le_iff hr.le]

@[simp]
/--
lemma `Fin.nndist_insertNth_insertNth` / 引理 `Fin.nndist_insertNth_insertNth`

English:
lemma Fin.nndist_insertNth_insertNth
  statement: {n : Nat} {α : Fin (n + 1) -> Type*}
  proof: eq_of_forall_ge_iff fun c => by simp [nndist_pi_le_iff, i.forall_iff_succAbove]

@[simp]

中文:
引理 有限集.nndist_insertNth_insertNth
  结论: {n : 自然数} {α : 有限集 (n + 1) -> 类型}
  证明: eq_of_forall_ge_iff fun c => by simp [nndist_pi_le_iff, i.forall_iff_succAbove]

@[simp]

Depends on / 依赖: eq_of_forall_ge_iff, forall_iff_succAbove, i.forall_iff_succAbove, nndist_pi_le_iff
-/
lemma Fin.nndist_insertNth_insertNth {n : Nat} {α : Fin (n + 1) -> Type*}
    [forall i, PseudoMetricSpace (α i)] (i : Fin (n + 1)) (x y : α i) (f g : forall j, α (i.succAbove j)) :
    nndist (i.insertNth x f) (i.insertNth y g) = max (nndist x y) (nndist f g) :=
  eq_of_forall_ge_iff fun c => by simp [nndist_pi_le_iff, i.forall_iff_succAbove]

@[simp]
/--
lemma `Fin.dist_insertNth_insertNth` / 引理 `Fin.dist_insertNth_insertNth`

English:
lemma Fin.dist_insertNth_insertNth
  statement: {n : Nat} {α : Fin (n + 1) -> Type*}
  proof: by
  simp only [dist_nndist, Fin.nndist_insertNth_insertNth, NNReal.coe_max]

中文:
引理 有限集.dist_insertNth_insertNth
  结论: {n : 自然数} {α : 有限集 (n + 1) -> 类型}
  证明: by
  simp only [dist_nndist, Fin.nndist_insertNth_insertNth, NNReal.coe_max]

Depends on / 依赖: Fin.nndist_insertNth_insertNth, NNReal, NNReal.coe_max, coe_max, dist_nndist, nndist_insertNth_insertNth
-/
lemma Fin.dist_insertNth_insertNth {n : Nat} {α : Fin (n + 1) -> Type*}
    [forall i, PseudoMetricSpace (α i)] (i : Fin (n + 1)) (x y : α i) (f g : forall j, α (i.succAbove j)) :
    dist (i.insertNth x f) (i.insertNth y g) = max (dist x y) (dist f g) := by
  simp only [dist_nndist, Fin.nndist_insertNth_insertNth, NNReal.coe_max]

/--
lemma `nndist_single_single` / 引理 `nndist_single_single`

English:
lemma nndist_single_single
  statement: {Y : Type*} [PseudoMetricSpace Y] [Zero Y] [DecidableEq β]
  proof: by
  refine le_antisymm (nndist_pi_le_iff.2 fun k => ?_) (max_le ?_ ?_)
  · simp only [Pi.single_apply]
    by_cases hki : k = i <;> by_cases hkj : k = j <;> simp_all [nndist_comm]
  · simpa [h] using nndist_le_pi_nndist (Pi.single i a : β -> Y) (Pi.single j b) i
  · simpa [h, nndist_comm] using nndist_le_pi_nndist (Pi.single i a : β -> Y) (Pi.single j b) j

中文:
引理 nndist_single_single
  结论: {Y : 类型} [伪度量空间 Y] [零 Y] [DecidableEq β]
  证明: by
  refine le_antisymm (nndist_pi_le_iff.2 fun k => ?_) (max_le ?_ ?_)
  · simp only [Pi.single_apply]
    by_cases hki : k = i <;> by_cases hkj : k = j <;> simp_all [nndist_comm]
  · simpa [h] using nndist_le_pi_nndist (Pi.single i a : β -> Y) (Pi.single j b) i
  · simpa [h, nndist_comm] using nndist_le_pi_nndist (Pi.single i a : β -> Y) (Pi.single j b) j

Depends on / 依赖: Pi.single, Pi.single_apply, le_antisymm, max_le, nndist_comm, nndist_le_pi_nndist, nndist_pi_le_iff, single, single_apply
-/
lemma nndist_single_single {Y : Type*} [PseudoMetricSpace Y] [Zero Y] [DecidableEq β]
    (i j : β) (a b : Y) (h : i != j) :
    nndist (Pi.single i a : β -> Y) (Pi.single j b) = max (nndist a 0) (nndist b 0) := by
  refine le_antisymm (nndist_pi_le_iff.2 fun k => ?_) (max_le ?_ ?_)
  · simp only [Pi.single_apply]
    by_cases hki : k = i <;> by_cases hkj : k = j <;> simp_all [nndist_comm]
  · simpa [h] using nndist_le_pi_nndist (Pi.single i a : β -> Y) (Pi.single j b) i
  · simpa [h, nndist_comm] using nndist_le_pi_nndist (Pi.single i a : β -> Y) (Pi.single j b) j

/--
lemma `dist_single_single` / 引理 `dist_single_single`

English:
lemma dist_single_single
  statement: {Y : Type*} [PseudoMetricSpace Y] [Zero Y] [DecidableEq β]
  proof: by
  simp only [dist_nndist, nndist_single_single i j a b h, NNReal.coe_max]

中文:
引理 dist_single_single
  结论: {Y : 类型} [伪度量空间 Y] [零 Y] [DecidableEq β]
  证明: by
  simp only [dist_nndist, nndist_single_single i j a b h, NNReal.coe_max]

Depends on / 依赖: NNReal, NNReal.coe_max, coe_max, dist_nndist, nndist_single_single
-/
lemma dist_single_single {Y : Type*} [PseudoMetricSpace Y] [Zero Y] [DecidableEq β]
    (i j : β) (a b : Y) (h : i != j) :
    dist (Pi.single i a : β -> Y) (Pi.single j b) = max (dist a 0) (dist b 0) := by
  simp only [dist_nndist, nndist_single_single i j a b h, NNReal.coe_max]
