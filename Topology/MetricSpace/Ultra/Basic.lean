/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.Clopen

/-!
## Ultrametric spaces

This file defines ultrametric spaces, implemented as a mixin on the `Dist`,
so that it can apply on pseudometric spaces as well.

## Main definitions

* `IsUltrametricDist X`: Annotates `dist : X → X → ℝ` as respecting the ultrametric inequality
  of `dist(x, z) ≤ max {dist(x,y), dist(y,z)}`

## Implementation details

The mixin could have been defined as a hypothesis to be carried around, instead of relying on
typeclass synthesis. However, since we declare a (pseudo)metric space on a type using
typeclass arguments, one can declare the ultrametricity at the same time.
For example, one could say `[Norm K] [Fact (IsNonarchimedean (norm : K → ℝ))]`,

The file imports a later file in the hierarchy of pseudometric spaces, since
`Metric.isClosed_closedBall` and `Metric.isClosed_sphere` is proven in a later file
using more conceptual results.

TODO: Generalize to ultrametric uniformities

## Tags

ultrametric, nonarchimedean
-/

public section

variable {X : Type*}

/--
Definition of `IsUltrametricDist` / `IsUltrametricDist` 的定义

English:
class IsUltrametricDist
  parameters: (X : Type*) [Dist X]
  axioms and operations (1):
    - dist_triangle_max : forall x y z : X, dist x z <= max (dist x y) (dist y z)

中文:
类 IsUltrametricDist
  参数: (X : 类型) [Dist X]
  公理与运算 (1 个):
    - dist_triangle_max : 对任意 x y z : X, dist x z <= max (dist x y) (dist y z)
-/
class IsUltrametricDist (X : Type*) [Dist X] : Prop where
  dist_triangle_max : forall x y z : X, dist x z <= max (dist x y) (dist y z)

open Metric

variable [PseudoMetricSpace X] [IsUltrametricDist X] (x y z : X) (r s : Real)

/--
lemma `dist_triangle_max` / 引理 `dist_triangle_max`

English:
lemma dist_triangle_max
  statement: dist x z <= max (dist x y) (dist y z)
  proof: IsUltrametricDist.dist_triangle_max x y z

中文:
引理 dist_triangle_max
  结论: dist x z <= max (dist x y) (dist y z)
  证明: IsUltrametricDist.dist_triangle_max x y z

Depends on / 依赖: IsUltrametricDist, IsUltrametricDist.dist_triangle_max, dist_triangle_max
-/
lemma dist_triangle_max : dist x z <= max (dist x y) (dist y z) :=
  IsUltrametricDist.dist_triangle_max x y z

namespace IsUltrametricDist

/--
lemma `dist_eq_max_of_dist_ne_dist` / 引理 `dist_eq_max_of_dist_ne_dist`

English:
lemma dist_eq_max_of_dist_ne_dist
  given: (h : dist x y != dist y z)
  proof: by
  apply le_antisymm (dist_triangle_max x y z)
  rcases h.lt_or_gt with h | h
  · rw [max_eq_right h.le]
    apply (le_max_iff.mp <| dist_triangle_max y x z).resolve_left
    simpa only [not_le, dist_comm x y] using h
  · rw [max_eq_left h.le, dist_comm x y, dist_comm x z]
    apply (le_max_iff.mp

中文:
引理 dist_eq_max_of_dist_ne_dist
  条件: (h : dist x y != dist y z)
  证明: by
  apply le_antisymm (dist_triangle_max x y z)
  rcases h.lt_or_gt with h | h
  · rw [max_eq_right h.le]
    apply (le_max_iff.mp <| dist_triangle_max y x z).resolve_left
    simpa only [not_le, dist_comm x y] using h
  · rw [max_eq_left h.le, dist_comm x y, dist_comm x z]
    apply (le_max_iff.mp

Depends on / 依赖: dist_comm, dist_triangle_max, h.le, h.lt_or_gt, le_antisymm, le_max_iff, le_max_iff.mp, lt_or_gt, max_eq_left, max_eq_right, not_le, resolve_left
-/
lemma dist_eq_max_of_dist_ne_dist (h : dist x y != dist y z) :
    dist x z = max (dist x y) (dist y z) := by
  apply le_antisymm (dist_triangle_max x y z)
  rcases h.lt_or_gt with h | h
  · rw [max_eq_right h.le]
    apply (le_max_iff.mp <| dist_triangle_max y x z).resolve_left
    simpa only [not_le, dist_comm x y] using h
  · rw [max_eq_left h.le, dist_comm x y, dist_comm x z]
    apply (le_max_iff.mp <| dist_triangle_max y z x).resolve_left
    simpa only [not_le, dist_comm x y] using h

/--
Instance `subtype` / 实例 `subtype`

English:
instance subtype
  signature: (p : X -> Prop)
  body: ⟨fun _ _ _ => by simpa [Subtype.dist_eq] using dist_triangle_max _ _ _⟩

中文:
实例 subtype
  签名: (p : X -> 命题)
  定义体: ⟨fun _ _ _ => by simpa [Subtype.dist_eq] using dist_triangle_max _ _ _⟩

Depends on / 依赖: Subtype, Subtype.dist_eq, dist_eq, dist_triangle_max
-/
instance subtype (p : X -> Prop) : IsUltrametricDist (Subtype p) :=
  ⟨fun _ _ _ => by simpa [Subtype.dist_eq] using dist_triangle_max _ _ _⟩

/--
lemma `ball_eq_of_mem` / 引理 `ball_eq_of_mem`

English:
lemma ball_eq_of_mem
  given: {x y : X} {r : Real} (h : y in ball x r)
  statement: ball x r = ball y r
  proof: by
  ext a
  simp_rw [mem_ball] at h ⊢
  constructor <;> intro h' <;>
  exact (dist_triangle_max _ _ _).trans_lt (max_lt h' (dist_comm x _ ▸ h))

中文:
引理 ball_eq_of_mem
  条件: {x y : X} {r : 实数} (h : y in ball x r)
  结论: ball x r = ball y r
  证明: by
  ext a
  simp_rw [mem_ball] at h ⊢
  constructor <;> intro h' <;>
  exact (dist_triangle_max _ _ _).trans_lt (max_lt h' (dist_comm x _ ▸ h))

Depends on / 依赖: dist_comm, dist_triangle_max, max_lt, mem_ball, simp_rw, trans_lt
-/
lemma ball_eq_of_mem {x y : X} {r : Real} (h : y in ball x r) : ball x r = ball y r := by
  ext a
  simp_rw [mem_ball] at h ⊢
  constructor <;> intro h' <;>
  exact (dist_triangle_max _ _ _).trans_lt (max_lt h' (dist_comm x _ ▸ h))

/--
lemma `ball_subset_trichotomy` / 引理 `ball_subset_trichotomy`

English:
lemma ball_subset_trichotomy
  proof: by
  wlog! hrs : r <= s generalizing x y r s
  · rw [disjoint_comm, ← or_assoc, or_comm (b := (_ : Set X) subseteq _), or_assoc]
    exact this y x s r hrs.le
.symm.imp (fun h => ?_) (Or.inr ·) · refine Set.disjoint_or_nonempty_inter (ball x r) (ball y s)
    obtain ⟨hxz, hyz⟩ := (Set.mem_inter_iff 

中文:
引理 ball_subset_trichotomy
  证明: by
  wlog! hrs : r <= s generalizing x y r s
  · rw [disjoint_comm, ← or_assoc, or_comm (b := (_ : Set X) subseteq _), or_assoc]
    exact this y x s r hrs.le
.symm.imp (fun h => ?_) (Or.inr ·) · refine Set.disjoint_or_nonempty_inter (ball x r) (ball y s)
    obtain ⟨hxz, hyz⟩ := (Set.mem_inter_iff 

Depends on / 依赖: Or.inr, Set.disjoint_or_nonempty_inter, Set.mem_inter_iff, ball_eq_of_mem, ball_subset_ball, disjoint_comm, disjoint_or_nonempty_inter, generalizing, h.some_mem, hrs.le, mem_inter_iff, or_assoc, or_comm, some_mem, subseteq, symm.imp
-/
lemma ball_subset_trichotomy :
    ball x r subseteq ball y s ∨ ball y s subseteq ball x r ∨ Disjoint (ball x r) (ball y s) := by
  wlog! hrs : r <= s generalizing x y r s
  · rw [disjoint_comm, ← or_assoc, or_comm (b := (_ : Set X) subseteq _), or_assoc]
    exact this y x s r hrs.le
.symm.imp (fun h => ?_) (Or.inr ·) · refine Set.disjoint_or_nonempty_inter (ball x r) (ball y s)
    obtain ⟨hxz, hyz⟩ := (Set.mem_inter_iff _ _ _).mp h.some_mem
    have hx := ball_subset_ball hrs (x := x)
    rwa [ball_eq_of_mem hyz |>.trans (ball_eq_of_mem <| hx hxz).symm]

/--
lemma `ball_eq_or_disjoint` / 引理 `ball_eq_or_disjoint`

English:
lemma ball_eq_or_disjoint
  proof: by
.symm.imp (fun h => ?_) id refine Set.disjoint_or_nonempty_inter (ball x r) (ball y r)
have h₁ := ball_eq_of_mem Set.inter_subset_left h.some_mem
have h₂ := ball_eq_of_mem Set.inter_subset_right h.some_mem
  exact h₁.trans h₂.symm

中文:
引理 ball_eq_or_disjoint
  证明: by
.symm.imp (fun h => ?_) id refine Set.disjoint_or_nonempty_inter (ball x r) (ball y r)
have h₁ := ball_eq_of_mem Set.inter_subset_left h.some_mem
have h₂ := ball_eq_of_mem Set.inter_subset_right h.some_mem
  exact h₁.trans h₂.symm

Depends on / 依赖: Set.disjoint_or_nonempty_inter, Set.inter_subset_left, Set.inter_subset_right, ball_eq_of_mem, disjoint_or_nonempty_inter, h.some_mem, inter_subset_left, inter_subset_right, some_mem, symm.imp
-/
lemma ball_eq_or_disjoint :
    ball x r = ball y r ∨ Disjoint (ball x r) (ball y r) := by
.symm.imp (fun h => ?_) id refine Set.disjoint_or_nonempty_inter (ball x r) (ball y r)
have h₁ := ball_eq_of_mem Set.inter_subset_left h.some_mem
have h₂ := ball_eq_of_mem Set.inter_subset_right h.some_mem
  exact h₁.trans h₂.symm

/--
lemma `closedBall_eq_of_mem` / 引理 `closedBall_eq_of_mem`

English:
lemma closedBall_eq_of_mem
  given: {x y : X} {r : Real} (h : y in closedBall x r)
  proof: by
  ext
  simp_rw [mem_closedBall] at h ⊢
  constructor <;> intro h' <;>
  exact (dist_triangle_max _ _ _).trans (max_le h' (dist_comm x _ ▸ h))

中文:
引理 closedBall_eq_of_mem
  条件: {x y : X} {r : 实数} (h : y in closedBall x r)
  证明: by
  ext
  simp_rw [mem_closedBall] at h ⊢
  constructor <;> intro h' <;>
  exact (dist_triangle_max _ _ _).trans (max_le h' (dist_comm x _ ▸ h))

Depends on / 依赖: dist_comm, dist_triangle_max, max_le, mem_closedBall, simp_rw
-/
lemma closedBall_eq_of_mem {x y : X} {r : Real} (h : y in closedBall x r) :
    closedBall x r = closedBall y r := by
  ext
  simp_rw [mem_closedBall] at h ⊢
  constructor <;> intro h' <;>
  exact (dist_triangle_max _ _ _).trans (max_le h' (dist_comm x _ ▸ h))

/--
lemma `closedBall_subset_trichotomy` / 引理 `closedBall_subset_trichotomy`

English:
lemma closedBall_subset_trichotomy
  proof: by
  wlog! hrs : r <= s generalizing x y r s
  · rw [disjoint_comm, ← or_assoc, or_comm (b := (_ : Set X) subseteq _), or_assoc]
    exact this y x s r hrs.le
.symm.imp · refine Set.disjoint_or_nonempty_inter (closedBall x r) (closedBall y s)
      (fun h => ?_) (Or.inr ·)
    obtain ⟨hxz, hyz⟩ := (

中文:
引理 closedBall_subset_trichotomy
  证明: by
  wlog! hrs : r <= s generalizing x y r s
  · rw [disjoint_comm, ← or_assoc, or_comm (b := (_ : Set X) subseteq _), or_assoc]
    exact this y x s r hrs.le
.symm.imp · refine Set.disjoint_or_nonempty_inter (closedBall x r) (closedBall y s)
      (fun h => ?_) (Or.inr ·)
    obtain ⟨hxz, hyz⟩ := (

Depends on / 依赖: Or.inr, Set.disjoint_or_nonempty_inter, Set.mem_inter_iff, closedBall, closedBall_eq_of_mem, closedBall_subset_closedBall, disjoint_comm, disjoint_or_nonempty_inter, generalizing, h.some_mem, hrs.le, mem_inter_iff, or_assoc, or_comm, some_mem, subseteq, symm.imp
-/
lemma closedBall_subset_trichotomy :
    closedBall x r subseteq closedBall y s ∨ closedBall y s subseteq closedBall x r ∨
    Disjoint (closedBall x r) (closedBall y s) := by
  wlog! hrs : r <= s generalizing x y r s
  · rw [disjoint_comm, ← or_assoc, or_comm (b := (_ : Set X) subseteq _), or_assoc]
    exact this y x s r hrs.le
.symm.imp · refine Set.disjoint_or_nonempty_inter (closedBall x r) (closedBall y s)
      (fun h => ?_) (Or.inr ·)
    obtain ⟨hxz, hyz⟩ := (Set.mem_inter_iff _ _ _).mp h.some_mem
    have hx := closedBall_subset_closedBall hrs (x := x)
    rwa [closedBall_eq_of_mem hyz |>.trans (closedBall_eq_of_mem <| hx hxz).symm]

/--
lemma `isClosed_ball` / 引理 `isClosed_ball`

English:
lemma isClosed_ball
  given: (x : X) (r : Real)
  statement: IsClosed (ball x r)
  proof: by
  cases le_or_gt r 0 with
  | inl hr =>
    simp [ball_eq_empty.mpr hr]
  | inr h =>
    rw [← isOpen_compl_iff]; rw [isOpen_iff]
    push _ in _
    intro y hy
    cases ball_eq_or_disjoint x y r with
    | inl hd =>
      rw [hd] at hy
      simp [h.not_ge] at hy
    | inr hd =>
      use r
   

中文:
引理 isClosed_ball
  条件: (x : X) (r : 实数)
  结论: IsClosed (ball x r)
  证明: by
  cases le_or_gt r 0 with
  | inl hr =>
    simp [ball_eq_empty.mpr hr]
  | inr h =>
    rw [← isOpen_compl_iff]; rw [isOpen_iff]
    push _ in _
    intro y hy
    cases ball_eq_or_disjoint x y r with
    | inl hd =>
      rw [hd] at hy
      simp [h.not_ge] at hy
    | inr hd =>
      use r
   

Depends on / 依赖: ball_eq_empty, ball_eq_empty.mpr, ball_eq_or_disjoint, h.not_ge, isOpen_compl_iff, isOpen_iff, le_compl_iff_disjoint_left, le_or_gt, not_ge
-/
lemma isClosed_ball (x : X) (r : Real) : IsClosed (ball x r) := by
  cases le_or_gt r 0 with
  | inl hr =>
    simp [ball_eq_empty.mpr hr]
  | inr h =>
    rw [← isOpen_compl_iff]; rw [isOpen_iff]
    push _ in _
    intro y hy
    cases ball_eq_or_disjoint x y r with
    | inl hd =>
      rw [hd] at hy
      simp [h.not_ge] at hy
    | inr hd =>
      use r
      simp [h, le_compl_iff_disjoint_left, hd]

/--
lemma `isClopen_ball` / 引理 `isClopen_ball`

English:
lemma isClopen_ball
  statement: IsClopen (ball x r)
  proof: ⟨isClosed_ball x r, isOpen_ball⟩

中文:
引理 isClopen_ball
  结论: IsClopen (ball x r)
  证明: ⟨isClosed_ball x r, isOpen_ball⟩

Depends on / 依赖: isClosed_ball, isOpen_ball
-/
lemma isClopen_ball : IsClopen (ball x r) := ⟨isClosed_ball x r, isOpen_ball⟩

/--
lemma `frontier_ball_eq_empty` / 引理 `frontier_ball_eq_empty`

English:
lemma frontier_ball_eq_empty
  statement: frontier (ball x r) = ∅
  proof: isClopen_iff_frontier_eq_empty.mp (isClopen_ball x r)

中文:
引理 frontier_ball_eq_empty
  结论: frontier (ball x r) = ∅
  证明: isClopen_iff_frontier_eq_empty.mp (isClopen_ball x r)

Depends on / 依赖: isClopen_ball, isClopen_iff_frontier_eq_empty, isClopen_iff_frontier_eq_empty.mp
-/
lemma frontier_ball_eq_empty : frontier (ball x r) = ∅ :=
  isClopen_iff_frontier_eq_empty.mp (isClopen_ball x r)

/--
lemma `closedBall_eq_or_disjoint` / 引理 `closedBall_eq_or_disjoint`

English:
lemma closedBall_eq_or_disjoint
  proof: by
.symm.imp refine Set.disjoint_or_nonempty_inter (closedBall x r) (closedBall y r)
    (fun h => ?_) id
have h₁ := closedBall_eq_of_mem Set.inter_subset_left h.some_mem
have h₂ := closedBall_eq_of_mem Set.inter_subset_right h.some_mem
  exact h₁.trans h₂.symm

中文:
引理 closedBall_eq_or_disjoint
  证明: by
.symm.imp refine Set.disjoint_or_nonempty_inter (closedBall x r) (closedBall y r)
    (fun h => ?_) id
have h₁ := closedBall_eq_of_mem Set.inter_subset_left h.some_mem
have h₂ := closedBall_eq_of_mem Set.inter_subset_right h.some_mem
  exact h₁.trans h₂.symm

Depends on / 依赖: Set.disjoint_or_nonempty_inter, Set.inter_subset_left, Set.inter_subset_right, closedBall, closedBall_eq_of_mem, disjoint_or_nonempty_inter, h.some_mem, inter_subset_left, inter_subset_right, some_mem, symm.imp
-/
lemma closedBall_eq_or_disjoint :
    closedBall x r = closedBall y r ∨ Disjoint (closedBall x r) (closedBall y r) := by
.symm.imp refine Set.disjoint_or_nonempty_inter (closedBall x r) (closedBall y r)
    (fun h => ?_) id
have h₁ := closedBall_eq_of_mem Set.inter_subset_left h.some_mem
have h₂ := closedBall_eq_of_mem Set.inter_subset_right h.some_mem
  exact h₁.trans h₂.symm

/--
lemma `isOpen_closedBall` / 引理 `isOpen_closedBall`

English:
lemma isOpen_closedBall
  given: {r : Real} (hr : r != 0)
  statement: IsOpen (closedBall x r)
  proof: by
  cases lt_or_gt_of_ne hr with
  | inl h =>
    simp [closedBall_eq_empty.mpr h]
  | inr h =>
    rw [isOpen_iff]
    simp only [gt_iff_lt]
    intro y hy
    cases closedBall_eq_or_disjoint x y r with
    | inl hd =>
      use r
      simp [h, hd, ball_subset_closedBall]
    | inr hd =>
      si

中文:
引理 isOpen_closedBall
  条件: {r : 实数} (hr : r != 0)
  结论: IsOpen (closedBall x r)
  证明: by
  cases lt_or_gt_of_ne hr with
  | inl h =>
    simp [closedBall_eq_empty.mpr h]
  | inr h =>
    rw [isOpen_iff]
    simp only [gt_iff_lt]
    intro y hy
    cases closedBall_eq_or_disjoint x y r with
    | inl hd =>
      use r
      simp [h, hd, ball_subset_closedBall]
    | inr hd =>
      si

Depends on / 依赖: ball_subset_closedBall, closedBall_eq_empty, closedBall_eq_empty.mpr, closedBall_eq_of_mem, closedBall_eq_or_disjoint, gt_iff_lt, h.not_gt, isOpen_iff, lt_or_gt_of_ne, not_gt
-/
lemma isOpen_closedBall {r : Real} (hr : r != 0) : IsOpen (closedBall x r) := by
  cases lt_or_gt_of_ne hr with
  | inl h =>
    simp [closedBall_eq_empty.mpr h]
  | inr h =>
    rw [isOpen_iff]
    simp only [gt_iff_lt]
    intro y hy
    cases closedBall_eq_or_disjoint x y r with
    | inl hd =>
      use r
      simp [h, hd, ball_subset_closedBall]
    | inr hd =>
      simp [closedBall_eq_of_mem hy, h.not_gt] at hd

/--
lemma `isClopen_closedBall` / 引理 `isClopen_closedBall`

English:
lemma isClopen_closedBall
  given: {r : Real} (hr : r != 0)
  statement: IsClopen (closedBall x r)
  proof: ⟨Metric.isClosed_closedBall, isOpen_closedBall x hr⟩

中文:
引理 isClopen_closedBall
  条件: {r : 实数} (hr : r != 0)
  结论: IsClopen (closedBall x r)
  证明: ⟨Metric.isClosed_closedBall, isOpen_closedBall x hr⟩

Depends on / 依赖: Metric, Metric.isClosed_closedBall, isClosed_closedBall, isOpen_closedBall
-/
lemma isClopen_closedBall {r : Real} (hr : r != 0) : IsClopen (closedBall x r) :=
  ⟨Metric.isClosed_closedBall, isOpen_closedBall x hr⟩

/--
lemma `frontier_closedBall_eq_empty` / 引理 `frontier_closedBall_eq_empty`

English:
lemma frontier_closedBall_eq_empty
  given: {r : Real} (hr : r != 0)
  statement: frontier (closedBall x r) = ∅
  proof: isClopen_iff_frontier_eq_empty.mp (isClopen_closedBall x hr)

中文:
引理 frontier_closedBall_eq_empty
  条件: {r : 实数} (hr : r != 0)
  结论: frontier (closedBall x r) = ∅
  证明: isClopen_iff_frontier_eq_empty.mp (isClopen_closedBall x hr)

Depends on / 依赖: isClopen_closedBall, isClopen_iff_frontier_eq_empty, isClopen_iff_frontier_eq_empty.mp
-/
lemma frontier_closedBall_eq_empty {r : Real} (hr : r != 0) : frontier (closedBall x r) = ∅ :=
  isClopen_iff_frontier_eq_empty.mp (isClopen_closedBall x hr)

/--
lemma `isOpen_sphere` / 引理 `isOpen_sphere`

English:
lemma isOpen_sphere
  given: {r : Real} (hr : r != 0)
  statement: IsOpen (sphere x r)
  proof: by
  rw [← closedBall_sdiff_ball]; rw [sdiff_eq]
  exact (isOpen_closedBall x hr).inter (isClosed_ball x r).isOpen_compl

中文:
引理 isOpen_sphere
  条件: {r : 实数} (hr : r != 0)
  结论: IsOpen (sphere x r)
  证明: by
  rw [← closedBall_sdiff_ball]; rw [sdiff_eq]
  exact (isOpen_closedBall x hr).inter (isClosed_ball x r).isOpen_compl

Depends on / 依赖: closedBall_sdiff_ball, isClosed_ball, isOpen_closedBall, isOpen_compl, sdiff_eq
-/
lemma isOpen_sphere {r : Real} (hr : r != 0) : IsOpen (sphere x r) := by
  rw [← closedBall_sdiff_ball]; rw [sdiff_eq]
  exact (isOpen_closedBall x hr).inter (isClosed_ball x r).isOpen_compl

/--
lemma `isClopen_sphere` / 引理 `isClopen_sphere`

English:
lemma isClopen_sphere
  given: {r : Real} (hr : r != 0)
  statement: IsClopen (sphere x r)
  proof: ⟨Metric.isClosed_sphere, isOpen_sphere x hr⟩

中文:
引理 isClopen_sphere
  条件: {r : 实数} (hr : r != 0)
  结论: IsClopen (sphere x r)
  证明: ⟨Metric.isClosed_sphere, isOpen_sphere x hr⟩

Depends on / 依赖: Metric, Metric.isClosed_sphere, isClosed_sphere, isOpen_sphere
-/
lemma isClopen_sphere {r : Real} (hr : r != 0) : IsClopen (sphere x r) :=
  ⟨Metric.isClosed_sphere, isOpen_sphere x hr⟩

end IsUltrametricDist
