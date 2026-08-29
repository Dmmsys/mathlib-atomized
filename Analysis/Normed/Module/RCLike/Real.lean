/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Patrick Massot, Eric Wieser, Yaël Dillies
-/
module

public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Basic facts about real (semi)normed spaces

In this file we prove some theorems about (semi)normed spaces over real numbers.

## Main results

- `closure_ball`, `frontier_ball`, `interior_closedBall`, `frontier_closedBall`, `interior_sphere`,
  `frontier_sphere`: formulas for the closure/interior/frontier
  of nontrivial balls and spheres in a real seminormed space;

- `interior_closedBall'`, `frontier_closedBall'`, `interior_sphere'`, `frontier_sphere'`:
  similar lemmas assuming that the ambient space is separated and nontrivial instead of `r ≠ 0`.
-/

public section

open Metric Set Function Filter
open scoped NNReal Topology

/--
Instance `Real.punctured_nhds_module_neBot` / 实例 `Real.punctured_nhds_module_neBot`

English:
instance Real.punctured_nhds_module_neBot
  signature: {E : Type*} [AddCommGroup E] [TopologicalSpace E]
  body: Module.punctured_nhds_neBot Real E x

中文:
实例 Real.punctured_nhds_module_neBot
  签名: {E : 类型} [AddCommGroup E] [TopologicalSpace E]
  定义体: Module.punctured_nhds_neBot Real E x

Depends on / 依赖: Module, Module.punctured_nhds_neBot, punctured_nhds_neBot
-/
instance Real.punctured_nhds_module_neBot {E : Type*} [AddCommGroup E] [TopologicalSpace E]
    [ContinuousAdd E] [Nontrivial E] [Module Real E] [ContinuousSMul Real E] (x : E) : NeBot (𝓝[!=] x) :=
  Module.punctured_nhds_neBot Real E x

section Seminormed

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace Real E]

/--
theorem `inv_norm_smul_mem_unitClosedBall` / 定理 `inv_norm_smul_mem_unitClosedBall`

English:
theorem inv_norm_smul_mem_unitClosedBall
  given: (x : E)
  proof: by
  simp only [mem_closedBall_zero_iff, norm_smul, norm_inv, norm_norm, ← div_eq_inv_mul,
    div_self_le_one]

中文:
定理 inv_norm_smul_mem_unitClosedBall
  条件: (x : E)
  证明: by
  simp only [mem_closedBall_zero_iff, norm_smul, norm_inv, norm_norm, ← div_eq_inv_mul,
    div_self_le_one]

Depends on / 依赖: div_eq_inv_mul, div_self_le_one, mem_closedBall_zero_iff, norm_inv, norm_norm, norm_smul
-/
theorem inv_norm_smul_mem_unitClosedBall (x : E) :
    ‖x‖⁻¹ • x in closedBall (0 : E) 1 := by
  simp only [mem_closedBall_zero_iff, norm_smul, norm_inv, norm_norm, ← div_eq_inv_mul,
    div_self_le_one]

/--
theorem `norm_smul_of_nonneg` / 定理 `norm_smul_of_nonneg`

English:
theorem norm_smul_of_nonneg
  given: {t : Real} (ht : 0 <= t) (x : E)
  statement: ‖t • x‖ = t * ‖x‖
  proof: by
  rw [norm_smul]; rw [Real.norm_eq_abs]; rw [abs_of_nonneg ht]

中文:
定理 norm_smul_of_nonneg
  条件: {t : 实数} (ht : 0 <= t) (x : E)
  结论: ‖t • x‖ = t * ‖x‖
  证明: by
  rw [norm_smul]; rw [Real.norm_eq_abs]; rw [abs_of_nonneg ht]

Depends on / 依赖: Real.norm_eq_abs, abs_of_nonneg, norm_eq_abs, norm_smul
-/
theorem norm_smul_of_nonneg {t : Real} (ht : 0 <= t) (x : E) : ‖t • x‖ = t * ‖x‖ := by
  rw [norm_smul]; rw [Real.norm_eq_abs]; rw [abs_of_nonneg ht]

/--
theorem `dist_smul_add_one_sub_smul_le` / 定理 `dist_smul_add_one_sub_smul_le`

English:
theorem dist_smul_add_one_sub_smul_le
  given: {r : Real} {x y : E} (h : r in Icc 0 1)
  proof: calc
    dist (r • x + (1 - r) • y) x = ‖1 - r‖ * ‖x - y‖ := by
      simp_rw [dist_eq_norm', ← norm_smul, sub_smul, one_smul, smul_sub, ← sub_sub, ← sub_add,
        sub_right_comm]
    _ = (1 - r) * dist y x := by
      rw [Real.norm_eq_abs]; rw [abs_eq_self.mpr (sub_nonneg.mpr h.2)]; rw [dist_eq_

中文:
定理 dist_smul_add_one_sub_smul_le
  条件: {r : 实数} {x y : E} (h : r in Icc 0 1)
  证明: calc
    dist (r • x + (1 - r) • y) x = ‖1 - r‖ * ‖x - y‖ := by
      simp_rw [dist_eq_norm', ← norm_smul, sub_smul, one_smul, smul_sub, ← sub_sub, ← sub_add,
        sub_right_comm]
    _ = (1 - r) * dist y x := by
      rw [Real.norm_eq_abs]; rw [abs_eq_self.mpr (sub_nonneg.mpr h.2)]; rw [dist_eq_

Depends on / 依赖: Real.norm_eq_abs, abs_eq_self, abs_eq_self.mpr, dist_eq_norm, norm_eq_abs, norm_smul, one_mul, one_smul, simp_rw, smul_sub, sub_add, sub_nonneg, sub_nonneg.mpr, sub_right_comm, sub_smul, sub_sub, sub_zero
-/
theorem dist_smul_add_one_sub_smul_le {r : Real} {x y : E} (h : r in Icc 0 1) :
    dist (r • x + (1 - r) • y) x <= dist y x :=
  calc
    dist (r • x + (1 - r) • y) x = ‖1 - r‖ * ‖x - y‖ := by
      simp_rw [dist_eq_norm', ← norm_smul, sub_smul, one_smul, smul_sub, ← sub_sub, ← sub_add,
        sub_right_comm]
    _ = (1 - r) * dist y x := by
      rw [Real.norm_eq_abs]; rw [abs_eq_self.mpr (sub_nonneg.mpr h.2)]; rw [dist_eq_norm']
    _ <= (1 - 0) * dist y x := by gcongr; exact h.1
    _ = dist y x := by rw [sub_zero, one_mul]

/--
theorem `closure_ball` / 定理 `closure_ball`

English:
theorem closure_ball
  given: (x : E) {r : Real} (hr : r != 0)
  statement: closure (ball x r) = closedBall x r
  proof: by
  refine Subset.antisymm closure_ball_subset_closedBall fun y hy => ?_
  have : ContinuousWithinAt (fun c : Real => c • (y - x) + x) (Ico 0 1) 1 := by fun_prop
  convert! this.mem_closure _ _
  · rw [one_smul, sub_add_cancel]
  · simp [closure_Ico zero_ne_one, zero_le_one]
  · rintro c ⟨hc0, hc1⟩

中文:
定理 closure_ball
  条件: (x : E) {r : 实数} (hr : r != 0)
  结论: closure (ball x r) = closedBall x r
  证明: by
  refine Subset.antisymm closure_ball_subset_closedBall fun y hy => ?_
  have : ContinuousWithinAt (fun c : Real => c • (y - x) + x) (Ico 0 1) 1 := by fun_prop
  convert! this.mem_closure _ _
  · rw [one_smul, sub_add_cancel]
  · simp [closure_Ico zero_ne_one, zero_le_one]
  · rintro c ⟨hc0, hc1⟩

Depends on / 依赖: ContinuousWithinAt, Real.norm_eq_abs, Subset, Subset.antisymm, abs_of_nonneg, add_sub_cancel_right, antisymm, closure_Ico, closure_ball_subset_closedBall, convert, dist_eq_norm, fun_prop, mem_ball, mem_closedBall, mem_closure, mul_comm, mul_one, norm_eq_abs, norm_smul, one_smul
-/
theorem closure_ball (x : E) {r : Real} (hr : r != 0) : closure (ball x r) = closedBall x r := by
  refine Subset.antisymm closure_ball_subset_closedBall fun y hy => ?_
  have : ContinuousWithinAt (fun c : Real => c • (y - x) + x) (Ico 0 1) 1 := by fun_prop
  convert! this.mem_closure _ _
  · rw [one_smul, sub_add_cancel]
  · simp [closure_Ico zero_ne_one, zero_le_one]
  · rintro c ⟨hc0, hc1⟩
    rw [mem_ball]; rw [dist_eq_norm]; rw [add_sub_cancel_right]; rw [norm_smul]; rw [Real.norm_eq_abs]; rw [abs_of_nonneg hc0]; rw [mul_comm]; rw [← mul_one r]
    rw [mem_closedBall]; rw [dist_eq_norm] at hy
    replace hr : 0 < r := ((norm_nonneg _).trans hy).lt_of_ne hr.symm
    apply mul_lt_mul' <;> assumption

/--
theorem `frontier_ball` / 定理 `frontier_ball`

English:
theorem frontier_ball
  given: (x : E) {r : Real} (hr : r != 0)
  proof: by
  rw [frontier]; rw [closure_ball x hr]; rw [isOpen_ball.interior_eq]; rw [closedBall_sdiff_ball]

中文:
定理 frontier_ball
  条件: (x : E) {r : 实数} (hr : r != 0)
  证明: by
  rw [frontier]; rw [closure_ball x hr]; rw [isOpen_ball.interior_eq]; rw [closedBall_sdiff_ball]

Depends on / 依赖: closedBall_sdiff_ball, closure_ball, frontier, interior_eq, isOpen_ball, isOpen_ball.interior_eq
-/
theorem frontier_ball (x : E) {r : Real} (hr : r != 0) :
    frontier (ball x r) = sphere x r := by
  rw [frontier]; rw [closure_ball x hr]; rw [isOpen_ball.interior_eq]; rw [closedBall_sdiff_ball]

/--
theorem `interior_closedBall` / 定理 `interior_closedBall`

English:
theorem interior_closedBall
  given: (x : E) {r : Real} (hr : r != 0)
  proof: by
  rcases hr.lt_or_gt with hr | hr
  · rw [closedBall_eq_empty.2 hr, ball_eq_empty.2 hr.le, interior_empty]
  refine Subset.antisymm ?_ ball_subset_interior_closedBall
  intro y hy
  rcases (mem_closedBall.1 <| interior_subset hy).lt_or_eq with (hr | rfl)
  · exact hr
  set f : Real -> E := fun c 

中文:
定理 interior_closedBall
  条件: (x : E) {r : 实数} (hr : r != 0)
  证明: by
  rcases hr.lt_or_gt with hr | hr
  · rw [closedBall_eq_empty.2 hr, ball_eq_empty.2 hr.le, interior_empty]
  refine Subset.antisymm ?_ ball_subset_interior_closedBall
  intro y hy
  rcases (mem_closedBall.1 <| interior_subset hy).lt_or_eq with (hr | rfl)
  · exact hr
  set f : Real -> E := fun c 

Depends on / 依赖: Subset, Subset.antisymm, antisymm, ball_eq_empty, ball_subset_interior_closedBall, closedBall, closedBall_eq_empty, hr.le, hr.lt_or_gt, interior, interior_empty, interior_mono, interior_subset, lt_or_eq, lt_or_gt, mem_closedBall, preimage_interior_subset_interior_preimage, subseteq
-/
theorem interior_closedBall (x : E) {r : Real} (hr : r != 0) :
    interior (closedBall x r) = ball x r := by
  rcases hr.lt_or_gt with hr | hr
  · rw [closedBall_eq_empty.2 hr, ball_eq_empty.2 hr.le, interior_empty]
  refine Subset.antisymm ?_ ball_subset_interior_closedBall
  intro y hy
  rcases (mem_closedBall.1 <| interior_subset hy).lt_or_eq with (hr | rfl)
  · exact hr
  set f : Real -> E := fun c : Real => c • (y - x) + x
  suffices f ⁻¹' closedBall x (dist y x) subseteq Icc (-1) 1 by
    have h1 : (1 : Real) in interior (Icc (-1 : Real) 1) :=
      interior_mono this (preimage_interior_subset_interior_preimage (by fun_prop) (by simpa [f]))
    simp at h1
  intro c hc
  rw [mem_Icc]; rw [← abs_le]; rw [← Real.norm_eq_abs]; rw [← mul_le_mul_iff_left₀ hr]
  simpa [f, dist_eq_norm, norm_smul] using hc

/--
theorem `frontier_closedBall` / 定理 `frontier_closedBall`

English:
theorem frontier_closedBall
  given: (x : E) {r : Real} (hr : r != 0)
  proof: by
  rw [frontier]; rw [closure_closedBall]; rw [interior_closedBall x hr]; rw [closedBall_sdiff_ball]

中文:
定理 frontier_closedBall
  条件: (x : E) {r : 实数} (hr : r != 0)
  证明: by
  rw [frontier]; rw [closure_closedBall]; rw [interior_closedBall x hr]; rw [closedBall_sdiff_ball]

Depends on / 依赖: closedBall_sdiff_ball, closure_closedBall, frontier, interior_closedBall
-/
theorem frontier_closedBall (x : E) {r : Real} (hr : r != 0) :
    frontier (closedBall x r) = sphere x r := by
  rw [frontier]; rw [closure_closedBall]; rw [interior_closedBall x hr]; rw [closedBall_sdiff_ball]

/--
theorem `interior_sphere` / 定理 `interior_sphere`

English:
theorem interior_sphere
  given: (x : E) {r : Real} (hr : r != 0)
  statement: interior (sphere x r) = ∅
  proof: by
  rw [← frontier_closedBall x hr]; rw [interior_frontier isClosed_closedBall]

中文:
定理 interior_sphere
  条件: (x : E) {r : 实数} (hr : r != 0)
  结论: interior (sphere x r) = ∅
  证明: by
  rw [← frontier_closedBall x hr]; rw [interior_frontier isClosed_closedBall]

Depends on / 依赖: frontier_closedBall, interior_frontier, isClosed_closedBall
-/
theorem interior_sphere (x : E) {r : Real} (hr : r != 0) : interior (sphere x r) = ∅ := by
  rw [← frontier_closedBall x hr]; rw [interior_frontier isClosed_closedBall]

/--
theorem `frontier_sphere` / 定理 `frontier_sphere`

English:
theorem frontier_sphere
  given: (x : E) {r : Real} (hr : r != 0)
  statement: frontier (sphere x r) = sphere x r
  proof: by
  rw [isClosed_sphere.frontier_eq]; rw [interior_sphere x hr]; rw [sdiff_empty]

中文:
定理 frontier_sphere
  条件: (x : E) {r : 实数} (hr : r != 0)
  结论: frontier (sphere x r) = sphere x r
  证明: by
  rw [isClosed_sphere.frontier_eq]; rw [interior_sphere x hr]; rw [sdiff_empty]

Depends on / 依赖: frontier_eq, interior_sphere, isClosed_sphere, isClosed_sphere.frontier_eq, sdiff_empty
-/
theorem frontier_sphere (x : E) {r : Real} (hr : r != 0) : frontier (sphere x r) = sphere x r := by
  rw [isClosed_sphere.frontier_eq]; rw [interior_sphere x hr]; rw [sdiff_empty]

variable [NontrivialTopology E]

section Surj
variable (E)

/--
theorem `exists_norm_eq` / 定理 `exists_norm_eq`

English:
theorem exists_norm_eq
  given: {c : Real} (hc : 0 <= c)
  statement: exists x : E, ‖x‖ = c
  proof: by
  rcases exists_norm_ne_zero E with ⟨x, hx⟩
  use c • ‖x‖⁻¹ • x
  simp [norm_smul, Real.norm_of_nonneg hc, inv_mul_cancel₀ hx]

@[simp]

中文:
定理 exists_norm_eq
  条件: {c : 实数} (hc : 0 <= c)
  结论: 存在 x : E, ‖x‖ = c
  证明: by
  rcases exists_norm_ne_zero E with ⟨x, hx⟩
  use c • ‖x‖⁻¹ • x
  simp [norm_smul, Real.norm_of_nonneg hc, inv_mul_cancel₀ hx]

@[simp]

Depends on / 依赖: Real.norm_of_nonneg, exists_norm_ne_zero, norm_of_nonneg, norm_smul
-/
theorem exists_norm_eq {c : Real} (hc : 0 <= c) : exists x : E, ‖x‖ = c := by
  rcases exists_norm_ne_zero E with ⟨x, hx⟩
  use c • ‖x‖⁻¹ • x
  simp [norm_smul, Real.norm_of_nonneg hc, inv_mul_cancel₀ hx]

@[simp]
/--
theorem `range_norm` / 定理 `range_norm`

English:
theorem range_norm
  statement: range (norm : E -> Real) = Ici 0
  proof: Subset.antisymm (range_subset_iff.2 norm_nonneg) fun _ => exists_norm_eq E

中文:
定理 range_norm
  结论: range (norm : E -> 实数) = Ici 0
  证明: Subset.antisymm (range_subset_iff.2 norm_nonneg) fun _ => exists_norm_eq E

Depends on / 依赖: Subset, Subset.antisymm, antisymm, exists_norm_eq, norm_nonneg, range_subset_iff
-/
theorem range_norm : range (norm : E -> Real) = Ici 0 :=
  Subset.antisymm (range_subset_iff.2 norm_nonneg) fun _ => exists_norm_eq E

/--
theorem `nnnorm_surjective` / 定理 `nnnorm_surjective`

English:
theorem nnnorm_surjective
  statement: Surjective (nnnorm : E -> Real>=0)
  proof: fun c =>
  (exists_norm_eq E c.coe_nonneg).imp fun _ h => NNReal.eq h

@[simp]

中文:
定理 nnnorm_surjective
  结论: Surjective (nnnorm : E -> 实数>=0)
  证明: fun c =>
  (exists_norm_eq E c.coe_nonneg).imp fun _ h => NNReal.eq h

@[simp]
-/
theorem nnnorm_surjective : Surjective (nnnorm : E -> Real>=0) := fun c =>
  (exists_norm_eq E c.coe_nonneg).imp fun _ h => NNReal.eq h

@[simp]
/--
theorem `range_nnnorm` / 定理 `range_nnnorm`

English:
theorem range_nnnorm
  statement: range (nnnorm : E -> Real>=0) = univ
  proof: (nnnorm_surjective E).range_eq

中文:
定理 range_nnnorm
  结论: range (nnnorm : E -> 实数>=0) = univ
  证明: (nnnorm_surjective E).range_eq

Depends on / 依赖: nnnorm_surjective, range_eq
-/
theorem range_nnnorm : range (nnnorm : E -> Real>=0) = univ :=
  (nnnorm_surjective E).range_eq

variable {E} in
/-- In a nontrivial real normed space, a sphere is nonempty if and only if its radius is
nonnegative. -/
@[simp]
/--
theorem `NormedSpace.sphere_nonempty` / 定理 `NormedSpace.sphere_nonempty`

English:
theorem NormedSpace.sphere_nonempty
  given: {x : E} {r : Real}
  statement: (sphere x r).Nonempty ↔ 0 <= r
  proof: by
  refine ⟨fun h => nonempty_closedBall.1 (h.mono sphere_subset_closedBall), fun hr => ?_⟩
  obtain ⟨y, hy⟩ := exists_norm_eq E hr
  exact ⟨x + y, by simpa using hy⟩

中文:
定理 NormedSpace.sphere_nonempty
  条件: {x : E} {r : 实数}
  结论: (sphere x r).Nonempty ↔ 0 <= r
  证明: by
  refine ⟨fun h => nonempty_closedBall.1 (h.mono sphere_subset_closedBall), fun hr => ?_⟩
  obtain ⟨y, hy⟩ := exists_norm_eq E hr
  exact ⟨x + y, by simpa using hy⟩

Depends on / 依赖: exists_norm_eq, h.mono, nonempty_closedBall, sphere_subset_closedBall
-/
theorem NormedSpace.sphere_nonempty {x : E} {r : Real} : (sphere x r).Nonempty ↔ 0 <= r := by
  refine ⟨fun h => nonempty_closedBall.1 (h.mono sphere_subset_closedBall), fun hr => ?_⟩
  obtain ⟨y, hy⟩ := exists_norm_eq E hr
  exact ⟨x + y, by simpa using hy⟩

end Surj

end Seminormed

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [Nontrivial E]

/--
theorem `interior_closedBall'` / 定理 `interior_closedBall'`

English:
theorem interior_closedBall'
  given: (x : E) (r : Real)
  statement: interior (closedBall x r) = ball x r
  proof: by
  rcases eq_or_ne r 0 with (rfl | hr)
  · rw [closedBall_zero, ball_zero, interior_singleton]
  · exact interior_closedBall x hr

中文:
定理 interior_closedBall'
  条件: (x : E) (r : 实数)
  结论: interior (closedBall x r) = ball x r
  证明: by
  rcases eq_or_ne r 0 with (rfl | hr)
  · rw [closedBall_zero, ball_zero, interior_singleton]
  · exact interior_closedBall x hr

Depends on / 依赖: ball_zero, closedBall_zero, eq_or_ne, interior_closedBall, interior_singleton
-/
theorem interior_closedBall' (x : E) (r : Real) : interior (closedBall x r) = ball x r := by
  rcases eq_or_ne r 0 with (rfl | hr)
  · rw [closedBall_zero, ball_zero, interior_singleton]
  · exact interior_closedBall x hr

/--
theorem `frontier_closedBall'` / 定理 `frontier_closedBall'`

English:
theorem frontier_closedBall'
  given: (x : E) (r : Real)
  statement: frontier (closedBall x r) = sphere x r
  proof: by
  rw [frontier]; rw [closure_closedBall]; rw [interior_closedBall' x r]; rw [closedBall_sdiff_ball]

@[simp]

中文:
定理 frontier_closedBall'
  条件: (x : E) (r : 实数)
  结论: frontier (closedBall x r) = sphere x r
  证明: by
  rw [frontier]; rw [closure_closedBall]; rw [interior_closedBall' x r]; rw [closedBall_sdiff_ball]

@[simp]

Depends on / 依赖: closedBall_sdiff_ball, closure_closedBall, frontier, interior_closedBall
-/
theorem frontier_closedBall' (x : E) (r : Real) : frontier (closedBall x r) = sphere x r := by
  rw [frontier]; rw [closure_closedBall]; rw [interior_closedBall' x r]; rw [closedBall_sdiff_ball]

@[simp]
/--
theorem `interior_sphere'` / 定理 `interior_sphere'`

English:
theorem interior_sphere'
  given: (x : E) (r : Real)
  statement: interior (sphere x r) = ∅
  proof: by
  rw [← frontier_closedBall' x]; rw [interior_frontier isClosed_closedBall]

@[simp]

中文:
定理 interior_sphere'
  条件: (x : E) (r : 实数)
  结论: interior (sphere x r) = ∅
  证明: by
  rw [← frontier_closedBall' x]; rw [interior_frontier isClosed_closedBall]

@[simp]

Depends on / 依赖: frontier_closedBall, interior_frontier, isClosed_closedBall
-/
theorem interior_sphere' (x : E) (r : Real) : interior (sphere x r) = ∅ := by
  rw [← frontier_closedBall' x]; rw [interior_frontier isClosed_closedBall]

@[simp]
/--
theorem `frontier_sphere'` / 定理 `frontier_sphere'`

English:
theorem frontier_sphere'
  given: (x : E) (r : Real)
  statement: frontier (sphere x r) = sphere x r
  proof: by
  rw [isClosed_sphere.frontier_eq]; rw [interior_sphere' x]; rw [sdiff_empty]

中文:
定理 frontier_sphere'
  条件: (x : E) (r : 实数)
  结论: frontier (sphere x r) = sphere x r
  证明: by
  rw [isClosed_sphere.frontier_eq]; rw [interior_sphere' x]; rw [sdiff_empty]

Depends on / 依赖: frontier_eq, interior_sphere, isClosed_sphere, isClosed_sphere.frontier_eq, sdiff_empty
-/
theorem frontier_sphere' (x : E) (r : Real) : frontier (sphere x r) = sphere x r := by
  rw [isClosed_sphere.frontier_eq]; rw [interior_sphere' x]; rw [sdiff_empty]

end Normed
