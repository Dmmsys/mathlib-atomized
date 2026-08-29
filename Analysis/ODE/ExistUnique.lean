/-
Copyright (c) 2026 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
module

public import Mathlib.Analysis.ODE.Basic
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.ODE.PicardLindelof

/-!
# Existence and uniqueness of solutions to ODEs

This file collects the public-facing existence and uniqueness theorems for solutions to ODEs in
normed spaces.

## Main results

* `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt`: the Picard-Lindelöf theorem,
  stating the existence of a local solution to a time-dependent ODE.
* `IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith`: the
  existence of a local flow that is Lipschitz continuous in the initial point.
* `IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn`: the existence
  of a local flow `E × ℝ → E` that is continuous on its domain.
* `IsPicardLindelof.exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt`: the existence
  of a local flow to a time-dependent vector field.
* `ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt`: a `C¹` vector
  field admits solutions on open intervals for all nearby initial points.
* `ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀`: a `C¹` vector
  field admits a local solution.
* `ContDiffAt.exists_eventually_eq_hasDerivAt`: a `C¹` vector field admits a local flow.
* `ODE_solution_unique` and variants: uniqueness statements for ODE solutions on various intervals.

## Tags

integral curve, vector field, existence, uniqueness, Picard-Lindelöf, Gronwall
-/

@[expose] public section

open Function intervalIntegral MeasureTheory Metric Set
open scoped Nat NNReal Topology

/-! ## Existence of solutions to ODEs -/

namespace IsPicardLindelof

open ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
  {f : Real -> E -> E} {tmin tmax : Real} {t₀ : Icc tmin tmax} {x₀ x : E} {a r L K : Real>=0}

/--
theorem `exists_eq_forall_mem_Icc_hasDerivWithinAt` / 定理 `exists_eq_forall_mem_Icc_hasDerivWithinAt`

English:
theorem exists_eq_forall_mem_Icc_hasDerivWithinAt
  proof: by
  obtain ⟨α, hα⟩ := FunSpace.exists_isFixedPt_next hf hx
  refine ⟨α.compProj, by rw [FunSpace.compProj_val, ← hα, FunSpace.next_apply₀], fun t ht => ?_⟩
  apply hasDerivWithinAt_picard_Icc t₀.2 hf.continuousOn_uncurry
    α.continuous_compProj.continuousOn (fun _ ht' => α.compProj_mem_closedBall

中文:
定理 存在_eq_对任意_mem_Icc_hasDerivWithinAt
  证明: by
  obtain ⟨α, hα⟩ := FunSpace.exists_isFixedPt_next hf hx
  refine ⟨α.compProj, by rw [FunSpace.compProj_val, ← hα, FunSpace.next_apply₀], fun t ht => ?_⟩
  apply hasDerivWithinAt_picard_Icc t₀.2 hf.continuousOn_uncurry
    α.continuous_compProj.continuousOn (fun _ ht' => α.compProj_mem_closedBall

Depends on / 依赖: FunSpace, FunSpace.compProj_of_mem, FunSpace.compProj_val, FunSpace.exists_isFixedPt_next, FunSpace.next_apply, compProj, compProj_mem_closedBall, compProj_of_mem, compProj_val, congr_of_mem, continuousOn, continuousOn_uncurry, continuous_compProj, continuous_compProj.continuousOn, exists_isFixedPt_next, hasDerivWithinAt_picard_Icc, hf.continuousOn_uncurry, hf.mul_max_le, mul_max_le, next_apply
-/
theorem exists_eq_forall_mem_Icc_hasDerivWithinAt
    (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x in closedBall x₀ r) :
    exists α : Real -> E, α t₀ = x ∧
      forall t in Icc tmin tmax, HasDerivWithinAt α (f t (α t)) (Icc tmin tmax) t := by
  obtain ⟨α, hα⟩ := FunSpace.exists_isFixedPt_next hf hx
  refine ⟨α.compProj, by rw [FunSpace.compProj_val, ← hα, FunSpace.next_apply₀], fun t ht => ?_⟩
  apply hasDerivWithinAt_picard_Icc t₀.2 hf.continuousOn_uncurry
    α.continuous_compProj.continuousOn (fun _ ht' => α.compProj_mem_closedBall hf.mul_max_le)
.congr_of_mem _ ht x ht
  intro t' ht'
  nth_rw 1 [← hα]
  rw [FunSpace.compProj_of_mem ht']; rw [FunSpace.next_apply]

/--
theorem `exists_eq_forall_mem_Icc_hasDerivWithinAt₀` / 定理 `exists_eq_forall_mem_Icc_hasDerivWithinAt₀`

English:
theorem exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  proof: exists_eq_forall_mem_Icc_hasDerivWithinAt hf (mem_closedBall_self le_rfl)

中文:
定理 存在_eq_对任意_mem_Icc_hasDerivWithinAt₀
  证明: exists_eq_forall_mem_Icc_hasDerivWithinAt hf (mem_closedBall_self le_rfl)

Depends on / 依赖: exists_eq_forall_mem_Icc_hasDerivWithinAt, le_rfl, mem_closedBall_self
-/
theorem exists_eq_forall_mem_Icc_hasDerivWithinAt₀
    (hf : IsPicardLindelof f t₀ x₀ a 0 L K) :
    exists α : Real -> E, α t₀ = x₀ ∧
      forall t in Icc tmin tmax, HasDerivWithinAt α (f t (α t)) (Icc tmin tmax) t :=
  exists_eq_forall_mem_Icc_hasDerivWithinAt hf (mem_closedBall_self le_rfl)

/--
theorem `exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith` / 定理 `exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith`

English:
theorem exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
  proof: by
  classical
  have (x) (hx : x in closedBall x₀ r) := FunSpace.exists_isFixedPt_next hf hx
  choose α hα using this
  set α' := fun (x : E) => if hx : x in closedBall x₀ r then
.compProj else 0 with hα' α x hx
  refine ⟨α', fun x hx => ⟨?_, fun t ht => ?_⟩, ?_⟩
  · rw [hα']
    beta_reduce
    rw

中文:
定理 存在_对任意_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
  证明: by
  classical
  have (x) (hx : x in closedBall x₀ r) := FunSpace.exists_isFixedPt_next hf hx
  choose α hα using this
  set α' := fun (x : E) => if hx : x in closedBall x₀ r then
.compProj else 0 with hα' α x hx
  refine ⟨α', fun x hx => ⟨?_, fun t ht => ?_⟩, ?_⟩
  · rw [hα']
    beta_reduce
    rw

Depends on / 依赖: FunSpace, FunSpace.compProj_apply, FunSpace.compProj_val, FunSpace.exists_isFixedPt_next, FunSpace.next_apply, beta_reduce, classical, closedBall, compProj, compProj_apply, compProj_val, continuousOn_uncurry, dif_pos, exists_isFixedPt_next, hasDerivWithinAt_picard_Icc, hf.continuousOn_uncurry
-/
theorem exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
    (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    exists α : E -> Real -> E, (forall x in closedBall x₀ r, α x t₀ = x ∧
      forall t in Icc tmin tmax, HasDerivWithinAt (α x) (f t (α x t)) (Icc tmin tmax) t) ∧
      exists L' : Real>=0, forall t in Icc tmin tmax, LipschitzOnWith L' (α · t) (closedBall x₀ r) := by
  classical
  have (x) (hx : x in closedBall x₀ r) := FunSpace.exists_isFixedPt_next hf hx
  choose α hα using this
  set α' := fun (x : E) => if hx : x in closedBall x₀ r then
.compProj else 0 with hα' α x hx
  refine ⟨α', fun x hx => ⟨?_, fun t ht => ?_⟩, ?_⟩
  · rw [hα']
    beta_reduce
    rw [dif_pos hx]; rw [FunSpace.compProj_val]; rw [← hα]; rw [FunSpace.next_apply₀]
  · rw [hα']
    beta_reduce
    rw [dif_pos hx]; rw [FunSpace.compProj_apply]
    apply hasDerivWithinAt_picard_Icc t₀.2 hf.continuousOn_uncurry
      (α x hx |>.continuous_compProj.continuousOn)
      (fun _ ht' => α x hx |>.compProj_mem_closedBall hf.mul_max_le)
.congr_of_mem _ ht x ht
    intro t' ht'
    nth_rw 1 [← hα]
    rw [FunSpace.compProj_of_mem ht']; rw [FunSpace.next_apply]
  · obtain ⟨L', h⟩ := FunSpace.exists_forall_closedBall_funSpace_dist_le_mul hf
    refine ⟨L', fun t ht => LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_⟩
    simp_rw [hα']
    rw [dif_pos hx]; rw [dif_pos hy]; rw [FunSpace.compProj_apply]; rw [FunSpace.compProj_apply]; rw [← FunSpace.toContinuousMap_apply_eq_apply]; rw [← FunSpace.toContinuousMap_apply_eq_apply]
    have : Nonempty (Icc tmin tmax) := ⟨t₀⟩
    apply ContinuousMap.dist_le_iff_of_nonempty.mp
    exact h x y hx hy (α x hx) (α y hy) (hα x hx) (hα y hy)

/--
theorem `exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn` / 定理 `exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn`

English:
theorem exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  proof: by
  obtain ⟨α, hα1, L', hα2⟩ := hf.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
  refine ⟨uncurry α, hα1, ?_⟩
  apply continuousOn_prod_of_continuousOn_lipschitzOnWith _ L' _ hα2
  exact fun x hx => HasDerivWithinAt.continuousOn (hα1 x hx).2

中文:
定理 存在_对任意_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  证明: by
  obtain ⟨α, hα1, L', hα2⟩ := hf.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
  refine ⟨uncurry α, hα1, ?_⟩
  apply continuousOn_prod_of_continuousOn_lipschitzOnWith _ L' _ hα2
  exact fun x hx => HasDerivWithinAt.continuousOn (hα1 x hx).2

Depends on / 依赖: HasDerivWithinAt, HasDerivWithinAt.continuousOn, continuousOn, continuousOn_prod_of_continuousOn_lipschitzOnWith, exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith, hf.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith, uncurry
-/
theorem exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
    (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    exists α : E × Real -> E, (forall x in closedBall x₀ r, α ⟨x, t₀⟩ = x ∧
      forall t in Icc tmin tmax, HasDerivWithinAt (α ⟨x, ·⟩) (f t (α ⟨x, t⟩)) (Icc tmin tmax) t) ∧
      ContinuousOn α (closedBall x₀ r ×ˢ Icc tmin tmax) := by
  obtain ⟨α, hα1, L', hα2⟩ := hf.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
  refine ⟨uncurry α, hα1, ?_⟩
  apply continuousOn_prod_of_continuousOn_lipschitzOnWith _ L' _ hα2
  exact fun x hx => HasDerivWithinAt.continuousOn (hα1 x hx).2

/--
theorem `exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt` / 定理 `exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt`

English:
theorem exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt
  proof: have ⟨α, hα⟩ := exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith hf
  ⟨α, hα.1⟩

中文:
定理 存在_对任意_mem_closedBall_eq_对任意_mem_Icc_hasDerivWithinAt
  证明: have ⟨α, hα⟩ := exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith hf
  ⟨α, hα.1⟩

Depends on / 依赖: exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
-/
theorem exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt
    (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    exists α : E -> Real -> E, forall x in closedBall x₀ r, α x t₀ = x ∧
      forall t in Icc tmin tmax, HasDerivWithinAt (α x) (f t (α x t)) (Icc tmin tmax) t :=
  have ⟨α, hα⟩ := exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith hf
  ⟨α, hα.1⟩

end IsPicardLindelof

/-! ## $C^1$ vector field -/

namespace ContDiffAt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
  {f : E -> E} {x₀ : E}

/--
theorem `exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt` / 定理 `exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt`

English:
theorem exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt
  proof: by
  have ⟨ε, hε, a, r, _, _, hr, hpl⟩ := IsPicardLindelof.of_contDiffAt_one hf
  refine ⟨r, hr, ε, hε, fun x hx => ?_⟩
  have ⟨α, hα1, hα2⟩ := (hpl t₀).exists_eq_forall_mem_Icc_hasDerivWithinAt hx
  refine ⟨α, hα1, fun t ht => ?_⟩
.hasDerivAt (Icc_mem_nhds ht.1 ht.2) exact hα2 t (Ioo_subset_Icc_sel

中文:
定理 存在_对任意_mem_closedBall_存在_eq_对任意_mem_Ioo_hasDerivAt
  证明: by
  have ⟨ε, hε, a, r, _, _, hr, hpl⟩ := IsPicardLindelof.of_contDiffAt_one hf
  refine ⟨r, hr, ε, hε, fun x hx => ?_⟩
  have ⟨α, hα1, hα2⟩ := (hpl t₀).exists_eq_forall_mem_Icc_hasDerivWithinAt hx
  refine ⟨α, hα1, fun t ht => ?_⟩
.hasDerivAt (Icc_mem_nhds ht.1 ht.2) exact hα2 t (Ioo_subset_Icc_sel

Depends on / 依赖: Icc_mem_nhds, Ioo_subset_Icc_self, IsPicardLindelof, IsPicardLindelof.of_contDiffAt_one, exists_eq_forall_mem_Icc_hasDerivWithinAt, hasDerivAt, of_contDiffAt_one
-/
theorem exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt
    (hf : ContDiffAt Real 1 f x₀) (t₀ : Real) :
    exists r > (0 : Real), exists ε > (0 : Real), forall x in closedBall x₀ r, exists α : Real -> E, α t₀ = x ∧
      forall t in Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (f (α t)) t := by
  have ⟨ε, hε, a, r, _, _, hr, hpl⟩ := IsPicardLindelof.of_contDiffAt_one hf
  refine ⟨r, hr, ε, hε, fun x hx => ?_⟩
  have ⟨α, hα1, hα2⟩ := (hpl t₀).exists_eq_forall_mem_Icc_hasDerivWithinAt hx
  refine ⟨α, hα1, fun t ht => ?_⟩
.hasDerivAt (Icc_mem_nhds ht.1 ht.2) exact hα2 t (Ioo_subset_Icc_self ht)

/--
theorem `exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀` / 定理 `exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀`

English:
theorem exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀
  proof: have ⟨_, hr, ε, hε, H⟩ := exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt hf t₀
  have ⟨α, hα1, hα2⟩ := H x₀ (mem_closedBall_self (le_of_lt hr))
  ⟨α, hα1, ε, hε, hα2⟩

中文:
定理 存在_对任意_mem_closedBall_存在_eq_对任意_mem_Ioo_hasDerivAt₀
  证明: have ⟨_, hr, ε, hε, H⟩ := exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt hf t₀
  have ⟨α, hα1, hα2⟩ := H x₀ (mem_closedBall_self (le_of_lt hr))
  ⟨α, hα1, ε, hε, hα2⟩

Depends on / 依赖: exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt, le_of_lt, mem_closedBall_self
-/
theorem exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀
    (hf : ContDiffAt Real 1 f x₀) (t₀ : Real) :
    exists α : Real -> E, α t₀ = x₀ ∧ exists ε > (0 : Real),
      forall t in Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (f (α t)) t :=
  have ⟨_, hr, ε, hε, H⟩ := exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt hf t₀
  have ⟨α, hα1, hα2⟩ := H x₀ (mem_closedBall_self (le_of_lt hr))
  ⟨α, hα1, ε, hε, hα2⟩

/--
theorem `exists_eventually_eq_hasDerivAt` / 定理 `exists_eventually_eq_hasDerivAt`

English:
theorem exists_eventually_eq_hasDerivAt
  proof: by
  classical
  obtain ⟨r, hr, ε, hε, H⟩ := exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt hf t₀
  choose α hα using H
  refine ⟨fun (x : E) => if hx : x in closedBall x₀ r then α x hx else 0, ?_⟩
  rw [Filter.eventually_iff_exists_mem]
  refine ⟨closedBall x₀ r ×ˢ Ioo (t₀ - ε) (t

中文:
定理 存在_eventually_eq_hasDerivAt
  证明: by
  classical
  obtain ⟨r, hr, ε, hε, H⟩ := exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt hf t₀
  choose α hα using H
  refine ⟨fun (x : E) => if hx : x in closedBall x₀ r then α x hx else 0, ?_⟩
  rw [Filter.eventually_iff_exists_mem]
  refine ⟨closedBall x₀ r ×ˢ Ioo (t₀ - ε) (t

Depends on / 依赖: Filter, Filter.eventually_iff_exists_mem, Filter.prod_mem_prod_iff, Ioo_mem_nhds, classical, closedBall, closedBall_mem_nhds, eventually_iff_exists_mem, exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt, prod_mem_prod_iff
-/
theorem exists_eventually_eq_hasDerivAt
    (hf : ContDiffAt Real 1 f x₀) (t₀ : Real) :
    exists α : E -> Real -> E, forallᶠ xt in 𝓝 x₀ ×ˢ 𝓝 t₀,
      α xt.1 t₀ = xt.1 ∧ HasDerivAt (α xt.1) (f (α xt.1 xt.2)) xt.2 := by
  classical
  obtain ⟨r, hr, ε, hε, H⟩ := exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt hf t₀
  choose α hα using H
  refine ⟨fun (x : E) => if hx : x in closedBall x₀ r then α x hx else 0, ?_⟩
  rw [Filter.eventually_iff_exists_mem]
  refine ⟨closedBall x₀ r ×ˢ Ioo (t₀ - ε) (t₀ + ε), ?_, ?_⟩
  · rw [Filter.prod_mem_prod_iff]
    exact ⟨closedBall_mem_nhds x₀ hr, Ioo_mem_nhds (by linarith) (by linarith)⟩
  · grind

end ContDiffAt

/-! ## Uniqueness of solutions to ODEs -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  {v : Real -> E -> E} {s : Real -> Set E} {K : Real>=0} {f g : Real -> E} {a b t₀ : Real}

/--
theorem `ODE_solution_unique_of_mem_Icc_right` / 定理 `ODE_solution_unique_of_mem_Icc_right`

English:
theorem ODE_solution_unique_of_mem_Icc_right
  proof: fun t ht => by
  have := dist_le_of_trajectories_ODE_of_mem hv hf hf' hfs hg hg' hgs (dist_le_zero.2 ha) t ht
  rwa [zero_mul, dist_le_zero] at this

中文:
定理 ODE_solution_unique_of_mem_Icc_right
  证明: fun t ht => by
  have := dist_le_of_trajectories_ODE_of_mem hv hf hf' hfs hg hg' hgs (dist_le_zero.2 ha) t ht
  rwa [zero_mul, dist_le_zero] at this

Depends on / 依赖: dist_le_of_trajectories_ODE_of_mem, dist_le_zero, zero_mul
-/
theorem ODE_solution_unique_of_mem_Icc_right
    (hv : forall t in Ico a b, LipschitzOnWith K (v t) (s t))
    (hf : ContinuousOn f (Icc a b))
    (hf' : forall t in Ico a b, HasDerivWithinAt f (v t (f t)) (Ici t) t)
    (hfs : forall t in Ico a b, f t in s t)
    (hg : ContinuousOn g (Icc a b))
    (hg' : forall t in Ico a b, HasDerivWithinAt g (v t (g t)) (Ici t) t)
    (hgs : forall t in Ico a b, g t in s t)
    (ha : f a = g a) :
    EqOn f g (Icc a b) := fun t ht => by
  have := dist_le_of_trajectories_ODE_of_mem hv hf hf' hfs hg hg' hgs (dist_le_zero.2 ha) t ht
  rwa [zero_mul, dist_le_zero] at this

/--
theorem `ODE_solution_unique_of_mem_Icc_left` / 定理 `ODE_solution_unique_of_mem_Icc_left`

English:
theorem ODE_solution_unique_of_mem_Icc_left
  proof: by
  have hv' : forall t in Ico (-b) (-a), LipschitzOnWith K (Neg.neg ∘ (v (-t))) (s (-t)) := by
    intro t ht
    replace ht : -t in Ioc a b := by
      push _ in _ at ht ⊢
      constructor <;> linarith
    rw [← one_mul K]
    exact LipschitzWith.id.neg.comp_lipschitzOnWith (hv _ ht)
  have hmt1

中文:
定理 ODE_solution_unique_of_mem_Icc_left
  证明: by
  have hv' : forall t in Ico (-b) (-a), LipschitzOnWith K (Neg.neg ∘ (v (-t))) (s (-t)) := by
    intro t ht
    replace ht : -t in Ioc a b := by
      push _ in _ at ht ⊢
      constructor <;> linarith
    rw [← one_mul K]
    exact LipschitzWith.id.neg.comp_lipschitzOnWith (hv _ ht)
  have hmt1

Depends on / 依赖: LipschitzOnWith, LipschitzWith, LipschitzWith.id.neg.comp_lipschitzOnWith, MapsTo, Neg.neg, comp_lipschitzOnWith, le_neg, le_neg.mp, lt_neg, lt_neg.mp, neg_le, neg_le.mp, one_mul, replace
-/
theorem ODE_solution_unique_of_mem_Icc_left
    (hv : forall t in Ioc a b, LipschitzOnWith K (v t) (s t))
    (hf : ContinuousOn f (Icc a b))
    (hf' : forall t in Ioc a b, HasDerivWithinAt f (v t (f t)) (Iic t) t)
    (hfs : forall t in Ioc a b, f t in s t)
    (hg : ContinuousOn g (Icc a b))
    (hg' : forall t in Ioc a b, HasDerivWithinAt g (v t (g t)) (Iic t) t)
    (hgs : forall t in Ioc a b, g t in s t)
    (hb : f b = g b) :
    EqOn f g (Icc a b) := by
  have hv' : forall t in Ico (-b) (-a), LipschitzOnWith K (Neg.neg ∘ (v (-t))) (s (-t)) := by
    intro t ht
    replace ht : -t in Ioc a b := by
      push _ in _ at ht ⊢
      constructor <;> linarith
    rw [← one_mul K]
    exact LipschitzWith.id.neg.comp_lipschitzOnWith (hv _ ht)
  have hmt1 : MapsTo Neg.neg (Icc (-b) (-a)) (Icc a b) :=
    fun _ ht => ⟨le_neg.mp ht.2, neg_le.mp ht.1⟩
  have hmt2 : MapsTo Neg.neg (Ico (-b) (-a)) (Ioc a b) :=
    fun _ ht => ⟨lt_neg.mp ht.2, neg_le.mp ht.1⟩
  have hmt3 (t : Real) : MapsTo Neg.neg (Ici t) (Iic (-t)) :=
fun _ ht' => mem_Iic.mpr neg_le_neg ht'
  suffices EqOn (f ∘ Neg.neg) (g ∘ Neg.neg) (Icc (-b) (-a)) by
    rw [eqOn_comp_right_iff] at this
    convert this
    simp
  apply ODE_solution_unique_of_mem_Icc_right hv'
    (hf.comp continuousOn_neg hmt1) _ (fun _ ht => hfs _ (hmt2 ht))
    (hg.comp continuousOn_neg hmt1) _ (fun _ ht => hgs _ (hmt2 ht)) (by simp [hb])
  · intro t ht
    convert!
      HasFDerivWithinAt.comp_hasDerivWithinAt t (hf' (-t) (hmt2 ht))
        (hasDerivAt_neg t).hasDerivWithinAt (hmt3 t)
    simp
  · intro t ht
    convert!
      HasFDerivWithinAt.comp_hasDerivWithinAt t (hg' (-t) (hmt2 ht))
        (hasDerivAt_neg t).hasDerivWithinAt (hmt3 t)
    simp

/--
theorem `ODE_solution_unique_of_mem_Icc` / 定理 `ODE_solution_unique_of_mem_Icc`

English:
theorem ODE_solution_unique_of_mem_Icc
  proof: by
  rw [← Icc_union_Icc_eq_Icc (le_of_lt ht.1) (le_of_lt ht.2)]
  apply EqOn.union
  · have hss : Ioc a t₀ subseteq Ioo a b := Ioc_subset_Ioo_right ht.2
    exact ODE_solution_unique_of_mem_Icc_left (fun t ht => hv t (hss ht))
      (hf.mono <| Icc_subset_Icc_right <| le_of_lt ht.2)
      (fun _ ht

中文:
定理 ODE_solution_unique_of_mem_Icc
  证明: by
  rw [← Icc_union_Icc_eq_Icc (le_of_lt ht.1) (le_of_lt ht.2)]
  apply EqOn.union
  · have hss : Ioc a t₀ subseteq Ioo a b := Ioc_subset_Ioo_right ht.2
    exact ODE_solution_unique_of_mem_Icc_left (fun t ht => hv t (hss ht))
      (hf.mono <| Icc_subset_Icc_right <| le_of_lt ht.2)
      (fun _ ht

Depends on / 依赖: EqOn.union, Icc_subset_Icc_right, Icc_union_Icc_eq_Icc, Ioc_subset_Ioo_right, ODE_solution_unique_of_mem_Icc_left, hasDerivWithinAt, hf.mono, hg.mono, le_of_lt, subseteq
-/
theorem ODE_solution_unique_of_mem_Icc
    (hv : forall t in Ioo a b, LipschitzOnWith K (v t) (s t))
    (ht : t₀ in Ioo a b)
    (hf : ContinuousOn f (Icc a b))
    (hf' : forall t in Ioo a b, HasDerivAt f (v t (f t)) t)
    (hfs : forall t in Ioo a b, f t in s t)
    (hg : ContinuousOn g (Icc a b))
    (hg' : forall t in Ioo a b, HasDerivAt g (v t (g t)) t)
    (hgs : forall t in Ioo a b, g t in s t)
    (heq : f t₀ = g t₀) :
    EqOn f g (Icc a b) := by
  rw [← Icc_union_Icc_eq_Icc (le_of_lt ht.1) (le_of_lt ht.2)]
  apply EqOn.union
  · have hss : Ioc a t₀ subseteq Ioo a b := Ioc_subset_Ioo_right ht.2
    exact ODE_solution_unique_of_mem_Icc_left (fun t ht => hv t (hss ht))
      (hf.mono <| Icc_subset_Icc_right <| le_of_lt ht.2)
      (fun _ ht' => (hf' _ (hss ht')).hasDerivWithinAt) (fun _ ht' => (hfs _ (hss ht')))
      (hg.mono <| Icc_subset_Icc_right <| le_of_lt ht.2)
      (fun _ ht' => (hg' _ (hss ht')).hasDerivWithinAt) (fun _ ht' => (hgs _ (hss ht'))) heq
  · have hss : Ico t₀ b subseteq Ioo a b := Ico_subset_Ioo_left ht.1
    exact ODE_solution_unique_of_mem_Icc_right (fun t ht => hv t (hss ht))
      (hf.mono <| Icc_subset_Icc_left <| le_of_lt ht.1)
      (fun _ ht' => (hf' _ (hss ht')).hasDerivWithinAt) (fun _ ht' => (hfs _ (hss ht')))
      (hg.mono <| Icc_subset_Icc_left <| le_of_lt ht.1)
      (fun _ ht' => (hg' _ (hss ht')).hasDerivWithinAt) (fun _ ht' => (hgs _ (hss ht'))) heq

/--
theorem `ODE_solution_unique_of_mem_Ioo` / 定理 `ODE_solution_unique_of_mem_Ioo`

English:
theorem ODE_solution_unique_of_mem_Ioo
  proof: by
  intro t' ht'
  rcases lt_or_ge t' t₀ with (h | h)
  · have hss : Icc t' t₀ subseteq Ioo a b :=
      fun _ ht'' => ⟨lt_of_lt_of_le ht'.1 ht''.1, lt_of_le_of_lt ht''.2 ht.2⟩
    exact ODE_solution_unique_of_mem_Icc_left
      (fun t'' ht'' => hv t'' ((Ioc_subset_Icc_self.trans hss) ht''))
      

中文:
定理 ODE_solution_unique_of_mem_Ioo
  证明: by
  intro t' ht'
  rcases lt_or_ge t' t₀ with (h | h)
  · have hss : Icc t' t₀ subseteq Ioo a b :=
      fun _ ht'' => ⟨lt_of_lt_of_le ht'.1 ht''.1, lt_of_le_of_lt ht''.2 ht.2⟩
    exact ODE_solution_unique_of_mem_Icc_left
      (fun t'' ht'' => hv t'' ((Ioc_subset_Icc_self.trans hss) ht''))
      

Depends on / 依赖: HasDerivAt, HasDerivAt.continuousOn, Ioc_subset_Icc_self, Ioc_subset_Icc_self.trans, ODE_solution_unique_of_mem_Icc_left, continuousOn, hasDerivWithinAt, lt_of_le_of_lt, lt_of_lt_of_le, lt_or_ge, subseteq
-/
theorem ODE_solution_unique_of_mem_Ioo
    (hv : forall t in Ioo a b, LipschitzOnWith K (v t) (s t))
    (ht : t₀ in Ioo a b)
    (hf : forall t in Ioo a b, HasDerivAt f (v t (f t)) t ∧ f t in s t)
    (hg : forall t in Ioo a b, HasDerivAt g (v t (g t)) t ∧ g t in s t)
    (heq : f t₀ = g t₀) :
    EqOn f g (Ioo a b) := by
  intro t' ht'
  rcases lt_or_ge t' t₀ with (h | h)
  · have hss : Icc t' t₀ subseteq Ioo a b :=
      fun _ ht'' => ⟨lt_of_lt_of_le ht'.1 ht''.1, lt_of_le_of_lt ht''.2 ht.2⟩
    exact ODE_solution_unique_of_mem_Icc_left
      (fun t'' ht'' => hv t'' ((Ioc_subset_Icc_self.trans hss) ht''))
      (HasDerivAt.continuousOn fun _ ht'' => (hf _ <| hss ht'').1)
      (fun _ ht'' => (hf _ <| hss <| Ioc_subset_Icc_self ht'').1.hasDerivWithinAt)
      (fun _ ht'' => (hf _ <| hss <| Ioc_subset_Icc_self ht'').2)
      (HasDerivAt.continuousOn fun _ ht'' => (hg _ <| hss ht'').1)
      (fun _ ht'' => (hg _ <| hss <| Ioc_subset_Icc_self ht'').1.hasDerivWithinAt)
      (fun _ ht'' => (hg _ <| hss <| Ioc_subset_Icc_self ht'').2) heq
      ⟨le_rfl, le_of_lt h⟩
  · have hss : Icc t₀ t' subseteq Ioo a b :=
      fun _ ht'' => ⟨lt_of_lt_of_le ht.1 ht''.1, lt_of_le_of_lt ht''.2 ht'.2⟩
    exact ODE_solution_unique_of_mem_Icc_right
      (fun t'' ht'' => hv t'' ((Ico_subset_Icc_self.trans hss) ht''))
      (HasDerivAt.continuousOn fun _ ht'' => (hf _ <| hss ht'').1)
      (fun _ ht'' => (hf _ <| hss <| Ico_subset_Icc_self ht'').1.hasDerivWithinAt)
      (fun _ ht'' => (hf _ <| hss <| Ico_subset_Icc_self ht'').2)
      (HasDerivAt.continuousOn fun _ ht'' => (hg _ <| hss ht'').1)
      (fun _ ht'' => (hg _ <| hss <| Ico_subset_Icc_self ht'').1.hasDerivWithinAt)
      (fun _ ht'' => (hg _ <| hss <| Ico_subset_Icc_self ht'').2) heq
      ⟨h, le_rfl⟩

/--
theorem `ODE_solution_unique_of_eventually` / 定理 `ODE_solution_unique_of_eventually`

English:
theorem ODE_solution_unique_of_eventually
  proof: by
  obtain ⟨ε, hε, h⟩ := eventually_nhds_iff_ball.mp (hv.and (hf.and hg))
  rw [Filter.eventuallyEq_iff_exists_mem]
  refine ⟨ball t₀ ε, ball_mem_nhds _ hε, ?_⟩
  simp_rw [Real.ball_eq_Ioo] at *
  apply ODE_solution_unique_of_mem_Ioo (fun _ ht => (h _ ht).1)
    (Real.ball_eq_Ioo t₀ ε ▸ mem_ball_se

中文:
定理 ODE_solution_unique_of_eventually
  证明: by
  obtain ⟨ε, hε, h⟩ := eventually_nhds_iff_ball.mp (hv.and (hf.and hg))
  rw [Filter.eventuallyEq_iff_exists_mem]
  refine ⟨ball t₀ ε, ball_mem_nhds _ hε, ?_⟩
  simp_rw [Real.ball_eq_Ioo] at *
  apply ODE_solution_unique_of_mem_Ioo (fun _ ht => (h _ ht).1)
    (Real.ball_eq_Ioo t₀ ε ▸ mem_ball_se

Depends on / 依赖: Filter, Filter.eventuallyEq_iff_exists_mem, ODE_solution_unique_of_mem_Ioo, Real.ball_eq_Ioo, ball_eq_Ioo, ball_mem_nhds, eventuallyEq_iff_exists_mem, eventually_nhds_iff_ball, eventually_nhds_iff_ball.mp, hf.and, hv.and, mem_ball_self, simp_rw
-/
theorem ODE_solution_unique_of_eventually
    (hv : forallᶠ t in 𝓝 t₀, LipschitzOnWith K (v t) (s t))
    (hf : forallᶠ t in 𝓝 t₀, HasDerivAt f (v t (f t)) t ∧ f t in s t)
    (hg : forallᶠ t in 𝓝 t₀, HasDerivAt g (v t (g t)) t ∧ g t in s t)
    (heq : f t₀ = g t₀) : f =ᶠ[𝓝 t₀] g := by
  obtain ⟨ε, hε, h⟩ := eventually_nhds_iff_ball.mp (hv.and (hf.and hg))
  rw [Filter.eventuallyEq_iff_exists_mem]
  refine ⟨ball t₀ ε, ball_mem_nhds _ hε, ?_⟩
  simp_rw [Real.ball_eq_Ioo] at *
  apply ODE_solution_unique_of_mem_Ioo (fun _ ht => (h _ ht).1)
    (Real.ball_eq_Ioo t₀ ε ▸ mem_ball_self hε)
    (fun _ ht => (h _ ht).2.1) (fun _ ht => (h _ ht).2.2) heq

/--
theorem `ODE_solution_unique` / 定理 `ODE_solution_unique`

English:
theorem ODE_solution_unique
  proof: have hfs : forall t in Ico a b, f t in univ := fun _ _ => trivial
  ODE_solution_unique_of_mem_Icc_right (fun t _ => (hv t).lipschitzOnWith) hf hf' hfs hg hg'
    (fun _ _ => trivial) ha

中文:
定理 ODE_solution_unique
  证明: have hfs : forall t in Ico a b, f t in univ := fun _ _ => trivial
  ODE_solution_unique_of_mem_Icc_right (fun t _ => (hv t).lipschitzOnWith) hf hf' hfs hg hg'
    (fun _ _ => trivial) ha

Depends on / 依赖: ODE_solution_unique_of_mem_Icc_right, lipschitzOnWith
-/
theorem ODE_solution_unique
    (hv : forall t, LipschitzWith K (v t))
    (hf : ContinuousOn f (Icc a b))
    (hf' : forall t in Ico a b, HasDerivWithinAt f (v t (f t)) (Ici t) t)
    (hg : ContinuousOn g (Icc a b))
    (hg' : forall t in Ico a b, HasDerivWithinAt g (v t (g t)) (Ici t) t)
    (ha : f a = g a) :
    EqOn f g (Icc a b) :=
  have hfs : forall t in Ico a b, f t in univ := fun _ _ => trivial
  ODE_solution_unique_of_mem_Icc_right (fun t _ => (hv t).lipschitzOnWith) hf hf' hfs hg hg'
    (fun _ _ => trivial) ha

/--
theorem `ODE_solution_unique_univ` / 定理 `ODE_solution_unique_univ`

English:
theorem ODE_solution_unique_univ
  proof: by
  ext t
  obtain ⟨A, B, Ht, Ht₀⟩ : exists A B, t in Set.Ioo A B ∧ t₀ in Set.Ioo A B := by
    use (min (-|t|) (-|t₀|) - 1), (max |t| |t₀| + 1)
    grind
  exact ODE_solution_unique_of_mem_Ioo
    (fun t _ => hv t) Ht₀ (fun t _ => hf t) (fun t _ => hg t) heq Ht

中文:
定理 ODE_solution_unique_univ
  证明: by
  ext t
  obtain ⟨A, B, Ht, Ht₀⟩ : exists A B, t in Set.Ioo A B ∧ t₀ in Set.Ioo A B := by
    use (min (-|t|) (-|t₀|) - 1), (max |t| |t₀| + 1)
    grind
  exact ODE_solution_unique_of_mem_Ioo
    (fun t _ => hv t) Ht₀ (fun t _ => hf t) (fun t _ => hg t) heq Ht

Depends on / 依赖: ODE_solution_unique_of_mem_Ioo, Set.Ioo
-/
theorem ODE_solution_unique_univ
    (hv : forall t, LipschitzOnWith K (v t) (s t))
    (hf : forall t, HasDerivAt f (v t (f t)) t ∧ f t in s t)
    (hg : forall t, HasDerivAt g (v t (g t)) t ∧ g t in s t)
    (heq : f t₀ = g t₀) : f = g := by
  ext t
  obtain ⟨A, B, Ht, Ht₀⟩ : exists A B, t in Set.Ioo A B ∧ t₀ in Set.Ioo A B := by
    use (min (-|t|) (-|t₀|) - 1), (max |t| |t₀| + 1)
    grind
  exact ODE_solution_unique_of_mem_Ioo
    (fun t _ => hv t) Ht₀ (fun t _ => hf t) (fun t _ => hg t) heq Ht
