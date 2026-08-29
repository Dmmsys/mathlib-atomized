/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Johannes Hölzl
-/
module

public import Mathlib.Dynamics.FixedPoints.Basic
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Topological properties of fixed points

Currently this file contains two lemmas:

- `isFixedPt_of_tendsto_iterate`: if `f^n(x) → y` and `f` is continuous at `y`, then `f y = y`;
- `isClosed_fixedPoints`: the set of fixed points of a continuous map is a closed set.

## TODO

fixed points, iterates
-/

public section


variable {α : Type*} [TopologicalSpace α] [T2Space α] {f : α -> α}

open Function Filter

open Topology

/--
theorem `isFixedPt_of_tendsto_iterate` / 定理 `isFixedPt_of_tendsto_iterate`

English:
theorem isFixedPt_of_tendsto_iterate
  statement: {x y : α} (hy : Tendsto (fun n => f^[n] x) atTop (𝓝 y))
  proof: by
  refine tendsto_nhds_unique ((tendsto_add_atTop_iff_nat 1).1 ?_) hy
  simp only [iterate_succ' f]
  exact hf.tendsto.comp hy

中文:
定理 isFixedPt_of_tendsto_iterate
  结论: {x y : α} (hy : Tendsto (fun n => f^[n] x) atTop (𝓝 y))
  证明: by
  refine tendsto_nhds_unique ((tendsto_add_atTop_iff_nat 1).1 ?_) hy
  simp only [iterate_succ' f]
  exact hf.tendsto.comp hy

Depends on / 依赖: hf.tendsto.comp, iterate_succ, tendsto, tendsto_add_atTop_iff_nat, tendsto_nhds_unique
-/
theorem isFixedPt_of_tendsto_iterate {x y : α} (hy : Tendsto (fun n => f^[n] x) atTop (𝓝 y))
    (hf : ContinuousAt f y) : IsFixedPt f y := by
  refine tendsto_nhds_unique ((tendsto_add_atTop_iff_nat 1).1 ?_) hy
  simp only [iterate_succ' f]
  exact hf.tendsto.comp hy

/--
theorem `isClosed_fixedPoints` / 定理 `isClosed_fixedPoints`

English:
theorem isClosed_fixedPoints
  given: (hf : Continuous f)
  statement: IsClosed (fixedPoints f)
  proof: isClosed_eq hf continuous_id

中文:
定理 isClosed_fixedPoints
  条件: (hf : Continuous f)
  结论: IsClosed (fixedPoints f)
  证明: isClosed_eq hf continuous_id

Depends on / 依赖: continuous_id, isClosed_eq
-/
theorem isClosed_fixedPoints (hf : Continuous f) : IsClosed (fixedPoints f) :=
  isClosed_eq hf continuous_id
