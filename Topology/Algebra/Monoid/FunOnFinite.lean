/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.LinearAlgebra.Finsupp.Pi

/-!
# Continuity of the functoriality of `X → M` when `X` is finite

-/

public section

namespace FunOnFinite

/--
lemma `continuous_map` / 引理 `continuous_map`

English:
lemma continuous_map
  proof: by
  classical
  have := Fintype.ofFinite X
  refine continuous_pi (fun y => ?_)
  simp only [FunOnFinite.map_apply_apply]
  exact continuous_finsetSum _ (fun _ _ => continuous_apply _)

中文:
引理 continuous_map
  证明: by
  classical
  have := Fintype.ofFinite X
  refine continuous_pi (fun y => ?_)
  simp only [FunOnFinite.map_apply_apply]
  exact continuous_finsetSum _ (fun _ _ => continuous_apply _)

Depends on / 依赖: Fintype, Fintype.ofFinite, FunOnFinite, FunOnFinite.map_apply_apply, classical, continuous_apply, continuous_finsetSum, continuous_pi, map_apply_apply, ofFinite
-/
lemma continuous_map
    (M : Type*) [AddCommMonoid M] [TopologicalSpace M] [ContinuousAdd M]
    {X Y : Type*} [Finite X] [Finite Y] (f : X -> Y) :
    Continuous (FunOnFinite.map (M := M) f) := by
  classical
  have := Fintype.ofFinite X
  refine continuous_pi (fun y => ?_)
  simp only [FunOnFinite.map_apply_apply]
  exact continuous_finsetSum _ (fun _ _ => continuous_apply _)

/--
lemma `continuous_linearMap` / 引理 `continuous_linearMap`

English:
lemma continuous_linearMap
  proof: FunOnFinite.continuous_map _ _

中文:
引理 continuous_linearMap
  证明: FunOnFinite.continuous_map _ _

Depends on / 依赖: FunOnFinite, FunOnFinite.continuous_map, continuous_map
-/
lemma continuous_linearMap
    (R M : Type*) [Semiring R] [AddCommMonoid M]
    [Module R M] [TopologicalSpace M] [ContinuousAdd M]
    {X Y : Type*} [Finite X] [Finite Y] (f : X -> Y) :
    Continuous (FunOnFinite.linearMap R M f) :=
  FunOnFinite.continuous_map _ _

end FunOnFinite
