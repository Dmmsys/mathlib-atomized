/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang
-/
module

public import Mathlib.Analysis.Calculus.Conformal.NormedSpace
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-!
# Angles and conformal maps

This file proves that conformal maps preserve angles.

-/

public section


namespace InnerProductGeometry

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace Real E] [InnerProductSpace Real F]

/--
theorem `IsConformalMap.preserves_angle` / 定理 `IsConformalMap.preserves_angle`

English:
theorem IsConformalMap.preserves_angle
  given: {f' : E ->L[Real] F} (h : IsConformalMap f') (u v : E)
  proof: by
  obtain ⟨c, hc, li, rfl⟩ := h
  exact (angle_smul_smul hc _ _).trans (li.angle_map _ _)

中文:
定理 IsConformalMap.preserves_angle
  条件: {f' : E ->L[实数] F} (h : IsConformalMap f') (u v : E)
  证明: by
  obtain ⟨c, hc, li, rfl⟩ := h
  exact (angle_smul_smul hc _ _).trans (li.angle_map _ _)

Depends on / 依赖: angle_map, angle_smul_smul, li.angle_map
-/
theorem IsConformalMap.preserves_angle {f' : E ->L[Real] F} (h : IsConformalMap f') (u v : E) :
    angle (f' u) (f' v) = angle u v := by
  obtain ⟨c, hc, li, rfl⟩ := h
  exact (angle_smul_smul hc _ _).trans (li.angle_map _ _)

/--
theorem `ConformalAt.preserves_angle` / 定理 `ConformalAt.preserves_angle`

English:
theorem ConformalAt.preserves_angle
  statement: {f : E -> F} {x : E} {f' : E ->L[Real] F} (h : HasFDerivAt f f' x)
  proof: let ⟨_, h₁, c⟩ := H
  h₁.unique h ▸ IsConformalMap.preserves_angle c u v

中文:
定理 ConformalAt.preserves_angle
  结论: {f : E -> F} {x : E} {f' : E ->L[实数] F} (h : 在点处Fréchet可导 f f' x)
  证明: let ⟨_, h₁, c⟩ := H
  h₁.unique h ▸ IsConformalMap.preserves_angle c u v

Depends on / 依赖: IsConformalMap, IsConformalMap.preserves_angle, preserves_angle, unique
-/
theorem ConformalAt.preserves_angle {f : E -> F} {x : E} {f' : E ->L[Real] F} (h : HasFDerivAt f f' x)
    (H : ConformalAt f x) (u v : E) : angle (f' u) (f' v) = angle u v :=
  let ⟨_, h₁, c⟩ := H
  h₁.unique h ▸ IsConformalMap.preserves_angle c u v

end InnerProductGeometry
