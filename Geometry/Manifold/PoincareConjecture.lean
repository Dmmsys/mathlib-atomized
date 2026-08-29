/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected -- shake: keep (`p_w`)
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.Util.Superscript

/-!
# Statement of the generalized Poincaré conjecture

https://en.wikipedia.org/wiki/Generalized_Poincar%C3%A9_conjecture

The mathlib notation `≃ₕ` stands for a homotopy equivalence, `≃ₜ` stands for a homeomorphism,
and `≃ₘ⟮𝓡 n, 𝓡 n⟯` stands for a diffeomorphism, where `𝓡 n` is the `n`-dimensional Euclidean
space viewed as a model space.
-/

@[expose] public section

open scoped Manifold ContDiff
open Metric (sphere)

local macro:max "Real" noWs n:superscript(term) : term => `(EuclideanSpace Real (Fin $(⟨n.raw[0]⟩)))
local macro:max "𝕊" noWs n:superscript(term) : term =>
  `(sphere (0 : EuclideanSpace Real (Fin ($(⟨n.raw[0]⟩) + 1))) 1)

variable (M : Type*) [TopologicalSpace M]

open ContinuousMap

/-- The generalized topological Poincaré conjecture.
- For n = 2 it follows from the classification of surfaces.
- For n ≥ 5 it was proven by Stephen Smale in 1961 assuming M admits a smooth structure;
  Newman (1966) and Connell (1967) proved it without the condition.
- For n = 4 it was proven by Michael Freedman in 1982.
- For n = 3 it was proven by Grigori Perelman in 2003. -/
proof_wanted ContinuousMap.HomotopyEquiv.nonempty_homeomorph_sphere [T2Space M]
    (n : Nat) [ChartedSpace Realⁿ M] : M ≃ₕ 𝕊ⁿ -> Nonempty (M ≃ₜ 𝕊ⁿ)

/-- The 3-dimensional topological Poincaré conjecture (proven by Perelman) -/
proof_wanted SimplyConnectedSpace.nonempty_homeomorph_sphere_three
    [T2Space M] [ChartedSpace Real³ M] [SimplyConnectedSpace M] [CompactSpace M] :
    Nonempty (M ≃ₜ 𝕊³)

/-- The 3-dimensional smooth Poincaré conjecture (proven by Perelman) -/
proof_wanted SimplyConnectedSpace.nonempty_sdiffeomorph_sphere_three
    [T2Space M] [ChartedSpace Real³ M] [IsManifold (𝓡 3) ∞ M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ 𝕊³)

/--
Definition of `ContinuousMap.HomotopyEquiv.NonemptyDiffeomorphSphere` / `ContinuousMap.HomotopyEquiv.NonemptyDiffeomorphSphere` 的定义

English:
definition ContinuousMap.HomotopyEquiv.NonemptyDiffeomorphSphere
  signature: (n : Nat)
  body: forall (_ : ChartedSpace Realⁿ M) (_ : IsManifold (𝓡 n) ∞ M),
    M ≃ₕ 𝕊ⁿ -> Nonempty (M ≃ₘ⟮𝓡 n, 𝓡 n⟯ 𝕊ⁿ)

中文:
定义 ContinuousMap.HomotopyEquiv.NonemptyDiffeomorphSphere
  签名: (n : 自然数)
  定义体: forall (_ : ChartedSpace Realⁿ M) (_ : IsManifold (𝓡 n) ∞ M),
    M ≃ₕ 𝕊ⁿ -> Nonempty (M ≃ₘ⟮𝓡 n, 𝓡 n⟯ 𝕊ⁿ)

Depends on / 依赖: ChartedSpace, IsManifold, Nonempty
-/
def ContinuousMap.HomotopyEquiv.NonemptyDiffeomorphSphere (n : Nat) : Prop :=
  forall (_ : ChartedSpace Realⁿ M) (_ : IsManifold (𝓡 n) ∞ M),
    M ≃ₕ 𝕊ⁿ -> Nonempty (M ≃ₘ⟮𝓡 n, 𝓡 n⟯ 𝕊ⁿ)

/-- The existence of an exotic 7-sphere (due to John Milnor) -/
proof_wanted exists_homeomorph_isEmpty_diffeomorph_sphere_seven :
    exists (M : Type) (_ : TopologicalSpace M) (_ : ChartedSpace Real⁷ M)
      (_ : IsManifold (𝓡 7) ∞ M) (_homeo : M ≃ₜ 𝕊⁷),
      IsEmpty (M ≃ₘ⟮𝓡 7, 𝓡 7⟯ 𝕊⁷)

/-- The existence of a small exotic ℝ⁴, i.e. an open subset of ℝ⁴ that is homeomorphic but
not diffeomorphic to ℝ⁴. See https://en.wikipedia.org/wiki/Exotic_R4. -/
proof_wanted exists_open_nonempty_homeomorph_isEmpty_diffeomorph_euclideanSpace_four :
    exists M : TopologicalSpace.Opens Real⁴, Nonempty (M ≃ₜ Real⁴) ∧ IsEmpty (M ≃ₘ⟮𝓡 4, 𝓡 4⟯ Real⁴)
