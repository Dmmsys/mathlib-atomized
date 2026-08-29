/-
Copyright (c) 2024 Elliot Dean Young and Jiazhen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhen Xia, Elliot Dean Young
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Category.TopCat.EpiMono

/-!
# Euclidean spheres

This file defines the `n`-sphere `𝕊 n`, the `n`-disk `𝔻 n`, its boundary `∂𝔻 n` and its interior
`𝔹 n` as objects in `TopCat`.

-/

@[expose] public section

universe u

namespace TopCat
open CategoryTheory

/--
Definition of `disk` / `disk` 的定义

English:
definition disk
  signature: (n : Nat)
  body: TopCat.of ULift Metric.closedBall (0 : EuclideanSpace Real (Fin n)) 1

中文:
定义 disk
  签名: (n : 自然数)
  定义体: TopCat.of ULift Metric.closedBall (0 : EuclideanSpace Real (Fin n)) 1

Depends on / 依赖: EuclideanSpace, Metric, Metric.closedBall, TopCat, TopCat.of, closedBall
-/
noncomputable def disk (n : Nat) : TopCat.{u} :=
TopCat.of ULift Metric.closedBall (0 : EuclideanSpace Real (Fin n)) 1

/--
Definition of `diskBoundary` / `diskBoundary` 的定义

English:
definition diskBoundary
  signature: (n : Nat)
  body: TopCat.of ULift Metric.sphere (0 : EuclideanSpace Real (Fin n)) 1

中文:
定义 diskBoundary
  签名: (n : 自然数)
  定义体: TopCat.of ULift Metric.sphere (0 : EuclideanSpace Real (Fin n)) 1

Depends on / 依赖: EuclideanSpace, Metric, Metric.sphere, TopCat, TopCat.of, sphere
-/
noncomputable def diskBoundary (n : Nat) : TopCat.{u} :=
TopCat.of ULift Metric.sphere (0 : EuclideanSpace Real (Fin n)) 1

/--
Definition of `sphere` / `sphere` 的定义

English:
definition sphere
  signature: (n : Nat)
  body: diskBoundary (n + 1)

中文:
定义 sphere
  签名: (n : 自然数)
  定义体: diskBoundary (n + 1)

Depends on / 依赖: diskBoundary
-/
noncomputable def sphere (n : Nat) : TopCat.{u} :=
  diskBoundary (n + 1)

/--
Definition of `ball` / `ball` 的定义

English:
definition ball
  signature: (n : Nat)
  body: TopCat.of ULift Metric.ball (0 : EuclideanSpace Real (Fin n)) 1

中文:
定义 ball
  签名: (n : 自然数)
  定义体: TopCat.of ULift Metric.ball (0 : EuclideanSpace Real (Fin n)) 1

Depends on / 依赖: EuclideanSpace, Metric, Metric.ball, TopCat, TopCat.of
-/
noncomputable def ball (n : Nat) : TopCat.{u} :=
TopCat.of ULift Metric.ball (0 : EuclideanSpace Real (Fin n)) 1

/-- `𝔻 n` denotes the `n`-disk. -/
scoped prefix:arg "𝔻 " => disk

/-- `∂𝔻 n` denotes the boundary of the `n`-disk. -/
scoped prefix:arg "∂𝔻 " => diskBoundary

/-- `𝕊 n` denotes the `n`-sphere. -/
scoped prefix:arg "𝕊 " => sphere

/-- `𝔹 n` denotes the `n`-ball, the interior of the `n`-disk. -/
scoped prefix:arg "𝔹 " => ball

/--
Definition of `diskBoundaryInclusion` / `diskBoundaryInclusion` 的定义

English:
definition diskBoundaryInclusion
  signature: (n : Nat)
  body: ofHom
    { toFun := fun ⟨p, hp⟩ => ⟨p, le_of_eq hp⟩
      continuous_toFun := ⟨fun t ⟨s, ⟨r, hro, hrs⟩, hst⟩ => by
        rw [isOpen_induced_iff]; rw [← hst]; rw [← hrs]
        tauto⟩ }

中文:
定义 diskBoundaryInclusion
  签名: (n : 自然数)
  定义体: ofHom
    { toFun := fun ⟨p, hp⟩ => ⟨p, le_of_eq hp⟩
      continuous_toFun := ⟨fun t ⟨s, ⟨r, hro, hrs⟩, hst⟩ => by
        rw [isOpen_induced_iff]; rw [← hst]; rw [← hrs]
        tauto⟩ }

Depends on / 依赖: continuous_toFun, isOpen_induced_iff, le_of_eq
-/
def diskBoundaryInclusion (n : Nat) : ∂𝔻 n ⟶ 𝔻 n :=
  ofHom
    { toFun := fun ⟨p, hp⟩ => ⟨p, le_of_eq hp⟩
      continuous_toFun := ⟨fun t ⟨s, ⟨r, hro, hrs⟩, hst⟩ => by
        rw [isOpen_induced_iff]; rw [← hst]; rw [← hrs]
        tauto⟩ }

/--
Definition of `ballInclusion` / `ballInclusion` 的定义

English:
definition ballInclusion
  signature: (n : Nat)
  body: ofHom
    { toFun := fun ⟨p, hp⟩ => ⟨p, Metric.ball_subset_closedBall hp⟩
      continuous_toFun := ⟨fun t ⟨s, ⟨r, hro, hrs⟩, hst⟩ => by
        rw [isOpen_induced_iff]; rw [← hst]; rw [← hrs]
        tauto⟩ }

中文:
定义 ballInclusion
  签名: (n : 自然数)
  定义体: ofHom
    { toFun := fun ⟨p, hp⟩ => ⟨p, Metric.ball_subset_closedBall hp⟩
      continuous_toFun := ⟨fun t ⟨s, ⟨r, hro, hrs⟩, hst⟩ => by
        rw [isOpen_induced_iff]; rw [← hst]; rw [← hrs]
        tauto⟩ }

Depends on / 依赖: Metric, Metric.ball_subset_closedBall, ball_subset_closedBall, continuous_toFun, isOpen_induced_iff
-/
def ballInclusion (n : Nat) : 𝔹 n ⟶ 𝔻 n :=
  ofHom
    { toFun := fun ⟨p, hp⟩ => ⟨p, Metric.ball_subset_closedBall hp⟩
      continuous_toFun := ⟨fun t ⟨s, ⟨r, hro, hrs⟩, hst⟩ => by
        rw [isOpen_induced_iff]; rw [← hst]; rw [← hrs]
        tauto⟩ }

set_option backward.isDefEq.respectTransparency false in
.mpr by instance {n : Nat} : Mono (diskBoundaryInclusion n) := mono_iff_injective _
  intro ⟨x, hx⟩ ⟨y, hy⟩ h
  obtain rfl : x = y := by simpa [diskBoundaryInclusion, disk] using h
  congr

set_option backward.isDefEq.respectTransparency false in
.mpr by instance {n : Nat} : Mono (ballInclusion n) := TopCat.mono_iff_injective _
  intro ⟨x, hx⟩ ⟨y, hy⟩ h
  obtain rfl : x = y := by simpa [ballInclusion, disk] using h
  congr

instance (n : Nat) : CompactSpace (𝔻 n) := by
  convert! Homeomorph.compactSpace Homeomorph.ulift.symm
  infer_instance

instance (n : Nat) : CompactSpace (∂𝔻 n) := by
  convert! Homeomorph.compactSpace Homeomorph.ulift.symm
  infer_instance

end TopCat
