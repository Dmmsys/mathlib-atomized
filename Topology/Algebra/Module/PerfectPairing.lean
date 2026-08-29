/-
Copyright (c) 2025 Yaël Dillies, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Andrew Yang
-/
module

public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Continuous perfect pairings

This file defines continuous perfect pairings.

For a topological ring `R` and two topological modules `M` and `N`, a continuous perfect pairing is
a continuous bilinear map `M × N → R` that is bijective in both arguments.

We require continuity in the forward direction only so that we can put several different topologies
on the continuous dual (e.g., strong, weak, weak-\*). For example, if `M` is weakly reflexive then
there is a continuous perfect pairing between `M` and `WeakDual R M`, even though the map
`WeakDual R M ≃ₗ[R] StrongDual R M` (where `StrongDual R M` is equipped with its strong topology) is
not in general a homeomorphism.

## TODO

Adapt `PerfectPairing` to this Prop-valued typeclass paradigm
-/

@[expose] public section

open Function

namespace LinearMap
variable {R M N : Type*}
  [CommRing R] [TopologicalSpace R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [AddCommGroup N] [Module R N] [TopologicalSpace N] (p : M ->ₗ[R] N ->ₗ[R] R) {x : M} {y : N}

/-- For a topological ring `R` and two topological modules `M` and `N`, a continuous perfect pairing
is a continuous bilinear map `M × N → R` that is bijective in both arguments.

We require continuity in the forward direction only so that we can put several different topologies
on the continuous dual: strong, weak, weak-\* topology... -/
@[ext]
/--
Definition of `IsContPerfPair` / `IsContPerfPair` 的定义

English:
class IsContPerfPair
  parameters: (p : M ->ₗ[R] N ->ₗ[R] R)
  axioms and operations (2):
    - continuous_uncurry((p)) : Continuous fun (x, y) => p x y
    - bijective_left((p))

中文:
类 IsContPerfPair
  参数: (p : M ->ₗ[R] N ->ₗ[R] R)
  公理与运算 (2 个):
    - continuous_uncurry((p)) : Continuous fun (x, y) => p x y
    - bijective_left((p))

Depends on / 依赖: IsContPerfPair, IsContPerfPair.continuous_uncurry, continuous_uncurry
-/
class IsContPerfPair (p : M ->ₗ[R] N ->ₗ[R] R) where
  continuous_uncurry (p) : Continuous fun (x, y) => p x y
  bijective_left (p) :
Bijective fun x => ContinuousLinearMap.mk (p x) continuous_uncurry.comp .prodMk_right x
  bijective_right (p) :
Bijective fun y => ContinuousLinearMap.mk (p.flip y) continuous_uncurry.comp .prodMk_left y

variable [p.IsContPerfPair]

alias continuous_uncurry_of_isContPerfPair :=
  IsContPerfPair.continuous_uncurry

/--
Instance `flip.instIsContPerfPair` / 实例 `flip.instIsContPerfPair`

English:
instance flip.instIsContPerfPair
  signature: : p.flip.IsContPerfPair where
  body: p.continuous_uncurry_of_isContPerfPair.comp continuous_swap
  bijective_left := IsContPerfPair.bijective_right p
  bijective_right := IsContPerfPair.bijective_left p

中文:
实例 flip.instIsContPerfPair
  签名: : p.flip.IsContPerfPair where
  定义体: p.continuous_uncurry_of_isContPerfPair.comp continuous_swap
  bijective_left := IsContPerfPair.bijective_right p
  bijective_right := IsContPerfPair.bijective_left p

Depends on / 依赖: continuous_swap, continuous_uncurry_of_isContPerfPair, p.continuous_uncurry_of_isContPerfPair.comp
-/
instance flip.instIsContPerfPair : p.flip.IsContPerfPair where
  continuous_uncurry := p.continuous_uncurry_of_isContPerfPair.comp continuous_swap
  bijective_left := IsContPerfPair.bijective_right p
  bijective_right := IsContPerfPair.bijective_left p

/--
lemma `continuous_of_isContPerfPair` / 引理 `continuous_of_isContPerfPair`

English:
lemma continuous_of_isContPerfPair
  statement: Continuous (p x)
  proof: p.continuous_uncurry_of_isContPerfPair.comp .prodMk_right x

中文:
引理 continuous_of_isContPerfPair
  结论: Continuous (p x)
  证明: p.continuous_uncurry_of_isContPerfPair.comp .prodMk_right x

Depends on / 依赖: continuous_uncurry_of_isContPerfPair, p.continuous_uncurry_of_isContPerfPair.comp, prodMk_right
-/
lemma continuous_of_isContPerfPair : Continuous (p x) :=
p.continuous_uncurry_of_isContPerfPair.comp .prodMk_right x

variable [IsTopologicalRing R]

/--
Definition of `toContPerfPair` / `toContPerfPair` 的定义

English:
definition toContPerfPair
  signature: : M ≃ₗ[R] StrongDual R N
  body: .ofBijective { toFun := _, map_add' x y := by ext; simp, map_smul' r x := by ext; simp }
    IsContPerfPair.bijective_left p

中文:
定义 toContPerfPair
  签名: : M ≃ₗ[R] StrongDual R N
  定义体: .ofBijective { toFun := _, map_add' x y := by ext; simp, map_smul' r x := by ext; simp }
    IsContPerfPair.bijective_left p

Depends on / 依赖: IsContPerfPair, IsContPerfPair.bijective_left, bijective_left, map_add, map_smul, ofBijective
-/
noncomputable def toContPerfPair : M ≃ₗ[R] StrongDual R N :=
.ofBijective { toFun := _, map_add' x y := by ext; simp, map_smul' r x := by ext; simp }
    IsContPerfPair.bijective_left p

/--
lemma `toLinearMap_toContPerfPair` / 引理 `toLinearMap_toContPerfPair`

English:
lemma toLinearMap_toContPerfPair
  given: (x : M)
  statement: p.toContPerfPair x = p x
  proof: rfl

中文:
引理 toLinearMap_toContPerfPair
  条件: (x : M)
  结论: p.toContPerfPair x = p x
  证明: rfl
-/
@[simp] lemma toLinearMap_toContPerfPair (x : M) : p.toContPerfPair x = p x := rfl
/--
lemma `toContPerfPair_apply` / 引理 `toContPerfPair_apply`

English:
lemma toContPerfPair_apply
  given: (x : M) (y : N)
  statement: p.toContPerfPair x y = p x y
  proof: rfl

中文:
引理 toContPerfPair_apply
  条件: (x : M) (y : N)
  结论: p.toContPerfPair x y = p x y
  证明: rfl
-/
@[simp] lemma toContPerfPair_apply (x : M) (y : N) : p.toContPerfPair x y = p x y := rfl

end LinearMap
