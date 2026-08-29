/-
Copyright (c) 2025 Bjørn Solheim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Solheim
-/
module

public import Mathlib.Geometry.Convex.Cone.Pointed

/-!
# Simplicial cones

A **simplicial cone** is a pointed convex cone that equals the conic hull of a finite linearly
independent set of vectors. We do not require that the generators span the ambient module.
However, when the cone is also generating, its generators linearly span the module.

## Main definitions

* `PointedCone.IsSimplicial`: A pointed cone is simplicial if it equals the conic hull of a finite
  linearly independent set.

## Results

* `PointedCone.IsSimplicial.span`: The conic hull of a linearly independent finite set is
  simplicial.

## References

* [Aubrun et al. *Entangleability of cones*][aubrunEntangleabilityCones2021]
-/

@[expose] public section

variable {R M : Type*}
variable [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommMonoid M] [Module R M]
variable (C : PointedCone R M)

namespace PointedCone

/--
Definition of `IsSimplicial` / `IsSimplicial` 的定义

English:
definition IsSimplicial
  signature: : Prop
  body: exists s : Set M, s.Finite ∧ LinearIndepOn R id s ∧ hull R s = C

中文:
定义 IsSimplicial
  签名: : 命题
  定义体: exists s : Set M, s.Finite ∧ LinearIndepOn R id s ∧ hull R s = C

Depends on / 依赖: Finite, LinearIndepOn, s.Finite
-/
def IsSimplicial : Prop :=
  exists s : Set M, s.Finite ∧ LinearIndepOn R id s ∧ hull R s = C

namespace IsSimplicial

/--
theorem `hull` / 定理 `hull`

English:
theorem hull
  given: {s : Set M} (hs : s.Finite) (hli : LinearIndepOn R id s)
  proof: ⟨s, hs, hli, rfl⟩

中文:
定理 hull
  条件: {s : 集合 M} (hs : s.有限) (hli : LinearIndepOn R id s)
  证明: ⟨s, hs, hli, rfl⟩
-/
protected theorem hull {s : Set M} (hs : s.Finite) (hli : LinearIndepOn R id s) :
    (PointedCone.hull R s).IsSimplicial := ⟨s, hs, hli, rfl⟩

end IsSimplicial

end PointedCone
