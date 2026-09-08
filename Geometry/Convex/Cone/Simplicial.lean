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

/-- A pointed cone is simplicial if it equals the conic hull of a finite set that is linearly
independent over `R`. -/
/-
**PointedCone.IsSimplicial** 是 Mathlib 中的一个定义，位于命名空间 `PointedCone`。
形式化陈述：IsSimplicial : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pointed cone is simplicial if it equals the conic hull of a finite set that is
 linearly
independent over `R`.
-/
def IsSimplicial : Prop :=
  ∃ s : Set M, s.Finite ∧ LinearIndepOn R id s ∧ hull R s = C

namespace IsSimplicial

/-- The conic hull of a finite linearly independent set is simplicial. -/
/-
**PointedCone.IsSimplicial.hull** 是 Mathlib 中的一个定理，位于命名空间 `PointedCone.IsSimplic
ial`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsOrderedRing R]   [inst_3 : AddCommMonoid M] [inst_4 : _root_.Mod
ule R M] {s : Set M},   s.Finite → LinearIndepOn R id s → (PointedCone.hull R s)
.IsSimplicial
参数：PointedCone.hull R s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The conic hull of a finite linearly independent set is simplicial.
-/
protected theorem hull {s : Set M} (hs : s.Finite) (hli : LinearIndepOn R id s) :
    (PointedCone.hull R s).IsSimplicial := ⟨s, hs, hli, rfl⟩

end IsSimplicial

end PointedCone

