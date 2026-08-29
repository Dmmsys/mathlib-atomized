/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.LinearAlgebra.Basis.Cardinality
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Dimension.Subsingleton
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# Linear algebra properties of `FreeAlgebra R X`

This file provides a `FreeMonoid X` basis on the `FreeAlgebra R X`, and uses it to show the
dimension of the algebra is the cardinality of `List X`
-/

@[expose] public section

open Module

universe u v

namespace FreeAlgebra

variable (R : Type u) (X : Type v)

section
variable [CommSemiring R]

-- @[simps]
/--
Definition of `basisFreeMonoid` / `basisFreeMonoid` 的定义

English:
definition basisFreeMonoid
  signature: : Basis (FreeMonoid X) R (FreeAlgebra R X)
  body: Finsupp.basisSingleOne.map
    (equivMonoidAlgebraFreeMonoid.toLinearEquiv.trans <| MonoidAlgebra.coeffLinearEquiv _).symm

中文:
定义 basisFreeMonoid
  签名: : Basis (FreeMonoid X) R (FreeAlgebra R X)
  定义体: Finsupp.basisSingleOne.map
    (equivMonoidAlgebraFreeMonoid.toLinearEquiv.trans <| MonoidAlgebra.coeffLinearEquiv _).symm

Depends on / 依赖: Finsupp, Finsupp.basisSingleOne.map, MonoidAlgebra, MonoidAlgebra.coeffLinearEquiv, basisSingleOne, coeffLinearEquiv, equivMonoidAlgebraFreeMonoid, equivMonoidAlgebraFreeMonoid.toLinearEquiv.trans, toLinearEquiv
-/
noncomputable def basisFreeMonoid : Basis (FreeMonoid X) R (FreeAlgebra R X) :=
  Finsupp.basisSingleOne.map
    (equivMonoidAlgebraFreeMonoid.toLinearEquiv.trans <| MonoidAlgebra.coeffLinearEquiv _).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module.Free R (FreeAlgebra R X)
  body: .of_equiv equivMonoidAlgebraFreeMonoid.symm.toLinearEquiv

中文:
实例 :
  签名: Module.Free R (FreeAlgebra R X)
  定义体: .of_equiv equivMonoidAlgebraFreeMonoid.symm.toLinearEquiv

Depends on / 依赖: equivMonoidAlgebraFreeMonoid, equivMonoidAlgebraFreeMonoid.symm.toLinearEquiv, of_equiv, toLinearEquiv
-/
instance : Module.Free R (FreeAlgebra R X) :=
  .of_equiv equivMonoidAlgebraFreeMonoid.symm.toLinearEquiv

end

/--
theorem `rank_eq` / 定理 `rank_eq`

English:
theorem rank_eq
  given: [CommRing R] [Nontrivial R]
  proof: by
  rw [← (Basis.mk_eq_rank'.{_]; rw [_]; rw [_]; rw [u} (basisFreeMonoid R X)).trans (Cardinal.lift_id _)]; rw [Cardinal.lift_umax.{v]; rw [u}]; rw [FreeMonoid]

中文:
定理 rank_eq
  条件: [CommRing R] [Nontrivial R]
  证明: by
  rw [← (Basis.mk_eq_rank'.{_]; rw [_]; rw [_]; rw [u} (basisFreeMonoid R X)).trans (Cardinal.lift_id _)]; rw [Cardinal.lift_umax.{v]; rw [u}]; rw [FreeMonoid]

Depends on / 依赖: Basis.mk_eq_rank, Cardinal, Cardinal.lift_id, Cardinal.lift_umax, FreeMonoid, basisFreeMonoid, lift_id, lift_umax, mk_eq_rank
-/
theorem rank_eq [CommRing R] [Nontrivial R] :
    Module.rank R (FreeAlgebra R X) = Cardinal.lift.{u} (Cardinal.mk (List X)) := by
  rw [← (Basis.mk_eq_rank'.{_]; rw [_]; rw [_]; rw [u} (basisFreeMonoid R X)).trans (Cardinal.lift_id _)]; rw [Cardinal.lift_umax.{v]; rw [u}]; rw [FreeMonoid]

end FreeAlgebra

open Cardinal

/--
theorem `Algebra.rank_adjoin_le` / 定理 `Algebra.rank_adjoin_le`

English:
theorem Algebra.rank_adjoin_le
  statement: {R : Type u} {S : Type v} [CommRing R] [Ring S] [Algebra R S]
  proof: by
  rw [adjoin_eq_range_freeAlgebra_lift]
  cases subsingleton_or_nontrivial R
  · rw [rank_subsingleton]; exact one_le_aleph0.trans (le_max_right _ _)
  rw [← lift_le.{max u v}]
  refine (lift_rank_range_le (FreeAlgebra.lift R ((↑) : s -> S)).toLinearMap).trans ?_
  rw [FreeAlgebra.rank_eq]; rw [l

中文:
定理 Algebra.rank_adjoin_le
  结论: {R : 类型u} {S : 类型v} [CommRing R] [Ring S] [Algebra R S]
  证明: by
  rw [adjoin_eq_range_freeAlgebra_lift]
  cases subsingleton_or_nontrivial R
  · rw [rank_subsingleton]; exact one_le_aleph0.trans (le_max_right _ _)
  rw [← lift_le.{max u v}]
  refine (lift_rank_range_le (FreeAlgebra.lift R ((↑) : s -> S)).toLinearMap).trans ?_
  rw [FreeAlgebra.rank_eq]; rw [l

Depends on / 依赖: FreeAlgebra, FreeAlgebra.lift, FreeAlgebra.rank_eq, adjoin_eq_range_freeAlgebra_lift, le_max_right, lift_id, lift_le, lift_rank_range_le, lift_umax, max_comm, mk_list_le_max, one_le_aleph0, one_le_aleph0.trans, rank_eq, rank_subsingleton, subsingleton_or_nontrivial, toLinearMap
-/
theorem Algebra.rank_adjoin_le {R : Type u} {S : Type v} [CommRing R] [Ring S] [Algebra R S]
    (s : Set S) : Module.rank R (adjoin R s) <= max #s ℵ₀ := by
  rw [adjoin_eq_range_freeAlgebra_lift]
  cases subsingleton_or_nontrivial R
  · rw [rank_subsingleton]; exact one_le_aleph0.trans (le_max_right _ _)
  rw [← lift_le.{max u v}]
  refine (lift_rank_range_le (FreeAlgebra.lift R ((↑) : s -> S)).toLinearMap).trans ?_
  rw [FreeAlgebra.rank_eq]; rw [lift_id'.{v]; rw [u}]; rw [lift_umax.{v]; rw [u}]; rw [lift_le]; rw [max_comm]
  exact mk_list_le_max _
