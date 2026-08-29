/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Algebra.Divisibility.Prod
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.RingTheory.Artinian.Module

/-!
# Instances related to Artinian rings

We show that every reduced Artinian ring and the polynomial ring over it
are decomposition monoids, and every reduced Artinian ring is semisimple.
-/

public section

/--
theorem `StrongRankCondition.of_isArtinian` / 定理 `StrongRankCondition.of_isArtinian`

English:
theorem StrongRankCondition.of_isArtinian
  statement: (R) [Semiring R] [Nontrivial R]
  proof: (strongRankCondition_iff_succ R).2 fun n f hf =>
    have e := LinearEquiv.piCongrLeft R (fun _ => R) (finSuccEquiv n) ≪≫ₗ .piOptionEquivProd _
not_subsingleton R IsArtinian.subsingleton_of_injective
      (f := f ∘ₗ e.symm.toLinearMap) (hf.comp e.symm.injective)

中文:
定理 StrongRankCondition.of_isArtinian
  结论: (R) [Semiring R] [Nontrivial R]
  证明: (strongRankCondition_iff_succ R).2 fun n f hf =>
    have e := LinearEquiv.piCongrLeft R (fun _ => R) (finSuccEquiv n) ≪≫ₗ .piOptionEquivProd _
not_subsingleton R IsArtinian.subsingleton_of_injective
      (f := f ∘ₗ e.symm.toLinearMap) (hf.comp e.symm.injective)

Depends on / 依赖: IsArtinian, IsArtinian.subsingleton_of_injective, LinearEquiv, LinearEquiv.piCongrLeft, e.symm.injective, e.symm.toLinearMap, finSuccEquiv, hf.comp, injective, not_subsingleton, piCongrLeft, piOptionEquivProd, strongRankCondition_iff_succ, subsingleton_of_injective, toLinearMap
-/
theorem StrongRankCondition.of_isArtinian (R) [Semiring R] [Nontrivial R]
    [forall n, IsArtinian R (Fin n -> R)] : StrongRankCondition R :=
  (strongRankCondition_iff_succ R).2 fun n f hf =>
    have e := LinearEquiv.piCongrLeft R (fun _ => R) (finSuccEquiv n) ≪≫ₗ .piOptionEquivProd _
not_subsingleton R IsArtinian.subsingleton_of_injective
      (f := f ∘ₗ e.symm.toLinearMap) (hf.comp e.symm.injective)

namespace IsArtinianRing

variable (R : Type*) [CommRing R] [IsArtinianRing R] [IsReduced R]

attribute [local instance] fieldOfSubtypeIsMaximal

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DecompositionMonoid R
  body: MulEquiv.decompositionMonoid (equivPi R)

中文:
实例 :
  签名: DecompositionMonoid R
  定义体: MulEquiv.decompositionMonoid (equivPi R)

Depends on / 依赖: MulEquiv, MulEquiv.decompositionMonoid, decompositionMonoid, equivPi
-/
instance : DecompositionMonoid R := MulEquiv.decompositionMonoid (equivPi R)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DecompositionMonoid (Polynomial R)
  body: MulEquiv.decompositionMonoid
    (Polynomial.mapEquiv <| (equivPi R).toRingEquiv).trans (Polynomial.piEquiv _)

中文:
实例 :
  签名: DecompositionMonoid (Polynomial R)
  定义体: MulEquiv.decompositionMonoid
    (Polynomial.mapEquiv <| (equivPi R).toRingEquiv).trans (Polynomial.piEquiv _)

Depends on / 依赖: MulEquiv, MulEquiv.decompositionMonoid, Polynomial, Polynomial.mapEquiv, Polynomial.piEquiv, decompositionMonoid, equivPi, mapEquiv, piEquiv, toRingEquiv
-/
instance : DecompositionMonoid (Polynomial R) :=
MulEquiv.decompositionMonoid
    (Polynomial.mapEquiv <| (equivPi R).toRingEquiv).trans (Polynomial.piEquiv _)

end IsArtinianRing
