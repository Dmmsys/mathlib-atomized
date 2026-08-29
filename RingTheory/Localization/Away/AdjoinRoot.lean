/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
The `R`-`AlgEquiv` between the localization of `R` away from `r` and
`R` with an inverse of `r` adjoined.
-/

@[expose] public section

open Polynomial AdjoinRoot Localization

variable {R : Type*} [CommRing R]

attribute [local instance] AdjoinRoot.algHom_subsingleton

/--
Definition of `Localization.awayEquivAdjoin` / `Localization.awayEquivAdjoin` 的定义

English:
definition Localization.awayEquivAdjoin
  signature: (r : R)
  body: AlgEquiv.ofAlgHom
    { awayLift _ r _ with
      commutes' :=
        IsLocalization.Away.lift_eq r (.of_mul_eq_one _ <| root_isInv r) }
    (liftAlgHom _ (Algebra.ofId _ _) (IsLocalization.Away.invSelf r) <| show aeval _ _ = _ by simp)
    (Subsingleton.elim _ _)
    (Subsingleton.elim (h := IsLoc

中文:
定义 Localization.awayEquivAdjoin
  签名: (r : R)
  定义体: AlgEquiv.ofAlgHom
    { awayLift _ r _ with
      commutes' :=
        IsLocalization.Away.lift_eq r (.of_mul_eq_one _ <| root_isInv r) }
    (liftAlgHom _ (Algebra.ofId _ _) (IsLocalization.Away.invSelf r) <| show aeval _ _ = _ by simp)
    (Subsingleton.elim _ _)
    (Subsingleton.elim (h := IsLoc

Depends on / 依赖: AlgEquiv, AlgEquiv.ofAlgHom, Algebra, Algebra.ofId, IsLocalization, IsLocalization.Away.invSelf, IsLocalization.Away.lift_eq, IsLocalization.algHom_subsingleton, Submonoid, Submonoid.powers, Subsingleton, Subsingleton.elim, algHom_subsingleton, awayLift, commutes, invSelf, liftAlgHom, lift_eq, ofAlgHom, of_mul_eq_one
-/
noncomputable def Localization.awayEquivAdjoin (r : R) : Away r ≃ₐ[R] AdjoinRoot (C r * X - 1) :=
  AlgEquiv.ofAlgHom
    { awayLift _ r _ with
      commutes' :=
        IsLocalization.Away.lift_eq r (.of_mul_eq_one _ <| root_isInv r) }
    (liftAlgHom _ (Algebra.ofId _ _) (IsLocalization.Away.invSelf r) <| show aeval _ _ = _ by simp)
    (Subsingleton.elim _ _)
    (Subsingleton.elim (h := IsLocalization.algHom_subsingleton (Submonoid.powers r)) _ _)

/--
theorem `IsLocalization.adjoin_inv` / 定理 `IsLocalization.adjoin_inv`

English:
theorem IsLocalization.adjoin_inv
  given: (r : R)
  statement: IsLocalization.Away r (AdjoinRoot <| C r * X - 1)
  proof: IsLocalization.isLocalization_of_algEquiv _ (Localization.awayEquivAdjoin r)

中文:
定理 是Localization.adjoin_inv
  条件: (r : R)
  结论: 是Localization.Away r (AdjoinRoot <| C r * X - 1)
  证明: IsLocalization.isLocalization_of_algEquiv _ (Localization.awayEquivAdjoin r)

Depends on / 依赖: IsLocalization, IsLocalization.isLocalization_of_algEquiv, Localization, Localization.awayEquivAdjoin, awayEquivAdjoin, isLocalization_of_algEquiv
-/
theorem IsLocalization.adjoin_inv (r : R) : IsLocalization.Away r (AdjoinRoot <| C r * X - 1) :=
  IsLocalization.isLocalization_of_algEquiv _ (Localization.awayEquivAdjoin r)

/--
theorem `IsLocalization.Away.finitePresentation` / 定理 `IsLocalization.Away.finitePresentation`

English:
theorem IsLocalization.Away.finitePresentation
  statement: (r : R) {S} [CommRing S] [Algebra R S]
  proof: (AdjoinRoot.finitePresentation _).equiv
(Localization.awayEquivAdjoin r).symm.trans IsLocalization.algEquiv (Submonoid.powers r) _ _

中文:
定理 是Localization.Away.finitePresentation
  结论: (r : R) {S} [交换环 S] [代数 R S]
  证明: (AdjoinRoot.finitePresentation _).equiv
(Localization.awayEquivAdjoin r).symm.trans IsLocalization.algEquiv (Submonoid.powers r) _ _

Depends on / 依赖: AdjoinRoot, AdjoinRoot.finitePresentation, IsLocalization, IsLocalization.algEquiv, Localization, Localization.awayEquivAdjoin, Submonoid, Submonoid.powers, algEquiv, awayEquivAdjoin, finitePresentation, powers, symm.trans
-/
theorem IsLocalization.Away.finitePresentation (r : R) {S} [CommRing S] [Algebra R S]
    [IsLocalization.Away r S] : Algebra.FinitePresentation R S :=
(AdjoinRoot.finitePresentation _).equiv
(Localization.awayEquivAdjoin r).symm.trans IsLocalization.algEquiv (Submonoid.powers r) _ _

/--
lemma `Algebra.FinitePresentation.of_isLocalizationAway` / 引理 `Algebra.FinitePresentation.of_isLocalizationAway`

English:
lemma Algebra.FinitePresentation.of_isLocalizationAway
  proof: have : Algebra.FinitePresentation S S' :=
    IsLocalization.Away.finitePresentation f
  .trans R S S'

中文:
引理 代数.有限呈现.of_isLocalizationAway
  证明: have : Algebra.FinitePresentation S S' :=
    IsLocalization.Away.finitePresentation f
  .trans R S S'

Depends on / 依赖: Algebra, Algebra.FinitePresentation, FinitePresentation, IsLocalization, IsLocalization.Away.finitePresentation, finitePresentation
-/
lemma Algebra.FinitePresentation.of_isLocalizationAway
    {R S S' : Type*} [CommRing R] [CommRing S] [CommRing S'] [Algebra R S] [Algebra R S']
    [Algebra S S'] [IsScalarTower R S S'] (f : S) [IsLocalization.Away f S']
    [Algebra.FinitePresentation R S] :
    Algebra.FinitePresentation R S' :=
  have : Algebra.FinitePresentation S S' :=
    IsLocalization.Away.finitePresentation f
  .trans R S S'

instance {S : Type*} [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S] (f : S) :
    Algebra.FinitePresentation R (Localization.Away f) :=
  .of_isLocalizationAway f

instance {S : Type*} [CommRing S] [Algebra R S] [Algebra.FiniteType R S] (f : S) :
    Algebra.FiniteType R (Localization.Away f) :=
  .trans ‹_› inferInstance
