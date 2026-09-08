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

/-- The `R`-`AlgEquiv` between the localization of `R` away from `r` and
`R` with an inverse of `r` adjoined. -/
/-
**Localization.awayEquivAdjoin** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Localization.awayEquivAdjoin (r : R) : Away r ≃ₐ[R] AdjoinRoot (C r * X - 
1)
参数：r : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `R`-`AlgEquiv` between the localization of `R` away from `r` and
`R` with an inverse of `r` adjoined.
-/
noncomputable def Localization.awayEquivAdjoin (r : R) : Away r ≃ₐ[R] AdjoinRoot (C r * X - 1) :=
  AlgEquiv.ofAlgHom
    { awayLift _ r _ with
      commutes' :=
        IsLocalization.Away.lift_eq r (.of_mul_eq_one _ <| root_isInv r) }
    (liftAlgHom _ (Algebra.ofId _ _) (IsLocalization.Away.invSelf r) <| show aeval _ _ = _ by simp)
    (Subsingleton.elim _ _)
    (Subsingleton.elim (h := IsLocalization.algHom_subsingleton (Submonoid.powers r)) _ _)
/-
**IsLocalization.adjoin_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalization.adjoin_inv (r : R) : IsLocalization.Away r (AdjoinRoot <| C
 r * X - 1)
参数：r : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.isLocalization_of_algEquiv`：isLocalization_of_algEquiv [A
lgebra R P] [IsLocalization M S] (h : S ≃ₐ[R] P) : IsLocalization M P
-/
theorem IsLocalization.adjoin_inv (r : R) : IsLocalization.Away r (AdjoinRoot <| C r * X - 1) :=
  IsLocalization.isLocalization_of_algEquiv _ (Localization.awayEquivAdjoin r)
/-
**IsLocalization.Away.finitePresentation** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalization.Away.finitePresentation (r : R) {S} [CommRing S] [Algebra R
 S] [IsLocalization.Away r S] : Algebra.FinitePresentation R S
参数：r : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FinitePresentation.equiv`：equiv [FinitePresentation R A] (e : A 
≃ₐ[R] B) : FinitePresentation R B
-/
theorem IsLocalization.Away.finitePresentation (r : R) {S} [CommRing S] [Algebra R S]
    [IsLocalization.Away r S] : Algebra.FinitePresentation R S :=
  (AdjoinRoot.finitePresentation _).equiv <|
    (Localization.awayEquivAdjoin r).symm.trans <| IsLocalization.algEquiv (Submonoid.powers r) _ _
/-
**Algebra.FinitePresentation.of_isLocalizationAway** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.FinitePresentation.of_isLocalizationAway {R S S' : Type*} [CommRin
g R] [CommRing S] [CommRing S'] [Algebra R S] [Algebra R S'] [Algebra S S'] [IsS
calarTower R S S'] (f : S) [IsLocalization.Away f S'] [Algebra.FinitePresentatio
n R S] : Algebra.FinitePresentation R S'
参数：f : S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.Away.finitePresentation`：IsLocalization.Away.finitePresen
tation (r : R) {S} [CommRing S] [Algebra R S] [IsLocalization.Away r S] : Algebr
a.FinitePresentation R S
· 使用定理 `Algebra.FinitePresentation.trans`：trans [Algebra A B] [IsScalarTower R A
 B] [FinitePresentation R A] [FinitePresentation A B] : FinitePresentation R B
-/
lemma Algebra.FinitePresentation.of_isLocalizationAway
    {R S S' : Type*} [CommRing R] [CommRing S] [CommRing S'] [Algebra R S] [Algebra R S']
    [Algebra S S'] [IsScalarTower R S S'] (f : S) [IsLocalization.Away f S']
    [Algebra.FinitePresentation R S] :
    Algebra.FinitePresentation R S' :=
  have : Algebra.FinitePresentation S S' :=
    IsLocalization.Away.finitePresentation f
  .trans R S S'
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {S : Type*} [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S] (f : S) :
    Algebra.FinitePresentation R (Localization.Away f) :=
  .of_isLocalizationAway f
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {S : Type*} [CommRing S] [Algebra R S] [Algebra.FiniteType R S] (f : S) :
    Algebra.FiniteType R (Localization.Away f) :=
  .trans ‹_› inferInstance
