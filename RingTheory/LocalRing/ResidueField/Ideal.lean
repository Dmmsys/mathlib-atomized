/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.SurjectiveOnStalks

/-!
# The residue field of a prime ideal

We define `Ideal.ResidueField I` to be the residue field of the local ring `Localization.Prime I`,
and provide an `IsFractionRing (R ⧸ I) I.ResidueField` instance.

-/

@[expose] public section

open scoped nonZeroDivisors

variable {R S A B : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B] (I : Ideal R) [I.IsPrime]

/--
Definition of `Ideal.ResidueField` / `Ideal.ResidueField` 的定义

English:
abbreviation Ideal.ResidueField
  signature: : Type _
  body: IsLocalRing.ResidueField (Localization.AtPrime I)

中文:
缩写 Ideal.ResidueField
  签名: : Type _
  定义体: IsLocalRing.ResidueField (Localization.AtPrime I)

Depends on / 依赖: AtPrime, IsLocalRing, IsLocalRing.ResidueField, Localization, Localization.AtPrime, ResidueField
-/
abbrev Ideal.ResidueField : Type _ :=
  IsLocalRing.ResidueField (Localization.AtPrime I)

/-- If `I = f⁻¹(J)`, then there is a canonical embedding `κ(I) ↪ κ(J)`. -/
noncomputable
/--
Definition of `Ideal.ResidueField.map` / `Ideal.ResidueField.map` 的定义

English:
abbreviation Ideal.ResidueField.map
  signature: (I : Ideal R) [I.IsPrime] (J : Ideal S) [J.IsPrime]
  body: IsLocalRing.ResidueField.map (Localization.localRingHom I J f hf)

@[simp]

中文:
缩写 Ideal.ResidueField.map
  签名: (I : Ideal R) [I.IsPrime] (J : Ideal S) [J.IsPrime]
  定义体: IsLocalRing.ResidueField.map (Localization.localRingHom I J f hf)

@[simp]

Depends on / 依赖: IsLocalRing, IsLocalRing.ResidueField.map, Localization, Localization.localRingHom, ResidueField, localRingHom
-/
abbrev Ideal.ResidueField.map (I : Ideal R) [I.IsPrime] (J : Ideal S) [J.IsPrime]
    (f : R ->+* S) (hf : I = J.comap f) : I.ResidueField ->+* J.ResidueField :=
  IsLocalRing.ResidueField.map (Localization.localRingHom I J f hf)

@[simp]
/--
lemma `Ideal.ResidueField.map_algebraMap` / 引理 `Ideal.ResidueField.map_algebraMap`

English:
lemma Ideal.ResidueField.map_algebraMap
  statement: (I : Ideal R) [I.IsPrime] (J : Ideal S) [J.IsPrime]
  proof: by
  rw [IsScalarTower.algebraMap_apply R (Localization.AtPrime I)]
  simp [IsLocalRing.ResidueField.map_residue, Localization.localRingHom_to_map]
  rfl

中文:
引理 Ideal.ResidueField.map_algebraMap
  结论: (I : Ideal R) [I.IsPrime] (J : Ideal S) [J.IsPrime]
  证明: by
  rw [IsScalarTower.algebraMap_apply R (Localization.AtPrime I)]
  simp [IsLocalRing.ResidueField.map_residue, Localization.localRingHom_to_map]
  rfl

Depends on / 依赖: AtPrime, IsLocalRing, IsLocalRing.ResidueField.map_residue, IsScalarTower, IsScalarTower.algebraMap_apply, Localization, Localization.AtPrime, Localization.localRingHom_to_map, ResidueField, algebraMap_apply, localRingHom_to_map, map_residue
-/
lemma Ideal.ResidueField.map_algebraMap (I : Ideal R) [I.IsPrime] (J : Ideal S) [J.IsPrime]
    (f : R ->+* S) (hf : I = J.comap f) (r : R) :
    ResidueField.map I J f hf (algebraMap _ _ r) = algebraMap _ _ (f r) := by
  rw [IsScalarTower.algebraMap_apply R (Localization.AtPrime I)]
  simp [IsLocalRing.ResidueField.map_residue, Localization.localRingHom_to_map]
  rfl

/--
lemma `RingHom.SurjectiveOnStalks.residueFieldMap_bijective` / 引理 `RingHom.SurjectiveOnStalks.residueFieldMap_bijective`

English:
lemma RingHom.SurjectiveOnStalks.residueFieldMap_bijective
  proof: by
  subst hf
  exact ⟨RingHom.injective _, Ideal.Quotient.lift_surjective_of_surjective _ _
    (Ideal.Quotient.mk_surjective.comp (H J ‹_›))⟩

中文:
引理 RingHom.SurjectiveOnStalks.residueFieldMap_bijective
  证明: by
  subst hf
  exact ⟨RingHom.injective _, Ideal.Quotient.lift_surjective_of_surjective _ _
    (Ideal.Quotient.mk_surjective.comp (H J ‹_›))⟩

Depends on / 依赖: Ideal.Quotient.lift_surjective_of_surjective, Ideal.Quotient.mk_surjective.comp, Quotient, RingHom, RingHom.injective, injective, lift_surjective_of_surjective, mk_surjective
-/
lemma RingHom.SurjectiveOnStalks.residueFieldMap_bijective
    {f : R ->+* S} (H : f.SurjectiveOnStalks)
    (I : Ideal R) [I.IsPrime] (J : Ideal S) [J.IsPrime] (hf : I = J.comap f) :
    Function.Bijective (Ideal.ResidueField.map I J f hf) := by
  subst hf
  exact ⟨RingHom.injective _, Ideal.Quotient.lift_surjective_of_surjective _ _
    (Ideal.Quotient.mk_surjective.comp (H J ‹_›))⟩

set_option backward.isDefEq.respectTransparency false in
/-- If `I = f⁻¹(J)`, then there is a canonical embedding `κ(I) ↪ κ(J)`. -/
noncomputable
/--
Definition of `Ideal.ResidueField.mapₐ` / `Ideal.ResidueField.mapₐ` 的定义

English:
definition Ideal.ResidueField.mapₐ
  signature: (I : Ideal A) [I.IsPrime] (J : Ideal B) [J.IsPrime]
  body: Ideal.ResidueField.map I J f hf
  commutes' r := by
    simp [IsScalarTower.algebraMap_apply R A I.ResidueField,
      IsScalarTower.algebraMap_apply R B J.ResidueField]

中文:
定义 Ideal.ResidueField.mapₐ
  签名: (I : Ideal A) [I.IsPrime] (J : Ideal B) [J.IsPrime]
  定义体: Ideal.ResidueField.map I J f hf
  commutes' r := by
    simp [IsScalarTower.algebraMap_apply R A I.ResidueField,
      IsScalarTower.algebraMap_apply R B J.ResidueField]

Depends on / 依赖: Ideal.ResidueField.map, ResidueField
-/
def Ideal.ResidueField.mapₐ (I : Ideal A) [I.IsPrime] (J : Ideal B) [J.IsPrime]
    (f : A ->ₐ[R] B) (hf : I = J.comap f.toRingHom) : I.ResidueField ->ₐ[R] J.ResidueField where
  __ := Ideal.ResidueField.map I J f hf
  commutes' r := by
    simp [IsScalarTower.algebraMap_apply R A I.ResidueField,
      IsScalarTower.algebraMap_apply R B J.ResidueField]

/--
lemma `Ideal.ResidueField.mapₐ_apply` / 引理 `Ideal.ResidueField.mapₐ_apply`

English:
lemma Ideal.ResidueField.mapₐ_apply
  statement: (I : Ideal A) [I.IsPrime] (J : Ideal B) [J.IsPrime]
  proof: rfl

中文:
引理 Ideal.ResidueField.mapₐ_apply
  结论: (I : Ideal A) [I.IsPrime] (J : Ideal B) [J.IsPrime]
  证明: rfl
-/
@[simp] lemma Ideal.ResidueField.mapₐ_apply (I : Ideal A) [I.IsPrime] (J : Ideal B) [J.IsPrime]
    (f : A ->ₐ[R] B) (hf : I = J.comap f.toRingHom) (x) :
    Ideal.ResidueField.mapₐ I J f hf x = Ideal.ResidueField.map I J _ hf x := rfl

variable {I} in
@[simp high] -- marked `high` to override the more general `FaithfulSMul.algebraMap_eq_zero_iff`
/--
lemma `Ideal.algebraMap_residueField_eq_zero` / 引理 `Ideal.algebraMap_residueField_eq_zero`

English:
lemma Ideal.algebraMap_residueField_eq_zero
  given: {x}
  proof: by
  rw [IsScalarTower.algebraMap_apply R (Localization.AtPrime I)]; rw [IsLocalRing.ResidueField.algebraMap_eq]; rw [IsLocalRing.residue_eq_zero_iff]
  exact IsLocalization.AtPrime.to_map_mem_maximal_iff _ _ _

@[simp high] -- marked `high` to override the more general `FaithfulSMul.ker_algebraMap_

中文:
引理 Ideal.algebraMap_residueField_eq_zero
  条件: {x}
  证明: by
  rw [IsScalarTower.algebraMap_apply R (Localization.AtPrime I)]; rw [IsLocalRing.ResidueField.algebraMap_eq]; rw [IsLocalRing.residue_eq_zero_iff]
  exact IsLocalization.AtPrime.to_map_mem_maximal_iff _ _ _

@[simp high] -- marked `high` to override the more general `FaithfulSMul.ker_algebraMap_

Depends on / 依赖: AtPrime, IsLocalRing, IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_eq_zero_iff, IsLocalization, IsLocalization.AtPrime.to_map_mem_maximal_iff, IsScalarTower, IsScalarTower.algebraMap_apply, Localization, Localization.AtPrime, ResidueField, algebraMap_apply, algebraMap_eq, residue_eq_zero_iff, to_map_mem_maximal_iff
-/
lemma Ideal.algebraMap_residueField_eq_zero {x} :
    algebraMap R I.ResidueField x = 0 ↔ x in I := by
  rw [IsScalarTower.algebraMap_apply R (Localization.AtPrime I)]; rw [IsLocalRing.ResidueField.algebraMap_eq]; rw [IsLocalRing.residue_eq_zero_iff]
  exact IsLocalization.AtPrime.to_map_mem_maximal_iff _ _ _

@[simp high] -- marked `high` to override the more general `FaithfulSMul.ker_algebraMap_eq_bot`
/--
lemma `Ideal.ker_algebraMap_residueField` / 引理 `Ideal.ker_algebraMap_residueField`

English:
lemma Ideal.ker_algebraMap_residueField
  proof: Ideal.ext fun _ => Ideal.algebraMap_residueField_eq_zero

中文:
引理 Ideal.ker_algebraMap_residueField
  证明: Ideal.ext fun _ => Ideal.algebraMap_residueField_eq_zero

Depends on / 依赖: Ideal.algebraMap_residueField_eq_zero, Ideal.ext, algebraMap_residueField_eq_zero
-/
lemma Ideal.ker_algebraMap_residueField :
    RingHom.ker (algebraMap R I.ResidueField) = I :=
  Ideal.ext fun _ => Ideal.algebraMap_residueField_eq_zero

attribute [-instance] IsLocalRing.ResidueField.field in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra (R ⧸ I) I.ResidueField
  body: (Ideal.Quotient.liftₐ I (Algebra.ofId _ _)
    fun _ => Ideal.algebraMap_residueField_eq_zero.mpr).toRingHom.toAlgebra

中文:
实例 :
  签名: Algebra (R ⧸ I) I.ResidueField
  定义体: (Ideal.Quotient.liftₐ I (Algebra.ofId _ _)
    fun _ => Ideal.algebraMap_residueField_eq_zero.mpr).toRingHom.toAlgebra

Depends on / 依赖: Algebra, Algebra.ofId, Ideal.Quotient.lift, Ideal.algebraMap_residueField_eq_zero.mpr, Quotient, algebraMap_residueField_eq_zero, toAlgebra, toRingHom, toRingHom.toAlgebra
-/
noncomputable instance : Algebra (R ⧸ I) I.ResidueField :=
  (Ideal.Quotient.liftₐ I (Algebra.ofId _ _)
    fun _ => Ideal.algebraMap_residueField_eq_zero.mpr).toRingHom.toAlgebra

instance (I : Ideal A) [I.IsPrime] : IsScalarTower R (A ⧸ I) I.ResidueField :=
  .of_algebraMap_eq' rfl

instance (I : Ideal R) [I.IsPrime] : (⊥ : Ideal I.ResidueField).LiesOver I :=
  ⟨I.ker_algebraMap_residueField.symm⟩

@[simp]
/--
lemma `Ideal.algebraMap_quotient_residueField_mk` / 引理 `Ideal.algebraMap_quotient_residueField_mk`

English:
lemma Ideal.algebraMap_quotient_residueField_mk
  given: (x)
  proof: rfl

中文:
引理 Ideal.algebraMap_quotient_residueField_mk
  条件: (x)
  证明: rfl
-/
lemma Ideal.algebraMap_quotient_residueField_mk (x) :
    algebraMap (R ⧸ I) I.ResidueField (Ideal.Quotient.mk _ x) =
    algebraMap R I.ResidueField x := rfl

/--
lemma `Ideal.injective_algebraMap_quotient_residueField` / 引理 `Ideal.injective_algebraMap_quotient_residueField`

English:
lemma Ideal.injective_algebraMap_quotient_residueField
  proof: by
  rw [RingHom.injective_iff_ker_eq_bot]
  refine (Ideal.ker_quotient_lift _ _).trans ?_
  change map (Quotient.mk I) (RingHom.ker (algebraMap R I.ResidueField)) = ⊥
  rw [Ideal.ker_algebraMap_residueField]; rw [map_quotient_self]

中文:
引理 Ideal.injective_algebraMap_quotient_residueField
  证明: by
  rw [RingHom.injective_iff_ker_eq_bot]
  refine (Ideal.ker_quotient_lift _ _).trans ?_
  change map (Quotient.mk I) (RingHom.ker (algebraMap R I.ResidueField)) = ⊥
  rw [Ideal.ker_algebraMap_residueField]; rw [map_quotient_self]

Depends on / 依赖: I.ResidueField, Ideal.ker_algebraMap_residueField, Ideal.ker_quotient_lift, Quotient, Quotient.mk, ResidueField, RingHom, RingHom.injective_iff_ker_eq_bot, RingHom.ker, algebraMap, completeSpace_coe, injective_iff_ker_eq_bot, isClosed_closure, isClosed_closure.completeSpace_coe, ker_algebraMap_residueField, ker_quotient_lift, map_quotient_self
-/
lemma Ideal.injective_algebraMap_quotient_residueField :
    Function.Injective (algebraMap (R ⧸ I) I.ResidueField) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  refine (Ideal.ker_quotient_lift _ _).trans ?_
  change map (Quotient.mk I) (RingHom.ker (algebraMap R I.ResidueField)) = ⊥
  rw [Ideal.ker_algebraMap_residueField]; rw [map_quotient_self]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsFractionRing (R ⧸ I) I.ResidueField
  body: isUnit_iff_ne_zero.mpr
    (map_ne_zero_of_mem_nonZeroDivisors _ I.injective_algebraMap_quotient_residueField y.2)
  surj x := by
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
    obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq I.primeCompl x
    refine ⟨⟨Ideal.Quotient.mk _ x, ⟨I

中文:
实例 :
  签名: IsFractionRing (R ⧸ I) I.ResidueField
  定义体: isUnit_iff_ne_zero.mpr
    (map_ne_zero_of_mem_nonZeroDivisors _ I.injective_algebraMap_quotient_residueField y.2)
  surj x := by
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
    obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq I.primeCompl x
    refine ⟨⟨Ideal.Quotient.mk _ x, ⟨I
-/
instance : IsFractionRing (R ⧸ I) I.ResidueField where
  map_units y := isUnit_iff_ne_zero.mpr
    (map_ne_zero_of_mem_nonZeroDivisors _ I.injective_algebraMap_quotient_residueField y.2)
  surj x := by
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
    obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq I.primeCompl x
    refine ⟨⟨Ideal.Quotient.mk _ x, ⟨Ideal.Quotient.mk _ s, ?_⟩⟩, ?_⟩
    · rwa [mem_nonZeroDivisors_iff_ne_zero, ne_eq, Ideal.Quotient.eq_zero_iff_mem]
    · simp [IsScalarTower.algebraMap_eq R (Localization.AtPrime I) I.ResidueField, ← map_mul]
  exists_of_eq {x y} e := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← sub_eq_zero]; rw [← map_sub]; rw [← map_sub] at e
    simp only [IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_eq_zero_iff,
      IsScalarTower.algebraMap_apply R (Localization.AtPrime I) I.ResidueField,
      Ideal.algebraMap_quotient_residueField_mk, IsLocalization.AtPrime.to_map_mem_maximal_iff _ I,
      ← Ideal.Quotient.mk_eq_mk_iff_sub_mem] at e
    use 1
    simp [e]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsDomain
  signature: R] : IsFractionRing R (⊥
  body: IsLocalization.of_ringEquiv_left (RingEquiv.quotientBot R).symm
    (MulEquivClass.map_nonZeroDivisors (RingEquiv.quotientBot R).symm) (by simp)

中文:
实例 [IsDomain
  签名: R] : IsFractionRing R (⊥
  定义体: IsLocalization.of_ringEquiv_left (RingEquiv.quotientBot R).symm
    (MulEquivClass.map_nonZeroDivisors (RingEquiv.quotientBot R).symm) (by simp)

Depends on / 依赖: IsLocalization, IsLocalization.of_ringEquiv_left, MulEquivClass, MulEquivClass.map_nonZeroDivisors, RingEquiv, RingEquiv.quotientBot, map_nonZeroDivisors, of_ringEquiv_left, quotientBot
-/
instance [IsDomain R] : IsFractionRing R (⊥ : Ideal R).ResidueField :=
  IsLocalization.of_ringEquiv_left (RingEquiv.quotientBot R).symm
    (MulEquivClass.map_nonZeroDivisors (RingEquiv.quotientBot R).symm) (by simp)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Finite
  signature: (R ⧸ I)] : Finite I.ResidueField
  body: IsLocalization.finite (R ⧸ I) (nonZeroDivisors (R ⧸ I))

中文:
实例 [Finite
  签名: (R ⧸ I)] : Finite I.ResidueField
  定义体: IsLocalization.finite (R ⧸ I) (nonZeroDivisors (R ⧸ I))

Depends on / 依赖: IsLocalization, IsLocalization.finite, finite, nonZeroDivisors
-/
instance [Finite (R ⧸ I)] : Finite I.ResidueField :=
  IsLocalization.finite (R ⧸ I) (nonZeroDivisors (R ⧸ I))

/--
lemma `Ideal.bijective_algebraMap_quotient_residueField` / 引理 `Ideal.bijective_algebraMap_quotient_residueField`

English:
lemma Ideal.bijective_algebraMap_quotient_residueField
  given: (I : Ideal R) [I.IsMaximal]
  proof: ⟨I.injective_algebraMap_quotient_residueField, IsFractionRing.surjective_iff_isField.mpr
    ((Quotient.maximal_ideal_iff_isField_quotient I).mp inferInstance)⟩

中文:
引理 Ideal.bijective_algebraMap_quotient_residueField
  条件: (I : Ideal R) [I.IsMaximal]
  证明: ⟨I.injective_algebraMap_quotient_residueField, IsFractionRing.surjective_iff_isField.mpr
    ((Quotient.maximal_ideal_iff_isField_quotient I).mp inferInstance)⟩

Depends on / 依赖: I.injective_algebraMap_quotient_residueField, IsFractionRing, IsFractionRing.surjective_iff_isField.mpr, Quotient, Quotient.maximal_ideal_iff_isField_quotient, injective_algebraMap_quotient_residueField, maximal_ideal_iff_isField_quotient, surjective_iff_isField
-/
lemma Ideal.bijective_algebraMap_quotient_residueField (I : Ideal R) [I.IsMaximal] :
    Function.Bijective (algebraMap (R ⧸ I) I.ResidueField) :=
  ⟨I.injective_algebraMap_quotient_residueField, IsFractionRing.surjective_iff_isField.mpr
    ((Quotient.maximal_ideal_iff_isField_quotient I).mp inferInstance)⟩

/--
lemma `Ideal.algebraMap_residueField_surjective` / 引理 `Ideal.algebraMap_residueField_surjective`

English:
lemma Ideal.algebraMap_residueField_surjective
  given: (I : Ideal R) [I.IsMaximal]
  proof: by
  rw [IsScalarTower.algebraMap_eq R (R ⧸ I) _]
  exact I.bijective_algebraMap_quotient_residueField.surjective.comp Ideal.Quotient.mk_surjective

中文:
引理 Ideal.algebraMap_residueField_surjective
  条件: (I : Ideal R) [I.IsMaximal]
  证明: by
  rw [IsScalarTower.algebraMap_eq R (R ⧸ I) _]
  exact I.bijective_algebraMap_quotient_residueField.surjective.comp Ideal.Quotient.mk_surjective

Depends on / 依赖: I.bijective_algebraMap_quotient_residueField.surjective.comp, Ideal.Quotient.mk_surjective, IsScalarTower, IsScalarTower.algebraMap_eq, Quotient, algebraMap_eq, bijective_algebraMap_quotient_residueField, mk_surjective, surjective
-/
lemma Ideal.algebraMap_residueField_surjective (I : Ideal R) [I.IsMaximal] :
    Function.Surjective (algebraMap R I.ResidueField) := by
  rw [IsScalarTower.algebraMap_eq R (R ⧸ I) _]
  exact I.bijective_algebraMap_quotient_residueField.surjective.comp Ideal.Quotient.mk_surjective

instance (I : Ideal R) [I.IsMaximal] : Module.Finite R I.ResidueField :=
  .of_surjective (Algebra.linearMap _ _) I.algebraMap_residueField_surjective

/--
Definition of `Ideal.algEquivResidueFieldOfField` / `Ideal.algEquivResidueFieldOfField` 的定义

English:
definition Ideal.algEquivResidueFieldOfField
  signature: {k : Type*} [Field k]
  body: AlgEquiv.ofBijective (Algebra.ofId k _) ⟨RingHom.injective _,
    haveI : p.IsMaximal := by simpa [p.eq_bot_of_prime] using Ideal.bot_isMaximal
    p.algebraMap_residueField_surjective⟩

@[simp]

中文:
定义 Ideal.algEquivResidueFieldOfField
  签名: {k : 类型} [Field k]
  定义体: AlgEquiv.ofBijective (Algebra.ofId k _) ⟨RingHom.injective _,
    haveI : p.IsMaximal := by simpa [p.eq_bot_of_prime] using Ideal.bot_isMaximal
    p.algebraMap_residueField_surjective⟩

@[simp]

Depends on / 依赖: AlgEquiv, AlgEquiv.ofBijective, Algebra, Algebra.ofId, Ideal.bot_isMaximal, IsMaximal, RingHom, RingHom.injective, algebraMap_residueField_surjective, bot_isMaximal, eq_bot_of_prime, injective, ofBijective, p.IsMaximal, p.algebraMap_residueField_surjective, p.eq_bot_of_prime
-/
noncomputable def Ideal.algEquivResidueFieldOfField {k : Type*} [Field k]
    (p : Ideal k) [p.IsPrime] : k ≃ₐ[k] p.ResidueField :=
  AlgEquiv.ofBijective (Algebra.ofId k _) ⟨RingHom.injective _,
    haveI : p.IsMaximal := by simpa [p.eq_bot_of_prime] using Ideal.bot_isMaximal
    p.algebraMap_residueField_surjective⟩

@[simp]
/--
lemma `Ideal.algEquivResidueFieldOfField_apply` / 引理 `Ideal.algEquivResidueFieldOfField_apply`

English:
lemma Ideal.algEquivResidueFieldOfField_apply
  statement: {k : Type*} [Field k] (p : Ideal k) [p.IsPrime]
  proof: rfl

中文:
引理 Ideal.algEquivResidueFieldOfField_apply
  结论: {k : 类型} [Field k] (p : Ideal k) [p.IsPrime]
  证明: rfl
-/
lemma Ideal.algEquivResidueFieldOfField_apply {k : Type*} [Field k] (p : Ideal k) [p.IsPrime]
    (x : k) : p.algEquivResidueFieldOfField x = algebraMap k p.ResidueField x :=
  rfl

/--
lemma `Ideal.surjectiveOnStalks_residueField` / 引理 `Ideal.surjectiveOnStalks_residueField`

English:
lemma Ideal.surjectiveOnStalks_residueField
  given: (I : Ideal R) [I.IsPrime]
  proof: (RingHom.surjectiveOnStalks_of_surjective Ideal.Quotient.mk_surjective).comp
    (RingHom.surjectiveOnStalks_of_isLocalization I.primeCompl _)

中文:
引理 Ideal.surjectiveOnStalks_residueField
  条件: (I : Ideal R) [I.IsPrime]
  证明: (RingHom.surjectiveOnStalks_of_surjective Ideal.Quotient.mk_surjective).comp
    (RingHom.surjectiveOnStalks_of_isLocalization I.primeCompl _)

Depends on / 依赖: I.primeCompl, Ideal.Quotient.mk_surjective, Quotient, RingHom, RingHom.surjectiveOnStalks_of_isLocalization, RingHom.surjectiveOnStalks_of_surjective, mk_surjective, primeCompl, surjectiveOnStalks_of_isLocalization, surjectiveOnStalks_of_surjective
-/
lemma Ideal.surjectiveOnStalks_residueField (I : Ideal R) [I.IsPrime] :
    (algebraMap R I.ResidueField).SurjectiveOnStalks :=
  (RingHom.surjectiveOnStalks_of_surjective Ideal.Quotient.mk_surjective).comp
    (RingHom.surjectiveOnStalks_of_isLocalization I.primeCompl _)

section

open Localization AtPrime

variable (J : Ideal A) (K : Ideal B) [J.IsPrime] [K.IsPrime]
  [J.LiesOver I] [Algebra (Localization.AtPrime I) (Localization.AtPrime J)] [IsLiesOverAlgebra I J]
  [K.LiesOver I] [Algebra (Localization.AtPrime I) (Localization.AtPrime K)] [IsLiesOverAlgebra I K]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsLocalHom (algebraMap (Localization.AtPrime I) (Localization.AtPrime J))
  body: by
  rw [IsLiesOverAlgebra.algebraMap_eq]
  exact isLocalHom_localRingHom _ _ _ (J.over_def I)

中文:
实例 :
  签名: IsLocalHom (algebraMap (Localization.AtPrime I) (Localization.AtPrime J))
  定义体: by
  rw [IsLiesOverAlgebra.algebraMap_eq]
  exact isLocalHom_localRingHom _ _ _ (J.over_def I)

Depends on / 依赖: IsLiesOverAlgebra, IsLiesOverAlgebra.algebraMap_eq, J.over_def, algebraMap_eq, isLocalHom_localRingHom, over_def
-/
instance : IsLocalHom (algebraMap (Localization.AtPrime I) (Localization.AtPrime J)) := by
  rw [IsLiesOverAlgebra.algebraMap_eq]
  exact isLocalHom_localRingHom _ _ _ (J.over_def I)

/--
Definition of `Ideal.residueFieldRingEquiv` / `Ideal.residueFieldRingEquiv` 的定义

English:
definition Ideal.residueFieldRingEquiv
  signature: (f : A ≃+* B) (h : J = K.comap f)
  body: IsLocalRing.ResidueField.mapEquiv (localRingEquiv J K f h)

中文:
定义 Ideal.residueFieldRingEquiv
  签名: (f : A ≃+* B) (h : J = K.comap f)
  定义体: IsLocalRing.ResidueField.mapEquiv (localRingEquiv J K f h)

Depends on / 依赖: IsLocalRing, IsLocalRing.ResidueField.mapEquiv, ResidueField, localRingEquiv, mapEquiv
-/
noncomputable def Ideal.residueFieldRingEquiv (f : A ≃+* B) (h : J = K.comap f) :
    J.ResidueField ≃+* K.ResidueField :=
  IsLocalRing.ResidueField.mapEquiv (localRingEquiv J K f h)

/--
Definition of `Ideal.residueFieldAlgEquiv` / `Ideal.residueFieldAlgEquiv` 的定义

English:
abbreviation Ideal.residueFieldAlgEquiv
  signature: (f : A ≃ₐ[R] B) (h : J = K.comap f)
  body: IsLocalRing.ResidueField.mapAlgEquiv (localAlgEquiv J K f h)

中文:
缩写 Ideal.residueFieldAlgEquiv
  签名: (f : A ≃ₐ[R] B) (h : J = K.comap f)
  定义体: IsLocalRing.ResidueField.mapAlgEquiv (localAlgEquiv J K f h)

Depends on / 依赖: IsLocalRing, IsLocalRing.ResidueField.mapAlgEquiv, ResidueField, localAlgEquiv, mapAlgEquiv
-/
noncomputable abbrev Ideal.residueFieldAlgEquiv (f : A ≃ₐ[R] B) (h : J = K.comap f) :
    J.ResidueField ≃ₐ[R] K.ResidueField :=
  IsLocalRing.ResidueField.mapAlgEquiv (localAlgEquiv J K f h)

/--
Definition of `Ideal.residueFieldAlgEquiv'` / `Ideal.residueFieldAlgEquiv'` 的定义

English:
abbreviation Ideal.residueFieldAlgEquiv'
  signature: (f : A ≃ₐ[R] B) (h : J = K.comap f)
  body: IsLocalRing.ResidueField.mapAlgEquiv' (localAlgEquiv' I J K f h)

中文:
缩写 Ideal.residueFieldAlgEquiv'
  签名: (f : A ≃ₐ[R] B) (h : J = K.comap f)
  定义体: IsLocalRing.ResidueField.mapAlgEquiv' (localAlgEquiv' I J K f h)

Depends on / 依赖: IsLocalRing, IsLocalRing.ResidueField.mapAlgEquiv, ResidueField, localAlgEquiv, mapAlgEquiv
-/
noncomputable abbrev Ideal.residueFieldAlgEquiv' (f : A ≃ₐ[R] B) (h : J = K.comap f) :
    J.ResidueField ≃ₐ[I.ResidueField] K.ResidueField :=
  IsLocalRing.ResidueField.mapAlgEquiv' (localAlgEquiv' I J K f h)

end

instance (p : Ideal R) [p.IsPrime] : Algebra.EssFiniteType R p.ResidueField :=
  .comp _ (Localization.AtPrime p) _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Algebra.EssFiniteType
  signature: R A]
  body: by
  have : Algebra.EssFiniteType R q.ResidueField := .comp _ A _
  refine .of_comp R _ _

中文:
实例 [Algebra.EssFiniteType
  签名: R A]
  定义体: by
  have : Algebra.EssFiniteType R q.ResidueField := .comp _ A _
  refine .of_comp R _ _

Depends on / 依赖: Algebra, Algebra.EssFiniteType, EssFiniteType, ResidueField, of_comp, q.ResidueField
-/
instance [Algebra.EssFiniteType R A]
    (p : Ideal R) [p.IsPrime] (q : Ideal A) [q.IsPrime] [q.LiesOver p]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [Localization.AtPrime.IsLiesOverAlgebra p q] :
    Algebra.EssFiniteType p.ResidueField q.ResidueField := by
  have : Algebra.EssFiniteType R q.ResidueField := .comp _ A _
  refine .of_comp R _ _

/--
Definition of `Ideal.ResidueField.lift` / `Ideal.ResidueField.lift` 的定义

English:
definition Ideal.ResidueField.lift
  body: IsLocalization.lift (M := (R ⧸ I)⁰) (g := Ideal.Quotient.lift I (f := f) hf₁) by
    simpa [Ideal.Quotient.mk_surjective.forall, Ideal.Quotient.eq_zero_iff_mem]

中文:
定义 Ideal.ResidueField.lift
  定义体: IsLocalization.lift (M := (R ⧸ I)⁰) (g := Ideal.Quotient.lift I (f := f) hf₁) by
    simpa [Ideal.Quotient.mk_surjective.forall, Ideal.Quotient.eq_zero_iff_mem]

Depends on / 依赖: Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.lift, Ideal.Quotient.mk_surjective.forall, IsLocalization, IsLocalization.lift, Quotient, eq_zero_iff_mem, mk_surjective
-/
noncomputable def Ideal.ResidueField.lift
    (f : R ->+* S) (hf₁ : I <= RingHom.ker f)
    (hf₂ : I.primeCompl <= (IsUnit.submonoid S).comap f) : I.ResidueField ->+* S :=
IsLocalization.lift (M := (R ⧸ I)⁰) (g := Ideal.Quotient.lift I (f := f) hf₁) by
    simpa [Ideal.Quotient.mk_surjective.forall, Ideal.Quotient.eq_zero_iff_mem]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `Ideal.ResidueField.lift_algebraMap` / 引理 `Ideal.ResidueField.lift_algebraMap`

English:
lemma Ideal.ResidueField.lift_algebraMap
  proof: by
  rw [lift]; rw [IsScalarTower.algebraMap_apply R (R ⧸ I) I.ResidueField]; rw [IsLocalization.lift_eq]
  simp

中文:
引理 Ideal.ResidueField.lift_algebraMap
  证明: by
  rw [lift]; rw [IsScalarTower.algebraMap_apply R (R ⧸ I) I.ResidueField]; rw [IsLocalization.lift_eq]
  simp
-/
@[simp] lemma Ideal.ResidueField.lift_algebraMap
    (f : R ->+* S) (hf₁ : I <= RingHom.ker f)
    (hf₂ : I.primeCompl <= (IsUnit.submonoid S).comap f) (r : R) :
    lift I f hf₁ hf₂ (algebraMap _ _ r) = f r := by
  rw [lift]; rw [IsScalarTower.algebraMap_apply R (R ⧸ I) I.ResidueField]; rw [IsLocalization.lift_eq]
  simp

/-- If `f` sends `I` to `0` and `Iᶜ` to units, then `f` lifts to `κ(I)`. -/
noncomputable
/--
Definition of `Ideal.ResidueField.liftₐ` / `Ideal.ResidueField.liftₐ` 的定义

English:
definition Ideal.ResidueField.liftₐ
  signature: (I : Ideal A) [I.IsPrime] (f : A ->ₐ[R] B) (hf₁ : I <= RingHom.ker f)
  body: Ideal.ResidueField.lift I f.toRingHom hf₁ hf₂
  commutes' r := by simp [IsScalarTower.algebraMap_apply R A I.ResidueField]

@[simp]

中文:
定义 Ideal.ResidueField.liftₐ
  签名: (I : Ideal A) [I.IsPrime] (f : A ->ₐ[R] B) (hf₁ : I <= RingHom.ker f)
  定义体: Ideal.ResidueField.lift I f.toRingHom hf₁ hf₂
  commutes' r := by simp [IsScalarTower.algebraMap_apply R A I.ResidueField]

@[simp]

Depends on / 依赖: Ideal.ResidueField.lift, ResidueField, StarSubalgebra, StarSubalgebra.commRingTopologicalClosure, commRingTopologicalClosure, f.toRingHom, fast_instance, mul_comm, toRingHom
-/
def Ideal.ResidueField.liftₐ (I : Ideal A) [I.IsPrime] (f : A ->ₐ[R] B) (hf₁ : I <= RingHom.ker f)
    (hf₂ : I.primeCompl <= (IsUnit.submonoid B).comap f) : I.ResidueField ->ₐ[R] B where
  __ := Ideal.ResidueField.lift I f.toRingHom hf₁ hf₂
  commutes' r := by simp [IsScalarTower.algebraMap_apply R A I.ResidueField]

@[simp]
/--
lemma `Ideal.ResidueField.liftₐ_algebraMap` / 引理 `Ideal.ResidueField.liftₐ_algebraMap`

English:
lemma Ideal.ResidueField.liftₐ_algebraMap
  statement: (I : Ideal A) [I.IsPrime] (f : A ->ₐ[R] B)
  proof: lift_algebraMap _ _ _ hf₂ _

中文:
引理 Ideal.ResidueField.liftₐ_algebraMap
  结论: (I : Ideal A) [I.IsPrime] (f : A ->ₐ[R] B)
  证明: lift_algebraMap _ _ _ hf₂ _

Depends on / 依赖: lift_algebraMap
-/
lemma Ideal.ResidueField.liftₐ_algebraMap (I : Ideal A) [I.IsPrime] (f : A ->ₐ[R] B)
    (hf₁ : I <= RingHom.ker f) (hf₂ : I.primeCompl <= (IsUnit.submonoid B).comap f) (r : A) :
    liftₐ I f hf₁ hf₂ (algebraMap _ _ r) = f r :=
  lift_algebraMap _ _ _ hf₂ _

/--
lemma `Ideal.ResidueField.liftₐ_comp_toAlgHom` / 引理 `Ideal.ResidueField.liftₐ_comp_toAlgHom`

English:
lemma Ideal.ResidueField.liftₐ_comp_toAlgHom
  statement: (I : Ideal A) [I.IsPrime] (f : A ->ₐ[R] B)
  proof: AlgHom.ext fun _ => liftₐ_algebraMap _ _ _ hf₂ _

@[ext high] -- higher than `RingHom.ext`.

中文:
引理 Ideal.ResidueField.liftₐ_comp_toAlgHom
  结论: (I : Ideal A) [I.IsPrime] (f : A ->ₐ[R] B)
  证明: AlgHom.ext fun _ => liftₐ_algebraMap _ _ _ hf₂ _

@[ext high] -- higher than `RingHom.ext`.

Depends on / 依赖: completeSpace_coe, isClosed_closure, isClosed_closure.completeSpace_coe
-/
@[simp] lemma Ideal.ResidueField.liftₐ_comp_toAlgHom (I : Ideal A) [I.IsPrime] (f : A ->ₐ[R] B)
    (hf₁ : I <= RingHom.ker f) (hf₂ : I.primeCompl <= (IsUnit.submonoid B).comap f) :
    (liftₐ I f hf₁ hf₂).comp (IsScalarTower.toAlgHom _ A _) = f :=
  AlgHom.ext fun _ => liftₐ_algebraMap _ _ _ hf₂ _

@[ext high] -- higher than `RingHom.ext`.
/--
lemma `Ideal.ResidueField.ringHom_ext` / 引理 `Ideal.ResidueField.ringHom_ext`

English:
lemma Ideal.ResidueField.ringHom_ext
  statement: {I : Ideal R} [I.IsPrime]
  proof: IsLocalization.ringHom_ext (R ⧸ I)⁰ (Ideal.Quotient.ringHom_ext H)

@[ext high] -- higher than `AlgHom.ext`.

中文:
引理 Ideal.ResidueField.ringHom_ext
  结论: {I : Ideal R} [I.IsPrime]
  证明: IsLocalization.ringHom_ext (R ⧸ I)⁰ (Ideal.Quotient.ringHom_ext H)

@[ext high] -- higher than `AlgHom.ext`.

Depends on / 依赖: Ideal.Quotient.ringHom_ext, IsLocalization, IsLocalization.ringHom_ext, Quotient, ringHom_ext
-/
lemma Ideal.ResidueField.ringHom_ext {I : Ideal R} [I.IsPrime]
    {f g : I.ResidueField ->+* S} (H : f.comp (algebraMap R _) = g.comp (algebraMap R _)) : f = g :=
  IsLocalization.ringHom_ext (R ⧸ I)⁰ (Ideal.Quotient.ringHom_ext H)

@[ext high] -- higher than `AlgHom.ext`.
/--
lemma `Ideal.ResidueField.algHom_ext` / 引理 `Ideal.ResidueField.algHom_ext`

English:
lemma Ideal.ResidueField.algHom_ext
  statement: {I : Ideal A} [I.IsPrime] {f g : I.ResidueField ->ₐ[R] B}
  proof: AlgHom.coe_ringHom_injective (ringHom_ext congr($H))

中文:
引理 Ideal.ResidueField.algHom_ext
  结论: {I : Ideal A} [I.IsPrime] {f g : I.ResidueField ->ₐ[R] B}
  证明: AlgHom.coe_ringHom_injective (ringHom_ext congr($H))

Depends on / 依赖: AlgHom, AlgHom.coe_ringHom_injective, coe_ringHom_injective, ringHom_ext
-/
lemma Ideal.ResidueField.algHom_ext {I : Ideal A} [I.IsPrime] {f g : I.ResidueField ->ₐ[R] B}
    (H : f.comp (IsScalarTower.toAlgHom R A _) = g.comp (IsScalarTower.toAlgHom R A _)) : f = g :=
  AlgHom.coe_ringHom_injective (ringHom_ext congr($H))

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `Ideal.ResidueField.mapₐ_id` / 引理 `Ideal.ResidueField.mapₐ_id`

English:
lemma Ideal.ResidueField.mapₐ_id
  given: (I : Ideal A) [I.IsPrime]
  proof: by ext; simp

中文:
引理 Ideal.ResidueField.mapₐ_id
  条件: (I : Ideal A) [I.IsPrime]
  证明: by ext; simp
-/
@[simp] lemma Ideal.ResidueField.mapₐ_id (I : Ideal A) [I.IsPrime] :
    Ideal.ResidueField.mapₐ I I (.id R A) rfl = .id _ _ := by ext; simp
