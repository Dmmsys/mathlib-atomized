/-
Copyright (c) 2025 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.RingTheory.DedekindDomain.PID
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.RingHom.Finite

/-!
# Instances for Dedekind domains

This file contains various instances to work with localization of a ring extension.

A very common situation in number theory is to have an extension of (say) Dedekind domains `R` and
`S`, and to prove a property of this extension it is useful to consider the localization `Rₚ` of `R`
at `P`, a prime ideal of `R`. One also works with the corresponding localization `Sₚ` of `S` and the
fraction fields `K` and `L` of `R` and `S`. In this situation there are many compatible algebra
structures and various properties of the rings involved. Another situation is when we have a
tower extension `R ⊆ S ⊆ T` and thus we work with `Rₚ ⊆ Sₚ ⊆ Tₚ` where
`Tₚ` is the localization of `T` at `P`. This file contains a collection of such instances.

## Implementation details
In general one wants all the results below for any algebra satisfying `IsLocalization`, but those
cannot be instances (since Lean has no way of guessing the submonoid). Having the instances in the
special case of *the* localization at a prime ideal is useful in working with Dedekind domains.

-/

public section

open nonZeroDivisors IsLocalization Algebra Module IsFractionRing IsScalarTower

attribute [local instance] FractionRing.liftAlgebra

variable {R : Type*} (S : Type*) (T : Type*) [CommRing R] [CommRing S] [CommRing T] [IsDomain R]
  [IsDomain S] [IsDomain T] [Algebra R S]

local notation3 "K" => FractionRing R
local notation3 "L" => FractionRing S
local notation3 "F" => FractionRing T

section

/--
theorem `algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul` / 定理 `algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul`

English:
theorem algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul
  statement: {A : Type*} (B : Type*)
  proof: map_le_nonZeroDivisors_of_injective _ (FaithfulSMul.algebraMap_injective A B) hS

中文:
定理 algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul
  结论: {A : 类型} (B : 类型)
  证明: map_le_nonZeroDivisors_of_injective _ (FaithfulSMul.algebraMap_injective A B) hS

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap_injective, map_le_nonZeroDivisors_of_injective
-/
theorem algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul {A : Type*} (B : Type*)
    [CommSemiring A] [CommSemiring B] [Algebra A B] [NoZeroDivisors B] [FaithfulSMul A B]
    {S : Submonoid A} (hS : S <= A⁰) : algebraMapSubmonoid B S <= B⁰ :=
  map_le_nonZeroDivisors_of_injective _ (FaithfulSMul.algebraMap_injective A B) hS

variable (Rₘ Sₘ : Type*) [CommRing Rₘ] [CommRing Sₘ] [Algebra R Rₘ] [IsTorsionFree R S]
    [Algebra.IsSeparable (FractionRing R) (FractionRing S)] {M : Submonoid R} [IsLocalization M Rₘ]
    [Algebra Rₘ Sₘ] [Algebra S Sₘ] [Algebra R Sₘ] [IsScalarTower R Rₘ Sₘ]
    [IsScalarTower R S Sₘ] [IsLocalization (algebraMapSubmonoid S M) Sₘ]
    [Algebra (FractionRing Rₘ) (FractionRing Sₘ)]
    [IsScalarTower Rₘ (FractionRing Rₘ) (FractionRing Sₘ)]

set_option backward.isDefEq.respectTransparency false in
include R S in
/--
theorem `FractionRing.isSeparable_of_isLocalization` / 定理 `FractionRing.isSeparable_of_isLocalization`

English:
theorem FractionRing.isSeparable_of_isLocalization
  given: (hM : M <= R⁰)
  proof: by
  let M' := algebraMapSubmonoid S M
  have hM' : algebraMapSubmonoid S M <= S⁰ := algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul
    _ hM
  let f₁ : Rₘ ->+* K := map _ (T := R⁰) (RingHom.id R) hM
  let f₂ : Sₘ ->+* L := map _ (T := S⁰) (RingHom.id S) hM'
  algebraize [f₁, f₂]
  have := lo

中文:
定理 FractionRing.isSeparable_of_isLocalization
  条件: (hM : M <= R⁰)
  证明: by
  let M' := algebraMapSubmonoid S M
  have hM' : algebraMapSubmonoid S M <= S⁰ := algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul
    _ hM
  let f₁ : Rₘ ->+* K := map _ (T := R⁰) (RingHom.id R) hM
  let f₂ : Sₘ ->+* L := map _ (T := S⁰) (RingHom.id S) hM'
  algebraize [f₁, f₂]
  have := lo

Depends on / 依赖: RingHom, RingHom.id, algebraMapSubmonoid, algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul, algebraize, isFractionRing_of_isDomain_of_i, isFractionRing_of_isDomain_of_isLocalization, localization_isScalarTower_of_submonoid_le
-/
theorem FractionRing.isSeparable_of_isLocalization (hM : M <= R⁰) :
    Algebra.IsSeparable (FractionRing Rₘ) (FractionRing Sₘ) := by
  let M' := algebraMapSubmonoid S M
  have hM' : algebraMapSubmonoid S M <= S⁰ := algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul
    _ hM
  let f₁ : Rₘ ->+* K := map _ (T := R⁰) (RingHom.id R) hM
  let f₂ : Sₘ ->+* L := map _ (T := S⁰) (RingHom.id S) hM'
  algebraize [f₁, f₂]
  have := localization_isScalarTower_of_submonoid_le Rₘ K _ _ hM
  have := localization_isScalarTower_of_submonoid_le Sₘ L _ _ hM'
  have := isFractionRing_of_isDomain_of_isLocalization M Rₘ K
  have := isFractionRing_of_isDomain_of_isLocalization M' Sₘ L
  have : IsDomain Rₘ := isDomain_of_le_nonZeroDivisors _ hM
  apply Algebra.IsSeparable.of_equiv_equiv (FractionRing.algEquiv Rₘ K).symm.toRingEquiv
    (FractionRing.algEquiv Sₘ L).symm.toRingEquiv
  apply ringHom_ext R⁰
  ext
  simp only [RingHom.coe_comp,
      RingHom.coe_coe, Function.comp_apply, ← algebraMap_apply]
  rw [algebraMap_apply R Rₘ (FractionRing R)]; rw [AlgEquiv.coe_ringEquiv]; rw [AlgEquiv.commutes]; rw [algebraMap_apply R S L]; rw [algebraMap_apply S Sₘ L]; rw [AlgEquiv.coe_ringEquiv]; rw [AlgEquiv.commutes]
  simp only [← algebraMap_apply]
  rw [algebraMap_apply R Rₘ (FractionRing Rₘ)]; rw [← algebraMap_apply Rₘ]; rw [← algebraMap_apply]

end

variable {P : Ideal R} [P.IsPrime]

local notation3 "P'" => algebraMapSubmonoid S P.primeCompl
local notation3 "Rₚ" => Localization.AtPrime P
local notation3 "Sₚ" => Localization P'

variable [FaithfulSMul R S]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsTorsionFree S Sₚ
  body: by
  rw [isTorsionFree_iff_algebraMap_injective]; rw [injective_iff_isRegular (algebraMapSubmonoid S P.primeCompl)]
exact fun ⟨x, hx⟩ => isRegular_iff_ne_zero'.mpr
ne_of_mem_of_not_mem hx by simp [Algebra.algebraMapSubmonoid]

中文:
实例 :
  签名: IsTorsionFree S Sₚ
  定义体: by
  rw [isTorsionFree_iff_algebraMap_injective]; rw [injective_iff_isRegular (algebraMapSubmonoid S P.primeCompl)]
exact fun ⟨x, hx⟩ => isRegular_iff_ne_zero'.mpr
ne_of_mem_of_not_mem hx by simp [Algebra.algebraMapSubmonoid]

Depends on / 依赖: Algebra, Algebra.algebraMapSubmonoid, P.primeCompl, algebraMapSubmonoid, injective_iff_isRegular, isRegular_iff_ne_zero, isTorsionFree_iff_algebraMap_injective, ne_of_mem_of_not_mem, primeCompl
-/
instance : IsTorsionFree S Sₚ := by
  rw [isTorsionFree_iff_algebraMap_injective]; rw [injective_iff_isRegular (algebraMapSubmonoid S P.primeCompl)]
exact fun ⟨x, hx⟩ => isRegular_iff_ne_zero'.mpr
ne_of_mem_of_not_mem hx by simp [Algebra.algebraMapSubmonoid]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsTorsionFree R Sₚ
  body: by
  have := IsLocalization.AtPrime.faithfulSMul Rₚ R P
  exact IsTorsionFree.trans_faithfulSMul R Rₚ _

中文:
实例 :
  签名: IsTorsionFree R Sₚ
  定义体: by
  have := IsLocalization.AtPrime.faithfulSMul Rₚ R P
  exact IsTorsionFree.trans_faithfulSMul R Rₚ _

Depends on / 依赖: AtPrime, IsLocalization, IsLocalization.AtPrime.faithfulSMul, IsTorsionFree, IsTorsionFree.trans_faithfulSMul, faithfulSMul, trans_faithfulSMul
-/
instance : IsTorsionFree R Sₚ := by
  have := IsLocalization.AtPrime.faithfulSMul Rₚ R P
  exact IsTorsionFree.trans_faithfulSMul R Rₚ _

/--
Definition of `Localization.AtPrime.liftAlgebra` / `Localization.AtPrime.liftAlgebra` 的定义

English:
abbreviation Localization.AtPrime.liftAlgebra
  signature: : Algebra Sₚ L
  body: (map _ (T := S⁰) (RingHom.id S)
    (algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _
      P.primeCompl_le_nonZeroDivisors)).toAlgebra

中文:
缩写 Localization.AtPrime.liftAlgebra
  签名: : Algebra Sₚ L
  定义体: (map _ (T := S⁰) (RingHom.id S)
    (algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _
      P.primeCompl_le_nonZeroDivisors)).toAlgebra

Depends on / 依赖: P.primeCompl_le_nonZeroDivisors, RingHom, RingHom.id, algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul, primeCompl_le_nonZeroDivisors, toAlgebra
-/
noncomputable abbrev Localization.AtPrime.liftAlgebra : Algebra Sₚ L :=
  (map _ (T := S⁰) (RingHom.id S)
    (algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _
      P.primeCompl_le_nonZeroDivisors)).toAlgebra

attribute [local instance] Localization.AtPrime.liftAlgebra

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsScalarTower S Sₚ L
  body: localization_isScalarTower_of_submonoid_le _ _ _ _
    (algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _
      P.primeCompl_le_nonZeroDivisors)

中文:
实例 :
  签名: IsScalarTower S Sₚ L
  定义体: localization_isScalarTower_of_submonoid_le _ _ _ _
    (algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _
      P.primeCompl_le_nonZeroDivisors)

Depends on / 依赖: P.primeCompl_le_nonZeroDivisors, algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul, localization_isScalarTower_of_submonoid_le, primeCompl_le_nonZeroDivisors
-/
instance : IsScalarTower S Sₚ L :=
  localization_isScalarTower_of_submonoid_le _ _ _ _
    (algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _
      P.primeCompl_le_nonZeroDivisors)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsFractionRing Rₚ K
  body: isFractionRing_of_isDomain_of_isLocalization P.primeCompl _ _

中文:
实例 :
  签名: IsFractionRing Rₚ K
  定义体: isFractionRing_of_isDomain_of_isLocalization P.primeCompl _ _

Depends on / 依赖: P.primeCompl, isFractionRing_of_isDomain_of_isLocalization, primeCompl
-/
instance : IsFractionRing Rₚ K :=
  isFractionRing_of_isDomain_of_isLocalization P.primeCompl _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsFractionRing Sₚ L
  body: isFractionRing_of_isDomain_of_isLocalization P' _ _

中文:
实例 :
  签名: IsFractionRing Sₚ L
  定义体: isFractionRing_of_isDomain_of_isLocalization P' _ _

Depends on / 依赖: isFractionRing_of_isDomain_of_isLocalization
-/
instance : IsFractionRing Sₚ L :=
  isFractionRing_of_isDomain_of_isLocalization P' _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra Rₚ L
  body: (lift (M := P.primeCompl) (g := algebraMap R L) <|
fun ⟨x, hx⟩ => by simpa using fun h => hx by simp [h]).toAlgebra

中文:
实例 :
  签名: Algebra Rₚ L
  定义体: (lift (M := P.primeCompl) (g := algebraMap R L) <|
fun ⟨x, hx⟩ => by simpa using fun h => hx by simp [h]).toAlgebra

Depends on / 依赖: P.primeCompl, algebraMap, primeCompl, toAlgebra
-/
noncomputable instance : Algebra Rₚ L :=
  (lift (M := P.primeCompl) (g := algebraMap R L) <|
fun ⟨x, hx⟩ => by simpa using fun h => hx by simp [h]).toAlgebra

-- Make sure there are no diamonds in the case `R = S`.
example : instAlgebraLocalizationAtPrime P = instAlgebraAtPrimeFractionRing (S := R) := by
  with_reducible_and_instances rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsScalarTower Rₚ K L
  body: of_algebraMap_eq' (ringHom_ext P.primeCompl
    (RingHom.ext fun x => by simp [RingHom.algebraMap_toAlgebra]))

中文:
实例 :
  签名: IsScalarTower Rₚ K L
  定义体: of_algebraMap_eq' (ringHom_ext P.primeCompl
    (RingHom.ext fun x => by simp [RingHom.algebraMap_toAlgebra]))

Depends on / 依赖: P.primeCompl, RingHom, RingHom.algebraMap_toAlgebra, RingHom.ext, algebraMap_toAlgebra, of_algebraMap_eq, primeCompl, ringHom_ext
-/
instance : IsScalarTower Rₚ K L :=
  of_algebraMap_eq' (ringHom_ext P.primeCompl
    (RingHom.ext fun x => by simp [RingHom.algebraMap_toAlgebra]))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsScalarTower R Rₚ K
  body: of_algebraMap_eq' (RingHom.ext fun x => by simp [RingHom.algebraMap_toAlgebra])

中文:
实例 :
  签名: IsScalarTower R Rₚ K
  定义体: of_algebraMap_eq' (RingHom.ext fun x => by simp [RingHom.algebraMap_toAlgebra])

Depends on / 依赖: RingHom, RingHom.algebraMap_toAlgebra, RingHom.ext, algebraMap_toAlgebra, of_algebraMap_eq
-/
instance : IsScalarTower R Rₚ K :=
  of_algebraMap_eq' (RingHom.ext fun x => by simp [RingHom.algebraMap_toAlgebra])

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsScalarTower Rₚ Sₚ L
  body: by
refine IsScalarTower.of_algebraMap_eq' IsLocalization.ringHom_ext P.primeCompl ?_
  rw [RingHom.comp_assoc]; rw [← IsScalarTower.algebraMap_eq R Rₚ Sₚ]; rw [IsScalarTower.algebraMap_eq R S Sₚ]; rw [← RingHom.comp_assoc]; rw [← IsScalarTower.algebraMap_eq S Sₚ L]; rw [IsScalarTower.algebraMap_eq R

中文:
实例 :
  签名: IsScalarTower Rₚ Sₚ L
  定义体: by
refine IsScalarTower.of_algebraMap_eq' IsLocalization.ringHom_ext P.primeCompl ?_
  rw [RingHom.comp_assoc]; rw [← IsScalarTower.algebraMap_eq R Rₚ Sₚ]; rw [IsScalarTower.algebraMap_eq R S Sₚ]; rw [← RingHom.comp_assoc]; rw [← IsScalarTower.algebraMap_eq S Sₚ L]; rw [IsScalarTower.algebraMap_eq R

Depends on / 依赖: IsLocalization, IsLocalization.ringHom_ext, IsScalarTower, IsScalarTower.algebraMap_eq, IsScalarTower.of_algebraMap_eq, P.primeCompl, RingHom, RingHom.comp_assoc, algebraMap_eq, comp_assoc, of_algebraMap_eq, primeCompl, ringHom_ext
-/
instance : IsScalarTower Rₚ Sₚ L := by
refine IsScalarTower.of_algebraMap_eq' IsLocalization.ringHom_ext P.primeCompl ?_
  rw [RingHom.comp_assoc]; rw [← IsScalarTower.algebraMap_eq R Rₚ Sₚ]; rw [IsScalarTower.algebraMap_eq R S Sₚ]; rw [← RingHom.comp_assoc]; rw [← IsScalarTower.algebraMap_eq S Sₚ L]; rw [IsScalarTower.algebraMap_eq Rₚ K L]; rw [RingHom.comp_assoc]; rw [← IsScalarTower.algebraMap_eq]; rw [← IsScalarTower.algebraMap_eq]; rw [← IsScalarTower.algebraMap_eq]

set_option linter.overlappingInstances false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsDedekindDomain
  signature: S] : IsDedekindDomain Sₚ
  body: isDedekindDomain S
    (algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _ P.primeCompl_le_nonZeroDivisors) _

中文:
实例 [IsDedekindDomain
  签名: S] : IsDedekindDomain Sₚ
  定义体: isDedekindDomain S
    (algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _ P.primeCompl_le_nonZeroDivisors) _

Depends on / 依赖: P.primeCompl_le_nonZeroDivisors, algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul, isDedekindDomain, primeCompl_le_nonZeroDivisors
-/
instance [IsDedekindDomain S] : IsDedekindDomain Sₚ :=
  isDedekindDomain S
    (algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _ P.primeCompl_le_nonZeroDivisors) _

set_option linter.overlappingInstances false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsDedekindDomain
  signature: R] [IsDedekindDomain S] [Module.Finite R S] [hP
  body: IsDedekindDomain.isPrincipalIdealRing_localization_over_prime S P (fun h => hP.1 h)

中文:
实例 [IsDedekindDomain
  签名: R] [IsDedekindDomain S] [Module.Finite R S] [hP
  定义体: IsDedekindDomain.isPrincipalIdealRing_localization_over_prime S P (fun h => hP.1 h)

Depends on / 依赖: IsDedekindDomain, IsDedekindDomain.isPrincipalIdealRing_localization_over_prime, isPrincipalIdealRing_localization_over_prime
-/
instance [IsDedekindDomain R] [IsDedekindDomain S] [Module.Finite R S] [hP : NeZero P] :
    IsPrincipalIdealRing Sₚ :=
  IsDedekindDomain.isPrincipalIdealRing_localization_over_prime S P (fun h => hP.1 h)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Algebra.IsSeparable
  signature: K L] :
  body: OreLocalization.instAlgebra
    Algebra.IsSeparable (FractionRing Rₚ) (FractionRing Sₚ) :=
  let _ : Algebra Rₚ (FractionRing Sₚ) := OreLocalization.instAlgebra
  FractionRing.isSeparable_of_isLocalization S _ _ P.primeCompl_le_nonZeroDivisors

local notation3 "P''" => algebraMapSubmonoid T P.primeC

中文:
实例 [Algebra.IsSeparable
  签名: K L] :
  定义体: OreLocalization.instAlgebra
    Algebra.IsSeparable (FractionRing Rₚ) (FractionRing Sₚ) :=
  let _ : Algebra Rₚ (FractionRing Sₚ) := OreLocalization.instAlgebra
  FractionRing.isSeparable_of_isLocalization S _ _ P.primeCompl_le_nonZeroDivisors

local notation3 "P''" => algebraMapSubmonoid T P.primeC

Depends on / 依赖: OreLocalization, OreLocalization.instAlgebra, instAlgebra
-/
instance [Algebra.IsSeparable K L] :
    -- Without the following line there is a timeout
    letI : Algebra Rₚ (FractionRing Sₚ) := OreLocalization.instAlgebra
    Algebra.IsSeparable (FractionRing Rₚ) (FractionRing Sₚ) :=
  let _ : Algebra Rₚ (FractionRing Sₚ) := OreLocalization.instAlgebra
  FractionRing.isSeparable_of_isLocalization S _ _ P.primeCompl_le_nonZeroDivisors

local notation3 "P''" => algebraMapSubmonoid T P.primeCompl
local notation3 "Tₚ" => Localization P''

variable [Algebra S T] [Algebra R T] [IsScalarTower R S T]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsLocalization (algebraMapSubmonoid T P') Tₚ
  body: by
  rw [show algebraMapSubmonoid T P' = P'' by simp]
  exact Localization.isLocalization

中文:
实例 :
  签名: IsLocalization (algebraMapSubmonoid T P') Tₚ
  定义体: by
  rw [show algebraMapSubmonoid T P' = P'' by simp]
  exact Localization.isLocalization

Depends on / 依赖: Localization, Localization.isLocalization, algebraMapSubmonoid, isLocalization
-/
instance : IsLocalization (algebraMapSubmonoid T P') Tₚ := by
  rw [show algebraMapSubmonoid T P' = P'' by simp]
  exact Localization.isLocalization

/--
Definition of `Localization.AtPrime.algebra_localization_localization` / `Localization.AtPrime.algebra_localization_localization` 的定义

English:
abbreviation Localization.AtPrime.algebra_localization_localization
  signature: :
  body: localizationAlgebra P' T

中文:
缩写 Localization.AtPrime.algebra_localization_localization
  签名: :
  定义体: localizationAlgebra P' T

Depends on / 依赖: localizationAlgebra
-/
noncomputable abbrev Localization.AtPrime.algebra_localization_localization :
    Algebra Sₚ Tₚ := localizationAlgebra P' T

attribute [local instance] Localization.AtPrime.algebra_localization_localization

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsScalarTower S Sₚ Tₚ
  body: IsScalarTower.of_algebraMap_eq'
    by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, ← IsScalarTower.algebraMap_eq]

中文:
实例 :
  签名: IsScalarTower S Sₚ Tₚ
  定义体: IsScalarTower.of_algebraMap_eq'
    by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, ← IsScalarTower.algebraMap_eq]

Depends on / 依赖: IsLocalization, IsLocalization.map_comp, IsScalarTower, IsScalarTower.algebraMap_eq, IsScalarTower.of_algebraMap_eq, RingHom, RingHom.algebraMap_toAlgebra, algebraMap_eq, algebraMap_toAlgebra, map_comp, of_algebraMap_eq
-/
instance : IsScalarTower S Sₚ Tₚ :=
IsScalarTower.of_algebraMap_eq'
    by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, ← IsScalarTower.algebraMap_eq]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsScalarTower R Sₚ Tₚ
  body: IsScalarTower.of_algebraMap_eq'
    by rw [IsScalarTower.algebraMap_eq R S Sₚ, ← RingHom.comp_assoc,
      ← IsScalarTower.algebraMap_eq S, ← IsScalarTower.algebraMap_eq]

中文:
实例 :
  签名: IsScalarTower R Sₚ Tₚ
  定义体: IsScalarTower.of_algebraMap_eq'
    by rw [IsScalarTower.algebraMap_eq R S Sₚ, ← RingHom.comp_assoc,
      ← IsScalarTower.algebraMap_eq S, ← IsScalarTower.algebraMap_eq]

Depends on / 依赖: IsScalarTower, IsScalarTower.algebraMap_eq, IsScalarTower.of_algebraMap_eq, RingHom, RingHom.comp_assoc, algebraMap_eq, comp_assoc, of_algebraMap_eq
-/
instance : IsScalarTower R Sₚ Tₚ :=
IsScalarTower.of_algebraMap_eq'
    by rw [IsScalarTower.algebraMap_eq R S Sₚ, ← RingHom.comp_assoc,
      ← IsScalarTower.algebraMap_eq S, ← IsScalarTower.algebraMap_eq]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Module.Finite
  signature: S T] : Module.Finite Sₚ Tₚ
  body: Module.Finite.of_isLocalization S T P'

中文:
实例 [Module.Finite
  签名: S T] : Module.Finite Sₚ Tₚ
  定义体: Module.Finite.of_isLocalization S T P'

Depends on / 依赖: Finite, Module, Module.Finite.of_isLocalization, of_isLocalization
-/
instance [Module.Finite S T] : Module.Finite Sₚ Tₚ := Module.Finite.of_isLocalization S T P'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsTorsionFree
  signature: S T] : IsTorsionFree Sₚ Tₚ
  body: .of_isLocalization S T algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _
    Ideal.primeCompl_le_nonZeroDivisors P

中文:
实例 [IsTorsionFree
  签名: S T] : IsTorsionFree Sₚ Tₚ
  定义体: .of_isLocalization S T algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _
    Ideal.primeCompl_le_nonZeroDivisors P

Depends on / 依赖: Ideal.primeCompl_le_nonZeroDivisors, algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul, of_isLocalization, primeCompl_le_nonZeroDivisors
-/
instance [IsTorsionFree S T] : IsTorsionFree Sₚ Tₚ :=
.of_isLocalization S T algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _
    Ideal.primeCompl_le_nonZeroDivisors P

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Algebra.IsIntegral
  signature: R S] : Algebra.IsIntegral Rₚ Sₚ
  body: Algebra.isIntegral_def.mpr (algebraMap_eq_map_map_submonoid P.primeCompl S Rₚ Sₚ ▸
    isIntegral_localization : (algebraMap Rₚ Sₚ).IsIntegral)

中文:
实例 [Algebra.IsIntegral
  签名: R S] : Algebra.Is整数egral Rₚ Sₚ
  定义体: Algebra.isIntegral_def.mpr (algebraMap_eq_map_map_submonoid P.primeCompl S Rₚ Sₚ ▸
    isIntegral_localization : (algebraMap Rₚ Sₚ).IsIntegral)

Depends on / 依赖: Algebra, Algebra.isIntegral_def.mpr, IsIntegral, P.primeCompl, algebraMap, algebraMap_eq_map_map_submonoid, isIntegral_def, isIntegral_localization, primeCompl
-/
instance [Algebra.IsIntegral R S] : Algebra.IsIntegral Rₚ Sₚ :=
Algebra.isIntegral_def.mpr (algebraMap_eq_map_map_submonoid P.primeCompl S Rₚ Sₚ ▸
    isIntegral_localization : (algebraMap Rₚ Sₚ).IsIntegral)

variable [IsTorsionFree R T]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsScalarTower Rₚ Sₚ Tₚ
  body: by
  refine ⟨fun a b c => a.ind fun ⟨a₁, a₂⟩ => ?_⟩
have : a₂.val != 0 := nonZeroDivisors.ne_zero Ideal.primeCompl_le_nonZeroDivisors P a₂.prop
  rw [← smul_right_inj this]; rw [← _root_.smul_assoc (M := R) (N := Sₚ)]; rw [← _root_.smul_assoc (M := R)
    (α := Sₚ)]; rw [← _root_.smul_assoc (M := R)

中文:
实例 :
  签名: IsScalarTower Rₚ Sₚ Tₚ
  定义体: by
  refine ⟨fun a b c => a.ind fun ⟨a₁, a₂⟩ => ?_⟩
have : a₂.val != 0 := nonZeroDivisors.ne_zero Ideal.primeCompl_le_nonZeroDivisors P a₂.prop
  rw [← smul_right_inj this]; rw [← _root_.smul_assoc (M := R) (N := Sₚ)]; rw [← _root_.smul_assoc (M := R)
    (α := Sₚ)]; rw [← _root_.smul_assoc (M := R)

Depends on / 依赖: Ideal.primeCompl_le_nonZeroDivisors, IsLocalization, IsLocalization.mk, Localization, Localization.mk_eq_mk, Localization.smul_mk, _mul_cancel_left, _root_, _root_.smul_assoc, a.ind, algebraMap_smul, mk_eq_mk, ne_zero, nonZeroDivisors, nonZeroDivisors.ne_zero, primeCompl_le_nonZeroDivisors, smul_assoc, smul_eq_mul, smul_mk, smul_right_inj
-/
instance : IsScalarTower Rₚ Sₚ Tₚ := by
  refine ⟨fun a b c => a.ind fun ⟨a₁, a₂⟩ => ?_⟩
have : a₂.val != 0 := nonZeroDivisors.ne_zero Ideal.primeCompl_le_nonZeroDivisors P a₂.prop
  rw [← smul_right_inj this]; rw [← _root_.smul_assoc (M := R) (N := Sₚ)]; rw [← _root_.smul_assoc (M := R)
    (α := Sₚ)]; rw [← _root_.smul_assoc (M := R) (α := Tₚ)]; rw [Localization.smul_mk]; rw [smul_eq_mul]; rw [Localization.mk_eq_mk']; rw [IsLocalization.mk'_mul_cancel_left]; rw [algebraMap_smul]; rw [algebraMap_smul]; rw [_root_.smul_assoc]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsTorsionFree
  signature: S T] [Algebra.IsSeparable L F] :
  body: by
  refine FractionRing.isSeparable_of_isLocalization T Sₚ Tₚ (M := P') ?_
  apply algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul
exact fun _ h => mem_nonZeroDivisors_of_ne_zero ne_of_mem_of_not_mem h by simp

中文:
实例 [IsTorsionFree
  签名: S T] [Algebra.IsSeparable L F] :
  定义体: by
  refine FractionRing.isSeparable_of_isLocalization T Sₚ Tₚ (M := P') ?_
  apply algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul
exact fun _ h => mem_nonZeroDivisors_of_ne_zero ne_of_mem_of_not_mem h by simp

Depends on / 依赖: FractionRing, FractionRing.isSeparable_of_isLocalization, algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul, isSeparable_of_isLocalization, mem_nonZeroDivisors_of_ne_zero, ne_of_mem_of_not_mem
-/
instance [IsTorsionFree S T] [Algebra.IsSeparable L F] :
    Algebra.IsSeparable (FractionRing Sₚ) (FractionRing Tₚ) := by
  refine FractionRing.isSeparable_of_isLocalization T Sₚ Tₚ (M := P') ?_
  apply algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul
exact fun _ h => mem_nonZeroDivisors_of_ne_zero ne_of_mem_of_not_mem h by simp
