/-
Copyright (c) 2020 Kenji Nakagawa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenji Nakagawa, Anne Baanen, Filippo A. E. Nuccio
-/
module

public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Dedekind rings and domains

This file defines the notion of a Dedekind ring (domain),
as a Noetherian integrally closed commutative ring (domain) of Krull dimension at most one.

## Main definitions

- `IsDedekindRing` defines a Dedekind ring as a commutative ring that is
  Noetherian, integrally closed in its field of fractions and has Krull dimension at most one.
  `isDedekindRing_iff` shows that this does not depend on the choice of field of fractions.
- `IsDedekindDomain` defines a Dedekind domain as a Dedekind ring that is a domain.

## Implementation notes

The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice. The `..._iff` lemmas express this independence.

`IsDedekindRing` and `IsDedekindDomain` form a cycle in the typeclass hierarchy:
`IsDedekindRing R + IsDomain R` imply `IsDedekindDomain R`, which implies `IsDedekindRing R`.
This should be safe since the start and end point is the literal same expression,
which the tabled typeclass synthesis algorithm can deal with.

Often, definitions assume that Dedekind rings are not fields. We found it more practical
to add a `(h : ¬ IsField A)` assumption whenever this is explicitly needed.

## References

* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags

dedekind domain, dedekind ring
-/

public section


variable (R A K : Type*) [CommRing R] [CommRing A] [Field K]

open scoped nonZeroDivisors Polynomial

/--
Definition of `Ring.DimensionLEOne` / `Ring.DimensionLEOne` 的定义

English:
class Ring.DimensionLEOne
  parameters: : Prop where
  axioms and operations (1):
    - (maximalOfPrime : forall {p : Ideal R}, p != ⊥ -> p.IsPrime -> p.IsMaximal)

中文:
类 Ring.DimensionLEOne
  参数: : 命题 where
  公理与运算 (1 个):
    - (maximalOfPrime : 对任意 {p : Ideal R}, p != ⊥ -> p.IsPrime -> p.IsMaximal)
-/
class Ring.DimensionLEOne : Prop where
  (maximalOfPrime : forall {p : Ideal R}, p != ⊥ -> p.IsPrime -> p.IsMaximal)

open Ideal Ring

/--
theorem `Ideal.IsPrime.isMaximal` / 定理 `Ideal.IsPrime.isMaximal`

English:
theorem Ideal.IsPrime.isMaximal
  statement: {R : Type*} [CommRing R] [DimensionLEOne R]
  proof: DimensionLEOne.maximalOfPrime hp h

中文:
定理 Ideal.IsPrime.isMaximal
  结论: {R : 类型} [CommRing R] [DimensionLEOne R]
  证明: DimensionLEOne.maximalOfPrime hp h

Depends on / 依赖: DimensionLEOne, DimensionLEOne.maximalOfPrime, maximalOfPrime
-/
theorem Ideal.IsPrime.isMaximal {R : Type*} [CommRing R] [DimensionLEOne R]
    {p : Ideal R} (h : p.IsPrime) (hp : p != ⊥) : p.IsMaximal :=
  DimensionLEOne.maximalOfPrime hp h

namespace Ring.DimensionLEOne

/--
Instance `principal_ideal_ring` / 实例 `principal_ideal_ring`

English:
instance principal_ideal_ring
  signature: [IsDomain A] [IsPrincipalIdealRing A]
  body: fun nonzero _ =>
    IsPrime.to_maximal_ideal nonzero

中文:
实例 principal_ideal_ring
  签名: [IsDomain A] [IsPrincipalIdealRing A]
  定义体: fun nonzero _ =>
    IsPrime.to_maximal_ideal nonzero

Depends on / 依赖: nonzero
-/
instance principal_ideal_ring [IsDomain A] [IsPrincipalIdealRing A] :
    DimensionLEOne A where
  maximalOfPrime := fun nonzero _ =>
    IsPrime.to_maximal_ideal nonzero

/--
theorem `of_isIntegral` / 定理 `of_isIntegral`

English:
theorem of_isIntegral
  statement: (B : Type*) [CommRing B] [IsDomain B] [Nontrivial R]
  proof: fun {p} ne_bot _ =>
    IsIntegral.isMaximal_of_isMaximal_comap p
      (Ideal.IsPrime.isMaximal inferInstance (IsIntegral.comap_ne_bot R ne_bot))

@[deprecated (since := "2026-05-08")] alias isIntegralClosure := of_isIntegral

nonrec instance integralClosure [Nontrivial R] [IsDomain A] [Algebra R A

中文:
定理 of_isIntegral
  结论: (B : 类型) [CommRing B] [IsDomain B] [Nontrivial R]
  证明: fun {p} ne_bot _ =>
    IsIntegral.isMaximal_of_isMaximal_comap p
      (Ideal.IsPrime.isMaximal inferInstance (IsIntegral.comap_ne_bot R ne_bot))

@[deprecated (since := "2026-05-08")] alias isIntegralClosure := of_isIntegral

nonrec instance integralClosure [Nontrivial R] [IsDomain A] [Algebra R A

Depends on / 依赖: ne_bot
-/
theorem of_isIntegral (B : Type*) [CommRing B] [IsDomain B] [Nontrivial R]
    [Algebra R B] [Algebra.IsIntegral R B] [DimensionLEOne R] :
    DimensionLEOne B where
  maximalOfPrime := fun {p} ne_bot _ =>
    IsIntegral.isMaximal_of_isMaximal_comap p
      (Ideal.IsPrime.isMaximal inferInstance (IsIntegral.comap_ne_bot R ne_bot))

@[deprecated (since := "2026-05-08")] alias isIntegralClosure := of_isIntegral

nonrec instance integralClosure [Nontrivial R] [IsDomain A] [Algebra R A] [DimensionLEOne R] :
    DimensionLEOne (integralClosure R A) :=
  DimensionLEOne.of_isIntegral R (integralClosure R A)

variable {R}

/--
theorem `not_lt_lt` / 定理 `not_lt_lt`

English:
theorem not_lt_lt
  statement: [Ring.DimensionLEOne R] (p₀ p₁ p₂ : Ideal R) [hp₁ : p₁.IsPrime]

中文:
定理 not_lt_lt
  结论: [Ring.DimensionLEOne R] (p₀ p₁ p₂ : Ideal R) [hp₁ : p₁.IsPrime]
-/
theorem not_lt_lt [Ring.DimensionLEOne R] (p₀ p₁ p₂ : Ideal R) [hp₁ : p₁.IsPrime]
    [hp₂ : p₂.IsPrime] : ¬(p₀ < p₁ ∧ p₁ < p₂)
  | ⟨h01, h12⟩ => h12.ne ((hp₁.isMaximal (bot_le.trans_lt h01).ne').eq_of_le hp₂.ne_top h12.le)

/--
theorem `eq_bot_of_lt` / 定理 `eq_bot_of_lt`

English:
theorem eq_bot_of_lt
  given: [Ring.DimensionLEOne R] (p P : Ideal R) [p.IsPrime] [P.IsPrime] (hpP : p < P)
  proof: by_contra fun hp0 => not_lt_lt ⊥ p P ⟨Ne.bot_lt hp0, hpP⟩

中文:
定理 eq_bot_of_lt
  条件: [Ring.DimensionLEOne R] (p P : Ideal R) [p.IsPrime] [P.IsPrime] (hpP : p < P)
  证明: by_contra fun hp0 => not_lt_lt ⊥ p P ⟨Ne.bot_lt hp0, hpP⟩

Depends on / 依赖: Ne.bot_lt, bot_lt, not_lt_lt
-/
theorem eq_bot_of_lt [Ring.DimensionLEOne R] (p P : Ideal R) [p.IsPrime] [P.IsPrime] (hpP : p < P) :
    p = ⊥ :=
  by_contra fun hp0 => not_lt_lt ⊥ p P ⟨Ne.bot_lt hp0, hpP⟩

variable {A} in
/--
theorem `of_ringEquiv` / 定理 `of_ringEquiv`

English:
theorem of_ringEquiv
  given: [hA : Ring.DimensionLEOne A] (e : R ≃+* A)
  statement: Ring.DimensionLEOne R where
  proof: by
    rw [← Ideal.map_comap_eq_self_of_equiv e.symm P]; rw [Ideal.isMaximal_map_iff_of_bijective _ e.symm.bijective]
    apply Ring.DimensionLEOne.maximalOfPrime ?_ (P.comap_isPrime e.symm)
    simp [Ideal.map_eq_bot_iff_of_injective e.injective, hP_ne]

中文:
定理 of_ringEquiv
  条件: [hA : Ring.DimensionLEOne A] (e : R ≃+* A)
  结论: Ring.DimensionLEOne R where
  证明: by
    rw [← Ideal.map_comap_eq_self_of_equiv e.symm P]; rw [Ideal.isMaximal_map_iff_of_bijective _ e.symm.bijective]
    apply Ring.DimensionLEOne.maximalOfPrime ?_ (P.comap_isPrime e.symm)
    simp [Ideal.map_eq_bot_iff_of_injective e.injective, hP_ne]

Depends on / 依赖: DimensionLEOne, Ideal.isMaximal_map_iff_of_bijective, Ideal.map_comap_eq_self_of_equiv, Ideal.map_eq_bot_iff_of_injective, P.comap_isPrime, Ring.DimensionLEOne.maximalOfPrime, bijective, comap_isPrime, e.injective, e.symm, e.symm.bijective, hP_ne, injective, isMaximal_map_iff_of_bijective, map_comap_eq_self_of_equiv, map_eq_bot_iff_of_injective, maximalOfPrime
-/
theorem of_ringEquiv [hA : Ring.DimensionLEOne A] (e : R ≃+* A) : Ring.DimensionLEOne R where
  maximalOfPrime {P} hP_ne hP_prime := by
    rw [← Ideal.map_comap_eq_self_of_equiv e.symm P]; rw [Ideal.isMaximal_map_iff_of_bijective _ e.symm.bijective]
    apply Ring.DimensionLEOne.maximalOfPrime ?_ (P.comap_isPrime e.symm)
    simp [Ideal.map_eq_bot_iff_of_injective e.injective, hP_ne]

-- TODO: replace `Ring.DimensionLEOne` with `Ring.KrullDimLE`.
instance (priority := low) {R : Type*} [CommRing R] [Ring.DimensionLEOne R] : Ring.KrullDimLE 1 R :=
  .mk₁' fun _ hI hI' => hI'.isMaximal hI

end Ring.DimensionLEOne

/--
Definition of `IsDedekindRing` / `IsDedekindRing` 的定义

English:
class IsDedekindRing
  parameters: : Prop
  extends: IsNoetherian A A, DimensionLEOne A, IsIntegralClosure A A (FractionRing A)
  (no additional axioms)

中文:
类 IsDedekindRing
  参数: : 命题
  继承: IsNoetherian A A, DimensionLEOne A, IsIntegralClosure A A (FractionRing A)
  (无附加公理)
-/
class IsDedekindRing : Prop
  extends IsNoetherian A A, DimensionLEOne A, IsIntegralClosure A A (FractionRing A)

/--
theorem `isDedekindRing_iff` / 定理 `isDedekindRing_iff`

English:
theorem isDedekindRing_iff
  given: (K : Type*) [CommRing K] [Algebra A K] [IsFractionRing A K]
  proof: ⟨fun _ => ⟨inferInstance, inferInstance,
             fun {_} => (isIntegrallyClosed_iff K).mp inferInstance⟩,
   fun ⟨hr, hd, hi⟩ => { hr, hd, (isIntegrallyClosed_iff K).mpr @hi with }⟩

中文:
定理 isDedekindRing_iff
  条件: (K : 类型) [CommRing K] [Algebra A K] [IsFractionRing A K]
  证明: ⟨fun _ => ⟨inferInstance, inferInstance,
             fun {_} => (isIntegrallyClosed_iff K).mp inferInstance⟩,
   fun ⟨hr, hd, hi⟩ => { hr, hd, (isIntegrallyClosed_iff K).mpr @hi with }⟩

Depends on / 依赖: isIntegrallyClosed_iff
-/
theorem isDedekindRing_iff (K : Type*) [CommRing K] [Algebra A K] [IsFractionRing A K] :
    IsDedekindRing A ↔
      IsNoetherianRing A ∧ DimensionLEOne A ∧
        forall {x : K}, IsIntegral A x -> exists y, algebraMap A K y = x :=
  ⟨fun _ => ⟨inferInstance, inferInstance,
             fun {_} => (isIntegrallyClosed_iff K).mp inferInstance⟩,
   fun ⟨hr, hd, hi⟩ => { hr, hd, (isIntegrallyClosed_iff K).mpr @hi with }⟩

/--
Definition of `IsDedekindDomain` / `IsDedekindDomain` 的定义

English:
class IsDedekindDomain
  parameters: : Prop
  extends: IsDomain A, IsDedekindRing A
  (no additional axioms)

中文:
类 IsDedekindDomain
  参数: : 命题
  继承: IsDomain A, IsDedekindRing A
  (无附加公理)
-/
class IsDedekindDomain : Prop
  extends IsDomain A, IsDedekindRing A

attribute [instance 90] IsDedekindDomain.toIsDomain

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsDomain
  signature: A] [IsDedekindRing A] : IsDedekindDomain A where

中文:
实例 [IsDomain
  签名: A] [IsDedekindRing A] : IsDedekindDomain A where
-/
instance [IsDomain A] [IsDedekindRing A] : IsDedekindDomain A where

/--
theorem `isDedekindDomain_iff` / 定理 `isDedekindDomain_iff`

English:
theorem isDedekindDomain_iff
  given: (K : Type*) [CommRing K] [Algebra A K] [IsFractionRing A K]
  proof: ⟨fun _ => ⟨inferInstance, inferInstance, inferInstance,
             fun {_} => (isIntegrallyClosed_iff K).mp inferInstance⟩,
   fun ⟨hid, hr, hd, hi⟩ => { hid, hr, hd, (isIntegrallyClosed_iff K).mpr @hi with }⟩

中文:
定理 isDedekindDomain_iff
  条件: (K : 类型) [CommRing K] [Algebra A K] [IsFractionRing A K]
  证明: ⟨fun _ => ⟨inferInstance, inferInstance, inferInstance,
             fun {_} => (isIntegrallyClosed_iff K).mp inferInstance⟩,
   fun ⟨hid, hr, hd, hi⟩ => { hid, hr, hd, (isIntegrallyClosed_iff K).mpr @hi with }⟩

Depends on / 依赖: isIntegrallyClosed_iff
-/
theorem isDedekindDomain_iff (K : Type*) [CommRing K] [Algebra A K] [IsFractionRing A K] :
    IsDedekindDomain A ↔
      IsDomain A ∧ IsNoetherianRing A ∧ DimensionLEOne A ∧
        forall {x : K}, IsIntegral A x -> exists y, algebraMap A K y = x :=
  ⟨fun _ => ⟨inferInstance, inferInstance, inferInstance,
             fun {_} => (isIntegrallyClosed_iff K).mp inferInstance⟩,
   fun ⟨hid, hr, hd, hi⟩ => { hid, hr, hd, (isIntegrallyClosed_iff K).mpr @hi with }⟩

-- See library note [lower instance priority]
instance (priority := 100) IsPrincipalIdealRing.isDedekindDomain
    [IsDomain A] [IsPrincipalIdealRing A] :
    IsDedekindDomain A :=
  { PrincipalIdealRing.isNoetherianRing, Ring.DimensionLEOne.principal_ideal_ring A,
    UniqueFactorizationMonoid.instIsIntegrallyClosed with }

variable {R} in
/--
theorem `IsLocalRing.primesOver_eq` / 定理 `IsLocalRing.primesOver_eq`

English:
theorem IsLocalRing.primesOver_eq
  statement: [IsLocalRing A] [IsDedekindDomain A] [Algebra R A]
  proof: by
  have : IsDomain R := .of_faithfulSMul R A
  refine Set.eq_singleton_iff_nonempty_unique_mem.mpr ⟨?_, fun P hP => ?_⟩
  · obtain ⟨w', hmax, hover⟩ := exists_maximal_ideal_liesOver_of_isIntegral (S := A) p
    exact ⟨w', hmax.isPrime, hover⟩
· exact IsLocalRing.eq_maximalIdeal hP.1.isMaximal (Ide

中文:
定理 IsLocalRing.primesOver_eq
  结论: [IsLocalRing A] [IsDedekindDomain A] [Algebra R A]
  证明: by
  have : IsDomain R := .of_faithfulSMul R A
  refine Set.eq_singleton_iff_nonempty_unique_mem.mpr ⟨?_, fun P hP => ?_⟩
  · obtain ⟨w', hmax, hover⟩ := exists_maximal_ideal_liesOver_of_isIntegral (S := A) p
    exact ⟨w', hmax.isPrime, hover⟩
· exact IsLocalRing.eq_maximalIdeal hP.1.isMaximal (Ide

Depends on / 依赖: Ideal.ne_bot_of_mem_primesOver, IsDomain, IsLocalRing, IsLocalRing.eq_maximalIdeal, Set.eq_singleton_iff_nonempty_unique_mem.mpr, eq_maximalIdeal, eq_singleton_iff_nonempty_unique_mem, exists_maximal_ideal_liesOver_of_isIntegral, hmax.isPrime, isMaximal, isPrime, ne_bot_of_mem_primesOver, of_faithfulSMul
-/
theorem IsLocalRing.primesOver_eq [IsLocalRing A] [IsDedekindDomain A] [Algebra R A]
    [FaithfulSMul R A] [Module.Finite R A] {p : Ideal R} [p.IsMaximal] (hp0 : p != ⊥) :
    Ideal.primesOver p A = {IsLocalRing.maximalIdeal A} := by
  have : IsDomain R := .of_faithfulSMul R A
  refine Set.eq_singleton_iff_nonempty_unique_mem.mpr ⟨?_, fun P hP => ?_⟩
  · obtain ⟨w', hmax, hover⟩ := exists_maximal_ideal_liesOver_of_isIntegral (S := A) p
    exact ⟨w', hmax.isPrime, hover⟩
· exact IsLocalRing.eq_maximalIdeal hP.1.isMaximal (Ideal.ne_bot_of_mem_primesOver hp0 hP)
