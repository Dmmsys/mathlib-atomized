/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.Algebra.Ring.Hom.InjSurj

/-!
# Integrally closed rings

An integrally closed ring `R` contains all the elements of `Frac(R)` that are
integral over `R`. A special case of integrally closed rings are the Dedekind domains.

## Main definitions

* `IsIntegrallyClosedIn R A` states `R` contains all integral elements of `A`
* `IsIntegrallyClosed R` states `R` contains all integral elements of `Frac(R)`

## Main results

* `isIntegrallyClosed_iff K`, where `K` is a fraction field of `R`, states `R`
  is integrally closed iff it is the integral closure of `R` in `K`

## TODO Related notions

The following definitions are closely related, especially in their applications in Mathlib.

A *normal domain* is a domain that is integrally closed in its field of fractions.
[Stacks: normal domain](https://stacks.math.columbia.edu/tag/037B#0309)
Normal domains are the major use case of `IsIntegrallyClosed` at the time of writing, and we have
quite a few results that can be moved wholesale to a new `NormalDomain` definition.
In fact, before PR https://github.com/leanprover-community/mathlib4/pull/6126 `IsIntegrallyClosed` was exactly defined to be a normal domain.
(So you might want to copy some of its API when you define normal domains.)

A normal ring means that localizations at all prime ideals are normal domains.
[Stacks: normal ring](https://stacks.math.columbia.edu/tag/037B#00GV)
This implies `IsIntegrallyClosed`,
[Stacks: Tag 034M](https://stacks.math.columbia.edu/tag/037B#034M)
but is equivalent to it only under some conditions (reduced + finitely many minimal primes),
[Stacks: Tag 030C](https://stacks.math.columbia.edu/tag/037B#030C)
in which case it's also equivalent to being a finite product of normal domains.

We'd need to add these conditions if we want exactly the products of Dedekind domains.

In fact Noetherianity is sufficient to guarantee finitely many minimal primes, so `IsDedekindRing`
could be defined as `IsReduced`, `IsNoetherian`, `Ring.DimensionLEOne`, and either
`IsIntegrallyClosed` or `NormalDomain`. If we use `NormalDomain` then `IsReduced` is automatic,
but we could also consider a version of `NormalDomain` that only requires the localizations are
`IsIntegrallyClosed` but may not be domains, and that may not equivalent to the ring itself being
`IsIntegrallyClosed` (even for Noetherian rings?).
-/

public section


open scoped nonZeroDivisors Polynomial

open Polynomial

/--
Definition of `IsIntegrallyClosedIn` / `IsIntegrallyClosedIn` 的定义

English:
abbreviation IsIntegrallyClosedIn
  signature: (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
  body: IsIntegralClosure R R A

中文:
缩写 Is整数egrallyClosedIn
  签名: (R A : 类型) [交换环 R] [交换环 A] [代数 R A]
  定义体: IsIntegralClosure R R A

Depends on / 依赖: IsIntegralClosure
-/
abbrev IsIntegrallyClosedIn (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] :=
  IsIntegralClosure R R A

/--
Definition of `IsIntegrallyClosed` / `IsIntegrallyClosed` 的定义

English:
abbreviation IsIntegrallyClosed
  signature: (R : Type*) [CommRing R]
  body: IsIntegrallyClosedIn R (FractionRing R)

中文:
缩写 是整闭
  签名: (R : 类型) [交换环 R]
  定义体: IsIntegrallyClosedIn R (FractionRing R)

Depends on / 依赖: FractionRing, IsIntegrallyClosedIn
-/
abbrev IsIntegrallyClosed (R : Type*) [CommRing R] := IsIntegrallyClosedIn R (FractionRing R)

section Iff

variable {R : Type*} [CommRing R]
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/--
theorem `AlgHom.isIntegrallyClosedIn` / 定理 `AlgHom.isIntegrallyClosedIn`

English:
theorem AlgHom.isIntegrallyClosedIn
  given: (f : A ->ₐ[R] B) (hf : Function.Injective f)
  proof: by
  rintro ⟨inj, cl⟩
  refine ⟨Function.Injective.of_comp (f := f) ?_, fun hx => ?_, ?_⟩
  · convert! inj
    aesop
  · obtain ⟨y, fx_eq⟩ := cl.mp ((isIntegral_algHom_iff f hf).mpr hx)
    aesop
  · rintro ⟨y, rfl⟩
    apply (isIntegral_algHom_iff f hf).mp
    simp_all

中文:
定理 代数态射.is整数egrallyClosedIn
  条件: (f : A ->ₐ[R] B) (hf : 函数.单射 f)
  证明: by
  rintro ⟨inj, cl⟩
  refine ⟨Function.Injective.of_comp (f := f) ?_, fun hx => ?_, ?_⟩
  · convert! inj
    aesop
  · obtain ⟨y, fx_eq⟩ := cl.mp ((isIntegral_algHom_iff f hf).mpr hx)
    aesop
  · rintro ⟨y, rfl⟩
    apply (isIntegral_algHom_iff f hf).mp
    simp_all

Depends on / 依赖: Function, Function.Injective.of_comp, Injective, cl.mp, convert, fx_eq, isIntegral_algHom_iff, of_comp
-/
theorem AlgHom.isIntegrallyClosedIn (f : A ->ₐ[R] B) (hf : Function.Injective f) :
    IsIntegrallyClosedIn R B -> IsIntegrallyClosedIn R A := by
  rintro ⟨inj, cl⟩
  refine ⟨Function.Injective.of_comp (f := f) ?_, fun hx => ?_, ?_⟩
  · convert! inj
    aesop
  · obtain ⟨y, fx_eq⟩ := cl.mp ((isIntegral_algHom_iff f hf).mpr hx)
    aesop
  · rintro ⟨y, rfl⟩
    apply (isIntegral_algHom_iff f hf).mp
    simp_all

/--
theorem `AlgEquiv.isIntegrallyClosedIn` / 定理 `AlgEquiv.isIntegrallyClosedIn`

English:
theorem AlgEquiv.isIntegrallyClosedIn
  given: (e : A ≃ₐ[R] B)
  proof: ⟨AlgHom.isIntegrallyClosedIn e.symm e.symm.injective, AlgHom.isIntegrallyClosedIn e e.injective⟩

中文:
定理 代数等价.is整数egrallyClosedIn
  条件: (e : A ≃ₐ[R] B)
  证明: ⟨AlgHom.isIntegrallyClosedIn e.symm e.symm.injective, AlgHom.isIntegrallyClosedIn e e.injective⟩

Depends on / 依赖: AlgHom, AlgHom.isIntegrallyClosedIn, e.injective, e.symm, e.symm.injective, injective, isIntegrallyClosedIn
-/
theorem AlgEquiv.isIntegrallyClosedIn (e : A ≃ₐ[R] B) :
    IsIntegrallyClosedIn R A ↔ IsIntegrallyClosedIn R B :=
  ⟨AlgHom.isIntegrallyClosedIn e.symm e.symm.injective, AlgHom.isIntegrallyClosedIn e e.injective⟩

variable (K : Type*) [CommRing K] [Algebra R K] [IsFractionRing R K]

/--
theorem `isIntegrallyClosed_iff_isIntegrallyClosedIn` / 定理 `isIntegrallyClosed_iff_isIntegrallyClosedIn`

English:
theorem isIntegrallyClosed_iff_isIntegrallyClosedIn
  proof: (IsLocalization.algEquiv R⁰ _ _).isIntegrallyClosedIn

中文:
定理 is整数egrallyClosed_iff_is整数egrallyClosedIn
  证明: (IsLocalization.algEquiv R⁰ _ _).isIntegrallyClosedIn

Depends on / 依赖: IsLocalization, IsLocalization.algEquiv, algEquiv, isIntegrallyClosedIn
-/
theorem isIntegrallyClosed_iff_isIntegrallyClosedIn :
    IsIntegrallyClosed R ↔ IsIntegrallyClosedIn R K :=
  (IsLocalization.algEquiv R⁰ _ _).isIntegrallyClosedIn

/--
theorem `isIntegrallyClosed_iff_isIntegralClosure` / 定理 `isIntegrallyClosed_iff_isIntegralClosure`

English:
theorem isIntegrallyClosed_iff_isIntegralClosure
  statement: IsIntegrallyClosed R ↔ IsIntegralClosure R R K
  proof: isIntegrallyClosed_iff_isIntegrallyClosedIn K

中文:
定理 is整数egrallyClosed_iff_is整数egralClosure
  结论: 是整闭 R ↔ 是整闭包 R R K
  证明: isIntegrallyClosed_iff_isIntegrallyClosedIn K

Depends on / 依赖: isIntegrallyClosed_iff_isIntegrallyClosedIn
-/
theorem isIntegrallyClosed_iff_isIntegralClosure : IsIntegrallyClosed R ↔ IsIntegralClosure R R K :=
  isIntegrallyClosed_iff_isIntegrallyClosedIn K

/--
theorem `isIntegrallyClosedIn_iff` / 定理 `isIntegrallyClosedIn_iff`

English:
theorem isIntegrallyClosedIn_iff
  proof: by
  constructor
  · rintro ⟨_, cl⟩
    simp_all
  · rintro ⟨inj, cl⟩
    refine ⟨inj, by simp_all, ?_⟩
    rintro ⟨y, rfl⟩
    apply isIntegral_algebraMap

中文:
定理 is整数egrallyClosedIn_iff
  证明: by
  constructor
  · rintro ⟨_, cl⟩
    simp_all
  · rintro ⟨inj, cl⟩
    refine ⟨inj, by simp_all, ?_⟩
    rintro ⟨y, rfl⟩
    apply isIntegral_algebraMap

Depends on / 依赖: isIntegral_algebraMap
-/
theorem isIntegrallyClosedIn_iff :
    IsIntegrallyClosedIn R A ↔
      Function.Injective (algebraMap R A) ∧
        forall {x : A}, IsIntegral R x -> exists y, algebraMap R A y = x := by
  constructor
  · rintro ⟨_, cl⟩
    simp_all
  · rintro ⟨inj, cl⟩
    refine ⟨inj, by simp_all, ?_⟩
    rintro ⟨y, rfl⟩
    apply isIntegral_algebraMap

/--
theorem `isIntegrallyClosed_iff` / 定理 `isIntegrallyClosed_iff`

English:
theorem isIntegrallyClosed_iff
  proof: by
  simp [isIntegrallyClosed_iff_isIntegrallyClosedIn K, isIntegrallyClosedIn_iff,
        IsFractionRing.injective R K]

中文:
定理 is整数egrallyClosed_iff
  证明: by
  simp [isIntegrallyClosed_iff_isIntegrallyClosedIn K, isIntegrallyClosedIn_iff,
        IsFractionRing.injective R K]

Depends on / 依赖: IsFractionRing, IsFractionRing.injective, injective, isIntegrallyClosedIn_iff, isIntegrallyClosed_iff_isIntegrallyClosedIn
-/
theorem isIntegrallyClosed_iff :
    IsIntegrallyClosed R ↔ forall {x : K}, IsIntegral R x -> exists y, algebraMap R K y = x := by
  simp [isIntegrallyClosed_iff_isIntegrallyClosedIn K, isIntegrallyClosedIn_iff,
        IsFractionRing.injective R K]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIntegrallyClosedIn (integralClosure R A) A
  body: isIntegrallyClosedIn_iff.mpr
    ⟨FaithfulSMul.algebraMap_injective _ _, fun h => ⟨⟨_, isIntegral_trans _ h⟩, rfl⟩⟩

中文:
实例 :
  签名: Is整数egrallyClosedIn (integralClosure R A) A
  定义体: isIntegrallyClosedIn_iff.mpr
    ⟨FaithfulSMul.algebraMap_injective _ _, fun h => ⟨⟨_, isIntegral_trans _ h⟩, rfl⟩⟩

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap_injective, isIntegral_trans, isIntegrallyClosedIn_iff, isIntegrallyClosedIn_iff.mpr
-/
instance : IsIntegrallyClosedIn (integralClosure R A) A :=
  isIntegrallyClosedIn_iff.mpr
    ⟨FaithfulSMul.algebraMap_injective _ _, fun h => ⟨⟨_, isIntegral_trans _ h⟩, rfl⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIntegrallyClosedIn (integralClosure R A).toSubring A
  body: inferInstanceAs (IsIntegrallyClosedIn (integralClosure R A) A)

中文:
实例 :
  签名: Is整数egrallyClosedIn (integralClosure R A).toSubring A
  定义体: inferInstanceAs (IsIntegrallyClosedIn (integralClosure R A) A)

Depends on / 依赖: IsIntegrallyClosedIn, integralClosure
-/
instance : IsIntegrallyClosedIn (integralClosure R A).toSubring A :=
  inferInstanceAs (IsIntegrallyClosedIn (integralClosure R A) A)

namespace Subring

variable {C : Type*} [SetLike C A] [SubringClass C A] {S : C}

/--
theorem `isIntegrallyClosedIn_iff` / 定理 `isIntegrallyClosedIn_iff`

English:
theorem isIntegrallyClosedIn_iff
  proof: by
  rw [isIntegrallyClosedIn_iff]; rw [and_iff_right (FaithfulSMul.algebraMap_injective _ _)]
  exact congr(forall _ _, _ in $Subtype.range_val)

中文:
定理 is整数egrallyClosedIn_iff
  证明: by
  rw [isIntegrallyClosedIn_iff]; rw [and_iff_right (FaithfulSMul.algebraMap_injective _ _)]
  exact congr(forall _ _, _ in $Subtype.range_val)
-/
protected theorem isIntegrallyClosedIn_iff :
    IsIntegrallyClosedIn S A ↔ forall ⦃x : A⦄, IsIntegral S x -> x in S := by
  rw [isIntegrallyClosedIn_iff]; rw [and_iff_right (FaithfulSMul.algebraMap_injective _ _)]
  exact congr(forall _ _, _ in $Subtype.range_val)

/--
theorem `isIntegrallyClosed_iff` / 定理 `isIntegrallyClosed_iff`

English:
theorem isIntegrallyClosed_iff
  given: [IsFractionRing S A]
  proof: by
  rw [isIntegrallyClosed_iff A]; exact congr(forall _ _, _ in $Subtype.range_val)

中文:
定理 is整数egrallyClosed_iff
  条件: [IsFractionRing S A]
  证明: by
  rw [isIntegrallyClosed_iff A]; exact congr(forall _ _, _ in $Subtype.range_val)
-/
protected theorem isIntegrallyClosed_iff [IsFractionRing S A] :
    IsIntegrallyClosed S ↔ forall ⦃x : A⦄, IsIntegral S x -> x in S := by
  rw [isIntegrallyClosed_iff A]; exact congr(forall _ _, _ in $Subtype.range_val)

/--
theorem `integralClosure_le_iff` / 定理 `integralClosure_le_iff`

English:
theorem integralClosure_le_iff
  given: {T : Subring A} [IsIntegrallyClosedIn T A]
  proof: h (algebraMap_mem (integralClosure R A) r)
mpr h a ha := Subring.isIntegrallyClosedIn_iff.mp ‹_›
let : Algebra R T := RingHom.toAlgebra .codRestrict _ _ h
    have : IsScalarTower R T A := .of_algebraMap_eq fun _ => rfl
    ha.tower_top

中文:
定理 integralClosure_le_iff
  条件: {T : 子环 A} [Is整数egrallyClosedIn T A]
  证明: h (algebraMap_mem (integralClosure R A) r)
mpr h a ha := Subring.isIntegrallyClosedIn_iff.mp ‹_›
let : Algebra R T := RingHom.toAlgebra .codRestrict _ _ h
    have : IsScalarTower R T A := .of_algebraMap_eq fun _ => rfl
    ha.tower_top

Depends on / 依赖: algebraMap_mem, integralClosure
-/
theorem integralClosure_le_iff {T : Subring A} [IsIntegrallyClosedIn T A] :
    (integralClosure R A).toSubring <= T ↔ forall r, algebraMap R A r in T where
  mp h r := h (algebraMap_mem (integralClosure R A) r)
mpr h a ha := Subring.isIntegrallyClosedIn_iff.mp ‹_›
let : Algebra R T := RingHom.toAlgebra .codRestrict _ _ h
    have : IsScalarTower R T A := .of_algebraMap_eq fun _ => rfl
    ha.tower_top

/--
theorem `integralClosure_subring_le_iff` / 定理 `integralClosure_subring_le_iff`

English:
theorem integralClosure_subring_le_iff
  given: {T : Subring A} [IsIntegrallyClosedIn T A]
  proof: by
  rw [integralClosure_le_iff]; rw [Subtype.forall]; rw [SetLike.le_def]; rfl

中文:
定理 integralClosure_subring_le_iff
  条件: {T : 子环 A} [Is整数egrallyClosedIn T A]
  证明: by
  rw [integralClosure_le_iff]; rw [Subtype.forall]; rw [SetLike.le_def]; rfl

Depends on / 依赖: SetLike, SetLike.le_def, Subtype, Subtype.forall, integralClosure_le_iff, le_def
-/
theorem integralClosure_subring_le_iff {T : Subring A} [IsIntegrallyClosedIn T A] :
    (integralClosure S A).toSubring <= T ↔ .ofClass S <= T := by
  rw [integralClosure_le_iff]; rw [Subtype.forall]; rw [SetLike.le_def]; rfl

end Subring

end Iff

namespace IsIntegrallyClosedIn

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIntegrallyClosedIn R R
  body: ⟨Function.injective_id, by simp [Algebra.IsIntegral.isIntegral]⟩

中文:
实例 :
  签名: Is整数egrallyClosedIn R R
  定义体: ⟨Function.injective_id, by simp [Algebra.IsIntegral.isIntegral]⟩

Depends on / 依赖: Algebra, Algebra.IsIntegral.isIntegral, Function, Function.injective_id, IsIntegral, injective_id, isIntegral
-/
instance : IsIntegrallyClosedIn R R :=
  ⟨Function.injective_id, by simp [Algebra.IsIntegral.isIntegral]⟩

/--
theorem `algebraMap_eq_of_integral` / 定理 `algebraMap_eq_of_integral`

English:
theorem algebraMap_eq_of_integral
  given: [IsIntegrallyClosedIn R A] {x : A}
  proof: IsIntegralClosure.isIntegral_iff.mp

中文:
定理 algebraMap_eq_of_integral
  条件: [Is整数egrallyClosedIn R A] {x : A}
  证明: IsIntegralClosure.isIntegral_iff.mp

Depends on / 依赖: IsIntegralClosure, IsIntegralClosure.isIntegral_iff.mp, isIntegral_iff
-/
theorem algebraMap_eq_of_integral [IsIntegrallyClosedIn R A] {x : A} :
    IsIntegral R x -> exists y : R, algebraMap R A y = x :=
  IsIntegralClosure.isIntegral_iff.mp

/--
theorem `isIntegral_iff` / 定理 `isIntegral_iff`

English:
theorem isIntegral_iff
  given: [IsIntegrallyClosedIn R A] {x : A}
  proof: IsIntegralClosure.isIntegral_iff

中文:
定理 is整数egral_iff
  条件: [Is整数egrallyClosedIn R A] {x : A}
  证明: IsIntegralClosure.isIntegral_iff

Depends on / 依赖: IsIntegralClosure, IsIntegralClosure.isIntegral_iff, isIntegral_iff
-/
theorem isIntegral_iff [IsIntegrallyClosedIn R A] {x : A} :
    IsIntegral R x ↔ exists y : R, algebraMap R A y = x :=
  IsIntegralClosure.isIntegral_iff

/--
theorem `exists_algebraMap_eq_of_isIntegral_pow` / 定理 `exists_algebraMap_eq_of_isIntegral_pow`

English:
theorem exists_algebraMap_eq_of_isIntegral_pow
  statement: [IsIntegrallyClosedIn R A]
  proof: isIntegral_iff.mp hx.of_pow hn

中文:
定理 存在_algebraMap_eq_of_is整数egral_pow
  结论: [Is整数egrallyClosedIn R A]
  证明: isIntegral_iff.mp hx.of_pow hn

Depends on / 依赖: hx.of_pow, isIntegral_iff, isIntegral_iff.mp, of_pow
-/
theorem exists_algebraMap_eq_of_isIntegral_pow [IsIntegrallyClosedIn R A]
    {x : A} {n : Nat} (hn : 0 < n)
    (hx : IsIntegral R <| x ^ n) : exists y : R, algebraMap R A y = x :=
isIntegral_iff.mp hx.of_pow hn

/--
theorem `exists_algebraMap_eq_of_pow_mem_subalgebra` / 定理 `exists_algebraMap_eq_of_pow_mem_subalgebra`

English:
theorem exists_algebraMap_eq_of_pow_mem_subalgebra
  statement: {A : Type*} [CommRing A] [Algebra R A]
  proof: exists_algebraMap_eq_of_isIntegral_pow hn isIntegral_iff.mpr ⟨⟨x ^ n, hx⟩, rfl⟩

中文:
定理 存在_algebraMap_eq_of_pow_mem_subalgebra
  结论: {A : 类型} [交换环 A] [代数 R A]
  证明: exists_algebraMap_eq_of_isIntegral_pow hn isIntegral_iff.mpr ⟨⟨x ^ n, hx⟩, rfl⟩

Depends on / 依赖: exists_algebraMap_eq_of_isIntegral_pow, isIntegral_iff, isIntegral_iff.mpr
-/
theorem exists_algebraMap_eq_of_pow_mem_subalgebra {A : Type*} [CommRing A] [Algebra R A]
    {S : Subalgebra R A} [IsIntegrallyClosedIn S A] {x : A} {n : Nat} (hn : 0 < n)
    (hx : x ^ n in S) : exists y : S, algebraMap S A y = x :=
exists_algebraMap_eq_of_isIntegral_pow hn isIntegral_iff.mpr ⟨⟨x ^ n, hx⟩, rfl⟩

variable (A)

/--
theorem `integralClosure_eq_bot_iff` / 定理 `integralClosure_eq_bot_iff`

English:
theorem integralClosure_eq_bot_iff
  given: (hRA : Function.Injective (algebraMap R A))
  proof: by
  refine eq_bot_iff.trans ?_
  constructor
  · intro h
    refine ⟨ hRA, fun hx => Set.mem_range.mp (Algebra.mem_bot.mp (h hx)), ?_⟩
    rintro ⟨y, rfl⟩
    apply isIntegral_algebraMap
  · intro h x hx
    rw [Algebra.mem_bot]; rw [Set.mem_range]
    exact isIntegral_iff.mp hx

中文:
定理 integralClosure_eq_bot_iff
  条件: (hRA : 函数.单射 (algebraMap R A))
  证明: by
  refine eq_bot_iff.trans ?_
  constructor
  · intro h
    refine ⟨ hRA, fun hx => Set.mem_range.mp (Algebra.mem_bot.mp (h hx)), ?_⟩
    rintro ⟨y, rfl⟩
    apply isIntegral_algebraMap
  · intro h x hx
    rw [Algebra.mem_bot]; rw [Set.mem_range]
    exact isIntegral_iff.mp hx

Depends on / 依赖: Algebra, Algebra.mem_bot, Algebra.mem_bot.mp, Set.mem_range, Set.mem_range.mp, eq_bot_iff, eq_bot_iff.trans, isIntegral_algebraMap, isIntegral_iff, isIntegral_iff.mp, mem_bot, mem_range
-/
theorem integralClosure_eq_bot_iff (hRA : Function.Injective (algebraMap R A)) :
    integralClosure R A = ⊥ ↔ IsIntegrallyClosedIn R A := by
  refine eq_bot_iff.trans ?_
  constructor
  · intro h
    refine ⟨ hRA, fun hx => Set.mem_range.mp (Algebra.mem_bot.mp (h hx)), ?_⟩
    rintro ⟨y, rfl⟩
    apply isIntegral_algebraMap
  · intro h x hx
    rw [Algebra.mem_bot]; rw [Set.mem_range]
    exact isIntegral_iff.mp hx

variable (R)

@[simp]
/--
theorem `integralClosure_eq_bot` / 定理 `integralClosure_eq_bot`

English:
theorem integralClosure_eq_bot
  statement: [IsIntegrallyClosedIn R A] [IsDomain R] [Module.IsTorsionFree R A]
  proof: (integralClosure_eq_bot_iff A (FaithfulSMul.algebraMap_injective _ _)).mpr ‹_›

中文:
定理 integralClosure_eq_bot
  结论: [Is整数egrallyClosedIn R A] [是整环 R] [模.是无挠 R A]
  证明: (integralClosure_eq_bot_iff A (FaithfulSMul.algebraMap_injective _ _)).mpr ‹_›

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap_injective, integralClosure_eq_bot_iff
-/
theorem integralClosure_eq_bot [IsIntegrallyClosedIn R A] [IsDomain R] [Module.IsTorsionFree R A]
    [Nontrivial A] : integralClosure R A = ⊥ :=
  (integralClosure_eq_bot_iff A (FaithfulSMul.algebraMap_injective _ _)).mpr ‹_›

variable {A} {B : Type*} [CommRing B]

/--
lemma `of_isIntegralClosure` / 引理 `of_isIntegralClosure`

English:
lemma of_isIntegralClosure
  statement: [Algebra R B] [Algebra A B] [IsScalarTower R A B]
  proof: have : Algebra.IsIntegral R A := IsIntegralClosure.isIntegral_algebra R B
  IsIntegralClosure.tower_top (R := R)

中文:
引理 of_is整数egralClosure
  结论: [代数 R B] [代数 A B] [标量塔 R A B]
  证明: have : Algebra.IsIntegral R A := IsIntegralClosure.isIntegral_algebra R B
  IsIntegralClosure.tower_top (R := R)

Depends on / 依赖: Algebra, Algebra.IsIntegral, IsIntegral, IsIntegralClosure, IsIntegralClosure.isIntegral_algebra, IsIntegralClosure.tower_top, isIntegral_algebra, tower_top
-/
lemma of_isIntegralClosure [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [IsIntegralClosure A R B] :
    IsIntegrallyClosedIn A B :=
  have : Algebra.IsIntegral R A := IsIntegralClosure.isIntegral_algebra R B
  IsIntegralClosure.tower_top (R := R)

variable {R}

/--
lemma `_root_.IsIntegralClosure.of_isIntegrallyClosedIn` / 引理 `_root_.IsIntegralClosure.of_isIntegrallyClosedIn`

English:
lemma _root_.IsIntegralClosure.of_isIntegrallyClosedIn
  proof: by
  refine ⟨IsIntegralClosure.algebraMap_injective _ A _, fun {x} =>
    ⟨fun hx => IsIntegralClosure.isIntegral_iff.mp (IsIntegral.tower_top (A := A) hx), ?_⟩⟩
  rintro ⟨y, rfl⟩
  exact IsIntegral.map (IsScalarTower.toAlgHom A A B) (Algebra.IsIntegral.isIntegral y)

中文:
引理 _root_.是整闭包.of_is整数egrallyClosedIn
  证明: by
  refine ⟨IsIntegralClosure.algebraMap_injective _ A _, fun {x} =>
    ⟨fun hx => IsIntegralClosure.isIntegral_iff.mp (IsIntegral.tower_top (A := A) hx), ?_⟩⟩
  rintro ⟨y, rfl⟩
  exact IsIntegral.map (IsScalarTower.toAlgHom A A B) (Algebra.IsIntegral.isIntegral y)

Depends on / 依赖: Algebra, Algebra.IsIntegral.isIntegral, IsIntegral, IsIntegral.map, IsIntegral.tower_top, IsIntegralClosure, IsIntegralClosure.algebraMap_injective, IsIntegralClosure.isIntegral_iff.mp, IsScalarTower, IsScalarTower.toAlgHom, algebraMap_injective, isIntegral, isIntegral_iff, toAlgHom, tower_top
-/
lemma _root_.IsIntegralClosure.of_isIntegrallyClosedIn
    [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [IsIntegrallyClosedIn A B] [Algebra.IsIntegral R A] :
    IsIntegralClosure A R B := by
  refine ⟨IsIntegralClosure.algebraMap_injective _ A _, fun {x} =>
    ⟨fun hx => IsIntegralClosure.isIntegral_iff.mp (IsIntegral.tower_top (A := A) hx), ?_⟩⟩
  rintro ⟨y, rfl⟩
  exact IsIntegral.map (IsScalarTower.toAlgHom A A B) (Algebra.IsIntegral.isIntegral y)

end IsIntegrallyClosedIn

namespace IsIntegrallyClosed

variable {R S : Type*} [CommRing R] [CommRing S]
variable {K : Type*} [CommRing K] [Algebra R K] [ifr : IsFractionRing R K]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [iic
  signature: : IsIntegrallyClosed R] : IsIntegralClosure R R K
  body: (isIntegrallyClosed_iff_isIntegralClosure K).mp iic

中文:
实例 [iic
  签名: : 是整闭 R] : 是整闭包 R R K
  定义体: (isIntegrallyClosed_iff_isIntegralClosure K).mp iic

Depends on / 依赖: isIntegrallyClosed_iff_isIntegralClosure
-/
instance [iic : IsIntegrallyClosed R] : IsIntegralClosure R R K :=
  (isIntegrallyClosed_iff_isIntegralClosure K).mp iic

/--
theorem `algebraMap_eq_of_integral` / 定理 `algebraMap_eq_of_integral`

English:
theorem algebraMap_eq_of_integral
  given: [IsIntegrallyClosed R] {x : K}
  proof: IsIntegralClosure.isIntegral_iff.mp

中文:
定理 algebraMap_eq_of_integral
  条件: [是整闭 R] {x : K}
  证明: IsIntegralClosure.isIntegral_iff.mp

Depends on / 依赖: IsIntegralClosure, IsIntegralClosure.isIntegral_iff.mp, isIntegral_iff
-/
theorem algebraMap_eq_of_integral [IsIntegrallyClosed R] {x : K} :
    IsIntegral R x -> exists y : R, algebraMap R K y = x :=
  IsIntegralClosure.isIntegral_iff.mp

/--
theorem `isIntegral_iff` / 定理 `isIntegral_iff`

English:
theorem isIntegral_iff
  given: [IsIntegrallyClosed R] {x : K}
  proof: IsIntegrallyClosedIn.isIntegral_iff

中文:
定理 is整数egral_iff
  条件: [是整闭 R] {x : K}
  证明: IsIntegrallyClosedIn.isIntegral_iff

Depends on / 依赖: IsIntegrallyClosedIn, IsIntegrallyClosedIn.isIntegral_iff, isIntegral_iff
-/
theorem isIntegral_iff [IsIntegrallyClosed R] {x : K} :
    IsIntegral R x ↔ exists y : R, algebraMap R K y = x :=
  IsIntegrallyClosedIn.isIntegral_iff

/--
theorem `exists_algebraMap_eq_of_isIntegral_pow` / 定理 `exists_algebraMap_eq_of_isIntegral_pow`

English:
theorem exists_algebraMap_eq_of_isIntegral_pow
  statement: [IsIntegrallyClosed R] {x : K} {n : Nat} (hn : 0 < n)
  proof: IsIntegrallyClosedIn.exists_algebraMap_eq_of_isIntegral_pow hn hx

中文:
定理 存在_algebraMap_eq_of_is整数egral_pow
  结论: [是整闭 R] {x : K} {n : 自然数} (hn : 0 < n)
  证明: IsIntegrallyClosedIn.exists_algebraMap_eq_of_isIntegral_pow hn hx

Depends on / 依赖: IsIntegrallyClosedIn, IsIntegrallyClosedIn.exists_algebraMap_eq_of_isIntegral_pow, exists_algebraMap_eq_of_isIntegral_pow
-/
theorem exists_algebraMap_eq_of_isIntegral_pow [IsIntegrallyClosed R] {x : K} {n : Nat} (hn : 0 < n)
    (hx : IsIntegral R <| x ^ n) : exists y : R, algebraMap R K y = x :=
  IsIntegrallyClosedIn.exists_algebraMap_eq_of_isIntegral_pow hn hx

/--
theorem `exists_algebraMap_eq_of_pow_mem_subalgebra` / 定理 `exists_algebraMap_eq_of_pow_mem_subalgebra`

English:
theorem exists_algebraMap_eq_of_pow_mem_subalgebra
  statement: {K : Type*} [CommRing K] [Algebra R K]
  proof: IsIntegrallyClosedIn.exists_algebraMap_eq_of_pow_mem_subalgebra hn hx

中文:
定理 存在_algebraMap_eq_of_pow_mem_subalgebra
  结论: {K : 类型} [交换环 K] [代数 R K]
  证明: IsIntegrallyClosedIn.exists_algebraMap_eq_of_pow_mem_subalgebra hn hx

Depends on / 依赖: IsIntegrallyClosedIn, IsIntegrallyClosedIn.exists_algebraMap_eq_of_pow_mem_subalgebra, exists_algebraMap_eq_of_pow_mem_subalgebra
-/
theorem exists_algebraMap_eq_of_pow_mem_subalgebra {K : Type*} [CommRing K] [Algebra R K]
    {S : Subalgebra R K} [IsIntegrallyClosed S] [IsFractionRing S K] {x : K} {n : Nat} (hn : 0 < n)
    (hx : x ^ n in S) : exists y : S, algebraMap S K y = x :=
  IsIntegrallyClosedIn.exists_algebraMap_eq_of_pow_mem_subalgebra hn hx

/--
theorem `of_equiv` / 定理 `of_equiv`

English:
theorem of_equiv
  given: (f : R ≃+* S) [h : IsIntegrallyClosed R]
  statement: IsIntegrallyClosed S
  proof: by
  let _ : Algebra S R := f.symm.toRingHom.toAlgebra
  let f : S ≃ₐ[S] R := AlgEquiv.ofRingEquiv fun _ => rfl
  let g : FractionRing S ≃ₐ[S] FractionRing R := IsFractionRing.algEquivOfAlgEquiv f
  refine (isIntegrallyClosed_iff (FractionRing S)).mpr (fun hx => ?_)
  rcases (isIntegrallyClosed_iff 

中文:
定理 of_equiv
  条件: (f : R ≃+* S) [h : 是整闭 R]
  结论: 是整闭 S
  证明: by
  let _ : Algebra S R := f.symm.toRingHom.toAlgebra
  let f : S ≃ₐ[S] R := AlgEquiv.ofRingEquiv fun _ => rfl
  let g : FractionRing S ≃ₐ[S] FractionRing R := IsFractionRing.algEquivOfAlgEquiv f
  refine (isIntegrallyClosed_iff (FractionRing S)).mpr (fun hx => ?_)
  rcases (isIntegrallyClosed_iff 

Depends on / 依赖: AlgEquiv, AlgEquiv.ofRingEquiv, AlgEquiv.symm_apply_eq, Algebra, FractionRing, IsFractionRing, IsFractionRing.algEquivOfAlgEquiv, IsFractionRing.algEquivOfAlgEquiv_algebraMap, algEquivOfAlgEquiv, algEquivOfAlgEquiv_algebraMap, f.symm, f.symm.toRingHom.toAlgebra, isIntegral_algEquiv, isIntegrallyClosed_iff, ofRingEquiv, symm.trans, symm_apply_eq, toAlgebra, toRingHom, tower_top
-/
theorem of_equiv (f : R ≃+* S) [h : IsIntegrallyClosed R] : IsIntegrallyClosed S := by
  let _ : Algebra S R := f.symm.toRingHom.toAlgebra
  let f : S ≃ₐ[S] R := AlgEquiv.ofRingEquiv fun _ => rfl
  let g : FractionRing S ≃ₐ[S] FractionRing R := IsFractionRing.algEquivOfAlgEquiv f
  refine (isIntegrallyClosed_iff (FractionRing S)).mpr (fun hx => ?_)
  rcases (isIntegrallyClosed_iff _).mp h ((isIntegral_algEquiv g).mpr hx).tower_top with ⟨z, hz⟩
exact ⟨f.symm z, (IsFractionRing.algEquivOfAlgEquiv_algebraMap f.symm z).symm.trans
    (AlgEquiv.symm_apply_eq g).mpr hz⟩

variable (R S K)

/--
Instance `_root_.IsIntegralClosure.of_isIntegrallyClosed` / 实例 `_root_.IsIntegralClosure.of_isIntegrallyClosed`

English:
instance _root_.IsIntegralClosure.of_isIntegrallyClosed
  signature: [IsIntegrallyClosed R]
  body: IsIntegralClosure.of_isIntegrallyClosedIn

中文:
实例 _root_.是整闭包.of_is整数egrallyClosed
  签名: [是整闭 R]
  定义体: IsIntegralClosure.of_isIntegrallyClosedIn

Depends on / 依赖: IsIntegralClosure, IsIntegralClosure.of_isIntegrallyClosedIn, of_isIntegrallyClosedIn
-/
instance _root_.IsIntegralClosure.of_isIntegrallyClosed [IsIntegrallyClosed R]
    [Algebra S R] [Algebra S K] [IsScalarTower S R K] [Algebra.IsIntegral S R] :
    IsIntegralClosure R S K :=
  IsIntegralClosure.of_isIntegrallyClosedIn

/--
lemma `of_isIntegrallyClosedIn` / 引理 `of_isIntegrallyClosedIn`

English:
lemma of_isIntegrallyClosedIn
  proof: by
  have : IsDomain R := (FaithfulSMul.algebraMap_injective R K).isDomain _
  let f : FractionRing R ->ₐ[R] K := IsFractionRing.liftAlgHom (g := Algebra.ofId _ _)
    (FaithfulSMul.algebraMap_injective R K)
  rw [isIntegrallyClosed_iff (K := FractionRing R)]
  intro x hx
  convert! (IsIntegralClosu

中文:
引理 of_is整数egrallyClosedIn
  证明: by
  have : IsDomain R := (FaithfulSMul.algebraMap_injective R K).isDomain _
  let f : FractionRing R ->ₐ[R] K := IsFractionRing.liftAlgHom (g := Algebra.ofId _ _)
    (FaithfulSMul.algebraMap_injective R K)
  rw [isIntegrallyClosed_iff (K := FractionRing R)]
  intro x hx
  convert! (IsIntegralClosu

Depends on / 依赖: Algebra, Algebra.ofId, FaithfulSMul, FaithfulSMul.algebraMap_injective, FractionRing, IsDomain, IsFractionRing, IsFractionRing.liftAlgHom, IsIntegralClosure, IsIntegralClosure.isIntegral_iff, algebraMap_injective, convert, eq_iff, f.toRingHom.injective.eq_iff, hx.map, injective, isDomain, isIntegral_iff, isIntegrallyClosed_iff, liftAlgHom
-/
lemma of_isIntegrallyClosedIn
    (R K : Type*) [CommRing R] [Field K] [Algebra R K] [FaithfulSMul R K]
    [IsIntegrallyClosedIn R K] : IsIntegrallyClosed R := by
  have : IsDomain R := (FaithfulSMul.algebraMap_injective R K).isDomain _
  let f : FractionRing R ->ₐ[R] K := IsFractionRing.liftAlgHom (g := Algebra.ofId _ _)
    (FaithfulSMul.algebraMap_injective R K)
  rw [isIntegrallyClosed_iff (K := FractionRing R)]
  intro x hx
  convert! (IsIntegralClosure.isIntegral_iff (A := R)).mp (hx.map f)
  simp [← f.toRingHom.injective.eq_iff]

/--
lemma `_root_.IsIntegralClosure.of_isIntegralClosure_of_isIntegrallyClosedIn` / 引理 `_root_.IsIntegralClosure.of_isIntegralClosure_of_isIntegrallyClosedIn`

English:
lemma _root_.IsIntegralClosure.of_isIntegralClosure_of_isIntegrallyClosedIn
  proof: by
  refine ⟨?_, ?_⟩
  · rw [IsScalarTower.algebraMap_eq S T U]
    exact (IsIntegralClosure.algebraMap_injective T T U).comp
      (IsIntegralClosure.algebraMap_injective S R T)
  · intro x
    refine ⟨fun h => ?_, ?_⟩
    · obtain ⟨x, rfl⟩ := (IsIntegralClosure.isIntegral_iff (R := T) (A := T)).mp

中文:
引理 _root_.是整闭包.of_is整数egralClosure_of_is整数egrallyClosedIn
  证明: by
  refine ⟨?_, ?_⟩
  · rw [IsScalarTower.algebraMap_eq S T U]
    exact (IsIntegralClosure.algebraMap_injective T T U).comp
      (IsIntegralClosure.algebraMap_injective S R T)
  · intro x
    refine ⟨fun h => ?_, ?_⟩
    · obtain ⟨x, rfl⟩ := (IsIntegralClosure.isIntegral_iff (R := T) (A := T)).mp

Depends on / 依赖: IsIntegralClosure, IsIntegralClosure.algebraMap_injective, IsIntegralClosure.isIntegral_iff, IsScalarTower, IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_eq, algebraMap_apply, algebraMap_eq, algebraMap_injective, h.tower_top, isIntegral_algebraMap_iff, isIntegral_iff, tower_top
-/
lemma _root_.IsIntegralClosure.of_isIntegralClosure_of_isIntegrallyClosedIn
    (R S T U : Type*) [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    [Algebra R T] [Algebra S T] [Algebra R U] [Algebra S U] [Algebra T U]
    [IsScalarTower S T U] [IsScalarTower R T U]
    [IsIntegralClosure S R T] [IsIntegrallyClosedIn T U] : IsIntegralClosure S R U := by
  refine ⟨?_, ?_⟩
  · rw [IsScalarTower.algebraMap_eq S T U]
    exact (IsIntegralClosure.algebraMap_injective T T U).comp
      (IsIntegralClosure.algebraMap_injective S R T)
  · intro x
    refine ⟨fun h => ?_, ?_⟩
    · obtain ⟨x, rfl⟩ := (IsIntegralClosure.isIntegral_iff (R := T) (A := T)).mp h.tower_top
      rw [isIntegral_algebraMap_iff (IsIntegralClosure.algebraMap_injective T T U)] at h
      obtain ⟨x, rfl⟩ := (IsIntegralClosure.isIntegral_iff (R := R) (A := S)).mp h
      exact ⟨x, IsScalarTower.algebraMap_apply ..⟩
    · rintro ⟨x, rfl⟩
      rw [IsScalarTower.algebraMap_apply S T U]
      exact ((IsIntegralClosure.isIntegral_iff (A := S) (R := R) (B := T)).mpr ⟨x, rfl⟩).map
        (IsScalarTower.toAlgHom R T U)

/--
lemma `of_isIntegrallyClosed_of_isIntegrallyClosedIn` / 引理 `of_isIntegrallyClosed_of_isIntegrallyClosedIn`

English:
lemma of_isIntegrallyClosed_of_isIntegrallyClosedIn
  proof: have : IsIntegrallyClosedIn R (FractionRing S) :=
    .of_isIntegralClosure_of_isIntegrallyClosedIn _ _ S _
  .of_isIntegrallyClosedIn R (FractionRing S)

中文:
引理 of_is整数egrallyClosed_of_is整数egrallyClosedIn
  证明: have : IsIntegrallyClosedIn R (FractionRing S) :=
    .of_isIntegralClosure_of_isIntegrallyClosedIn _ _ S _
  .of_isIntegrallyClosedIn R (FractionRing S)

Depends on / 依赖: FractionRing, IsIntegrallyClosedIn, of_isIntegralClosure_of_isIntegrallyClosedIn, of_isIntegrallyClosedIn
-/
lemma of_isIntegrallyClosed_of_isIntegrallyClosedIn
    [Algebra R S] [IsDomain S] [FaithfulSMul R S]
    [IsIntegrallyClosed S] [IsIntegrallyClosedIn R S] : IsIntegrallyClosed R :=
  have : IsIntegrallyClosedIn R (FractionRing S) :=
    .of_isIntegralClosure_of_isIntegrallyClosedIn _ _ S _
  .of_isIntegrallyClosedIn R (FractionRing S)

variable {R}

/--
theorem `integralClosure_eq_bot_iff` / 定理 `integralClosure_eq_bot_iff`

English:
theorem integralClosure_eq_bot_iff
  statement: integralClosure R K = ⊥ ↔ IsIntegrallyClosed R
  proof: (IsIntegrallyClosedIn.integralClosure_eq_bot_iff _ (IsFractionRing.injective _ _)).trans
    (isIntegrallyClosed_iff_isIntegrallyClosedIn _).symm

@[simp]

中文:
定理 integralClosure_eq_bot_iff
  结论: integralClosure R K = ⊥ ↔ 是整闭 R
  证明: (IsIntegrallyClosedIn.integralClosure_eq_bot_iff _ (IsFractionRing.injective _ _)).trans
    (isIntegrallyClosed_iff_isIntegrallyClosedIn _).symm

@[simp]

Depends on / 依赖: IsFractionRing, IsFractionRing.injective, IsIntegrallyClosedIn, IsIntegrallyClosedIn.integralClosure_eq_bot_iff, injective, integralClosure_eq_bot_iff, isIntegrallyClosed_iff_isIntegrallyClosedIn
-/
theorem integralClosure_eq_bot_iff : integralClosure R K = ⊥ ↔ IsIntegrallyClosed R :=
  (IsIntegrallyClosedIn.integralClosure_eq_bot_iff _ (IsFractionRing.injective _ _)).trans
    (isIntegrallyClosed_iff_isIntegrallyClosedIn _).symm

@[simp]
/--
theorem `pow_dvd_pow_iff` / 定理 `pow_dvd_pow_iff`

English:
theorem pow_dvd_pow_iff
  statement: [IsDomain R] [IsIntegrallyClosed R]
  proof: by
  refine ⟨fun ⟨x, hx⟩ => ?_, fun h => pow_dvd_pow_of_dvd h n⟩
  by_cases ha : a = 0
  · simpa [ha, hn] using hx
  let K := FractionRing R
  replace ha : algebraMap R K a != 0 := fun h =>
ha (injective_iff_map_eq_zero _).1 (IsFractionRing.injective R K) _ h
  let y := (algebraMap R K b) / (algebra

中文:
定理 pow_dvd_pow_iff
  结论: [是整环 R] [是整闭 R]
  证明: by
  refine ⟨fun ⟨x, hx⟩ => ?_, fun h => pow_dvd_pow_of_dvd h n⟩
  by_cases ha : a = 0
  · simpa [ha, hn] using hx
  let K := FractionRing R
  replace ha : algebraMap R K a != 0 := fun h =>
ha (injective_iff_map_eq_zero _).1 (IsFractionRing.injective R K) _ h
  let y := (algebraMap R K b) / (algebra

Depends on / 依赖: FractionRing, IsFractionRing, IsFractionRing.injective, IsIntegral, algebraMap, congr_arg, div_pow, injective, injective_iff_map_eq_zero, map_pow, monic_X_pow_sub_C, pow_dvd_pow_of_dvd, replace
-/
theorem pow_dvd_pow_iff [IsDomain R] [IsIntegrallyClosed R]
    {n : Nat} (hn : n != 0) {a b : R} : a ^ n ∣ b ^ n ↔ a ∣ b := by
  refine ⟨fun ⟨x, hx⟩ => ?_, fun h => pow_dvd_pow_of_dvd h n⟩
  by_cases ha : a = 0
  · simpa [ha, hn] using hx
  let K := FractionRing R
  replace ha : algebraMap R K a != 0 := fun h =>
ha (injective_iff_map_eq_zero _).1 (IsFractionRing.injective R K) _ h
  let y := (algebraMap R K b) / (algebraMap R K a)
  have hy : IsIntegral R y := by
    refine ⟨X ^ n - C x, monic_X_pow_sub_C _ hn, ?_⟩
    simp only [y, eval₂_sub, eval₂_X_pow, div_pow, eval₂_C]
    replace hx := congr_arg (algebraMap R K) hx
    rw [map_pow] at hx
    simp [hx, ha]
  obtain ⟨k, hk⟩ := algebraMap_eq_of_integral hy
  refine ⟨k, IsFractionRing.injective R K ?_⟩
  rw [map_mul]; rw [hk]; rw [mul_div_cancel₀ _ ha]

@[simp]
/--
theorem `_root_.Associated.pow_iff` / 定理 `_root_.Associated.pow_iff`

English:
theorem _root_.Associated.pow_iff
  statement: [IsDomain R] [IsIntegrallyClosed R] {n : Nat} (hn : n != 0)
  proof: by
  simp_rw [← dvd_dvd_iff_associated, pow_dvd_pow_iff hn]

中文:
定理 _root_.Associated.pow_iff
  结论: [是整环 R] [是整闭 R] {n : 自然数} (hn : n != 0)
  证明: by
  simp_rw [← dvd_dvd_iff_associated, pow_dvd_pow_iff hn]

Depends on / 依赖: dvd_dvd_iff_associated, pow_dvd_pow_iff, simp_rw
-/
theorem _root_.Associated.pow_iff [IsDomain R] [IsIntegrallyClosed R] {n : Nat} (hn : n != 0)
    {a b : R} :
    Associated (a ^ n) (b ^ n) ↔ Associated a b := by
  simp_rw [← dvd_dvd_iff_associated, pow_dvd_pow_iff hn]

variable (R)

/-- This is almost a duplicate of `IsIntegrallyClosedIn.integralClosure_eq_bot`,
except the `Module.IsTorsionFree` hypothesis isn't inferred automatically from `IsFractionRing`. -/
@[simp]
/--
theorem `integralClosure_eq_bot` / 定理 `integralClosure_eq_bot`

English:
theorem integralClosure_eq_bot
  given: [IsIntegrallyClosed R]
  statement: integralClosure R K = ⊥
  proof: (integralClosure_eq_bot_iff K).mpr ‹_›

中文:
定理 integralClosure_eq_bot
  条件: [是整闭 R]
  结论: integralClosure R K = ⊥
  证明: (integralClosure_eq_bot_iff K).mpr ‹_›

Depends on / 依赖: integralClosure_eq_bot_iff
-/
theorem integralClosure_eq_bot [IsIntegrallyClosed R] : integralClosure R K = ⊥ :=
  (integralClosure_eq_bot_iff K).mpr ‹_›

end IsIntegrallyClosed

namespace integralClosure

open IsIntegrallyClosed

variable {R : Type*} [CommRing R]
variable (K : Type*) [Field K] [Algebra R K]
variable [IsFractionRing R K]
variable {L : Type*} [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]

-- Can't be an instance because you need to supply `K`.
/--
theorem `isIntegrallyClosedOfFiniteExtension` / 定理 `isIntegrallyClosedOfFiniteExtension`

English:
theorem isIntegrallyClosedOfFiniteExtension
  given: [IsDomain R] [FiniteDimensional K L]
  proof: letI : IsFractionRing (integralClosure R L) L := isFractionRing_of_finite_extension K L
  (integralClosure_eq_bot_iff L).mp integralClosure_idem

中文:
定理 is整数egrallyClosedOfFiniteExtension
  条件: [是整环 R] [有限维 K L]
  证明: letI : IsFractionRing (integralClosure R L) L := isFractionRing_of_finite_extension K L
  (integralClosure_eq_bot_iff L).mp integralClosure_idem

Depends on / 依赖: IsFractionRing, integralClosure, integralClosure_eq_bot_iff, integralClosure_idem, isFractionRing_of_finite_extension
-/
theorem isIntegrallyClosedOfFiniteExtension [IsDomain R] [FiniteDimensional K L] :
    IsIntegrallyClosed (integralClosure R L) :=
  letI : IsFractionRing (integralClosure R L) L := isFractionRing_of_finite_extension K L
  (integralClosure_eq_bot_iff L).mp integralClosure_idem

end integralClosure

section localization

variable {R : Type*} (S : Type*) [CommRing R] [CommRing S] [Algebra R S]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `isIntegrallyClosed_of_isLocalization` / 引理 `isIntegrallyClosed_of_isLocalization`

English:
lemma isIntegrallyClosed_of_isLocalization
  statement: [IsIntegrallyClosed R] [IsDomain R] (M : Submonoid R)
  proof: by
  let K := FractionRing R
  let g : S ->+* K := IsLocalization.map _ (T := R⁰) (RingHom.id R) hM
  let := g.toAlgebra
  have : IsScalarTower R S K := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, RingHomCompTriple.comp_eq])
  have := IsFraction

中文:
引理 is整数egrallyClosed_of_isLocalization
  结论: [是整闭 R] [是整环 R] (M : 子幺半群 R)
  证明: by
  let K := FractionRing R
  let g : S ->+* K := IsLocalization.map _ (T := R⁰) (RingHom.id R) hM
  let := g.toAlgebra
  have : IsScalarTower R S K := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, RingHomCompTriple.comp_eq])
  have := IsFraction

Depends on / 依赖: FractionRing, IsFractionRing, IsFractionRing.injective, IsFractionRing.isFractionRing_of_isDomain_of_isLocalization, IsLocalization, IsLocalization.map, IsLocalization.map_comp, IsScalarTower, IsScalarTower.of_algebraMap_eq, RingHom, RingHom.algebraMap_toAlgebra, RingHom.id, RingHomCompTriple, RingHomCompTriple.comp_eq, algebraMap_toAlgebra, choose_spec, comp_eq, e.choose_spec, g.toAlgebra, injective
-/
lemma isIntegrallyClosed_of_isLocalization [IsIntegrallyClosed R] [IsDomain R] (M : Submonoid R)
    (hM : M <= R⁰) [IsLocalization M S] : IsIntegrallyClosed S := by
  let K := FractionRing R
  let g : S ->+* K := IsLocalization.map _ (T := R⁰) (RingHom.id R) hM
  let := g.toAlgebra
  have : IsScalarTower R S K := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, RingHomCompTriple.comp_eq])
  have := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M S K
  refine (isIntegrallyClosed_iff_isIntegralClosure (K := K)).mpr
    ⟨IsFractionRing.injective _ _, fun {x} => ⟨?_, fun e => e.choose_spec ▸ isIntegral_algebraMap⟩⟩
  intro hx
  obtain ⟨⟨y, y_mem⟩, hy⟩ := hx.exists_multiple_integral_of_isLocalization M _
  obtain ⟨z, hz⟩ := (isIntegrallyClosed_iff _).mp ‹_› hy
  refine ⟨IsLocalization.mk' S z ⟨y, y_mem⟩, (IsLocalization.lift_mk'_spec _ _ _ _).mpr ?_⟩
  rw [RingHom.comp_id]; rw [hz]; rw [← Algebra.smul_def]; rw [Submonoid.mk_smul]

end localization

/-- Any field is integral closed. -/
/--
Instance `Field.instIsIntegrallyClosed` / 实例 `Field.instIsIntegrallyClosed`

English:
instance Field.instIsIntegrallyClosed
  signature: (K : Type*) [Field K]
  body: (isIntegrallyClosed_iff K).mpr fun {x} _ => ⟨x, rfl⟩

中文:
实例 域.instIs整数egrallyClosed
  签名: (K : 类型) [域 K]
  定义体: (isIntegrallyClosed_iff K).mpr fun {x} _ => ⟨x, rfl⟩

Depends on / 依赖: isIntegrallyClosed_iff
-/
instance Field.instIsIntegrallyClosed (K : Type*) [Field K] : IsIntegrallyClosed K :=
  (isIntegrallyClosed_iff K).mpr fun {x} _ => ⟨x, rfl⟩
