/-
Copyright (c) 2025 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Ideal.Prime

/-!
# Localizations of modules at the complement of a prime ideal
-/

public section

/--
Definition of `IsLocalizedModule.AtPrime` / `IsLocalizedModule.AtPrime` 的定义

English:
abbreviation IsLocalizedModule.AtPrime
  signature: {R M M' : Type*} [CommSemiring R] (P : Ideal R)
  body: IsLocalizedModule P.primeCompl f

中文:
缩写 IsLocalizedModule.AtPrime
  签名: {R M M' : 类型} [CommSemiring R] (P : Ideal R)
  定义体: IsLocalizedModule P.primeCompl f
-/
protected abbrev IsLocalizedModule.AtPrime {R M M' : Type*} [CommSemiring R] (P : Ideal R)
    [P.IsPrime] [AddCommMonoid M] [AddCommMonoid M'] [Module R M] [Module R M'] (f : M ->ₗ[R] M') :=
  IsLocalizedModule P.primeCompl f

/--
Definition of `LocalizedModule.AtPrime` / `LocalizedModule.AtPrime` 的定义

English:
abbreviation LocalizedModule.AtPrime
  signature: {R : Type*} [CommSemiring R] (P : Ideal R) [P.IsPrime]
  body: LocalizedModule P.primeCompl M

中文:
缩写 LocalizedModule.AtPrime
  签名: {R : 类型} [CommSemiring R] (P : Ideal R) [P.IsPrime]
  定义体: LocalizedModule P.primeCompl M
-/
protected abbrev LocalizedModule.AtPrime {R : Type*} [CommSemiring R] (P : Ideal R) [P.IsPrime]
    (M : Type*) [AddCommMonoid M] [Module R M] :=
  LocalizedModule P.primeCompl M
