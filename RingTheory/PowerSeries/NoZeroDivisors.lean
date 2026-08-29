/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau
-/
module

public import Mathlib.RingTheory.PowerSeries.Order
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Power series over rings with no zero divisors

This file proves, using the properties of orders of power series,
that `R⟦X⟧` is an integral domain when `R` is.

We then state various results about `R⟦X⟧` with `R` an integral domain.

## Instance

If `R` has `NoZeroDivisors`, then so does `R⟦X⟧`.

-/

public section


variable {R : Type*}

namespace PowerSeries

section NoZeroDivisors

variable [Semiring R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NoZeroDivisors
  signature: R] : NoZeroDivisors R⟦X⟧ where
  body: by
    simp_rw [← order_eq_top, order_mul] at h ⊢
    exact WithTop.add_eq_top.mp h

中文:
实例 [无零因子
  签名: R] : 无零因子 R⟦X⟧ where
  定义体: by
    simp_rw [← order_eq_top, order_mul] at h ⊢
    exact WithTop.add_eq_top.mp h

Depends on / 依赖: WithTop, WithTop.add_eq_top.mp, add_eq_top, order_eq_top, order_mul, simp_rw
-/
instance [NoZeroDivisors R] : NoZeroDivisors R⟦X⟧ where
  eq_zero_or_eq_zero_of_mul_eq_zero {φ ψ} h := by
    simp_rw [← order_eq_top, order_mul] at h ⊢
    exact WithTop.add_eq_top.mp h

end NoZeroDivisors

section IsDomain

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Ring
  signature: R] [IsDomain R] : IsDomain R⟦X⟧
  body: NoZeroDivisors.to_isDomain _

中文:
实例 [环
  签名: R] [是整环 R] : 是整环 R⟦X⟧
  定义体: NoZeroDivisors.to_isDomain _

Depends on / 依赖: NoZeroDivisors, NoZeroDivisors.to_isDomain, to_isDomain
-/
instance [Ring R] [IsDomain R] : IsDomain R⟦X⟧ :=
  NoZeroDivisors.to_isDomain _

variable [CommRing R] [IsDomain R]

/--
theorem `span_X_isPrime` / 定理 `span_X_isPrime`

English:
theorem span_X_isPrime
  statement: (Ideal.span ({X} : Set R⟦X⟧)).IsPrime
  proof: by
  suffices Ideal.span ({X} : Set R⟦X⟧) = RingHom.ker constantCoeff by
    rw [this]
    exact RingHom.ker_isPrime _
  apply Ideal.ext
  intro φ
  rw [RingHom.mem_ker]; rw [Ideal.mem_span_singleton]; rw [X_dvd_iff]

中文:
定理 span_X_isPrime
  结论: (理想.span ({X} : 集合 R⟦X⟧)).是素
  证明: by
  suffices Ideal.span ({X} : Set R⟦X⟧) = RingHom.ker constantCoeff by
    rw [this]
    exact RingHom.ker_isPrime _
  apply Ideal.ext
  intro φ
  rw [RingHom.mem_ker]; rw [Ideal.mem_span_singleton]; rw [X_dvd_iff]

Depends on / 依赖: Ideal.ext, Ideal.mem_span_singleton, Ideal.span, RingHom, RingHom.ker, RingHom.ker_isPrime, RingHom.mem_ker, X_dvd_iff, constantCoeff, ker_isPrime, mem_ker, mem_span_singleton
-/
theorem span_X_isPrime : (Ideal.span ({X} : Set R⟦X⟧)).IsPrime := by
  suffices Ideal.span ({X} : Set R⟦X⟧) = RingHom.ker constantCoeff by
    rw [this]
    exact RingHom.ker_isPrime _
  apply Ideal.ext
  intro φ
  rw [RingHom.mem_ker]; rw [Ideal.mem_span_singleton]; rw [X_dvd_iff]

/--
theorem `X_prime` / 定理 `X_prime`

English:
theorem X_prime
  statement: Prime (X : R⟦X⟧)
  proof: by
  rw [← Ideal.span_singleton_prime]
  · exact span_X_isPrime
  · intro h
    simpa [map_zero (coeff 1)] using congr_arg (coeff 1) h

中文:
定理 X_prime
  结论: 素 (X : R⟦X⟧)
  证明: by
  rw [← Ideal.span_singleton_prime]
  · exact span_X_isPrime
  · intro h
    simpa [map_zero (coeff 1)] using congr_arg (coeff 1) h

Depends on / 依赖: Ideal.span_singleton_prime, congr_arg, map_zero, span_X_isPrime, span_singleton_prime
-/
theorem X_prime : Prime (X : R⟦X⟧) := by
  rw [← Ideal.span_singleton_prime]
  · exact span_X_isPrime
  · intro h
    simpa [map_zero (coeff 1)] using congr_arg (coeff 1) h

/--
theorem `X_irreducible` / 定理 `X_irreducible`

English:
theorem X_irreducible
  statement: Irreducible (X : R⟦X⟧)
  proof: X_prime.irreducible

中文:
定理 X_irreducible
  结论: 不可约 (X : R⟦X⟧)
  证明: X_prime.irreducible

Depends on / 依赖: X_prime, X_prime.irreducible, irreducible
-/
theorem X_irreducible : Irreducible (X : R⟦X⟧) := X_prime.irreducible

/--
theorem `rescale_injective` / 定理 `rescale_injective`

English:
theorem rescale_injective
  given: {a : R} (ha : a != 0)
  statement: Function.Injective (rescale a)
  proof: by
  intro p q h
  rw [PowerSeries.ext_iff] at *
  intro n
  specialize h n
  rwa [coeff_rescale, coeff_rescale, mul_right_inj' <| pow_ne_zero _ ha] at h

中文:
定理 rescale_injective
  条件: {a : R} (ha : a != 0)
  结论: 函数.单射 (rescale a)
  证明: by
  intro p q h
  rw [PowerSeries.ext_iff] at *
  intro n
  specialize h n
  rwa [coeff_rescale, coeff_rescale, mul_right_inj' <| pow_ne_zero _ ha] at h

Depends on / 依赖: PowerSeries, PowerSeries.ext_iff, coeff_rescale, ext_iff, mul_right_inj, pow_ne_zero, specialize
-/
theorem rescale_injective {a : R} (ha : a != 0) : Function.Injective (rescale a) := by
  intro p q h
  rw [PowerSeries.ext_iff] at *
  intro n
  specialize h n
  rwa [coeff_rescale, coeff_rescale, mul_right_inj' <| pow_ne_zero _ ha] at h

end IsDomain

end PowerSeries
