/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Chris Hughes
-/
module

public import Mathlib.Algebra.GCDMonoid.Basic
public import Mathlib.Algebra.EuclideanDomain.Basic
public import Mathlib.RingTheory.Ideal.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Lemmas about Euclidean domains

Various about Euclidean domains are proved; all of them seem to be true
more generally for principal ideal domains, so these lemmas should
probably be reproved in more generality and this file perhaps removed?

## Tags

euclidean domain
-/

@[expose] public section


section

open EuclideanDomain Set Ideal

section GCDMonoid

variable {R : Type*} [EuclideanDomain R] [GCDMonoid R] {p q : R}

/--
theorem `left_div_gcd_ne_zero` / 定理 `left_div_gcd_ne_zero`

English:
theorem left_div_gcd_ne_zero
  given: {p q : R} (hp : p != 0)
  statement: p / GCDMonoid.gcd p q != 0
  proof: by
  obtain ⟨r, hr⟩ := GCDMonoid.gcd_dvd_left p q
  obtain ⟨pq0, r0⟩ : GCDMonoid.gcd p q != 0 ∧ r != 0 := mul_ne_zero_iff.mp (hr ▸ hp)
  nth_rw 1 [hr]
  rw [mul_comm]; rw [mul_div_cancel_right₀ _ pq0]
  exact r0

中文:
定理 left_div_gcd_ne_zero
  条件: {p q : R} (hp : p != 0)
  结论: p / 最大公约数幺半群.最大公约数 p q != 0
  证明: by
  obtain ⟨r, hr⟩ := GCDMonoid.gcd_dvd_left p q
  obtain ⟨pq0, r0⟩ : GCDMonoid.gcd p q != 0 ∧ r != 0 := mul_ne_zero_iff.mp (hr ▸ hp)
  nth_rw 1 [hr]
  rw [mul_comm]; rw [mul_div_cancel_right₀ _ pq0]
  exact r0

Depends on / 依赖: GCDMonoid, GCDMonoid.gcd, GCDMonoid.gcd_dvd_left, gcd_dvd_left, mul_comm, mul_ne_zero_iff, mul_ne_zero_iff.mp, nth_rw
-/
theorem left_div_gcd_ne_zero {p q : R} (hp : p != 0) : p / GCDMonoid.gcd p q != 0 := by
  obtain ⟨r, hr⟩ := GCDMonoid.gcd_dvd_left p q
  obtain ⟨pq0, r0⟩ : GCDMonoid.gcd p q != 0 ∧ r != 0 := mul_ne_zero_iff.mp (hr ▸ hp)
  nth_rw 1 [hr]
  rw [mul_comm]; rw [mul_div_cancel_right₀ _ pq0]
  exact r0

/--
theorem `right_div_gcd_ne_zero` / 定理 `right_div_gcd_ne_zero`

English:
theorem right_div_gcd_ne_zero
  given: {p q : R} (hq : q != 0)
  statement: q / GCDMonoid.gcd p q != 0
  proof: by
  obtain ⟨r, hr⟩ := GCDMonoid.gcd_dvd_right p q
  obtain ⟨pq0, r0⟩ : GCDMonoid.gcd p q != 0 ∧ r != 0 := mul_ne_zero_iff.mp (hr ▸ hq)
  nth_rw 1 [hr]
  rw [mul_comm]; rw [mul_div_cancel_right₀ _ pq0]
  exact r0

中文:
定理 right_div_gcd_ne_zero
  条件: {p q : R} (hq : q != 0)
  结论: q / 最大公约数幺半群.最大公约数 p q != 0
  证明: by
  obtain ⟨r, hr⟩ := GCDMonoid.gcd_dvd_right p q
  obtain ⟨pq0, r0⟩ : GCDMonoid.gcd p q != 0 ∧ r != 0 := mul_ne_zero_iff.mp (hr ▸ hq)
  nth_rw 1 [hr]
  rw [mul_comm]; rw [mul_div_cancel_right₀ _ pq0]
  exact r0

Depends on / 依赖: GCDMonoid, GCDMonoid.gcd, GCDMonoid.gcd_dvd_right, gcd_dvd_right, mul_comm, mul_ne_zero_iff, mul_ne_zero_iff.mp, nth_rw
-/
theorem right_div_gcd_ne_zero {p q : R} (hq : q != 0) : q / GCDMonoid.gcd p q != 0 := by
  obtain ⟨r, hr⟩ := GCDMonoid.gcd_dvd_right p q
  obtain ⟨pq0, r0⟩ : GCDMonoid.gcd p q != 0 ∧ r != 0 := mul_ne_zero_iff.mp (hr ▸ hq)
  nth_rw 1 [hr]
  rw [mul_comm]; rw [mul_div_cancel_right₀ _ pq0]
  exact r0

/--
theorem `isCoprime_div_gcd_div_gcd` / 定理 `isCoprime_div_gcd_div_gcd`

English:
theorem isCoprime_div_gcd_div_gcd
  given: (hq : q != 0)
  proof: (gcd_isUnit_iff _ _).1
    isUnit_gcd_of_eq_mul_gcd
        (EuclideanDomain.mul_div_cancel' (gcd_ne_zero_of_right hq) <| gcd_dvd_left _ _).symm
(EuclideanDomain.mul_div_cancel' (gcd_ne_zero_of_right hq) <| gcd_dvd_right _ _).symm
      gcd_ne_zero_of_right hq

中文:
定理 isCoprime_div_gcd_div_gcd
  条件: (hq : q != 0)
  证明: (gcd_isUnit_iff _ _).1
    isUnit_gcd_of_eq_mul_gcd
        (EuclideanDomain.mul_div_cancel' (gcd_ne_zero_of_right hq) <| gcd_dvd_left _ _).symm
(EuclideanDomain.mul_div_cancel' (gcd_ne_zero_of_right hq) <| gcd_dvd_right _ _).symm
      gcd_ne_zero_of_right hq

Depends on / 依赖: EuclideanDomain, EuclideanDomain.mul_div_cancel, gcd_dvd_left, gcd_dvd_right, gcd_isUnit_iff, gcd_ne_zero_of_right, isUnit_gcd_of_eq_mul_gcd, mul_div_cancel
-/
theorem isCoprime_div_gcd_div_gcd (hq : q != 0) :
    IsCoprime (p / GCDMonoid.gcd p q) (q / GCDMonoid.gcd p q) :=
(gcd_isUnit_iff _ _).1
    isUnit_gcd_of_eq_mul_gcd
        (EuclideanDomain.mul_div_cancel' (gcd_ne_zero_of_right hq) <| gcd_dvd_left _ _).symm
(EuclideanDomain.mul_div_cancel' (gcd_ne_zero_of_right hq) <| gcd_dvd_right _ _).symm
      gcd_ne_zero_of_right hq

/--
theorem `isCoprime_div_gcd_div_gcd_of_gcd_ne_zero` / 定理 `isCoprime_div_gcd_div_gcd_of_gcd_ne_zero`

English:
theorem isCoprime_div_gcd_div_gcd_of_gcd_ne_zero
  given: (hpq : GCDMonoid.gcd p q != 0)
  proof: (gcd_isUnit_iff _ _).1
    isUnit_gcd_of_eq_mul_gcd
        (EuclideanDomain.mul_div_cancel' (hpq) <| gcd_dvd_left _ _).symm
(EuclideanDomain.mul_div_cancel' (hpq) <| gcd_dvd_right _ _).symm hpq

中文:
定理 isCoprime_div_gcd_div_gcd_of_gcd_ne_zero
  条件: (hpq : 最大公约数幺半群.最大公约数 p q != 0)
  证明: (gcd_isUnit_iff _ _).1
    isUnit_gcd_of_eq_mul_gcd
        (EuclideanDomain.mul_div_cancel' (hpq) <| gcd_dvd_left _ _).symm
(EuclideanDomain.mul_div_cancel' (hpq) <| gcd_dvd_right _ _).symm hpq

Depends on / 依赖: EuclideanDomain, EuclideanDomain.mul_div_cancel, gcd_dvd_left, gcd_dvd_right, gcd_isUnit_iff, isUnit_gcd_of_eq_mul_gcd, mul_div_cancel
-/
theorem isCoprime_div_gcd_div_gcd_of_gcd_ne_zero (hpq : GCDMonoid.gcd p q != 0) :
    IsCoprime (p / GCDMonoid.gcd p q) (q / GCDMonoid.gcd p q) :=
(gcd_isUnit_iff _ _).1
    isUnit_gcd_of_eq_mul_gcd
        (EuclideanDomain.mul_div_cancel' (hpq) <| gcd_dvd_left _ _).symm
(EuclideanDomain.mul_div_cancel' (hpq) <| gcd_dvd_right _ _).symm hpq

end GCDMonoid

namespace EuclideanDomain

/-- Create a `GCDMonoid` whose `GCDMonoid.gcd` matches `EuclideanDomain.gcd`. -/
@[instance_reducible]
/--
Definition of `gcdMonoid` / `gcdMonoid` 的定义

English:
definition gcdMonoid
  signature: (R) [EuclideanDomain R] [DecidableEq R]
  body: gcd
  lcm := lcm
  gcd_dvd_left := gcd_dvd_left
  gcd_dvd_right := gcd_dvd_right
  dvd_gcd := dvd_gcd
  gcd_mul_lcm a b := by rw [EuclideanDomain.gcd_mul_lcm]; rfl
  lcm_zero_left := lcm_zero_left
  lcm_zero_right := lcm_zero_right

中文:
定义 gcdMonoid
  签名: (R) [欧几里得整环 R] [DecidableEq R]
  定义体: gcd
  lcm := lcm
  gcd_dvd_left := gcd_dvd_left
  gcd_dvd_right := gcd_dvd_right
  dvd_gcd := dvd_gcd
  gcd_mul_lcm a b := by rw [EuclideanDomain.gcd_mul_lcm]; rfl
  lcm_zero_left := lcm_zero_left
  lcm_zero_right := lcm_zero_right
-/
def gcdMonoid (R) [EuclideanDomain R] [DecidableEq R] : GCDMonoid R where
  gcd := gcd
  lcm := lcm
  gcd_dvd_left := gcd_dvd_left
  gcd_dvd_right := gcd_dvd_right
  dvd_gcd := dvd_gcd
  gcd_mul_lcm a b := by rw [EuclideanDomain.gcd_mul_lcm]; rfl
  lcm_zero_left := lcm_zero_left
  lcm_zero_right := lcm_zero_right

variable {α : Type*} [EuclideanDomain α]

/--
theorem `span_gcd` / 定理 `span_gcd`

English:
theorem span_gcd
  given: [DecidableEq α] (x y : α)
  proof: letI := EuclideanDomain.gcdMonoid α
  _root_.span_gcd x y

中文:
定理 span_gcd
  条件: [DecidableEq α] (x y : α)
  证明: letI := EuclideanDomain.gcdMonoid α
  _root_.span_gcd x y

Depends on / 依赖: EuclideanDomain, EuclideanDomain.gcdMonoid, _root_, _root_.span_gcd, gcdMonoid, span_gcd
-/
theorem span_gcd [DecidableEq α] (x y : α) :
    span ({gcd x y} : Set α) = span ({x, y} : Set α) :=
  letI := EuclideanDomain.gcdMonoid α
  _root_.span_gcd x y

/--
theorem `gcd_isUnit_iff` / 定理 `gcd_isUnit_iff`

English:
theorem gcd_isUnit_iff
  given: [DecidableEq α] {x y : α}
  statement: IsUnit (gcd x y) ↔ IsCoprime x y
  proof: letI := EuclideanDomain.gcdMonoid α
  _root_.gcd_isUnit_iff x y

中文:
定理 gcd_isUnit_iff
  条件: [DecidableEq α] {x y : α}
  结论: 是单位 (最大公约数 x y) ↔ IsCoprime x y
  证明: letI := EuclideanDomain.gcdMonoid α
  _root_.gcd_isUnit_iff x y

Depends on / 依赖: EuclideanDomain, EuclideanDomain.gcdMonoid, _root_, _root_.gcd_isUnit_iff, gcdMonoid, gcd_isUnit_iff
-/
theorem gcd_isUnit_iff [DecidableEq α] {x y : α} : IsUnit (gcd x y) ↔ IsCoprime x y :=
  letI := EuclideanDomain.gcdMonoid α
  _root_.gcd_isUnit_iff x y

-- this should be proved for UFDs surely?
/--
theorem `isCoprime_of_dvd` / 定理 `isCoprime_of_dvd`

English:
theorem isCoprime_of_dvd
  statement: {x y : α} (nonzero : ¬(x = 0 ∧ y = 0))
  proof: letI := Classical.decEq α
  letI := EuclideanDomain.gcdMonoid α
  _root_.isCoprime_of_dvd x y nonzero H

中文:
定理 isCoprime_of_dvd
  结论: {x y : α} (nonzero : ¬(x = 0 ∧ y = 0))
  证明: letI := Classical.decEq α
  letI := EuclideanDomain.gcdMonoid α
  _root_.isCoprime_of_dvd x y nonzero H

Depends on / 依赖: Classical, Classical.decEq, EuclideanDomain, EuclideanDomain.gcdMonoid, _root_, _root_.isCoprime_of_dvd, gcdMonoid, isCoprime_of_dvd, nonzero
-/
theorem isCoprime_of_dvd {x y : α} (nonzero : ¬(x = 0 ∧ y = 0))
    (H : forall z in nonunits α, z != 0 -> z ∣ x -> ¬z ∣ y) : IsCoprime x y :=
  letI := Classical.decEq α
  letI := EuclideanDomain.gcdMonoid α
  _root_.isCoprime_of_dvd x y nonzero H

-- this should be proved for UFDs surely?
/--
theorem `dvd_or_coprime` / 定理 `dvd_or_coprime`

English:
theorem dvd_or_coprime
  given: (x y : α) (h : Irreducible x)
  proof: letI := Classical.decEq α
  letI := EuclideanDomain.gcdMonoid α
  _root_.dvd_or_isCoprime x y h

中文:
定理 dvd_or_coprime
  条件: (x y : α) (h : 不可约 x)
  证明: letI := Classical.decEq α
  letI := EuclideanDomain.gcdMonoid α
  _root_.dvd_or_isCoprime x y h

Depends on / 依赖: Classical, Classical.decEq, EuclideanDomain, EuclideanDomain.gcdMonoid, _root_, _root_.dvd_or_isCoprime, dvd_or_isCoprime, gcdMonoid
-/
theorem dvd_or_coprime (x y : α) (h : Irreducible x) :
    x ∣ y ∨ IsCoprime x y :=
  letI := Classical.decEq α
  letI := EuclideanDomain.gcdMonoid α
  _root_.dvd_or_isCoprime x y h

end EuclideanDomain

end
