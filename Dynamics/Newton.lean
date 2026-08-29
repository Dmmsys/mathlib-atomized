/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, Oliver Nash
-/
module

public import Mathlib.RingTheory.Polynomial.Nilpotent

/-!
# Newton-Raphson method

Given a single-variable polynomial `P` with derivative `P'`, Newton's method concerns iteration of
the rational map: `x ↦ x - P(x) / P'(x)`.

Over a field, it can serve as a root-finding algorithm. It is also useful in proving results such
as Hensel's lemma and the Jordan-Chevalley decomposition.

## Main definitions / results:

* `Polynomial.newtonMap`: the map `x ↦ x - P(x) / P'(x)`, where `P'` is the derivative of the
  polynomial `P`.
* `Polynomial.isFixedPt_newtonMap_of_isUnit_iff`: `x` is a fixed point for Newton iteration iff
  it is a root of `P` (provided `P'(x)` is a unit).
* `Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero`: if `x` is almost a root of `P` in the
  sense that `P(x)` is nilpotent (and `P'(x)` is a unit) then we may write `x` as a sum
  `x = n + r` where `n` is nilpotent and `r` is a root of `P`. This can be used to prove the
  Jordan-Chevalley decomposition of linear endomorphisms.

-/

@[expose] public section

open Set Function

noncomputable section

namespace Polynomial

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (P : R[X]) {x : S}

/--
Definition of `newtonMap` / `newtonMap` 的定义

English:
definition newtonMap
  signature: (x : S)
  body: x - (Ring.inverse <| aeval x (derivative P)) * aeval x P

中文:
定义 newtonMap
  签名: (x : S)
  定义体: x - (Ring.inverse <| aeval x (derivative P)) * aeval x P

Depends on / 依赖: Ring.inverse, derivative, inverse
-/
def newtonMap (x : S) : S :=
  x - (Ring.inverse <| aeval x (derivative P)) * aeval x P

/--
theorem `newtonMap_apply` / 定理 `newtonMap_apply`

English:
theorem newtonMap_apply
  proof: rfl

中文:
定理 newtonMap_apply
  证明: rfl
-/
theorem newtonMap_apply :
    P.newtonMap x = x - (Ring.inverse <| aeval x (derivative P)) * (aeval x P) :=
  rfl

variable {P}

/--
theorem `newtonMap_apply_of_isUnit` / 定理 `newtonMap_apply_of_isUnit`

English:
theorem newtonMap_apply_of_isUnit
  given: (h : IsUnit <| aeval x (derivative P))
  proof: by
  simp [newtonMap_apply, Ring.inverse, h]

中文:
定理 newtonMap_apply_of_isUnit
  条件: (h : 是单位 <| aeval x (derivative P))
  证明: by
  simp [newtonMap_apply, Ring.inverse, h]

Depends on / 依赖: Ring.inverse, inverse, newtonMap_apply
-/
theorem newtonMap_apply_of_isUnit (h : IsUnit <| aeval x (derivative P)) :
    P.newtonMap x = x - h.unit⁻¹ * aeval x P := by
  simp [newtonMap_apply, Ring.inverse, h]

/--
theorem `newtonMap_apply_of_not_isUnit` / 定理 `newtonMap_apply_of_not_isUnit`

English:
theorem newtonMap_apply_of_not_isUnit
  given: (h : ¬ (IsUnit <| aeval x (derivative P)))
  proof: by
  simp [newtonMap_apply, Ring.inverse, h]

中文:
定理 newtonMap_apply_of_not_isUnit
  条件: (h : ¬ (是单位 <| aeval x (derivative P)))
  证明: by
  simp [newtonMap_apply, Ring.inverse, h]

Depends on / 依赖: Ring.inverse, inverse, newtonMap_apply
-/
theorem newtonMap_apply_of_not_isUnit (h : ¬ (IsUnit <| aeval x (derivative P))) :
    P.newtonMap x = x := by
  simp [newtonMap_apply, Ring.inverse, h]

/--
theorem `isNilpotent_iterate_newtonMap_sub_of_isNilpotent` / 定理 `isNilpotent_iterate_newtonMap_sub_of_isNilpotent`

English:
theorem isNilpotent_iterate_newtonMap_sub_of_isNilpotent
  given: (h : IsNilpotent <| aeval x P) (n : Nat)
  proof: by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ']; rw [comp_apply]; rw [newtonMap_apply]; rw [sub_right_comm]
refine (Commute.all _ _).isNilpotent_sub ih (Commute.all _ _).isNilpotent_mul_left ?_
    simpa using Commute.isNilpotent_add (Commute.all _ _)
      (isNilpotent_aeval_sub_of_isNilpotent_sub P ih) h

中文:
定理 isNilpotent_iterate_newtonMap_sub_of_isNilpotent
  条件: (h : 是幂零 <| aeval x P) (n : 自然数)
  证明: by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ']; rw [comp_apply]; rw [newtonMap_apply]; rw [sub_right_comm]
refine (Commute.all _ _).isNilpotent_sub ih (Commute.all _ _).isNilpotent_mul_left ?_
    simpa using Commute.isNilpotent_add (Commute.all _ _)
      (isNilpotent_aeval_sub_of_isNilpotent_sub P ih) h

Depends on / 依赖: Commute, Commute.all, Commute.isNilpotent_add, comp_apply, isNilpotent_add, isNilpotent_aeval_sub_of_isNilpotent_sub, isNilpotent_mul_left, isNilpotent_sub, iterate_succ, newtonMap_apply, sub_right_comm
-/
theorem isNilpotent_iterate_newtonMap_sub_of_isNilpotent (h : IsNilpotent <| aeval x P) (n : Nat) :
IsNilpotent P.newtonMap^[n] x - x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ']; rw [comp_apply]; rw [newtonMap_apply]; rw [sub_right_comm]
refine (Commute.all _ _).isNilpotent_sub ih (Commute.all _ _).isNilpotent_mul_left ?_
    simpa using Commute.isNilpotent_add (Commute.all _ _)
      (isNilpotent_aeval_sub_of_isNilpotent_sub P ih) h

/--
theorem `isFixedPt_newtonMap_of_aeval_eq_zero` / 定理 `isFixedPt_newtonMap_of_aeval_eq_zero`

English:
theorem isFixedPt_newtonMap_of_aeval_eq_zero
  given: (h : aeval x P = 0)
  proof: by
  rw [IsFixedPt]; rw [newtonMap_apply]; rw [h]; rw [mul_zero]; rw [sub_zero]

中文:
定理 isFixedPt_newtonMap_of_aeval_eq_zero
  条件: (h : aeval x P = 0)
  证明: by
  rw [IsFixedPt]; rw [newtonMap_apply]; rw [h]; rw [mul_zero]; rw [sub_zero]

Depends on / 依赖: IsFixedPt, mul_zero, newtonMap_apply, sub_zero
-/
theorem isFixedPt_newtonMap_of_aeval_eq_zero (h : aeval x P = 0) :
    IsFixedPt P.newtonMap x := by
  rw [IsFixedPt]; rw [newtonMap_apply]; rw [h]; rw [mul_zero]; rw [sub_zero]

/--
theorem `isFixedPt_newtonMap_of_isUnit_iff` / 定理 `isFixedPt_newtonMap_of_isUnit_iff`

English:
theorem isFixedPt_newtonMap_of_isUnit_iff
  given: (h : IsUnit <| aeval x (derivative P))
  proof: by
  rw [IsFixedPt]; rw [newtonMap_apply]; rw [sub_eq_self]; rw [Ring.inverse_mul_eq_iff_eq_mul _ _ _ h]; rw [mul_zero]

中文:
定理 isFixedPt_newtonMap_of_isUnit_iff
  条件: (h : 是单位 <| aeval x (derivative P))
  证明: by
  rw [IsFixedPt]; rw [newtonMap_apply]; rw [sub_eq_self]; rw [Ring.inverse_mul_eq_iff_eq_mul _ _ _ h]; rw [mul_zero]

Depends on / 依赖: IsFixedPt, Ring.inverse_mul_eq_iff_eq_mul, inverse_mul_eq_iff_eq_mul, mul_zero, newtonMap_apply, sub_eq_self
-/
theorem isFixedPt_newtonMap_of_isUnit_iff (h : IsUnit <| aeval x (derivative P)) :
    IsFixedPt P.newtonMap x ↔ aeval x P = 0 := by
  rw [IsFixedPt]; rw [newtonMap_apply]; rw [sub_eq_self]; rw [Ring.inverse_mul_eq_iff_eq_mul _ _ _ h]; rw [mul_zero]

/--
theorem `aeval_pow_two_pow_dvd_aeval_iterate_newtonMap` / 定理 `aeval_pow_two_pow_dvd_aeval_iterate_newtonMap`

English:
theorem aeval_pow_two_pow_dvd_aeval_iterate_newtonMap
  proof: by
  induction n with
  | zero => simp
  | succ n ih =>
    have ⟨d, hd⟩ := binomExpansion (P.map (algebraMap R S)) (P.newtonMap^[n] x)
      (-Ring.inverse (aeval (P.newtonMap^[n] x) <| derivative P) * aeval (P.newtonMap^[n] x) P)
    rw [eval_map_algebraMap]; rw [eval_map_algebraMap] at hd
    rw [iterate_succ']; rw [comp_apply]; rw [newtonMap_apply]; rw [sub_eq_add_neg]; rw [neg_mul_eq_neg_mul]; rw [hd]
    refine dvd_add ?_ (dvd_mul_of_dvd_right ?_ _)
    · convert! dvd_zero _
      have : IsUnit (aeval (P.newtonMap^[n] x) <| derivative P) :=
isUnit_aeval_of_isUnit_aeval_of_isNilpotent_sub h'
        isNilpotent_iterate_newtonMap_sub_of_isNilpotent h n
      rw [derivative_map]; rw [eval_map_algebraMap]; rw [← mul_assoc]; rw [mul_neg]; rw [Ring.mul_inverse_cancel _ this]; rw [neg_mul]; rw [one_mul]; rw [add_neg_cancel]
    · rw [neg_mul, even_two.neg_pow, mul_pow, pow_succ, pow_mul]
      exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd ih 2) _

中文:
定理 aeval_pow_two_pow_dvd_aeval_iterate_newtonMap
  证明: by
  induction n with
  | zero => simp
  | succ n ih =>
    have ⟨d, hd⟩ := binomExpansion (P.map (algebraMap R S)) (P.newtonMap^[n] x)
      (-Ring.inverse (aeval (P.newtonMap^[n] x) <| derivative P) * aeval (P.newtonMap^[n] x) P)
    rw [eval_map_algebraMap]; rw [eval_map_algebraMap] at hd
    rw [iterate_succ']; rw [comp_apply]; rw [newtonMap_apply]; rw [sub_eq_add_neg]; rw [neg_mul_eq_neg_mul]; rw [hd]
    refine dvd_add ?_ (dvd_mul_of_dvd_right ?_ _)
    · convert! dvd_zero _
      have : IsUnit (aeval (P.newtonMap^[n] x) <| derivative P) :=
isUnit_aeval_of_isUnit_aeval_of_isNilpotent_sub h'
        isNilpotent_iterate_newtonMap_sub_of_isNilpotent h n
      rw [derivative_map]; rw [eval_map_algebraMap]; rw [← mul_assoc]; rw [mul_neg]; rw [Ring.mul_inverse_cancel _ this]; rw [neg_mul]; rw [one_mul]; rw [add_neg_cancel]
    · rw [neg_mul, even_two.neg_pow, mul_pow, pow_succ, pow_mul]
      exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd ih 2) _

Depends on / 依赖: IsUnit, P.map, P.newtonMap, Ring.inverse, algebraMap, binomExpansion, comp_apply, convert, derivative, dvd_add, dvd_mul_of_dvd_right, dvd_zero, eval_map_algebraMap, inverse, iterate_succ, neg_mul_eq_neg_mul, newtonMap, newtonMap_apply, sub_eq_add_neg
-/
theorem aeval_pow_two_pow_dvd_aeval_iterate_newtonMap
    (h : IsNilpotent (aeval x P)) (h' : IsUnit (aeval x <| derivative P)) (n : Nat) :
    (aeval x P) ^ (2 ^ n) ∣ aeval (P.newtonMap^[n] x) P := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ⟨d, hd⟩ := binomExpansion (P.map (algebraMap R S)) (P.newtonMap^[n] x)
      (-Ring.inverse (aeval (P.newtonMap^[n] x) <| derivative P) * aeval (P.newtonMap^[n] x) P)
    rw [eval_map_algebraMap]; rw [eval_map_algebraMap] at hd
    rw [iterate_succ']; rw [comp_apply]; rw [newtonMap_apply]; rw [sub_eq_add_neg]; rw [neg_mul_eq_neg_mul]; rw [hd]
    refine dvd_add ?_ (dvd_mul_of_dvd_right ?_ _)
    · convert! dvd_zero _
      have : IsUnit (aeval (P.newtonMap^[n] x) <| derivative P) :=
isUnit_aeval_of_isUnit_aeval_of_isNilpotent_sub h'
        isNilpotent_iterate_newtonMap_sub_of_isNilpotent h n
      rw [derivative_map]; rw [eval_map_algebraMap]; rw [← mul_assoc]; rw [mul_neg]; rw [Ring.mul_inverse_cancel _ this]; rw [neg_mul]; rw [one_mul]; rw [add_neg_cancel]
    · rw [neg_mul, even_two.neg_pow, mul_pow, pow_succ, pow_mul]
      exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd ih 2) _

/--
theorem `existsUnique_nilpotent_sub_and_aeval_eq_zero` / 定理 `existsUnique_nilpotent_sub_and_aeval_eq_zero`

English:
theorem existsUnique_nilpotent_sub_and_aeval_eq_zero
  proof: by
  simp_rw [(neg_sub _ x).symm, isNilpotent_neg_iff]
  refine existsUnique_of_exists_of_unique ?_ fun r₁ r₂ ⟨hr₁, hr₁'⟩ ⟨hr₂, hr₂'⟩ => ?_
  · -- Existence
    obtain ⟨n, hn⟩ := id h
    refine ⟨P.newtonMap^[n] x, isNilpotent_iterate_newtonMap_sub_of_isNilpotent h n, ?_⟩
    rw [← zero_dvd_iff]; rw [← pow_eq_zero_of_le (n.lt_two_pow_self).le hn]
    exact aeval_pow_two_pow_dvd_aeval_iterate_newtonMap h h' n
  · -- Uniqueness
    have ⟨u, hu⟩ := binomExpansion (P.map (algebraMap R S)) r₁ (r₂ - r₁)
    suffices IsUnit (aeval r₁ (derivative P) + u * (r₂ - r₁)) by
      rwa [derivative_map, eval_map_algebraMap, eval_map_algebraMap, eval_map_algebraMap,
        add_sub_cancel, hr₂', hr₁', zero_add, pow_two, ← mul_assoc, ← add_mul, eq_comm,
        this.mul_right_eq_zero, sub_eq_zero, eq_comm] at hu
    have : IsUnit (aeval r₁ (derivative P)) :=
      isUnit_aeval_of_isUnit_aeval_of_isNilpotent_sub h' hr₁
    rw [← sub_sub_sub_cancel_right r₂ r₁ x]
    refine IsNilpotent.isUnit_add_left_of_commute ?_ this (Commute.all _ _)
exact (Commute.all _ _).isNilpotent_mul_left (Commute.all _ _).isNilpotent_sub hr₂ hr₁

中文:
定理 存在Unique_nilpotent_sub_and_aeval_eq_zero
  证明: by
  simp_rw [(neg_sub _ x).symm, isNilpotent_neg_iff]
  refine existsUnique_of_exists_of_unique ?_ fun r₁ r₂ ⟨hr₁, hr₁'⟩ ⟨hr₂, hr₂'⟩ => ?_
  · -- Existence
    obtain ⟨n, hn⟩ := id h
    refine ⟨P.newtonMap^[n] x, isNilpotent_iterate_newtonMap_sub_of_isNilpotent h n, ?_⟩
    rw [← zero_dvd_iff]; rw [← pow_eq_zero_of_le (n.lt_two_pow_self).le hn]
    exact aeval_pow_two_pow_dvd_aeval_iterate_newtonMap h h' n
  · -- Uniqueness
    have ⟨u, hu⟩ := binomExpansion (P.map (algebraMap R S)) r₁ (r₂ - r₁)
    suffices IsUnit (aeval r₁ (derivative P) + u * (r₂ - r₁)) by
      rwa [derivative_map, eval_map_algebraMap, eval_map_algebraMap, eval_map_algebraMap,
        add_sub_cancel, hr₂', hr₁', zero_add, pow_two, ← mul_assoc, ← add_mul, eq_comm,
        this.mul_right_eq_zero, sub_eq_zero, eq_comm] at hu
    have : IsUnit (aeval r₁ (derivative P)) :=
      isUnit_aeval_of_isUnit_aeval_of_isNilpotent_sub h' hr₁
    rw [← sub_sub_sub_cancel_right r₂ r₁ x]
    refine IsNilpotent.isUnit_add_left_of_commute ?_ this (Commute.all _ _)
exact (Commute.all _ _).isNilpotent_mul_left (Commute.all _ _).isNilpotent_sub hr₂ hr₁

Depends on / 依赖: Existence, IsUnit, P.map, P.newtonMap, Uniqueness, aeval_pow_two_pow_dvd_aeval_iterate_newtonMap, algebraMap, binomExpansion, existsUnique_of_exists_of_unique, isNilpotent_iterate_newtonMap_sub_of_isNilpotent, isNilpotent_neg_iff, lt_two_pow_self, n.lt_two_pow_self, neg_sub, newtonMap, pow_eq_zero_of_le, simp_rw, zero_dvd_iff
-/
theorem existsUnique_nilpotent_sub_and_aeval_eq_zero
    (h : IsNilpotent (aeval x P)) (h' : IsUnit (aeval x <| derivative P)) :
    exists! r, IsNilpotent (x - r) ∧ aeval r P = 0 := by
  simp_rw [(neg_sub _ x).symm, isNilpotent_neg_iff]
  refine existsUnique_of_exists_of_unique ?_ fun r₁ r₂ ⟨hr₁, hr₁'⟩ ⟨hr₂, hr₂'⟩ => ?_
  · -- Existence
    obtain ⟨n, hn⟩ := id h
    refine ⟨P.newtonMap^[n] x, isNilpotent_iterate_newtonMap_sub_of_isNilpotent h n, ?_⟩
    rw [← zero_dvd_iff]; rw [← pow_eq_zero_of_le (n.lt_two_pow_self).le hn]
    exact aeval_pow_two_pow_dvd_aeval_iterate_newtonMap h h' n
  · -- Uniqueness
    have ⟨u, hu⟩ := binomExpansion (P.map (algebraMap R S)) r₁ (r₂ - r₁)
    suffices IsUnit (aeval r₁ (derivative P) + u * (r₂ - r₁)) by
      rwa [derivative_map, eval_map_algebraMap, eval_map_algebraMap, eval_map_algebraMap,
        add_sub_cancel, hr₂', hr₁', zero_add, pow_two, ← mul_assoc, ← add_mul, eq_comm,
        this.mul_right_eq_zero, sub_eq_zero, eq_comm] at hu
    have : IsUnit (aeval r₁ (derivative P)) :=
      isUnit_aeval_of_isUnit_aeval_of_isNilpotent_sub h' hr₁
    rw [← sub_sub_sub_cancel_right r₂ r₁ x]
    refine IsNilpotent.isUnit_add_left_of_commute ?_ this (Commute.all _ _)
exact (Commute.all _ _).isNilpotent_mul_left (Commute.all _ _).isNilpotent_sub hr₂ hr₁

end Polynomial
