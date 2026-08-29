/-
Copyright (c) 2023 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching, Ashvni Narayanan, Michael Stoll
-/
module

public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Lemmas about units in `ZMod`.
-/

@[expose] public section

assert_not_exists TwoSidedIdeal

namespace ZMod

variable {n m : Nat}
/--
Definition of `unitsMap` / `unitsMap` 的定义

English:
definition unitsMap
  signature: (hm : n ∣ m)
  body: Units.map (castHom hm (ZMod n))

中文:
定义 unitsMap
  签名: (hm : n ∣ m)
  定义体: Units.map (castHom hm (ZMod n))

Depends on / 依赖: Units.map, castHom
-/
def unitsMap (hm : n ∣ m) : (ZMod m)ˣ ->* (ZMod n)ˣ := Units.map (castHom hm (ZMod n))

/--
lemma `unitsMap_def` / 引理 `unitsMap_def`

English:
lemma unitsMap_def
  given: (hm : n ∣ m)
  statement: unitsMap hm = Units.map (castHom hm (ZMod n))
  proof: rfl

中文:
引理 unitsMap_def
  条件: (hm : n ∣ m)
  结论: unitsMap hm = 单位群.map (castHom hm (ZMod n))
  证明: rfl
-/
lemma unitsMap_def (hm : n ∣ m) : unitsMap hm = Units.map (castHom hm (ZMod n)) := rfl

/--
lemma `unitsMap_comp` / 引理 `unitsMap_comp`

English:
lemma unitsMap_comp
  given: {d : Nat} (hm : n ∣ m) (hd : m ∣ d)
  proof: by
  simp only [unitsMap_def]
  rw [← Units.map_comp]
exact congr_arg Units.map congr_arg RingHom.toMonoidHom castHom_comp hm hd

@[simp]

中文:
引理 unitsMap_comp
  条件: {d : 自然数} (hm : n ∣ m) (hd : m ∣ d)
  证明: by
  simp only [unitsMap_def]
  rw [← Units.map_comp]
exact congr_arg Units.map congr_arg RingHom.toMonoidHom castHom_comp hm hd

@[simp]

Depends on / 依赖: RingHom, RingHom.toMonoidHom, Units.map, Units.map_comp, castHom_comp, congr_arg, map_comp, toMonoidHom, unitsMap_def
-/
lemma unitsMap_comp {d : Nat} (hm : n ∣ m) (hd : m ∣ d) :
    (unitsMap hm).comp (unitsMap hd) = unitsMap (dvd_trans hm hd) := by
  simp only [unitsMap_def]
  rw [← Units.map_comp]
exact congr_arg Units.map congr_arg RingHom.toMonoidHom castHom_comp hm hd

@[simp]
/--
lemma `unitsMap_self` / 引理 `unitsMap_self`

English:
lemma unitsMap_self
  given: (n : Nat)
  statement: unitsMap (dvd_refl n) = MonoidHom.id _
  proof: by
  simp [unitsMap, castHom_self]

中文:
引理 unitsMap_self
  条件: (n : 自然数)
  结论: unitsMap (dvd_refl n) = 幺半群态射.id _
  证明: by
  simp [unitsMap, castHom_self]

Depends on / 依赖: castHom_self, unitsMap
-/
lemma unitsMap_self (n : Nat) : unitsMap (dvd_refl n) = MonoidHom.id _ := by
  simp [unitsMap, castHom_self]

/--
lemma `unitsMap_val` / 引理 `unitsMap_val`

English:
lemma unitsMap_val
  given: (h : n ∣ m) (a : (ZMod m)ˣ)
  proof: rfl

中文:
引理 unitsMap_val
  条件: (h : n ∣ m) (a : (ZMod m)ˣ)
  证明: rfl
-/
lemma unitsMap_val (h : n ∣ m) (a : (ZMod m)ˣ) :
    ↑(unitsMap h a) = ((a : ZMod m).cast : ZMod n) := rfl

/--
lemma `isUnit_cast_of_dvd` / 引理 `isUnit_cast_of_dvd`

English:
lemma isUnit_cast_of_dvd
  given: (hm : n ∣ m) (a : Units (ZMod m))
  statement: IsUnit (cast (a : ZMod m) : ZMod n)
  proof: Units.isUnit (unitsMap hm a)

中文:
引理 isUnit_cast_of_dvd
  条件: (hm : n ∣ m) (a : 单位群 (ZMod m))
  结论: 是单位 (cast (a : ZMod m) : ZMod n)
  证明: Units.isUnit (unitsMap hm a)

Depends on / 依赖: Units.isUnit, isUnit, unitsMap
-/
lemma isUnit_cast_of_dvd (hm : n ∣ m) (a : Units (ZMod m)) : IsUnit (cast (a : ZMod m) : ZMod n) :=
  Units.isUnit (unitsMap hm a)
/--
theorem `unitsMap_surjective` / 定理 `unitsMap_surjective`

English:
theorem unitsMap_surjective
  given: [hm : NeZero m] (h : n ∣ m)
  proof: by
  suffices forall x : Nat, x.Coprime n -> exists k : Nat, (x + k * n).Coprime m by
    intro x
    have ⟨k, hk⟩ := this x.val.val (val_coe_unit_coprime x)
    refine ⟨unitOfCoprime _ hk, Units.ext ?_⟩
    have : NeZero n := ⟨fun hn => hm.out (eq_zero_of_zero_dvd (hn ▸ h))⟩
    simp [unitsMap_def, -castHom_apply]
  intro x hx
  let ps : Finset Nat := {p in m.primeFactors | ¬p ∣ x}
  use ps.prod id
  apply Nat.coprime_of_dvd
  intro p pp hp hpn
  by_cases hpx : p ∣ x
  · have h := Nat.dvd_sub hp hpx
    rw [add_comm]; rw [Nat.add_sub_cancel] at h
    rcases pp.dvd_mul.mp h with h | h
    · have ⟨q, hq, hq'⟩ := (pp.prime.dvd_finsetProd_iff id).mp h
      rw [Finset.mem_filter]; rw [Nat.mem_primeFactors]; rw [← (Nat.prime_dvd_prime_iff_eq pp hq.1.1).mp hq'] at hq
      exact hq.2 hpx
    · exact Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, pp, hpx, h⟩ hx
  · have pps : p in ps := Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨pp, hpn, hm.out⟩, hpx⟩
    have h := Nat.dvd_sub hp ((Finset.dvd_prod_of_mem id pps).mul_right n)
    rw [Nat.add_sub_cancel] at h
    contradiction

中文:
定理 unitsMap_surjective
  条件: [hm : NeZero m] (h : n ∣ m)
  证明: by
  suffices forall x : Nat, x.Coprime n -> exists k : Nat, (x + k * n).Coprime m by
    intro x
    have ⟨k, hk⟩ := this x.val.val (val_coe_unit_coprime x)
    refine ⟨unitOfCoprime _ hk, Units.ext ?_⟩
    have : NeZero n := ⟨fun hn => hm.out (eq_zero_of_zero_dvd (hn ▸ h))⟩
    simp [unitsMap_def, -castHom_apply]
  intro x hx
  let ps : Finset Nat := {p in m.primeFactors | ¬p ∣ x}
  use ps.prod id
  apply Nat.coprime_of_dvd
  intro p pp hp hpn
  by_cases hpx : p ∣ x
  · have h := Nat.dvd_sub hp hpx
    rw [add_comm]; rw [Nat.add_sub_cancel] at h
    rcases pp.dvd_mul.mp h with h | h
    · have ⟨q, hq, hq'⟩ := (pp.prime.dvd_finsetProd_iff id).mp h
      rw [Finset.mem_filter]; rw [Nat.mem_primeFactors]; rw [← (Nat.prime_dvd_prime_iff_eq pp hq.1.1).mp hq'] at hq
      exact hq.2 hpx
    · exact Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, pp, hpx, h⟩ hx
  · have pps : p in ps := Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨pp, hpn, hm.out⟩, hpx⟩
    have h := Nat.dvd_sub hp ((Finset.dvd_prod_of_mem id pps).mul_right n)
    rw [Nat.add_sub_cancel] at h
    contradiction

Depends on / 依赖: Coprime, Finset, Nat.add_sub, Nat.coprime_of_dvd, Nat.dvd_sub, NeZero, Units.ext, add_comm, add_sub, castHom_apply, coprime_of_dvd, dvd_sub, eq_zero_of_zero_dvd, hm.out, m.primeFactors, primeFactors, ps.prod, unitOfCoprime, unitsMap_def, val_coe_unit_coprime
-/
theorem unitsMap_surjective [hm : NeZero m] (h : n ∣ m) :
    Function.Surjective (unitsMap h) := by
  suffices forall x : Nat, x.Coprime n -> exists k : Nat, (x + k * n).Coprime m by
    intro x
    have ⟨k, hk⟩ := this x.val.val (val_coe_unit_coprime x)
    refine ⟨unitOfCoprime _ hk, Units.ext ?_⟩
    have : NeZero n := ⟨fun hn => hm.out (eq_zero_of_zero_dvd (hn ▸ h))⟩
    simp [unitsMap_def, -castHom_apply]
  intro x hx
  let ps : Finset Nat := {p in m.primeFactors | ¬p ∣ x}
  use ps.prod id
  apply Nat.coprime_of_dvd
  intro p pp hp hpn
  by_cases hpx : p ∣ x
  · have h := Nat.dvd_sub hp hpx
    rw [add_comm]; rw [Nat.add_sub_cancel] at h
    rcases pp.dvd_mul.mp h with h | h
    · have ⟨q, hq, hq'⟩ := (pp.prime.dvd_finsetProd_iff id).mp h
      rw [Finset.mem_filter]; rw [Nat.mem_primeFactors]; rw [← (Nat.prime_dvd_prime_iff_eq pp hq.1.1).mp hq'] at hq
      exact hq.2 hpx
    · exact Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, pp, hpx, h⟩ hx
  · have pps : p in ps := Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨pp, hpn, hm.out⟩, hpx⟩
    have h := Nat.dvd_sub hp ((Finset.dvd_prod_of_mem id pps).mul_right n)
    rw [Nat.add_sub_cancel] at h
    contradiction

-- This needs `Nat.primeFactors`, so cannot go into `Mathlib/Data/ZMod/Basic.lean`.
open Nat in
/--
lemma `not_isUnit_of_mem_primeFactors` / 引理 `not_isUnit_of_mem_primeFactors`

English:
lemma not_isUnit_of_mem_primeFactors
  given: {n p : Nat} (h : p in n.primeFactors)
  proof: by
  rw [isUnit_iff_coprime]
exact (Prime.dvd_iff_not_coprime <| prime_of_mem_primeFactors h).mp dvd_of_mem_primeFactors h

中文:
引理 not_isUnit_of_mem_primeFactors
  条件: {n p : 自然数} (h : p in n.primeFactors)
  证明: by
  rw [isUnit_iff_coprime]
exact (Prime.dvd_iff_not_coprime <| prime_of_mem_primeFactors h).mp dvd_of_mem_primeFactors h

Depends on / 依赖: Prime.dvd_iff_not_coprime, dvd_iff_not_coprime, dvd_of_mem_primeFactors, isUnit_iff_coprime, prime_of_mem_primeFactors
-/
lemma not_isUnit_of_mem_primeFactors {n p : Nat} (h : p in n.primeFactors) :
    ¬ IsUnit (p : ZMod n) := by
  rw [isUnit_iff_coprime]
exact (Prime.dvd_iff_not_coprime <| prime_of_mem_primeFactors h).mp dvd_of_mem_primeFactors h

set_option backward.isDefEq.respectTransparency false in
/--
lemma `eq_unit_mul_divisor` / 引理 `eq_unit_mul_divisor`

English:
lemma eq_unit_mul_divisor
  given: {N : Nat} (a : ZMod N)
  proof: by
  rcases eq_or_ne N 0 with rfl | hN
  -- Silly special case : N = 0. Of no mathematical interest, but true, so let's prove it.
  · change Int at a
    rcases eq_or_ne a 0 with rfl | ha
    · refine ⟨0, dvd_zero _, 1, isUnit_one, by rw [Nat.cast_zero, mul_zero]⟩
    refine ⟨a.natAbs, dvd_zero _, Int.sign a, ?_, (Int.sign_mul_natAbs a).symm⟩
    rcases lt_or_gt_of_ne ha with h | h
    · simp only [Int.sign_eq_neg_one_of_neg h, IsUnit.neg_iff, isUnit_one]
    · simp only [Int.sign_eq_one_of_pos h, isUnit_one]
  -- now the interesting case
  have : NeZero N := ⟨hN⟩
  -- Define `d` as the GCD of a lift of `a` and `N`.
  let d := a.val.gcd N
  have hd : d != 0 := Nat.gcd_ne_zero_right hN
  obtain ⟨a₀, (ha₀ : _ = d * _)⟩ := a.val.gcd_dvd_left N
  obtain ⟨N₀, (hN₀ : _ = d * _)⟩ := a.val.gcd_dvd_right N
  refine ⟨d, ⟨N₀, hN₀⟩, ?_⟩
  -- Show `a` is a unit mod `N / d`.
  have hu₀ : IsUnit (a₀ : ZMod N₀) := by
    refine (isUnit_iff_coprime _ _).mpr (Nat.isCoprime_iff_coprime.mp ?_)
    obtain ⟨p, q, hpq⟩ : exists (p q : Int), d = a.val * p + N * q := ⟨_, _, Nat.gcd_eq_gcd_ab _ _⟩
    rw [ha₀]; rw [hN₀]; rw [Nat.cast_mul]; rw [Nat.cast_mul]; rw [mul_assoc]; rw [mul_assoc]; rw [← mul_add]; rw [eq_comm]; rw [mul_comm _ p]; rw [mul_comm _ q] at hpq
    exact ⟨p, q, Int.eq_one_of_mul_eq_self_right (Nat.cast_ne_zero.mpr hd) hpq⟩
  -- Lift it arbitrarily to a unit mod `N`.
  obtain ⟨u, hu⟩ := (unitsMap_surjective (⟨d, mul_comm d N₀ ▸ hN₀⟩ : N₀ ∣ N)) hu₀.unit
  rw [unitsMap_def]; rw [← Units.val_inj]; rw [Units.coe_map]; rw [IsUnit.unit_spec]; rw [MonoidHom.coe_coe] at hu
  refine ⟨u.val, u.isUnit, ?_⟩
  rw [← natCast_zmod_val a]; rw [← natCast_zmod_val u.1]; rw [ha₀]; rw [← Nat.cast_mul]; rw [natCast_eq_natCast_iff]; rw [mul_comm _ d]; rw [Nat.ModEq]
  simp only [hN₀, Nat.mul_mod_mul_left, Nat.mul_right_inj hd]
  rw [← Nat.ModEq]; rw [← natCast_eq_natCast_iff]; rw [← hu]; rw [natCast_val]; rw [castHom_apply]

中文:
引理 eq_unit_mul_divisor
  条件: {N : 自然数} (a : ZMod N)
  证明: by
  rcases eq_or_ne N 0 with rfl | hN
  -- Silly special case : N = 0. Of no mathematical interest, but true, so let's prove it.
  · change Int at a
    rcases eq_or_ne a 0 with rfl | ha
    · refine ⟨0, dvd_zero _, 1, isUnit_one, by rw [Nat.cast_zero, mul_zero]⟩
    refine ⟨a.natAbs, dvd_zero _, Int.sign a, ?_, (Int.sign_mul_natAbs a).symm⟩
    rcases lt_or_gt_of_ne ha with h | h
    · simp only [Int.sign_eq_neg_one_of_neg h, IsUnit.neg_iff, isUnit_one]
    · simp only [Int.sign_eq_one_of_pos h, isUnit_one]
  -- now the interesting case
  have : NeZero N := ⟨hN⟩
  -- Define `d` as the GCD of a lift of `a` and `N`.
  let d := a.val.gcd N
  have hd : d != 0 := Nat.gcd_ne_zero_right hN
  obtain ⟨a₀, (ha₀ : _ = d * _)⟩ := a.val.gcd_dvd_left N
  obtain ⟨N₀, (hN₀ : _ = d * _)⟩ := a.val.gcd_dvd_right N
  refine ⟨d, ⟨N₀, hN₀⟩, ?_⟩
  -- Show `a` is a unit mod `N / d`.
  have hu₀ : IsUnit (a₀ : ZMod N₀) := by
    refine (isUnit_iff_coprime _ _).mpr (Nat.isCoprime_iff_coprime.mp ?_)
    obtain ⟨p, q, hpq⟩ : exists (p q : Int), d = a.val * p + N * q := ⟨_, _, Nat.gcd_eq_gcd_ab _ _⟩
    rw [ha₀]; rw [hN₀]; rw [Nat.cast_mul]; rw [Nat.cast_mul]; rw [mul_assoc]; rw [mul_assoc]; rw [← mul_add]; rw [eq_comm]; rw [mul_comm _ p]; rw [mul_comm _ q] at hpq
    exact ⟨p, q, Int.eq_one_of_mul_eq_self_right (Nat.cast_ne_zero.mpr hd) hpq⟩
  -- Lift it arbitrarily to a unit mod `N`.
  obtain ⟨u, hu⟩ := (unitsMap_surjective (⟨d, mul_comm d N₀ ▸ hN₀⟩ : N₀ ∣ N)) hu₀.unit
  rw [unitsMap_def]; rw [← Units.val_inj]; rw [Units.coe_map]; rw [IsUnit.unit_spec]; rw [MonoidHom.coe_coe] at hu
  refine ⟨u.val, u.isUnit, ?_⟩
  rw [← natCast_zmod_val a]; rw [← natCast_zmod_val u.1]; rw [ha₀]; rw [← Nat.cast_mul]; rw [natCast_eq_natCast_iff]; rw [mul_comm _ d]; rw [Nat.ModEq]
  simp only [hN₀, Nat.mul_mod_mul_left, Nat.mul_right_inj hd]
  rw [← Nat.ModEq]; rw [← natCast_eq_natCast_iff]; rw [← hu]; rw [natCast_val]; rw [castHom_apply]

Depends on / 依赖: eq_or_ne
-/
lemma eq_unit_mul_divisor {N : Nat} (a : ZMod N) :
    exists d : Nat, d ∣ N ∧ exists (u : ZMod N), IsUnit u ∧ a = u * d := by
  rcases eq_or_ne N 0 with rfl | hN
  -- Silly special case : N = 0. Of no mathematical interest, but true, so let's prove it.
  · change Int at a
    rcases eq_or_ne a 0 with rfl | ha
    · refine ⟨0, dvd_zero _, 1, isUnit_one, by rw [Nat.cast_zero, mul_zero]⟩
    refine ⟨a.natAbs, dvd_zero _, Int.sign a, ?_, (Int.sign_mul_natAbs a).symm⟩
    rcases lt_or_gt_of_ne ha with h | h
    · simp only [Int.sign_eq_neg_one_of_neg h, IsUnit.neg_iff, isUnit_one]
    · simp only [Int.sign_eq_one_of_pos h, isUnit_one]
  -- now the interesting case
  have : NeZero N := ⟨hN⟩
  -- Define `d` as the GCD of a lift of `a` and `N`.
  let d := a.val.gcd N
  have hd : d != 0 := Nat.gcd_ne_zero_right hN
  obtain ⟨a₀, (ha₀ : _ = d * _)⟩ := a.val.gcd_dvd_left N
  obtain ⟨N₀, (hN₀ : _ = d * _)⟩ := a.val.gcd_dvd_right N
  refine ⟨d, ⟨N₀, hN₀⟩, ?_⟩
  -- Show `a` is a unit mod `N / d`.
  have hu₀ : IsUnit (a₀ : ZMod N₀) := by
    refine (isUnit_iff_coprime _ _).mpr (Nat.isCoprime_iff_coprime.mp ?_)
    obtain ⟨p, q, hpq⟩ : exists (p q : Int), d = a.val * p + N * q := ⟨_, _, Nat.gcd_eq_gcd_ab _ _⟩
    rw [ha₀]; rw [hN₀]; rw [Nat.cast_mul]; rw [Nat.cast_mul]; rw [mul_assoc]; rw [mul_assoc]; rw [← mul_add]; rw [eq_comm]; rw [mul_comm _ p]; rw [mul_comm _ q] at hpq
    exact ⟨p, q, Int.eq_one_of_mul_eq_self_right (Nat.cast_ne_zero.mpr hd) hpq⟩
  -- Lift it arbitrarily to a unit mod `N`.
  obtain ⟨u, hu⟩ := (unitsMap_surjective (⟨d, mul_comm d N₀ ▸ hN₀⟩ : N₀ ∣ N)) hu₀.unit
  rw [unitsMap_def]; rw [← Units.val_inj]; rw [Units.coe_map]; rw [IsUnit.unit_spec]; rw [MonoidHom.coe_coe] at hu
  refine ⟨u.val, u.isUnit, ?_⟩
  rw [← natCast_zmod_val a]; rw [← natCast_zmod_val u.1]; rw [ha₀]; rw [← Nat.cast_mul]; rw [natCast_eq_natCast_iff]; rw [mul_comm _ d]; rw [Nat.ModEq]
  simp only [hN₀, Nat.mul_mod_mul_left, Nat.mul_right_inj hd]
  rw [← Nat.ModEq]; rw [← natCast_eq_natCast_iff]; rw [← hu]; rw [natCast_val]; rw [castHom_apply]

/--
theorem `coe_int_mul_inv_eq_one` / 定理 `coe_int_mul_inv_eq_one`

English:
theorem coe_int_mul_inv_eq_one
  given: {n : Nat} {x : Int} (h : IsCoprime x n)
  proof: by
  by_cases hn : n = 0
  · simp only [hn, Nat.cast_zero, isCoprime_zero_right] at h
    rcases Int.isUnit_eq_one_or h with h | h <;> simp [h]
  have : NeZero n := ⟨hn⟩
  rw [← natCast_zmod_val x]
  apply coe_mul_inv_eq_one
  rwa [Int.isCoprime_iff_gcd_eq_one, ← Int.gcd_emod, ← val_intCast] at h

中文:
定理 coe_int_mul_inv_eq_one
  条件: {n : 自然数} {x : 整数} (h : IsCoprime x n)
  证明: by
  by_cases hn : n = 0
  · simp only [hn, Nat.cast_zero, isCoprime_zero_right] at h
    rcases Int.isUnit_eq_one_or h with h | h <;> simp [h]
  have : NeZero n := ⟨hn⟩
  rw [← natCast_zmod_val x]
  apply coe_mul_inv_eq_one
  rwa [Int.isCoprime_iff_gcd_eq_one, ← Int.gcd_emod, ← val_intCast] at h

Depends on / 依赖: Int.gcd_emod, Int.isCoprime_iff_gcd_eq_one, Int.isUnit_eq_one_or, Nat.cast_zero, NeZero, cast_zero, coe_mul_inv_eq_one, gcd_emod, isCoprime_iff_gcd_eq_one, isCoprime_zero_right, isUnit_eq_one_or, natCast_zmod_val, val_intCast
-/
theorem coe_int_mul_inv_eq_one {n : Nat} {x : Int} (h : IsCoprime x n) :
    (x : ZMod n) * (x : ZMod n)⁻¹ = 1 := by
  by_cases hn : n = 0
  · simp only [hn, Nat.cast_zero, isCoprime_zero_right] at h
    rcases Int.isUnit_eq_one_or h with h | h <;> simp [h]
  have : NeZero n := ⟨hn⟩
  rw [← natCast_zmod_val x]
  apply coe_mul_inv_eq_one
  rwa [Int.isCoprime_iff_gcd_eq_one, ← Int.gcd_emod, ← val_intCast] at h

/--
theorem `coe_int_inv_mul_eq_one` / 定理 `coe_int_inv_mul_eq_one`

English:
theorem coe_int_inv_mul_eq_one
  given: {n : Nat} {x : Int} (h : IsCoprime x n)
  proof: by
  rw [mul_comm]; rw [coe_int_mul_inv_eq_one h]

中文:
定理 coe_int_inv_mul_eq_one
  条件: {n : 自然数} {x : 整数} (h : IsCoprime x n)
  证明: by
  rw [mul_comm]; rw [coe_int_mul_inv_eq_one h]

Depends on / 依赖: coe_int_mul_inv_eq_one, mul_comm
-/
theorem coe_int_inv_mul_eq_one {n : Nat} {x : Int} (h : IsCoprime x n) :
    (x : ZMod n)⁻¹ * (x : ZMod n) = 1 := by
  rw [mul_comm]; rw [coe_int_mul_inv_eq_one h]

/--
lemma `coe_int_mul_val_inv` / 引理 `coe_int_mul_val_inv`

English:
lemma coe_int_mul_val_inv
  given: {n : Nat} [NeZero n] {m : Int} (h : IsCoprime m n)
  proof: by
  rw [natCast_zmod_val]; rw [coe_int_mul_inv_eq_one h]

中文:
引理 coe_int_mul_val_inv
  条件: {n : 自然数} [NeZero n] {m : 整数} (h : IsCoprime m n)
  证明: by
  rw [natCast_zmod_val]; rw [coe_int_mul_inv_eq_one h]

Depends on / 依赖: coe_int_mul_inv_eq_one, natCast_zmod_val
-/
lemma coe_int_mul_val_inv {n : Nat} [NeZero n] {m : Int} (h : IsCoprime m n) :
    (m * (m⁻¹ : ZMod n).val : ZMod n) = 1 := by
  rw [natCast_zmod_val]; rw [coe_int_mul_inv_eq_one h]

/--
lemma `coe_int_val_inv_mul` / 引理 `coe_int_val_inv_mul`

English:
lemma coe_int_val_inv_mul
  given: {n : Nat} [NeZero n] {m : Int} (h : IsCoprime m n)
  proof: by
  rw [mul_comm]; rw [coe_int_mul_val_inv h]

中文:
引理 coe_int_val_inv_mul
  条件: {n : 自然数} [NeZero n] {m : 整数} (h : IsCoprime m n)
  证明: by
  rw [mul_comm]; rw [coe_int_mul_val_inv h]

Depends on / 依赖: coe_int_mul_val_inv, mul_comm
-/
lemma coe_int_val_inv_mul {n : Nat} [NeZero n] {m : Int} (h : IsCoprime m n) :
    ((m⁻¹ : ZMod n).val : ZMod n) * m = 1 := by
  rw [mul_comm]; rw [coe_int_mul_val_inv h]

/--
Definition of `unitOfIsCoprime` / `unitOfIsCoprime` 的定义

English:
definition unitOfIsCoprime
  signature: {m : Nat} (n : Int)
  body: n
  inv := n⁻¹
  val_inv := coe_int_mul_inv_eq_one h
  inv_val := coe_int_inv_mul_eq_one h

@[simp]

中文:
定义 unitOfIsCoprime
  签名: {m : 自然数} (n : 整数)
  定义体: n
  inv := n⁻¹
  val_inv := coe_int_mul_inv_eq_one h
  inv_val := coe_int_inv_mul_eq_one h

@[simp]
-/
def unitOfIsCoprime {m : Nat} (n : Int)
    (h : IsCoprime n (m : Int)) : (ZMod m)ˣ where
  val := n
  inv := n⁻¹
  val_inv := coe_int_mul_inv_eq_one h
  inv_val := coe_int_inv_mul_eq_one h

@[simp]
/--
theorem `coe_unitOfIsCoprime` / 定理 `coe_unitOfIsCoprime`

English:
theorem coe_unitOfIsCoprime
  given: {m : Nat} (n : Int) (h : IsCoprime n ↑m)
  proof: rfl

中文:
定理 coe_unitOfIsCoprime
  条件: {m : 自然数} (n : 整数) (h : IsCoprime n ↑m)
  证明: rfl
-/
theorem coe_unitOfIsCoprime {m : Nat} (n : Int) (h : IsCoprime n ↑m) :
    (unitOfIsCoprime n h : ZMod m) = n := rfl

/--
theorem `isUnit_inv` / 定理 `isUnit_inv`

English:
theorem isUnit_inv
  given: {m : Nat} {n : Int} (h : IsUnit (n : ZMod m))
  proof: by
  rw [isUnit_iff_exists]
  exact ⟨n, inv_mul_of_unit _ h, mul_inv_of_unit _ h⟩

中文:
定理 isUnit_inv
  条件: {m : 自然数} {n : 整数} (h : 是单位 (n : ZMod m))
  证明: by
  rw [isUnit_iff_exists]
  exact ⟨n, inv_mul_of_unit _ h, mul_inv_of_unit _ h⟩

Depends on / 依赖: inv_mul_of_unit, isUnit_iff_exists, mul_inv_of_unit
-/
theorem isUnit_inv {m : Nat} {n : Int} (h : IsUnit (n : ZMod m)) :
    IsUnit (n : ZMod m)⁻¹ := by
  rw [isUnit_iff_exists]
  exact ⟨n, inv_mul_of_unit _ h, mul_inv_of_unit _ h⟩

/--
theorem `coe_int_isUnit_iff_isCoprime` / 定理 `coe_int_isUnit_iff_isCoprime`

English:
theorem coe_int_isUnit_iff_isCoprime
  given: (n : Int) (m : Nat)
  proof: by
  refine ⟨fun h => ?_, fun h => ⟨unitOfIsCoprime n (isCoprime_comm.mp h), by simp⟩⟩
  obtain rfl | hm := eq_or_ne m 0
  · rw [Nat.cast_zero, isCoprime_zero_left]
    exact_mod_cast h
  · have : NeZero m := ⟨hm⟩
    obtain ⟨u, hu⟩ := h
    have h_coprime := val_coe_unit_coprime u
    rw [hu]; rw [Nat.coprime_iff_gcd_eq_one]; rw [← Int.gcd_natCast_natCast]; rw [val_intCast]; rw [Int.gcd_emod] at h_coprime
    rwa [isCoprime_comm, Int.isCoprime_iff_gcd_eq_one]

中文:
定理 coe_int_isUnit_iff_isCoprime
  条件: (n : 整数) (m : 自然数)
  证明: by
  refine ⟨fun h => ?_, fun h => ⟨unitOfIsCoprime n (isCoprime_comm.mp h), by simp⟩⟩
  obtain rfl | hm := eq_or_ne m 0
  · rw [Nat.cast_zero, isCoprime_zero_left]
    exact_mod_cast h
  · have : NeZero m := ⟨hm⟩
    obtain ⟨u, hu⟩ := h
    have h_coprime := val_coe_unit_coprime u
    rw [hu]; rw [Nat.coprime_iff_gcd_eq_one]; rw [← Int.gcd_natCast_natCast]; rw [val_intCast]; rw [Int.gcd_emod] at h_coprime
    rwa [isCoprime_comm, Int.isCoprime_iff_gcd_eq_one]

Depends on / 依赖: Int.gcd_emod, Int.gcd_natCast_natCast, Int.isCoprime_iff_gcd_eq_one, Nat.cast_zero, Nat.coprime_iff_gcd_eq_one, NeZero, cast_zero, coprime_iff_gcd_eq_one, eq_or_ne, gcd_emod, gcd_natCast_natCast, h_coprime, isCoprime_comm, isCoprime_comm.mp, isCoprime_iff_gcd_eq_one, isCoprime_zero_left, unitOfIsCoprime, val_coe_unit_coprime, val_intCast
-/
theorem coe_int_isUnit_iff_isCoprime (n : Int) (m : Nat) :
    IsUnit (n : ZMod m) ↔ IsCoprime (m : Int) n := by
  refine ⟨fun h => ?_, fun h => ⟨unitOfIsCoprime n (isCoprime_comm.mp h), by simp⟩⟩
  obtain rfl | hm := eq_or_ne m 0
  · rw [Nat.cast_zero, isCoprime_zero_left]
    exact_mod_cast h
  · have : NeZero m := ⟨hm⟩
    obtain ⟨u, hu⟩ := h
    have h_coprime := val_coe_unit_coprime u
    rw [hu]; rw [Nat.coprime_iff_gcd_eq_one]; rw [← Int.gcd_natCast_natCast]; rw [val_intCast]; rw [Int.gcd_emod] at h_coprime
    rwa [isCoprime_comm, Int.isCoprime_iff_gcd_eq_one]

/--
Instance `instFiniteZModUnits` / 实例 `instFiniteZModUnits`

English:
instance instFiniteZModUnits
  signature: : (n : Nat) -> Finite (ZMod n)ˣ

中文:
实例 instFiniteZModUnits
  签名: : (n : 自然数) -> 有限 (ZMod n)ˣ
-/
instance instFiniteZModUnits : (n : Nat) -> Finite (ZMod n)ˣ
  | 0 => Finite.of_fintype Intˣ
  | _ + 1 => inferInstance

end ZMod
