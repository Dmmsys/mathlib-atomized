/-
Copyright (c) 2026 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.LinearAlgebra.SModEq.Basic
public import Mathlib.RingTheory.Ideal.Operations

/-! # Lemmas about SModEq related to powers -/

public section

namespace SModEq
variable {R : Type*} [CommRing R] {I J : Ideal R} {p : Nat} (hpI : (p : R) in I)
include hpI

/--
theorem `pow_mul_of_le` / 定理 `pow_mul_of_le`

English:
theorem pow_mul_of_le
  given: {x y : R} (h : x ≡ y [SMOD J]) (hJI : J <= I)
  proof: by
have h₁ := idealQuotientMk.mp h.mono hJI
  rw [SModEq.sub_mem] at h ⊢
  rw [← Commute.mul_neg_geom_sum₂ (.all _ _)]
  refine Ideal.mul_mem_mul h ?_
  have h₂ : (p : R ⧸ I) = 0 := by simpa using Ideal.Quotient.eq_zero_iff_mem.mpr hpI
  simp only [← Ideal.Quotient.eq_zero_iff_mem, map_sum, map_mul,

中文:
定理 pow_mul_of_le
  条件: {x y : R} (h : x ≡ y [SMOD J]) (hJI : J <= I)
  证明: by
have h₁ := idealQuotientMk.mp h.mono hJI
  rw [SModEq.sub_mem] at h ⊢
  rw [← Commute.mul_neg_geom_sum₂ (.all _ _)]
  refine Ideal.mul_mem_mul h ?_
  have h₂ : (p : R ⧸ I) = 0 := by simpa using Ideal.Quotient.eq_zero_iff_mem.mpr hpI
  simp only [← Ideal.Quotient.eq_zero_iff_mem, map_sum, map_mul,

Depends on / 依赖: Commute, Commute.mul_neg_geom_sum, Finset, Finset.range, Finset.sum_congr, Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.eq_zero_iff_mem.mpr, Ideal.Quotient.mk, Ideal.mul_mem_mul, Quotient, SModEq, SModEq.sub_mem, eq_zero_iff_mem, h.mono, idealQuotientMk, idealQuotientMk.mp, map_mul, map_pow, map_sum, mul_mem_mul
-/
theorem pow_mul_of_le {x y : R} (h : x ≡ y [SMOD J]) (hJI : J <= I) :
    x ^ p ≡ y ^ p [SMOD J * I] := by
have h₁ := idealQuotientMk.mp h.mono hJI
  rw [SModEq.sub_mem] at h ⊢
  rw [← Commute.mul_neg_geom_sum₂ (.all _ _)]
  refine Ideal.mul_mem_mul h ?_
  have h₂ : (p : R ⧸ I) = 0 := by simpa using Ideal.Quotient.eq_zero_iff_mem.mpr hpI
  simp only [← Ideal.Quotient.eq_zero_iff_mem, map_sum, map_mul, map_pow, h₁, ← pow_add]
  trans ∑ x in Finset.range p, Ideal.Quotient.mk I y ^ (p - 1)
  · exact Finset.sum_congr rfl fun _ _ => by grind
  simp [h₂]

/--
theorem `pow_add_one` / 定理 `pow_add_one`

English:
theorem pow_add_one
  given: {x y : R} {m : Nat} (hm : m != 0) (h : x ≡ y [SMOD I ^ m])
  proof: h.pow_mul_of_le hpI I.pow_le_self hm

中文:
定理 pow_add_one
  条件: {x y : R} {m : 自然数} (hm : m != 0) (h : x ≡ y [SMOD I ^ m])
  证明: h.pow_mul_of_le hpI I.pow_le_self hm

Depends on / 依赖: I.pow_le_self, h.pow_mul_of_le, pow_le_self, pow_mul_of_le
-/
theorem pow_add_one {x y : R} {m : Nat} (hm : m != 0) (h : x ≡ y [SMOD I ^ m]) :
x ^ p ≡ y ^ p [SMOD I ^ (m + 1)] := h.pow_mul_of_le hpI I.pow_le_self hm

/--
theorem `pow_pow_add_one` / 定理 `pow_pow_add_one`

English:
theorem pow_pow_add_one
  given: {x y : R} (h : x ≡ y [SMOD I]) (m : Nat)
  proof: by
  induction m with
  | zero => simpa
  | succ m ih =>
    simp_rw [pow_succ _ m, pow_mul]
    exact ih.pow_add_one hpI m.succ_ne_zero

中文:
定理 pow_pow_add_one
  条件: {x y : R} (h : x ≡ y [SMOD I]) (m : 自然数)
  证明: by
  induction m with
  | zero => simpa
  | succ m ih =>
    simp_rw [pow_succ _ m, pow_mul]
    exact ih.pow_add_one hpI m.succ_ne_zero

Depends on / 依赖: ih.pow_add_one, m.succ_ne_zero, pow_add_one, pow_mul, pow_succ, simp_rw, succ_ne_zero
-/
theorem pow_pow_add_one {x y : R} (h : x ≡ y [SMOD I]) (m : Nat) :
    x ^ p ^ m ≡ y ^ p ^ m [SMOD I ^ (m + 1)] := by
  induction m with
  | zero => simpa
  | succ m ih =>
    simp_rw [pow_succ _ m, pow_mul]
    exact ih.pow_add_one hpI m.succ_ne_zero

end SModEq
